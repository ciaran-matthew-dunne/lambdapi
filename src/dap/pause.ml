(** Kernel-side hook callbacks.

    The kernel thread runs [Compile.compile_file], which fires
    [Handle.Dap_hooks] callbacks at each tactic / proof boundary.
    These callbacks consult [State] to decide whether to pause. When
    pausing:

    1. Mark [State.status <- Paused …] under the lock.
    2. Emit a [stopped] DAP event from the kernel thread.
    3. Loop on [State.wakeup_cv] servicing one [kernel_action] per
       wake. [Eval] is run inline (mutates kernel state, replies to
       the I/O thread). [Resume] returns from this function. [Rewind]
       raises [Dap_hooks.Rewind_to k], which the kernel's
       [Command.handle] wrapper catches to restart the proof.

    The wait happens *with the lock held* — [Condition.wait] atomically
    releases the mutex while waiting and reacquires it on wake, which
    is the standard condvar discipline. *)

module H = Handle.Dap_hooks
module J = Yojson.Safe

let kernel_thread_id = 1

let stopped_event ~(reason : string) : J.t =
  Msg.event ~event:"stopped"
    ~body:(`Assoc [
      "reason",            `String reason
    ; "threadId",          `Int kernel_thread_id
    ; "allThreadsStopped", `Bool true
    ])
    ()

let send_stopped reason = Io.send (stopped_event ~reason)

(** Decide whether to pause at a [before_tactic] boundary, and if so,
    why. We treat the very first tactic of a [launch ~stopOnEntry:true]
    run as ["entry"] (handled separately in [on_before_proof]); explicit
    [next] from the user is ["step"]; breakpoints are ["breakpoint"]. *)
let reason_for_pause (s : State.t) (e : H.before_tactic_event) : string option =
  State.with_lock s (fun () ->
    match s.status with
    | State.Paused _ | Idle | Configuring | Terminated -> None
    | Running ->
        let bp =
          let path = e.bt_pos.fname in
          (match Hashtbl.find_opt s.breakpoints
                   (State.normalise_path path) with
           | None -> false
           | Some lines -> List.mem e.bt_pos.start_line lines)
        in
        if bp then Some "breakpoint"
        else match s.step_mode with
          | Continue -> None
          | Step     -> Some "step"
          | Step_out -> None  (* Step_out resolves at after_proof. *))

(** Run an [Eval] action: parse the user's expression as a query and
    run it against the live [ss]/[ps]. Tactic-style probes are
    deferred to a later milestone (they need parser work to scope
    a free-floating tactic).

    Catches [Fatal] so a bad expression doesn't kill the kernel. *)
let run_eval
    (ss : Core.Sig_state.t) (ps : Handle.Proof.proof_state) (expr : string)
  : State.eval_outcome =
  let open Parsing in
  let trimmed =
    let n = String.length expr in
    if n > 0 && expr.[n - 1] = ';' then expr else expr ^ ";"
  in
  let cmd : Syntax.p_command option =
    try
      let stream = Parser.Lp.parse_string "<dap-eval>" trimmed in
      (* Take the first parsed command; ignore anything after. *)
      let result = ref None in
      (try
         Common.Debug.stream_iter
           (fun cmd -> result := Some cmd; raise Exit)
           stream
       with Exit -> ());
      !result
    with _ -> None
  in
  match cmd with
  | None ->
      Eval_err "could not parse expression as a query (compute / type / print / proofterm / search)"
  | Some { elt = P_query q; _ } ->
      (try
         match Handle.Query.handle ss (Some ps) q with
         | None     -> Eval_ok ""
         | Some thunk -> Eval_ok (thunk ())
       with
       | Common.Error.Fatal (_, msg) -> Eval_err msg
       | e -> Eval_err (Printexc.to_string e))
  | Some _ ->
      Eval_err "only queries are supported here \
                (compute, type, print, proofterm, search)"

(** Block the kernel until the I/O thread releases it via [Resume] or
    redirects via [Rewind]. [Eval] actions run inline and the loop
    continues. Other control state (step_mode, etc.) is set by the
    I/O thread before broadcasting [wakeup_cv]. *)
let pause_kernel
    (s : State.t)
    ~(reason : string) ~(pos : H.tactic_pos)
    ~(snapshot : H.proof_snapshot) ~(error : string option)
    ~(index : int)
    ~(live_ss : Core.Sig_state.t option)
    ~(live_ps : Handle.Proof.proof_state option) : unit =
  let enter () =
    Mutex.lock s.m;
    s.status <- State.Paused
      { reason; pos; snapshot; error; index; live_ss; live_ps };
    Mutex.unlock s.m;
    send_stopped reason
  in
  enter ();
  let rec loop () =
    Mutex.lock s.m;
    while s.next_action = None
       && (match s.status with State.Terminated -> false | _ -> true) do
      Condition.wait s.wakeup_cv s.m
    done;
    let act = s.next_action in
    s.next_action <- None;
    (match act with
     | Some State.Resume | None ->
         (* [None] only happens on [Terminated]. Either way: leave. *)
         Mutex.unlock s.m
     | Some (State.Rewind _ | State.Eval _) ->
         Mutex.unlock s.m);
    match act with
    | None | Some State.Resume -> ()
    | Some (State.Rewind k) ->
        (* Hand control back to [Command.handle]. The kernel will
           catch this, restore [Time], and re-fold from idx 0,
           replaying tactics 0..k-1 silently. *)
        raise (H.Rewind_to k)
    | Some (State.Eval (expr, reply)) ->
        let outcome =
          match live_ss, live_ps with
          | Some ss, Some ps -> run_eval ss ps expr
          | _ -> State.Eval_err "no live proof state at this pause point"
        in
        reply outcome;
        (* Re-enter paused state and resume waiting. *)
        Mutex.lock s.m;
        s.status <- State.Paused
          { reason; pos; snapshot; error; index; live_ss; live_ps };
        Mutex.unlock s.m;
        loop ()
  in
  loop ()

let on_before_proof (s : State.t) (e : H.before_proof_event) : unit =
  if s.stop_on_entry then
    pause_kernel s ~reason:"entry" ~pos:e.bp_pos
      ~snapshot:e.bp_state ~error:None
      ~index:(-1)
      ~live_ss:(Some e.bp_ss) ~live_ps:(Some e.bp_ps)

let on_before_tactic (s : State.t) (e : H.before_tactic_event) : unit =
  match reason_for_pause s e with
  | None -> ()
  | Some reason ->
      pause_kernel s ~reason ~pos:e.bt_pos
        ~snapshot:e.bt_state ~error:None
        ~index:e.bt_index
        ~live_ss:(Some e.bt_ss) ~live_ps:(Some e.bt_ps)

let on_after_tactic (s : State.t) (e : H.after_tactic_event) : unit =
  match e.at_error with
  | None -> ()
  | Some msg ->
      pause_kernel s ~reason:"exception" ~pos:e.at_pos
        ~snapshot:e.at_state ~error:(Some msg)
        ~index:(-1)
        ~live_ss:None ~live_ps:None

let on_after_proof (s : State.t) (_e : H.after_proof_event) : unit =
  State.with_lock s (fun () ->
    match s.step_mode with
    | Step_out ->
        (* [stepOut] resolves at the proof boundary — drop back to
           [Continue] and we'll hit the next user-set breakpoint. *)
        s.step_mode <- State.Continue
    | _ -> ())

let install (s : State.t) : unit =
  let cb : H.callbacks =
    { before_proof  = on_before_proof  s
    ; before_tactic = on_before_tactic s
    ; after_tactic  = on_after_tactic  s
    ; after_proof   = on_after_proof   s }
  in
  H.set_callbacks cb
