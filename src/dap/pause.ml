(** Kernel-side hook callbacks.

    The kernel thread runs [Compile.compile_file], which fires
    [Handle.Dap_hooks] callbacks at each tactic / proof boundary.
    These callbacks consult [State] to decide whether to pause. When
    pausing:

    1. Mark [State.status <- Paused …] under the lock.
    2. Emit a [stopped] DAP event from the kernel thread.
    3. Block on [State.run_cv] until the main thread, in response to a
       [continue]/[next]/[stepOut] request, signals it.

    The wait happens *with the lock held* — [Condition.wait] atomically
    releases the mutex while waiting and reacquires it on wake, which
    is the standard condvar discipline. *)

module H = Handle.Dap_hooks
module J = Yojson.Safe

let stopped_event ~(reason : string) ~(thread_id : int) : J.t =
  Msg.event ~event:"stopped"
    ~body:(`Assoc [
      "reason",            `String reason
    ; "threadId",          `Int thread_id
    ; "allThreadsStopped", `Bool true
    ])
    ()

let kernel_thread_id = 1

let send_stopped reason = Io.send (stopped_event ~reason ~thread_id:kernel_thread_id)

(** Decide whether to pause at a [before_tactic] boundary, and if so,
    why. We treat the very first tactic of a [launch ~stopOnEntry:true]
    run as ["entry"]; explicit [next] from the user is ["step"];
    breakpoints are ["breakpoint"]. *)
let reason_for_pause (s : State.t) (e : H.before_tactic_event) : string option =
  State.with_lock s (fun () ->
    match s.status with
    | State.Paused _ | Idle | Configuring | Terminated -> None
    | Running ->
        let bp =
          State.(s.breakpoints) |> ignore;  (* keep ref *)
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

let pause_kernel (s : State.t) ~(reason : string) ~(pos : H.tactic_pos)
    ~(snapshot : H.proof_snapshot) ~(error : string option) : unit =
  Mutex.lock s.m;
  s.status <- State.Paused { reason; pos; snapshot; error };
  Mutex.unlock s.m;
  send_stopped reason;
  (* Wait until the main thread flips status back to Running. *)
  Mutex.lock s.m;
  let rec wait () =
    match s.status with
    | State.Running | Terminated -> ()
    | _ -> Condition.wait s.run_cv s.m; wait ()
  in
  wait ();
  Mutex.unlock s.m

let on_before_proof (s : State.t) (e : H.before_proof_event) : unit =
  if s.stop_on_entry then
    pause_kernel s ~reason:"entry" ~pos:e.bp_pos
      ~snapshot:e.bp_state ~error:None

let on_before_tactic (s : State.t) (e : H.before_tactic_event) : unit =
  match reason_for_pause s e with
  | None -> ()
  | Some reason ->
      pause_kernel s ~reason ~pos:e.bt_pos
        ~snapshot:e.bt_state ~error:None

let on_after_tactic (s : State.t) (e : H.after_tactic_event) : unit =
  match e.at_error with
  | None -> ()
  | Some msg ->
      pause_kernel s ~reason:"exception" ~pos:e.at_pos
        ~snapshot:e.at_state ~error:(Some msg)

let on_after_proof (s : State.t) (_e : H.after_proof_event) : unit =
  State.with_lock s (fun () ->
    match s.step_mode with
    | Step_out ->
        (* [stepOut] resolves at the proof boundary — drop back to
           [Continue] and we'll hit the next user-set breakpoint. *)
        s.step_mode <- Continue
    | _ -> ())

let install (s : State.t) : unit =
  let cb : H.callbacks =
    { before_proof  = on_before_proof  s
    ; before_tactic = on_before_tactic s
    ; after_tactic  = on_after_tactic  s
    ; after_proof   = on_after_proof   s }
  in
  H.set_callbacks cb
