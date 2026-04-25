(** Main DAP server loop.

    The main thread reads DAP requests from [stdin], dispatches them,
    and writes responses & events to [stdout]. On [launch], it spawns
    the kernel thread which drives [Compile.compile_file]. The kernel
    thread blocks on [State.run_cv] at each pause point; the main
    thread releases it via [continue]/[next]/[stepOut].

    Kernel exceptions are caught and surfaced as a [terminated] event
    plus an [exited] event with a non-zero code; the adapter does not
    exit (the client decides when to disconnect). *)

module J = Yojson.Safe

(* --- Capabilities (sent in the [initialize] response). --- *)

let capabilities : J.t =
  `Assoc [
    "supportsConfigurationDoneRequest",      `Bool true
  ; "supportsTerminateRequest",              `Bool true
  ; "supportsSingleThreadExecutionRequests", `Bool true
  ; "supportsCancelRequest",                 `Bool false
  ; "supportsStepBack",                      `Bool true
  ; "supportsRestartFrame",                  `Bool true
  ; "supportsRestartRequest",                `Bool false
  ; "supportsExceptionInfoRequest",          `Bool false
  ; "supportsValueFormattingOptions",        `Bool false
  ]

(* --- Variable references --------------------------------------------

   We only emit references during a pause; they're invalidated on
   resume. Encoding:
     1            → "Goals" scope (top-level)
     100 + i      → hypotheses of [paused.snapshot.goals[i]]
   Anything else is treated as a leaf (no children).
*)

let goals_scope_ref      = 1
let unif_scope_ref       = 2
let goal_hyps_ref_base   = 100
let unif_hyps_ref_base   = 200

(* --- Breakpoint snapping -------------------------------------------- *)

(** Collect the 1-based start line of every tactic in [path], sorted
    ascending and deduplicated. Used by [setBreakpoints] to snap a
    user's requested line to the nearest real tactic — without that,
    a breakpoint on a comment or blank line silently never fires.

    Parsing only — no scoping, typing, or signature loading. Returns
    [[]] if the file fails to parse; the kernel will surface the same
    error at [launch] time, so we don't double-report it here. *)
let tactic_lines_in_file (path : string) : int list =
  let acc = ref [] in
  let visit_proof proof =
    let _ : unit =
      Parsing.Syntax.fold_proof
        (fun () tac _n_sub ->
          match tac.Common.Pos.pos with
          | Some p -> acc := p.start_line :: !acc
          | None -> ())
        ()
        proof
    in
    ()
  in
  let consume (cmd : Parsing.Syntax.p_command) =
    match cmd.elt with
    | P_symbol { p_sym_prf = Some (proof, _); _ } -> visit_proof proof
    | _ -> ()
  in
  (try Common.Debug.stream_iter consume (Parsing.Parser.parse_file path)
   with _ -> ());
  List.sort_uniq compare !acc

(** Given the (sorted asc) tactic-line list and a single requested
    breakpoint line, return the line we should actually pause on,
    or [None] if no tactic exists at or after [requested]. *)
let snap_one (tac_lines : int list) (requested : int) : int option =
  try Some (List.find (fun t -> t >= requested) tac_lines)
  with Not_found -> None

(* --- Helpers -------------------------------------------------------- *)

let kernel_thread_id = Pause.kernel_thread_id

let single_thread_body : J.t =
  `Assoc ["threads", `List [
    `Assoc [
      "id",   `Int kernel_thread_id
    ; "name", `String "checker"
    ]]]

let source_for (path : string) : J.t =
  `Assoc [
    "name", `String (Filename.basename path)
  ; "path", `String path
  ]

let stack_frame_of_pause (paused : State.paused_at) : J.t =
  let p = paused.pos in
  `Assoc [
    "id",     `Int 1
  ; "name",   `String paused.snapshot.proof_name
  ; "source", source_for p.fname
  ; "line",   `Int p.start_line
  ; "column", `Int (max 1 (p.start_col + 1))     (* DAP cols are 1-based. *)
  ; "endLine",   `Int p.end_line
  ; "endColumn", `Int (max 1 (p.end_col + 1))
  ; "presentationHint", `String "normal"
  ]

(** Partition a goal list into [(typ_goals, unif_goals)] preserving
    relative order — typing goals end up under the [Goals] scope,
    unification constraints under [Constraints]. *)
let split_goals (gs : Handle.Dap_hooks.goal_snapshot list)
  : Handle.Dap_hooks.goal_snapshot list * Handle.Dap_hooks.goal_snapshot list =
  List.partition (fun g -> g.Handle.Dap_hooks.goal_kind = `Typ) gs

let scopes_body (paused : State.paused_at) : J.t =
  let typs, unifs = split_goals paused.snapshot.goals in
  let scope name ref_ count =
    `Assoc [
      "name",               `String name
    ; "variablesReference", `Int ref_
    ; "namedVariables",     `Int count
    ; "expensive",          `Bool false
    ; "presentationHint",   `String "locals"
    ]
  in
  let scopes = [scope "Goals" goals_scope_ref (List.length typs)] in
  let scopes = if unifs = [] then scopes
               else scopes @ [scope "Constraints" unif_scope_ref (List.length unifs)]
  in
  `Assoc ["scopes", `List scopes]

let typ_variable (i : int) (g : Handle.Dap_hooks.goal_snapshot) : J.t =
  let ref_ =
    if g.goal_hyps = [] then 0
    else goal_hyps_ref_base + i
  in
  `Assoc [
    "name",               `String (Printf.sprintf "goal[%d]" i)
  ; "value",              `String g.goal_label
  ; "type",               `String "Typ"
  ; "variablesReference", `Int ref_
  ]

let unif_variable (i : int) (g : Handle.Dap_hooks.goal_snapshot) : J.t =
  let ref_ =
    if g.goal_hyps = [] then 0
    else unif_hyps_ref_base + i
  in
  `Assoc [
    "name",               `String (Printf.sprintf "constr[%d]" i)
  ; "value",              `String g.goal_label
  ; "type",               `String "Unif"
  ; "variablesReference", `Int ref_
  ]

let hyp_variable ((name, ty) : string * string) : J.t =
  `Assoc [
    "name",               `String name
  ; "value",              `String ty
  ; "variablesReference", `Int 0
  ]

let variables_body (paused : State.paused_at) (reference : int) : J.t =
  let typs, unifs = split_goals paused.snapshot.goals in
  let vars : J.t list =
    if reference = goals_scope_ref then
      List.mapi typ_variable typs
    else if reference = unif_scope_ref then
      List.mapi unif_variable unifs
    else if reference >= goal_hyps_ref_base
         && reference < goal_hyps_ref_base + List.length typs
    then List.map hyp_variable
           (List.nth typs (reference - goal_hyps_ref_base)).goal_hyps
    else if reference >= unif_hyps_ref_base
         && reference < unif_hyps_ref_base + List.length unifs
    then List.map hyp_variable
           (List.nth unifs (reference - unif_hyps_ref_base)).goal_hyps
    else []
  in
  `Assoc ["variables", `List vars]

(* --- Output redirection --------------------------------------------- *)

(** Build a [Format.formatter] that buffers writes and emits one DAP
    [output] event per flush. Used to redirect [Common.Error.err_fmt]
    and [Common.Console.out_fmt] so kernel debug traces / warnings /
    [print]-from-tactic output land in the editor's Debug Console
    instead of being silently written to the adapter's stderr. *)
let make_output_formatter ~(category : string) : Format.formatter =
  let buf = Buffer.create 256 in
  let out s pos len = Buffer.add_substring buf s pos len in
  let flush () =
    let s = Buffer.contents buf in
    Buffer.clear buf;
    if s <> "" then
      Io.send (Msg.event ~event:"output"
                 ~body:(`Assoc [
                   "category", `String category
                 ; "output",   `String s
                 ])
                 ())
  in
  Format.make_formatter out flush

(* --- Kernel thread -------------------------------------------------- *)

let kernel_thread (s : State.t) (path : string) : unit =
  let exit_code, term_msg =
    try
      Common.Console.reset_default ();
      (* Disable ANSI colors — escape sequences in the Debug Console
         render as garbage. *)
      Lplib.Color.color := false;
      Common.Error.err_fmt   := make_output_formatter ~category:"stderr";
      Common.Console.out_fmt := make_output_formatter ~category:"stdout";
      (* Apply [launch.debug] if requested. *)
      let dbg = State.with_lock s (fun () -> s.debug_flags) in
      if dbg <> "" then Common.Logger.set_debug true dbg;
      Pause.install s;
      let _sign = Handle.Compile.compile_file path in
      (0, None)
    with
    | Common.Error.Fatal (popt_opt, msg) ->
        let where =
          match popt_opt with
          | Some p -> Common.Pos.popt_to_string p
          | None -> "<no position>"
        in
        (1, Some (Printf.sprintf "%s: %s" where msg))
    | e ->
        (1, Some (Printf.sprintf "Uncaught: %s" (Printexc.to_string e)))
  in
  Handle.Dap_hooks.clear_callbacks ();
  State.with_lock s (fun () -> s.status <- State.Terminated;
    Condition.broadcast s.wakeup_cv);
  (match term_msg with
   | None -> ()
   | Some m ->
       Io.send
         (Msg.event ~event:"output"
            ~body:(`Assoc [
              "category", `String "stderr"
            ; "output",   `String (m ^ "\n")
            ])
            ()));
  Io.send (Msg.event ~event:"terminated" ~body:(`Assoc []) ());
  Io.send
    (Msg.event ~event:"exited"
       ~body:(`Assoc ["exitCode", `Int exit_code])
       ())

let spawn_kernel (s : State.t) (path : string) : unit =
  let _t = Thread.create (fun () -> kernel_thread s path) () in ()

(* --- Request dispatch ----------------------------------------------- *)

(** Reply with an error response. Generic; [message] is short
    machine-readable, [text] is human-readable. *)
let error_reply ~(seq : int) ~(command : string) ~(message : string)
    ?(text : string option) () : unit =
  let body = match text with
    | None -> None
    | Some t -> Some (`Assoc ["error", `Assoc [
                  "id",       `Int 1
                ; "format",   `String t
                ; "showUser", `Bool true
                ]])
  in
  Io.send
    (Msg.response ~request_seq:seq ~command ~success:false ~message
       ?body ())

(** [release_kernel s mode] must be called with [s.m] held. Sets
    [step_mode], flips status to [Running], and tells the kernel to
    [Resume]. *)
let release_kernel (s : State.t) (mode : State.step_mode) : unit =
  s.step_mode   <- mode;
  s.status      <- State.Running;
  s.next_action <- Some State.Resume;
  Condition.broadcast s.wakeup_cv

(** Push a [Rewind] action and wake the kernel. The kernel replays
    silently up to [target]; we set [step_mode = Step] so the
    *first* hook firing after replay pauses (not the next breakpoint).
    That matches the DAP intent: [stepBack]/[restartFrame] should
    leave the user paused exactly at the rewind target, regardless of
    where bps are set. *)
let request_rewind (s : State.t) ~(target : int) : unit =
  s.step_mode   <- State.Step;
  s.status      <- State.Running;
  s.next_action <- Some (State.Rewind target);
  Condition.broadcast s.wakeup_cv

let handle_request (s : State.t) (req : J.t) : bool =
  let seq     = Msg.field_int req "seq" in
  let command = Msg.field_string req "command" in
  let args    = match Msg.field req "arguments" with
    | Some a -> a
    | None -> `Null
  in
  match command with
  | "initialize" ->
      State.with_lock s (fun () ->
        match s.status with
        | Idle -> s.status <- State.Configuring
        | _ -> ());
      Io.send (Msg.response ~request_seq:seq ~command ~body:capabilities ());
      Io.send (Msg.event ~event:"initialized" ());
      true
  | "launch" ->
      let path = Msg.field_string args "program" in
      let stop_on_entry = Msg.field_bool ~default:true args "stopOnEntry" in
      let debug_flags = Msg.field_string args "debug" in
      if path = "" then begin
        error_reply ~seq ~command
          ~message:"missing 'program'"
          ~text:"launch requires { program: <path-to-.lp-file> }" ();
        true
      end else begin
        State.with_lock s (fun () ->
          s.launch_path   <- Some (State.normalise_path path);
          s.stop_on_entry <- stop_on_entry;
          s.debug_flags   <- debug_flags;
          s.step_mode     <- Continue);
        Io.send (Msg.response ~request_seq:seq ~command ());
        true
      end
  | "configurationDone" ->
      Io.send (Msg.response ~request_seq:seq ~command ());
      State.with_lock s (fun () -> s.status <- State.Running);
      (match s.launch_path with
       | None -> ()
       | Some p -> spawn_kernel s p);
      true
  | "setBreakpoints" ->
      let path =
        match Msg.field args "source" with
        | Some src -> Msg.field_string src "path"
        | None -> ""
      in
      let requested =
        match Msg.field args "breakpoints" with
        | Some (`List bps) ->
            List.map (fun bp -> Msg.field_int bp "line") bps
        | _ -> []
      in
      let tac_lines = tactic_lines_in_file path in
      let snapped = List.map (snap_one tac_lines) requested in
      let kernel_lines =
        List.filter_map (fun x -> x) snapped |> List.sort_uniq compare
      in
      State.set_breakpoints s ~path ~lines:kernel_lines;
      let verified =
        List.map2 (fun req snap ->
          match snap with
          | Some line ->
              `Assoc [
                "verified", `Bool true
              ; "line",     `Int line
              ]
          | None ->
              `Assoc [
                "verified", `Bool false
              ; "line",     `Int req
              ; "message",  `String "no tactic at or after this line"
              ])
          requested snapped
      in
      Io.send (Msg.response ~request_seq:seq ~command
                 ~body:(`Assoc ["breakpoints", `List verified]) ());
      true
  | "setExceptionBreakpoints" ->
      Io.send (Msg.response ~request_seq:seq ~command ());
      true
  | "threads" ->
      Io.send (Msg.response ~request_seq:seq ~command
                 ~body:single_thread_body ());
      true
  | "stackTrace" ->
      let frames =
        State.with_lock s (fun () ->
          match s.status with
          | Paused p -> [stack_frame_of_pause p]
          | _ -> [])
      in
      Io.send
        (Msg.response ~request_seq:seq ~command
           ~body:(`Assoc [
             "stackFrames", `List frames
           ; "totalFrames", `Int (List.length frames)
           ])
           ());
      true
  | "scopes" ->
      let body =
        State.with_lock s (fun () ->
          match s.status with
          | Paused p -> scopes_body p
          | _ -> `Assoc ["scopes", `List []])
      in
      Io.send (Msg.response ~request_seq:seq ~command ~body ());
      true
  | "variables" ->
      let reference = Msg.field_int args "variablesReference" in
      let body =
        State.with_lock s (fun () ->
          match s.status with
          | Paused p -> variables_body p reference
          | _ -> `Assoc ["variables", `List []])
      in
      Io.send (Msg.response ~request_seq:seq ~command ~body ());
      true
  | "continue" ->
      State.with_lock s (fun () -> release_kernel s Continue);
      Io.send (Msg.response ~request_seq:seq ~command
                 ~body:(`Assoc ["allThreadsContinued", `Bool true]) ());
      true
  | "next"
  | "stepIn" ->
      State.with_lock s (fun () -> release_kernel s Step);
      Io.send (Msg.response ~request_seq:seq ~command ());
      true
  | "stepOut" ->
      State.with_lock s (fun () -> release_kernel s Step_out);
      Io.send (Msg.response ~request_seq:seq ~command ());
      true
  | "pause" ->
      (* Cooperative: we don't preempt mid-tactic. Instead, set [Step]
         so the next [before_tactic] boundary halts. *)
      State.with_lock s (fun () ->
        match s.status with
        | Running -> s.step_mode <- State.Step
        | _ -> ());
      Io.send (Msg.response ~request_seq:seq ~command ());
      true
  | "evaluate" ->
      let expr = Msg.field_string args "expression" in
      let reply (out : State.eval_outcome) =
        let success, body =
          match out with
          | State.Eval_ok r ->
              true,
              `Assoc [
                "result",             `String r
              ; "variablesReference", `Int 0
              ]
          | State.Eval_err msg ->
              false,
              `Assoc [
                "result",             `String msg
              ; "variablesReference", `Int 0
              ]
        in
        Io.send (Msg.response ~request_seq:seq ~command ~success ~body ())
      in
      let queued =
        State.with_lock s (fun () ->
          match s.status with
          | Paused _ ->
              s.next_action <- Some (State.Eval (expr, reply));
              Condition.broadcast s.wakeup_cv;
              true
          | _ -> false)
      in
      if not queued then reply (State.Eval_err "evaluate: not paused");
      true
  | "stepBack" ->
      State.with_lock s (fun () ->
        match s.status with
        | Paused p -> request_rewind s ~target:(max 0 (p.index - 1))
        | _ -> ());
      Io.send (Msg.response ~request_seq:seq ~command ());
      true
  | "restartFrame" ->
      State.with_lock s (fun () ->
        match s.status with
        | Paused _ -> request_rewind s ~target:0
        | _ -> ());
      Io.send (Msg.response ~request_seq:seq ~command ());
      true
  | "terminate"
  | "disconnect" ->
      State.with_lock s (fun () ->
        s.status <- State.Terminated;
        s.next_action <- Some State.Resume;
        Condition.broadcast s.wakeup_cv);
      Io.send (Msg.response ~request_seq:seq ~command ());
      false  (* Stop the read loop. *)
  | other ->
      error_reply ~seq ~command
        ~message:"unsupportedCommand"
        ~text:(Printf.sprintf "DAP command %S is not supported" other) ();
      true

(* --- Entry point ---------------------------------------------------- *)

let main () : unit =
  let s = State.create () in
  let rec loop () =
    match Io.read_message () with
    | exception Io.Read_error msg ->
        Common.Console.out 0
          "[dap] read error: %s — closing session" msg
    | req ->
        if handle_request s req then loop ()
  in
  loop ()
