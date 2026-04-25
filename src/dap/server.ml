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
  ; "supportsStepBack",                      `Bool false
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
let goal_hyps_ref_base   = 100

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

let scopes_body (paused : State.paused_at) : J.t =
  let n = List.length paused.snapshot.goals in
  `Assoc ["scopes", `List [
    `Assoc [
      "name",               `String "Goals"
    ; "variablesReference", `Int goals_scope_ref
    ; "namedVariables",     `Int n
    ; "expensive",           `Bool false
    ; "presentationHint",   `String "locals"
    ]]]

let goal_variable (i : int) (g : Handle.Dap_hooks.goal_snapshot) : J.t =
  let ref_ =
    if g.goal_hyps = [] then 0
    else goal_hyps_ref_base + i
  in
  let kind = match g.goal_kind with `Typ -> "Typ" | `Unif -> "Unif" in
  `Assoc [
    "name",               `String (Printf.sprintf "goal[%d]" i)
  ; "value",              `String g.goal_label
  ; "type",               `String kind
  ; "variablesReference", `Int ref_
  ]

let hyp_variable ((name, ty) : string * string) : J.t =
  `Assoc [
    "name",               `String name
  ; "value",              `String ty
  ; "variablesReference", `Int 0
  ]

let variables_body (paused : State.paused_at) (reference : int) : J.t =
  let vars : J.t list =
    if reference = goals_scope_ref then
      List.mapi goal_variable paused.snapshot.goals
    else if reference >= goal_hyps_ref_base
         && reference < goal_hyps_ref_base + List.length paused.snapshot.goals
    then
      let i = reference - goal_hyps_ref_base in
      let g = List.nth paused.snapshot.goals i in
      List.map hyp_variable g.goal_hyps
    else []
  in
  `Assoc ["variables", `List vars]

(* --- Kernel thread -------------------------------------------------- *)

let kernel_thread (s : State.t) (path : string) : unit =
  let exit_code, term_msg =
    try
      Common.Console.reset_default ();
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
    Condition.broadcast s.run_cv);
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

(** [release_kernel s mode] must be called with [s.m] held. Switches
    [step_mode], flips status to [Running], and broadcasts. *)
let release_kernel (s : State.t) (mode : State.step_mode) : unit =
  s.step_mode <- mode;
  s.status <- State.Running;
  Condition.broadcast s.run_cv

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
      if path = "" then begin
        error_reply ~seq ~command
          ~message:"missing 'program'"
          ~text:"launch requires { program: <path-to-.lp-file> }" ();
        true
      end else begin
        State.with_lock s (fun () ->
          s.launch_path   <- Some (State.normalise_path path);
          s.stop_on_entry <- stop_on_entry;
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
      let bp_lines =
        match Msg.field args "breakpoints" with
        | Some (`List bps) ->
            List.map (fun bp -> Msg.field_int bp "line") bps
        | _ -> []
      in
      State.set_breakpoints s ~path ~lines:bp_lines;
      let verified =
        List.map (fun line ->
          `Assoc [
            "verified", `Bool true
          ; "line",     `Int line
          ]) bp_lines
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
  | "terminate"
  | "disconnect" ->
      State.with_lock s (fun () ->
        s.status <- State.Terminated;
        Condition.broadcast s.run_cv);
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
