(** Shared session state.

    Two threads access this state — the main I/O thread (services DAP
    requests, sends events) and the kernel thread (runs
    [Compile.compile_file], fires [Dap_hooks] callbacks). All access
    goes through [with_lock]. We never call into kernel code while
    holding [m]: locks are short and only protect mutable fields here.

    The DAP-side variable / stackTrace requests are answered by
    snapshotting [paused] under the lock — these requests can arrive
    while the kernel is paused, so the kernel-side [Dap_hooks]
    callback that *put us in [`Paused]* is the canonical writer of
    [paused.snapshot]. While paused, the kernel is blocked on
    [run_cv]; once a [continue]/[next]/[stepOut] request fires
    [run_cv], the kernel resumes and clears [paused] on its next pause
    point. *)

module H = Handle.Dap_hooks

type step_mode =
  | Continue            (** Run until the next breakpoint / proof end. *)
  | Step                (** Pause at the next [before_tactic] boundary. *)
  | Step_out            (** Pause at the [after_proof] boundary. *)

(** A request from the I/O thread to the kernel thread. The kernel
    consumes one of these on each wake-up while paused.

    - [Resume]: leave [Paused], let [pause_kernel] return.
    - [Eval (expr, reply)]: parse [expr] as a query, run it against the
      live [ss]/[ps], hand the result back via [reply], remain paused.
    - [Rewind k]: raise [Dap_hooks.Rewind_to k] from the pause site so
      the kernel's [Command.handle] catches it and replays the proof
      from index 0 up to [k]. *)
type kernel_action =
  | Resume
  | Eval of string * (eval_outcome -> unit)
  | Rewind of int

and eval_outcome =
  | Eval_ok of string
  | Eval_err of string

type status =
  | Idle                (** Adapter started, no [launch] yet. *)
  | Configuring         (** [initialize] received, awaiting [configurationDone]. *)
  | Running             (** Kernel thread is running. *)
  | Paused of paused_at (** Kernel is blocked at a hook boundary. *)
  | Terminated          (** Kernel finished or errored out. *)

and paused_at =
  { reason   : string                      (** [entry|step|breakpoint|exception]. *)
  ; pos      : H.tactic_pos
  ; snapshot : H.proof_snapshot
  ; error    : string option
  ; index    : int      (** Tactic index at the pause site (-1 = before_proof). *)
  ; live_ss  : Core.Sig_state.t option     (** Available outside [before_proof]. *)
  ; live_ps  : Handle.Proof.proof_state option }

(** Per-source-file breakpoint set: 1-based line numbers. *)
type breakpoints = (string, int list) Hashtbl.t

type t =
  { mutable status        : status
  ; mutable step_mode     : step_mode
  ; mutable breakpoints   : breakpoints
  ; mutable launch_path   : string option
  ; mutable stop_on_entry : bool
  ; mutable debug_flags   : string
        (** Logger flags requested via [launch.debug] (e.g. ["iut"]). *)
  ; mutable next_action   : kernel_action option
        (** Set by main thread, drained by kernel on each [wakeup_cv] wake. *)
  ; m           : Mutex.t
  ; wakeup_cv   : Condition.t
        (** Kernel waits on this when paused; main signals it for both
            control (continue/next/...) and request (eval/rewind). *)
  }

let create () : t =
  { status        = Idle
  ; step_mode     = Continue
  ; breakpoints   = Hashtbl.create 8
  ; launch_path   = None
  ; stop_on_entry = true
  ; debug_flags   = ""
  ; next_action   = None
  ; m             = Mutex.create ()
  ; wakeup_cv     = Condition.create () }

let with_lock (s : t) (f : unit -> 'a) : 'a =
  Mutex.lock s.m;
  match f () with
  | r -> Mutex.unlock s.m; r
  | exception e -> Mutex.unlock s.m; raise e

(** Realpath-equivalent: collapses ["./"] / ["//"] / [".."] components
    using Unix when available, but tolerates non-existent paths (DAP
    clients sometimes set breakpoints before [launch]). *)
let normalise_path (p : string) : string =
  if p = "" then p
  else
    let p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p
            else p in
    try Unix.realpath p
    with Unix.Unix_error _ -> p

let set_breakpoints (s : t) ~(path : string) ~(lines : int list) : unit =
  with_lock s (fun () ->
    Hashtbl.replace s.breakpoints (normalise_path path) lines)

let has_breakpoint (s : t) ~(path : string) ~(line : int) : bool =
  with_lock s (fun () ->
    match Hashtbl.find_opt s.breakpoints (normalise_path path) with
    | None -> false
    | Some lines -> List.mem line lines)
