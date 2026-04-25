(** Hook points for the DAP server.

    The kernel calls into these hooks at the boundaries that matter for
    a debugger: the start and end of each proof, and before/after each
    tactic. By default every hook is a no-op, so a non-DAP run pays
    only an indirect call per tactic.

    The DAP library installs real callbacks via [set_callbacks] when
    the [lambdapi dap] subcommand starts. Keeping the hook registry
    inside the [handle] library lets us pass typed proof state
    ([proof_state], [Goal.info]) without making [handle] depend on
    [dap]. *)

open Common
open Pos

(** Position of a tactic, normalised to the fields a DAP source-mapped
    breakpoint cares about. ['fname] is the absolute path of the source
    file (or ["unknown"] when the kernel had no position to attribute);
    line numbers are 1-based, matching DAP's default. *)
type tactic_pos =
  { fname      : string
  ; start_line : int
  ; start_col  : int
  ; end_line   : int
  ; end_col    : int }

let tactic_pos_of_popt : popt -> tactic_pos = function
  | None ->
      { fname = "unknown"; start_line = 1; start_col = 0
      ; end_line = 1; end_col = 0 }
  | Some p ->
      let fname =
        match p.fname with
        | None -> "unknown"
        | Some f -> f
      in
      { fname
      ; start_line = p.start_line
      ; start_col  = p.start_col
      ; end_line   = p.end_line
      ; end_col    = p.end_col }

(** Snapshot of a proof state, pre-flattened to the strings the DAP
    server hands back to the editor in [variables] responses. We
    pre-flatten in the kernel so the DAP I/O thread never has to
    pretty-print a [term] (which uses kernel state and is not
    thread-safe). *)
type goal_snapshot =
  { goal_kind  : [`Typ | `Unif]
  ; goal_label : string  (** ["?42: Π x:ℕ, ..."] or ["lhs ≡ rhs"]. *)
  ; goal_hyps  : (string * string) list  (** [(name, type-or-defn)]. *)
  }

type proof_snapshot =
  { proof_name : string
  ; goals      : goal_snapshot list }

(** The four hook points called by the kernel. Each takes a single
    record so the signature can grow without churning every callsite.

    A [before_tactic] callback runs *before* the kernel calls the
    tactic handler — this is the natural pause point ("about to run
    [reflexivity]"). [after_tactic] fires whether the tactic succeeded
    or raised; [error] is [None] on success and [Some msg] on a fatal
    raised by the tactic. *)
type before_tactic_event =
  { bt_pos      : tactic_pos
  ; bt_state    : proof_snapshot
  ; bt_subgoals : int  (** Number of subproofs declared after this tac. *)
  ; bt_index    : int  (** 0-based index of this tactic in the proof. *)
  ; bt_ss       : Core.Sig_state.t
  ; bt_ps       : Proof.proof_state }

type after_tactic_event =
  { at_pos   : tactic_pos
  ; at_state : proof_snapshot
  ; at_error : string option }

type before_proof_event =
  { bp_name  : string
  ; bp_pos   : tactic_pos
  ; bp_state : proof_snapshot
  ; bp_ss    : Core.Sig_state.t
  ; bp_ps    : Proof.proof_state }

type after_proof_event =
  { ap_name : string
  ; ap_pos  : tactic_pos
  ; ap_open_goals : int  (** Non-zero when the proof was [admitted]. *) }

(** Raised by a hook callback to ask the kernel to rewind execution
    of the current proof to tactic index [k] (0-based). [k = 0] means
    rewind to the start of the proof; [k = n - 1] means re-pause at
    the previously-executed tactic. The caller side
    ([Command.handle]) catches this exception, restores
    [Timed.Time.save] to the proof's start, replays tactics 0..k-1
    silently, then resumes normal hook firing at tactic [k]. *)
exception Rewind_to of int

type callbacks =
  { before_proof  : before_proof_event  -> unit
  ; before_tactic : before_tactic_event -> unit
  ; after_tactic  : after_tactic_event  -> unit
  ; after_proof   : after_proof_event   -> unit }

let nop_callbacks : callbacks =
  { before_proof  = (fun _ -> ())
  ; before_tactic = (fun _ -> ())
  ; after_tactic  = (fun _ -> ())
  ; after_proof   = (fun _ -> ()) }

let installed : callbacks ref = ref nop_callbacks

let active : bool ref = ref false

let set_callbacks (cb : callbacks) : unit =
  installed := cb; active := true

let clear_callbacks () : unit =
  installed := nop_callbacks; active := false

let is_active () : bool = !active

let before_proof  (e : before_proof_event)  : unit = !installed.before_proof  e
let before_tactic (e : before_tactic_event) : unit = !installed.before_tactic e
let after_tactic  (e : after_tactic_event)  : unit = !installed.after_tactic  e
let after_proof   (e : after_proof_event)   : unit = !installed.after_proof   e

(** [Goal.to_info] formats a hypothesis's body as [": τ nat"] (or
    [" ≔ value"] when there's a let-binding). DAP renders variables as
    [name = value], so we want the value sans its leading separator —
    the [name] cell already implies the colon. Strip [": "] / [" ≔ "]
    and fall back to the raw text if neither prefix is present. *)
let trim_hyp_value (s : string) : string =
  let drop n =
    if String.length s >= n then String.sub s n (String.length s - n)
    else s
  in
  if String.length s >= 2 && String.sub s 0 2 = ": " then drop 2
  else if String.length s >= 4 && String.sub s 0 4 = " \xe2\x89\x94 " then
    (* Three bytes of UTF-8 ≔ (U+2254) plus the trailing space. *)
    drop 4
  else s

(** Build a [proof_snapshot] from a raw [Proof.proof_state]. Lives
    here (not in [Proof]) because it depends on [Goal.to_info], which
    already does the work of pretty-printing every hypothesis and
    goal target. *)
let snapshot_of_proof_state (ps : Proof.proof_state) : proof_snapshot =
  let trim_hyps = List.map (fun (n, v) -> n, trim_hyp_value v) in
  let one g =
    let hyps, body = Goal.to_info g in
    let hyps = trim_hyps hyps in
    match body with
    | Goal.Typ (name, ty) ->
        { goal_kind  = `Typ
        ; goal_label = Printf.sprintf "%s: %s" name ty
        ; goal_hyps  = hyps }
    | Goal.Unif s ->
        { goal_kind  = `Unif
        ; goal_label = s
        ; goal_hyps  = hyps }
  in
  { proof_name = ps.proof_name.elt
  ; goals      = List.map one ps.proof_goals }
