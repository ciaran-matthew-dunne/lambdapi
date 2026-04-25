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
  ; bt_subgoals : int  (** Number of subproofs declared after this tac. *) }

type after_tactic_event =
  { at_pos   : tactic_pos
  ; at_state : proof_snapshot
  ; at_error : string option }

type before_proof_event =
  { bp_name  : string
  ; bp_pos   : tactic_pos
  ; bp_state : proof_snapshot }

type after_proof_event =
  { ap_name : string
  ; ap_pos  : tactic_pos
  ; ap_open_goals : int  (** Non-zero when the proof was [admitted]. *) }

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

(** Build a [proof_snapshot] from a raw [Proof.proof_state]. Lives
    here (not in [Proof]) because it depends on [Goal.to_info], which
    already does the work of pretty-printing every hypothesis and
    goal target. *)
let snapshot_of_proof_state (ps : Proof.proof_state) : proof_snapshot =
  let one g =
    let hyps, body = Goal.to_info g in
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
