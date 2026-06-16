(** Proof state. *)

open Lplib open Base
open Timed
open Core open Term
open Common open Pos
open Goal

(** Representation of the proof state of a theorem. *)
type proof_state =
  { proof_name  : strloc (** Name of the theorem. *)
  ; proof_term  : meta option
  (** Optional metavariable holding the goal associated to a symbol used as a
     theorem/definition and not just a simple declaration *)
  ; proof_goals : goal list (** Open goals (focused goal is first). *) }

(** [finished ps] tells whether there are unsolved goals in [ps]. *)
let finished : proof_state -> bool = fun ps -> ps.proof_goals = []

(** [goals ppf gl] prints the goal list [gl] to channel [ppf]. *)
let goals : proof_state pp = fun ppf ps ->
  match ps.proof_goals with
  | [] -> out ppf "No goal."
  | g::gs ->
      let idmap = Goal.get_names g in
      out ppf "%a0. %a" (Goal.hyps idmap) g (Goal.concl idmap) g;
      let goal ppf i g = out ppf "\n%d. %a" (i+1) Goal.pp_no_hyp g in
      List.iteri (goal ppf) gs

(** [goals_json ps] encodes the open goals of [ps] as JSON: a list of objects,
    each carrying its hypotheses (as name/type pairs) and its conclusion. This
    is the structured counterpart of {!val:goals}, for machine consumers (see
    {!module:Common.Json_out}). *)
let goals_json : proof_state -> Yojson.Basic.t = fun ps ->
  let info_json ((hyps, concl) : Goal.info) : Yojson.Basic.t =
    let hyp (n, t) : Yojson.Basic.t =
      (* [to_info] renders a hypothesis as ": T" (typed) or " ≔ D" (a local
         definition); drop the ": " so a typed [type] field is just [T]. *)
      let t =
        if String.length t >= 2 && t.[0] = ':' && t.[1] = ' '
        then String.sub t 2 (String.length t - 2) else t in
      `Assoc ["name", `String n; "type", `String t] in
    let hyps = `List (List.map hyp hyps) in
    match concl with
    | Typ (gid, typ) ->
        `Assoc ["meta", `String gid; "hyps", hyps; "concl", `String typ]
    | Unif constr ->
        `Assoc ["hyps", hyps; "constr", `String constr]
  in
  `List (List.map (fun g -> info_json (Goal.to_info g)) ps.proof_goals)

(** [remove_solved_goals ps] removes from the proof state [ps] the typing
   goals that are solved. *)
let remove_solved_goals : proof_state -> proof_state = fun ps ->
  let f = function
    | Typ gt -> !(gt.goal_meta.meta_value) = None
    | Unif _ -> true
  in {ps with proof_goals = List.filter f ps.proof_goals}

(** [meta_of_key ps i] returns [Some m] where [m] is a meta of [ps] whose key
   is [i], or else it returns [None]. *)
let meta_of_key : proof_state -> int -> meta option = fun ps key ->
  let f = function
    | Typ {goal_meta=m;_} when m.meta_key = key -> Some m
    | _ -> None
  in
  List.find_map f ps.proof_goals

(** [focus_env ps] returns the scoping environment of the focused goal or the
   empty environment if there is none. *)
let focus_env : proof_state option -> Env.t = fun ps ->
  match ps with
  | None -> Env.empty
  | Some(ps) ->
      match ps.proof_goals with
      | [] -> Env.empty
      | g::_ -> Goal.env g
