open Terms
open Extra

(** Type of the leaves of the tree.  See {!file:terms.ml}, {!recfield:rhs}. *)
type action = (term_env, term) Bindlib.mbinder

(** Tree type.  {!const:Leaf}[(t, a)] are the leaves of the tree holding the
    targets of the rewriting as an {!type:action}; for [t], see
    {!recfield:switch} of {!type:node_data}.  The term option evinces--if the
    leaf has been obtained by a switch--the term that has been matched before
    reaching the leaf.  The {!const:Node}[n] constructor allows primarily to
    perform a switch among subtrees recorded in {!recfield:children} of [n].
    {!const:Fail} is a matching failure. *)
type t = Leaf of term option * action
       | Node of node_data
       | Fail

(** Data contained in a node of the tree.  {!recfield:switch} contains the
    term on which the switch that gave birth to this node has been performed
    (or none if the node has been obtained by a default matrix);
    {!recfield:swap} indicates whether the columns of the matrix have been
    swapped before the switch, with an int indicating the column which has
    been swapped with the first one (or None if no swap is performed) and
    {!recfield:children} contains the subtrees. *)
and node_data = { switch : term option
                ; swap : int option
                ; children : t list}

(** [iter l n f t] is a generic iterator on trees; with function [l] performed
    on leaves, function [n] performed on nodes, [f] returned in case of
    {!const:Fail} on tree [t]. *)
let iter : (term option -> action -> 'a) ->
  (term option -> int option -> t list -> 'a) ->
  'a -> t -> 'a = fun do_leaf do_node fail t ->
  let rec loop = function
    | Leaf(teo, a)                                   -> do_leaf teo a
    | Fail                                           -> fail
    | Node({ switch = s ; swap = p ; children = c }) ->
      do_node s p (List.map loop c) in
  loop t

(** [to_dot f t] creates a dot graphviz file [f].gv for tree [t].  Each node
    of the tree embodies a pattern matrix.  The label on the node is the
    column index in the matrix on which the matching is performed to give
    birth to children nodes.  The label on the edge between a node and its
    child represents the term matched to generate the next pattern matrix (the
    one of the child node); and is therefore one of the terms in the column of
    the pattern matrix whose index is the label of the node. *)
let to_dot : string -> t -> unit = fun fname tree ->
  let module F = Format in
  let module P = Print in
  let ochan = open_out (fname ^ ".gv") in
  let ppf = F.formatter_of_out_channel ochan in
  let nodecount = ref 0 in
  F.fprintf ppf "graph {@[<v>" ;
  let pp_opterm : term option pp = fun oc teo -> match teo with
    | Some(t) -> P.pp oc t
    | None    -> F.fprintf oc "d" in
  let rec write_tree : int -> t -> unit = fun father_l tree ->
  (* We cannot use iter since we need the father to be passed. *)
    match tree with
    | Leaf(t, a)  ->
      incr nodecount ;
      F.fprintf ppf "@ %d [label=\"" !nodecount ;
      let _, acte = Bindlib.unmbind a in
      P.pp ppf acte ; F.fprintf ppf "\"]" ;
      F.fprintf ppf "@ %d -- %d [label=\"" father_l !nodecount ;
      pp_opterm ppf t ; F.fprintf ppf "\"];"
    | Node(ndata) ->
      let { switch = t ; swap = swa ; children = c } = ndata in
      incr nodecount ;
      let tag = !nodecount in
      F.fprintf ppf "@ %d [label=\"" tag ;
      F.fprintf ppf "%d" (match swa with None -> 0 | Some(i) -> i) ;
      F.fprintf ppf "\"]" ;
      F.fprintf ppf "@ %d -- %d [label=\"" father_l tag ;
      pp_opterm ppf t ; F.fprintf ppf "\"];" ;
      List.iter (fun e -> write_tree tag e) c ;
    | Fail        ->
      incr nodecount ;
      F.fprintf ppf "@ %d -- %d [label=\"%s\"];" father_l !nodecount "f"
  in
  write_tree 0 tree ;
  F.fprintf ppf "@.}@\n@?" ;
  close_out ochan

(** Pattern matrices is a way to encode a pattern matching problem.  A line is
    a candidate instance of the values matched.  Each line is a pattern having
    an action attached.  This module provides functions to operate on these
    matrices. *)
module Pattmat =
struct
  (** Type used to describe a line of a matrix (either a column or a row). *)
  type line = term list

  (** Mainly for debugging purposes, shows where the matrix comes from,
      i.e. generated by a specialization, a default case or the initial
      matrix *)
  type operation = Init
                 | Default
                 | Specialized of term

  (** The core data, contains the rewrite rules. *)
  type matrix = (line * action) list

  (** Type of a matrix of patterns.  Each line is a row having an attached
      action. *)
  type t = { origin : operation
           ; values : matrix }

  (** [pp_line o l] prints line [l] to out channel [o]. *)
  let pp_line : line pp = List.pp Print.pp ";"

  (** [pp o m] prints matrix [m] to out channel [o]. *)
  let pp : t pp = fun oc { values = va ; _ } ->
    let module F = Format in
    F.fprintf oc "[|@[<v>@," ;
    List.pp pp_line "\n  " oc (List.map (fun (l, _) -> l) va) ;
    (* List.pp does not process Format "@" directives when in sep *)
    F.fprintf oc "@.|]@,@?"

  (** [of_rules r] creates the initial pattern matrix from a list of rewriting
      rules. *)
  let of_rules : rule list -> t = fun rs ->
    { values = List.map (fun r -> r.lhs, r.rhs) rs
    ; origin = Init }

  (** [is_empty m] returns whether matrix [m] is empty. *)
  let is_empty : t -> bool = fun m -> List.length m.values = 0

  (** [get_col n m] retrieves column [n] of matrix [m].  There is some
      processing because all rows do not have the same length. *)
  let get_col : int -> t -> line = fun ind { values = valu ; _ } ->
    let opcol = List.fold_left (fun acc (li, _) ->
        List.nth_opt li ind :: acc) []
        valu in
    let rem = List.filter (function None -> false | Some(_) -> true) opcol in
    List.map (function Some(e) -> e | None -> assert false) rem

  (** [select m i] keeps the columns of [m] whose index are in [i]. *)
  let select : t -> int array -> t = fun m indexes ->
    { values = List.map (fun (l, a) ->
          (Array.fold_left (fun acc i -> List.nth l i :: acc) [] indexes),
          a) m.values
    ; origin = m.origin }

  (** [swap p i] swaps the first column with the [i]th one. *)
  let swap : t -> int -> t = fun pm c ->
    { pm with values = List.map (fun (l, a) -> (List.swapf l c, a)) pm.values }

  (** [cmp c d] compares columns [c] and [d] returning:  +1 if c > d, 0 if c =
      d or -1 if c < d; where <, = and > are defined according to a heuristic.
  *)
  let cmp : line -> line -> int = fun _ _ -> 0

  (** [pick_best m] returns the index of the best column of matrix [m]
      according to a heuristic. *)
  let pick_best : t -> int = fun _ -> 0

  (** [is_pattern_free l] returns whether a line contains patterns or not.
      Typically, a line full of wildcards is pattern free. *)
  let rec is_pattern_free : line -> bool = function
    | []      -> true
    | x :: xs ->
      begin
        match x with
        (* Wildcards as Patt(None, _, _). *)
        | Patt(None, _, [| |]) -> is_pattern_free xs
        (* The condition might be too restrictive. *)
        | _                   -> false
      end

  (** [discard_patt_free m] returns the list of indexes of columns containing
      terms that can be matched against (discard pattern-free columns). *)
  let discard_patt_free : t -> int array = fun m ->
    let ncols = List.fold_left (fun acc (l, _) ->
        let le = List.length l in
      if le > acc then le else acc) 0 m.values in
    let pattfree = List.init ncols (fun k ->
        let col = get_col k m in
        is_pattern_free col) in
    let indexes = List.mapi (fun k pf ->
        if pf then None else Some k) pattfree in
    let remaining = List.filter (function
        | None    -> false
        | Some(_) -> true) indexes in
    let unpacked = List.map (function
        | Some(k) -> k
        | None    -> assert false) remaining in
    assert ((List.length unpacked) > 0) ;
    Array.of_list unpacked
end

(** [specialize p m]  specializes the matrix [m] when matching against pattern
    [p].  A matrix can be specialized by a user defined symbol, an abstraction
    or a pattern variable.  The specialization always happen on the first
    column (which is swapped if needed). *)
let specialize : term -> Pattmat.t -> Pattmat.t = fun p m ->
  let up = unfold p in
  let filtered = List.filter (fun (l, _) ->
      (* Removed rules starting with a different constructor*)
      match up, unfold (List.hd l) with
      | Symb(s, _)          , Symb(s', _)          -> s == s'
      | Patt (Some _, _, e1), Patt (Some _, _, e2) ->
        Array.length e1 = Array.length e2 (* Arity verification *)
      (* A check should be done regarding non linear variables *)
      | Patt(None, _, [| |]), Patt(None, _, [| |]) -> true
      | Abst(_, b1)         , Abst(_, b2)          ->
        let _, _, _ = Bindlib.unbind2 b1 b2 in
        true
      (* We should check that bodies depend on the same variables. *)
      | Appl(_, _)          , Appl(_, _)           -> true
      (* All below ought to be put in catch-all case*)
      | Symb(_, _)   , Appl(_, _)    -> false
      | Patt(_, _, _), Symb(_, _)    -> false
      | Patt(_, _, _), Appl(_, _)    -> false
      | Symb(_, _)   , Patt(_, _, _) -> false
      | Appl(_, _)   , Symb(_, _)    -> false
      | Appl(_, _)   , Patt(_, _, _) -> false
      | x            , y             ->
        Buffer.clear Format.stdbuf ; Print.pp Format.str_formatter x ;
        Print.pp Format.str_formatter y ;
        let msg = Printf.sprintf "%s: suspicious specialization-filtering"
            (Buffer.contents Format.stdbuf) in
        failwith msg) m.values in
  let unfolded = List.map (fun (l, a) ->
      match up, unfold (List.hd l) with
      | _                   , Symb(_, _)                 ->
        (List.tl l, a) (* Eat the symbol? *)
      (* Checks could be done on arity of symb. *)
      | _                   , Abst(_, b)                 ->
        let _, t = Bindlib.unbind b in (t :: List.tl l, a)
      | _                   , Appl(t1, t2)               ->
        (t1 :: t2 :: List.tl l, a)
        (* Might need to add wildcard to other lines. *)
      | Patt(Some(_), _, e1)   , Patt(None, _, _) ->
        let ari = Array.length e1 in
        (List.init ari (fun _ -> Patt(None, "w", [| |])) @ (List.tl l), a)
      | _                   , Patt(Some(_), _, _)        ->
        (List.tl l, a)
      | _                   , x                          ->
        Buffer.clear Format.stdbuf ; Print.pp Format.str_formatter x ;
        let msg = Printf.sprintf "%s: suspicious specialization unfold"
            (Buffer.contents Format.stdbuf) in
        failwith msg) filtered in
  { origin = Specialized(up)
  ; values = unfolded }

(** [default m] computes the default matrix containing what remains to be
    matched if no specialization occurred. *)
let default : Pattmat.t -> Pattmat.t =
  fun { origin = _ ; values = m } ->
  let filtered = List.filter (fun (l, _) ->
      match List.hd l with
      | Patt(None , _, _)                                          -> true
      | Symb(_, _) | Abst(_, _) | Patt(Some(_), _, _) | Appl(_, _) -> false
      | x                                                          ->
        Print.pp Format.err_formatter x ;
        assert false) m in
  let unfolded = List.map (fun (l, a) ->
      match List.hd l with
      | Patt(None, _, _) -> (List.tl l, a)
      (* | Appl(t1, t2)     -> (t1 :: t2 :: List.tl l, a) *)
      | _                -> assert false) filtered in
  { origin = Default
  ; values = unfolded }

(** [compile m] returns the decision tree allowing to parse efficiently the
    pattern matching problem contained in pattern matrix [m]. *)
let compile : Pattmat.t -> t = fun patterns ->
  let module Pm = Pattmat in
  let rec grow : Pm.t -> t = fun pm ->
    let { Pm.origin = o ; Pm.values = m } = pm in
    (* Pm.pp Format.std_formatter pm ; *)
    if Pm.is_empty pm then
      begin
        failwith "matching failure" ; (* For debugging purposes *)
        (* Dtree.Fail *)
      end
    else
      (* Look at the first line, if it contains only wildcards, then
         execute the associated action. *)
      (* Might be relevant to abstract the following operations in module
         dtree.ml. *)
      let swi = match o with
        | Init | Default -> None
        | Specialized(t) -> Some t in
      let fline = fst @@ List.hd m in
      if Pm.is_pattern_free fline then
        Leaf(swi, snd @@ List.hd m)
      else
        (* Pick a column in the matrix and pattern match on the constructors in
           it to grow the tree. *)
        let kept_cols = Pm.discard_patt_free pm in
        let sel_in_partial = Pm.pick_best (Pm.select pm kept_cols) in
        let swap = if kept_cols.(sel_in_partial) = 0 then None
          else Some kept_cols.(sel_in_partial) in
        let spm = match swap with
          | None    -> pm
          | Some(i) -> Pm.swap pm i in
        let fcol = Pm.get_col 0 spm in
        let cons = List.filter (fun x -> match x with
            | Symb(_, _) | Abst(_, _) | Patt(Some(_), _, _)-> true
            | Appl(_, _) -> true
            | _                                            -> false)
            fcol in
        let spepatts = List.map (fun s -> specialize s spm) cons in
        let defpatts = default spm in
        let children =
          List.map grow (if Pm.is_empty defpatts
                         then spepatts
                         else spepatts @ [defpatts]) in
        Node({ switch = swi ; swap = swap ; children = children }) in
  grow patterns
