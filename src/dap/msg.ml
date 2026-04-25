(** Helpers for building DAP responses and events.

    We don't model every DAP request as a typed variant — the surface
    is large and most fields pass through opaquely. Instead, requests
    arrive as raw JSON ([Yojson.Safe.t]); the server pattern-matches
    on the [command] field and constructs replies via the helpers
    below.

    DAP shape, as a reminder:
      Request : { seq, type:"request", command, arguments? }
      Response: { seq, type:"response", request_seq, success, command,
                  message?, body? }
      Event   : { seq, type:"event", event, body? } *)

module J = Yojson.Safe

(** Monotonic [seq] used for outbound messages (responses & events).
    DAP requires this to be unique within the session. *)
let next_seq : int ref = ref 0

let alloc_seq () : int =
  incr next_seq; !next_seq

let response
    ~(request_seq : int) ~(command : string) ?(success = true)
    ?(message : string option) ?(body : J.t option) () : J.t =
  let base : (string * J.t) list =
    [ "seq",         `Int (alloc_seq ())
    ; "type",        `String "response"
    ; "request_seq", `Int request_seq
    ; "success",     `Bool success
    ; "command",     `String command ]
  in
  let base = match message with
    | None -> base
    | Some m -> base @ ["message", `String m]
  in
  let base = match body with
    | None -> base
    | Some b -> base @ ["body", b]
  in
  `Assoc base

let event ~(event : string) ?(body : J.t option) () : J.t =
  let base : (string * J.t) list =
    [ "seq",   `Int (alloc_seq ())
    ; "type",  `String "event"
    ; "event", `String event ]
  in
  let base = match body with
    | None -> base
    | Some b -> base @ ["body", b]
  in
  `Assoc base

(** Field accessors with sensible defaults. *)
let field (j : J.t) (k : string) : J.t option =
  match j with
  | `Assoc xs -> List.assoc_opt k xs
  | _ -> None

let field_string ?(default = "") (j : J.t) (k : string) : string =
  match field j k with
  | Some (`String s) -> s
  | _ -> default

let field_int ?(default = 0) (j : J.t) (k : string) : int =
  match field j k with
  | Some (`Int n) -> n
  | _ -> default

let field_bool ?(default = false) (j : J.t) (k : string) : bool =
  match field j k with
  | Some (`Bool b) -> b
  | _ -> default
