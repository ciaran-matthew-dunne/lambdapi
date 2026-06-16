(** Structured NDJSON output for machine consumers. See [json_out.mli]. *)

module J = Yojson.Basic

let schema_version = "1.0.0"

let enabled : bool Stdlib.ref = Stdlib.ref false

let out_fmt : Format.formatter Stdlib.ref = Stdlib.ref Format.std_formatter

(* ISO 8601 UTC timestamp with millisecond resolution (e.g.
   "2026-04-22T12:34:56.789Z"). *)
let iso_timestamp () =
  let t = Unix.gettimeofday () in
  let tm = Unix.gmtime t in
  let ms = int_of_float ((t -. floor t) *. 1000.) in
  Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02d.%03dZ"
    (tm.Unix.tm_year + 1900) (tm.Unix.tm_mon + 1) tm.Unix.tm_mday
    tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec ms

let emit ~kind (fields : (string * J.t) list) =
  let record =
    `Assoc (("kind", `String kind)
            :: ("ts", `String (iso_timestamp ()))
            :: fields)
  in
  Format.fprintf Stdlib.(!out_fmt) "%s@\n%!" (J.to_string record)

type severity = [`Error | `Warning | `Info]

let string_of_severity = function
  | `Error   -> "error"
  | `Warning -> "warning"
  | `Info    -> "info"

(* LSP-style range object. Lines are 1-indexed and columns are 0-indexed
   UTF-8 codepoints — the convention [Pos.to_string] already uses, so
   the JSON record agrees with the "file:line:col" banners consumers see
   in text mode. Note: the LSP server shifts lines to 0-indexed to
   satisfy the LSP spec; this output targets CLI consumers, not LSP
   clients, so we keep the CLI's 1-indexed convention. *)
let range_of_pos (p : Pos.pos) : J.t =
  `Assoc [
    "start", `Assoc ["line", `Int p.Pos.start_line;
                     "col",  `Int p.Pos.start_col];
    "end",   `Assoc ["line", `Int p.Pos.end_line;
                     "col",  `Int p.Pos.end_col];
  ]

let diagnostic ~severity (pos : Pos.popt) (message : string) =
  let base = [
    "severity", `String (string_of_severity severity);
    "message",  `String message;
  ] in
  let fields =
    match pos with
    | None -> base
    | Some p ->
      let file = match p.Pos.fname with
        | None   -> []
        | Some f -> ["file", `String f]
      in
      file @ ("range", range_of_pos p) :: base
  in
  emit ~kind:"diagnostic" fields

let file_start ~file =
  emit ~kind:"file_start" ["file", `String file]

let file_end ~file ~status ~elapsed_ms =
  let s = match status with `Ok -> "ok" | `Error -> "error" in
  emit ~kind:"file_end" [
    "file",       `String file;
    "status",     `String s;
    "elapsed_ms", `Int elapsed_ms;
  ]

let summary ~files_checked ~files_ok ~files_failed ~elapsed_ms =
  emit ~kind:"summary" [
    "schema_version", `String schema_version;
    "files_checked",  `Int files_checked;
    "files_ok",       `Int files_ok;
    "files_failed",   `Int files_failed;
    "elapsed_ms",     `Int elapsed_ms;
  ]
