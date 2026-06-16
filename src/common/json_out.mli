(** Structured NDJSON output for machine consumers.

    When {!enabled} is [true], the CLI emits one newline-terminated JSON
    object per event to {!out_fmt} (stdout by default) in place of
    colored human-oriented text. Each record carries at least a [kind]
    (string) and a [ts] (ISO 8601 timestamp).

    Record kinds produced today: [file_start], [file_end], [diagnostic],
    [summary]. See [lambdapi check --help] and [doc/options.rst] for the
    schema reference. *)

(** Current schema version (semantic versioning). Bumped per the rules
    documented alongside {!schema_version} in the schema doc. *)
val schema_version : string

(** Global on/off switch. [Config.init] sets this from the [--json] CLI
    flag; diagnostic sites consult it to pick between text and JSON
    output paths. Using an [Stdlib.ref] avoids the [Timed] machinery,
    which is unnecessary for a CLI-startup-only flag. *)
val enabled : bool Stdlib.ref

(** Formatter receiving NDJSON records. Defaults to [Format.std_formatter];
    tests may swap it out to capture output. *)
val out_fmt : Format.formatter Stdlib.ref

type severity = [`Error | `Warning | `Info]

(** Extra JSON fields to attach to the NEXT {!val:diagnostic} emitted, then
    cleared. A site raising a rich diagnostic (e.g. a tactic failure under
    [--proof-state-on-error]) sets this just before raising, so its structured
    payload reaches the emitter even though the [Fatal] in flight is a bare
    string. Empty for ordinary errors and warnings. *)
val diagnostic_extra : (string * Yojson.Basic.t) list Stdlib.ref

(** [diagnostic ~severity pos msg] emits a [diagnostic] record. The [file] and
    [range] fields appear when [pos] carries them, and any fields staged in
    {!val:diagnostic_extra} are appended (and the stage cleared). *)
val diagnostic : severity:severity -> Pos.popt -> string -> unit

(** [file_start ~file] emits a [file_start] record (call just before
    beginning to check [file]). *)
val file_start : file:string -> unit

(** [file_end ~file ~status ~elapsed_ms] emits a [file_end] record.
    [status] is [`Ok] when the file checked without error, else
    [`Error]. *)
val file_end :
  file:string -> status:[`Ok | `Error] -> elapsed_ms:int -> unit

(** [summary ~files_checked ~files_ok ~files_failed ~elapsed_ms] emits
    the terminal summary of a batch invocation. *)
val summary :
  files_checked:int -> files_ok:int -> files_failed:int ->
  elapsed_ms:int -> unit
