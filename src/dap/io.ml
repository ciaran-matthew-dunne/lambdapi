(** DAP wire-format I/O over stdio.

    DAP uses the same framing as LSP: an HTTP-like ["Content-Length:"]
    header line, a blank line, then a UTF-8 JSON body of the declared
    length. We can't reuse [Lsp.Lsp_io] because the DAP server is
    multi-threaded — the kernel thread emits [stopped]/[output] events
    while the main thread is mid-read on [stdin] for the next request.
    We need a writer mutex; LSP didn't.

    Reads come from [stdin] only (single thread — the main DAP loop).
    Writes come from any thread; [send] takes the writer mutex.

    We do not buffer reads through [Stdlib.in_channel] because the
    [Unix.read] path is what guarantees we don't read past the current
    message into an opaque buffer. *)

module J = Yojson.Safe

exception Read_error of string

(* --- Reader (single-threaded, called only from the main DAP loop) --- *)

let in_buf : Buffer.t = Buffer.create 4096

let drop_first n =
  let len = Buffer.length in_buf in
  if n >= len then Buffer.clear in_buf
  else begin
    let rest = Buffer.sub in_buf n (len - n) in
    Buffer.clear in_buf;
    Buffer.add_string in_buf rest
  end

let chunk = Bytes.create 4096

let read_more () =
  let n = Unix.read Unix.stdin chunk 0 (Bytes.length chunk) in
  if n = 0 then raise End_of_file;
  Buffer.add_subbytes in_buf chunk 0 n

let rec read_line_ub () : string =
  let s = Buffer.contents in_buf in
  match String.index_opt s '\n' with
  | Some i ->
      let raw = String.sub s 0 i in
      drop_first (i + 1);
      (* Strip trailing \r if present (CRLF terminator). *)
      let len = String.length raw in
      if len > 0 && raw.[len - 1] = '\r' then String.sub raw 0 (len - 1)
      else raw
  | None ->
      read_more (); read_line_ub ()

let rec read_exact n : string =
  if Buffer.length in_buf >= n then begin
    let s = Buffer.sub in_buf 0 n in
    drop_first n;
    s
  end else begin
    read_more (); read_exact n
  end

let read_message () : J.t =
  try
    (* Loop over header lines until we find Content-Length and the
       blank separator. DAP allows other headers (e.g.
       Content-Type), though no client sends them in practice. *)
    let size = ref None in
    let rec read_headers () =
      let line = read_line_ub () in
      if line = "" then ()
      else begin
        (try
           Scanf.sscanf line "Content-Length: %d" (fun n -> size := Some n)
         with _ -> ());
        read_headers ()
      end
    in
    read_headers ();
    match !size with
    | None -> raise (Read_error "missing Content-Length header")
    | Some n -> J.from_string (read_exact n)
  with
  | End_of_file -> raise (Read_error "EOF")
  | Scanf.Scan_failure msg
  | Failure msg
  | Invalid_argument msg -> raise (Read_error msg)

(* --- Writer (any thread) --- *)

let write_mutex = Mutex.create ()

let send (j : J.t) : unit =
  let body = J.to_string j in
  let header = Printf.sprintf "Content-Length: %d\r\n\r\n" (String.length body) in
  Mutex.lock write_mutex;
  (try
     output_string stdout header;
     output_string stdout body;
     flush stdout
   with e -> Mutex.unlock write_mutex; raise e);
  Mutex.unlock write_mutex
