open Core

let c0 = ['.']
let err s = failwith s
let flag_keep_rnode = false
let flag_build_parse_tree = false

(* NOTE - restore the following for release *)
(* let debug s =
   assert (
     print_endline (Printf.sprintf "▶%s◀" s);
     flag_debug) *)

let readFile filename =
  let chan = Stdio.In_channel.create filename in
  let lines = ref [] in
  let _ =
    try
      while true do
        let () = print_endline "one line" in
        lines := Stdio.In_channel.input_line chan :: !lines
      done
    with End_of_file -> Stdio.In_channel.close chan
  in
  let () = print_endline "file read" in
  List.rev !lines

let readTokens filename =
  (* return: values, w *)
  let lines = In_channel.read_lines filename in
  let f0 i _ = i % 2 = 0 in
  let f1 i _ = i % 2 = 1 in
  (List.filteri lines ~f:f0, List.filteri lines ~f:f1)

let hd l = match l with [] -> None | m :: _ -> Some m
let tl l = match l with [] -> [] | _ :: l -> l
let hdi l = match l with [] -> 0 | i :: _ -> i
let last l = List.hd_exn (List.rev l)

module Cmp (T : sig
  type t

  val compare : t -> t -> int
  val sexp_of_t : t -> Ppx_sexp_conv_lib.Sexp.t
  val equal : t -> t -> bool
  val show : t -> string
  val pp : Format.formatter -> t -> unit
end) =
struct
  include T
  include Comparator.Make (T)
end

let break st =
  match st with [] -> err "empty stack" | top :: tail -> (top, tail)