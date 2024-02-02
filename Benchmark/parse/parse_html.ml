(* NOTE - Parse html files *)

open TCFGParser.Utils
open Core
open Printf
open TCFGParser.CoqVPG

open TCFGParser.Unmarshall.Unmarshall (struct
  include Tree_action_html

  let path = "dict_html/"
  let grammar_name = "HTML"
end)

let flag_debug = false

let debug s = if flag_debug then print_endline (Printf.sprintf "▶%s◀" s) else ()

(* NOTE - cmd arguments *)
let usage_msg = "Parse HTML files."
let do_lex = ref false
let do_parse = ref false
let do_extract = ref false
let do_tree = ref false
let do_print = ref false
let input_file = ref ""
let output_file = ref ""
let anon_fun filename = input_file := filename

let speclist =
  [
    ("-lex", Arg.Set do_lex, "Only do lexing.");
    ("-parse", Arg.Set do_parse, "Do lexing and parsing.");
    ("-extract", Arg.Set do_extract, "Do lexing, parsing and extraction.");
    ( "-tree",
      Arg.Set do_tree,
      "Do lexing, parsing, extraction and build the parse tree." );
    ("-print-tree", Arg.Set do_print, "Print the parse tree.");
  ]

let () = Arg.parse speclist anon_fun usage_msg


let text, tokens = readTokens !input_file
let w = text

(* NOTE - leaves should be given by the lexer *)
let leaves = Tree_action_html.restore_leaves w tokens |> List.to_array

(* NOTE - h should be given by the lexer *)
let h =
  tokens
  |> List.map ~f:(fun x ->
         match x with
         | "TAG_OPEN_h1" -> lookup_sym (call x)
         | "TAG_OPEN_h2" -> lookup_sym (call x)
         | "TAG_OPEN_h3" -> lookup_sym (call x)
         | "TAG_OPEN_h4" -> lookup_sym (call x)
         | "TAG_OPEN_div" -> lookup_sym (call x)
         | "TAG_OPEN_b" -> lookup_sym (call x)
         | "TAG_OPEN_i" -> lookup_sym (call x)
         | "TAG_OPEN_ul" -> lookup_sym (call x)
         | "TAG_OPEN_ol" -> lookup_sym (call x)
         | "TAG_OPEN_table" -> lookup_sym (call x)
         | "TAG_CLOSE_h1" -> lookup_sym (ret x)
         | "TAG_CLOSE_h2" -> lookup_sym (ret x)
         | "TAG_CLOSE_h3" -> lookup_sym (ret x)
         | "TAG_CLOSE_h4" -> lookup_sym (ret x)
         | "TAG_CLOSE_div" -> lookup_sym (ret x)
         | "TAG_CLOSE_b" -> lookup_sym (ret x)
         | "TAG_CLOSE_i" -> lookup_sym (ret x)
         | "TAG_CLOSE_ul" -> lookup_sym (ret x)
         | "TAG_CLOSE_ol" -> lookup_sym (ret x)
         | "TAG_CLOSE_table" -> lookup_sym (ret x)
         | _ -> lookup_sym (plain x))

let hint = Array.of_list h
let num_round = 10
let forest = Array.create ~len:(List.length h) 0

(* NOTE - time the parsing function *)
let () =
  let t = Time_ns.now () in
  for _ = 1 to num_round do
    let _ = run_ppda hint forest in
    ()
  done;
  let t = Time_ns.diff (Time_ns.now ()) t in
  printf "%.0f," (Time_ns.Span.to_ns t /. Int.to_float num_round)

let t_extract = ref 0.

(* NOTE - time the extraction function *)
let () =
  let t = Time_ns.now () in
  for _ = 1 to num_round do
    let _ = run_epda_no_act forest hint in
    ()
  done;
  let t = Time_ns.diff (Time_ns.now ()) t in
  t_extract := Time_ns.Span.to_ns t /. Int.to_float num_round;
  printf "%.0f," !t_extract

(* NOTE - time the semantic actions *)
let () =
  let t = Time_ns.now () in
  for _ = 1 to num_round do
    let tree = run_epda_act forest hint leaves in
    ()
  done;
  let t = Time_ns.diff (Time_ns.now ()) t in
  let t_run_act = Time_ns.Span.to_ns t /. Int.to_float num_round in
  printf "%.0f\n" (t_run_act -. !t_extract)
