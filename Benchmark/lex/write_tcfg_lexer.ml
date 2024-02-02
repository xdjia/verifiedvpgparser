open Core
open TCFGParser.CoqVPG
open TCFGParser.Utils

let flag_debug = false

let debug s = if flag_debug then print_endline (Printf.sprintf "▶%s◀" s) else ()

let tokenDefs =
  [
    (plain "WS", "Plus (Chars \" \\n\\t\\r\")");
    (plain "Others", "'A'..'Z' | 'a'..'z' | '_' | '0'..'9'");
    (plain "Terminal", "'A'..'Z', Star token_1 | '\"', Plus (Compl '\"'),'\"' ");
    (plain "Nonterminal", "'a'..'z', Star token_1");
    (plain "Comment", "\"//\", Star (Compl '\\n'), '\\n'");
    (plain "Reg_op", "Chars \"+?*\"");
    (plain "->", "\"->\"");
    (plain "<", "'<'");
    (plain ">", "'>'");
    (plain "{", "'{'");
    (plain "}", "'}'");
    (plain "..", "\"..\"");
    (plain ".", "'.'");
    (plain "Char", "'\\'',Compl '\\'' ,'\\''");
    (plain "@", "'@'");
    (plain "|", "'|'");
    (plain ":", "':'");
    (plain ";", "';'");
    (call "(", "'('");
    (ret ")", "')'");
    (plain "Ignore", "\"Ignore\"");
    (plain "[^", "\"[^\"");
    (plain "]", "']'");
    (plain "Action", "\"@{.*}\"");
    (* # "String": "'\"', Star (Compl '\"') ,'\"'" *)
  ]

let callSyms = [ call "(" ]
let retSyms = [ ret ")" ]
let syms = tokenDefs |> List.map ~f:fst

(* let syms = List.sort syms ~compare:compare_tagged *)
let syms = syms @ [ Plain c0 ]
(* let () = debug (sprintf "#syms=%d" (List.length syms)) *)

(* let () =
   debug
     (List.mapi syms ~f:(fun i x -> sprintf "Sym %d %s" i (show_tagged x))
     |> String.concat ~sep:"\n") *)

let sym2int =
  syms |> List.mapi ~f:(fun i x -> (x, i)) |> Map.of_alist_exn (module Symbol)

let int2sym =
  syms |> List.mapi ~f:(fun i x -> (i, x)) |> Map.of_alist_exn (module Int)

let text_action_plain d =
  sprintf
    ("    (let me = Map.find_exn pda (List.hd_exn m, 0, %d) in\n"
   ^^ "        _parse buf (plain::h) (Sedlexing.Utf8.lexeme buf::w) (me::m) stack)"
    )
    d

let text_action_call d =
  sprintf
    ("    let m1 = List.hd_exn m in\n"
   ^^ "        let me = Map.find_exn pda (m1, 0, %d) in\n"
   ^^ "        _parse buf (call::h) (Sedlexing.Utf8.lexeme buf::w) (me::m) \
       (m1::stack)")
    d

let text_action_ret d =
  sprintf
    ("    let stack_top, stack_tail = split_stack stack in\n"
   ^^ "    let me = Map.find_exn pda (List.hd_exn m, stack_top, %d) in\n"
   ^^ "    _parse buf (Return::h) (Sedlexing.Utf8.lexeme buf::w) (me::m) stack_tail")
    d

let token_to_skip = [ plain "WS"; plain "Comment" ]

let prog_head =
  [ "(* VPGLexer *)\n" ] @ [ "open Utils" ]
  @ [ "module Map = Core.Map" ]
  @ [ "module List = Core.List" ]
  @ [ "module String = Core.String" ]
  @ [ "module Hashtbl = Core.Hashtbl" ]
  @ [ "module Pda = TCFGParser.Unmarshall (struct let path = \"dict_vpg/\" end)" ]
  @ [ "let pda = Map.of_alist_exn (module TCFGParser.IntVPG.Int3) Pda.int_trans" ]
  @ [ "let int_trans_eps = Map.of_alist_exn (module Core.Int) Pda.trans_eps" ]
  @ [
      "let int_epda = Map.of_alist_exn (module TCFGParser.IntVPG.Int3) Pda.int_epda";
    ]
  @ [ "let int2funs = Pda.int2funs" ]
  @ [ "let int2sym = Pda.int2sym" ]
  @ [ "let leps2funs = Pda.leps2funs" ]
  @ [ "let int2estate = Map.of_alist_exn (module Core.Int) Pda.int2estate" ]
  @ [
      "let split_stack st = match st with [] -> (0, []) | top::tail -> (top, \
       tail)";
    ]
  @ [ "type hint = Call | Return | Plain" ]
  @ [
      "let show_tagged = function Types.VPGType.Call x | Types.VPGType.Ret x | \
       Types.VPGType.Plain x -> x";
    ]
  @ (tokenDefs
    |> List.map ~f:(fun (sym, def) ->
           let token_index = Map.find_exn sym2int sym in
           let ss =
             sprintf "let token_%d = [%%sedlex.regexp? %s]" token_index def
           in
           ss))

let prog_extract =
  [
    "let rec _extract w m v stack =\n\
    \    match w with\n\
    \    | [] -> v\n\
    \    | i :: w' -> (\n\
    \        let r = List.hd_exn v in\n\
    \        let me, m' = (List.hd_exn m, List.tl_exn m) in";
    (* "let () = debug (Printf.sprintf \"%s\" (Map.find_exn int2estate r |> \
       TCFGParser.CoqParseTree.show_coq_VE)) in"; *)
    "  match i with\n\
    \        | Call ->\n\
    \            let top, stack' = split_stack stack in";
    (* "            let () = debug \"Call\" in"; *)
    "            let r' = Map.find_exn int_epda (r, top, me) in\n\
    \            _extract w' m' (r' :: v) stack'\n\
    \        | Plain ->";
    (* "            let () = debug \"Plain\" in"; *)
    "            let r' = Map.find_exn int_epda (r, 0, me) in\n\
    \            _extract w' m' (r' :: v) stack\n\
    \        | Return -> (";
    (* "            let () = debug \"Return\" in"; *)
    "            let r' = Map.find_exn int_epda (r, 0, me) in\n\
    \            _extract w' m' (r' :: v) (r' :: stack)))";
    "let extract w m =\n\
    \    let me, m' = (List.hd_exn m, List.tl_exn m) in\n\
    \    match w with\n\
    \    | [] -> err \"w is empty\" \n\
    \    | i::w ->\n\
    \    match Map.find int_trans_eps me with\n\
    \    | None -> err \"\"\n\
    \    | Some re -> (\n\
    \        match i with\n\
    \        | Return -> _extract w m' [ re ] [ re ]\n\
    \        | _ -> _extract w m' [ re ] [])";
  ]

let prog_main =
  let show_tagged = function Call x | Ret x | Plain x -> x in
  [ "\n"; "let rec _parse buf h w m stack ="; "  match%sedlex buf with" ]
  @ (tokenDefs
    |> List.map ~f:(fun (sym, def) ->
           let token_index = Map.find_exn sym2int sym in
           if List.mem token_to_skip sym ~equal:equal_symbol then
             [ sprintf "  | token_%d -> _parse buf h w m stack" token_index ]
           else
             let prog_def_head = sprintf "  | token_%d ->" token_index in
             let prog_def_body =
               if List.mem callSyms sym ~equal:equal_symbol then
                 text_action_call token_index
               else if List.mem retSyms sym ~equal:equal_symbol then
                 text_action_ret token_index
               else text_action_plain token_index
             in
             [
               prog_def_head;
               (* sprintf
                  "    debug \"%s ▷ %%s\\n\" (Sedlexing.Utf8.lexeme \
                   buf); "
                  (show_tagged sym); *)
               prog_def_body;
             ])
    |> List.concat)
  @ [
      "  | eof -> debug \"EOF\\n\"; (h, w, m)";
      "  | _ -> err \"Lexing error %d, %d\\n\" (fst (Sedlexing.loc buf)) \
       (snd (Sedlexing.loc buf)); failwith \"Unexpected character\" ";
    ]

let prog_body =
  [
    "let forest =";
    "  let in_channel = open_in Sys.argv.(1) in";
    "  let lexbuf = Sedlexing.Utf8.from_channel in_channel in";
    "  (* NOTE - State 1 is the initial state *)";
    "  let w, forest = _parse lexbuf [] [] [1] [] in";
    "  let v = extract w forest in";
    "  debug (Printf.sprintf \"#v=%d\" (List.length v));";
    "  v";
  ]

let prog_parser : string =
  String.concat ~sep:"\n" (prog_head @ prog_extract @ prog_main @ prog_body)

let export () = Out_channel.write_all "parse_tcfg.ml" ~data:prog_parser
(* let () = export () *)

let () = debug (String.concat ~sep:"\n" prog_main)