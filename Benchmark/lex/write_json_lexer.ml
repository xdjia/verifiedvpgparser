open Core
open TCFGParser.CoqVPG
open TCFGParser.Utils

let flag_use_symbol = false

(* STRING
      : '"' (ESC | SAFECODEPOINT)* '"'
      ;


   fragment ESC
      : '\\' (["\\/bfnrt] | UNICODE)
      ;


   fragment UNICODE
      : 'u' HEX HEX HEX HEX
      ;


   fragment HEX
      : [0-9a-fA-F]
      ;


   fragment SAFECODEPOINT
      : ~ ["\\\u0000-\u001F]
      ;


   NUMBER
      : '-'? INT ('.' [0-9] +)? EXP?
      ;


   fragment INT
      : '0' | [1-9] [0-9]*
      ;

   // no leading zeros

   fragment EXP
      : [Ee] [+\-]? INT
      ;

   // \- since - means "range" inside [...]

   WS
      : [ \t\n\r] + -> skip
      ; *)

let tokenDefs =
  [
    (plain "WS", "Plus (Chars \" \\n\\t\\r\")");
    (plain "INT", "'0' | '0' .. '9', Star '0' .. '9'");
    (plain "EXP", "('E' | 'e'), Opt ('+' | '\\\\' | '-'), token_1");
    (plain "NUMBER", "Opt '-', token_1, Opt ('.', Plus '0' .. '9'), Opt token_2");
    (plain "SAFECODEPOINT", "Compl ('\"' | '\\\\' | 0x0000 .. 0x001F)");
    (plain "HEX", "'A' .. 'Z' | 'a' .. 'z' | '0' .. '9'");
    (plain "UNICODE", "'u', token_5, token_5, token_5, token_5");
    ( plain "ESC",
      "'\\\\', ('\"' | '\\\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' | token_6)" );
    (plain "STRING", "'\"', Star (token_7 | token_4), '\"'");
    (call "{", "'{'");
    (ret "}", "'}'");
    (call "[", "'['");
    (ret "]", "']'");
    (plain "true", "\"true\"");
    (plain "false", "\"false\"");
    (plain "null", "\"null\"");
    (plain ",", "','");
    (plain ":", "':'");
  ]


(* NOTE - Tokens to ignore by the lexer *)
let fragment =
  [
    plain "ESC";
    plain "UNICODE";
    plain "HEX";
    plain "SAFECODEPOINT";
    plain "INT";
    plain "EXP";
  ]

let callSyms = [ call "{"; call "[" ]
let retSyms = [ ret "}"; ret "]" ]
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
    ("    (let me = lookup_pda (List.hd_exn m, %s, %s) in\n"
   ^^ "        _parse buf (HPln::h) (Sedlexing.Utf8.lexeme buf::w) (me::m) \
       stack)")
    (if flag_use_symbol then "None" else "0")
    d

let text_action_call d =
  sprintf
    ("    let m1 = List.hd_exn m in\n"
   ^^ "        let me = lookup_pda (m1, %s, %s) in\n"
   ^^ "        _parse buf (HCall::h) (Sedlexing.Utf8.lexeme buf::w) (me::m) \
       (m1::stack)")
    (if flag_use_symbol then "None" else "0")
    d

let text_action_ret d =
  sprintf
    ("    let stack_top, stack_tail = split_stack stack in\n"
   ^^ "    let me = lookup_pda (List.hd_exn m, stack_top, %s) in\n"
   ^^ "    _parse buf (HRet::h) (Sedlexing.Utf8.lexeme buf::w) (me::m) \
       stack_tail")
    d

let text_action_plain d =
  sprintf "        lex buf (Ip %s::h) ((Sedlexing.Utf8.lexeme buf)::w)" d

let text_action_call d =
  sprintf "        lex buf (Ic %s::h)  ((Sedlexing.Utf8.lexeme buf)::w)"   d

let text_action_ret d =
  sprintf "        lex buf (Ir %s::h) ((Sedlexing.Utf8.lexeme buf)::w)" d

let token_to_skip = [ plain "WS" ]

let prog_head =
  [ "(* VPGLexer *)\n" ] @ [ "open Utils" ] @ [ "open Core" ]
  @ [ "open Printf" ]
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
  @ [
      "let show_tagged = function Types.VPGType.call x | Types.VPGType.ret x | \
       Types.VPGType.plain x -> x";
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
    \        | HCall ->\n\
    \            let top, stack' = split_stack stack in";
    (* "            let () = debug \"call\" in"; *)
    "            let r' = Map.find_exn int_epda (r, top, me) in\n\
    \            _extract w' m' (r' :: v) stack'\n\
    \        | HPln ->";
    (* "            let () = debug \"plain\" in"; *)
    "            let r' = Map.find_exn int_epda (r, 0, me) in\n\
    \            _extract w' m' (r' :: v) stack\n\
    \        | HRet -> (";
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
  [ "\n"; "let rec lex buf h w ="; "  match%sedlex buf with" ]
  @ (tokenDefs
    |> List.map ~f:(fun (sym, def) ->
           let token_index = Map.find_exn sym2int sym in
           let token =
             if flag_use_symbol then sprintf "%s" (code_symbol sym)
             else Int.to_string (Map.find_exn sym2int sym)
           in
           if List.mem token_to_skip sym ~equal:equal_symbol then
             [ sprintf "  | token_%d -> lex buf h w" token_index ]
           else if List.mem fragment sym ~equal:equal_symbol then []
           else
             let prog_def_head = sprintf "  | token_%d ->" token_index in
             let prog_def_body =
               if List.mem callSyms sym ~equal:equal_symbol then
                 text_action_call token
               else if List.mem retSyms sym ~equal:equal_symbol then
                 text_action_ret token
               else text_action_plain token
             in
             [
               prog_def_head;
               (* sprintf
                  "    if do_debug then debug (sprintf \"%s ▷ %%s\" (Sedlexing.Utf8.lexeme \
                   buf)) else (); "
                  (show_tagged sym); *)
               prog_def_body;
             ])
    |> List.concat)
  @ [
      "  | eof -> if do_debug then debug \"EOF\" else (); (h,w)";
      "  | _ -> err (sprintf \"Lexing error %d, %d\\n\" (fst (Sedlexing.loc \
       buf)) (snd (Sedlexing.loc buf))) ";
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
  String.concat ~sep:"\n"
    (* (prog_head @ prog_extract @ prog_main @ prog_body) *)
    (prog_head @ prog_main @ prog_body)

let export () =
  if flag_use_symbol then
    Out_channel.write_all "parse_json.ml" ~data:prog_parser
  else Out_channel.write_all "iparse_json.ml" ~data:prog_parser

(* let () = export () *)

let () = print_endline (String.concat ~sep:"\n" (prog_head @ prog_main))
