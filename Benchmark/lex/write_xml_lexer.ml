open Core
open TCFGParser.CoqVPG
open TCFGParser.Utils

let flag_use_symbol = false

(* /** XML lexer derived from ANTLR v4 ref guide book example */
lexer grammar XMLLexer;

// Default "mode": Everything OUTSIDE of a tag
COMMENT     :   '<!--' .*? '-->' ;
CDATA       :   '<![CDATA[' .*? ']]>' ;
/** Scarf all DTD stuff, Entity Declarations like <!ENTITY ...>,
 *  and Notation Declarations <!NOTATION ...>
 */
DTD         :   '<!' .*? '>'            -> skip ;
EntityRef   :   '&' Name ';' ;
CharRef     :   '&#' DIGIT+ ';'
            |   '&#x' HEXDIGIT+ ';'
            ;
SEA_WS      :   (' '|'\t'|'\r'? '\n')+ ;

OPEN        :   '<'                     -> pushMode(INSIDE) ;
XMLDeclOpen :   '<?xml' S               -> pushMode(INSIDE) ;
SPECIAL_OPEN:   '<?' Name               -> more, pushMode(PROC_INSTR) ;

TEXT        :   ~[<&]+ ;        // match any 16 bit char other than < and &

// ----------------- Everything INSIDE of a tag ---------------------
mode INSIDE;

CLOSE       :   '>'                     -> popMode ;
SPECIAL_CLOSE:  '?>'                    -> popMode ; // close <?xml...?>
SLASH_CLOSE :   '/>'                    -> popMode ;
SLASH       :   '/' ;
EQUALS      :   '=' ;
STRING      :   '"' ~[<"]* '"'
            |   '\'' ~[<']* '\''
            ;
Name        :   NameStartChar NameChar* ;
S           :   [ \t\r\n]               -> skip ;

fragment
HEXDIGIT    :   [a-fA-F0-9] ;

fragment
DIGIT       :   [0-9] ;

fragment
NameChar    :   NameStartChar
            |   '-' | '_' | '.' | DIGIT
            |   '\u00B7'
            |   '\u0300'..'\u036F'
            |   '\u203F'..'\u2040'
            ;

fragment
NameStartChar
            :   [:a-zA-Z]
            |   '\u2070'..'\u218F'
            |   '\u2C00'..'\u2FEF'
            |   '\u3001'..'\uD7FF'
            |   '\uF900'..'\uFDCF'
            |   '\uFDF0'..'\uFFFD'
            ;

// ----------------- Handle <? ... ?> ---------------------
mode PROC_INSTR;

PI          :   '?>'                    -> popMode ; // close <?...?>
IGNORE      :   .                       -> more ; *)

let used_tokens =
  [
    plain "XMLDeclOpen";
    plain "SPECIAL_CLOSE";
    plain "CDATA";
    plain "COMMENT";
    plain "SingleTag";
    plain "EntityRef";
    plain "CharRef";
    plain "Name";
    plain "'='";
    plain "STRING";
    plain "TEXT";
    plain "COMMENT";
    plain "PI";
    plain "SEA_WS";
    call "OpenTag";
    ret "CloseTag";
  ]

let tokenNames =
  [
    (* 0 *)
    plain "NameStartChar";
    (* 1 *)
    plain "DIGIT";
    (* 2 *)
    plain "NameChar";
    (* 3 *)
    plain "HEXDIGIT";
    (* 4 *)
    plain "S";
    (* 5 *)
    plain "Name";
    (* 6 *)
    plain "COMMENT";
    (* 7 *)
    plain "CDATA";
    (* 8 *)
    plain "DTD";
    (* 9 *)
    plain "EntityRef";
    (* 10 *)
    plain "CharRef";
    (* 11 *)
    plain "SEA_WS";
    (* 12 *)
    plain "'<'";
    (* 13 *)
    plain "XMLDeclOpen";
    (* 14 *)
    plain "SPECIAL_OPEN";
    (* 15 *)
    plain "TEXT";
    (* 16 *)
    plain "'>'";
    (* 17 *)
    plain "SPECIAL_CLOSE";
    (* 18 *)
    plain "'/>'";
    (* 19 *)
    plain "'/'";
    (* 20 *)
    plain "'='";
    (* 21 *)
    plain "STRING";
    (* 22 *)
    plain "PI";
    (* 23 *)
    plain "IGNORE";
    (* 24 *)
    plain "SingleTag";
    (* 25 *)
    call "OpenTag";
    (* 26 *)
    ret "CloseTag";
  ]

let find_sym_index name =
  let rec _f names i =
    match names with
    | x :: names -> if equal_symbol name x then i else _f names (i + 1)
    | [] -> err "Can't find the token"
  in
  _f tokenNames 0 |> Int.to_string |> sprintf "token_%s"

let tokenDefs =
  [
    "";
    "";
    "";
    {|[%sedlex.regexp? ( ':' | 'a' .. 'z' | 'A' .. 'Z' | 0x0000 .. 0x001F | 0x2070 .. 0x218F | 0x2C00 .. 0x2FEF | 0x3001 .. 0xD7FF | 0xF900 .. 0xFDCF | 0xFDF0 .. 0xFFFD )]|};
    {|[%sedlex.regexp? '0' .. '9']|};
    {|[%sedlex.regexp? ( |} ^ "token_NameStartChar" ^ {| | Chars "-_." | |}
    ^ "token_DIGIT"
    ^ {| | 0x0000 .. 0x001F | 0x2070 .. 0x218F | 0x2C00 .. 0x2FEF | 0x3001 .. 0xD7FF | 0xF900 .. 0xFDCF | 0xFDF0 .. 0xFFFD )]|};
    {|[%sedlex.regexp? 'a' .. 'f' | 'A' .. 'F' | '0' .. '9']|};
    {|[%sedlex.regexp? Chars " \t\r\n"]|};
    {|[%sedlex.regexp?  |} ^ "token_NameStartChar" ^ {| , Star  |}
    ^ "token_NameChar" ^ {| ]|};
    {|[%sedlex.regexp? "<!--", Star any, "-->"]|};
    {|[%sedlex.regexp? "<![CDATA[", Star any, "]]>"]|};
    {|[%sedlex.regexp? "<!", Star any, ">"]|};
    {|[%sedlex.regexp? "&",  |} ^ "token_Name" ^ {| , ";"]|};
    {|[%sedlex.regexp? Chars "&#", Plus  |} ^ "token_DIGIT"
    ^ {|  | Chars "&#x", Plus  |} ^ "token_HEXDIGIT" ^ {| ]|};
    {|[%sedlex.regexp? Plus (Star (Opt (Chars " \t\r"), '\n'))]|};
    {|[%sedlex.regexp? '<']|};
    {|[%sedlex.regexp? "<?xml",  |} ^ "token_S" ^ {| ]|};
    {|[%sedlex.regexp? "<?",  |} ^ "token_Name" ^ {| ]|};
    {|[%sedlex.regexp? "<?xml", Plus (Compl ('<' | '&'))]|};
    {|[%sedlex.regexp? '>']|};
    {|[%sedlex.regexp? "?>"]|};
    {|[%sedlex.regexp? "/>"]|};
    {|[%sedlex.regexp? '/']|};
    {|[%sedlex.regexp? '=']|};
    {|[%sedlex.regexp? '"', Star (Compl ('<' | '"')), '"' | '\'', Star (Compl ('<' | '\'')), '\'']|};
    {|[%sedlex.regexp? "?>"]|};
    {|[%sedlex.regexp? any]|};
  ]
(* @
   [(* NOTE - SingleTag *)
   {|[%sedlex.regexp? '<', |}
   ^ find_sym_index (plain "Name")
   ^ {|, Star (|}
   ^ find_sym_index (plain "Name")
   ^ {|, '=', |}
   ^ find_sym_index (plain "STRING")
   ^ {|), "/>"]|};
   (* NOTE - OpenTag *)
   {|[%sedlex.regexp? '<', |}
   ^ find_sym_index (plain "Name")
   ^ {|, Star (|}
   ^ find_sym_index (plain "Name")
   ^ {|, '=', |}
   ^ find_sym_index (plain "STRING")
   ^ {|), ">"]|};
   (* NOTE - CloseTag *)
   {|[%sedlex.regexp? "</", |} ^ find_sym_index (plain "Name") ^ {|, ">"]|};] *)

let () = assert (List.length tokenNames = List.length tokenDefs)

(* NOTE - Tokens to ignore by the lexer *)
let fragment =
  [ plain "NameStartChar"; plain "DIGIT"; plain "NameChar"; plain "HEXDIGIT" ]
  @ [ plain "S"; plain "DTD" ]
  @ [ plain "PI"; plain "IGNORE" ]
  @ [ plain "SingleTag"; call "OpenTag"; ret "CloseTag" ]

let callSyms = [ call "OpenTag" ]
let retSyms = [ ret "CloseTag" ]
let syms = tokenNames

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
  sprintf "        lex buf (Ic %s::h)  ((Sedlexing.Utf8.lexeme buf)::w)" d

let text_action_ret d =
  sprintf "        lex buf (Ir %s::h) ((Sedlexing.Utf8.lexeme buf)::w)" d

let token_to_skip = [ plain "WS" ]

let prog_head =
  [ "(* VPGLexer *)\n" ] @ [ "open Utils" ] @ [ "open Core" ]
  @ [ "open Printf" ]
  @ [
      "module Pda = TCFGParser.Unmarshall (struct let path = \"dict_vpg/\" end)";
    ]
  @ [
      "let pda = Map.of_alist_exn (module TCFGParser.IntVPG.Int3) Pda.int_trans";
    ]
  @ [ "let int_trans_eps = Map.of_alist_exn (module Core.Int) Pda.trans_eps" ]
  @ [
      "let int_epda = Map.of_alist_exn (module TCFGParser.IntVPG.Int3) \
       Pda.int_epda";
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
      "let show_tagged = function Types.VPGType.Call x | Types.VPGType.Ret x | \
       Types.VPGType.Plain x -> x";
    ]
  @ (tokenDefs
    |> List.mapi ~f:(fun i def ->
           let ss =
             sprintf "let token_%s = %s"
               (List.nth_exn tokenNames i |> strip_symbol)
               def
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
    (* "            let () = debug \"Call\" in"; *)
    "            let r' = Map.find_exn int_epda (r, top, me) in\n\
    \            _extract w' m' (r' :: v) stack'\n\
    \        | HPln ->";
    (* "            let () = debug \"Plain\" in"; *)
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
    |> List.mapi ~f:(fun token_index def ->
           let sym = List.nth_exn syms token_index in
           let token =
             if flag_use_symbol then sprintf "%s" (code_symbol sym)
             else Int.to_string token_index
           in
           if List.mem token_to_skip sym ~equal:equal_symbol then
             [
               sprintf "  | token_%s -> lex buf h w"
                 (List.nth_exn tokenNames token_index |> strip_symbol);
             ]
           else if List.mem fragment sym ~equal:equal_symbol then []
           else
             let prog_def_head =
               sprintf "  | token_%s ->"
                 (List.nth_exn tokenNames token_index |> strip_symbol)
             in
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

let prog_extract =
  syms
  |> List.mapi ~f:(fun token_index sym ->
         (* if List.mem token_to_skip sym ~equal:equal_symbol then []
            else if List.mem fragment sym ~equal:equal_symbol then []
            else *)
         let prog_def_body =
           if List.mem callSyms sym ~equal:equal_symbol then
             sprintf "else if Int.equal i %d then extract_call m2" token_index
           else if List.mem retSyms sym ~equal:equal_symbol then
             sprintf "else if Int.equal i %d then extract_return m2" token_index
           else
             sprintf "else if Int.equal i %d then extract_plain m2" token_index
         in
         [ prog_def_body ])
  |> List.concat

let prog_parse =
  syms
  |> List.mapi ~f:(fun token_index sym ->
         (* if List.mem token_to_skip sym ~equal:equal_symbol then []
            else if List.mem fragment sym ~equal:equal_symbol then []
            else *)
         let prog_def_body =
           if List.mem callSyms sym ~equal:equal_symbol then
             sprintf "else if Int.equal i %d then parse_call l me i st"
               token_index
           else if List.mem retSyms sym ~equal:equal_symbol then
             sprintf "else if Int.equal i %d then parse_ret l me i st"
               token_index
           else
             sprintf "else if Int.equal i %d then parse_plain l me i st"
               token_index
         in
         [ prog_def_body ])
  |> List.concat

let () = print_endline (String.concat ~sep:"\n" prog_extract)
let () = print_endline ""
let () = print_endline (String.concat ~sep:"\n" prog_parse)
