open TCFGParser.CoqVPG
open TCFGParser.CoqParseTree
open TCFGParser.Utils
module List = Core.List

module Info = TCFGParser.Translation.GInfo (struct
  let tcfg = Tcfgs.tcfg
  let grammar_name = "TCFG"
end)

let p = Info.p
let fb = Info.f_b
let f_init = Info.f_init

let split_stack st =
  match st with [] -> (None, []) | top :: tail -> (Some top, tail)

let rec _extract w m (v, stack) =
  match w with
  | [] -> v
  | i :: w' ->
      let r = List.hd_exn v in
      let me, m' = (List.hd_exn m, List.tl_exn m) in
      let v_stack =
        match fb me [ (v, stack) ] with
        | [] -> err "cannot extract partial parse tree"
        | vt :: _ -> vt
      in
      _extract w' m' v_stack

let extract w forest =
  match forest with
  | [] -> []
  | me :: forest' -> (
      let w = List.tl_exn w in
      match f_init me with
      | [] -> err "Cannot terminate parse tree"
      | vs :: _ -> _extract w forest' vs)

let m0 =
  let l0 = V0 (str2cl "grammar") in
  PlnCME (Coq_vc_set.singleton (None, PlnE (l0, TCFGParser.Utils.c0, l0)))

let token_WS = [%sedlex.regexp? Plus (Chars " \n\t\r")]
let token_Others = [%sedlex.regexp? 'A' .. 'Z' | 'a' .. 'z' | '_' | '0' .. '9']

let token_Terminal =
  [%sedlex.regexp?
    'A' .. 'Z', Star token_Others | '\'', Plus (Compl '\''), '\'']

let token_Nonterminal = [%sedlex.regexp? 'a' .. 'z', Star token_Others]
let token_Comment = [%sedlex.regexp? "//", Star (Compl '\n'), '\n']
let token_Reg_op = [%sedlex.regexp? Chars "+?*"]
let token_Rightarrow = [%sedlex.regexp? "->"]
let token_LeftAngleBracket = [%sedlex.regexp? '<']
let token_RightAngleBracket = [%sedlex.regexp? '>']
let token_LeftCurlyBracket = [%sedlex.regexp? '{']
let token_RightCurlyBracket = [%sedlex.regexp? '}']
let token_TwoDots = [%sedlex.regexp? ".."]
let token_Dot = [%sedlex.regexp? '.']
let token_Char = [%sedlex.regexp? '\'', Compl '\'', '\'']
let token_Action = [%sedlex.regexp? "@{", Star (Compl '}'), "}"]
let token_VerticalBar = [%sedlex.regexp? '|']
let token_Colon = [%sedlex.regexp? ':']
let token_Semicolon = [%sedlex.regexp? ';']
let token_LeftRoundBracket = [%sedlex.regexp? '(']
let token_RightRoundBracket = [%sedlex.regexp? ')']
let token_Ignore = [%sedlex.regexp? "Ignore"]
let token_NotStart = [%sedlex.regexp? "[^"]
let token_RightSquareBracket = [%sedlex.regexp? ']']

let rec _parse buf w m stack =
  match%sedlex buf with
  | token_WS -> _parse buf w m stack
  | token_Others ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Others ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "Others") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Terminal ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Terminal ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "Terminal") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Nonterminal ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Nonterminal ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "Nonterminal") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Comment -> _parse buf w m stack
  | token_Reg_op ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Reg_op ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "Reg_op") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Rightarrow ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Rightarrow ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "->") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_LeftAngleBracket ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "LeftAngleBracket ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "'<'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_RightAngleBracket ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "RightAngleBracket ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "'>'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_LeftCurlyBracket ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "LeftCurlyBracket ▷ %s\n" lexeme;
      let m1 = List.hd_exn m in
      let me, stack = p (List.hd_exn m) stack (call "'{'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (call lexeme :: w) (me :: m) stack
  | token_RightCurlyBracket ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "RightCurlyBracket ▷ %s\n" lexeme;
      let stack_top, stack_tail = split_stack stack in
      let me, stack = p (List.hd_exn m) stack (ret "'}'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (ret lexeme :: w) (me :: m) stack
  | token_TwoDots ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "TwoDots ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "'..'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Dot ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Dot ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "'.'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Char ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Char ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "Char") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Action ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Action ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "Action") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_VerticalBar ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "VerticalBar ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "'|'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Colon ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Colon ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "':'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_Semicolon ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Semicolon ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "';'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_LeftRoundBracket ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "LeftRoundBracket ▷ %s\n" lexeme;
      let m1 = List.hd_exn m in
      let me, stack = p (List.hd_exn m) stack (call "'('") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (call lexeme :: w) (me :: m) stack
  | token_RightRoundBracket ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "RightRoundBracket ▷ %s\n" lexeme;
      let stack_top, stack_tail = split_stack stack in
      let me, stack = p (List.hd_exn m) stack (ret "')'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (ret lexeme :: w) (me :: m) stack
  | token_Ignore ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "Ignore ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "Ignore") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_NotStart ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "NotStart ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "'[^'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | token_RightSquareBracket ->
      let lexeme = Sedlexing.Utf8.lexeme buf in
      Printf.printf "RightSquareBracket ▷ %s\n" lexeme;
      let me, stack = p (List.hd_exn m) stack (plain "']'") in
      if is_empty_me me then err "empty m" else ();
      _parse buf (plain lexeme :: w) (me :: m) stack
  | eof ->
      Printf.printf "EOF\n";
      (w, m)
  | _ ->
      err
        (Printf.sprintf "Lexing err at %d, %d"
           (fst (Sedlexing.loc buf))
           (snd (Sedlexing.loc buf)))

let w, forest =
  let in_channel = open_in Sys.argv.(1) in
  let lexbuf = Sedlexing.Utf8.from_channel in_channel in
  let w, forest = _parse lexbuf [] [ m0 ] [] in
  (w, forest)

let vpg_parse_tree = extract w forest

