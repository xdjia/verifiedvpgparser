"""
Generate programs for lexers.

Usage: In shell, run the following commend.
```
python gen_vpg_parse_online.py && dune exec ./parse_tcfg.exe vpgs/vpg.vpg
```
"""


def gen_lexer(terminals, calls, returns, indices: list, need_print, terminals_to_skip):
    """ NOTE - Create the file `Lexer/VPGLexer.ml` """

    text = ["open TCFGParser.CoqVPG"]
    text += ["open TCFGParser.CoqParseTree"]
    text += ["open TCFGParser.Utils"]
    # text += ["module Map = Core.Map"]
    text += ["module List = Core.List"]
    # text += ["module String = Core.String"]

    text += ["""
module Info = TCFGParser.Translation.GInfo (struct
    let tcfg = Tcfgs.tcfg
    let grammar_name = "TCFG"
end)

let p = Info.p
let fb = Info.f_b
let f_init = Info.f_init

let split_stack st = match st with [] -> (None, []) | top::tail -> (Some top, tail)

let rec _extract w m (v, stack) =
  match w with
  | [] -> v
  | i :: w' -> (
      let r = List.hd_exn v in
      let me, m' = (List.hd_exn m, List.tl_exn m) in
      let v_stack = match fb me [ (v, stack) ] with [] -> err "cannot extract partial parse tree" | vt :: _ -> vt in
      _extract w' m' v_stack)

let extract w forest =
  match forest with
  | [] -> []
  | me::forest' ->
    let w = List.tl_exn w in
    match f_init me with
    | [] -> err "Cannot terminate parse tree"
    | vs::_ -> (_extract w forest' vs)

let m0 = 
  let l0 = V0 (str2cl "grammar") in
  PlnCME (Coq_vc_set.singleton (None, PlnE (l0, TCFGParser.Utils.c0, l0)))
    """]

    for i, terminal in enumerate(terminals):
        text += [f"let token_{terminal} = [%sedlex.regexp? {terminals[terminal]}]"]

    text += ["\n"]
    text += ["let rec _parse buf w m stack ="]
    text += ["""  match%sedlex buf with"""]

    ident = " " * 4

    text_err = "\n" + ident + """if is_empty_me me then err "empty m" else ();"""

    text_action_plain = ident + \
        """let me, stack = p (List.hd_exn m) stack ({}) in""" + \
        text_err
    text_action_plain += "\n" + ident + \
        "_parse buf (plain lexeme::w) (me::m) stack"

    text_action_call = ident + "let m1 = List.hd_exn m in"
    text_action_call += "\n" + ident + \
        """let me, stack = p (List.hd_exn m) stack ({}) in""" + \
        text_err
    text_action_call += "\n" + ident + \
        "_parse buf (call lexeme::w) (me::m) stack"

    text_action_ret = ident + "let stack_top, stack_tail = split_stack stack in"
    text_action_ret += "\n" + ident + \
        """let me, stack = p (List.hd_exn m) stack ({}) in""" + \
        text_err
    text_action_ret += "\n" + ident + \
        "_parse buf (ret lexeme::w) (me::m) stack"

    for terminal in terminals:
        # NOTE add branches and actions

        if terminal in terminals_to_skip:
            text += [f"  | token_{terminal} -> _parse buf w m stack"]
        else:
            text += [f"  | token_{terminal} ->"]

            if need_print:
                text += [
                    f"""    let lexeme = (Sedlexing.Utf8.lexeme buf) in
    Printf.printf "{terminal} ▷ %s\\n" lexeme;"""]

            # text += [f"  | token_{terminal} -> Some {i}"]
            i = indices.index(terminal)
            if terminal in calls:
                text += [text_action_call.format(
                    'call "{}"'.format(terminals2symbols[terminal]))]
            elif terminal in returns:
                text += [text_action_ret.format(
                    'ret "{}"'.format(terminals2symbols[terminal]))]
            else:
                text += [text_action_plain.format(
                    'plain "{}"'.format(terminals2symbols[terminal]))]

    if need_print:
        text += ["  | eof -> Printf.printf \"EOF\\n\"; (w, m)"]
    else:
        text += ["  | eof -> (w, m)"]

    text += [
        """  | _ -> err ( Printf.sprintf "Lexing err at %d, %d" (fst (Sedlexing.loc buf)) (snd (Sedlexing.loc buf)) )"""]

    text += ["\nlet w, forest =",
             "  let in_channel = open_in Sys.argv.(1) in",
             "  let lexbuf = Sedlexing.Utf8.from_channel in_channel in",
             "  let w, forest = _parse lexbuf [] [m0] [] in",
             "  w, forest"]

    text += ["""
let vpg_parse_tree = extract w forest
    """]

    with open("parse/parse_tcfg.ml", "w") as f:
        f.write("\n".join(text))


terminals = {
    "WS": "Plus (Chars \" \\n\\t\\r\")",
    "Others": "'A'..'Z' | 'a'..'z' | '_' | '0'..'9'",
    "Terminal": "'A'..'Z', Star token_Others | '\\'', Plus (Compl '\\''), '\\'' ",
    "Nonterminal": "'a'..'z', Star token_Others",
    "Comment": "\"//\", Star (Compl '\\n'), '\\n'",
    "Reg_op": "Chars \"+?*\"",
    "Rightarrow": "\"->\"",
    "LeftAngleBracket": "'<'",
    "RightAngleBracket": "'>'",
    "LeftCurlyBracket": "'{'",
    "RightCurlyBracket": "'}'",
    "TwoDots": "\"..\"",
    "Dot": "'.'",
    "Char": "'\\'',Compl '\\'' ,'\\''",
    "Action": """ "@{", Star (Compl '}'), "}" """,
    "VerticalBar": "'|'",
    "Colon": "':'",
    "Semicolon": "';'",
    "LeftRoundBracket": "'('",
    "RightRoundBracket": "')'",
    "Ignore": "\"Ignore\"",
    "NotStart": """\"[^\"""",
    "RightSquareBracket": """']'""",
    # "String": "'\"', Star (Compl '\"') ,'\"'"
}

terminals2symbols = {
    "Others": "Others",
    "Ignore": "Ignore",
    "Terminal": "Terminal",
    "Nonterminal": "Nonterminal",
    "Comment": "Comment",
    "Reg_op": "Reg_op",
    "Rightarrow": "->",
    "LeftAngleBracket": "'<'",
    "RightAngleBracket": "'>'",
    "LeftCurlyBracket": "'{'",
    "RightCurlyBracket": "'}'",
    "TwoDots": "'..'",
    "Dot": "'.'",
    "Char": "Char",
    "At": "'@'",
    "VerticalBar": "'|'",
    "Colon": "':'",
    "Semicolon": "';'",
    "LeftRoundBracket": "'('",
    "RightRoundBracket": "')'",
    "NotStart": "'[^'",
    "RightSquareBracket": "']'",
    "Action": "Action"
}

indices: list[str] = [
    "LeftRoundBracket", "RightRoundBracket", "Rightarrow", "Dot", "TwoDots", "Colon", "Semicolon", "LeftAngleBracket", "RightAngleBracket", "Char", "Comment", "Nonterminal", "Reg_op", "Terminal", "NotStart", "RightSquareBracket", "Action", "Ignore", "VerticalBar"]
indices += ["Others", "WS", "LeftCurlyBracket", "RightCurlyBracket", "At"]


calls = ["LeftCurlyBracket", "LeftRoundBracket"]
returns = ["RightCurlyBracket", "RightRoundBracket"]

if __name__ == "__main__":

    gen_lexer(terminals, calls, returns, indices, need_print=True,
              terminals_to_skip=["WS", "Comment"])
