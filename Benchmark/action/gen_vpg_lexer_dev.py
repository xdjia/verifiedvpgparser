"""
Generate programs for lexers.

Usage: In shell, run the following commend.
```
python gen_vpg_lexer_dev.py && dune exec ./parse_tcfg.exe vpgs/vpg.vpg
```
"""


raise ValueError("Obsolete!")

def gen_lexer(terminals, calls, returns, indices: list, need_print, terminals_to_skip):
    """ Create the file `Lexer/VPGLexer.ml` """

    text = ["open TCFGParser.Utils"]
    text += ["(* VPGLexer *)\n"]
    text += ["module Map = Core.Map"]
    text += ["module List = Core.List"]
    text += ["module String = Core.String"]
    text += ["module Hashtbl = Core.Hashtbl"]

    # text += ["module Dict = TCFGParser.RRParser.Unmarshall(struct let path = \"dict_vpg/\" end)\n"]

    # text += ["let pda = Pda.pda"]
    # text += ["let epda = Pda.epda"]
    # text += ["let m0 = Pda.m0"]
    # text += ["let trans_eps = Pda.trans_eps"]
    text += ["let int_trans = Pda.int_trans"]
    text += ["let int_eTrans = Pda.int_eTrans"]
    text += ["let int_epda = Pda.int_epda"]
    text += ["let int2funs = Pda.int2funs"]
    text += ["let int2sym = Pda.int2sym"]
    text += ["let leps2funs = Pda.leps2funs"]
    text += ["let int2estate = Pda.int2estate"]

    text += [
        "let split_stack st = match st with [] -> (None, []) | top::tail -> (Some top, tail)"]

    text += ["type kind = Call | Return | Plain"]

    for i, terminal in enumerate(terminals):
        text += [f"let token_{terminal} = [%sedlex.regexp? {terminals[terminal]}]"]

    text += ["\n"]

    text += ["""let rec _extract w m v stack =
  match w with
  | [] -> v
  | i :: w' -> (
      let r = List.hd_exn v in
      let me, m' = (List.hd_exn m, List.tl_exn m) in
      let top, stack' = split_stack stack in
      match i with
      | Call ->
          let () = debug "Call" in
          let r' = Map.find_exn epda (r, top, me) in
          _extract w' m' (r' :: v) stack'
      | Plain ->
          let () = debug "Plain" in
          let r' = Map.find_exn epda (r, top, me) in
          _extract w' m' (r' :: v) stack
      | Return -> (
          let () = debug "Return" in
          let r' = Map.find_exn epda (r, top, me) in
          match r' with Retv r'' -> _extract w' m' (r' :: v) (r'' :: stack))
      | _ -> raise (Invalid_argument "i and r don't match"))

let extract w m =
  let me, m' = (List.hd_exn m, List.tl_exn m) in
  let w = List.tl_exn w in
  match Map.find_exn trans_eps me with
  | None -> raise (Invalid_argument "")
  | Some re -> (
      match re with
      | Retv re' -> _extract w m' [ re ] [ re' ]
      | _ -> _extract w m' [ re ] [])"""]

    text += ["\n"]
    text += ["let rec _parse buf w m stack ="]
    text += ["""  match%sedlex buf with"""]

    ident = " " * 4
    text_action_plain = ident + \
        "(let me = Map.find_exn pda (List.hd_exn m, None, {}) in"
    text_action_plain += "\n" + ident + "_parse buf (Plain::w) (me::m) stack)"

    text_action_call = ident + "let m1 = List.hd_exn m in"
    text_action_call += "\n" + ident + \
        "let me = Map.find_exn pda (m1, None, {}) in"
    text_action_call += "\n" + ident + \
        "_parse buf (Call::w) (me::m) (m1::stack)"

    text_action_ret = ident + "let stack_top, stack_tail = split_stack stack in"
    text_action_ret += "\n" + ident + \
        "let me = Map.find_exn pda (List.hd_exn m, stack_top, {}) in"
    text_action_ret += "\n" + ident + \
        "_parse buf (Return::w) (me::m) stack_tail"

    for terminal in terminals:
        # NOTE add branches and actions

        if terminal in terminals_to_skip:
            text += [f"  | token_{terminal} -> _parse buf w m stack"]
        else:
            text += [f"  | token_{terminal} ->"]

            if need_print:
                text += [
                    f"""    Printf.printf "{terminal} ▷ %s\\n" (Sedlexing.Utf8.lexeme buf); """]

            # text += [f"  | token_{terminal} -> Some {i}"]
            i = indices.index(terminal)
            if terminal in calls:
                text += [text_action_call.format(
                    'Call "{}"'.format(terminals2symbols[terminal]))]
            elif terminal in returns:
                text += [text_action_ret.format(
                    'Ret "{}"'.format(terminals2symbols[terminal]))]
            else:
                text += [text_action_plain.format(
                    'Plain "{}"'.format(terminals2symbols[terminal]))]

    if need_print:
        text += ["  | eof -> Printf.printf \"EOF\\n\"; (w, m)"]
    else:
        text += ["  | eof -> (w, m)"]

    text += [
        """  | _ -> Printf.printf "error %d, %d\\n" (fst (Sedlexing.loc buf)) (snd (Sedlexing.loc buf)); failwith "Unexpected character" """]

    text += ["\nlet forest =",
             "  let in_channel = open_in Sys.argv.(1) in",
             "  let lexbuf = Sedlexing.Utf8.from_channel in_channel in",
             "  (* NOTE State 0 is the initial state *)",
             "  let w, forest = _parse lexbuf [] [m0] [] in",
             "  w, forest"]

    return "\n".join(text)


terminals = {
    "WS": "Plus (Chars \" \\n\\t\\r\")",
    "Others": "'A'..'Z' | 'a'..'z' | '_' | '0'..'9'",
    "Terminal": "'A'..'Z', Star token_Others | '\"', Plus (Compl '\"'),'\"' ",
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
    "At": "'@'",
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
    "LeftAngleBracket": "<",
    "RightAngleBracket": ">",
    "LeftCurlyBracket": "{",
    "RightCurlyBracket": "}",
    "TwoDots": "..",
    "Dot": ".",
    "Char": "Char",
    "At": "@",
    "VerticalBar": "|",
    "Colon": ":",
    "Semicolon": ";",
    "LeftRoundBracket": "(",
    "RightRoundBracket": ")",
    "NotStart": "[^",
    "RightSquareBracket": "]",
}

indices: list[str] = [
    "LeftRoundBracket", "RightRoundBracket", "Rightarrow", "Dot", "TwoDots", "Colon", "Semicolon", "LeftAngleBracket", "RightAngleBracket", "Char", "Comment", "Nonterminal", "Reg_op", "Terminal", "NotStart", "RightSquareBracket", "Action", "Ignore", "VerticalBar"]
indices += ["Others", "WS", "LeftCurlyBracket", "RightCurlyBracket", "At"]


calls = ["LeftCurlyBracket", "LeftRoundBracket"]
returns = ["RightCurlyBracket", "RightRoundBracket"]

if __name__ == "__main__":

    prog_lexer = gen_lexer(terminals, calls, returns, indices, need_print=True,
                           terminals_to_skip=["WS", "Comment"])
    with open("parse_tcfg.ml", "w") as f:
        f.write(prog_lexer)
