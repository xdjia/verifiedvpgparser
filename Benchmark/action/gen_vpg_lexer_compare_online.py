"""
Generate programs for lexers.

Usage: In shell, run the following commend.
```
python gen_vpg_lexer_compare_online.py && dune exec ./parse_tcfg.exe vpgs/vpg.vpg
```
"""


def gen_lexer(terminals, calls, returns, indices: list, need_print, terminals_to_skip):
    """ Create the file `Lexer/VPGLexer.ml` """

    text = []
    text += ["(* VPGLexer *)\n"]
    text += ["module Map = Core.Map"]
    text += ["module List = Core.List"]
    text += ["module String = Core.String"]
    text += ["module Hashtbl = Core.Hashtbl"]
    text += ["open TCFGParser.Utils"]

    text += ["let p = TCFGParser.RRParser.Coq_parser.p Others.g"]
    text += ["let fb = TCFGParser.RRParser.Extract.f_b Others.g"]

    text += ["let trans_eps = !Gen_pda.trans_eps"]
    text += ["let debug = TCFGParser.Utils.debug"]
    # text += ["let err = TCFGParser.RRParser.err"]


    # text += ["module Dict = TCFGParser.RRParser.Unmarshall(struct let path = \"dict_vpg/\" end)\n"]

    text += ["let equal_coq_ME = TCFGParser.RRParser.CoqDef.equal_coq_ME"]
    text += ["let pda = !Gen_pda.trans"]
    text += ["let epda = !Gen_pda.etrans'"]
    text += ["let m0 = Gen_pda.m0"]

    text += [
        "let split_stack st = match st with [] -> (None, []) | top::tail -> (Some top, tail)"]

    text += ["type kind = Call | Return | Plain"]

    text += ["""let rec _extract w m v stack =
  match w with
  | [] -> v
  | i :: w' -> (
      let r = List.hd_exn v in
      let me, m' = (List.hd_exn m, List.tl_exn m) in
      let r_online = match fb me [ (v, stack) ] with [] -> err "no onlinre r" | vt :: _ -> vt in
      match i with
      | Call ->
        let top, stack' = split_stack stack in
          let () = debug "Call" in
          let r' = Map.find_exn epda (r, top, me) in
          _extract w' m' (r' :: v) stack'
      | Plain ->
          let () = debug "Plain" in
          let r' = Map.find_exn epda (r, None, me) in
          _extract w' m' (r' :: v) stack
      | Return -> (
          let () = debug "Return" in
          let r' = Map.find_exn epda (r, None, me) in
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

    for i, terminal in enumerate(terminals):
        text += [f"let token_{terminal} = [%sedlex.regexp? {terminals[terminal]}]"]

    text += ["\n"]
    text += ["let rec _parse buf w m stack ="]
    text += ["""  match%sedlex buf with"""]

    ident = " " * 4
    text_action_plain = ident + \
        "let me_online = match p (List.hd_exn m) None ({s}) with | None -> raise (Invalid_argument \"\") | Some me -> me in"
    text_action_plain += ident + \
        "let me = match Map.find_exn pda (List.hd_exn m, None, {s}) with | None -> raise (Invalid_argument \"\") | Some me -> me in"
    text_action_plain += ident + \
        "let () = if equal_coq_ME me_online me then () else raise (Invalid_argument \"not the same\") in"
    text_action_plain += "\n" + ident + "_parse buf (Plain::w) (me::m) stack"

    text_action_call = ident + "let m1 = List.hd_exn m in"
    text_action_call += "\n" + ident + \
        "let me = match Map.find_exn pda (m1, None, {s}) with None -> raise (Invalid_argument \"\") | Some me -> me in"
    text_action_call += "\n" + ident + \
        "let me_online = match p m1 None ({s}) with None -> raise (Invalid_argument \"\") | Some me -> me in"
    text_action_call += ident + \
        "let () = if equal_coq_ME me_online me then () else raise (Invalid_argument \"not the same\") in"
    text_action_call += "\n" + ident + \
        "_parse buf (Call::w) (me::m) (m1::stack)"

    text_action_ret = ident + "let stack_top, stack_tail = split_stack stack in"
    text_action_ret += "\n" + ident + \
        "let me = match Map.find_exn pda (List.hd_exn m, stack_top, {s}) with None -> raise (Invalid_argument \"\") | Some me -> me in"
    text_action_ret += "\n" + ident + \
        "let me_online = match p (List.hd_exn m) stack_top ({s}) with None -> raise (Invalid_argument \"\") | Some me -> me in"
    text_action_ret += ident + \
        "let () = if equal_coq_ME me_online me then () else raise (Invalid_argument \"not the same\") in"
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
                    s='Call "{}"'.format(terminals2symbols[terminal]))]
            elif terminal in returns:
                text += [text_action_ret.format(
                    s='Ret "{}"'.format(terminals2symbols[terminal]))]
            else:
                text += [text_action_plain.format(
                    s='Plain "{}"'.format(terminals2symbols[terminal]))]

    if need_print:
        text += ["  | eof -> Printf.printf \"EOF\\n\"; (w, m)"]
    else:
        text += ["  | eof -> (w, m)"]

    text += [
        """  | _ -> Printf.printf "error %d, %d\\n" (fst (Sedlexing.loc buf)) (snd (Sedlexing.loc buf)); failwith "Unexpected character" """]

    text += ["\nlet forest =",
             "  let in_channel = open_in Sys.argv.(1) in",
             "  let lexbuf = Sedlexing.Utf8.from_channel in_channel in",
             "  (* FIXME 1 should always be the start state, but currently this is not guaranteed. *)",
             "  (* FIXME record words. *)",
             "  (* State 0 means \"no state\" *)",
             "  let w, forest = _parse lexbuf [] [m0] [] in",
             "  let v = extract w forest in",
             "  v"]

    with open("parse_tcfg.ml", "w") as f:
        f.write("\n".join(text))


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

    gen_lexer(terminals, calls, returns, indices, need_print=True,
              terminals_to_skip=["WS", "Comment"])
