"""
Generate programs for lexers.
"""


def gen_lexer(terminals, calls, returns, indices:list, need_print, terminals_to_skip):
    """ Create the file `Lexer/VPGLexer.ml` """

    text = []
    text += ["(* VPGLexer *)\n"]
    text += ["module Map = Core.Map"]
    text += ["module List = Core.List"]
    text += ["module String = Core.String"]
    text += ["module Hashtbl = Core.Hashtbl"]

    text += ["module Dict = TCFGParser.RRParser.Unmarshall(struct let path = \"dict_vpg/\" end)\n"]

    text += ["let pda = Dict.pda"]
    text += ["let epda = Dict.epda"]

    text += ["let split_stack st = match st with [] -> (0, []) | top::tail -> (top, tail)"]

    text += ["type kind = Call | Return | Plain"]

    for i, terminal in enumerate(terminals):
        text += [f"let token_{terminal} = [%sedlex.regexp? {terminals[terminal]}]"]

    text += ["\n"]
    text += ["let rec _parse buf w m stack ="]
    text += ["""  match%sedlex buf with"""]

    ident = " " * 4
    text_action_plain = ident + "let m = Core.Hashtbl.find_exn pda (List.hd_exn m, 0, {})::m in"
    text_action_plain += "\n" + ident + "_parse buf (Plain::w) m stack"

    text_action_call = ident + "let m1 = List.hd_exn m in"
    text_action_call += "\n" + ident + "let m = Core.Hashtbl.find_exn pda (m1, 0, {})::m in"
    text_action_call += "\n" + ident + "_parse buf (Call::w) m (m1::stack)"

    text_action_ret = ident + "let stack_top, stack_tail = split_stack stack in"
    text_action_ret += "\n" + ident + "let m = Core.Hashtbl.find_exn pda (List.hd_exn m, stack_top, {})::m in"
    text_action_ret += "\n" + ident + "_parse buf (Return::w) m stack_tail"


    for terminal in terminals:
        # NOTE add branches and actions

        if terminal in terminals_to_skip:
            text += [f"  | token_{terminal} -> _parse buf w m stack"]
        else:
            text += [f"  | token_{terminal} ->"]

            if need_print:
                text += [f"""    Printf.printf "{terminal} ▷ %s\\n" (Sedlexing.Utf8.lexeme buf); """]
            
            # text += [f"  | token_{terminal} -> Some {i}"]
            i = indices.index(terminal)
            if terminal in calls:
                text += [text_action_call.format(i)]
            elif terminal in returns:
                text += [text_action_ret.format(i)]
            else:
                text += [text_action_plain.format(i)]

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
             "  let w, forest = _parse lexbuf [] [1] [] in",
             "  w, forest"]

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

indices : list[str] = [
    "LeftRoundBracket"
    , "RightRoundBracket"
    , "Rightarrow"
    , "Dot"
    , "TwoDots"
    , "Colon"
    , "Semicolon"
    , "LeftAngleBracket"
    , "RightAngleBracket"
    , "Char"
    , "Comment"
    , "Nonterminal"
    , "Reg_op"
    , "Terminal"
    , "NotStart"
    , "RightSquareBracket"
    , "Action"
    , "Ignore"
    , "VerticalBar"]
indices += ["Others", "WS", "LeftCurlyBracket", "RightCurlyBracket", "At"]


calls = ["LeftCurlyBracket", "LeftRoundBracket"]
returns = ["RightCurlyBracket", "RightRoundBracket"]

if __name__ == "__main__":

    gen_lexer(terminals, calls, returns, indices, need_print=True, terminals_to_skip=["WS", "Comment"])

    