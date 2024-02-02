open TCFGParser.Utils
open Core
open Printf
let token_0 = [%sedlex.regexp? Plus (Chars " \n\t\r")]
let token_1 = [%sedlex.regexp? '0' | '0' .. '9', Star '0' .. '9']
let token_2 = [%sedlex.regexp? ('E' | 'e'), Opt ('+' | '\\' | '-'), token_1]

let token_3 =
  [%sedlex.regexp? Opt '-', token_1, Opt ('.', Plus '0' .. '9'), Opt token_2]

let token_4 = [%sedlex.regexp? Compl ('"' | '\\' | 0x0000 .. 0x001F)]
let token_5 = [%sedlex.regexp? 'A' .. 'Z' | 'a' .. 'z' | '0' .. '9']
let token_6 = [%sedlex.regexp? 'u', token_5, token_5, token_5, token_5]

let token_7 =
  [%sedlex.regexp?
    '\\', ('"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' | token_6)]

let token_8 = [%sedlex.regexp? '"', Star (token_7 | token_4), '"']
let token_9 = [%sedlex.regexp? '{']
let token_10 = [%sedlex.regexp? '}']
let token_11 = [%sedlex.regexp? '[']
let token_12 = [%sedlex.regexp? ']']
let token_13 = [%sedlex.regexp? "true"]
let token_14 = [%sedlex.regexp? "false"]
let token_15 = [%sedlex.regexp? "null"]
let token_16 = [%sedlex.regexp? ',']
let token_17 = [%sedlex.regexp? ':']

let rec _parse buf w=
  match%sedlex buf with
  | token_0 -> _parse buf w
  | token_3 ->
        _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_8 ->
        _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_9 ->
        _parse buf  (Sedlexing.Utf8.lexeme buf::w)
  | token_10 ->
    _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_11 ->
        _parse buf  (Sedlexing.Utf8.lexeme buf::w)
  | token_12 ->
    _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_13 ->
        _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_14 ->
        _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_15 ->
        _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_16 ->
        _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | token_17 ->
        _parse buf (Sedlexing.Utf8.lexeme buf::w)
  | eof -> w
  | _ -> err (sprintf "Lexing error %d, %d\n" (fst (Sedlexing.loc buf)) (snd (Sedlexing.loc buf))) 

let w =
  let in_channel = In_channel.create (Sys.get_argv ()).(1) in
  let lexbuf = Sedlexing.Utf8.from_channel in_channel in
  (* NOTE - Number 1 represents the initial state *)
  _parse lexbuf []