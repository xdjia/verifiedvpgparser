open Utils

let str2cl s = s |> String.to_seq |> List.of_seq

open Core

let cl2str = String.of_char_list

module Basic = struct
  type terminal = [%import: CoqParser.VerifiedParser.Basic.terminal]
  [@@deriving equal, show, compare, sexp_of]

  type variable = [%import: CoqParser.VerifiedParser.Basic.variable]
  [@@deriving equal, show, compare, sexp_of]
end

type vpg_var = [%import: CoqParser.VerifiedParser.Coq_vpg.vpg_var]
[@@deriving equal, show, compare, sexp_of]

module Vpg_var = Cmp (struct
  type t = vpg_var [@@deriving equal, show, compare, sexp_of]
end)

type symbol = [%import: CoqParser.VerifiedParser.Coq_vpg.symbol]
[@@deriving equal, show, compare, sexp_of]

let show_symbol = function 
| Call s -> "<" ^ (cl2str s)
| Plain s -> cl2str s
| Ret s -> (cl2str s) ^ ">"

let strip_symbol s =
  s |> (function Call s -> s | Plain s -> s | Ret s -> s) |> cl2str

module HashSymbol = struct
  type t = symbol [@@deriving equal, show, compare, sexp_of, equal]

  let hash = Hashtbl.hash
end

module Symbol = Cmp (HashSymbol)

let call s = Call (str2cl s)
let ret s = Ret (str2cl s)
let plain s = Plain (str2cl s)

let code_symbol = function
  | Call s -> sprintf "call \"%s\"" (cl2str s)
  | Plain s -> sprintf "plain \"%s\"" (cl2str s)
  | Ret s -> sprintf "ret \"%s\"" (cl2str s)

type alt = [%import: CoqParser.VerifiedParser.Coq_vpg.alt]
[@@deriving equal, show, compare, sexp_of]

module Alt = Cmp (struct
  type t = alt [@@deriving equal, show, compare, sexp_of]
end)

type rule = vpg_var * alt [@@deriving equal, show, compare, sexp_of]

module Rule = Cmp (struct
  type t = rule [@@deriving equal, show, compare, sexp_of]
end)

module HashRule = struct
  type t = rule [@@deriving equal, show, compare, sexp_of]

  let hash = Hashtbl.hash
end

type rules = rule list [@@deriving equal, show, compare, sexp_of]

let display_vpg_var = function
  | V0 nt -> if String.equal (cl2str nt) "_E" then "ε" else cl2str nt
  | V1 nt -> cl2str nt

let show_coq_vpg rules =
  List.map rules ~f:(fun (nt, alt) ->
      sprintf "%s → %s" (display_vpg_var nt)
        (match alt with
        | Alt_Epsilon -> "ε"
        | Alt_Linear (symbol, vpg_var) ->
            sprintf "%s %s" (show_symbol symbol) (display_vpg_var vpg_var)
        | Alt_Match (a, b, l1, l2) ->
            sprintf "<%s %s %s> %s" (cl2str a) (display_vpg_var l1) (cl2str b)
              (display_vpg_var l2)))
  |> String.concat ~sep:"\n"
