open Utils
open Core

module SimpleForm = struct
  (* NOTE - Simple form:
     Terminal, nonterminal and matching term *)

  let equal_string = String.equal

  type terminal = string [@@deriving show, equal, compare, sexp]
  type variable = string [@@deriving show, equal, compare, sexp]

  module Variable = String

  type term =
    | STrm of terminal
    | SVar of variable
    | SMat of (terminal * variable * terminal)
  [@@deriving show, equal, compare, sexp]

  type terms = term list [@@deriving show, equal, compare, sexp]

  module Terms = Cmp (struct
    type t = terms [@@deriving show, equal, compare, sexp]
  end)

  type alt_is = terms * int list [@@deriving show, equal, compare, sexp]
  type rule_is = variable * alt_is list [@@deriving show, equal, compare, sexp]
  type grammar_is = rule_is list [@@deriving show, equal, compare, sexp]
  type alts = terms list [@@deriving show, equal, compare, sexp]
  type tNFun = variable * int [@@deriving show, equal, compare, sexp]
  type tNFuns = tNFun list [@@deriving show, equal, compare, sexp]
  type altFuns = (terms * tNFuns) list [@@deriving show, equal, compare, sexp]
  type ruleFun = variable * altFuns [@@deriving show, equal, compare, sexp]
  type rule_with_actions = ruleFun list [@@deriving show, equal, compare, sexp]
  type rule = variable * alts [@@deriving show, equal, compare, sexp]
  type grammar = rule list [@@deriving show, equal, compare, sexp]

  let strip_is (g : grammar_is) : grammar =
    List.map g ~f:(function nt, alts -> (nt, alts |> List.map ~f:fst))
end

module Show = struct
  open SimpleForm

  let show_term = function
    | STrm v -> sprintf "%s" v
    | SVar v -> sprintf "%s" (if String.equal v "" then "△" else v)
    | SMat (call, v, ret) -> sprintf "<%s %s %s>" call v ret

  let show_terms terms =
    terms |> List.map ~f:show_term |> String.concat ~sep:"，" |> sprintf "《%s》"

  let show_alts alts =
    alts |> List.map ~f:show_terms |> String.concat ~sep:"，" |> sprintf "%s"

  let show_rule (l, alts) =
    sprintf "%s ->\n     %s" (show_variable l) (show_alts alts)

  let show_action (var, i) = sprintf "(%s^%d)" (show_variable var) i

  let show_falt (alt, f) =
    sprintf "%s@{%s}" (show_terms alt)
      (f |> List.map ~f:show_action |> String.concat ~sep:";")

  let show_falts alts =
    alts |> List.map ~f:show_falt
    |> String.concat ~sep:";\n      "
    |> sprintf "%s"

  let show_rules rs =
    rs |> List.map ~f:(fun r -> show_rule r) |> String.concat ~sep:"\n  "

  let show_frule (l, alts) =
    sprintf "%s ->\n      %s" (show_variable l) (show_falts alts)

  let show_frules (rs : rule_with_actions) =
    rs |> List.map ~f:(fun r -> show_frule r) |> String.concat ~sep:"\n  "
end
