(* NOTE - Tagged CFGs *)

open Core
open Utils

type terminal = string [@@deriving equal, show, compare, sexp]
type variable = string [@@deriving equal, show, compare, sexp]

type term =
  | Trm of terminal
  | Var of variable
  | Mat of (terminal * terms * terminal)
  | Chc of terms
  | Seq of terms
  | Pls of terms
  | Qst of terms
  | Ast of terms
  | Rng of (char * char)
[@@deriving equal, show, compare, sexp]

and terms = term list [@@deriving equal]

type alt_is = terms * int list
type rule_is = variable * alt_is list
type grammar_is = rule_is list

let rec show_terms terms =
  terms |> List.map ~f:show_term |> String.concat ~sep:" "

and show_term term =
  match term with
  | Trm v -> v
  | Var v -> v
  | Mat (call, terms, ret) -> sprintf "<%s %s %s>" call (show_terms terms) ret
  | Chc terms ->
      terms |> List.map ~f:show_term |> String.concat ~sep:"|" |> sprintf "(%s)"
  | Seq terms -> show_terms terms |> sprintf "(%s)"
  | Pls terms -> show_terms terms |> sprintf "(%s)+"
  | Qst terms -> show_terms terms |> sprintf "(%s)?"
  | Ast terms -> show_terms terms |> sprintf "(%s)*"
  | Rng (a, b) -> sprintf "(%c..%c)" a b

type rule = variable * terms list [@@deriving equal, show, compare, sexp_of]
type single_rule = variable * terms [@@deriving equal, show, compare, sexp_of]

module SingleRule = Cmp (struct
  type t = single_rule [@@deriving equal, show, compare, sexp_of]
end)

let show_single_rule (nt, terms) =
  sprintf "%s → %s" nt (show_terms terms)

let show_rule (nt, alts) =
  let s_alts = alts |> List.map ~f:show_terms |> String.concat ~sep:"\n  | " in
  sprintf "%s:\n    %s" nt s_alts

type grammar = rule list [@@deriving equal]

let show_grammar (g : grammar) =
  g |> List.map ~f:show_rule |> String.concat ~sep:" ;\n" |> sprintf "%s ;"

type alt_act = terms * (string option) 

type rule_act = variable * alt_act list

type grammar_act = rule_act list * (string option)
