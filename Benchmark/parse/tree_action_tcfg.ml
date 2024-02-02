open Printf
open TCFGParser.TCFG
open TCFGParser.Utils
open TCFGParser

type value_stack =
  | Stack_op of string
  | Stack_action of string
  | Stack_token of (string * string)
  | Stack_term of TCFG.term
  | Stack_terms of TCFG.terms
  | Stack_call of string
  | Stack_return of string
  | Stack_alt of TCFG.alt_act
  | Stack_alts of TCFG.alt_act list
  | Stack_rule of TCFG.rule_act
  | Stack_rules of TCFG.rule_act list

let add_op op terms =
  match op with
  | "*" -> Stack_term (Ast terms)
  | "+" -> Stack_term (Pls terms)
  | "?" -> Stack_term (Qst terms)
  | _ -> err (sprintf "invalid regular operator: %s" op)

let value_stack_err = "value stack error"

(* NOTE - grammar *)

let grammar_0 = function
  | [ Stack_action s; Stack_rules rules ] -> (rules, Some s)
  | _ -> err value_stack_err

let grammar_1 = function
  | [ Stack_rules rules ] -> (rules, None)
  | _ -> err value_stack_err

(* NOTE - vv4 *)

let vv4_0 = function
  | Stack_rule rule_act :: value_stack ->
      Stack_rules [ rule_act ] :: value_stack
  | _ -> err value_stack_err

let vv4_1 = function
  | Stack_rule rule_act :: Stack_rules rule_acts :: value_stack ->
      Stack_rules (rule_act :: rule_acts) :: value_stack
  | _ -> err value_stack_err

(* NOTE - rule *)

let rule_0 = function
  | Stack_term (Var nt)
    :: _
    :: Stack_alt alt
    :: Stack_alts alts
    :: _ :: value_stack ->
      Stack_rule (nt, alt :: alts) :: value_stack
  | _ -> err "Invalid stack values"

let rule_1 = function
  | Stack_term (Var nt) :: _ :: Stack_alt alt :: _ :: value_stack ->
      Stack_rule (nt, [ alt ]) :: value_stack
  | _ -> err "Invalid stack values"

let vv3_0 = function
  | _ :: Stack_alt alt :: value_stack -> Stack_alts [ alt ] :: value_stack
  | _ -> err "Invalid stack values"

let vv3_1 = function
  | _ :: Stack_alt alt :: Stack_alts alts :: value_stack ->
      Stack_alts (alt :: alts) :: value_stack
  | _ -> err "Invalid stack values"

(* NOTE - ruleBody *)

let ruleBody_0 = function
  | Stack_terms terms :: Stack_token (_, action) :: value_stack ->
      Stack_alts [ (terms, Some action) ] :: value_stack
  | _ -> err "Invalid stack values"

let ruleBody_1 = function
  | Stack_alt alt :: value_stack -> Stack_alts [ alt ] :: value_stack
  | _ -> err "Invalid stack values"

(* NOTE - vv2 *)

let vv2_0 = function
  | Stack_term term :: value_stack -> Stack_terms [ term ] :: value_stack
  | _ -> err "Invalid stack values"

let vv2_1 = function
  | Stack_term term :: Stack_terms terms :: value_stack ->
      Stack_terms (term :: terms) :: value_stack
  | _ -> err "Invalid stack values"

(* NOTE - term *)

let term_0 = function
  | _ :: Stack_terms terms :: _ :: Stack_op op :: value_stack ->
      add_op op terms :: value_stack
  | _ -> err "Invalid stack values"

let term_1 = function
  | _ :: Stack_terms terms :: value_stack ->
      Stack_term (Seq terms) :: value_stack
  | _ -> err "Invalid stack values"

let term_3 value_stack = value_stack
let term_4 value_stack = value_stack

let term_5 = function
  | Stack_token (name, lexeme) :: Stack_op op :: value_stack ->
      add_op op [ Var lexeme ] :: value_stack
  | _ -> err "Invalid stack values"

let term_6 = function
  | Stack_token (name, lexeme) :: value_stack ->
      Stack_term (Var lexeme) :: value_stack
  | _ -> err "Invalid stack values"

let term_7 = function
  | Stack_token (name, lexeme) :: Stack_op op :: value_stack ->
      add_op op [ Trm lexeme ] :: value_stack
  | _ -> err "Invalid stack values"

let term_8 = function
  | Stack_token (name, lexeme) :: value_stack ->
      Stack_term (Trm lexeme) :: value_stack
  | _ -> err "Invalid stack values"

(* NOTE - vv1 *)
