open Core
open Utils
open SimpleForm.SimpleForm
open TCFGParseTree
open CoqVPG
open CoqParseTree
open CoqParseTree.Show
open CParser

let flag_debug = false

let debug s = if flag_debug then print_endline (Printf.sprintf "▶%s◀" s) else ()

let advance_l0 l0 vpg =
  let rec f g1 g2 =
    match g2 with
    | [] -> err "L0 not found"
    | (nt, alts) :: g2' ->
        if String.equal nt l0 then ((nt, alts) :: g1) @ g2'
        else f (g1 @ [ (nt, alts) ]) g2'
  in
  f [] vpg

module type GrammarInfo = sig
  include CoqParserType

  val grammar_name : string

  (* NOTE - get the index of a TCFG rule *)
  val rule2i :
    (TCFG.single_rule, int, TCFG.SingleRule.comparator_witness) Map_intf.Map.t

  (* NOTE - get the i-th TCFG rule *)
  val i2rule :
    (int, TCFG.single_rule, Core.Int.comparator_witness) Map_intf.Map.t

  val vpg : rules
  val vpg2action : (CoqVPG.rule, t_action, Rule.comparator_witness) Base.Map.t
  val plainSyms : symbol list
  val callSyms : symbol list
  val retSyms : symbol list
  val l0 : variable
  val tcfg_nts : (variable, Variable.comparator_witness) Base.Set.t
  val lookup_actions : ve -> int list
end

module ExpandRules (Info : sig
  val sform :
    (variable, alt_is list, Variable.comparator_witness) Map_intf.Map.t
end) : sig
  val table_nt2rules :
    ( variable,
      (alt * int list) list,
      Variable.comparator_witness )
    Map_intf.Map.t

  val table_terms2nt : (terms, string, Terms.comparator_witness) Base.Map.t
end = struct
  open Info

  let table_nt2rules :
      ( variable,
        (CoqVPG.alt * int list) list,
        Variable.comparator_witness )
      Base.Map.t
      ref =
    ref (Map.empty (module Variable))

  let table_terms2nt : (terms, string, Terms.comparator_witness) Base.Map.t ref
      =
    ref (Map.empty (module Terms))

  let fetch_nt terms =
    match Map.find !table_terms2nt terms with
    | Some nt -> nt
    | None ->
        let nt =
          match terms with
          | [] -> "_E"
          | _ -> sprintf "_X%d" (Map.length !table_terms2nt)
        in
        table_terms2nt := Map.add_exn !table_terms2nt ~key:terms ~data:nt;
        nt

  type int_list = int list [@@deriving equal]

  let add_rule_to_table terms ((alt, rules) : alt * int list) : unit =
    table_nt2rules :=
      Map.update !table_nt2rules terms ~f:(function
        | None -> [ (alt, rules) ]
        | Some rs -> (
            (* NOTE - remove duplicates *)
            List.find rs ~f:(fun (alt', rules') ->
                equal_alt alt alt' && not (equal_int_list rules rules'))
            |> function
            | None -> rs @ [ (alt, rules) ]
            | Some _ -> err "Confliction!"))

  let visited = ref []

  let split_by_1st_nt terms =
    (* NOTE - Split terms to [terminals] [NT, ...] *)
    let rec _f terms_l terms_r =
      match terms_r with
      | [] -> (terms_l, terms_r)
      | SVar _ :: _ -> (terms_l, terms_r)
      | x :: terms_r' -> _f (terms_l @ [ x ]) terms_r'
    in
    _f [] terms

  let rm_E (terms : terms) =
    List.filter terms ~f:(function
      | SVar nt when String.equal nt "_E" -> false
      | _ -> true)

  let rec expand_node depth terms (nodes : terms) (rules : int list) : unit =
    (* NOTE - For the rule `terms -> nodes`, expand nodes until the first term is a terminal or mat. *)
    debug
      (sprintf "terms=%s; nodes=%s"
         (SimpleForm.Show.show_terms terms)
         (SimpleForm.Show.show_terms nodes));
    let nt = match terms with [ SVar nt ] -> nt | _ -> fetch_nt terms in
    if
      List.mem !visited (nt, nodes) ~equal:(fun (nt1, terms1) (nt2, terms2) ->
          equal_variable nt1 nt2 && equal_terms terms1 terms2)
    then ()
    else (
      visited := (nt, nodes) :: !visited;
      match nodes with
      | [] -> add_rule_to_table nt (CoqVPG.Alt_Epsilon, rules)
      | _ -> (
          let nodes_l, nodes_r = split_by_1st_nt nodes in
          match nodes_l with
          | [] -> (
              match nodes_r with
              | SVar nt' :: nodes_r ->
                  Map.find_exn sform nt'
                  |> List.iter ~f:(fun (alt, is) ->
                         let action = (nt', alt) in
                         expand_node (depth + 1) terms
                           (rm_E alt @ nodes_r)
                           (is @ rules))
              | _ -> err "impl err")
          | leaf :: nodes_l ->
              let terms2 = nodes_l @ nodes_r in
              let nt2 =
                match terms2 with [ SVar nt2 ] -> nt2 | _ -> fetch_nt terms2
              in
              let rule =
                match leaf with
                (* FIXME - nt2 should be symbol before this function *)
                | STrm c -> Alt_Linear (Plain (str2cl c), V0 (str2cl nt2))
                | SMat (a, nt1, b) ->
                    Alt_Match
                      (str2cl a, str2cl b, V0 (str2cl nt1), V0 (str2cl nt2))
                (* FIXME - SVar shouldn't appear; change the type of leaf *)
                | SVar _ -> err "FIXME"
              in
              add_rule_to_table nt (rule, rules);
              let () =
                match leaf with
                | SMat (a, nt1, b) ->
                    expand_node (depth + 1) [ SVar nt1 ] [ SVar nt1 ] []
                | _ -> ()
              in
              expand_node (depth + 1) terms2 terms2 []))

  let () =
    (* NOTE - Build VPG rules and actions *)
    sform
    |> Map.iteri ~f:(fun ~key:nt ~data:_ ->
           expand_node 0 [ SVar nt ] [ SVar nt ] [])

  let table_terms2nt = !table_terms2nt
  let table_nt2rules = !table_nt2rules

  let () =
    (* NOTE - Print info about VPG rules *)
    debug (sprintf "|table_terms2nt|=%d" (Map.length table_terms2nt));
    debug (sprintf "|table_nt2rules|=%d" (Map.length table_nt2rules));
    debug
      (sprintf "|table_nt2rules with actions|=%d"
         (table_nt2rules
         |> Map.fold ~init:0 ~f:(fun ~key:nt ~data:alts acc ->
                acc
                + List.count alts ~f:(fun (_, actions) ->
                      List.length actions <> 0))));
    debug
      (sprintf "|table_nt2rules without actions|=%d"
         (table_nt2rules
         |> Map.fold ~init:0 ~f:(fun ~key:nt ~data:alts acc ->
                acc
                + List.count alts ~f:(fun (_, actions) ->
                      List.length actions = 0))));
    debug
      (table_nt2rules |> Map.to_alist
      |> List.map ~f:(fun (nt, _) -> nt)
      |> String.concat ~sep:";")
end

module GInfoTools = struct
  let get_tcfg_nts tcfg =
    let rec get_nts_in_term (term : TCFG.term) : string list =
      match term with
      | Trm v -> []
      | Var v -> [ v ]
      | Mat (_, terms, _)
      | Chc terms
      | Seq terms
      | Pls terms
      | Qst terms
      | Ast terms ->
          List.map terms ~f:get_nts_in_term |> List.concat
      | Rng (a, b) -> []
    and get_nts_in_terms terms =
      terms |> List.map ~f:get_nts_in_term |> List.concat
    in
    tcfg
    |> List.map ~f:(fun (l, terms) ->
           let ls = terms |> List.map ~f:get_nts_in_terms |> List.concat in
           l :: ls)
    |> List.concat
    |> Set.of_list (module String)

  let add_index_to_grammar g =
    g
    |> List.fold ~init:(0, []) ~f:(fun (i, g) (nt, alts) ->
           let i, altsi =
             List.fold alts ~init:(i, []) ~f:(fun (i, altsi) alt ->
                 (i + 1, (alt, [ i ]) :: altsi))
           in
           (i, (nt, altsi) :: g))
    |> snd |> List.rev
end

module GInfo (Info : sig
  val grammar_name : string
  val tcfg : TCFG.grammar
end) : GrammarInfo = struct
  open Info
  open DeSugRe.TCFG2VPG
  open GInfoTools

  let grammar_name = grammar_name
  let tcfg_nts = get_tcfg_nts tcfg

  let () =
    (* NOTE - Print all nonterminals in tcfg *)
    debug
      (sprintf "nonterminals are %s"
         (String.concat ~sep:";" (Set.to_list tcfg_nts)))

  let () =
    (* NOTE - Print the number of rules in tcfg *)
    let rec sum_int_list sum l =
      match l with [] -> sum | i :: l' -> sum_int_list (sum + i) l'
    in
    debug
      (sprintf "#tcfg rules=%d"
         (tcfg
         |> List.map ~f:(fun (_, alts) -> List.length alts)
         |> sum_int_list 0))

  let l0 = tcfg |> List.hd_exn |> fst
  let desug = desugar_re tcfg

  let rule2i =
    let len, lmap =
      desug
      |> List.fold ~init:(0, []) ~f:(fun (len, lmap) (nt, alts) ->
             alts
             |> List.fold ~init:(len, lmap) ~f:(fun (len, lmap) alt ->
                    (* FIXME - not sure why below is needed *)
                    if
                      List.exists lmap ~f:(fun (r, _) ->
                          TCFG.equal_single_rule r (nt, alt))
                    then (len, lmap)
                    else (len + 1, ((nt, alt), len) :: lmap)))
    in
    Map.of_alist_exn (module TCFG.SingleRule) lmap

  let i2rule =
    rule2i |> Map.to_alist
    |> List.map ~f:(fun (x, y) -> (y, x))
    |> Map.of_alist_exn (module Int)

  (** Print desugared grammar *)
  let () =
    debug
      (sprintf "|Desugared Tagged CFG|=%d"
         (List.fold ~f:( + ) ~init:0
            (List.map desug ~f:(fun (_, alts) -> List.length alts))));
    let path = Filename.concat "tcfgs" (grammar_name ^ ".tcfg") in
    print_endline (sprintf "Desugared Tagged CFG is written to %s" path);
    Out_channel.write_all path ~data:(TCFG.show_grammar desug)

  let sform = desug |> add_index_to_grammar |> tcfg2simpleform |> advance_l0 l0

  (** Print simple forms *)
  let () =
    debug (sprintf "|Simple Form|=%d" (List.length sform));
    debug (sprintf "Simple Form");
    debug (show_grammar_is sform)

  (** Add the rule _E -> ε *)
  let sform =
    let sform = Map.of_alist_exn (module Variable) sform in
    match Map.find sform "_E" with
    | None -> Map.add_exn sform ~key:"_E" ~data:[ ([], []) ]
    | Some _ -> sform

  open ExpandRules (struct
    let sform = sform
  end)

  let r0 = (V0 (str2cl l0), Alt_Linear (Plain c0, V0 (str2cl l0)))

  let vpg : rules =
    r0
    :: (table_nt2rules |> Map.to_alist
       |> List.map ~f:(fun (nt, alts) ->
              List.map alts ~f:(fun (alt, _) -> (CoqVPG.V0 (str2cl nt), alt)))
       |> List.concat)

  module G : VPG = struct
    let coq_L_0 = V0 (str2cl l0)
    let coq_P = vpg
  end

  module CParser = CParser (G)
  include CParser

  (** Actions are just TCFG rules (each rule is typed as `terms`) *)
  let vpg2action : (CoqVPG.rule, int list, Rule.comparator_witness) Base.Map.t =
    (r0, [])
    :: (table_nt2rules |> Map.to_alist
       |> List.map ~f:(fun (nt, alts) ->
              List.map alts ~f:(fun (alt, action) ->
                  ((CoqVPG.V0 (str2cl nt), alt), action)))
       |> List.concat)
    |> Map.of_alist_exn (module Rule)

  let r2action =
    Hashtbl.of_alist_exn ~growth_allowed:false ~size:(Map.length vpg2action)
      (module HashRule)
      (Map.to_alist vpg2action)

  let lookup_actions e : int list =
    match GrammarTools.edge2rule e with
    | None -> []
    | Some r -> Hashtbl.find_exn r2action r

  let callSyms, plainSyms, retSyms =
    let pickCall acc alt =
      List.fold alt ~init:acc ~f:(fun acc term ->
          match term with
          | TCFG.Mat (s, _, _) ->
              let sym = Call (str2cl s) in
              if List.mem acc sym ~equal:equal_symbol then acc else sym :: acc
          | _ -> acc)
    in
    let pickPlain acc alt =
      List.fold alt ~init:acc ~f:(fun acc term ->
          match term with
          | TCFG.Trm s ->
              let sym = Plain (str2cl s) in
              if List.mem acc sym ~equal:equal_symbol then acc else sym :: acc
          | _ -> acc)
    in
    let pickRet acc alt =
      List.fold alt ~init:acc ~f:(fun acc term ->
          match term with
          | TCFG.Mat (_, _, s) ->
              let sym = Ret (str2cl s) in
              if List.mem acc sym ~equal:equal_symbol then acc else sym :: acc
          | _ -> acc)
    in
    let getSyms pick =
      List.fold desug ~init:[] ~f:(fun acc (_, alts) ->
          List.fold alts ~init:acc ~f:(fun acc alt -> pick acc alt))
    in
    ( getSyms pickCall |> List.rev,
      getSyms pickPlain |> List.rev,
      getSyms pickRet |> List.rev )

  let vpg2action : (CoqVPG.rule, t_action, Rule.comparator_witness) Base.Map.t =
    (r0, [||])
    :: (table_nt2rules |> Map.to_alist
       |> List.map ~f:(fun (nt, alts) ->
              List.map alts ~f:(fun (alt, action) ->
                  ((CoqVPG.V0 (str2cl nt), alt), Array.of_list action)))
       |> List.concat)
    |> Map.of_alist_exn (module Rule)

  (** Print the number of terminals *)
  let () =
    print_endline
      (sprintf "|Terminals|=%d"
         (List.length callSyms + List.length plainSyms + List.length retSyms))
  let syms = plainSyms @ callSyms @ retSyms

  let () =
    List.iteri syms ~f:(fun i x ->
      print_endline (Printf.sprintf "Sym %d %s\n" i (show_symbol x)))
end
