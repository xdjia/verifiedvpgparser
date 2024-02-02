(* NOTE - tcfg -> simple form -> vpg with semantic actions *)

open Core
open TCFG
open Utils
open SimpleForm

let flag_debug = false
let flag_save_re_in_name = false

let debug s = if flag_debug then print_endline (Printf.sprintf "▶%s◀" s) else ()

module TCFG2VPG : sig
  val desugar_re : TCFG.rule list -> TCFG.grammar
  val tcfg2simpleform : TCFG.grammar_is -> SimpleForm.grammar_is
end = struct
  open SimpleForm

  let index_re_var = ref 0

  let create_re_var name =
    index_re_var := !index_re_var + 1;
    (* sprintf "_L_%s" name *)
    let name = String.map name ~f:(function ' ' -> '_' | c -> c) in
    if flag_save_re_in_name then sprintf "vv%d_%s" !index_re_var name
    else sprintf "vv%d" !index_re_var

  let create_group_var name =
    index_re_var := !index_re_var + 1;
    (* sprintf "_L_%s" name *)
    (* sprintf "vv%d" !index_re_var *)
    sprintf "vv%d_%s" !index_re_var name
  (* sprintf "_g_%d" !index_re_var *)

  let merge_neighor_pls (alt : TCFG.terms) =
    let rec f alt1 alt2 : TCFG.terms =
      match alt2 with
      | [] | [ _ ] -> alt1 @ alt2
      | term1 :: term2 :: alt2' -> (
          match (term1, term2) with
          | Pls t1, Pls t2 ->
              if TCFG.equal_terms t1 t2 then f alt1 (term2 :: alt2')
              else f (alt1 @ [ term1 ]) (term2 :: alt2')
          | _ -> f (alt1 @ [ term1 ]) (term2 :: alt2'))
    in
    f [] alt

  module Key_TERM = Cmp (struct
    type t = TCFG.term [@@deriving equal, compare, sexp_of, show]
  end)

  module TERMS = Cmp (struct
    type t = TCFG.terms [@@deriving equal, compare, sexp_of, show]
  end)

  (* NOTE - Regular term -> nonterminal *)
  let table_term2var = ref (Map.empty (module Key_TERM))

  let rm_dup_alts alts =
    List.fold alts ~init:[] ~f:(fun acc alt ->
        if List.mem acc alt ~equal:TCFG.equal_terms then acc else alt :: acc)

  let _desugar_re_one_round (alt : TCFG.terms) new_rules =
    (* NOTE - Desugar tcfg, shallow, one round. *)
    let rec f alts alt2 (new_rules : TCFG.grammar) =
      (* NOTE - INV: alt = alt1 @ alt2 *)
      match alt2 with
      | [] ->
          debug
            (sprintf "sub alts are\n %s"
               (List.map alts ~f:TCFG.show_terms |> String.concat ~sep:";"));
          (alts, new_rules)
      | term :: alt2' -> (
          match term with
          | Qst terms ->
              let alts1, rules1 = f alts alt2' new_rules in
              let alts2, rules2 = f alts (terms @ alt2') rules1 in
              (alts1 @ alts2, rules2)
          | Ast terms ->
              let alts1, rules1 = f alts alt2' new_rules in
              let alts2, rules2 = f alts ([ Pls terms ] @ alt2') rules1 in
              (alts1 @ alts2, rules2)
          | Chc terms ->
              let res, rules =
                terms
                |> List.fold ~init:([], new_rules) ~f:(fun (acc, rules) term1 ->
                       let alts', rules = f alts (term1 :: alt2') rules in
                       (acc @ alts', rules))
              in
              (res, rules)
          | Seq terms -> f alts (terms @ alt2') new_rules
          | Pls terms -> (
              debug (sprintf "Expand an Pls: %s" (TCFG.show_term term));
              match terms with
              | [] -> f alts alt2' new_rules
              | _ -> (
                  match Map.find !table_term2var term with
                  | None ->
                      let pls_var =
                        match terms with
                        | [ Trm t ] -> create_re_var (t ^ "+")
                        | _ ->
                            create_re_var
                              (sprintf "(%s)+" (TCFG.show_terms terms))
                      in
                      table_term2var :=
                        Map.add_exn !table_term2var ~key:term ~data:pls_var;
                      let pls_rule =
                        (pls_var, [ terms; terms @ [ Var pls_var ] ])
                      in
                      f
                        (List.map alts ~f:(fun alt -> alt @ [ Var pls_var ]))
                        alt2' (pls_rule :: new_rules)
                  | Some pls_var ->
                      f
                        (List.map alts ~f:(fun alt -> alt @ [ Var pls_var ]))
                        alt2' new_rules))
          | Mat (call, terms, ret) -> (
              match terms with
              | [] | [ Var _ ] ->
                  f
                    (List.map alts ~f:(fun alt -> alt @ [ term ]))
                    alt2' new_rules
              | [ Ast terms ] ->
                  let alts1, rules1 =
                    f alts (Mat (call, [], ret) :: alt2') new_rules
                  in
                  let alts2, rules2 =
                    f alts ([ Mat (call, [ Pls terms ], ret) ] @ alt2') rules1
                  in
                  (alts1 @ alts2, rules2)
              | _ -> (
                  let term1 = Seq terms in
                  match Map.find !table_term2var term1 with
                  | None ->
                      let new_var =
                        sprintf "(%s)" (TCFG.show_terms terms) |> create_re_var
                      in
                      let () =
                        table_term2var :=
                          Map.add_exn !table_term2var ~key:term1 ~data:new_var
                      in
                      let nterm = Mat (call, [ Var new_var ], ret) in
                      let new_rule = (new_var, [ terms ]) in
                      f
                        (List.map alts ~f:(fun alt -> alt @ [ nterm ]))
                        alt2' (new_rule :: new_rules)
                  | Some new_var ->
                      let nterm = Mat (call, [ Var new_var ], ret) in
                      f
                        (List.map alts ~f:(fun alt -> alt @ [ nterm ]))
                        alt2' new_rules))
          | (Trm _ | Var _ | Rng _) as term ->
              (* FIXME - add support for Range *)
              let alts' = List.map alts ~f:(fun alt -> alt @ [ term ]) in
              f alts' alt2' new_rules)
    in
    debug (sprintf "alt is\n %s" (TCFG.show_terms alt));
    let alts, new_rules = f [ [] ] alt new_rules in
    debug
      (sprintf "alt is desugared to\n %s"
         (List.map alts ~f:TCFG.show_terms |> String.concat ~sep:";"));
    (List.map alts ~f:merge_neighor_pls, new_rules)

  let desugar_single_re g =
    g
    |> List.fold ~init:[] ~f:(fun rules (nt, alts) ->
           match alts with
           | [ [ Pls terms ] ] -> (nt, [ terms; terms @ [ Var nt ] ]) :: rules
           | [ [ Ast terms ] ] ->
               (nt, [ []; terms; terms @ [ Var nt ] ]) :: rules
           | _ -> (nt, alts) :: rules)

  let desugar_re_one_round g : TCFG.grammar =
    g
    (* TODO - A -> c+ no new var *)
    |> desugar_single_re
    |> List.fold ~init:[] ~f:(fun new_rules (nt, alts) ->
           debug (sprintf "old rule is\n  %s" (TCFG.show_rule (nt, alts)));
           let alts', new_rules =
             alts
             |> List.fold ~init:([], new_rules) ~f:(fun (acc, new_rules) alt ->
                    let new_alts, new_rules =
                      _desugar_re_one_round alt new_rules
                    in

                    (acc @ new_alts, new_rules))
           in

           debug (sprintf "new rule is\n  %s" (TCFG.show_rule (nt, alts')));
           (nt, rm_dup_alts alts') :: new_rules)

  let num_rules g =
    List.length (g |> List.map ~f:(fun (_, alts) -> alts) |> List.concat)

  let rec exists_re terms =
    List.exists terms ~f:(function
      | Trm _ | Var _ -> false
      | Mat (_, terms, _) -> exists_re terms
      | _ -> true)

  let desugar_re g : TCFG.grammar =
    let rec f g =
      let g' = desugar_re_one_round g in
      debug (Printf.sprintf "▷ Expand RE; |G|=%d" (num_rules g));
      if List.exists g' ~f:(fun (_, alts) -> List.exists alts ~f:exists_re) then
        f g'
      else g'
    in
    f g

  let rec group_terms_in_mat table_group_rules g =
    let new_rules = ref [] in
    let add_terms terms =
      match Map.find !table_group_rules terms with
      | None ->
          let nt = create_group_var (TCFG.show_terms terms) in
          table_group_rules :=
            Map.add_exn !table_group_rules ~key:terms ~data:nt;
          new_rules :=
            !new_rules
            @ group_terms_in_mat table_group_rules [ (nt, [ (terms, []) ]) ];
          nt
      | Some nt -> nt
    in
    let g' =
      g
      |> List.map ~f:(fun (nt, alts) ->
             let new_alts =
               alts
               |> List.map ~f:(fun (alt, is) ->
                      let alt =
                        List.map alt ~f:(fun term ->
                            match term with
                            | Trm v -> STrm v
                            | Var v -> SVar v
                            | Mat (call, [], ret) -> SMat (call, "_E", ret)
                            | Mat (call, terms, ret) -> (
                                match terms with
                                | [ Var nt ] -> SMat (call, nt, ret)
                                | _ ->
                                    let nt = add_terms terms in
                                    SMat (call, nt, ret))
                            | Chc v ->
                                err
                                  (sprintf "▷ Include Chc rule %s -> %s\n" nt
                                     (TCFG.show_term term))
                            | Seq v ->
                                err
                                  (sprintf "▷ Include Seq rule %s -> %s\n" nt
                                     (TCFG.show_term term))
                            | Pls v ->
                                err
                                  (sprintf "▷ Include Pls rule %s -> %s\n" nt
                                     (TCFG.show_term term))
                            | Qst v ->
                                err
                                  (sprintf "▷ Include Qst rule %s -> %s\n" nt
                                     (TCFG.show_term term))
                            | Ast v ->
                                err
                                  (sprintf "▷ Include Ast rule %s -> %s\n" nt
                                     (TCFG.show_term term))
                            | Rng v ->
                                err
                                  (sprintf "▷ Include Rng rule %s -> %s\n" nt
                                     (TCFG.show_term term)))
                      in
                      (alt, is))
             in
             (nt, new_alts))
    in
    g' @ !new_rules

  let tcfg2simpleform (tcfg_is : TCFG.grammar_is) : SimpleForm.grammar_is =
    (* NOTE - convert TCFG to simple forms *)
    let table_group_rules =
      (* NOTE - Group terms in Mat to a new nonterminal *)
      ref (Map.empty (module TERMS))
    in
    let tcfg_is = group_terms_in_mat table_group_rules tcfg_is in
    tcfg_is
end

(* module VALIDATOR = struct
     (* FIXME - Todo. *)
     open TCFG2VPG

     let hds l =
       match l with [] -> l | _ -> l |> List.rev |> List.tl_exn |> List.rev

     let detectCycle (g : TCFGM.grammar) nt_in =
       let ntSet = Set.empty (module String) in
       let rec f nt ntSet =
         let d ntSet alt =
           match hds alt with
           | [] -> false
           | l ->
               let h t = match t with Var nt -> f nt ntSet | _ -> false in
               List.exists l ~f:h
         in
         if Set.mem ntSet nt then true
         else
           let ntSet = Set.add ntSet nt in
           let _, alts =
             List.find_exn g ~f:(fun (nt', _) -> equal_string nt' nt)
           in
           List.exists alts ~f:(d ntSet)
       in
       f nt_in ntSet
   end *)
