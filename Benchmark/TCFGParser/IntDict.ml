open CoqParseTree
open CoqVPG
open Utils
open Core
open SimpleForm
open TCFGParseTree

let flag_debug = false

let debug s = if flag_debug then print_endline (Printf.sprintf "▶%s◀" s) else ()

module type PreIntDict = sig
  val vpg : CoqVPG.rules

  val pda :
    (TransitionKey.t, me, TransitionKey.comparator_witness) Base.Map.t

  val states : (me, ME.comparator_witness) Base.Set.t
  val epda : (ETransitionKey.t * (ve * t_action)) list
  val eps_trans : (me * (ve * t_action)) list
  val estates : ve list

  val vpg2action :
    ( CoqVPG.rule,
      t_action,
      CoqVPG.Rule.comparator_witness )
    Base.Map.t

  val sym2int : (symbol, int, Symbol.comparator_witness) Base.Map.t
  val int2sym : (int, symbol, Core.Int.comparator_witness) Base.Map.t
  val l0 : SimpleForm.variable
  val i2rule : (int, TCFG.single_rule, Core.Int.comparator_witness) Map_intf.Map.t

end

module type IntDict = sig
  val int_pda : (IntVPG.Int3.t * int) list
  val int_trans_eps : (int * (int * t_action)) list
  val int_epda : ((int * int * int) * (int * t_action)) list
  (* val int2actions : (int * SimpleForm.terms list) list *)

  val int2estate :
    (int, CoqParseTree.ve, Core.Int.comparator_witness) Base.Map.t

  val int2sym : (int, symbol, Core.Int.comparator_witness) Base.Map.t

  val int2state :
    (int, CoqParseTree.me_list, Core.Int.comparator_witness) Base.Map.t

  val i2rule : (int, TCFG.single_rule, Core.Int.comparator_witness) Map_intf.Map.t
end

module IntDict (Info : PreIntDict) : IntDict = struct
  include Info

  type t_g = (vpg_var * CoqVPG.alt) list [@@deriving show]
  type t_trans_eps = (me * ve) list [@@deriving show]

  let () = debug (sprintf "L0=%s" (CoqVPG.show_vpg_var (V0 (str2cl l0))))
  let r0 = CoqParseTree.PlnE (V0 (str2cl l0), (c0), V0 (str2cl l0))

  let m0 =
    CoqParseTree.PlnCME (CoqParseTree.Coq_vc_set.singleton (None, r0))

  type int_tagged = int * symbol [@@deriving show]

  let show_int2sym int2sym =
    int2sym |> Map.to_alist
    |> List.map ~f:show_int_tagged
    |> String.concat ~sep:";"
    |> sprintf "Map.of_alist_exn (module Int) [%s]"

  let state_list =
    let state_list1 = Set.to_list states in
    let rec _split l1 l2 =
      match l2 with
      | x :: l2' -> if equal_me x m0 then l1 @ l2' else _split (x :: l1) l2'
      | [] -> raise (Invalid_argument "m0 is not in the state list.")
    in
    m0 :: _split [] state_list1

  let state2int =
    state_list
    |> List.mapi ~f:(fun i x -> (x, i + 1))
    |> Map.of_alist_exn (module ME)

  type int_me_list = int * me_list [@@deriving show]

  let int2state =
    state_list
    |> List.mapi ~f:(fun i x -> (i + 1, cme2cmel x))
    |> Map.of_alist_exn (module Int)

  let show_int2state int2state =
    int2state |> Map.to_alist
    |> List.map ~f:show_int_me_list
    |> String.concat ~sep:";"
    |> sprintf "Map.of_alist_exn [%s]"

  type int3int = ((int * int * int) * int) list [@@deriving show]

  let int_pda : (IntVPG.Int3.t * int) list =
    let m2i m = Map.find_exn state2int m in
    let s2i s = Map.find_exn sym2int s in
    pda |> Map.to_alist
    |> List.map ~f:(fun ((m, _m, i), m') ->
           let i_m =
             match _m with
             | None -> 0
             | Some _m -> (
                 match i with Call _ | Plain _ -> 0 | Ret _ -> m2i _m)
           in
           ((m2i m, i_m, s2i i), m2i m'))

  let () =
    match int_pda |> Map.of_alist (module IntVPG.Int3) with
    | `Ok _ -> ()
    | `Duplicate_key i3 ->
        debug (IntVPG.Int3.show i3);
        int_pda
        |> List.iter ~f:(fun (key, data) ->
               if IntVPG.equal_int3 key i3 then debug (sprintf "%d" data));
        exit 1

  let estate2int =
    estates
    |> List.mapi ~f:(fun i r -> (r, i + 1))
    |> Map.of_alist_exn (module VE)

  type t_int_ve = int * ve [@@deriving show]

  let int2estate =
    estates
    |> List.mapi ~f:(fun i r -> (i + 1, r))
    |> Map.of_alist_exn (module Int)

  let show_int2estate int2estate =
    int2estate |> Map.to_alist |> List.map ~f:show_t_int_ve
    |> String.concat ~sep:";"
    |> sprintf "Map.of_alist_exn (module Int) [%s]"

  type t_int2funs = (int * SimpleForm.terms list) list [@@deriving show]

  (* let int2actions : (int * SimpleForm.terms list) list =
       int2estate |> Map.to_alist
       |> List.filter_map ~f:(fun (i, e) ->
              match GrammarTools.edge2rule e with
              | None -> None
              | Some r -> (
                  match Map.find vpg2action r with
                  | None -> None
                  | Some terms -> Some (i, terms)))

     let map_int2funs = int2actions |> Map.of_alist_exn (module Int)
     let i2action i = Map.find_exn map_int2funs i *)

  let int_epda : ((int * int * int) * (int * t_action)) list =
    let m2i m = Map.find_exn state2int m in
    let r2i s = Map.find_exn estate2int s in
    epda
    |> List.map ~f:(fun ((r, rOp, m), (r', actions)) ->
           let i_r = match rOp with None -> 0 | Some _r -> r2i (Retv _r) in
           ((r2i r, i_r, m2i m), (r2i r', actions)))

  (* let int_epda =
     List.fold int_epda ~init:[] ~f:(fun acc one_map ->
         let key, (i, actions) = one_map in
         match List.find acc ~f:(fun (x, _) -> IntVPG.equal_int3 x key) with
         | None -> one_map :: acc
         | Some (_, (i', actions')) ->
             debug "Found dup key";
             if Int.equal i i' && equal_pre_pts actions actions' then acc
             else
               err
                 (sprintf "Duplicate maps: %s %s %s" (IntVPG.show_int3 key)
                    (show_pre_pts actions) (show_pre_pts actions'))) *)

  let int_trans_eps : (int * (int * t_action)) list =
    let m2i m = Map.find_exn state2int m in
    let r2i s = Map.find_exn estate2int s in
    eps_trans
    |> List.map ~f:(fun (m, (r, actions)) -> (m2i m, (r2i r, actions)))

  type int2_list = (int * int) list [@@deriving show]

end
