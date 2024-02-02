open Core
open Utils
open SimpleForm.SimpleForm
open TCFGParseTree
open CoqVPG
open CoqParseTree
open CoqParseTree.Show
open CParser
open Translation

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

let show_me = ShowCoqM.show_me
let show_symbol = ShowCoqVPG.show_symbol
let show_VE = ShowCoqV.show_VE

let show_eb_op ebop =
  match ebop with None -> "None" | Some eb -> show_retEdge eb

let show_me_op m = match m with None -> "None" | Some m -> show_me m
let show_VE_op ve = match ve with None -> "None" | Some ve -> show_VE ve

let show_Option_me_Key me_op =
  match me_op with None -> "None" | Some me -> show_me me

let show_ETransitionKey (ve, ve_op, me) =
  sprintf "[%s, %s, %s]" (show_VE ve) (show_eb_op ve_op) (show_me me)

type table_m_a_mb =
  ( Option_me_A_Key.t,
    (me, ME.comparator_witness) Base.Set.t,
    Option_me_A_Key.comparator_witness )
  Map.t

type table_ma_mam =
  ( Option_me_Key.t,
    (MCM.t, MCM.comparator_witness) Base.Set.t,
    Option_me_Key.comparator_witness )
  Map_intf.Map.t

type table_ma_can_reach =
  ( Option_me_Key.t,
    (me, ME.comparator_witness) Base.Set.t,
    Option_me_Key.comparator_witness )
  Map_intf.Map.t

type table_ma_mcm =
  ( Option_me_Key.t,
    (MCM.t, MCM.comparator_witness) Base.Set.t,
    Option_me_Key.comparator_witness )
  Map_intf.Map.t

module type Dict = sig
  val pda : (TransitionKey.t, me, TransitionKey.comparator_witness) Base.Map.t
  val lookup_pda : TransitionKey.t -> me
  val lookup_epda : ETransitionKey.t -> ve * t_action
  val lookup_eps : me -> ve * t_action
  val split_stack : 'a list -> 'a option * 'a list
  val states : (me, ME.comparator_witness) Set.t
  val epda : (ETransitionKey.t * (ve * t_action)) list
  val eps_trans : (me * (ve * t_action)) list
  val estates : ve list
  val m0 : me
end

module type PDAInfo = sig
  include CoqParserType

  val vpg : CoqVPG.rules
  val table_ma_mam : table_ma_mam
  val show_table_ma_mam : table_ma_mam -> string
  val table_m_a_mb : table_m_a_mb
  val table_ma_can_reach : table_ma_can_reach
  val show_table_m_a_mb : table_m_a_mb -> string
  val table_ma_mcm : table_ma_mcm

  val trans :
    ( TransitionKey.t,
      me option,
      TransitionKey.comparator_witness )
    Map_intf.Map.t
end

module EPDA (Info : PDAInfo) : sig
  val etrans :
    ( ETransitionKey.t,
      ve option,
      ETransitionKey.comparator_witness )
    Map_intf.Map.t

  val eps_trans : (me, ve option, ME.comparator_witness) Map_intf.Map.t
  val ambi : bool
end = struct
  (* NOTE - Explore extraction PDA transitions *)
  open Info

  let etrans = ref (Map.empty (module ETransitionKey))

  let show_etrans
      (table :
        ( ETransitionKey.t,
          ve option,
          ETransitionKey.comparator_witness )
        Base.Map.t) =
    table |> Map.to_alist
    |> List.map ~f:(fun (k, v) ->
           show_ETransitionKey k ^ " -> " ^ (v |> show_VE_op))
    |> String.concat ~sep:"\n"

  let show_MR ((m, r) : MR.t) = sprintf "(%s,%s)" (show_me m) (show_VE r)

  let show_Key_MR ((m, r) : Key_MR.t) =
    sprintf "(%s,%s)" (show_me_op m) (ShowCoqM.show_rb_op r)

  let show_ras ras =
    ras |> Set.to_list |> List.map ~f:show_MR |> String.concat ~sep:";"

  let show_table_ras
      (table :
        ( Key_MR.t,
          (MR.t, MR.comparator_witness) Base.Set.t,
          Key_MR.comparator_witness )
        Map.t) : string =
    table |> Map.to_alist
    |> List.map ~f:(fun (k, v) -> show_Key_MR k ^ " ->\n  " ^ (v |> show_ras))
    |> String.concat ~sep:"\n"

  let table_cxt2Ra =
    (* NOTE - table_cxt2Ra: (ma, rb) |-> {ra}, where ra is call ve *)
    ref (Map.empty (module Key_MR))

  let trans_eps : (me, ve option, ME.comparator_witness) Map.t ref =
    ref (Map.empty (module ME))

  let fb rules ambi r t m =
    let t' = match t with None -> [] | Some t -> [ t ] in
    let simpl_key = (r, t, m) in
    match Map.find !etrans simpl_key with
    | Some ra -> ra
    | None ->
        let vt' = f_b m [ ([ r ], t') ] in
        let () = if List.length vt' > 1 then ambi := true in
        if List.length vt' = 0 then
          let () = etrans := Map.add_exn !etrans ~key:simpl_key ~data:None in
          None
        else
          let r', t' = List.hd_exn vt' in
          let r' = List.hd_exn r' in
          let () =
            etrans := Map.add_exn !etrans ~key:simpl_key ~data:(Some r')
          in
          Some r'

  let table_ma__ma_mb = ref (Map.empty (module Key_MM))
  let set_m_a_rb = ref (Set.empty (module Key_MM))

  let find_subcxt ma mb : me option list =
    match Map.find !table_ma__ma_mb (ma, mb) with
    | Some ma_list -> ma_list
    | None ->
        let ma_set =
          match Map.find table_ma_mam ma with
          | None ->
              debug (show_table_ma_mam table_ma_mam);
              debug (show_me_op ma);
              err "Can't extract"
          | Some mams ->
              mams
              |> Set.filter_map
                   (module ME)
                   ~f:(fun (m1, a, m2) ->
                     match Map.find table_m_a_mb (Some (m1, a)) with
                     | None ->
                         debug
                           (sprintf "table_m_a_mb:\n%s"
                              (show_table_m_a_mb table_m_a_mb));
                         debug (sprintf "me:\n%s" (show_me m1));
                         debug (sprintf "symbol:\n%s" (show_symbol a));
                         err ""
                     | Some mbs -> if Set.mem mbs mb then Some m2 else None)
        in
        if Set.is_empty ma_set then
          let () =
            table_ma__ma_mb :=
              Map.add_exn !table_ma__ma_mb ~key:(ma, mb) ~data:[ None ]
          in
          [ None ]
        else
          let ma_list =
            ma_set |> Set.to_list |> List.map ~f:(fun x -> Some x)
          in
          let () =
            table_ma__ma_mb :=
              Map.add_exn !table_ma__ma_mb ~key:(ma, mb) ~data:ma_list
          in
          ma_list

  let emp_rs = Set.empty (module VE)
  let updated = ref false

  let update_ras key (ma, ra) =
    table_cxt2Ra :=
      Map.update !table_cxt2Ra key ~f:(fun x ->
          match x with
          | None ->
              let () = updated := true in
              Set.singleton (module MR) (ma, ra)
          | Some rs ->
              if Set.mem rs (ma, ra) then rs
              else
                let () = updated := true in
                Set.add rs (ma, ra))

  let fetch_Ra_set key =
    match Map.find !table_cxt2Ra key with
    | None ->
        table_cxt2Ra :=
          Map.add_exn !table_cxt2Ra ~key ~data:(Set.empty (module MR));
        None
    | Some rs -> Some rs

  let table_cxt__mcrr = ref (Map.empty (module Key_MR))

  let has_checked_mcrr key (mcrr : ETransitionKey.t) =
    match Map.find !table_cxt__mcrr key with
    | None ->
        let () =
          table_cxt__mcrr :=
            Map.add_exn !table_cxt__mcrr ~key
              ~data:(Set.empty (module ETransitionKey))
        in
        false
    | Some mcrr_set ->
        if Set.mem mcrr_set mcrr then true
        else
          let () =
            table_cxt__mcrr :=
              Map.update !table_cxt__mcrr key ~f:(fun _ ->
                  Set.add mcrr_set mcrr)
          in
          false

  let rec f_cxt_inner rules ambi cxt (m, r) : unit =
    (* NOTE - In the context (ma, rb), f_cxt_inner starts from r, which is derived by m, until it reaches ma *)
    let ma, rb = cxt in
    debug
      (sprintf "f_cxt_inner |> ma=%s, rb=%s, m=%s, r=%s" (show_me_op ma)
         (ShowCoqM.show_rb_op rb) (show_me m) (show_VE r));
    let fb = fb rules ambi in
    match r with
    | Retv r' -> f_cxt_rb rules ambi cxt (m, r')
    | Plnv _ | Calv _ -> (
        (* FIXME - We assume the reachable table mₐ ~> {m} does not include the key mₐ, but if mₐ appears not as a key then the table should include mₐ. Not sure the preceding assumption is guaranteed. *)
        (* NOTE - 1. m' ~ c ~ m 2. m' ~ a ~ m *)
        let () =
          (* NOTE - 1. m' ~ c ~ m *)
          match Map.find table_ma_mcm ma with
          | None -> ()
          | Some mcm ->
              mcm
              |> Set.iter ~f:(fun (m', _, m1) ->
                     if not (equal_me m m1) then ()
                     else if has_checked_mcrr cxt (r, rb, m') then ()
                     else
                       match fb r rb m' with
                       | None -> ()
                       | Some r' -> (
                           match r' with
                           | Calv _ ->
                               update_ras cxt (m', r')
                           | _ ->
                               debug
                                 (sprintf "from mcm %s -> %s" (show_me m')
                                    (show_me m1));
                               f_cxt_inner rules ambi cxt (m', r')))
        in
        match Map.find table_ma_mam ma with
        | None ->
            ()
        | Some mam ->
            mam
            |> Set.iter ~f:(fun (m', _, m1) ->
                   if not (equal_me m m1) then ()
                   else if has_checked_mcrr cxt (r, rb, m') then ()
                   else
                     match fb r rb m' with
                     | None -> ()
                     | Some r' -> (
                         match r' with
                         | Calv _ ->
                             update_ras cxt (m', r')
                         | _ ->
                             debug
                               (sprintf "from mam %s -> %s" (show_me m')
                                  (show_me m1));
                             f_cxt_inner rules ambi cxt (m', r'))))

  and f_cxt_rb rules ambi cxt (mb, rb) =
    (* NOTE - Within cxt, f_cxt_rb finds paired (ma,rb),
       and explores from { ra | ma |-> ra } *)
    debug
      (sprintf "f_cxt_rb |> mb=%s, rb=%s" (show_me mb) (ShowCoqM.show_rb rb));
    find_subcxt (fst cxt) mb
    |> List.iter ~f:(fun ma ->
           let ras =
             match fetch_Ra_set (ma, Some rb) with
             | None ->
                 debug "f_cxt_rb: Can't find {ra}~rb, explore it";
                 f_cxt rules ambi (ma, rb);
                 Map.find_exn !table_cxt2Ra (ma, Some rb)
             | Some ras -> ras
           in
           debug (sprintf "f_cxt_rb: Has ras %s" (show_ras ras));
           Set.iter ras ~f:(fun (ma, ra) -> f_cxt_inner rules ambi cxt (ma, ra)))

  and f_cxt rules ambi (ma, rb) =
    (* NOTE - In context (ma,rb), f_cxt starts from possbile ends
       and moves to ma *)
    debug
      (sprintf "f_cxt |> ma=%s, rb=%s" (show_me_op ma) (ShowCoqM.show_rb rb));
    let fb = fb rules ambi in
    let ms =
      Map.find_exn table_ma_can_reach ma
    in
    debug
      (sprintf "Reach %s"
         (ms |> Set.to_list |> List.map ~f:show_me |> String.concat ~sep:","));
    Set.iter ms ~f:(fun m ->
        match fb (Retv rb) (Some rb) m with
        | None ->
            debug
              (sprintf "f_cxt |> compute {} = fb %s %s" (ShowCoqM.show_rb rb)
                 (show_me m));
            ()
        | Some r -> (
            debug
              (sprintf "f_cxt |> compute %s = fb %s %s" (show_VE r)
                 (ShowCoqM.show_rb rb) (show_me m));
            match m with
            | CalCME _ -> update_ras (ma, Some rb) (m, r)
            | _ ->
                ();
                f_cxt_inner rules ambi (ma, Some rb) (m, r)))

  let ambi = ref false
  let pick_one = List.hd_exn

  let fetch_eps rules m =
    match Map.find !trans_eps m with
    | Some None -> None
    | Some re -> re
    | None -> (
        match f_init m with
        | [] ->
            let () = trans_eps := Map.add_exn !trans_eps ~key:m ~data:None in
            None
        | ves -> (
            let () = if List.length ves > 1 then ambi := true in
            let v, t = pick_one ves in
            match v with
            | [] -> err "f_init gives empty v"
            | r :: _ ->
                trans_eps := Map.add_exn !trans_eps ~key:m ~data:(Some r);
                Some r))

  let rec explore_epda rules =
    updated := false;
    table_ma_can_reach
    |> Map.iteri ~f:(fun ~key:ma ~data:ms ->
           ms
           |> Set.iter ~f:(fun m ->
                  match fetch_eps rules m with
                  | None -> ()
                  | Some (Calv _) -> err "this cannot happen"
                  | Some (Plnv r) ->
                      f_cxt_inner rules ambi (ma, None) (m, Plnv r)
                  | Some (Retv r) -> f_cxt_rb rules ambi (ma, None) (m, r)));
    !table_cxt2Ra
    |> Map.iter_keys ~f:(fun (m, rb) ->
           match rb with Some rb -> f_cxt rules ambi (m, rb) | None -> ());
    if !updated then explore_epda rules else ()

  let () = explore_epda vpg

  let () =
    debug (Map.length !table_cxt2Ra |> sprintf "#table_cxt2Ra=%d");
    debug (show_table_ras !table_cxt2Ra |> sprintf "table ras is\n%s");
    debug (sprintf "#etrans=%d" (Map.length !etrans));
    debug (sprintf "etrans is %s" (show_etrans !etrans));
    debug (sprintf "#eps_trans=%d" (Map.length !trans_eps))

  let etrans = !etrans
  let eps_trans = !trans_eps
  let ambi = !ambi

  let show_eps_trans eps_trans =
    List.filter_map eps_trans ~f:(fun (m, r) ->
        match r with
        | None -> None
        | Some r -> Some (sprintf "%s -> %s" (show_me m) (show_VE r)))
    |> String.concat ~sep:"\n"

  let () =
    debug
      (sprintf "EPDA ε trans:\n%s" (show_eps_trans (Map.to_alist eps_trans)))
end

module PDA (Info : sig
  include CoqParserType

  val plainSyms : symbol list
  val callSyms : symbol list
  val retSyms : symbol list
  val m0 : me
  val vpg : CoqVPG.rules
end) : PDAInfo = struct
  (* NOTE - Explore parser PDA transitions *)
  include Info

  let emp = Set.empty (module ME)

  let table_ma_can_reach =
    (* NOTE - ma? ↦ {m | m is reachable in context (ma, _)} *)
    ref (Map.of_alist_exn (module Option_me_Key) [ (None, emp) ])

  let show_table_ma_can_reach
      (table :
        ( Option_me_Key.t,
          (me, ME.comparator_witness) Base.Set.t,
          Option_me_Key.comparator_witness )
        Map.t) =
    table |> Map.to_alist
    |> List.map ~f:(fun (k, v) ->
           show_Option_me_Key k ^ " ==>\n  "
           ^ (v |> Set.elements |> List.map ~f:show_me
            |> String.concat ~sep:";\n  "))
    |> String.concat ~sep:"\n\n"

  let trans =
    (* NOTE - All transitions *)
    ref (Map.empty (module TransitionKey))

  let show_TransitionKey (me, me_op, sym) =
    sprintf "[%s, %s, %s]" (show_me me) (show_me_op me_op) (show_symbol sym)

  let show_trans
      (table :
        (TransitionKey.t, me option, TransitionKey.comparator_witness) Map.t) =
    table |> Map.to_alist
    |> List.map ~f:(fun (k, v) ->
           show_TransitionKey k ^ " -> " ^ (v |> show_me_op))
    |> String.concat ~sep:"\n"

  let table_m_a_mb : table_m_a_mb ref =
    (* NOTE - (m,a) ↦ {mb} *)
    ref (Map.empty (module Option_me_A_Key))

  let show_Option_me_A_Key = function
    | None -> "None"
    | Some (me, sym) -> sprintf "(%s,%s)" (show_me me) (show_symbol sym)

  let show_table_m_a_mb (table : table_m_a_mb) =
    table |> Map.to_alist
    |> List.map ~f:(fun (k, v) ->
           show_Option_me_A_Key k ^ " -> "
           ^ (v |> Set.elements |> List.map ~f:show_me
            |> String.concat ~sep:" | "))
    |> String.concat ~sep:"\n"

  let table_ma_mcm =
    (* NOTE - ma ↦ (m,c,m) *)
    ref (Map.empty (module Option_me_Key))

  let table_ma_mam =
    (* NOTE - ma ↦ (m,a,ma) *)
    ref
      (Map.of_alist_exn
         (module Option_me_Key)
         [ (None, Set.empty (module MCM)) ])

  let show_MCM (m1, i, m2) =
    sprintf "<%s, %s> ==> %s" (show_me m1) (show_symbol i) (show_me m2)

  let show_table_ma_mam
      (table :
        ( Option_me_Key.t,
          (MCM.t, MCM.comparator_witness) Base.Set.t,
          Option_me_Key.comparator_witness )
        Map.t) =
    table |> Map.to_alist
    |> List.map ~f:(fun (k, v) ->
           show_Option_me_Key k ^ " ->\n  "
           ^ (v |> Set.elements |> List.map ~f:show_MCM
            |> String.concat ~sep:"\n  "))
    |> String.concat ~sep:"\n"

  let updated = ref false

  let add_table_ma_mim table ma m1_i_m2 =
    table :=
      Map.update !table ma ~f:(fun mcms ->
          match mcms with
          | None -> Set.singleton (module MCM) m1_i_m2
          | Some mcms ->
              if Set.mem mcms m1_i_m2 then mcms
              else
                let () = updated := true in
                Set.add mcms m1_i_m2)

  let add_table_ma_mcm ma key = add_table_ma_mim table_ma_mcm ma key
  let add_table_ma_mam ma key = add_table_ma_mim table_ma_mam ma key

  let add_table_m_a_mb ta mb =
    table_m_a_mb :=
      Map.update !table_m_a_mb ta ~f:(fun mbs ->
          match mbs with
          | None -> Set.singleton (module ME) mb
          | Some mbs ->
              if Set.mem mbs mb then mbs
              else
                let () = updated := true in
                Set.add mbs mb)

  let fetch_trans rules key =
    let m, t, i = key in
    let simpl_t = match i with Ret _ -> t | _ -> None in
    let simpl_key = (m, simpl_t, i) in
    let t0 = match t with None -> [] | Some t -> [ t ] in
    match Map.find !trans simpl_key with
    | Some None -> None
    | Some m -> m
    | None ->
        let _m', _ = p m t0 i in
        let m' = if is_empty_me _m' then None else Some _m' in
        let () = trans := Map.add_exn !trans ~key:simpl_key ~data:m' in
        let () = updated := true in
        m'

  let fetch_table_m_a_mb key =
    match Map.find !table_m_a_mb key with Some mbs -> mbs | None -> emp

  let gen_c_one_step rules ma ms acc m =
    (* NOTE - deriv m with c to m', check if m' is in ms
       return: m' that's not in ms *)
    plainSyms
    |> List.fold ~init:acc ~f:(fun acc c ->
           let key : TransitionKey.t = (m, None, c) in
           let mc = fetch_trans rules key in
           match mc with
           | None -> acc
           | Some mc ->
               let () = add_table_ma_mcm ma (m, c, mc) in
               if Set.mem ms mc then acc else Set.add acc mc)

  let rec gen_c_full rules cxt ms ms_new : unit =
    (* NOTE - gen_c_full computes derivatives of plain symbols until converge,
       then ret the new states *)
    if Set.is_empty ms_new then
      table_ma_can_reach := Map.update !table_ma_can_reach cxt ~f:(fun x -> ms)
    else
      let ms_new' =
        ms_new
        |> Set.fold ~init:emp ~f:(fun acc m ->
               if Set.mem acc m then acc else gen_c_one_step rules cxt ms acc m)
      in
      gen_c_full rules cxt (Set.union ms_new ms) ms_new'

  let rec gen_c rules cxt new_ms : (me, ME.comparator_witness) Set.t =
    (* NOTE - gen_c returns { mb | cxt ~> mb }} *)
    let ms = Map.find_exn !table_ma_can_reach cxt in
    let new_ms = Set.diff new_ms ms in

    (* let () =
         debug (sprintf "gen_c: old: %d new:%d" (Set.length ms) (Set.length new_ms) )
       in *)
    if Set.is_empty new_ms then
      (* FIXME - consider pending ret *)
      match cxt with None -> emp | _ -> gen_b_all rules cxt
      (* let new_ms = Set.diff mbs ms in
         if Set.is_empty new_ms then mbs else gen_c rules cxt new_ms *)
    else
      (* debug (sprintf "gen_c: compute new_ms" ); *)
      let () = gen_c_full rules cxt ms new_ms in
      gen_a rules cxt

  and gen_a rules cxt =
    (* NOTE - gen_a: (m,a) ↦ {mb | mb matched with (m, a) } *)
    (* debug (sprintf "gen_a" ); *)
    let ms = Map.find_exn !table_ma_can_reach cxt in
    let mbs =
      ms
      |> Set.fold ~init:emp ~f:(fun acc m ->
             callSyms
             |> List.fold ~init:acc ~f:(fun acc a ->
                    match fetch_trans rules (m, None, a) with
                    | None -> acc
                    | Some ma ->
                        let () = add_table_ma_mam cxt (m, a, ma) in
                        let mbs =
                          match Map.find !table_ma_can_reach (Some ma) with
                          | Some mac ->
                              (* NOTE - ma has been checked *)
                              fetch_table_m_a_mb (Some (m, a))
                          | None ->
                              let () =
                                table_ma_can_reach :=
                                  Map.add_exn !table_ma_can_reach ~key:(Some ma)
                                    ~data:emp
                              in
                              gen_c rules (Some ma)
                                (Set.singleton (module ME) ma)
                        in
                        Set.union acc mbs))
    in
    gen_c rules cxt mbs

  and gen_b_all rules cxt =
    (* FIXME - cxt could be None, in the pending cases *)
    let cxt = Option.value_exn cxt in
    let mbs =
      !table_ma_mam |> Map.to_alist
      |> List.fold ~init:emp ~f:(fun acc (ma, set_mam) ->
             set_mam |> Set.to_list
             |> List.fold ~init:acc ~f:(fun acc (m1, a, m2) ->
                    if equal_me m2 cxt then
                      let ms = Map.find_exn !table_ma_can_reach (Some cxt) in
                      retSyms
                      |> List.fold ~init:emp ~f:(fun acc b ->
                             ms
                             |> Set.fold ~init:acc ~f:(fun acc m ->
                                    match fetch_trans rules (m, Some m1, b) with
                                    | None -> acc
                                    | Some mb ->
                                        let () =
                                          add_table_m_a_mb (Some (m1, a)) mb
                                        in
                                        Set.add acc mb))
                    else acc))
    in
    mbs

  let ms0 = Set.singleton (module ME) m0

  let rec explore_ppda rules =
    let () = updated := false in
    let () =
      !table_ma_can_reach
      |> Map.iteri ~f:(fun ~key:ma ~data:mset ->
             let _ = gen_a rules ma in
             ())
    in
    if !updated then explore_ppda rules else ()

  let () =
    let _ = gen_c vpg None ms0 in
    explore_ppda vpg

  let () =
    debug (Map.length !table_ma_can_reach |> sprintf "#table_ma_can_reach=%d");
    debug (sprintf "table_m_a_mb:\n%s" (show_table_m_a_mb !table_m_a_mb));
    debug (sprintf "table_m_a_mam:\n%s" (show_table_ma_mam !table_ma_mam));
    debug (sprintf "table_m_a_mcm:\n%s" (show_table_ma_mam !table_ma_mcm));
    debug
      (sprintf "table_ma_can_reach:\n%s"
         (show_table_ma_can_reach !table_ma_can_reach))

  let () = debug (sprintf "#trans=%d" (Map.length !trans))
  let vpg = vpg
  let table_ma_mam = !table_ma_mam
  let table_m_a_mb = !table_m_a_mb
  let table_ma_can_reach = !table_ma_can_reach
  let table_ma_mcm = !table_ma_mcm
  let trans = !trans
end

module AddEpsAction (Info : sig
  val tcfg_nts : (variable, Variable.comparator_witness) Base.Set.t
  val eps_trans : (me, ve option, ME.comparator_witness) Map.t
  val lookup_actions : ve -> int list

  val rule2i :
    (TCFG.single_rule, int, TCFG.SingleRule.comparator_witness) Map_intf.Map.t

  val etrans :
    ( ETransitionKey.t,
      ve option,
      ETransitionKey.comparator_witness )
    Map_intf.Map.t
end) : sig
  val eps_trans : (me, ve * t_action, ME.comparator_witness) Map_intf.Map.t

  val epda :
    ( ETransitionKey.t,
      ve * t_action,
      ETransitionKey.comparator_witness )
    Map_intf.Map.t
end = struct
  open Info

  let extract_nt nt = nt |> function V0 l | V1 l -> l |> cl2str

  let is_original_nt l =
    Set.mem tcfg_nts (extract_nt l)

  let eps_trans =
    eps_trans
    |> Map.filter_map ~f:(fun r ->
           match r with
           | None -> None
           | Some r -> (
               match lookup_actions r with
               | [] -> Some (r, [||])
               | actions ->
                   let actions =
                     (* NOTE - Insert (L->ε) to TCFG rule index list *)
                     match r with
                     | Calv (MatCalE _) -> err ""
                     | Calv (PndCalE (_, _, l'))
                     | Plnv (PlnE (_, _, l'))
                     | Retv (MatRetE (_, _, _, _, l'))
                     | Retv (PndRetE (_, _, l')) ->
                         if is_original_nt l' then (
                           debug
                             (sprintf "ε rule %s get eps nt actions %s"
                                (show_VE r) (extract_nt l'));
                           let i = Map.find_exn rule2i (extract_nt l', []) in
                           i :: actions)
                         else actions
                   in
                   Some (r, Array.of_list actions)))

  let epda =
    etrans
    |> Map.filter_mapi ~f:(fun ~key:(r, r', m) ~data:r_m ->
           match r_m with
           | None -> None
           | Some r_m -> (
               match r_m with
               | Plnv (PlnE (_, c, _)) when CoqVPG.Basic.equal_terminal c c0 ->
                   None
               | _ -> (
                   match lookup_actions r_m with
                   | [] -> Some (r_m, [||])
                   | actions ->
                       let actions =
                         match r with
                         | Retv (MatRetE _) -> (
                             match r_m with
                             | Retv (PndRetE (_, _, _))
                             | Calv (PndCalE (_, _, _)) ->
                                 err ""
                             | Calv (MatCalE (_, _, l', _, _))
                             | Plnv (PlnE (_, _, l'))
                             | Retv (MatRetE (_, _, _, _, l')) ->
                                 if is_original_nt l' then (
                                   debug
                                     (sprintf "e rule %s get eps nt actions %s"
                                        (show_VE r_m) (extract_nt l'));
                                   let i =
                                     Map.find_exn rule2i (extract_nt l', [])
                                   in
                                   i :: actions)
                                 else actions)
                         | _ -> actions
                       in
                       Some (r_m, Array.of_list actions))))
end

module OtherPDAInfo = struct
  let get_epda_states e_trans =
    e_trans
    |> List.map ~f:(fun ((r, _, m), (r', _)) -> [ r; r' ])
    |> List.concat

  let get_eps_states eps_trans =
    eps_trans |> List.map ~f:(fun (_, (r', _)) -> r')

  let get_pda_states
      (trans : (TransitionKey.t, me, TransitionKey.comparator_witness) Map.t) =
    trans |> Map.to_alist
    |> List.map ~f:(fun ((s, s_, i), s') -> [ s; s' ])
    |> List.concat
    |> Set.of_list (module ME)
end

module BuildDict (Info : GrammarInfo) : Dict = struct
  include Info
  open Utils

  let r0 = CoqParseTree.PlnE (V0 (str2cl l0), c0, V0 (str2cl l0))
  let m0 = CoqParseTree.PlnCME (CoqParseTree.Coq_vc_set.singleton (None, r0))

  module PDA = PDA (struct
    include Info

    let m0 = m0
  end)

  module EPDA = EPDA (PDA)

  module EPDA_EPS = AddEpsAction (struct
    include EPDA
    include Info
  end)

  let pda =
    PDA.trans
    |> Map.filter_map ~f:(fun m : me option ->
           match m with Some m -> Some m | None -> None)

  let epda = EPDA_EPS.epda
  let eps_trans = EPDA_EPS.eps_trans
  let ambi = EPDA.ambi
  let lookup_pda = Map.find_exn pda

  let lookup_epda key : ve * t_action =
    match Map.find epda key with
    | Some r -> r
    | None -> err (show_ETransitionKey key)

  let lookup_eps : me -> ve * t_action = Map.find_exn eps_trans
  let states = pda |> OtherPDAInfo.get_pda_states
  let epda : (ETransitionKey.t * (ve * t_action)) list = epda |> Map.to_alist
  let eps_trans : (me * (ve * t_action)) list = eps_trans |> Map.to_alist
  let e_states = OtherPDAInfo.get_epda_states epda
  let eps_state = OtherPDAInfo.get_eps_states eps_trans
  let estates = e_states @ eps_state |> Set.of_list (module VE) |> Set.to_list

  let split_stack st =
    match st with [] -> (None, []) | top :: tail -> (Some top, tail)

  let show_eps_trans eps_trans =
    List.map eps_trans ~f:(fun (m, (r, is)) ->
        sprintf "%s -> %s" (show_me m) (show_VE r))
    |> String.concat ~sep:"\n"

  let () =
    print_endline (sprintf "|pda|=%d" (Map.length pda));
    print_endline (sprintf "|epda|=%d" (List.length epda));
    print_endline (sprintf "|ε trans|=%d" (List.length eps_trans));
    print_endline (sprintf "|epda states|=%d" (List.length e_states));
    print_endline (sprintf "|ε states|=%d" (List.length eps_trans));
    print_endline (sprintf "%s" (show_eps_trans eps_trans));
    if ambi then print_endline "The grammar is ambiguous."
    else print_endline "The grammar is unambiguous."
end
