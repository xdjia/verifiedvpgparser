(* open Core
open CoqVPG
open CoqParseTree


(** val findRuleWithLc :
        CoqVPG.vpg_var -> CoqVPG.symbol -> (CoqVPG.vpg_var * CoqVPG.alt)
        list **)

let findRuleWithLc p l i =
  filter
    (fun r ->
      let lr, y = r in
      match y with
      | CoqVPG.Alt_Linear (i', _) -> equal_vpg_var lr l && equal_symbol i i'
      | _ -> false)
    p

(** val findRuleWithMa :
        CoqVPG.vpg_var -> string -> (CoqVPG.vpg_var * CoqVPG.alt) list **)

let findRuleWithMa rules l i =
  filter
    (fun r ->
      let lr, y = r in
      match y with
      | CoqVPG.Alt_Match (i', _, _, _) ->
          equal_vpg_var lr l && String.equal i i'
      | _ -> false)
    rules

(** val convert2PlainE :
        CoqVPG.vpg_var -> string -> CoqParseTree.plnEdge list **)

let convert2PlainE rules l s =
  let rs = findRuleWithLc rules l (Plain s) in
  map
    (fun r ->
      let _, y0 = r in
      match y0 with
      | CoqVPG.Alt_Linear (_, l') -> CoqParseTree.PlnE (l, s, l')
      | _ -> CoqParseTree.PlnE (l, s, l))
    rs

(** val convert2CallLinearE :
        CoqVPG.vpg_var -> string -> CoqParseTree.calEdge list **)

let convert2CallLinearE rules l s =
  let rs = findRuleWithLc rules l (Call s) in
  map
    (fun r ->
      let _, y0 = r in
      match y0 with
      | CoqVPG.Alt_Linear (_, l') -> CoqParseTree.PndCalE (l, s, l')
      | _ -> CoqParseTree.PndCalE (l, s, l))
    rs

(** val convert2CallMatchE :
        CoqVPG.vpg_var -> string -> CoqParseTree.calEdge list **)

let convert2CallMatchE rules l s =
  let rs = findRuleWithMa rules l s in
  map
    (fun r ->
      let _, y0 = r in
      match y0 with
      | CoqVPG.Alt_Match (_, b, l', l2) -> CoqParseTree.MatCalE (l, s, l', b, l2)
      | _ -> CoqParseTree.MatCalE (l, s, l, s, l))
    rs

(** val convert2RetLinearE :
        CoqVPG.vpg_var -> string -> CoqParseTree.retEdge list **)

let convert2RetLinearE rules l s =
  let rs = findRuleWithLc rules l (Ret s) in
  map
    (fun r ->
      let _, y0 = r in
      match y0 with
      | CoqVPG.Alt_Linear (_, l') -> CoqParseTree.PndRetE (l, s, l')
      | _ -> CoqParseTree.PndRetE (l, s, l))
    rs

(** val e2PlainE : CoqParseTree.ve -> string -> CoqParseTree.plnEdge list **)

let e2PlainE rules e' s = convert2PlainE rules (endE e') s

(** val e2CallLinearE rules :
        CoqParseTree.ve -> string -> CoqParseTree.calEdge list **)

let e2CallLinearE rules e' s = convert2CallLinearE rules (endE e') s

(** val e2CallMatchE rules : CoqParseTree.ve -> string -> CoqParseTree.calEdge list **)

let e2CallMatchE rules e' s = convert2CallMatchE rules (endE e') s

(** val e2RetLinearE rules :
        CoqParseTree.ve -> string -> CoqParseTree.retEdge list **)

let e2RetLinearE rules e' s = convert2RetLinearE rules (endE e') s
let va_of_list = Set.of_list (module Ea)
let vc_of_list = Set.of_list (module Ec)
let vb_of_list = Set.of_list (module Eb)
let va_to_list = Set.to_list
let vc_to_list = Set.to_list
let vb_to_list = Set.to_list

(** val m2PlainM : CoqParseTree.me -> string -> CoqParseTree.me **)

let m2PlainM rules m' s =
  match m' with
  | CoqParseTree.CalME m'0 ->
      CoqParseTree.PlnME
        (vc_of_list
           (concat
              (map
                 (fun v ->
                   let r, e = v in
                   map (fun x -> (r, x)) (e2PlainE rules (CoqParseTree.Calv e) s))
                 (va_to_list m'0))))
  | CoqParseTree.PlnME m'0 ->
      CoqParseTree.PlnME
        (vc_of_list
           (concat
              (map
                 (fun v ->
                   let r, e = v in
                   map (fun x -> (r, x)) (e2PlainE rules (CoqParseTree.Plnv e) s))
                 (vc_to_list m'0))))
  | CoqParseTree.RetME m'0 ->
      CoqParseTree.PlnME
        (vc_of_list
           (concat
              (map
                 (fun v ->
                   let r, e = v in
                   map (fun x -> (r, x)) (e2PlainE rules (CoqParseTree.Retv e) s))
                 (vb_to_list m'0))))

(** val m2CallM : CoqParseTree.me -> string -> CoqParseTree.me **)

let m2CallM rules m' s =
  match m' with
  | CoqParseTree.CalME m'0 ->
      CoqParseTree.CalME
        (va_of_list
           (concat
              (map
                 (fun v ->
                   let r, e = v in
                   match r with
                   | Some c -> (
                       match c with
                       | CoqParseTree.PndCalE (_, _, _) ->
                           map
                             (fun x -> (Some x, x))
                             (app
                                (e2CallLinearE rules (CoqParseTree.Calv e) s)
                                (e2CallMatchE rules (CoqParseTree.Calv e) s))
                       | CoqParseTree.MatCalE (_, _, _, _, _) ->
                           map
                             (fun x -> (Some x, x))
                             (e2CallMatchE rules (CoqParseTree.Calv e) s))
                   | None ->
                       map
                         (fun x -> (Some x, x))
                         (app
                            (e2CallLinearE rules (CoqParseTree.Calv e) s)
                            (e2CallMatchE rules (CoqParseTree.Calv e) s)))
                 (va_to_list m'0))))
  | CoqParseTree.PlnME m'0 ->
      CoqParseTree.CalME
        (va_of_list
           (concat
              (map
                 (fun v ->
                   let r, e = v in
                   match r with
                   | Some c -> (
                       match c with
                       | CoqParseTree.PndCalE (_, _, _) ->
                           map
                             (fun x -> (Some x, x))
                             (app
                                (e2CallLinearE rules (CoqParseTree.Plnv e) s)
                                (e2CallMatchE rules (CoqParseTree.Plnv e) s))
                       | CoqParseTree.MatCalE (_, _, _, _, _) ->
                           map
                             (fun x -> (Some x, x))
                             (e2CallMatchE rules (CoqParseTree.Plnv e) s))
                   | None ->
                       map
                         (fun x -> (Some x, x))
                         (app
                            (e2CallLinearE rules (CoqParseTree.Plnv e) s)
                            (e2CallMatchE rules (CoqParseTree.Plnv e) s)))
                 (vc_to_list m'0))))
  | CoqParseTree.RetME m'0 ->
      CoqParseTree.CalME
        (va_of_list
           (concat
              (map
                 (fun v ->
                   let r, e = v in
                   match r with
                   | Some c -> (
                       match c with
                       | CoqParseTree.PndCalE (_, _, _) ->
                           map
                             (fun x -> (Some x, x))
                             (app
                                (e2CallLinearE rules (CoqParseTree.Retv e) s)
                                (e2CallMatchE rules (CoqParseTree.Retv e) s))
                       | CoqParseTree.MatCalE (_, _, _, _, _) ->
                           map
                             (fun x -> (Some x, x))
                             (e2CallMatchE rules (CoqParseTree.Retv e) s))
                   | None ->
                       map
                         (fun x -> (Some x, x))
                         (app
                            (e2CallLinearE rules (CoqParseTree.Retv e) s)
                            (e2CallMatchE rules (CoqParseTree.Retv e) s)))
                 (vb_to_list m'0))))

(** val filter_map :
        'a1 list -> ('a1 -> bool) -> ('a1 -> 'a2) -> 'a2 list **)

let filter_map l f g =
  let l' = filter f l in
  map g l'

(** val goEps rules : CoqParseTree.ve -> bool **)

let goEps rules e =
  existsb
    (fun x ->
      let l1, y = x in
      match y with
      | CoqVPG.Alt_Epsilon -> equal_vpg_var (endE e) l1
      | _ -> false)
    rules

(** val m2RetM :
        CoqParseTree.me -> CoqParseTree.me option -> string -> CoqParseTree.me **)

let m2RetM rules m' t0 s =
  match m' with
  | CoqParseTree.CalME m'0 ->
      let m'1 = va_to_list m'0 in
      CoqParseTree.RetME
        (vb_of_list
           (match t0 with
           | Some c -> (
               match c with
               | CoqParseTree.CalME t1 ->
                   let t2 = va_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Calv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Calv te))
                                           lr
                                         && goEps rules (CoqParseTree.Calv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Calv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Calv e) s))))
                        t2)
               | CoqParseTree.PlnME t1 ->
                   let t2 = vc_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Plnv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Plnv te))
                                           lr
                                         && goEps rules (CoqParseTree.Calv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Calv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Calv e) s))))
                        t2)
               | CoqParseTree.RetME t1 ->
                   let t2 = vb_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Retv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Retv te))
                                           lr
                                         && goEps rules (CoqParseTree.Calv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Calv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Calv e) s))))
                        t2))
           | None ->
               concat
                 (map
                    (fun v ->
                      let _, e = v in
                      map
                        (fun e0 -> (None, e0))
                        (e2RetLinearE rules (CoqParseTree.Calv e) s))
                    m'1)))
  | CoqParseTree.PlnME m'0 ->
      let m'1 = vc_to_list m'0 in
      CoqParseTree.RetME
        (vb_of_list
           (match t0 with
           | Some c -> (
               match c with
               | CoqParseTree.CalME t1 ->
                   let t2 = va_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Calv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Calv te))
                                           lr
                                         && goEps rules (CoqParseTree.Plnv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Plnv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Plnv e) s))))
                        t2)
               | CoqParseTree.PlnME t1 ->
                   let t2 = vc_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Plnv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Plnv te))
                                           lr
                                         && goEps rules (CoqParseTree.Plnv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Plnv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Plnv e) s))))
                        t2)
               | CoqParseTree.RetME t1 ->
                   let t2 = vb_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Retv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Retv te))
                                           lr
                                         && goEps rules (CoqParseTree.Plnv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Plnv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Plnv e) s))))
                        t2))
           | None ->
               concat
                 (map
                    (fun v ->
                      let _, e = v in
                      map
                        (fun e0 -> (None, e0))
                        (e2RetLinearE rules (CoqParseTree.Plnv e) s))
                    m'1)))
  | CoqParseTree.RetME m'0 ->
      let m'1 = vb_to_list m'0 in
      CoqParseTree.RetME
        (vb_of_list
           (match t0 with
           | Some c -> (
               match c with
               | CoqParseTree.CalME t1 ->
                   let t2 = va_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Calv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Calv te))
                                           lr
                                         && goEps rules (CoqParseTree.Retv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Retv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Retv e) s))))
                        t2)
               | CoqParseTree.PlnME t1 ->
                   let t2 = vc_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Plnv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Plnv te))
                                           lr
                                         && goEps rules (CoqParseTree.Retv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Retv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Retv e) s))))
                        t2)
               | CoqParseTree.RetME t1 ->
                   let t2 = vb_to_list t1 in
                   concat
                     (map
                        (fun tre ->
                          let tr, te = tre in
                          concat
                            (filter_map m'1
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (lr, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Retv te))
                                           lr
                                     | CoqParseTree.MatCalE (lr, _, _, _, _) ->
                                         equal_vpg_var (endE (CoqParseTree.Retv te))
                                           lr
                                         && goEps rules (CoqParseTree.Retv e))
                                 | None -> false)
                               (fun v ->
                                 let r, e = v in
                                 match r with
                                 | Some c0 -> (
                                     match c0 with
                                     | CoqParseTree.PndCalE (_, _, _) ->
                                         map
                                           (fun e0 -> (tr, e0))
                                           (e2RetLinearE rules (CoqParseTree.Retv e) s)
                                     | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                                         if String.equal s b then
                                           [
                                             ( tr,
                                               CoqParseTree.MatRetE (l, a, l1, b, l2)
                                             );
                                           ]
                                         else [])
                                 | None ->
                                     map
                                       (fun e0 -> (tr, e0))
                                       (e2RetLinearE rules (CoqParseTree.Retv e) s))))
                        t2))
           | None ->
               concat
                 (map
                    (fun v ->
                      let _, e = v in
                      map
                        (fun e0 -> (None, e0))
                        (e2RetLinearE rules (CoqParseTree.Retv e) s))
                    m'1)))

(** val p :
        CoqParseTree.me -> CoqParseTree.me list -> CoqVPG.symbol ->
        CoqParseTree.me * CoqParseTree.me list **)

let emp_ME m =
  match m with
  | CalME m' -> if Set.is_empty m' then None else Some m
  | PlnME m' -> if Set.is_empty m' then None else Some m
  | RetME m' -> if Set.is_empty m' then None else Some m

let p rules m t0 = function
  | Plain s -> m2PlainM rules m s |> emp_ME
  | Call s -> m2CallM rules m s |> emp_ME
  | Ret s -> m2RetM rules m t0 s |> emp_ME *)
