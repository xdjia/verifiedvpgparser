(* open CoqVPG
open Coq_parser
open CoqParseTree

let f_init rules m =
  match m with
  | CoqParseTree.CalME m0 ->
      let m1 = va_to_list m0 in
      let f v =
        let r, e = v in
        match r with
        | Some c -> (
            match c with
            | CoqParseTree.PndCalE (_, _, _) -> goEps rules (CoqParseTree.Calv e)
            | CoqParseTree.MatCalE (_, _, _, _, _) -> false)
        | None -> goEps rules (CoqParseTree.Calv e)
      in
      let g v =
        let _, e = v in
        ([ CoqParseTree.Calv e ], [])
      in
      filter_map m1 f g
  | CoqParseTree.PlnME m0 ->
      let m1 = vc_to_list m0 in
      let f v =
        let r, e = v in
        match r with
        | Some c -> (
            match c with
            | CoqParseTree.PndCalE (_, _, _) -> goEps rules (CoqParseTree.Plnv e)
            | CoqParseTree.MatCalE (_, _, _, _, _) -> false)
        | None -> goEps rules (CoqParseTree.Plnv e)
      in
      let g v =
        let _, e = v in
        ([ CoqParseTree.Plnv e ], [])
      in
      filter_map m1 f g
  | CoqParseTree.RetME m0 ->
      let m1 = vb_to_list m0 in
      let f v =
        let r, e = v in
        match r with
        | Some c -> (
            match c with
            | CoqParseTree.PndCalE (_, _, _) -> goEps rules (CoqParseTree.Retv e)
            | CoqParseTree.MatCalE (_, _, _, _, _) -> false)
        | None -> goEps rules (CoqParseTree.Retv e)
      in
      let g v =
        let _, e = v in
        ([ CoqParseTree.Retv e ], [ e ])
      in
      filter_map m1 f g

let f_b rules m v =
  match m with
  | CoqParseTree.CalME m0 ->
      let m1 = va_to_list m0 in
      concat
        (map
           (fun v0 ->
             let r, e = v0 in
             match r with
             | Some c -> (
                 match c with
                 | CoqParseTree.PndCalE (_, _, _) ->
                     let f vt =
                       let v1, t0 = vt in
                       match t0 with
                       | [] -> (
                           match v1 with
                           | [] -> false
                           | ve :: _ ->
                               equal_vpg_var (endE (CoqParseTree.Calv e)) (beginE ve))
                       | r0 :: _ -> (
                           match r0 with
                           | CoqParseTree.PndRetE (_, _, _) -> (
                               match v1 with
                               | [] -> false
                               | ve :: _ ->
                                   equal_vpg_var (endE (CoqParseTree.Calv e))
                                     (beginE ve))
                           | CoqParseTree.MatRetE (_, _, _, _, _) -> false)
                     in
                     let g vt =
                       let v1, t0 = vt in
                       (CoqParseTree.Calv e :: v1, tl t0)
                     in
                     filter_map v f g
                 | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                     let f vt =
                       let v1, t0 = vt in
                       match t0 with
                       | [] -> false
                       | r0 :: _ -> (
                           match r0 with
                           | CoqParseTree.PndRetE (_, _, _) -> false
                           | CoqParseTree.MatRetE (l', a', l1', b', l2') -> (
                               ((((equal_vpg_var l l' && equal_vpg_var l1 l1')
                                 && equal_vpg_var l2 l2')
                                && String.equal a a')
                               && String.equal b b')
                               &&
                               match v1 with
                               | [] -> false
                               | ve :: _ -> (
                                   match ve with
                                   | CoqParseTree.Retv _ ->
                                       goEps rules (CoqParseTree.Calv e)
                                   | _ ->
                                       equal_vpg_var (endE (CoqParseTree.Calv e))
                                         (beginE ve))))
                     in
                     let g vt =
                       let v1, t0 = vt in
                       (CoqParseTree.Calv e :: v1, tl t0)
                     in
                     filter_map v f g)
             | None ->
                 let f vt =
                   let v1, t0 = vt in
                   match t0 with
                   | [] -> (
                       match v1 with
                       | [] -> false
                       | ve :: _ ->
                           equal_vpg_var (endE (CoqParseTree.Calv e)) (beginE ve))
                   | r0 :: _ -> (
                       match r0 with
                       | CoqParseTree.PndRetE (_, _, _) -> (
                           match v1 with
                           | [] -> false
                           | ve :: _ ->
                               equal_vpg_var (endE (CoqParseTree.Calv e)) (beginE ve))
                       | CoqParseTree.MatRetE (_, _, _, _, _) -> false)
                 in
                 let g vt =
                   let v1, t0 = vt in
                   (CoqParseTree.Calv e :: v1, tl t0)
                 in
                 filter_map v f g)
           m1)
  | CoqParseTree.PlnME m0 ->
      let m1 = vc_to_list m0 in
      concat
        (map
           (fun v0 ->
             let r, e = v0 in
             match r with
             | Some c -> (
                 match c with
                 | CoqParseTree.PndCalE (_, _, _) ->
                     let f vt =
                       let v1, t0 = vt in
                       match t0 with
                       | [] -> (
                           match v1 with
                           | [] -> false
                           | ve :: _ ->
                               equal_vpg_var (endE (CoqParseTree.Plnv e)) (beginE ve))
                       | r0 :: _ -> (
                           match r0 with
                           | CoqParseTree.PndRetE (_, _, _) -> (
                               match v1 with
                               | [] -> false
                               | ve :: _ ->
                                   equal_vpg_var (endE (CoqParseTree.Plnv e))
                                     (beginE ve))
                           | CoqParseTree.MatRetE (_, _, _, _, _) -> false)
                     in
                     let g vt =
                       let v1, t0 = vt in
                       (CoqParseTree.Plnv e :: v1, t0)
                     in
                     filter_map v f g
                 | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                     let f vt =
                       let v1, t0 = vt in
                       match t0 with
                       | [] -> false
                       | r0 :: _ -> (
                           match r0 with
                           | CoqParseTree.PndRetE (_, _, _) -> false
                           | CoqParseTree.MatRetE (l', a', l1', b', l2') -> (
                               ((((equal_vpg_var l l' && equal_vpg_var l1 l1')
                                 && equal_vpg_var l2 l2')
                                && String.equal a a')
                               && String.equal b b')
                               &&
                               match v1 with
                               | [] -> false
                               | ve :: _ -> (
                                   match ve with
                                   | CoqParseTree.Retv _ ->
                                       goEps rules (CoqParseTree.Plnv e)
                                   | _ ->
                                       equal_vpg_var (endE (CoqParseTree.Plnv e))
                                         (beginE ve))))
                     in
                     let g vt =
                       let v1, t0 = vt in
                       (CoqParseTree.Plnv e :: v1, t0)
                     in
                     filter_map v f g)
             | None ->
                 let f vt =
                   let v1, t0 = vt in
                   match t0 with
                   | [] -> (
                       match v1 with
                       | [] -> false
                       | ve :: _ ->
                           equal_vpg_var (endE (CoqParseTree.Plnv e)) (beginE ve))
                   | r0 :: _ -> (
                       match r0 with
                       | CoqParseTree.PndRetE (_, _, _) -> (
                           match v1 with
                           | [] -> false
                           | ve :: _ ->
                               equal_vpg_var (endE (CoqParseTree.Plnv e)) (beginE ve))
                       | CoqParseTree.MatRetE (_, _, _, _, _) -> false)
                 in
                 let g vt =
                   let v1, t0 = vt in
                   (CoqParseTree.Plnv e :: v1, t0)
                 in
                 filter_map v f g)
           m1)
  | CoqParseTree.RetME m0 ->
      let m1 = vb_to_list m0 in
      concat
        (map
           (fun v0 ->
             let r, e = v0 in
             match r with
             | Some c -> (
                 match c with
                 | CoqParseTree.PndCalE (_, _, _) ->
                     let f vt =
                       let v1, t0 = vt in
                       match t0 with
                       | [] -> (
                           match v1 with
                           | [] -> false
                           | ve :: _ ->
                               equal_vpg_var (endE (CoqParseTree.Retv e)) (beginE ve))
                       | r0 :: _ -> (
                           match r0 with
                           | CoqParseTree.PndRetE (_, _, _) -> (
                               match v1 with
                               | [] -> false
                               | ve :: _ ->
                                   equal_vpg_var (endE (CoqParseTree.Retv e))
                                     (beginE ve))
                           | CoqParseTree.MatRetE (_, _, _, _, _) -> false)
                     in
                     let g vt =
                       let v1, t0 = vt in
                       (CoqParseTree.Retv e :: v1, e :: t0)
                     in
                     filter_map v f g
                 | CoqParseTree.MatCalE (l, a, l1, b, l2) ->
                     let f vt =
                       let v1, t0 = vt in
                       match t0 with
                       | [] -> false
                       | r0 :: _ -> (
                           match r0 with
                           | CoqParseTree.PndRetE (_, _, _) -> false
                           | CoqParseTree.MatRetE (l', a', l1', b', l2') -> (
                               ((((equal_vpg_var l l' && equal_vpg_var l1 l1')
                                 && equal_vpg_var l2 l2')
                                && String.equal a a')
                               && String.equal b b')
                               &&
                               match v1 with
                               | [] -> false
                               | ve :: _ -> (
                                   match ve with
                                   | CoqParseTree.Retv _ ->
                                       goEps rules (CoqParseTree.Retv e)
                                   | _ ->
                                       equal_vpg_var (endE (CoqParseTree.Retv e))
                                         (beginE ve))))
                     in
                     let g vt =
                       let v1, t0 = vt in
                       (CoqParseTree.Retv e :: v1, e :: t0)
                     in
                     filter_map v f g)
             | None ->
                 let f vt =
                   let v1, t0 = vt in
                   match t0 with
                   | [] -> (
                       match v1 with
                       | [] -> false
                       | ve :: _ ->
                           equal_vpg_var (endE (CoqParseTree.Retv e)) (beginE ve))
                   | r0 :: _ -> (
                       match r0 with
                       | CoqParseTree.PndRetE (_, _, _) -> (
                           match v1 with
                           | [] -> false
                           | ve :: _ ->
                               equal_vpg_var (endE (CoqParseTree.Retv e)) (beginE ve))
                       | CoqParseTree.MatRetE (_, _, _, _, _) -> false)
                 in
                 let g vt =
                   let v1, t0 = vt in
                   (CoqParseTree.Retv e :: v1, e :: t0)
                 in
                 filter_map v f g)
           m1) *)
