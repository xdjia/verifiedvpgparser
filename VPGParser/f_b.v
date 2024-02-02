Definition f_b (m:ME) (V:list (list VE * list RetEdge)) : list (list VE * list RetEdge) :=
    match m with
    | PlnCME m =>
        let m := vc_set.elements m in
        let sth :=
          map (
            fun vt : (list VE * list RetEdge) =>
              let (v,T) := vt in
              let g (rr: option CalEdge * PlnEdge) : PlnEdge := 
                (snd rr) in
              let f (rr: option CalEdge * PlnEdge) :=
                let (r,e) := rr in
                match r with
                | Some (MatCalE L a L1 b L2) => 
                  match T with
                  | (MatRetE L' a' L1' b' L2')::_ =>
                    eqvv L L' &&
                    eqvv L1 L1' &&
                    eqvv L2 L2' &&
                    eq_str a a' &&
                    eq_str b b' &&
                    match v with
                    | (Retv _)::_ =>
                      goEps (Plnv e)
                    | ve::_ => eqvv (endE (Plnv e)) (beginE ve)
                    | _ => false
                    end
                  | _ => false
                  end
                | _ => 
                  match T with
                  | [] => 
                    match v with
                    | ve::_ => eqvv (endE (Plnv e)) (beginE ve)
                    | [] => false
                    end
                  | (PndRetE _ _ _)::_ =>
                    match v with
                    | ve::_ => eqvv (endE (Plnv e)) (beginE ve)
                    | [] => false
                    end
                  | (MatRetE _ _ _ _ _)::_ => false
                  end
                end
              in
              let ms := PreTimed.nodup ec_inlist (filter_map m f g) in
              map (fun e => (Plnv e::v, T)) ms
          ) V
        in
        concat sth

    | CalCME m =>
        let m := va_set.elements m in
        let sth :=
          map (
            fun vt : (list VE * list RetEdge) =>
              let (v,T) := vt in
              let g (rr: option CalEdge * CalEdge) : CalEdge := 
                (snd rr) in
              let f (rr: option CalEdge * CalEdge) :=
                let (r,e) := rr in
                match r with
                | Some (MatCalE L a L1 b L2) => 
                  match T with
                  | (MatRetE L' a' L1' b' L2')::_ =>
                    eqvv L L' &&
                    eqvv L1 L1' &&
                    eqvv L2 L2' &&
                    eq_str a a' &&
                    eq_str b b' &&
                    match v with
                    | (Retv _)::_ =>
                      goEps (Calv e)
                    | ve::_ => eqvv (endE (Calv e)) (beginE ve)
                    | _ => false
                    end
                  | _ => false
                  end
                | _ => 
                  match T with
                  | [] => 
                    match v with
                    | ve::_ => eqvv (endE (Calv e)) (beginE ve)
                    | [] => false
                    end
                  | (PndRetE _ _ _)::_ =>
                    match v with
                    | ve::_ => eqvv (endE (Calv e)) (beginE ve)
                    | [] => false
                    end
                  | (MatRetE _ _ _ _ _)::_ => false
                  end
                end
              in
              let ms := PreTimed.nodup ea_inlist (filter_map m f g) in
              map (fun e => (Calv e::v, tl T)) ms
          ) V
        in
        concat sth

    | RetCME m =>
        let m := vb_set.elements m in
        let sth :=
          map (
            fun vt : (list VE * list RetEdge) =>
              let (v,T) := vt in
              let g (rr: option CalEdge * RetEdge) : RetEdge := 
                (snd rr) in
              let f (rr: option CalEdge * RetEdge) :=
                let (r,e) := rr in
                match r with
                | Some (MatCalE L a L1 b L2) => 
                  match T with
                  | (MatRetE L' a' L1' b' L2')::_ =>
                    eqvv L L' &&
                    eqvv L1 L1' &&
                    eqvv L2 L2' &&
                    eq_str a a' &&
                    eq_str b b' &&
                    match v with
                    | (Retv _)::_ =>
                      goEps (Retv e)
                    | ve::_ => eqvv (endE (Retv e)) (beginE ve)
                    | _ => false
                    end
                  | _ => false
                  end
                | _ => 
                  match T with
                  | [] => 
                    match v with
                    | ve::_ => eqvv (endE (Retv e)) (beginE ve)
                    | [] => false
                    end
                  | (PndRetE _ _ _)::_ =>
                    match v with
                    | ve::_ => eqvv (endE (Retv e)) (beginE ve)
                    | [] => false
                    end
                  | (MatRetE _ _ _ _ _)::_ => false
                  end
                end
              in
              let ms := PreTimed.nodup eb_inlist (filter_map m f g) in
              map (fun e => (Retv e::v, e::T)) ms
          ) V
        in
        concat sth

    end.
