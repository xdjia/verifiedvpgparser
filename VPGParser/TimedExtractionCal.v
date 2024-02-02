(** This file provides sub-monadic functions for the function [extract']
    defined in the module [TimedExtraction]. *)

(* begin hide *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

Require Import Program.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Wf.
Require Import Coq.Unicode.Utf8_core.
Require Import Lia.
Require Import Arith.PeanoNat.
Require Import Monad.
Require Import MonadicUtils.

Require Import Misc.
Import Misc.Basic.
Import Misc.vpg.

Require Import Misc.

Require Import PreTimed.

Require Import TimedExtractionPln.

Module TimedExtractionCal (G:Def.VPG).

  Module TimedExtractionPln := TimedExtractionPln (G).

  Import TimedExtractionPln.
  Import ExtractionWNoDup.
  Import Transducer.TimedSets.Parser.PreTimed.
  Import Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Tacs.
  Import Transducer.TimedSets.Parser.
  Import Transducer.TimedSets.
  Import Transducer.PreTransducer.
  Import Transducer.Transducer2.

  Opaque cost_eqvv.
  Opaque cost_endE.
  Opaque cost_beginE.
  Opaque cost_andb.

  Definition cost_if_stmt := 1.
  Definition cost_filter_reti_var := 1.
  Definition time_filter_reti_base := 1.

  Opaque cons_ct.
  Opaque time_pair.

  Definition cost_snd := 1.
  Opaque cost_snd.

  Lemma bound_filter_map: ∀ A B f (g:A->B) m, 
    |filter_map m f g| <= |m|.
  Proof.
    intros.
    unfold filter_map.
    rewrite map_length.
    induction m. simpl; eauto.
    simpl.
    destruct_with_eqn (f a); simpl; eauto.
    lia.
  Qed.


  Section timed_Cal.
    Variable A: Type.

    Definition cost_var_f_Cal_branch1_Cal := 1.
    Definition cost_var_f_Cal_branch2_Cal := 1.
    Definition cost_var_f_Cal_branch3_Cal := 1.
    Definition cost_var_f_Cal_branch4_Cal := 1.
    Definition cost_var_f_Cal_branch5_Cal := 1.

    Definition f_Cal v T (rr: option CalEdge * CalEdge) :=
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
      end.

    Definition cost_f_Cal_branch1 := 1.
    Definition cost_f_Cal_branch2 := 1.
    Definition cost_f_Cal_branch3 := 1.
    Definition cost_f_Cal_branch4 := 1.
    Definition cost_f_Cal_branch5 := 1.
    Definition cost_f_Cal_branch6 := 1.
    Definition cost_f_Cal_branch7 := 1.
    Definition cost_f_Cal_branch8 := 1.
    Definition cost_f_Cal_branch9 := 1.
    Opaque cost_f_Cal_branch1.
    Opaque cost_f_Cal_branch2.
    Opaque cost_f_Cal_branch3.
    Opaque cost_f_Cal_branch4.
    Opaque cost_f_Cal_branch5.
    Opaque cost_f_Cal_branch6.
    Opaque cost_f_Cal_branch7.
    Opaque cost_f_Cal_branch8.
    Opaque cost_f_Cal_branch9.


    Definition cost_f_Cal (v:list VE) (T:list RetEdge) (rr: option CalEdge * CalEdge) : nat
    :=
      match rr with 
      | (r,e) =>
        match r with
        | Some (MatCalE L a L1 b L2) => 
          match T with
          | (MatRetE L' a' L1' b' L2')::_ => 
            match v with
            | (Retv _)::_ =>
                cost_goEps P (Calv e) +
                cost_eqvv L L' +
                cost_eqvv L1 L1' +
                cost_eqvv L2 L2' +
                5 * cost_andb
                + 2 * cost_eq_str + cost_f_Cal_branch1
            | ve::_ =>
              cost_endE + cost_beginE + 
              cost_eqvv (endE (Calv e)) (beginE ve) +
              cost_eqvv L L' +
              cost_eqvv L1 L1' +
              cost_eqvv L2 L2' +
              2 * cost_eq_str
              + 5 * cost_andb + cost_f_Cal_branch2
            | _ =>
              cost_f_Cal_branch3
            end
          | _ =>
            cost_f_Cal_branch4
          end
        | _ =>
          match T with
          | [] =>
            match v with
            | ve::_ =>
            cost_endE + (cost_beginE + (vpg.cost_eqvv (endE (Calv e)) (beginE ve) + cost_f_Cal_branch5))
            | [] =>  
              cost_f_Cal_branch6
            end
          | (PndRetE _ _ _)::_ =>
            match v with
            | ve::_ => 
            cost_endE + (cost_beginE + (vpg.cost_eqvv (endE (Calv e)) (beginE ve) + cost_f_Cal_branch7))
            | [] => 
              cost_f_Cal_branch8
            end
          | (MatRetE _ _ _ _ _)::_ =>
            cost_f_Cal_branch9
          end
        end
      end.

    Opaque endE.
    Opaque _endE.
    Opaque beginE.
    Opaque _beginE.
    Opaque cost_endE.
    Opaque cost_beginE.
    Opaque cost_eq_str.

    Program Definition f_Cal' v T (rr: option CalEdge * CalEdge) 
    : {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !}
    :=
      match rr as rr' return (rr=rr')-> 
        {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !}
      with 
      | (r,e) =>
        fun hyp =>
        match r as r' return (r=r')->
          {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !}
        with
        | Some (MatCalE L a L1 b L2) => 
          fun hyp =>
          match T as T' return (T=T')-> 
            {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !}
          with
          | (MatRetE L' a' L1' b' L2')::_ =>
            fun hyp =>
            match v as v' return (v=v')-> 
            {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !}
            with
            | (Retv _)::_ =>
              fun hyp =>
                bb <- goEps' (Calv e);
                out1 <- eqvv' L L';
                out2 <- eqvv' L1 L1';
                out3 <- eqvv' L2 L2';
                out4 <- eq_str' a a';
                out5 <- eq_str' b b';
                += 5 * cost_andb + cost_f_Cal_branch1;
                <==
                bb && out1 && out2 && out3 && out4 && out5
            | ve::_ => fun hyp =>
              out1 <- eqvv' L L';
              out2 <- eqvv' L1 L1';
              out3 <- eqvv' L2 L2';
              out4 <- eq_str' a a';
              out5 <- eq_str' b b';
              _l1 <- _endE (Calv e);
              _l2 <- _beginE ve;
              out0 <- eqvv' _l1 _l2;
              += 5 * cost_andb + cost_f_Cal_branch2;
              <== 
              out0 && out1 && out2 && out3 && out4 && out5
            | _ => fun hyp => 
              += cost_f_Cal_branch3;
              <== false
            end (eq_refl v)
          | _ =>
            fun hyp =>
            += cost_f_Cal_branch4;
            <== false
          end (eq_refl T)
        | _ => 
          fun hyp =>
          match T as T' return (T=T')-> 
            {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !}
          with
          | [] =>
            fun hyp =>
            match v as v' return (v=v')-> 
            {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !} with
            | ve::_ =>
              fun hyp =>
              _l1 <- _endE (Calv e);
              _l2 <- _beginE ve;
              out <- eqvv' _l1 _l2;
              += cost_f_Cal_branch5;
              <== out
            | [] =>
              fun hyp =>
              += cost_f_Cal_branch6;
              <== false
            end (eq_refl v)
          | (PndRetE _ _ _)::_ =>
            fun hyp =>
            match v as v' return (v=v')-> 
            {! y !:! bool !<! c !>! c = cost_f_Cal v T rr /\ y = f_Cal v T rr !} with
            | ve::_ => 
              fun hyp =>
              _l1 <- _endE (Calv e);
              _l2 <- _beginE ve;
              out <- eqvv' _l1 _l2;
              += cost_f_Cal_branch7;
              <== out
            | [] => 
              fun hyp =>
            += cost_f_Cal_branch8;
            <== false
            end (eq_refl v)
          | (MatRetE _ _ _ _ _)::_ =>
            fun hyp => 
            += cost_f_Cal_branch9;
            <== false
          end (eq_refl T)
        end (eq_refl r)
      end (eq_refl rr).

    Next Obligation.
      simpl.
      getAnd; eauto.
      lia.
    Qed.

    Next Obligation.
      simpl.
      getAnd; eauto.
      lia.
      repeat rewrite <- andb_assoc.
      rewrite andb_comm.
      repeat rewrite andb_assoc.
      easy.
    Qed.

    Next Obligation.
      simpl.
      getAnd; eauto.
      lia.
      repeat rewrite <- andb_assoc.
      rewrite andb_comm.
      repeat rewrite andb_assoc.
      easy.
    Qed.

    Next Obligation.
      simpl.
      getAnd; eauto.
      lia.
      repeat rewrite <- andb_assoc.
      rewrite andb_comm.
      repeat rewrite andb_assoc.
      easy.
    Qed.

    Definition cost_g_Cal := cost_snd.
    Program Definition g_Cal' (rr: option CalEdge * CalEdge) 
    : {! y !:! CalEdge !<! c !>! c = cost_g_Cal /\ y = snd rr !}
    := += cons_snd; <== (snd rr).


    Definition cost_filter_Cal_branch1 := 1.
    Definition cost_filter_Cal_branch2 := 1.
    Opaque cost_filter_Cal_branch1.
    Opaque cost_filter_Cal_branch2.

    Fixpoint cost_filter_Cal v T m : nat :=
      match m as m' with 
      | [] => cost_filter_Cal_branch1
      | x::m' =>
        cost_f_Cal v T x +
        cost_if_stmt +
        cost_filter_Cal_branch2 +
        if (f_Cal v T x) then
        cost_g_Cal + cost_filter_Cal v T m' +
        cons_ct
        else
        cost_filter_Cal v T m'
      end.

    Definition filter_Cal v T m :=
      filter_map m (f_Cal v T) snd.


    Program Fixpoint filter_Cal' v T m 
    : {! y !:! _ !<! c !>! c = cost_filter_Cal v T m /\ y = filter_Cal v T m !}
    :=
    match m as m' with 
    | [] => += cost_filter_Cal_branch1; <== []
    | x::m' =>
      fx <- f_Cal' v T x;
      if dec fx then 
      gx <- g_Cal' x;
      res <- filter_Cal' v T m';
      out <- cons' _ gx res;
      += cost_filter_Cal_branch2 + cost_if_stmt; <== out
      else
      out <- filter_Cal' v T m';
      += cost_filter_Cal_branch2 + cost_if_stmt; <== out
    end.

    Next Obligation.
      getAnd. rewrite e. lia.
      simpl.
      unfold filter_Cal.
      rewrite filter_map_split.
      unfold filter_map at 2.
      unfold filter. rewrite e.
      simpl. auto.
    Qed.

    Next Obligation.
      getAnd. rewrite e. lia.
      simpl.
      unfold filter_Cal.
      rewrite filter_map_split.
      unfold filter_map at 2.
      unfold filter. rewrite e.
      simpl. auto.
    Qed.


    Definition cost_ea_inlist_branch1 := 1.
    Definition cost_ea_inlist_branch2 := 1.
    Definition cost_ea_inlist_branch3 := 1.
    Opaque cost_ea_inlist_branch1.
    Opaque cost_ea_inlist_branch2.
    Opaque cost_ea_inlist_branch3.

    Fixpoint cost_ea_inlist x l :=
      match l with 
      | [] => cost_ea_inlist_branch1
      | y::l' =>
        timed_ea.cost_compare x y +
        match ea_as_OT.compare x y with 
        | Eq => cost_ea_inlist_branch2
        | _ => cost_ea_inlist x l' + cost_ea_inlist_branch3
        end
      end.

    Lemma bound_cost_ea_inlist: ∃ k b, ∀ x l, cost_ea_inlist x l <= k * |l| + b.
    Proof.
      destruct (timed_ea.bound_cost_compare) as [k h].
      exists (k+cost_ea_inlist_branch3), (cost_ea_inlist_branch1+cost_ea_inlist_branch2).
      intros.
      induction l. simpl. lia.
      simpl. destruct_with_eqn (ea_as_OT.compare x a); pose (h x a); lia.
    Qed.
    

    Program Fixpoint ea_inlist' x l 
    :{! y !:! bool !<! c !>! c = cost_ea_inlist x l /\ y = ea_inlist x l !}
    :=
      match l as l' return (l=l')->
        {! y !:! bool !<! c !>! c = cost_ea_inlist x l /\ y = ea_inlist x l !}
      with
      | [] => 
        fun hyp =>
        += cost_ea_inlist_branch1; <== false
      | y::l' =>
        fun hyp =>
        out1 <- timed_ea.compare' x y;
        out <- 
          match out1 as out1' return (out1=out1')->
            {! res !:! bool !<! c !>! c = match ea_as_OT.compare x y with 
            | Eq => cost_ea_inlist_branch2
            | _ => cost_ea_inlist x l' + cost_ea_inlist_branch3
            end /\ res = match ea_as_OT.compare x y with 
            | Eq => true
            | _ => ea_inlist x l'
            end !}
          with
          | Eq => fun hyp => += cost_ea_inlist_branch2; <== true
          | _ => fun hyp => 
            out <- ea_inlist' x l';
            += cost_ea_inlist_branch3; <== out
          end (eq_refl out1);
        <== out
      end (eq_refl l).

    Next Obligation.
      rewrite hyp.
      getAnd; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      getAnd; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      getAnd; auto.
    Defined.

    Next Obligation.
      destruct_with_eqn (ea_as_OT.compare x y).

      all: (repeat (getAnd + rewrite Heqc + unfold cost_ea_inlist +
        unfold ea_inlist + simpl + easy + lia)).
    Defined.


    Definition cost_nodup_Cal v t m :=
      cost_filter_Cal v t m +
      cost_nodup _ ea_inlist cost_ea_inlist (filter_Cal v t m).

    Program Definition nodup_Cal' v t m
    : {! y !:! _ !<! c !>! c = cost_nodup_Cal v t m /\
      y = nodup ea_inlist (filter_Cal v t m) !}
    :=
      m' <- filter_Cal' v t m ;
      out <- nodup' _ ea_inlist' m';
      <== out.

    Next Obligation.
      getAnd; eauto.
      unfold cost_nodup_Cal.
      lia.
    Qed.

    Definition cost_map_sub_Cal vt m :=
      match vt with 
      | (v,t) =>
      cost_nodup_Cal v t m +
      cost_map _ (fun _ => cons_ct+time_pair + cost_tail _ t) 
        (nodup ea_inlist (filter_Cal v t m))
      end.

    Definition map_sub_Cal vt m :=
      match vt with 
      | (v,t) =>
        map (fun e => (Calv e::v, tl t)) 
          (nodup ea_inlist (filter_Cal v t m))
      end.

    Program Definition map_sub_Cal' vt m 
    : {! y !:! _ !<! c !>! c = cost_map_sub_Cal vt m /\ 
      y = map_sub_Cal vt m !}
    :=
    match vt as vt' return (vt=vt') -> 
      {! y !:! _ !<! c !>! c = cost_map_sub_Cal vt m /\ 
      y = map_sub_Cal vt m !}
    with 
    | (v,t) => 
    fun hyp =>
      m <- nodup_Cal' v t m;
      out <- map' _ _ (fun e => (Calv e::v, tl t))
        (fun _ => cons_ct+time_pair+cost_tail _ t)
        (fun e => 
          ve <- cons' _ (Calv e) v;
          t' <- tail' _ t;
          out <- pair' _ _ ve t';
          <== out) m;
      <== out
    end (eq_refl vt).

    Next Obligation.
      getAnd; eauto. unfold cost_map_sub_Cal.
      simpl. eauto. lia.
    Qed.

    Next Obligation.
      getAnd; eauto. unfold cost_map_sub_Cal.
      simpl. eauto. 
    Qed.

    Definition cost_map_v_Cal m V :=
      cost_map _ (fun vt => cost_map_sub_Cal vt m) V.

    Definition map_v_Cal m V := map (fun vt => map_sub_Cal vt m) V.
    Program Definition map_v_Cal' m V 
    : {! y !:! _ !<! c !>! c = cost_map_v_Cal m V /\ 
      y = map_v_Cal m V !}
    := 
      map' _ _ 
        (fun vt => map_sub_Cal vt m)
        (fun vt => cost_map_sub_Cal vt m)
        (fun vt => map_sub_Cal' vt m) V.

    Definition cost_elements_Cal := 1.
    Opaque cost_elements_Cal.

    Definition cost_inner_Cal m V := 
      cost_elements_Cal +
      cost_map_v_Cal ((va_set.elements m)) V + 
      cost_concat _ (map_v_Cal (va_set.elements m) V).

    Definition inner_Cal m V := concat (map_v_Cal (va_set.elements m) V).

    Program Definition va_elements (m:va_set.t) 
    : {! res !:! list va_set.elt !<! c !>! 
      c = cost_elements_Cal /\ res = va_set.elements m !}
    := += cost_elements_Cal; <== va_set.elements m.

    Program Definition inner_Cal' m V 
    : {! y !:! _ !<! c !>! c = cost_inner_Cal m V /\ 
      y = inner_Cal m V !}
    :=
      m' <- va_elements m;
      m' <- map_v_Cal' m' V;
      out <- _concat _ m';
      <== out.

    Next Obligation.
      getAnd; eauto.
      unfold cost_inner_Cal; eauto.
      lia.
    Defined.

    Lemma L_fb_fb'_Cal: ∀ m V, f_b (CalCME m) V = inner_Cal m V.
    Proof.
      easy.
    Qed.

  End timed_Cal.


  Section bound_Cal.

    Lemma bound_cost_f_Cal :
    ∃ k, 
    ∀ v t rr,
      cost_f_Cal v t rr <= k.
    Proof.
      destruct bound_cost_goEps as [k [b He]].
      destruct bound_cost_eqvv as [kv Hv].
      exists (
        (k * | P | + b + 3 * kv 
                + 5 * cost_andb
                + 2 * cost_eq_str + cost_f_Cal_branch1) +
          (cost_endE + cost_beginE + 
              4 * kv + 2 * cost_eq_str
              + 5 * cost_andb + cost_f_Cal_branch2) +
        cost_f_Cal_branch3 +
        cost_f_Cal_branch4 +
                (cost_endE + cost_beginE + kv + cost_f_Cal_branch5) +
          cost_f_Cal_branch6 +
                (cost_endE + cost_beginE + kv + cost_f_Cal_branch7) +
          cost_f_Cal_branch8 +
        cost_f_Cal_branch9).

      intros.
      unfold cost_f_Cal.
      destruct rr.
      destruct o.
      destruct c0.
      all: try destruct t.
      all: try destruct r.
      all: try destruct v.
      all: try destruct v.

      all: try lia.

      Ltac boundEqVV Hv h :=
        match h with 
        | (cost_eqvv ?x ?y) =>
          match goal with
          | h1: cost_eqvv x y <= _ |- _ => auto 
          | _ => pose (Hv x y)
          end
        | (cost_eqvv ?x ?y) + ?h' =>
          match goal with
        | h1: cost_eqvv x y <= _ |- _ => boundEqVV Hv h'
          | _ => pose (Hv x y)
          end
        | _ + ?h' =>
          boundEqVV Hv h'
        | _ => auto
        end.

      all: repeat rewrite <- Nat.add_assoc.
      all: repeat match goal with
      | |- ?h <= _ =>
        try boundEqVV Hv h
        ; try lia
      end.

      match goal with
      | |- cost_goEps P ?x + _ <= _ =>
        pose (He P x)
      end.
      lia.
    Qed.

    Lemma bound_cost_filter_Cal: ∃ k b, 
      ∀ v T m, cost_filter_Cal v T m <= k*|m|+b.
    Proof.
      destruct bound_cost_f_Cal as [k h1].
      exists (k + cost_if_stmt +
      cost_filter_Cal_branch2 + cost_g_Cal + cons_ct), cost_filter_Cal_branch1.
      intros.
      induction m. simpl. lia.
      simpl.
      pose (h1 v T a).
      destruct_with_eqn (f_Cal v T a);
      nia.
    Qed.



    Lemma bound_cost_nodup_Cal: 
    ∃ k k1 b,
    ∀ v t m,
    cost_nodup_Cal v t m <= k*|m|*|m|+k1*|m|+b.

    Proof.
      destruct (bound_cost_filter_Cal) as [k [b h1]].
      destruct bound_cost_ea_inlist as [k1 [b1 h2]].

      exists k1, (k+b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2), (b+b1+time_nodup_branch0).

      intros.
      unfold cost_nodup_Cal.
      specialize h1 with v t m.

      assert (| (filter_Cal v t m) | <= |m|).
      1:{
        unfold filter_Cal.
        apply (bound_filter_map).
      }

      Opaque time_nodup_branch1.
      Opaque time_nodup_branch2.

      match goal with
      | h: | ?x | <= |m| |- _ =>
      set (a:=x);
      fold a in h
      end.

      assert (cost_nodup CalEdge ea_inlist cost_ea_inlist a
        <= (k1 * |a| + b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2) * |a| + 
          time_nodup_branch0).
      1:{
        induction a.
        simpl. lia.

        getH. tac_app. simpl in *; lia.
        simpl.

        pose (h2 a a0).

        destruct_with_eqn (ea_inlist a a0); nia. 
      }

      assert ((k1 * | a | + b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2) <=
      (k1 * | m | + b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2)).
      nia. nia.
    Qed.

    Lemma bound_cost_map_sub_Cal: ∃ k k1 b, ∀ vt m, 
    cost_map_sub_Cal vt m <= k*|m|*|m|+k1*|m|+b.
    Proof.
      pose (bound_cost_nodup_Cal).

      destruct e as [k [k1 [b1 h1]]].

      exists k, 
        (k1+cons_ct +cons_ct + time_pair+ time_map_branch2 + tail_bt + tail_inner_time),
        (time_map_branch1+b1).
      
      intros.
      unfold cost_map_sub_Cal.
      destruct vt.

      specialize h1 with l l0 m.

      assert (| (nodup ea_inlist (filter_Cal l l0 m)) | <= |m|).
      assert (| (nodup ea_inlist (filter_Cal l l0 m)) | <= |filter_Cal l l0 m|).
      apply (bound_nodup); eauto.
      assert (| (filter_Cal l l0 m) | <= |m|).
      unfold filter_Cal.

      apply bound_filter_map. lia.

      pose (bound_cost_map).

      assert (cost_tail RetEdge l0 <= tail_bt + tail_inner_time)
      by (unfold cost_tail; destruct l0; lia).

      assert (cost_map ea_as_OT.t
        (λ _ : ea_as_OT.t, cons_ct + time_pair + cost_tail RetEdge l0)
        (nodup ea_inlist (filter_Cal l l0 m))
        <= (cons_ct +cons_ct + time_pair+ time_map_branch2+ tail_bt + tail_inner_time) * | m | +
        (time_map_branch1)
      ).

      1:{
        clear H h1. induction m. simpl. lia.
        simpl.
        unfold filter_Cal in *. rewrite filter_map_split.
        unfold filter_map at 1. simpl.

        destruct_with_eqn (f_Cal l l0 a);
        unfold map;
        simpl;
        unfold cost_map in *;
        destruct_with_eqn (ea_inlist (snd a) (filter_map m (f_Cal l l0) snd));
        nia.
      }

      unfold ea_as_OT.t in H1.
      nia.
    Qed.

    Lemma bound_cost_map_v_Cal: 
    ∃ k k1 b b1,
    ∀ m V, 
    cost_map_v_Cal m V <= (k*|m|*|m|+k1*|m|+b) * |V| + b1.
    Proof.
      destruct (bound_cost_map_sub_Cal) as [k [k1 [b h]]].
      exists (k), k1, (b+cons_ct + time_map_branch2), time_map_branch1.
      intros.
      induction V. simpl. lia.
      simpl.
      specialize h with a m.
      lia.
    Qed.

    Lemma bound_cost_inner_Cal : ∃ k k1 b b1, ∀ m V,
      cost_inner_Cal m V <= (k * |(va_set.elements m)| * |(va_set.elements m)| +
      k1 * |(va_set.elements m)| + b) * |V| + b1.
    Proof.
      destruct bound_cost_map_v_Cal as [k [k1 [b [b1 h1]]]].
      destruct (bound_cost_concat ((list VE * list RetEdge)))
        as [k1' [b1' [b2' h1']]].

      exists k, (k1+k1'), (b+b1'), (b2'+ b1+cost_elements_Cal).

      intros.
      specialize h1 with (va_set.elements m) V.

      unfold cost_inner_Cal.
      specialize h1' with (map_v_Cal (va_set.elements m) V) (| (va_set.elements m) |).

      getH. tac_app. intros.
      unfold map_v_Cal in H.
      apply_in_map.
      unfold map_sub_Cal in H. destruct x.
      subst.
      rewrite map_length.
      rewrite (bound_nodup).
      unfold filter_Cal.
      rewrite (bound_filter_map). auto.

      clear h1'.

      unfold map_v_Cal at 2 in H.
      rewrite map_length in H.

      match goal with
      | h: ?x <= ?a, h1: ?y <= ?b |- ?z + ?x + ?y <= ?p =>
      assert (x + y <= a + b) by nia
      ; replace p with (z + a + b)
      ; try nia
      end.



      assert (cost_elements_Cal +
        ((k * | (va_set.elements m) | * | (va_set.elements m) | +
          k1 * | (va_set.elements m) | + b) * | V | + b1) +
        ((k1' * | (va_set.elements m) | + b1') * | V | + b2') =
        (k * | (va_set.elements m) | * | (va_set.elements m) | +
        (k1 + k1') * | (va_set.elements m) | + (b + b1')) * 
        | V | + (b2' + b1) + cost_elements_Cal) as e by nia.
      
        match goal with
        | h: ?z = _ |- ?x = ?y =>
          replace x with z; try auto
        end.
        
    
        lia.
    Qed.
  End bound_Cal.

End TimedExtractionCal.

(* end hide *)
