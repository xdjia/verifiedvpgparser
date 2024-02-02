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

Require Import ExtractionW.

Module TimedExtractionPln (G:Def.VPG).
  Module ExtractionWNoDup := ExtractionWNoDup(G).

  Import ExtractionWNoDup.
  Import ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.
  Import ExtractionWNoDup.Transducer.TimedSets.Parser.
  Import ExtractionWNoDup.Transducer.TimedSets.
  Import ExtractionWNoDup.Transducer.PreTransducer.
  Import ExtractionWNoDup.Transducer.Transducer2.
  Import ExtractionWNoDup.Transducer.TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Tacs.


  Opaque cost_eqvv.
  (* Opaque t_cmp_string. *)
  (* Opaque t_ct. *)
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

  Section timed_Pln.
    Variable A: Type.

    Definition cost_var_f_pln_branch1_Pln := 1.
    Definition cost_var_f_pln_branch2_Pln := 1.
    Definition cost_var_f_pln_branch3_Pln := 1.
    Definition cost_var_f_pln_branch4_Pln := 1.
    Definition cost_var_f_pln_branch5_Pln := 1.

    Definition f_Pln v T (rr: option CalEdge * PlnEdge) :=
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
      end.

    Definition cost_f_pln_branch1 := 1.
    Definition cost_f_pln_branch2 := 1.
    Definition cost_f_pln_branch3 := 1.
    Definition cost_f_pln_branch4 := 1.
    Definition cost_f_pln_branch5 := 1.
    Definition cost_f_pln_branch6 := 1.
    Definition cost_f_pln_branch7 := 1.
    Definition cost_f_pln_branch8 := 1.
    Definition cost_f_pln_branch9 := 1.
    Opaque cost_f_pln_branch1.
    Opaque cost_f_pln_branch2.
    Opaque cost_f_pln_branch3.
    Opaque cost_f_pln_branch4.
    Opaque cost_f_pln_branch5.
    Opaque cost_f_pln_branch6.
    Opaque cost_f_pln_branch7.
    Opaque cost_f_pln_branch8.
    Opaque cost_f_pln_branch9.


    Definition cost_f_Pln (v:list VE) (T:list RetEdge) (rr: option CalEdge * PlnEdge) : nat
    :=
      match rr with 
      | (r,e) =>
        match r with
        | Some (MatCalE L a L1 b L2) => 
          match T with
          | (MatRetE L' a' L1' b' L2')::_ => 
            match v with
            | (Retv _)::_ =>
                cost_goEps P (Plnv e) +
                cost_eqvv L L' +
                cost_eqvv L1 L1' +
                cost_eqvv L2 L2' +
                5 * cost_andb
                + 2 * cost_eq_str + cost_f_pln_branch1
            | ve::_ =>
              cost_endE + cost_beginE + 
              cost_eqvv (endE (Plnv e)) (beginE ve) +
              cost_eqvv L L' +
              cost_eqvv L1 L1' +
              cost_eqvv L2 L2' +
              2 * cost_eq_str
              + 5 * cost_andb + cost_f_pln_branch2
            | _ =>
              cost_f_pln_branch3
            end
          | _ =>
            cost_f_pln_branch4
          end
        | _ =>
          match T with
          | [] =>
            match v with
            | ve::_ =>
            cost_endE + (cost_beginE + (vpg.cost_eqvv (endE (Plnv e)) (beginE ve) + cost_f_pln_branch5))
            | [] =>  
              cost_f_pln_branch6
            end
          | (PndRetE _ _ _)::_ =>
            match v with
            | ve::_ => 
            cost_endE + (cost_beginE + (vpg.cost_eqvv (endE (Plnv e)) (beginE ve) + cost_f_pln_branch7))
            | [] => 
              cost_f_pln_branch8
            end
          | (MatRetE _ _ _ _ _)::_ =>
            cost_f_pln_branch9
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

    Program Definition f_Pln' v T (rr: option CalEdge * PlnEdge) 
    : {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !}
    :=
      match rr as rr' return (rr=rr')-> 
        {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !}
      with 
      | (r,e) =>
        fun hyp =>
        match r as r' return (r=r')->
          {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !}
        with
        | Some (MatCalE L a L1 b L2) => 
          fun hyp =>
          match T as T' return (T=T')-> 
            {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !}
          with
          | (MatRetE L' a' L1' b' L2')::_ =>
            fun hyp =>
            match v as v' return (v=v')-> 
            {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !}
            with
            | (Retv _)::_ =>
              fun hyp =>
                bb <- goEps' (Plnv e);
                out1 <- eqvv' L L';
                out2 <- eqvv' L1 L1';
                out3 <- eqvv' L2 L2';
                out4 <- eq_str' a a';
                out5 <- eq_str' b b';
                += 5 * cost_andb + cost_f_pln_branch1;
                <==
                bb && out1 && out2 && out3 && out4 && out5
            | ve::_ => fun hyp =>
              out1 <- eqvv' L L';
              out2 <- eqvv' L1 L1';
              out3 <- eqvv' L2 L2';
              out4 <- eq_str' a a';
              out5 <- eq_str' b b';
              _l1 <- _endE (Plnv e);
              _l2 <- _beginE ve;
              out0 <- eqvv' _l1 _l2;
              += 5 * cost_andb + cost_f_pln_branch2;
              <== 
              out0 && out1 && out2 && out3 && out4 && out5
            | _ => fun hyp => 
              += cost_f_pln_branch3;
              <== false
            end (eq_refl v)
          | _ =>
            fun hyp =>
            += cost_f_pln_branch4;
            <== false
          end (eq_refl T)
        | _ => 
          fun hyp =>
          match T as T' return (T=T')-> 
            {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !}
          with
          | [] =>
            fun hyp =>
            match v as v' return (v=v')-> 
            {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !} with
            | ve::_ =>
              fun hyp =>
              _l1 <- _endE (Plnv e);
              _l2 <- _beginE ve;
              out <- eqvv' _l1 _l2;
              += cost_f_pln_branch5;
              <== out
            | [] =>
              fun hyp =>
              += cost_f_pln_branch6;
              <== false
            end (eq_refl v)
          | (PndRetE _ _ _)::_ =>
            fun hyp =>
            match v as v' return (v=v')-> 
            {! y !:! bool !<! c !>! c = cost_f_Pln v T rr /\ y = f_Pln v T rr !} with
            | ve::_ => 
              fun hyp =>
              _l1 <- _endE (Plnv e);
              _l2 <- _beginE ve;
              out <- eqvv' _l1 _l2;
              += cost_f_pln_branch7;
              <== out
            | [] => 
              fun hyp =>
            += cost_f_pln_branch8;
            <== false
            end (eq_refl v)
          | (MatRetE _ _ _ _ _)::_ =>
            fun hyp => 
            += cost_f_pln_branch9;
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

    Definition cost_g_Pln := cost_snd.
    Program Definition g_Pln' (rr: option CalEdge * PlnEdge) 
    : {! y !:! PlnEdge !<! c !>! c = cost_g_Pln /\ y = snd rr !}
    := += cost_snd; <== (snd rr).


    Definition cost_filter_Pln_branch1 := 1.
    Definition cost_filter_Pln_branch2 := 1.
    Opaque cost_filter_Pln_branch1.
    Opaque cost_filter_Pln_branch2.

    Fixpoint cost_filter_Pln v T m : nat :=
      match m as m' with 
      | [] => cost_filter_Pln_branch1
      | x::m' =>
        cost_f_Pln v T x +
        cost_if_stmt +
        cost_filter_Pln_branch2 +
        if (f_Pln v T x) then
        cost_g_Pln + cost_filter_Pln v T m' +
        cons_ct
        else
        cost_filter_Pln v T m'
      end.

    Definition filter_Pln v T m :=
      Parser.filter_map m (f_Pln v T) snd.

    Program Fixpoint filter_Pln' v T m 
    : {! y !:! _ !<! c !>! c = cost_filter_Pln v T m /\ y = filter_Pln v T m !}
    :=
    match m as m' with 
    | [] => += cost_filter_Pln_branch1; <== []
    | x::m' =>
      fx <- f_Pln' v T x;
      if dec fx then 
      gx <- g_Pln' x;
      res <- filter_Pln' v T m';
      out <- cons' _ gx res;
      += cost_filter_Pln_branch2 + cost_if_stmt; <== out
      else
      out <- filter_Pln' v T m';
      += cost_filter_Pln_branch2 + cost_if_stmt; <== out
    end.

    Next Obligation.
      getAnd. rewrite e. lia.
      simpl.
      unfold filter_Pln.
      rewrite filter_map_split.
      unfold filter_map at 2.
      unfold filter. rewrite e.
      simpl. auto.
    Qed.

    Next Obligation.
      getAnd. rewrite e. lia.
      simpl.
      unfold filter_Pln.
      rewrite filter_map_split.
      unfold filter_map at 2.
      unfold filter. rewrite e.
      simpl. auto.
    Qed.


    Definition cost_ec_inlist_branch1 := 1.
    Definition cost_ec_inlist_branch2 := 1.
    Definition cost_ec_inlist_branch3 := 1.
    Opaque cost_ec_inlist_branch1.
    Opaque cost_ec_inlist_branch2.
    Opaque cost_ec_inlist_branch3.

    Fixpoint cost_ec_inlist x l :=
      match l with 
      | [] => cost_ec_inlist_branch1
      | y::l' =>
        timed_ec.cost_compare x y +
        match ec_as_OT.compare x y with 
        | Eq => cost_ec_inlist_branch2
        | _ => cost_ec_inlist x l' + cost_ec_inlist_branch3
        end
      end.

    Lemma bound_cost_ec_inlist: ∃ k b, ∀ x l, cost_ec_inlist x l <= k * |l| + b.
    Proof.
      destruct (timed_ec.bound_cost_compare) as [k h].
      exists (k+cost_ec_inlist_branch3), (cost_ec_inlist_branch1+cost_ec_inlist_branch2).
      intros.
      induction l. simpl. lia.
      simpl. destruct_with_eqn (ec_as_OT.compare x a); pose (h x a); lia.
    Qed.
    

    Program Fixpoint ec_inlist' x l 
    :{! y !:! bool !<! c !>! c = cost_ec_inlist x l /\ y = ec_inlist x l !}
    :=
      match l as l' return (l=l')->
        {! y !:! bool !<! c !>! c = cost_ec_inlist x l /\ y = ec_inlist x l !}
      with
      | [] => 
        fun hyp =>
        += cost_ec_inlist_branch1; <== false
      | y::l' =>
        fun hyp =>
        out1 <- timed_ec.compare' x y;
        out <- 
          match out1 as out1' return (out1=out1')->
            {! res !:! bool !<! c !>! c = match ec_as_OT.compare x y with 
            | Eq => cost_ec_inlist_branch2
            | _ => cost_ec_inlist x l' + cost_ec_inlist_branch3
            end /\ res = match ec_as_OT.compare x y with 
            | Eq => true
            | _ => ec_inlist x l'
            end !}
          with
          | Eq => fun hyp => += cost_ec_inlist_branch2; <== true
          | _ => fun hyp => 
            out <- ec_inlist' x l';
            += cost_ec_inlist_branch3; <== out
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
      destruct_with_eqn (ec_as_OT.compare x y).

      all: (repeat (getAnd + rewrite Heqc + unfold cost_ec_inlist +
        unfold ec_inlist + simpl + easy + lia)).
    Defined.

    Import PreTimed.

    Definition cost_nodup_Pln v t m :=
      cost_filter_Pln v t m +
      PreTimed.cost_nodup _ ec_inlist cost_ec_inlist (filter_Pln v t m).

    Program Definition nodup_Pln' v t m
    : {! y !:! _ !<! c !>! c = cost_nodup_Pln v t m /\
      y = PreTimed.nodup ec_inlist (filter_Pln v t m) !}
    :=
      m' <- filter_Pln' v t m ;
      out <- PreTimed.nodup' _ ec_inlist' m';
      <== out.

    Next Obligation.
      getAnd; eauto.
      unfold cost_nodup_Pln.
      lia.
    Qed.

    Definition cost_map_sub_Pln vt m :=
      match vt with 
      | (v,t) =>
      cost_nodup_Pln v t m +
      cost_map _ (fun _ => cons_ct+time_pair) 
        (PreTimed.nodup ec_inlist (filter_Pln v t m))
      end.


    Definition map_sub_Pln vt m :=
      match vt with 
      | (v,T) =>
        map (fun e => (Plnv e::v, T)) 
          (PreTimed.nodup ec_inlist (filter_Pln v T m))
      end.

    Program Definition map_sub_Pln' vt m 
    : {! y !:! _ !<! c !>! c = cost_map_sub_Pln vt m /\ 
      y = map_sub_Pln vt m !}
    :=
    match vt as vt' return (vt=vt') -> 
      {! y !:! _ !<! c !>! c = cost_map_sub_Pln vt m /\ 
      y = map_sub_Pln vt m !}
    with 
    | (v,t) => 
    fun hyp =>
      m <- nodup_Pln' v t m;
      out <- map' _ _ (fun e => (Plnv e::v, t))
        (fun _ => cons_ct+time_pair)
        (fun e => 
          ve <- cons' _ (Plnv e) v;
          out <- pair' _ _ ve t;
          <== out) m;
      <== out
    end (eq_refl vt).

    Next Obligation.
      getAnd; eauto. unfold cost_map_sub_Pln.
      simpl. eauto.
    Qed.

    Definition cost_map_v_Pln m V :=
      cost_map _ (fun vt => cost_map_sub_Pln vt m) V.


    Definition map_v_Pln m V := map (fun vt => map_sub_Pln vt m) V.
    Program Definition map_v_Pln' m V 
    : {! y !:! _ !<! c !>! c = cost_map_v_Pln m V /\ 
      y = map_v_Pln m V !}
    := 
      map' _ _ 
        (fun vt => map_sub_Pln vt m)
        (fun vt => cost_map_sub_Pln vt m)
        (fun vt => map_sub_Pln' vt m) V.

    Definition cost_elements_Pln := 1.
    Opaque cost_elements_Pln.

    Definition cost_inner_Pln m V := 
      cost_elements_Pln +
      cost_map_v_Pln ((vc_set.elements m)) V + 
      cost_concat _ (map_v_Pln (vc_set.elements m) V).

    Definition inner_Pln m V := concat (map_v_Pln (vc_set.elements m) V).

    Program Definition vc_elements (m:vc_set.t) 
    : {! res !:! list vc_set.elt !<! c !>! 
      c = cost_elements_Pln /\ res = vc_set.elements m !}
    := += cost_elements_Pln; <== vc_set.elements m.

    Program Definition inner_Pln' m V 
    : {! y !:! _ !<! c !>! c = cost_inner_Pln m V /\ 
      y = inner_Pln m V !}
    :=
      m' <- vc_elements m;
      m' <- map_v_Pln' m' V;
      out <- _concat _ m';
      <== out.

    Next Obligation.
      getAnd; eauto.
      unfold cost_inner_Pln; eauto.
      lia.
    Defined.

    Lemma L_fb_fb'_Pln: ∀ m V, f_b (PlnCME m) V = inner_Pln m V.
    Proof.
      easy.
      (* intros.
      unfold f_b; unfold inner_Pln.
      unfold map_v_Pln. unfold map_sub_Pln.
      unfold filter_Pln.
      unfold f_Pln.
      reflexivity. *)
    Qed.

  End timed_Pln.

  Section bound_Pln.

    Lemma bound_cost_f_Pln :
    ∃ k, 
    ∀ v t rr,
      cost_f_Pln v t rr <= k.
    Proof.
      destruct bound_cost_goEps as [k [b He]].
      destruct bound_cost_eqvv as [kv Hv].
      exists (
        (k * | P | + b + 3 * kv 
                + 5 * cost_andb
                + 2 * cost_eq_str + cost_f_pln_branch1) +
          (cost_endE + cost_beginE + 
              4 * kv + 2 * cost_eq_str
              + 5 * cost_andb + cost_f_pln_branch2) +
        cost_f_pln_branch3 +
        cost_f_pln_branch4 +
                (cost_endE + cost_beginE + kv + cost_f_pln_branch5) +
          cost_f_pln_branch6 +
                (cost_endE + cost_beginE + kv + cost_f_pln_branch7) +
          cost_f_pln_branch8 +
        cost_f_pln_branch9).

      intros.
      unfold cost_f_Pln.
      destruct rr.
      destruct o.
      destruct c.
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

    Lemma bound_cost_filter_Pln: ∃ k b, 
      ∀ v T m, cost_filter_Pln v T m <= k*|m|+b.
    Proof.
      destruct bound_cost_f_Pln as [k h1].
      exists (k + cost_if_stmt +
      cost_filter_Pln_branch2 + cost_g_Pln + cons_ct), cost_filter_Pln_branch1.
      intros.
      induction m. simpl. lia.
      simpl.
      pose (h1 v T a).
      destruct_with_eqn (f_Pln v T a);
      nia.
    Qed.


    Lemma bound_cost_nodup_Pln: 
      ∃ k k1 b,
      ∀ v t m,
      cost_nodup_Pln v t m <= k*|m|*|m|+k1*|m|+b.
    Proof.

      destruct (bound_cost_filter_Pln) as [k [b h1]].
      destruct bound_cost_ec_inlist as [k1 [b1 h2]].

      exists k1, (k+b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2), (b+b1+time_nodup_branch0).

      intros.
      unfold cost_nodup_Pln.
      specialize h1 with v t m.

      assert (| (filter_Pln v t m) | <= |m|).
      1:{
        unfold filter_Pln.
        apply (bound_filter_map).
      }

      Opaque time_nodup_branch1.
      Opaque time_nodup_branch2.

      match goal with
      | h: | ?x | <= |m| |- _ =>
      set (a:=x);
      fold a in h
      end.

      assert (cost_nodup PlnEdge ec_inlist cost_ec_inlist a
        <= (k1 * |a| + b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2) * |a| + 
          time_nodup_branch0).
      1:{
        induction a.
        simpl. lia.

        getH. tac_app. simpl in *; lia.
        simpl.

        pose (h2 a a0).

        destruct_with_eqn (ec_inlist a a0); nia. 
      }

      assert ((k1 * | a | + b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2) <=
      (k1 * | m | + b1 + cons_ct + time_nodup_branch1 + time_nodup_branch2)).
      nia. nia.
    Qed.

    Lemma bound_cost_map_sub_Pln: ∃ k k1 b, ∀ vt m, 
    cost_map_sub_Pln vt m <= k*|m|*|m|+k1*|m|+b.
    Proof.
      pose (bound_cost_nodup_Pln).
      pose (bound_cost_map (ec_as_OT.t) (fun _ => cons_ct+time_pair)).

      getH. tac_app. exists (cons_ct+time_pair). easy.
      clear e0.
      destruct H as [k2 [b2 h2]].
      destruct e as [k [k1 [b1 h1]]].
      exists k, (k1+k2), (b1+b2).
      
      intros.
      unfold cost_map_sub_Pln.
      destruct vt.

      specialize h1 with l l0 m.
      specialize h2 with (nodup ec_inlist (filter_Pln l l0 m)).

      assert (| (nodup ec_inlist (filter_Pln l l0 m)) | <= |m|).
      assert (| (nodup ec_inlist (filter_Pln l l0 m)) | <= |filter_Pln l l0 m|).
      apply (bound_nodup); eauto.
      assert (| (filter_Pln l l0 m) | <= |m|).
      unfold filter_Pln.

      apply bound_filter_map. lia.

      unfold ec_as_OT.t in h2.
      nia.
    Qed.

    Lemma bound_cost_map_v_Pln: 
    ∃ k k1 b b1,
    ∀ m V, 
    cost_map_v_Pln m V <= (k*|m|*|m|+k1*|m|+b) * |V| + b1.
    Proof.
      destruct (bound_cost_map_sub_Pln) as [k [k1 [b h]]].
      exists (k), k1, (b+cons_ct + time_map_branch2), time_map_branch1.
      intros.
      induction V. simpl. lia.
      simpl.
      specialize h with a m.
      lia.
    Qed.

    Lemma bound_cost_inner_Pln : ∃ k k1 b b1, ∀ m V,
      cost_inner_Pln m V <= (k * |(vc_set.elements m)| * |(vc_set.elements m)| +
      k1 * |(vc_set.elements m)| + b) * |V| + b1.
    Proof.
      destruct bound_cost_map_v_Pln as [k [k1 [b [b1 h1]]]].
      destruct (bound_cost_concat ((list VE * list RetEdge)))
        as [k1' [b1' [b2' h1']]].

      exists k, (k1+k1'), (b+b1'), (b2'+ b1+cost_elements_Pln).

      intros.
      specialize h1 with (vc_set.elements m) V.

      unfold cost_inner_Pln.
      specialize h1' with (map_v_Pln (vc_set.elements m) V) (| (vc_set.elements m) |).

      getH. tac_app. intros.
      unfold map_v_Pln in H.
      apply_in_map.
      unfold map_sub_Pln in H. destruct x.
      subst.
      rewrite map_length.
      rewrite (bound_nodup).
      unfold filter_Pln.
      rewrite (bound_filter_map). auto.

      clear h1'.

      unfold map_v_Pln at 2 in H.
      rewrite map_length in H.

      match goal with
      | h: ?x <= ?a, h1: ?y <= ?b |- ?z + ?x + ?y <= ?p =>
      assert (x + y <= a + b) by nia
      ; replace p with (z + a + b)
      ; try nia
      end.

      assert (cost_elements_Pln +
        ((k * | (vc_set.elements m) | * | (vc_set.elements m) | +
          k1 * | (vc_set.elements m) | + b) * | V | + b1) +
        ((k1' * | (vc_set.elements m) | + b1') * | V | + b2') =
        (k * | (vc_set.elements m) | * | (vc_set.elements m) | +
        (k1 + k1') * | (vc_set.elements m) | + (b + b1')) * 
        | V | + (b2' + b1) + cost_elements_Pln) as e by nia.
      
      match goal with
      | h: ?z = _ |- ?x = ?y =>
        replace x with z; try auto
      end.
      lia.
    Qed.
  End bound_Pln.

End TimedExtractionPln.

(* end hide *)
