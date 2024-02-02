(** This file provides the extraction functions and bridges the
    properties of the relation [Forest] and the extraction functions. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

Require Import Coq.Program.Equality.
Require Import Coq.Init.Wf.

Require Import Lia.

Require Import ForwardSmallStep.
Require Import BackwardSmallStep.

Require Import Coq.Unicode.Utf8_core.

Require Def.

Require Import Misc.
Import Misc.Basic.
Import Misc.vpg.

Require Import Lia.
Require Import Arith.PeanoNat.

Require Import Program.
Require Import Monad.
Require Import TimedSets.

Module Transducer(G:Def.VPG).

  Module TimedSets := TimedSets(G).

  Import TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Tacs.

  Import Def.DEF.
  Import TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Def.DB.
  Import TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Def.DF.
  Import TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.
  Import TimedSets.Parser.
  Import TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.DFX.
  Import TimedSets.Parser.PreTimed.Dbx.

  (* begin hide *)
  Ltac mergeBegin :=
    match goal with 
    | h: VBeginWith [?e] ?L
    |- _ =>
      inversion h; repeat breakEx; subst;
    simplList; subst
      ; clear h
    | h: VBeginWith ?v1 ?L,
      h2: VBeginWith ?v1 ?L1
    |- _
      =>
      destruct (VBeginSameEq _ _ _ h2 h)
      ; subst
    end.

  Ltac tac_invalid_db :=
    match goal with
    | h:Db [] _ _ |- _ =>
      exfalso; inversion h
    | h:Db _ _ [] |- _ =>
      exfalso; inversion h
    end.  
  (* end hide *)

  Module PreTransducer.

    (* begin hide *)

    Ltac eqstr_True :=
      match goal with 
      | h: eq_str ?v ?u = true |- _ =>
        rewrite L_eq_str in h
        ; destruct (String.eqb_eq v u) as [_H _]
        ; pose (_H h) as e
        ; rewrite e in *
        ; clear e
        ; clear h
        ; clear _H
      | h: String.eqb ?v ?u = true |- _ =>
        destruct (String.eqb_eq v u) as [_H _]
        ; pose (_H h) as e
        ; rewrite e in *
        ; clear e
        ; clear h
        ; clear _H
      end.

    Definition getSymVE e := 
      match e with 
      | Plnv (PlnE _ i _) => Plain i
      | Calv (PndCalE _ i _) => Call i
      | Calv (MatCalE _ i _ _ _) => Call i
      | Retv (PndRetE _ i _) => Ret i
      | Retv (MatRetE _ _ _ i _) => Ret i
      end.

    Lemma L_f_b_rules: ∀ m M T w, Forest (m::M) T w ->
      w!=[] ->
      ∀ r e, inRM (r, e) m ->
      match e with 
      | Plnv (PlnE L c L1) => 
        in_rules (L, Alt_Linear (Plain c) L1) P
      | Calv (PndCalE L a L1) => 
        in_rules (L, Alt_Linear (Call a) L1) P
      | Calv (MatCalE L a L1 b L2) =>
        in_rules (L, Alt_Match a b L1 L2) P
      | Retv (PndRetE L b L1) => 
        in_rules (L, Alt_Linear (Ret b) L1) P
      | Retv (MatRetE L a L1 b L2) => 
        in_rules (L, Alt_Match a b L1 L2) P
      end.
    Proof.
      intros.
      pose (PForest2) as d.
      specialize d with (1:=H) (3:=H1).
      rmDirect.
      breakAll.
      destruct r.
      1:{
        specialize H2 with (ea:=c).
        rmDirect.
        breakAll.
        destruct e as [[]|[]|[]];

        match goal with
        | h:Df _ _ _ |- _ =>
        inversion h; subst; tac_inj; subst 
        ;(match goal with
        | h: Calv _ = Calv _ |- _ =>
        inversion h; subst
        | h: Plnv _ = Plnv _ |- _ =>
        inversion h; subst
        | h: Retv _ = Retv _ |- _ =>
        inversion h; subst
        end; eauto)
        ;eauto
        end.
        pose (DF_dfx) as d.
        specialize d with (1:=H8); breakAll.


        resolveRule.
      }
      rmDirect; breakAll.
      destruct e as [[]|[]|[]];
      match goal with
      | h:Df _ _ _ |- _ =>
      inversion h; subst; tac_inj; subst; 
      (match goal with
      | h: Calv _ = Calv _ |- _ =>
      inversion h; subst
      | h: Plnv _ = Plnv _ |- _ =>
      inversion h; subst
      | h: Retv _ = Retv _ |- _ =>
      inversion h; subst
      end; eauto);
      eauto
      end.
      pose (DF_dfx) as d.
      specialize d with (1:=H8); breakAll.
      resolveRule.
    Qed.

    Lemma L_f_b_rules2: ∀ m M T w, Forest (m::M) T w ->
    w!=[] ->
      ∀ r e, inRM (r, e) m ->
      match r with 
      | Some (PndCalE L a L1) => in_rules (L, Alt_Linear (Call a) L1) P
      | Some (MatCalE L a L1 b L2) =>in_rules (L, Alt_Match a b L1 L2) P
      | None => True
      end.
    Proof.
      intros.
      pose (PForest2) as d.
      specialize d with (1:=H) (3:=H1).
      rmDirect.
      breakAll.
      destruct r; eauto.
      specialize H2 with (ea:=c).
      rmDirect. breakAll.

      match goal with
      | h:Df ?v ?T ?w |- _ =>
        pose (ForwardSmallStep.DFX.DF_dfx _ _ _ h)
      ; do 4 breakEx
      end.

      destruct c.
      pose DFX_df_rule1 as h1.
      specialize h1 with (1:=e0). eauto.
      
      pose DFX_df_rule2 as h1.
      specialize h1 with (1:=e0). eauto.
    Qed.

    Lemma L_f_b_synCall: ∀ m M T w, Forest (CalCME m::M) T w ->
      w!=[]->
      ∀ r e, va_set.In (r, e) m -> r=Some e.
    Proof.
      intros.
      pose (PForest2) as d.
      specialize d with (1:=H) (r:=r) (e:=Calv e).
      rmDirect.
      getH. tac_app. simpl. eauto.
      breakAll.
      destruct r.
      specialize H3 with (ea := c).
      rmDirect.
      rmDirect.
      breakAll.
      inversion H6; subst; tac_inj; subst; inversion a0; subst; eauto.
      rmDirect.
      rmDirect.
      breakAll.
      inversion H6; subst; tac_inj; subst; inversion a0; subst; eauto.
    Qed.

    (* end hide *)

    (** [L_invalid_df_T]: if the top of the forest stack is a pending
      rule, then all rules on the stack are pending. *)
    Lemma L_invalid_df_T: ∀ v L a L1 L' a' L1' b' L2' T w, 
      Df v (PndCalE L a L1::MatCalE L' a' L1' b' L2'::T) w -> False.
    (* begin hide *)
    Proof.
      Import ForwardSmallStep.Core.

      intros.
      pose DF_dfx as f.
      specialize f with (1:=H).
      breakAll. 
      pose DFX_df_sub as g.
      specialize g with (1:=f).
      breakAll; try discriminate; tac_inj; subst.
      simplList; subst.
      destruct x0.
      1:{
        pose (DFX_v) as o.
        specialize o with (1:=f).
        breakAll; try discriminate; tac_inj; subst.
        simplList; subst.
        simpl in *.

        inversion f; subst; tac_inj; subst.

        pose DFX_df_sub as g2.
        specialize g2 with (1:=H14).
        breakAll; try discriminate; tac_inj; subst.
        simplList; subst.

        assert (Df [Calv (MatCalE L' a' L1' b' L2')] 
          [MatCalE L' a' L1' b' L2'] [Call a']) as hcal.
        1:{
          constructor.
          resolveRule.
        }

        pose (DFX_v) as o.
        specialize o with (1:=H14).
        breakAll; try discriminate; tac_inj; subst.
        simplList; subst.

        destruct v2.
        1:{
          simpl in *.
          rewrite <- app_assoc in H.
          inversion H; subst; tac_inj;
          repeat match goal with
          | h:_ = ?x ++ [?y;?z] |- _ =>
            assert (x++[y;z]=(x++[y])++[z]) as rw
            by (repeat rewrite <- app_assoc; eauto)
            ; rewrite rw in h
            ; clear rw
            ; tac_inj
          end.
          subst.
          assert (L1'=L).
          inversion H17; breakAll; tac_inj; subst; eauto.
          inversion a4; subst; eauto.
          subst.

          pose A_VPG_Match as ax1.
          inversion hcal; tac_inj; subst; try tac_invalid_df.
          specialize ax1 with (1:=H5); breakAll; subst.
          pose A_VPG_Linear as ax2.
          specialize ax2 with (1:=H10); breakAll; subst.
          getH. apply ax2; eauto. breakAll; discriminate.
        }

        pose VConnect as e.
        rmDirect.
        pose (VHasHead _ _ _ H5).
        breakAll.
        specialize e with (1:=H) 
          (v1:=v1 ++ [Calv (MatCalE L' a' L1' b' L2')])
          (v2:=v :: v2 ++ [Calv (PndCalE L a L1)])
          (Lv1:=L1')
          (Lv2:=x).
        getH. apply e; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc;
        repeat rewrite -> app_comm_cons; eauto.
        repeat rewrite app_comm_cons; 
        eauto using app_cons_not_nil.
        BackwardSmallStep.Core.tryResolveEnd.
        repeat rewrite app_comm_cons.
        apply VListBeginSame2; eauto.
        subst. 

        repeat rewrite <- app_assoc in H.

        pose (VHasEnd _ _ _ H5). breakAll.
        pose VConnect as e2.
        rmDirect.
        specialize e2 with (1:=H) 
          (v1:=v1 ++ [Calv (MatCalE L' a' x b' L2')] ++ v :: v2)
          (v2:=[Calv (PndCalE L a L1)])
          (Lv1:=x0)
          (Lv2:=L).
        getH. apply e2; eauto using app_cons_not_nil, nil_cons.
        repeat rewrite <- app_assoc;
        repeat rewrite -> app_comm_cons; eauto.
        repeat rewrite app_comm_cons; 
        eauto using app_cons_not_nil.
        repeat rewrite app_assoc.
        apply VListEndSame2; eauto.
        tryResolveBegin.
        subst.


        pose A_VPG_Match as ax1.
        inversion hcal; tac_inj; subst; try tac_invalid_df.
        specialize ax1 with (1:=H7); breakAll; subst.

        pose VConnectTrue as ht.
        specialize ht with (1:=H5) (L:=x0).
        getH. apply ht; eauto.
        specialize H3 with (v1:=v::v2) (v2:=[]).
        getH. apply H3; simpl; eauto using nil_cons. rewrite app_nil_r; eauto.
        breakAll.
        mergeEnds.

        pose A_VPG_Linear as ax2.
        specialize ax2 with (1:=H10); breakAll; subst.
        getH. apply ax2; eauto. breakAll; discriminate.
      }

      1:{
        rmDirect.
        pose (DFX_v) as o;
        specialize o with (1:=f);
        breakAll; try discriminate; tac_inj; subst;
        simplList; subst;
        simpl in *.

        match goal with
        | h:Df ?v ?T w |- _ =>
        pose (ForwardSmallStep.Core.L4_2 v T w) as bk;
        inversion bk
        ; rmDirect
        end.
        breakAll; try discriminate; tac_inj; subst.
        rmDirect.
        breakAll; try discriminate; tac_inj; subst.
        simplList; eauto; subst.

        destruct x6; repeat rmDirect; try discriminate.
        rewrite H6 in *.

        pose DF_dfx as f2.
        specialize f2 with (1:=H5).
        breakAll.       
        pose DFX_df_sub as g2.
        specialize g2 with (1:=f2).
        breakAll; try discriminate; tac_inj; subst;
        simplList; subst.

        pose (DFX_v) as o.
        specialize o with (1:=f2).
        breakAll; try discriminate; tac_inj; subst.
        simplList; subst.

        destruct x11.
        1:{
          simpl in *.
          rewrite <- app_assoc in H.

          pose VConnect as e.
          specialize e with (1:=H) 
            (v1:=x3 ++ [Calv (MatCalE L' a' L1' b' L2')])
            (v2:=Calv (PndCalE x9 x8 x10) :: x5)
            (Lv1:=L1')
            (Lv2:=x9).
          getH. apply e; eauto using app_cons_not_nil, nil_cons.
          repeat rewrite <- app_assoc;
          repeat rewrite -> app_comm_cons; eauto.
          repeat rewrite app_comm_cons; 
          eauto using app_cons_not_nil.
          BackwardSmallStep.Core.tryResolveEnd.
          tryResolveBegin.
          subst. 

          assert (in_rules (L', Alt_Match a' b' x9 L2') P).
          1:{
            inversion H5; tac_inj; subst; eauto.
          }

          pose A_VPG_Match as ax1.
          specialize ax1 with (1:=H9); breakAll; subst.
          pose A_VPG_Linear as ax2.
          specialize ax2 with (1:=H12); breakAll; subst.
          getH. apply ax2; eauto. breakAll; discriminate.
        }

        simpl in *.
        rewrite <- app_assoc in H.
        rmDirect.

        pose (VHasHead _ _ _ H9).
        breakAll.

        pose VConnect as e2.
        specialize e2 with (1:=H) 
          (v1:=x3 ++ [Calv (MatCalE L' a' L1' b' L2')])
          (v2:=v :: x11 ++ Calv (PndCalE x9 x8 x10) :: x5)
          (Lv1:=L1')
          (Lv2:=x4).
        getH. apply e2; eauto using app_cons_not_nil, nil_cons.
        repeat rewrite <- app_assoc;
        repeat rewrite -> app_comm_cons; eauto.
        repeat rewrite app_comm_cons; 
        eauto using app_cons_not_nil.
        BackwardSmallStep.Core.tryResolveEnd.
        repeat rewrite app_comm_cons.
        apply VListBeginSame2; eauto.
        subst. 

        pose (VHasEnd _ _ _ H9). breakAll.
        pose VConnect as e3.
        specialize e3 with (1:=H) 
          (v1:=x3 ++ [Calv (MatCalE L' a' x4 b' L2')] ++ v :: x11)
          (v2:=Calv (PndCalE x9 x8 x10) :: x5)
          (Lv1:=x14)
          (Lv2:=x9).
        getH. apply e3; eauto using app_cons_not_nil, nil_cons.
        repeat rewrite <- app_assoc;
        repeat rewrite -> app_comm_cons; eauto.
        repeat rewrite app_comm_cons; 
        eauto using app_cons_not_nil.
        repeat rewrite app_assoc.
        apply VListEndSame2; eauto.
        tryResolveBegin.
        subst. 


        pose A_VPG_Match as ax1.
        assert (in_rules (L', Alt_Match a' b' x4 L2') P).
        1:{
          resolveRule.
        }
        specialize ax1 with (1:=H14); breakAll; subst.

        pose VConnectTrue as ht.
        specialize ht with (1:=H9) (L:=x14).
        getH. apply ht; eauto.
        specialize H15 with (v1:=v::x11) (v2:=[]).
        getH. apply H15; simpl; eauto using nil_cons. rewrite app_nil_r; eauto.
        breakAll.
        mergeEnds.

        pose A_VPG_Linear as ax2.
        specialize ax2 with (1:=H12); breakAll; subst.
        getH. apply ax2; eauto. breakAll; discriminate.
      }
    Qed.
    (* end hide *)

    (** [L_invalid_mb]: if a parse tree in the forward small-step
        derivation ends with a pending rule, then all rules on the stack
        are pending. *)
    Lemma L_invalid_mb:
      ∀ x L a L1 b L2 L1' b' L2' _T _w,
      Df (x ++ [Retv (PndRetE L1' b' L2')]) 
        (MatCalE L a L1 b L2 :: _T) 
        _w
      -> False.
    (* begin hide *)
    Proof.

      intros.

      inversion H; subst; tac_inj; subst.

      destruct t.

      pose L_invalid_df_T as f2.
      specialize f2 with (1:=H3). easy.

      pose DF_dfx as e.
      specialize e with (1:=H3).

      breakAll.

      pose ForwardSmallStep.DFX.DFX_v as g.
      specialize g with (1:=e).
      breakAll; try discriminate; simplList; subst; eauto.


      match goal with
      | h:Dfx _ (MatCalE ?L ?a ?L1 ?b ?L2::_) _ _ _ _ _ |- _ =>
       assert (in_rules (L, Alt_Match a b L1 L2) P) by
         resolveRule
      end.

      destruct x1.
      1:{
        simpl in *.
        rewrite <- app_assoc in H.
        inversion H; subst; tac_inj;
        repeat match goal with
        | h:_ = ?x ++ [?y;?z] |- _ =>
          assert (x++[y;z]=(x++[y])++[z]) as rw
          by (repeat rewrite <- app_assoc; eauto)
          ; rewrite rw in h
          ; clear rw
          ; tac_inj
        end.
        subst.
        assert (L5=L7).
        inversion H7; breakAll; tac_inj; subst; eauto.
        inversion a4; subst; eauto.
        subst.

        inversion a0; inversion a3; subst.

        pose A_VPG_Match as ax1.
        specialize ax1 with (1:=H0); breakAll; subst.
        pose A_VPG_Linear as ax2.
        specialize ax2 with (1:=H6); breakAll; subst.
        getH. apply ax2; eauto. breakAll; discriminate.
      }

      pose ForwardSmallStep.DFX.DFX_df_sub as g.
      specialize g with (1:=e).
      breakAll; try discriminate; simplList; subst; eauto.

      pose VConnect as e2.
      rmDirect.
      pose (VHasHead _ _ _ H5).
      breakAll.
      match goal with
      | h:in_rules (?L, Alt_Match ?a ?b ?L1 ?L2) _ |- _ =>
       specialize e2 with (1:=H) 
         (v1:=x0 ++ [Calv (MatCalE L a L1 b L2)])
         (v2:=v :: x1 ++ [Retv (PndRetE L1' b' L2')])
         (Lv1:=L1)
         (Lv2:=x)
      end.
      getH. apply e2; eauto using app_cons_not_nil.
      repeat rewrite <- app_assoc;
      repeat rewrite -> app_comm_cons; eauto.
      repeat rewrite app_comm_cons; 
      eauto using app_cons_not_nil.
      BackwardSmallStep.Core.tryResolveEnd.
      repeat rewrite app_comm_cons.
      apply VListBeginSame2; eauto.
      subst. 

      repeat rewrite <- app_assoc in H.

      pose (VHasEnd _ _ _ H5). breakAll.
      pose VConnect as e3.
      match goal with
      | h:in_rules (?L, Alt_Match ?a ?b ?L1 ?L2) _ |- _ =>
      specialize e3 with (1:=H) 
        (v1:=x0 ++ [Calv (MatCalE L a L1 b L2)] ++ v :: x1)
        (v2:=[Retv (PndRetE L1' b' L2')])
        (Lv1:=x4)
        (Lv2:=L1')
      end.

      getH. apply e3; eauto using app_cons_not_nil, nil_cons.
      repeat rewrite <- app_assoc;
      repeat rewrite -> app_comm_cons; eauto.
      repeat rewrite app_comm_cons; 
      eauto using app_cons_not_nil.
      repeat rewrite app_assoc.
      apply VListEndSame2; eauto.
      tryResolveBegin.
      subst.


      pose A_VPG_Match as ax1.
      specialize ax1 with (1:=H0); breakAll; subst.

      pose VConnectTrue as ht.
      specialize ht with (1:=H5) (L:=x4).
      getH. apply ht; eauto.
      specialize H7 with (v1:=v::x1) (v2:=[]).
      getH. apply H7; simpl; eauto using nil_cons. rewrite app_nil_r; eauto.
      breakAll.
      mergeEnds.
      
      assert (∃ L2, in_rules ((V0 x), Alt_Linear (Ret b') L2) P).
      1:{
        inversion H; subst; tac_inj; subst;
        repeat rewrite app_comm_cons in *;
        repeat rewrite app_assoc in *;
        tac_inj; subst.
        inversion a2; subst; eauto.
        inversion a3; subst; eauto.
      }
      breakAll.
      
      pose A_VPG_Linear as ax2.
      specialize ax2 with (1:=H9); breakAll; subst.
      getH. apply ax2; eauto. breakAll; discriminate.
    Qed.
    (* end hide *)

  End PreTransducer.


  Module Transducer2.
    Import PreTransducer.

    (* begin hide *)

    Global Hint Resolve eq_nat_dec: misc.

    Lemma rci_eq_dec: ∀ x y : PlnEdge * nat, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma rai_eq_dec: ∀ x y : CalEdge * nat, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma rbi_eq_dec: ∀ x y : RetEdge * nat, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Ltac down_in :=
      match goal with
      | h: In ?x (va_set.elements ?s) |- _ =>
        destruct (va_set.elements_spec1 s x) as [_hs _]
        ; getH; [tac_app; eauto |]
        ; clear _hs
      | h: In ?x (vc_set.elements ?s) |- _ =>
        destruct (vc_set.elements_spec1 s x) as [_hs _]
        ; getH; [tac_app; eauto |]
        ; clear _hs
      | h: In ?x (vb_set.elements ?s) |- _ =>
        destruct (vb_set.elements_spec1 s x) as [_hs _]
        ; getH; [tac_app; eauto |]
        ; clear _hs
      end.
    
      Ltac synci :=
        match goal with
        | h:In (?r', ?e') _,
          Hrm: ∀ _ _, inRM _ _ -> _ = _ |- _ =>
          specialize Hrm with (r:=r') (e:=Calv e')
          ; match type of Hrm with
          | _ -> ?g =>
          assert g
          end; [apply Hrm; simpl; eauto |]
          ; eauto
        | h:In (?r', ?e') _,
          Hrm: ∀ _ _, inRM _ _ -> _ = _ |- _ =>
          specialize Hrm with (r:=r') (e:=Plnv e')
          ; match type of Hrm with
          | _ -> ?g =>
          assert g
          end; [apply Hrm; simpl; eauto |]
          ; eauto
        | h:In (?r', ?e') _,
          Hrm: ∀ _ _, inRM _ _ -> _ = _ |- _ =>
          specialize Hrm with (r:=r') (e:=Retv e')
          ; match type of Hrm with
          | _ -> ?g =>
          assert g
          end; [apply Hrm; simpl; eauto |]
          ; eauto
        end.

    Lemma rc_eq_dec: ∀ x y : 
      option CalEdge * PlnEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma ra_eq_dec: ∀ x y : 
      option CalEdge * CalEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma la_eq_dec: ∀ x y : list CalEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma lb_eq_dec: ∀ x y : list RetEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma lc_eq_dec: ∀ x y : list PlnEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma ve_eq_dec: ∀ x y : VE, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma lve_eq_dec: ∀ x y : list VE, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Fixpoint inlist {A} (compareA:A->A->comparison) (x:A) l := 
      match l with
      | [] => false
      | y::l' =>
        match compareA x y with
        | Eq => true
        | _ => inlist compareA x l'
        end
      end.

    Definition ec_inlist := inlist ec_as_OT.compare.
    Definition ea_inlist := inlist ea_as_OT.compare.
    Definition eb_inlist := inlist eb_as_OT.compare.

    Lemma L_ec_inlist: ∀ x l, ec_inlist x l = true <-> In x l.
    Proof.
      intros.
      generalize dependent x.
      induction l.
      easy.

      split; intros;
      simpl in H.

      destruct_with_eqn (ec_as_OT.compare x a).

      rewrite TimedSets.timed_ec.L_compare_eq in Heqc; subst.
      constructor 1; auto.
      constructor 2; auto.
      apply IHl; auto.
      unfold ec_inlist in H. simpl in H. rewrite Heqc in H. auto.
      constructor 2; auto.
      apply IHl; auto.
      unfold ec_inlist in H. simpl in H. rewrite Heqc in H. auto.

      breakOr. subst.
      unfold ec_inlist; simpl.
      destruct (ec_as_OT.compare_spec x x); try easy.
      1,2: destruct (ec_as_OT.lt_strorder) as [h _];
        pose (h x); easy.

      unfold ec_inlist; simpl.
      destruct_with_eqn (ec_as_OT.compare x a); try easy.
      all: apply IHl; eauto.
    Qed.

    Lemma L_ea_inlist: ∀ x l, ea_inlist x l = true <-> In x l.
    Proof.
      intros.
      generalize dependent x.
      induction l.
      easy.

      split; intros;
      simpl in H.

      destruct_with_eqn (ea_as_OT.compare x a).

      rewrite TimedSets.timed_ea.L_compare_eq in Heqc; subst.
      constructor 1; auto.
      constructor 2; auto.
      apply IHl; auto.
      unfold ea_inlist in H. simpl in H. rewrite Heqc in H. auto.
      constructor 2; auto.
      apply IHl; auto.
      unfold ea_inlist in H. simpl in H. rewrite Heqc in H. auto.

      breakOr. subst.
      unfold ea_inlist; simpl.
      destruct (ea_as_OT.compare_spec x x); try easy.
      1,2: destruct (ea_as_OT.lt_strorder) as [h _];
        pose (h x); easy.

      unfold ea_inlist; simpl.
      destruct_with_eqn (ea_as_OT.compare x a); try easy.
      all: apply IHl; eauto.
    Qed.

    Lemma L_eb_inlist: ∀ x l, eb_inlist x l = true <-> In x l.
    Proof.
      intros.
      generalize dependent x.
      induction l.
      easy.

      split; intros;
      simpl in H.

      destruct_with_eqn (eb_as_OT.compare x a).

      rewrite TimedSets.timed_eb.L_compare_eq in Heqc; subst.
      constructor 1; auto.
      constructor 2; auto.
      apply IHl; auto.
      unfold eb_inlist in H. simpl in H. rewrite Heqc in H. auto.
      constructor 2; auto.
      apply IHl; auto.
      unfold eb_inlist in H. simpl in H. rewrite Heqc in H. auto.

      breakOr. subst.
      unfold eb_inlist; simpl.
      destruct (eb_as_OT.compare_spec x x); try easy.
      1,2: destruct (eb_as_OT.lt_strorder) as [h _];
        pose (h x); easy.

      unfold eb_inlist; simpl.
      destruct_with_eqn (eb_as_OT.compare x a); try easy.
      all: apply IHl; eauto.
    Qed.

    (* end hide *)

    (** [f_b]: the one-step extraction function [f_b:(m,V) ↦ V'] uses
      rules in [m] to extend partial parse trees in [V], resulting in a
      new set [V'] of partial pares trees. *)

    Load "f_b.v".

    (* begin hide *)
    
    Ltac invalid_ma :=
      match goal with
      | h0:Forest _ _ _,
        hw:?w!=[],
        h:_ (Some (PndCalE _ _ _), MatCalE _ _ _ _ _) _ |- _ =>
        pose L_f_b_synCall as f
        ; specialize f with (1:=h0) (2:=hw) (3:=h)
        ; discriminate
      | h0:Forest _ _ _,
        hw:?w!=[],
        h:_ (Some (MatCalE _ _ _ _ _), PndCalE _ _ _) _ |- _ =>
          pose L_f_b_synCall as f
          ; specialize f with (1:=h0) (2:=hw) (3:=h)
          ; discriminate
      | h0:Forest _ _ _,
        hw:?w!=[],
        h:_ (None, PndCalE _ _ _) _ |- _ =>
        pose L_f_b_synCall as f
        ; specialize f with (1:=h0) (2:=hw) (3:=h)
        ; discriminate
      | h0:Forest _ _ _,
        hw:?w!=[],
        h:_ (None, MatCalE _ _ _ _ _) _ |- _ =>
          pose L_f_b_synCall as f
          ; specialize f with (1:=h0) (2:=hw) (3:=h)
          ; discriminate
      end.

    Ltac resolveRule_fb:=
      match goal with
      | h:Forest _ _ _, h2: In (?r', ?e') ?m,
        h3: ?w != [] |- _ =>
          pose L_f_b_rules as fbf
          ; specialize fbf with (1:=h) (2:=h3) (r:=r') (e:=Calv e')
          ; getH; [apply fbf; eauto; clear fbf|]; simpl in *
          ; eauto
      | h:Forest _ _ _, h2: In (?r', ?e') ?m,
        h3: ?w != [] |- _ =>
          pose L_f_b_rules as fbf
          ; specialize fbf with (1:=h) (2:=h3) (r:=r') (e:=Plnv e')
          ; getH; [apply fbf; eauto; clear fbf|]; simpl in *
          ; eauto
      | h:Forest _ _ _, h2: In (?r', ?e') ?m,
        h3: ?w != [] |- _ =>
          pose L_f_b_rules as fbf
          ; specialize fbf with (1:=h) (2:=h3) (r:=r') (e:=Retv e')
          ; getH; [apply fbf; eauto; clear fbf|]; simpl in *
          ; eauto
      end.

    Ltac apply_nodup_in :=
      match goal with
      | h:In ?x (PreTimed.nodup ec_inlist ?l) |- _ =>
        destruct (PreTimed.nodup_In _ x l ec_inlist L_ec_inlist) as [_H _]
        ; specialize _H with (1:=h)
        ; clear h
        ; rename _H into h
      | h:In ?x (PreTimed.nodup ea_inlist ?l) |- _ =>
        destruct (PreTimed.nodup_In _ x l ea_inlist L_ea_inlist) as [_H _]
        ; specialize _H with (1:=h)
        ; clear h
        ; rename _H into h
      | h:In ?x (PreTimed.nodup eb_inlist ?l) |- _ =>
        destruct (PreTimed.nodup_In _ x l eb_inlist L_eb_inlist) as [_H _]
        ; specialize _H with (1:=h)
        ; clear h
        ; rename _H into h
      | |- In ?x (PreTimed.nodup ?inlist ?l) =>
        try apply (PreTimed.nodup_In _ x l ea_inlist L_ea_inlist)
        ; try apply (PreTimed.nodup_In _ x l ec_inlist L_ec_inlist)
        ; try apply (PreTimed.nodup_In _ x l eb_inlist L_eb_inlist)
      end.

    Ltac apply_filter_map :=
      match goal with 
      | h: In ?x (filter_map ?l ?f ?g) |- _ =>
        let _h := fresh "_h" in
        destruct (L_filter_map l f g x) as [_h _]
        ; specialize _h with (1:=h)
        ; clear h
        ; repeat (breakAnd+breakEx)
        | |- In ?x (filter_map ?l ?f ?g) => 
        apply (L_filter_map l f g x)
      end.

    Ltac apply_concat :=
      match goal with 
      | h: In ?x (concat ?l) |- _ =>
        let _h := fresh "_h" in
        destruct (in_concat l x) as [_h _]
        ; specialize _h with (1:=h)
        ; clear h
        ; repeat (breakAnd+breakEx)
        | |- In ?x (concat ?l) =>
        let _h := fresh "_h" in
        pose (in_concat l x) as h
      end.

    Ltac apply_in_map :=
      match goal with 
      | h: In ?x (map ?f ?l) |- _ =>
        let _h := fresh "_h" in
        destruct (in_map_iff f l x) as [_h _]
        ; specialize _h with (1:=h)
        ; clear h
        ; repeat (breakAnd+breakEx)
      | |- In ?x (map ?f ?l) => 
        apply (in_map_iff f l x)
      end.

    (* end hide *)

    (** [L_f_b]: given [V'=f_b m V], this lemma shows that if parse
        trees in [V] satisfies the backward small-step relation [Db],
        then parse trees in [V'] also satisfies [Db]. *)
    Lemma L_f_b: ∀ m V i w,
      (∀ v T, In (v,T) V -> Db v T w) ->
      (∃ _M _T _w, _w != [] /\ Forest (m::_M) _T _w) ->
      (∀ r e, inRM (r,e) m -> getSymVE e = i) ->
        ∀ v' T',
        In (v',T') (f_b m V)
          -> Db v' T' (i::w).
    (* begin hide *)
    Proof.

      Import TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.Core.

      intros.
      rename H0 into Him.
      destruct Him as [_M [_T [_w [Hw Him]]]].
      rename H1 into Hrm.
      rename H2 into H0.
      destruct m; simpl in H0.

      2:{

        apply_concat.
        breakAll. 
        apply_in_map. 
        destruct x0.
        subst.

        apply_in_map.

        apply_nodup_in.

        apply_filter_map.
        destruct x0;
        destruct o.

        1:{
          destruct c;
          destruct l0;
          breakTuple; rmDirect;
          match goal with
          | h:In (?v, ?I) V |- _ =>
            specialize H with (1:=h)
          end.
          1:{
    
            simpl.
            destruct l; try discriminate.
    
            destruct p0.
    
            assert (i=Plain c) by (down_in;synci); subst.
            destruct v.
            1:{
              pose V_Pln_a as ap.
              destruct va;
              assert (∃ a w', w=Call a::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
    
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
              resolveRule_fb.
              up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_c as ap.
              destruct vc;
              assert (∃ w', w=Plain c0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
    
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v
              ; tryResolveBegin
              end.
            }
    
            1:{
              inversion H.
            }
          }
          1:{
    
            simpl.
            destruct l; try discriminate.
            tac_invalid_db.
            destruct r; try discriminate.
    
            destruct p0.
            assert (i=Plain c) by (down_in;synci); subst.
            destruct v.
            1:{
              pose V_Pln_a as ap;
              destruct va;
              assert (∃ w', w=Call a0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_c as ap.
              destruct vc;
              assert (∃ w', w=Plain c0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
    
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_b1 as ap.
              destruct vb.
              assert (∃ w', w=Ret b0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto; subst; simpl; eauto
                end.
              assert (b0=b) by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto; subst; simpl; eauto
                end.
              
              breakAll; subst.
              resolve_eqvv.
              specialize ap with (2:=H).
              simpl in ap. simpl.
    
              inversion H; subst;
              apply ap; eauto;
              resolveRule_fb; up_in.
    
              inversion H.
            }
          }
          match goal with
          | h:false = true |- _ =>
            inversion h 
          end.
          1:{
    
            simpl.
            destruct l; try discriminate.
            tac_invalid_db.
            destruct r; try discriminate.
    
            destruct p0.
            assert (i=Plain c) by (down_in;synci); subst.
            destruct v.
            1:{
              pose V_Pln_a as ap;
              destruct va;
              assert (∃ w', w=Call a1::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              all: repeat (match goal with 
              | Heq: ?s1 && ?s2 = true |- _ =>
                  destruct (andb_true_iff s1 s2) as [_h1 _];
                  destruct (_h1 Heq) as [_hsep1 _hsep2]
              end; resolve_eqvv).
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
              resolveRule_fb. up_in.
              
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_c as ap.
              destruct vc;
              assert (∃ w', w=Plain c0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
    
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              repeat (match goal with 
              | Heq: ?s1 && ?s2 = true |- _ =>
                  destruct (andb_true_iff s1 s2) as [_h1 _];
                  destruct (_h1 Heq) as [_hsep1 _hsep2]
              end; resolve_eqvv).
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_b2 as ap.
              destruct vb.
              1:{
                inversion H.
              }
              assert (∃ w', w=Ret b0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto; subst; simpl; eauto
                end.
    
              match goal with
              |  |- Db (_ :: Retv (MatRetE ?L8 ?a1 ?L9 ?b1 ?L10) :: l)
              (MatRetE ?L3 ?a0 ?L4 ?b0 ?L5 :: _) (Plain c :: w) =>
               assert (MatRetE L8 a1 L9 b1 L10=MatRetE L3 a0 L4 b0 L5) as H3 by
                 match goal with
                 | h:Db _ _ w |- _ =>
                   inversion h; eauto; subst; simpl; eauto
                 end
              ; inversion H3
              end.
              
              breakAll; subst.
              simpl in ap.
              specialize ap with (3:=H).
              repeat match goal with 
              | Heq: ?s1 && ?s2 = true |- _ =>
                destruct (andb_true_iff s1 s2) as [_h1 _];
                destruct (_h1 Heq) as [? ?]
                ; clear Heq _h1
              end;
              
              repeat resolve_eqvv;
              repeat eqstr_True.
              resolve_goEps.
              simpl in i; eauto.
              apply ap; eauto.
    
              resolveRule_fb; up_in.
            }
          }
        }

        1:{
          destruct l0;
          breakTuple; rmDirect;
          match goal with
          | h:In (?v, ?I) V |- _ =>
            specialize H with (1:=h)
          end.
          1:{
    
            simpl.
            destruct l; try discriminate.
    
            destruct p0.
    
            assert (i=Plain c) by (down_in;synci); subst.
            destruct v.
            1:{
              pose V_Pln_a as ap.
              destruct va;
              assert (∃ a w', w=Call a::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
    
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
              resolveRule_fb.
              up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_c as ap.
              destruct vc;
              assert (∃ w', w=Plain c0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
    
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v
              ; tryResolveBegin
              end.
            }
    
            1:{
              inversion H.
            }
          }
          1:{
    
            simpl.
            destruct l; try discriminate.
            tac_invalid_db.
            destruct r; try discriminate.
    
            destruct p0.
            assert (i=Plain c) by (down_in;synci); subst.
            destruct v.
            1:{
              pose V_Pln_a as ap;
              destruct va;
              assert (∃ w', w=Call a::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_c as ap.
              destruct vc;
              assert (∃ w', w=Plain c0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H);
    
              apply ap; eauto.
              resolveRule_fb. up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v
              ; tryResolveBegin
              end.
            }
    
            1:{
              pose V_Pln_b1 as ap.
              destruct vb.
              assert (∃ w', w=Ret b0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto; subst; simpl; eauto
                end.
              assert (b0=b) by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto; subst; simpl; eauto
                end.
              
              breakAll; subst.
              resolve_eqvv.
              specialize ap with (2:=H).
              simpl in ap. simpl.
    
              inversion H; subst;
              apply ap; eauto;
              resolveRule_fb; up_in.
    
              inversion H.
            }
          }
        }
      }

      1:{
        apply_concat. 
        apply_in_map. 
        destruct x0.

        subst.
        apply_in_map.
        apply_nodup_in.
        apply_filter_map.
        destruct x0;
        destruct o;
        destruct c;
        try (destruct c0);
        destruct l0;
        breakTuple; rmDirect;
        match goal with
        | h:In (?v, ?I) V |- _ =>
          specialize H with (1:=h)
        end.

        all: try discriminate.
        all: try (down_in; invalid_ma).
        1:{

          simpl.
          destruct l; try discriminate.


          assert (i=Call a).
          1:{
            match goal with
            | h:In (?r', ?e') _ |- _ =>
              specialize Hrm with (r:=r') (e:=Calv e')
              ; match type of Hrm with
              | _ -> ?g =>
                assert g
              end; [apply Hrm; simpl; eauto |]
              ; eauto
            end.

            up_in.
          }
          
          subst.
          constructor; eauto.
          resolveRule_fb; up_in.
          resolve_eqvv.
          match goal with
          | |- VBeginWith (?v::_) (beginE ?v) =>
            destruct v as [[? | ?] | [?] | [? | ?]]
            ; tryResolveBegin
          end.
          match goal with
          | h:Db (Retv (MatRetE _ _ _ _ _)::_) _ _ |- _ =>
            inversion h
          end.
        }

        1:{

          simpl.
          destruct r; try discriminate.
          destruct l; try discriminate.
          resolve_eqvv.


          assert (i=Call a).
          synci.
          up_in.

          subst.
          apply V_Cal_b1 with (3:=H); eauto.
          resolveRule_fb; up_in.
          
          match goal with
          | |- VBeginWith (?v::_) (beginE ?v) =>
            destruct v as [[? | ?] | [?] | [? | ?]]
            ; tryResolveBegin
          end.
          match goal with
          | h:Db (Retv (MatRetE _ _ _ _ _)::_) _ _ |- _ =>
            inversion h
          end.


        }

        1:{

          simpl.
          destruct r; try discriminate.
          destruct l; try discriminate.

          inversion H.

          assert (i=Call a).
          synci.
          up_in.

          subst.

          repeat match goal with 
          | Heq: ?s1 && ?s2 = true |- _ =>
            destruct (andb_true_iff s1 s2) as [_h1 _];
            destruct (_h1 Heq) as [? ?]
            ; clear Heq _h1
          end;
          
          repeat resolve_eqvv;
          repeat eqstr_True.

          destruct v.

          1:{
            pose V_Cal_a as ap.
            assert (∃ a w', w=Call a::w') by
              match goal with
              | h:Db _ _ w |- _ =>
                inversion h; eauto 
              end.
            breakAll; subst.
            specialize ap with (2:=H).
            
            Ltac syncMMa :=
            match goal with
            | h0:Forest _ _ _,
              hw:?w!=[],
              h:va_set.In (Some (MatCalE _ _ _ _ _), MatCalE _ _ _ _ _) _ |- _ =>
              pose L_f_b_synCall as f
              ; specialize f with (1:=h0) (2:=hw) (3:=h)
              ; inversion f; subst
            | h0:Forest _ _ _,
              hw:?w!=[],
              h:va_set.In (Some (PndCalE _ _ _), PndCalE _ _ _) _ |- _ =>
                pose L_f_b_synCall as f
                ; specialize f with (1:=h0) (2:=hw) (3:=h)
                ; inversion f; subst
            end.
            
            down_in. syncMMa.
            apply ap; eauto.

            resolve_eqvv.

            match goal with
            | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
            end.
          }

          1:{
            pose V_Cal_c as ap.
            assert (∃ a w', w=Plain a::w') by
              match goal with
              | h:Db _ _ w |- _ =>
                inversion h; eauto 
              end.
            breakAll; subst.
            specialize ap with (2:=H).
            down_in; syncMMa.
            apply ap; eauto.

            resolve_eqvv.

            match goal with
            | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v
              ; tryResolveBegin
            end.
          }

          1:{
            pose V_Cal_b2 as ap.
            assert (∃ w', w=Ret b1::w') by
              match goal with
              | h:Db _ _ w |- _ =>
                inversion h; eauto 
              end.
            breakAll; subst.
            specialize ap with (2:=H).
            down_in; syncMMa.
            apply ap; eauto.
            resolve_goEps.
            simpl in *; eauto.
          }
        }
      }

      1:{
        apply_concat.
        apply_in_map. 
        destruct x0.

        subst.
        apply_in_map.
        apply_nodup_in. 
        apply_filter_map.
        destruct x0.
        destruct o.

        1:{
          destruct c.
          1:{
            destruct l0;
            breakTuple; rmDirect;
            match goal with
            | h:In (?v, ?I) V |- _ =>
              specialize H with (1:=h)
            end.
      
            all: try discriminate.
            all: try (down_in; invalid_ma).
      
            1:{
      
              simpl.
              destruct l; try discriminate.
      
              destruct r.
              assert (i=Ret b) by (down_in;synci); subst.
              1:{
                pose (V_Ret_Pnd_bot) as ap.
                specialize ap with (3:=H).
                apply ap; eauto.
                resolveRule_fb; up_in.
                
                resolve_eqvv.
                match goal with
                | |- VBeginWith (?v::_) (beginE ?v) =>
                  destruct v as [[? | ?] | [?] | [? | ?]]
                  ; tryResolveBegin
                end.
                inversion H.
              }
      
              assert (i=Ret b) by (down_in;synci); subst.
              1:{
                pose (V_Ret_bot) as ap.
                
                specialize ap with (3:=H).
                apply ap; eauto.
                resolveRule_fb; up_in.
                
                resolve_eqvv.
                match goal with
                | |- VBeginWith (?v::_) (beginE ?v) =>
                  destruct v as [[? | ?] | [?] | [? | ?]]
                  ; tryResolveBegin
                end.
                inversion H.
              }
            }

            1:{
      
              simpl.
              destruct l; try discriminate.
              tac_invalid_db.
              
              destruct r0; try discriminate.
              
              destruct r;
              assert (i=Ret b0) by (down_in;synci); subst.
              1:{
                pose (V_Ret_Pnd) as ap.
                specialize ap with (3:=H).
                apply ap; eauto.
                resolveRule_fb; up_in.
                
                resolve_eqvv.
                match goal with
                | |- VBeginWith (?v::_) (beginE ?v) =>
                  destruct v as [[? | ?] | [?] | [? | ?]]
                  ; tryResolveBegin
                end.
                inversion H.
              }
      
              1:{
                pose (V_Ret_b1) as ap.
                specialize ap with (3:=H).
                apply ap; eauto.
                resolveRule_fb; up_in.
                
                resolve_eqvv.
                match goal with
                | |- VBeginWith (?v::_) (beginE ?v) =>
                  destruct v as [[? | ?] | [?] | [? | ?]]
                  ; tryResolveBegin
                end.
                inversion H.
              }
            }
          }

          1:{
    
            destruct l0; try discriminate.
            destruct r0; try discriminate.


            breakTuple; rmDirect;
            match goal with
            | h:In (?v, ?I) V |- _ =>
              specialize H with (1:=h)
            end.
    
            repeat match goal with 
            | Heq: ?s1 && ?s2 = true |- _ =>
              destruct (andb_true_iff s1 s2) as [_h1 _];
              destruct (_h1 Heq) as [? ?]
              ; clear Heq _h1
            end;
            
            repeat resolve_eqvv;
            repeat eqstr_True.
            destruct l; try discriminate.

            destruct v.

            1:{
              pose V_Ret_b2_a as ap;
              destruct va.
              1:{
                inversion H.
                match goal with
                | h:Db ?v ?T ?w |- _ =>
                  pose (BackwardSmallStep.Core.L4_2 v T w) as d
                  ; inversion d
                  ; rmDirect
                  ; breakAll; try discriminate; tac_inj; subst
                end;
                try (simplList; subst);
  
                try rmPendMat;
                try match goal with
                | h:PendT _ |- _ =>
                  inversion h; breakAll; subst; simplList; subst
                end;
                try rmPendMat.
              }
              assert (∃ w', w=Call a1::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H).

              destruct r;
              assert (i=Ret b2) by (down_in;synci); subst.

              1:{
                pose PForest2 as f.
                match goal with
                | h:In (?r', ?e') (vb_set.elements mb) |- _ =>
                  specialize f with (1:=Him) (2:=Hw) (r:=r') (e:=Retv e')
                end.
                getH. apply f. simpl; eauto. up_in.
                breakAll.
                match goal with
                | h:∀v1, Some ?v = Some _ -> _ |- _ =>
                  specialize h with (v1:=v)
                end.
                getH. apply f; eauto.
                simpl; up_in.
                breakAll.
    
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                  end.
                  
                destruct t.
    
                pose L_invalid_df_T as f2.
                specialize f2 with (1:=H9). easy.
    
                pose L_invalid_mb as f2.
                specialize f2 with (1:=H5). easy.
              }

              apply ap; eauto.
              resolveRule_fb; up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v as [? | ?]
              ; tryResolveBegin
              end.
            }

            1:{
              pose V_Ret_b2_c as ap;
              destruct vc;
              assert (∃ w', w=Plain c::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto 
                end;
              breakAll; subst;
              specialize ap with (3:=H).
              simpl in ap.
              
              destruct r;
              assert (i=Ret b1) by (down_in;synci); subst.

              1:{
                pose PForest2 as f.
                match goal with
                | h:In (?r', ?e') (vb_set.elements mb) |- _ =>
                  specialize f with (1:=Him) (2:=Hw) (r:=r') (e:=Retv e')
                end.
                getH. apply f. simpl; eauto. up_in.
                breakAll.
                match goal with
                | h:∀v1, Some ?v = Some _ -> _ |- _ =>
                  specialize h with (v1:=v)
                end.
                getH. apply f; eauto.
                simpl; up_in.
                breakAll.
    
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                  end.
                  
                destruct t.
    
                pose L_invalid_df_T as f2.
                specialize f2 with (1:=H9). easy.
    
                pose L_invalid_mb as f2.
                specialize f2 with (1:=H5). easy.
              }
    
              apply ap; eauto.
              resolveRule_fb; up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith ((_ ?v)::_) (beginE (_ ?v)) =>
              destruct v
              ; tryResolveBegin
              end.
            }

            1:{
              pose V_Ret_b2_b as ap.
              destruct vb.
              1:{
                inversion H.
              }
              assert (∃ w', w=Ret b0::w') by
                match goal with
                | h:Db _ _ w |- _ =>
                  inversion h; eauto; subst; simpl; eauto
                end.

              match goal with
              |  |- Db (_ :: Retv (MatRetE ?L8 ?a1 ?L9 ?b1 ?L10) :: _)
                (_::MatRetE ?L3 ?a0 ?L4 ?b0 ?L5 :: _) _ =>
                 assert (MatRetE L8 a1 L9 b1 L10=MatRetE L3 a0 L4 b0 L5) as _h by
                   match goal with
                   | h:Db _ _ w |- _ =>
                     inversion h; eauto; subst; simpl; eauto
                   end
                ; inversion _h
              end.

              breakAll; subst.
              simpl in ap.
              specialize ap with (2:=H).
              resolve_goEps.
              simpl in i0; eauto.
              destruct r;
              assert (i=Ret b1) by (down_in;synci); subst.

              1:{
                pose PForest2 as f.
                match goal with
                | h:In (?r', ?e') (vb_set.elements mb) |- _ =>
                  specialize f with (1:=Him) (2:=Hw) (r:=r') (e:=Retv e')
                end.
                getH. apply f. simpl; eauto. up_in.
                breakAll.
                match goal with
                | h:∀v1, Some ?v = Some _ -> _ |- _ =>
                  specialize h with (v1:=v)
                end.
                getH. apply f; eauto.
                simpl; up_in.
                breakAll.
    
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                  end.
                  
                destruct t.
    
                pose L_invalid_df_T as f2.
                match goal with
                | h:DF.Df _ _ _ |- _ =>
                  specialize f2 with (1:=h); easy
                end.

                pose L_invalid_mb as f2.
                match goal with
                | h:DF.Df _ _ _ |- _ =>
                  specialize f2 with (1:=h); easy
                end.
  
              }
              
              apply ap; eauto.
    
              resolveRule_fb; up_in.
    
            }
          }
        }
    
        1:{
          1:{
            destruct l0;
            breakTuple; rmDirect;
            match goal with
            | h:In (?v, ?I) V |- _ =>
              specialize H with (1:=h)
            end.
      
            all: try discriminate.
            all: try (down_in; invalid_ma).
      
            1:{
      
              simpl.
              destruct l; try discriminate.
      
              destruct r.
              assert (i=Ret b) by (down_in;synci); subst.
              1:{
                pose (V_Ret_Pnd_bot) as ap.
                specialize ap with (3:=H).
                apply ap; eauto.
                resolveRule_fb; up_in.
                
                resolve_eqvv.
                match goal with
                | |- VBeginWith (?v::_) (beginE ?v) =>
                  destruct v as [[? | ?] | [?] | [? | ?]]
                  ; tryResolveBegin
                end.
                inversion H.
              }
      
              assert (i=Ret b) by (down_in;synci); subst.
              1:{
                pose (V_Ret_bot) as ap.
                
                specialize ap with (3:=H).
                apply ap; eauto.
                resolveRule_fb; up_in.
                
                resolve_eqvv.
                match goal with
                | |- VBeginWith (?v::_) (beginE ?v) =>
                  destruct v as [[? | ?] | [?] | [? | ?]]
                  ; tryResolveBegin
                end.
                inversion H.
              }
            }

    
            simpl.
            destruct l; try discriminate.
            tac_invalid_db.
            
            destruct r0; try discriminate.
            
            destruct r;
            assert (i=Ret b0) by (down_in;synci); subst.
            1:{
              pose (V_Ret_Pnd) as ap.
              specialize ap with (3:=H).
              apply ap; eauto.
              resolveRule_fb; up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith (?v::_) (beginE ?v) =>
                destruct v as [[? | ?] | [?] | [? | ?]]
                ; tryResolveBegin
              end.
              inversion H.
            }
    
            1:{
              pose (V_Ret_b1) as ap.
              specialize ap with (3:=H).
              apply ap; eauto.
              resolveRule_fb; up_in.
              
              resolve_eqvv.
              match goal with
              | |- VBeginWith (?v::_) (beginE ?v) =>
                destruct v as [[? | ?] | [?] | [? | ?]]
                ; tryResolveBegin
              end.
              inversion H.
            }
          }
        }
      }
    Qed.
    (* end hide *)

    (** [pg2]: this lemma shows that given [V'=f_b m V], each parse tree
        in [v] is extended from a parse tree in [V], with some
        additional details. *)
    Lemma pg2:
      ∀ m V v T, In (v,T) (f_b m V) ->
      (∃ _M _T _w, _w != [] /\ Forest (m::_M) _T _w) ->
      ∃ v' I', In (v', I') V /\
      ∃ e, v=e::v' /\
        (∃ r,
          inRM (r,e) m /\
          (
            (
              I'=[] /\
              (
                (
                  r = None
                ) \/
                (
                  ∃ L1 a L2, r=Some (PndCalE L1 a L2) 
                )
              )
            ) \/
            (
              ∃ L1' b L2' I'',
                I'=PndRetE L1' b L2'::I'' /\ 
                (r=None \/ ∃ L1 a L2, r=Some (PndCalE L1 a L2))
            ) \/
            (
              ∃ L1 a L2 b L3 I'',
                I'=MatRetE L1 a L2 b L3::I'' /\
                r=Some (MatCalE L1 a L2 b L3)
            )
          )
        ).
    (* begin hide *)
    Proof.
      intros.
      rename H0 into Him.
      destruct Him as [_M [_T [_w [Hw Him]]]].
      destruct m; simpl in H.
      1:{
        apply_concat.
        apply_in_map. 
        destruct x0.

        subst.
        apply_in_map. 
        apply_nodup_in.
        apply_filter_map.
        destruct x0; 
        down_in.
        destruct o.
        destruct c0.

        destruct l0;
        breakTuple; rmDirect;
        simpl.
        1:{

          destruct l; try discriminate.


          destruct c;
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          left;
          getAnd; eauto.
        }

        1:{
          destruct l; try discriminate;
          destruct r; try discriminate;
          destruct c; try discriminate;

          try (discriminate);

          repeat (addEx + getAnd + eauto);
          right;
          left;
          repeat (addEx + getAnd + eauto).
        }


        destruct l0;
        breakTuple; rmDirect;
        simpl.
        discriminate.

        destruct l; try discriminate;
        destruct r; try discriminate;
        repeat (breakland;
        match goal with
        | h:true && true = true |- _ =>
        clear h
        end).
        repeat resolve_eqvv.
        repeat eqstr_True.
        destruct v; down_in.
        1:{
          destruct c.
          down_in;invalid_ma.

          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          right;
          right.
          repeat addEx; getAnd; eauto.
        }

        1:{
          destruct c.
          down_in;invalid_ma.
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          right;
          right.
          repeat addEx; getAnd; eauto.
        }

        1:{
          destruct c.
          
          down_in;invalid_ma.
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          right;
          right.
          repeat addEx; getAnd; eauto.
        }
        destruct l0;
        breakTuple; rmDirect;
        simpl.
        1:{

          destruct l; try discriminate.

          destruct c;
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          left;
          getAnd; eauto.
        }

        1:{

          destruct l; try discriminate;
          destruct r; try discriminate;
          destruct c; try discriminate;

          try (discriminate);

          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          down_in;invalid_ma.
        }
      }

      1:{
        apply_concat. 
        apply_in_map. 
        destruct x0.

        subst.
        apply_in_map.
        apply_nodup_in. 
        apply_filter_map.
        destruct x0; down_in.
        destruct o.
        destruct c.
        destruct l0;
        breakTuple; rmDirect.

        1:{

          simpl.
          destruct l; try discriminate.

          destruct p0.
          do 2 eexists; getAnd; eauto.
          eexists; getAnd; eauto.
          eexists; getAnd; eauto.
          left.
          getAnd; eauto.
        }

        1:{

          simpl.
          destruct l; try discriminate;
          destruct r; try discriminate.

          destruct p0.
          do 2 eexists; getAnd; eauto.
          eexists; getAnd; eauto.
          eexists; getAnd; eauto.
          right.
          left.
          repeat addEx; getAnd; eauto.
        }

        destruct l0;
        breakTuple; rmDirect.
        discriminate.


        simpl.
        destruct r; try discriminate.
        repeat (breakland;
          match goal with
          | h:true && true = true |- _ =>
          clear h
          end).
        repeat resolve_eqvv.
        repeat eqstr_True.
        
        destruct p0; try discriminate.

        destruct l; try discriminate.
        destruct v;

        do 2 eexists; getAnd; eauto;
        eexists; getAnd; eauto;
        eexists; getAnd; eauto;
        right;
        right;
        repeat addEx; getAnd; eauto.

        destruct l0;
        breakTuple; rmDirect.

        1:{

          simpl.
          destruct l; try discriminate.

          destruct p0.
          do 2 eexists; getAnd; eauto.
          eexists; getAnd; eauto.
          eexists; getAnd; eauto.
        }

        1:{

          simpl.
          destruct l; try discriminate;
          destruct r; try discriminate.

          destruct p0.
          do 2 eexists; getAnd; eauto.
          eexists; getAnd; eauto.
          eexists; getAnd; eauto.
          right.
          left.
          repeat addEx; getAnd; eauto.
        }
      }

      1:{
        apply_concat.
        apply_in_map. 
        destruct x0.

        subst.
        apply_in_map.
        apply_nodup_in. 

        apply_filter_map.
        destruct x0; down_in.
        destruct o.
        destruct c.
        destruct l0;
        breakTuple; rmDirect.
        1:{

          simpl.
          destruct l; try discriminate.

          destruct r;
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          left;
          repeat addEx; getAnd; eauto.
        }

        1:{

          simpl.
          destruct l; try discriminate;
          destruct r0; try discriminate;
          try discriminate.
          destruct r;
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          right;
          left;
          repeat addEx; getAnd; eauto.
        }

        destruct l0;
        breakTuple; rmDirect.
        discriminate.


        simpl.
        destruct r0; try discriminate.
        repeat (breakland;
          match goal with
          | h:true && true = true |- _ =>
          clear h
          end).
        repeat resolve_eqvv.
        repeat eqstr_True.
        
        destruct r; try discriminate.
        1:{
          pose PForest2 as f.
          match goal with
          | h:In (?r', ?e') (vb_set.elements mb) |- _ =>
            specialize f with (1:=Him) (2:=Hw) (r:=r') (e:=Retv e')
          end.
          getH. apply f. simpl; eauto.
          breakAll.
          match goal with
          | h:∀v1, Some ?v = Some _ -> _ |- _ =>
            specialize h with (v1:=v)
          end.
          getH. apply f; eauto. 
          breakAll.

          pose L_invalid_mb as f2.
          specialize f2 with (1:=H4).
          easy.
        }
        destruct l; try discriminate;
        destruct v; try discriminate;

        do 2 eexists; getAnd; eauto;
        eexists; getAnd; eauto;
        eexists; getAnd; eauto;
        right;
        right;
        repeat addEx; getAnd; eauto.

        destruct l0;
        breakTuple; rmDirect.
        1:{

          simpl.
          destruct l; try discriminate.

          destruct r;
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          left;
          repeat addEx; getAnd; eauto.
        }

        1:{

          simpl.
          destruct l; try discriminate;
          destruct r0; try discriminate;
          try discriminate.
          destruct r;
          do 2 eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          eexists; getAnd; eauto;
          right;
          left;
          repeat addEx; getAnd; eauto.
        }
      }
    Qed.

    Global Hint Resolve la_eq_dec: misc.
    Global Hint Resolve lc_eq_dec: misc.
    Global Hint Resolve lb_eq_dec: misc.
    Global Hint Resolve lve_eq_dec: misc.

    Lemma lvb_eq_dec: ∀ x y : list VE * list RetEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma lva_eq_dec: ∀ x y : list VE * list CalEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Lemma lvc_eq_dec: ∀ x y : list VE * list PlnEdge, {x = y} + {x != y}.
    Proof.
      decide equality;
      eauto with misc.
    Qed.

    Global Hint Resolve lvb_eq_dec: misc.
    Global Hint Resolve lva_eq_dec: misc.
    Global Hint Resolve lvc_eq_dec: misc.
    (* end hide *)

    (** [f_init]: the initialization extraction function [f_init] builds
        the initial partial parse trees from the last state in a forest.
    *)
    Definition f_init (m:ME) 
    : list (list VE * list RetEdge) 
    :=
      match m with
      | PlnCME m =>
        let m := vc_set.elements m in
        let f (v:option CalEdge * PlnEdge) :=
          let (r, e) := v in
          match r with
          | None => goEps (Plnv e)
          | Some (PndCalE _ _ _) => goEps (Plnv e)
          | _ => false
          end
        in
        let g (v:option CalEdge * PlnEdge) :=
          let (r, e) := v in
          e
        in
        let es := (filter_map m f g) in 
        map 
        (fun e => ([Plnv e],[]))
        (PreTimed.nodup ec_inlist es )
      | CalCME m =>
        let m := va_set.elements m in
        let f (v:option CalEdge * CalEdge) :=
        let (r, e) := v in
          match r with
          | None => goEps (Calv e)
          | Some (PndCalE _ _ _) => goEps (Calv e)
          | _ => false
          end
        in
        let g (v:option CalEdge * CalEdge) :=
          let (r, e) := v in
          e
        in
        map 
        (fun e => ([Calv e],[]))
        (PreTimed.nodup ea_inlist (filter_map m f g))
      | RetCME m =>
        let m := vb_set.elements m in
        let f (v:option CalEdge * RetEdge) :=
        let (r, e) := v in
          match r with
          | None => goEps (Retv e)
          | Some (PndCalE _ _ _) => goEps (Retv e)
          | _ => false
          end
        in
        let g (v:option CalEdge * RetEdge) :=
          let (r, e) := v in
          e
        in
        map 
        (fun e => ([Retv e],[e]))
        (PreTimed.nodup eb_inlist (filter_map m f g))
      end.

    (* begin hide *)

    Ltac resolve_goEps2 :=
      match goal with 
      | h:  in_rules (?L1, Alt_Epsilon) P |- _ =>
        apply (L_goEps); simpl; eauto 
      end.

    Lemma L_syncMi: ∀ m M T w i,
      Forest (m::M) T (w++[i]) ->
      ∀ r e, inRM (r,e) m -> getSymVE e = i.
    Proof.
      intros.
      inversion H; subst; tac_inj; subst.

      destruct m1;
      simpl in H6; try breakTuple;
      destruct i;
      match goal with
      | h:_ = p _ _ _ |- _ =>
      unfold p in h
      end;
      (breakTuple + (destruct T0; breakTuple)); rmDirect.

      all: match goal with
      | h: inRM (?r, ?e) (m2CallM ?m' ?s) |- _ =>
        destruct (L_m2CallM m' s r e) as [d _]
        ; rmDirect
      | h: inRM (?r, ?e) (m2PlainM ?m' ?s) |- _ =>
        destruct (L_m2PlainM m' s r e) as [d _]
        ; rmDirect
      | h: inRM (?r, ?e) (m2RetM ?m' ?t ?s) |- _ =>
        destruct (L_m2RetM m' t s r e) as [d _]
        ; rmDirect
      end.

      all: breakAll.

      all: match goal with
      | h: inRM (?x, _) _ |- _ =>
        destruct x as [[] | ]
      end.
      
      all: try match goal with
      | h: _ = None \/ _ -> ?g |- _ =>
        assert g; [apply h; ((left; eauto) + (right; repeat addEx; eauto)); fail |]
      end +
      match goal with
      | h: (∃ _, _) -> ?g |- _ =>
        assert g; [apply h; repeat addEx; eauto; fail |]
      end;
      breakAll; subst; simpl; eauto.
    Qed.

    (* end hide *)

    (** [L_f_init]: the lemmas shows that the parse trees built by
       [f_init] satisfies the backward small-step relation. *)
    Lemma L_f_init : ∀ m M T w i,
      Forest (m::M) T (w++[i]) ->
      ∀ v I,
      (In (v,I) (f_init m) <->
        Db v I [i] /\
        ∃ e, v=[e] /\
        (inRM (None,e) m
          \/ ∃ L1 a C, inRM (Some (PndCalE L1 a C),e) m)).
    (* begin hide *)
    Proof.
      intros.
      split.
      1:{
        intros.
        destruct m.
        1:{

          simpl in H0.
          apply_in_map; breakTuple; rmDirect.
          apply_nodup_in.

          (* match goal with
          | h:In ?x (nodup ?dec ?l) |- _ =>
            destruct (nodup_In dec l x) as [_H _]
            ; specialize _H with (1:=h)
            ; clear h
            ; rename _H into h
          end. *)
          apply_filter_map.
          destruct x0.
          destruct o.
          1:{
            destruct c0.
            1:{
              resolve_goEps.
              subst.
              rmDirect.
              (* rmDirect. *)
              
              getAnd.
              1:{
                match goal with
                | h:Forest _ T ?w |- _ =>
                assert (w != []) by eauto using app_cons_not_nil
                end.
                destruct c.
                assert (i=Call a0).
                1:{
                  inversion H; subst; tac_inj; subst.
                  match goal with
                  | h:_ = p _ _ _ |- _ =>
                  unfold p in h
                  end.
                  destruct i.
                  breakTuple.
                  Ltac syncim :=
                  match goal with
                  | h: Forest _ _ _, h2: In (?r', ?e') _ |- _ =>
                    pose L_syncMi as f_L_syncMi
                    ; specialize f_L_syncMi with (1:=h) (r:=r')
                      (e:=Calv e')
                    ; getH; [apply f_L_syncMi; simpl; eauto |]
                    ; simpl in *; eauto
                  | h: Forest _ _ _, h2: In (?r', ?e') _ |- _ =>
                    pose L_syncMi as f_L_syncMi
                    ; specialize f_L_syncMi with (1:=h) (r:=r')
                      (e:=Plnv e')
                    ; getH; [apply f_L_syncMi; simpl; eauto |]
                    ; simpl in *; eauto
                  | h: Forest _ _ _, h2: In (?r', ?e') _ |- _ =>
                    pose L_syncMi as f_L_syncMi
                    ; specialize f_L_syncMi with (1:=h) (r:=r')
                      (e:=Retv e')
                    ; getH; [apply f_L_syncMi; simpl; eauto |]
                    ; simpl in *; eauto
                  end.
                  syncim; up_in.
                  destruct m; simpl in H8; discriminate.
                  destruct T0; simpl in H8;
                  destruct m; simpl in H8; discriminate.
                }
                
                subst.
                constructor; eauto.

                down_in.
                syncMMa.
                resolveRule_fb; up_in.
                down_in;invalid_ma.
              }
              down_in.
              eexists; getAnd; eauto.

            }
            discriminate.
          }

          1:{
            resolve_goEps.
            subst.
            rmDirect.
            
            getAnd.
            1:{
              match goal with
              | h:Forest _ T ?w |- _ =>
              assert (w != []) by eauto using app_cons_not_nil
              end.
              destruct c;
              down_in;invalid_ma.
            }
            down_in.
            eexists; getAnd; eauto.
          }
        }

        1:{

          simpl in H0.
          apply_in_map; breakTuple; rmDirect.

          apply_nodup_in. 

          apply_filter_map.
          destruct x0.
          destruct o.
          1:{
            destruct c.
            1:{
              resolve_goEps.
              subst.
              rmDirect.
              
              getAnd.
              1:{
                destruct p0.
                match goal with
                | h:Forest _ T ?w |- _ =>
                assert (w != []) by eauto using app_cons_not_nil
                end.
                syncim; subst. up_in.
                constructor; eauto.
                resolveRule_fb; up_in.
              }
              down_in.
              eexists; getAnd; eauto.
            }
            discriminate.
          }

          1:{
            resolve_goEps.
            subst.
            rmDirect.
            
            getAnd.
            1:{
              destruct p0.
              match goal with
              | h:Forest _ T ?w |- _ =>
              assert (w != []) by eauto using app_cons_not_nil
              end.
              syncim; subst. up_in.
              constructor; eauto.
              resolveRule_fb; up_in.
            }
            down_in.
            eexists; getAnd; eauto.
          }
        }

        1:{

          simpl in H0.
          apply_in_map; breakTuple; rmDirect.
          apply_nodup_in.

          apply_filter_map.
          destruct x0.
          destruct o.
          1:{
            destruct c.
            1:{
              resolve_goEps.
              subst.
              rmDirect.
              
              getAnd.
              1:{
                match goal with
                | h:Forest _ T ?w |- _ =>
                assert (w != []) by eauto using app_cons_not_nil
                end.

                destruct r;
                down_in; syncim; subst;
                constructor; eauto;
                resolveRule_fb; up_in.
              }
              down_in.
              eexists; getAnd; eauto.
            }
            discriminate.
          }

          1:{
            resolve_goEps.
            subst.
            rmDirect.
            down_in.
            
            getAnd.
            1:{
              match goal with
              | h:Forest _ T ?w |- _ =>
              assert (w != []) by eauto using app_cons_not_nil
              end.

              destruct r;
              syncim; subst;
              constructor; eauto;
              resolveRule_fb; up_in.
            }
            eexists; getAnd; eauto.
          }
        }
      }

      1:{
        intros.
        breakAll; subst.

        1:{
          inversion H1; subst; simpl;
          destruct m; simpl in H0; try easy
          ; simpl; 
          apply_in_map.

          all: eexists; getAnd; eauto;
          apply_nodup_in;
          apply_filter_map;
          eexists;
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in;
          getAnd; eauto;
          resolve_goEps2.
        }

        1:{
          inversion H1; subst; simpl;
          destruct m; simpl in H0; try easy
          ; simpl; apply_in_map.
          all: eexists; getAnd; eauto;
          apply_nodup_in;
          apply_filter_map;
          eexists;
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in;
          getAnd; eauto;
          resolve_goEps2.
        }
      }
    Qed.
    (* end hide *)

    (** [Extract]: the relation [Extract] formalizes the behaviour of
        the extraction function [f_b]. [Extract m M V (w++[i]) w'] means
        that we have extracted a set of partial parse trees [V], and the
        rest forest is [m::M], which is the forest of the string
        (w++[i]), and [w++[i]++w'] is the input string. *)
    Inductive Extract : list ME -> list (list VE * list RetEdge) -> 
      list symbol -> list symbol -> Prop := 
    | EInit m M T w i : 
      Forest (m::M) T (w++[i]) 
      -> Extract M (f_init m) w [i]
    | EInte m M V w1 i w2: 
      Extract (m::M) V (w1++[i]) w2
      -> Extract M (f_b m V) w1 (i::w2).

    (** [L_forest]: intuitively, a state is a compression of a set of
      parse trees. This lemma formalizes this intuition and shows that
      each rule in the state [m] must be the last rule of some parse
      trees in the forward small-step derivation [Df]. *)
    Lemma L_forest : ∀ m M T w,
      Forest (m::M) T w 
      -> w!=[] 
      -> ∀ r e, inRM (r, e) m 
      -> ∃ v1 T1, Df (v1++[e]) T1 w 
        /\ VBeginWith (v1++[e]) L_0
        /\ (r=None -> T1=[])
        /\ (∀ i, r=Some i -> ∃ T1', T1=i::T1').
    (* begin hide *)
    Proof.
      intros.
      pose PForest2 as d.
      specialize d with (1:=H) (3:=H1).
      rmDirect.
      breakAll.
      destruct r.
      1:{
        specialize H2 with (ea:=c).
        rmDirect.
        breakAll.
        exists x, (c::x0).
        getAnd; eauto.
        getAnd; eauto.
        getAnd; intros.
        discriminate.
        inversion H5; subst.
        eauto.
      }

      1:{
        rmDirect.
        breakAll.
        exists x, [].
        getAnd; eauto.
        getAnd; eauto.
        getAnd; intros; eauto.
        discriminate.
      }
    Qed.
    (* end hide *)

    (* begin hide *)
    Lemma Db_rule: ∀ v T w, Db v T w 
      -> ∀ L a L1 b L2 T', T = MatRetE L a L1 b L2 :: T'
      -> in_rules (L, Alt_Match a b L1 L2) P.
    Proof.
      intros v T w H.
      induction H; intros; try discriminate;
      try simplList; subst.
      all: try (apply (IHDb) with (T'0:=T'); eauto; fail).

      all: try (match goal with
      | h: Db ?v ?T ?w |- _ =>
        pose (BackwardSmallStep.Core.L4_2 v T w) as h0
        ; inversion h0
      end;
      rmDirect;
      breakAll; subst; tac_inj; try discriminate);

      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end; eauto;
      try (
        match goal with
      | h: PendT (PndRetE _ _ _ :: MatRetE _ _ _ _ _:: _) |- _ =>
      inversion h; breakAll; subst
      end;
      simplList; subst;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end
      );
      try match goal with
      | h:Db _ _ _ |- _ =>
        inversion h; eauto; subst; fail
      end.

      try (do 2 match goal with
      | h: Db _ _ _ |- _ =>
        inversion h; subst
      end; fail).

      all: repeat (simplList; subst).

      do 2 match goal with
      | h: Db _ _ _ |- _ =>
        inversion h; subst; eauto; try tac_invalid_db
      end.
      
      match goal with
      | h: BreakDV _ _ _ |- _ =>
        inversion h
      end;
      rmDirect; breakAll; subst; tac_inj; try discriminate;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end; repeat (simplList; subst); eauto.


      do 2 match goal with
      | h: Db _ _ _ |- _ =>
        inversion h; subst; eauto; try tac_invalid_db
      end.

      match goal with
      | h: BreakDV _ _ _ |- _ =>
        inversion h
      end;
      rmDirect; breakAll; subst; tac_inj; try discriminate;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end; repeat (simplList; subst); eauto.

      match goal with
      | h: BreakDV _ _ _ |- _ =>
        inversion h
      end;
      rmDirect; breakAll; subst; tac_inj; try discriminate;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end; repeat (simplList; subst); eauto.

      match goal with
      | h: BreakDV _ _ _ |- _ =>
        inversion h
      end.
      rmDirect; breakAll; subst; tac_inj; try discriminate;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end; repeat (simplList; subst); eauto.

      match goal with
      | h: BreakDV _ _ _ |- _ =>
        inversion h
      end.
      rmDirect; breakAll; subst; tac_inj; try discriminate;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end; repeat (simplList; subst); eauto.

      match goal with
      | h: BreakDV _ _ _ |- _ =>
        inversion h
      end.
      rmDirect; breakAll; subst; tac_inj; try discriminate;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end; repeat (simplList; subst); eauto.
    Qed.

    Ltac assertLast h := 
      match h with 
      | _ -> ?h2 => assertLast h2
      | ?h2 => assert h2
      end.

    Ltac getH := match goal with
    | h: _ -> ?h2 |- _ =>
      assertLast h2
    end.

    Lemma pf1_sub: ∀ M V w1 w2,
      Extract M V w1 w2 ->
      ∃ T, Forest M T w1.
    Proof.
      intros.
      induction H.
      inversion H; subst; tac_inj; subst; eauto.
      breakEx.
      inversion IHExtract; subst; tac_inj; subst; eauto.
    Qed.
    (* end hide *)

    (** [pf1]: this lemma shows that if we extract a set of parse trees
        [V], then each rule in [V] satisfies the forward small-step
        derivation. *)
    Lemma pf1:
      ∀ m M V w1 w2,
      Extract (m :: M) V w1 w2 ->
      w1 != [] ->
      ∀ e, 
      (
        inRM (None,e) m ->
          ∃ v1e, Df (v1e++[e]) [] w1 /\ VBeginWith (v1e++[e]) L_0
      ) /\
      (
        ∀ r,
        inRM (Some r,e) m ->
          ∃ v1e T1e, Df (v1e++[e]) (r::T1e) w1 /\ VBeginWith (v1e++[e]) L_0
      ).
    (* begin hide *)
    Proof.
      intros.
      pose (pf1_sub) as d.
      specialize d with (1:=H). breakEx.
      pose  TimedSets.Parser.PForest2 as d1.
      specialize d1 with (1:=d).
      rmDirect.

      getAnd; intros; specialize H1 with (1:=H2).
      breakAll; rmDirect; breakAll; eauto.
      breakAll.
      specialize H1 with (ea:=r).
      rmDirect; breakAll; eauto.
    Qed.
    (* end hide *)

    (** [pf3]: this lemma shows that when we extract a set of parse
        trees from part of a forest and the rest forest is [m::M] of the
        string [w1], then the last rule of each parse tree of [w1] must
        reside in [m]. *)
    Lemma pf3: 
      ∀ m M V w1 w2, 
      Extract (m :: M) V w1 w2 ->
      ∀ v T, Df v T w1 ->
      VBeginWith v L_0 ->
      ∃ e v' r, v=v'++[e] /\ inRM (r,e) m.
    (* begin hide *)
    Proof.
      intros.
      pose (pf1_sub) as d.
      specialize d with (1:=H). breakEx.
      pose TimedSets.Parser.PForest1 as d1.
      specialize d1 with (1:=d).

      destruct w1. tac_invalid_df.
      pose ForwardSmallStep.DFX.DF_dfx as a.
      specialize a with (1:=H0). breakAll.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion a; subst; eauto;
        eexists; exists []; simpl; eauto. 
      }
      breakAll; subst.
      specialize d1 with (1:=a) (Le:=endE x4).
      getH. apply d1; eauto.
      resolveEndESelf.
      breakAll; subst; eauto.
    Qed.
    (* end hide *)

    (* begin hide *)
    Lemma list_inj2: ∀ (l1:list symbol) l2 l3 l4,
      l1++l2=l3++l4 ->
      length l2 = length l4 ->
      l2 = l4.
    Proof.
      intros l1 l2 l3.
      generalize dependent l1.
      generalize dependent l2.
      induction l3 using 
        (well_founded_ind (Def.LEN_WF.len_wf _)).
      intros.
      destruct l1; destruct l3;
      simpl in *; eauto.

      exfalso.
      subst.
      simpl in H1.
      rewrite (app_length l3 l4) in H1.
      match goal with
      | h:S (?a+?b) = ?b |- _ =>
        rewrite <- (Nat.add_succ_l a b) in h
      end.
      lia.

      exfalso.
      subst.
      simpl in H1.
      rewrite (app_length l1 l2) in H1.
      match goal with
      | h:?b = S (?a+?b) |- _ =>
        rewrite <- (Nat.add_succ_l a b) in h
      end.
      lia.

      simplList.
      apply H with (2:=H4); eauto.
      unfold Def.LEN_WF.len.
      simpl. lia.
    Qed.

    Lemma list_inj: ∀ (l1:list symbol) l2 l3 l4,
      l1++l2=l3++l4 ->
      length l1 = length l3 ->
      l1 = l3.
    Proof.
      intro l1.
      induction l1 using 
        (well_founded_ind (Def.LEN_WF.len_wf _)).
      intros.

      destruct l1; destruct l3;
      simpl in *; eauto;  try discriminate.

      simplList.
      specialize H with (2:=H4); eauto.
      getH. apply H.
      unfold Def.LEN_WF.len.
      simpl. lia.
      inversion H1; eauto.
      subst; eauto.
    Qed.

    Ltac tryResolveBegin1 :=
      match goal with
      | h:VBeginWith ?x ?L |- VBeginWith (?x ++ _) ?L =>
        inversion h; subst; simpl; breakAll; subst
        ; repeat rewrite <- app_assoc
        ; tryResolveBegin
      end.

    Ltac resolveRule :=
      match goal with
      | h:Dfx _ (MatCalE ?L1 ?a ?L2 ?b ?L3::_) _ _ _ _ _
      |- In (?L1, Alt_Match ?a ?b ?L2 ?L3) P =>
        apply (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ h)
      | h:Dfx _ [PndCalE ?L1 ?a ?L2] _ _ _ _ _
      |- In (?L1, Alt_Linear (Call ?a) ?L2) P =>
        apply (DFX_df_rule1 _ _ _ _ _ _ _ _ _ _ h)
      | h:Dfx _ (PndCalE ?L1 ?a ?L2::_) _ _ _ _ _
      |- In (?L1, Alt_Linear (Call ?a) ?L2) P =>
        apply (DFX_df_rule1 _ _ _ _ _ _ _ _ _ _ h)
      | h:Dfx _ (MatCalE ?L1 ?a ?L2 ?b ?L3::_) _ _ _ _ _
      |- in_rules (?L1, Alt_Match ?a ?b ?L2 ?L3) P =>
        apply (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ h)
      | h:Dfx _ [PndCalE ?L1 ?a ?L2] _ _ _ _ _
      |- in_rules (?L1, Alt_Linear (Call ?a) ?L2) P =>
        apply (DFX_df_rule1 _ _ _ _ _ _ _ _ _ _ h)
      | h:Dfx _ (PndCalE ?L1 ?a ?L2::_) _ _ _ _ _
      |- in_rules (?L1, Alt_Linear (Call ?a) ?L2) P =>
        apply (DFX_df_rule1 _ _ _ _ _ _ _ _ _ _ h)
      end.
    (* end hide *)

    (** [L_Db_uniqueT]: this lemmas shows that each backward small-step
        relation has a unique stack. *)
    Lemma L_Db_uniqueT: ∀ v T1 T2 w1 w2, 
      Db v T1 w1 -> Db v T2 w2 ->
      T1=T2.
    (* begin hide *)
    Proof.
      intro v.
      induction v using 
        (well_founded_ind (Def.LEN_WF.len_wf _)).
      intros.
      match goal with
      | h: Db _ _ _, h1: Db _ _ _ |- _ =>
      inversion h; inversion h1; subst; eauto
      end.

      all: try match goal with
      | h: Db [?v] _ _, h1: Db [?v] _ _ |- _ =>
        inversion h; inversion h1; subst;
        tac_invalid_db
      end.

      all: try (simplList; subst).

      all: try tac_invalid_db.

      all: try (
        match goal with
        | h: Db ?v _ _, h1: Db ?v _ _ |- _ =>
        specialize H with (y:=v0) (2:=h) (3:=h1)
        ; apply H
        ; unfold Def.LEN_WF.len
        ; simpl
        ; lia
        end).

      all: try match goal with
      | h: Db ?v _ _, h1: Db ?v _ _ |- _ =>
        specialize H with (y:=v0) (2:=h) (3:=h1)
      ; getH
      ; [tac_app; 
        unfold Def.LEN_WF.len
        ; simpl
        ; lia; discriminate | discriminate]
      end.

      all: try match goal with
      | h: Db ?v _ _, h1: Db ?v _ _ |- _ =>
        specialize H with (y:=v0) (2:=h) (3:=h1)
        ; getH
        ; [tac_app; 
          unfold Def.LEN_WF.len
          ; simpl
          ; lia |]
        ; simplList; eauto
      end.

      all: eauto.
      all: try (simpl in *; discriminate).

      all: try (simpl in *; simplList; subst;
      match goal with
      | h: Db ?v _ _, h1: Db ?v _ _ |- _ =>
        specialize H with (y:=v0) (2:=h) (3:=h1)
        ; getH
        ; [tac_app; 
        unfold Def.LEN_WF.len
        ; simpl
        ; lia; discriminate | discriminate]
      end).

    Qed.
    (* end hide *)

    (** [L_invalid_comb]: this lemmas shows that we cannot concatenate a
        forward small-step parse tree with a backward small-step parse
        tree, if the forward small-step parse tree has an empty stack,
        while the backward small-step parse tree has a stack with its
        top to be a matching rule. *)
    Lemma L_invalid_comb: ∀ v L a L1 b L2 T w', 
      Db v (MatRetE L a L1 b L2::T) w' ->
      ∀ x e w'', Df (x ++ [e]) [] w'' ->
      DM.Dm L_0 (w''++w') ((x ++ [e]) ++ v) -> False.
    (* begin hide *)
    Proof.
      Import ForwardSmallStep.Core.
      intros.
      pose (CompleteM) as d0.
      specialize d0 with (1:=H1).
      getH. tac_app; 
      eauto using nil_cons, app_cons_not_nil.
      destruct w''; eauto using nil_cons.
      tac_invalid_df.
      clear d0.
      breakEx.
      breakAnd.
      rename H3 into Ha.

      match goal with
      | h: Db ?v ?T ?w |- _ =>
        pose (BackwardSmallStep.Core.L4_2 v T w) as aa
      end.
      inversion aa; subst.
      rmDirect.
      breakAll; subst; tac_inj; subst; try discriminate;
      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end;
      simplList; subst.

      all: try (
        inversion Ha;
        tac_inj;
        subst;
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end).


      all: try (match goal with
      | h: Df (?x ++ ?ee ::?v') _ (?w1 ++ ?i :: ?w') |- _ =>
        pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
        specialize sp with (1:=h) (v1:=x ++ [ee])
          (v2:=v')
        ; getH; [apply sp; [repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl; eauto |
          eauto using app_cons_not_nil] |]
        ; breakAll
        ; clear sp
      end;
      match goal with
      | h:Df _ _ _ |- _ =>
      inversion h
      end;
      tac_inj;
      repeat match goal with
      | h:_ = ?x ++ [?y;?z] |- _ =>
        assert (x++[y;z]=(x++[y])++[z]) as rw
        by (repeat rewrite <- app_assoc; eauto)
        ; rewrite rw in h
        ; clear rw
        ; tac_inj
      end;
      subst;
      match goal with
      | h: Df ?v _ _, 
        h1: Df ?v _ _ |- _ =>
        destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
        ; eauto
        ; try discriminate
        ; try simplList
        ; eauto
      end).


      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        inversion Ha; try rmInvalidList; subst; tac_inj; subst.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        inversion Ha; try rmInvalidList; subst; tac_inj; subst.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H5; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }


      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H5; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H4; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H4; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

    Qed.
    (* end hide *)
    
    (** [L_invalid_comb_pndc]: this lemmas shows that we cannot
        concatenate a forward small-step parse tree with a backward
        small-step parse tree, if the forward small-step parse tree has
        a stack with its top to be a pending rule, while the backward
        small-step parse tree has a stack with its top to be a matching
        rule. *)
    Lemma L_invalid_comb_pndc: ∀ v L a L1 b L2 T w', 
      Db v (MatRetE L a L1 b L2::T) w' ->
      ∀ x e T' L' a L'' w'', Df (x ++ [e]) (PndCalE L' a L''::T') w'' ->
      DM.Dm L_0 (w''++w') ((x ++ [e]) ++ v) -> False.
    (* begin hide *)
    Proof.
      intros.
      pose (ForwardSmallStep.Core.CompleteM) as d0.
      specialize d0 with (1:=H1).
      getH. tac_app; 
      eauto using nil_cons, app_cons_not_nil.
      destruct w''; eauto using nil_cons.
      tac_invalid_df.
      clear d0.
      breakEx.
      breakAnd.
      rename H3 into Ha.

      match goal with
      | h: Db ?v ?T ?w |- _ =>
        pose (BackwardSmallStep.Core.L4_2 v T w) as aa
      end.
      inversion aa; subst.
      rmDirect.
      breakAll; subst; tac_inj; subst; try discriminate;

      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end;
      simplList; subst.

      all: try (
        inversion Ha;
        tac_inj;
        subst;
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end).


      all: try (match goal with
      | h: Df (?x ++ ?ee ::?v') _ (?w1 ++ ?i :: ?w') |- _ =>
        pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
        specialize sp with (1:=h) (v1:=x ++ [ee])
          (v2:=v')
        ; getH; [apply sp; [repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl; eauto |
          eauto using app_cons_not_nil] |]
        ; breakAll
        ; clear sp
      end;
      match goal with
      | h:Df _ _ _ |- _ =>
      inversion h
      end;
      tac_inj;
      repeat match goal with
      | h:_ = ?x ++ [?y;?z] |- _ =>
        assert (x++[y;z]=(x++[y])++[z]) as rw
        by (repeat rewrite <- app_assoc; eauto)
        ; rewrite rw in h
        ; clear rw
        ; tac_inj
      end;
      subst;
      match goal with
      | h: Df ?v _ _, 
        h1: Df ?v _ _ |- _ =>
        destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
        ; eauto
        ; try discriminate
        ; try simplList
        ; eauto
      end).


      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        inversion Ha; try rmInvalidList; subst; tac_inj; subst.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        inversion Ha; try rmInvalidList; subst; tac_inj; subst.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H5; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }


      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H5; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H4; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

      1:{
        match goal with
        | h: ∀ _ _ _, Df _ _ _ -> _,
          h2: Df (x++[?ee]) _ _ |- _ =>
          specialize h with (1:=h2) 
          ; getH; [apply h; exists (endE ee); getAnd; eauto |]
        end.
        apply VListEndSame2.
        resolveEndESelf.

        destruct x9;
        try match goal with 
        | h: VBeginWithS [] _ _ |- _ => inversion h; breakAll; subst; discriminate
        end.
        match goal with
        | h: Df ((x++[e]) ++ (?e'::?v) ++ ?v') _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=x++[e]) (v2:=[e']++v++v')
          (Lv1:=endE e)
          (Lv2:=beginE e')
        end.
        getH. apply d; eauto using app_cons_not_nil.
        repeat rewrite <- app_assoc; 
        repeat rewrite <- app_comm_cons;
        simpl;
        eauto.
        destruct v; eauto using nil_cons.
        apply VListEndSame2; resolveEndESelf.

        apply VListBeginSame2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.
        rewrite H2.
        match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; tryResolveBegin
        end;
        match goal with
        | h:DM.Dm _ _ _ |- _ =>
          inversion h
        end.

        match goal with
        | h: Df (?x ++ ?v' ++ [Retv ?eb] ++ ?v'') _ _ |- _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=h) (v1:=x ++ v' ++ [Retv eb])
            (v2:=v'')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; rewrite <- app_comm_cons; simpl; eauto |
            repeat rewrite app_assoc;
            eauto using app_cons_not_nil] |]
          ; breakAll
        end.
        inversion H4; subst; try rmInvalidList; tac_inj; subst.
        rewrite <- app_assoc in *.
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
          ; try discriminate
          ; try simplList
          ; eauto
        end.
      }

    Qed.

    Lemma VListEndSame: ∀ x e v L, 
      VEndWith (x++e::v) L -> VEndWith (e::v) L.
    Proof.
      intros.

      assert (e:: v!=[]) as notnil by eauto using nil_cons
      ; destruct (exists_last notnil) as [? [? _s]]
      ; rewrite _s in *
      ; clear notnil _s
      ; repeat rewrite app_assoc in h.
      rewrite app_assoc in H;
      inversion H
      ; repeat (breakEx)
      ; subst;
      tac_inj; subst;
      BackwardSmallStep.Core.tryResolveEnd.
    Qed.
    (* end hide *)

    (** [L_invalid_comb_matc_e]: this lemmas shows that we cannot
        concatenate a forward small-step parse tree with a backward
        small-step parse tree, if the forward small-step parse tree has
        a stack with its top to be a matching rule, while the backward
        small-step parse tree has an empty stack. *)
    Lemma L_invalid_comb_matc_e: ∀ v w', 
      Db v [] w' ->
      ∀ x e T' L a L1 b L2 w'', 
      Df (x ++ [e]) (MatCalE L a L1 b L2::T') w'' ->
      DM.Dm L_0 (w''++w') ((x ++ [e]) ++ v) -> False.
    (* begin hide *)
    Proof.
      intros.
      pose (ForwardSmallStep.Core.CompleteM) as d0.
      specialize d0 with (1:=H1).
      getH. tac_app; 
      eauto using nil_cons, app_cons_not_nil.
      destruct w''; eauto using nil_cons.
      tac_invalid_df.
      clear d0.
      breakEx.
      breakAnd.
      rename H3 into Ha.

      pose (L5_2 _ _ _ H1) as f.
      getH. apply f. destruct w''; try tac_invalid_df; eauto using nil_cons.
      repeat (breakAnd + breakEx).

      pose (BackwardSmallStep.Core.SoundV) as d0.
      destruct v; try tac_invalid_db.

      specialize d0 with (1:=H) (Le:=x1) (Lv:=beginE v).
      getH. apply d0; eauto. 
      match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; simpl
        ; tryResolveBegin
      end.
      inversion H.
      apply VListEndSame with (x ++ [e]); eauto.
      
      match goal with
      | h:Df ?v ?T w'' |- _ =>
      pose (ForwardSmallStep.Core.L4_2 v T w'') as bk
      ; inversion bk
      ; rmDirect
      end.

      assert (True -> x0 = []
      ∨ (∃ (L1 : var) (a : terminal) (L2 : var) (T' : list CalEdge),
        x0 = PndCalE L1 a L2 :: T')).
      1:{
        intro. eauto.
      }
      
      clear H2.
      breakAll; try discriminate; tac_inj; subst.
      rmDirect.
      breakAll; try discriminate; tac_inj; subst.
      simplList; eauto; subst.

      rewrite H10 in H0.
      pose (ForwardSmallStep.Split.DF_SPLIT) as sp.
      specialize sp with (1:=H0) (v1:=x3 ++ [Calv (MatCalE x8 x7 x9 x10 x11)])
        (v2:=x4)
      ; getH; [apply sp; [repeat rewrite <- app_assoc; 
      repeat rewrite <- app_comm_cons;
      simpl; eauto |
        eauto using app_cons_not_nil] |]
      ; breakAll
      ; clear sp.

      assert ((∃ T, x12=MatCalE x8 x7 x9 x10 x11::T)).
      1:{
        inversion H9; subst; tac_inj; subst;
        inversion a0; subst; eauto.
      }

      assert ((∃ w', x13=w'++[Call x7])).
      1:{
        inversion H9; subst; tac_inj; subst;
        inversion a0; subst; eauto.
        exists []; eauto.
      }
      repeat breakEx; subst.

      pose (L4_5) as g.
      specialize g with (1:=H9).

      specialize H8 with (3:=H6) (Lv:=L_0).
      getH. apply H8.
      pose (L5_1 _ _ _ H1).
      getH. apply v1; eauto using nil_cons.
      destruct x5; simpl; eauto using nil_cons.
      apply VListBeginSame with (v::v0); eauto using nil_cons.
      eauto using app_cons_not_nil.
      match goal with
      | h: Df ((x ++ [e]) ++ v :: v0) _ _ |- _ =>
        pose (VConnect) as d;
        specialize d with (1:=h) (v1:=(x ++ [e])) (v2:=v :: v0)
        (Lv1:=endE e)
        (Lv2:=beginE v)
      end.
      getH. apply d; eauto using app_cons_not_nil, nil_cons.
      apply VListEndSame2; resolveEndESelf.
      match goal with
      | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; simpl
        ; tryResolveBegin
      end.
      inversion H.
      rewrite <- H11.
      apply VListEndSame2; resolveEndESelf.

      pose (ForwardSmallStep.Core.CompleteM) as d1.
      specialize d1 with (1:=H11).
      getH. tac_app; 
      eauto using nil_cons, app_cons_not_nil.
      destruct x6; eauto using nil_cons.
      destruct w'; eauto using nil_cons.
      simpl in *; tac_invalid_db.
      repeat (breakAnd + breakEx).

      pose A_VPG_Match as ax1.
      specialize ax1 with (1:=H16).
      repeat (breakAnd + breakEx); subst.
      specialize H20 with (x13).
      rmDirect; subst.
      specialize g with (1:=H19).
      clear H19 H18 ax1.

      getH. apply g.
      pose (L5_1 _ _ _ H11).
      getH. apply v1; eauto using nil_cons.
      destruct x6; simpl; eauto using nil_cons.
      destruct w'; simpl; eauto using nil_cons.
      simpl in *; tac_invalid_db. eauto.

      pose ForwardSmallStep.Df2.L_Df_unique as l.
      rewrite H10 in *.
      rewrite <- app_assoc in *.
      match goal with
      | h: Df ?v _ _, 
        h1: Df ?v _ _ |- _ =>
        destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
        ; eauto
      end.
      simpl in *.
      
      assert (x0 = []
      ∨ (∃ (L1 : var) (a : terminal) (L2 : var) (T' : list CalEdge),
        x0 = PndCalE L1 a L2 :: T')).
      apply H7.
      eauto.
      breakAll; subst;
      discriminate.
    Qed.
    (* end hide *)

    (** [L_invalid_comb_matc_pnd]: this lemmas shows that we cannot
        concatenate a forward small-step parse tree with a backward
        small-step parse tree, if the forward small-step parse tree has
        a stack with its top to be a matching rule, while the backward
        small-step parse tree has a stack with a pending rule on top. *)
    Lemma L_invalid_comb_matc_pnd: ∀ v L' a L'' T'' w', 
      Db v (PndRetE L' a L''::T'') w' 
      -> ∀ x e T' L a L1 b L2 w'', 
          Df (x ++ [e]) (MatCalE L a L1 b L2::T') w'' 
          -> DM.Dm L_0 (w''++w') ((x ++ [e]) ++ v) -> False.
    (* begin hide *)
    Proof.
      intros.
      pose (ForwardSmallStep.Core.CompleteM) as d0.
      specialize d0 with (1:=H1).
      getH. tac_app; 
      eauto using nil_cons, app_cons_not_nil.
      destruct w''; eauto using nil_cons.
      tac_invalid_df.
      clear d0.
      breakEx.
      breakAnd.
      rename H3 into Ha.

      pose (L5_2 _ _ _ H1) as f.
      getH. apply f. destruct w''; try tac_invalid_df; eauto using nil_cons.
      repeat (breakAnd + breakEx).

      pose (BackwardSmallStep.Core.SoundV) as d0.
      destruct v; try tac_invalid_db.

      specialize d0 with (1:=H) (Le:=x1) (Lv:=beginE v).
      getH. apply d0; eauto. 
      match goal with
        | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; simpl
        ; tryResolveBegin
      end.
      inversion H.
      apply VListEndSame with (x ++ [e]); eauto.
      right.
      eauto.

      match goal with
      | h:Df ?v ?T w'' |- _ =>
      pose (ForwardSmallStep.Core.L4_2 v T w'') as bk;
      inversion bk
      ; rmDirect
      end.



      assert (True -> x0 = []
      ∨ (∃ (L1 : var) (a : terminal) (L2 : var) (T' : list CalEdge),
        x0 = PndCalE L1 a L2 :: T')).
      1:{
        intro. eauto.
      }
      
      clear H2.
      breakAll; try discriminate; tac_inj; subst.
      rmDirect.
      breakAll; try discriminate; tac_inj; subst.
      simplList; eauto; subst.

      rewrite H10 in H0.
      pose (ForwardSmallStep.Split.DF_SPLIT) as sp.
      specialize sp with (1:=H0) (v1:=x3 ++ [Calv (MatCalE x8 x7 x9 x10 x11)])
        (v2:=x4)
      ; getH; [apply sp; [repeat rewrite <- app_assoc; 
      repeat rewrite <- app_comm_cons;
      simpl; eauto |
        eauto using app_cons_not_nil] |]
      ; breakAll
      ; clear sp.

      assert ((∃ T, x12=MatCalE x8 x7 x9 x10 x11::T)).
      1:{
        inversion H9; subst; tac_inj; subst;
        inversion a1; subst; eauto.
      }

      assert ((∃ w', x13=w'++[Call x7])).
      1:{
        inversion H9; subst; tac_inj; subst;
        inversion a1; subst; eauto.
        exists []; eauto.
      }
      repeat breakEx; subst.

      pose (L4_5) as g.
      specialize g with (1:=H9).

      specialize H8 with (3:=H6) (Lv:=L_0).
      getH. apply H8.

      pose (L5_1 _ _ _ H1).
      getH. apply v1; eauto using nil_cons.
      destruct x5; simpl; eauto using nil_cons.
      apply VListBeginSame with (v::v0); eauto using nil_cons.
      eauto using app_cons_not_nil.
      match goal with
      | h: Df ((x ++ [e]) ++ v :: v0) _ _ |- _ =>
        pose (VConnect) as d;
        specialize d with (1:=h) (v1:=(x ++ [e])) (v2:=v :: v0)
        (Lv1:=endE e)
        (Lv2:=beginE v)
      end.
      getH. apply d; eauto using app_cons_not_nil, nil_cons.
      apply VListEndSame2; resolveEndESelf.
      match goal with
      | |- VBeginWith (?v::_) (beginE ?v) =>
        destruct v as [[? | ?] | [?] | [? | ?]]
        ; simpl
        ; tryResolveBegin
      end.
      inversion H.
      rewrite <- H11.
      apply VListEndSame2; resolveEndESelf.

      pose (ForwardSmallStep.Core.CompleteM) as d1.
      specialize d1 with (1:=H11).
      getH. tac_app; 
      eauto using nil_cons, app_cons_not_nil.
      destruct x6; eauto using nil_cons.
      destruct w'; eauto using nil_cons.
      simpl in *; tac_invalid_db.
      repeat (breakAnd + breakEx).

      pose A_VPG_Match as ax1.
      specialize ax1 with (1:=H16).
      repeat (breakAnd + breakEx); subst.
      specialize H20 with (x13).
      rmDirect; subst.
      specialize g with (1:=H19).
      clear H19 H18 ax1.

      getH. apply g.
      pose (L5_1 _ _ _ H11).
      getH. apply v1; eauto using nil_cons.
      destruct x6; simpl; eauto using nil_cons.
      destruct w'; simpl; eauto using nil_cons.
      simpl in *; tac_invalid_db. eauto.

      pose ForwardSmallStep.Df2.L_Df_unique as l.
      rewrite H10 in *.
      rewrite <- app_assoc in *.
      match goal with
      | h: Df ?v _ _, 
        h1: Df ?v _ _ |- _ =>
        destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
        ; eauto
      end.
      simpl in *.
      
      assert (x0 = []
      ∨ (∃ (L1 : var) (a : terminal) (L2 : var) (T' : list CalEdge),
        x0 = PndCalE L1 a L2 :: T')).
      apply H7.
      eauto.
      breakAll; subst;
      discriminate.
    Qed.
    (* end hide *)

    (** [L_comb_mat_mat]: this lemmas shows that if we can concatenate a
        forward small-step parse tree with a backward small-step parse
        tree, and their stack top are matching rules, then the matching
        rules are the same. *)
    Lemma L_comb_mat_mat: 
      ∀ v L a L1 b L2 T w', 
      Db v (MatRetE L a L1 b L2::T) w' ->
        ∀ x e L' a' L1' b' L2' T' w'', 
        Df (x ++ [e]) (MatCalE L' a' L1' b' L2'::T') w''
        -> DM.Dm L_0 (w''++w') ((x ++ [e]) ++ v) 
        -> eqvv L' L 
            && eqvv L1' L1 
            && eqvv L2' L2 
            && (a' =? a)%string 
            && (b' =? b)%string = true.
    (* begin hide *)
    Proof.
      intros.
      pose (ForwardSmallStep.Core.CompleteM) as d0.
      specialize d0 with (1:=H1).
      getH. tac_app; 
      eauto using nil_cons, app_cons_not_nil.
      destruct w''; eauto using nil_cons.
      tac_invalid_df.
      clear d0.
      breakEx.
      breakAnd.
      rename H3 into Ha.

      clear H2.

      match goal with
      | h:Df ?v ?T w'' |- _ =>
      pose (ForwardSmallStep.Core.L4_2 v T w'') as bk;
      inversion bk
      ; rmDirect
      end.


      breakAll; try discriminate; tac_inj; subst.
      rmDirect.
      breakAll; try discriminate; tac_inj; subst.
      simplList; eauto; subst.

      rewrite H5 in H0.
      pose (ForwardSmallStep.Split.DF_SPLIT) as sp.
      specialize sp with (1:=H0) (v1:=x2 ++ [Calv (MatCalE x7 x6 x8 x9 x10)])
        (v2:=x3)
      ; getH; [apply sp; [repeat rewrite <- app_assoc; 
      repeat rewrite <- app_comm_cons;
      simpl; eauto |
        eauto using app_cons_not_nil] |]
      ; breakAll
      ; clear sp.

      assert ((∃ T, x11=(MatCalE x7 x6 x8 x9 x10)::T)).
      1:{
        inversion H4; subst; tac_inj; subst;
        inversion a1; subst; eauto.
      }

      assert ((∃ w', x12=w'++[Call x6])).
      1:{
        inversion H4; subst; tac_inj; subst;
        inversion a1; subst; eauto.
        exists []; eauto.
      }
      repeat breakEx; subst.

      pose (L4_5) as g.
      specialize g with (1:=H4).

      rewrite H5 in *.

      match goal with
      | h: Db ?v ?T ?w |- _ =>
        pose (BackwardSmallStep.Core.L4_2 v T w) as aa
      end.

      inversion aa; subst;
      rmDirect;
      breakAll; subst; tac_inj; subst; try discriminate;

      try match goal with
      | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
        inversion h; breakAll; subst; discriminate
      end;
      simplList; subst.

      1:{
        inversion Ha; subst; tac_inj; subst.
        inversion a1; subst.

        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simpl in *.
        simplList; subst.


        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.
      }

      1:{
        match type of Ha with
        | Df (?x ++ ?ee :: ?v') _ (?w1 ++ ?i :: ?w') =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=Ha) (v1:=x ++ [ee])
            (v2:=v')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; 
          repeat rewrite <- app_comm_cons;
          simpl; eauto |
            eauto using app_cons_not_nil] |]
          ; breakAll
          ; clear sp
        end.

        inversion H13; subst; tac_inj; subst; try rmInvalidList;
        try match goal with
        | h: [_] = (?x1 ++ _ :: ?x2) ++ _ |- _ =>
          destruct x1; simpl in *; try discriminate;
          destruct x2; simpl in *; try discriminate;
          inversion h; try discriminate;
          destruct x1; try discriminate
        end.



        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simplList; subst.
        inversion a0; subst.


        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.
      }


      1:{
        match type of Ha with
        | Df (?x ++ ?ee :: ?v') _ (?w1 ++ ?i :: ?w') =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=Ha) (v1:=x ++ [ee])
            (v2:=v')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; 
          repeat rewrite <- app_comm_cons;
          simpl; eauto |
            eauto using app_cons_not_nil] |]
          ; breakAll
          ; clear sp
        end.

        inversion H6; subst; tac_inj; subst; try rmInvalidList;
        try match goal with
        | h: [_] = (?x1 ++ _ :: ?x2) ++ _ |- _ =>
          destruct x1; simpl in *; try discriminate;
          destruct x2; simpl in *; try discriminate;
          inversion h; try discriminate;
          destruct x1; try discriminate
        end.



        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simplList; subst.
        inversion a0; subst.


        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.
      }

      1:{
        specialize H3 with (3:=H19) (Lv:=L_0).
        match type of H3 with
        |  _ -> _ -> ?g =>
        assert g; [apply H3|]
        end.
        pose (L5_1 _ _ _ H1) as v1.
        getH. apply v1; eauto using nil_cons.
        destruct x4; simpl; eauto using nil_cons.
        match goal with
        | h: VBeginWith (?v++?v') _ |- VBeginWith ?v _ =>
          apply VListBeginSame with (v'); eauto using nil_cons
        end.
        eauto using app_cons_not_nil.

        rewrite <- H5 in *.
        match goal with
        | h: Df ((x ++ [e]) ++ ?v ++ ?v0) _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=h) (v1:=(x ++ [e])) (v2:=v ++ v0)
          (Lv1:=endE e)
          (Lv2:=x20)
        end.
        getH. apply d; eauto using app_cons_not_nil, nil_cons.
        apply VListEndSame2; resolveEndESelf.
        apply VListBeginSame2.
        inversion H18; breakAll; subst; tryResolveBegin.
        rewrite <- H6.
        apply VListEndSame2; resolveEndESelf.

        
        pose (ForwardSmallStep.Core.CompleteM) as d1.
        specialize d1 with (1:=H6).
        getH. tac_app; 
        eauto using nil_cons, app_cons_not_nil.
        repeat (breakAnd + breakEx); subst.

        match goal with
        | h: Df ?v _ _ |- _ =>
          destruct (VHasHead _ _ _ h)
        end.

        match type of Ha with
        | Df ((?x ++ [?e] ++ ?y) ++ ?v ++ ?v0) _ _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=(x ++ [e])) (v2:= y ++ v ++ v0)
          (Lv1:=endE e)
          (Lv2:=x19)
        end.
        getH. apply d; eauto using app_cons_not_nil, nil_cons.
        repeat rewrite <- app_assoc; eauto.
        repeat rewrite app_assoc; eauto.
        eauto using app_cons_not_nil, nil_cons.

        apply VListEndSame2; resolveEndESelf.
        repeat rewrite app_assoc; eauto.
        apply VListBeginSame2; eauto.
        match goal with
        | h: _ = _ |- _ =>
          simpl in h; subst
        end.
        
    
        pose A_VPG_Match as ax1.
        match goal with
        | h:in_rules (_, Alt_Match _ _ x19 _) _ |- _ =>
        specialize ax1 with (1:=h)
        end.
        breakAnd; breakEx; subst.
        specialize H16 with (x8).
        rmDirect; subst.

        match goal with
        | h:Df _ [] _ |- _ =>
        specialize g with (1:=h)
        end.
        match type of g with
        | _ -> ?h =>
        assert h; [apply g; eauto |]
        end.
        clear H19 H18 ax1.

        inversion Ha; subst; tac_inj; subst; try rmInvalidList.
        inversion a0. inversion a1. subst.

        simpl in *.
        repeat (rewrite <- app_assoc in *; rewrite app_comm_cons in *; simpl in *).
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simplList; subst.

        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.
      }

      1:{
        specialize H3 with (3:=H19) (Lv:=L_0).
        match type of H3 with
        |  _ -> _ -> ?g =>
        assert g; [apply H3|]
        end.
        pose (L5_1 _ _ _ H1) as v1.
        getH. apply v1; eauto using nil_cons.
        destruct x4; simpl; eauto using nil_cons.
        match goal with
        | h: VBeginWith (?v++?v') _ |- VBeginWith ?v _ =>
          apply VListBeginSame with (v'); eauto using nil_cons
        end.
        eauto using app_cons_not_nil.

        rewrite <- H5 in *.
        match goal with
        | h: Df ((x ++ [e]) ++ ?v ++ ?v0) _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=h) (v1:=(x ++ [e])) (v2:=v ++ v0)
          (Lv1:=endE e)
          (Lv2:=x20)
        end.
        getH. apply d; eauto using app_cons_not_nil, nil_cons.
        apply VListEndSame2; resolveEndESelf.
        apply VListBeginSame2.
        inversion H18; breakAll; subst; tryResolveBegin.
        rewrite <- H13.
        apply VListEndSame2; resolveEndESelf.


        assert (x5 ++ x23 != []) as hnot.
        1:{

          destruct x5; destruct x23; subst.
          simpl in *; inversion H13; subst; rewrite <- H14 in *.
          destruct x21. inversion H18; breakAll; discriminate.
          destruct x3; simpl in *; discriminate.
          all: eauto using app_cons_not_nil, nil_cons.
        }
        
        pose (ForwardSmallStep.Core.CompleteM) as d1.
        specialize d1 with (1:=H13).
        getH. tac_app; 
        eauto using nil_cons, app_cons_not_nil.
        repeat (breakAnd + breakEx); subst; eauto.

        match goal with
        | h: Df ?v _ _ |- _ =>
          destruct (VHasHead _ _ _ h)
        end.

        match type of Ha with
        | Df ((?x ++ [?e] ++ ?y) ++ ?v ++ ?v0) _ _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=(x ++ [e])) (v2:= y ++ v ++ v0)
          (Lv1:=endE e)
          (Lv2:=x22)
        end.
        getH. apply d; eauto using app_cons_not_nil, nil_cons.
        repeat rewrite <- app_assoc; eauto.
        repeat rewrite app_assoc; eauto.
        eauto using app_cons_not_nil, nil_cons.

        apply VListEndSame2; resolveEndESelf.
        repeat rewrite app_assoc; eauto.
        apply VListBeginSame2; eauto.
        apply VListBeginSame2; eauto.
        match goal with
        | h: _ = _ |- _ =>
          simpl in h
          ; rewrite h in *
        end.
        
    
        pose A_VPG_Match as ax1.
        match goal with
        | h:in_rules (_, Alt_Match _ _ x22 _) _ |- _ =>
        specialize ax1 with (1:=h)
        end.
        breakAnd; breakEx; subst.
        specialize H17 with (x24).
        rmDirect; subst.
        rmDirect; subst.

        match goal with
        | h:Df _ [] _ |- _ =>
        specialize g with (1:=h)
        end.
        match type of g with
        | _ -> ?h =>
        assert h; [apply g; eauto |]
        end.
        clear H19 H18 ax1.

        do 2 rewrite app_assoc in Ha.
        match type of Ha with
        | Df (?x ++ ?v') _ _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=Ha) (v1:=x)
            (v2:=v')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; 
          repeat rewrite <- app_comm_cons;
          simpl; eauto |
            eauto using app_cons_not_nil] |]
          ; repeat breakEx
          ; clear sp
        end.

        inversion H18; subst; tac_inj; subst; try rmInvalidList;
        inversion a0;  subst.

        simpl in *.
        repeat (rewrite <- app_assoc in *; rewrite app_comm_cons in *; simpl in *).
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simplList; subst.

        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.

        simpl in *.
        repeat (rewrite <- app_assoc in *; rewrite app_comm_cons in *; simpl in *).
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simplList; subst.

        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.
      }

      1:{
        specialize H3 with (3:=H19) (Lv:=L_0).
        match type of H3 with
        |  _ -> _ -> ?g =>
        assert g; [apply H3|]
        end.
        pose (L5_1 _ _ _ H1) as v1.
        getH. apply v1; eauto using nil_cons.
        destruct x4; simpl; eauto using nil_cons.
        match goal with
        | h: VBeginWith (?v++?v') _ |- VBeginWith ?v _ =>
          apply VListBeginSame with (v'); eauto using nil_cons
        end.
        eauto using app_cons_not_nil.

        rewrite <- H5 in *.
        match goal with
        | h: Df ((x ++ [e]) ++ ?v ++ ?v0) _ _ |- _ =>
          pose (VConnect) as d;
          specialize d with (1:=h) (v1:=(x ++ [e])) (v2:=v ++ v0)
          (Lv1:=endE e)
          (Lv2:=x20)
        end.
        getH. apply d; eauto using app_cons_not_nil, nil_cons.
        apply VListEndSame2; resolveEndESelf.
        apply VListBeginSame2.
        inversion H18; breakAll; subst; tryResolveBegin.
        rewrite <- H6.
        apply VListEndSame2; resolveEndESelf.


        assert (x5 ++ x23 != []) as hnot.
        1:{
          destruct x5; destruct x23; subst.
          simpl in *; inversion H6; subst; rewrite <- H13 in *.
          destruct x21. inversion H18; breakAll; discriminate.
          destruct x3; simpl in *; discriminate.
          all: eauto using app_cons_not_nil, nil_cons.
        }
        
        pose (ForwardSmallStep.Core.CompleteM) as d1.
        specialize d1 with (1:=H6).
        getH. tac_app; 
        eauto using nil_cons, app_cons_not_nil.
        repeat (breakAnd + breakEx); subst; eauto.

        match goal with
        | h: Df ?v _ _ |- _ =>
          destruct (VHasHead _ _ _ h)
        end.

        match type of Ha with
        | Df ((?x ++ [?e] ++ ?y) ++ ?v ++ ?v0) _ _ =>
          pose (VConnect) as d;
          specialize d with (1:=Ha) (v1:=(x ++ [e])) (v2:= y ++ v ++ v0)
          (Lv1:=endE e)
          (Lv2:=x18)
        end.
        getH. apply d; eauto using app_cons_not_nil, nil_cons.
        repeat rewrite <- app_assoc; eauto.
        destruct x3; eauto using app_cons_not_nil, nil_cons.
        repeat rewrite app_assoc; eauto.
        eauto using app_cons_not_nil, nil_cons.

        apply VListEndSame2; resolveEndESelf.
        repeat rewrite app_assoc; eauto.
        apply VListBeginSame2; eauto.
        apply VListBeginSame2; eauto.
        match goal with
        | h: _ = _ |- _ =>
          simpl in h
          ; rewrite h in *
        end.

    
        pose A_VPG_Match as ax1.
        match goal with
        | h:in_rules (_, Alt_Match _ _ x18 _) _ |- _ =>
        specialize ax1 with (1:=h)
        end.
        breakAnd; breakEx; subst.
        specialize H16 with (x24).
        rmDirect; subst.
        rmDirect; subst.

        match goal with
        | h:Df _ [] _ |- _ =>
        specialize g with (1:=h)
        end.
        match type of g with
        | _ -> ?h =>
        assert h; [apply g; eauto |]
        end.
        clear H19 H18 ax1.

        do 2 rewrite app_assoc in Ha.
        match type of Ha with
        | Df (?x ++ ?v') _ _ =>
          pose (ForwardSmallStep.Split.DF_SPLIT) as sp;
          specialize sp with (1:=Ha) (v1:=x)
            (v2:=v')
          ; getH; [apply sp; [repeat rewrite <- app_assoc; 
          repeat rewrite <- app_comm_cons;
          simpl; eauto |
            eauto using app_cons_not_nil] |]
          ; repeat breakEx
          ; clear sp
        end.

        inversion H18; subst; tac_inj; subst; try rmInvalidList;
        inversion a0;  subst.

        simpl in *.
        repeat (rewrite <- app_assoc in *; rewrite app_comm_cons in *; simpl in *).
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simplList; subst.

        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.

        simpl in *.
        repeat (rewrite <- app_assoc in *; rewrite app_comm_cons in *; simpl in *).
        match goal with
        | h: Df ?v _ _, 
          h1: Df ?v _ _ |- _ =>
          destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
          ; eauto
        end.
        simplList; subst.

        repeat (apply andb_true_iff; getAnd).
        all: try (apply vvot.eqb_eq + apply String.eqb_eq); eauto.
      }
    Qed.

    Lemma L_extract_sub : ∀ m M V w1 w2, 
      Extract (m::M) V w1 w2 ->
      ∃ _T, Forest (m::M) _T w1.
    Proof.
      intros.
      induction H.
      inversion H; subst; tac_inj; subst; eauto.
      breakAll.
      inversion IHExtract; subst; tac_inj; subst; eauto.
    Qed.
    (* end hide *)

    (** [L_extract]: this is the main theorem of the correctness as well
        as the invariant of the extraction function. The theorem shows
        that during the extraction, for each extracted parse tree [v],
        there exists a counterpart parse tree [v'], such that [v'++v] is
        a parse tree  in the big-step derivation of the input string
        [w]. *)
    Theorem L_extract : ∀ M V w1 w2, Extract M V w1 w2 -> 
      ∀ v I, In (v, I) V <->
        (
          Db v I w2 /\
          (
            (w1=[] /\ DM.Dm L_0 w2 v) \/
            (∃ v1 I1, VBeginWith v1 L_0 /\ Df v1 I1 w1 /\ DM.Dm L_0 (w1++w2) (v1++v))
          )
        ).
    (* begin hide *)
    Proof.
      intros.
      generalize dependent v.
      generalize dependent I.
      induction H.

      1:{
        split; intros.
        1:{
          match goal with
          | h: Forest _ _ _ |- _ =>
            pose (PForest1 _ _ _ _ h) as p
          end.

          pose (L_f_init) as d.
          specialize d with (1:=H) (v:=v) (I:=I).
          destruct d as [? _].
          rmDirect.
          breakAnd.
          getAnd; auto.

          pose L_forest as d.
          specialize d with (1:=H).
          breakAll; subst.

          
          1,2: match goal with
          | h: inRM ?e ?m |- _ =>
            specialize d with (2:=h)
          end;
          breakAll.

          1,2: match goal with
          | h: Db [?e] _ _ |- _ =>
            assert (exists E, VEndWith [e] E /\ In (E, Alt_Epsilon) P) by 
            (inversion H1; subst;
            try (match goal with
            | h: in_rules (?L, Alt_Epsilon) _ |- _ =>
              exists L
            end;
            getAnd; [try_resolve_end | eauto]);
            tac_invalid_db)
          end;
          breakAll.

          1:{
            getH. apply d. eauto using app_cons_not_nil.
            breakAll.
            rmDirect; subst.

            destruct w.
            1:{
              left.
              split; auto.

              assert (x1 = []) by
              match goal with
              | h: Df _ _ _ |- _ =>
                inversion h 
                ; subst
                ; tac_inj
                ; subst
                ; auto
                ; tac_df
              end;
              subst.
              
              match goal with
              | h: Df _ _ _, h2: In (?x, Alt_Epsilon) _ |- _ =>
                simpl in h
                ; apply (ForwardSmallStep.Core.SoundV _ _ _ L_0 x h)
                ; eauto
              end.
            }

            right.
            assert (exists I1, Df x1 I1 (s::w)).
            1:{
                match goal with
                | h: Df _ _ _ |- _ =>
                inversion h 
                ; tac_inj
                ; subst
                ; eauto
                end.
            }
            breakEx.
            match goal with
            | h:Df ?v ?T (_::_) |- _ => exists v, T
            end.
            split; auto.
            extractHead; eauto.
            split; auto.
            match goal with
            | h: Df (_++_) _ _, h2: VEndWith [_] ?x |- _ =>
              apply (ForwardSmallStep.Core.SoundV _ _ _ L_0 x h)
              ; auto
            end.
            extractEnds; BackwardSmallStep.Core.tryResolveEnd.
          }

          getH. apply d. eauto using app_cons_not_nil.
          breakAll.
          specialize H5 with (i:=(PndCalE x0 x1 x2)).
          rmDirect; subst.
          breakAll; subst.
          destruct w.
          1:{
            left. split; eauto.
            assert (x4 = []).
            1:{
                match goal with
                | h: Df _ _ _ |- _ =>
                inversion h 
                ; subst
                ; tac_inj
                ; subst
                ; auto
                ; tac_df
                end.
            }
            subst.
            match goal with
            | h: Df (_++[?x]) _ _, h2: VEndWith [?x] ?nx |- _ =>
              simpl in h
              ; apply (ForwardSmallStep.Core.SoundV _ _ _ L_0 nx h)
              ; auto
            end.

            match goal with
            | h:?x = None -> _ = [] |- _ =>
              destruct x
            end;
            try rmDirect; eauto.
            right.
            match goal with
            | h:Df [_] _ _ |- _ =>
              inversion h; subst; tac_inj; subst; try tac_invalid_df; eauto
            end.
          }
          right.
          assert (exists I2, Df x4 I2 (s::w)).
          1:{
            match goal with
            | h: Df _ _ _ |- _ =>
              inversion h 
              ; subst
              ; eauto
              ; try rmDirect
              ; tac_inj
              ; subst
              ; eauto
            end.
          }
          breakEx.

          match goal with
          | h:Df ?v ?T (_::_) |- _ => exists v, T
          end.
          split; eauto.
          extractHead; eauto.
          split; eauto.
          match goal with
          | h: Df (_++[?x]) _ _, h2: VEndWith [?x] ?nx |- _ =>
            simpl in h
            ; apply (ForwardSmallStep.Core.SoundV _ _ _ L_0 nx h)
            ; auto
          end.
          extractEnds; BackwardSmallStep.Core.tryResolveEnd.

          right.
          eauto.
        }


        breakAnd.
        pose L_f_init as d.
        specialize d with (1:=H).

        apply (d).
        split; auto.

        assert (exists e, v=[e]).
        1:{
          match goal with
          | h:Db v _ [_] |- _ =>
            inversion h; subst; eauto; try tac_invalid_db
          end.
        }
        breakEx.
        eexists. split; eauto.

        pose PForest1 as a.
        specialize a with (1:=H).

        breakAll; subst.
        1:{
          match goal with
          | h: DM.Dm _ _ _ |- _ =>
            pose (ForwardSmallStep.Core.CompleteM _ _ _ h) as e
          end.
          breakInfer. tac_app. eauto using nil_cons. clear e. 
          breakEx.
          breakAnd.
          breakAnd.

          assert (exists Le, VEndWith [x] Le) by
            match goal with
            | h:Df [x] _ _ |- _ =>
              apply (VHasEnd) with (1:=h)
            end.
          breakEx.

          match goal with
          | h:Df ?v ?T ?w |- _ =>
            pose (ForwardSmallStep.DFX.DF_dfx _ _ _ h)
          ; do 4 breakEx
          end.

          match goal with
          | h: Dfx [?x] ?I [?i] ?v1 ?v2 ?w1 ?w2 |- _ =>
            pose (a [] x I x1 v1 v2 w1 w2) as o
          end.
          getH. apply o; eauto. simpl. 
          1:{
            simpl.
            match goal with
            | h:DM.Dm L_0 _ [x] |- _ =>
              inversion h; subst; eauto
            end;
            try try_resolve_begin.
            try rmInvalidList.
          }
          clear a o.

          breakOr.
          1:{
            subst.
            left.
            breakAll; subst; eauto; discriminate.
          }
          1:{
            right.
            breakAll; subst; try discriminate.
            simplList; subst; eauto.
          }
        }

        match goal with
        | h: DM.Dm _ _ _ |- _ =>
          pose (ForwardSmallStep.Core.CompleteM _ _ _ h)
        end.
        breakInfer. tac_app. eauto using app_cons_not_nil. clear e. 
        
        breakEx. breakAnd. breakAnd.

        assert (exists Le, VEndWith [x] Le).
        1:{
          destruct x;
          match goal with
          | |- ∃ _, VEndWith [_ ?v] _ =>
            destruct v
          end.
          all: eexists; try_resolve_end.
        }
        breakEx.

        match goal with
        | h:Df ?v ?T ?w |- _ =>
          pose (ForwardSmallStep.DFX.DF_dfx _ _ _ h)
          ; do 4 breakEx
        end.

        match goal with
        | h: Dfx (?x0++[?x]) ?I (?w++[?i]) ?v1 ?v2 ?w1 ?w2 |- _ =>
          pose (a x0 x I x3 v1 v2 w1 w2) as o
        end.
        getH. apply o; eauto.

        tryResolveBegin1.
        clear o.

        breakOr; subst.
        1:{
          left.
          breakAll; subst; eauto; discriminate.
        }

        1:{
          right.
          breakAll; subst; try discriminate.
          simplList; subst; eauto.
        }
      }

      1:{
        pose (L_f_b) as d.

        pose L_extract_sub as H_extract_sub.
        specialize H_extract_sub with (1:=H).
        destruct H_extract_sub as [_T H_extract_sub].
        pose (L_syncMi) as H_syncMi.
        specialize H_syncMi with (1:=H_extract_sub).

        split; intros.
        1:{
          assert (Db v I (i :: w2)).
          1:{
            apply (d m V); eauto.
            intros. 
            apply IHExtract.
            auto.
            exists M, _T, (w1++[i]).
            eauto using app_cons_not_nil.
          }
          split; auto.

          pose (pg2 _ _ _ _ H0).
          getH. apply e.
          exists M, _T, (w1++[i]).
          eauto using app_cons_not_nil.
          clear e. rename H2 into e.

          breakAll; subst;

          match goal with
          | h:Db (?x1::?x) ?x2 _ |- _ =>
            rename x1 into e;
            rename x into v';
            rename x2 into T'
          end;

          match goal with
          | h:inRM (_,?e1) _ |- _ =>
            pose pf1 as pf1;
            specialize pf1 with (1:=H) (e:=e1);
            destruct pf1 as [pf1 pf2]
            ; eauto using app_cons_not_nil
          end.
          
          all: match goal with
          | h:inRM (None, _) _ |- _ =>
            destruct (pf1 h) as [v1e ?]
          | h: inRM (Some ?r1, _) _ |- _ =>
            destruct (pf2 r1 h) as [v1e [T1e ?]]
          end;
          try clear pf1; try clear pf2.

          (* NOTE
            I'=[], r=None  
            I'=[], r=PndCal
            I'=PndRet, r=PndCal
            I'=MatRet, r=MatCal
          *)
          
          1:{
            match goal with
            | h: In (?v,?I)  V |- _ =>
              destruct (IHExtract I v) as [IH1 _]
              ; rmDirect
            end.
            repeat (breakEx + breakAnd)
            ; subst
            ; tac_inj.
    
            breakOr. breakAnd; tac_inj. 
            repeat (breakEx + breakAnd).
    
            rename x into v1.
            rename x0 into T1.




            match goal with
            | h: Df (v1e++[e]) _ _,
              h1: Df v1 _ _ |- _ =>
              pose (ForwardSmallStep.DFX.DF_dfx _ _ _ h)
              ; pose (ForwardSmallStep.DFX.DF_dfx _ _ _ h1)
              ; repeat breakEx
            end.

            match goal with
            | h: Dfx _ _ _ _ _ _ _,
              h1: Dfx _ _ _ _ _ _ _ |- _ =>
              pose (ForwardSmallStep.DFX.DFX_df_sub _ _ _ _ _ _ _ h)
              ; pose (ForwardSmallStep.DFX.DFX_df_sub _ _ _ _ _ _ _ h1)
            end.

            do 2 breakOr;
            repeat (breakAnd + breakEx); subst; try discriminate.

            2: match goal with
                | h: Df _ (_::_) ?w, 
                  h1: Df _ [] _ |- _ =>
                  pose (ForwardSmallStep.Df2.L_Df_uniqueT _ _ _ _ _ h h1) as _h
                  ; simpl in _h
                  ; discriminate
                end.
            


            match goal with
            | h: DM.Dm ?L ?w ?v |- _ =>
              pose (ForwardSmallStep.Core.CompleteM _ _ _ h)
              ; pose (L5_2 L w v h) as HDmEnd
            end.
            do 2 match goal with
              | h: _ -> ?g |- _ =>
              assert g by
              (apply h;
                rewrite  <- app_assoc;
                eauto using app_cons_not_nil)
              ; clear h
              end.

            breakEx.
            breakAnd.
            breakAnd.
            breakEx.
            breakAnd.

            match goal with
            | h: Df (v1 ++ v') ?T ?w |- _ =>
              assert (Df ((v1e++[e])++v') T w)
            end.
            match goal with
            | h: Df v1 _ _ |- _ =>
              destruct (VHasEnd _ _ _ h) as [Lv1 ?]
            end.
            apply (ForwardSmallStep.Df2.L_DF_Local2) with (v:=v1) (E:=Lv1); eauto.

            1:{
              assert (∃ L, VBeginWith v' L) as Hv' by
                match goal with
                | h:Db v' [] _ |- _ =>
                  inversion h;
                  exists L; 
                  tryResolveBegin
                end.
              
              destruct Hv' as [L Hv'].

              match goal with
              | h: Df (?v1 ++ ?v') _ _ |- _ =>
                pose (VConnect _ _ _ h v1 v' Lv1 L) as hconnect
              end.

              
              assert (Lv1=L) by (
                destruct v1; try tac_invalid_df;
                destruct v'; try tac_invalid_db;
                apply hconnect; eauto using app_cons_not_nil, nil_cons;
                repeat rewrite <- app_assoc; eauto;
                tryResolveBegin);
              subst; eauto.


              assert (VEndWith [e] L).
              match goal with
              | h:Db (e::v') _ _ |- _ =>
                inversion h; subst
                ; try tac_invalid_db
              end.
              
              all: try match goal with
              | h:Db ?v' _ _, h1: Db ?v' _ _ |- _ =>
                pose (L_Db_uniqueT _ _ _ _ _ h h1)
                ; try discriminate
                ; subst
              end.

              all: try (mergeBegins; try_resolve_end).

              apply VListEndSame2; eauto.
            }

            match goal with
            | h: Df ?v ?T ?w |- _ =>
            assert (DM.Dm L_0 w v)
            end.
            match goal with
            | h: Df ?v ?T ?w,
              h2: in_rules (?L,_) _ |- _ =>
              apply (ForwardSmallStep.Core.SoundV v T w L_0 L)
              ; eauto
            end.
            1:{
              inversion H3; breakAll; subst;
              match goal with
              | h: v1e ++ [_] = _ |- _ =>
                rewrite h
              end;
              rewrite <- app_assoc;
              tryResolveBegin.
            }


            1:{
              destruct v'; try tac_invalid_db.

              match goal with
              | h:VEndWith (?v++?e::?v') ?L |- VEndWith (?v1++?e::?v') ?L =>
              assert ((e::v') != []) as _HnotNil by eauto using nil_cons
              ; destruct (exists_last _HnotNil) as [? _s]
              ; destruct _s as [? _h]
              ; rewrite _h in *
              ; clear _h _HnotNil
              ; repeat rewrite app_assoc in h
              ; repeat rewrite app_assoc
              ; inversion h; breakAll; subst
              ; tac_inj
              ; subst
              end;
              BackwardSmallStep.Core.tryResolveEnd.
            }

            destruct w1.
            left.
            assert (v1e=[]).
            1:{
              simpl in *;
              inversion e0; subst; tac_inj; subst
              ; eauto;
              match goal with
              | h: Dfx _ _ [] _ _ _ _ |- _ =>
                pose (DFX_df _ _ _ _ _ _ _ h)
                ; tac_df
              end.
            }
            subst.
            split; eauto.

            right.
            match goal with
            | h: DM.Dm _ _ _ |- _ =>
              repeat rewrite <- app_assoc in h
              ; simpl in h
            end. 
            exists v1e.
            match goal with
            | h: Df (v1e++_) _ _ |- _ =>
              inversion h; eauto; try discriminate
              ; tac_inj; subst; eauto;
              eexists
            end. 
            all: split; eauto.
            all: destruct v1e; try tac_invalid_df.
            all: match goal with
            | h: VBeginWith ((_ :: _) ++ _) L_0 |- _ =>
              simpl in h;
              inversion h; breakAll; subst;
              simplList;
              tryResolveBegin
            end.
          }

          1:{
            match goal with
            | h: In (?v,?I)  V |- _ =>
              destruct (IHExtract I v) as [IH1 _]
              ; rmDirect
            end.
            repeat (breakEx + breakAnd)
            ; subst
            ; tac_inj.

            breakOr. breakAnd; tac_inj. 
            repeat (breakEx + breakAnd).

            rename x into v1.
            rename x0 into T1.


            match goal with
            | h: DM.Dm ?L ?w ?v |- _ =>
              pose (ForwardSmallStep.Core.CompleteM _ _ _ h)
              ; pose (L5_2 L w v h) as HDmEnd
            end.           
            do 2 match goal with
            | h: _ -> ?g |- _ =>
            assert g by
            (apply h;
              rewrite  <- app_assoc;
              eauto using app_cons_not_nil)
            ; clear h
            end.

            breakEx.
            breakAnd.
            breakAnd.
            breakEx.
            breakAnd.


            match goal with
            | h: Db ?v ?T ?w |- _ =>
              pose (BackwardSmallStep.Core.L4_2 v T w) as h0
              ; inversion h0
            end.
            rmDirect.
            breakOr.
            2:{
              breakOr.
              2:{
                breakAll; subst; tac_inj; try discriminate.
              }

              repeat (breakAnd + breakEx).
    
              1:{
                match goal with
                | h: Df (v1e++?x) ?T ?w |- _ =>
                  pose (ForwardSmallStep.Core.L4_2 (v1e++x) T w) as b
                  ; inversion b; subst
                end.
    
                match goal with
                | H28: Df _ _ _ -> _,
                  H6: Df (v1e++[_]) _ _,
                  H16: _ = [] ∨ _ |- _ =>
                  pose (H28 H6);
                  clear H16;
                  breakAll; subst; try discriminate; tac_inj; eauto;
                  rmDirect;
                  breakAll; subst; try discriminate; tac_inj; eauto;
                  clear H28
                end.
    
                match goal with
                | H29: ∀ _ _ _ _ , _ -> _,
                  H27: DM.Dm _ _ _ |- _ =>
                  specialize H29 with (Lv:=L_0) (3:=H27)
                  ; getH; [apply H29; eauto|]
                end.
    
                1:{
                  inversion H1; subst
                  ; try tac_invalid_db;
                  try match goal with
                  | h:Db _ [] (Ret _::_) |- _ =>
                    inversion h
                  end;
    
                  mergeBegins;
                  BackwardSmallStep.Core.tryResolveEnd.
                }
                breakAnd.
                
                destruct w1.
    
                simpl in *.
                match goal with
                | h:[_] = ?x1++ _ :: ?x2 |- _ =>
                  assert (x1=[] /\ x2=[]) by
                  (destruct x1; 
                  destruct x2; eauto;
                  simpl in *;
                  repeat simplList
                  ; destruct x1; discriminate)
                end.
                breakAnd; subst; simpl in *.
                left; getAnd; eauto.
                repeat rmDirect; subst;
                simpl in *.
                match goal with
                | h:[_]=[_] |- _ =>
                  inversion h; clear h; subst
                end.
                assert (v1e=[]).
                1:{
                  match goal with
                  | h:Df (v1e ++ [e]) _ _ |- _ =>
                    inversion h; subst; eauto
                    ; tac_inj; eauto
                    ; subst; tac_invalid_df
                  end.
                }
                subst; simpl in *.
                eauto.
    
    
                right.
    
                exists v1e.

                match goal with
                | H6: Df (v1e ++ [_]) _ _ |- _ =>
                  inversion H6; subst; eauto; tac_inj; subst
                end;
                match goal with
                | h:Df v1e ?x _ |- _ =>
                  exists x
                end;
                getAnd; eauto;
                extractHead; eauto;
                getAnd; eauto;
                repeat rewrite <- app_assoc in *
                ; eauto.
              }
            }

            repeat (breakAnd + breakEx).

            1:{
              match goal with
              | h: Df (v1e++?x) ?T ?w |- _ =>
                pose (ForwardSmallStep.Core.L4_2 (v1e++x) T w) as b
                ; inversion b; subst
              end.

              match goal with
              | H28: Df _ _ _ -> _,
                H6: Df (v1e++[_]) _ _,
                H16: _ = [] ∨ _ |- _ =>
                pose (H28 H6);
                clear H16;
                breakAll; subst; try discriminate; tac_inj; eauto;
                rmDirect;
                breakAll; subst; try discriminate; tac_inj; eauto;
                clear H28
              end.

              match goal with
              | H29: ∀ _ _ _ _ , _ -> _,
                H27: DM.Dm _ _ _ |- _ =>
                specialize H29 with (Lv:=L_0) (3:=H27)
                ; getH; [apply H29; eauto|]
              end.

              1:{
                inversion H1; subst
                ; try tac_invalid_db;
                try match goal with
                | h:Db _ [] (Ret _::_) |- _ =>
                  inversion h
                end;

                mergeBegins;
                BackwardSmallStep.Core.tryResolveEnd.
              }
              breakAnd.
              
              destruct w1.

              simpl in *.
              match goal with
              | h:[_] = ?x1++ _ :: ?x2 |- _ =>
                assert (x1=[] /\ x2=[]) by
                (destruct x1; 
                destruct x2; eauto;
                simpl in *;
                repeat simplList
                ; destruct x1; discriminate)
              end.
              breakAnd; subst; simpl in *.
              left; getAnd; eauto.
              repeat rmDirect; subst;
              simpl in *.
              match goal with
              | h:[_]=[_] |- _ =>
                inversion h; clear h; subst
              end.
              assert (v1e=[]).
              1:{
                match goal with
                | h:Df (v1e ++ [e]) _ _ |- _ =>
                  inversion h; subst; eauto
                  ; tac_inj; eauto
                  ; subst; tac_invalid_df
                end.
              }
              subst; simpl in *.
              eauto.


              right.

              exists v1e.

              match goal with
              | H6: Df (v1e ++ [_]) _ _ |- _ =>
                inversion H6; subst; eauto; tac_inj; subst
              end;
              match goal with
              | h:Df v1e ?x _ |- _ =>
                exists x
              end;
              getAnd; eauto;
              extractHead; eauto;
              getAnd; eauto;
              repeat rewrite <- app_assoc in *
              ; eauto.
            }
          }



          1:{
            match goal with
            | h: In (?v,?I)  V |- _ =>
              destruct (IHExtract I v) as [IH1 _]
              ; rmDirect
            end.
            repeat (breakEx + breakAnd)
            ; subst
            ; tac_inj.

            breakOr. breakAnd; tac_inj. 
            repeat (breakEx + breakAnd).

            rename x into v1.
            rename x0 into T1.

            assert (T1=[]).
            1:{
              pose (ForwardSmallStep.Df2.L_Df_uniqueT) as a.
              specialize a with (1:=H7) (2:=H9).
              destruct T1; eauto.
              simpl in a; discriminate.
            }
            subst.

            match goal with
            | h: DM.Dm ?L ?w ?v |- _ =>
              pose (ForwardSmallStep.Core.CompleteM _ _ _ h)
              ; pose (L5_2 L w v h) as HDmEnd
            end.           
            do 2 match goal with
            | h: _ -> ?g |- _ =>
            assert g by
            (apply h;
              rewrite  <- app_assoc;
              eauto using app_cons_not_nil)
            ; clear h
            end.

            breakEx.
            breakAnd.
            breakAnd.
            breakEx.
            breakAnd.


            match goal with
            | h: Db ?v ?T ?w |- _ =>
              pose (BackwardSmallStep.Core.L4_2 v T w) as h0
              ; inversion h0
              ; subst
            end.
            rmDirect.
            breakOr.
            2:{
              breakOr.
              2:{
                breakAll; subst; tac_inj; try discriminate.
              }

              repeat (breakAnd + breakEx).
    
              1:{
                match goal with
                | h: Df (v1e++?x) ?T ?w |- _ =>
                  pose (ForwardSmallStep.Core.L4_2 (v1e++x) T w) as b
                  ; inversion b; subst
                end.
                rmDirect.
                breakAnd.
                rmDirect.
                rmDirect.
                repeat (breakEx + breakAnd).

                assert (x1=x7).
                1:{

                  inversion H1; subst; try tac_invalid_db.
                  all: try match goal with
                    | h:Db _ _ (Ret _::_) |- _ =>
                      inversion h; subst; eauto
                      ; mergeBegin; eauto
                  end.

                  all: match goal with
                    | h:VEndWith (_++[?e]) ?L |- _ =>
                      assert (endE e = L)
                      ; simpl
                      ; inversion h
                      ; subst
                      ; breakAll
                      ; tac_inj
                      ; match goal with
                        | h: _ = _ |- _ =>
                        inversion h; subst
                        end
                      ; eauto
                  end.

                  all: simpl in *.
                  all: try match goal with
                    | h: VBeginWith (?e :: _) ?L |- _ =>
                      assert (beginE e = L)
                      ; simpl
                      ; inversion h
                      ; subst
                      ; breakAll
                      ; tac_inj
                      ; match goal with
                        | h: _ = _ |- _ =>
                        inversion h; subst
                        end
                      ; eauto
                    end.

                  all: repeat match goal with
                    | h: ?v, h1:?v |- _ =>
                      clear h1
                    end.
                  all: mergeBegins; eauto.
                }
                subst.

                specialize H19 with (1:=H15).
                mergeBegins.
                
                destruct w1.
    
                simpl in *.

                assert (v1e=[]).
                1:{
                  match goal with
                  | h:Df (v1e ++ [e]) _ _ |- _ =>
                    inversion h; subst; eauto
                    ; tac_inj; eauto
                    ; subst; tac_invalid_df
                  end.
                }
                subst; simpl in *.
                eauto.
    
    
                right.
    
                exists v1e.
    
                match goal with
                | H6: Df (v1e ++ [_]) _ _ |- _ =>
                  inversion H6; subst; eauto; tac_inj; subst
                end;
                match goal with
                | h:Df v1e ?x _ |- _ =>
                  exists x
                end;
                getAnd; eauto;
                extractHead; eauto;
                getAnd; eauto;
                repeat rewrite <- app_assoc in *
                ; eauto.
              }
            }

            repeat (breakAnd + breakEx).

            1:{
              match goal with
              | h: Df (v1e++?x) ?T ?w |- _ =>
                pose (ForwardSmallStep.Core.L4_2 (v1e++x) T w) as b
                ; inversion b; subst
              end.

              match goal with
              | H28: Df _ _ _ -> _,
                H6: Df (v1e++[_]) _ _,
                H16: _ = [] ∨ _ |- _ =>
                pose (H28 H6);
                clear H16;
                breakAll; subst; try discriminate; tac_inj; eauto;
                rmDirect;
                breakAll; subst; try discriminate; tac_inj; eauto;
                clear H28
              end.
            }
          }
          
          (* NOTE I'=PndRet, r=PndCal *)
          1:{
            match goal with
            | h: In (?v,?I)  V |- _ =>
              destruct (IHExtract I v) as [IH1 _]
              ; rmDirect
            end.
            repeat (breakEx + breakAnd)
            ; subst
            ; tac_inj.

            breakOr. breakAnd; tac_inj. 
            repeat (breakEx + breakAnd).

            rename x into v1.
            rename x0 into T1.


            match goal with
            | h: DM.Dm ?L ?w ?v |- _ =>
              pose (ForwardSmallStep.Core.CompleteM _ _ _ h)
              ; pose (L5_2 L w v h) as HDmEnd
            end.           
            do 2 match goal with
            | h: _ -> ?g |- _ =>
            assert g by
            (apply h;
              rewrite  <- app_assoc;
              eauto using app_cons_not_nil)
            ; clear h
            end.

            breakEx.
            breakAnd.
            breakAnd.
            breakEx.
            breakAnd.


            match goal with
            | h: Db ?v ?T ?w |- _ =>
              pose (BackwardSmallStep.Core.L4_2 v T w) as h0
              ; inversion h0
            end.
            rmDirect.
            breakOr.
            2:{
              breakOr.
              2:{
                breakAll; subst; tac_inj; try discriminate.
              }

              repeat (breakAnd + breakEx).

              1:{
                match goal with
                | h: Df (v1e++?x) ?T ?w |- _ =>
                  pose (ForwardSmallStep.Core.L4_2 (v1e++x) T w) as b
                  ; inversion b; subst
                end.
    
                match goal with
                | H28: Df _ _ _ -> _,
                  H6: Df (v1e++[_]) _ _,
                  H16: _ = [] ∨ _ |- _ =>
                  pose (H28 H6);
                  clear H16;
                  breakAll; subst; try discriminate; tac_inj; eauto;
                  rmDirect;
                  breakAll; subst; try discriminate; tac_inj; eauto;
                  clear H28
                end.
    
                match goal with
                | H29: ∀ _ _ _ _ , _ -> _,
                  H27: DM.Dm _ _ _ |- _ =>
                  specialize H29 with (Lv:=L_0) (3:=H27)
                  ; getH; [apply H29; eauto|]
                end.
    
                assert (endE e=x1).
                1:{
                  inversion H1; subst; try tac_invalid_db;
                  simpl.
                  all: try 
                    match goal with
                      | h:Db _ _ (Ret _::_) |- _ =>
                        inversion h; subst; eauto
                    end.
                  all: simpl in *.
                  all: try match goal with
                    | h: VBeginWith [?e] ?L |- _ =>
                      assert (beginE e = L)
                      ; simpl
                      ; inversion h
                      ; subst
                      ; breakAll
                      ; tac_inj
                      ; match goal with
                        | h: _ = _ |- _ =>
                        inversion h; subst
                        end
                      ; eauto
                    | h: VBeginWith (?e :: _) ?L |- _ =>
                      assert (beginE e = L)
                      ; simpl
                      ; inversion h
                      ; subst
                      ; breakAll
                      ; tac_inj
                      ; match goal with
                        | h: _ = _ |- _ =>
                        inversion h; subst
                        end
                      ; eauto
                    end.
                    all: repeat match goal with
                    | h: ?v, h1:?v |- _ =>
                      clear h1
                    end.
                    all: mergeBegins; eauto.
                }

                apply VListEndSame2.
                inversion H21; eauto.
                resolveEndESelf.

                breakAnd.
                
                destruct w1.
    
                simpl in *.
                match goal with
                | h:[_] = ?x1++ _ :: ?x2 |- _ =>
                  assert (x1=[] /\ x2=[]) by
                  (destruct x1; 
                  destruct x2; eauto;
                  simpl in *;
                  repeat simplList
                  ; destruct x1; discriminate)
                end.
                breakAnd; subst; simpl in *.
                left; getAnd; eauto.
                repeat rmDirect; subst;
                simpl in *.
                match goal with
                | h:[_]=[_] |- _ =>
                  inversion h; clear h; subst
                end.
                assert (v1e=[]).
                1:{
                  match goal with
                  | h:Df (v1e ++ [e]) _ _ |- _ =>
                    inversion h; subst; eauto
                    ; tac_inj; eauto
                    ; subst; tac_invalid_df
                  end.
                }
                subst; simpl in *.
                eauto.
    
    
                right.
    
                exists v1e.
    
                match goal with
                | H6: Df (v1e ++ [_]) _ _ |- _ =>
                  inversion H6; subst; eauto; tac_inj; subst
                end;
                match goal with
                | h:Df v1e ?x _ |- _ =>
                  exists x
                end;
                getAnd; eauto;
                extractHead; eauto;
                getAnd; eauto;
                repeat rewrite <- app_assoc in *
                ; eauto.
              }
            }

            repeat (breakAnd + breakEx).

            1:{
              match goal with
              | h: Df (v1e++?x) ?T ?w |- _ =>
                pose (ForwardSmallStep.Core.L4_2 (v1e++x) T w) as b
                ; inversion b; subst
              end.

              match goal with
              | H28: Df _ _ _ -> _,
                H6: Df (v1e++[_]) _ _,
                H16: _ = [] ∨ _ |- _ =>
                pose (H28 H6);
                clear H16;
                breakAll; subst; try discriminate; tac_inj; eauto;
                rmDirect;
                breakAll; subst; try discriminate; tac_inj; eauto;
                clear H28
              end.
            }
          }


          1:{
            match goal with
            | h: In (?v,?I)  V |- _ =>
              destruct (IHExtract I v) as [IH1 _]
              ; rmDirect
            end.
            repeat (breakEx + breakAnd)
            ; subst
            ; tac_inj.

            breakOr. breakAnd; tac_inj. 
            repeat (breakEx + breakAnd).

            rename x into v1.
            rename x0 into T1.


            match goal with
            | h: DM.Dm ?L ?w ?v |- _ =>
              pose (ForwardSmallStep.Core.CompleteM _ _ _ h)
              ; pose (L5_2 L w v h) as HDmEnd
            end.           
            do 2 match goal with
            | h: _ -> ?g |- _ =>
            assert g by
            (apply h;
              rewrite  <- app_assoc;
              eauto using app_cons_not_nil)
            ; clear h
            end.


            breakEx.
            breakAnd.
            breakAnd.
            breakEx.
            breakAnd.


            match goal with
            | h: Df (v1e++[e]) _ _,
              h1: Df v1 _ _ |- _ =>
              pose (ForwardSmallStep.DFX.DF_dfx _ _ _ h)
              ; pose (ForwardSmallStep.DFX.DF_dfx _ _ _ h1)
              ; repeat breakEx
            end.
            match goal with
            | h: Dfx _ _ _ _ _ _ _,
              h1: Dfx _ _ _ _ _ _ _ |- _ =>
              pose (ForwardSmallStep.DFX.DFX_df_sub _ _ _ _ _ _ _ h)
              ; pose (ForwardSmallStep.DFX.DFX_df_sub _ _ _ _ _ _ _ h1)
            end.

            do 2 breakOr;
            repeat (breakAnd + breakEx); subst; try discriminate.

            match goal with
            | h: Df _ (_::_) ?w, 
              h1: Df _ [] _ |- _ =>
              pose (ForwardSmallStep.Df2.L_Df_uniqueT _ _ _ _ _ h h1) as _h
              ; simpl in _h
              ; discriminate
            end.


            simplList; subst.

            match goal with
            | h: Dfx _ _ _ _ _ _ _,
              h2: Dfx _ _ _ _ _ _ _ |- _ =>
              pose (DFX_v _ _ _ _ _ _ _ h)
              ; pose (DFX_v _ _ _ _ _ _ _ h2)
              ; pose (DFX_w _ _ _ _ _ _ _ h)
              ; pose (DFX_w _ _ _ _ _ _ _ h2)
            end.
            breakOr. breakAnd. discriminate.
            breakOr. breakAnd. discriminate.
            breakOr. breakAnd. discriminate.
            breakOr. breakAnd. discriminate.
            repeat (breakEx + breakAnd).

            repeat simplList; subst.


            match goal with
            | h:v1e ++ [e] = ?x3 ++ [Calv _] ++ ?x4
            |- _ =>
              rename x3 into v1e1
              ; rename x4 into v1e2
            end.
            

            match goal with
            | h:Df ((?x ++ [Calv ?x18] ++ ?x0) ++ v') 
              ?x17 ((_ ++ [_]) ++ _) 
            |- _ =>
              rename x18 into v1a
              ; rename x into v11
              ; rename x0 into v12
            end.
            

            match goal with
            | h1: _ ++ [_] = _,
              h2: _ ++ [_] = _,
              h3: _ ++ [_] = _ |- _ =>
              rewrite h1 in *
              ; rewrite h2 in *
              ; rewrite h3 in *
            end.

            match goal with
            | h: Dfx _ _ ?w ?v1 ?v2 ?w1 ?w2,
              h2: Dfx _ _ ?w ?v1' ?v2' ?w1' ?w2' |- _ =>
              assert (w1 = w1' /\ w2 = w2')
            end.

            match goal with
            | h: Dfx _ _ ?w ?v1 ?v2 ?w1 ?w2,
              h2: Dfx _ _ ?w ?v1' ?v2' ?w1' ?w2' |- _ =>
              refine (DFX_len_w _ _ _ _ _ _ _ _ _ h _ _ _ _ _ h2)
            end.

            match goal with
            | h: Df ?v1 _ ?w, h2: ?v2 _ ?w |- length ?w1 = length ?w2 =>
              refine (ForwardSmallStep.Df2.L_Df_uniqueV _ _ _ _ _ h h2)
            end.

            breakAnd; subst.

            match goal with
            | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?v') _ ((?w1 ++ [?a] ++ ?w2) ++ ?w'), 
              h2: Df (?v1 ++ [?ea] ++ ?v2) ?T (?w1 ++ [?a] ++ ?w2) |- _ =>
              assert (Df (v1 ++ [ea]) T (w1 ++ [a]))
            end.
            1:{
              destruct v11.
              syncEmpW; subst.
              simpl; eauto.
              match goal with
              | h: Dfx _ _ _ [] _ _ _ |- _ =>
                rewrite (DF_dfx_nohead _ _ _ _ _ _ _ h) in *
                ; rewrite (DF_dfx_nohead _ _ _ _ _ _ _ h) in h
              end.
              match goal with
              |  |- Df _ [?x] _ =>
                destruct x; constructor; eauto;
                try resolveRule
              end.

              rmDirect.
              assert (v :: v11!=[]) as notnil by eauto using nil_cons
              ; destruct (exists_last notnil) as [? [? _s]]
              ; rewrite _s in *
              ; clear notnil _s
              ; repeat rewrite app_assoc in h.


              match goal with
              | h:Df ?v _ _ |- _ =>
                destruct (VHasEnd _ _ _ h) as [Le ?]
              end.

              match goal with
              |  |- Df _ (?x::_) _ =>
                destruct x; constructor; eauto;
                try resolveRule
              end;

              match goal with
              | h: Df ((?v ++ [Calv ?ea] ++ ?v') ++ ?v'') _ _ |- _ =>
                pose (VConnect _ _ _ h v ([Calv ea] ++ v' ++ v'') Le L) as hconnect
              end;

              assert (Le=L) by (
                apply hconnect; eauto using app_cons_not_nil, nil_cons;
                repeat rewrite <- app_assoc; eauto;
                tryResolveBegin);
              subst; eauto.
            }


            match goal with
            | h:_ ++ [DF.getSym (?ea)] ++ _ =
            _ ++ [DF.getSym v1a] ++ _ |- _ =>
              assert (v1a=ea)
            end.
            1:{
              match goal with
              | h: Db ?v ?T ?w |- _ =>
                pose (BackwardSmallStep.Core.L4_2 v T w) as b0
              end.
              inversion b0.
              rmDirect.
              match goal with
              | H16: _ = [] ∨ _ |- _ =>
                clear H16
              end.
              breakAll; subst; tac_inj; subst; try discriminate;
              try match goal with
              | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
                inversion h; breakAll; subst; discriminate
              end.

              1:{
                inversion H12; subst;
                tac_inj; subst;
                try match goal with
                | h: [_] = (?x1 ++ _ :: ?x2) ++ [_] |- _ =>
                  destruct x1; simpl in *; try discriminate;
                  destruct x2; simpl in *; try discriminate;
                  inversion h; try discriminate;
                  destruct x1; try discriminate
                end.
                match goal with
                | h: Df ?v _ _, 
                  h1: Df ?v _ _ |- _ =>
                  destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                  ; eauto
                  ; try discriminate
                  ; try simplList
                  ; eauto
                end.
                try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  | h: Retv _ = Retv _ |- _ =>
                    inversion h
                end; subst; eauto.
                simplList; subst; eauto.
              }

              1:{
                match goal with
                | h: Df
                ((v11 ++ [Calv v1a] ++ v12) ++
                  ?eb :: ?eb2:: ?v'') _ _
                |- _ =>
                  pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v11 ++ [Calv v1a] ++ v12 ++ [eb]) (eb2::v'')) as _c
                  ; assert (∃ T1 w1, Df (v11 ++ [Calv v1a] ++ v12 ++ [eb]) T1 w1)
                  ; [apply _c; eauto |]
                  ; clear _c
                end.
                repeat (rewrite <- app_assoc + simpl); eauto.
                eauto using app_cons_not_nil.

                do 2 breakEx.
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst;
                  tac_inj; subst;
                  try match goal with
                    | h: [_] = ?x1 ++ _ :: ?x2 ++ [_] |- _ =>
                      destruct x1; simpl in *; try discriminate;
                      destruct x2; simpl in *; try discriminate;
                      inversion h; try discriminate;
                      destruct x1; try discriminate
                    end
                end.
                match goal with
                | h: Df ?v _ _, 
                  h1: Df ?v _ _ |- _ =>
                  destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                  ; eauto
                  ; try discriminate
                  ; try simplList
                  ; eauto
                end.
                try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  | h: Retv _ = Retv _ |- _ =>
                    inversion h
                end; subst; eauto.
                simplList; subst; eauto.
              }

              1:{
                match goal with
                | h: Df
                ((v11 ++ [Calv v1a] ++ v12) ++
                  ?eb :: ?v'') _ _
                |- _ =>
                  pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v11 ++ [Calv v1a] ++ v12 ++ [eb]) (v'')) as _c
                  ; assert (∃ T1 w1, Df (v11 ++ [Calv v1a] ++ v12 ++ [eb]) T1 w1)
                  ; [apply _c; eauto |]
                  ; clear _c
                end.
                repeat (rewrite <- app_assoc + simpl); eauto.
                eauto using app_cons_not_nil.

                do 2 breakEx.
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst;
                  tac_inj; subst;
                  try match goal with
                    | h: [_] = ?x1 ++ _ :: ?x2 ++ [_] |- _ =>
                      destruct x1; simpl in *; try discriminate;
                      destruct x2; simpl in *; try discriminate;
                      inversion h; try discriminate;
                      destruct x1; try discriminate
                    end
                end.
                match goal with
                | h: Df ?v _ _, 
                  h1: Df ?v _ _ |- _ =>
                  destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                  ; eauto
                  ; try discriminate
                  ; try simplList
                  ; eauto
                end.
                try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  | h: Retv _ = Retv _ |- _ =>
                    inversion h
                end; subst; eauto.
                simplList; subst; eauto.
              }


              1:{
                inversion H12; subst;
                tac_inj; subst;
                try match goal with
                | h: [_] = (?x1 ++ _ :: ?x2) ++ [_] |- _ =>
                  destruct x1; simpl in *; try discriminate;
                  destruct x2; simpl in *; try discriminate;
                  inversion h; try discriminate;
                  destruct x1; try discriminate
                end.

                match goal with
                | H40: ∀ _ _ _, Df _ _ _ -> _,
                  H10: Df (v11 ++ [Calv v1a] ++ _) (v1a :: _) _ |- _ => 
                  specialize H40 with (1:=H10)
                end.
                getH. tac_app.
                
                match goal with
                | h: VBeginWithS ?x18 ?x17 ?x20 |- _ =>
                  exists x17
                end.

                getAnd; eauto.
                2: match goal with
                  | h: VBeginWithS ?x18 ?x17 ?x20 |- _ =>
                    inversion h
                  end;
                  repeat breakEx; subst;
                  tryResolveBegin.

                1:{
                  match goal with
                  | h: VBeginWithS ?x18 ?x17 ?x20 |- _ =>
                    destruct x18; [simpl in *; inversion h
                    ; breakAll; subst; try discriminate |]
                  end.

                  match goal with
                  | h: Df ((v11 ++ Calv v1a:: v12) ++ ?vv :: ?v'') _ _
                  |- _ =>
                    pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v11 ++ Calv v1a:: v12 ++ [vv]) (v'')) as _c
                    ; assert (∃ T1 w1, Df (v11 ++ [Calv v1a] ++ v12 ++ [vv]) T1 w1)
                    ; [apply _c; eauto |]
                    ; clear _c
                  end.
                  repeat (rewrite <- app_assoc + simpl); eauto.
                  eauto using app_cons_not_nil.
                  do 2 breakEx.
                  
                  match goal with
                  | h:VBeginWithS _ ?x _ |- VEndWith _ ?x =>
                    inversion h
                  end
                  ; repeat breakEx; simplList; subst
                  ; simplList; subst;

                  match goal with
                  | h:Df _ _ _ |- _ =>
                  inversion h; subst; try simplList; subst
                  end;
                  tac_inj; subst;
                  try match goal with
                  | h: [_] = ?x1 ++ _ :: ?x2 ++ [_] |- _ =>
                    destruct x1; simpl in *; try discriminate;
                    destruct x2; simpl in *; try discriminate;
                    inversion h; try discriminate;
                    destruct x1; try discriminate
                  end;
                  try match goal with
                    | h: Calv _ = Calv _ |- _ =>
                      inversion h
                    | h: Plnv _ = Plnv _ |- _ =>
                      inversion h
                    | h: Retv _ = Retv _ |- _ =>
                      inversion h
                  end; subst; eauto.
                }

                match goal with
                | h: Df ?v _ _, 
                  h1: Df ?v _ _ |- _ =>
                  destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                  ; eauto
                  ; try discriminate
                  ; try simplList
                  ; eauto
                end.

                try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  | h: Retv _ = Retv _ |- _ =>
                    inversion h
                end; subst; eauto.
                simplList; subst; eauto.
              }



              1:{
                match goal with
                | h: Df
                ((v11 ++ [Calv v1a] ++ v12) ++ ?vv ++
                  [?eb] ++ ?eb2:: ?v'') _ _
                |- _ =>
                  pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v11 ++ [Calv v1a] ++ v12 ++ vv ++ [eb]) (eb2::v'')) as _c
                  ; assert (∃ T1 w1, Df (v11 ++ [Calv v1a] ++ v12 ++ vv ++ [eb]) T1 w1)
                  ; [apply _c; eauto |]
                  ; clear _c
                end.
                repeat (rewrite <- app_assoc + simpl); eauto.
                eauto using app_cons_not_nil.
                do 2 breakEx.

                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h
                end; subst;
                tac_inj; subst;
                try match goal with
                | h: [_] = ?x1 ++ _ :: ?x2 ++ _ ++ [_] |- _ =>
                  destruct x1; simpl in *; try discriminate;
                  destruct x2; simpl in *; try discriminate;
                  inversion h; try discriminate;
                  destruct x1; try discriminate
                end;
                match goal with
                | h: _ = _ |- _ =>
                  rewrite app_comm_cons in h;
                  repeat rewrite app_assoc in h;
                  tac_inj; subst
                end.
                

                match goal with
                | H40: ∀ _ _ _, Df _ _ _ -> _,
                  H10: Df (v11 ++ [Calv v1a] ++ _) (v1a :: _) _ |- _ => 
                  specialize H40 with (1:=H10)
                end.
                getH. tac_app.
                
                match goal with
                | h: VBeginWithS ?x18 ?x17 ?x20 |- _ =>
                  exists x17
                end.

                getAnd; eauto.
                2: match goal with
                  | h: VBeginWithS ?x18 ?x17 ?x20 |- _ =>
                    inversion h
                  end;
                  repeat breakEx; subst;
                  tryResolveBegin.

                1:{
                  match goal with
                  | h: VBeginWithS ?x18 ?x17 ?x20 |- _ =>
                    destruct x18; [simpl in *; inversion h
                    ; breakAll; subst; try discriminate |]
                  end.

                  match goal with
                  | h: Df ((v11 ++ Calv v1a:: v12) ++ ?vv :: ?v'') _ _
                  |- _ =>
                    pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v11 ++ Calv v1a:: v12 ++ [vv]) (v'')) as _c
                    ; assert (∃ T1 w1, Df (v11 ++ [Calv v1a] ++ v12 ++ [vv]) T1 w1)
                    ; [apply _c; eauto |]
                    ; clear _c
                  end.
                  repeat (rewrite <- app_assoc + simpl); eauto.
                  eauto using app_cons_not_nil.
                  do 2 breakEx.
                  
                  match goal with
                  | h:VBeginWithS _ ?x _ |- VEndWith _ ?x =>
                    inversion h
                  end
                  ; repeat breakEx; simplList; subst
                  ; simplList; subst;

                  match goal with
                  | h:Df _ _ _ |- _ =>
                  inversion h; subst; try simplList; subst
                  end;
                  tac_inj; subst;
                  try match goal with
                  | h: [_] = ?x1 ++ _ :: ?x2 ++ [_] |- _ =>
                    destruct x1; simpl in *; try discriminate;
                    destruct x2; simpl in *; try discriminate;
                    inversion h; try discriminate;
                    destruct x1; try discriminate
                  end;
                  try match goal with
                    | h: Calv _ = Calv _ |- _ =>
                      inversion h
                    | h: Plnv _ = Plnv _ |- _ =>
                      inversion h
                    | h: Retv _ = Retv _ |- _ =>
                      inversion h
                  end; subst; eauto.
                }

                match goal with
                | h: Df ?v _ _, 
                  h1: Df ?v _ _ |- _ =>
                  destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                  ; eauto
                  ; try discriminate
                  ; try simplList
                  ; eauto
                end.

                try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  | h: Retv _ = Retv _ |- _ =>
                    inversion h
                end; subst; eauto.
                simplList; subst; eauto.
              }

              1:{
                match goal with
                | h: Df
                ((v11 ++ [Calv v1a] ++ v12) ++ ?vv ++
                  [?eb] ++ ?v'') _ _
                |- _ =>
                  pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v11 ++ [Calv v1a] ++ v12 ++ vv ++ [eb]) (v'')) as _c
                  ; assert (∃ T1 w1, Df (v11 ++ [Calv v1a] ++ v12 ++ vv ++ [eb]) T1 w1)
                  ; [apply _c; eauto |]
                  ; clear _c
                end.
                repeat (rewrite <- app_assoc + simpl); eauto.
                eauto using app_cons_not_nil.
                do 2 breakEx.

                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h
                end; subst;
                tac_inj; subst;
                try match goal with
                | h: [_] = ?x1 ++ _ :: ?x2 ++ _ ++ [_] |- _ =>
                  destruct x1; simpl in *; try discriminate;
                  destruct x2; simpl in *; try discriminate;
                  inversion h; try discriminate;
                  destruct x1; try discriminate
                end;
                match goal with
                | h: _ = _ |- _ =>
                  rewrite app_comm_cons in h;
                  repeat rewrite app_assoc in h;
                  tac_inj; subst
                end.
                

                match goal with
                | H40: ∀ _ _ _, Df _ _ _ -> _,
                  H10: Df (v11 ++ [Calv v1a] ++ _) (v1a :: _) _ |- _ => 
                  specialize H40 with (1:=H10)
                end.
                getH. tac_app.
                
                match goal with
                | h: VBeginWithS ?x18 ?x17 ?x20 |- ∃ _, _ /\ VBeginWith ?x18 _ =>
                  exists x17
                  ; getAnd; 
                  [
                    destruct x18; [simpl in *; inversion h
                    ; breakAll; subst; try discriminate |]
                  |
                    inversion h; repeat breakEx; subst;
                    tryResolveBegin
                  ]
                end.
                
                1:{
                  match goal with
                  | h: Df ((v11 ++ Calv v1a:: v12) ++ ?vv :: ?v'') _ _
                  |- _ =>
                    pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v11 ++ Calv v1a:: v12 ++ [vv]) (v'')) as _c
                    ; assert (∃ T1 w1, Df (v11 ++ [Calv v1a] ++ v12 ++ [vv]) T1 w1)
                    ; [apply _c; eauto |]
                    ; clear _c
                  end.
                  repeat (rewrite <- app_assoc + simpl); eauto.
                  eauto using app_cons_not_nil.
                  do 2 breakEx.
                  
                  match goal with
                  | h:VBeginWithS _ ?x _ |- VEndWith _ ?x =>
                    inversion h
                  end
                  ; repeat breakEx; simplList; subst
                  ; simplList; subst;

                  match goal with
                  | h:Df _ _ _ |- _ =>
                  inversion h; subst; try simplList; subst
                  end;
                  tac_inj; subst;
                  try match goal with
                  | h: [_] = ?x1 ++ _ :: ?x2 ++ [_] |- _ =>
                    destruct x1; simpl in *; try discriminate;
                    destruct x2; simpl in *; try discriminate;
                    inversion h; try discriminate;
                    destruct x1; try discriminate
                  end;
                  try match goal with
                    | h: Calv _ = Calv _ |- _ =>
                      inversion h
                    | h: Plnv _ = Plnv _ |- _ =>
                      inversion h
                    | h: Retv _ = Retv _ |- _ =>
                      inversion h
                  end; subst; eauto.
                }

                match goal with
                | h: Df ?v _ _, 
                  h1: Df ?v _ _ |- _ =>
                  destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                  ; eauto
                  ; try discriminate
                  ; try simplList
                  ; eauto
                end.

                try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  | h: Retv _ = Retv _ |- _ =>
                    inversion h
                end; subst; eauto.
                simplList; subst; eauto.
              }
            }


            subst.

            match goal with
            | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?v') _ ((?w1 ++ [?a] ++ ?w2) ++ ?w'), 
              h2: Df (?v1 ++ [?ea] ++ ?v2) ?T (?w1 ++ [?a] ++ ?w2),
              h3: Df (?ve ++ [?ee] ++ ?ve') _ (?we ++ [?e] ++ ?we') |- _ =>
              assert (Df (v1 ++ [ea] ++ ve') T (w1 ++ [a] ++ w2))
            end.
            1:{
              match goal with
              | |- Df (_ ++ [_] ++ ?x) _ _ =>
                destruct x as [|v1e2e ?]
              end.
              syncEmpW; subst.
              simpl; eauto.

              rmDirect.
              do 2 rewrite app_assoc.

              match goal with
              | h: Df ?v _ _ |- _ =>
                destruct (VHasHead _ _ _ h)
              end.

              match goal with
              | h: ∀ _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v) _ (_++?w),
                h2: VBeginWith ?v ?Lv' |- 
                Df (_ ++ ?v) _ (_++?w) =>
                  apply h with (Lv := Lv'); eauto
              end.

              match goal with
              | h:Df (v1e1 ++ [Calv (MatCalE ?x3 ?x4 ?x5 ?x6 ?x7)] ++ v1e2e :: v1e2) _ _,
                H22: VBeginWith (v1e2e :: v1e2) ?x1 |- _ =>
                pose (VConnect _ _ _ h (v1e1 ++ [Calv (MatCalE x3 x4 x5 x6 x7)]) (v1e2e :: v1e2)
                    x5 x1
                ) as hconnect
                ; assert (x5=x1)
                ; [apply hconnect; 
                  eauto using app_cons_not_nil, nil_cons|]
              end.
              rewrite <- app_assoc; eauto.
              BackwardSmallStep.Core.tryResolveEnd.
              subst.
              BackwardSmallStep.Core.tryResolveEnd.
            }




            match goal with
            | h:Db (e::v') _ _ |- _ =>
              inversion h; subst
              ; try tac_invalid_db
            end;
            try match goal with
            | h:Db ?v' _ _, h1: Db ?v' _ _ |- _ =>
              pose (L_Db_uniqueT _ _ _ _ _ h h1)
              ; try discriminate
              ; subst
            end;
            try simplList; subst; eauto.

            (* SECTION e=Pln, v'=MatRet *)
            1:{
              match goal with
              | h: Df (v11 ++ [?ea] ++ v1e2) _ _ |- _ =>
                assert (VEndWith ((v11 ++ [ea]) ++ v1e2) L1)
              end.
              1:{
                destruct v1e2.
                simpl in *; tac_inj.
                match goal with
                | h: _++[_]=_++_++?e::?v |- _ =>
                  assert (e::v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                  ; tac_inj
                  ; subst
                end.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
              }

              assert (∃v'', v'=Retv (MatRetE L2 a L3 b L4)::v'')
              by match goal with
                  | h: Db _ _ _ |- _ =>
                    inversion h; subst; simpl; eauto
                  end.

              breakEx.
              subst.


              match goal with
              | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?e' :: ?v'') _ ((?w1 ++ [?a] ++ ?w2)++ ?w' :: _), 
                h2: Df (?v1 ++ [?ea] ++ ?v2') _ (?w1 ++ [?a] ++ ?w2') 
              |- _ =>
                pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v1 ++ [ea] ++ v2 ++ [e']) v'') as _h
                ; assert (∃ T1 w1, Df (v1 ++ [ea] ++ v2 ++ [e']) T1 w1)
                ; [apply _h; eauto |]
                ; clear _h
              end.
              repeat (simpl + (repeat rewrite <- app_assoc) + eauto).
              eauto using app_cons_not_nil.
              do 2 breakEx.


              match goal with
              | h: Df (v11 ++ [Calv ?ea] ++ v12 ++ [Retv (MatRetE ?L2 ?a ?L3 ?b ?L4)]) ?x0 ?x3,
                h2: Df (v11 ++ [Calv ?ea] ++ v12) (?ea :: ?x19) ?w
              |- _ =>
                assert (x0=x19 /\ 
                  (x3=w ++ [Ret b]))
              end.
              1: {
                match goal with
                | h: Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                end.

                all: try getAnd.
                all: try getAnd.

                all: try (
                  try inversion a; try inversion a1; 
                  try inversion a2; subst;
                  match goal with
                  | h: Df ?v _ _, 
                    h1: Df ?v _ _ |- _ =>
                    destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                    ; eauto
                    ; try discriminate
                    ; try simplList
                    ; eauto
                  end).


                all: try match goal with
                  | h:[_] = ?v ++ _ :: _ ++ _ ::_ |- _ =>
                    destruct v; simpl in *; simplList; tac_inj; try discriminate
                  end.

                all: try rewrite <- H29; simpl; subst; eauto.
              }
              breakAnd; subst.


              match goal with
              | h: Df (?x++?y++v1e2) (?t::?T) ?w |- _ =>
                assert (Df (x++y++v1e2++[Retv (MatRetE L2 a L3 b L4)]) T (w++[Ret b]))
              end.
              pose V_Ret as hc.
              match goal with
              | H26: Df (v11 ++ [Calv (_)] ++ v1e2) 
                (_ :: _)
                (?x1 ++ [DF.getSym (_)] ++ ?x2) |- _ =>
                specialize hc with (3:=H26) (L:=L1)
              end.
              repeat rewrite app_assoc in *.
              apply (hc); eauto.

              match goal with
              | h: Df (v11++_) ?x19 _, h2: Df (v11++_) ?x19 _ |- _ =>
                repeat rewrite app_assoc in h
                ; repeat rewrite app_assoc in h2
                ; pose (ForwardSmallStep.Df2.L_DF_Local _ _ _ _ _ h h2) as Hlocal
                ; repeat rewrite <- app_assoc in Hlocal
              end.
              match goal with
              | H19: Df ((v11 ++ [Calv _] ++ v12) ++ Retv _ :: _) _
              ((?x1 ++ [DF.getSym _] ++ ?x2) ++ Ret b :: w) |- _ =>
                repeat rewrite <- app_assoc in H19;
                simpl in H19
              end.
              match goal with
              | h: Db (Retv _ :: ?x) (_ :: T) (Ret b :: ?w),
                h2: Df (v11 ++ _ :: v12 ++ _ :: ?x) ?x12
                (?x1 ++ Call a :: ?x2 ++ Ret b :: ?w) |- _ =>
                pose (Hlocal x x12 w);
                repeat rewrite <- app_assoc in d0;
                simpl in d0;
                pose (d0 h2)
              end.

              match goal with
              | h: VEndWith ((v11 ++ [Calv _] ++ v12) ++ _ :: _) ?x13 |- _ =>
                pose (ForwardSmallStep.Core.SoundV) as _h
                ; specialize _h with (Lv:=L_0) (L:=x13) (1:=d1)
              end.
              getH. apply _h; eauto.
              1:{
                match goal with
                | h: VBeginWith (v11 ++ [Calv ?v1a] ++ ?v12) L_0
                  |- _ =>
                  rewrite app_assoc in h
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              1:{
                rewrite app_comm_cons.
                rewrite app_assoc.
                match goal with
                | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ ?e :: ?v) ?x13 |- _ =>
                  assert (e :: v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                end.

                extractEnds;
                repeat rewrite app_assoc;
                BackwardSmallStep.Core.tryResolveEnd.
              }

              destruct w1.
              simpl in *.
              match goal with
              | h: [_] = ?x1 ++ _::_ |- _ =>
                destruct x1; simpl in *
                ; repeat simplList
                ; try discriminate; subst
                ; destruct x1; try discriminate
              end.

              right.
              simpl.

              match goal with
              | H30: DM.Dm _ _ _, 
                H23: (_ :: _) ++ [_] = ?x1 ++ [_] ++ ?x2 |- _ =>
                repeat rewrite app_comm_cons in H30;
                repeat rewrite app_assoc in H30;
                simpl in H23;
                rewrite <- H23 in H30
              end.
              destruct v1e2; simpl in *.
              tac_inj.


              assert (v :: v1e2!=[]) as notnil by eauto using nil_cons
              ; destruct (exists_last notnil) as [? [? _s]]
              ; rewrite _s in *
              ; clear notnil _s
              ; repeat rewrite app_assoc in h.

              match goal with
              | H25: v1e ++ [_] = _ |- _ =>
                repeat rewrite app_comm_cons in H25;
                repeat rewrite app_assoc in H25;
                destruct (app_inj_tail _ _ _ _ H25);
                subst
              end.


              
              match goal with
              | H22: ?x1 ++ _ :: ?x2 = _,
                H23: ?s :: ?w1 ++ [_] = _,
                H26: Df (v11 ++ Calv _ :: ?x ++ [_]) _ _ |- _ =>
                rewrite <- H23 in H26;
                repeat rewrite app_assoc in H26
              end.

              match goal with
              | h:DM.Dm L_0 _
              ((v11 ++ Calv (MatCalE L2 a L3 b L4) :: ?x0 ++ [_]) ++ _) |- _ =>
                exists (v11 ++ Calv (MatCalE L2 a L3 b L4) :: x0);
                assert (∃ I1, Df (v11 ++ Calv (MatCalE L2 a L3 b L4) :: x0) I1 (s :: w1))
              end.
              1:{
                match goal with
                | h: Df (v11 ++ Calv _ :: _ ++ [Plnv _]) (_ :: _) _ |- _ =>
                  inversion h; subst; tac_inj; subst;
                  try (match goal with
                  | h:Df _ ?T _ |- _ =>
                    exists T; eauto
                  end; fail)
                end.
              }
              breakEx.

              match goal with
              | h: Df _ ?T _ |- _ =>
                exists T
              end.
              getAnd; eauto.
              1: {
                match goal with
                | h: VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0
                  |- _ =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e in h
                  ; clear _e
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              getAnd; eauto.
              match goal with
              | H30: DM.Dm _ _ _ |- _ =>
                repeat (rewrite <- app_assoc in H30 + simpl in H30); eauto;
                repeat (rewrite <- app_assoc + simpl); eauto
              end.
            }


            (* SECTION e=Pln, v'=Call a *)
            1:{
              match goal with
              | h: Df (v11 ++ [?ea] ++ v1e2) _ _ |- _ =>
                assert (VEndWith ((v11 ++ [ea]) ++ v1e2) L1)
              end.
              1:{
                destruct v1e2.
                simpl in *; tac_inj.
                match goal with
                | h: _++[_]=_++_++?e::?v |- _ =>
                  assert (e::v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                  ; tac_inj
                  ; subst
                end.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
              }

              assert (∃ea v'', v'=Calv ea::v'').
              1:{
                match goal with
                | h:Db _ _ _ |- _ =>
                  inversion h; subst; simpl; eauto
                end.
              }
              do 2 breakEx; subst.
              match goal with
              | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?e' :: ?v'') _ ((?w1 ++ [?a] ++ ?w2)++ ?w' :: _), 
                h2: Df (?v1 ++ [?ea] ++ ?v2') _ (?w1 ++ [?a] ++ ?w2') 
              |- _ =>
                pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v1 ++ [ea] ++ v2 ++ [e']) v'') as _h
                ; assert (∃ T1 w1, Df (v1 ++ [ea] ++ v2 ++ [e']) T1 w1)
                ; [apply _h; eauto |]
                ; clear _h
              end.
              repeat (simpl + (repeat rewrite <- app_assoc) + eauto).
              eauto using app_cons_not_nil.
              do 2 breakEx.

              match goal with
              | h: Df _ ?x3 ?x5,
                h2: VBeginWith (Calv ?x :: _) _,
                h3: Df (v11 ++ [Calv ?v1a]) (_ :: ?x19) (?x1 ++ [?i]),
                h4: v1e2 != [] → Df v1e2 [] ?x2 |- _ =>
                assert (x3 = x :: v1a :: x19 /\ 
                (x5=x1 ++ [i] ++ x2 ++ [Call a]))
              end.
              1: {
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                end.

                all: try getAnd.

                all: try (
                  try inversion a; try inversion a1; 
                  try inversion a2; subst;
                  match goal with
                  | h: Df ?v _ _, 
                    h1: Df ?v _ _ |- _ =>
                    destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                    ; eauto
                    ; try discriminate
                    ; try simplList
                    ; eauto
                  end).


                all: try match goal with
                  | h:[_] = ?v ++ _ :: _ ++ _ ::_ |- _ =>
                    destruct v; simpl in *; simplList; tac_inj; try discriminate
                  end.

                all: try match goal with
                  | H16: _ :: _ = _ |- _ =>
                  rewrite <- H16
                  end; simpl; subst; eauto.
                all: match goal with
                  | h: Db _ _ _ |- _ =>
                  inversion h; subst; 
                  simpl;
                  rewrite <- app_assoc;
                  eauto
                  end.
              }
              breakAnd; subst.


              match goal with
              | h: Df (?x1++?y++v1e2) ?T ?w,
                h2: VBeginWith (Calv ?x :: _) _ |- _ =>
                assert (Df (x1++y++v1e2++[Calv x]) (x::T) (w++[Call a]))
                ; [destruct x;
                assert (a=a0) by (match goal with | h:Db _ _ _ |- _ => inversion h; eauto end);
                subst |]
              end.
              1:{
                pose V_Pnd_Cal as hc.
                match goal with
                | h:Df (v11 ++ [Calv ?v1a] ++ v1e2) (_ :: _) (?x1 ++ [DF.getSym ?v1a] ++ ?x2) 
                |- _ =>
                  specialize hc with (3:=h)
                end.
                repeat rewrite app_assoc in *.
                apply (hc); eauto.

                match goal with
                | h: Db _ _ _ |- _ =>
                  inversion h; eauto
                end.

                match goal with
                | h: VBeginWith (Calv (_ ?L2 _ _) :: _) L1 |- _ =>
                  assert (L2=L1) by
                  (inversion h; subst; breakAll; simplList;
                    eauto)
                  ; subst
                end.
                eauto.
              }
              1:{
                pose V_Cal as hc.
                match goal with
                | h:Df (v11 ++ [Calv ?v1a] ++ v1e2) (_ :: _) (?x1 ++ [DF.getSym ?v1a] ++ ?x2) 
                |- _ =>
                  specialize hc with (3:=h)
                end.
                repeat rewrite app_assoc in *.
                apply (hc); eauto.

                match goal with
                | h: Df (?v ++ Calv ?ea :: ?v'') _ _
                |- _ =>
                  pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v ++ [Calv ea]) v'') as _h
                  ; assert (∃ T1 w1, Df (v ++ [Calv ea]) T1 w1)
                  ; [apply _h; eauto using app_cons_not_nil |]
                  ; clear _h
                end.

                rewrite app_nil_r; eauto.
                do 2 breakEx.
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; eauto; tac_inj; subst; eauto;
                  match goal with
                  | h:Calv _ = Calv _ |- _ =>
                  inversion h; subst; eauto
                  end
                end.


                match goal with
                | h: VBeginWith (Calv (_ ?L2 _ _ _ _) :: _) L1 |- _ =>
                  assert (L2=L1) by
                  (inversion h; subst; breakAll; simplList;
                    eauto)
                  ; subst
                end.
                eauto.
              }

              match goal with
              | h: Df (v11++_) ?T _, h2: Df (v11++_) ?T _ |- _ =>
                repeat rewrite app_assoc in h
                ; repeat rewrite app_assoc in h2
                ; pose (ForwardSmallStep.Df2.L_DF_Local _ _ _ _ _ h h2) as Hlocal
                ; repeat rewrite <- app_assoc in Hlocal
              end.
              match goal with
              | H19: Df ((v11 ++ [Calv ?v1a] ++ v12) ++ Calv _ :: ?x0) ?x12 
                ((?x1 ++ [DF.getSym ?v1a] ++ ?x2) ++ Call a :: ?w) 
              |- _ =>
                repeat rewrite <- app_assoc in H19;
                simpl in H19;
                pose (Hlocal x0 x12 w);
                repeat rewrite <- app_assoc in d0;
                simpl in d0;
                pose (d0 H19)
              end.


              match goal with
              | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ _ :: _) ?x13 |- _ =>
                pose (ForwardSmallStep.Core.SoundV) as _h
                ; specialize _h with (Lv:=L_0) (L:=x13) (1:=d1)
              end.
              getH. apply _h; eauto.
              1:{
                match goal with
                | h: VBeginWith (v11 ++ [Calv ?v1a] ++ ?v12) L_0
                  |- _ =>
                  rewrite app_assoc in h
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              1:{
                rewrite app_comm_cons.
                rewrite app_assoc.
                match goal with
                | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ ?e :: ?v) ?x13 |- _ =>
                  assert (e :: v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                end.

                extractEnds;
                repeat rewrite app_assoc;
                BackwardSmallStep.Core.tryResolveEnd.
              }


              destruct w1.
              simpl in *.


              match goal with
              | h: [_] = ?x1 ++ _::_ |- _ =>
                destruct x1; simpl in *
                ; repeat simplList
                ; try discriminate; subst
                ; destruct x1; try discriminate
              end.

              right.
              simpl.

              match goal with
              | H30: DM.Dm _ _ _, H23: (_ :: _) ++ [_] = _ |- _ =>
                repeat rewrite app_comm_cons in H30;
                repeat rewrite app_assoc in H30;
                simpl in H23;
                rewrite <- H23 in H30
              end.

              destruct v1e2; simpl in *.
              tac_inj.


              assert (v :: v1e2!=[]) as notnil by eauto using nil_cons
              ; destruct (exists_last notnil) as [? [? _s]]
              ; rewrite _s in *
              ; clear notnil _s
              ; repeat rewrite app_assoc in h.

              match goal with
              | H25: v1e ++ [_] = v1e1 ++ Calv ?v1ea :: ?x3 ++ [_],
                H23: ?s :: ?w1 ++ [_] = _,
                H26: Df (v11 ++ Calv ?v1a :: _ ++ [_]) _ _ |- _ =>
                repeat rewrite app_comm_cons in H25;
                repeat rewrite app_assoc in H25;
                destruct (app_inj_tail _ _ _ _ H25);
                subst;

                exists (v11 ++ Calv v1a :: x3);
                rewrite <- H23 in H26;
                repeat rewrite app_assoc in H26;

                assert (∃ I1, Df (v11 ++ Calv v1a :: x3) I1 (s :: w1)) 
              end.

              match goal with
              | H26: Df (v11 ++ Calv ?v1a :: ?x3 ++ [Plnv _]) (_ :: _) (?s :: ?w1 ++ [_]) |- _ =>
                inversion H26; subst; tac_inj; subst;
                try (match goal with
                | h:Df _ ?T _ |- _ =>
                  exists T; eauto
                end; fail)
              end.



              breakEx.
              match goal with
              | h: Df _ ?T _ |- _ =>
                exists T
              end.
              getAnd; eauto.
              1: {
                match goal with
                | h: VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0
                  |- _ =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e in h
                  ; clear _e
                end;

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              getAnd; eauto.
              match goal with
              | H30: DM.Dm _ _ _ |- _ =>
                repeat (rewrite <- app_assoc in H30 + simpl in H30); eauto;
                repeat (rewrite <- app_assoc + simpl); eauto
              end.
            }
            
            1:{
              match goal with
              | h: Df (v11 ++ [?ea] ++ v1e2) _ _ |- _ =>
                assert (VEndWith ((v11 ++ [ea]) ++ v1e2) L1)
              end.
              1:{
                destruct v1e2.
                simpl in *; tac_inj.
                match goal with
                | h: _++[_]=_++_++?e::?v |- _ =>
                  assert (e::v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                  ; tac_inj
                  ; subst
                end.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
              }

              assert (∃ec v'', v'=Plnv ec::v'').
              1:{
                match goal with
                | h: Db v' _ _ |- _ =>
                  inversion h; subst; simpl; eauto
                end.
              }
              do 2 breakEx; subst.
              match goal with
              | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?e' :: ?v'') _ ((?w1 ++ [?a] ++ ?w2)++ ?w' :: _), 
                h2: Df (?v1 ++ [?ea] ++ ?v2') _ (?w1 ++ [?a] ++ ?w2') 
              |- _ =>
                pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v1 ++ [ea] ++ v2 ++ [e']) v'') as _h
                ; assert (∃ T1 w1, Df (v1 ++ [ea] ++ v2 ++ [e']) T1 w1)
                ; [apply _h; eauto |]
                ; clear _h
              end.
              repeat (simpl + (repeat rewrite <- app_assoc) + eauto).
              eauto using app_cons_not_nil.
              do 2 breakEx.

              match goal with
              | h: Df _ ?x3 ?x5,
                h2: VBeginWith (Plnv ?x :: _) _,
                h3: Df (v11 ++ [Calv ?v1a]) (_ :: ?x19) (?x1 ++ [?i]),
                h4: v1e2 != [] → Df v1e2 [] ?x2 |- _ =>
                assert (x3 = v1a :: x19 /\ 
                (x5=x1 ++ [i] ++ x2 ++ [Plain c2]))
              end.
              1: {
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                end.

                all: try getAnd.

                all: try (
                  try inversion a; try inversion a1; 
                  try inversion a2; subst;
                  match goal with
                  | h: Df ?v _ _, 
                    h1: Df ?v _ _ |- _ =>
                    destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                    ; eauto
                    ; try discriminate
                    ; try simplList
                    ; eauto
                  end).


                all: try match goal with
                  | h:[_] = ?v ++ _ :: _ ++ _ ::_ |- _ =>
                    destruct v; simpl in *; simplList; tac_inj; try discriminate
                  end.

                all: try match goal with
                  | H16: _ :: _ = _ |- _ =>
                  rewrite <- H16
                  end; simpl; subst; eauto.
                all: match goal with
                  | h: Db _ _ _ |- _ =>
                  inversion h; subst; 
                  simpl;
                  rewrite <- app_assoc;
                  eauto
                  end.
              }
              breakAnd; subst.

              match goal with
              | h: Df (?x1++?y++v1e2) ?T ?w,
                h2: VBeginWith (Plnv ?x :: _) _ |- _ =>
                assert (Df (x1++y++v1e2++[Plnv x]) (T) (w++[Plain c2]))
                ; [destruct x;
                assert (c0=c2) by (match goal with | h:Db _ _ _ |- _ => inversion h; eauto end);
                subst |]
              end.
              1:{
                pose V_Pln as hc.
                match goal with
                | H26: Df (v11 ++ [Calv ?v1a] ++ v1e2) _ _ |- _ =>
                  specialize hc with (3:=H26)
                end.
                repeat rewrite app_assoc in *.
                apply (hc); eauto.
                match goal with
                | h: Db _ _ _ |- _ =>
                  inversion h; eauto
                end.

                match goal with
                | h: VBeginWith (Plnv (PlnE ?L2 _ _) :: _) L1 |- _ =>
                  assert (L2=L1) by
                  (inversion h; subst; breakAll; simplList;
                    eauto)
                  ; subst
                end.
                eauto.
              }

              match goal with
              | h: Df (v11++_) ?T _, h2: Df (v11++_) ?T _ |- _ =>
                repeat rewrite app_assoc in h
                ; repeat rewrite app_assoc in h2
                ; pose (ForwardSmallStep.Df2.L_DF_Local _ _ _ _ _ h h2) as Hlocal
                ; repeat rewrite <- app_assoc in Hlocal
              end.

              match goal with
              | H19: Df ((v11 ++ [Calv ?v1a] ++ v12) ++ _ :: ?x0) ?x12 
                ((?x1 ++ [DF.getSym ?v1a] ++ ?x2) ++ _ :: ?w) 
              |- _ =>
                repeat rewrite <- app_assoc in H19;
                simpl in H19;
                pose (Hlocal x0 x12 w);
                repeat rewrite <- app_assoc in d0;
                simpl in d0;
                pose (d0 H19)
              end.


              match goal with
              | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ _ :: _) ?x13 |- _ =>
                pose (ForwardSmallStep.Core.SoundV) as _h
                ; specialize _h with (Lv:=L_0) (L:=x13) (1:=d1)
              end.
              getH. apply _h; eauto.
              1:{
                match goal with
                | h: VBeginWith (v11 ++ [Calv ?v1a] ++ ?v12) L_0
                  |- _ =>
                  rewrite app_assoc in h
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              1:{
                rewrite app_comm_cons.
                rewrite app_assoc.
                match goal with
                | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ ?e :: ?v) ?x13 |- _ =>
                  assert (e :: v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                end.

                extractEnds;
                repeat rewrite app_assoc;
                BackwardSmallStep.Core.tryResolveEnd.
              }

              destruct w1.
              simpl in *.


              match goal with
              | h: [_] = ?x1 ++ _::_ |- _ =>
                destruct x1; simpl in *
                ; repeat simplList
                ; try discriminate; subst
                ; destruct x1; try discriminate
              end.

              right.
              simpl.

              match goal with
              | H30: DM.Dm _ _ _,
                H29: Df _ _ _,
                H23: (_ :: _) ++ [_] = _ |- _ =>
                repeat rewrite app_comm_cons in H30;
                repeat rewrite app_assoc in H30;
                simpl in H23;
                rewrite <- H23 in H30
              end.

              destruct v1e2; simpl in *.
              tac_inj.


              assert (v :: v1e2!=[]) as notnil by eauto using nil_cons
              ; destruct (exists_last notnil) as [? [? _s]]
              ; rewrite _s in *
              ; clear notnil _s
              ; repeat rewrite app_assoc in h.

              match goal with
              | H25:  v1e ++ [_] = _++_::?x3++_,
                H23: ?s :: ?w1 ++ [_] = _,
                H26: Df (v11 ++ Calv ?v1a :: ?x3 ++ [_]) _ _ |- _ =>
                repeat rewrite app_comm_cons in H25;
                repeat rewrite app_assoc in H25;
                destruct (app_inj_tail _ _ _ _ H25);
                subst;
                exists (v11 ++ Calv v1a :: x3);
                rewrite <- H23 in H26;
                repeat rewrite app_assoc in H26;
                assert (∃ I1, Df (v11 ++ Calv v1a :: x3) I1 (s :: w1)) by
                (inversion H26; subst; tac_inj; subst;
                try (match goal with
                | h:Df _ ?T _ |- _ =>
                  exists T; eauto
                end; fail))
              end.

              breakEx.
              match goal with
              | h: Df _ ?T _ |- _ =>
                exists T
              end.
              getAnd; eauto.
              1: {
                match goal with
                | h: VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0
                  |- _ =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e in h
                  ; clear _e
                end;

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              getAnd; eauto.
              match goal with
              | H30: DM.Dm _ _ _ |- _ =>
                repeat (rewrite <- app_assoc in H30 + simpl in H30); eauto;
                repeat (rewrite <- app_assoc + simpl); eauto
              end.
            }


            
            (* SECTION e=Cal, v'=MatRet *)
            1:{
              assert (∃v'', v'=Retv (MatRetE L a L1 b L2)::v'').
              1:{
                match goal with
                | h: Db _ _ _ |- _ =>
                  inversion h; subst; simpl; eauto
                end.
              }
              breakEx; subst.


              match goal with
              | H25: v1e ++ [Calv (MatCalE L a L1 b L2)] = _,
                e0: Dfx (v1e1 ++ [Calv _] ++ v1e2) _ _ _ _ _ _ |- _ =>
                rewrite <- H25 in e0
              end.

              match goal with
              | h: w1 ++ [Call _] = _ ++ [DF.getSym _] ++ ?x10 |- _ =>
                assert (v1e2=[] /\ x10=[])
              end.
              1:{
                inversion e0; subst; eauto; tac_inj; subst.
              }
              breakAnd; subst.

              assert (v12=[]).
              1:{     
                destruct v12; eauto.
                rmDirect.
                tac_invalid_df.
              }
              subst.

              simpl in *.


              destruct w1.
              left.
              getAnd; eauto.
              match goal with
              | h: Df (v11 ++ [Calv _]) _ (?x1 ++ [Call _]) |- _ =>
              assert (x1=[]) by
                (destruct x1; simpl in *; do 2 simplList; eauto;
                destruct x1; try discriminate)
              end.
              subst.
              simpl in *.
              assert (v11=[]).
              1:{
                destruct v11; eauto. rmDirect; tac_invalid_df.
              }
              subst.
              simpl in *.
              eauto.


              right.
              match goal with
              | h: (?s::?w1) ++[_] = ?x1 ++ [_] |- _ =>
                assert (s::w1=x1) by (tac_inj; eauto)
              end.
              subst.
              pose H3.

              exists v11.

              destruct v11.
              1:{
                match goal with
                | H26: Df ([] ++_) _ _ |- _ =>
                  inversion H26; subst; tac_inj; subst; try tac_invalid_df
                end.
                
              }

              rmDirect.
              match goal with
              | h: Df _ ?x19 _ |- _ =>
                exists x19
              end.
              getAnd; eauto.
              extractHead; eauto.
              getAnd; eauto. 
              simpl in *.
              match goal with
              | h: DM.Dm _ _ _ |- _ =>
                repeat rewrite <- app_assoc in h
              end.
              eauto.
            }


            (* SECTION e=Cal, v'=Cal, T=MatRet *)
            1:{
              assert (∃e v'', v'=(Calv e)::v'').
              1:{
                match goal with
                | H33: Db _ _ _  |- _ =>
                  inversion H33; subst; simpl; eauto
                end.
              }
              breakEx; subst.


              match goal with
              | H25: v1e ++ [Calv (MatCalE L a L1 b L2)] = _,
                e0: Dfx (v1e1 ++ [Calv _] ++ v1e2) _ _ _ _ _ _ |- _ =>
                rewrite <- H25 in e0
              end.

              match goal with
              | h: w1 ++ [Call _] = _ ++ [DF.getSym _] ++ ?x10 |- _ =>
                assert (v1e2=[] /\ x10=[])
              end.
              1:{
                inversion e0; subst; eauto; tac_inj; subst.
              }
              breakAnd; subst.

              assert (v12=[]).
              1:{     
                destruct v12; eauto.
                rmDirect.
                tac_invalid_df.
              }
              subst.

              simpl in *.


              destruct w1.
              left.
              getAnd; eauto.
              match goal with
              | h: Df (v11 ++ [Calv _]) _ (?x1 ++ [Call _]) |- _ =>
              assert (x1=[]) by
                (destruct x1; simpl in *; do 2 simplList; eauto;
                destruct x1; try discriminate)
              end.
              subst.
              simpl in *.
              assert (v11=[]).
              1:{
                destruct v11; eauto. rmDirect; tac_invalid_df.
              }
              subst.
              simpl in *.
              eauto.


              right.
              match goal with
              | h: (?s::?w1) ++[_] = ?x1 ++ [_] |- _ =>
                assert (s::w1=x1) by (tac_inj; eauto)
              end.
              subst.
              pose H3.

              exists v11.

              destruct v11.
              1:{
                match goal with
                | H26: Df ([]++_) _ _ |- _ =>
                  inversion H26; subst; tac_inj; subst; try tac_invalid_df
                end.
              }

              rmDirect.
              match goal with
              | h: Df _ ?x19 _ |- _ =>
              exists x19
              end.
              getAnd; eauto. 
              extractHead; eauto.
              getAnd; eauto. 
              match goal with
              | h: DM.Dm _ _ _ |- _ =>
                repeat rewrite <- app_assoc in h
              end.
              eauto.
            }


            (* SECTION e=Cal, v'=Pln, T=MatRet *)
            1:{
              assert (∃e v'', v'=(Plnv e)::v'').
              1:{
                match goal with
                | H33: Db _ _ _  |- _ =>
                  inversion H33; subst; simpl; eauto
                end.
              }
              breakEx; subst.


              match goal with
              | H25: v1e ++ [_] = _ ++ [Calv _] ++ _ |- _ =>
                rewrite <- H25 in e0
              end.

              match goal with
              | h: w1 ++ [Call _] = _ ++ [DF.getSym _] ++ ?x10 |- _ =>
                assert (v1e2=[] /\ x10=[])
              end.
              1:{
                inversion e0; subst; eauto; tac_inj; subst.
              }
              breakAnd; subst.

              assert (v12=[]).
              1:{     
                destruct v12; eauto.
                rmDirect.
                tac_invalid_df.
              }
              subst.

              simpl in *.

              destruct w1.
              left.
              getAnd; eauto.
              match goal with
              | h: Df (v11 ++ [Calv _]) _ (?x1 ++ [Call _]) |- _ =>
              assert (x1=[]) by
                (destruct x1; simpl in *; do 2 simplList; eauto;
                destruct x1; try discriminate)
              end.
              subst.
              simpl in *.
              
              assert (v11=[]).
              1:{
                destruct v11; eauto. rmDirect; tac_invalid_df.
              }
              subst.
              simpl in *.
              eauto.


              right.
              match goal with
              | h: (?s::?w1) ++[_] = ?x1 ++ [_] |- _ =>
                assert (s::w1=x1) by (tac_inj; eauto)
              end.
              subst.

              exists v11.

              destruct v11.
              1:{
                match goal with
                | H26: Df _ _ _ |- _ =>
                  inversion H26; subst; tac_inj; subst; try tac_invalid_df
                end.
              }

              rmDirect.
              match goal with
              | h: Df _ ?x19 _ |- _ =>
                exists x19
              end.
              getAnd; eauto.
              extractHead; eauto.
              getAnd; eauto.
              match goal with
              | h: DM.Dm _ _ _ |- _ =>
                simpl in h;
                simpl;
                repeat rewrite <- app_assoc in h;
                eauto
              end.
            }


            1:{
              match goal with
              | h: in_rules (?L2, Alt_Epsilon) P,
                h2: Df (v11 ++ [Calv ?v1a] ++ v1e2) _ _ |- _ =>
                assert (VEndWith ((v11 ++ [Calv v1a]) ++ v1e2) L2)
              end.
              1:{
                destruct v1e2.
                simpl in *; tac_inj.
                match goal with
                | h: _++[_]=_++_++?e::?v |- _ =>
                  assert (e::v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                  ; tac_inj
                  ; subst
                end.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
              }

              pose (V_Ret) as pre_cons.

              match goal with
              | h: Db v' (MatRetE ?L3 ?a2 ?L4 ?b2 ?L5 :: T) (Ret ?b2 :: _) |- _ =>
                assert (∃v'', v'=Retv (MatRetE L3 a2 L4 b2 L5)::v'')
                by (inversion h; subst; simpl; eauto)
              end.
              breakEx.
              subst.

              match goal with
              | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?e' :: ?v'') _ ((?w1 ++ [?a] ++ ?w2)++ ?w' :: _), 
                h2: Df (?v1 ++ [?ea] ++ ?v2') _ (?w1 ++ [?a] ++ ?w2') 
              |- _ =>
                pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v1 ++ [ea] ++ v2 ++ [e']) v'') as _h
                ; assert (∃ T1 w1, Df (v1 ++ [ea] ++ v2 ++ [e']) T1 w1)
                ; [apply _h; eauto |]
                ; clear _h
              end.
              repeat (simpl + (repeat rewrite <- app_assoc) + eauto).
              eauto using app_cons_not_nil.
              do 2 breakEx.


              match goal with
              | h: Df _ ?x3 ?x5,
                h3: Df (v11 ++ [Calv ?v1a]) (_ :: ?x19) (?x1 ++ [?i]),
                h4: v1e2 != [] → Df v1e2 [] ?x2 |- _ =>
                assert (x3 = x19 /\ 
                  (x5=x1 ++ [i] ++ x2 ++ [Ret b2]))
              end.
              1: {
                match goal with
                | h:Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                end.

                all: try getAnd.
                all: try getAnd.

                all: try (
                  try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  | h: Retv _ = Retv _ |- _ =>
                    inversion h
                  end; subst;
                  match goal with
                  | h: Df ?v _ _, 
                    h1: Df ?v _ _ |- _ =>
                    destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                    ; eauto
                    ; try discriminate
                    ; try simplList
                    ; eauto
                  end).

                all: try match goal with
                  | h:[_] = ?v ++ _ :: _ ++ _ ::_ |- _ =>
                    destruct v; simpl in *; simplList; tac_inj; try discriminate
                  end.

                all: try 
                  match goal with
                  | h:_ ++ [_] ++ _ = _ |- _ =>
                    rewrite <- h
                  end
                  ; simpl; subst; eauto.
                
                all: rewrite <- app_assoc; eauto.
              }
              breakAnd; subst.

              match goal with
              | h: Df (?x++?y++v1e2) (?t::?T) ?w,
                h2: Db (Retv (MatRetE ?L3 ?a2 ?L4 ?b2 ?L5) :: _) (_ :: _) (Ret ?b2 :: _),
                h3: VEndWith ((v11 ++ [Calv _]) ++ v1e2) ?L2
              |- _ =>
                assert (Df (x++y++v1e2++[Retv (MatRetE L3 a2 L4 b2 L5)]) T (w++[Ret b2])) by
                (pose V_Ret as hc;
                specialize hc with (3:=h) (L:=L2);
                repeat rewrite app_assoc in *;
                apply (hc); eauto)
              end.

              match goal with
              | h: Df (v11++_) _ _, h2: Df (v11++_) _ _ |- _ =>
                repeat rewrite app_assoc in h
                ; repeat rewrite app_assoc in h2
                ; pose (ForwardSmallStep.Df2.L_DF_Local _ _ _ _ _ h h2) as Hlocal
                ; repeat rewrite <- app_assoc in Hlocal
              end.

              match goal with
              | H19: Df ((v11 ++ [Calv _] ++ v12) ++ Retv _ :: ?x) 
                  ?x12 
                  ((_ ++ [DF.getSym _] ++ _) ++ Ret _ :: ?w) |- _ =>
                repeat rewrite <- app_assoc in H19;
                simpl in H19;
                pose (Hlocal x x12 w) as d0;
                repeat rewrite <- app_assoc in d0;
                simpl in d0;
                pose (d0 H19) as d1
              end.

              match goal with
              | h: VEndWith
              ((v11 ++ [Calv _] ++ v12) ++ Retv _ :: _) ?x13 |- _ =>
                pose (ForwardSmallStep.Core.SoundV) as _h
                ; specialize _h with (Lv:=L_0) (L:=x13) (1:=d1)
              end.
              getH. apply _h; eauto.
              1:{
                match goal with
                | h: VBeginWith (v11 ++ [Calv ?v1a] ++ ?v12) L_0
                  |- _ =>
                  rewrite app_assoc in h
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              1:{
                rewrite app_comm_cons.
                rewrite app_assoc.
                match goal with
                | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ ?e :: ?v) ?x13 |- _ =>
                  assert (e :: v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                end.

                extractEnds;
                repeat rewrite app_assoc;
                BackwardSmallStep.Core.tryResolveEnd.
              }

              match goal with
              | |- (?w1=[] /\ _) \/ _ =>
                destruct w1
              end.
              simpl in *.

              match goal with
              | h: DM.Dm _ (?x1 ++ _) _ |- _ =>
                destruct x1; simpl in *; repeat simplList; try discriminate; subst;
                destruct x1; try discriminate
              end.

              right.
              simpl.

              match goal with
              | h: DM.Dm _ _ _, 
                h2: (_ :: _) ++ [Ret _] = ?x1 ++ [_] ++ ?x2
              |- _ =>
                repeat rewrite app_comm_cons in h;
                repeat rewrite app_assoc in h;
                simpl in h2;
                rewrite <- h2 in h
              end.

              destruct v1e2; simpl in *.
              tac_inj.

              assert (v :: v1e2!=[]) as notnil by eauto using nil_cons
              ; destruct (exists_last notnil) as [? [? _s]]
              ; rewrite _s in *
              ; clear notnil _s
              ; repeat rewrite app_assoc in h.

              match goal with
              | h: v1e ++ [Retv _] = v1e1 ++ Calv ?v1ea :: _ ++ [_] 
              |- _ =>
                repeat rewrite app_comm_cons in h;
                repeat rewrite app_assoc in h;
                destruct (app_inj_tail _ _ _ _ h);
                subst
              end.

              match goal with
              | H23: ?s :: ?w1 ++ [Ret _] = ?x1 ++ Call _ :: ?x2,
                H26: Df (v11 ++ Calv (MatCalE ?L3 ?a2 ?L4 ?b2 ?L5) :: ?x0 ++ [_])
                (MatCalE ?L3 ?a2 ?L4 ?b2 ?L5 :: _) (?x1 ++ Call ?a2 :: ?x2) 
              |- _ =>
                exists (v11 ++ Calv (MatCalE L3 a2 L4 b2 L5) :: x0);
                rewrite <- H23 in H26;
                repeat rewrite app_assoc in H26;
                assert (∃ I1, Df (v11 ++ Calv (MatCalE L3 a2 L4 b2 L5) :: x0) I1 (s :: w1)) by
                (inversion H26; subst; tac_inj; subst;
                  try (match goal with
                  | h:Df _ ?T _ |- _ =>
                    exists T; eauto
                  end; fail))
              end.

              breakEx.
              match goal with
              | h: Df _ ?T _ |- _ =>
                exists T
              end.
              getAnd; eauto.
              1: {
                match goal with
                | h: VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0
                  |- _ =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e in h
                  ; clear _e
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              getAnd; eauto.
              match goal with
              | h:DM.Dm _ _ _ |- _ =>
                repeat (rewrite <- app_assoc in h + simpl in h); eauto;
                repeat (rewrite <- app_assoc + simpl); eauto
              end.
            }


            1:{
              match goal with
              | h: VBeginWith v' ?L2,
              h2: Df (v11 ++ [Calv ?v1a] ++ v1e2) _ _ |- _ =>
                assert (VEndWith ((v11 ++ [Calv v1a]) ++ v1e2) L2)
              end.
              1:{
                destruct v1e2.
                simpl in *; tac_inj.
                match goal with
                | h: _++[_]=_++_++?e::?v |- _ =>
                  assert (e::v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                  ; tac_inj
                  ; subst
                end.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
              }

              pose (V_Ret) as pre_cons.

              match goal with
              | h: Db v' (_ :: _) (Plain ?c2 :: _), h2: VBeginWith v' ?L2 |- _ =>
                assert (∃Le v'', v'=(Plnv (PlnE L2 c2 Le))::v'')
              end.
              1:{
                match goal with
                | h: Db v' (_ :: _) (Plain ?c2 :: _), h2: VBeginWith v' ?L2 |- _ =>
                  inversion h; subst; tac_inj; eauto
                end.
                
                all: simpl in *.
                Ltac getHead :=
                match goal with
                | h: VBeginWith (?e::_) ?L |- _ =>
                  assert (beginE e=L) as _h
                  by (
                    simpl; inversion h; breakAll; subst; eauto
                    ; simplList; eauto
                  )
                  ; simpl in _h
                end.

                all: getHead; subst;
                do 2 eexists; simpl; eauto.
              }
              do 2 breakEx.
              subst.

              match goal with
              | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?e' :: ?v'') _ ((?w1 ++ [?a] ++ ?w2)++ ?w' :: _), 
                h2: Df (?v1 ++ [?ea] ++ ?v2') _ (?w1 ++ [?a] ++ ?w2') 
              |- _ =>
                pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v1 ++ [ea] ++ v2 ++ [e']) v'') as _h
                ; assert (∃ T1 w1, Df (v1 ++ [ea] ++ v2 ++ [e']) T1 w1)
                ; [apply _h; eauto |]
                ; clear _h
              end.
              repeat (simpl + (repeat rewrite <- app_assoc) + eauto).
              eauto using app_cons_not_nil.
              do 2 breakEx.


              match goal with
              | h: Df _ ?x3 ?x5,
                h2: VBeginWith (Plnv ?x :: _) _,
                h3: Df (v11 ++ [Calv ?v1a]) (?v1a :: ?x19) (?x1 ++ [?i]),
                h4: v1e2 != [] → Df v1e2 [] ?x2 |- _ =>
                assert (x3 = v1a :: x19 /\ 
                (x5=x1 ++ [i] ++ x2 ++ [Plain c2]))
              end.
              1: {
                match goal with
                | h: Df _ _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                end.

                all: try getAnd.
                all: try getAnd.

                all: try (
                  try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  | h: Plnv _ = Plnv _ |- _ =>
                    inversion h
                  end; subst;
                  match goal with
                  | h: Df ?v _ _, 
                    h1: Df ?v _ _ |- _ =>
                    destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                    ; eauto
                    ; try discriminate
                    ; try simplList
                    ; eauto
                  end).

                all: try match goal with
                  | h:[_] = ?v ++ _ :: _ ++ _ ::_ |- _ =>
                    destruct v; simpl in *; simplList; tac_inj; try discriminate
                  end.

                all: try 
                match goal with
                | h: _ ++ [_] ++ _ = _ |- _ => rewrite <- h
                end;
                simpl; subst; eauto.

                all: rewrite <- app_assoc; eauto.
              }
              breakAnd; subst.

              match goal with
              | h: Df (?x1++?y++v1e2) (?t::?T) ?w,
                h2: VBeginWith (Plnv (PlnE ?L2 ?c2 ?x) :: _) _,
                H: Db _ _ _ |- _ =>
                assert (Df (x1++y++v1e2++[Plnv (PlnE L2 c2 x)]) (t::T) (w++[Plain c2]));
                [pose V_Pln as hc;
                specialize hc with (3:=h) (L:=L2);
                repeat rewrite app_assoc in *;
                apply (hc); eauto;
                inversion H; eauto |]
              end.

              match goal with
              | h: Df (v11++_) (_ :: _) _, h2: Df (v11++_) (_ :: _) _ |- _ =>
                repeat rewrite app_assoc in h
                ; repeat rewrite app_assoc in h2
                ; pose (ForwardSmallStep.Df2.L_DF_Local _ _ _ _ _ h h2) as Hlocal
                ; repeat rewrite <- app_assoc in Hlocal
              end.

              match goal with
              | h: Df ((v11 ++ [Calv ?v1a] ++ v12) ++ Plnv _ :: ?x0) ?x12
                ((?x1 ++ [DF.getSym ?v1a] ++ ?x2) ++ Plain _ :: ?w) 
              |- _ =>
                repeat rewrite <- app_assoc in h;
                simpl in h;
                pose (Hlocal x0 x12 w) as d0;
                repeat rewrite <- app_assoc in d0;
                simpl in d0;
                pose (d0 h)
              end.


              match goal with
              | d1: Df _ _ _, 
                h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ Plnv _ :: _) ?x13 |- _ =>
                pose (ForwardSmallStep.Core.SoundV) as _h
                ; specialize _h with (Lv:=L_0) (L:=x13) (1:=d1)
              end.
              getH. apply _h; eauto.

              1:{
                match goal with
                | h: VBeginWith (v11 ++ [Calv ?v1a] ++ ?v12) L_0
                  |- _ =>
                  rewrite app_assoc in h
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              1:{
                rewrite app_comm_cons.
                rewrite app_assoc.
                match goal with
                | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ ?e :: ?v) ?x13 |- _ =>
                  assert (e :: v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                end.

                extractEnds;
                repeat rewrite app_assoc;
                BackwardSmallStep.Core.tryResolveEnd.
              }

              match goal with
              | |- (?w1=[] /\ _) \/ _ =>
                destruct w1
              end.

              simpl in *.

              match goal with
              | h:DM.Dm _ (?x1 ++ _) _ |- _ =>
                destruct x1; simpl in *; repeat simplList; try discriminate; subst;
                simpl in *; eauto; try discriminate;
                destruct x1; try discriminate
              end.

              right.
              simpl.

              match goal with
              | h: (s :: _) ++ [Ret _] = _ ++ _ ++ _,
                h2: DM.Dm _ _ _ |- _ =>
                repeat rewrite app_comm_cons in h2;
                repeat rewrite app_assoc in h2;
                simpl in h;
                rewrite <- h in h2
              end.

              destruct v1e2; simpl in *.
              tac_inj.




              assert (v :: v1e2!=[]) as notnil by eauto using nil_cons
              ; destruct (exists_last notnil) as [? [? _s]]
              ; rewrite _s in *
              ; clear notnil _s
              ; repeat rewrite app_assoc in h.

              match goal with
              | h: v1e ++ [Retv _] = v1e1 ++ Calv _ :: _ ++ [_] |- _ =>
                repeat rewrite app_comm_cons in h;
                repeat rewrite app_assoc in h;
                destruct (app_inj_tail _ _ _ _ h);
                subst
              end.

              match goal with
              | h: DM.Dm _ _ ((?v11 ++ Calv ?v1a :: ?x3 ++ _) ++ _) |- _ =>
                exists (v11 ++ Calv v1a :: x3)
              end.
              match goal with
              | H23: s :: ?w1 ++ [Ret _] = ?x1 ++ Call ?a :: ?x2,
                H26: Df (v11 ++ Calv ?v1a :: _ ++ [Retv _]) 
                  (?v1a :: _) (?x1 ++ Call ?a :: ?x2) |- _ =>
                rewrite <- H23 in H26
                ; repeat rewrite app_assoc in H26
                ; match goal with
                  | h: DM.Dm _ _ ((_++_::?x3++[_])++_) |- _ =>
                    assert (∃ I1, Df (v11 ++ Calv v1a :: x3) I1 (s :: w1)) by
                    match goal with
                    | h:Df (v11 ++ Calv ?v1a :: _ ++ [Retv _]) 
                      (?v1a :: _) (s :: ?w1 ++ [Ret _]) |- _ =>
                      inversion h; subst; tac_inj; subst;
                      try (match goal with
                      | h:Df _ ?T _ |- _ =>
                        exists T; eauto
                      end; fail)
                    end
                end
              end.

              
              breakEx.
              match goal with
              | h: Df _ ?T _ |- _ =>
                exists T
              end.
              getAnd; eauto.
              1: {
                match goal with
                | h: VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0
                  |- _ =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e in h
                  ; clear _e
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              getAnd; eauto.
              match goal with
              | H30: DM.Dm _ _ _ |- _ =>
                repeat (rewrite <- app_assoc in H30 + simpl in H30); eauto;
                repeat (rewrite <- app_assoc + simpl); eauto
              end.
            }


            1:{
              match goal with
              | h: VBeginWith v' ?L2,
              h2: Df (v11 ++ [Calv ?v1a] ++ v1e2) _ _ |- _ =>
                assert (VEndWith ((v11 ++ [Calv v1a]) ++ v1e2) L2)
              end.
              1:{
                destruct v1e2.
                simpl in *; tac_inj.
                match goal with
                | h: _++[_]=_++_++?e::?v |- _ =>
                  assert (e::v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                  ; tac_inj
                  ; subst
                end.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
                repeat rewrite app_assoc.
                BackwardSmallStep.Core.tryResolveEnd.
              }

              pose (V_Ret) as pre_cons.


              match goal with
              | h: Db (Retv (MatRetE _ _ _ _ ?L2) :: v')
                (MatRetE _ _ _ _ ?L2 :: _ :: T)
                (Ret _ :: Call ?a3 :: _) |- _ =>
                assert (∃ d3 d4 d5 v'', v'=(Calv (MatCalE L2 a3 d3 d4 d5))::v'')
              end.
              1:{
                match goal with
                | h: Db v' (MatRetE _ _ _ _ _ :: T) (Call _ :: _) |- _ =>
                  inversion h; subst; tac_inj; eauto
                end.

                all: try (simpl in *; getHead; subst;
                  repeat addEx; simpl; eauto; fail).
                
                match goal with
                | h:Db ?x (PndRetE ?v1 ?v2 ?v3::MatRetE ?q1 ?q2 ?q3 ?q4 ?q5 ::?T) ?w |- _ =>
                  pose (BackwardSmallStep.Core.L4_2 x (PndRetE v1 v2 v3::MatRetE q1 q2 q3 q4 q5 ::T) w) as _h
                  ; inversion _h
                end;
                rmDirect;
                breakAll; subst; try discriminate;
                do 2 match goal with
                | h: PendT _ |- _ =>
                  inversion h; breakAll; simplList; subst
                end.

              }

              do 4 breakEx.
              subst.

              match goal with
              | h: Df ((?v1 ++ [?ea] ++ ?v2) ++ ?e' :: ?v'') _ ((?w1 ++ [?a] ++ ?w2)++ ?w' :: _), 
                h2: Df (?v1 ++ [?ea] ++ ?v2') _ (?w1 ++ [?a] ++ ?w2') 
              |- _ =>
                pose (ForwardSmallStep.Split.DF_SPLIT _ _ _ h (v1 ++ [ea] ++ v2 ++ [e']) v'') as _h
                ; assert (∃ T1 w1, Df (v1 ++ [ea] ++ v2 ++ [e']) T1 w1)
                ; [apply _h; eauto |]
                ; clear _h
              end.
              repeat (simpl + (repeat rewrite <- app_assoc) + eauto).
              eauto using app_cons_not_nil.
              do 2 breakEx.



              match goal with
              | h: Df (_++?y++v1e2) (?t::?T) ?w,
                h2: VBeginWith (Calv (MatCalE ?L2 ?a3 ?x ?x0 ?x3) :: ?x5) ?L2,
                h3: Df (_++[_]++_++[_]) ?x6 ?x7,
                h4: Df (v11 ++ [Calv ?v1a]) (?v1a :: ?x19) (?x1 ++ [?i]),
                h5: v1e2 != [] → Df v1e2 [] ?x2 |- _ =>
                assert (x6=(MatCalE L2 a3 x x0 x3)::v1a::T /\ 
                  (x7=(x1 ++ [i] ++ x2) ++ [Call a3]))
              end.
              1: {
                match goal with
                | h: Df (_++[_]++_++[_]) _ _ |- _ =>
                  inversion h; subst; tac_inj; subst
                end.

                all: try getAnd.
                all: try getAnd.

                all: try (
                  try match goal with
                  | h: Calv _ = Calv _ |- _ =>
                    inversion h
                  end; subst;
                  match goal with
                  | h: Df ?v _ _, 
                    h1: Df ?v _ _ |- _ =>
                    destruct (ForwardSmallStep.Df2.L_Df_unique _ _ _ _ _ h h1)
                    ; eauto
                    ; try discriminate
                    ; try simplList
                    ; eauto
                  end).

                all: try match goal with
                  | h:[_] = ?v ++ _ :: _ ++ _ ::_ |- _ =>
                    destruct v; simpl in *; simplList; tac_inj; try discriminate
                  end.

                all: try 
                match goal with
                | h: _ ++ [_] ++ _ = _ |- _ =>
                  rewrite <- h
                end ; simpl; subst; eauto.
              }
              breakAnd; subst.

              match goal with
              | h: Df (?x1++?y++v1e2) (?t::?T) ?w,
                h2: VBeginWith (Calv (MatCalE ?L2 ?a3 ?x ?x0 ?x3) :: ?x5) ?L2 |- _ =>
                assert (Df (x1++y++v1e2++[Calv (MatCalE L2 a3 x x0 x3)]) 
                  ((MatCalE L2 a3 x x0 x3)::t::T) (w++[Call a3]));
                pose V_Cal as hc;
                specialize hc with (3:=h) (L:=L2);
                [repeat rewrite app_assoc in *; apply (hc); eauto |]
              end.

              1:{
                match goal with
                | h: Db _ _ _|- in_rules _ _ =>
                  inversion h; subst
                end;
                match goal with
                | h: Db _ (MatRetE ?L2 ?a3 ?x ?x0 ?x3 :: _) _|- in_rules _ _ =>
                apply (Db_rule _ _ _ h) with (T':=MatRetE L3 a2 L4 b2 L5::T)
                ; eauto
                end.
              }


              match goal with
              | h: Df (v11++_) (_ :: _ :: _) _, h2: Df (v11++_) (_ :: _ :: _) _ |- _ =>
                repeat rewrite app_assoc in h
                ; repeat rewrite app_assoc in h2
                ; pose (ForwardSmallStep.Df2.L_DF_Local _ _ _ _ _ h h2) as Hlocal
                ; repeat rewrite <- app_assoc in Hlocal
              end.
              match goal with
              | H19: Df ((v11 ++ [Calv ?v1a] ++ v12) ++ Calv (MatCalE L2 ?a3 _ _ _) :: ?x5)
                ?x12 ((?x1 ++ [DF.getSym ?v1a] ++ ?x2) ++ Call ?a3 :: ?w) |- _ =>
                repeat rewrite <- app_assoc in H19;
                simpl in H19;
                pose (Hlocal x5 x12 w) as d0;
                repeat rewrite <- app_assoc in d0;
                simpl in d0;
                pose (d0 H19)
              end.


              match goal with
              | h:VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ _ :: _) ?x13, 
                d1: Df _ _ _ |- _ =>
                pose (ForwardSmallStep.Core.SoundV) as _h
                ; specialize _h with (Lv:=L_0) (L:=x13) (1:=d1)
              end.
              getH. apply _h; eauto.
              1:{
                match goal with
                | h: VBeginWith (v11 ++ [Calv ?v1a] ++ ?v12) L_0
                  |- _ =>
                  rewrite app_assoc in h
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              1:{
                rewrite app_comm_cons.
                rewrite app_assoc.
                match goal with
                | h: VEndWith ((v11 ++ [Calv ?v1a] ++ v12) ++ ?e :: ?v) ?x13 |- _ =>
                  assert (e :: v!=[]) as notnil by eauto using nil_cons
                  ; destruct (exists_last notnil) as [? [? _s]]
                  ; rewrite _s in *
                  ; clear notnil _s
                  ; repeat rewrite app_assoc in h
                end.

                extractEnds;
                repeat rewrite app_assoc;
                BackwardSmallStep.Core.tryResolveEnd.
              }


              match goal with
              | |- (?w1=[] /\ _) \/ _ =>
                destruct w1
              end.
              simpl in *.

              match goal with
              | h:DM.Dm _ (?x1++ _) _ |- _ =>
                destruct x1; simpl in *; repeat simplList; try discriminate; subst;
                simpl in *; eauto; try discriminate;
                destruct x1; try discriminate
              end.

              right.
              simpl.

              match goal with
              | h:DM.Dm _ _ _, h2: (s :: ?w1) ++ [_] = _ ++ [_] ++ _ |- _ =>
                repeat rewrite app_comm_cons in h;
                repeat rewrite app_assoc in h;
                simpl in h2;
                rewrite <- h2 in h
              end.

              destruct v1e2; simpl in *.
              tac_inj.


              assert (v :: v1e2!=[]) as notnil by eauto using nil_cons
              ; destruct (exists_last notnil) as [? [? _s]]
              ; rewrite _s in *
              ; clear notnil _s.

              match goal with
              | h: v1e++[_]=_++_::_++[_] |- _ =>
                repeat rewrite app_comm_cons in h;
                repeat rewrite app_assoc in h;
                destruct (app_inj_tail _ _ _ _ h);
                subst
              end.

              match goal with
              | h: DM.Dm _ _ ((?v11 ++ Calv ?v1a :: ?x3 ++ _) ++ _) |- _ =>
                exists (v11 ++ Calv v1a :: x3)
              end.
              match goal with
              | h: s::?w1++[_]=_++_::_, h2: Df (_++_::_++[_]) (?v1a::_) (_++_::_) |- _ =>
                rewrite <- h in h2
                ; repeat rewrite app_assoc in h2
              end.

              match goal with
              | h:DM.Dm _ (?s :: (?w1 ++ [Ret _]) ++ Call _ :: _) ((_ ++ Calv ?v1a :: ?x6 ++ _) ++ _) |- _ =>
                assert (∃ I1, Df (v11 ++ Calv v1a :: x6) I1 (s :: w1))
              end.
              match goal with
              | h: Df _ (?v1a::_) (?s::?w1 ++ [_]) |- _ =>
                inversion h; subst; tac_inj; subst;
                try (match goal with
                | h:Df _ ?T _ |- _ =>
                  exists T; eauto
                end; fail)
              end.

              breakEx.
              match goal with
              | h: Df _ ?T _ |- _ =>
                exists T
              end.
              getAnd; eauto.
              1: {
                match goal with
                | h: VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0
                  |- _ =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e in h
                  ; clear _e
                end.

                match goal with
                | |- VBeginWith (v11 ++ Calv ?v1a :: ?v12) L_0 =>
                  assert (v11 ++ Calv v1a :: v12=
                  (v11 ++ [Calv v1a]) ++ v12) as _e by
                  (rewrite <- app_assoc; eauto)
                  ; rewrite _e
                  ; clear _e
                end.

                extractHead.
                apply (VListBeginSame2); eauto.
              }
              getAnd; eauto.
              match goal with
              | h:DM.Dm _ _ _ |- _ => 
                repeat (rewrite <- app_assoc in h + simpl in h); eauto
              end.
              repeat (rewrite <- app_assoc + simpl); eauto.
            }

          }

        }



        breakAll; subst.

        1:{
          assert (∃ e v' T', v=e::v' /\ Db v' T' w2) as Hex.
          1:{
            match goal with
            | h:Db v I _ |- _ =>
              inversion h; subst
            end;
            try match goal with
            | h: Extract _ _ _ [] |- _ =>
              inversion H
            end;
            simpl;
            do 3 eexists; 
            getAnd; eauto.
          }
          destruct Hex as [e [v' [T' [? Hdb]]]].
          subst.

          match goal with
          | h: Db ?v ?T _ |- _ =>
            destruct (IHExtract T v) as [_ ?]
          end.

          assert (∃ T1, Df [e] T1 [i]).
          1:{
            pose (ForwardSmallStep.Core.CompleteM) as d0.
            specialize d0 with (1:=H0).
            getH. tac_app. eauto using nil_cons.
            breakAll; subst;

            match goal with
            | h: Df (?e :: ?v') _ (?i :: ?w2)
            |- _ =>
              pose (ForwardSmallStep.Split.DF_SPLIT2 _ _ _ h [e] v') as _h
              ; getH
              ; [apply _h; eauto using nil_cons |]
              ; clear _h
            end;
            breakAll;
            match goal with
            | h:Df [e] ?x ?x0 |- _ =>
              exists x;
              assert (x0=[i]) by
              match goal with
              | h:Df [_] _ _ |- _ =>
              inversion h; subst; simpl in *;
              try (simplList; subst); eauto
              ; tac_inj; subst; eauto
              ; tac_invalid_df
              end;
              subst; eauto
            end.
          }
          breakEx.

          getH. tac_app.

          getAnd; eauto. right.

          match goal with
          | h:Df [e] ?T [i] |- _ =>
            exists [e], T
          end.
          split; auto.
          match goal with
          | h:DM.Dm _ _ _ |- _ =>
            inversion h; tryResolveBegin
          end.

          pose (pf1_sub) as a.
          specialize a with (1:=H).
          breakAll.

          simpl in *.
          pose (ForwardSmallStep.DFX.DF_dfx) as a1.
          specialize a1 with (1:=H3).
          breakAll.
          pose (PForest1) as a2.
          specialize a2 with (1:=a) (v:=[]) (2:=a1) (Le:=endE e).
          getH. apply a2. simpl.
          1:{
            inversion H0; subst; tryResolveBegin.
          }
          resolveEndESelf.
          clear a2.
          breakAll; subst.

          1:{
            destruct m.
            1:{
              simpl in H7.
              destruct e; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              

              exists (v', T').
              getAnd; eauto.
              apply_in_map.
              exists va.
              getAnd; eauto.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.
              apply_filter_map.
              exists (None, va);
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              getAnd; eauto.


              destruct T'.
              1:{
                destruct v'.
                tac_invalid_db.
                destruct va.
                1:{
                  inversion H1; subst;
                  getHead; subst;
                  apply vvot.eqb_eq; eauto.
                }
                1:{
                  simpl;
                  inversion H1; subst; eauto;
                  pose L_Db_uniqueT as h;
                  match goal with
                  | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                    specialize h with (1:=h1) (2:=h2)
                  end;
                  discriminate.
                }
              }

              assert ([i]!=[]) as Hw by eauto using nil_cons.
              destruct va;
              invalid_ma.
            }

            1:{
              simpl in H7.
              destruct e; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              

              exists (v', T').
              getAnd; eauto.
              apply_in_map.
              exists vc.
              getAnd; eauto.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.
              apply_filter_map.
              exists (None, vc);
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              getAnd.

              2:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }


              destruct T'.
              1:{
                destruct v'.
                tac_invalid_db.
                destruct vc.
                1:{
                  inversion H1; subst;
                  try match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto; fail
                  end.
                  1,2: inversion H15; breakAll; subst; simplList; simpl;
                  apply vvot.eqb_eq; eauto.
                }
              }

              destruct r.
              destruct vc.
              destruct v'; try tac_invalid_db.


              1:{
                inversion H1; subst; try tac_invalid_db.
                1,2: match goal with
                | h:Db _ _ (Ret _::_) |- _ =>
                  inversion h; subst; eauto
                  ; simpl; apply vvot.eqb_eq; eauto
                end;
                inversion Hdb; subst; eauto.
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end.
                1,2: getHead; subst;
                apply vvot.eqb_eq; eauto.
              }


              exfalso.
              inversion H0; subst.
              pose (BackwardSmallStep.Core.CompleteM) as d0.
              specialize d0 with (1:=H13).
              getH. tac_app; 
              eauto using nil_cons, app_cons_not_nil.
              destruct w2; try tac_invalid_db; eauto using nil_cons.
              breakAll; subst.
              

              match goal with
              | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                pose L_Db_uniqueT as h;
                specialize h with (1:=h1) (2:=h2)
              end.
              subst.
              inversion H8.
              breakAll; discriminate.

            }

            1:{
              simpl in H7.
              destruct e; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.

              exists (v', T').
              getAnd; eauto.
              apply_in_map.
              exists vb.
              getAnd; eauto.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.
              apply_filter_map.
              exists (None, vb);
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              getAnd.

              2:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }

              destruct T'.
              1:{
                destruct v'.
                tac_invalid_db.
                destruct vb.
                1:{
                  inversion H1; subst;
                  try match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto; fail
                  end.
                  1,2: inversion H15; breakAll; subst; simplList; simpl;
                  apply vvot.eqb_eq; eauto.
                }

                1:{
                  inversion H1; subst;
                  try match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto; fail
                  end;inversion H17; breakAll; subst; simplList; simpl;
                  apply vvot.eqb_eq; eauto.
                }
              }

              destruct r.
              destruct vb;
              destruct v'; try tac_invalid_db.


              1:{
                inversion H1; subst; try tac_invalid_db.
                match goal with
                | h:Db _ _ (Ret _::_) |- _ =>
                  inversion h; subst; eauto
                  ; simpl; apply vvot.eqb_eq; eauto
                end;
                inversion Hdb; subst; eauto;
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end.
                all: getHead; subst;
                simpl;
                apply vvot.eqb_eq; eauto.
                all: apply vvot.eqb_eq; eauto.
              }
              1:{
                inversion H1; subst; try tac_invalid_db;
                match goal with
                | h:Db _ _ (Ret _::_) |- _ =>
                  inversion h; subst; eauto
                  ; simpl; apply vvot.eqb_eq; eauto
                end;
                inversion Hdb; subst; eauto;
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end.
                
                all: try getHead; subst;
                simpl;
                apply vvot.eqb_eq; eauto.
                all: apply vvot.eqb_eq; eauto.
                all: match goal with
                | h: VBeginWith (?e::_) ?L |- _ =>
                    simpl; inversion h; breakAll; subst; eauto
                    ; repeat simplList; eauto
                end.
              }

              exfalso.
              inversion H0; subst.
              pose (BackwardSmallStep.Core.CompleteM) as d0.
              specialize d0 with (1:=H13).
              getH. tac_app; 
              eauto using nil_cons, app_cons_not_nil.
              destruct w2; try tac_invalid_db; eauto using nil_cons.
              breakAll; subst.
              

              match goal with
              | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                pose L_Db_uniqueT as h;
                specialize h with (1:=h1) (2:=h2)
              end.
              subst.
              inversion H8.
              breakAll; discriminate.
            }

          }

          1:{
            inversion a1; subst; tac_inj; subst; try tac_invalid_dfx;
            inversion H5; subst; tac_inj.
            1:{
              simpl in H7.
              destruct m; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              getAnd; eauto.
              


              simpl.
              apply_in_map.
              addEx.
              getAnd; eauto.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.
              apply_filter_map.
              match goal with
              | h:va_set.In (?x, ?y) ma |- _ =>
                exists (x, y)
              end.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

              getAnd; eauto.


              destruct T'.
              1:{
                destruct v'.
                tac_invalid_db.
                1:{
                  inversion H1; subst;
                  getHead; subst;
                  apply vvot.eqb_eq; eauto.
                }

              }

              destruct r.
              1:{
                destruct v'.
                tac_invalid_db.
                1:{
                  inversion H1; subst;
                  getHead; subst;
                  apply vvot.eqb_eq; eauto.
                }

              }

              exfalso.
              inversion H0; subst.
              pose (BackwardSmallStep.Core.CompleteM) as d0.
              specialize d0 with (1:=H15).
              getH. tac_app; 
              eauto using nil_cons, app_cons_not_nil.
              destruct w2; try tac_invalid_db; eauto using nil_cons.
              breakAll; subst.
              

              match goal with
              | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                pose L_Db_uniqueT as h;
                specialize h with (1:=h1) (2:=h2)
              end.
              subst.
              inversion H9.
              breakAll; discriminate.
            }

            1:{
              simpl in H7.
              destruct m; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              getAnd; eauto.
              


              simpl.
              apply_in_map.
              addEx. getAnd.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.
              apply_filter_map.
              match goal with
              | h:va_set.In (?x, ?y) ma |- _ =>
                exists (x, y)
              end.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

              getAnd; eauto.

              destruct T'.
              1:{
                simpl;
                inversion H1; subst; eauto;
                pose L_Db_uniqueT as h; try tac_invalid_db;
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  specialize h with (1:=h1) (2:=h2)
                end;
                try discriminate
                ;subst ;eauto.
              }



              destruct r.
              1:{
                simpl;
                inversion H1; subst; eauto;
                pose L_Db_uniqueT as h; try tac_invalid_db;
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  specialize h with (1:=h1) (2:=h2)
                end;
                try discriminate
                ;subst ;eauto.
              }

              apply andb_true_iff.
              getAnd.
              inversion H1; subst; eauto;
              pose L_Db_uniqueT as h; try tac_invalid_db;
              match goal with
              | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                specialize h with (1:=h1) (2:=h2)
              end;
              try discriminate
              ; subst; eauto
              ; simplList; subst;

              repeat (getAnd + rewrite L_eq_str+ (apply vvot.eqb_eq; eauto) +
              apply andb_true_iff + (apply String.eqb_eq; eauto)).

              destruct v'.
              tac_invalid_db.
              destruct v.
    
              1:{
                simpl;
                inversion H1; subst; eauto; try tac_invalid_db;
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end;

                simplList; eauto; subst; eauto; destruct va.

                all: try match goal with
                | h:Db _ _ _ |- _ =>
                  inversion h; fail
                end.

                1:{
                  match goal with
                  | h: Db ?v ?T ?w |- _ =>
                    pose (BackwardSmallStep.Core.L4_2 v T w) as b0
                  end.
                  inversion b0.
                  rmDirect.

                  breakAll; subst; tac_inj; subst; try discriminate;
                  try match goal with
                  | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
                    inversion h; breakAll; subst; discriminate
                  end.
                  simplList; subst.
                  simplList; subst.
                  1:{
                    inversion Hdb; subst.
                    match goal with
                    | h: Db ?v ?T ?w |- _ =>
                      pose (BackwardSmallStep.Core.L4_2 v T w) as aa
                    end.
                    inversion aa.
                    rmDirect.
    
                    breakAll; subst; tac_inj; subst; try discriminate;
                    try match goal with
                    | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
                      inversion h; breakAll; subst; discriminate
                    end.
                    match goal with
                    | h:PendT _ |- _ =>
                      inversion h; breakAll
                    end.
                    match goal with
                    | h:[_;_]=_ |- _ =>
                      inversion h; subst
                    end.
                    match goal with
                    | h:PendT _ |- _ =>
                      inversion h; breakAll
                    end.
                    breakAll; discriminate.
                  }
                  1:{
                    inversion Hdb; subst.
                    match goal with
                    | h: Db ?v ?T ?w |- _ =>
                      pose (BackwardSmallStep.Core.L4_2 v T w) as aa
                    end.
                    inversion aa.
                    rmDirect.
    
                    breakAll; subst; tac_inj; subst; try discriminate;
                    try match goal with
                    | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
                      inversion h; breakAll; subst; discriminate
                    end.
                    match goal with
                    | h:PendT _ |- _ =>
                      inversion h; breakAll
                    end.
                    match goal with
                    | h:_::_=_ |- _ =>
                      inversion h; subst
                    end.
                    match goal with
                    | h:PendT _ |- _ =>
                      inversion h; breakAll
                    end.
                    breakAll; discriminate.
                  }

                  1:{
                    inversion Hdb; subst.
                    match goal with
                    | h: Db ?v ?T ?w |- _ =>
                      pose (BackwardSmallStep.Core.L4_2 v T w) as aa
                    end.
                    inversion aa.
                    rmDirect.
    
                    breakAll; subst; tac_inj; subst; try discriminate;
                    try match goal with
                    | h: PendT (MatRetE _ _ _ _ _:: _) |- _ =>
                      inversion h; breakAll; subst; discriminate
                    end.
                    match goal with
                    | h:PendT _ |- _ =>
                      inversion h; breakAll
                    end.
                    match goal with
                    | h:_::_=_ |- _ =>
                      inversion h; subst
                    end.
                    match goal with
                    | h:PendT _ |- _ =>
                      inversion h; breakAll
                    end.
                    breakAll; discriminate.
                  }
                }

                inversion H15; breakAll; subst; simplList; apply vvot.eqb_eq; eauto.
              }

              1:{
                destruct vc; simpl.
                inversion H1; subst; eauto; try tac_invalid_db.
                inversion Hdb.
                inversion H15; breakAll; subst; simplList; apply vvot.eqb_eq; eauto.
                inversion H15; breakAll; subst; simplList; apply vvot.eqb_eq; eauto.
              }
              apply L_goEps; simpl; eauto.
              1:{
                inversion H1; subst; eauto; try tac_invalid_db;
                match goal with
                | h:Db _ _ _ |- _ =>
                  inversion h 
                end.
              }
            }
          }
        }

        1:{
          assert (∃ e v' T', v=e::v' 
            /\ Db v' T' w2) as Hex.
          1:{
            match goal with
            | h:Db v I _ |- _ =>
              inversion h; subst
            end;
            try match goal with
            | h: Extract _ _ _ [] |- _ =>
              inversion H
            end;
            simpl;
            do 3 eexists; 
            getAnd; eauto.
          }

          breakAll; subst.

          assert (∃ T, Df (x++[x1]) T (w1++[i])).
          1:{
            pose (ForwardSmallStep.Core.CompleteM) as d0.
            specialize d0 with (1:=H0).
            getH. tac_app; 
            eauto using nil_cons, app_cons_not_nil.

            breakAll; subst;

            match goal with
            | h: Df (?x ++ ?e :: ?v') _ (?w1 ++ ?i :: ?w2)
            |- _ =>
              pose (ForwardSmallStep.Split.DF_SPLIT2 _ _ _ h (x++[e]) v') as _h
              ; getH
              ; [apply _h; eauto using nil_cons, app_cons_not_nil |]
              ; clear _h
            end;
            breakAll;
            try rewrite <- app_assoc; eauto;
            match goal with
            | h:Df _ ?x ?x0 |- _ =>
            exists x
            ; assert (x0=w1++[i])
            end.

            1:{
              pose (TimedSets.Parser.PreTimed.Dbx.L_Db_vw _ _ _ Hex).
              match goal with
              | h: Df (x ++ x1 :: x2) [] (w1 ++ i :: w2) |- _ =>
              pose (ForwardSmallStep.Df2.L_Df_vw _ _ _ h) as h1
              ; pose (app_length (x++[x1]) x2) as r1
              ; rewrite <- app_assoc in r1
              ; simpl in r1
              ; rewrite r1 in h1
              ; clear r1
              ; pose (app_length (w1++[i]) w2) as r1
              ; rewrite <- app_assoc in r1
              ; simpl in r1
              ; rewrite r1 in h1
              ; clear r1
              end.

              assert (Datatypes.length (x ++ [x1]) = Datatypes.length (w1 ++ [i])) as e0.
              lia.

              pose (ForwardSmallStep.Df2.L_Df_vw _ _ _ H7) as e1.
              rewrite e1 in e0.



              match goal with
              | h: ?a + ?b = ?c + ?d,
                h2: ?x5 ++ ?x6 = ?w1 ++ ?i :: ?w2 |- _ =>
                pose (list_inj x5 x6 (w1++[i]) w2) as _h
                ; rewrite <- app_assoc in _h
                ; rmDirect
                ; getH; [tac_app |]
              end.
              rewrite <- e0. eauto. eauto.
            }

            subst; eauto.
            1:{
              pose (TimedSets.Parser.PreTimed.Dbx.L_Db_vw _ _ _ Hex).
              match goal with
              | h: Df (x ++ x1 :: x2) _ (w1 ++ i :: w2) |- _ =>
              pose (ForwardSmallStep.Df2.L_Df_vw _ _ _ h) as h1
              ; pose (app_length (x++[x1]) x2) as r1
              ; rewrite <- app_assoc in r1
              ; simpl in r1
              ; rewrite r1 in h1
              ; clear r1
              ; pose (app_length (w1++[i]) w2) as r1
              ; rewrite <- app_assoc in r1
              ; simpl in r1
              ; rewrite r1 in h1
              ; clear r1
              end.

              assert (Datatypes.length (x ++ [x1]) = Datatypes.length (w1 ++ [i])) as e0.
              lia.

              pose (ForwardSmallStep.Df2.L_Df_vw _ _ _ H7) as e1.
              rewrite e1 in e0.

              match goal with
              | h: ?a + ?b = ?c + ?d,
                h2: ?x5 ++ ?x6 = ?w1 ++ ?i :: ?w2 |- _ =>
                pose (list_inj x5 x6 (w1++[i]) w2) as _h
                ; rewrite <- app_assoc in _h
                ; rmDirect
                ; getH; [tac_app |]
              end.
              rewrite <- e0. eauto. eauto.
            }

            subst; eauto.
          }
          breakEx.

          match goal with
          | h: Db ?v ?T _ |- _ =>
            destruct (IHExtract T v) as [_ ?]
          end.

          getH. tac_app.

          getAnd; eauto. right.
          match goal with
          | h:Df ?v ?T (w1++[i]) |- _ =>
          exists v, T
          end.
          split; auto.
          apply (VListBeginSame2); eauto.
          split; auto.
          do 2 rewrite <- app_assoc; eauto.
          clear H5.


          pose (pf1_sub) as a.
          specialize a with (1:=H).
          breakAll.

          simpl in *.
          pose (ForwardSmallStep.DFX.DF_dfx) as a1.
          specialize a1 with (1:=H4).
          breakAll.
          pose (PForest1) as a2.
          specialize a2 with (1:=a) (2:=a1) (Le:=endE x1).
          getH. apply a2.
          1:{
            assert (x ++ x1 :: x2=(x ++ [x1]) ++ x2) as rw by 
              (rewrite <- app_assoc; eauto).
            rewrite rw in H0.
            inversion H0; subst; tryResolveBegin;
            try match goal with
            | h:[] = ?v ++ _ :: _ |- _ =>
              destruct v; simpl in *; try simplList; tac_inj; try discriminate
            end;
            apply VListBeginSame with (v1:=x2); eauto using app_cons_not_nil
            ; rewrite <- H7;
            tryResolveBegin.
          }
          resolveEndESelf.
          clear a2.
          breakAll; subst.

          1:{
            rename x2 into v'.
            rename x3 into T'.
            destruct m.
            1:{
              simpl in H8.
              destruct x1; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.

              apply_in_map.
              addEx. getAnd.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.
              apply_filter_map.
              addEx.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.


              getAnd; eauto.

              destruct T'.
              1:{
                destruct v'.
                tac_invalid_db.
                destruct va.
                1:{
                  inversion H1; subst;
                  getHead; subst;
                  apply vvot.eqb_eq; eauto.
                }
                1:{
                  simpl;
                  inversion H1; subst; eauto;
                  pose L_Db_uniqueT as h;
                  match goal with
                  | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                    specialize h with (1:=h1) (2:=h2)
                  end;
                  discriminate.
                }

              }

              assert (w1++[i]!=[]) as Hw by eauto using app_cons_not_nil.
              destruct va; invalid_ma.
            }

            1:{
              simpl in H8.
              destruct x1; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.

              apply_in_map.
              addEx. getAnd.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.
              apply_filter_map.
              addEx.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.


              getAnd; eauto.

              destruct T'.
              1:{
                destruct v'.
                tac_invalid_db.
                destruct vc.
                1:{
                  inversion H1; subst;
                  try match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto; fail
                  end.
                  1,2: inversion H16; breakAll; subst; simplList; simpl;
                  apply vvot.eqb_eq; eauto.
                }

              }

              destruct r.
              destruct vc.

              destruct v'; try tac_invalid_db.

              1:{
                inversion H1; subst; try tac_invalid_db.
                1,2: match goal with
                | h:Db _ _ (Ret _::_) |- _ =>
                  inversion h; subst; eauto
                  ; simpl; apply vvot.eqb_eq; eauto
                end;
                inversion Hex; subst; eauto.
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end.
                1,2: getHead; subst;
                apply vvot.eqb_eq; eauto.
              }


              exfalso.
              match goal with
              | h:Db ?v (MatRetE _ _ _ _ _:: _) ?w,
                h2: Df _ [] _ |- _ =>
                pose (L_invalid_comb) as f;
                specialize f with (1:=h) (2:=h2)
                ; apply f; repeat rewrite <- app_assoc; eauto
              end.
            }

            1:{
              simpl in H8.
              destruct x1; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.

              apply_in_map.
              addEx. getAnd.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.

              apply_filter_map.
              addEx.
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.


              getAnd; eauto.


              destruct T'.
              1:{
                destruct v'.
                tac_invalid_db.
                destruct vb.
                1:{
                  inversion H1; subst;
                  try match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto; fail
                  end.
                  1,2: inversion H16; breakAll; subst; simplList; simpl;
                  apply vvot.eqb_eq; eauto.
                }



                1:{
                  simpl;
                  inversion H1; subst; eauto;
                  pose L_Db_uniqueT as h;
                  match goal with
                  | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                    specialize h with (1:=h1) (2:=h2)
                  end;
                  try discriminate
                  ;subst ;eauto.

                  getHead; subst.
                  apply vvot.eqb_eq; eauto.
                }
              }

              destruct r.
              destruct vb.

              destruct v'; try tac_invalid_db.

              1:{
                inversion H1; subst; try tac_invalid_db;
                match goal with
                | h:Db _ _ (Ret _::_) |- _ =>
                  inversion h; subst; eauto
                  ; simpl; apply vvot.eqb_eq; eauto
                end;
                inversion Hex; subst; eauto;
                simpl; getHead; subst; eauto.
              }


              destruct v'; try tac_invalid_db.
              1:{
                inversion H1; subst; try tac_invalid_db;
                match goal with
                | h:Db _ _ (Ret _::_) |- _ =>
                  inversion h; subst; eauto
                  ; simpl; apply vvot.eqb_eq; eauto
                end;
                inversion Hex; subst; eauto;
                simpl; getHead; subst; eauto.

              }
              exfalso.
              match goal with
              | h:Db ?v (MatRetE _ _ _ _ _:: _) ?w,
                h2: Df _ [] _ |- _ =>
                pose (L_invalid_comb) as f;
                specialize f with (1:=h) (2:=h2)
                ; apply f; repeat rewrite <- app_assoc; eauto
              end.
            }
          }

          1:{
            rename x2 into v'.
            rename x3 into T'.
            destruct m.
            1:{
              simpl in H8.
              destruct x1; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.


              apply_in_map.
              addEx. getAnd.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.

              apply_filter_map.
              addEx.

              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.

              getAnd.
              2:
              inversion H1; subst; try tac_invalid_db;
              match goal with
              | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                pose L_Db_uniqueT as h;
                specialize h with (1:=h1) (2:=h2)
              end
              ; subst; try easy.


              destruct x12.

              1:{
                destruct T'.
                1:{
                  destruct v'.
                  tac_invalid_db.
                  destruct va.
                  1:{
                    inversion H1; subst;
                    getHead; subst;
                    apply vvot.eqb_eq; eauto.
                  }
                  1:{
                    simpl;
                    inversion H1; subst; eauto;
                    pose L_Db_uniqueT as h;
                    match goal with
                    | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                      specialize h with (1:=h1) (2:=h2)
                    end;
                    discriminate.
                  }
                }
    
                assert (va=PndCalE L a0 L1).
                1:{
                  assert (w1++[i]!=[]) as Hw by eauto using app_cons_not_nil.
                  destruct va.
                  syncMMa; eauto.
                  invalid_ma.
                }
                subst.
                destruct r.
                destruct v'.
                tac_invalid_db.
    
                1:{
                  inversion H1; subst;
                  getHead; subst;
                  apply vvot.eqb_eq; eauto.
                }

                exfalso.
                match goal with
                | h:Db ?v (MatRetE _ _ _ _ _:: _) ?w,
                  h2: Df _ (PndCalE _ _ _::_) _ |- _ =>
                  pose (L_invalid_comb_pndc) as f;
                  specialize f with (1:=h) (2:=h2)
                  ; apply f; repeat rewrite <- app_assoc; eauto
                end.
              }

              1:{
                destruct T'.
                1:{
                  exfalso.
                  pose (L_invalid_comb_matc_e) as f.
                  specialize f with (1:=Hex) (2:=H4).
                  repeat rewrite <- app_assoc in f.
                  specialize f with (1:=H0).
                  eauto.
                }


    
                assert (va=MatCalE L a0 L1 b L2).
                1:{
                  assert (w1++[i]!=[]) as Hw by eauto using app_cons_not_nil.

                  destruct va.

                  invalid_ma.
                  syncMMa; eauto.
                }
                subst.
                destruct r.
                exfalso.

                pose L_invalid_comb_matc_pnd as f.
                specialize f with (1:=Hex) (2:=H4).
                repeat rewrite <- app_assoc in f.
                specialize f with (1:=H0).
                eauto.

                apply andb_true_iff.
                getAnd.
                inversion H1; subst; eauto;
                pose L_Db_uniqueT as h; try tac_invalid_db;
                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  specialize h with (1:=h1) (2:=h2)
                end;
                try discriminate
                ; subst; eauto
                ; simplList; subst;
    
                repeat (getAnd + (apply vvot.eqb_eq; eauto) +
                apply andb_true_iff + 
                rewrite L_eq_str +
                (apply String.eqb_eq; eauto)).
    
                destruct v'.
                tac_invalid_db.
                destruct v.


                1:{
                  inversion H1; subst;
                  match goal with
                  | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    ; getHead; subst
                    ; simpl
                    ; apply vvot.eqb_eq; eauto
                  end.
                }
                1:{
                  inversion H1; subst;
                  match goal with
                  | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    ; getHead; subst
                    ; simpl
                    ; apply vvot.eqb_eq; eauto
                  end.
                }
                apply L_goEps; simpl; eauto.
                1:{
                  inversion H1; subst; eauto; try tac_invalid_db;
                  match goal with
                  | h:Db _ _ _ |- _ =>
                  inversion h 
                  end.
                }
              }
            }

            1:{
              simpl in H8.
              destruct x1; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.
              apply_in_map.
              addEx. getAnd.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.

              apply_filter_map.
              addEx.

              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.

              getAnd.
              2:
              inversion H1; subst; try tac_invalid_db;
              match goal with
              | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                pose L_Db_uniqueT as h;
                specialize h with (1:=h1) (2:=h2)
              end
              ; subst; try easy.


              destruct x12.
              1:{
    
                destruct T'.
                1:{
                  destruct v'.
                  tac_invalid_db.
                  destruct vc.
                  1:{
                    inversion H1; subst;
                    try match goal with
                    | h:Db _ _ (Ret _::_) |- _ =>
                      inversion h; subst; eauto
                      ; simpl; apply vvot.eqb_eq; eauto; fail
                    end.
                    1,2: inversion H17; breakAll; subst; simplList; simpl;
                    apply vvot.eqb_eq; eauto.
                  }
                }
    
                destruct r.
                destruct vc.
    
                destruct v'; try tac_invalid_db.
    
                1:{
                  inversion H1; subst; try tac_invalid_db.
                  1,2: match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto
                  end;
                  inversion Hex; subst; eauto.
                  match goal with
                  | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                    pose L_Db_uniqueT as h;
                    specialize h with (1:=h1) (2:=h2)
                  end.
                  1,2: getHead; subst;
                  apply vvot.eqb_eq; eauto.
                }

    
                exfalso.
                match goal with
                | h:Db ?v (MatRetE _ _ _ _ _:: _) ?w,
                  h2: Df _ (PndCalE _ _ _::_) _ |- _ =>
                  pose (L_invalid_comb_pndc) as f;
                  specialize f with (1:=h) (2:=h2)
                  ; apply f; repeat rewrite <- app_assoc; eauto
                end.
              }

              1:{
    
                destruct T'.
                1:{
                  exfalso.
                  pose (L_invalid_comb_matc_e) as f.
                  specialize f with (1:=Hex) (2:=H4).
                  repeat rewrite <- app_assoc in f.
                  specialize f with (1:=H0).
                  eauto.
                }
    
                destruct r.
                exfalso.
                pose L_invalid_comb_matc_pnd as f.
                specialize f with (1:=Hex) (2:=H4).
                repeat rewrite <- app_assoc in f.
                specialize f with (1:=H0).
                eauto.

                apply andb_true_iff.
                getAnd.
                pose L_comb_mat_mat as f.
                specialize f with (1:=Hex) (2:=H4).
                repeat rewrite <- app_assoc in f.
                specialize f with (1:=H0).
                repeat rewrite L_eq_str.
                eauto.

                destruct v'.
                tac_invalid_db.
                1:{
                  destruct v.
                  inversion H1; subst;
                  match goal with
                  | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    ; getHead; subst
                    ; simpl
                    ; apply vvot.eqb_eq; eauto
                  end.

                  destruct vc;
                  inversion H1; subst;
                  match goal with
                  | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    ; getHead; subst
                    ; simpl
                    ; apply vvot.eqb_eq; eauto
                  end.

                  apply L_goEps; simpl; eauto.
                  1:{
                    inversion H1; subst; eauto; try tac_invalid_db;
                    match goal with
                    | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    end; inversion Hex.
                  }
                }
              }
            }

            1:{
              simpl in H8.
              destruct x1; try easy.
              simpl.
              apply in_concat.
              eexists.
              getAnd.
              apply in_map_iff.
              addEx.
              
              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.

              apply_in_map.
              addEx. getAnd.
              1:{
                inversion H1; subst; try tac_invalid_db;

                match goal with
                | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                  pose L_Db_uniqueT as h;
                  specialize h with (1:=h1) (2:=h2)
                end
                ; subst; try easy.
              }
              apply_nodup_in.

              apply_filter_map.
              addEx.

              getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
              simpl.

              getAnd.
              2:
              inversion H1; subst; try tac_invalid_db;
              match goal with
              | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                pose L_Db_uniqueT as h;
                specialize h with (1:=h1) (2:=h2)
              end
              ; subst; try easy.


              destruct x12.
              1:{
                destruct T'.
                1:{
                  destruct v'.
                  tac_invalid_db.
                  destruct vb.
                  1:{
                    inversion H1; subst;
                    try match goal with
                    | h:Db _ _ (Ret _::_) |- _ =>
                      inversion h; subst; eauto
                      ; simpl; apply vvot.eqb_eq; eauto; fail
                    end.
                    1,2: inversion H17; breakAll; subst; simplList; simpl;
                    apply vvot.eqb_eq; eauto.
                  }

                  1:{
                    simpl;
                    inversion H1; subst; eauto;
                    pose L_Db_uniqueT as h;
                    match goal with
                    | h1: Db ?v _ _, h2: Db ?v _ _ |- _ =>
                      specialize h with (1:=h1) (2:=h2)
                    end;
                    try discriminate
                    ;subst ;eauto.
    
                    getHead; subst.
                    apply vvot.eqb_eq; eauto.
                  }
                }
    
                destruct r.
                destruct vb.
    
                destruct v'; try tac_invalid_db.
    
                1:{
                  inversion H1; subst; try tac_invalid_db;
                  match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto
                  end;
                  inversion Hex; subst; eauto;
                  simpl; getHead; subst; eauto.
                }

                destruct v'; try tac_invalid_db.
                1:{
                  inversion H1; subst; try tac_invalid_db;
                  match goal with
                  | h:Db _ _ (Ret _::_) |- _ =>
                    inversion h; subst; eauto
                    ; simpl; apply vvot.eqb_eq; eauto
                  end;
                  inversion Hex; subst; eauto;
                  simpl; getHead; subst; eauto.

                }

                exfalso.
                match goal with
                | h:Db ?v (MatRetE _ _ _ _ _:: _) ?w,
                  h2: Df _ (PndCalE _ _ _::_) _ |- _ =>
                  pose (L_invalid_comb_pndc) as f;
                  specialize f with (1:=h) (2:=h2)
                  ; apply f; repeat rewrite <- app_assoc; eauto
                end.

              }

              1:{
                destruct T'.
                1:{
                  exfalso.
                  pose (L_invalid_comb_matc_e) as f.
                  specialize f with (1:=Hex) (2:=H4).
                  repeat rewrite <- app_assoc in f.
                  specialize f with (1:=H0).
                  eauto.
                }

                destruct r.
                exfalso.
                pose L_invalid_comb_matc_pnd as f.
                specialize f with (1:=Hex) (2:=H4).
                repeat rewrite <- app_assoc in f.
                specialize f with (1:=H0).
                eauto.

                apply andb_true_iff.
                getAnd.
                pose L_comb_mat_mat as f.
                specialize f with (1:=Hex) (2:=H4).
                repeat rewrite <- app_assoc in f.
                specialize f with (1:=H0).
                repeat rewrite L_eq_str.

                eauto.

                destruct v'.
                tac_invalid_db.
                1:{
                  destruct v.
                  inversion H1; subst;
                  match goal with
                  | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    ; getHead; subst
                    ; simpl
                    ; apply vvot.eqb_eq; eauto
                  end.

                  destruct vc;
                  inversion H1; subst;
                  match goal with
                  | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    ; getHead; subst
                    ; simpl
                    ; apply vvot.eqb_eq; eauto
                  end.

                  apply L_goEps; simpl; eauto.
                  1:{
                    inversion H1; subst; eauto; try tac_invalid_db;
                    match goal with
                    | h:Db _ _ _ |- _ =>
                    inversion h; subst
                    end; inversion Hex.
                  }
                }
              }
            }
          }
        }
      }

    Qed.
    (* end hide *)

  End Transducer2.
End Transducer.
