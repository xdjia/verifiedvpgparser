(** This files declares useful Coq tactics. *)

(* begin hide *)

Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import Coq.Unicode.Utf8_core.

Require Import Misc.

Import Misc.Basic.
Import Misc.vpg.

Require Import Def.

Module Tac(G:VPG).

  Module Def := Def(G).

  Import Def.DF.
  Import Def.DEF.
  Import Def.DM.

  Module Tacs.
    Ltac rmDirect :=
      match goal with 
      | h: ?v::?s != [] -> ?g |- _ =>
          assert (g) by 
          (apply h
          ; eauto using nil_cons)
          ; clear h
      | h1:?h -> ?v, g:?h |- _ =>
          assert v by auto using h1
          ; clear h1
      | h: [] != [] -> _ |- _ =>
          clear h
      | h: [] = [] -> ?g |- _ => 
          assert g by (apply h; auto)
          ; clear h
      | h: ?v::?s != [] -> ?g |- _ =>
        assert (g) by 
          (apply h
        ; eauto using nil_cons)
        ; clear h
      | h1:?h -> ?v, g:?h |- _ =>
          assert v by auto using h1
          ; clear h1
      | h: ?w ++ [?i] = [] |- _ =>
        pose (app_cons_not_nil w [] i) as _H
        ; rewrite h in _H
        ; contradiction
      | h: [] = ?w ++ [?i] |- _ =>
        pose (app_cons_not_nil w [] i) as _H
        ; rewrite <- h in _H
        ; contradiction
      | h: (?x = ?x) -> ?g |- _ =>
          assert g by (apply h; auto)
          ; clear h
      | h: ?x = ?x |- _ =>
          clear h
      end.


    Ltac eqs_True :=
      match goal with 
      | h: eqs ?s1 ?s2 = true |- _ =>
          destruct (sot.eqb_eq s1 s2)
          ; rmDirect
          ; clear h
      end.

    Ltac rmRefl :=
      match goal with 
      | h1: ?v = ?v -> ?h |- _ => 
        assert h as h2 by (apply h1; auto)
        ; clear h1
        ; rename h2 into h1
      end.

    Lemma L_Dv_w: ∀ v w T, Df v T w -> w != [].
    Proof.
      intros v w T hDv.
      induction hDv;
      auto using nil_cons, app_cons_not_nil.
    Qed.
      
    Lemma L_Dv_v: ∀ v w T, Df v T w -> v != [].
    Proof.
      intros v w T hDv.
      induction hDv; eauto using nil_cons, app_cons_not_nil.
    Qed.

    Ltac breakEx :=
      match goal with
      | h: ∃ _, _ |- _ =>
        destruct h as [? h]
      end.

    Ltac breakAnd :=
      match goal with
      | h: _ /\ _ |- _ =>
        destruct h as [? h]
      end.

    Ltac breakOr :=
      match goal with
      | h: _ \/ _ |- _ =>
        destruct h
      end.

    Ltac mergeV :=
      match goal with 
      | h: _ ++ [_] = _ ++ [_] |- _ => 
        destruct (app_inj_tail _ _ _ _ h)
        ; clear h
      end.

    Ltac simplList :=
      match goal with 
      | h: ?v1 :: ?_v1 = ?v2 :: ?_v2 |- _ => 
        inversion h
        ;clear h
      | h: ?v1 :: ?_v1 = [?v2] ++ ?_v2 |- _ => 
        inversion h
        ;clear h
      | h: [?v1] ++ ?_v1 = [?v2] ++ ?_v2 |- _ => 
        inversion h
        ;clear h
      | h: ?v1 :: ?_v1 = [?v2] |- _ =>
        inversion h
        ;clear h
      | h: [?v1] = ?v2 :: ?_v2 |- _ =>
        inversion h
        ;clear h
      | h: [?v1] = ?v2 ++ ?_v2 |- _ =>
        inversion h
        ;clear h
      end.

    (* Hint Constructors Df : hint_Dv. *)

    Lemma L_hdtl: ∀ {x:Type} (l1: list x) l2 a l3, (l1++l2=a::l3)->
      (l1 != [])->
      ∃ l, l1=a::l.
    Proof.
      intros x l1 l2 a l3 h1 h2.
      pose (destruct_list l1).
      destruct s. destruct s. destruct s.
      rewrite e in h1.
      inversion h1. subst. eauto.
      contradiction.
    Qed.

    Lemma VEndSameEq: ∀ v L L',
      VEndWith v L -> VEndWith v L' ->
      L=L'.
    Proof.
      intros.
      inversion H
      ; inversion H0
      ; repeat (breakEx + breakAnd)
      ; subst;

      auto using app_inj_tail;
      mergeV; subst;
      inversion H2; auto. 
    Qed.

    Lemma VBeginSameEq: ∀ v L L', 
      VBeginWith v L -> VBeginWith v L' ->
      L=L'.
    Proof.
      intros.
      inversion H
      ; inversion H0
      ; repeat (breakEx + breakAnd)
      ; subst;

      inversion H4; auto. 
    Qed.

    Lemma _VListBeginSame: ∀ e v1 L, 
      VBeginWith (e::v1) L -> VBeginWith [e] L.
    Proof.
      intros.
      inversion H
      ; repeat (breakEx + breakAnd)
      ; simplList
      ; subst.
      apply BeginC.
      exists [], x0, x1; auto.
      apply BeginA1.
      exists [], x0, x1; auto.
      apply BeginA2.
      exists [], x0, x1, x2, x3; auto.
      apply BeginB.
      exists [], x0, x1; auto.
    Qed.

    Lemma VListBeginSame: ∀ v v1 L, 
      VBeginWith (v++v1) L -> (v != []) -> 
        VBeginWith v L.
    Proof.
      intros.
      destruct v; try contradiction.
      inversion H
      ; repeat (breakEx)
      ; subst
      ; inversion H1.
      apply BeginC.
      exists v0, x0, x1; auto.
      apply BeginA1.
      exists v0, x0, x1; auto.
      apply BeginA2.
      exists v0, x0, x1, x2, x3; auto.
      apply BeginB.
      exists v0, x0, x1; auto.
    Qed.

    Lemma VListBeginSame2: ∀ v v1 L, 
      VBeginWith v L -> VBeginWith (v++v1) L.
    Proof.
      intros.
      inversion H
      ; repeat (breakEx)
      ; subst.
      apply BeginC.
      exists (x ++ v1), x0, x1; auto.
      apply BeginA1.
      exists (x ++ v1), x0, x1; auto.
      apply BeginA2.
      exists (x ++ v1), x0, x1, x2, x3; auto.
      apply BeginB.
      exists (x ++ v1), x0, x1; auto.
    Qed.

    Lemma VListEndSame2: ∀ v v1 L, 
      VEndWith v L -> VEndWith (v1++v) L.
    Proof.
      intros.
      inversion H
      ; repeat (breakEx)
      ; subst.
      apply EndC.
      exists (v1++x), x0, x1; eauto using app_assoc.
      apply EndA1.
      exists (v1++x), x0, x1; eauto using app_assoc.
      apply EndA2.
      exists (v1++x), x0, x1, x2, x3; eauto using app_assoc.

      apply EndB1.
      exists (v1++x), x0, x1; eauto using app_assoc.
      apply EndB2.
      exists (v1++x), x0, x1; eauto using app_assoc.
    Qed.

    Lemma VListBeginSame3: ∀ v v1 L L', 
      VBeginWith v L -> VBeginWith (v++v1) L' -> L=L'.
    Proof.
      intros.
      inversion H
      ; inversion H0
      ; repeat (breakEx)
      ; subst
      ; inversion H4; auto.
    Qed.

    Ltac extractHead :=
      match goal with 
      | h: VBeginWith (?v++?_v) ?L,
        Hv: Df ?v _ _
      |- _ =>
        pose (VListBeginSame _ _v _ h (L_Dv_v _ _ _ Hv)) as HvHead
      end.

    Ltac mergeBegin :=
      match goal with 
      | h: VBeginWith [?e] ?L
      |- _ =>
        inversion h; repeat breakEx; subst;
        simplList; subst
      end.

    Ltac rmIndtT_bak :=
      match goal with 
      | IHHvTw: ?t::?T != [] -> exists _, _ 
      |- _ =>
        assert (t::T != []) as HtTNotEmp by (eauto using nil_cons; eauto) 
        ; pose (IHHvTw HtTNotEmp) as Ind
      end.

    Ltac rmIndtT :=
      match goal with 
      | IHHvTw: ?t::?T != [] -> _ 
      |- _ =>
        assert (t::T != []) as HtTNotEmp by (eauto using nil_cons; eauto) 
        ; pose (IHHvTw HtTNotEmp) as Ind
      end.


    (* NOTE Ltac: merge the ends *)
    Ltac mergeEnds :=
      match goal with 
      | h: VEndWith ?v1 (?L),
        h2: VEndWith ?v1 (?L1)
      |- _
      =>
        destruct (VEndSameEq _ _ _ h2 h)
        ; subst
      end.


    Ltac rmEmpRefl :=
      match goal with 
      | h1: [] = [] -> ?h |- _ => 
        assert h as h2 by (apply h1; auto)
        ; clear h1
        ; rename h2 into h1
      end.


    Ltac rmIndTEmp :=
      match goal with 
      | IHHvTw: ?T = [] -> ∃ _, _,
        h: ?T = []
      |- _ =>
          destruct (IHHvTw h) as [Lv [uv [_L [_u Ind]]]]
          ; destruct Ind as [HvBegin [_H Ind]]
      end.


    Ltac mergeBegins :=
      match goal with 
      | h: VBeginWith ?v1 (?L),
        h2: VBeginWith ?v1 (?L1)
      |- _
      =>
        destruct (VBeginSameEq _ _ _ h2 h)
        ; subst
      end.

    Ltac mergeBegins2 :=
      match goal with 
      | h: VBeginWith (?v1++[?ea]) ?L,
        h2: VBeginWith ?v1 ?L1
      |- _
      =>
        destruct (VListBeginSame3 _ _ _ _ h2 h); subst
      end.

    Ltac rmEmpConsInfer :=
      match goal with 
      | h: _::_ = [] -> _ |- _ =>
        clear h
      end.


    (* extract the sub Df *)
    Ltac getSubDv :=
      match goal with 
      | Hw1NotEmpDv: ?c::?w != [] -> Df _ _ _ |- _ =>
        assert (c::w != []) as _Hnot2 by eauto using nil_cons
        ; pose (Hw1NotEmpDv _Hnot2) as HDvSub
      end.

    Ltac mergeeiv' :=
      match goal with 
      | H: in_rules (?L, _ ?i ?L1) _,
        HDm: Dm (?L1, ?u) ?w' ?v',
        Ind: ∀ _ _, Dm _ _ _ -> _ |- _ =>
        pose (DLc _ _ _ _ w' v' H HDm) as HDm'
        ; pose (Ind _ _ HDm') as HDm2
      end.

    Ltac mergeeav' :=
      match goal with 
      | H: in_rules (?L, _ ?i ?L1) _,
        HDm: Dm (?L1, ?u) ?w' ?v',
        Ind: ∀ _ _, Dm _ _ _ -> _ |- _ =>
        pose (DLa _ _ _ w' v' H HDm) as HDm'
        (* ; pose (Ind _ _ HDm') as HDm2 *)
      end.

    Ltac breakInfer :=
      match goal with
      | h: _ -> ?g |- _ =>
          assert g
      end.

    Ltac tac_app :=
      match goal with
      | h:_ -> ?g |- ?g =>
          apply h
          ; clear h
      end.

    Ltac breakAll :=
      repeat (breakAnd + breakEx + breakOr).

    Ltac tac_inj :=
      repeat match goal with 
      | h: ?v ++ [?e] = [] |- _ =>
          pose (app_cons_not_nil v [] e) as _h
          ; rewrite h in _h
          ; contradiction
      | h: [] = _ ++ _ |- _ =>
          symmetry in h
          ; destruct (app_eq_nil _ _ h)
      | h: [_] = _ ++ [_] |- _ =>
          pose (app_inj_tail [] _ _ _ h)
          ; breakAll
          ; try discriminate
          ; clear h
      | h: [_] = _ ++ _ ++ [_] |- _ =>
          rewrite app_assoc in h
          ; pose (app_inj_tail [] _ _ _ h)
          ; breakAll
          ; try discriminate
          ; clear h
      | h: _ ++ [_] = [_] |- _ =>
          pose (app_inj_tail _ [] _ _ h)
          ; breakAll
          ; try discriminate
          ; clear h
      | h: _ ++ [_] = _ ++ [_] |- _ =>
          pose (app_inj_tail _ _ _ _ h)
          ; breakAll
          ; try discriminate
          ; clear h
      | h: ?u ++ [?a] = ?v::?w ++ [?b] |- _ =>
          pose (app_inj_tail u (v::w) a b h)
          ; breakAll
          ; try discriminate
          ; clear h
          | h: _ ++ [_] = _ ++ _ ++ [_] |- _ =>
          rewrite app_assoc in h
          ; pose (app_inj_tail _ _ _ _ h)
          ; breakAll
          ; try discriminate
          ; clear h
      | h: _ ++ [_] = _ ++ _ :: _ ++ [_] |- _ =>
          rewrite app_comm_cons in h
          ; rewrite app_assoc in h
          ; pose (app_inj_tail _ _ _ _ h)
          ; breakAll
          ; try discriminate
          ; clear h
      end.


    Ltac try_resolve_end :=
      (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
      exists []; repeat eexists; fail.

    Ltac try_resolve_end_with x :=
      (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
        exists x; repeat rewrite app_assoc; repeat eexists; fail.

    Ltac try_resolve_begin :=
      (apply BeginA1+ apply BeginA2 + apply BeginC + apply BeginB);
        exists []; repeat eexists; fail.


    Ltac tac_df :=
      match goal with
      | h: Df _ _ [] |- _ =>
        pose (L_Dv_w _ _ _ h)
        ; contradiction
      | h: Df [] _ _ |- _ =>
        pose (L_Dv_v _ _ _ h)
        ; contradiction
      end.


    Ltac breakland :=
      match goal with
      | h: ?g && ?w = true |- _ =>
          destruct_with_eqn (g);
          destruct_with_eqn (w);
          try discriminate
      end.

    Ltac tac_invalid_df :=
      match goal with 
      | h: Df _ _ [] |- _ => 
          pose (L_Dv_w _ _ _ h)
          ; contradiction
      | h: Df [] _ _ |- _ => 
          pose (L_Dv_v _ _ _ h)
          ; contradiction
      | h: Df (_ ++ [Retv _]) _ ([] ++ [_]) |- _ => 
          inversion h
      end.

    Ltac extractEnds :=
      match goal with
      | h:VEndWith [_] ?L |- _ =>
          inversion h
          ; breakAll
          ; tac_inj
          ; subst
          ; clear h
      | h:VEndWith (_++[_]) ?L |- _ =>
          inversion h
          ; breakAll
          ; tac_inj
          ; subst
          ; clear h
      end.

    Ltac rmInvalidList :=
      match goal with
      | h:[_] = ?v ++ _ :: _ ++ [_] |- _ =>
        destruct v; simpl in *; simplList; tac_inj; try discriminate
      | h:?v ++ _ :: _ = [] |- _ =>
        destruct v; simpl in *; try simplList; tac_inj; try discriminate
      | h:[] = ?v ++ _ |- _ =>
        destruct v; simpl in *; try simplList; tac_inj; try discriminate
      | h:[_] = ?v ++ _ :: _ ++ _ :: _ |- _ =>
        destruct v; simpl in *; try simplList; tac_inj; try discriminate
      end.

    Ltac addEx :=
      match goal with 
      | |- ∃ _, _ => 
        eexists
      end.

    Ltac breakTuple :=
      match goal with
      | h:(?x1,?y1)=(?x,?y) |- _ =>
        assert (x1=x) by (inversion h; eauto); 
        assert (y1=y) by (inversion h; eauto);
        subst
      end.

    Ltac assertLast h := 
      match h with 
      | _ -> ?h2 => assertLast h2
      | ?h2 => assert h2
      end.

    Ltac getH := match goal with
    | h: _ -> ?h2 |- _ =>
        assertLast h2
    end.

  End Tacs.

End Tac.

(* end hide *)
