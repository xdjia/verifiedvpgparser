(** This file declares the types for VPG module and parser PDA states.
  *)

Require Import Misc.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Unicode.Utf8_core.
Open Scope list_scope.

Import Misc.vpg.
Import Misc.Basic.

From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

(* begin hide *)

Module LEN_WF.
  Definition len {A} (ls1 ls2 : list A) :=
  length ls1 < length ls2.

  Theorem len_wf : ∀ A, well_founded (@len A).
  Proof.
  red.
  intros.
  induction a.

  constructor. intros. inversion H.

  constructor. intros.
  inversion H.

  inversion IHa.
  unfold len in H0.
  rewrite <- H1 in H0.
  fold (@len A) in H0.
  constructor.
  apply H0.

  inversion IHa.
  apply H2.
  eauto.
  Qed.

End LEN_WF.

Import LEN_WF.

Module String_as_OT := Misc.String_as_OT.

(* end hide *)

(** The module type [VPG] for a VPG. *)
Module Type VPG.
  (** [L_0]: the start nonterminal. *)
  Parameter L_0 : vpg_var.

  (** [P]: the production rules. *)
  Parameter P : vpg.rules.

  (** [A_VPG_Linear]: this axiom shows that in a linear rule L -> i L',
      if L ∈ V0, then L' ∈ V0. *)
  Axiom A_VPG_Linear: ∀ L c L1,
  in_rules (L, Alt_Linear c L1) P
  -> (∃ u, L = V0 u)
  -> ∃ u1 i, L1 = V0 u1 /\ c=Plain i.

  (** [A_VPG_Linear]: this axiom shows that in a matching rule L -> a L1
      b L2, L1 ∈ V0, and if L ∈ V0, then L2 ∈ V0. *)
  Axiom A_VPG_Match: ∀ L a L1 b L2,
    in_rules (L, Alt_Match a b L1 L2) P
    -> (∃ u1, L1 = V0 u1) /\ 
      ((∃ u, L = V0 u) -> ∃ u2, L2 = V0 u2).
End VPG.

(* begin hide *)

Module LocalTac.
  Ltac resolve_eqb :=
    match goal with
    | h: eqs ?x ?x = false |- _ =>
      assert (eqs x x=true) as _h by
      (apply (sot.eqb_eq x x); eauto)
      ; rewrite _h in h
      ; inversion h
    | h: vvot.eqb ?x ?x = false |- _ =>
      assert (vvot.eqb x x=true) as _h by
      (apply (vvot.eqb_eq x x); eauto)
      ; rewrite _h in h
      ; inversion h
    | h: eqvv ?x ?x = false |- _ =>
      assert (eqvv x x=true) as _h by
      (apply (vvot.eqb_eq x x); eauto)
      ; rewrite _h in h
      ; inversion h
    | h: symbol_as_OT.lt ?t ?t |- _ =>
      destruct (symbol_as_OT.lt_strorder) as [tacH _]
      ; pose (tacH t)
      ; contradiction
    | h: String_as_OT.lt ?t ?t |- _ =>
      destruct (String_as_OT.lt_strorder) as [tacH _]
      ; pose (tacH t)
      ; contradiction
    | h: String.eqb ?x ?x = false |- _ =>
      assert (String.eqb x x=true) as _h by
      (apply (String.eqb_eq x x); eauto)
      ; rewrite _h in h
      ; inversion h
    end.

  Ltac resolveBool :=
    match goal with
    | h: ?g=true, x:?g=false |- _ =>
      rewrite h in x; discriminate
    end.

  Ltac f1 :=
    match goal with 
    | [h : context [ negb (eqs  ?u ?v) ] |- _] => 
      let g := fresh "g" in
      case_eq (eqs  u v); intro g; rewrite g in h; simpl in h
    | [h : context [ negb (eqvv  ?u ?v) ] |- _] => 
      let g := fresh "g" in
      case_eq (eqvv  u v); intro g; rewrite g in h; simpl in h
    | [h: eqs ?u ?v = true, g: eqs ?v ?w = true |- context [negb (eqs ?u ?w)]] =>
      let q := fresh "q" in
      assert (eqs u w=true) as q by eapply (sym_eq_transb u v w h g);
      rewrite q; simpl; clear q
    | [h: vpg_var_as_OT.lt ?u ?v, g: vpg_var_as_OT.lt ?v ?w |- vpg_var_as_OT.lt ?u ?w] =>
      eapply (vv_lt_trans u v w h g)
    | |- context [negb (eqs ?u ?v)] => 
      let g := fresh "g" in
      case_eq (eqs u v); intro g
    | |- context [negb (eqvv ?u ?v)] => 
      let g := fresh "g" in
      case_eq (eqvv u v); intro g
    | |- context [ (negb false) ] => simpl
    | |- context [ (negb true) ] => simpl
    end.

  Ltac trans_s :=
    match goal with
    | h: eqs ?x ?y = true |- _ =>
      pose (sot.eqb_eq x y) as i; destruct i as [q1 _]; 
      pose (q1 h) as e; rewrite e in *;
      clear e; clear q1; clear h
    end.

  Ltac resolve_eqs := 
    match goal with
    | H: eqs ?s1 ?s2 = true |- _ =>
      pose (sot.eqb_eq s1 s2) as _e;
      destruct _e as [_e1 _];
      pose (_e1 H) as _e;
      rewrite _e in *;
      clear _e _e1 H
    end.

  Ltac app_lt_trans :=
    match goal with
    | H: symbol_as_OT.lt ?t0 ?t1,
      H0: symbol_as_OT.lt ?t1 ?t2 |- _ =>
      destruct (symbol_as_OT.lt_strorder) as [_ h]
      ; pose (h t0 t1 t2 H H0)
    | H: String_as_OT.lt ?t0 ?t1,
      H0: String_as_OT.lt ?t1 ?t2 |- _ =>
      destruct (String_as_OT.lt_strorder) as [_ h]
      ; pose (h t0 t1 t2 H H0)
    | H: vpg_var_as_OT.lt ?t0 ?t1,
      H0: vpg_var_as_OT.lt ?t1 ?t2 |- _ =>
      destruct (vpg_var_as_OT.lt_strorder) as [_ h]
      ; pose (h t0 t1 t2 H H0)
    end.

  Ltac eqvv_refl x := 
    assert (eqvv x x=true) by
    (apply (vvot.eqb_eq x x); eauto).

  Ltac resolveVV :=
    match goal with
    | h: eqvv ?v ?v = false |- _ =>
      eqvv_refl v
    | h: vpg_var_as_OT.lt ?t ?t |- _ =>
      destruct (vpg_var_as_OT.lt_strorder) as [tacH _]
      ;  pose (tacH t)
      ; contradiction
    end.

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
    end.

  Ltac eqb_True :=
    match goal with 
    | h: String.eqb ?v ?u = true |- _ =>
      destruct (String.eqb_eq v u) as [_H _]
      ; pose (_H h) as e
      ; rewrite e in *
      ; clear e
      ; clear h
      ; clear _H
    | h: eqvv ?v ?u = true |- _ =>
      pose (vv_lt_eqbeq v u h) as eqvv_True_e
      ; rewrite eqvv_True_e in *
      ; clear eqvv_True_e
      ; clear h
    | h: eqs ?s1 ?s2 = true |- _ =>
      destruct (sot.eqb_eq s1 s2)
      ; rmDirect
      ; clear h
    | H: eqvv ?v1 ?v2 = true |- _ =>
      pose (vv_lt_eqbeq _ _ H) as _e;
      rewrite _e in *;
      clear _e H
    | H: vvot.eqb ?v1 ?v2 = true |- _ =>
      pose (vv_lt_eqbeq _ _ H) as _e;
      rewrite _e in *;
      clear _e H
    end.

  Ltac destruct_eqb:=
    match goal with 
    | h: if negb (?eqb ?x ?x) then _ else _ |- _ =>
      destruct_with_eqn (eqb x x)
      ; simpl in h
      ; eauto with misc
    | h: (if negb (?eqb ?x ?x) then _ else _) = _ |- _ =>
      destruct_with_eqn (eqb x x)
      ; simpl in h
    | h: (if negb (?eqb ?x ?y) then _ else _) = _ |- _ =>
      destruct_with_eqn (eqb x y)
      ; simpl in h
    | h: if negb (?eqb ?x ?y) then _ else _ |- _ =>
      destruct_with_eqn (eqb x y)
      ; simpl in h
      ; eauto with misc
      ; simpl
    | |- if negb (?eqb ?x ?y) then _ else _ =>
      destruct_with_eqn (eqb x y)
      ; simpl
      ; eauto with misc
      ; simpl
    end.

  Ltac resolve_Eq :=
    match goal with
    | h: vpg_var_as_OT.compare ?v ?v0 = Eq |- _ =>
      pose (vv_cmp_eq) as e
      ; specialize e with (1:=h)
      ; rewrite e in *
      ; clear e h
    | h: symbol_as_OT.compare ?v ?v0 = Eq |- _ =>
      pose (alt_as_OT.sot_cmp_eq) as e
      ; specialize e with (1:=h)
      ; rewrite e in *
      ; clear e h
    | h: compare_str ?v ?v0 = Eq |- _ =>
      pose (str_cmp_eq) as e
      ; specialize e with (1:=h)
      ; rewrite e in *
      ; clear e h
    end.

  Ltac refl_gt_lt :=
  match goal with
  | h: compare_str ?x ?y = Gt |- _ =>
    destruct (String_as_OT.compare_spec x y);
    try easy
  end.
End LocalTac.

(* end hide *)

(** The module [DEF] declares PDA states. *)
Module DEF.
  Import LocalTac.

  (** [var]: a VPG nonterminal. *)
  Definition var := vpg_var.

  (** [PlnEdge]: a plain VPG rule. *)
  Inductive PlnEdge : Type :=
  | PlnE (L:var) (c:terminal) (L1:var).

  (** [CalEdge]: a call VPG rule, linear or matching. *)
  Inductive CalEdge : Type :=
  | PndCalE (L:var) (a:terminal) (L1:var)
  | MatCalE (L:var) (a:terminal) (L1:var) (b:terminal)(L2:var).

  (** [RetEdge]: a return VPG rule, linear or matching. *)
  Inductive RetEdge : Type :=
  | PndRetE (L:var) (b:terminal) (L1:var)
  | MatRetE (L:var) (a:terminal) (L1:var) (b:terminal) (L2:var).

  (** [VE]: an element of a parse tree [v] is a rule. *)
  Inductive VE : Type :=
  | Calv (va: CalEdge)
  | Plnv (vc: PlnEdge)
  | Retv (vb: RetEdge).

  (* begin hide *)

  Module ea_as_OT <: OrderedType.
    Definition t := CalEdge.
    Definition eq := @eq CalEdge.
    Local Instance eq_equiv : Equivalence eq.
    split; unfold eq.
    intros s; induction s; simpl; auto.
    eauto with misc.
    unfold Transitive. apply eq_trans.
    Qed.

    Definition cale_dec : forall c1 c2 : t, {c1 = c2} + {c1 <> c2}.
    Proof. decide equality; eauto with misc. Qed.
    Definition eq_dec := cale_dec.

    Global Hint Resolve cale_dec : misc.


    Definition lt (x y: t) := 
      match x, y with 
      | PndCalE _ _ _, MatCalE _ _ _ _ _ => True 
      | PndCalE L1 a L2, PndCalE L1' a' L2' =>
        if negb (eq_str a a') then 
          String_as_OT.lt a a'
        else if negb (vvot.eqb L1 L1') then 
          vpg_var_as_OT.lt L1 L1'
        else
          vpg_var_as_OT.lt L2 L2'
      | MatCalE L1 a L2 b L3, MatCalE L1' a' L2' b' L3' => 
        if negb (eq_str a a') then String_as_OT.lt a a' else 
        if negb (eq_str b b') then String_as_OT.lt b b' else 
        if negb (eqvv L1 L1') then vpg_var_as_OT.lt L1 L1' else 
        if negb (eqvv L2 L2') then vpg_var_as_OT.lt L2 L2' else 
          vpg_var_as_OT.lt L3 L3'
      | _, _ => False
      end.


    Local Instance lt_strorder : StrictOrder lt.
    Proof.
      split; unfold lt.
      1: {
        intros s t; destruct s; try (contradiction);

        repeat
        destruct_eqb;
        resolve_eqb;
        resolveBool.
      }

      intros s t z; destruct s; destruct t; destruct z.
      all: try contradiction; intros; eauto with misc.

      all: repeat destruct_eqb;
      repeat eqb_True;

      rewrite L_eq_str in *.

      all: repeat (resolve_eqb + eqb_True); auto.

      all: auto.


      all: try match goal with
      | H: vpg_var_as_OT.lt ?t0 ?t1,
        H0: vpg_var_as_OT.lt ?t1 ?t2 |- _ =>
        destruct (vpg_var_as_OT.lt_strorder) as [_ h]
        ; pose (h t0 t1 t2 H H0)
      end; auto.

      all: try match goal with 
      | h1: vpg_var_as_OT.lt ?v1 ?v2,
        h2: vpg_var_as_OT.lt ?v2 ?v1 |- _ =>
        pose (vv_lt_itrefl _ _ h1 h2)
        ; contradiction
      end.

      all: try (app_lt_trans; try resolve_eqb; eauto).
    Qed.


    Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof.
      unfold Proper, eq, lt; split; 
      destruct x; destruct x0; destruct y; destruct y0;
      eauto with misc; intro h; try (contradiction); 
      inversion H; inversion H0; subst; eauto with misc.
    Qed.

    Definition compare x y : comparison :=
      match x, y with 
      | PndCalE _ _ _, MatCalE _ _ _ _ _ => Lt 
      | PndCalE L1 a L2, PndCalE L1' a' L2' =>
        if negb (eq_str a a') then 
          compare_str a a'
        else if negb (vvot.eqb L1 L1') then 
          vpg_var_as_OT.compare L1 L1'
        else
          vpg_var_as_OT.compare L2 L2'
      | MatCalE L1 a L2 b L3, MatCalE L1' a' L2' b' L3' => 
        if negb (eq_str a a') then compare_str a a' else 
        if negb (eq_str b b') then compare_str b b' else 
        if negb (eqvv L1 L1') then vpg_var_as_OT.compare L1 L1' else 
        if negb (eqvv L2 L2') then vpg_var_as_OT.compare L2 L2' else 
          vpg_var_as_OT.compare L3 L3'
      | _, _ => Gt
      end.

    Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
    Proof.
      intros x y;
      case_eq (compare x y);
      destruct x; destruct y;
      intro h; unfold compare in h;
      try rewrite L_eq_str in *;

      repeat destruct_eqb;
      repeat eqb_True;
      try resolve_Eq.
      all: try constructor; try reflexivity; try resolve_eqb; try easy.
      
      all: try rewrite L_eq_str in *; try eqb_True; try easy;
      try resolve_eqb.
      all: simpl.
      all: repeat destruct_eqb.
      all: try rewrite L_eq_str in *.
      all: try resolve_eqb; try easy.

      all: try match goal with
      | h: ?x=true, h1: ?x=false |- _ =>
      rewrite h in h1; easy
      end.

      Ltac resolve_lt_gt :=
      match goal with
      | h: vpg_var_as_OT.compare ?L1 ?L2 = Lt |- _ =>
        pose vv_cmp_lt as _h;
        specialize _h with (1:=h)
      | h: compare_str ?L1 ?L2 = Lt |- _ =>
        pose str_cmp_lt as _h;
        specialize _h with (1:=h)
      end.

      all: try resolve_lt_gt; eauto.

      all: try (eqb_True; resolve_eqb).

      all: try refl_gt_lt; subst; try resolve_eqb.

      all: match goal with
      | |- _ ?x ?y =>
        unfold compare_str in h;
        destruct (OrderedTypeEx.String_as_OT.cmp_lt y x);
        destruct (String_as_OT.compare_spec y x); subst; try easy
      end.
      
    Qed.

  End ea_as_OT.

  Module ec_as_OT <: OrderedType.
    Definition t := PlnEdge.
    Definition eq := @eq PlnEdge.
    Local Instance eq_equiv : Equivalence eq.
    split; unfold eq.
    intros s; induction s; simpl; auto.
    eauto with misc.
    unfold Transitive. apply eq_trans.
    Qed.

    Definition plne_dec : forall c1 c2 : t, {c1 = c2} + {c1 <> c2}.
    Proof. decide equality; eauto with misc. Qed.
    Definition eq_dec := plne_dec.

    Global Hint Resolve plne_dec : misc.

    Definition lt (x y: t) := 
      match x, y with 
      | PlnE L1 a L2, PlnE L1' a' L2' =>
        if negb (eq_str a a') then 
          String_as_OT.lt a a'
        else if negb (vvot.eqb L1 L1') then 
          vpg_var_as_OT.lt L1 L1'
        else
          vpg_var_as_OT.lt L2 L2'
      end.


    Local Instance lt_strorder : StrictOrder lt.
    Proof.
      split; unfold lt.
      1: {
        intros s t; destruct s; try (contradiction);

        repeat
        destruct_eqb;
        resolve_eqb;
        resolveBool.
      }

      intros s t z; destruct s; destruct t; destruct z.
      all: try contradiction; intros; eauto with misc.


      rewrite L_eq_str in *.


      all: repeat destruct_eqb
      ;
      repeat eqb_True;

      try (match goal with
      | |- if negb (?eqb ?x ?x) then _ else _ =>
        assert (eqb x x = true) as _h
        by (apply vvot.eqb_eq 
          + apply vot.eqb_eq; eauto)
        ; rewrite _h
        ; simpl
        ; try app_lt_trans
        ; eauto
      end
      );
      try match goal with 
      | h: ?x=_ |- if negb ?x then _ else _ =>
        rewrite h
        ; simpl
        ; eauto
      end;

      try (resolve_eqb;
      resolveBool)
      ; eauto.

      all: try match goal with
      | H: vpg_var_as_OT.lt ?t0 ?t1,
        H0: vpg_var_as_OT.lt ?t1 ?t2 |- _ =>
        destruct (vpg_var_as_OT.lt_strorder) as [_ h]
        ; pose (h t0 t1 t2 H H0)
      end; auto.

      all: try match goal with 
      | h1: vpg_var_as_OT.lt ?v1 ?v2,
        h2: vpg_var_as_OT.lt ?v2 ?v1 |- _ =>
        pose (vv_lt_itrefl _ _ h1 h2)
        ; contradiction
      end.


      all: try (app_lt_trans; try resolve_eqb; eauto).
    Qed.

    
    Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof.
      unfold Proper, eq, lt; split; 
      destruct x; destruct x0; destruct y; destruct y0;
      eauto with misc; intro h; try (contradiction); 
      inversion H; inversion H0; subst; eauto with misc.
    Qed.

    Definition compare x y : comparison :=
      match x, y with 
      | PlnE L1 a L2, PlnE L1' a' L2' =>
        if negb (eq_str a a') then 
          compare_str a a'
        else if negb (vvot.eqb L1 L1') then 
          vpg_var_as_OT.compare L1 L1'
        else
          vpg_var_as_OT.compare L2 L2'
      end.

    Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
    Proof.
      intros x y;
      case_eq (compare x y);
      destruct x; destruct y;
      intro h; unfold compare in h;
      try rewrite L_eq_str in *;

      repeat destruct_eqb;
      repeat eqb_True;
      try resolve_Eq.

      all: try constructor; try reflexivity; try resolve_eqb; try easy.
      
      all: try rewrite L_eq_str in *; try eqb_True; try easy;
      try resolve_eqb.
      all: simpl.
      all: repeat destruct_eqb.
      all: try rewrite L_eq_str in *.
      all: try resolve_eqb; try easy.

      all: try match goal with
      | h: ?x=true, h1: ?x=false |- _ =>
      rewrite h in h1; easy
      end.


      all: try resolve_eqb.

      Ltac resolve_lt_gt :=
      match goal with
      | h: vpg_var_as_OT.compare ?L1 ?L2 = Lt |- _ =>
        pose vv_cmp_lt as _h;
        specialize _h with (1:=h)
      | h: compare_str ?L1 ?L2 = Lt |- _ =>
        pose str_cmp_lt as _h;
        specialize _h with (1:=h)
      end.

      all: try resolve_lt_gt; eauto.

      all: try (eqb_True; resolve_eqb).

      unfold compare_str in h;
      destruct (OrderedTypeEx.String_as_OT.cmp_lt c c0);
      destruct (String_as_OT.compare_spec c c0); subst; try easy.

    Qed.

  End ec_as_OT.

  Module eb_as_OT <: OrderedType.
    Definition t := RetEdge.
    Definition eq := @eq RetEdge.
    Local Instance eq_equiv : Equivalence eq.
    split; unfold eq.
    intros s; induction s; simpl; auto.
    eauto with misc.
    unfold Transitive. apply eq_trans.
    Qed.

    Definition rete_dec : forall c1 c2 : t, {c1 = c2} + {c1 <> c2}.
    Proof. decide equality; eauto with misc. Qed.
    Definition eq_dec := rete_dec.

    Global Hint Resolve rete_dec : misc.

    Definition lt (x y: t) := 
      match x, y with 
      | PndRetE _ _ _, MatRetE _ _ _ _ _ => True 
      | PndRetE L1 a L2, PndRetE L1' a' L2' =>
        if negb (eq_str a a') then 
          String_as_OT.lt a a'
        else if negb (vvot.eqb L1 L1') then 
          vpg_var_as_OT.lt L1 L1'
        else
          vpg_var_as_OT.lt L2 L2'
      | MatRetE L1 a L2 b L3, MatRetE L1' a' L2' b' L3' => 
        if negb (eq_str a a') then String_as_OT.lt a a' else 
        if negb (eq_str b b') then String_as_OT.lt b b' else 
        if negb (eqvv L1 L1') then vpg_var_as_OT.lt L1 L1' else 
        if negb (eqvv L2 L2') then vpg_var_as_OT.lt L2 L2' else 
          vpg_var_as_OT.lt L3 L3'
      | _, _ => False
      end.


    Local Instance lt_strorder : StrictOrder lt.
    Proof.
      split; unfold lt.
      1: {
        intros s t; destruct s; try (contradiction);

        repeat
        destruct_eqb;
        resolve_eqb;
        resolveBool.
      }

      intros s t z; destruct s; destruct t; destruct z.
      all: try contradiction; intros; eauto with misc.

      all: repeat destruct_eqb;
      repeat eqb_True;

      rewrite L_eq_str in *.

      all: repeat (resolve_eqb + eqb_True); auto.

      all: auto.


      all: try match goal with
      | H: vpg_var_as_OT.lt ?t0 ?t1,
        H0: vpg_var_as_OT.lt ?t1 ?t2 |- _ =>
        destruct (vpg_var_as_OT.lt_strorder) as [_ h]
        ; pose (h t0 t1 t2 H H0)
      end; auto.

      all: try match goal with 
      | h1: vpg_var_as_OT.lt ?v1 ?v2,
        h2: vpg_var_as_OT.lt ?v2 ?v1 |- _ =>
        pose (vv_lt_itrefl _ _ h1 h2)
        ; contradiction
      end.

      all: try (app_lt_trans; try resolve_eqb; eauto).
    Qed.

    
    Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof.
      unfold Proper, eq, lt; split; 
      destruct x; destruct x0; destruct y; destruct y0;
      eauto with misc; intro h; try (contradiction); 
      inversion H; inversion H0; subst; eauto with misc.
    Qed.

    Definition compare x y : comparison :=
      match x, y with 
      | PndRetE _ _ _, MatRetE _ _ _ _ _ => Lt 
      | PndRetE L1 a L2, PndRetE L1' a' L2' =>
        if negb (eq_str a a') then 
          compare_str a a'
        else if negb (vvot.eqb L1 L1') then 
          vpg_var_as_OT.compare L1 L1'
        else
          vpg_var_as_OT.compare L2 L2'
      | MatRetE L1 a L2 b L3, MatRetE L1' a' L2' b' L3' => 
        if negb (eq_str a a') then compare_str a a' else 
        if negb (eq_str b b') then compare_str b b' else 
        if negb (eqvv L1 L1') then vpg_var_as_OT.compare L1 L1' else 
        if negb (eqvv L2 L2') then vpg_var_as_OT.compare L2 L2' else 
          vpg_var_as_OT.compare L3 L3'
      | _, _ => Gt
      end.

    Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
    Proof.
      intros x y;
      case_eq (compare x y);
      destruct x; destruct y;
      intro h; unfold compare in h;
      try rewrite L_eq_str in *;

      repeat destruct_eqb;
      repeat eqb_True;
      try resolve_Eq.
      all: try constructor; try reflexivity; try resolve_eqb; try easy.
      
      all: try rewrite L_eq_str in *; try eqb_True; try easy;
      try resolve_eqb.
      all: simpl.
      all: repeat destruct_eqb.
      all: try rewrite L_eq_str in *.
      all: try resolve_eqb; try easy.

      all: try match goal with
      | h: ?x=true, h1: ?x=false |- _ =>
      rewrite h in h1; easy
      end.

      Ltac resolve_lt_gt :=
      match goal with
      | h: vpg_var_as_OT.compare ?L1 ?L2 = Lt |- _ =>
        pose vv_cmp_lt as _h;
        specialize _h with (1:=h)
      | h: compare_str ?L1 ?L2 = Lt |- _ =>
        pose str_cmp_lt as _h;
        specialize _h with (1:=h)
      end.

      all: try resolve_lt_gt; eauto.

      all: try (eqb_True; resolve_eqb).

      all: try refl_gt_lt; subst; try resolve_eqb.

      all: match goal with
      | |- _ ?x ?y =>
        unfold compare_str in h;
        destruct (OrderedTypeEx.String_as_OT.cmp_lt y x);
        destruct (String_as_OT.compare_spec y x); subst; try easy
      end.
      
    Qed.


  End eb_as_OT.

  Ltac app_lt_trans_ve :=
    match goal with
    | H: ea_as_OT.lt ?t0 ?t1,
      H0: ea_as_OT.lt ?t1 ?t2 |- _ =>
      destruct (ea_as_OT.lt_strorder) as [_ h]
      ; pose (h t0 t1 t2 H H0)
    | H: ec_as_OT.lt ?t0 ?t1,
      H0: ec_as_OT.lt ?t1 ?t2 |- _ =>
      destruct (ec_as_OT.lt_strorder) as [_ h]
      ; pose (h t0 t1 t2 H H0)
    | H: eb_as_OT.lt ?t0 ?t1,
      H0: eb_as_OT.lt ?t1 ?t2 |- _ =>
      destruct (eb_as_OT.lt_strorder) as [_ h]
      ; pose (h t0 t1 t2 H H0)
    end.

  Ltac resolve_CompareSpec_ve :=
    match goal with
    | h: ea_as_OT.compare ?v ?v0 = _ |- _ =>
      destruct (ea_as_OT.compare_spec v v0) as [_h | _h | _h]
      ; try (inversion _h; subst; constructor)
      ; try easy
    | h: ec_as_OT.compare ?v ?v0 = _ |- _ =>
      destruct (ec_as_OT.compare_spec v v0) as [_h | _h | _h]
      ; try (inversion _h; subst; constructor)
      ; try easy
    | h: eb_as_OT.compare ?v ?v0 = _ |- _ =>
      destruct (eb_as_OT.compare_spec v v0) as [_h | _h | _h]
      ; try (inversion _h; subst; constructor)
      ; try easy
    end.

  Module vaot := Compare2EqBool(ea_as_OT).
  Module vcot := Compare2EqBool(ec_as_OT).
  Module vbot := Compare2EqBool(eb_as_OT).

  Module opea_as_OT <: OrderedType.
    Definition t := option CalEdge.
    Definition eq := @eq (option CalEdge).
    Local Instance eq_equiv : Equivalence eq.
      split; unfold eq.
      intros s; induction s; simpl; auto.
      eauto with misc.
      unfold Transitive. apply eq_trans.
    Qed.

    Definition cale_dec : forall c1 c2 : t, {c1 = c2} + {c1 <> c2}.
    Proof. decide equality; eauto with misc. Qed.
    Definition eq_dec := cale_dec.

    Global Hint Resolve cale_dec : misc.

    Definition lt (x y: t) := 
      match x, y with 
      | None, Some _ => True
      | Some v1, Some v2 => ea_as_OT.lt v1 v2
      | _, _ => False
      end.


    Local Instance lt_strorder : StrictOrder lt.
    Proof.
      split; unfold lt.
      1: {
        intros s t; destruct s; try (contradiction);

        match goal with
        | h: _ ?x ?x |- _ =>
          (destruct (ea_as_OT.lt_strorder);
          destruct (StrictOrder_Irreflexive x); eauto) +
          (destruct (ec_as_OT.lt_strorder);
          destruct (StrictOrder_Irreflexive x); eauto) +
          (destruct (eb_as_OT.lt_strorder);
          destruct (StrictOrder_Irreflexive x); eauto)
        end.
      }

      intros s t z; destruct s; destruct t; destruct z;
      try contradiction; intros; eauto with misc.
      app_lt_trans_ve; eauto.
    Qed.
    
    Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof.
      unfold Proper, eq, lt; split; 
      destruct x; destruct x0; destruct y; destruct y0;
      eauto with misc; intro h; try (contradiction); 
      inversion H; inversion H0; subst; eauto with misc.
    Qed.

    Definition compare x y : comparison :=
      match x, y with 
      | None, None => Eq
      | None, Some _ => Lt 
      | Some _, None => Gt 
      | Some v1, Some v2 => ea_as_OT.compare v1 v2
      end.

    Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
    Proof.
      intros x y;
      case_eq (compare x y);
      destruct x; destruct y;
      intro h; unfold compare in h.

      resolve_CompareSpec_ve.
      all: inversion h.
      all: repeat (constructor).
      all: resolve_CompareSpec_ve;
      constructor; eauto.
    Qed.

  End opea_as_OT.

  Module ve_as_OT <: OrderedType.
    Definition t := VE.
    Definition eq := @eq VE.
    Local Instance eq_equiv : Equivalence eq.
    Proof.
      split; unfold eq.
      intros s; induction s; simpl; auto.
      eauto with misc.
      unfold Transitive. apply eq_trans.
    Qed.

    Definition ve_dec : ∀ c1 c2 : VE, {c1 = c2} + {c1 != c2}.
    Proof. decide equality; eauto with misc. Qed.
    Definition eq_dec := ve_dec.

    Global Hint Resolve ve_dec : misc.

    Definition lt (x y: t) := 
      match x, y with 
      | Calv _, Plnv _ => True
      | Calv _, Retv _ => True
      | Calv v1, Calv v2 => ea_as_OT.lt v1 v2
      | Plnv v1, Plnv v2 => ec_as_OT.lt v1 v2
      | Plnv _, Calv _ => False
      | Plnv _, Retv _ => True
      | Retv _, Plnv _ => False
      | Retv _, Calv _ => False
      | Retv v1, Retv v2 => eb_as_OT.lt v1 v2
      end.

    Local Instance lt_strorder : StrictOrder lt.
    Proof.
      split; unfold lt.
      1: {
        intros s t; destruct s; try (contradiction);

        match goal with
        | h: _ ?x ?x |- _ =>
          (destruct (ea_as_OT.lt_strorder);
          destruct (StrictOrder_Irreflexive x); eauto) +
          (destruct (ec_as_OT.lt_strorder);
          destruct (StrictOrder_Irreflexive x); eauto) +
          (destruct (eb_as_OT.lt_strorder);
          destruct (StrictOrder_Irreflexive x); eauto)
        end.
      }

      intros s t z; destruct s; destruct t; destruct z;
      try contradiction; intros; eauto with misc;
      app_lt_trans_ve; eauto.
    Qed.

    
    Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
    Proof.
      unfold Proper, eq, lt; split; 
      destruct x; destruct x0; destruct y; destruct y0;
      eauto with misc; intro h; try (contradiction); 
      inversion H; inversion H0; subst; eauto with misc.
    Qed.

    Definition compare x y : comparison :=
      match x, y with
      | Calv _, Plnv _ => Lt
      | Calv _, Retv _ => Lt
      | Calv v1, Calv v2 => ea_as_OT.compare v1 v2
      | Plnv v1, Plnv v2 => ec_as_OT.compare v1 v2
      | Plnv _, Calv _ => Gt
      | Plnv _, Retv _ => Lt
      | Retv _, Plnv _ => Gt
      | Retv _, Calv _ => Gt
      | Retv v1, Retv v2 => eb_as_OT.compare v1 v2
      end.

    Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
      Proof.
        intros x y;
        case_eq (compare x y);
        destruct x; destruct y;
        intro h; unfold compare in h.

        all: constructor; simpl.
        
        all: try easy.

        all: try resolve_CompareSpec_ve.
      Qed.

  End ve_as_OT.

  Module ra_as_OT := PairOrderedType opea_as_OT ea_as_OT.
  Module rc_as_OT := PairOrderedType opea_as_OT ec_as_OT.
  Module rb_as_OT := PairOrderedType opea_as_OT eb_as_OT.

  Module va_set := MSetList.Make ra_as_OT.
  Module vc_set := MSetList.Make rc_as_OT.
  Module vb_set := MSetList.Make rb_as_OT.

  (* end hide *)

  (** [ME]: an element of a forest [M], i.e., a parser PDA state. *)
  Inductive ME : Type :=
  | CalCME (ma: va_set.t)
  | PlnCME (mc: vc_set.t)
  | RetCME (mb: vb_set.t).

  (** [VEndWith]: whether a rule ends with a nonterminal. *)
  Inductive VEndWith : (list VE)->var->Prop :=
  | EndC v L: 
    (∃ _v _i _L, v=_v++[Plnv (PlnE _L _i L)])
    -> VEndWith v L
  | EndA1 v L:
    (∃ _v _i _L, v=_v++[Calv (PndCalE _L _i L)])
    -> VEndWith v L
  | EndA2 v L: 
    (∃ _v _a _b _L1 _L2, 
    v=_v++[Calv (MatCalE _L1 _a L _b _L2)])
    -> VEndWith v L
  | EndB1 v L:
    (∃ _v _i _L, v=_v++[Retv (PndRetE _L _i L)])
    -> VEndWith v L
  | EndB2 v L:
    (∃ _v _a _b _L1 _L2,
    v=_v++[Retv (MatRetE _L1 _a _L2 _b L)])
    -> VEndWith v L.

  (** [VBeginWith]: whether a rule begins with a nonterminal. *)
  Inductive VBeginWith : (list VE)->var->Prop :=
  | BeginC v L: 
    (∃ _v _i _L, v=[Plnv (PlnE L _i _L)]++ _v) 
    -> VBeginWith v L
  | BeginA1 v L: 
    (∃ _v _i _L, v=[Calv (PndCalE L _i _L)]++ _v) 
    -> VBeginWith v L
  | BeginA2 v L: 
    (∃ _v _a _b _L1 _L2,  
    v=[Calv (MatCalE L _a _L1 _b _L2)]++ _v) 
    -> VBeginWith v L
  | BeginB v L: 
    (∃ _v _i _L, v=[Retv (PndRetE L _i _L)]++ _v)
    -> VBeginWith v L.

End DEF.

(** The module [Def(G)] declares the big-step derivation [Dm], meaning
    "major derivation", the forward small-step derivation [Df], and the
    backward small-step derivation [Db]. *)
Module Def(G:VPG).

  Include DEF.
  Include G.

  Module DM.
    Import DEF.

    (** [Dm]: the big-step derivation for general VPGs. [Dm] defines 
      how to "correctly" derive a VPG parse tree. *)
    Inductive Dm : var -> list symbol -> list VE -> Prop :=
      | DEps : ∀ L, (in_rules (L, Alt_Epsilon) P) ->  
        Dm L [] []
      | DLa : ∀ L a L1 w' pt', 
        (in_rules (L, Alt_Linear (Call a) L1) P)
        -> Dm L1 w' pt'
        -> Dm L (Call a::w') (Calv (PndCalE L a L1)::pt')
      | DLc : ∀ L c L1 w' pt', 
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> Dm L1 w' pt' 
        -> Dm L (Plain c::w') (Plnv (PlnE L c L1)::pt')
      | DLb : ∀ L b L1 w' pt', 
        (in_rules (L, Alt_Linear (Ret b) L1) P) 
        -> Dm L1 w' pt' 
        -> Dm L (Ret b::w') (Retv (PndRetE L b L1)::pt')
      | DMat : ∀ L a b L1 L2 w1 w2 pt1 pt2, 
        (in_rules (L, Alt_Match (a) (b) L1 L2) P) 
        -> Dm L1 w1 pt1
        -> Dm L2 w2 pt2 
        -> Dm L ([Call a] ++ w1 ++ [Ret b] ++ w2) 
          ([Calv (MatCalE L a L1 b L2)]++pt1++
          [Retv (MatRetE L a L1 b L2)]++pt2).
  End DM.
  
  Module DF.
    Import DEF.

    (** [Df]: the forward small-step derivation for general VPGs. [Df]
        formalizes how the parser PDA extends a single parse tree. *)
    Inductive Df : list VE -> list CalEdge -> list symbol -> Prop :=
      | V_S_Pln : ∀ L c L1, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) -> 
        Df [Plnv ( PlnE L c L1)] [] [Plain c]
      | V_Pln : ∀ L c L1 T v w, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) ->
        VEndWith v L -> 
        Df v T w -> 
        Df (v++[Plnv (PlnE L c L1)]) T (w++[Plain c])

      | V_S_Pnd_Cal: ∀ L a L1, 
        (in_rules (L, Alt_Linear (Call a) L1) P) -> 
        Df [Calv (PndCalE L a L1)] [PndCalE L a L1] [Call a]
      | V_Pnd_Cal : ∀ L a L1 T v w, 
        (in_rules (L, Alt_Linear (Call a) L1) P) -> 
        VEndWith v L ->
        Df v T w -> 
        Df (v++[Calv (PndCalE L a L1)]) 
            ((PndCalE L a L1)::T) 
            (w++[Call a])
      | V_S_Cal : ∀ L a b L1 L2,
        (in_rules (L, Alt_Match (a) (b)  L1 L2) P) -> 
        Df ([Calv (MatCalE L a L1 b L2)]) 
          [(MatCalE L a L1 b L2)] 
          [Call a]
      | V_Cal : ∀ L a b L1 L2 T v w, 
        (in_rules (L, Alt_Match (a) (b)  L1 L2) P) -> 
        VEndWith v L ->
        Df v T w -> 
        Df (v++[Calv (MatCalE L a L1 b L2)]) 
          ((MatCalE L a L1 b L2)::T) 
            (w++[Call a])

      | V_S_Pen_Ret: ∀ L L1 b, 
        (in_rules (L, Alt_Linear (Ret b) L1) P) -> 
        Df [Retv (PndRetE L b L1)] [] [Ret b]
      | V_Pnd_Ret_bot : ∀ L b L1 v w, 
        (in_rules (L, Alt_Linear (Ret b) L1) P) -> 
        VEndWith v L ->
        Df v [] w -> 
        Df (v++[Retv (PndRetE L b L1)]) [] (w++[Ret b])
      | V_Pnd_Ret : ∀ L b L1 v w t T, 
        (in_rules (L, Alt_Linear (Ret b) L1) P) -> 
        VEndWith v L ->
        Df v (t::T) w -> 
        Df (v++[Retv (PndRetE L b L1)]) T (w++[Ret b])
      | V_Ret : ∀ L a b L1 L2 L3 v w T, 
        (* (in_rules (L1, Alt_Match (a) (b)  L2 L3) P) -> *)
        VEndWith v L -> 
        (in_rules (L, Alt_Epsilon) P) -> 
        Df v ((MatCalE L1 a L2 b L3)::T) w -> 
        Df (v++[Retv (MatRetE L1 a L2 b L3)])
        T
        (w ++ [Ret b]).

    (** [getSym]: get the symbol of a call rule.  *)
    Definition getSym t := 
      match t with 
      | PndCalE _ a _ => Call a
      | MatCalE _ a _ _ _ => Call a
      end.

    (** [Dfx]: the extended forward small-step derivation 
        [Dfx v T w v1 v2 w1 w2]; 
        the string [w] is split to [w=w1 a w2], where [a] is the last
        unmatched call symbol; the parse tree [v] is accordingly split 
        to [v=v1 ++ [ra] ++ v2]. *)
    Inductive Dfx : list VE -> list CalEdge -> list symbol -> 
    (list VE) -> (list VE) -> (list symbol) -> (list symbol) -> Prop 
    :=
      | Vx_S_Pln : ∀ L c L1, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) -> 
        Dfx [Plnv (PlnE L c L1)] [] [Plain c] 
        [] [Plnv (PlnE L c L1)] [] [Plain c]
      | Vx_Pln : ∀ L c L1 T v w v1 v2 w1 w2, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) ->
        VEndWith v L -> 
        Dfx v T w v1 v2 w1 w2 -> 
        Dfx (v++[Plnv (PlnE L c L1)]) T (w++[Plain c])
        v1 (v2++[Plnv (PlnE L c L1)]) w1 (w2++[Plain c])

      | Vx_S_Pnd_Cal: ∀ L a L1, 
        (in_rules (L, Alt_Linear (Call a) L1) P) -> 
        Dfx [Calv (PndCalE L a L1)] [PndCalE L a L1] [Call a]
        [] [] [] []
      | Vx_Pnd_Cal : ∀ L a L1 T v w v1 v2 w1 w2,
        (in_rules (L, Alt_Linear (Call a) L1) P) -> 
        VEndWith v L ->
        Dfx v T w v1 v2 w1 w2 -> 
        Dfx (v++[Calv (PndCalE L a L1)]) 
          ((PndCalE L a L1)::T) 
          (w++[Call a])
          v [] w []
      | Vx_S_Cal : ∀ L a b L1 L2,
        (in_rules (L, Alt_Match (a) (b)  L1 L2) P) -> 
        Dfx [Calv (MatCalE L a L1 b L2)] [MatCalE L a L1 b L2] [Call a]
        [] [] [] []
      | Vx_Cal : ∀ L a b L1 L2 T v w v1 v2 w1 w2, 
        (in_rules (L, Alt_Match (a) (b)  L1 L2) P) -> 
        VEndWith v L ->
        Dfx v T w v1 v2 w1 w2 ->
        Dfx (v++[Calv (MatCalE L a L1 b L2)]) 
          ((MatCalE L a L1 b L2)::T) 
          (w++[Call a])
          v [] w []

      | Vx_S_Pen_Ret: ∀ L L1 b, 
        (in_rules (L, Alt_Linear (Ret b) L1) P) -> 
        Dfx [Retv (PndRetE L b L1)] [] [Ret b]
        [] [Retv (PndRetE L b L1)] [] [Ret b]
      | Vx_Pnd_Ret_bot : ∀ L b L1 v w v1 v2 w1 w2,
        (in_rules (L, Alt_Linear (Ret b) L1) P) -> 
        VEndWith v L ->
        Dfx v [] w v1 v2 w1 w2 ->
        Dfx (v++[Retv (PndRetE L b L1)]) [] (w++[Ret b])
        [] (v++[Retv (PndRetE L b L1)]) [] (w++[Ret b])
      | Vx_Pnd_Ret_nohead : ∀ L b L1 v w t v2 w1 w2,
        (in_rules (L, Alt_Linear (Ret b) L1) P) -> 
        VEndWith v L ->
        Dfx v [t] w [] v2 w1 w2 ->
        Dfx (v++[Retv (PndRetE L b L1)]) [] (w++[Ret b])
        [] (v++[Retv (PndRetE L b L1)]) [] (w++[Ret b])
      | Vx_Pnd_Ret : ∀ L b L1 v w t T v1 v2 w1 w2 v11 v12 w11 w12,
        (in_rules (L, Alt_Linear (Ret b) L1) P) -> 
        VEndWith v L ->
        Dfx v (t::T) w v1 v2 w1 w2 ->
        Dfx v1 T w1 v11 v12 w11 w12 ->
        Dfx (v++[Retv (PndRetE L b L1)]) T (w++[Ret b])
          v11 (v12++[Calv t]++v2++[Retv (PndRetE L b L1)]) w11 
          (w12++[getSym t]++w2++[Ret b])
      | Vx_Ret_nohead : ∀ L a b L1 L2 L3 v w v2 w1 w2,
        VEndWith v L -> 
        (in_rules (L, Alt_Epsilon) P) -> 
        Dfx v [MatCalE L1 a L2 b L3] w [] v2 w1 w2 -> 
        Dfx (v++[Retv (MatRetE L1 a L2 b L3)]) [] (w ++ [Ret b])
        [] (v++[Retv (MatRetE L1 a L2 b L3)]) [] (w ++[Ret b])
      | Vx_Ret : ∀ L a b L1 L2 L3 v w T v1 v2 w1 w2 v11 v12 w11 w12,
        VEndWith v L -> 
        (in_rules (L, Alt_Epsilon) P) -> 
        Dfx v ((MatCalE L1 a L2 b L3)::T) w v1 v2 w1 w2 -> 
        Dfx v1 T w1 v11 v12 w11 w12 ->
        Dfx (v++[Retv (MatRetE L1 a L2 b L3)]) T (w ++ [Ret b])
        v11 (v12++[Calv (MatCalE L1 a L2 b L3)]++v2++
          [Retv (MatRetE L1 a L2 b L3)]) 
          w11 
          (w12++[Call a]++w2++[Ret b]).

  End DF.

  Module DB.
    Import DEF.

    (** [Db]: the backward small-step derivation for general VPGs. [Db]
        formalizes how the extraction PDA extends a single parse tree.
        *)
    Inductive Db : list VE -> list RetEdge -> list symbol -> Prop :=
      | V_S_Pln : ∀ L c L1, 
        (in_rules (L, Alt_Linear (Plain c) L1) P)
        -> (in_rules (L1, Alt_Epsilon) P)
        -> Db [Plnv (PlnE L c L1)] [] [Plain c]
      | V_Pln_b1 : ∀ L c b L1 L2 T v w, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> Db v ((PndRetE L1 b L2)::T) (Ret b::w)
        -> Db ([Plnv (PlnE L c L1)]++v) 
          ((PndRetE L1 b L2)::T) (Plain c::Ret b::w)
      | V_Pln_b2 : ∀ L c b L1 L2 a L3 L4 T v w, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> (in_rules (L1, Alt_Epsilon) P)
        -> Db v ((MatRetE L2 a L3 b L4)::T) (Ret b::w)
        -> Db ([Plnv (PlnE L c L1)]++v) 
          ((MatRetE L2 a L3 b L4)::T) (Plain c::Ret b::w)
      | V_Pln_a : ∀ L c a L1 T v w, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> VBeginWith v L1
        -> Db v T (Call a::w)
        -> Db ([Plnv (PlnE L c L1)]++v) T (Plain c::Call a::w)
      | V_Pln_c : ∀ L c c2 L1 T v w, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> VBeginWith v L1
        -> Db v T (Plain c2::w)
        -> Db ([Plnv (PlnE L c L1)]++v) T 
          (Plain c::Plain c2::w)
      | V_Cal_Pnd_S: ∀ L a L1, 
        (in_rules (L, Alt_Linear (Call a) L1) P) 
        -> (in_rules (L1, Alt_Epsilon) P) 
        -> Db [Calv (PndCalE L a L1)] [] [Call a]
      | V_Cal_Pnd_bot : ∀ L a L1 v w, 
        (in_rules (L, Alt_Linear (Call a) L1) P) 
        -> VBeginWith v L1
        -> Db v [] w 
        -> Db ([Calv (PndCalE L a L1)]++v) [] (Call a::w)
      | V_Cal_b1 : ∀ L a L1 L2 b L3 T v w, 
        (in_rules (L, Alt_Linear (Call a) L1) P) 
        -> VBeginWith v L1
        -> Db v ((PndRetE L2 b L3)::T) w 
        -> Db ([Calv (PndCalE L a L1)]++v) T (Call a::w)
      | V_Cal_b2 : ∀ L a b L1 L2 T v w, 
        (in_rules (L1, Alt_Epsilon) P)
        -> Db v ((MatRetE L a L1 b L2)::T) (Ret b::w) 
        -> Db ([Calv (MatCalE L a L1 b L2)]++v) T 
          (Call a::Ret b::w)
      | V_Cal_a : ∀ L a a2 b L1 L2 T v w, 
        VBeginWith v L1
        -> Db v ((MatRetE L a L1 b L2)::T) (Call a2::w) 
        -> Db ([Calv (MatCalE L a L1 b L2)]++v) T 
          (Call a::Call a2::w)
      | V_Cal_c : ∀ L a c b L1 L2 T v w, 
        VBeginWith v L1
        -> Db v ((MatRetE L a L1 b L2)::T) (Plain c::w) 
        -> Db ([Calv (MatCalE L a L1 b L2)]++v) T 
          (Call a::Plain c::w)
      | V_Ret_Pnd_S : ∀ L L1 b, 
        (in_rules (L, Alt_Linear (Ret b) L1) P) 
        -> (in_rules (L1, Alt_Epsilon) P) 
        -> Db [Retv (PndRetE L b L1)] [(PndRetE L b L1)] 
          [Ret b]
      | V_Ret_Pnd_bot : ∀ L b L1 v w,
        (in_rules (L, Alt_Linear (Ret b) L1) P)
        -> VBeginWith v L1
        -> Db v [] w
        -> Db (Retv (PndRetE L b L1)::v)
          [PndRetE L b L1] (Ret b::w)
      | V_Ret_Pnd : ∀ L b L1 L2 b2 L3 v w T,
        (in_rules (L, Alt_Linear (Ret b) L1) P)
        -> VBeginWith v L1
        -> Db v (PndRetE L2 b2 L3::T) w
        -> Db (Retv (PndRetE L b L1)::v)
          (PndRetE L b L1::PndRetE L2 b2 L3::T) ([Ret b]++w)
      | V_Ret_S : ∀ L a b L1 L2,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> in_rules (L2, Alt_Epsilon) P 
        -> Db [Retv (MatRetE L a L1 b L2)] 
          [MatRetE L a L1 b L2] [Ret b]
      | V_Ret_bot : ∀ L a b L1 L2 v w,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Db v [] w
        -> Db (Retv (MatRetE L a L1 b L2)::v)
          [MatRetE L a L1 b L2] (Ret b::w)
      | V_Ret_b1 : ∀ L a b L1 L2 L3 b2 L4 v w T,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Db v (PndRetE L3 b2 L4::T) w
        -> Db (Retv (MatRetE L a L1 b L2)::v)
          (MatRetE L a L1 b L2::PndRetE L3 b2 L4::T) (Ret b::w)
      | V_Ret_b2_b : ∀ L a b L1 L2 L3 a2 L4 b2 L5 v w T,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> Db v (MatRetE L3 a2 L4 b2 L5::T) (Ret b2::w)
        -> (in_rules (L2, Alt_Epsilon) P)
        -> Db ([Retv (MatRetE L a L1 b L2)]++v)
          (MatRetE L a L1 b L2::MatRetE L3 a2 L4 b2 L5::T) 
          (Ret b::Ret b2::w)
      | V_Ret_b2_c : 
        ∀ L a b L1 L2 L3 a2 L4 b2 L5 c2 v w T,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Db v (MatRetE L3 a2 L4 b2 L5::T) (Plain c2::w)
        -> Db ([Retv (MatRetE L a L1 b L2)]++v)
          (MatRetE L a L1 b L2::MatRetE L3 a2 L4 b2 L5::T) 
          (Ret b::Plain c2::w)
      | V_Ret_b2_a : 
        ∀ L a b L1 L2 L3 a2 L4 b2 L5 a3 v w T,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Db v (MatRetE L3 a2 L4 b2 L5::T) (Call a3::w)
        -> Db ([Retv (MatRetE L a L1 b L2)]++v)
          (MatRetE L a L1 b L2::MatRetE L3 a2 L4 b2 L5::T) 
          (Ret b::Call a3::w).

    (** [Dfx]: the extended backward small-step derivation 
      [Dbx v T w v1 v2 w1 w2]; 
      the string [w] is split to [w=w1 b w2], where [b] is the last
      unmatched return symbol; the parse tree [v] is accordingly split 
      to [v=v1 ++ [rb] ++ v2]. *)
    Inductive Dbx : list VE -> list RetEdge -> list symbol 
      -> (list VE) -> (list VE) -> (list symbol) -> (list symbol) 
      -> Prop :=
      | Vb_S_Pln : ∀ L c L1, 
        (in_rules (L, Alt_Linear (Plain c) L1) P)
        -> (in_rules (L1, Alt_Epsilon) P)
        -> Dbx [Plnv (PlnE L c L1)] [] [Plain c]
        [Plnv (PlnE L c L1)] [] [Plain c] []
      | Vb_Pln_b1 : ∀ L c b L1 L2 T v w v1 w1,
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> Dbx v ((PndRetE L1 b L2)::T) (Ret b::w)
          [] v1 [] w1
        -> Dbx ([Plnv (PlnE L c L1)]++v) ((PndRetE L1 b L2)::T) 
        (Plain c::Ret b::w)
          [Plnv (PlnE L c L1)] v1 [Plain c] w1
      | Vb_Pln_b2 : ∀ L c b L1 L2 a L3 L4 T v w v1 w1,
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> (in_rules (L1, Alt_Epsilon) P)
        -> Dbx v ((MatRetE L2 a L3 b L4)::T) (Ret b::w)
          [] v1 [] w1
        -> Dbx ([Plnv (PlnE L c L1)]++v) ((MatRetE L2 a L3 b L4)::T) 
        (Plain c::Ret b::w)
          [Plnv (PlnE L c L1)] v1 [Plain c] w1
      | Vb_Pln_a : ∀ L c a L1 T v w v1 v2 w1 w2, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> VBeginWith v L1
        -> Dbx v T (Call a::w)
          v1 v2 w1 w2
        -> Dbx ([Plnv (PlnE L c L1)]++v) T (Plain c::Call a::w)
          (Plnv (PlnE L c L1)::v1) v2 (Plain c::w1) w2
      | Vb_Pln_c : ∀ L c c2 L1 T v w v1 v2 w1 w2, 
        (in_rules (L, Alt_Linear (Plain c) L1) P) 
        -> VBeginWith v L1
        -> Dbx v T (Plain c2::w)
          v1 v2 w1 w2
        -> Dbx ([Plnv (PlnE L c L1)]++v) T (Plain c::Plain c2::w)
          (Plnv (PlnE L c L1)::v1) v2 (Plain c::w1) w2

      | Vb_Cal_Pnd_S: ∀ L a L1, 
        (in_rules (L, Alt_Linear (Call a) L1) P) 
        -> (in_rules (L1, Alt_Epsilon) P) 
        -> Dbx [Calv (PndCalE L a L1)] [] [Call a]
          [Calv (PndCalE L a L1)] [] [Call a] []
      | Vb_Cal_Pnd_bot : ∀ L a L1 v w v1 w1, 
        (in_rules (L, Alt_Linear (Call a) L1) P) 
        -> VBeginWith v L1
        -> Dbx v [] w v1 [] w1 []
        -> Dbx ([Calv (PndCalE L a L1)]++v) [] (Call a::w)
          ([Calv (PndCalE L a L1)]++v) [] (Call a::w) []
      | Vb_Cal_b1_emp : ∀ L a L1 L2 b L3 v w v1 w1,
        (in_rules (L, Alt_Linear (Call a) L1) P) 
        -> VBeginWith v L1
        -> Dbx v [PndRetE L2 b L3] w v1 [] w1 []
        -> Dbx ([Calv (PndCalE L a L1)]++v) [] (Call a::w)
          ([Calv (PndCalE L a L1)]++v) []
          ([Call a]++w) []
      | Vb_Cal_b1 : ∀ L a L1 L2 b L3 T v w v1 v2 w1 w2 v21 v22 w21 w22,
        (in_rules (L, Alt_Linear (Call a) L1) P) 
        -> VBeginWith v L1
        -> Dbx v ((PndRetE L2 b L3)::T) w v1 v2 w1 w2
        -> Dbx v2 T w2 v21 v22 w21 w22
        -> Dbx ([Calv (PndCalE L a L1)]++v) T (Call a::w)
          ([Calv (PndCalE L a L1)]++v1++[Retv (PndRetE L2 b L3)]++v21) v22
          ([Call a]++w1++[Ret b]++w21) w22
      | Vb_Cal_b2_b_emp : ∀ L a b L1 L2,
        (in_rules (L1, Alt_Epsilon) P)
        -> Dbx [Retv (MatRetE L a L1 b L2)] [MatRetE L a L1 b L2] [Ret b]
          [] [] [] [] 
        -> Dbx 
          ([Calv (MatCalE L a L1 b L2)]++[Retv (MatRetE L a L1 b L2)]) 
          [] 
          ([Call a]++[Ret b])
          ([Calv (MatCalE L a L1 b L2)]++[Retv (MatRetE L a L1 b L2)]) 
          []
          ([Call a]++[Ret b]) []
      | Vb_Cal_b2_b : ∀ L a b L1 L2 T v w v2 w2 v21 v22 w21 w22, 
        (in_rules (L1, Alt_Epsilon) P)
        -> Dbx v ((MatRetE L a L1 b L2)::T) (Ret b::w)
          [] v2 [] w2
        -> Dbx v2 T w2 v21 v22 w21 w22
        -> Dbx ([Calv (MatCalE L a L1 b L2)]++v) T (Call a::Ret b::w)
          ([Calv (MatCalE L a L1 b L2)]
            ++[Retv (MatRetE L a L1 b L2)]++v21) v22
          ([Call a]++[Ret b]++w21) w22
      | Vb_Cal_b2_a : ∀ L a a2 b L1 L2 T 
          v w v1 v2 w1 w2 v21 v22 w21 w22, 
        VBeginWith v L1
        -> Dbx v ((MatRetE L a L1 b L2)::T) (Call a2::w) v1 v2 w1 w2
        -> Dbx v2 T w2 v21 v22 w21 w22
        -> Dbx ([Calv (MatCalE L a L1 b L2)]++v) T (Call a::Call a2::w)
          ([Calv (MatCalE L a L1 b L2)]++v1
            ++[Retv (MatRetE L a L1 b L2)]++v21) v22
          ([Call a]++w1++[Ret b]++w21) w22
      | Vb_Cal_b2_a_emp : ∀ L a a2 b L1 L2 v w v1 w1,
        VBeginWith v L1
        -> Dbx v [MatRetE L a L1 b L2] (Call a2::w) v1 [] w1 []
        -> Dbx ([Calv (MatCalE L a L1 b L2)]++v) [] (Call a::Call a2::w)
          ([Calv (MatCalE L a L1 b L2)]++v) []
          ([Call a]++[Call a2]++w) []
      | Vb_Cal_b2_c : ∀ L a c b L1 L2 T v w v1 v2 w1 w2 v21 v22 w21 w22, 
        VBeginWith v L1
        -> Dbx v ((MatRetE L a L1 b L2)::T) (Plain c::w) v1 v2 w1 w2
        -> Dbx v2 T w2 v21 v22 w21 w22
        -> Dbx ([Calv (MatCalE L a L1 b L2)]++v) T (Call a::Plain c::w)
          ([Calv (MatCalE L a L1 b L2)]++v1
            ++[Retv (MatRetE L a L1 b L2)]++v21) v22
          ([Call a]++w1++[Ret b]++w21) w22
      | Vb_Cal_b2_c_emp : ∀ L a c b L1 L2 v w v1 w1, 
        VBeginWith v L1
        -> Dbx v [MatRetE L a L1 b L2] (Plain c::w) v1 [] w1 []
        -> Dbx ([Calv (MatCalE L a L1 b L2)]++v) [] (Call a::Plain c::w)
          ([Calv (MatCalE L a L1 b L2)]++v) []
          ([Call a]++[Plain c]++w) []

      | Vb_Ret_Pnd_S : ∀ L L1 b, 
        (in_rules (L, Alt_Linear (Ret b) L1) P) 
        -> (in_rules (L1, Alt_Epsilon) P) 
        -> Dbx [Retv (PndRetE L b L1)] [(PndRetE L b L1)] 
          [Ret b] [] [] [] []
      | Vb_Ret_Pnd_bot : ∀ L b L1 v w,
        (in_rules (L, Alt_Linear (Ret b) L1) P)
        -> VBeginWith v L1
        -> Dbx v [] w v [] w []
        -> Dbx (Retv (PndRetE L b L1)::v) [PndRetE L b L1] (Ret b::w)
          [] v [] w
      | Vb_Ret_Pnd : ∀ L b L1 L2 b2 L3 v w T v1 v2 w1 w2,
        (in_rules (L, Alt_Linear (Ret b) L1) P)
        -> VBeginWith v L1
        -> Dbx v (PndRetE L2 b2 L3::T) w v1 v2 w1 w2
        -> Dbx (Retv (PndRetE L b L1)::v) 
          (PndRetE L b L1::PndRetE L2 b2 L3::T) ([Ret b]++w)
          [] v [] w
      | Vb_Ret_S : ∀ L a b L1 L2,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> in_rules (L2, Alt_Epsilon) P 
        -> Dbx [Retv (MatRetE L a L1 b L2)] [MatRetE L a L1 b L2] 
          [Ret b]
          [] [] [] []
      | Vb_Ret_bot : ∀ L a b L1 L2 v w,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Dbx v [] w v [] w []
        -> Dbx (Retv (MatRetE L a L1 b L2)::v) [MatRetE L a L1 b L2] 
          (Ret b::w)
          [] v [] w
      | Vb_Ret_b1 : ∀ L a b L1 L2 L3 b2 L4 v w T v1 v2 w1 w2,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Dbx v (PndRetE L3 b2 L4::T) w v1 v2 w1 w2
        -> Dbx (Retv (MatRetE L a L1 b L2)::v) 
          (MatRetE L a L1 b L2::PndRetE L3 b2 L4::T) (Ret b::w)
          [] v [] w
      | Vb_Ret_b2_b : ∀ L a b L1 L2 L3 a2 L4 b2 L5 v w T v1 v2 w1 w2,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> Dbx v (MatRetE L3 a2 L4 b2 L5::T) (Ret b2::w) v1 v2 w1 w2
        -> (in_rules (L2, Alt_Epsilon) P)
        -> Dbx ([Retv (MatRetE L a L1 b L2)]++v) 
          (MatRetE L a L1 b L2::MatRetE L3 a2 L4 b2 L5::T) 
          (Ret b::Ret b2::w)
          [] v [] (Ret b2::w)
      | Vb_Ret_b2_c : 
        ∀ L a b L1 L2 L3 a2 L4 b2 L5 c2 v w T v1 v2 w1 w2,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Dbx v (MatRetE L3 a2 L4 b2 L5::T) (Plain c2::w) v1 v2 w1 w2
        -> Dbx ([Retv (MatRetE L a L1 b L2)]++v) 
          (MatRetE L a L1 b L2::MatRetE L3 a2 L4 b2 L5::T) 
          (Ret b::Plain c2::w)
          [] v [] (Plain c2::w)
      | Vb_Ret_b2_a : 
        ∀ L a b L1 L2 L3 a2 L4 b2 L5 a3 v w T v1 v2 w1 w2,
        (in_rules (L, Alt_Match (a) (b) L1 L2) P)
        -> VBeginWith v L2
        -> Dbx v (MatRetE L3 a2 L4 b2 L5::T) (Call a3::w) v1 v2 w1 w2
        -> Dbx ([Retv (MatRetE L a L1 b L2)]++v) 
          (MatRetE L a L1 b L2::MatRetE L3 a2 L4 b2 L5::T) 
          (Ret b::Call a3::w)
          [] v [] (Call a3::w).
    
    (** [getSym]: get the symbol of a return rule.  *)
    Definition getSym t := 
      match t with 
      | PndRetE _ b _ => Ret b
      | MatRetE _ _ _ b _ => Ret b
      end.
  End DB.

  (** [|V|]: the number of parse trees in [V]. *)
  Notation "| V |" := (List.length V)
  (at level 10, V at next level).

  Definition lenM m :=
    match m with
    | DEF.PlnCME m => length (DEF.vc_set.elements m)
    | DEF.CalCME m => length (DEF.va_set.elements m)
    | DEF.RetCME m => length (DEF.vb_set.elements m)
    end.

  (** [||M||]: the length of a parse forest. *)
  Notation "|| m ||" := (lenM m)
  (at level 10, m at next level).

End Def.
