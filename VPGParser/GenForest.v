(** This file first defines the parsing function [p], which reads a
    string [s], runs the parser PDA, and generates a forest [M]. The
    relation [Forest w T M] is then defined based on [p], which
    roughly means M=p(w). This file then verifies two properties for
    the forest relation, namely [PForest1] and [PForest2]. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

Require Import Coq.Unicode.Utf8_core.

Require Import Misc.
Require Import Def.

Require Import ForwardSmallStep.

Import Misc.Basic.
Import Misc.vpg.

Require Import Lia.
Require Import PreTimed.

Import LEN_WF.


(** The module [Parser] accepts a VPG and declares the parsing function
  [p]. *)
Module Parser (G:VPG).
  (* begin hide *)

  Module PreTimed := PreTimed(G).
  Include PreTimed.

  Import PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Tacs.
  Import PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Def.DF.
  Import PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.DFX.
  Import PreTimed.Dbx.BackwardSmallStep.Core.
  Import PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Core.
  Import PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Df2.

  Ltac resolve_eqvv := match goal with
  | H: eqvv ?v1 ?v2 = true |- _ =>
    pose (vv_lt_eqbeq _ _ H) as _e;
    rewrite _e in *;
    clear _e H
  end.

  Ltac resolve_eqb := match goal with
  | H: eqb ?v1 ?v2 = true |- _ =>
      destruct (eqb_true_iff v1 v2) as [_H1 _];
      pose (_H1 H) as _e;
      rewrite _e in *;
      clear _e H
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

  Ltac resolveIn :=
    match goal with 
    | H: ∀ rr, In ?r ?l <-> _ ,
      H2: In ?x ?l
    |- _ =>
      pose (H x) as Hex
      ; destruct Hex as [_Hex _]
      ; pose (_Hex H2) as Hex
      ; destruct Hex as [L' [Hex1 Hex2]]
      ; clear _Hex
    end.

  (* end hide *)

  (** [p_sym]: the pseudo-symbol used for constructing the initial state
      [m0], which is defined below. *)
  Definition p_sym := ""%string.

  (** [m0]: the initial parser PDA state is [{None, L0 -> c0 L0}]. *)
  Definition m0 : ME :=
      PlnCME (vc_set.singleton (None, PlnE L_0 p_sym L_0)).

  (* begin hide *)

  Ltac resolveEndESelf :=
    match goal with
    | |- VEndWith [?v] (endE ?v) =>
     destruct v
    end;
    match goal with
    | |- VEndWith [_ ?v] _ =>
     destruct v
    end;
    try extractEnds;
    simpl;
    match goal with
    | |- VEndWith [Calv (PndCalE _ _ _)] _ =>
      apply EndA1;
      exists []; simpl; eauto
    | |- VEndWith [Calv (MatCalE _ _ _ _ _)] _ =>
      apply EndA2;
      exists []; simpl; eauto
      | |- VEndWith [Plnv (PlnE _ _ _)] _ =>
      apply EndC;
      exists []; simpl; eauto
    | |- VEndWith [Retv (PndRetE _ _ _)] _ =>
      apply EndB1;
      exists []; simpl; eauto
    | |- VEndWith [Retv (MatRetE _ _ _ _ _)] _ =>
      apply EndB2;
      exists []; simpl; eauto
    end.

  Definition findRuleWithLc L i :=
    List.filter (fun r =>
      match r with
      | (Lr, Alt_Linear i' L') => andb (eqvv Lr L) (eqs i i')
      | _ => false
      end) P.

  Lemma L_findRuleWithLc: ∀ L i, ∀ r,
    List.In r (findRuleWithLc L i) <->
    ∃ L', r = (L, Alt_Linear i L') /\ in_rules r P.
  Proof.
    unfold findRuleWithLc.
    split.

    1:{
      intro Hin.
      pose (List.filter_In).

      match goal with 
      | Hin : In ?r (filter ?f ?P) |- _ =>
        pose (List.filter_In f r P) as Hin2
      end.

      destruct Hin2 as [Hin1 _].
      pose (Hin1 Hin).
      destruct r as [v alt].

      destruct alt;
      try (destruct a;
      inversion H0).

      exists v0.

      match goal with 
      | Heq: ?s1 && ?s2 = true |- _ =>
        destruct (andb_true_iff s1 s2) as [_h1 _];
        destruct (_h1 Heq) as [_hsep1 _hsep2]
      end.

      resolve_eqs.
      resolve_eqvv.

      split; auto. 
    }

    intro Hin.
    destruct Hin as [L' [Hin1 Hin2]].
    apply (List.filter_In).
    split.
    eauto.
    inversion Hin1.
    eauto.

    match goal with 
    | |- ?s1 && ?s2 = true =>
      apply (andb_true_iff s1 s2)
    end.

    split.
    apply vvot.eqb_eq. auto.
    apply sot.eqb_eq. auto.
  Qed.

  Ltac getAnd :=
    match goal with 
    | |- _ /\ _ => 
      split
    end.

  Ltac resolve_eqstr := 
    match goal with
    | H: (?s1 =? ?s2)%string = true |- _ =>
      destruct (String.eqb_eq s1 s2) as [_e _]
      ; specialize _e with (1:=H)
      ; rewrite _e in *
      ; clear _e H
    end.

  Definition findRuleWithMa L i := 
    List.filter (fun r => 
      match r with 
      | (Lr, Alt_Match i' b L' L2) => andb (eqvv Lr L) (String.eqb i i')
      | _ => false
      end) P.
  
  Lemma L_findRuleWithMa: 
    ∀ L i, ∀ r, List.In r (findRuleWithMa L i) <-> 
    ∃ b L' L2, r = (L, Alt_Match i b L' L2) /\ in_rules r P.
  Proof.
    unfold findRuleWithMa.
    split.
    1:{
      intro Hin.
      pose (List.filter_In).

      match goal with 
      | Hin : In ?r (filter ?f ?P) |- _ =>
        pose (List.filter_In f r P) as Hin2
      end.

      destruct Hin2 as [Hin1 _].
      pose (Hin1 Hin).
      destruct r as [v alt].

      destruct alt;
      breakAnd; try discriminate.
      exists t2, v1, v2.
      getAnd; eauto.

      match goal with 
      | Heq: ?s1 && ?s2 = true |- _ =>
        destruct (andb_true_iff s1 s2) as [_h1 _];
        destruct (_h1 Heq) as [_hsep1 _hsep2]
      end.


      resolve_eqstr.
      resolve_eqvv.

      auto. 
    }

    intro Hin.
    destruct Hin as [L' [Hin1 Hin2]].
    apply (List.filter_In).
    destruct Hin2.
    destruct H.
    split.
    eauto.
    inversion H.

    match goal with 
    | |- ?s1 && ?s2 = true =>
      apply (andb_true_iff s1 s2)
    end.

    split.
    apply vvot.eqb_eq. auto.
    apply String.eqb_eq. auto.
  Qed.

  Definition findRuleWithMb L a L1 b :=
    List.filter (fun r => 
    match r with 
    | (Lr, Alt_Match i' i2 L' L'') => 
      (eqvv Lr L) && (eqvv L' L1) && (String.eqb i' a) && (String.eqb i2 b)
    | _ => false
    end) P.
  
  Lemma L_findRuleWithMb: ∀ L a L1 b, ∀ r, List.In r (findRuleWithMb L a L1 b) <-> 
    ∃ L2, r = (L, Alt_Match a b L1 L2) /\ in_rules r P.
  Proof.
    unfold findRuleWithMb.

    split.
    1:{
      intro Hin.
      pose (List.filter_In ).

      match goal with 
      | Hin : In ?r (filter ?f ?P) |- _ =>
        pose (List.filter_In f r P) as Hin2
      end.

      destruct Hin2 as [Hin1 _].
      pose (Hin1 Hin).
      destruct r as [v alt].

      destruct alt;
      try (destruct a0;
      inversion H0).

      exists v2.

      Ltac splitEq := match goal with 
      | Heq: ?s1 && ?s2 = true |- _ =>
        destruct (andb_true_iff s1 s2) as [_h1 _];
        destruct (_h1 Heq) as [_hsep1 _hsep2]
      end.
      splitEq.

      match goal with 
      | Heq: ?s1 && ?s2 && ?s3 = true |- _ =>
        destruct (andb_true_iff s1 (s2 && s3)) as [_h1' _]
      end.
      rewrite <- andb_assoc  in _hsep1.
      pose (_h1' _hsep1).
      destruct a0.

      match goal with 
      | Heq: ?s1 && ?s2 = true |- _ =>
        destruct (andb_true_iff s1 s2) as [_h1'' _];
        destruct (_h1'' Heq) as [_hsep1'' _hsep2'']
      end.

      do 2 resolve_eqstr.


      match goal with
      | H: eqvv ?v1 ?v2 = true |- _ =>
        pose (vv_lt_eqbeq _ _ H) as _e;
        rewrite _e in *;
        clear _e H
      end.
      match goal with
      | H: eqvv ?v1 ?v2 = true |- _ =>
        pose (vv_lt_eqbeq _ _ H) as _e;
        rewrite _e in *;
        clear _e H
      end.
      split; eauto.
    }

    intro Hin.
    destruct Hin as [L' [Hin1 Hin2]].
    apply (List.filter_In).
    destruct r.
    inversion Hin1.
    subst.
    split.
    eauto.

    match goal with 
    | |- ?s1 && ?s2 = true =>
      apply (andb_true_iff s1 s2)
    end.
    split.

    match goal with 
    | |- ?s1 && ?s2 = true =>
      apply (andb_true_iff s1 s2)
    end.
    split.

    match goal with 
    | |- ?s1 && ?s2 = true =>
      apply (andb_true_iff s1 s2)
    end.
    split.

    apply vvot.eqb_eq. auto.
    apply vvot.eqb_eq. auto.
    1,2: apply String.eqb_eq; auto.
  Qed.

  Definition convert2PlainE L s :=
    let rs := findRuleWithLc L (Plain s) in
    map (fun r =>
        (match r with 
        | (_, Alt_Linear _ L') => PlnE L s L'
        | _ => PlnE L s L
        end)) rs.

  Lemma L_convert2PlainE: ∀ L s,
    ∀ e, List.In e (convert2PlainE L s) <-> 
        ∃ L', e = (PlnE L s L')
        /\ in_rules (L, Alt_Linear (Plain s) L') P.
  Proof.
    unfold convert2PlainE.

    split.
    1:{
      intros Hin.

      Ltac resolve_inmap :=
      match goal with 
      | H: In ?e (map ?f ?l) |- _ =>
      (* auto *)
        destruct (List.in_map_iff  f l e) as [_e1 _];
        pose (_e1 H) as Hex;
        destruct Hex as [r Hex];
        clear _e1
      end.

      resolve_inmap.
      destruct r as [v alt].
      destruct Hex as [_H1 _H2].

      destruct (L_findRuleWithLc L (Plain s) (v,alt)).
      rmDirect.
      breakAll.
      match goal with
      | h:(_,_)=_ |- _ =>
       inversion h; subst
      end.
      eauto.
    }

    intro Hex.
    destruct Hex as [L' [He Hin]].
    apply List.in_map_iff.
    exists (L, Alt_Linear (Plain s) L').
    split.
    eauto.
    apply L_findRuleWithLc.
    exists L'.
    eauto.
  Qed.

  Definition convert2CallLinearE L s :=
    let rs := findRuleWithLc L (Call s) in
    map (fun r => 
    (match r 
      with 
      | (_, Alt_Linear _ L') => PndCalE L s L'
      | _ => PndCalE L s L
    end)) rs.

  Lemma L_convert2CallLinearE : ∀ L s,
    ∀ e, List.In e (convert2CallLinearE L s) <-> 
      ∃ L', e = (PndCalE L s L')
    /\ in_rules (L, Alt_Linear (Call s) L') P.
  Proof.
    unfold convert2CallLinearE.
    split.
    1:{
      intros Hin.

      resolve_inmap.
      destruct r as [v alt].
      destruct Hex as [_H1 _H2].

      destruct (L_findRuleWithLc L (Call s) (v,alt)).
      rmDirect.
      breakAll.
      match goal with
      | h:(_,_)=_ |- _ =>
       inversion h; subst
      end.
      eauto.
    }

    intro Hex.
    destruct Hex as [L' [He Hin]].
    apply List.in_map_iff.
    exists (L, Alt_Linear (Call s) L').
    split.
    eauto.
    apply L_findRuleWithLc.
    exists L'.
    eauto.
  Qed.

  Definition convert2CallMatchE L s :=
    let rs := findRuleWithMa L s in
    map (fun r => 
        (match r 
          with 
          | (_, Alt_Match _ b L' L2) => (MatCalE L s L' b L2)
          (* fake *)
          | _ => (MatCalE L s L s L)
        end)) rs.

  Lemma L_convert2CallMatchE: ∀ L s,
    ∀ e, List.In e (convert2CallMatchE L s) <-> ∃ L' b L2, e = (MatCalE L s L' b L2)
    /\ in_rules (L, Alt_Match s b L' L2) P.
  Proof.
    unfold convert2CallMatchE.
    split.
    1:{
      intros Hin.

      resolve_inmap.
      destruct r as [v alt].
      destruct Hex as [_H1 _H2].

      destruct (L_findRuleWithMa L s (v,alt)).
      rmDirect.
      breakAll.
      match goal with
      | h:(_,_)=_ |- _ =>
       inversion h; subst
      end.
      eauto.
    }

    intro Hex.
    breakAll; subst.
    apply List.in_map_iff.
    match goal with
    | h: in_rules ?r P |- _ =>
     exists r
    end.
    getAnd; eauto.

    apply L_findRuleWithMa. eauto.
  Qed.

  Definition convert2RetLinearE L s :=
    let rs := findRuleWithLc L (Ret s) in
    map (fun r => 
        (match r 
          with 
          | (_, Alt_Linear _ L') => ((PndRetE L s L'))
          | _ => ((PndRetE L s L))
        end)) rs.

  Lemma L_convert2RetLinearE: ∀ L s,
    ∀ e, List.In e (convert2RetLinearE L s) <-> 
      ∃ L', e = (PndRetE L s L')
      /\ in_rules (L, Alt_Linear (Ret s) L') P.
  Proof.
    unfold convert2RetLinearE.
    split.
    1:{
      intros Hin.

      resolve_inmap.
      destruct r as [v alt].
      destruct Hex as [_H1 _H2].

      destruct (L_findRuleWithLc L (Ret s) (v,alt)).
      rmDirect.
      breakAll.
      match goal with
      | h:(_,_)=_ |- _ =>
        inversion h; subst
      end.
      eauto.
    }

    intro Hex.
    destruct Hex as [L' [He Hin]].
    apply List.in_map_iff.
    exists (L, Alt_Linear (Ret s) L').
    split.
    eauto.
    apply L_findRuleWithLc.
    exists L'.
    eauto.
  Qed.

  Definition convert2RetMatchE L a L1 s :=
    let rs := findRuleWithMb L a L1 s in
    map (fun r => 
    (match r with 
      | (_, Alt_Match a _ _ L') => 
       (MatRetE L a L1 s L')
      | _ => (PndRetE L s L)
    end)) rs.
  
  Lemma L_convert2RetMatchE: ∀ L a L1 s, 
    ∀ e, List.In e (convert2RetMatchE L a L1 s) <-> 
      ∃ L', e = (MatRetE L a L1 s L')
      /\ in_rules (L, Alt_Match a s L1 L') P.
  Proof.
    unfold convert2RetMatchE.
    split.
    1:{
      intros Hin.

      resolve_inmap.
      destruct r as [v alt].
      destruct Hex as [_H1 _H2].

      destruct (L_findRuleWithMb L a L1 s (v,alt)).
      rmDirect.
      breakAll.
      match goal with
      | h:(_,_)=_ |- _ =>
        inversion h; subst
      end.
      eauto.
    }

    intro Hex.
    destruct Hex as [L' [He Hin]].
    apply List.in_map_iff.
    exists (L, Alt_Match a s L1 L').
    split.
    eauto.
    apply L_findRuleWithMb.
    exists L'.
    eauto.
    
  Qed.

  Definition e2PlainE e' s := (convert2PlainE (endE e') s).

  Lemma L_e2PlainE: ∀ e' s, ∀ L, 
    endE e' = L -> (∀ e, List.In e (e2PlainE e' s) <-> 
    ∃ L', e = (PlnE L s L') 
      /\ in_rules (L, Alt_Linear (Plain s) L') P).
  Proof.
    split.
    1:{
      intro Hin.
      destruct (L_convert2PlainE L s e).
      subst.
      rmDirect.
      eauto.
    }

    intro Hex; breakAll.
    destruct e'; subst;
    apply L_convert2PlainE; eauto.
  Qed.

  Definition e2CallLinearE e' s := 
      convert2CallLinearE (endE e') s.

  Lemma L_e2CallLinearE: ∀ e' s,  
    ∀ L, endE e' = L -> (∀ e, List.In e (e2CallLinearE e' s) <-> 
    ∃ L', e = (PndCalE L s L')
      /\ in_rules (L, Alt_Linear (Call s) L') P).
  Proof.
    split.
    1:{
      intro Hin.
      destruct (L_convert2CallLinearE L s e).
      subst.
      rmDirect.
      eauto.
    }

    intro Hex; breakAll.
    destruct e'; subst;
    apply L_convert2CallLinearE; eauto.
  Qed.

  Definition e2CallMatchE e' s := convert2CallMatchE (endE e') s.

  Lemma L_e2CallMatchE : ∀ e' s, 
    ∀ L, endE e' = L -> (∀ e, List.In e (e2CallMatchE e' s) <-> 
    ∃ L' b L2, e = (MatCalE L s L' b L2) 
      /\ in_rules (L, Alt_Match s b L' L2) P).
  Proof.
    split.
    1:{
      intro Hin.
      destruct (L_convert2CallMatchE L s e);
      subst.
      rmDirect.
      eauto.
    }

    intro Hex; breakAll.
    destruct e'; subst;
    apply L_convert2CallMatchE; eauto.
  Qed.

  Definition e2RetLinearE e' s :=
    convert2RetLinearE (endE e') s.

  Lemma L_e2RetLinearE : ∀ e' s,
    ∀ L, endE e' = L -> (∀ e, List.In e (e2RetLinearE e' s) <-> 
    ∃ L', e = (PndRetE L s L') 
      /\ in_rules (L, Alt_Linear (Ret s) L') P).
  Proof.
    split.
    1:{
      intro Hin.

      destruct (L_convert2RetLinearE L s e);
      subst.
      rmDirect.
      eauto.
    }

    intro Hex; breakAll.
    destruct e'; subst;
    apply L_convert2RetLinearE; eauto.
  Qed.

  Definition inRM e m :=
    match e, m with 
    | (r, Calv e), CalCME m => va_set.In (r, e) m
    | (r, Plnv e), PlnCME m => vc_set.In (r, e) m
    | (r, Retv e), RetCME m => vb_set.In (r, e) m
    | _, _ => False
    end.

  Definition va_of_list va :=
    List.fold_left 
    (fun i s => 
      va_set.add s i)
    va
    (va_set.empty).

  Definition vc_of_list vc :=
    List.fold_left 
    (fun i s => 
      vc_set.add s i)
    vc
    (vc_set.empty).

  Definition vb_of_list vb :=
    List.fold_left 
    (fun i s => 
      vb_set.add s i)
    vb
    (vb_set.empty).

  Lemma L_va_of_list: ∀ va l, va_set.In l (va_of_list va) <-> In l va.
  Proof.
    intros.
    split; intros.

    1: {
      generalize dependent va; intros.
      induction va using (well_founded_ind (LEN_WF.len_wf va_set.elt)).

      rename H0 into HInd.

      destruct va.

      1:{
        simpl in H.
        inversion H.
      }

      assert (e::va!=[]) as Hne by eauto using nil_cons.
      destruct (exists_last Hne) as [? [? _h]].
      rewrite _h in *; clear _h Hne.

      simpl in H.
      specialize HInd with x.

      unfold va_of_list in H.
      match goal with
      | h: va_set.In _ (fold_left ?f (?x++?x0) ?i) |- _ =>
        pose (fold_left_app f x x0 i) as _h
        ; rewrite _h in h
        ; clear _h
        ; simpl in H
      end.

      match goal with
      | h: va_set.In ?x (va_set.add ?y ?s) |- _ =>
        destruct (va_set.add_spec s y x) as [_h _]
        ; specialize _h with (1:=h)
        ; destruct _h
      end.

      1:{
        destruct x0.
        destruct l.
        inversion H0.
        inversion H1.
        inversion H2.
        simpl in *; subst.
        apply List.in_app_iff.
        right; simpl; eauto.
      }

      unfold va_of_list in HInd.

      assert (In l x).
      1:{
        apply HInd.
        unfold LEN_WF.len.
        match goal with
        | |- _ < ?len (?v ++ [?e]) =>
          rewrite (last_length v e)
          ; eauto
        end.
        eauto.
      }

      apply (List.in_app_iff).
      eauto.
    }

    generalize dependent va; intros.
    induction va using (well_founded_ind (LEN_WF.len_wf va_set.elt)).

    rename H0 into HInd.

    destruct va.

    1:{
      simpl in H.
      inversion H.
    }

    assert (e::va!=[]) as Hne by eauto using nil_cons.
    destruct (exists_last Hne) as [? [? _h]].
    rewrite _h in *; clear _h Hne.

    destruct (List.in_app_or _ _ _ H).

    specialize HInd with x.

    assert (va_set.In l (va_of_list x)).
    1:{
      apply HInd.
      unfold LEN_WF.len.
      match goal with
      | |- _ < ?len (?v ++ [?e]) =>
        rewrite (last_length v e)
        ; eauto
      end.
      eauto.
    }

    unfold va_of_list.
    match goal with
    | |- va_set.In _ (fold_left ?f (?x++?x0) ?i) =>
      pose (fold_left_app f x x0 i) as _h
      ; rewrite _h
      ; clear _h
      ; simpl
    end.

    apply va_set.add_spec.
    right.
    eauto.


    inversion H0; subst; try easy.

    unfold va_of_list.
    match goal with
    | |- va_set.In _ (fold_left ?f (?x++?x0) ?i) =>
      pose (fold_left_app f x x0 i) as _h
      ; rewrite _h
      ; clear _h
      ; simpl
    end.

    apply va_set.add_spec.
    left.
    eauto.
  Qed.

  Lemma L_vc_of_list: ∀ vc l, vc_set.In l (vc_of_list vc) <-> In l vc.
  Proof.
    intros.
    split; intros.

    1: {
      generalize dependent vc; intros.
      induction vc using (well_founded_ind (LEN_WF.len_wf vc_set.elt)).

      rename H0 into HInd.

      destruct vc.

      1:{
        simpl in H.
        inversion H.
      }

      assert (e::vc!=[]) as Hne by eauto using nil_cons.
      destruct (exists_last Hne) as [? [? _h]].
      rewrite _h in *; clear _h Hne.

      simpl in H.
      specialize HInd with x.

      unfold vc_of_list in H.
      match goal with
      | h: vc_set.In _ (fold_left ?f (?x++?x0) ?i) |- _ =>
        pose (fold_left_app f x x0 i) as _h
        ; rewrite _h in h
        ; clear _h
        ; simpl in H
      end.

      match goal with
      | h: vc_set.In ?x (vc_set.add ?y ?s) |- _ =>
        destruct (vc_set.add_spec s y x) as [_h _]
        ; specialize _h with (1:=h)
        ; destruct _h
      end.

      1:{
        destruct x0.
        destruct l.
        inversion H0.
        inversion H1.
        inversion H2.
        simpl in *; subst.
        apply List.in_app_iff.
        right; simpl; eauto.
      }

      unfold vc_of_list in HInd.

      assert (In l x).
      1:{
        apply HInd.
        unfold LEN_WF.len.
        match goal with
        | |- _ < ?len (?v ++ [?e]) =>
          rewrite (last_length v e)
          ; eauto
        end.
        eauto.
      }

      apply (List.in_app_iff).
      eauto.
    }

    generalize dependent vc; intros.
    induction vc using (well_founded_ind (LEN_WF.len_wf vc_set.elt)).

    rename H0 into HInd.

    destruct vc.

    1:{
      simpl in H.
      inversion H.
    }

    assert (e::vc!=[]) as Hne by eauto using nil_cons.
    destruct (exists_last Hne) as [? [? _h]].
    rewrite _h in *; clear _h Hne.

    destruct (List.in_app_or _ _ _ H).

    specialize HInd with x.

    assert (vc_set.In l (vc_of_list x)).
    1:{
      apply HInd.
      unfold LEN_WF.len.
      match goal with
      | |- _ < ?len (?v ++ [?e]) =>
        rewrite (last_length v e)
        ; eauto
      end.
      eauto.
    }

    unfold vc_of_list.
    match goal with
    | |- vc_set.In _ (fold_left ?f (?x++?x0) ?i) =>
      pose (fold_left_app f x x0 i) as _h
      ; rewrite _h
      ; clear _h
      ; simpl
    end.

    apply vc_set.add_spec.
    right.
    eauto.


    inversion H0; subst; try easy.

    unfold vc_of_list.
    match goal with
    | |- vc_set.In _ (fold_left ?f (?x++?x0) ?i) =>
      pose (fold_left_app f x x0 i) as _h
      ; rewrite _h
      ; clear _h
      ; simpl
    end.

    apply vc_set.add_spec.
    left.
    eauto.
  Qed.

  Lemma L_vb_of_list: ∀ vb l, vb_set.In l (vb_of_list vb) <-> In l vb.
  Proof.
    intros.
    split; intros.

    1: {
      generalize dependent vb; intros.
      induction vb using (well_founded_ind (LEN_WF.len_wf vb_set.elt)).

      rename H0 into HInd.

      destruct vb.

      1:{
        simpl in H.
        inversion H.
      }

      assert (e::vb!=[]) as Hne by eauto using nil_cons.
      destruct (exists_last Hne) as [? [? _h]].
      rewrite _h in *; clear _h Hne.

      simpl in H.
      specialize HInd with x.

      unfold vb_of_list in H.
      match goal with
      | h: vb_set.In _ (fold_left ?f (?x++?x0) ?i) |- _ =>
        pose (fold_left_app f x x0 i) as _h
        ; rewrite _h in h
        ; clear _h
        ; simpl in H
      end.

      match goal with
      | h: vb_set.In ?x (vb_set.add ?y ?s) |- _ =>
        destruct (vb_set.add_spec s y x) as [_h _]
        ; specialize _h with (1:=h)
        ; destruct _h
      end.

      1:{
        destruct x0.
        destruct l.
        inversion H0.
        inversion H1.
        inversion H2.
        simpl in *; subst.
        apply List.in_app_iff.
        right; simpl; eauto.
      }

      unfold vb_of_list in HInd.

      assert (In l x).
      1:{
        apply HInd.
        unfold LEN_WF.len.
        match goal with
        | |- _ < ?len (?v ++ [?e]) =>
          rewrite (last_length v e)
          ; eauto
        end.
        eauto.
      }

      apply (List.in_app_iff).
      eauto.
    }

    generalize dependent vb; intros.
    induction vb using (well_founded_ind (LEN_WF.len_wf vb_set.elt)).

    rename H0 into HInd.

    destruct vb.

    1:{
      simpl in H.
      inversion H.
    }

    assert (e::vb!=[]) as Hne by eauto using nil_cons.
    destruct (exists_last Hne) as [? [? _h]].
    rewrite _h in *; clear _h Hne.

    destruct (List.in_app_or _ _ _ H).

    specialize HInd with x.

    assert (vb_set.In l (vb_of_list x)).
    1:{
      apply HInd.
      unfold LEN_WF.len.
      match goal with
      | |- _ < ?len (?v ++ [?e]) =>
        rewrite (last_length v e)
        ; eauto
      end.
      eauto.
    }

    unfold vb_of_list.
    match goal with
    | |- vb_set.In _ (fold_left ?f (?x++?x0) ?i) =>
      pose (fold_left_app f x x0 i) as _h
      ; rewrite _h
      ; clear _h
      ; simpl
    end.

    apply vb_set.add_spec.
    right.
    eauto.


    inversion H0; subst; try easy.

    unfold vb_of_list.
    match goal with
    | |- vb_set.In _ (fold_left ?f (?x++?x0) ?i) =>
      pose (fold_left_app f x x0 i) as _h
      ; rewrite _h
      ; clear _h
      ; simpl
    end.

    apply vb_set.add_spec.
    left.
    eauto.
  Qed.

  Definition m2PlainM m' s := 
    match m' with 
    | CalCME m' =>
      PlnCME
      (vc_of_list
      (concat (map (fun v : option CalEdge * CalEdge => 
        let (r,e) := v in
        map (fun x => (r,x)) (e2PlainE (Calv e) s)) (va_set.elements m'))))
    | PlnCME m' => 
      PlnCME 
      (vc_of_list
      (concat (map (fun v : option CalEdge * PlnEdge => 
        let (r,e) := v in
        map (fun x => (r,x)) (e2PlainE (Plnv e) s)) (vc_set.elements m'))))
    | RetCME m' =>
      PlnCME 
      (vc_of_list  
        (concat (map (fun v : option CalEdge * RetEdge =>
        let (r,e) := v in
        map (fun x => (r,x)) (e2PlainE (Retv e) s)) (vb_set.elements m'))))
    end.

  Lemma L_ra_in: ∀ x l, InA (ra_as_OT.eq) x l -> In x l.
  Proof.
    intros.
    match goal with
    | |- In ?x ?l =>
      destruct (InA_alt ra_as_OT.eq x l)
      ; rmDirect
      ; breakAll
    end.

    assert (x=x0).
    1:{
      inversion H0.
      destruct x; destruct x0.
      inversion H3; simpl in *.
      inversion H4; simpl in *.
      subst.
      eauto.
    }
    subst; eauto.
  Qed.

  Lemma L_rc_in: ∀ x l, InA (rc_as_OT.eq) x l -> In x l.
  Proof.
    intros.
    match goal with
    | |- In ?x ?l =>
      destruct (InA_alt rc_as_OT.eq x l)
      ; rmDirect
      ; breakAll
    end.

    assert (x=x0).
    1:{
      inversion H0.
      destruct x; destruct x0.
      inversion H3; simpl in *.
      inversion H4; simpl in *.
      subst.
      eauto.
    }
    subst; eauto.
  Qed.

  Lemma L_rb_in: ∀ x l, InA (rb_as_OT.eq) x l -> In x l.
  Proof.
    intros.
    match goal with
    | |- In ?x ?l =>
      destruct (InA_alt rb_as_OT.eq x l)
      ; rmDirect
      ; breakAll
    end.

    assert (x=x0).
    1:{
      inversion H0.
      destruct x; destruct x0.
      inversion H3; simpl in *.
      inversion H4; simpl in *.
      subst.
      eauto.
    }
    subst; eauto.
  Qed.

  Lemma L_m2PlainM : ∀ (m':ME) (s:terminal), 
    ∀ r e, inRM (r, e) (m2PlainM m' s) <-> 
      ∃ e' L L', 
        inRM (r, e') m'
        /\ endE e' = L
        /\ e = Plnv (PlnE L s L')
        /\ in_rules (L, Alt_Linear (Plain s) L') P.
  Proof.
    split.
    1:{
      intros Hin'.

      (* resolve concat *)
      Ltac resolve_concat :=
        match goal with 
        | H: In ?x (concat ?l)
        |- _ =>
          destruct (List.in_concat l x) as [_HinCC _];
          destruct (_HinCC H)  as [_m HinCC];
          clear _HinCC;
          destruct HinCC as [HCC1 HCC2]
          ; clear H
        end.

      Ltac resolve_inmap2 :=
        match goal with 
        | H: In ?e (map ?f ?l) |- _ =>
          destruct (List.in_map_iff  f l e) as [_e1 _]
          ; rmDirect
          ; clear H
        end.

      unfold m2PlainM in *;
      destruct m';
      unfold inRM in *;
      destruct e; try easy;
      match goal with
      | h: vc_set.In ?x (vc_of_list ?y) |- _ =>
        destruct (L_vc_of_list y x) as [_h _]
        ; specialize _h with (1:=h)
        ; clear h
      end.

      all: resolve_concat;
        resolve_inmap2;
        breakAll;
        match goal with
        | x: _ * _ |- _ =>
        destruct x; subst
        end.

      all: resolve_inmap2; breakAll;
        match goal with
        | h: (_,_) = (_,_) |- _ =>
          inversion h; subst; clear h
        end;
        match goal with
        | h: In (?r,?c) ?ma |- _ =>
        destruct c
        end.

      all: match goal with
      | h: In ?ve (e2PlainE ?r ?s) |- _ =>
        pose (L_e2PlainE r s (endE r)) as i
        ; specialize i with (e := vc)
        ; breakInfer
        ; [tac_app; simpl; eauto|]
        ; clear i
      end;
      match goal with
      | h:_ <-> _ |- _ =>
       destruct h; rmDirect; breakAll; subst
      end.

      all: simpl in *.

      all: match goal with
        | h: In (?r, ?e') _, h2: in_rules (?L1, Alt_Linear (Plain ?s) ?L2) P |- _ =>
          match e' with 
          | PlnE _ _ _ =>
            exists (Plnv e'), L1, L2
          | PndCalE _ _ _ =>
            exists (Calv e'), L1, L2
          | MatCalE _ _ _ _ _ =>
            exists (Calv e'), L1, L2
          | PndRetE _ _ _ =>
            exists (Retv e'), L1, L2
          | MatRetE _ _ _ _ _ =>
            exists (Retv e'), L1, L2
          end
        end;
        eauto.

      all: match goal with
        | h: In ?ve (e2PlainE (?r) ?s) |- _ =>
          pose (L_e2PlainE (r) s (endE r)) as _hv
          ; specialize _hv with (e := ve)
          ; breakInfer
          ; [tac_app; simpl; eauto |]
          ; clear h
        end.
      
      all: match goal with
        | h:_ <-> _ |- _ =>
        destruct h; rmDirect; breakAll; subst
        end.

      (* 加的补丁 *)
      all: split; eauto.

      Ltac up_in :=
        match goal with
        | |- va_set.In ?x ?s =>
          destruct (va_set.elements_spec1 s x) as [_hs _]
          ; apply _hs
          ; eauto
        | |- vc_set.In ?x ?s =>
          destruct (vc_set.elements_spec1 s x) as [_hs _]
          ; apply _hs
          ; eauto
        | |- vb_set.In ?x ?s =>
          destruct (vb_set.elements_spec1 s x) as [_hs _]
          ; apply _hs
          ; eauto
        end.

      all: up_in.
    }

    intro Hex.
    breakAll; subst.

    simpl.
    destruct m'.

    all: unfold m2PlainM in *.

    all: apply L_vc_of_list.

    all: apply List.in_concat.

    all: destruct x; simpl in H; try easy.

    all: match goal with
    | h: va_set.In (?r, ?v) _ |- _ =>
      exists (map (λ x2 : PlnEdge, (r, x2)) (e2PlainE (Calv v) s))
      ; getAnd; eauto; apply List.in_map_iff; 
      [exists (r, v); getAnd; eauto |]
    | h: vc_set.In (?r, ?v) _ |- _ =>
      exists (map (λ x2 : PlnEdge, (r, x2)) (e2PlainE (Plnv v) s))
      ; getAnd; eauto; apply List.in_map_iff; 
      [exists (r, v); getAnd; eauto |]
    | h: vb_set.In (?r, ?v) _ |- _ =>
      exists (map (λ x2 : PlnEdge, (r, x2)) (e2PlainE (Retv v) s))
      ; getAnd; eauto; apply List.in_map_iff; 
      [exists (r, v); getAnd; eauto |]
    end.

    all: eauto using L_ra_in, L_rc_in, L_rb_in.
    all: eexists; getAnd; eauto.

    all: match goal with
    | h: in_rules (endE ?v, Alt_Linear (Plain ?s) _) _ |- _ =>
     apply (L_e2PlainE v s (endE v)); eauto
    end.
  Qed.

  Definition m2CallM (m':ME) s : ME :=
    match m' with
    | CalCME m' =>
      CalCME (
        va_of_list
        (concat (map 
        (fun v : option CalEdge * CalEdge => 
          let (r,e) := v in
          match r with
          | None => 
            map (fun x => (Some x,x)) ((e2CallLinearE (Calv e) s) ++ (e2CallMatchE (Calv e) s))%list
          | Some (PndCalE _ _ _) => 
            map (fun x => (Some x,x)) ((e2CallLinearE (Calv e) s) ++ (e2CallMatchE (Calv e) s))%list
          | Some (MatCalE _ _ _ _ _) => 
            map (fun x => (Some x,x)) (e2CallMatchE (Calv e) s)
          end) (va_set.elements m'))))
    | PlnCME m' =>
      CalCME (
        va_of_list
        (concat (map 
        (fun v : option CalEdge * PlnEdge => 
          let (r,e) := v in
          match r with
          | None => 
            map (fun x => (Some x,x)) ((e2CallLinearE (Plnv e) s) ++ (e2CallMatchE (Plnv e) s))%list
          | Some (PndCalE _ _ _) => 
            map (fun x => (Some x,x)) ((e2CallLinearE (Plnv e) s) ++ (e2CallMatchE (Plnv e) s))%list
          | Some (MatCalE _ _ _ _ _) => 
            map (fun x => (Some x,x)) (e2CallMatchE (Plnv e) s)
          end) (vc_set.elements m'))))
    | RetCME m' =>
      CalCME (
        va_of_list
        (concat (map 
        (fun v : option CalEdge * RetEdge => 
          let (r,e) := v in
          match r with
          | None => 
            map (fun x => (Some x,x)) (((e2CallLinearE (Retv e) s) ++ (e2CallMatchE (Retv e) s))%list)
          | Some (PndCalE _ _ _) => 
            map (fun x => (Some x,x)) (((e2CallLinearE (Retv e) s) ++ (e2CallMatchE (Retv e) s))%list)
          | Some (MatCalE _ _ _ _ _) => 
            map (fun x => (Some x,x)) (e2CallMatchE (Retv e) s)
          end) (vb_set.elements m'))))
    end.


  Lemma L_m2CallM: ∀ m' s,
    ∀ r e, inRM (r,e) (m2CallM m' s) <->
        ∃ r' e', 
        inRM (r', e') m'
        /\ ∃ L, endE e' = L
        /\ 
        ( ( (r' = None \/ ∃ L1 a L2, r'=Some (PndCalE L1 a L2)) -> 
          (∃ L', e = Calv (PndCalE L s L') /\
            r = Some (PndCalE L s L') /\
            in_rules (L, Alt_Linear (Call s) L') P) \/
          (∃ L' b L2, e = Calv (MatCalE L s L' b L2) /\
            r = Some (MatCalE L s L' b L2) /\
            in_rules (L, Alt_Match s b L' L2) P)  
          ) 
        /\ ((∃ L1 a L2 b L3, r'=Some (MatCalE L1 a L2 b L3)) -> 
          ∃ L' b L2, e = Calv (MatCalE L s L' b L2) /\
            r = Some (MatCalE L s L' b L2) /\
            in_rules (L, Alt_Match s b L' L2) P
        )).
  Proof.
    split.
    1:{
      intros Hin'.

      unfold m2CallM in *;
      destruct m';
      unfold inRM in *;
      destruct e; try easy;
      match goal with
      | h: va_set.In ?x (va_of_list ?y) |- _ =>
        destruct (L_va_of_list y x) as [_h _]
        ; specialize _h with (1:=h)
        ; clear h
      end.

      all: resolve_concat.

      all: resolve_inmap2;
      breakAll;
      match goal with
      | x: _ * _ |- _ =>
       destruct x; subst
      end.

      1:{
        destruct o.
        1:{
          destruct c0.
          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists (Some (PndCalE L a L1)), (Calv c).
            getAnd; eauto.

            up_in.

            exists (endE (Calv c)).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
              inversion H1; subst.
  
              destruct va.
              1:{
                left. exists L1; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L1; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  do 2 eexists.
                  
                  inversion H4; subst.
                  getAnd; eauto.
                }
              }
            }

            intros. breakAll; discriminate.
          }

          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists (Some (MatCalE L a L1 b L2)), (Calv c).
            getAnd; eauto.
            up_in.
            exists (endE (Calv c)).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
            }

            intros; breakAll; subst. inversion H1; subst.

            match goal with
            | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
              pose (L_e2CallMatchE e' i (endE e')) as _h;
              breakInfer; [tac_app; eauto|]; clear _h;
              match goal with 
              | h2: ∀ _, _ <-> _ |- _ =>
                destruct (h2 e); clear h2; rmDirect
                ; breakAll; subst
              end
            end.
            do 3 eexists; eauto.
          }
        }

        1:{
          destruct c.
          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists None, (Calv (PndCalE L a L1)).
            getAnd; eauto.
            up_in.
            exists (endE (Calv (PndCalE L a L1))).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
              inversion H1; subst.
  
              destruct va.
              1:{
                left. exists L2; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L2; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  simpl in *.
                  inversion H4; subst.
                  do 2 eexists.
                  
                  getAnd; eauto.
                }
              }
            }

            intros. breakAll; discriminate.
          }

          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists None, (Calv (MatCalE L a L1 b L2)).
            getAnd; eauto. up_in.
            exists (endE (Calv (MatCalE L a L1 b L2))).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.

              destruct va.
              1:{
                left. exists L3; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L3; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  do 2 eexists.
                  
                  inversion H4; subst.
                  getAnd; eauto.
                }
              }
            }

            intros; breakAll; subst. inversion H1; subst.
          }
        }
      }
      
      1:{
        destruct o.
        1:{
          destruct c.
          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists (Some (PndCalE L a L1)), (Plnv p).
            getAnd; eauto.
            up_in.
            exists (endE (Plnv p)).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
              inversion H1; subst.
  
              destruct va.
              1:{
                left. exists L1; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L1; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  do 2 eexists.
                  
                  inversion H4; subst.
                  getAnd; eauto.
                }
              }
            }

            intros. breakAll; discriminate.
          }

          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists (Some (MatCalE L a L1 b L2)), (Plnv p).
            getAnd; eauto.
            up_in.
            exists (endE (Plnv p)).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
            }

            intros; breakAll; subst. inversion H1; subst.

            match goal with
            | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
              pose (L_e2CallMatchE e' i (endE e')) as _h;
              breakInfer; [tac_app; eauto|]; clear _h;
              match goal with 
              | h2: ∀ _, _ <-> _ |- _ =>
                destruct (h2 e); clear h2; rmDirect
                ; breakAll; subst
              end
            end.
            do 3 eexists; eauto.
          }
        }

        1:{
          destruct p.
          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists None, (Plnv (PlnE L c L1)).
            getAnd; eauto.
            up_in.
            exists (endE (Plnv (PlnE L c L1))).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
              inversion H1; subst.
  
              destruct va.
              1:{
                left. exists L2; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L2; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  do 2 eexists.
                  
                  inversion H4; subst.
                  getAnd; eauto.
                }
              }
            }

            intros. breakAll; discriminate.
          }
        }
      }

      1:{
        destruct o.
        1:{
          destruct c.
          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists (Some (PndCalE L a L1)), (Retv r0).
            getAnd; eauto.
            up_in.
            exists (endE (Retv r0)).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
              inversion H1; subst.
  
              destruct va.
              1:{
                left. exists L1; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L1; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  do 2 eexists.
                  
                  inversion H4; subst.
                  getAnd; eauto.
                }
              }
            }

            intros. breakAll; discriminate.
          }

          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists (Some (MatCalE L a L1 b L2)), (Retv r0).
            getAnd; eauto.
            up_in.
            exists (endE (Retv r0)).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
            }

            intros; breakAll; subst. inversion H1; subst.

            match goal with
            | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
              pose (L_e2CallMatchE e' i (endE e')) as _h;
              breakInfer; [tac_app; eauto|]; clear _h;
              match goal with 
              | h2: ∀ _, _ <-> _ |- _ =>
                destruct (h2 e); clear h2; rmDirect
                ; breakAll; subst
              end
            end.
            do 3 eexists; eauto.
          }
        }

        1:{
          destruct r0.
          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists None, (Retv (PndRetE L b L1)).
            getAnd; eauto.
            up_in.
            exists (endE (Retv (PndRetE L b L1))).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.
              inversion H1; subst.
  
              destruct va.
              1:{
                left. exists L2; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L2; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  do 2 eexists.
                  
                  inversion H4; subst.
                  getAnd; eauto.
                }
              }
            }

            intros. breakAll; discriminate.
          }

          1:{
            resolve_inmap2; breakAll;
            match goal with
            | h: (_,_) = (_,_) |- _ =>
            inversion h; subst; clear h
            end.
            exists None, (Retv (MatRetE L a L1 b L2)).
            getAnd; eauto.
            up_in.
            exists (endE (Retv (MatRetE L a L1 b L2))).
            getAnd; eauto.
            getAnd; eauto.
            1:{
              intros.
              breakAll; try discriminate.

              destruct va.
              1:{
                left. exists L3; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  inversion H4; subst.
                  getAnd; eauto.
                }
  
                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }
              }
              1:{
                right. exists L3; eauto.
  
                pose (List.in_app_or _ _ _ H0) as TwoCases.
                destruct TwoCases.
                1:{
                  match goal with
                  | h:In ?e (e2CallLinearE ?e' ?i) |- _ =>
                    pose (L_e2CallLinearE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  discriminate.
                }

                1:{
                  match goal with
                  | h:In ?e (e2CallMatchE ?e' ?i) |- _ =>
                    pose (L_e2CallMatchE e' i (endE e')) as _h;
                    breakInfer; [tac_app; eauto|]; clear _h;
                    match goal with 
                    | h2: ∀ _, _ <-> _ |- _ =>
                      destruct (h2 e); clear h2; rmDirect
                      ; breakAll; subst
                    end
                  end.
                  do 2 eexists.
                  
                  inversion H4; subst.
                  getAnd; eauto.
                }
              }
            }

            intros; breakAll; subst. inversion H1; subst.
          }
        }
      }
    }

    intros. breakAll; subst.

    destruct x.
    1:{
      destruct c.
      
      1:{
        clear H.
        breakInfer. tac_app. eauto. clear H2.
        breakAll; subst.
        1:{
          unfold m2CallM in *;
          destruct m';
          unfold inRM in *;
          destruct x0; try easy;
          apply L_va_of_list.

  
          apply in_concat.
          exists (map (λ x1 : CalEdge, (Some x1, x1))
            (e2CallLinearE (Calv va) s ++ e2CallMatchE (Calv va) s)).
          getAnd; eauto.
          apply List.in_map_iff.
          exists (Some (PndCalE L a L1), va).
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

          apply List.in_map_iff.
          eexists.
          getAnd; eauto.
          apply in_or_app.
          left.
          apply (L_e2CallLinearE (Calv va) s (endE (Calv va) )); eauto.


          apply in_concat.
          exists (map (λ x1 : CalEdge, (Some x1, x1))
            (e2CallLinearE (Plnv vc) s ++ e2CallMatchE (Plnv vc) s)).
          getAnd; eauto.
          apply List.in_map_iff.
          exists (Some (PndCalE L a L1), vc).
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
          apply List.in_map_iff.
          eexists.
          getAnd; eauto.
          apply in_or_app.
          left.
          apply (L_e2CallLinearE (Plnv vc) s (endE (Plnv vc) )); eauto.


          apply in_concat.
          exists (map (λ x1 : CalEdge, (Some x1, x1))
            (e2CallLinearE (Retv vb) s ++ e2CallMatchE (Retv vb) s)).
          getAnd; eauto.
          apply List.in_map_iff.
          exists (Some (PndCalE L a L1), vb).
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
          apply List.in_map_iff.
          eexists.
          getAnd; eauto.
          apply in_or_app.
          left.
          apply (L_e2CallLinearE (Retv vb) s (endE (Retv vb) )); eauto.
        }

        1:{
          unfold m2CallM in *;
          destruct m';
          unfold inRM in *;
          destruct x0; try easy;
          apply L_va_of_list.

          apply in_concat.
          exists (map (λ x1 : CalEdge, (Some x1, x1))
            (e2CallLinearE (Calv va) s ++ e2CallMatchE (Calv va) s)).
          getAnd; eauto.
          apply List.in_map_iff.
          exists (Some (PndCalE L a L1), va).
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

          apply List.in_map_iff.
          eexists.
          getAnd; eauto.
          apply in_or_app.
          right.
          apply (L_e2CallMatchE (Calv va) s (endE (Calv va) )); eauto.


          apply in_concat.
          exists (map (λ x1 : CalEdge, (Some x1, x1))
            (e2CallLinearE (Plnv vc) s ++ e2CallMatchE (Plnv vc) s)).
          getAnd; eauto.
          apply List.in_map_iff.
          exists (Some (PndCalE L a L1), vc).
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

          apply List.in_map_iff.
          eexists.
          getAnd; eauto.
          apply in_or_app.
          right.
          apply (L_e2CallMatchE (Plnv vc) s (endE (Plnv vc) )); eauto.


          apply in_concat.
          exists (map (λ x1 : CalEdge, (Some x1, x1))
            (e2CallLinearE (Retv vb) s ++ e2CallMatchE (Retv vb) s)).
          getAnd; eauto.
          apply List.in_map_iff.
          exists (Some (PndCalE L a L1), vb).
          getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
          apply List.in_map_iff.
          eexists.
          getAnd; eauto.
          apply in_or_app.
          right.
          apply (L_e2CallMatchE (Retv vb) s (endE (Retv vb) )); eauto.
        }
      }

      1:{
        clear H2.
        breakInfer. tac_app. do 5 eexists; eauto. clear H.
        breakAll; subst.

        unfold m2CallM in *;
        destruct m';
        unfold inRM in *;
        destruct x0; try easy;
        apply L_va_of_list.



        apply in_concat.
        exists (map (λ x3 : CalEdge, (Some x3, x3))
          (e2CallMatchE (Calv va) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (Some (MatCalE L a L1 b L2), va).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply (L_e2CallMatchE (Calv va) s (endE (Calv va) )); eauto.


        apply in_concat.
        exists (map (λ x3 : CalEdge, (Some x3, x3))
          (e2CallMatchE (Plnv vc) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (Some (MatCalE L a L1 b L2), vc).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply (L_e2CallMatchE (Plnv vc) s (endE (Plnv vc) )); eauto.


        apply in_concat.
        exists (map (λ x3 : CalEdge, (Some x3, x3))
          (e2CallMatchE (Retv vb) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (Some (MatCalE L a L1 b L2), vb).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply (L_e2CallMatchE (Retv vb) s (endE (Retv vb) )); eauto.
      }
    }

    1:{
      clear H.
      breakInfer. tac_app. eauto. clear H2.
      breakAll; subst.
      1:{
        unfold m2CallM in *;
        destruct m';
        unfold inRM in *;
        destruct x0; try easy;
        apply L_va_of_list.

        apply in_concat.
        exists (map (λ x1 : CalEdge, (Some x1, x1))
          (e2CallLinearE (Calv va) s ++ e2CallMatchE (Calv va) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (None, va).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply in_or_app.
        left.
        apply (L_e2CallLinearE (Calv va) s (endE (Calv va) )); eauto.


        apply in_concat.
        exists (map (λ x1 : CalEdge, (Some x1, x1))
          (e2CallLinearE (Plnv vc) s ++ e2CallMatchE (Plnv vc) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (None, vc).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply in_or_app.
        left.
        apply (L_e2CallLinearE (Plnv vc) s (endE (Plnv vc) )); eauto.


        apply in_concat.
        exists (map (λ x1 : CalEdge, (Some x1, x1))
          (e2CallLinearE (Retv vb) s ++ e2CallMatchE (Retv vb) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (None, vb).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply in_or_app.
        left.
        apply (L_e2CallLinearE (Retv vb) s (endE (Retv vb) )); eauto.
      }

      1:{
        unfold m2CallM in *;
        destruct m';
        unfold inRM in *;
        destruct x0; try easy;
        apply L_va_of_list.

        apply in_concat.
        exists (map (λ x1 : CalEdge, (Some x1, x1))
          (e2CallLinearE (Calv va) s ++ e2CallMatchE (Calv va) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (None, va).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply in_or_app.
        right.
        apply (L_e2CallMatchE (Calv va) s (endE (Calv va) )); eauto.


        apply in_concat.
        exists (map (λ x1 : CalEdge, (Some x1, x1))
          (e2CallLinearE (Plnv vc) s ++ e2CallMatchE (Plnv vc) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (None, vc).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply in_or_app.
        right.
        apply (L_e2CallMatchE (Plnv vc) s (endE (Plnv vc) )); eauto.


        apply in_concat.
        exists (map (λ x1 : CalEdge, (Some x1, x1))
          (e2CallLinearE (Retv vb) s ++ e2CallMatchE (Retv vb) s)).
        getAnd; eauto.
        apply List.in_map_iff.
        exists (None, vb).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply List.in_map_iff.
        eexists.
        getAnd; eauto.
        apply in_or_app.
        right.
        apply (L_e2CallMatchE (Retv vb) s (endE (Retv vb) )); eauto.
      }
    }
  Qed.


  (* SECTION 从transducer那里拷过来的 *)
  Definition filter_map {A} {B} l f g := 
    let l' := @List.filter A f l in
    @map A B g l'.

  Lemma L_filter_map: ∀ {A} {B} l f g y,
    @List.In B y (filter_map l f g) <-> ∃ x, @List.In A x l /\ f x = true /\ y=g(x).
  Proof.
    intros.
    destruct (in_map_iff g (filter f l) y).

    split.
    intros.
    rmDirect.
    breakAll.
    exists x.

    destruct (filter_In f x l).
    rmDirect.
    breakAll.
    split; auto.
    

    intros.
    destruct (in_map_iff g (filter f l) y).
    breakAll.

    destruct (filter_In f x l).

    unfold filter_map.
    apply H3.
    exists x.
    split; auto.
  Qed.

  Ltac apply_concat :=
    match goal with 
    | h: In ?x (concat ?l) |- _ =>
      pose (in_concat l x) as Hi
    | |- In ?x (concat ?l) =>
      pose (in_concat l x) as Hi
    end.


  Ltac apply_filter_map :=
    match goal with 
    | h: In ?x (filter_map ?l ?f ?g) |- _ =>
      pose (L_filter_map l f g x) as Hfm
    | |- In ?x (filter_map ?l ?f ?g) => 
      apply (L_filter_map l f g x)
    end.

  Ltac apply_in_map :=
    match goal with 
    | h: In ?x (map ?f ?l) |- _ =>
      pose (in_map_iff f l x) as Hfm
    | |- In ?x (map ?f ?l) => 
      apply (in_map_iff f l x)
    end.
  (* !SECTION *)

  Definition m2RetM m' (t:option ME) s :=
    match m' with
    | CalCME m' =>
      let m' := va_set.elements m' in
      RetCME (
        vb_of_list
        match t with
        | None =>
          concat (
          map (fun v : option CalEdge * CalEdge =>
            let (r,e) := v in
            map (fun e => (None, e)) (e2RetLinearE (Calv e) s)
          ) m')
        | Some (CalCME t) =>
          let t := va_set.elements t in
          concat (
            map (fun tre : option CalEdge * CalEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * CalEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Calv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Calv te)) Lr) && (goEps (Calv e))
                | None => false
                end
              )
              (fun v : option CalEdge * CalEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Calv e) s))
                end
              ))
          ) t)
        | Some (PlnCME t) =>
          let t := vc_set.elements t in
          concat (
            map (fun tre : option CalEdge * PlnEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * CalEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Plnv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Plnv te)) Lr) && (goEps (Calv e))
                | None => false
                end
              )
              (fun v : option CalEdge * CalEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Calv e) s))
                end
              ))
          ) t)
        | Some (RetCME t) =>
          let t := vb_set.elements t in
          concat (
            map (fun tre : option CalEdge * RetEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * CalEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Retv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Retv te)) Lr) && (goEps (Calv e))
                | None => false
                end
              )
              (fun v : option CalEdge * CalEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Calv e) s))
                end
              ))
          ) t)
        end
      )
    | PlnCME m' =>
      let m' := vc_set.elements m' in
      RetCME (
        vb_of_list
        match t with
        | None =>
          concat (
          map (fun v : option CalEdge * PlnEdge =>
            let (r,e) := v in
            map (fun e => (None, e)) (e2RetLinearE (Plnv e) s)
          ) m')
        | Some (CalCME t) =>
          let t := va_set.elements t in
          concat (
            map (fun tre : option CalEdge * CalEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * PlnEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Calv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Calv te)) Lr) && (goEps (Plnv e))
                | None => false
                end
              )
              (fun v : option CalEdge * PlnEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Plnv e) s))
                end
              ))
          ) t)
        | Some (PlnCME t) =>
          let t := vc_set.elements t in
          concat (
            map (fun tre : option CalEdge * PlnEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * PlnEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Plnv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Plnv te)) Lr) && (goEps (Plnv e))
                | None => false
                end
              )
              (fun v : option CalEdge * PlnEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Plnv e) s))
                end
              ))
          ) t)
        | Some (RetCME t) =>
          let t := vb_set.elements t in
          concat (
            map (fun tre : option CalEdge * RetEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * PlnEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Retv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Retv te)) Lr) && (goEps (Plnv e))
                | None => false
                end
              )
              (fun v : option CalEdge * PlnEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Plnv e) s))
                end
              ))
          ) t)
        end
      )
    | RetCME m' =>
      let m' := vb_set.elements m' in
      RetCME (
        vb_of_list
        match t with
        | None =>
          concat (
          map (fun v : option CalEdge * RetEdge =>
            let (r,e) := v in
            map (fun e => (None, e)) (e2RetLinearE (Retv e) s)
          ) m')
        | Some (CalCME t) =>
          let t := va_set.elements t in
          concat (
            map (fun tre : option CalEdge * CalEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * RetEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Calv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Calv te)) Lr) && (goEps (Retv e))
                | None => false
                end
              )
              (fun v : option CalEdge * RetEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Retv e) s))
                end
              ))
          ) t)
        | Some (PlnCME t) =>
          let t := vc_set.elements t in
          concat (
            map (fun tre : option CalEdge * PlnEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * RetEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Plnv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Plnv te)) Lr) && (goEps (Retv e))
                | None => false
                end
              )
              (fun v : option CalEdge * RetEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Retv e) s))
                end
              ))
          ) t)
        | Some (RetCME t) =>
          let t := vb_set.elements t in
          concat (
            map (fun tre : option CalEdge * RetEdge =>
            let (tr, te) := tre in
            concat (
              filter_map m'
              (fun v : option CalEdge * RetEdge =>
                let (r,e) := v in
                match r with
                | Some (PndCalE Lr _ _) => eqvv (endE (Retv te)) Lr
                | Some (MatCalE Lr _ _ _ _) => 
                  (eqvv (endE (Retv te)) Lr) && (goEps (Retv e))
                | None => false
                end
              )
              (fun v : option CalEdge * RetEdge =>
                let (r,e) := v in
                match r with
                | Some (MatCalE L a L1 b L2) =>
                  if String.eqb s b then
                    [(tr, MatRetE L a L1 b L2)]
                  else []
                | _ =>
                  (map (fun e => (tr, e)) (e2RetLinearE (Retv e) s))
                end
              ))
          ) t)
        end
      )
    end.

  Lemma L_goEps : forall e, goEps e = true <-> in_rules (endE (e), Alt_Epsilon) P .
  Proof.
    intro.
    split; intros.
    unfold goEps in H.
    match goal with 
    | H: existsb ?f ?l = true |- _ =>
      destruct (existsb_exists f l) as [_He _];
      destruct (_He H) as [xe Hex];
      clear _He
    end.
    destruct xe.
    breakAll.
    destruct a; try discriminate.
    unfold ff in *.
    resolve_eqvv.
    unfold in_rules. eauto.
    unfold goEps.

    match goal with 
    | |- existsb ?f ?l = true =>
      destruct (existsb_exists f l) as [_ _He]
      (* destruct (_He H) as [xe Hex]; *)
      (* clear _He *)
    end.
    tac_app.

    exists (endE e, Alt_Epsilon).
    getAnd; eauto.
    apply vvot.eqb_eq; eauto.
  Qed.

  Ltac resolve_goEps :=
    match goal with 
    | h:  goEps ?e = true |- _ =>
      destruct (L_goEps e) as [Heps1 Heps2]
      ; pose (Heps1 h)
    end.
  

  Lemma L_m2RetM : ∀ m' t s,
    ∀ r e, inRM (r,e) (m2RetM m' t s) <-> 
      (
        (
          t = None /\
          r = None /\
          ∃ r' e',
          inRM (r', e') m' /\
          ∃ L',
          e = Retv (PndRetE (endE e') s L') /\
          in_rules ((endE e'), Alt_Linear (Ret s) L') P
        ) \/
        (
          ∃ t', t = Some t' /\
          ∃ r' e', 
          inRM (Some r', e') m' /\
          match t' with
          | CalCME t' =>
            ∃ e'', 
            va_set.In (r, e'') t' /\
            endE (Calv e'') = beginE (Calv r')
          | PlnCME t' =>
            ∃ e'', 
            vc_set.In (r, e'') t' /\
            endE (Plnv e'') = beginE (Calv r')
          | RetCME t' =>
            ∃ e'', 
            vb_set.In (r, e'') t' /\
            endE (Retv e'') = beginE (Calv r')
          end /\
          (
            (∃ L a L1 L',
              r' = PndCalE L a L1 /\
              e = Retv (PndRetE (endE e') s L') /\
              in_rules ((endE e'), Alt_Linear (Ret s) L') P)
            \/
            (
              ∃ a L L1 L',
              r' = MatCalE L a L1 s L' /\
              e = Retv (MatRetE L a L1 s L') /\
              in_rules (endE e', Alt_Epsilon) P
            )
          )
        )
      ).
  Proof.
    split.

    1:{
      intro H. unfold m2RetM in H. unfold inRM in H.
      destruct m'; destruct e; try easy;
      match goal with
      | h: vb_set.In ?x (vb_of_list ?y) |- _ =>
        destruct (L_vb_of_list y x) as [_h _]
        ; specialize _h with (1:=h)
        ; clear h
      end.
      1:{
        destruct t.
        2:{
          left.
          resolve_concat.
          resolve_inmap2.
          breakAll. destruct x.

          getAnd; eauto.
          rewrite <- H0 in HCC2.
          resolve_inmap2.
          breakAll.
          inversion H2; subst.

          pose (L_e2RetLinearE (Calv c) s (endE(Calv c))).
          rmDirect.
          specialize H0 with (e:=vb).
          destruct H0. rmDirect.
          breakAll. subst.
          
          getAnd; eauto.
          exists o, (Calv c).
          getAnd; eauto.
          simpl; up_in.
        }
        
        1:{
          right.
          eexists.
          getAnd; eauto.
          destruct m.
          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c1.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Calv c0) s (endE (Calv c0))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Calv c0).
                getAnd; eauto.
                simpl; up_in.
                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.
                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Calv c0).
                getAnd; eauto.
                simpl; up_in.
                getAnd; eauto.

                exists c. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }

          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c0.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Calv c) s (endE (Calv c))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Calv c).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Calv c).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.

                exists p. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }
          
          1:{

            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c0.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Calv c) s (endE (Calv c))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Calv c).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Calv c).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.

                exists r0. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }
        }
      }

      1:{
        destruct t.
        2:{
          left.

          resolve_concat.
          resolve_inmap2.
          breakAll. destruct x.

          getAnd; eauto.
          rewrite <- H0 in HCC2.
          resolve_inmap2.
          breakAll.
          inversion H2; subst.

          pose (L_e2RetLinearE (Plnv p) s (endE(Plnv p))).
          rmDirect.
          specialize H0 with (e:=vb).
          destruct H0. rmDirect.
          breakAll. subst.
          
          getAnd; eauto.
          exists o, (Plnv p).
          getAnd; eauto.
          simpl; up_in.

        }
        
        1:{
          right.
          eexists.
          getAnd; eauto.
          destruct m.
          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c0.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Plnv p) s (endE (Plnv p))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Plnv p).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Plnv p).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.

                exists c. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }

          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Plnv p0) s (endE (Plnv p0))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Plnv p0).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Plnv p0).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.

                exists p. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }
          
          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Plnv p) s (endE (Plnv p))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Plnv p).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Plnv p).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.

                exists r0. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }
        }
      }

      1:{
        destruct t.
        2:{
          left.
          resolve_concat.
          resolve_inmap2.
          breakAll. destruct x.

          getAnd; eauto.
          rewrite <- H0 in HCC2.
          resolve_inmap2.
          breakAll.
          inversion H2; subst.

          pose (L_e2RetLinearE (Retv r0) s (endE(Retv r0))).
          rmDirect.
          specialize H0 with (e:=vb).
          destruct H0. rmDirect.
          breakAll. subst.
          
          getAnd; eauto.
          exists o, (Retv r0).
          getAnd; eauto.
          simpl; up_in.


        }
        
        1:{
          right.
          eexists.
          getAnd; eauto.
          destruct m.
          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c0.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Retv r0) s (endE (Retv r0))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Retv r0).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Retv r0).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.

                exists c. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }

          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Retv r0 ) s (endE (Retv r0 ))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Retv r0 ).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Retv r0).
                getAnd; eauto.

                simpl; up_in.

                getAnd; eauto.

                exists p. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }
          
          1:{
            resolve_concat.

            resolve_inmap2;
            breakAll;
            match goal with
            | x: _ * _ |- _ =>
             destruct x; subst
            end.
            rename HCC2 into H2.
            resolve_concat.

            apply_filter_map.
            destruct Hfm as [H1 _].
            rmDirect; clear HCC1.
            breakAll.
            destruct x.

            (* context r *)
            destruct o0.
            1:{
              (* same context r *)
              destruct c.
              1:{
                subst.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.
                
                resolve_inmap2;
                breakAll;
                match goal with
                | x: (_,_) = _ |- _ =>
                  inversion x; clear x
                end;
                match goal with
                | h1: _ = _, h2: _ = _ |- _ =>
                  rewrite h1 in *
                  ; rewrite h2 in *
                  ; clear h1 h2
                end.
  
                pose (L_e2RetLinearE (Retv r1) s (endE (Retv r1))).
                breakInfer. tac_app; eauto. clear i.
                specialize H3 with (e:=vb).
                destruct H3 as [H11 _].
                rmDirect.
                breakAll.
                rewrite H4 in *; clear H4.
  
                exists (PndCalE L a L1), (Retv r1).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.
                eexists. getAnd; simpl; try up_in; simpl; eauto.

                
                left.

                do 4 eexists.
                getAnd; eauto.
              }

              1:{
                subst.
                breakland.
  
                match goal with
                | H: eqvv ?v1 ?v2 = true |- _ =>
                  pose (vv_lt_eqbeq _ _ H) as _e
                end.

                destruct_with_eqn (String.eqb s b).
                2:{
                   inversion HCC2. 
                }
                  
                inversion HCC2;
                inversion H0. 
                clear H0.

                destruct (String.eqb_eq s b).
                rmDirect.
                rewrite H6 in *; clear H6.

                exists (MatCalE L a L1 b L2), (Retv r1).
                getAnd; eauto.
                simpl; up_in.

                getAnd; eauto.

                exists r0. rewrite <- H4 in *; clear H4.
                getAnd; eauto.
                simpl; up_in.

                right.
                do 4 eexists. 
                getAnd; eauto.
                getAnd; eauto.
                resolve_goEps; eauto.
              }
            }

            1:{
              (* same context r *)
              subst.
              discriminate.
            }
          }
        }
      }
    }


    1:{
      intro H. unfold m2RetM in H. unfold inRM in H.

      breakAll.
      1:{
        destruct x0; destruct m'; try easy; subst;
        apply L_vb_of_list.


        unfold m2RetM.
        unfold inRM.

        apply in_concat.

        exists (map (λ e0 : RetEdge, (None, e0)) 
          (e2RetLinearE (Calv va) s)).
        getAnd; eauto.
        apply in_map_iff.
        exists (x,va).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply in_map_iff.
        eexists.
        getAnd; eauto.
        apply (L_e2RetLinearE (Calv va) s (endE (Calv va))); eauto.


        unfold m2RetM.
        unfold inRM.
        apply in_concat.

        exists (map (λ e0 : RetEdge, (None, e0)) 
          (e2RetLinearE (Plnv vc) s)).
        getAnd; eauto.
        apply in_map_iff.
        exists (x,vc).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply in_map_iff.
        eexists.
        getAnd; eauto.
        apply (L_e2RetLinearE (Plnv vc) s (endE (Plnv vc))); eauto.


        unfold m2RetM.
        unfold inRM.
        apply in_concat.

        exists (map (λ e0 : RetEdge, (None, e0)) 
          (e2RetLinearE (Retv vb) s)).
        getAnd; eauto.
        apply in_map_iff.
        exists (x,vb).
        getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

        apply in_map_iff.
        eexists.
        getAnd; eauto.
        apply (L_e2RetLinearE (Retv vb) s (endE (Retv vb))); eauto.
      }

      1:{
        subst.
        destruct x1; try easy; subst;
        destruct m'; try easy; apply L_vb_of_list.

        1:{
          destruct x;
          breakAll;
          unfold m2RetM;
          unfold inRM;
          apply in_concat.

          1:{
            exists (concat
            (filter_map (va_set.elements ma)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Calv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Calv x)) Lr && goEps (Calv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Calv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Calv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), va).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Calv va) s (endE (Calv va))); eauto.
          }

          1:{
            exists (concat
            (filter_map (va_set.elements ma)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Plnv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Plnv x)) Lr && goEps (Calv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Calv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Calv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), va).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Calv va) s (endE (Calv va))); eauto.
          }

          1:{
            exists (concat
            (filter_map (va_set.elements ma)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Retv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Retv x)) Lr && goEps (Calv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Calv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Calv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), va).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Calv va) s (endE (Calv va))); eauto.
          }
        }

        1:{
          destruct x;
          breakAll;
          unfold m2RetM;
          unfold inRM;
          apply in_concat.

          1:{
            exists (concat
            (filter_map (vc_set.elements mc)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Calv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Calv x)) Lr && goEps (Plnv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Plnv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Plnv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), vc).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Plnv vc) s (endE (Plnv vc))); eauto.
          }

          1:{
            exists (concat
            (filter_map (vc_set.elements mc)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Plnv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Plnv x)) Lr && goEps (Plnv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Plnv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Plnv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), vc).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Plnv vc) s (endE (Plnv vc))); eauto.
          }

          1:{
            exists (concat
            (filter_map (vc_set.elements mc)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Retv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Retv x)) Lr && goEps (Plnv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Plnv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Plnv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), vc).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Plnv vc) s (endE (Plnv vc))); eauto.
          }
        }

        1:{
          destruct x;
          breakAll;
          unfold m2RetM;
          unfold inRM;
          apply in_concat.

          1:{
            exists (concat
            (filter_map (vb_set.elements mb)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Calv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Calv x)) Lr && goEps (Retv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Retv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Retv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), vb).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Retv vb) s (endE (Retv vb))); eauto.
          }

          1:{
            exists (concat
            (filter_map (vb_set.elements mb)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Plnv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Plnv x)) Lr && goEps (Retv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Retv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Retv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), vb).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Retv vb) s (endE (Retv vb))); eauto.
          }

          1:{
            exists (concat
            (filter_map (vb_set.elements mb)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Retv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Retv x)) Lr && goEps (Retv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Retv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Retv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (PndCalE x2 x3 x4), vb).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            getAnd; eauto.
            rewrite H2. simpl.
            apply (vvot.eqb_eq x2 x2); eauto.
            apply in_map_iff.
            eexists.
            getAnd; eauto.

            apply (L_e2RetLinearE (Retv vb) s (endE (Retv vb))); eauto.
          }
        }

      }

      1:{
        subst.
        destruct x1; try easy; subst;
        destruct m'; try easy; apply L_vb_of_list.

        1:{
          destruct x;
          breakAll;
          unfold m2RetM;
          unfold inRM;
          apply in_concat.

          1:{
            exists (concat
            (filter_map (va_set.elements ma)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Calv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Calv x)) Lr && goEps (Calv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Calv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Calv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), va).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Calv ?v) = true =>
              apply (L_goEps (Calv va))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }

          1:{
            exists (concat
            (filter_map (va_set.elements ma)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Plnv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Plnv x)) Lr && goEps (Calv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Calv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Calv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), va).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Calv ?v) = true =>
              apply (L_goEps (Calv va))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }

          1:{
            exists (concat
            (filter_map (va_set.elements ma)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Retv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Retv x)) Lr && goEps (Calv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * CalEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Calv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Calv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), va).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Calv ?v) = true =>
              apply (L_goEps (Calv va))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }
        }

        1:{
          destruct x;
          breakAll;
          unfold m2RetM;
          unfold inRM;
          apply in_concat.

          1:{
            exists (concat
            (filter_map (vc_set.elements mc)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Calv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Calv x)) Lr && goEps (Plnv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Plnv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Plnv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.

            exists (Some (MatCalE x3 x2 x4 s x5), vc).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            getAnd; eauto.

            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Plnv ?v) = true =>
              apply (L_goEps (Plnv vc))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }

          1:{
            exists (concat
            (filter_map (vc_set.elements mc)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Plnv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Plnv x)) Lr && goEps (Plnv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Plnv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Plnv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), vc).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Plnv ?v) = true =>
              apply (L_goEps (Plnv vc))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }

          1:{
            exists (concat
            (filter_map (vc_set.elements mc)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Retv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Retv x)) Lr && goEps (Plnv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * PlnEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Plnv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Plnv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), vc).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Plnv ?v) = true =>
              apply (L_goEps (Plnv vc))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }
        }

        1:{
          destruct x;
          breakAll;
          unfold m2RetM;
          unfold inRM;
          apply in_concat.

          1:{
            exists (concat
            (filter_map (vb_set.elements mb)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Calv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Calv x)) Lr && goEps (Retv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Retv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Retv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), vb).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Retv ?v) = true =>
              apply (L_goEps (Retv vb))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }

          1:{
            exists (concat
            (filter_map (vb_set.elements mb)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Plnv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Plnv x)) Lr && goEps (Retv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Retv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Retv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), vb).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.
            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Retv ?v) = true =>
              apply (L_goEps (Retv vb))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }

          1:{
            exists (concat
            (filter_map (vb_set.elements mb)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE Lr _ _ => eqvv (endE (Retv x)) Lr
                  | MatCalE Lr _ _ _ _ =>
                    eqvv (endE (Retv x)) Lr && goEps (Retv e)
                  end
                | None => false
                end)
               (λ v : option CalEdge * RetEdge,
                let (r0, e) := v in
                match r0 with
                | Some c =>
                  match c with
                  | PndCalE _ _ _ =>
                    map (λ e0 : RetEdge, (r, e0))
                    (e2RetLinearE (Retv e) s)
                  | MatCalE L a L1 b L2 =>
                    if (s =? b)%string
                    then [(r, MatRetE L a L1 b L2)]
                    else []
                  end
                | None =>
                  map (λ e0 : RetEdge, (r, e0))
                  (e2RetLinearE (Retv e) s)
                end))).
            getAnd; eauto.
            apply in_map_iff.
            exists (r, x).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            apply in_concat.

            eexists.
            getAnd; eauto.
            apply_filter_map.
            exists (Some (MatCalE x3 x2 x4 s x5), vb).
            getAnd; eauto using L_ra_in, L_rc_in, L_rb_in.

            getAnd; eauto.
            rewrite H2. simpl.
            apply andb_true_iff.
            getAnd; eauto.
            apply (vvot.eqb_eq x3 x3); eauto.
            match goal with
            | |- goEps (Retv ?v) = true =>
              apply (L_goEps (Retv vb))
            end.
            eauto.

            assert (String.eqb s s = true).
            apply String.eqb_eq; eauto.
            rewrite H3.
            constructor; eauto.
          }
        }
      }
    }

  Qed.

  (* end hide *)


  (** [p]: the one-step parsing function [p] transfers from the current
      configuration [(m,T)] to the next configuration [(m',T')] when
      reading the symbol [i]. *)
  Definition p m T i :=
    match i with 
    | Plain s => 
      let res := m2PlainM m s in
      (res, T)
    | Call s => 
      let res := m2CallM m s in
      (res, m::T)
    | Ret s => 
      match T with 
      | [] => (m2RetM m None s, [])
      | t::T => (m2RetM m (Some t) s, T)
      end
    end.

  (** [Forest]: the relation [Forest M T w] means that the initial
        configuration [(m0,[])] is transferred to the configuration
        [(M,T)] after reading the string [w] *)
  Inductive Forest : (list ME) -> (list ME) -> (list symbol) -> Prop :=
  | FInit: Forest [m0] [] []
  | FInte i m M T w m' T': 
    Forest (m::M) T w
    -> (m', T') = p m T i
    -> Forest (m'::m::M) T' (w++[i]).

  (* begin hide *)
    
  Ltac cmp_len3 :=
    match goal with
    | |- len ?v (?v ++ [?e]) =>
      unfold len
      ; rewrite (last_length v e)
      ; eauto
    | |- len ?v (?v ++ ?w) =>
    unfold len;
    rewrite app_length;
    simpl; eauto;
    lia
    end.

  Fixpoint syncT (I: list CalEdge) (T: list ME) :=
    match I, T with 
    | [], [] => True 
    | i::I', t::T' => syncT I' T'
    | _, _ => False
    end.

  Ltac contraVPG :=
    match goal with
    | h: in_rules (V0 _, Alt_Linear (Ret _) _ ) _ |- _ =>
      destruct (A_VPG_Linear _ _ _ h); eauto; subst;
      repeat (breakEx + breakAnd); subst; discriminate
    | h: in_rules (V0 _, Alt_Linear (Call _) _ ) _ |- _ =>
      destruct (A_VPG_Linear _ _ _ h); eauto; subst;
      repeat (breakEx + breakAnd); subst; discriminate
    end.

  (* end hide *)

  (** [PForest1]: the first property [PForest1] reveals the relation
      between the forest [Forest (m::M) T w] and a VPG parse tree [v] in
      forward small-step relation [Df v I w]. The relation is two-fold:
      (1) if the parse tree stack [I] is empty then the forest stack [T]
      must also be empty, and the context in the last state [m] must be
      [None]; (2) if the parse tree stack [I] is nonempty, then the
      forest stack [T] must also be nonempty, and the context in the
      last state [m] must not be [None]. The relation [Dfx] is an
      extension of the forward small-step relation [Df]. *)
  Lemma PForest1: ∀ m M T w, Forest (m::M) T w ->
    ∀ v e I Le v1 v2 w1 w2,
      Dfx (v++[e]) I w v1 v2 w1 w2 ->
      VBeginWith (v++[e]) L_0 ->
      VEndWith [e] Le ->
        syncT I T /\
        ∃ r, inRM (r,e) m /\
        (
          I=[] /\ T=[] /\ r=None 
          \/
          ∃ I' i, I = i::I' /\
            r = Some i /\
            ∃ t T', T=t::T' /\
            ∃ M', Forest (t::M') T' w1
        ).
  (* begin hide *)
  Proof.
    intros m M T w.
    generalize dependent m.
    generalize dependent M.
    generalize dependent T.

    induction w using (well_founded_ind (len_wf _)).

    intros; breakAll.
    
    match goal with
    | h:Dfx _ _ _ _ _ _ _ |- _ =>
      inversion h; subst; tac_inj; subst
    end.

    (* NOTE T != [] + MatRet *)
    12:{
      extractEnds. inversion a0; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      (* 用归纳假设 *)
      pose (H w0) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H7; subst; eauto.
        eexists. exists []. 
        rewrite <- app_nil_r.
        eauto using app_nil_r.
      }
      destruct H4 as [e [v' Hv]]. subst.
      specialize (H3) with (1:=H11) (2:=H7) (Le:=endE e).
      getH. apply H3.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.
      extractEnds; try_resolve_end.
      clear H3.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
      simplList; subst.
      inversion H12; subst.
      rmDirect.

      pose (H w3) as a.
      breakInfer. tac_app; eauto.
      1:{
        pose (DFX_w) as d.
        specialize d with (1:=H7).
        breakAll. discriminate. simplList; subst.
        repeat rewrite <- app_assoc.
        cmp_len3.
      }


      assert (∃ x e, v3=x++[e]).
      1:{
        destruct v3. tac_invalid_dfx.
        assert (v::v3 != []) as r by eauto using nil_cons.
        destruct (exists_last r) as [? [? e9]]; rewrite e9.
        eauto.
      }
      breakAll; subst.
      specialize H10 with (1:=H4) (2:=H8) (Le:=endE x5).
      getH. apply H10; eauto.

      1:{
        pose (DFX_v) as d.
        specialize d with (1:=H7).
        breakAll. discriminate. simplList; subst.
        rewrite H12 in H2.
        rewrite <- app_assoc in H2.
        apply (VListBeginSame) with (1:=H2).
        eauto using app_cons_not_nil.
      }

      resolveEndESelf.

      clear H10 a.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
      simpl in H3; getAnd; eauto.

      1:{
        exists None.
        getAnd; eauto.
        1:{
          apply L_m2RetM.
          right.
          eexists; getAnd; eauto.
          do 2 eexists; getAnd; eauto.
          destruct x6.
          1: {

            unfold inRM in H13.
            destruct x5; try easy.
            getAnd; eauto.
            exists va.
            getAnd; eauto.

            1:{
              pose DFX_v as o.
              specialize o with (1:=H7).
              breakAll; try discriminate.
              simplList; subst.
              rewrite H12 in *.
              pose (DFX_df) as d.
              specialize d with (1:=H7).
              pose (VConnect) as o.
              specialize o with (1:=d) (v1:=(x ++ [Calv va]))
                (v2:=([Calv (MatCalE x2 x0 x3 x1 Le)] ++ v4))
                (Lv1:=endE (Calv va))
                (Lv2:=x2).
              assert (endE (Calv va) = x2).
              apply o; eauto using app_cons_not_nil, nil_cons.
              destruct va; simpl; tryResolveEnd.
              tryResolveBegin.
              subst.
              simpl; eauto.
            }
            right.
            do 4 eexists.
            getAnd; eauto.
            getAnd; eauto.
            extractEnds; simpl; eauto.
          }
  
          1: {

            unfold inRM in H13.
            destruct x5; try easy.
            getAnd; eauto.
            exists vc.
            getAnd; eauto.

            1:{
              pose DFX_v as o.
              specialize o with (1:=H7).
              breakAll; try discriminate.
              simplList; subst.
              rewrite H12 in *.
              pose (DFX_df) as d.
              specialize d with (1:=H7).
              pose (VConnect) as o.
              specialize o with (1:=d) (v1:=(x ++ [Plnv vc]))
                (v2:=([Calv (MatCalE x2 x0 x3 x1 Le)] ++ v4))
                (Lv1:=endE (Plnv vc))
                (Lv2:=x2).
              assert (endE (Plnv vc) = x2).
              apply o; eauto using app_cons_not_nil, nil_cons.
              destruct vc; simpl; tryResolveEnd.
              tryResolveBegin.
              subst.
              simpl; eauto.
            }
            right.
            do 4 eexists.
            getAnd; eauto.
            getAnd; eauto.
            extractEnds; simpl; eauto.
          }

          1: {

            unfold inRM in H13.
            destruct x5; try easy.
            getAnd; eauto.
            exists vb.
            getAnd; eauto.

            1:{
              pose DFX_v as o.
              specialize o with (1:=H7).
              breakAll; try discriminate.
              simplList; subst.
              rewrite H12 in *.
              pose (DFX_df) as d.
              specialize d with (1:=H7).
              pose (VConnect) as o.
              specialize o with (1:=d) (v1:=(x ++ [Retv vb]))
                (v2:=([Calv (MatCalE x2 x0 x3 x1 Le)] ++ v4))
                (Lv1:=endE (Retv vb))
                (Lv2:=x2).
              assert (endE (Retv vb) = x2).
              apply o; eauto using app_cons_not_nil, nil_cons.
              destruct vb; simpl; tryResolveEnd.
              tryResolveBegin.
              subst.
              simpl; eauto.
            }
            right.
            do 4 eexists.
            getAnd; eauto.
            getAnd; eauto.
            extractEnds; simpl; eauto.
          }
        }
      }

      exists (Some x11).
      getAnd; eauto.
      (* NOTE 证明x10在m里面好像还挺简单的? *)
      1:{
        apply L_m2RetM.
        right.
        eexists; getAnd; eauto.
        do 2 eexists; getAnd; eauto.
        destruct x6.
        1:{
          getAnd; eauto.
          unfold inRM in H13.
          destruct x5; try easy.
          exists va.
          
          getAnd; eauto.
          
          1:{
            pose DFX_v as o.
            specialize o with (1:=H7).
            breakAll; try discriminate; subst.
            simplList; subst.
            rewrite H14 in *.
            pose (DFX_df) as d.
            specialize d with (1:=H7).
            pose (VConnect) as o.
            specialize o with (1:=d) (v1:=(x ++ [Calv va]))
              (v2:=([Calv (MatCalE x2 x0 x3 x1 Le)] ++ v4))
              (Lv1:=endE (Calv va))
              (Lv2:=x2).
            assert (endE (Calv va) = x2).
            apply o; eauto using app_cons_not_nil, nil_cons.
            destruct va; simpl; tryResolveEnd.
            tryResolveBegin.
            subst.
            simpl; eauto.
          }
          right.
          do 4 eexists.
          getAnd; eauto.
          getAnd; eauto.
          extractEnds; simpl; eauto.
        }


        1:{
          getAnd; eauto.
          unfold inRM in H13.
          destruct x5; try easy.
          exists vc.
          
          getAnd; eauto.
          
          1:{
            pose DFX_v as o.
            specialize o with (1:=H7).
            breakAll; try discriminate; subst.
            simplList; subst.
            rewrite H14 in *.
            pose (DFX_df) as d.
            specialize d with (1:=H7).
            pose (VConnect) as o.
            specialize o with (1:=d) (v1:=(x ++ [Plnv vc]))
              (v2:=([Calv (MatCalE x2 x0 x3 x1 Le)] ++ v4))
              (Lv1:=endE (Plnv vc))
              (Lv2:=x2).
            assert (endE (Plnv vc) = x2).
            apply o; eauto using app_cons_not_nil, nil_cons.
            destruct vc; simpl; tryResolveEnd.
            tryResolveBegin.
            subst.
            simpl; eauto.
          }
          right.
          do 4 eexists.
          getAnd; eauto.
          getAnd; eauto.
          extractEnds; simpl; eauto.
        }

        1:{
          getAnd; eauto.
          unfold inRM in H13.
          destruct x5; try easy.
          exists vb.
          
          getAnd; eauto.
          
          1:{
            pose DFX_v as o.
            specialize o with (1:=H7).
            breakAll; try discriminate; subst.
            simplList; subst.
            rewrite H14 in *.
            pose (DFX_df) as d.
            specialize d with (1:=H7).
            pose (VConnect) as o.
            specialize o with (1:=d) (v1:=(x ++ [Retv vb]))
              (v2:=([Calv (MatCalE x2 x0 x3 x1 Le)] ++ v4))
              (Lv1:=endE (Retv vb))
              (Lv2:=x2).
            assert (endE (Retv vb) = x2).
            apply o; eauto using app_cons_not_nil, nil_cons.
            destruct vb; simpl; tryResolveEnd.
            tryResolveBegin.
            subst.
            simpl; eauto.
          }
          right.
          do 4 eexists.
          getAnd; eauto.
          getAnd; eauto.
          extractEnds; simpl; eauto.
        }
      }

      (* NOTE 因为H8和H15 *)
      right.

      do 2 eexists; getAnd; eauto.
      getAnd; eauto.
    }

    (* NOTE T = [] + MatRet *)
    11:{
      extractEnds. inversion a0; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      (* 用归纳假设 *)
      pose (H w0) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H7; subst; eauto.
        eexists. exists []. 
        rewrite <- app_nil_r.
        eauto using app_nil_r.
      }
      destruct H4 as [e [v' Hv]]. subst.
      specialize H3 with (1:=H10) (2:=H7) (Le:=endE e).
      getH. apply H3.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.
      extractEnds; try_resolve_end.
      clear H3.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
      simplList; subst.
      inversion H11; subst.
      rmDirect.

  
      assert (w3=[]).
      1:{
        pose (DFX_len_vw) as d.
        specialize d with (1:=H7).
        breakAll.
        destruct w3; eauto.
        simpl in H9. discriminate.
      }
      subst.

      inversion H4; subst; tac_inj.
      getAnd; eauto.
      exists None.
      getAnd; eauto.
      apply L_m2RetM.
      right.
      eexists; getAnd; eauto.
      do 2 eexists; getAnd; eauto.
      unfold m0.
      getAnd.
      1:{
        exists (PlnE L_0 p_sym L_0).

        getAnd; eauto.
        constructor; eauto.
        simpl.
        pose (DFX_v) as d.
        specialize d with (1:=H7).
        breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
        simplList; subst.
        simpl in H9.
        rewrite H9 in H2.
        simpl in H2.
        inversion H2; breakAll; simplList; eauto.
      }

      right.
      do 4 eexists; getAnd; eauto.
      getAnd; eauto.

      extractEnds; simpl; eauto.
    }

    (* NOTE T!=[] + PndRet *)
    10:{
      extractEnds. inversion a; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      (* 用归纳假设 *)
      pose (H w0) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H6; breakAll; eauto.
      }
      destruct H4 as [e [v' Hv]]. subst.
      specialize (H3) with (1:=H11) (2:=H7) (Le:=endE e).
      getH. apply H3.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.
      extractEnds; try_resolve_end.
      clear H3.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
      simplList; subst.
      inversion H12; subst.
      rmDirect.

      pose (H w3) as a.
      breakInfer. tac_app; eauto.
      1:{
        pose (DFX_w) as d.
        specialize d with (1:=H7).
        breakAll. discriminate. simplList; subst.
        repeat rewrite <- app_assoc.
        cmp_len3.
      }


      assert (∃ x e, v3=x++[e]).
      1:{
        destruct v3. tac_invalid_dfx.
        assert (v::v3 != []) as r by eauto using nil_cons.
        destruct (exists_last r) as [? [? e9]]; rewrite e9.
        eauto.
      }
      breakAll; subst.
      specialize H10 with (1:=H4) (2:=H8) (Le:=endE x7).
      getH. apply H10; eauto.

      1:{
        pose (DFX_v) as d.
        specialize d with (1:=H7).
        breakAll. discriminate. simplList; subst.
        rewrite H12 in H2.
        rewrite <- app_assoc in H2.
        apply (VListBeginSame) with (1:=H2).
        eauto using app_cons_not_nil.
      }

      resolveEndESelf.

      clear H10 a.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
      simpl in H3; getAnd; eauto.

      1:{
        exists None.
        getAnd; eauto.
        1:{
          apply L_m2RetM.
          right.
          eexists; getAnd; eauto.
          do 2 eexists; getAnd; eauto.
          destruct x4.
          1: {

            unfold inRM in H13.
            destruct x7; try easy.
            getAnd; eauto.
            exists va.
            getAnd; eauto.

            1:{
              pose DFX_v as o.
              specialize o with (1:=H7).
              breakAll; try discriminate.
              simplList; subst.
              rewrite H12 in *.
              pose (DFX_df) as d.
              specialize d with (1:=H7).
              pose (VConnect) as o.
              specialize o with (1:=d) (v1:=(x ++ [Calv va]))
                (v2:=([Calv x2] ++ v4))
                (Lv1:=endE (Calv va))
                (Lv2:=beginE (Calv x2)).
              assert (endE (Calv va) = beginE (Calv x2)).
              apply o; eauto using app_cons_not_nil, nil_cons.
              destruct va; simpl; tryResolveEnd.
              tryResolveBegin.
              subst.
              simpl; eauto.
              destruct x2;
              tryResolveBegin.
              eauto.
            }
            destruct x3.
            left.
            do 4 eexists.
            getAnd; eauto.
            getAnd; eauto.
            extractEnds; simpl; eauto.
            extractEnds; simpl; eauto.

            (* NOTE 这还是不可能的 *)
            exfalso.
            pose (DFX_v) as d.
            specialize d with (1:=H7).
            breakAll; try discriminate; simplList; subst.
            pose (DFX_df_sub) as d.
            specialize d with (1:=H7).
            breakAll; try discriminate; simplList; subst.

            
            pose (DFX_df) as d.
            specialize d with (1:=H1).
            rewrite H12 in d.
            pose (DFX_df_rule2) as i.
            specialize i with (1:=H7).

            assert (Df [Calv (MatCalE L a L1 b L2)] [(MatCalE L a L1 b L2)] [Call a])
            as h.
            1:{
              constructor; eauto.
            }
            destruct (A_VPG_Match _ _ _ _ _ i);
            repeat (breakAnd + breakEx); subst.
            destruct v4.
            1:{
              simpl in H12; rewrite H12 in *.
              rewrite <- app_assoc in H1.

              pose (VConnect) as g.
              specialize g with (1:=d) 
                (v1:=((x ++ [Calv va]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
                (v2:=[Retv (PndRetE x1 x0 Le)])
                (Lv1:=V0 x2) (Lv2:=x1).
              assert (V0 x2 = x1).
              apply g; eauto using app_cons_not_nil, nil_cons.
              tryResolveEnd.
              tryResolveBegin.
              rewrite <- H15 in *.

              contraVPG.
            }


            rmDirect.
            pose VHasHead as e0.
            specialize e0 with (1:=H15).
            destruct e0 as [x3 ?].
            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [Calv va]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
              (v2:=v::v4++[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x2) (Lv2:=x3).
            assert (V0 x2 = x3).
            apply g; eauto using app_cons_not_nil, nil_cons.
            repeat rewrite <- app_assoc; eauto.
            tryResolveEnd.
            rewrite app_comm_cons.
            apply (VListBeginSame2); eauto.
            pose VConnectTrue as e0.
            specialize e0 with (1:=H15) (L:=x2) (v1:=v::v4) (v2:=[]).
            getH. apply e0. rewrite H19; eauto.
            rewrite app_nil_r; eauto.
            eauto using nil_cons.
            breakEx.

            clear g.
            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [Calv va]) ++ [Calv (MatCalE L a (V0 x2) b L2)]++v::v4))
              (v2:=[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x4) (Lv2:=x1).
            assert (V0 x4 = x1).
            apply g; eauto using app_cons_not_nil, nil_cons.
            rewrite app_assoc.
            apply VListEndSame2 with (1:=H20).
            tryResolveBegin.
            rewrite <- H21 in *.
            contraVPG.
          }

          1: {

            unfold inRM in H13.
            destruct x7; try easy.
            getAnd; eauto.
            exists vc.
            getAnd; eauto.

            1:{
              pose DFX_v as o.
              specialize o with (1:=H7).
              breakAll; try discriminate.
              simplList; subst.
              rewrite H12 in *.
              pose (DFX_df) as d.
              specialize d with (1:=H7).
              pose (VConnect) as o.
              specialize o with (1:=d) (v1:=(x ++ [Plnv vc]))
                (v2:=([Calv x2] ++ v4))
                (Lv1:=endE (Plnv vc))
                (Lv2:=beginE (Calv x2)).
              assert (endE (Plnv vc) = beginE (Calv x2)).
              apply o; eauto using app_cons_not_nil, nil_cons.
              destruct vc; simpl; tryResolveEnd.
              tryResolveBegin.
              subst.
              simpl; eauto.
              destruct x2;
              tryResolveBegin.
              eauto.
            }
            destruct x3.
            left.
            do 4 eexists.
            getAnd; eauto.
            getAnd; eauto.
            extractEnds; simpl; eauto.
            extractEnds; simpl; eauto.

            (* NOTE 这还是不可能的 *)
            exfalso.
            pose (DFX_v) as d.
            specialize d with (1:=H7).
            breakAll; try discriminate; simplList; subst.
            pose (DFX_df_sub) as d.
            specialize d with (1:=H7).
            breakAll; try discriminate; simplList; subst.

            
            pose (DFX_df) as d.
            specialize d with (1:=H1).
            rewrite H12 in d.
            pose (DFX_df_rule2) as i.
            specialize i with (1:=H7).

            assert (Df [Calv (MatCalE L a L1 b L2)] [(MatCalE L a L1 b L2)] [Call a])
            as h.
            1:{
              constructor; eauto.
            }
            destruct (A_VPG_Match _ _ _ _ _ i);
            repeat (breakAnd + breakEx); subst.
            destruct v4.
            1:{
              simpl in H12; rewrite H12 in *.
              rewrite <- app_assoc in H1.

              pose (VConnect) as g.
              specialize g with (1:=d) 
                (v1:=((x ++ [Plnv vc]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
                (v2:=[Retv (PndRetE x1 x0 Le)])
                (Lv1:=V0 x2) (Lv2:=x1).
              assert (V0 x2 = x1).
              apply g; eauto using app_cons_not_nil, nil_cons.
              tryResolveEnd.
              tryResolveBegin.
              rewrite <- H15 in *.

              contraVPG.
            }


            rmDirect.
            pose VHasHead as e0.
            specialize e0 with (1:=H15).
            destruct e0 as [x3 ?].
            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [Plnv vc]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
              (v2:=v::v4++[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x2) (Lv2:=x3).
            assert (V0 x2 = x3).
            apply g; eauto using app_cons_not_nil, nil_cons.
            repeat rewrite <- app_assoc; eauto.
            tryResolveEnd.
            rewrite app_comm_cons.
            apply (VListBeginSame2); eauto.
            pose VConnectTrue as e0.
            specialize e0 with (1:=H15) (L:=x2) (v1:=v::v4) (v2:=[]).
            getH. apply e0. rewrite H19; eauto.
            rewrite app_nil_r; eauto.
            eauto using nil_cons.
            breakEx.

            clear g.
            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [Plnv vc]) ++ [Calv (MatCalE L a (V0 x2) b L2)]++v::v4))
              (v2:=[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x4) (Lv2:=x1).
            assert (V0 x4 = x1).
            apply g; eauto using app_cons_not_nil, nil_cons.
            rewrite app_assoc.
            apply VListEndSame2 with (1:=H20).
            tryResolveBegin.
            rewrite <- H21 in *.
            contraVPG.
          }

          1: {

            unfold inRM in H13.
            destruct x7; try easy.
            getAnd; eauto.
            exists vb.
            getAnd; eauto.

            1:{
              pose DFX_v as o.
              specialize o with (1:=H7).
              breakAll; try discriminate.
              simplList; subst.
              rewrite H12 in *.
              pose (DFX_df) as d.
              specialize d with (1:=H7).
              pose (VConnect) as o.
              specialize o with (1:=d) (v1:=(x ++ [Retv vb]))
                (v2:=([Calv x2] ++ v4))
                (Lv1:=endE (Retv vb))
                (Lv2:=beginE (Calv x2)).
              assert (endE (Retv vb) = beginE (Calv x2)).
              apply o; eauto using app_cons_not_nil, nil_cons.
              destruct vb; simpl; tryResolveEnd.
              tryResolveBegin.
              subst.
              simpl; eauto.
              destruct x2;
              tryResolveBegin.
              eauto.
            }
            destruct x3.
            left.
            do 4 eexists.
            getAnd; eauto.
            getAnd; eauto.
            extractEnds; simpl; eauto.
            extractEnds; simpl; eauto.

            (* NOTE 这还是不可能的 *)
            exfalso.
            pose (DFX_v) as d.
            specialize d with (1:=H7).
            breakAll; try discriminate; simplList; subst.
            pose (DFX_df_sub) as d.
            specialize d with (1:=H7).
            breakAll; try discriminate; simplList; subst.

            
            pose (DFX_df) as d.
            specialize d with (1:=H1).
            rewrite H12 in d.
            pose (DFX_df_rule2) as i.
            specialize i with (1:=H7).

            assert (Df [Calv (MatCalE L a L1 b L2)] [(MatCalE L a L1 b L2)] [Call a])
            as h.
            1:{
              constructor; eauto.
            }
            destruct (A_VPG_Match _ _ _ _ _ i);
            repeat (breakAnd + breakEx); subst.
            destruct v4.
            1:{
              simpl in H12; rewrite H12 in *.
              rewrite <- app_assoc in H1.

              pose (VConnect) as g.
              specialize g with (1:=d) 
                (v1:=((x ++ [Retv vb]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
                (v2:=[Retv (PndRetE x1 x0 Le)])
                (Lv1:=V0 x2) (Lv2:=x1).
              assert (V0 x2 = x1).
              apply g; eauto using app_cons_not_nil, nil_cons.
              tryResolveEnd.
              tryResolveBegin.
              rewrite <- H15 in *.

              contraVPG.
            }


            rmDirect.
            pose VHasHead as e0.
            specialize e0 with (1:=H15).
            destruct e0 as [x3 ?].
            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [Retv vb]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
              (v2:=v::v4++[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x2) (Lv2:=x3).
            assert (V0 x2 = x3).
            apply g; eauto using app_cons_not_nil, nil_cons.
            repeat rewrite <- app_assoc; eauto.
            tryResolveEnd.
            rewrite app_comm_cons.
            apply (VListBeginSame2); eauto.
            pose VConnectTrue as e0.
            specialize e0 with (1:=H15) (L:=x2) (v1:=v::v4) (v2:=[]).
            getH. apply e0. rewrite H19; eauto.
            rewrite app_nil_r; eauto.
            eauto using nil_cons.
            breakEx.

            clear g.
            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [Retv vb]) ++ [Calv (MatCalE L a (V0 x2) b L2)]++v::v4))
              (v2:=[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x4) (Lv2:=x1).
            assert (V0 x4 = x1).
            apply g; eauto using app_cons_not_nil, nil_cons.
            rewrite app_assoc.
            apply VListEndSame2 with (1:=H20).
            tryResolveBegin.
            rewrite <- H21 in *.
            contraVPG.
          }
        }
      }

      exists (Some x10).
      getAnd; eauto.
      (* NOTE 证明x10在m里面好像还挺简单的? *)
      1:{
        apply L_m2RetM.
        right.
        eexists; getAnd; eauto.
        do 2 eexists; getAnd; eauto.
        destruct x4.
        1:{
          getAnd; eauto.
          unfold inRM in H13.
          destruct x7; try easy.
          exists va.
          
          getAnd; eauto.
          
          1:{
            pose DFX_v as o.
            specialize o with (1:=H7).
            breakAll; try discriminate; subst.
            simplList; subst.
            rewrite H14 in *.
            pose (DFX_df) as d.
            specialize d with (1:=H7).
            pose (VConnect) as o.
            specialize o with (1:=d) (v1:=(x ++ [Calv va]))
              (v2:=([Calv x2] ++ v4))
              (Lv1:=endE (Calv va))
              (Lv2:=beginE (Calv x2)).
            assert (endE (Calv va) = beginE (Calv x2)).
            apply o; eauto using app_cons_not_nil, nil_cons.
            destruct va; simpl; tryResolveEnd.
            tryResolveBegin.
            subst.
            simpl; eauto.
            destruct x2;
            tryResolveBegin.
            eauto.
          }
          destruct x3.
          left.
          do 4 eexists.
          getAnd; eauto.
          getAnd; eauto.
          extractEnds; simpl; eauto.
          extractEnds; simpl; eauto.

          (* NOTE 这还是不可能的 *)
          exfalso.
          pose (DFX_v) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.
          pose (DFX_df_sub) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.

          
          pose (DFX_df) as d.
          specialize d with (1:=H1).
          rewrite H14 in d.
          pose (DFX_df_rule2) as i.
          specialize i with (1:=H7).

          assert (Df [Calv (MatCalE L a L1 b L2)] [(MatCalE L a L1 b L2)] [Call a])
          as h.
          1:{
            constructor; eauto.
          }
          destruct (A_VPG_Match _ _ _ _ _ i);
          repeat (breakAnd + breakEx); subst.
          destruct v4.
          1:{
            simpl in H14; rewrite H14 in *.
            rewrite <- app_assoc in H1.

            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
              (v2:=[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x2) (Lv2:=x1).
            assert (V0 x2 = x1).
            apply g; eauto using app_cons_not_nil, nil_cons.
            tryResolveEnd.
            tryResolveBegin.
            rewrite <- H16 in *.

            contraVPG.
          }


          rmDirect.
          pose VHasHead as e0.
          specialize e0 with (1:=H16).
          destruct e0 as [x3 ?].
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
            (v2:=v::v4++[Retv (PndRetE x1 x0 Le)])
            (Lv1:=V0 x2) (Lv2:=x3).
          assert (V0 x2 = x3).
          apply g; eauto using app_cons_not_nil, nil_cons.
          repeat rewrite <- app_assoc; eauto.
          tryResolveEnd.
          rewrite app_comm_cons.
          apply (VListBeginSame2); eauto.
          pose VConnectTrue as e0.
          specialize e0 with (1:=H16) (L:=x2) (v1:=v::v4) (v2:=[]).
          getH. apply e0. rewrite H20; eauto.
          rewrite app_nil_r; eauto.
          eauto using nil_cons.
          breakEx.

          clear g.
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]++v::v4))
            (v2:=[Retv (PndRetE x1 x0 Le)])
            (Lv1:=V0 x4) (Lv2:=x1).
          assert (V0 x4 = x1).
          apply g; eauto using app_cons_not_nil, nil_cons.
          rewrite app_assoc.
          apply VListEndSame2 with (1:=H21).
          tryResolveBegin.
          rewrite <- H22 in *.
          contraVPG.
        }

        1:{
          getAnd; eauto.
          unfold inRM in H13.
          destruct x7; try easy.
          exists vc.
          
          getAnd; eauto.
          
          1:{
            pose DFX_v as o.
            specialize o with (1:=H7).
            breakAll; try discriminate; subst.
            simplList; subst.
            rewrite H14 in *.
            pose (DFX_df) as d.
            specialize d with (1:=H7).
            pose (VConnect) as o.
            specialize o with (1:=d) (v1:=(x ++ [Plnv vc]))
              (v2:=([Calv x2] ++ v4))
              (Lv1:=endE (Plnv vc))
              (Lv2:=beginE (Calv x2)).
            assert (endE (Plnv vc) = beginE (Calv x2)).
            apply o; eauto using app_cons_not_nil, nil_cons.
            destruct vc; simpl; tryResolveEnd.
            tryResolveBegin.
            subst.
            simpl; eauto.
            destruct x2;
            tryResolveBegin.
            eauto.
          }
          destruct x3.
          left.
          do 4 eexists.
          getAnd; eauto.
          getAnd; eauto.
          extractEnds; simpl; eauto.
          extractEnds; simpl; eauto.

          (* NOTE 这还是不可能的 *)
          exfalso.
          pose (DFX_v) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.
          pose (DFX_df_sub) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.

          
          pose (DFX_df) as d.
          specialize d with (1:=H1).
          rewrite H14 in d.
          pose (DFX_df_rule2) as i.
          specialize i with (1:=H7).

          assert (Df [Calv (MatCalE L a L1 b L2)] [(MatCalE L a L1 b L2)] [Call a])
          as h.
          1:{
            constructor; eauto.
          }
          destruct (A_VPG_Match _ _ _ _ _ i);
          repeat (breakAnd + breakEx); subst.
          destruct v4.
          1:{
            simpl in H14; rewrite H14 in *.
            rewrite <- app_assoc in H1.

            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
              (v2:=[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x2) (Lv2:=x1).
            assert (V0 x2 = x1).
            apply g; eauto using app_cons_not_nil, nil_cons.
            tryResolveEnd.
            tryResolveBegin.
            rewrite <- H16 in *.

            contraVPG.
          }


          rmDirect.
          pose VHasHead as e0.
          specialize e0 with (1:=H16).
          destruct e0 as [x3 ?].
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
            (v2:=v::v4++[Retv (PndRetE x1 x0 Le)])
            (Lv1:=V0 x2) (Lv2:=x3).
          assert (V0 x2 = x3).
          apply g; eauto using app_cons_not_nil, nil_cons.
          repeat rewrite <- app_assoc; eauto.
          tryResolveEnd.
          rewrite app_comm_cons.
          apply (VListBeginSame2); eauto.
          pose VConnectTrue as e0.
          specialize e0 with (1:=H16) (L:=x2) (v1:=v::v4) (v2:=[]).
          getH. apply e0. rewrite H20; eauto.
          rewrite app_nil_r; eauto.
          eauto using nil_cons.
          breakEx.

          clear g.
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]++v::v4))
            (v2:=[Retv (PndRetE x1 x0 Le)])
            (Lv1:=V0 x4) (Lv2:=x1).
          assert (V0 x4 = x1).
          apply g; eauto using app_cons_not_nil, nil_cons.
          rewrite app_assoc.
          apply VListEndSame2 with (1:=H21).
          tryResolveBegin.
          rewrite <- H22 in *.
          contraVPG.
        }

        1:{
          getAnd; eauto.
          unfold inRM in H13.
          destruct x7; try easy.
          exists vb.
          
          getAnd; eauto.
          
          1:{
            pose DFX_v as o.
            specialize o with (1:=H7).
            breakAll; try discriminate; subst.
            simplList; subst.
            rewrite H14 in *.
            pose (DFX_df) as d.
            specialize d with (1:=H7).
            pose (VConnect) as o.
            specialize o with (1:=d) (v1:=(x ++ [Retv vb]))
              (v2:=([Calv x2] ++ v4))
              (Lv1:=endE (Retv vb))
              (Lv2:=beginE (Calv x2)).
            assert (endE (Retv vb) = beginE (Calv x2)).
            apply o; eauto using app_cons_not_nil, nil_cons.
            destruct vb; simpl; tryResolveEnd.
            tryResolveBegin.
            subst.
            simpl; eauto.
            destruct x2;
            tryResolveBegin.
            eauto.
          }
          destruct x3.
          left.
          do 4 eexists.
          getAnd; eauto.
          getAnd; eauto.
          extractEnds; simpl; eauto.
          extractEnds; simpl; eauto.

          (* NOTE 这还是不可能的 *)
          exfalso.
          pose (DFX_v) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.
          pose (DFX_df_sub) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.

          
          pose (DFX_df) as d.
          specialize d with (1:=H1).
          rewrite H14 in d.
          pose (DFX_df_rule2) as i.
          specialize i with (1:=H7).

          assert (Df [Calv (MatCalE L a L1 b L2)] [(MatCalE L a L1 b L2)] [Call a])
          as h.
          1:{
            constructor; eauto.
          }
          destruct (A_VPG_Match _ _ _ _ _ i);
          repeat (breakAnd + breakEx); subst.
          destruct v4.
          1:{
            simpl in H14; rewrite H14 in *.
            rewrite <- app_assoc in H1.

            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
              (v2:=[Retv (PndRetE x1 x0 Le)])
              (Lv1:=V0 x2) (Lv2:=x1).
            assert (V0 x2 = x1).
            apply g; eauto using app_cons_not_nil, nil_cons.
            tryResolveEnd.
            tryResolveBegin.
            rewrite <- H16 in *.

            contraVPG.
          }


          rmDirect.
          pose VHasHead as e0.
          specialize e0 with (1:=H16).
          destruct e0 as [x3 ?].
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]))
            (v2:=v::v4++[Retv (PndRetE x1 x0 Le)])
            (Lv1:=V0 x2) (Lv2:=x3).
          assert (V0 x2 = x3).
          apply g; eauto using app_cons_not_nil, nil_cons.
          repeat rewrite <- app_assoc; eauto.
          tryResolveEnd.
          rewrite app_comm_cons.
          apply (VListBeginSame2); eauto.
          pose VConnectTrue as e0.
          specialize e0 with (1:=H16) (L:=x2) (v1:=v::v4) (v2:=[]).
          getH. apply e0. rewrite H20; eauto.
          rewrite app_nil_r; eauto.
          eauto using nil_cons.
          breakEx.

          clear g.
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=((x ++ [x7]) ++ [Calv (MatCalE L a (V0 x2) b L2)]++v::v4))
            (v2:=[Retv (PndRetE x1 x0 Le)])
            (Lv1:=V0 x4) (Lv2:=x1).
          assert (V0 x4 = x1).
          apply g; eauto using app_cons_not_nil, nil_cons.
          rewrite app_assoc.
          apply VListEndSame2 with (1:=H21).
          tryResolveBegin.
          rewrite <- H22 in *.
          contraVPG.
        }
      }

      (* NOTE 因为H8和H15 *)
      right.

      do 2 eexists; getAnd; eauto.
      getAnd; eauto.
    }


    (* NOTE T=[] + PndRet *)
    9:{

      extractEnds. inversion a; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      (* 用归纳假设 *)
      pose (H w0) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H6; breakAll; subst; eauto.
      }
      destruct H4 as [e [v' Hv]]. subst.
      specialize H3 with (1:=H10) (2:=H7) (Le:=endE e).
      getH. apply H3.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.
      extractEnds; try_resolve_end.
      clear H3.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
      simplList; subst.
      inversion H11; subst.
      rmDirect.

  
      assert (w3=[]).
      1:{
        pose (DFX_len_vw) as d.
        specialize d with (1:=H7).
        breakAll.
        destruct w3; eauto.
        simpl in H9. discriminate.
      }
      subst.

      inversion H4; subst; tac_inj.
      getAnd; eauto.
      exists None.
      getAnd; eauto.
      apply L_m2RetM.
      right.
      eexists; getAnd; eauto.
      do 2 eexists; getAnd; eauto.
      unfold m0.
      getAnd.
      1:{
        exists (PlnE L_0 p_sym L_0).

        getAnd; eauto.
        constructor; eauto.
        simpl.
        pose (DFX_v) as d.
        specialize d with (1:=H7).
        breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx;
        simplList; subst.
        simpl in H9.
        rewrite H9 in H2.
        simpl in H2.
        inversion H2; breakAll; simplList; eauto.
      }


      destruct x3.

      left.
      do 4 eexists; getAnd; eauto.
      getAnd; eauto.

      extractEnds; simpl; eauto.
      extractEnds; simpl; eauto.

      right.
      (* NOTE 这是不可能的, 因为是PndRet *)
      pose (VConnectTrue).

      (* NOTE 这还是不可能的 *)
      exfalso.
      pose (DFX_v) as d.
      specialize d with (1:=H7).
      breakAll; try discriminate; simplList; subst.
      pose (DFX_df_sub) as d.
      specialize d with (1:=H7).
      breakAll; try discriminate; simplList; subst.

      
      pose (DFX_df) as d.
      specialize d with (1:=H1).
      simpl in H9.
      rewrite H9 in d.
      pose (DFX_df_rule2) as i.
      specialize i with (1:=H7).

      destruct (A_VPG_Match _ _ _ _ _ i);
      repeat (breakAnd + breakEx); subst.
      destruct v3.
      1:{
        pose (VConnect) as g.
        specialize g with (1:=d) 
          (v1:=([Calv (MatCalE L a (V0 x) b L2)]))
          (v2:=[Retv (PndRetE x1 x0 Le)])
          (Lv1:=V0 x) (Lv2:=x1).
        assert (V0 x = x1).
        apply g; eauto using app_cons_not_nil, nil_cons.
        try_resolve_end.
        tryResolveBegin.
        rewrite <- H12 in *.

        contraVPG.
      }


      rmDirect.
      pose VHasHead as e2.
      specialize e2 with (1:=H12).
      destruct e2 as [x3 ?].
      pose (VConnect) as g.
      specialize g with (1:=d) 
        (v1:=([Calv (MatCalE L a (V0 x) b L2)]))
        (v2:=v::v3++[Retv (PndRetE x1 x0 Le)])
        (Lv1:=V0 x) (Lv2:=x3).
      assert (V0 x = x3).
      apply g; eauto using app_cons_not_nil, nil_cons.
      repeat rewrite <- app_assoc; eauto.
      try_resolve_end.
      rewrite app_comm_cons.
      apply (VListBeginSame2); eauto.
      pose VConnectTrue as e2.
      specialize e2 with (1:=H12) (L:=x) (v1:=v::v3) (v2:=[]).
      getH. apply e2. rewrite H16; eauto.
      rewrite app_nil_r; eauto.
      eauto using nil_cons.
      breakEx.

      clear g.
      pose (VConnect) as g.
      specialize g with (1:=d) 
        (v1:=([Calv (MatCalE L a (V0 x) b L2)]++v::v3))
        (v2:=[Retv (PndRetE x1 x0 Le)])
        (Lv1:=V0 x2) (Lv2:=x1).
      assert (V0 x2 = x1).
      apply g; eauto using app_cons_not_nil, nil_cons.
      apply VListEndSame2 with (1:=H17).
      tryResolveBegin.
      rewrite <- H18 in *.
      contraVPG.
    }

    (* NOTE T=[] + PndRet *)
    8:{

      extractEnds. inversion a; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      (* 用归纳假设 *)
      pose (H w0) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H6; breakAll; subst; eauto.
      }
      destruct H4 as [e [v' Hv]]. subst.
      specialize H3 with (1:=H10) (2:=H7) (Le:=endE e).
      getH. apply H3.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.
      extractEnds; try_resolve_end.
      clear H3.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx.
      inversion H11; subst.
      rmDirect.
      rmDirect.

  
      assert (w3=[]).
      1:{
        pose (DFX_w2) as d.
        specialize d with (1:=H7).
        breakAll; subst. eauto.
        discriminate.
      }
      subst.

      getAnd; eauto.
      exists None.
      getAnd; eauto.
      apply L_m2RetM.
      left.
      getAnd; eauto.
      getAnd; eauto.
      do 2 eexists; getAnd; eauto.
      exists Le.
      getAnd; eauto.
      extractEnds; simpl; eauto.
      extractEnds; simpl; eauto.
    }

    7:{

      extractEnds. inversion a; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      inversion H8; subst; tac_inj.

      breakTuple.
      rmDirect.
      getAnd; eauto.
      constructor; eauto.
      exists None.
      getAnd; eauto.
      apply L_m2RetM.
      left.
      getAnd; eauto.
      getAnd; eauto.
      unfold m0.
      exists None, (Plnv (PlnE L_0 p_sym L_0)).
      getAnd; eauto.
      simpl; eauto.

      apply vc_set.singleton_spec; eauto.

      exists Le.

      simpl in H2.
      getAnd; eauto;
      simpl;
      mergeBegin; eauto.
    }

    (* NOTE T!=[] + MatCal *)
    6:{
      extractEnds. inversion a0; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      inversion H11; subst; tac_inj.
      rmDirect.


      pose (H w1) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H6; breakAll; eauto.
      }
      destruct H4 as [e [v' Hv]]. subst.
      specialize (H3) with (1:=H10) (2:=H7) (Le:=endE e).
      getH. apply H3.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.
      extractEnds; try_resolve_end.
      clear H3.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx.

      1:{
        getAnd. constructor; eauto.
        exists (Some (MatCalE x2 x0 Le x1 x3)).
        getAnd; eauto.
        1:{
          apply L_m2CallM.
          do 2 eexists; getAnd; eauto.
          exists (endE e).
          getAnd; eauto.
          getAnd; eauto.
          1:{
            intros.
            right.
            
            do 3 eexists; getAnd; eauto.
            extractEnds; simpl; eauto.
            extractEnds; simpl; eauto.
          }
          intros. breakAll; discriminate.
        }

        right.
        do 2 eexists; getAnd; eauto.
        getAnd; eauto.
      }

      1:{
        getAnd.
        simpl in H3.
        simpl; eauto.
        exists (Some (MatCalE x2 x0 Le x1 x3)).
        getAnd; eauto.
        1:{
          apply L_m2CallM.
          do 2 eexists; getAnd; eauto.
          exists (endE e).
          getAnd; eauto.
          getAnd; eauto.
          1:{
            intros.
            right.
            
            do 3 eexists; getAnd; eauto.
            extractEnds; simpl; eauto.
            extractEnds; simpl; eauto.
          }
          intros. breakAll; subst.
          inversion H9; subst.
          do 3 eexists; getAnd; eauto.
          extractEnds; simpl; eauto.
          extractEnds; simpl; eauto.
        }

        right.
        do 2 eexists; getAnd; eauto.
        getAnd; eauto.
      }
    }

    (* NOTE T=[i] + MatCal *)
    5:{
      extractEnds. inversion a0; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      inversion H9; subst; tac_inj.
      rmDirect.

      
      inversion H8; subst; tac_inj.
      getAnd.
      constructor; eauto.
      exists (Some (MatCalE x2 x0 Le x1 x3)).
      getAnd; eauto.
      1:{

        apply L_m2CallM.
        unfold m0.
        exists None, (Plnv (PlnE L_0 p_sym L_0)).
        getAnd; eauto.
        constructor; eauto.
        exists L_0.

        getAnd; eauto.
        getAnd; eauto.
        1:{
          intros.
          right.
          
          simpl in H2.
          assert (x2=L_0).
          1:{
            mergeBegin. eauto.
          }
          subst.
          do 3 eexists; getAnd; eauto.
        }
        intros. breakAll; discriminate.
      }

      right.
      do 2 eexists; getAnd; eauto.
      getAnd; eauto.
    }


    (* NOTE T!=[] + PndCal *)
    4:{
      extractEnds. inversion a0; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      inversion H11; subst; tac_inj.
      rmDirect.


      pose (H w1) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H6; breakAll; eauto.
      }
      destruct H4 as [e [v' Hv]]. subst.
      specialize (H3) with (1:=H10) (2:=H7) (Le:=endE e).
      getH. apply H3.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.
      extractEnds; try_resolve_end.
      clear H3.
      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx.

      1:{
        getAnd. constructor; eauto.
        exists (Some (PndCalE x1 x0 Le)).
        getAnd; eauto.
        1:{
          apply L_m2CallM.
          do 2 eexists; getAnd; eauto.
          exists (endE e).
          getAnd; eauto.
          getAnd; eauto.
          1:{
            intros.
            left.
            
            eexists Le; getAnd; eauto;
            extractEnds; simpl; eauto.
          }
          intros. breakAll; discriminate.
        }

        right.
        do 2 eexists; getAnd; eauto.
        getAnd; eauto.
      }

      1:{
        getAnd.
        simpl in H3.
        simpl; eauto.
        exists (Some (PndCalE x1 x0 Le)).
        getAnd; eauto.
        1:{
          apply L_m2CallM.
          do 2 eexists; getAnd; eauto.
          exists (endE e).
          getAnd; eauto.
          getAnd; eauto.
          1:{
            intros.
            left.
            
            exists Le; getAnd; eauto;
            extractEnds; simpl; eauto.
          }
          intros. breakAll; subst.
          inversion H9; subst.
          (* NOTE 这里H9根据stack可以证伪 *)

          exfalso.
          pose (DFX_v) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.
          pose (DFX_df_sub) as d.
          specialize d with (1:=H7).
          breakAll; try discriminate; simplList; subst.

          
          pose (DFX_df) as d.
          specialize d with (1:=H1).
          rewrite H11 in d.
          pose (DFX_df_rule2) as i.
          specialize i with (1:=H7).

          assert (Df [Calv (MatCalE x x7 x8 x9 x10)] [(MatCalE x x7 x8 x9 x10)] [Call x7])
          as h.
          1:{
            constructor; eauto.
          }
          destruct (A_VPG_Match _ _ _ _ _ i);
          repeat (breakAnd + breakEx); subst.
          destruct v4.
          1:{
            simpl in H11; rewrite H11 in *.
            rewrite <- app_assoc in H1.

            pose (VConnect) as g.
            specialize g with (1:=d) 
              (v1:=(v3 ++ [Calv (MatCalE x x7 (V0 x2) x9 x10)]))
              (v2:=[Calv (PndCalE x1 x0 Le)])
              (Lv1:=V0 x2) (Lv2:=x1).
            assert (V0 x2 = x1).
            apply g; eauto using app_cons_not_nil, nil_cons.
            simpl; eauto.
            tryResolveEnd.
            tryResolveBegin.
            rewrite <- H13 in *.

            contraVPG.
          }


          rmDirect.
          pose VHasHead as e0.
          specialize e0 with (1:=H13).
          destruct e0 as [p1 ?].
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=(v3 ++ [Calv (MatCalE x x7 (V0 x2) x9 x10)]))
            (v2:=v::v4++[Calv (PndCalE x1 x0 Le)])
            (Lv1:=V0 x2) (Lv2:=p1).
          assert (V0 x2 = p1).
          apply g; eauto using app_cons_not_nil, nil_cons.
          repeat rewrite <- app_assoc; eauto.
          tryResolveEnd.
          rewrite app_comm_cons.
          apply (VListBeginSame2); eauto.
          pose VConnectTrue as e0.
          specialize e0 with (1:=H13) (L:=x2) (v1:=v::v4) (v2:=[]).
          getH. apply e0. rewrite H17; eauto.
          rewrite app_nil_r; eauto.
          eauto using nil_cons.
          breakEx.

          clear g.
          pose (VConnect) as g.
          specialize g with (1:=d) 
            (v1:=(v3 ++ [Calv (MatCalE x x7 (V0 x2) x9 x10)]++v::v4))
            (v2:=[Calv (PndCalE x1 x0 Le)])
            (Lv1:=V0 x8) (Lv2:=x1).
          assert (V0 x8 = x1).
          apply g; eauto using app_cons_not_nil, nil_cons.
          rewrite app_assoc.
          apply VListEndSame2 with (1:=H18).
          tryResolveBegin.
          rewrite <- H19 in *.
          contraVPG.
        }

        right.
        do 2 eexists; getAnd; eauto.
        getAnd; eauto.
      }
    }

    3:{
      extractEnds. inversion a0; subst.
      rmDirect.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.

      inversion H9; subst; tac_inj.
      rmDirect.

      
      inversion H8; subst; tac_inj.
      getAnd.
      constructor; eauto.
      exists (Some (PndCalE x1 x0 Le)).
      getAnd; eauto.
      1:{

        apply L_m2CallM.
        unfold m0.
        exists None, (Plnv (PlnE L_0 p_sym L_0)).
        getAnd; eauto.
        constructor; eauto.
        exists L_0.

        getAnd; eauto.
        getAnd; eauto.
        1:{
          intros.
          left.
          
          simpl in H2.
          assert (x1=L_0).
          1:{
            mergeBegin. eauto.
          }
          subst.
          exists Le; getAnd; eauto.
        }
        intros. breakAll; discriminate.
      }

      right.
      do 2 eexists; getAnd; eauto.
      getAnd; eauto.
    }

    2:{
      simpl in H1; simpl in H2.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.
      inversion H12; subst.
      rmDirect.

      pose (H w0) as e.
      breakInfer. tac_app; eauto.
      cmp_len3. clear e.
      assert (exists e v', v=v'++[e]).
      1:{
        inversion H6; breakAll; eauto.
      }
      destruct H8 as [e [v' Hv]]. subst.
      specialize (H4) with (1:=H11) (2:=H7) (Le:=endE e).
      getH. apply H4.
      
      apply (VListBeginSame) with (1:=H2).
      eauto using app_cons_not_nil.

      (* FIXME copy *)
      resolveEndESelf.

      breakAll; try discriminate; tac_inj; subst; try tac_invalid_dfx.
      1:{
        getAnd; eauto.
        exists None.
        getAnd; eauto.

        apply L_m2PlainM.
        exists e, (endE e), L1.
        getAnd; eauto.
        getAnd; eauto.
        getAnd; eauto;
        extractEnds; simpl; eauto;
        inversion a; subst; eauto;
        extractEnds; simpl; eauto.
      }

      simpl in H9.
      getAnd; eauto.
      exists (Some x1).
      getAnd; eauto.
      apply L_m2PlainM.
      exists e, (endE e), L1.
      getAnd; eauto.
      getAnd; eauto.
      getAnd; eauto;
      extractEnds; simpl; eauto;
      inversion a; subst; eauto;
      extractEnds; simpl; eauto.
      right.

      do 2 eexists; getAnd; eauto. 
      getAnd; eauto. 
    }

    1:{
      simpl in H1; simpl in H2.
      inversion H0; subst; tac_inj; subst.
      match goal with
      | h: _ = p _ _ _ |- _ =>
        unfold p in h
      end.
      inversion H10; subst.
      rmDirect.

      inversion H9; subst; tac_inj.
      getAnd; eauto.
      constructor; eauto.

      exists None.
      getAnd; eauto.

      simpl in H2. mergeBegin.

      apply (L_m2PlainM).

      exists (Plnv (PlnE L_0 p_sym L_0)).
      do 2 eexists. 
      getAnd; eauto.
      simpl; eauto.
      apply vc_set.singleton_spec; eauto.
    }

  Qed.
  (* end hide *)

  (** [PForest2]: the second property [PForest2] is in the other
      direction of the first property [PForest1]: (1) if the context in
      the last state of the forest is [None], then both stacks [I] and
      [T] must be empty; (2) otherwise the stacks must be nonempty, and
      the context should be the top of the parse tree stack for some
      parse tree. *)
  Lemma PForest2: ∀ w m M T, Forest (m::M) T w ->
      w != [] ->
      ∀ r e, inRM (r, e) m ->
      (
        r=None -> ∃ v, Df (v++[e]) [] w /\ VBeginWith (v++[e]) L_0
      )
      /\
      (
        ∀ ea, r=Some ea -> ∃ v T', Df (v++[e]) (ea::T') w
        /\ VBeginWith (v++[e]) L_0
      ).
  (* begin hide *)
  Proof.
    intro w.
    induction w using (well_founded_ind (len_wf _)).
    intros.
    inversion H0; subst.
    contradiction.

    
    match goal with
    | h: _ = p _ _ _ |- _ =>
      unfold p in h
    end.

    destruct w0.
    1: {
      inversion H5; subst; tac_inj.
      destruct i; breakTuple; rmDirect.

      1:{
        match goal with
        | h: inRM (?r, ?e) (m2CallM ?m' ?s) |- _ =>
         destruct (L_m2CallM m' s r e) as [d _]
         ; rmDirect
        end.
        breakAll.

        unfold m0 in H4.
        simpl in H4.
        destruct x0; try easy.

        Ltac breakSingleton :=
        match goal with
        | h:vc_set.In ?x (vc_set.singleton ?y) |- _ =>
         destruct (vc_set.singleton_spec y x) as [? _]
         ; rmDirect
        end;
        match goal with
        | h:(eq * eq)%signature ?x ?y |- _ =>
          assert (x=y) by
          (inversion h as [_h1 _h2];
          inversion _h1;
          inversion _h2;
          simpl in *; subst; eauto)
          ; clear h
        end.

        breakSingleton.
        
        breakAll; try easy.
        breakTuple.
        rmDirect.
        clear H3.
        getH. apply H7. left; eauto. clear H7.
        breakAll; subst.
        1:{
          getAnd; intros; subst.
          discriminate.

          exists [], []. simpl.
          breakSingleton.
          getAnd; eauto.
          inversion H6.
          constructor; eauto.
          tryResolveBegin.
        }
        getAnd; intros; subst.
        inversion H6.

        inversion H6.
        exists [], []. simpl.
        inversion H4; subst.
        getAnd; eauto.

        constructor; eauto.
        tryResolveBegin.

        inversion H9.
      }

      1:{
        match goal with
        | h: inRM (?r, ?e) (m2PlainM ?m' ?s) |- _ =>
         destruct (L_m2PlainM m' s r e) as [d _]
         ; rmDirect
        end.
        breakAll.

        unfold m0 in H4.
        simpl in H4.
        destruct x; try easy.
        breakSingleton.
        breakAll; try easy.
        breakTuple.
        rmDirect.
        getAnd; intros; subst.

        exists []. simpl.
        getAnd; eauto.
        constructor; eauto.
        tryResolveBegin.
        discriminate.
      }

      1:{
        match goal with
        | h: inRM (?r, ?e) (m2RetM ?m' ?t ?s) |- _ =>
         destruct (L_m2RetM m' t s r e) as [d _]
         ; rmDirect
        end.
        breakAll; subst; try discriminate.

        unfold m0 in H7.
        simpl in H7.
        destruct x0; try easy.

        breakSingleton.
        breakAll; try easy.
        breakTuple.
        rmDirect.
        getAnd; intros; subst.

        exists []. simpl.
        getAnd; eauto.
        constructor; eauto.
        tryResolveBegin.

        discriminate.
      }
    
    }


    pose (H (s::w0)) as a.
    breakInfer. tac_app; eauto.
    cmp_len3. clear a.
    specialize (H3) with (1:=H5).
    getH. apply H3. eauto using nil_cons. clear H3.
    rename H4 into hi.

    destruct i.
    
    1:{
      breakTuple; rmDirect.
      match goal with
      | h: inRM (?r, ?e) (m2CallM ?m' ?s) |- _ =>
       destruct (L_m2CallM m' s r e) as [d _]
       ; rmDirect
      end.
      breakAll.
      specialize hi with (1:=H4).
      breakAll.

      destruct x.
      1:{
        clear H8.
        specialize hi with (ea:=c).
        rmDirect.
        breakAll.
        destruct c.
        1:{
          clear H3.
          getH. apply H7.
          right. do 3 eexists; eauto.
          breakAll; subst.
          1:{

            clear H7.
            
            getAnd; intros. discriminate.
            inversion H6; subst.
            rmDirect.
            match goal with
            | h:Df ?v ?T _ |- _ =>
            exists v, T
            end.
            getAnd; eauto.
            constructor; eauto.
            apply VListEndSame2.
            resolveEndESelf.
            apply VListBeginSame2; eauto.
          }

          getAnd; intros. discriminate.
          inversion H6; subst.
          rmDirect.
          match goal with
          | h:Df ?v ?T _ |- _ =>
          exists v, T
          end.
          getAnd; eauto.
          constructor; eauto.
          apply VListEndSame2.
          resolveEndESelf.
          apply VListBeginSame2; eauto.
        }
        
        clear H7.
        getH. apply H3.
        do 5 eexists; eauto.
        breakAll; subst.

        clear H3.
        
        getAnd; intros. discriminate.
        inversion H3; subst.
        rmDirect.
        match goal with
        | h:Df ?v ?T _ |- _ =>
        exists v, T
        end.
        getAnd; eauto.
        constructor; eauto.
        apply VListEndSame2.
        resolveEndESelf.
        apply VListBeginSame2; eauto.
      }

      rmDirect.
      breakAll.
      clear H3.
      getH. apply H7. eauto. clear H7.
      breakAll; subst.
      
      getAnd; intros; try discriminate.
      inversion H6; subst.
      rmDirect.
      match goal with
      | h:Df ?v ?T _ |- _ =>
      exists v, T
      end.
      getAnd; eauto.
      constructor; eauto.
      apply VListEndSame2.
      resolveEndESelf.
      apply VListBeginSame2; eauto.

      getAnd; intros; try discriminate.
      inversion H6; subst.
      rmDirect.
      match goal with
      | h:Df ?v ?T _ |- _ =>
      exists v, T
      end.
      getAnd; eauto.
      constructor; eauto.
      apply VListEndSame2.
      resolveEndESelf.
      apply VListBeginSame2; eauto.
    }

    1:{
      breakTuple; rmDirect.
      match goal with
      | h: inRM (?r, ?e) (m2PlainM ?m' ?s) |- _ =>
       destruct (L_m2PlainM m' s r e) as [d _]
       ; rmDirect
      end.
      breakAll.
      specialize hi with (1:=H4).
      breakAll.

      destruct r; subst.
      1:{
        clear H8.
        specialize hi with (ea:=c).
        rmDirect.
        breakAll.
        destruct c.
        1:{
          getAnd; intros; try discriminate.
          inversion H8; subst.
          rmDirect.
          match goal with
          | h:Df ?v (_::?T) _ |- _ =>
          exists v, T
          end.
          getAnd; eauto.
          constructor; eauto.
          apply VListEndSame2.
          resolveEndESelf.
          apply VListBeginSame2; eauto.
        }
        getAnd; intros; try discriminate.
        inversion H8; subst.
        rmDirect.
        match goal with
        | h:Df ?v (_::?T) _ |- _ =>
        exists v, T
        end.
        getAnd; eauto.
        constructor; eauto.
        apply VListEndSame2.
        resolveEndESelf.
        apply VListBeginSame2; eauto.
      }


      
      getAnd; intros; try discriminate.
      rmDirect.
      breakAll.
      match goal with
      | h:Df ?v ?T _ |- _ =>
      exists v
      end.
      getAnd; eauto.
      constructor; eauto.
      apply VListEndSame2.
      resolveEndESelf.
      apply VListBeginSame2; eauto.
    }

    1:{
      destruct T0; breakTuple; rmDirect.
      1:{
        match goal with
        | h: inRM (?r, ?e) (m2RetM ?m' ?t ?s) |- _ =>
         destruct (L_m2RetM m' t s r e) as [d _]
         ; rmDirect
        end;
        breakAll; subst; try discriminate.
        specialize hi with (1:=H7).
        breakAll.
        destruct x.
        1:{
          clear H6.
          specialize hi with (ea:=c).
          rmDirect.
          breakAll.
          destruct c.
          1:{
            getAnd; intros; try discriminate.
            rmDirect.

            pose (DF_dfx) as d.
            specialize d with (1:=H8).
            breakAll.
            pose (PForest1) as e.
            specialize e with (1:=H5) (2:=d) (Le:=endE x0).
            getH. apply e; eauto.
            resolveEndESelf.
            breakAll; discriminate.
          }
          getAnd; intros; try discriminate.
          rmDirect.

          pose (DF_dfx) as d.
          specialize d with (1:=H8).
          breakAll.
          pose (PForest1) as e.
          specialize e with (1:=H5) (2:=d) (Le:=endE x0).
          getH. apply e; eauto.
          resolveEndESelf.
          breakAll; discriminate.

        }
  
        rmDirect.
        breakAll.
        
        getAnd; intros; try discriminate.
        rmDirect.
        match goal with
        | h:Df ?v ?T _ |- _ =>
        exists v
        end.
        getAnd; eauto.
        constructor; eauto.
        apply VListEndSame2.
        resolveEndESelf.
        apply VListBeginSame2; eauto.
      }

      1:{
        match goal with
        | h: inRM (?r, ?e) (m2RetM ?m' ?t ?s) |- _ =>
         destruct (L_m2RetM m' t s r e) as [d _]
         ; rmDirect
        end;
        breakAll; subst; try discriminate;
        specialize hi with (1:=H6);
        breakAll;
        inversion H4; subst.

        (* NOTE context is PndCal *)
        1:{
          (* SECTION 先把当前的dfx搞出来 *)
          specialize hi with (ea := PndCalE x2 x3 x4).
          rmDirect.
          breakAll.
          pose (DF_dfx) as a.
          specialize a with (1:=H10).
          breakAll.
          (* !SECTION *)


          (* SECTION  *)
          
          (* !SECTION *)
          pose (PForest1) as b.
          specialize b with (1:=H5) (2:=a) (Le:=endE x1).
          getH. apply b; eauto.
          resolveEndESelf. clear b.
          breakAll; try discriminate; repeat simplList; subst.
          rename t into b.
          rename x14 into t.

          destruct r.
          1:{
            getAnd; intros; try discriminate; inversion H14; subst.
            rmDirect.
            rmDirect.
            destruct t.
            1:{
              breakAll.

              (* SECTION 必然有一个以x结尾的v', 以ea为栈顶 *)
              pose (H x9) as d.
              destruct x9.
              inversion H11; subst; eauto; tac_inj.
              specialize d with (2:=H11) (r:=Some ea) (e:=Calv x).
              getH. apply d; eauto using nil_cons.
              1:{
                pose (DFX_w) as e.
                specialize e with (1:=a).
                breakAll; try discriminate; simplList; subst.
                rewrite H14.
                rewrite <- app_assoc.
                cmp_len3.
              }
              clear d.
              breakAll. clear H15.
              specialize H14 with (ea:=ea).
              rmDirect.
              breakAll.
              (* !SECTION *)

              (* SECTION 换头 *)
              assert (Df (x6 ++ [Calv x] ++ [Calv (PndCalE x2 x3 x4)]) 
                (PndCalE x2 x3 x4 :: ea :: x11) (s0 :: x9 ++ [Call x3])) as hh1.
              1:{
                pose (V_Pnd_Cal) as d.
                specialize d with (3:=H14).
                rewrite app_assoc.
                apply d; eauto.
                resolveRule.

                1:{
                  simpl in H7.
                  destruct x; subst;
                  tryResolveEnd.
                }
              }

              assert (Df (x6 ++ [Calv x] ++ [Calv (PndCalE x2 x3 x4)] ++ x8) 
                (PndCalE x2 x3 x4 :: ea :: x11) 
                (s0 :: x9 ++ [Call x3] ++ x10)) as hh2.
              1:{
                destruct x8.
                1:{
                  assert (x10=[]).
                  1:{
                    pose DFX_len_vw as d.
                    specialize d with (1:=a).
                    breakAll.
                    destruct x10; eauto.
                    simpl in d. discriminate.
                  }
                  subst.
                  do 2 rewrite app_nil_r.
                  eauto.
                }
                pose (DFX_df_sub) as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                specialize H16 with (1:=hh1) (Lv:=x4).
                repeat rewrite <- app_assoc in H16.
                rewrite <- app_comm_cons in H16.
                simpl in H16.
                repeat rewrite <- app_assoc in H16.
                simpl.
                apply H16; eauto.
                1:{
                  pose DFX_v as d.
                  specialize d with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H17 in H10.
                  pose VHasHead as e.
                  rmDirect.
                  specialize e with (1:=H20).
                  breakEx.
                  pose VConnect as d.
                  specialize d with (1:=H10) 
                    (v1:=x7 ++ [Calv (PndCalE x2 x3 x4)])
                    (v2:=v :: x8)
                    (Lv1:=x4)
                    (Lv2:=x12).
                  getH. apply d; eauto using app_cons_not_nil, nil_cons.
                  rewrite app_assoc; eauto.
                  tryResolveEnd.
                  subst.
                  eauto.
                }
                1:{
                  apply EndA1.
                  exists (x6 ++ [Calv x]).
                  do 2 eexists; rewrite <- app_assoc; simpl; eauto.
                }
              }

              match goal with
              | h:Df ?v (_::_::?T) _ |- _ =>
                exists v, T
              end.

              getAnd.
              pose (DFX_w) as d.
              specialize d with (1:=a).
              breakAll; try discriminate; simplList; subst.
              rewrite H16.
              apply V_Pnd_Ret with (t:=PndCalE x2 x3 x4); eauto.
              1:{
                pose DFX_v as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                (* H17看着办吧 *)
                destruct x8.
                simpl in H17.
                tac_inj; subst.
                rewrite app_nil_r.
                rewrite app_assoc.
                tryResolveEnd.
                assert (v::x8!=[]) as d by eauto using nil_cons.
                destruct (exists_last d) as [? [? e]].
                rewrite e in *.
                do 2 rewrite app_assoc in H17.
                tac_inj; subst.
                repeat rewrite app_assoc.
                apply VListEndSame2.
                resolveEndESelf.
              }
              
              1:{
                rewrite app_assoc.
                apply VListBeginSame2.
                apply VListBeginSame2.
                eauto.
              }
              (* !SECTION *)
            }

            1:{
              breakAll.

              (* SECTION 必然有一个以x结尾的v', 以ea为栈顶 *)
              pose (H x9) as d.
              destruct x9.
              inversion H11; subst; eauto; tac_inj.
              breakSingleton; try breakTuple; try discriminate.
              specialize d with (2:=H11) (r:=Some ea) (e:=Plnv x).
              getH. apply d; eauto using nil_cons.
              1:{
                pose (DFX_w) as e.
                specialize e with (1:=a).
                breakAll; try discriminate; simplList; subst.
                rewrite H14.
                rewrite <- app_assoc.
                cmp_len3.
              }
              clear d.
              breakAll. clear H15.
              specialize H14 with (ea:=ea).
              rmDirect.
              breakAll.
              (* !SECTION *)

              (* SECTION 换头 *)
              assert (Df (x6 ++ [Plnv x] ++ [Calv (PndCalE x2 x3 x4)]) 
                (PndCalE x2 x3 x4 :: ea :: x11) (s0 :: x9 ++ [Call x3])) as hh1.
              1:{
                pose (V_Pnd_Cal) as d.
                specialize d with (3:=H14).
                rewrite app_assoc.
                apply d; eauto.
                resolveRule.

                1:{
                  simpl in H7.
                  destruct x; subst;
                  tryResolveEnd.
                }
              }

              assert (Df (x6 ++ [Plnv x] ++ [Calv (PndCalE x2 x3 x4)] ++ x8) 
                (PndCalE x2 x3 x4 :: ea :: x11) 
                (s0 :: x9 ++ [Call x3] ++ x10)) as hh2.
              1:{
                destruct x8.
                1:{
                  assert (x10=[]).
                  1:{
                    pose DFX_len_vw as d.
                    specialize d with (1:=a).
                    breakAll.
                    destruct x10; eauto.
                    simpl in d. discriminate.
                  }
                  subst.
                  do 2 rewrite app_nil_r.
                  eauto.
                }
                pose (DFX_df_sub) as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                specialize H16 with (1:=hh1) (Lv:=x4).
                repeat rewrite <- app_assoc in H16.
                rewrite <- app_comm_cons in H16.
                simpl in H16.
                repeat rewrite <- app_assoc in H16.
                simpl.
                apply H16; eauto.
                1:{
                  pose DFX_v as d.
                  specialize d with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H17 in H10.
                  pose VHasHead as e.
                  rmDirect.
                  specialize e with (1:=H20).
                  breakEx.
                  pose VConnect as d.
                  specialize d with (1:=H10) 
                    (v1:=x7 ++ [Calv (PndCalE x2 x3 x4)])
                    (v2:=v :: x8)
                    (Lv1:=x4)
                    (Lv2:=x12).
                  getH. apply d; eauto using app_cons_not_nil, nil_cons.
                  rewrite app_assoc; eauto.
                  tryResolveEnd.
                  subst.
                  eauto.
                }
                1:{
                  apply EndA1.
                  exists (x6 ++ [Plnv x]).
                  do 2 eexists; rewrite <- app_assoc; simpl; eauto.
                }
              }

              match goal with
              | h:Df ?v (_::_::?T) _ |- _ =>
                exists v, T
              end.

              getAnd.
              pose (DFX_w) as d.
              specialize d with (1:=a).
              breakAll; try discriminate; simplList; subst.
              rewrite H16.
              apply V_Pnd_Ret with (t:=PndCalE x2 x3 x4); eauto.
              1:{
                pose DFX_v as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                (* H17看着办吧 *)
                destruct x8.
                simpl in H17.
                tac_inj; subst.
                rewrite app_nil_r.
                rewrite app_assoc.
                tryResolveEnd.
                assert (v::x8!=[]) as d by eauto using nil_cons.
                destruct (exists_last d) as [? [? e]].
                rewrite e in *.
                do 2 rewrite app_assoc in H17.
                tac_inj; subst.
                repeat rewrite app_assoc.
                apply VListEndSame2.
                resolveEndESelf.
              }
              
              1:{
                rewrite app_assoc.
                apply VListBeginSame2.
                apply VListBeginSame2.
                eauto.
              }
              (* !SECTION *)
            }

            1:{
              breakAll.

              (* SECTION 必然有一个以x结尾的v', 以ea为栈顶 *)
              pose (H x9) as d.
              destruct x9.
              inversion H11; subst; eauto; tac_inj.
              specialize d with (2:=H11) (r:=Some ea) (e:=Retv x).
              getH. apply d; eauto using nil_cons.
              1:{
                pose (DFX_w) as e.
                specialize e with (1:=a).
                breakAll; try discriminate; simplList; subst.
                rewrite H14.
                rewrite <- app_assoc.
                cmp_len3.
              }
              clear d.
              breakAll. clear H15.
              specialize H14 with (ea:=ea).
              rmDirect.
              breakAll.
              (* !SECTION *)

              (* SECTION 换头 *)
              assert (Df (x6 ++ [Retv x] ++ [Calv (PndCalE x2 x3 x4)]) 
                (PndCalE x2 x3 x4 :: ea :: x11) (s0 :: x9 ++ [Call x3])) as hh1.
              1:{
                pose (V_Pnd_Cal) as d.
                specialize d with (3:=H14).
                rewrite app_assoc.
                apply d; eauto.
                resolveRule.

                1:{
                  simpl in H7.
                  destruct x; subst;
                  tryResolveEnd.
                }
              }

              assert (Df (x6 ++ [Retv x] ++ [Calv (PndCalE x2 x3 x4)] ++ x8) 
                (PndCalE x2 x3 x4 :: ea :: x11) 
                (s0 :: x9 ++ [Call x3] ++ x10)) as hh2.
              1:{
                destruct x8.
                1:{
                  assert (x10=[]).
                  1:{
                    pose DFX_len_vw as d.
                    specialize d with (1:=a).
                    breakAll.
                    destruct x10; eauto.
                    simpl in d. discriminate.
                  }
                  subst.
                  do 2 rewrite app_nil_r.
                  eauto.
                }
                pose (DFX_df_sub) as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                specialize H16 with (1:=hh1) (Lv:=x4).
                repeat rewrite <- app_assoc in H16.
                rewrite <- app_comm_cons in H16.
                simpl in H16.
                repeat rewrite <- app_assoc in H16.
                simpl.
                apply H16; eauto.
                1:{
                  pose DFX_v as d.
                  specialize d with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H17 in H10.
                  pose VHasHead as e.
                  rmDirect.
                  specialize e with (1:=H20).
                  breakEx.
                  pose VConnect as d.
                  specialize d with (1:=H10) 
                    (v1:=x7 ++ [Calv (PndCalE x2 x3 x4)])
                    (v2:=v :: x8)
                    (Lv1:=x4)
                    (Lv2:=x12).
                  getH. apply d; eauto using app_cons_not_nil, nil_cons.
                  rewrite app_assoc; eauto.
                  tryResolveEnd.
                  subst.
                  eauto.
                }
                1:{
                  apply EndA1.
                  exists (x6 ++ [Retv x]).
                  do 2 eexists; rewrite <- app_assoc; simpl; eauto.
                }
              }

              match goal with
              | h:Df ?v (_::_::?T) _ |- _ =>
                exists v, T
              end.

              getAnd.
              pose (DFX_w) as d.
              specialize d with (1:=a).
              breakAll; try discriminate; simplList; subst.
              rewrite H16.
              apply V_Pnd_Ret with (t:=PndCalE x2 x3 x4); eauto.
              1:{
                pose DFX_v as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                (* H17看着办吧 *)
                destruct x8.
                simpl in H17.
                tac_inj; subst.
                rewrite app_nil_r.
                rewrite app_assoc.
                tryResolveEnd.
                assert (v::x8!=[]) as d by eauto using nil_cons.
                destruct (exists_last d) as [? [? e]].
                rewrite e in *.
                do 2 rewrite app_assoc in H17.
                tac_inj; subst.
                repeat rewrite app_assoc.
                apply VListEndSame2.
                resolveEndESelf.
              }
              
              1:{
                rewrite app_assoc.
                apply VListBeginSame2.
                apply VListBeginSame2.
                eauto.
              }
              (* !SECTION *)
            }

          }

          1:{
            getAnd; intros; try discriminate.
            rmDirect.
            rmDirect.

            destruct t; breakAll; subst.

            1:{
              assert (x12=[]).
              1:{
                destruct x9.
                1:{
                  inversion H11; tac_inj.
                }
  
                (* SECTION 这里H4要弄一个Df出来 *)
                pose (H (s0 :: x9)) as d.
                specialize d with (2:=H11) (r:=None) (e:=Calv x).
                getH. apply d; eauto using nil_cons.
                1:{
                  pose (DFX_w) as e.
                  specialize e with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H14.
                  rewrite <- app_assoc.
                  cmp_len3.
                }
                clear d.
                breakAll. clear H14.
                rmDirect.
                breakAll.
                (* !SECTION *)
  
                (* SECTION 再把a的sub Df弄出来 *)
                pose DFX_df_sub as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                destruct x7.
  
                pose DFX_len_vw as d.
                specialize d with (1:=a).
                breakAll.
                simpl in H17. discriminate.
                rmDirect.
  
                match goal with
                | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
                  pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
                  inversion _H
                end.
                destruct x13; eauto.
                simpl in *; discriminate.
                
                (* !SECTION *)
              }
              subst.
  
              (* NOTE 根绝H2这个情况应该是不可能的--好像又是可能的 *)
              match goal with
              | h:Df ?v ?T _ |- _ =>
              exists v
              end.
              getAnd; eauto.
              apply V_Pnd_Ret with (t:=PndCalE x2 x3 x4); eauto.
              apply VListEndSame2.
              resolveEndESelf.
              apply VListBeginSame2; eauto.
            }

            1:{
              assert (x12=[]).
              1:{
                destruct x9.
                1:{
                  inversion H11; tac_inj; subst.
                  destruct x12; eauto;
                  simpl in H12; easy.
                }
  
                (* SECTION 这里H4要弄一个Df出来 *)
                pose (H (s0 :: x9)) as d.
                specialize d with (2:=H11) (r:=None) (e:=Plnv x).
                getH. apply d; eauto using nil_cons.
                1:{
                  pose (DFX_w) as e.
                  specialize e with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H14.
                  rewrite <- app_assoc.
                  cmp_len3.
                }
                clear d.
                breakAll. clear H14.
                rmDirect.
                breakAll.
                (* !SECTION *)
  
                (* SECTION 再把a的sub Df弄出来 *)
                pose DFX_df_sub as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                destruct x7.
  
                pose DFX_len_vw as d.
                specialize d with (1:=a).
                breakAll.
                simpl in H17. discriminate.
                rmDirect.
  
                match goal with
                | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
                  pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
                  inversion _H
                end.
                destruct x13; eauto.
                simpl in *; discriminate.
                
                (* !SECTION *)
              }
              subst.
  
              (* NOTE 根绝H2这个情况应该是不可能的--好像又是可能的 *)
              match goal with
              | h:Df ?v ?T _ |- _ =>
              exists v
              end.
              getAnd; eauto.
              apply V_Pnd_Ret with (t:=PndCalE x2 x3 x4); eauto.
              apply VListEndSame2.
              resolveEndESelf.
              apply VListBeginSame2; eauto.
            }

            1:{
              assert (x12=[]).
              1:{
                destruct x9.
                1:{
                  inversion H11; tac_inj.
                }
  
                (* SECTION 这里H4要弄一个Df出来 *)
                pose (H (s0 :: x9)) as d.
                specialize d with (2:=H11) (r:=None) (e:=Retv x).
                getH. apply d; eauto using nil_cons.
                1:{
                  pose (DFX_w) as e.
                  specialize e with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H14.
                  rewrite <- app_assoc.
                  cmp_len3.
                }
                clear d.
                breakAll. clear H14.
                rmDirect.
                breakAll.
                (* !SECTION *)
  
                (* SECTION 再把a的sub Df弄出来 *)
                pose DFX_df_sub as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                destruct x7.
  
                pose DFX_len_vw as d.
                specialize d with (1:=a).
                breakAll.
                simpl in H17. discriminate.
                rmDirect.
  
                match goal with
                | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
                  pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
                  inversion _H
                end.
                destruct x13; eauto.
                simpl in *; discriminate.
                
                (* !SECTION *)
              }
              subst.
  
              (* NOTE 根绝H2这个情况应该是不可能的--好像又是可能的 *)
              match goal with
              | h:Df ?v ?T _ |- _ =>
              exists v
              end.
              getAnd; eauto.
              apply V_Pnd_Ret with (t:=PndCalE x2 x3 x4); eauto.
              apply VListEndSame2.
              resolveEndESelf.
              apply VListBeginSame2; eauto.
            }
          }
          
        }

        (* NOTE context is MatCal *)
        1:{
          (* SECTION 先把当前的dfx搞出来 *)
          specialize hi with (ea := MatCalE x3 x2 x4 t x5).
          rmDirect.
          breakAll.
          pose (DF_dfx) as a.
          specialize a with (1:=H10).
          breakAll.
          (* !SECTION *)


          (* SECTION  *)
          
          (* !SECTION *)
          pose (PForest1) as b.
          specialize b with (1:=H5) (2:=a) (Le:=endE x1).
          getH. apply b; eauto.
          resolveEndESelf. clear b.
          breakAll; try discriminate; repeat simplList; subst.
          rename t into b.
          rename x14 into t.

          destruct r.
          1:{
            getAnd; intros; try discriminate; inversion H14; subst.
            rmDirect.
            rmDirect.
            destruct t.
            1:{
              breakAll.

              (* SECTION 必然有一个以x结尾的v', 以ea为栈顶 *)
              pose (H x9) as d.
              destruct x9.
              inversion H11; subst; eauto; tac_inj.
              specialize d with (2:=H11) (r:=Some ea) (e:=Calv x).
              getH. apply d; eauto using nil_cons.
              1:{
                pose (DFX_w) as e.
                specialize e with (1:=a).
                breakAll; try discriminate; simplList; subst.
                rewrite H14.
                rewrite <- app_assoc.
                cmp_len3.
              }
              clear d.
              breakAll. clear H15.
              specialize H14 with (ea:=ea).
              rmDirect.
              breakAll.
              (* !SECTION *)

              (* SECTION 换头 *)
              assert (Df (x6 ++ [Calv x] ++ [Calv (MatCalE x3 x2 x4 b x5)]) 
                (MatCalE x3 x2 x4 b x5 :: ea :: x11) (s0 :: x9 ++ [Call x2])) as hh1.
              1:{
                pose (V_Cal) as d.
                specialize d with (3:=H14).
                rewrite app_assoc.
                apply d; eauto.
                resolveRule.
                1:{
                  simpl in H7.
                  destruct x; subst;
                  tryResolveEnd.
                }
              }

              assert (Df (x6 ++ [Calv x] ++ [Calv (MatCalE x3 x2 x4 b x5)] ++ x8) 
                (MatCalE x3 x2 x4 b x5 :: ea :: x11) 
                (s0 :: x9 ++ [Call x2] ++ x10)) as hh2.
              1:{
                destruct x8.
                1:{
                  assert (x10=[]).
                  1:{
                    pose DFX_len_vw as d.
                    specialize d with (1:=a).
                    breakAll.
                    destruct x10; eauto.
                    simpl in d. discriminate.
                  }
                  subst.
                  do 2 rewrite app_nil_r.
                  eauto.
                }
                pose (DFX_df_sub) as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                specialize H16 with (1:=hh1) (Lv:=x4).
                repeat rewrite <- app_assoc in H16.
                rewrite <- app_comm_cons in H16.
                simpl in H16.
                repeat rewrite <- app_assoc in H16.
                simpl.
                apply H16; eauto.
                1:{
                  pose DFX_v as d.
                  specialize d with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H17 in H10.
                  pose VHasHead as e.
                  rmDirect.
                  specialize e with (1:=H20).
                  breakEx.
                  pose VConnect as d.
                  specialize d with (1:=H10) 
                    (v1:=x7 ++ [Calv (MatCalE x3 x2 x4 b x5)])
                    (v2:=v :: x8)
                    (Lv1:=x4)
                    (Lv2:=x12).
                  getH. apply d; eauto using app_cons_not_nil, nil_cons.
                  rewrite app_assoc; eauto.
                  tryResolveEnd.
                  subst.
                  eauto.
                }
                1:{
                  apply EndA2.
                  exists (x6 ++ [Calv x]).
                  do 4 eexists; rewrite <- app_assoc; simpl; eauto.
                }
              }

              match goal with
              | h:Df ?v (_::_::?T) _ |- _ =>
                exists v, T
              end.

              getAnd.
              pose (DFX_w) as d.
              specialize d with (1:=a).
              breakAll; try discriminate; simplList; subst.
              rewrite H16.
              1:{
                pose DFX_v as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                (* H17看着办吧 *)
                destruct x8.
                simpl in H17.
                tac_inj; subst.
                rewrite app_nil_r.
                rewrite app_assoc.
                apply V_Ret with (L:=x4); eauto.
                tryResolveEnd.
                simpl in hh2; eauto.
                repeat rewrite <- app_assoc.
                simpl; eauto.

                assert (v::x8!=[]) as d by eauto using nil_cons.
                destruct (exists_last d) as [? [? e]].
                rewrite e in *.
                do 2 rewrite app_assoc in H17.
                tac_inj; subst.
                apply V_Ret with (L:=endE x14); eauto.

                repeat rewrite app_assoc.
                apply VListEndSame2.
                resolveEndESelf.
              }
              
              1:{
                rewrite app_assoc.
                apply VListBeginSame2.
                apply VListBeginSame2.
                eauto.
              }
              (* !SECTION *)
            }

            1:{
              breakAll.

              (* SECTION 必然有一个以x结尾的v', 以ea为栈顶 *)
              pose (H x9) as d.
              destruct x9.
              inversion H11; subst; eauto; tac_inj.
              1:{
                breakSingleton.
                discriminate.
              }
              specialize d with (2:=H11) (r:=Some ea) (e:=Plnv x).
              getH. apply d; eauto using nil_cons.
              1:{
                pose (DFX_w) as e.
                specialize e with (1:=a).
                breakAll; try discriminate; simplList; subst.
                rewrite H14.
                rewrite <- app_assoc.
                cmp_len3.
              }
              clear d.
              breakAll. clear H15.
              specialize H14 with (ea:=ea).
              rmDirect.
              breakAll.
              (* !SECTION *)

              (* SECTION 换头 *)
              assert (Df (x6 ++ [Plnv x] ++ [Calv (MatCalE x3 x2 x4 b x5)]) 
                (MatCalE x3 x2 x4 b x5 :: ea :: x11) (s0 :: x9 ++ [Call x2])) as hh1.
              1:{
                pose (V_Cal) as d.
                specialize d with (3:=H14).
                rewrite app_assoc.
                apply d; eauto.
                resolveRule.
                1:{
                  simpl in H7.
                  destruct x; subst;
                  tryResolveEnd.
                }
              }

              assert (Df (x6 ++ [Plnv x] ++ [Calv (MatCalE x3 x2 x4 b x5)] ++ x8) 
                (MatCalE x3 x2 x4 b x5 :: ea :: x11) 
                (s0 :: x9 ++ [Call x2] ++ x10)) as hh2.
              1:{
                destruct x8.
                1:{
                  assert (x10=[]).
                  1:{
                    pose DFX_len_vw as d.
                    specialize d with (1:=a).
                    breakAll.
                    destruct x10; eauto.
                    simpl in d. discriminate.
                  }
                  subst.
                  do 2 rewrite app_nil_r.
                  eauto.
                }
                pose (DFX_df_sub) as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                specialize H16 with (1:=hh1) (Lv:=x4).
                repeat rewrite <- app_assoc in H16.
                rewrite <- app_comm_cons in H16.
                simpl in H16.
                repeat rewrite <- app_assoc in H16.
                simpl.
                apply H16; eauto.
                1:{
                  pose DFX_v as d.
                  specialize d with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H17 in H10.
                  pose VHasHead as e.
                  rmDirect.
                  specialize e with (1:=H20).
                  breakEx.
                  pose VConnect as d.
                  specialize d with (1:=H10) 
                    (v1:=x7 ++ [Calv (MatCalE x3 x2 x4 b x5)])
                    (v2:=v :: x8)
                    (Lv1:=x4)
                    (Lv2:=x12).
                  getH. apply d; eauto using app_cons_not_nil, nil_cons.
                  rewrite app_assoc; eauto.
                  tryResolveEnd.
                  subst.
                  eauto.
                }
                1:{
                  apply EndA2.
                  exists (x6 ++ [Plnv x]).
                  do 4 eexists; rewrite <- app_assoc; simpl; eauto.
                }
              }

              match goal with
              | h:Df ?v (_::_::?T) _ |- _ =>
                exists v, T
              end.

              getAnd.
              pose (DFX_w) as d.
              specialize d with (1:=a).
              breakAll; try discriminate; simplList; subst.
              rewrite H16.
              1:{
                pose DFX_v as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                (* H17看着办吧 *)
                destruct x8.
                simpl in H17.
                tac_inj; subst.
                rewrite app_nil_r.
                rewrite app_assoc.
                apply V_Ret with (L:=x4); eauto.
                tryResolveEnd.
                simpl in hh2; eauto.
                repeat rewrite <- app_assoc.
                simpl; eauto.

                assert (v::x8!=[]) as d by eauto using nil_cons.
                destruct (exists_last d) as [? [? e]].
                rewrite e in *.
                do 2 rewrite app_assoc in H17.
                tac_inj; subst.
                apply V_Ret with (L:=endE x14); eauto.

                repeat rewrite app_assoc.
                apply VListEndSame2.
                resolveEndESelf.
              }
              
              1:{
                rewrite app_assoc.
                apply VListBeginSame2.
                apply VListBeginSame2.
                eauto.
              }
              (* !SECTION *)
            }

            1:{
              breakAll.

              (* SECTION 必然有一个以x结尾的v', 以ea为栈顶 *)
              pose (H x9) as d.
              destruct x9.
              inversion H11; subst; eauto; tac_inj.
              specialize d with (2:=H11) (r:=Some ea) (e:=Retv x).
              getH. apply d; eauto using nil_cons.
              1:{
                pose (DFX_w) as e.
                specialize e with (1:=a).
                breakAll; try discriminate; simplList; subst.
                rewrite H14.
                rewrite <- app_assoc.
                cmp_len3.
              }
              clear d.
              breakAll. clear H15.
              specialize H14 with (ea:=ea).
              rmDirect.
              breakAll.
              (* !SECTION *)

              (* SECTION 换头 *)
              assert (Df (x6 ++ [Retv x] ++ [Calv (MatCalE x3 x2 x4 b x5)]) 
                (MatCalE x3 x2 x4 b x5 :: ea :: x11) (s0 :: x9 ++ [Call x2])) as hh1.
              1:{
                pose (V_Cal) as d.
                specialize d with (3:=H14).
                rewrite app_assoc.
                apply d; eauto.
                resolveRule.
                1:{
                  simpl in H7.
                  destruct x; subst;
                  tryResolveEnd.
                }
              }

              assert (Df (x6 ++ [Retv x] ++ [Calv (MatCalE x3 x2 x4 b x5)] ++ x8) 
                (MatCalE x3 x2 x4 b x5 :: ea :: x11) 
                (s0 :: x9 ++ [Call x2] ++ x10)) as hh2.
              1:{
                destruct x8.
                1:{
                  assert (x10=[]).
                  1:{
                    pose DFX_len_vw as d.
                    specialize d with (1:=a).
                    breakAll.
                    destruct x10; eauto.
                    simpl in d. discriminate.
                  }
                  subst.
                  do 2 rewrite app_nil_r.
                  eauto.
                }
                pose (DFX_df_sub) as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                specialize H16 with (1:=hh1) (Lv:=x4).
                repeat rewrite <- app_assoc in H16.
                rewrite <- app_comm_cons in H16.
                simpl in H16.
                repeat rewrite <- app_assoc in H16.
                simpl.
                apply H16; eauto.
                1:{
                  pose DFX_v as d.
                  specialize d with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H17 in H10.
                  pose VHasHead as e.
                  rmDirect.
                  specialize e with (1:=H20).
                  breakEx.
                  pose VConnect as d.
                  specialize d with (1:=H10) 
                    (v1:=x7 ++ [Calv (MatCalE x3 x2 x4 b x5)])
                    (v2:=v :: x8)
                    (Lv1:=x4)
                    (Lv2:=x12).
                  getH. apply d; eauto using app_cons_not_nil, nil_cons.
                  rewrite app_assoc; eauto.
                  tryResolveEnd.
                  subst.
                  eauto.
                }
                1:{
                  apply EndA2.
                  exists (x6 ++ [Retv x]).
                  do 4 eexists; rewrite <- app_assoc; simpl; eauto.
                }
              }

              match goal with
              | h:Df ?v (_::_::?T) _ |- _ =>
                exists v, T
              end.

              getAnd.
              pose (DFX_w) as d.
              specialize d with (1:=a).
              breakAll; try discriminate; simplList; subst.
              rewrite H16.
              1:{
                pose DFX_v as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                (* H17看着办吧 *)
                destruct x8.
                simpl in H17.
                tac_inj; subst.
                rewrite app_nil_r.
                rewrite app_assoc.
                apply V_Ret with (L:=x4); eauto.
                tryResolveEnd.
                simpl in hh2; eauto.
                repeat rewrite <- app_assoc.
                simpl; eauto.

                assert (v::x8!=[]) as d by eauto using nil_cons.
                destruct (exists_last d) as [? [? e]].
                rewrite e in *.
                do 2 rewrite app_assoc in H17.
                tac_inj; subst.
                apply V_Ret with (L:=endE x14); eauto.

                repeat rewrite app_assoc.
                apply VListEndSame2.
                resolveEndESelf.
              }
              
              1:{
                rewrite app_assoc.
                apply VListBeginSame2.
                apply VListBeginSame2.
                eauto.
              }
              (* !SECTION *)
            }
          }

          1:{
            getAnd; intros; try discriminate.
            rmDirect.
            rmDirect.

            destruct t; breakAll; subst.

            1:{
              assert (x12=[]).
              1:{
                destruct x9.
                1:{
                  inversion H11; tac_inj.
                }
  
                (* SECTION 这里H4要弄一个Df出来 *)
                pose (H (s0 :: x9)) as d.
                specialize d with (2:=H11) (r:=None) (e:=Calv x).
                getH. apply d; eauto using nil_cons.
                1:{
                  pose (DFX_w) as e.
                  specialize e with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H14.
                  rewrite <- app_assoc.
                  cmp_len3.
                }
                clear d.
                breakAll. clear H14.
                rmDirect.
                breakAll.
                (* !SECTION *)
  
                (* SECTION 再把a的sub Df弄出来 *)
                pose DFX_df_sub as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                destruct x7.
  
                pose DFX_len_vw as d.
                specialize d with (1:=a).
                breakAll.
                simpl in H17. discriminate.
                rmDirect.
  
                match goal with
                | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
                  pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
                  inversion _H
                end.
                destruct x13; eauto.
                simpl in *; discriminate.
                
                (* !SECTION *)
              }
              subst.
  
              (* NOTE 根绝H2这个情况应该是不可能的--好像又是可能的 *)
              match goal with
              | h:Df ?v ?T _ |- _ =>
              exists v
              end.
              getAnd; eauto.
              apply V_Ret with (L:=endE x1); eauto.
              apply VListEndSame2.
              resolveEndESelf.
              apply VListBeginSame2; eauto.
            }

            1:{
              assert (x12=[]).
              1:{
                destruct x9.
                1:{
                  inversion H11; tac_inj; subst.
                  destruct x12; eauto.
                  simpl in H12; easy.
                }
  
                (* SECTION 这里H4要弄一个Df出来 *)
                pose (H (s0 :: x9)) as d.
                specialize d with (2:=H11) (r:=None) (e:=Plnv x).
                getH. apply d; eauto using nil_cons.
                1:{
                  pose (DFX_w) as e.
                  specialize e with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H14.
                  rewrite <- app_assoc.
                  cmp_len3.
                }
                clear d.
                breakAll. clear H14.
                rmDirect.
                breakAll.
                (* !SECTION *)
  
                (* SECTION 再把a的sub Df弄出来 *)
                pose DFX_df_sub as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                destruct x7.
  
                pose DFX_len_vw as d.
                specialize d with (1:=a).
                breakAll.
                simpl in H17. discriminate.
                rmDirect.
  
                match goal with
                | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
                  pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
                  inversion _H
                end.
                destruct x13; eauto.
                simpl in *; discriminate.
                
                (* !SECTION *)
              }
              subst.
  
              (* NOTE 根绝H2这个情况应该是不可能的--好像又是可能的 *)
              match goal with
              | h:Df ?v ?T _ |- _ =>
              exists v
              end.
              getAnd; eauto.
              apply V_Ret with (L:=endE x1); eauto.
              apply VListEndSame2.
              resolveEndESelf.
              apply VListBeginSame2; eauto.
            }

            1:{
              assert (x12=[]).
              1:{
                destruct x9.
                1:{
                  inversion H11; tac_inj.
                }
  
                (* SECTION 这里H4要弄一个Df出来 *)
                pose (H (s0 :: x9)) as d.
                specialize d with (2:=H11) (r:=None) (e:=Retv x).
                getH. apply d; eauto using nil_cons.
                1:{
                  pose (DFX_w) as e.
                  specialize e with (1:=a).
                  breakAll; try discriminate; simplList; subst.
                  rewrite H14.
                  rewrite <- app_assoc.
                  cmp_len3.
                }
                clear d.
                breakAll. clear H14.
                rmDirect.
                breakAll.
                (* !SECTION *)
  
                (* SECTION 再把a的sub Df弄出来 *)
                pose DFX_df_sub as d.
                specialize d with (1:=a).
                breakAll; try discriminate; simplList; subst.
                destruct x7.
  
                pose DFX_len_vw as d.
                specialize d with (1:=a).
                breakAll.
                simpl in H17. discriminate.
                rmDirect.
  
                match goal with
                | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
                  pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
                  inversion _H
                end.
                destruct x13; eauto.
                simpl in *; discriminate.
                
                (* !SECTION *)
              }
              subst.
  
              (* NOTE 根绝H2这个情况应该是不可能的--好像又是可能的 *)
              match goal with
              | h:Df ?v ?T _ |- _ =>
              exists v
              end.
              getAnd; eauto.
              apply V_Ret with (L:=endE x1); eauto.
              apply VListEndSame2.
              resolveEndESelf.
              apply VListBeginSame2; eauto.
            }
          }
        }
      }
    }
  Qed.
  (* end hide *)

End Parser.