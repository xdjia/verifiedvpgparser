(** This file provides the end-to-end extraction function [extract] and
    verifies that, during extraction, [extract] maintains a list [V]
    that contains no duplicates, and the size of [V] does not decrease
    at each step, where [V] is a list of extracted partial parse tree.
  *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties 
  MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

Require Import Coq.Program.Equality.
Require Import Coq.Init.Wf.

Require Import Lia.

Require Import Misc.
Require Import ForwardSmallStep.
Require Import BackwardSmallStep.

Require Import Coq.Unicode.Utf8_core.

Require Import Def.
Import Def.DEF.
Require Import Misc.

Import Misc.Basic.
Import Misc.vpg.

Require Import Arith.PeanoNat.

Import Misc.Basic.
Import Misc.vpg.

Require Import Program.
Require Import Monad.
Require Import Lia.

Require Import Transducer.
Require Import PreTimed.

(** The module [ExtractionWNoDup] provides the extraction function that
    maintains a list of partial parse trees during the extraction. The
    list is verified to have no duplicates, therefore can be viewed as a set. *)
Module ExtractionWNoDup (G:VPG).
  Module Transducer := Transducer(G).

  Import Transducer.
  Import TimedSets.Parser.
  Import PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.
  Import Def.
  Import Tac.Tacs.

  Import TimedSets.Parser.

  (** [extraction]: the extraction function working on the whole pares
      forest; extended from the one-step extraction functin [f_b].*)
  Fixpoint extraction M V :=
    match M with
    | [] => V
    | m::M' =>
      match M' with
      | [] => V
      | _ =>
        let V' := Transducer2.f_b m V in
        let out := extraction M' V' in
        out
      end
    end.

  (** [extraction_and_its_one_step]: the relation between
      [extraction] and [f_b].*)
  Lemma extraction_and_its_one_step: 
    ∀ x M V m,
    Transducer2.f_b x (extraction (M ++ [x]) V) =
    extraction ((M ++ [x]) ++ [m]) V.
  (* begin hide *)
  Proof.
    intros.
    generalize dependent V.
    induction M; intros.
    simpl; eauto.

    replace ((a :: M) ++ [x]) with (a :: (M ++ [x])); eauto using app_comm_cons.
    replace ((a :: M ++ [x]) ++ [m]) with (a :: (M ++ [x]) ++ [m]); eauto using app_comm_cons.
    unfold extraction at 1.

    assert (exists e y, e::y=M++[x]).
    1:{
      destruct M; simpl; eauto.
    }

    destruct H as [? [? ?]].
    rewrite <- H at 1.
    fold extraction.

    unfold extraction.
    fold extraction.

    assert (exists e y, e::y=(M ++ [x]) ++ [m]).
    1:{
      destruct M; simpl; eauto.
    }

    destruct H0 as [? [? ?]].
    rewrite <- H0.
    rewrite H0.
    eauto.
  Qed.
  (* end hide *)

  (** [L_forest_length]: the length of the forest is the length of the
      string plus one. *)
  Lemma L_forest_length: ∀ M T w, Forest M T w -> |M| = |w| + 1.
  (* begin hide *)
  Proof.
    intros.
    induction H.
    simpl; eauto.
    simpl in *; eauto.
    rewrite app_length.
    simpl. lia.
  Qed.
  (* end hide *)

  (** [L_extract_extract]: the partial parse trees and the forest during
      the extraction satisfy the relation [Extract]. *)
  Lemma L_extract_extract: ∀ m M T w i,
    Forest (m::M) T (w++[i]) -> 
    ∀ M1 m' M2, 
      M = ((M1++[m'])++M2) ->
      ∃ w1 w2, 
        Transducer2.Extract 
          (m'::M2) 
          (extraction (app M1 [m']) (Transducer2.f_init m)) 
          w1 w2
        /\ w1++w2=w++[i] 
        /\ |M2| = |w1|.
  (* begin hide *)
  Proof.
    intros.

    generalize dependent m'.
    generalize dependent M2.

    induction M1 using rev_ind.

    1:{
      intros.
  
      exists w, ([i]).
      subst.
      split; eauto.
      apply Transducer2.EInit with (T:=T);
      eauto.
      split; eauto.
      pose (L_forest_length _ _ _ H).
      simpl in *.
      rewrite app_length in e.
      simpl in *.
      
      lia.
    }

    intros.

    rewrite <- app_assoc in H0.
    destruct (IHM1 _ _ H0) as [w1 [w2 ?]].
    repeat breakAnd.


    destruct w1.
    1:{
      simpl in H1. easy.
    }

    assert (s :: w1 != []) as notnil.
    eauto using nil_cons.

    destruct (exists_last notnil).
    destruct s0.
    rewrite e in *.
      
    pose (Transducer2.EInte _ _ _ _ _ _ H2).

    exists x0, (x1::w2).
    simpl in e0.
    getAnd; eauto.

    match goal with
    | h: Transducer2.Extract _ ?x _ _ |- Transducer2.Extract _ ?y _ _ =>
     replace y with x; auto
    end.

    apply extraction_and_its_one_step.

    getAnd; eauto.
    rewrite <- H3.
    rewrite <- app_assoc. eauto.
    repeat rewrite app_length in H1.
    simpl in *.
    lia.
  Qed.
  (* end hide *)

  (* begin hide *)
  Lemma nodup_app: ∀ A (l1:list A) l2, NoDup l1 -> NoDup l2 ->
    (∀ x, In x l1 -> ~ (In x l2)) -> NoDup (l1 ++ l2).
  Proof.
    intros.
    induction l1.
    simpl; eauto.

    simpl.
    constructor.
    1:{
      unfold not; intro.
      pose (in_app_or _ _ _ H2).
      breakOr.
      inversion H. eauto.
      assert (¬ In a l2).
      apply H1.
      constructor; eauto. contradiction.
    }

    apply IHl1. inversion H; eauto.
    intros.
    apply H1.
    
    constructor 2.
    eauto.
  Qed.
  (* end hide *)

  (** [no_dup_init]: the initial list of partial parse trees generated
      by [f_init] has no duplicates. *)
  Lemma no_dup_init:
    ∀ m M T w i,
    Forest (m::M) T (w++[i]) -> 
    NoDup (Transducer2.f_init m).
  (* begin hide *)
  Proof.
    intros.
    unfold Transducer2.f_init.
    destruct m.

    match goal with
    | |- NoDup (map ?f (nodup ?inlist ?l)) =>
    pose (NoDup_nodup _ l inlist Transducer2.L_ea_inlist) as h
    ; set (a:=nodup inlist l)
    ; fold a in h
    ; assert (∀ y, NoDup y -> NoDup (map f y)) as p
    end.
    1:{
      intros.
      induction y.
      simpl. constructor 1.
      inversion H0; subst. rmDirect.
      simpl. constructor 2; auto.
      unfold not; intros.
      Transducer2.apply_in_map.
      breakTuple.
      simplList.
      subst.
      easy.
    }
    apply p; auto.

    match goal with
    | |- NoDup (map ?f (nodup ?inlist ?l)) =>
    pose (NoDup_nodup _ l inlist Transducer2.L_ec_inlist) as h
    ; set (a:=nodup inlist l)
    ; fold a in h
    ; assert (∀ y, NoDup y -> NoDup (map f y)) as p
    end.
    1:{
      intros.
      induction y.
      simpl. constructor 1.
      inversion H0; subst. rmDirect.
      simpl. constructor 2; auto.
      unfold not; intros.
      Transducer2.apply_in_map.
      breakTuple.
      simplList.
      subst.
      easy.
    }
    apply p; auto.

    match goal with
    | |- NoDup (map ?f (nodup ?inlist ?l)) =>
    pose (NoDup_nodup _ l inlist Transducer2.L_eb_inlist) as h
    ; set (a:=nodup inlist l)
    ; fold a in h
    ; assert (∀ y, NoDup y -> NoDup (map f y)) as p
    end.
    1:{
      intros.
      induction y.
      simpl. constructor 1.
      inversion H0; subst. rmDirect.
      simpl. constructor 2; auto.
      unfold not; intros.
      Transducer2.apply_in_map.
      breakTuple.
      simplList.
      subst.
      easy.
    }
    apply p; auto.
  Qed.
  (* end hide *)

  (** [f_init_same_t]: in the initial list of partial parse trees
      generated by [f_init], each rule has a unique stack. *)
  Lemma f_init_same_t:  
    ∀ m e t1 t2, 
      In (e,t1) (Transducer2.f_init m) -> 
      In (e,t2) (Transducer2.f_init m) -> t1=t2.
  (* begin hide *)
  Proof.
    intros.
    unfold Transducer2.f_init in H.
    unfold Transducer2.f_init in H0.
    destruct m.

    all: do 2 (Transducer2.apply_in_map;
    Transducer2.apply_nodup_in;
    Transducer2.apply_filter_map).


    all: repeat match goal with
    | h: (match ?x with _ => _ end) = _ |- _ =>
      destruct x
    end;
    do 2 (breakTuple; subst; try rmDirect); auto.

    all: match goal with
    | h:[_]=[_] |- _ =>
    inversion h; auto
    end.

  Qed.
  (* end hide *)

  (* begin hide *)
  Lemma filter_map_split: ∀ {A} {B} f (g:A->B) a l, filter_map (a::l) f g  = 
    (filter_map [a] f g) ++ (filter_map l f g).
  Proof.
    intros.
    unfold filter_map.
    unfold filter.
    destruct_with_eqn (f a).
    rewrite map_cons. eauto.
    simpl; eauto.
  Qed.
  (* end hide *)

  (** [L_f_b_nodup_nodup_sub_tlt, L_f_b_nodup_nodup_sub_t,
      L_f_b_nodup_nodup_sub_et]: these three lemmas show that when the
      list of parse trees contain no duplicates, extending the parse
      trees does not introduce duplicates. *)
  Lemma L_f_b_nodup_nodup_sub_tlt: 
  ∀ {A} l (t:A) m, 
    NoDup m ->
    NoDup (map (λ e : CalEdge, (Calv e :: l, t)) m).
  (* begin hide *)
  Proof.
    intros.
    induction m. constructor.
    inversion H; subst.
    rmDirect.
    constructor 2; try easy.
    unfold not; intro.

    destruct (in_map_iff 
      (fun a => (Calv a :: l, t)) m (Calv a :: l, t)) as [h _].
    unfold map in h.
    rmDirect.
    breakAll.
    breakTuple; subst.
    simplList; subst.
    repeat rmDirect.
    contradiction.
  Qed.
  (* end hide *)

  Lemma L_f_b_nodup_nodup_sub_t: 
  ∀ {A} l (t:A) m, NoDup m ->
    NoDup (map (λ e : PlnEdge, (Plnv e :: l, t)) m).
  (* begin hide *)
  Proof.
    intros.
    induction m. constructor.
    inversion H; subst.
    rmDirect.
    constructor 2; try easy.
    unfold not; intro.

    destruct (in_map_iff 
      (fun a => (Plnv a :: l, t)) m (Plnv a :: l, t)) as [h _].
    unfold map in h.
    rmDirect.
    breakAll.
    breakTuple; subst.
    simplList; subst.
    repeat rmDirect.
    contradiction.
  Qed.
  (* end hide *)

  Lemma L_f_b_nodup_nodup_sub_et: 
  ∀ l t m, NoDup m ->
    NoDup (map (λ e : RetEdge, (Retv e :: l, e::t)) m).
  (* begin hide *)
  Proof.
    intros.
    induction m. constructor.
    inversion H; subst.
    rmDirect.
    constructor 2; try easy.
    unfold not; intro.

    destruct (in_map_iff 
      (fun a => (Retv a :: l, a::t)) m (Retv a :: l, a::t)) as [h _].
    unfold map in h.
    rmDirect.
    breakAll.
    breakTuple; subst.
    simplList; subst.
    repeat rmDirect.
    contradiction.
  Qed.
  (* end hide *)


  (* begin hide *)
  Lemma L_f_b_nodup_nodup_compose: ∀ m V x, 
    In x (Transducer2.f_b m V) ->
    match m with
    | PlnCME m => ∃ e v t, In (v, t) V /\ x = (e::v, t)
    | CalCME m => ∃ e v t, In (v, t) V /\ x = (e::v, tl t)
    | RetCME m => ∃ e v t, In (v, t) V /\ x = (Retv e::v, e::t)
    end.
  Proof.
    Import Transducer2.
    intros.
    destruct m.
    1:{
      unfold Transducer2.f_b in H.
      apply_concat.
      apply_in_map.
      destruct x1.
      subst.
      apply_in_map.
      apply_nodup_in.
      apply_filter_map.
      destruct x1.
      destruct o.
      destruct c0.
      destruct l0.
      destruct l.
      all: try easy; eauto.
    }
    1:{
      unfold f_b in H.
      apply_concat.
      apply_in_map.
      destruct x1.
      subst.
      apply_in_map.
      apply_nodup_in.
      apply_filter_map.
      destruct x1.
      destruct o.
      destruct c.
      destruct l0.
      destruct l.
      all: try easy; eauto.
    }
    1:{
      unfold f_b in H.
      apply_concat.
      apply_in_map.
      destruct x1.
      subst.
      apply_in_map.
      apply_nodup_in.
      apply_filter_map.
      destruct x1.
      destruct o.
      destruct c.
      destruct l0.
      destruct l.
      all: try easy; eauto.
    }
  Qed.
  (* end hide *)

  (** [L_f_b_nodup_nodup]: if the list [V] of partial parse trees
      contains no duplicates, then [V'=f_b m V] also contains no
      duplicates. *)
  Lemma L_f_b_nodup_nodup: ∀ m V, 
    (∀ v t1 t2, In (v,t1) V -> In (v,t2) V -> t1=t2) ->
    (NoDup V) ->
    NoDup (f_b m V).
  (* begin hide *)
  Proof.
    intros.
    unfold f_b.
    destruct m.

    1:{
      (* set (m:=(va_set.elements ma)). *)
      (* assert (NoDup m) by admit. *)
      induction V.
      simpl. constructor.

      inversion H0; subst.

      rewrite map_cons.
      rewrite concat_cons.
      apply nodup_app.

      2:{
        apply IHV.
        intros.
        apply (H v t1 t2); constructor 2; eauto.
        inversion H0; eauto.
      }

      1:{
        clear IHV.
        set (m:=va_set.elements ma).

        destruct a.
        induction m.
        1:{
          unfold filter_map.
          simpl. eauto. constructor.
        }
        apply L_f_b_nodup_nodup_sub_tlt.
        apply NoDup_nodup.
        apply L_ea_inlist.
      }

      clear IHV.
      destruct a.

      intros.
      assert (∃ e, x = (Calv e :: l, tl l0)).
      1:{
        apply_in_map.
        apply_nodup_in.

        apply_filter_map.
        destruct x1.
        destruct o.
        destruct c0.
        destruct l0.
        destruct l.
        all: try easy; eauto.
      }

      clear H1.
      breakAll.

      unfold not; intro.

      pose (L_f_b_nodup_nodup_compose (CalCME ma) V x) as h.
      unfold f_b in h.
      rmDirect.
      breakAll.
      clear H1.
      subst.
      breakTuple; subst. clear H5.
      simplList; subst.
      match goal with
      | h:~ In (?x,?y) V, h1: In (?x,?z) V |- _ =>
       assert (y=z);
       [apply H with x|]
      end.
      (try constructor; eauto). constructor 2; eauto.
      subst. contradiction.
    }

    1:{
      (* set (m:=(va_set.elements ma)). *)
      (* assert (NoDup m) by admit. *)
      induction V.
      simpl. constructor.

      inversion H0; subst.

      rewrite map_cons.
      rewrite concat_cons.
      apply nodup_app.

      2:{
        apply IHV.
        intros.
        apply (H v t1 t2); constructor 2; eauto.
        inversion H0; eauto.
      }

      1:{
        clear IHV.
        set (m:=vc_set.elements mc).


        destruct a.
        induction m.
        1:{
          unfold filter_map.
          simpl. eauto. constructor.
        }
        apply L_f_b_nodup_nodup_sub_t.
        apply NoDup_nodup.
        apply L_ec_inlist.
      }

      clear IHV.
      destruct a.

      intros.
      assert (∃ e, x = (Plnv e :: l, l0)).
      1:{
        apply_in_map.
        apply_nodup_in.

        apply_filter_map.
        destruct x1.
        destruct o.
        destruct c.
        destruct l0.
        destruct l.
        all: try easy; eauto.
      }

      clear H1.
      breakAll.

      unfold not; intro.

      pose (L_f_b_nodup_nodup_compose (PlnCME mc) V x) as h.
      unfold f_b in h.
      rmDirect.
      breakAll.
      clear H1.
      subst.
      breakTuple; subst. clear H5.
      simplList; subst.
      match goal with
      | h:~ In (?x,?y) V, h1: In (?x,?z) V |- _ =>
       assert (y=z);
       [apply H with x|]
      end.
      (try constructor; eauto). constructor 2; eauto.
      subst. contradiction.
    }

    1:{
      (* set (m:=(va_set.elements ma)). *)
      (* assert (NoDup m) by admit. *)
      induction V.
      simpl. constructor.

      inversion H0; subst.

      rewrite map_cons.
      rewrite concat_cons.
      apply nodup_app.

      2:{
        apply IHV.
        intros.
        apply (H v t1 t2); constructor 2; eauto.
        inversion H0; eauto.
      }

      1:{
        clear IHV.
        set (m:=vb_set.elements mb).


        destruct a.
        induction m.
        1:{
          unfold filter_map.
          simpl. eauto. constructor.
        }
        apply L_f_b_nodup_nodup_sub_et.
        apply NoDup_nodup.
        apply L_eb_inlist.
      }

      clear IHV.
      destruct a.

      intros.
      assert (∃ e, x = (Retv e :: l, e::l0)).
      1:{
        apply_in_map.
        apply_nodup_in.

        apply_filter_map.
        destruct x1.
        destruct o.
        destruct c.
        destruct l0.
        destruct l.
        all: try easy; eauto.
      }

      clear H1.
      breakAll.

      unfold not; intro.

      pose (L_f_b_nodup_nodup_compose (RetCME mb) V x) as h.
      unfold f_b in h.
      rmDirect.
      breakAll.
      clear H1.
      subst.
      breakTuple; subst. clear H5.
      simplList; subst.
      simplList; subst.
      match goal with
      | h:~ In (?x,?y) V, h1: In (?x,?z) V |- _ =>
       assert (y=z);
       [apply H with x|]
      end.
      (try constructor; eauto). constructor 2; eauto.
      subst. contradiction.
    }
  Qed.
  (* end hide *)

  (** [extraction_nodup_nodup]: during the extraction, the list [V] of
      partial parse trees contains no duplicates. *)
  Lemma extraction_nodup_nodup:
    ∀ m M T w i,
      Forest (m::M) T (w++[i]) ->
    ∀ M1 m' M2,
      M = ((M1++[m'])++M2) ->
      NoDup (extraction M1 (f_init m)) /\ 
      ∀ e t1 t2, In (e,t1) (extraction M1 (f_init m)) -> 
        In (e,t2) (extraction M1 (f_init m)) -> t1=t2.
  (* begin hide *)
  Proof.
    intros.
    generalize dependent M2.
    generalize dependent m'.
    induction M1 using rev_ind; intros. simpl.
    split. apply no_dup_init with (1:=H).
    intros. apply f_init_same_t with (1:=H1); auto.

    pose (extraction_and_its_one_step ) as hw.
    destruct M1. simpl.
    split. apply no_dup_init with (1:=H).
    intros. apply f_init_same_t with (1:=H1); auto.

    split.
    assert (∃ x M', m1 :: M1 = (M' ++ [x])).
    1:{
      assert ( m1 :: M1 != []) as notnil.
      eauto using nil_cons.
      destruct (exists_last notnil).
      destruct s.
      rewrite e in *.
      clear notnil e.

      eauto.
    }
    repeat breakEx.
    rewrite H1.
    rewrite <- hw.

    apply L_f_b_nodup_nodup.

    intros.
    rewrite <- app_assoc in H0.
    pose (IHM1 x ([m']++M2) H0).
    breakAll.
    rewrite <- H1 in *.
    apply a with v; auto.

    rewrite <- H1.
    apply (IHM1 x ([m']++M2)).
    rewrite app_assoc.
    eauto.

    intros.


    pose (L_extract_extract) as h.
    rewrite <- app_assoc in H0.
    specialize h with (1:=H) (M1:=m1::M1) (m':=x) (M2:=[m']++M2) (2:=H0).

    breakAll.

    pose (L_extract) as _h.
    specialize _h with (1:=H3).
    match goal with
    | h:In (?v,?T) (extraction _ _) |- _ =>
     destruct (_h v T) as [? _];
     rmDirect
     ; clear h _h
    end.

    pose (L_extract) as _h.
    specialize _h with (1:=H3).
    match goal with
    | h:In (?v,?T) (extraction _ _) |- _ =>
     destruct (_h v T) as [? _];
     rmDirect
     ; clear h _h
    end.

    destruct H5, H6.
    match goal with
    | h:DB.Db ?v' _ _, h1: DB.Db ?v' _ _ |- _ =>
      pose (L_Db_uniqueT _ _ _ _ _ h h1)
      ; auto
    end.
  Qed.
  (* end hide *)

  (* begin hide *)
  Lemma L_compare_list : ∀ A (eq_dec : forall x y : A, {x = y}+{x <> y}) 
    (l1:list A) l2,
    (∀ v, In v l1 -> In v l2) ->
    NoDup l1 -> |l1| <= |l2|.
  Proof.
    intros.
    generalize dependent l2.
    induction l1; intros.
    simpl; lia.

    simpl.
    pose (H a).
    getH. tac_app. constructor; eauto.
    assert (|l1| <= |remove eq_dec a l2|).
    1:{
      apply IHl1.
      inversion H0; eauto.
      intros.
      pose (H v).
      getH. tac_app.
      constructor 2; auto.

      apply in_in_remove; auto.
      unfold not; intro.
      subst. inversion H0. contradiction.
    }

    assert (| (remove eq_dec a l2) | < |l2|).
    apply remove_length_lt; auto.
    lia.
  Qed.

  Lemma L23: ∀ A B (l:list (A*B)), 
    NoDup l 
      -> (∀ a b1 b2, In (a,b1) l -> In (a,b2) l -> b1=b2) 
      -> NoDup (map (fun ab => match ab with (a,b)=> a end) l).
  Proof.
    intros.
    induction l.
    simpl. constructor.
    simpl.
    constructor 2; eauto.

    2:{
      apply IHl. inversion H; eauto. intros. apply H0 with (a:=a0); constructor 2; auto.
    }
    
    unfold not.
    intro.
    apply_in_map.
    destruct x. destruct a. subst.
    assert (b=b0).
    apply H0 with (a:=a). constructor 2; auto. constructor. auto.
    subst.
    inversion H.
    easy.
  Qed.

  Lemma L_length_eq: ∀ A (x:list A) y z w, 
    x++y=z++w -> |x| = |z| -> x = z.
  Proof.
    intros.
    generalize dependent z.
    induction x; intros.
    simpl in H0. 
    destruct z; auto.
    simpl in H0.
    easy.
    
    destruct z;
    simpl in H0.
    easy.
    repeat rewrite <- app_comm_cons in H.
    simplList; subst.
    replace z with x; auto.
  Qed.
  (* end hide *)


  (** [bound_extraction]: during extraction, the length of [V] does not
      decrease, where [V] is the set of partial parse trees. *)
  Lemma bound_extraction: 
    ∀ m M T w i,
      Forest (m::M) T (w++[i]) -> 
    ∀ M1 m' M2, 
      M = ((M1++[m'])++M2) ->
      | extraction M1 (f_init m)| <= |extraction (M1++[m']) (f_init m)|.
  (* begin hide *)
  Proof.
    intros.

    pose (L_extract_extract _ _ _ w i H (M1) m' M2 H0) as Hex.
    destruct Hex as [w1 [w2 Hex1]].
    repeat breakAnd.

    generalize dependent m'.
    generalize dependent M2.
    induction M1 using rev_ind.

    1:{
      intros. simpl. auto.
    }

    intros.

    match goal with
    | |- _ <= |?l| =>
      set (ml2:= map (fun vt : list VE * list RetEdge => 
        match vt with 
        (v,t) => (tl v) end) l)
    end.

    match goal with
    | |- |?l| <= _ =>
      set (ml1:= map (fun vt : list VE * list RetEdge => match vt with (v,t) => v end) l)
    end.

    assert (|ml1| <= |ml2|).
    1:{
      apply L_compare_list.
      eauto with misc.
      2:{
        apply L23; auto;

        apply extraction_nodup_nodup with (1:=H) (m':=m') (M2:=M2); auto.
      }

      intros.

      unfold ml1 in H3.
      apply_in_map.

      rewrite <- app_assoc in H0.
      pose (L_extract_extract _ _ _ w i H M1 x ([m']++M2) H0) as Hex.
      breakAll.
      rename _h into h.

      pose (L_extract _ _ _ _ H4) as _h.
      destruct x0 as (v1,t1).
      specialize _h with v1 t1.
      destruct _h as [? _].
      rmDirect.

      breakAll; subst.
      1:{
        simpl in *.
        inversion Hex.
      }

      destruct x0. tac_invalid_df.
      assert (∃ x y, v0 :: x0 = (x ++ [y])) as hw.
      1:{
        assert ( v0 :: x0 != []) as notnil.
        eauto using nil_cons.
        destruct (exists_last notnil) as [? _h].
        destruct _h.
        rewrite e in *.
        clear notnil e.
  
        eauto.
      }

      destruct hw as [? [? hw]].
      rewrite hw in H8.


      destruct x1. inversion Hex.
      assert (∃ x y, s :: x1 = (x ++ [y])) as hw2.
      1:{
        assert ( s :: x1 != []) as notnil.
        eauto using nil_cons.
        destruct (exists_last notnil) as [? _h].
        destruct _h.
        rewrite e in *.
        clear notnil e.
  
        eauto.
      }
      destruct hw2 as [? [? hw2]].
      rewrite hw2 in H5.
      rewrite <- app_assoc in H5.

      unfold ml2.
      apply_in_map.

      assert (|x0| = |x1|).
      1:{
        pose (Df2.L_Df_vw _ _ _ H9).

        simpl in e.
        lia.
      }
      assert (|x0| = |x4|).
      1:{
        assert (|v0 :: x0| = |x4 ++ [x5]|).
        rewrite hw. auto.
        rewrite app_length in *.
        simpl in *.
        lia.
      }
      assert (|x1| = |x6|).
      1:{
        assert (|s :: x1| = |x6 ++ [x7]|).
        rewrite hw2. auto.
        rewrite app_length in *.
        simpl in *.
        lia.
      }
      assert (|x4| = |x6|).
      1:{
        lia.
      }

      destruct x4.
      1:{
        simpl in *.
        simplList; subst.
        assert (x1 = []).
        1:{
          inversion H9; subst; eauto; tac_inj; subst; try tac_invalid_df.
        }
        assert (x6 = []).
        1:{
          subst.
          tac_inj; subst. eauto.
        }
        subst; simpl in *.

        (* Get Db *)
        pose (TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.Core.CompleteM) as d0.
        specialize d0 with (1:=H7).
        getH. tac_app; 
        eauto using nil_cons, app_cons_not_nil.
        destruct x2; simpl; try tac_invalid_db; eauto using nil_cons.
        breakAll; subst.
        match goal with
        | h:DB.Db ?v ?t _ |- _ =>
         exists (v, t)
        end.
        split; eauto.

        apply (L_extract _ _ _ _ H1).

        assert (w1=[]).
        inversion Hex.
        destruct M2; simpl in Hex1; try easy.
        destruct w1; simpl in Hex1; try easy.

        replace (w2) with (x7 :: s0 :: x2); eauto.
        simplList; subst. auto. subst.
        rewrite H5.  eauto.
      }

      assert (∃ t, DB.Db ([x5]++v) t ([x7]++x2)) as _h.
      1:{
        pose (TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.Core.CompleteM) as d0.
        specialize d0 with (1:=H7).
        getH. tac_app; 
        eauto using nil_cons, app_cons_not_nil.
        repeat (breakEx + breakAnd).
        rewrite hw in H12.
        rewrite hw2 in H12.
        do 2 rewrite <- app_assoc in H12.

        pose (Dbx.L_split_db) as _h.
        match goal with
        | h: DB.Db (?v++_) _ (?w++_) |- _ =>
          specialize _h with (1:=h) (v1:=v) (w1:=w)
        end.
        apply _h; eauto using nil_cons.

        do 2 rewrite app_length; simpl.

        match goal with
        | h:DB.Db _ _ _ |- _ =>
          pose (Dbx.L_Db_vw _ _ _ H12) as q
        end.
        repeat rewrite app_assoc in q.
        rewrite <- hw2 in q.
        repeat rewrite app_length in q.
        simpl in q.
        simpl in *. 
        lia.
      }
      destruct (_h) as [t' ?].
      exists ([x5]++v, t').
      split; eauto.

      apply (L_extract _ _ _ _ H1).

      assert (w2=x7::x2).
      1:{
        rewrite hw2 in H7.
        rewrite hw in H7.
        rewrite <- app_assoc in H7.
        simpl in Hex.
        inversion Hex.
        rewrite Hex1 in H14.
        rewrite H10 in H14.
        assert (x6=w1).
        rewrite <- H5 in H2.

        symmetry.
        apply L_length_eq with (1:=H2). eauto.
        subst.
        rewrite <- H5 in H2.

        apply (app_inv_head) with (1:=H2).
      }
      rewrite H13.

      split; eauto.
      right.
      rewrite hw in H7.
      rewrite hw2 in H7.
      repeat rewrite <- app_assoc in H7.

      Ltac dm2df :=
        match goal with
        | h: Dm L_0 ?w ?v |- _ =>
          pose (TimedSets.Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Core.CompleteM) as d0;
          specialize d0 with (1:=h);
          getH; [tac_app; eauto using nil_cons, app_cons_not_nil|]
          ; clear d0; breakEx; breakAnd
        end.
        
      dm2df.

      rename _h into _H.

      (* TODO *)
      match goal with
      | h: Df (?v1 ++ ?v2) _ (?w1 ++ ?w2)
      |- _ =>
        pose (Split.DF_SPLIT2 _ _ _ h v1 v2) as _h
        ; getH
        ; [apply _h; eauto using nil_cons |]
        ; clear _h
      end.

      repeat (breakEx + breakAnd).
      exists (v1 :: x4), x9.

      (* match goal with
      | h:Df ?v ?t _ |- _ =>
        exists v, t
      end. *)

      getAnd; eauto.
      apply (VListBeginSame) with (1:=H8). eauto using nil_cons.

      assert (x10=w1).
      1:{
        rewrite H5 in H16.
        rewrite <- H2 in H16.

        pose (Df2.L_Df_vw _ _ _ H17).
        rewrite <- H3 in e.
        rewrite H0 in e.
        simpl in Hex. inversion Hex.
        rewrite Hex1 in H20.
        rewrite <- H20 in e.
        symmetry in e.
        apply (L_length_eq _ _ _ _ _ H16); auto.
      }
      subst. auto.
      getAnd; eauto.


      replace w1 with x6; auto.

      simpl in Hex. inversion Hex.
      rewrite <- H0 in H19.
      rewrite H3 in H19.
      rewrite Hex1 in H19.
      rewrite H11 in H19.
      symmetry.
      apply (L_length_eq _ _ _ _ _ H16); auto.
    }

    unfold ml1 in H3.
    unfold ml2 in H3.

    match goal with 
    | h: |map ?f1 ?l1| <= |map ?f2 ?l2| |- _ => 
      rewrite <- (map_length f1 l1)
      ; rewrite <- (map_length f2 l2)
    end.
    auto.
  Qed.
  (* end hide *)

End ExtractionWNoDup.