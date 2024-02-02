(** This file provides the monadic functions [goEps'] and [nodup'], each
  function attached with its time complexity, with the assumption that
  some basic operations cost only one time unit. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Unicode.Utf8_core.

Require Import Lia.

Require Import Misc.
Import Misc.Basic.
Import Misc.vpg.

Require Import Def.
Require Import Dbx.

Require Import Program.
Require Import Monad.
Require Import MonadicUtils.

Module PreTimed(G:VPG).

  Module Dbx := DBX(G).

  Include Dbx.BackwardSmallStep.ForwardSmallStep.Def.

  (* begin hide *)

  (** [endE]: take the last nonterminal of a rule.  *)
  Definition endE e :=
    match e with
    | Plnv (PlnE _ _ L) => L
    | Calv (PndCalE _ _ L) => L
    | Calv (MatCalE _ _ L _ _) => L
    | Retv (PndRetE _ _ L) => L
    | Retv (MatRetE _ _ _ _ L) => L
    end.

  (** [beginE]: take the first nonterminal of a rule.  *)
  Definition beginE e :=
    match e with
    | Plnv (PlnE L _ _) => L
    | Calv (PndCalE L _ _) => L
    | Calv (MatCalE L _ _ _ _) => L
    | Retv (PndRetE L _ _) => L
    | Retv (MatRetE L _ _ _ _) => L
    end.
    
  (* end hide *)

  (* Definition t_cmp_string := 1. *)
  (* Definition t_ct := 1. *)

  (** [cost_endE]: taking the last nonterminal from a rule is a basic
    operation. *)
  Definition cost_endE := 1.

  (** [cost_beginE]: taking the first nonterminal from a rule is a basic
    operation. *)
  Definition cost_beginE := 1.

  (** [cons_snd]: taking the second element from a tuple is a basic
    operation. *)
  Definition cons_snd := 1.

  (* begin hide *)

  Ltac unfold_ct :=
    try (unfold cost_eqvv);
    (* try (unfold t_cmp_string); *)
    (* try (unfold t_ct); *)
    try (unfold cost_endE);
    try (unfold cost_beginE);
    try (unfold cost_andb);
    try (unfold cons_snd);
    try (unfold cost_orb);
    try lia.

  Program Definition _endE e 
    : {! y !:! _ !<! c !>! c = cost_endE /\ y = endE e !}
    :=
      match e with
      | Plnv (PlnE _ _ L) => += cost_endE; <== L
      | Calv (PndCalE _ _ L) => += cost_endE; <== L
      | Calv (MatCalE _ _ L _ _) => += cost_endE; <== L
      | Retv (PndRetE _ _ L) => += cost_endE; <== L
      | Retv (MatRetE _ _ _ _ L) => += cost_endE; <== L
      end.

  Program Definition _beginE e 
    : {! y !:! _ !<! c !>! c = cost_beginE /\ y = beginE e !}
    :=
      match e with
      | Plnv (PlnE L _ _) => += cost_beginE; <== L
      | Calv (PndCalE L _ _) => += cost_beginE; <== L
      | Calv (MatCalE L _ _ _ _) => += cost_beginE; <== L
      | Retv (PndRetE L _ _) => += cost_beginE; <== L
      | Retv (MatRetE L _ _ _ _) => += cost_beginE; <== L
      end.

  (* begin hide *)

  (** [ff]: checks if the rule [e] ends with a nonterminal that derives
    the empty string *)
  Definition ff e r :=
    match r with 
    | (L1, Alt_Epsilon) => eqvv (endE e) L1
    | _ => false
    end.

  Definition cost_ff_branch1 := 1.
  Definition cost_ff_branch2 := 1.
  Opaque cost_ff_branch1.
  Opaque cost_ff_branch2.

  (** [cost_ff]: the time cost of the function [ff]. *)
  Definition cost_ff e r := 
    match r with
    | (L1, Alt_Epsilon) => cost_eqvv (endE e) L1 + cost_endE
      + cost_ff_branch1
    | _ => cost_ff_branch2
    end.

  (** [bound_cost_ff]: the time cost of the function [ff] is constant.
    *)
  Lemma bound_cost_ff: ∃ k, ∀ e r, cost_ff e r <= k.
  (* begin hide *)
  Proof.
    destruct bound_cost_eqvv as [k H].
    exists (k + cost_endE + cost_ff_branch1 + cost_ff_branch2).
    intros.
    
    unfold cost_ff. destruct r; destruct a.
    pose (H (endE e) v).
    all: lia.
  Qed.
  (* end hide *)
  
  (* [ff']: the monadic version of [ff]. *)
  Program Definition ff' e (r:rule)
  : {! y !:! bool !<! c !>! c = cost_ff e r
    /\ y = ff e r !}
  :=
    match r as x' return r = x' -> 
      {! y !:! bool !<! c !>! c = cost_ff e r
      /\ y = ff e r !} with
    | (L1, Alt_Epsilon) =>
      fun hyp =>
        (end_of_e <- _endE e;
        += cost_ff_branch1;
        out <- eqvv' end_of_e L1;
        <== out)
    | _ =>
      fun hyp =>
        (+= cost_ff_branch2; <== false)
    end (eq_refl r).

  (* begin hide *)
  Next Obligation.
    split; auto. unfold cost_ff. lia.
  Defined.
  (* end hide *)

  (** [cost_goEps]: the cost of the function [goEps] *)
  Definition cost_goEps (P:rules) e : nat :=
    cost_existb _ (cost_ff e) P.
  
  Opaque cost_endE.
  Opaque cost_orb.
  Opaque cost_existb_branch1.
  Opaque cost_existb_branch2.

  (** [cost_goEps]: the cost of the function [goEps] is O(|P|) *)
  Lemma bound_cost_goEps: ∃ k b, ∀ P e, cost_goEps P e <= k * |P| + b.
  (* begin hide *)
  Proof.
    destruct (bound_cost_eqvv) as [k H].
    destruct (bound_cost_ff) as [k1 H1].

    exists (k1 + k + cost_endE + cost_orb + cost_existb_branch2), 
      (cost_existb_branch1).

    intros.
    match goal with
    | P: rules |- _ =>
     induction P;
     simpl; try lia
    end.

    match goal with
    | a: rule, e:VE |- _ =>
      destruct a as [v ]
      ; pose (H (endE e) v)
      ; pose (H1 e (v, a))
    end.
    
    lia.
  Qed.
  (* end hide *)

  (** [goEps]: checks if the rule [e] can terminate. *)
  Definition goEps e :=
    List.existsb (ff e) P.

  (** [goEps']: the monadic version of [goEps]. *)
  Definition goEps' e
    : {! y !:! bool !<! c !>! c = cost_goEps P e /\ y = goEps e !}
    :=
    existsb' (ff' e) P.

End PreTimed.

Section nodup.
  Variable A : Type.

  Definition time_nodup_branch0 := 1.
  Definition time_nodup_branch1 := 1.
  Definition time_nodup_branch2 := 1.

  Opaque time_nodup_branch0.
  Opaque time_nodup_branch1.
  Opaque time_nodup_branch2.

  (** [cost_nodup]: the cost of the function [nodup] *)
  Fixpoint cost_nodup
    (inlist:A->list A->bool)
    cost_inlist
    (l:list A) :=
    match l with
    | nil => time_nodup_branch0
    | x::xs =>
      cost_inlist x xs +
      if inlist x xs then
        time_nodup_branch1 + cost_nodup inlist cost_inlist xs
      else
        time_nodup_branch2 + cons_ct + (cost_nodup inlist cost_inlist xs)
    end.

  (** [cost_nodup]: the cost of the function [nodup] is O(|l|), where
      [l] is the list to remove duplicates. *)
  Lemma bound_cost_nodup: forall inlist cost_inlist ln, 
    (forall a l, cost_inlist a l <= ln) ->
      exists k b, forall l,
        cost_nodup inlist cost_inlist l <= k * (length l)+b.
  (* begin hide *)
  Proof.
    intros.
    exists (
      ln + time_nodup_branch1 + time_nodup_branch2 + cons_ct
    ), time_nodup_branch0.

    intros.
    induction l. simpl. lia.
    simpl.
    pose (H a l).
    destruct_with_eqn (inlist a l); simpl; lia.
  Qed.
  (* end hide *)

  Definition cost_in_dec_branch1 := 1.
  Definition cost_in_dec_branch2 := 1.
  Definition cost_in_dec_branch3 := 1.
  Definition cost_in_dec_branch4 := 1.
  Opaque cost_in_dec_branch1.
  Opaque cost_in_dec_branch2.
  Opaque cost_in_dec_branch3.
  Opaque cost_in_dec_branch4.
  Opaque cons_ct.

  (** [nodup]: removes the duplicates in a list. *)
  Fixpoint nodup (inlist:A->list A->bool) (l:list A) :=
    match l with
    | nil => nil
    | x::xs =>
        if inlist x xs then
          nodup inlist xs
        else
          let out1 := nodup inlist xs in
          let out2 := x::out1 in
          out2
    end.

  (** [bound_nodup]: the list shrinks with duplicates removed. *)
  Lemma bound_nodup: forall cost_inlist (l:list A), 
    (length (nodup cost_inlist l)) <= (length l).
  (* begin hide *)
  Proof.
    intros.
    induction l; simpl; eauto.
    destruct_with_eqn (cost_inlist a l); simpl; eauto.
    lia.
  Qed.
  (* end hide *)

  (** [nodup']: the monadic version of [nodup]. *)
  Program Fixpoint nodup' 
    {inlist}
    {cost_inlist}
    (inlist':
      forall a l,
      {! y !:! bool
        !<! c !>! c = cost_inlist a l /\ 
        y = inlist a l !})
    l 
  : {! y !:! list A !<! c !>! c = cost_nodup inlist cost_inlist l 
    /\ y = nodup inlist l !}
  :=
    match l as l' return (l=l')->
      {! y !:! list A !<! c !>! c = cost_nodup inlist cost_inlist l 
        /\ y = nodup inlist l !}
    with
    | nil =>
      fun hyp =>
        += time_nodup_branch0; <== nil
    | x::xs =>
      fun hyp =>
        b <- inlist' x xs;
        if dec b then
          out <- nodup' inlist' xs;
          += time_nodup_branch1; 
          <== out
        else
          out1 <- nodup' inlist' xs;
          out2 <- cons' _ x out1;
          += time_nodup_branch2; 
          <== out2
    end (eq_refl l).
  (* begin hide *)
  Next Obligation.
    split; simpl. rewrite e. lia. rewrite e.
    eauto.
  Defined.

  Next Obligation.
    split; simpl; rewrite e. lia. eauto.
  Defined.
  (* end hide *)


  (** [nodup_In]: if [x] is in the list, then [x] is also in the list 
    without duplicates. *)
  Lemma nodup_In x l inlist (p: ∀ a b, inlist a b = true <-> In a b):
    In x (nodup inlist l) <-> In x l.
  (* begin hide *)
  Proof.
    generalize dependent x.

    induction l. simpl in *. easy.
    intros.
    split; intros.
    1: {
      simpl in H.
      destruct_with_eqn (inlist a l).
      1:{
        destruct (IHl x) as [h _].
        specialize h with (1:=H).
        constructor 2. auto.
      }
      
      inversion H; subst.
      constructor 1. auto.
      destruct (IHl x) as [h _].
      specialize h with (1:=H0).
      constructor 2. auto.
    }

    inversion H; subst.
    simpl.
    destruct_with_eqn (inlist x l).
    apply IHl.
    apply p. auto.
    constructor 1. auto.

    simpl.
    destruct_with_eqn (inlist a l).
    apply IHl. auto.

    constructor 2. auto.    
    apply IHl. auto.
  Qed.
  (* end hide *)

  (** [NoDup_nodup]: the list without duplicates satisfies the relation
    [NoDup]. 
  *)
  Lemma NoDup_nodup (l:list A) inlist 
    (p: ∀ a b, inlist a b = true <-> In a b): 
    NoDup (nodup inlist l).
  (* begin hide *)
  Proof.
    induction l.
    simpl. constructor 1.
    simpl.
    destruct_with_eqn (inlist a l). auto.
    constructor 2; auto.

    unfold not; intro.
    assert (In a l).
    apply (nodup_In a l inlist p); auto.
    assert (inlist a l = true).
    apply p; auto.
    rewrite H1 in Heqb. easy.
  Qed.
  (* end hide *)
End nodup.

Arguments nodup {A}.
