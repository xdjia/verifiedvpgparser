(** This file provides the basic monadic functions used by the parsing
    and extraction functions. Each monadic function is attached with its
    time complexity, with the assumption that some _basic operations_
    cost only one time unit. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import 
  MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require 
  Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Unicode.Utf8_core.
Require Import Program.
Require Import Lia.

Require Import Misc.
Import Basic.
Import vpg.
Require Import Def.
Require Import Monad.
Require Import MonadicUtils.

Require Import GenForest.

Module TimedSets(G:VPG).

  Module Parser := Parser(G).

  Import Parser.
  Import Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Tacs.

  (** [cost_negb]: the function [negb] negates a boolean is viewed as a
    basic operation. *)
  Definition cost_negb := 1.

  (* begin hide *)
  Opaque cost_negb.
  Opaque cost_eq_str.

  Ltac breakEq H1 H2 h :=
    match h with
    | (if negb (eqvv ?L ?L1) then _ else _) =>
      destruct (negb (eqvv L L1))
      ; pose (H1 L L1)
      ; pose (H2 L L1); try lia
    | (if negb (eqvv ?L ?L1) then _ else _) + _  =>
      destruct (negb (eqvv L L1))
      ; pose (H1 L L1)
      ; pose (H2 L L1); try lia
    | (if negb (eq_str ?L ?L1) then _ else _) =>
      destruct (negb (eq_str L L1))
      ; try lia
    | (if negb (eq_str ?L ?L1) then _ else _) + _  =>
      destruct (negb (eq_str L L1))
      ; try lia
    | _ + ?h1 =>
      breakEq H1 H2 h1
    end.

  Ltac AddHyp H1 H2 h :=
    match h with
    | (cost_compare_vv ?L ?L1) =>
      pose (H1 L L1)
      ; pose (H2 L L1); try lia
    | (cost_compare_vv ?L ?L1) + _  =>
      pose (H1 L L1)
      ; pose (H2 L L1); try lia
    | _ + ?h1 =>
      AddHyp H1 H2 h1
    end.
  (* end hide *)

  
  (** The module [timed_ea] provides a monadic function that compares 
    two call rules. *)
  Module timed_ea.

    (** Each program branch is assigned with a constant value. *)
    Definition compare_branch1 := 1.
    Definition compare_branch2 := 1.
    Definition compare_branch3 := 1.
    Definition compare_branch4 := 1.
    Definition compare_branch5 := 1.
    Definition compare_branch6 := 1.
    Definition compare_branch7 := 1.
    Definition compare_branch8 := 1.
    Definition compare_branch9 := 1.
    Definition compare_branch10 := 1.

    Opaque compare_branch1.
    Opaque compare_branch2.
    Opaque compare_branch3.
    Opaque compare_branch4.
    Opaque compare_branch5.
    Opaque compare_branch6.
    Opaque compare_branch7.
    Opaque compare_branch8.
    Opaque compare_branch9.
    Opaque compare_branch10.

    (** [cost_compare_str]: comparing two terminals is a basic
      operation. *)
    Opaque cost_compare_str.
    (** [cost_compare_vv]: comparing two nonterminals is a basic
      operation. *)
    Opaque cost_compare_vv.

    (** [cost_compare]: the cost of comparing two call rules. *)
    Definition cost_compare x y :=
      match x, y with
      | PndCalE _ _ _, MatCalE _ _ _ _ _ =>
        compare_branch1
      | PndCalE L1 a L2, PndCalE L1' a' L2' =>
        cost_eq_str + cost_negb +
        if negb (eq_str a a') then
          cost_compare_str + compare_branch2
        else 
        cost_eqvv L1 L1' + cost_negb +
        if negb (eqvv L1 L1') then
          cost_compare_vv L1 L1' + compare_branch3
        else
          cost_compare_vv L2 L2' + compare_branch4
      | MatCalE L1 a L2 b L3, MatCalE L1' a' L2' b' L3' =>
        cost_eq_str + cost_negb +
        if negb (eq_str a a') then
          cost_compare_str
          + compare_branch5
        else
        cost_eq_str + cost_negb +
        if negb (eq_str b b') then
          cost_compare_str +
          compare_branch6 else
        cost_eqvv L1 L1' + cost_negb +
        if negb (eqvv L1 L1') then
          cost_compare_vv L1 L1' + compare_branch7 else
        cost_eqvv L2 L2' + cost_negb +
        if negb (eqvv L2 L2') then
          cost_compare_vv L2 L2' + compare_branch8 else
          cost_compare_vv L3 L3' + compare_branch9
      | _, _ =>
        compare_branch10
      end.

    (** [bound_cost_compare]: the cost of comparing two call rules take
      constant time. *)
    Lemma bound_cost_compare:
      ∃ k, ∀ x y, cost_compare x y <= k.
    (* begin hide *)
    Proof.
      destruct bound_cost_eqvv as [k1 H1].
      destruct bound_cost_compare_vv as [k2 H2].
      
      exists (
        compare_branch1  +
        compare_branch2  +
        compare_branch3  +
        compare_branch4  +
        compare_branch5  +
        compare_branch6  +
        compare_branch7  +
        compare_branch8  +
        compare_branch9  +
        compare_branch10 +
        k1 + k2 + 
        k1 + k2 + 
        k1 + k2 + 
        k1 + k2 + 
        cost_eq_str + cost_negb + cost_compare_str +
        cost_eq_str + cost_negb + cost_compare_str +
        cost_eq_str + cost_negb + cost_compare_str + cost_negb
      ).

      intros.

      destruct x; destruct y; unfold cost_compare.
      destruct (negb (eq_str a a0)).
      rewrite Nat.add_assoc. 
      lia.
      repeat rewrite Nat.add_assoc.

      all: try lia.

      all: repeat match goal with
      | |- ?h <= _ =>
        try breakEq H1 H2 h
      end.

      all: match goal with
      | |- ?h <= _ =>
        try AddHyp H1 H2 h
      end.

    Qed.
    (* end hide *)

    (** [compare']: the monadic function to compare two call rules,
      where [y] is the result of the function, and [c] is the time cost.
    *)
    Program Definition compare' a b
    :{! y !:! comparison !<! c !>! 
      c = cost_compare a b /\ 
      y = ea_as_OT.compare a b !}
      :=
      match a as a', b as b' return
        (a=a')->(b=b')->
        {! y !:! comparison !<! c !>! 
          c = cost_compare a b /\ 
          y = ea_as_OT.compare a b !}
      with 
      | PndCalE _ _ _, MatCalE _ _ _ _ _ =>
        fun hyp1 hyp2 => 
        += compare_branch1;
        <== Lt 
      | PndCalE L1 a L2, PndCalE L1' a' L2' =>
        fun hyp1 hyp2 =>
        if dec (negb (eq_str a a')) then
          += cost_negb + cost_eq_str +
          cost_compare_str +
          compare_branch2;
          <== compare_str a a'
        else 
        res <- eqvv' L1 L1';
        if dec (negb res) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str + cost_negb
          + compare_branch3;
          <== out
        else
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str + cost_negb
          + compare_branch4;
          <== out
      | MatCalE L1 a L2 b L3, MatCalE L1' a' L2' b' L3' =>
        fun hyp1 hyp2 => 
        if dec (negb (eq_str a a')) then
          += cost_negb + cost_eq_str +
          cost_compare_str +
          compare_branch5;
          <== compare_str a a' else
        if dec (negb (eq_str b b')) then
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str +
          cost_compare_str +
          compare_branch6;
          <== compare_str b b' else
        if dec (negb (eqvv L1 L1')) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' +
          compare_branch7;
          <== out else
        if dec (negb (eqvv L2 L2')) then 
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' +
          cost_negb + cost_eqvv L2 L2' +
          compare_branch8;
          <== out else 
        out <- compare_vv' L3 L3';
        += cost_negb + cost_eq_str +
        cost_negb + cost_eq_str + 
        cost_negb + cost_eqvv L1 L1' +
        cost_negb + cost_eqvv L2 L2' +
        compare_branch9;
        <== out
      | _, _ =>
        fun hyp1 hyp2 => 
        += compare_branch10;
        <== Gt
      end (eq_refl a) (eq_refl b).
    (* begin hide *)

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e. lia.

      simpl.
      
      rewrite e.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e. lia.
      simpl.
      rewrite e. auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      lia.
      simpl.
      rewrite e.
      rewrite e0. auto.
    Qed.
    
    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      rewrite e1.

      lia.
      simpl.
      rewrite e.
      rewrite e0.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
        rewrite e1.
      
      auto.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1'); auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      lia.

      simpl.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      lia.

      simpl.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      auto.
    Qed.
    (* end hide *)
    (* begin hide *)

    Lemma L_compare_eq: ∀ a b, ea_as_OT.compare a b = Eq <->
      a = b.
    Proof.
      intros.
      destruct (ea_as_OT.compare_spec a b); try easy;
      split; intros; subst; try easy;
      destruct (ea_as_OT.lt_strorder);
      match goal with
          | h: _ ?x ?x |- _ =>
            (destruct (ea_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto) +
            (destruct (ec_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto) +
            (destruct (eb_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto)
          end.
    Qed.
    (* end hide *)

(* end hide *)
  End timed_ea.

  (** The rest modules are quite similar to the module [timed_ea]; their
    documentation are omitted. *)
  Module timed_eb.
      (* begin hide *)

    Definition compare_branch1 := 1.
    Definition compare_branch2 := 1.
    Definition compare_branch3 := 1.
    Definition compare_branch4 := 1.
    Definition compare_branch5 := 1.
    Definition compare_branch6 := 1.
    Definition compare_branch7 := 1.
    Definition compare_branch8 := 1.
    Definition compare_branch9 := 1.
    Definition compare_branch10 := 1.

    Opaque compare_branch1.
    Opaque compare_branch2.
    Opaque compare_branch3.
    Opaque compare_branch4.
    Opaque compare_branch5.
    Opaque compare_branch6.
    Opaque compare_branch7.
    Opaque compare_branch8.
    Opaque compare_branch9.
    Opaque compare_branch10.
    Opaque cost_compare_str.
    Opaque cost_compare_vv.

    Definition cost_compare x y :=
      match x, y with
      | PndRetE _ _ _, MatRetE _ _ _ _ _ =>
        compare_branch1
      | PndRetE L1 a L2, PndRetE L1' a' L2' =>
        cost_eq_str + cost_negb +
        if negb (eq_str a a') then
          cost_compare_str + compare_branch2
        else 
        cost_eqvv L1 L1' + cost_negb +
        if negb (eqvv L1 L1') then
          cost_compare_vv L1 L1' + compare_branch3
        else
          cost_compare_vv L2 L2' + compare_branch4
      | MatRetE L1 a L2 b L3, MatRetE L1' a' L2' b' L3' =>
        cost_eq_str + cost_negb +
        if negb (eq_str a a') then
          cost_compare_str
          + compare_branch5
        else
        cost_eq_str + cost_negb +
        if negb (eq_str b b') then
          cost_compare_str +
          compare_branch6 else
        cost_eqvv L1 L1' + cost_negb +
        if negb (eqvv L1 L1') then
          cost_compare_vv L1 L1' + compare_branch7 else
        cost_eqvv L2 L2' + cost_negb +
        if negb (eqvv L2 L2') then
          cost_compare_vv L2 L2' + compare_branch8 else
          cost_compare_vv L3 L3' + compare_branch9
      | _, _ =>
        compare_branch10
      end.

      Lemma bound_cost_compare:
        ∃ k, ∀ x y, cost_compare x y <= k.
      Proof.
        destruct bound_cost_eqvv as [k1 H1].
        destruct bound_cost_compare_vv as [k2 H2].
        
        exists (
          compare_branch1  +
          compare_branch2  +
          compare_branch3  +
          compare_branch4  +
          compare_branch5  +
          compare_branch6  +
          compare_branch7  +
          compare_branch8  +
          compare_branch9  +
          compare_branch10 +
          k1 + k2 + 
          k1 + k2 + 
          k1 + k2 + 
          k1 + k2 + 
          cost_eq_str + cost_negb + cost_compare_str +
          cost_eq_str + cost_negb + cost_compare_str +
          cost_eq_str + cost_negb + cost_compare_str + cost_negb
        ).

        intros.

        destruct x; destruct y; unfold cost_compare.

        all: try lia.

        all: repeat match goal with
        | |- ?h <= _ =>
          try breakEq H1 H2 h
        end.
    
        all: match goal with
        | |- ?h <= _ =>
          try AddHyp H1 H2 h
        end.
      Qed.

    Program Definition compare' a b
    :{! y !:! comparison !<! c !>! 
      c = cost_compare a b /\ 
      y = eb_as_OT.compare a b !}
    :=
      match a as a', b as b' return
        (a=a')->(b=b')->
        {! y !:! comparison !<! c !>! 
          c = cost_compare a b /\ 
          y = eb_as_OT.compare a b !}
      with 
      | PndRetE _ _ _, MatRetE _ _ _ _ _ =>
        fun hyp1 hyp2 => 
        += compare_branch1;
        <== Lt 
      | PndRetE L1 a L2, PndRetE L1' a' L2' =>
        fun hyp1 hyp2 =>
        if dec (negb (eq_str a a')) then
          += cost_negb + cost_eq_str +
          cost_compare_str +
          compare_branch2;
          <== compare_str a a'
        else 
        res <- eqvv' L1 L1';
        if dec (negb res) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str + cost_negb
          + compare_branch3;
          <== out
        else
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str + cost_negb
          + compare_branch4;
          <== out
      | MatRetE L1 a L2 b L3, MatRetE L1' a' L2' b' L3' =>
        fun hyp1 hyp2 => 
        if dec (negb (eq_str a a')) then
          += cost_negb + cost_eq_str +
          cost_compare_str +
          compare_branch5;
          <== compare_str a a' else
        if dec (negb (eq_str b b')) then
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str +
          cost_compare_str +
          compare_branch6;
          <== compare_str b b' else
        if dec (negb (eqvv L1 L1')) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' +
          compare_branch7;
          <== out else
        if dec (negb (eqvv L2 L2')) then 
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' +
          cost_negb + cost_eqvv L2 L2' +
          compare_branch8;
          <== out else 
        out <- compare_vv' L3 L3';
        += cost_negb + cost_eq_str +
        cost_negb + cost_eq_str + 
        cost_negb + cost_eqvv L1 L1' +
        cost_negb + cost_eqvv L2 L2' +
        compare_branch9;
        <== out
      | _, _ =>
        fun hyp1 hyp2 => 
        += compare_branch10;
        <== Gt
      end (eq_refl a) (eq_refl b).

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e. lia.
      simpl.
      rewrite e.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e. lia.
      simpl.
      rewrite e. auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      lia.
      simpl.
      rewrite e.
      rewrite e0. auto.
    Qed.
    
    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      rewrite e1.

      lia.
      simpl.
      rewrite e.
      rewrite e0.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
        rewrite e1.
      
      auto.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1'); auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      lia.

      simpl.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      lia.

      simpl.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      auto.
    Qed.

    Lemma L_compare_eq: ∀ a b, eb_as_OT.compare a b = Eq <->
      a = b.
    Proof.
      intros.
      destruct (eb_as_OT.compare_spec a b); try easy;
      split; intros; subst; try easy;
      destruct (eb_as_OT.lt_strorder);
      match goal with
          | h: _ ?x ?x |- _ =>
            (destruct (eb_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto) +
            (destruct (ec_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto) +
            (destruct (eb_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto)
          end.
    Qed.
(* end hide *)
  End timed_eb.

  Module timed_ec.
      (* begin hide *)

    Definition compare_branch1 := 1.
    Definition compare_branch2 := 1.
    Definition compare_branch3 := 1.
    Definition compare_branch4 := 1.

    Opaque compare_branch1.
    Opaque compare_branch2.
    Opaque compare_branch3.
    Opaque compare_branch4.

    Opaque cost_compare_str.
    Opaque cost_compare_vv.

    Definition cost_compare x y :=
      match x, y with
      | PlnE L1 a L2, PlnE L1' a' L2' =>
        cost_eq_str + cost_negb +
        if negb (eq_str a a') then
          cost_compare_str + compare_branch2
        else 
        cost_eqvv L1 L1' + cost_negb +
        if negb (eqvv L1 L1') then
          cost_compare_vv L1 L1' + compare_branch3
        else
          cost_compare_vv L2 L2' + compare_branch4
      end.

    Lemma bound_cost_compare:
      ∃ k, ∀ x y, cost_compare x y <= k.
    Proof.
      destruct bound_cost_eqvv as [k1 H1].
      destruct bound_cost_compare_vv as [k2 H2].
      
      exists (
        compare_branch1  +
        compare_branch2  +
        compare_branch3  +
        compare_branch4  +
        k1 + k2 + 
        k1 + k2 + 
        k1 + k2 + 
        k1 + k2 + 
        cost_eq_str + cost_negb + cost_compare_str +
        cost_eq_str + cost_negb + cost_compare_str +
        cost_eq_str + cost_negb + cost_compare_str + cost_negb
      ).

      intros.

      destruct x; destruct y; unfold cost_compare.

      all: try lia.

      all: repeat match goal with
      | |- ?h <= _ =>
        try breakEq H1 H2 h
      end.

      all: match goal with
      | |- ?h <= _ =>
        try AddHyp H1 H2 h
      end.
    Qed.

    Program Definition compare' a b
    :{! y !:! comparison !<! c !>! 
      c = cost_compare a b /\ 
      y = ec_as_OT.compare a b !}
    :=
      match a as a', b as b' return
        (a=a')->(b=b')->
        {! y !:! comparison !<! c !>! 
          c = cost_compare a b /\ 
          y = ec_as_OT.compare a b !}
      with 
      | PlnE L1 a L2, PlnE L1' a' L2' =>
        fun hyp1 hyp2 =>
        if dec (negb (eq_str a a')) then
          += cost_negb + cost_eq_str +
          cost_compare_str +
          compare_branch2;
          <== compare_str a a'
        else 
        res <- eqvv' L1 L1';
        if dec (negb res) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str + cost_negb
          + compare_branch3;
          <== out
        else
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str + cost_negb
          + compare_branch4;
          <== out
      end (eq_refl a) (eq_refl b).

    Next Obligation.
      split; auto.
      unfold cost_compare.
      rewrite e. lia.
      simpl.
      rewrite e.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Lemma L_compare_eq: ∀ a b, ec_as_OT.compare a b = Eq <->
      a = b.
    Proof.
      intros.
      destruct (ec_as_OT.compare_spec a b); try easy;
      split; intros; subst; try easy;
      destruct (ec_as_OT.lt_strorder);
      match goal with
          | h: _ ?x ?x |- _ =>
            (destruct (ea_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto) +
            (destruct (ec_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto) +
            (destruct (eb_as_OT.lt_strorder);
            destruct (StrictOrder_Irreflexive x); eauto)
          end.
    Qed.

(* end hide *)
  End timed_ec.

  Module timed_op_ea.
      (* begin hide *)

    Definition compare_branch1 := 1.
    Definition compare_branch2 := 1.
    Definition compare_branch3 := 1.
    Definition compare_branch4 := 1.


    Opaque compare_branch1.
    Opaque compare_branch2.
    Opaque compare_branch3.
    Opaque compare_branch4.

    Opaque cost_compare_str.
    Opaque cost_compare_vv.

    Definition cost_compare (a:option ea_as_OT.t) (b:option ea_as_OT.t) :=
      match a, b with
      | None, None => compare_branch1
      | None, Some _ => compare_branch2
      | Some _, None => compare_branch3
      | Some a, Some b => 
        timed_ea.cost_compare a b + compare_branch4
      end.

    Lemma bound_cost_compare:
      ∃ k, ∀ x y, cost_compare x y <= k.
    Proof.
      destruct timed_ea.bound_cost_compare as [k1 H1].
      
      exists (
        compare_branch1  +
        compare_branch2  +
        compare_branch3  +
        compare_branch4  +
        k1).

      intros.

      destruct x; destruct y; unfold cost_compare; try lia.
      pose (H1 t t0). lia.
    Qed.

    Program Definition compare' a b
    :{! y !:! comparison !<! c !>! 
      c = cost_compare a b /\ 
      y = opea_as_OT.compare a b !}
    :=
      match a as a', b as b' return
        (a=a')->(b=b')->
        {! y !:! comparison !<! c !>! 
          c = cost_compare a b /\ 
          y = opea_as_OT.compare a b !}
      with 
      | None, None =>
        fun hyp1 hyp2 => 
          += compare_branch1;
          <== Eq
      | None, Some _ =>
        fun hyp1 hyp2 =>
          += compare_branch2;
          <== Lt
      | Some _, None =>
        fun hyp1 hyp2 => 
          += compare_branch3;
          <== Gt
      | Some a, Some b =>
        fun hyp1 hyp2 => 
        out <- timed_ea.compare' a b;
        += compare_branch4;
        <== out
      end (eq_refl a) (eq_refl b).
(* end hide *)
  End timed_op_ea.

  Module timed_ra.
      (* begin hide *)

    Definition va_compare := va_set.compare.

    Definition compare x y :=
      match (opea_as_OT.compare (fst x) (fst y))
      with 
      | Eq => (ea_as_OT.compare (snd x) (snd y)) 
      | Lt => Lt 
      | Gt => Gt 
      end.

    Lemma L_compare: ∀ x y,
      compare x y = ra_as_OT.compare x y.
    Proof.
      easy.
    Qed.

    Definition compare_branch1 := 1.
    Definition compare_branch2 := 1.
    Definition compare_branch3 := 1.
    Opaque compare_branch1.
    Opaque compare_branch2.
    Opaque compare_branch3.

    Definition cost_compare x y :=
      timed_op_ea.cost_compare (fst x) (fst y) + 
      match opea_as_OT.compare (fst x) (fst y) with 
      | Eq => compare_branch1 + 
          timed_ea.cost_compare (snd x) (snd y)
      | Lt => compare_branch2
      | Gt => compare_branch3
      end.

    Lemma bound_cost_compare:
      ∃ k, ∀ x y, cost_compare x y <= k.
    Proof.
      destruct timed_op_ea.bound_cost_compare as [k1 H1].
      destruct timed_ea.bound_cost_compare as [k2 H2].
      
      exists (
        compare_branch1  +
        compare_branch2  +
        compare_branch3  +
        k1 + k2
      ).

      intros.

      destruct x; destruct y; unfold cost_compare. simpl.
      pose (H1 o o0).
      pose (H2 c c0).

      destruct (opea_as_OT.compare o o0); lia.
    Qed.

    Program Definition compare' x y 
    :{! res !:! _ !<! c !>! c = cost_compare x y
      /\ res = compare x y !}
    :=
      out1 <- timed_op_ea.compare' (fst x) (fst y);
      out <- match out1 as out1' return (out1=out1')->
      {! res !:! _ !<! c !>! c = 
        match out1 with 
        | Eq => compare_branch1 + 
            timed_ea.cost_compare (snd x) (snd y)
        | Lt => compare_branch2
        | Gt => compare_branch3
        end
      /\ res = match out1
          with 
          | Eq => (ea_as_OT.compare (snd x) (snd y)) 
          | Lt => Lt 
          | Gt => Gt 
          end !}
      with 
      | Eq => 
        fun hyp =>
        out <- timed_ea.compare' (snd x) (snd y);
        += compare_branch1;
        <== out
      | Lt => 
        fun hyp =>
        += compare_branch2;
        <== Lt 
      | Gt => 
        fun hyp =>
        += compare_branch3;
        <== Gt 
      end (eq_refl out1);
      <== out.

    Next Obligation.
      rewrite hyp.
      split; auto.
      simpl. lia.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      unfold cost_compare.

      simpl.
      split; auto.

      destruct (opea_as_OT.compare o0 o); lia.
      unfold compare.
      simpl.
      destruct (opea_as_OT.compare o0 o); auto.
    Defined.
(* end hide *)
  End timed_ra.

  Module timed_va_set.
      (* begin hide *)

    Fixpoint raw_equal s s' :=
      match s, s' with 
      | [], [] => true 
      | x::l, x'::l' => 
        match timed_ra.compare x x' with 
        | Eq => raw_equal l l' 
        | _ => false
        end
      | _, _ => false
      end.

    Lemma L_raw_equal: ∀ s s', 
      raw_equal s s' = va_set.Raw.equal s s'.
    Proof.
      easy.
    Qed.

    Definition cost_branch1 := 1.
    Definition cost_branch2 := 1.
    Definition cost_branch3 := 1.
    Definition cost_branch4 := 1.
    Opaque cost_branch1.
    Opaque cost_branch2.
    Opaque cost_branch3.
    Opaque cost_branch4.

    Fixpoint cost_raw_equal s s' :=
      match s, s' with 
      | [], [] => cost_branch1 
      | x::l, x'::l' => 
        timed_ra.cost_compare x x' +
        match timed_ra.compare x x' with 
        | Eq => 
          cost_branch2 + 
          cost_raw_equal l l' 
        | _ => cost_branch3
        end
      | _, _ => cost_branch4
      end.

    Lemma bound_cost_raw_equal: ∃ k b, ∀ s s',
      cost_raw_equal s s' <= k * |s| + b.
    Proof.
      destruct (timed_ra.bound_cost_compare) as [k H].
      exists 
        (cost_branch2+k), 
        (cost_branch1+cost_branch3+cost_branch4).

      intro s.
      induction s.
      simpl. destruct s'; lia.

      intro s'.
      simpl.
      destruct s'.
      lia.
      match goal with
      | |- _ ?a ?p + _ <= _ =>
      pose (H a p);
      destruct (timed_ra.compare a p)
      end. 
      pose (IHs s').
      all: lia.
    Qed.

    Program Fixpoint raw_equal' s s' 
      :{! y !:! _ !<! c !>! c = cost_raw_equal s s' /\ 
        y = raw_equal s s' !}
      :=
      match s as s1, s' as s2 return (s=s1)->(s'=s2)->
        {! y !:! _ !<! c !>! c = cost_raw_equal s s' /\ 
          y = raw_equal s s' !}
      with 
      | [], [] =>
        fun hyp1 hyp2 => += cost_branch1; <== true 
      | x::l, x'::l' =>
        fun hyp1 hyp2 => 
        out1 <- timed_ra.compare' x x';
        out<- match out1 as out1' return (out1=out1')->
          {! y !:! _ !<! c !>! 
            c = match out1 with 
            | Eq => 
              cost_branch2 + 
              cost_raw_equal l l' 
            | _ => cost_branch3
            end /\ 
            y = match out1 with 
                | Eq => raw_equal l l'
                | _ => false
                end !}
        with 
        | Eq =>
          fun hyp => 
          out <- raw_equal' l l';
          += cost_branch2;
          <== out
        | _ =>
          fun hyp => += cost_branch3; <== false
        end (eq_refl out1);
        <== out
      | _, _ =>
        fun hyp1 hyp2 => += cost_branch4; <== false
      end (eq_refl s) (eq_refl s').

    Next Obligation.
      rewrite hyp.
      split; auto. lia. 
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      unfold cost_raw_equal.
      split; auto.
      destruct (timed_ra.compare (o0, c0) (o, c));
      auto.
      unfold raw_equal.
      destruct (timed_ra.compare (o0, c0) (o, c));
      auto.
    Defined.

    Definition equal s s' := 
      raw_equal (va_set.this s) (va_set.this s').
    
    Lemma L_equal: ∀ s s', equal s s' = va_set.equal s s'.
    Proof.
      easy.
    Qed.

    Definition cost_equal s s' :=
      cost_raw_equal (va_set.this s) (va_set.this s').
    
    Lemma bound_cost_equal: ∃ k b, ∀ s s',
      cost_equal s s' <= k * (va_set.cardinal s) + b.
    Proof.
      destruct (bound_cost_raw_equal) as [k [b H]].
      exists k, b.
      intros.
      specialize H with (va_set.this s) (va_set.this s').
      unfold cost_equal. eauto.
    Qed.

    Definition equal' s s' 
    :{! y !:! _ !<! c !>! c = cost_equal s s' /\ y = equal s s' !}
    :=
      raw_equal' (va_set.this s) (va_set.this s').

(* end hide *)
  End timed_va_set.

  Module timed_rb.
      (* begin hide *)

    Definition vb_compare := vb_set.compare.

    Definition compare x y :=
      match (opea_as_OT.compare (fst x) (fst y))
      with 
      | Eq => (eb_as_OT.compare (snd x) (snd y)) 
      | Lt => Lt 
      | Gt => Gt 
      end.

    Lemma L_compare: ∀ x y,
      compare x y = rb_as_OT.compare x y.
    Proof.
      easy.
    Qed.

    Definition compare_branch1 := 1.
    Definition compare_branch2 := 1.
    Definition compare_branch3 := 1.
    Opaque compare_branch1.
    Opaque compare_branch2.
    Opaque compare_branch3.

    Definition cost_compare x y :=
      timed_op_ea.cost_compare (fst x) (fst y) + 
      match opea_as_OT.compare (fst x) (fst y) with 
      | Eq => compare_branch1 + 
          timed_eb.cost_compare (snd x) (snd y)
      | Lt => compare_branch2
      | Gt => compare_branch3
      end.

    Lemma bound_cost_compare:
      ∃ k, ∀ x y, cost_compare x y <= k.
    Proof.
      destruct timed_op_ea.bound_cost_compare as [k1 H1].
      destruct timed_eb.bound_cost_compare as [k2 H2].
      
      exists (
        compare_branch1  +
        compare_branch2  +
        compare_branch3  +
        k1 + k2
      ).

      intros.

      destruct x; destruct y; unfold cost_compare. simpl.
      pose (H1 o o0).
      pose (H2 r r0).

      destruct (opea_as_OT.compare o o0); lia.
    Qed.

    Program Definition compare' x y 
    :{! res !:! _ !<! c !>! c = cost_compare x y
      /\ res = compare x y !}
    :=
      out1 <- timed_op_ea.compare' (fst x) (fst y);
      out <- match out1 as out1' return (out1=out1')->
      {! res !:! _ !<! c !>! c = 
        match out1 with 
        | Eq => compare_branch1 + 
            timed_eb.cost_compare (snd x) (snd y)
        | Lt => compare_branch2
        | Gt => compare_branch3
        end
      /\ res = match out1
          with 
          | Eq => (eb_as_OT.compare (snd x) (snd y)) 
          | Lt => Lt 
          | Gt => Gt 
          end !}
      with 
      | Eq => 
        fun hyp =>
        out <- timed_eb.compare' (snd x) (snd y);
        += compare_branch1;
        <== out
      | Lt => 
        fun hyp =>
        += compare_branch2;
        <== Lt 
      | Gt => 
        fun hyp =>
        += compare_branch3;
        <== Gt 
      end (eq_refl out1);
      <== out.

    Next Obligation.
      rewrite hyp.
      split; auto.
      simpl. lia.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      unfold cost_compare.

      simpl.
      split; auto.

      destruct (opea_as_OT.compare o0 o); lia.
      unfold compare.
      simpl.
      destruct (opea_as_OT.compare o0 o); auto.
    Defined.
(* end hide *)
  End timed_rb.

  Module timed_vb_set.
      (* begin hide *)

    Fixpoint raw_equal s s' :=
      match s, s' with 
      | [], [] => true 
      | x::l, x'::l' => 
        match timed_rb.compare x x' with 
        | Eq => raw_equal l l' 
        | _ => false
        end
      | _, _ => false
      end.

    Lemma L_raw_equal: ∀ s s', 
      raw_equal s s' = vb_set.Raw.equal s s'.
    Proof.
      easy.
    Qed.

    Definition cost_branch1 := 1.
    Definition cost_branch2 := 1.
    Definition cost_branch3 := 1.
    Definition cost_branch4 := 1.
    Opaque cost_branch1.
    Opaque cost_branch2.
    Opaque cost_branch3.
    Opaque cost_branch4.

    Fixpoint cost_raw_equal s s' :=
      match s, s' with 
      | [], [] => cost_branch1 
      | x::l, x'::l' => 
        timed_rb.cost_compare x x' +
        match timed_rb.compare x x' with 
        | Eq => 
          cost_branch2 + 
          cost_raw_equal l l' 
        | _ => cost_branch3
        end
      | _, _ => cost_branch4
      end.

    Lemma bound_cost_raw_equal: ∃ k b, ∀ s s',
      cost_raw_equal s s' <= k * |s| + b.
    Proof.
      destruct (timed_rb.bound_cost_compare) as [k H].
      exists 
        (cost_branch2+k), 
        (cost_branch1+cost_branch3+cost_branch4).

      intro s.
      induction s.
      simpl. destruct s'; lia.

      intro s'.
      simpl.
      destruct s'.
      lia.

      match goal with
      | |- ?cmp ?a ?p + _ <= _ =>
      pose (H a p)
      ; destruct (timed_rb.compare a p)
      end.

      pose (IHs s').
      lia.
      lia.
      lia.
    Qed.

    Program Fixpoint raw_equal' s s' 
      :{! y !:! _ !<! c !>! c = cost_raw_equal s s' /\ 
        y = raw_equal s s' !}
      :=
      match s as s1, s' as s2 return (s=s1)->(s'=s2)->
        {! y !:! _ !<! c !>! c = cost_raw_equal s s' /\ 
          y = raw_equal s s' !}
      with 
      | [], [] =>
        fun hyp1 hyp2 => += cost_branch1; <== true 
      | x::l, x'::l' =>
        fun hyp1 hyp2 => 
        out1 <- timed_rb.compare' x x';
        out<- match out1 as out1' return (out1=out1')->
          {! y !:! _ !<! c !>! 
            c = match out1 with 
            | Eq => 
              cost_branch2 + 
              cost_raw_equal l l' 
            | _ => cost_branch3
            end /\ 
            y = match out1 with 
                | Eq => raw_equal l l'
                | _ => false
                end !}
        with 
        | Eq =>
          fun hyp => 
          out <- raw_equal' l l';
          += cost_branch2;
          <== out
        | _ =>
          fun hyp => += cost_branch3; <== false
        end (eq_refl out1);
        <== out
      | _, _ =>
        fun hyp1 hyp2 => += cost_branch4; <== false
      end (eq_refl s) (eq_refl s').

    Next Obligation.
      rewrite hyp.
      split; auto. lia. 
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      unfold cost_raw_equal.
      split; auto.
      destruct (timed_rb.compare (o0, r0) (o, r));
      auto.
      unfold raw_equal.
      destruct (timed_rb.compare (o0, r0) (o, r));
      auto.
    Defined.

    Definition equal s s' := 
      raw_equal (vb_set.this s) (vb_set.this s').
    
    Lemma L_equal: ∀ s s', equal s s' = vb_set.equal s s'.
    Proof.
      easy.
    Qed.

    Definition cost_equal s s' :=
      cost_raw_equal (vb_set.this s) (vb_set.this s').
    
    Lemma bound_cost_equal: ∃ k b, ∀ s s',
      cost_equal s s' <= k * (vb_set.cardinal s) + b.
    Proof.
      destruct (bound_cost_raw_equal) as [k [b H]].
      exists k, b.
      intros.
      specialize H with (vb_set.this s) (vb_set.this s').
      unfold cost_equal. eauto.
    Qed.

    Definition equal' s s' 
    :{! y !:! _ !<! c !>! c = cost_equal s s' /\ y = equal s s' !}
    :=
      raw_equal' (vb_set.this s) (vb_set.this s').

(* end hide *)
  End timed_vb_set.

  Module timed_rc.
      (* begin hide *)

    Definition va_compare := va_set.compare.

    Definition compare x y :=
      match (opea_as_OT.compare (fst x) (fst y))
      with 
      | Eq => (ec_as_OT.compare (snd x) (snd y)) 
      | Lt => Lt 
      | Gt => Gt 
      end.

    Lemma L_compare: ∀ x y,
      compare x y = rc_as_OT.compare x y.
    Proof.
      easy.
    Qed.

    Definition compare_branch1 := 1.
    Definition compare_branch2 := 1.
    Definition compare_branch3 := 1.
    Opaque compare_branch1.
    Opaque compare_branch2.
    Opaque compare_branch3.

    Definition cost_compare x y :=
      timed_op_ea.cost_compare (fst x) (fst y) + 
      match opea_as_OT.compare (fst x) (fst y) with 
      | Eq => compare_branch1 + 
          timed_ec.cost_compare (snd x) (snd y)
      | Lt => compare_branch2
      | Gt => compare_branch3
      end.

    Lemma bound_cost_compare:
      ∃ k, ∀ x y, cost_compare x y <= k.
    Proof.
      destruct timed_op_ea.bound_cost_compare as [k1 H1].
      destruct timed_ec.bound_cost_compare as [k2 H2].
      
      exists (
        compare_branch1  +
        compare_branch2  +
        compare_branch3  +
        k1 + k2
      ).

      intros.

      destruct x; destruct y; unfold cost_compare. simpl.
      pose (H1 o o0).
      pose (H2 p0 p1).

      destruct (opea_as_OT.compare o o0); lia.
    Qed.

    Program Definition compare' x y 
    :{! res !:! _ !<! c !>! c = cost_compare x y
      /\ res = compare x y !}
    :=
      out1 <- timed_op_ea.compare' (fst x) (fst y);
      out <- match out1 as out1' return (out1=out1')->
      {! res !:! _ !<! c !>! c = 
        match out1 with 
        | Eq => compare_branch1 + 
            timed_ec.cost_compare (snd x) (snd y)
        | Lt => compare_branch2
        | Gt => compare_branch3
        end
      /\ res = match out1
          with 
          | Eq => (ec_as_OT.compare (snd x) (snd y)) 
          | Lt => Lt 
          | Gt => Gt 
          end !}
      with 
      | Eq => 
        fun hyp =>
        out <- timed_ec.compare' (snd x) (snd y);
        += compare_branch1;
        <== out
      | Lt => 
        fun hyp =>
        += compare_branch2;
        <== Lt 
      | Gt => 
        fun hyp =>
        += compare_branch3;
        <== Gt 
      end (eq_refl out1);
      <== out.

    Next Obligation.
      rewrite hyp.
      split; auto.
      simpl. lia.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      unfold cost_compare.

      simpl.
      split; auto.

      destruct (opea_as_OT.compare o0 o); lia.
      unfold compare.
      simpl.
      destruct (opea_as_OT.compare o0 o); auto.
    Defined.
(* end hide *)
  End timed_rc.

  Module timed_vc_set.
      (* begin hide *)

    Fixpoint raw_equal s s' :=
      match s, s' with 
      | [], [] => true 
      | x::l, x'::l' => 
        match timed_rc.compare x x' with 
        | Eq => raw_equal l l' 
        | _ => false
        end
      | _, _ => false
      end.

    Lemma L_raw_equal: ∀ s s', 
      raw_equal s s' = vc_set.Raw.equal s s'.
    Proof.
      easy.
    Qed.

    Definition cost_branch1 := 1.
    Definition cost_branch2 := 1.
    Definition cost_branch3 := 1.
    Definition cost_branch4 := 1.
    Opaque cost_branch1.
    Opaque cost_branch2.
    Opaque cost_branch3.
    Opaque cost_branch4.

    Fixpoint cost_raw_equal s s' :=
      match s, s' with
      | [], [] => cost_branch1 
      | x::l, x'::l' => 
        timed_rc.cost_compare x x' +
        match timed_rc.compare x x' with 
        | Eq => 
          cost_branch2 + 
          cost_raw_equal l l' 
        | _ => cost_branch3
        end
      | _, _ => cost_branch4
      end.

    Lemma bound_cost_raw_equal: ∃ k b, ∀ s s',
      cost_raw_equal s s' <= k * |s| + b.
    Proof.
      destruct (timed_rc.bound_cost_compare) as [k H].
      exists 
        (cost_branch2+k), 
        (cost_branch1+cost_branch3+cost_branch4).

      intro s.
      induction s.
      simpl. destruct s'; lia.

      intro s'.
      simpl.
      destruct s'.
      lia.
      match goal with
      | |- ?cmp ?a ?p + _ <= _ =>
      pose (H a p)
      ; destruct (timed_rc.compare a p)
      end.
      pose (IHs s').
      lia.
      lia.
      lia.
    Qed.

    Program Fixpoint raw_equal' s s' 
      :{! y !:! _ !<! c !>! c = cost_raw_equal s s' /\ 
        y = raw_equal s s' !}
      :=
      match s as s1, s' as s2 return (s=s1)->(s'=s2)->
        {! y !:! _ !<! c !>! c = cost_raw_equal s s' /\ 
          y = raw_equal s s' !}
      with 
      | [], [] =>
        fun hyp1 hyp2 => += cost_branch1; <== true 
      | x::l, x'::l' =>
        fun hyp1 hyp2 => 
        out1 <- timed_rc.compare' x x';
        out<- match out1 as out1' return (out1=out1')->
          {! y !:! _ !<! c !>! 
            c = match out1 with 
            | Eq => 
              cost_branch2 + 
              cost_raw_equal l l' 
            | _ => cost_branch3
            end /\ 
            y = match out1 with 
                | Eq => raw_equal l l'
                | _ => false
                end !}
        with 
        | Eq =>
          fun hyp => 
          out <- raw_equal' l l';
          += cost_branch2;
          <== out
        | _ =>
          fun hyp => += cost_branch3; <== false
        end (eq_refl out1);
        <== out
      | _, _ =>
        fun hyp1 hyp2 => += cost_branch4; <== false
      end (eq_refl s) (eq_refl s').

    Next Obligation.
      rewrite hyp.
      split; auto. lia. 
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      rewrite hyp.
      split; auto.
    Defined.

    Next Obligation.
      unfold cost_raw_equal.
      split; auto.

      match goal with
      | h: ?x = ?x |- _  =>
        destruct (x);
        auto
      end. 

      unfold raw_equal.

      match goal with
      | h: ?x = ?x |- _  =>
        destruct (x);
        auto
      end. 

    Defined.

    Definition equal s s' := 
      raw_equal (vc_set.this s) (vc_set.this s').
    
    Lemma L_equal: ∀ s s', equal s s' = vc_set.equal s s'.
    Proof.
      easy.
    Qed.

    Definition cost_equal s s' :=
      cost_raw_equal (vc_set.this s) (vc_set.this s').
    
    Lemma bound_cost_equal: ∃ k b, ∀ s s',
      cost_equal s s' <= k * (vc_set.cardinal s) + b.
    Proof.
      destruct (bound_cost_raw_equal) as [k [b H]].
      exists k, b.
      intros.
      specialize H with (vc_set.this s) (vc_set.this s').
      unfold cost_equal. eauto.
    Qed.

    Definition equal' s s' 
    :{! y !:! _ !<! c !>! c = cost_equal s s' /\ y = equal s s' !}
    :=
      raw_equal' (vc_set.this s) (vc_set.this s').

(* end hide *)
  End timed_vc_set.

  Module va_of_list.
      (* begin hide *)


    Fixpoint va_set_raw_add
      (x : option CalEdge * CalEdge) 
      (s : list (option CalEdge * CalEdge))
    := 
    match s with 
    | [] => [x]
    | y::l =>
      match ra_as_OT.compare x y with
      | Eq => s
      | Lt => x :: s
      | Gt => y :: va_set_raw_add x l
      end
    end.

    Lemma L_va_set_raw_add: ∀ x s, 
      va_set_raw_add x s = va_set.Raw.add x s.
    Proof.
      intros.
      induction s; simpl; eauto.
    Qed.

    Definition cost_va_set_raw_add_branch1 := 1.
    Definition cost_va_set_raw_add_branch2 := 1.
    Definition cost_va_set_raw_add_branch3 := 1.
    Definition cost_va_set_raw_add_branch4 := 1.
    Definition cost_va_set_raw_add_branch5 := 1.

    Opaque cost_va_set_raw_add_branch1.
    Opaque cost_va_set_raw_add_branch2.
    Opaque cost_va_set_raw_add_branch3.
    Opaque cost_va_set_raw_add_branch4.
    Opaque cost_va_set_raw_add_branch5.

    Opaque cons_ct.

    Fixpoint cost_va_set_raw_add
      (x : option CalEdge * CalEdge) 
      (s : list (option CalEdge * CalEdge))
    := 
    match s with 
    | [] => cons_ct + cost_va_set_raw_add_branch1
    | y::l =>
      match ra_as_OT.compare x y with
      | Eq => cost_va_set_raw_add_branch2
      | Lt => cons_ct + cost_va_set_raw_add_branch3
      | Gt => cons_ct + cost_va_set_raw_add_branch4 + 
        cost_va_set_raw_add x l
      end
    end.

    Program Fixpoint va_set_raw_add'
      (x : option CalEdge * CalEdge) 
      (s : list (option CalEdge * CalEdge))
    :{! y !:! _ !<! c !>! c = cost_va_set_raw_add x s /\ 
        y = va_set_raw_add x s !}
    := 
    match s as s' return (s=s')->
      {! y !:! _ !<! c !>! c = cost_va_set_raw_add x s /\ 
          y = va_set_raw_add x s !}
      with 
      | [] => 
        fun hyp =>
        out <- cons' _ x nil;
        += cost_va_set_raw_add_branch1;
        <== out
      | y::l =>
        fun hyp =>
        match ra_as_OT.compare x y with
        | Eq => 
          += cost_va_set_raw_add_branch2; <== s
        | Lt => 
            out <- cons' _ x s; 
            += cost_va_set_raw_add_branch3; <== out
        | Gt => 
          out1 <- va_set_raw_add' x l;
          out2 <- cons' _ y out1;
          += cost_va_set_raw_add_branch4; <== out2
        end
    end (eq_refl s).

    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous. auto.
    Defined.

    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous. auto.
    Defined.

    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous.
      split; auto. lia.
    Defined.

    Definition va_set_add
      (s : va_set.t) (x : va_set.elt) :=
      match s with
      | {| va_set.this := this; va_set.is_ok := is_ok |} =>
        {|
          va_set.this := va_set_raw_add x this;
          (* NOTE add_ok returns a property *)
          va_set.is_ok := va_set.Raw.add_ok (s:= this) x is_ok
        |}
      end.

    Definition cost_va_set_add_branch1 := 1.
    Opaque cost_va_set_add_branch1.

    Definition cost_va_set_add (s : va_set.t) (x : va_set.elt) 
    := 
    match s with
    | {| va_set.this := this; va_set.is_ok := is_ok |} =>
      cost_va_set_add_branch1 +
      cost_va_set_raw_add x this
    end.

    Program Definition va_set_add' (s : va_set.t) (x : va_set.elt)
    : {! res !:! va_set.t !<! c !>! c = cost_va_set_add s x
      /\ res = va_set_add s x !}
    :=
      match s with
      | {| va_set.this := this; va_set.is_ok := is_ok |} =>
        out <- va_set_raw_add' x this;
        += cost_va_set_add_branch1;
        <== {|
          va_set.this := out;
          (* NOTE add_ok returns a property *)
          va_set.is_ok := va_set.Raw.add_ok (s:=this) x is_ok
        |}
      end.

    Next Obligation.
      split; auto.
      lia.
    Defined.

    Lemma L_va_set_add: ∀ x s,
      va_set_add x s = va_set.add s x.
    Proof.
      intros.
      unfold va_set_add.
      destruct s.
      destruct x.
      easy.
    Qed.

    Definition cost_va_of_list va :=
      @cost_fold va_set.t va_set.elt
      va_set_add cost_va_set_add
      va va_set.empty.

    Program Definition va_of_list' va 
    :{! y !:! _ !<! c !>! 
      c = cost_va_of_list va /\ 
      y = va_of_list va !}
    := 
      out <- fold' va_set.t va_set.elt va_set_add' va va_set.empty;
      <== out.

    Next Obligation.
      split; auto.
      unfold va_of_list.

      generalize va_set.empty.
      induction va; intros.
      simpl; auto.
      simpl; auto.
      rmDirect.

      rewrite L_va_set_add.
      specialize H with (va_set.add a t).
      easy.
    Qed.

(* end hide *)
  End va_of_list. 

  Section vb_of_list.
      (* begin hide *)

    Definition vb_compare := vb_set.compare.

    Definition cost_eb_as_OT__compare_branch1 := 1.
    Definition cost_eb_as_OT__compare_branch2 := 1.
    Definition cost_eb_as_OT__compare_branch3 := 1.
    Definition cost_eb_as_OT__compare_branch4 := 1.
    Definition cost_eb_as_OT__compare_branch5 := 1.
    Definition cost_eb_as_OT__compare_branch6 := 1.
    Definition cost_eb_as_OT__compare_branch7 := 1.
    Definition cost_eb_as_OT__compare_branch8 := 1.
    Definition cost_eb_as_OT__compare_branch9 := 1.
    Definition cost_eb_as_OT__compare_branch10 := 1.

    Opaque cost_eb_as_OT__compare_branch1.
    Opaque cost_eb_as_OT__compare_branch2.
    Opaque cost_eb_as_OT__compare_branch3.
    Opaque cost_eb_as_OT__compare_branch4.
    Opaque cost_eb_as_OT__compare_branch5.
    Opaque cost_eb_as_OT__compare_branch6.
    Opaque cost_eb_as_OT__compare_branch7.
    Opaque cost_eb_as_OT__compare_branch8.
    Opaque cost_eb_as_OT__compare_branch9.
    Opaque cost_eb_as_OT__compare_branch10.
    Opaque cost_compare_str.
    Opaque cost_compare_vv.

    Definition cost_eb_as_OT__compare x y :=
      match x, y with
      | PndRetE _ _ _, MatRetE _ _ _ _ _ =>
        cost_eb_as_OT__compare_branch1
      | PndRetE L1 a L2, PndRetE L1' a' L2' =>
        cost_eq_str + cost_negb +
        if negb (eq_str a a') then
          cost_compare_str + cost_eb_as_OT__compare_branch2
        else 
        cost_eqvv L1 L1' + cost_negb +
        if negb (eqvv L1 L1') then
          cost_compare_vv L1 L1' + cost_eb_as_OT__compare_branch3
        else
          cost_compare_vv L2 L2' + cost_eb_as_OT__compare_branch4
      | MatRetE L1 a L2 b L3, MatRetE L1' a' L2' b' L3' =>
        cost_eq_str + cost_negb +
        if negb (eq_str a a') then
          cost_compare_str
          + cost_eb_as_OT__compare_branch5
        else
        cost_eq_str + cost_negb +
        if negb (eq_str b b') then
          cost_compare_str +
          cost_eb_as_OT__compare_branch6 else
        cost_eqvv L1 L1' + cost_negb +
        if negb (eqvv L1 L1') then
          cost_compare_vv L1 L1' + cost_eb_as_OT__compare_branch7 else
        cost_eqvv L2 L2' + cost_negb +
        if negb (eqvv L2 L2') then
          cost_compare_vv L2 L2' + cost_eb_as_OT__compare_branch8 else
          cost_compare_vv L3 L3' + cost_eb_as_OT__compare_branch9
      | _, _ =>
        cost_eb_as_OT__compare_branch10
      end.

    Program Definition eb_as_OT__compare' a b
    :{! y !:! comparison !<! c !>! 
      c = cost_eb_as_OT__compare a b /\ 
      y = eb_as_OT.compare a b !}
    :=
      match a as a', b as b' return
        (a=a')->(b=b')->
        {! y !:! comparison !<! c !>! 
          c = cost_eb_as_OT__compare a b /\ 
          y = eb_as_OT.compare a b !}
      with 
      | PndRetE _ _ _, MatRetE _ _ _ _ _ =>
        fun hyp1 hyp2 => 
        += cost_eb_as_OT__compare_branch1;
        <== Lt 
      | PndRetE L1 a L2, PndRetE L1' a' L2' =>
        fun hyp1 hyp2 =>
        if dec (negb (eq_str a a')) then
          += cost_negb + cost_eq_str +
          cost_compare_str +
          cost_eb_as_OT__compare_branch2;
          <== compare_str a a'
        else 
        res <- eqvv' L1 L1';
        if dec (negb res) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str + cost_negb
          + cost_eb_as_OT__compare_branch3;
          <== out
        else
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str + cost_negb
          + cost_eb_as_OT__compare_branch4;
          <== out
      | MatRetE L1 a L2 b L3, MatRetE L1' a' L2' b' L3' =>
        fun hyp1 hyp2 => 
        if dec (negb (eq_str a a')) then
          += cost_negb + cost_eq_str +
          cost_compare_str +
          cost_eb_as_OT__compare_branch5;
          <== compare_str a a' else
        if dec (negb (eq_str b b')) then
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str +
          cost_compare_str +
          cost_eb_as_OT__compare_branch6;
          <== compare_str b b' else
        if dec (negb (eqvv L1 L1')) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' +
          cost_eb_as_OT__compare_branch7;
          <== out else
        if dec (negb (eqvv L2 L2')) then 
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str +
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' +
          cost_negb + cost_eqvv L2 L2' +
          cost_eb_as_OT__compare_branch8;
          <== out else 
        out <- compare_vv' L3 L3';
        += cost_negb + cost_eq_str +
        cost_negb + cost_eq_str + 
        cost_negb + cost_eqvv L1 L1' +
        cost_negb + cost_eqvv L2 L2' +
        cost_eb_as_OT__compare_branch9;
        <== out
      | _, _ =>
        fun hyp1 hyp2 => 
        += cost_eb_as_OT__compare_branch10;
        <== Gt
      end (eq_refl a) (eq_refl b).

    Next Obligation.
      split; auto.
      unfold cost_eb_as_OT__compare.
      rewrite e. lia.
      simpl.
      rewrite e.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      rewrite e0.
      split; auto.
      replace vpg.cost_eqvv with cost_eqvv; auto.

      lia.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      rewrite e0.
      auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_eb_as_OT__compare.
      rewrite e. lia.
      simpl.
      rewrite e. auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_eb_as_OT__compare.
      rewrite e.
      rewrite e0.
      lia.
      simpl.
      rewrite e.
      rewrite e0. auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_eb_as_OT__compare.
      rewrite e.
      rewrite e0.
      rewrite e1.

      lia.
      simpl.
      rewrite e.
      rewrite e0.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
        rewrite e1.
      
      auto.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1'); auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_eb_as_OT__compare.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      lia.

      simpl.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      auto.
    Qed.

    Next Obligation.
      split; auto.
      unfold cost_eb_as_OT__compare.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      lia.

      simpl.
      rewrite e.
      rewrite e0.
      rewrite e1.
      rewrite e2.
      auto.
    Qed.


    Definition rb_as_OT_compare x y :=
      PositiveSet.lex 
      (opea_as_OT.compare (fst x) (fst y)) (eb_as_OT.compare (snd x) (snd y)).

    Lemma L_rb_as_OT_compare: ∀ x y,
      rb_as_OT_compare x y = rb_as_OT.compare x y.
    Proof.
      easy.
    Qed.


    Fixpoint vb_set_raw_add
      (x : option CalEdge * RetEdge) 
      (s : list (option CalEdge * RetEdge))
    := 
    match s with 
    | [] => [x]
    | y::l =>
      match rb_as_OT.compare x y with
      | Eq => s
      | Lt => x :: s
      | Gt => y :: vb_set_raw_add x l
      end
    end.

    Lemma L_vb_set_raw_add: ∀ x s, 
      vb_set_raw_add x s = vb_set.Raw.add x s.
    Proof.
      intros.
      induction s; simpl; eauto.
    Qed.

    Definition cost_vb_set_raw_add_branch1 := 1.
    Definition cost_vb_set_raw_add_branch2 := 1.
    Definition cost_vb_set_raw_add_branch3 := 1.
    Definition cost_vb_set_raw_add_branch4 := 1.
    Definition cost_vb_set_raw_add_branch5 := 1.

    Opaque cost_vb_set_raw_add_branch1.
    Opaque cost_vb_set_raw_add_branch2.
    Opaque cost_vb_set_raw_add_branch3.
    Opaque cost_vb_set_raw_add_branch4.
    Opaque cost_vb_set_raw_add_branch5.

    Opaque cons_ct.

    Fixpoint cost_vb_set_raw_add
      (x : option CalEdge * RetEdge) 
      (s : list (option CalEdge * RetEdge))
    := 
    match s with 
    | [] => cons_ct + cost_vb_set_raw_add_branch1
    | y::l =>
      match rb_as_OT.compare x y with
      | Eq => cost_vb_set_raw_add_branch2
      | Lt => cons_ct + cost_vb_set_raw_add_branch3
      | Gt => cons_ct + cost_vb_set_raw_add_branch4 + 
        cost_vb_set_raw_add x l
      end
    end.

    Program Fixpoint vb_set_raw_add'
      (x : option CalEdge * RetEdge) 
      (s : list (option CalEdge * RetEdge))
    :{! y !:! _ !<! c !>! c = cost_vb_set_raw_add x s /\ 
        y = vb_set_raw_add x s !}
    := 
    match s as s' return (s=s')->
      {! y !:! _ !<! c !>! c = cost_vb_set_raw_add x s /\ 
          y = vb_set_raw_add x s !}
      with 
      | [] => 
        fun hyp =>
        out <- cons' _ x nil;
        += cost_vb_set_raw_add_branch1;
        <== out
      | y::l =>
        fun hyp =>
        match rb_as_OT.compare x y with
        | Eq => 
          += cost_vb_set_raw_add_branch2; <== s
        | Lt => 
            out <- cons' _ x s; 
            += cost_vb_set_raw_add_branch3; <== out
        | Gt => 
          out1 <- vb_set_raw_add' x l;
          out2 <- cons' _ y out1;
          += cost_vb_set_raw_add_branch4; <== out2
        end
    end (eq_refl s).

    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous. auto.
    Defined.

    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous. auto.
    Defined.

    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous.
      split; auto. lia.
    Defined.

    Definition vb_set_add
      (s : vb_set.t) (x : vb_set.elt) :=
      match s with
      | {| vb_set.this := this; vb_set.is_ok := is_ok |} =>
        {|
          vb_set.this := vb_set_raw_add x this;
          (* NOTE add_ok returns a property *)
          vb_set.is_ok := vb_set.Raw.add_ok (s:= this) x is_ok
        |}
      end.

    Definition cost_vb_set_add_branch1 := 1.
    Opaque cost_vb_set_add_branch1.

    Definition cost_vb_set_add (s : vb_set.t) (x : vb_set.elt) 
    := 
    match s with
    | {| vb_set.this := this; vb_set.is_ok := is_ok |} =>
      cost_vb_set_add_branch1 +
      cost_vb_set_raw_add x this
    end.

    Program Definition vb_set_add' (s : vb_set.t) (x : vb_set.elt)
    : {! res !:! vb_set.t !<! c !>! c = cost_vb_set_add s x
      /\ res = vb_set_add s x !}
    :=
      match s with
      | {| vb_set.this := this; vb_set.is_ok := is_ok |} =>
        out <- vb_set_raw_add' x this;
        += cost_vb_set_add_branch1;
        <== {|
          vb_set.this := out;
          (* NOTE add_ok returns a property *)
          vb_set.is_ok := vb_set.Raw.add_ok (s:=this) x is_ok
        |}
      end.

    Next Obligation.
      split; auto.
      lia.
    Defined.

    Lemma L_vb_set_add: ∀ x s,
      vb_set_add x s = vb_set.add s x.
    Proof.
      intros.
      unfold vb_set_add.
      destruct s.
      destruct x.
      easy.
    Qed.

    Definition cost_vb_of_list vb :=
      @cost_fold vb_set.t vb_set.elt
      vb_set_add cost_vb_set_add
      vb vb_set.empty.

    Program Definition vb_of_list' vb 
    :{! y !:! _ !<! c !>! 
      c = cost_vb_of_list vb /\ 
      y = vb_of_list vb !}
    := 
      out <- fold' vb_set.t vb_set.elt vb_set_add' vb vb_set.empty;
      <== out.

    Next Obligation.
      split; auto.
      unfold vb_of_list.

      generalize vb_set.empty.
      induction vb; intros.
      simpl; auto.
      simpl; auto.
      rmDirect.

      rewrite L_vb_set_add.
      specialize H with (vb_set.add a t).
      easy.
    Qed.

(* end hide *)
  End vb_of_list.

  Section vc_of_list.
      (* begin hide *)
    Definition vc_compare := vc_set.compare.
    
    Definition cost_ec_as_OT__compare_branch1 := 1.
    Definition cost_ec_as_OT__compare_branch2 := 1.
    Definition cost_ec_as_OT__compare_branch3 := 1.
    
    Opaque cost_ec_as_OT__compare_branch1.
    Opaque cost_ec_as_OT__compare_branch2.
    Opaque cost_ec_as_OT__compare_branch3.
    Opaque cost_compare_str.
    Opaque cost_compare_vv.
    
    Definition cost_ec_as_OT__compare x y :=
      match x, y with 
      | PlnE L1 a L2, PlnE L1' a' L2' =>
        if negb (eq_str a a') then 
          cost_negb + cost_eq_str + 
          cost_ec_as_OT__compare_branch1
        else if negb (vvot.eqb L1 L1') then 
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' + 
          cost_compare_vv L1 L1' +
          cost_ec_as_OT__compare_branch2
        else
          cost_negb + cost_eq_str + 
          cost_negb + cost_eqvv L1 L1' + 
          cost_compare_vv L2 L2' +
          cost_ec_as_OT__compare_branch3
      end.
    
    Program Definition ec_as_OT__compare' a b
    :{! y !:! comparison !<! c !>! 
      c = cost_ec_as_OT__compare a b /\ 
      y = ec_as_OT.compare a b !}
    :=
      match a as a', b as b' return
        (a=a')->(b=b')->
        {! y !:! comparison !<! c !>! 
          c = cost_ec_as_OT__compare a b /\ 
          y = ec_as_OT.compare a b !}
      with 
      | PlnE L1 a L2, PlnE L1' a' L2' =>
        fun hyp1 hyp2 => 
        if dec (negb (eq_str a a')) then 
          += cost_negb + cost_eq_str + 
          cost_ec_as_OT__compare_branch1;
          <== compare_str a a'
        else 
        out <- eqvv' L1 L1';
        if dec (negb out) then 
          out <- compare_vv' L1 L1';
          += cost_negb + cost_eq_str + 
          cost_negb +
          cost_ec_as_OT__compare_branch2;
          <== out
        else
          out <- compare_vv' L2 L2';
          += cost_negb + cost_eq_str + 
          cost_negb + cost_ec_as_OT__compare_branch3;
          <== out
      end (eq_refl a) (eq_refl b).
    
    Next Obligation.
      split; auto.
      unfold cost_ec_as_OT__compare.
      rewrite e. lia.
      simpl.
      rewrite e.
      auto.
    Qed.
    
    Next Obligation.
      simpl.
      rewrite e.
      replace vpg.cost_eqvv with cost_eqvv; auto.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      
      rewrite e0.
      split; auto.
    
      lia.
    Qed.

    Next Obligation.
      simpl.
      rewrite e.
      replace vpg.cost_eqvv with cost_eqvv; auto.
      replace (vvot.eqb L1 L1') with (eqvv L1 L1').
      
      rewrite e0.
      split; auto.
    
      lia.
    Qed.
    
    Definition rc_as_OT_compare x y :=
      PositiveSet.lex 
      (opea_as_OT.compare (fst x) (fst y)) (ec_as_OT.compare (snd x) (snd y)).
    
    Lemma L_rc_as_OT_compare: ∀ x y,
      rc_as_OT_compare x y = rc_as_OT.compare x y.
    Proof.
      easy.
    Qed.
    
    
    Fixpoint vc_set_raw_add
      (x : option CalEdge * PlnEdge) 
      (s : list (option CalEdge * PlnEdge))
    := 
    match s with 
    | [] => [x]
    | y::l =>
      match rc_as_OT.compare x y with
      | Eq => s
      | Lt => x :: s
      | Gt => y :: vc_set_raw_add x l
      end
    end.
    
    Lemma L_vc_set_raw_add: ∀ x s, 
      vc_set_raw_add x s = vc_set.Raw.add x s.
    Proof.
      intros.
      induction s; simpl; eauto.
    Qed.
    
    Definition cost_vc_set_raw_add_branch1 := 1.
    Definition cost_vc_set_raw_add_branch2 := 1.
    Definition cost_vc_set_raw_add_branch3 := 1.
    Definition cost_vc_set_raw_add_branch4 := 1.
    Definition cost_vc_set_raw_add_branch5 := 1.
    
    Opaque cost_vc_set_raw_add_branch1.
    Opaque cost_vc_set_raw_add_branch2.
    Opaque cost_vc_set_raw_add_branch3.
    Opaque cost_vc_set_raw_add_branch4.
    Opaque cost_vc_set_raw_add_branch5.
    
    Opaque cons_ct.
    
    Fixpoint cost_vc_set_raw_add
      (x : option CalEdge * PlnEdge) 
      (s : list (option CalEdge * PlnEdge))
    := 
    match s with 
    | [] => cons_ct + cost_vc_set_raw_add_branch1
    | y::l =>
      match rc_as_OT.compare x y with
      | Eq => cost_vc_set_raw_add_branch2
      | Lt => cons_ct + cost_vc_set_raw_add_branch3
      | Gt => cons_ct + cost_vc_set_raw_add_branch4 + 
        cost_vc_set_raw_add x l
      end
    end.
    
    Program Fixpoint vc_set_raw_add'
      (x : option CalEdge * PlnEdge) 
      (s : list (option CalEdge * PlnEdge))
    :{! y !:! _ !<! c !>! c = cost_vc_set_raw_add x s /\ 
        y = vc_set_raw_add x s !}
    := 
    match s as s' return (s=s')->
      {! y !:! _ !<! c !>! c = cost_vc_set_raw_add x s /\ 
          y = vc_set_raw_add x s !}
      with 
      | [] => 
        fun hyp =>
        out <- cons' _ x nil;
        += cost_vc_set_raw_add_branch1;
        <== out
      | y::l =>
        fun hyp =>
        match rc_as_OT.compare x y with
        | Eq => 
          += cost_vc_set_raw_add_branch2; <== s
        | Lt => 
            out <- cons' _ x s; 
            += cost_vc_set_raw_add_branch3; <== out
        | Gt => 
          out1 <- vc_set_raw_add' x l;
          out2 <- cons' _ y out1;
          += cost_vc_set_raw_add_branch4; <== out2
        end
    end (eq_refl s).
    
    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous. auto.
    Defined.
    
    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous. auto.
    Defined.
    
    Next Obligation.
      simpl.
      rewrite <- Heq_anonymous.
      split; auto. lia.
    Defined.
    
    Definition vc_set_add
      (s : vc_set.t) (x : vc_set.elt) :=
      match s with
      | {| vc_set.this := this; vc_set.is_ok := is_ok |} =>
        {|
          vc_set.this := vc_set_raw_add x this;
          (* NOTE add_ok returns a property *)
          vc_set.is_ok := vc_set.Raw.add_ok (s:= this) x is_ok
        |}
      end.
    
    Definition cost_vc_set_add_branch1 := 1.
    Opaque cost_vc_set_add_branch1.
    
    Definition cost_vc_set_add (s : vc_set.t) (x : vc_set.elt) 
    := 
    match s with
    | {| vc_set.this := this; vc_set.is_ok := is_ok |} =>
      cost_vc_set_add_branch1 +
      cost_vc_set_raw_add x this
    end.
    
    Program Definition vc_set_add' (s : vc_set.t) (x : vc_set.elt)
    : {! res !:! vc_set.t !<! c !>! c = cost_vc_set_add s x
      /\ res = vc_set_add s x !}
    :=
      match s with
      | {| vc_set.this := this; vc_set.is_ok := is_ok |} =>
        out <- vc_set_raw_add' x this;
        += cost_vc_set_add_branch1;
        <== {|
          vc_set.this := out;
          (* NOTE add_ok returns a property *)
          vc_set.is_ok := vc_set.Raw.add_ok (s:=this) x is_ok
        |}
      end.
    
    Next Obligation.
      split; auto.
      lia.
    Defined.
    
    Lemma L_vc_set_add: ∀ x s,
      vc_set_add x s = vc_set.add s x.
    Proof.
      intros.
      unfold vc_set_add.
      destruct s.
      destruct x.
      easy.
    Qed.
    
    Definition cost_vc_of_list vc :=
      @cost_fold vc_set.t vc_set.elt
      vc_set_add cost_vc_set_add
      vc vc_set.empty.
    
    Program Definition vc_of_list' vc 
    :{! y !:! _ !<! c !>! 
      c = cost_vc_of_list vc /\ 
      y = vc_of_list vc !}
    := 
      out <- fold' vc_set.t vc_set.elt vc_set_add' vc vc_set.empty;
      <== out.
    
    Next Obligation.
      split; auto.
      unfold vc_of_list.
    
      generalize vc_set.empty.
      induction vc; intros.
      simpl; auto.
      simpl; auto.
      rmDirect.
    
      rewrite L_vc_set_add.
      specialize H with (vc_set.add a t).
      easy.
    Qed.

(* end hide *)
  End vc_of_list.

End TimedSets.
