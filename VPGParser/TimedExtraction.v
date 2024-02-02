(** This file defines the monadic function [extract'] and summarizes the
    verified properties of the parser generator. *)

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

Require Import TimedExtractionRet.

Module TimedExtraction (G:Def.VPG).

  Module TimedExtractionRet := TimedExtractionRet (G).

  Import TimedExtractionRet.
  Import TimedExtractionCal.
  Import TimedExtractionPln.
  Import ExtractionWNoDup.
  Import Transducer.TimedSets.Parser.PreTimed.
  Import Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Tacs.
  Import Transducer.TimedSets.Parser.
  Import Transducer.TimedSets.
  Import Transducer.PreTransducer.
  Import Transducer.Transducer2.

  (** [cost_extraction_one_step]: the time cost of the one-step
      extraction function [f_b]. *)
  Definition cost_extraction_one_step m V :=
    match m with
    | PlnCME m => cost_inner_Pln m V
    | CalCME m => cost_inner_Cal m V
    | RetCME m => cost_inner     m V
    end.

  (** [cost_extraction_one_step]: the time cost of the one-step
      extraction function [f_b] is O(|m|·|m|·|V|). *)
  Lemma bound_cost_extraction_one_step: ∃ k k1 b1 b2, ∀ V m, 
    cost_extraction_one_step m V 
      <= (k * ||m|| * ||m|| + k1 * ||m|| + b1) * |V| + b2.
  (* begin hide *)
  Proof.
    destruct (bound_cost_inner_Pln) as [kc [k1 [b1 [b2 h1]]]].
    destruct (bound_cost_inner_Cal) as [ka [k1' [b1' [b2' h1']]]].
    destruct (bound_cost_inner_Ret) as [kb [k1'' [b1'' [b2'' h1'']]]].

    exists (kc + ka + kb).
    exists (k1 + k1' + k1'').
    exists (b1 + b1' + b1'').
    exists (b2 + b2' + b2'').

    intros.
    destruct m as [m | m | m].
    specialize h1' with m V; simpl; lia.
    specialize h1 with m V; simpl; lia.
    specialize h1'' with m V; simpl; lia.
  Qed.
  (* end hide *)

  (** [extraction_one_step]: this version of [f_b] provides a different
      implementation for simpler running-time verification. *)
  Definition extraction_one_step
    (m:ME) (V:list (list VE * list RetEdge)) :=
    match m with
    | PlnCME m => inner_Pln m V
    | CalCME m => inner_Cal m V
    | RetCME m => inner     m V
    end.

  (** [extraction_one_step']: the monadic version of
      [extraction_one_step]. *)
  Program Definition extraction_one_step'
    (m:ME) (V:list (list VE * list RetEdge))
    : {! y !:! list (list VE * list RetEdge) !<! c !>! 
      c = cost_extraction_one_step m V /\ y = extraction_one_step m V !}
    :=
    match m with
    | PlnCME m => out <- inner_Pln' m V; <== out
    | CalCME m => out <- inner_Cal' m V; <== out
    | RetCME m => out <- inner'     m V; <== out
    end.

  (** [L_ex_fb]: verify that [extraction_one_step] is a different
      version of [f_b]. *)
  Lemma L_ex_fb: ∀ m V, extraction_one_step m V = f_b m V.
  (* begin hide *)
  Proof.
    intros.
    unfold f_b.
    destruct m; simpl; eauto.
  Qed.
  (* end hide *)


  (** [cost_extraction_bt]: the branch time for the base case of the
      function [extraction']. *)
  Definition cost_extraction_bt    := 1.
  (** [cost_extraction_inner]: the branch time for the second case of
      the function [extraction']. *)
  Definition cost_extraction_inner := 1.

  (** [cost_extraction]: the time cost of [extraction']. *)
  Fixpoint cost_extraction M V : nat :=
    match M with
    | [] => cost_extraction_bt 
    | m::M' =>
      match M' with 
      | [] => cost_extraction_bt
      | _ =>
        cost_extraction_one_step m V +
        let V' := extraction_one_step m V in 
        cost_extraction M' V' +
        cost_extraction_inner
      end
    end.

  (** [extraction']: the monadic version of [extraction]. *)
  Program Fixpoint extraction' M V
    : {! V' !:! list (list VE * list RetEdge) !<! c !>!
        c = cost_extraction M V /\ V' = extraction M V !}
  :=
    match M with
    | [] =>  
      (+= cost_extraction_bt; <== V)
    | cons m M' => 
      match M' with
      | [] =>
        (+= cost_extraction_bt; <== V)
      | _ =>
        V' <- extraction_one_step' m V;
        out <- extraction' M' V';
        += cost_extraction_inner; <== out
      end
    end.

  (* begin hide *)
  Next Obligation.
    destruct M'. contradiction.
    split;
    auto.
  Defined.

  Opaque cost_extraction_bt.
  Opaque cost_extraction_inner.
  (* end hide *)

  (** [cost_extraction_and_its_one_step]: the relation between the time
      cost of [extraction'] and [extraction_one_step']. *)
  Lemma cost_extraction_and_its_one_step: 
    ∀ x M V m,
    cost_extraction_one_step x (extraction (M ++ [x]) V) +
    cost_extraction (M ++ [x]) V + cost_extraction_inner =
    cost_extraction ((M ++ [x]) ++ [m]) V.
  (* begin hide *)
  Proof.
    intros.
    generalize dependent V.
    induction M; intros.
    simpl; eauto. lia.

    replace ((a :: M) ++ [x]) with (a :: (M ++ [x])); 
      eauto using app_comm_cons.
    replace ((a :: M ++ [x]) ++ [m]) with (a :: (M ++ [x]) ++ [m]); 
      eauto using app_comm_cons.
    unfold extraction at 1.

    assert (exists e y, e::y=M++[x]).
    1:{
      destruct M; simpl; eauto.
    }

    destruct H as [? [? ?]].
    rewrite <- H at 1.
    fold extraction.

    unfold cost_extraction at 1.
    rewrite <- H at 2.
    fold cost_extraction.

    unfold cost_extraction at 2.
    fold cost_extraction.


    assert (exists e y, e::y=(M ++ [x]) ++ [m]).
    1:{
      destruct M; simpl; eauto.
    }

    destruct H0 as [? [? ?]].
    rewrite <- H0.
    rewrite H0.

    repeat rewrite Nat.add_assoc.

    match goal with
    | |- ?hh =>
      assert (cost_extraction_one_step x 
        (extraction (M ++ [x]) (f_b a V)) +
          cost_extraction (M ++ [x]) (extraction_one_step a V) + 
        cost_extraction_inner =
      cost_extraction 
        ((M ++ [x]) ++ [m]) (extraction_one_step a V) -> hh)
      ; try lia
    end.
    tac_app.

    pose (IHM (extraction_one_step a V)) as hw.

    rewrite <- hw.

    rewrite <- (L_ex_fb). auto.
  Qed.
  (* end hide *)

  (* begin hide *)
  Lemma bound_cost_extraction_sub:
    ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    ∀ M1 M2,
      (M=M1++M2) ->
      |extraction M1 (f_init m)| <= |extraction M (f_init m)|.
  Proof.
    set (H:=1).
    intros.
    generalize dependent M1.
    induction M2; intros.

    1:{
      simpl.
      pose (bound_extraction).
      rewrite app_nil_r in H1. subst. eauto.
    }

    specialize IHM2 with (M1 ++ [a]).
    rewrite <- app_assoc in IHM2.
    simpl in *.
    rmDirect.

    pose (extraction_and_its_one_step).

    destruct M1. 
    
    1:{
      simpl in *. auto.
    }

    assert (m1::M1!=[]) as notnil by eauto using nil_cons
      ; destruct (exists_last notnil) as [? [? _s]]
      ; rewrite _s in *
      ; clear notnil _s
      ; repeat rewrite app_assoc in h.

    specialize e with (x:=x0) (M:=x) (V:=(f_init m)) (m:=a).
    rewrite <- e in H2.
    pose (bound_extraction).
    assert (| (extraction (x ++ [x0]) (f_init m)) |
      <= | (f_b x0 (extraction (x ++ [x0]) (f_init m))) |).
    
    1:{
      specialize l with (1:=H0) (M1:=x++[x0]) (m':=a) (M2:=M2).
      rewrite <- app_assoc in l. simpl in l. 
      rmDirect.
      rewrite <- (extraction_and_its_one_step) in H3.
      auto.
    }
    lia.

  Qed.

  Definition map_r_to_edge1 := fun rule =>
    match rule with
    | (L, alt) =>
      match alt with
      | Alt_Epsilon => None
      | Alt_Linear t v =>
        match t with 
        | Call a  => Some (Calv (PndCalE L a v))
        | Ret b   => Some (Retv (PndRetE L b v))
        | Plain c => Some (Plnv (PlnE    L c v))
        end
      | Alt_Match t1 t2 v1 v2 =>
        Some (Calv (MatCalE L t1 v1 t2 v2))
      end
    end.

  Definition map_r_to_edge2 := fun rule =>
    match rule with
    | (L, alt) =>
      match alt with
      | Alt_Epsilon => None
      | Alt_Linear t v =>
        match t with 
        | Call a  => Some (Calv (PndCalE L a v))
        | Ret b   => Some (Retv (PndRetE L b v))
        | Plain c => Some (Plnv (PlnE    L c v))
        end
      | Alt_Match t1 t2 v1 v2 =>
        Some (Retv (MatRetE L t1 v1 t2 v2))
      end
    end.

  Definition map_P_to_edge :=
    (map map_r_to_edge1 P) ++ (map map_r_to_edge2 P).

  Lemma L_map_P_to_edge: ∀ r, In r P -> 
    In (map_r_to_edge1 r) (map_P_to_edge) /\
    In (map_r_to_edge2 r) (map_P_to_edge).
  Proof.
    intros.
    unfold map_P_to_edge.
    getAnd; apply in_or_app.
    left; apply_in_map; eauto.
    right; apply_in_map; eauto.
  Qed.

  Ltac convert_r_to_edge :=
    match goal with
    | h:in_rules ?r ?P |- _ =>
      pose (L_map_P_to_edge r) as _h
      ; rmDirect
    end.

  Lemma L_bound_m_sub1: ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    ∀ x y, inRM (x,y) m -> In (Some y) map_P_to_edge.
  Proof.
    intros.
    pose (L_f_b_rules) as h.
    specialize h with (1:=H).
    getH. tac_app. eauto using app_cons_not_nil.
    clear h.
    specialize H1 with (1:=H0).

    destruct y.
    all: try destruct va;
      try destruct vc;
      try destruct vb.
    all: try convert_r_to_edge; breakAnd; eauto.
  Qed.

  Lemma L_bound_m_sub2: ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    ∀ x y, inRM (Some x,y) m -> In (Some (Calv x)) map_P_to_edge.
  Proof.
    intros.
    pose (L_f_b_rules2) as h.
    specialize h with (1:=H).
    getH. tac_app. eauto using app_cons_not_nil.
    clear h.
    specialize H1 with (1:=H0).
    simpl in H1.

    destruct x.
    all: try convert_r_to_edge; breakAnd; eauto.
  Qed.

  Definition m_to_PE m := 
    match m with 
    | CalCME m => 
      map (
        fun e =>
        match e with 
        | (Some r, e) => (Some (Calv r), Some (Calv e))
        | (None, e) => (None, Some (Calv e))
        end
      ) (va_set.elements m)
    | PlnCME m => 
      map (
        fun e =>
        match e with 
        | (Some r, e) => (Some (Calv r), Some (Plnv e))
        | (None, e) => (None, Some (Plnv e))
        end
      ) (vc_set.elements m)
    | RetCME m => 
      map (
        fun e =>
        match e with 
        | (Some r, e) => (Some (Calv r), (Some (Retv e)))
        | (None, e) => (None, (Some (Retv e)))
        end
      ) (vb_set.elements m)
    end.


  Lemma L_bound_m_sub3: ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    incl (m_to_PE m) (list_prod (None::map_P_to_edge) map_P_to_edge).
  Proof.
    intros.
    unfold incl.
    intros.
    destruct a as [x y].
    apply in_prod_iff.
    unfold m_to_PE in H0.
    destruct m; apply_in_map;
    destruct x;
    destruct x0;
    destruct o;
    try destruct v;
    breakTuple;
    try match goal with
    | h: Some _ = Some _ |- _ =>
      destruct h; repeat rmDirect
    end.

    all: getAnd.
    all: try match goal with
    | h: In (?x,?y) _ |- _ =>
      apply (L_bound_m_sub1 _ _ _ _ _ H x)
      ; simpl
      ; up_in; eauto
      ; apply In_InA
      ; eauto using ra_as_OT.eq_equiv
      ; eauto using rb_as_OT.eq_equiv
      ; eauto using rc_as_OT.eq_equiv
      ; fail
    end.
    
    all: try match goal with
    | h: In (Some ?x, ?c) _ |- _ =>
      constructor 2
      ; try apply (L_bound_m_sub2 _ _ _ _ _ H x (Calv c))
      ; try apply (L_bound_m_sub2 _ _ _ _ _ H x (Plnv c))
      ; try apply (L_bound_m_sub2 _ _ _ _ _ H x (Retv c))
      ; simpl
      ; up_in; eauto
      ; apply In_InA
      ; eauto using ra_as_OT.eq_equiv
      ; eauto using rb_as_OT.eq_equiv
      ; eauto using rc_as_OT.eq_equiv
    end.
    
    all: try easy.

    all: try (constructor; eauto; fail).
  Qed.

  Lemma len_m_sub : 
  ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    (NoDup (m_to_PE m)) ->
    |m_to_PE m| <= |list_prod (None::map_P_to_edge) map_P_to_edge|.
  Proof.
    intros.
    apply NoDup_incl_length; eauto using L_bound_m_sub3.
  Qed.

  Lemma L_bound_with_P: 
    |list_prod (None::map_P_to_edge) map_P_to_edge| = 
      (1+|P|+|P|)*(|P|+|P|).
  Proof.
    rewrite prod_length.
    unfold map_P_to_edge.
    simpl.
    rewrite app_length.
    rewrite map_length.
    rewrite map_length.
    auto.
  Qed.

  Lemma L31: ∀ A B (l:list (A*B)), 
    NoDupA (eq*eq)%signature l -> NoDup l .
  Proof.
    intros.
    induction l. constructor.
    inversion H; subst. rmDirect.
    constructor 2; eauto.
    unfold not; intro.
    
    pose (In_InA _ H1).

    contradiction.
  Qed.

  Lemma L_nodup_m_m :
    ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    (NoDup (m_to_PE m)).
  Proof.
    intros.
    destruct m; simpl;
    match goal with
    | |- NoDup (map _ (?ele ?m)) =>
      assert (NoDup (ele m))
      ; [
        try pose (va_set.elements_spec2w m);
        try pose (vc_set.elements_spec2w m);
        try pose (vb_set.elements_spec2w m);
        apply L31; auto
      |]
    end.

    1:{
      set (a:=(va_set.elements ma)).
      fold a in H0.
      induction a. 
      simpl. constructor.
      rewrite map_cons. 
      inversion H0; subst. 
      constructor 2; eauto.
      unfold not; intro.

      destruct a;
      destruct o;
      apply_in_map;
      destruct x;
      destruct o.

      all: try breakTuple;
      repeat match goal with
        | h: Some _ = Some _ |- _ =>
        inversion h ; clear h
      end;
      subst;
      rmDirect;
      try contradiction; easy.
    }

    1:{
      set (a:=(vc_set.elements mc)).
      fold a in H0.
      induction a. 
      simpl. constructor.
      rewrite map_cons. 
      inversion H0; subst. 
      constructor 2; eauto.
      unfold not; intro.

      destruct a;
      destruct o;
      apply_in_map;
      destruct x;
      destruct o.

      all: try breakTuple;
      repeat match goal with
        | h: Some _ = Some _ |- _ =>
        inversion h ; clear h
      end;
      subst;
      rmDirect;
      try contradiction; easy.
    }

    1:{
      set (a:=(vb_set.elements mb)).
      fold a in H0.
      induction a. 
      simpl. constructor.
      rewrite map_cons. 
      inversion H0; subst. 
      constructor 2; eauto.
      unfold not; intro.

      destruct a;
      destruct o;
      apply_in_map;
      destruct x;
      destruct o.

      all: try breakTuple;
      repeat match goal with
        | h: Some _ = Some _ |- _ =>
        inversion h ; clear h
      end;
      subst;
      rmDirect;
      try contradiction; easy.
    }

  Qed.
  (* end hide *)


  (** [L_len_m_sub]: the size of a parser PndCalE state [m] is
      O(|P|·|P|). *)
  Lemma L_len_m_sub: ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    ||m|| <= (1+|P|+|P|)*(|P|+|P|).
  (* begin hide *)
  Proof.
    intros.
    rewrite <- L_bound_with_P.
    replace (||m||) with (|m_to_PE m|).

    apply len_m_sub with (1:=H).
    apply L_nodup_m_m with (1:=H).

    unfold m_to_PE.
    destruct m; simpl;
    rewrite map_length;
    auto.
  Qed.
  (* end hide *)

  (* begin hide *)
  Lemma L_Forest_ind: ∀ M T w, 
    Forest M T w ->
      ∀ M1 m M2, M=M1++[m]++M2 ->
      ∃ T' w', Forest (m::M2) T' w'.
  Proof.
    intros.
    generalize dependent M2.
    generalize dependent m.
    induction M1 using rev_ind; intros. simpl in *; subst. eauto.
    rewrite <- app_assoc in H0.
    specialize IHM1 with (m:=x) (M2:=[m]++M2) (1:=H0).
    breakAll.
    inversion IHM1.
    eauto.
  Qed.

  Lemma L_len_m: ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    ∀ M1 m M2, M=M1++[m]++M2 ->
    ||m|| <= (1+|P|+|P|)*(|P|+|P|) + 1.
  Proof.
    intros.
    pose (L_Forest_ind _ _ _ H (m::M1) m1 M2).
    getH; [tac_app; rewrite H0; eauto|].

    breakAll.
    pose L_len_m_sub.
    destruct x0.
    1:{
      inversion H1; subst.
      2:{
        tac_inj.
      }
      simpl. lia.
    }

    assert (s::x0!=[]) as notnil by eauto using nil_cons
    ; destruct (exists_last notnil) as [? [? _s]]
    ; rewrite _s in *
    ; clear notnil _s
    ; repeat rewrite app_assoc in h.

    pose (L_len_m_sub _ _ _ _ _ H1).
    lia.
  Qed.

  Lemma bound_cost_extraction_sub1:
    ∃ k b1 b2,
    ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    ∀ M1 M2,
      (M=M1++M2) ->
      let V0 := (f_init m) in
      let Vw := extraction M V0 in
      cost_extraction M1 V0 <=
      (k * |Vw| + b1) * |M1| + b2.
  Proof.
    set (H:=1).
    intros.
    destruct (bound_cost_extraction_one_step) as [k [k1 [b1 [b2 h]]]].
    set (mn:=(1+|P|+|P|)*(|P|+|P|)+1).
    exists 
      (k*mn*mn+mn*k1+b1),
      (b2+cost_extraction_inner),
      (cost_extraction_bt).

    intros.
    generalize dependent M2.
    induction M1 using rev_ind; intros.

    1:{
      simpl.

      unfold V2; unfold Vw.
      unfold V2.
      pose (bound_extraction). lia.
    }

    pose (bound_extraction) as h1.
    specialize h1 with (1:=H0) (2:=H1).
    pose (extraction_and_its_one_step).

    destruct M1. 
    
    1:{
      simpl in *.
      lia.
    }

    assert (m1::M1!=[]) as notnil by eauto using nil_cons
      ; destruct (exists_last notnil) as [? [? _s]]
      ; rewrite _s in *
      ; clear notnil _s
      ; repeat rewrite app_assoc in h.

    rewrite <- (cost_extraction_and_its_one_step).


    pose (IHM1 ([x]++M2)) as _h.
    getH. tac_app; eauto. rewrite app_assoc. auto.
    clear _h.

    pose (h (extraction (x0 ++ [x1]) V2) x1).


    pose (L_len_m m) as l0.
    repeat rewrite <- app_assoc in H1.
    specialize l0 with (1:=H0) (M1:=x0) (m:=x1) (M2:=[x]++M2) (2:=H1).

    assert (k*|| x1 || <= k*mn).
    nia.
    assert (k*|| x1 || * || x1 || <= k*mn*mn).
    nia.
    assert (
      (k * || x1 || * || x1 || + k1 * || x1 || + b1) <= 
        (k * mn * mn + k1 * mn + b1)
    ). nia.
    assert (
      cost_extraction_one_step x1 (extraction (x0 ++ [x1]) V2) <=
        (k *mn *mn + k1 * mn + b1) * | (extraction (x0 ++ [x1]) V2) | 
          + b2
    ).
    nia.

    rewrite app_length.
    rewrite Nat.add_assoc.

    replace 
        (((k*mn*mn + mn * k1 + b1) * | Vw | + b2 
          + cost_extraction_inner) 
          * (| (x0 ++ [x1]) | + | [x] |) + cost_extraction_bt) 
      with 
        (((k*mn*mn + mn * k1 + b1) * | Vw | 
          + b2 + cost_extraction_inner) 
          * (| (x0 ++ [x1]) |)  +
          ((k*mn*mn + mn * k1 + b1) * | Vw | + b2 
          + cost_extraction_inner) 
          * | [x] | + cost_extraction_bt); 
    try nia.

    simpl. 
    rewrite Nat.mul_1_r.

    pose (bound_cost_extraction_sub) as hs.
    rewrite app_assoc in H1.
    specialize hs with (1:=H0) (M1:=(x0 ++ [x1])) (M2:=[x]++M2) (2:=H1).
    unfold V2 in H6.
    assert 
      (cost_extraction_one_step x1 (extraction (x0 ++ [x1]) (f_init m))  
        <= (k*mn*mn+k1 * mn + b1) * | (extraction M (f_init m)) | + b2). 
    nia.

    assert (
      cost_extraction_one_step x1 (extraction (x0 ++ [x1]) V2) +
      cost_extraction (x0 ++ [x1]) V2 <=
      ((k*mn*mn+mn * k1 + b1) * | Vw | + b2 + cost_extraction_inner) 
      * | (x0 ++ [x1]) | +
      ((k*mn*mn+mn * k1 + b1) * | Vw | + b2) + cost_extraction_bt
      ->
      cost_extraction_one_step x1 (extraction (x0 ++ [x1]) V2) +
      cost_extraction (x0 ++ [x1]) V2 + cost_extraction_inner <=
      ((k*mn*mn+mn * k1 + b1) * | Vw | + b2 + cost_extraction_inner) 
        * | (x0 ++ [x1]) | +
      ((k*mn*mn+mn * k1 + b1) * | Vw | + b2 + cost_extraction_inner) 
        + cost_extraction_bt
    ) by nia.

    tac_app.

    unfold Vw in *.
    unfold V2 in *.

    assert (
      cost_extraction_one_step x1
        (extraction (x0 ++ [x1]) (f_init m)) 
        + cost_extraction (x0 ++ [x1]) (f_init m)
        <= (k*mn*mn+k1 * mn + b1) * | (extraction M (f_init m)) | + b2
          + cost_extraction (x0 ++ [x1]) (f_init m) ).
    nia.

    assert (
      ∀ x y, x<=y ->
      (k*mn*mn+k1 * mn + b1) * | (extraction M (f_init m)) | + b2 + x <=
      (k*mn*mn+k1 * mn + b1) * | (extraction M (f_init m)) | + b2 + y
    ) as h0. intros; lia.
    
    specialize h0 with (1:=l).
    nia.
  Qed.


  Lemma bound_cost_extraction_sub2:
    ∃ k b1 b2,
    ∀ m M T w i, Forest (m::M) T (w++[i]) ->
    ∀ M1 M2,
      (M=M1++M2) ->
      let V0 := (f_init m) in
      let Vw := extraction M V0 in
      cost_extraction M1 V0 <=
      (k * |Vw| + b1) * |w++[i]| + b2.
  Proof.
    destruct bound_cost_extraction_sub1 as [k1 [b1 [b2 h]]].
    exists k1, b1, b2.
    intros.

    pose (L_forest_length (m::M) T (w++[i]) H).

    specialize h with (1:=H) (M1:=M1) (M2:=M2) (2:=H0).
    rewrite H0 in e.
    simpl in e.
    assert (|M1| <= |w++[i]|). rewrite app_length in e. lia.
    simpl in h.
    simpl.
    unfold V2, Vw, V2.
    assert (
      | M1 | <= | (w ++ [i]) | ->
      (k1 * | (extraction M (f_init m)) | + b1) * | M1 | + b2 <=
      (k1 * | (extraction M (f_init m)) | + b1) * | (w ++ [i]) | + b2
    ).
    set (v:=(k1 * | (extraction M (f_init m)) | + b1)).
    nia.
    lia.
  Qed.
  (* end hide *)

  (** [Property_VPG_Parser_Generator]: the property of the end-to-end
      VPG parser. *)
  Theorem Property_VPG_Parser_Generator:
    ∃ k b1 b2,
    ∀ m M T w i, Forest (m::M) T (w++[i]) ->
      let Vinit := f_init m in
      let Vw := extraction M Vinit in
      (** - The list [Vw] of extracted parse trees contains no
          duplicates. *)
      NoDup Vw /\
      (** - The time cost of [extraction'] is O(k·|Vw|·|w|). *)
      cost_extraction M Vinit <= (k * |Vw| + b1) * |w++[i]| + b2 /\
      (** - The correctness of [Vw]: [v] is a parse tree of [w], iff [v]
          is in [Vw]. *)
      (∀ v, (∃ I, In (v, I) Vw) <-> DM.Dm L_0 (w ++ [i]) v).
  (* begin hide *)
  Proof.
    destruct bound_cost_extraction_sub2 as [k [b1 [b2 h]]].
    exists k, b1, b2.
    intros.

    destruct M.
    inversion H; tac_inj.

    getAnd; [|getAnd].
    2:{
      apply h with (T:=T) (M2:=[]); eauto.
      rewrite app_nil_r. auto.
    }

    all: assert (m1::M!=[]) as notnil by eauto using nil_cons
    ; destruct (exists_last notnil) as [? [? _s]]
    ; rewrite _s in *
    ; clear notnil 
    ; repeat rewrite app_assoc in h.

    all: pose (L_extract_extract) as h1;
    specialize h1 with (1:=H) (M1:=x) (m':=x0) (M2:=[]);
    rewrite app_nil_r in h1; rmDirect;
    breakAll;
    simpl in H0;
    destruct x1; try easy;
    simpl in H0, H2; rmDirect;
    subst.

    1:{
      unfold Vw, Vinit.
      pose (extraction_nodup_nodup) as p.
      rewrite _s.
      specialize p with (1:=H) (M1:=x) (m':=x0) (M2:=[]).
      rewrite app_nil_r in p. rmDirect.
      breakAll.

      destruct x.
      simpl. eauto.
      assert (m2::x!=[]) as notnil by eauto using nil_cons
      ; destruct (exists_last notnil) as [? [? _s2]]
      ; rewrite _s2 in *
      ; clear notnil 
      ; repeat rewrite app_assoc in h.
      rewrite <- extraction_and_its_one_step.
      apply L_f_b_nodup_nodup; auto.
    }

    intros.
    pose (L_extract) as h2.

    split;intro.
    destruct H0 as [I H0].
    specialize h2 with (1:=H1) (v:=v) (I:=I).
    destruct h2 as [h2 h3].

    1:{
      unfold Vw, Vinit.
      pose (extraction_nodup_nodup) as p.

      unfold Vw in H0.
      rewrite _s in H0.

      rmDirect.
      breakAll; eauto.
      tac_invalid_df.
    }

    pose (Dbx.BackwardSmallStep.Core.CompleteM) as d0.
    specialize d0 with (1:=H0).
    getH. tac_app; 
    eauto using nil_cons, app_cons_not_nil.

    destruct H2.
    exists x1.
    
    specialize h2 with (1:=H1) (v:=v) (I:=x1).
    destruct h2 as [h2 h3].
    unfold Vw. rewrite _s.
    eauto.
    tac_app.
    breakAll.
    getAnd; eauto.
  Qed.
  (* end hide *)

End TimedExtraction.
