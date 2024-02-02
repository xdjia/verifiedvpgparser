(** This file verifies that running a parser PDA takes linear-time. *)

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
Import vpg.
Require Import Def.
Require Import Tac.
Require Import Monad.
Require Import MonadicUtils.

Require Import TimedSets.


Module PDA(G:VPG).

  Module TimedSets := TimedSets(G).

  Import TimedSets.
  Import Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Def.

  (** [State]: a parser PDA state. *)
  Definition State := ME.
  (** [Forest]: a parser PDA forest. *)
  Definition Forest := list ME.
  (** [StackElt]: a stack element. *)
  Definition StackElt := ME.

  (* begin hide *)
  Definition Symbol := symbol.
  Definition String := list Symbol.
  (* end hide *)

  (** [Stack]: a stack in a configuration. *)
  Definition Stack : Type := list ME.
  (** [Configuration]: a configuration. *)
  Definition Configuration : Type := State * Stack.

  (** [Transition]: A transition entry. *)
  Definition Transition : Type := 
      ((Symbol * ME * option ME) * ME).
  
  (* begin hide *)
  Definition eq_symbol := eqs.
  (* end hide *)

  (** [initState]: the initial state. *)
  Parameter initState : State.
  (** [transitions]: the transition table, implemented as a list of
    transition entries for simplicity. *)
  Parameter transitions : list Transition.

  (* begin hide *)
  Fixpoint max_state (transitions:list Transition) (m:nat) :=
    match transitions with
    | [] => m 
    | ((i,s,t),s')::transitions' =>
      let mt :=
        match t with 
        | None => 0
        | Some t => ||t||
        end in
      max_state transitions'
        (max m (max (||s||) (max (||s'||) mt)))
    end.

  Lemma L_max_state: ∀ l m, max_state l m >= m.
  Proof.
    intro l.
    induction l; intro. simpl. auto.
    simpl. destruct a, p, p.
    match goal with
    | |- max_state _ ?m' >= _ =>
     specialize IHl with m';
     assert (m' >= m) by apply Nat_as_OT.le_max_l
    end.
    lia.
  Defined.

  Lemma L_max_state': ∀ l m1 m2,
    m1 >= m2 ->
    max_state l m1 >= max_state l m2.
  Proof.
    intro l.
    induction l; intros. simpl. lia. 
    simpl. destruct a, p, p.
    apply IHl.
    lia.
  Defined.
  (* end hide *)

  (** [bound_m]: the size of each entry is bounded by a constant
      independent of the input string. This lemma is used for bounding
      the lookup time. *)
  Lemma bound_m: ∃ k, ∀ sym s t s1, 
    In ((sym,s,t),s1) transitions ->
    ||s|| <= k /\ ||s1|| <= k /\ 
      (∀ t', t=Some t' -> ||t'|| <= k).
  (* begin hide *)
  Proof.
    exists (max_state transitions 0).
    induction transitions; intros.
    inversion H.

    inversion H.
    1:{
      subst.
      simpl.
      
      match goal with
      | |- _ <= max_state ?l ?m' /\ _ =>
       pose (L_max_state l m');
       assert (m' >= ||s||) by lia;
       assert (m' >= ||s1||) by lia;
       assert (m' >= match t with
        | Some t0 => || t0 ||
        | None => 0
        end) by lia
      end.

      split. lia.
      split. lia.
      intros; subst.
      lia.
    }
    destruct (IHl sym s t s1 H0) as [H1 [H2 H3]].
    
    simpl. destruct a, p, p.
    split. 
    match goal with
    | h:?x <= ?y |- ?x <= ?z =>
     assert (y<=z) by (apply L_max_state'; lia)
    end.
    lia.

    split. 
    match goal with
    | h:?x <= ?y |- ?x <= ?z =>
     assert (y<=z) by (apply L_max_state'; lia)
    end.
    lia.

    intros.
    pose (H3 t' H4).
    match goal with
    | h:?x <= ?y |- ?x <= ?z =>
     assert (y<=z) by (apply L_max_state'; lia)
    end.
    lia.
  Qed.

  Definition eq_state (state1:ME) (state2:ME) : bool :=
    match state1, state2 with
    | CalCME state1, CalCME state2 =>
      va_set.equal state1 state2
    | PlnCME state1, PlnCME state2 =>
      vc_set.equal state1 state2      
    | RetCME state1, RetCME state2 =>
      vb_set.equal state1 state2
    | _, _ => false
    end.

  Definition cost_eq_state_branch1 := 1.
  Definition cost_eq_state_branch2 := 1.
  Definition cost_eq_state_branch3 := 1.
  Definition cost_eq_state_branch4 := 1.
  Opaque cost_eq_state_branch1.
  Opaque cost_eq_state_branch2.
  Opaque cost_eq_state_branch3.
  Opaque cost_eq_state_branch4.

  Definition cost_eq_state (state1:ME) (state2:ME) : nat :=
    match state1, state2 with
    | CalCME state1, CalCME state2 =>
      cost_eq_state_branch1 +
      timed_va_set.cost_equal state1 state2
    | PlnCME state1, PlnCME state2 =>
      cost_eq_state_branch2 +
      timed_vc_set.cost_equal state1 state2      
    | RetCME state1, RetCME state2 =>
      cost_eq_state_branch3 +
      timed_vb_set.cost_equal state1 state2
    | _, _ => 
      cost_eq_state_branch4
    end.

  Definition bound_cost_eq_state: ∃ k b, ∀ s1 s2,
    cost_eq_state s1 s2 <= k * ||s1|| + b.
  Proof.
    destruct timed_va_set.bound_cost_equal as [ka [ba Ha]].
    destruct timed_vc_set.bound_cost_equal as [kc [bc Hc]].
    destruct timed_vb_set.bound_cost_equal as [kb [bb Hb]].

    exists (ka + kc + kb +
      cost_eq_state_branch1+cost_eq_state_branch2+cost_eq_state_branch3),
       (ba + bb + bc + cost_eq_state_branch1+cost_eq_state_branch2
       +cost_eq_state_branch3 +cost_eq_state_branch4).
    intro s1.

    induction s1; intro s2; 
    simpl.
    all: destruct s2.
    all: try match goal with
      | |- _ + ?equal ?x ?y <= _ =>
       try (pose (Ha x y);rewrite <- (va_set.cardinal_spec));
       try (pose (Hb x y);rewrite <- (vb_set.cardinal_spec));
       try (pose (Hc x y);rewrite <- (vc_set.cardinal_spec))
      end.
    all: lia.
  Qed.

  Program Definition eq_state' (state1:ME) (state2:ME) 
  :{! y !:! _ !<! c !>! c = cost_eq_state state1 state2 /\ 
    y = eq_state state1 state2 !}
  :=
    match state1 as s1, state2 as s2 return 
      (state1=s1)->(state2=s2)->
      {! y !:! _ !<! c !>! c = cost_eq_state state1 state2 /\ 
      y = eq_state state1 state2 !}
    with
    | CalCME state1, CalCME state2 =>
      fun hyp1 hyp2 =>
      out <- timed_va_set.equal' state1 state2;
      += cost_eq_state_branch1;
      <== out
    | PlnCME state1, PlnCME state2 =>
      fun hyp1 hyp2 =>
      out <- timed_vc_set.equal' state1 state2      ;
      += cost_eq_state_branch2;
      <== out
    | RetCME state1, RetCME state2 =>
      fun hyp1 hyp2 =>
      out <- timed_vb_set.equal' state1 state2;
      += cost_eq_state_branch3;
      <== out
    | _, _ => 
      fun hyp1 hyp2 =>
      += cost_eq_state_branch4; <== false
    end (eq_refl state1) (eq_refl state2).
  (* end hide *)

  (* begin hide *)

  Next Obligation.
    unfold cost_eq_state.
    split. lia. auto.
  Defined.

  Next Obligation.
    unfold cost_eq_state.
    split. lia. auto.
  Defined.

  Next Obligation.
    unfold cost_eq_state.
    split. lia. auto.
  Defined.
  (* end hide *)

  (* begin hide *)
  Definition cost_eq_stackTop_branch1 := 1.
  Definition cost_eq_stackTop_branch2 := 1.
  Definition cost_eq_stackTop_branch3 := 1.
  Opaque cost_eq_stackTop_branch1.
  Opaque cost_eq_stackTop_branch2.
  Opaque cost_eq_stackTop_branch3.

  Definition cost_eq_stackTop (st1:option ME) (st2:option ME) : nat :=
    match st1, st2 with
    | None, None => cost_eq_stackTop_branch1  
    | Some s1, Some s2 => 
      cost_eq_stackTop_branch2 + cost_eq_state s1 s2 
    | _, _ => cost_eq_stackTop_branch3 
    end.

  Definition bound_cost_eq_stackTop: ∃ k b, ∀ s1 s2,
    cost_eq_stackTop s1 s2 <= 
    match s1 with 
    | None => b 
    | Some s1 => k * ||s1|| + b
    end.
  Proof.
    destruct bound_cost_eq_state as [k [b H]].
    exists k, (cost_eq_stackTop_branch1 + cost_eq_stackTop_branch2 + 
      cost_eq_stackTop_branch3 + b).
    intros.
    destruct s1.
    simpl. destruct s2.
    pose (H m m0); lia. 
    lia.

    simpl. destruct s2; lia. 
  Qed.

  Definition eq_stackTop (st1:option ME) (st2:option ME)
  :=
  match st1, st2 with
  | None, None => true 
  | Some s1, Some s2 => eq_state s1 s2 
  | _, _ => false
  end.

  Program Definition eq_stackTop' (st1:option ME) (st2:option ME)
  :{! y !:! _ !<! c !>! c = cost_eq_stackTop st1 st2 /\ 
    y = eq_stackTop st1 st2 !}
  :=
  match st1 as st1', st2 as st2' return
    (st1=st1')->(st2=st2')->
    {! y !:! _ !<! c !>! c = cost_eq_stackTop st1 st2 /\ 
    y = eq_stackTop st1 st2 !}
  with
  | None, None =>
    fun hyp1 hyp2 => 
      += cost_eq_stackTop_branch1; <== true 
  | Some s1, Some s2 =>
    fun hyp1 hyp2 => 
      out <- eq_state' s1 s2;
      += cost_eq_stackTop_branch2; <== out
  | _, _ =>
    fun hyp1 hyp2 => 
      += cost_eq_stackTop_branch3; <== false
  end (eq_refl st1) (eq_refl st2).

  Next Obligation.
    split. unfold cost_eq_stackTop. lia. auto.
  Defined.
  (* end hide *)

  (** [lookUp]: lookup a transition. *)
  Fixpoint lookUp (sym:Symbol) (state:ME) (stackTop:option ME) 
  (transitions:list Transition)
  : option State := 
    match transitions with
    | [] => None
    | ((sym1,state1,stackTop1),state2)::transitions' => 
      let is_eq_sym := eqs sym sym1 in
      let is_eq_state := eq_state state1 state in
      let is_eq_stackTop := eq_stackTop stackTop1 stackTop in
      if is_eq_sym && is_eq_state && is_eq_stackTop
      then Some state2
      else lookUp sym state stackTop transitions'
    end.
  (* begin hide *)

  Definition cost_lookUp_branch1 := 1.
  Definition cost_lookUp_branch2 := 1.
  Definition cost_lookUp_branch3 := 1.
  Definition cost_lookUp_branch4 := 1.
  Opaque cost_lookUp_branch1.
  Opaque cost_lookUp_branch2.
  Opaque cost_lookUp_branch3.
  Opaque cost_lookUp_branch4.

  Fixpoint cost_lookUp (sym:Symbol) (state:ME) (stackTop:option ME)
    (transitions:list Transition)
  :=    
      match transitions with
      | [] => cost_lookUp_branch1
      | ((sym1,state1,stackTop1),state2)::transitions' => 
        let is_eq_sym := eqs sym sym1 in
        let is_eq_state := eq_state state1 state in
        let is_eq_stackTop := eq_stackTop stackTop1 stackTop in
        if is_eq_sym && is_eq_state && is_eq_stackTop
        then cost_eqs sym sym1 +
          cost_eq_state state1 state +
          cost_eq_stackTop stackTop1 stackTop + cost_lookUp_branch2
        else cost_eqs sym sym1 +
          cost_eq_state state1 state +
          cost_eq_stackTop stackTop1 stackTop +
          cost_lookUp sym state stackTop transitions' +
          cost_lookUp_branch3
      end.
  (* end hide *)


  (** [cost_lookUp]: the time cost of lookuping a transition is
      O(|transitions|. When the transition table is implemented as a
      hashtable, the time should be (amortized) constant; here we
      implement the table as a list for simplicity. *)
  Lemma bound_cost_lookUp: ∃ k b, ∀ sym state stackTop, 
    cost_lookUp sym state stackTop transitions <= k * |transitions| + b.
  (* begin hide *)
  Proof.
    Import Parser.PreTimed.Dbx.BackwardSmallStep.ForwardSmallStep.Tac.Tacs.
    destruct bound_m as [km hm].

    destruct bound_cost_eq_state as [k1 [b1 H1]].
    destruct bound_cost_eq_stackTop as [k2 [b2 H2]].
    destruct bound_cost_eqs as [k3 H3].

    exists (k3 + (k1 * km + b1) + (k2 * km + b2) + cost_lookUp_branch3).
    exists (cost_lookUp_branch1 + cost_lookUp_branch2 +
      k3 + (k1 * km + b1) + (k2 * km + b2)).

    induction transitions; intros.
    1:{
      simpl.
      destruct stackTop;
      lia.
    }

    simpl.
    destruct a, p, p.

    pose (H3 sym s) as l3.
    pose (H1 m0 state) as l1.
    pose (H2 o stackTop) as l2.

    pose (hm s m0 o m) as hm1.
    match type of hm1 with
    | _ -> ?g =>
     assert g as hg; [apply hm1; constructor; auto|]
     ; destruct hg as [g1 g2]
    end.

    assert (cost_eq_state m0 state <= k1 * km + b1) by nia.
    assert (cost_eq_stackTop o stackTop <= k2 * km + b2).
    1:{
      destruct o.
      destruct g2 as [g3 g4].
      specialize g4 with m1.
      getH. tac_app. auto. nia. nia.
    }

    destruct (eqs sym s && eq_state m0 state && eq_stackTop o stackTop).
    try nia; try lia.


    match type of IHl with
    | _ -> ?g =>
     assert g as hg; [apply IHl; auto|]
    end.
    1:{
      intros.
      pose (hm sym0 s0 t s1) as hm2.
      getH. tac_app. constructor 2. auto.
      easy.
    }
    specialize hg with sym state stackTop.
    try nia; try lia.
  Qed.
  (* end hide *)
  
  (** [lookUp']: the monadic verision of [lookUp]. *)
  Program Fixpoint lookUp' (sym:Symbol) (state:ME) (stackTop:option ME) 
  transitions
  :{! y !:! _ !<! c !>! c = cost_lookUp sym state stackTop transitions /\ 
    y = lookUp sym state stackTop transitions !}
  := 
    match transitions as transitions'' return 
      (transitions=transitions'')->
      {! y !:! _ !<! c !>! 
        c = cost_lookUp sym state stackTop transitions /\ 
      y = lookUp sym state stackTop transitions !}
    with
    | [] =>
      fun hyp => += cost_lookUp_branch1; <== None
    | ((sym1,state1,stackTop1),state2)::transitions' =>
      fun hyp => 
      is_eq_sym <- eqs' sym sym1;
      is_eq_state <- eq_state' state1 state;
      is_eq_stackTop <- eq_stackTop' stackTop1 stackTop;
      if dec (is_eq_sym && is_eq_state && is_eq_stackTop)
      then += cost_lookUp_branch2; <== Some state2
      else out <- lookUp' sym state stackTop transitions';
      += cost_lookUp_branch3; <== out
    end (eq_refl transitions).

  (* begin hide *)
  Next Obligation.
    split; auto.
    unfold cost_lookUp.
    rewrite e. lia.
    simpl. rewrite e. auto.
  Qed.

  Next Obligation.
    split; auto.
    simpl.
    rewrite e.
    lia.
    simpl. rewrite e. auto.
  Qed.
  (* end hide *)

  (** [transition]: the one-step transition function. *)
  Definition transition (sym:Symbol) (config:Configuration) :=
    match config with
    | (state, stack) =>
      match stack with
      | [] => lookUp sym state None transitions
      | st::_ => lookUp sym state (Some st) transitions
      end
    end.

  (* begin hide *)
  Definition cost_transition_branch1 := 1.
  Definition cost_transition_branch2 := 1.
  Opaque cost_transition_branch1.
  Opaque cost_transition_branch2.
  
  Definition cost_transition (sym:Symbol) (config:Configuration) :=
    match config with
    | (state, stack) =>
      match stack with
      | [] => 
        cost_transition_branch1 + cost_lookUp sym state None transitions
      | st::_ => cost_transition_branch2 + 
        cost_lookUp sym state (Some st) transitions
      end
    end.
  (* end hide *)
  
  (** [transition]: the time cost of the one-step transition function is
      O(|transitions|). *)
  Lemma bound_cost_transition: ∃ k b, ∀ sym config, 
    cost_transition sym config <= k * |transitions| + b.
  (* begin hide *)
  Proof.
    destruct bound_cost_lookUp as [k [b h]].
    exists (k), 
      (b+cost_transition_branch1+cost_transition_branch2).
    intros.
    unfold cost_transition. destruct config.
    destruct s0. 
    specialize h with sym s None. nia.
    specialize h with sym s (Some m). nia.
  Qed.
  (* end hide *)

  (** [transition']: the monadic version of [transition]. *)
  Program Definition transition' (sym:Symbol) (config:Configuration) 
  :{! y !:! _ !<! c !>! c = cost_transition sym config /\ 
    y = transition sym config !}
  :=
    match config as config' return (config=config') ->
    {! y !:! _ !<! c !>! c = cost_transition sym config /\ 
    y = transition sym config !}
    with
    | (state, stack) =>
      fun hyp =>
      match stack as stack' return (stack=stack') ->
      {! y !:! _ !<! c !>! c = cost_transition sym config /\ 
      y = transition sym config !}
      with
      | [] =>
        fun hyp => out <- lookUp' sym state None transitions;
        += cost_transition_branch1; <== out
      | st::_ =>
        fun hyp => out <- lookUp' sym state (Some st) transitions;
        += cost_transition_branch2; <== out
      end (eq_refl stack)
    end (eq_refl config).

  (* begin hide *)
  Next Obligation.
    split; auto.
    unfold cost_transition. lia.
  Defined.

  Next Obligation.
    split; auto.
    unfold cost_transition. lia.
  Defined.
  (* end hide *)

  (** [run]: run a parser PDA and generate a forest. *)
  Fixpoint run config forest (w:String) : option Forest :=
    match w with
    | [] => Some forest
    | sym::w' =>
      match transition sym config with 
      | None => None 
      | Some state' =>
        let forest' := state' :: forest in
        let config' :=
          match config with 
          | (state, stack) =>
            match sym with
            | Call s => (state', state::stack)
            | Plain s => (state', stack)
            | Ret s => (state', tl stack)
            end 
          end in
        run config' forest' w'
      end
    end.

  (* begin hide *)
  Definition cost_run_branch1 := 1.
  Definition cost_run_branch2 := 1.
  Definition cost_run_branch3 := 1.
  Definition cost_run_branch4 := 1.
  Definition cost_run_branch5 := 1.
  Opaque cost_run_branch1.
  Opaque cost_run_branch2.
  Opaque cost_run_branch3.
  Opaque cost_run_branch4.
  Opaque cost_run_branch5.

  Opaque cons_ct.

  Fixpoint cost_run config forest (w:String) : nat :=
    match w with
    | [] => cost_run_branch1
    | sym::w' =>
      cost_transition sym config +
      match transition sym config with 
      | None => cost_run_branch2
      | Some state' =>
        let forest' := state' :: forest in
        match config with 
        | (state, stack) =>
          match sym with
          | Call s => 
            cons_ct + cost_run (state', state::stack) forest' w' + 
            cost_run_branch3
          | Plain s => 
            cons_ct + cost_run (state', stack) forest' w' + 
            cost_run_branch4
          | Ret s => 
            cons_ct + cost_run (state', tl stack) forest' w' + 
            cost_run_branch5
          end 
        end
      end
    end.
  (* end hide *)

  (** [bound_cost_run]: the time cost of running a parser PDA is O(|w|)
    *)
  Lemma bound_cost_run: ∃ k b b1, ∀ w config forest,
    cost_run config forest (w:String) 
      <= (k * |transitions| + b) * |w| + b1.
  (* begin hide *)
  Proof.
    destruct (bound_cost_transition) as [k [b h]].
    exists k, (b+cost_run_branch2+cost_run_branch3+cost_run_branch4+cost_run_branch5
      +cons_ct), cost_run_branch1.

    intro w.
    induction w. 
    simpl. lia.
    intros.
    simpl.

    destruct (transition a config).
    1:{
      pose (h a config).
      destruct config. destruct a.
      pose (IHw (s, s0 :: s1) (s :: forest)). nia.
      pose (IHw (s, s1) (s :: forest)). nia.
      pose (IHw (s, tl s1) (s :: forest)). nia.
    }
    pose (h a config); nia.
  Qed.

  Definition cost_run_sub config forest sym w' : nat :=
    match transition sym config with 
    | None => cost_run_branch2
    | Some state' =>
      let forest' := state' :: forest in
      match config with 
      | (state, stack) =>
        match sym with
        | Call s => 
        cons_ct +
        cost_run (state', state::stack) forest' w' + cost_run_branch3
        | Plain s => cons_ct + cost_run (state', stack) forest' w' + cost_run_branch4
        | Ret s => cons_ct + cost_run (state', tl stack) forest' w' + cost_run_branch5
        end 
      end
    end.
  (* end hide *)

  (** [run']: the monadic verision of [run]. *)
  Program Fixpoint run' config forest (w:String) 
  :{! y !:! option Forest !<! c !>! c = cost_run config forest w /\ 
    y = run config forest w !}
  :=
    match w as w'' return (w=w'')->
      {! y !:! _ !<! c !>! c = cost_run config forest w /\ 
        y = run config forest w !}
    with
    | [] =>
      fun hyp => += cost_run_branch1; <== Some forest
    | sym::w' =>
      fun hyp =>
      out <- transition' sym config;
      out1 <- match out as out' return (out=out')->
        {! y !:! _ !<! c !>! c = cost_run_sub config forest sym w' /\ 
          y = run config forest w !}
      with 
      | None =>
        fun hyp => += cost_run_branch2; <== None 
      | Some state' =>
        fun hyp =>
        match config as config' return (config=config')->
        {! y !:! _ !<! c !>! c = cost_run_sub config forest sym w' /\ 
          y = run config forest w !}
        with 
        | (state, stack) =>
          fun hyp =>
          match sym as sym' return (sym=sym')->
          {! y !:! _ !<! c !>! c = cost_run_sub config forest sym w' /\ 
            y = run config forest w !}
          with
          | Call s =>
            fun hyp => 
            forest' <- cons' _ state' forest;
            out <- run' (state', state::stack) forest' w';
            += cost_run_branch3; <==out
          | Plain s =>
            fun hyp => 
            forest' <- cons' _ state' forest;
            out <- run' (state', stack) forest' w';
            += cost_run_branch4; <==out
          | Ret s =>
            fun hyp => 
            forest' <- cons' _ state' forest;
            out <- run' (state', tl stack) forest' w';
            += cost_run_branch5; <==out
          end (eq_refl sym)
        end (eq_refl config)
      end (eq_refl out);
      <== out1
    end (eq_refl w).

  (* begin hide *)
  Next Obligation.
    split; auto. unfold cost_run_sub. rewrite hyp1. easy.
    unfold run.
    rewrite hyp1. auto.
  Defined.
  
  Next Obligation.
    split; auto. unfold cost_run_sub. rewrite hyp1. easy.
    unfold run.
    rewrite hyp1. auto.
  Defined.

  Next Obligation.
    split; auto. unfold cost_run_sub. rewrite hyp1. easy.
    unfold run.
    rewrite hyp1. auto.
  Defined.

  Next Obligation.
    split; auto. unfold cost_run_sub. rewrite hyp. easy.
    unfold run.
    rewrite hyp. auto.
  Defined.

  Next Obligation.
    split; auto.
    unfold cost_run.
    unfold cost_run_sub.
    fold cost_run. lia.
  Defined.
  (* end hide *)

  (** [runPDA]: a wrap of [run]. *)
  Definition run_PDA (w:String) :=
    let initConfig := (initState, []) in 
    run initConfig [] w.

  (* begin hide *)
  Definition cost_run_PDA_branch1 := 1.
  Opaque cost_run_PDA_branch1.
  Definition cost_run_PDA (w:String) :=
    let initConfig := (initState, []) in 
    time_pair + cost_run initConfig [] w + cost_run_PDA_branch1.
  (* end hide *)

  (** [bound_cost_run_PDA]: the time cost of running a PDA is O(|w|). *)
  Lemma bound_cost_run_PDA: ∃ k b, ∀ w, cost_run_PDA w
    <= k * |w| + b.
  (* begin hide *)
  Proof.
    destruct bound_cost_run as [k [b [b1 h]]].
    set (k1:=|transitions|).
    exists (k * |transitions| + b), (b1+time_pair+cost_run_PDA_branch1).

    intros.
    unfold cost_run_PDA.
    pose (h w (initState, []) []). 
    assert (k * | transitions | + b <= k * k1 + b).
    nia.
    assert (cost_run (initState, []) [] w <= (k * k1 + b) * | w | + b1).
    nia. 
    lia.
  Defined.
  (* end hide *)

  (** [runPDA']: the monadic version of [runPDA]. *)
  Program Definition runPDA' (w:String) 
  :{! y !:! option Forest !<! c !>! c = cost_run_PDA w /\ 
    y = run_PDA w !}
  :=     
    initConfig <- pair' _ _ initState [];
    out <- run' initConfig [] w;
    += cost_run_PDA_branch1;
    <== out.

End PDA.