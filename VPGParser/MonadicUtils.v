(** This file provides some basic monadic functions.  *)

Require Import Monad.
Require Import Program List.
Require Import Lia.

Section cons'.
  Variable A: Type.
  (** [cons_ct]: adding an element to a list is a basic operation. *)
  Definition cons_ct := 5.

  (** [cons']: the monadic version of [cons]. *)
  Program Definition cons' (x:A) xs 
  :{! y !:! list A !<! c !>! c = cons_ct /\ y = cons x xs !} :=
    += cons_ct; <== cons x xs.
End cons'.


Section filter_map'.

  Variables A B : Type.
  Variable P_map : (list A) -> nat -> Prop.

  (* begin hide *)

  Definition map_vf_count := 1.

  Definition map_f_type _f := forall (x:A),
  {! acc' !:! B !<! c !>!
    (forall xs accC,
      P_map        xs       accC ->
      P_map  (x :: xs) (accC + c + cons_ct + map_vf_count)) /\
      acc' = _f x !}.

  Definition map_result
            _f
             (f : map_f_type _f)
             l
             (res:list B)
             (c : nat) := P_map l c.

  Definition map_bt := 4.
  Variable p: P_map nil map_bt.

  Program Fixpoint map2 (_f:A->B) (f: map_f_type _f) xs:
  {! res !:! list B !<! c !>!
      map_result _f f xs res c /\
      res = map _f xs !} :=
    match xs with
    | nil => 
      += map_bt; <== nil
    | x::xs' =>
      res <- map2 _f f xs';
      fx <- f x;
      out <- cons' B fx res;
      += map_vf_count; <== out
    end.


  Next Obligation.
    split.
    replace (an1 + (an0 + (cons_ct + map_vf_count))) with 
      (an1 + an0 + cons_ct + map_vf_count); try lia.
    unfold map_result in *.
    apply H1.
    auto.

    auto.
  Defined.

  Definition filter_vf_count := 1.
  Definition filter_bt := 1.

  Definition time_filter_branch1 := 1.
  Definition time_filter_branch2 := 1.
  Definition time_filter_branch3 := 1.

  Opaque time_filter_branch1.
  Opaque time_filter_branch2.
  Opaque time_filter_branch3.

  Fixpoint cost_filter (f:A->bool) cost_f (l:list A) :=
    match l with 
    | nil => time_filter_branch1
    | x::l =>
      cost_f x +
      if f x then
        cost_filter f cost_f l + cons_ct + time_filter_branch2
      else
        cost_filter f cost_f l + time_filter_branch3
    end.
  (* end hide *)

  (** [filter']: the monadic version of [filter], which filters a list
    with a boolean function of the list elements. *)
  Program Fixpoint filter' {f} {cost_f}
    (f':forall x, {! y !:! bool !<! c !>! 
      c = cost_f x /\ y = f x !}) 
    (l:list A)
  : {! y !:! list A !<! c !>! 
      c = cost_filter f cost_f l /\ 
      y = List.filter f l !} :=
      match l with
      | nil =>
        += time_filter_branch1; <== nil
      | x :: l =>
        fx <- f' x;
        if dec fx then
          acc <- filter' f' l;
          out <- cons' A x acc;
          += time_filter_branch2;
          <== out
        else
          out <- filter' f' l;
          += time_filter_branch3;
          <== out
      end.
  (* begin hide *)
  Next Obligation.
    rewrite e.
    split; auto.
    lia.
  Defined.
  

  Next Obligation.
    rewrite e.
    split; auto.
  Defined.
  (* end hide *)
End filter_map'.


Section exitsb'.
  Variable A: Type.
  Variable f: A -> bool.
  Variable cost_f: A -> nat.
  Variable f': forall x, {! y !:! _ !<! c !>! c = cost_f x /\ y = f x !}.

  (* begin hide *)

  Definition cost_andb := 1.
  Definition cost_orb := 1.
  Definition cost_existb_branch1 := 1.
  Definition cost_existb_branch2 := 1.

  Opaque cost_andb.
  Opaque cost_orb.
  Opaque cost_existb_branch1.
  Opaque cost_existb_branch2.

  Fixpoint cost_existb l :=
    match l with 
    | nil => cost_existb_branch1
    | x::l' => cost_f x + cost_orb + cost_existb l' + cost_existb_branch2 
    end.
  (* begin hide *)

  (** [existsb']: the monadic version of [existsb], which checks if a
      list includes a certain element. *)
  Program Fixpoint existsb' (l:list A)
    : {! res !:! bool !<! c !>!
        c = cost_existb l /\ res = existsb f l !}
    :=
    match l with
    | nil => += cost_existb_branch1; <== false
    | x::l' => 
      fx <- f' x;
      res <- existsb' l';
      += cost_orb+ cost_existb_branch2;
      <== orb fx res
    end.

  (* begin hide *)
  Next Obligation.
    split. lia. auto.
  Defined.
  (* end hide *)

End exitsb'.

Arguments existsb' {A} {f} {cost_f}.

Section concat'.
  Variable A: Type.
  (* begin hide *)

  Definition app_bt := 1.
  Definition app_inner_time := 1.

  Definition cost_app (l:list A) :=
    (cons_ct + app_inner_time) * (length l) + app_bt.
  
  Lemma bound_cost_app: exists k b, forall l, cost_app l <= k * (length l) + b.
  Proof.
    unfold cost_app.
    eauto.
  Qed.
  
  Program Fixpoint _app l1 l2 :
    {! res !:! list A !<! c !>! 
      c = cost_app l1
        /\ res = app l1 l2 !}
  :=
    match l1 with
    | nil => += app_bt; <== l2
    | a :: l1 => 
      l' <- _app l1 l2;
      out <- cons' _ a l';
      += app_inner_time; <== out
    end.

  Opaque cons_ct.
  Opaque app_inner_time.
  Next Obligation.
    split.
    unfold cost_app.
    simpl.
    lia.

    eauto.
  Defined.

  Definition concat_bt := 1.
  Definition concat_inner_time := 1.

  Fixpoint cost_concat ls :=
    match ls with 
    | nil => concat_bt
    | cons x ls' => cost_app x + concat_inner_time + cost_concat ls'
    end.
  (* end hide *)

  (** [bound_cost_concat]: cost of concating a list of lists depends on
      the number and the maximal length [ln] of the lists. *)
  Lemma bound_cost_concat: 
    exists k b1 b2, 
    forall ls ln,
    (forall l, (In l ls) -> (length l <= ln)) ->
    cost_concat ls <= (k * ln + b1) * (length ls) + b2.
  (* begin hide *)
  Proof.
    destruct (bound_cost_app) as [k1 [b1 ?]].
    exists (k1).
    exists (b1 + concat_inner_time).
    exists (concat_bt).
    intros.
    induction ls.
    
    simpl. lia.

    assert (In a (a::ls)).
    unfold In; eauto.
    pose (H0 a H1).
    pose (H a).
    simpl.

    match type of IHls with
    | _ -> ?g =>
     assert g; [apply IHls|]
    end.
    eauto using in_cons.

    nia.
  Qed.
  (* end hide *)

  (** [_concat']: the monadic version of [concat], which concat a list
    of lists to a list. *)
  Program Fixpoint _concat (l : list (list A)) 
    : {! res !:! list A !<! c !>! 
      c = cost_concat l /\ res = concat l !}
    :=
    match l with
    | nil => += concat_bt; <== nil
    | cons x l =>
      l' <- _concat l;
      out <- _app x l';
      += concat_inner_time; <== out
    end.

  (* begin hide *)
  Next Obligation.
    split.
    unfold cost_app.
    simpl.
    lia.

    auto.
  Defined.
  (* end hide *)

End concat'.


Section tail'.
  Variable A: Type.

  (* begin hide *)
  Definition tail_bt := 1.
  Definition tail_inner_time := 1.

  Definition cost_tail (l: list A) := 
    match l with 
    | nil => tail_bt
    | _ => tail_inner_time
    end.
  (* end hide *)

  (** [tail']: the monadic version of [tail], which takes the tail of a
    list. *)
  Program Fixpoint tail' l :
    {! res !:! list A !<! c !>! c = cost_tail l /\ res = tl l !}
  :=
    match l as l' return l=l' -> 
      {! res !:! list A !<! c !>! 
        c = cost_tail l /\ res = tl l !} with
    | nil => 
      fun hyp =>
        += tail_bt; <== nil
    | cons _ m => 
      fun hyp =>
        += tail_inner_time; <== m
    end (eq_refl l).

End tail'.


Section map'.
  Definition time_map_branch1 := 1.
  Definition time_map_branch2 := 1.

  Opaque time_map_branch1.
  Opaque time_map_branch2.
  Opaque cons_ct.

  Variable A: Type.
  Variable B: Type.
  Variable f: A->B.
  Variable cost_f: A->nat.

  Fixpoint cost_map l :=
    match l with
    | nil => time_map_branch1
    | x::l' =>
      cost_f x + (cost_map l') + 
      cons_ct + time_map_branch2
    end.

  Hint Unfold cost_map : misc.

  (** [bound_cost_map]: the cost of [map'] is bounded by the length of
      the list, and the maximal cost of the function [f] on each
      element. *)
  Lemma bound_cost_map:
    (exists k, forall a, cost_f a <= k) ->
      exists k b, forall l, cost_map l <= k * (length l) + b.
  (* begin hide *)
  Proof.
    intro.
    destruct H as [k1 ?].
    exists (k1 + cons_ct + time_map_branch2), time_map_branch1.
    intros.
    induction l.
    simpl.
    lia.
    simpl.
    pose (H a).
    lia.
  Qed.
  (* end hide *)
  
  (** [map']: the monadic version of [map], which maps the elements in a
    list to another elements. *)
  Program Fixpoint map'
    (f': forall (x:A), 
      {! y !:! B !<! c !>! c = cost_f x /\ y = f x !})
    l
  : {! y !:! list B !<! c !>! c = cost_map l /\ y = map f l !}
  :=
    match l as ll return (l=ll)->
    {! y !:! list B !<! c !>! c = cost_map l /\ y = map f l !}
    with
    | nil =>
      fun hyp =>
        += time_map_branch1; <== nil
    | x::l' =>
      fun hyp =>
        res <- map' f' l';
        fx <- f' x;
        out <- cons' B fx res;
        += time_map_branch2; <== out
    end (eq_refl l).

  (* begin hide *)
  Next Obligation.
    split.
    simpl.
    lia.
    simpl.
    eauto.
  Defined.  

  Definition time_pair := 1.
  (* end hide *)


  (** [pair']: the monadic version of [pair], which makes a tuple. *)
  Program Definition pair' (a:A) (b:B)
  : {! y !:! A*B !<! c !>! c = time_pair /\ y = pair a b !}
  := += time_pair; <== pair a b.

End map'.


Section fold'.
  Variable A B : Type.

  Definition cost_fold_branch1 := 1.
  Definition cost_fold_branch2 := 1.
  Opaque cost_fold_branch1.
  Opaque cost_fold_branch2.

  Fixpoint cost_fold 
    {f:A->B->A} 
    {cost_f:A->B->nat} l a :=
    match l with
    | nil => cost_fold_branch1
    | cons b t =>
      cost_f a b +
      @cost_fold f cost_f t (f a b) +
      cost_fold_branch2
    end.

  (** [fold']: the monadic version of [fold]. *)
  Program Fixpoint fold' 
    {f:A->B->A} 
    {cost_f:A->B->nat}
    (f':forall a b, 
      {! y !:! A !<! c !>! c = cost_f a b /\ 
        y = f a b !})
    l a
  :{! y !:! _ !<! c !>! c = @cost_fold f cost_f l a /\ 
    y = fold_left f l a !}
  := 
  match l as l' return (l=l')->
  {! y !:! _ !<! c !>! c = @cost_fold f cost_f l a /\
    y = fold_left f l a !}
  with
  | nil =>
    fun hyp =>
    += cost_fold_branch1; <== a
  | cons b t =>
    fun hyp =>
    fab <- f' a b;
    out <- @fold' f cost_f f' t fab;
    += cost_fold_branch2; <== out
  end (eq_refl l).

  (* begin hide *)
  Next Obligation.
    simpl. split; auto. lia.
  Qed.
  (* end hide *)
End fold'.