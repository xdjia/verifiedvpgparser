(** This library is from _Jay McCarthy, Burke Fetscher, Max New, Daniel
  Feltey, and Robert Bruce Findler. 2016. A Coq library for internal
  verification of running-times. In International Symposium on
  Functional and Logic Programming. Springer, 144–162.  *)

(* START: C *)
Definition C (A:Type) (P:A -> nat -> Prop) : Type :=
   {a : A | exists (an:nat), (P a an)}.
(* STOP: C *)
Local Hint Unfold C : monad.

(* START: ret *)
Definition ret (A:Type) (P:A -> nat -> Prop) (a:A) (Pa0:P a 0) : C A P
:= exist (fun x => exists n, P x n) a (ex_intro (fun n => P a n) 0 Pa0).
(* STOP: ret *)
(* Proof.
  exists a.
  exists 0.
  apply Pa0.
Defined. *)

(* START: bind *)
Definition bind (A:Type) (PA:A -> nat -> Prop)
                (B:Type) (PB:B -> nat -> Prop)
                (am:C A PA)
                (bf:forall (a:A) (pa:exists an, PA a an),
                  C B (fun b bn => forall an, PA a an -> PB b (an+bn)))
          : C B PB.
(* STOP: bind *)
Proof.
  destruct am as [a Pa].
  edestruct (bf a Pa) as [b Pb].
  exists b.
  destruct Pa as [an Pa].
  destruct Pb as [bn Pb].
  exists (an + bn).
  eapply Pb.
  apply Pa.
Defined.

(* START: inc *)
Definition inc (A:Type) k (PA : A -> nat -> Prop)
           (xc:C A (fun x xn => forall xm, xn + k = xm -> PA x xm))
: C A PA.
(* STOP: inc *)
Proof.
  destruct xc as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + k).
  apply Px.
  reflexivity.
Defined.

Notation "<== x" := (ret _ _ x _) (at level 55).
Notation "+= k ; c" := (inc _ k _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ _ y (fun (x : _) (am : _) => z))
                           (at level 30, right associativity).
Notation "x >>= y" := (bind _ _ _ _ x y) (at level 55).
Notation "x >> y" := (bind _ _ _ _ x (fun _ => y)) (at level 30, right associativity).

Notation "{! x !:! A !<! c !>!  P !}" := (C A (fun (x:A) (c:nat) => P)) (at level 55). 