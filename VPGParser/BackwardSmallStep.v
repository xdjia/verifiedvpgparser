(** This file verifies the properties of the backward small-step
    relation [Db v I w]. The relation [Db] formalizes how a single parse
    tree is extended in a _backward_ way during running the extraction
    PDA. "Backward" here means that the tree is extended from the rule
    that derives the last symbol of the input string to the rule that
    derives the first symbol. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

Require Import Coq.Program.Equality.
Require Import Misc.

Open Scope list_scope.

Require Import Coq.Unicode.Utf8_core.
Require Import ForwardSmallStep.

Require Import Def.
Require Import Misc.
Require Import Tac.

Import Misc.Basic.
Import Misc.vpg.

Module BackwardSmallStep(G:VPG).

  Module ForwardSmallStep := ForwardSmallStep(G).

  Import ForwardSmallStep.
  Import ForwardSmallStep.DB.


  (** The module [Core] provides the core lemmas used in the correctness
    proof *)
  Module Core.
    Import Misc.Basic.
    Import Misc.vpg.

    (* begin hide *)

    Lemma VBeginSameEq: ∀ v L L', 
      VBeginWith v L -> VBeginWith v L' -> L=L'.
    Proof.
      intros.
      inversion H.
      all: (destruct H1 as [* [* [* [* [* h1]]]]] 
        + destruct H1 as [* [* [* h1]]])
      ; inversion H0
      ; (destruct H1 as [* [* [* [* [* h2]]]]] 
        + destruct H1 as [* [* [* h2]]])
      ; try rewrite h1 in h2.
      all: inversion h2; auto.
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

    Ltac clearRf :=
      repeat match goal with 
      | h: ?v = ?v |- _ => 
      clear h 
      end.

    Ltac instant :=
      match goal with 
      | |- [] = _::_ =>
        instantiate (1:=[])
      | |- [?v1;?v2] = _ ++ [?v2] => 
        instantiate (1:=[v1])
      | |- [?v1;?v2] = _::_ ++ [?v2] => 
        instantiate (2:=v1)
        ; instantiate (1:=[])
      | |- [?v1;?v2;?v3] = _ ++ [?v3] => 
        instantiate (1:=[v1;v2])
      | |- [?v1;?v2;?v3] = _ :: _ ++ [?v3] => 
        instantiate (1:=[v2])
        ; instantiate (1:=v1)
      | |- ?v1::?v2::?v4++[?v3] = _ ++ [?v3] => 
        instantiate (1:=v1::v2::v4)
      | |- ?v1::?v2::?v4++[?v3] = _ :: _ ++ [?v3] => 
        instantiate (1:=v2::v4)
        ; instantiate (1:=v1)
      | |- ?v1::?v2++[?v3] = _ ++ [?v3] => 
        instantiate (1:=v1::v2)
      | |- ?v1::?v2::?v3::?v4 = _ ++ ?v3 :: _ => 
        instantiate (2:=[v1;v2]);
        instantiate (1:=v4)
      | |- ?v1::?v2::?v3 = _ ++ ?v2 :: _ => 
        instantiate (2:=[v1]);
        instantiate (1:=v3)
      | |- ?v1::?v2::?v3::?v4 = _ ++ ?v2 :: _ => 
        instantiate (2:=[v1]);
        instantiate (1:=v3::v4)
      | |- ?v1::?v2++?v3::?v4::?v5 = _ ++ ?v3 :: _ => 
        instantiate (1:=v4::v5)
        ; instantiate (1:=v1::v2)
      | |- ?v1::?v2++[?v3]++?v4::?v5 = _ ++ [?v3] ++ _ => 
        instantiate (1:=v4::v5)
        ; instantiate (1:=v1::v2)
      | |- ?v1::?v2++?v3::?v4 = _ ++ ?v3 :: _ => 
        instantiate (1:=v4)
        ; instantiate (1:=v1::v2)
      | |- [_] ++ ?x = [_] ++ _ =>
        instantiate (1:=x)
      | |- ?v1::?v2::?v3::?x10 ++ [?vb] =
            _ ++ [?vb] =>
        instantiate (1:=v1::v2::v3::x10)
      | |- ?v1::?v2::?v3::?x10 ++ [?vb] =
            _ :: _ ++ [?vb] =>
        instantiate (1:=v2::v3::x10)
      | |- ?v1::?v2::?v3::?x10 ++ ?vb :: ?x11 =
            _ ++ ?vb :: _ =>
        instantiate (1:=x11)
        ; instantiate (1:=v1::v2::v3::x10)
      | |- ?v1::?v2::?v3 ++ ?vb::?v4::?v5 =
            _ ++ ?vb :: _ =>
        instantiate (1:=v4::v5)
        ; instantiate (1:=v1::v2::v3)
      | |- ?v1::?v2::?v3::?v4++[?vb] = _ ++ [?vb] => 
        instantiate (1:=v1::v2::v3::v4)
      | |- ?v1::?v2::?v3::?v4++[?b] = _ :: _ ++ [?b] => 
        instantiate (1:=v2::v3::v4)
        ; instantiate (1:=v1)
      |  |- ?v::?v1::?v2++[?v3]=_++_ => 
        instantiate (1:=v1::v2++[v3])
      | |- [?x1]++?x2++[?x3]++[?vb]=_++[?vb] => 
        instantiate (1:= [x1]++x2++[x3])
      | |- ?x1::?x2++[?x3]++[?vb]=_::_++[?vb] => 
        instantiate (1:= x2++[x3])
        ; instantiate (1:= x1)
      | |- ?x1::?x2++[?x3;?vb]=_++[?vb] => 
        instantiate (1:= x1::x2++[x3])
      | |- ?x1::?x2++[?x3;?vb]=_::_++[?vb] => 
        instantiate (1:= x2++[x3])
      | |- ?x1::?x2++?x3::?vb::?x4=(_++_)++?vb::?x5 => 
        instantiate (1:= x4)
        ; instantiate (1:= x2++[x3])
      | |- ?x1::?x2++?x3::?vb::?x4=_++?vb::_ => 
        instantiate (1:= x4)
        ; instantiate (1:= x1::x2++[x3])
      end.


    Ltac rmEmpRefl :=
      match goal with 
      | h1: [] = [] -> ?h |- _ => 
        assert h as h2 by (apply h1; auto)
        ; clear h1
        ; rename h2 into h1
      end.
    
    Ltac mergeBegins :=
      match goal with
      | h: VBeginWith ?v1 ?L,
        h2: VBeginWith ?v1 ?L1
      |- _
      =>
        destruct (VBeginSameEq _ _ _ h2 h)
        ; subst
      end.

    Ltac rmENE :=
      match goal with 
          | h: _::_=[] |- _ => 
          inversion h 
          end.

    Ltac breakDirect :=
      match goal with 
      | h: ?v -> _, h2: ?v |- _ => 
        destruct (h h2)
        ; clear h
      end.

    Lemma LSameEnd: 
      ∀ {A} (x:list A) a y z t, x++[a]=y++t::z ->
      ∃ w, t::z=w++[a].
    Proof.
      intros.
      generalize dependent y.
      induction z using rev_ind;

      intros y h.
      pose (app_inj_tail _ _ _ _ h).
      destruct a0; subst.
      exists []; auto.

      rewrite app_comm_cons in h.
      rewrite -> app_assoc in h.
      pose (app_inj_tail _ _ _ _ h).
      destruct a0.
      subst.
      exists (t::z).
      auto.
    Qed.

    (* end hide *)

    (** [VBeginWithS]: a parse tree begins with a symbol. *)
    Inductive VBeginWithS : list VE -> var -> symbol -> Prop :=
    | BeginSC v L i: 
      (∃ _v _L, v=[Plnv (PlnE L i _L)]++ _v) 
      -> VBeginWithS v L (Plain i)
    | BeginSA1 v L i: 
      (∃ _v _L, v=[Calv (PndCalE L i _L)]++ _v) 
      -> VBeginWithS v L (Call i)
    | BeginSA2 v L a:
      (∃ _v _b _L1 _L2,  
        v=[Calv (MatCalE L a _L1 _b _L2)]++ _v) 
      -> VBeginWithS v L (Call a)
    | BeginSB v L i: 
      (∃ _v _L, v=[Retv (PndRetE L i _L)]++ _v)
      -> VBeginWithS v L (Ret i).

    (** [PendT]: if a stack has a pending rule as its top, then all 
      rules on the stack must be pending. *)
    Inductive PendT : list RetEdge -> Prop :=
    | PdTE: PendT []
    | PdTC: ∀ T, (∃ L b L1 T', T=(PndRetE L b L1)::T' /\ PendT T')
      -> PendT T.
    (* begin hide *)
    Ltac mergeBeginW :=
      match goal with 
      | h: VBeginWithS (?v) ?L _,
        h2: VBeginWith (?v++_) ?L1 |- _ => 
        inversion h;
        inversion h2;
        repeat (breakEx + breakAnd);
        subst;
        simpl in *;
        simplList;
        subst; auto
      | h: VBeginWithS (?v) ?L _,
        h2: VBeginWith (?v) ?L1 |- _ => 
        inversion h;
        inversion h2;
        repeat (breakEx + breakAnd);
        subst;
        simpl in *;
        simplList;
        subst; auto
      | h: VBeginWithS (?v) ?L _,
        h2: VBeginWithS (?v++_) ?L1 _ |- _ => 
        inversion h;
        inversion h2;
        repeat (breakEx + breakAnd);
        subst;
        simpl in *;
        simplList;
        subst; auto
      | h: VBeginWithS (?v) ?L _,
        h2: VBeginWithS (?v) ?L1 _ |- _ => 
        inversion h;
        inversion h2;
        repeat (breakEx + breakAnd);
        subst;
        simpl in *;
        simplList;
        subst; auto
      end.

    Ltac rmPendMat :=
      match goal with 
      | h: PendT (MatRetE _ _ _ _ _ :: _) |- _ => 
        inversion h
        ; repeat (breakEx+breakAnd)
        ; discriminate
      end.
    
    Ltac invMat :=
      clearRf;
      match goal with 
      | h: MatRetE _ _ _ _ _ = MatRetE _ _ _ _ _
      |- _ =>
        inversion h
        ; subst
        ; clearRf
      end.

    Ltac getAnd :=
      match goal with 
      | |- _ /\ _ => 
        split
      end.
    
    Ltac consMat :=
      match goal with 
      | |- Dm ?x [?a; ?b] 
            ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)] 
            ++ [?vb]) => 
        apply (DMat x x0 x2 x1 x3 [] [] [] [])
      | |- Dm ?x [?a; ?b] 
            ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3);?vb]) => 
        apply (DMat x x0 x2 x1 x3 [] [] [] [])
      | |- Dm ?x [?a; ?b; ?i] 
            ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)]++[?vb;?vc]) => 
          apply (DMat x x0 x2 x1 x3 [] [i] [] [vc])
      | |- Dm ?x (?a :: ?b :: ?i :: ?v)
            ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)] ++ 
              ?vb :: [?ei] ++ ?vc) => 
          apply (DMat x x0 x2 x1 x3 [] (i::v) [] (ei::vc))
      | |- Dm ?x (?a :: ?b :: ?i :: ?v)
            (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)::
              ?vb :: ?ei :: ?vc) => 
          apply (DMat x x0 x2 x1 x3 [] (i::v) [] (ei::vc))
      | |- Dm ?x (?a :: ?b :: ?i)
          (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)::
            ?vb :: ?ei :: ?vc) => 
          apply (DMat x x0 x2 x1 x3 [] (i) [] (ei::vc))
      | |- Dm ?x (?a :: ?v1 :: ?v2 ++ [?b])
          (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)::
            ?v3 :: ?v4 ++ [?vb]) => 
          apply (DMat x x0 x2 x1 x3 (v1::v2) [] (v3::v4) [])
      | |- Dm ?x (?a :: ?v1 :: ?v2 ++ [?b])
          ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)] ++
            ?v3 ++ [?vb]) => 
          apply (DMat x x0 x2 x1 x3 (v1::v2) [] (v3) [])
      | |- Dm ?x (?a :: ?v1 ++ [?b])
          (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3) ::
            ?v3 ++ [?vb]) => 
          apply (DMat x x0 x2 x1 x3 (v1) [] (v3) [])
      | |- Dm _ [] [] =>
        constructor
      end.

    Ltac rmEDv :=
      match goal with 
      | h: Db [] _ _ |- _ => 
      inversion h 
      | h: Db _ _ [] |- _ => 
      inversion h 
      end.

    Ltac rmRetDv :=
      match goal with 
      | h: Db (Retv _ :: _) [] _ |- _ => 
        inversion h
      | h: Db (Retv (MatRetE _ _ _ _ _) :: _) 
          (PndRetE _ _ _ :: _) _ |- _ =>
        inversion h
      end.
    
    Ltac rmBeginMRet :=
      match goal with 
      | h: Retv (MatRetE _ _ _ _ _) :: _ = ?v ++ _,
      h2: VBeginWithS ?v _ _ |- _ => 
        inversion h2;
        repeat breakEx;
        subst;
        discriminate
      end.

    Ltac solveBeginSA :=
      match goal with 
      | |- VBeginWithS _ _ _ => 
        constructor 3
        ; repeat eexists
        ; auto
      end.
    (* end hide *)

    (** [BreakDV]: the invariant of the backward small-step derivation [Db
        v T w]. The invariant [BreakDV] basically shows that we can
        break the parse tree [v] into [v=v1++[rb]++v2], where [rb] is
        the last unmatched return rule, [v1] satisfies the forward
        small-step derivation [Df], and [v2] satisfies [Db].
        Additionally, under certain conditions we can extend [Df] or
        [Db] to the big-step derivation [Dm]: when the stack [T] is
        empty or the top of [T] is a pending rule, then [Db v T w]
        indicates [Dm L v w]; when the top of [T] is a macthing rule,
        the extension is based on whether [v1] and [v2] are empty. *)
    Inductive BreakDV:
      (list VE) -> list RetEdge -> list symbol -> Prop :=
    | BK : ∀ v T w, 
      (Db v T w ->
        (
          (T=[] /\ ∃ Lv, VBeginWith v Lv /\ Dm Lv w v) \/
          (
            (PendT T /\ ∃ Lv, VBeginWith v Lv /\ Dm Lv w v) \/
            (
              ∃ L1 a L2 b L3 t T', 
                t=MatRetE L1 a L2 b L3 /\ T=t::T' /\
                in_rules (L1, Alt_Match (a) (b) L2 L3) P /\
                (
                  (v = [Retv t] /\ w = [Ret b] 
                    /\ in_rules (L3, Alt_Epsilon) P) 
                  \/
                  (∃ v2 w2,
                    v = Retv t::v2 /\ w=(Ret b)::w2 /\
                    Db v2 T' w2 /\ BreakDV v2 T' w2 /\ 
                    (
                      (* Consider w2 *)
                      (∃ L4 a2 L5 b2 L6 w3 v3,
                        w2=Ret b2::w3 /\ 
                        v2=Retv (MatRetE L4 a2 L5 b2 L6) ::v3 /\
                        in_rules (L3, Alt_Epsilon) P) \/
                      (∃ L4 i w3, w2=i::w3 /\
                        VBeginWithS v2 L4 i /\ L3=L4)
                    )
                  ) \/
                  (
                    ∃ Lv v1 w1 i, 
                      v = v1 ++ [Retv t]  /\ 
                      w = i::w1++[Ret b]  /\
                      VBeginWithS v1 Lv i /\ 
                      Dm Lv (i ::w1) v1   /\
                      (∀ v T w, Def.DF.Df v T w 
                        -> (∃ Le, VEndWith v Le /\ VBeginWith v1 Le) 
                        -> Def.DF.Df (v++v1) T (w++i::w1)) /\
                      in_rules (L3, Alt_Epsilon) P /\
                      T'=[]
                  ) \/
                  (
                    ∃ Lv v1 v2 w1 w2 i,
                    v = v1 ++ [Retv t] ++ v2 /\
                    w = w1 ++ [Ret b] ++ w2  /\
                    VBeginWithS v1 Lv i      /\ 
                    Dm Lv w1 v1              /\
                    (∀ v T w, Def.DF.Df v T w -> 
                      (∃ Le, VEndWith v Le /\ VBeginWith v1 Le) 
                      -> Def.DF.Df (v++v1) T (w++w1)) /\
                      Db v2 T' w2 /\ BreakDV v2 T' w2 /\
                    (
                      (* Consider w2 *)
                      (
                        ∃ L4 a2 L5 b2 L6 w3 v3, 
                          w2=Ret b2::w3 /\ 
                          v2=Retv (MatRetE L4 a2 L5 b2 L6) ::v3 /\ 
                          in_rules (L3, Alt_Epsilon) P
                      ) \/
                      (∃ L4 i w3, w2=i::w3 
                        /\ VBeginWithS v2 L4 i /\ L3=L4)
                    )
                  )
                )
            )
          )))
        -> BreakDV v T w.


    (* begin hide *)
    Lemma mergeBeginS: ∀ v L i L1, 
      VBeginWith v L -> VBeginWithS v L1 i -> L=L1.
    Proof.
      intros.
      
      inversion H;
      inversion H0;
      repeat breakEx;
      subst;
      inversion H4; auto.
    Qed.
    (* end hide *)


    (** [L4_2]: Lemma 4.2 shows the backward small-step derivation [Db]
      satisfies [BreakDV]. *)
    Lemma L4_2: ∀ v T w, BreakDV v T w.
    (* begin hide *)
    Proof.
      constructor.
      intros HvTw.
      induction HvTw.


      (* V_S_Pln *)
      1: {
        (* split.
        apply BeginC.
        exists [].
        simpl.
        eauto. *)

        left.
        split; auto.
        exists L.
        constructor; auto.
        apply BeginC; exists []; simpl; eauto.
        constructor; auto.
        constructor; auto.
      }


      (* V_Pln_b1 *)
      1: {
        repeat (breakOr;
          repeat (breakEx + breakAnd);
          try mergeBegins; auto; 
          subst;
          try discriminate).

        try ((right+left);
          repeat (breakEx + breakAnd);
          repeat eexists;
          try simplList; 
          simpl in *;
          subst;
          auto;
          try discriminate).

        left;
        split; auto.
        exists L.
        split; auto; constructor; auto.
        repeat eexists.
        inversion HvTw; subst; auto;
        inversion H2; 
        repeat (breakEx + breakAnd);
        repeat simplList; subst; auto;
        inversion H3; subst; auto.
      }

      (* Plain + matret *)
      1: {
        repeat (breakOr;
          repeat (breakEx + breakAnd);
          try mergeBegins; auto; 
          subst;
          try discriminate).

        all: try inversion H2;
          repeat (breakEx + breakAnd);
          repeat simplList; subst; clearRf.

        all: ((right+left);
          repeat (breakEx + breakAnd);
          repeat eexists;
          try simplList; 
          simpl in *;
          subst;
          auto;
          try discriminate).

        1:{
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          left.
          repeat addEx.
          repeat split; eauto.
          instant; auto.
          instant; auto.
          constructor; repeat eexists.
          constructor; auto.
          constructor; auto.

          intros. 
          constructor; eauto.
          breakAll. mergeBegin; eauto.

          inversion HvTw; subst; auto.
          inversion H13.
        }

        1:{
          right.
          do 7 eexists.
          repeat split; eauto.
          right.
          right.
          right.
          repeat addEx.
          split; eauto.
          instant; auto.
          split; eauto.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          constructor; auto.
          constructor; auto.
          constructor; auto.
          split; eauto.

          intros. 
          constructor; eauto.
          breakAll. mergeBegin; eauto.

          split; eauto.
          split; eauto.
          left.
          repeat addEx.
          split; eauto.
        }

        1:{
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          right.
          repeat addEx.
          split; eauto.
          instant; auto.
          split; eauto.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          constructor; auto.
          constructor; auto.
          constructor; auto.
          split; eauto.

          intros. 
          constructor; eauto.
          breakAll. mergeBegin; eauto.
          split; eauto.
          split; eauto.
          right.
          repeat addEx.
          split; eauto.
        }

        1:{
          inversion H6.
          repeat (breakEx + breakAnd).
          subst.
          inversion HvTw.
        }

        1: {
          inversion HvTw; subst;
          inversion H6; subst;
          repeat (breakEx + breakAnd);
          subst;
          discriminate.
        }

        1:{
          inversion HvTw; subst;
          inversion H6; subst;
          repeat (breakEx + breakAnd);
          subst;
          discriminate.
        }
      }



      (* Plain + Call *)
      1: {
        repeat (breakOr;
          repeat (breakEx + breakAnd);
          try mergeBegins; auto; 
          subst;
          try discriminate).

        1:{
          left.
          split; auto.
          exists L.
          split; auto.
          constructor.
          repeat addEx; eauto.
          constructor; auto.
        }

        1:{
          inversion H2.
          left.
          split; auto.
          exists L.
          split; auto.
          constructor.
          repeat addEx; eauto.
          constructor; auto.

          right; left.
          split; auto.
          exists L.
          split; auto.
          constructor.
          repeat addEx; eauto.
          constructor; auto.
        }

        1:{
          right.
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          left.
          repeat addEx.
          split; eauto.
          simpl.
          instant; auto.
          split; eauto.
          rewrite H3.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          constructor; auto.
          constructor; auto.
          mergeBeginW.
          split; eauto.

          intros.
          match goal with
          | |- DF.Df (?v++?e::?v') ?T (?w++?i::?w') =>
            pose (H7 (v++[e]) T (w++[i])) as d
            ; repeat rewrite <- app_assoc in d
            ; apply d
          end.
          constructor; eauto.
          breakAll. 
          Ltac mergeBegin :=
            match goal with 
            | h: VBeginWith [?e] ?L
            |- _ =>
              inversion h; repeat breakEx; subst;
              simplList; subst
            | h: VBeginWith (?e::_) ?L
              |- _ =>
                inversion h; repeat breakEx; subst;
                simpl in *;
                simplList; subst
            | h: VBeginWith (?e++_) ?L
              |- _ =>
                inversion h; repeat breakEx; subst;
                simpl in *;
                simplList; subst
            end.
          mergeBegin; eauto.

          exists L1.
          split; eauto.
          Ltac tryResolveEnd :=
            match goal with
            | |- VEndWith (?x++_) _ =>
              try_resolve_end_with x
            end.
          tryResolveEnd.
          
          apply (VListBeginSame _ _ _ H0).
          destruct x6.
          inversion H5; subst; breakAll; discriminate.
          eauto using nil_cons.
        }

        1:{
          right.
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          right.
          repeat addEx.
          split; eauto.
          simpl.
          instant; auto.
          split; eauto.
          rewrite H3.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          split; eauto.
          constructor; auto.
          mergeBeginW.
          split; eauto.

          1:{
            intros.
            match goal with
            | |- DF.Df (?v++?e::?v') ?T (?w++?i::?w') =>
              pose (H7 (v++[e]) T (w++[i])) as d
              ; repeat rewrite <- app_assoc in d
              ; apply d
            end.
            constructor; eauto.
            breakAll. 

            mergeBegin; eauto.
    
            exists L1.
            split; eauto.
            tryResolveEnd.
            
            apply (VListBeginSame _ _ _ H0).
            destruct x6.
            inversion H5; subst; breakAll; discriminate.
            eauto using nil_cons.
          }

          split; eauto.
          split; eauto.
          left.
          repeat eexists; auto.
        }

        1:{
          right.
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          right.
          repeat addEx.
          split; eauto.
          simpl.
          instant; auto.
          split; eauto.
          rewrite H3.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          split; eauto.
          constructor; auto.
          mergeBeginW.
          split; eauto.

          1:{
            intros.
            match goal with
            | |- DF.Df (?v++?e::?v') ?T (?w++?i::?w') =>
              pose (H7 (v++[e]) T (w++[i])) as d
              ; repeat rewrite <- app_assoc in d
              ; apply d
            end.
            constructor; eauto.
            breakAll. 

            mergeBegin; eauto.
    
            exists L1.
            split; eauto.
            tryResolveEnd.
            
            apply (VListBeginSame _ _ _ H0).
            destruct x6.
            inversion H5; subst; breakAll; discriminate.
            eauto using nil_cons.
          }

          split; eauto.
          split; eauto.
          right.
          repeat eexists; auto.
        }
      }

      (* Plain + Plain *)
      1: {
        repeat (breakOr;
          repeat (breakEx + breakAnd);
          try mergeBegins; auto; 
          subst;
          try discriminate).

        1:{
          left.
          split; auto.
          exists L.
          split; auto.
          constructor.
          repeat addEx; eauto.
          constructor; auto.
        }

        1:{
          inversion H2.
          left.
          split; auto.
          exists L.
          split; auto.
          constructor.
          repeat addEx; eauto.
          constructor; auto.

          right; left.
          split; auto.
          exists L.
          split; auto.
          constructor.
          repeat addEx; eauto.
          constructor; auto.
        }

        1:{
          right.
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          left.
          repeat addEx.
          split; eauto.
          simpl.
          instant; auto.
          split; eauto.
          rewrite H3.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          constructor; auto.
          constructor; auto.
          mergeBeginW.

          split; eauto.

          1:{
            intros.
            match goal with
            | |- DF.Df (?v++?e::?v') ?T (?w++?i::?w') =>
              pose (H7 (v++[e]) T (w++[i])) as d
              ; repeat rewrite <- app_assoc in d
              ; apply d
            end.
            constructor; eauto.
            breakAll. 

            mergeBegin; eauto.
    
            exists L1.
            split; eauto.
            tryResolveEnd.
            
            apply (VListBeginSame _ _ _ H0).
            destruct x6.
            inversion H5; subst; breakAll; discriminate.
            eauto using nil_cons.
          }
          
        }

        1:{
          right.
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          right.
          repeat addEx.
          split; eauto.
          simpl.
          instant; auto.
          split; eauto.
          rewrite H3.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          split; eauto.
          constructor; auto.
          mergeBeginW.
          split; eauto.

          1:{
            intros.
            match goal with
            | |- DF.Df (?v++?e::?v') ?T (?w++?i::?w') =>
              pose (H7 (v++[e]) T (w++[i])) as d
              ; repeat rewrite <- app_assoc in d
              ; apply d
            end.
            constructor; eauto.
            breakAll. 

            mergeBegin; eauto.
    
            exists L1.
            split; eauto.
            tryResolveEnd.
            
            apply (VListBeginSame _ _ _ H0).
            destruct x6.
            inversion H5; subst; breakAll; discriminate.
            eauto using nil_cons.
          }
          split; eauto.
          split; eauto.
          left.
          repeat eexists; auto.
        }

        1:{
          right.
          right.
          repeat addEx.
          repeat split; eauto.
          right.
          right.
          right.
          repeat addEx.
          split; eauto.
          simpl.
          instant; auto.
          split; eauto.
          rewrite H3.
          instant; auto.
          split; eauto.
          constructor. repeat eexists.
          split; eauto.
          constructor; auto.
          mergeBeginW.
          split; eauto.
          1:{
            intros.
            match goal with
            | |- DF.Df (?v++?e::?v') ?T (?w++?i::?w') =>
              pose (H7 (v++[e]) T (w++[i])) as d
              ; repeat rewrite <- app_assoc in d
              ; apply d
            end.
            constructor; eauto.
            breakAll. 

            mergeBegin; eauto.
    
            exists L1.
            split; eauto.
            tryResolveEnd.
            
            apply (VListBeginSame _ _ _ H0).
            destruct x6.
            inversion H5; subst; breakAll; discriminate.
            eauto using nil_cons.
          }
          split; eauto.
          split; eauto.
          right.
          repeat eexists; auto.
        }
      }

      (* V_Cal_Pnd_S *)
      1: {
        left.
        split; auto.
        exists L.
        split; auto.
        constructor 2; auto.
        repeat eexists.
        constructor; auto.
        constructor; auto.
      }

      (* V_Cal_Pnd_bot *)
      1: {
        left.
        split; auto.
        exists L.
        split; auto.
        constructor 2; auto.
        repeat eexists.
        constructor; auto.

        repeat (breakOr;
          repeat (breakEx + breakAnd);
          try mergeBegins; auto; 
          try discriminate).
      }


      (* V_Cal_b1 *)
      1: {
        repeat (breakOr;
          repeat (breakEx + breakAnd);
          subst;
          try (mergeBegins; auto); 
          try discriminate).

          destruct T.
          left; auto.
          split; auto.
          exists L. 
          split; auto; 
          constructor 2;
          repeat eexists.
          auto.
          auto.

          right; left.
          inversion H2.
          repeat (breakEx + breakAnd).
          simplList. subst.
          split; auto.
          exists L.
          split; 
          constructor 2;
          repeat eexists; auto.
      }
    

      (* V_Cal_b2 *)
      1: {
        repeat (breakAnd + breakOr + breakEx + simplList);
          subst;
          try invMat;
          try discriminate;
          try rmPendMat.

        1:{
          (* w1=v1=w2=v2=[] *)

          left.
          inversion HvTw; subst;
            repeat (getAnd + addEx + constructor 3); 
            auto.

          all: repeat (consMat + constructor + rmEDv); auto.
        }

        Ltac selectBranch :=
          match goal with 
          | |- _\/_ => 
            (left
            ; repeat (addEx)
            ; getAnd
            ; [match goal with 
              | |- [_] = [_] =>
                auto
              | |- [_] ++ [_; ?vb] = _ ++ [?vb] =>
                auto
              | |- _ =>
                fail
              end | ])
            + right
          | |- _ =>
            fail
          end.

        1:{ (* w1=v1=[], v2 ≠ [] *)

          right.
          right.
          inversion H6; subst;
          repeat (getAnd + addEx + 
            constructor 3 + rmRetDv + breakAnd + breakOr); 
            auto.

          all: repeat selectBranch.

          Ltac complex1 :=
            intros; breakAll;
            match goal with
            | |- DF.Df (?v++[Calv ?e;?v']) ?T (?w++?i::?w') =>
              assert (DF.Df (v++[Calv e]) (e::T) (w++[i])) as d
            end;
            [constructor; eauto |];
            mergeBegin; eauto;
            match goal with
            | h: DF.Df (?v++[Calv (MatCalE ?a ?b ?c ?d ?e)]) (_::?T) (?w++?i) |- _ =>
              assert (DF.Df (v++[Calv (MatCalE a b c d e)]++[Retv (MatRetE a b c d e)]) T (w++i++[Ret d]))
            end;
            [do 2 rewrite app_assoc |];
            [
              match goal with
              | h: VBeginWith [Calv (MatCalE _ _ ?x _ _);_] _ |- _ =>
                apply DF.V_Ret with (L:=x)
              end
              ; eauto; tryResolveEnd|];
              simpl in *; eauto.

          all: repeat (getAnd + simpl + 
            (instant; auto) + addEx + 
            solveBeginSA + consMat + complex1); auto.


          all: 
            (* consider the Db ind *)
            match goal with 
            | h: Db ?v ?t ?u, 
              h2: BreakDV ?v ?t ?u |- _ => 
              inversion h2;
              breakDirect
            end;
            
            repeat (breakEx + breakAnd + breakOr +
              discriminate + rmPendMat + simplList + subst);
              try discriminate;
              try rmEDv;
              try rmBeginMRet;
              auto.
          
          all: invMat.
          all: 
            (* The last two branches *)
            try (
              right;
              inversion H14; subst; eauto;
              repeat (addEx + getAnd); subst; eauto;
              inversion H13;
              repeat (breakEx); simplList; subst; eauto;
              constructor; repeat eexists; fail).
        all: try 
          (left;
            inversion H13;
            repeat (addEx + getAnd); subst; eauto;
            repeat (breakEx); try simplList; subst; eauto;
            try constructor; repeat eexists; fail).
        }



        1:{ (* w1=v1=[], v2 ≠ [], v2 starts linearly *)

          inversion H7; subst;
          breakDirect;
          inversion H9; subst;
          repeat (getAnd + addEx + 
            constructor 3 + rmRetDv + breakAnd + breakOr
            + breakEx + simplList); 
            auto;
            subst.

          all: try mergeBeginW.

          all: try (  
            left;
            inversion HvTw; subst;
              repeat (getAnd + addEx + constructor 3); 
              auto;

            repeat (consMat + constructor + rmEDv); auto;
            inversion H15; subst; auto;
            inversion H1; subst; auto;
            fail).

          (* NOTE 27 *)
          (* 下面这个得删除unshelve *)

          all: try (
            (* w1=v1=w2=v2=[] *)

            right; left;
            repeat (getAnd + (exists x) + (do 5 eexists) +
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst;

            repeat (consMat + constructor + rmEDv); auto;
            inversion H6; subst; auto;
            inversion H1; subst; auto;
            fail).

          (* NOTE 9 *)

          repeat selectBranch.
          
          repeat (getAnd + addEx + 
          constructor 3 + rmRetDv + breakAnd + breakOr
          + breakEx + simplList); 
          auto; subst.
          Ltac selectBranch2 :=
            match goal with 
            | |- _\/_ => 
              (left
              ; repeat (addEx)
              ; getAnd
              ; [match goal with 
                | |- [_] = [_] =>
                  auto
                | |- [_] ++ [_; ?vb] = _ ++ [?vb] =>
                  auto
                | |- _::_::_::_ ++ [?vb] = _ ++ [?vb] =>
                  auto
                | |- _ =>
                  fail
                end | ])
              + right
            | |- _ =>
              fail
            end.

          repeat selectBranch2.
          
          1,2: repeat (getAnd + simpl + 
            (instant; auto) + 
            addEx + 
            solveBeginSA + consMat); auto.

          Ltac try_resolve_begin_with x :=
            (apply BeginA1+ apply BeginA2 + apply BeginC + apply BeginB);
                    exists x; repeat eexists; fail.

          Ltac tryResolveBegin :=
            match goal with
            | |- VBeginWith (_::?x) _ =>
              try try_resolve_begin_with x
            | |- VBeginWith (_++?x) _ =>
              try try_resolve_begin_with x
            end.

          Ltac complex2 :=
            intros; breakAll;
            (* 先搞出来然后用H13 *)
            match goal with
            |  |- DF.Df (?v ++ Calv ?ea :: Retv ?eb :: ?v') ?T (?w ++ Call ?a :: Ret ?b :: ?w' ) =>
              assert (DF.Df (v ++ [Calv ea]) (ea::T) (w++[Call a]))
              by (constructor; eauto; mergeBegin; eauto)
            end;
            match goal with
            | h: DF.Df (?v ++ [Calv ?ea]) (?ea::?T) (?w++[Call ?a]) 
            |- DF.Df (?v ++ Calv (MatCalE _ ?a ?L1 ?b ?L2) :: Retv ?eb :: ?v') ?T (?w ++ Call ?a :: Ret ?b :: ?w' ) =>
              assert (DF.Df ((v ++ [Calv ea]) ++ [Retv eb]) (T) ((w++[Call a])++[Ret b])) by
              (apply DF.V_Ret with (L:=L1); eauto; tryResolveEnd)
            end;
            match goal with
            | h: DF.Df ((?v ++ [Calv ?ea]) ++ [Retv ?eb]) (?T) ((?w++[Call ?a])++[Ret ?b]),
              H: forall _ _ _, _ -> _ |- _ =>
              pose (H _ _ _ h) as _h
              ; repeat  rewrite <- app_assoc in _h
              ; apply _h
            end;
            match goal with
            | |- ∃ _, VEndWith (?v++_++[Retv (MatRetE _ _ _ _ ?L2)]) _ /\ _ =>
              exists L2
              ; getAnd; eauto
            end;
            [rewrite app_assoc; tryResolveEnd | tryResolveBegin].
          
          complex2.

          all: repeat selectBranch2;
            repeat (getAnd + addEx + 
            constructor 3 + rmRetDv + breakAnd + breakOr + complex2
            + breakEx + simplList); 
            auto; subst;
            repeat selectBranch2;

            repeat (getAnd + simpl + complex2 +
              (instant; simpl; auto) + 
              addEx + 
              solveBeginSA + consMat); auto;

            try rewrite H10;

            repeat (getAnd + simpl + complex2 +
              (instant; simpl; auto) + 
              addEx + 
              solveBeginSA + consMat); auto;

            (* The last two branches *)
            (left+right);
            repeat (addEx + getAnd + complex2); subst; eauto; fail.
        }

        1: { (* v1=b+, v2=[] *)

          inversion H6; subst;
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr
            + breakEx + simplList); 
            subst.
          inversion HvTw.
        }

        1:{ (* w1=b+, v2=b+ *)
          inversion H6; subst;
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr
            + breakEx + simplList); 
            subst;
          inversion HvTw.
        }

        1:{ (* w1=b+, v2=b+ *)
          inversion H6; subst;
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr
            + breakEx + simplList); 
            subst;
          inversion HvTw.
        }
      }


      
      (* V_Cal_a *)
      1: {
        
        repeat (breakAnd + breakOr + breakEx + simplList);
          subst;
          try invMat;
          try discriminate;
          try rmPendMat.

        1: {
          (* w1=v1=w2=v2=[] *)
          
          left.
          
          (* inversion HvTw; subst; *)
          repeat (getAnd + addEx + constructor 3 + 
            (instant; auto)); 
          auto.

          repeat (consMat + constructor + rmEDv); auto.
          mergeBeginW.
        }



        (* 1:{
          admit.
        } *)
        1:{ (* w1=i+, v2 ≠ [] *)

          right; right.

          rewrite H5.
          
          inversion H9; subst;
            repeat (getAnd + addEx + 
            constructor 3 + rmRetDv + breakAnd + breakOr); 
            auto.


          Ltac selectBranch3 :=
            match goal with 
            | |- _\/_ => 
              (left
              ; repeat (addEx)
              ; getAnd
              ; [match goal with 
                | |- [_] = [_] =>
                  auto
                | |- [_] ++ [_; ?vb] = _ ++ [?vb] =>
                  auto
                | |- [_] ++ _ ++ _ ++ [?vb] = _ ++ [?vb] =>
                  auto
                | |- _ =>
                  fail
                end | ])
              + right
            | |- _ =>
              fail
            end.


          all: repeat selectBranch3.


          repeat (getAnd + simpl + 
            (instant; simpl;
            repeat rewrite <- app_assoc; auto) + addEx + 
            solveBeginSA + consMat); auto.
            
          repeat (getAnd + simpl + 
            (instant; simpl;
            repeat rewrite <- app_assoc; auto) + addEx + 
            solveBeginSA + consMat); auto.
            

          mergeBeginW.

          Ltac complex3 :=
            intros; breakAll;
            (* 先搞出来然后用H13 *)
            match goal with
            |  |- DF.Df (?v ++ Calv ?ea :: ?v2 ++ [Retv ?eb]) ?T (?w ++ Call ?a :: ?w2++ [Ret ?b]) =>
              assert (DF.Df (v ++ [Calv ea]) (ea::T) (w++[Call a]))
              by (constructor; eauto; mergeBegin; eauto)
            end;
            
            match goal with
            | H: forall _ _ _, _ -> _,
            h: DF.Df (?v ++ [Calv ?ea]) (?ea::?T) (?w ++ [Call ?a])
            |- DF.Df (?v ++ Calv ?ea :: ?v2 ++ [Retv ?eb]) ?T (?w ++ Call ?a :: ?w2++ [Ret ?b]) =>
            assert (DF.Df (v ++ [Calv ea] ++ v2) (ea::T) (w++[Call a]++w2))
            ; pose (H _ _ _ h) as _e
            ; do 2 rewrite <- app_assoc in _e
            ; [apply _e|]
            ; clear _e
            ; [match goal with
              | |- ∃ _, VEndWith (?v++[Calv (MatCalE _ _ ?L2 _ _)]) _ /\ _ =>
                exists L2; getAnd; eauto
              end |]
            end;
            try tryResolveEnd;
            try match goal with
            | h: VBeginWith (?x ++ _) ?L,
            H: VBeginWithS ?x _ _ |- VBeginWith ?x ?L =>
              apply (VListBeginSame _ _ _ h)
              ; destruct x
              ; inversion H
              ; breakAll
              ; try discriminate
            end;
            
            match goal with
            | H: forall _ _ _, _ -> _,
            h: DF.Df (?v ++ [Calv ?ea] ++ ?v2) (?ea::?T) (?w ++ [Call ?a] ++ ?w2)
            |- DF.Df (?v ++ Calv ?ea :: ?v2 ++ [Retv ?eb]) ?T (?w ++ Call ?a :: ?w2++ [Ret ?b]) =>
              assert (DF.Df (v ++ [Calv ea] ++ v2 ++ [Retv eb]) (T) (w++[Call a]++w2 ++ [Ret b]))
            end;
            repeat rewrite app_assoc;

            match goal with
            | h: Dm ?L ?w ?v |- _ =>
              assert (w!=[]) as _h
              by (destruct w; simpl in *; discriminate; eauto using nil_cons)
              ; pose (ForwardSmallStep.Core.L5_2 _ _ _ h _h)
              ; breakAll
            end;

            [match goal with
            | h: VEndWith ?x ?Lx |- _ =>
              apply (DF.V_Ret) with (L:=Lx); eauto
            end|];
            
            try match goal with
            | h: VEndWith ?x ?Lx |- VEndWith (?v++?x) ?Lx =>
              apply (VListEndSame2 _ v _ h)
            end;

            repeat rewrite <- app_assoc; eauto.
          complex3.


          all: repeat (getAnd + simpl + complex3 +
            (instant; simpl;
            repeat rewrite <- app_assoc; auto) + addEx + 
            solveBeginSA + consMat); auto.


          all: try match goal with 
          |  |- Dm _ _ _ => 
            mergeBeginW
          end.

          all: try 
            (* consider the Db ind *)
          match goal with 
            | h: Db ?v ?t ?u, 
            h2: BreakDV ?v ?t ?u |- BreakDV _ _ _ => 
            inversion h2;
            breakDirect
            end;
            
            repeat (breakEx + breakAnd + breakOr + complex3 +
            discriminate + rmPendMat + simplList + subst);
            try discriminate;
            try rmEDv;
            try rmBeginMRet;
            auto.

          all: 
            (* The last two branches *)
            try inversion H18; subst; eauto;
            inversion H17;
            repeat breakEx; subst; try (simplList; subst).

          all: try (right; (do 3 eexists); getAnd; eauto; getAnd; eauto; subst;
              constructor; ((eexists [] + exists x4); simpl; eauto; fail)).


          all: try (left; (do 7 eexists); getAnd; eauto; getAnd; eauto; subst;
              constructor; ((eexists [] + exists x4); simpl; eauto; fail)).

          right. exists x16. do 2 eexists; eauto.
          
          getAnd; eauto; eauto; subst; constructor; eauto.
          constructor. eexists x4, x8. eauto.

        }



        Ltac rmBeginMRetS :=
          match goal with 
          | h: VBeginWithS [Retv (MatRetE _ _ _ _ _)] _ _ 
          |- _ => 
            inversion h;
            repeat breakEx;
            subst;
            discriminate
          | h: VBeginWithS (Retv (MatRetE _ _ _ _ _)::_) _ _ 
            |- _ => 
              inversion h;
              repeat breakEx;
              subst;
              discriminate
          | h: ?v ++ _ = Retv (MatRetE _ _ _ _ _) :: _ ,
            h2: VBeginWithS ?v _ _ |- _ => 
              inversion h2;
              repeat breakEx;
              subst;
              discriminate
          end.

        1:{ (* w1=i+, v2 ≠ [] *)
          rewrite H5.
          inversion H10; breakDirect;
          repeat (breakAnd + breakOr + breakEx + simplList);
          subst;
          try invMat;
          try discriminate;
          try rmBeginMRetS;
          try rmPendMat.

          4:{
            rewrite H16.

            (* inversion H9; breakDirect;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            subst. *)

            right.
            right.
            repeat addEx.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst.
            right.
            right.
            right.

            repeat addEx.
            
            split.

            Ltac instant3 := 
            match goal with 
            | |- [?v1]++?v2++[?v3]++?v4++[?vb]++?v5::?v6 
                  = _ ++ [?vb] ++ _ => 
              instantiate (1:=v5::v6)
              ; instantiate (1:=[v1]++v2++[v3]++v4)
            | |- ?v1::?v2++[?v3]++?v4++[?vb]++?v5::?v6 
                  = _ ++ [?vb] ++ _ => 
              instantiate (1:=v5::v6)
              ; instantiate (1:=[v1]++v2++[v3]++v4)
            end.

            repeat (getAnd +
              (instant3; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            repeat (getAnd +
              (instant3; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            match goal with 
            | |- Dm ?x ([?a] ++ ?v1 ++ [?b] ++ ?v2)
              ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)] ++
                ?v4 ++ [?vb] ++ ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.

            Ltac complex4 :=
              intros; breakAll;
              (* 先搞出来然后用H13 *)
              match goal with
              |  |- DF.Df (?v ++ [Calv ?ea] ++ ?v2 ++ [Retv ?eb] ++ _) ?T (?w ++ [Call ?a] ++ ?w2++ [Ret ?b] ++ _) =>
                assert (DF.Df (v ++ [Calv ea]) (ea::T) (w++[Call a]))
                by (constructor; eauto; mergeBegin; eauto)
              end;
              
              match goal with
              | H: forall _ _ _, _ -> _,
                h: DF.Df (?v ++ [Calv ?ea]) (?ea::?T) (?w ++ [Call ?a])
              |- DF.Df (?v ++ [Calv ?ea] ++ ?v2 ++ [Retv ?eb] ++ _) ?T (?w ++ [Call ?a] ++ ?w2++ [Ret ?b] ++ _) 
              =>
                assert (DF.Df (v ++ [Calv ea] ++ v2) (ea::T) (w++[Call a]++w2))
                ; pose (H _ _ _ h) as _e
                ; do 2 rewrite <- app_assoc in _e
                ; [apply _e|]
                ; clear _e
                ; [match goal with
                  | |- ∃ _, VEndWith (?v++[Calv (MatCalE _ _ ?L2 _ _)]) _ /\ _ =>
                    exists L2; getAnd; eauto
                  end |]
                end;
                try tryResolveEnd;
                try match goal with
                | h: VBeginWith (?x ++ _) ?L,
                H: VBeginWithS ?x _ _ |- VBeginWith ?x ?L =>
                  apply (VListBeginSame _ _ _ h)
                  ; destruct x
                  ; inversion H
                  ; breakAll
                  ; try discriminate
                end;
              
              match goal with
              | H: forall _ _ _, _ -> _,
              h: DF.Df (?v ++ [Calv ?ea] ++ ?v2) (?ea::?T) (?w ++ [Call ?a] ++ ?w2)
              |- DF.Df (?v ++ [Calv ?ea] ++ ?v2 ++ [Retv ?eb] ++ _) ?T (?w ++ [Call ?a] ++ ?w2++ [Ret ?b] ++ _) =>
                assert (DF.Df (v ++ [Calv ea] ++ v2 ++ [Retv eb]) (T) (w++[Call a]++w2 ++ [Ret b]))
              end;
              repeat rewrite app_assoc;

              match goal with
              | h: Dm ?L ?w ?v |- _ =>
                assert (w!=[]) as _h
                by (destruct w; simpl in *; discriminate; eauto using nil_cons)
                ; pose (ForwardSmallStep.Core.L5_2 _ _ _ h _h)
                ; breakAll
              end;

              [match goal with
                | h: VEndWith ?x ?Lx |- _ =>
                apply (DF.V_Ret) with (L:=Lx); eauto
              end|];
              
              try match goal with
              | h: VEndWith ?x ?Lx |- VEndWith (?v++?x) ?Lx =>
                apply (VListEndSame2 _ v _ h)
              end;

              repeat rewrite <- app_assoc; eauto;

              match goal with
              | H: forall _ _ _, _ -> _,
                h: DF.Df (?v ++ [Calv ?ea] ++ ?v2 ++ [Retv ?eb]) ?T (?w ++ [Call ?a] ++ ?w2++ [Ret ?b])
              |- DF.Df (?v ++ [Calv ?ea] ++ ?v2 ++ [Retv ?eb] ++ _) ?T (?w ++ [Call ?a] ++ ?w2++ [Ret ?b] ++ _) =>
                pose (H _ _ _ h) as _e 
                ; repeat rewrite <- app_assoc in _e
                ; apply _e
                ; clear _e
              end;

              match goal with
              | |- ∃ _, VEndWith (_ ++ _ ++ _ ++ [Retv (MatRetE _ _ _ _ ?Lx)]) _ /\ _ =>
                exists Lx
                ; split; eauto
              end;
              repeat rewrite app_assoc;
              [tryResolveEnd|];
              
              match goal with
              | h: VBeginWithS ?x _ _,
                h2: VBeginWithS (?x++_) _ _ |- VBeginWith ?x ?L =>
                destruct x
                ; inversion h
                ; breakAll; subst; try discriminate
                ; inversion h2; breakAll; subst; eauto
                ; simpl in *; simplList; tryResolveBegin
              end.

            complex4.


            left.
            repeat (getAnd +
            (instant3; simpl; repeat rewrite <- app_assoc;
              auto) + 
            addEx + 
            solveBeginSA + consMat); auto.
          
          }

          1:{
            left;
            repeat (getAnd + addEx + constructor 3 + 
            (instant; auto)); 
            auto;
            repeat (consMat + constructor + rmEDv); auto;
            mergeBeginW.
            all: mergeBeginW.
          }

          1:{
            right; left;
            repeat (getAnd + addEx + constructor 3 + 
            (instant; auto)); 
            auto;
            repeat (consMat + constructor + rmEDv); auto;
            mergeBeginW.
            all: mergeBeginW.
          }

          Ltac selectBranch4 :=
            match goal with 
            | |- _\/_ => 
              (left
              ; repeat (addEx)
              ; getAnd
              ; [match goal with 
                | |- [_] = [_] =>
                  auto
                | |- [_] ++ [_; ?vb] = _ ++ [?vb] =>
                  auto
                | |- [_] ++ _ ++ _ ++ [?vb] = _ ++ [?vb] =>
                  auto
                | |- [_] ++ _ ++ _ ++ _ ++ [?vb]
                        = _ ++ [?vb] =>
                  auto
                | |- _ =>
                  fail
                end | ])
              + right
            | |- _ =>
              fail
            end.


          1:{
            inversion H10; breakDirect;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            subst.

            repeat selectBranch4.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst.
            
            repeat selectBranch4.

            Ltac instant2 := 
            match goal with 
            | |- [?v1]++?v2++[?v3]++?v4++[?vb] = _ ++ [?vb] => 
              instantiate (1:=v1::v2++v3::v4)
            | |- ?v1::?v2++[?v3]++?v4::?v5++[?vb] = 
                _ :: _ ++ [?vb] => 
              instantiate (1:=v2++v3::v4::v5)
            end.

            repeat (getAnd +
              (instant2; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            repeat (getAnd +
              (instant2; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            match goal with 
            | |- Dm ?x (?a :: ?v1 ++ ?b :: ?v2 :: ?v3)
              (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)::
                ?v4 ++ ?vb :: ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2::v3) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            repeat mergeV; subst; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.

            Ltac complex5 :=
              intros; breakAll;
              (* 先搞出来然后用H13 *)
              match goal with
              |  |- DF.Df (?v ++ Calv ?ea:: ?v2 ++ Retv ?eb:: _) ?T (?w ++Call ?a :: ?w2++ Ret ?b:: _) =>
                assert (DF.Df (v ++ [Calv ea]) (ea::T) (w++[Call a]))
                by (constructor; eauto; mergeBegin; eauto)
              end;
              
              match goal with
              | H: forall _ _ _, _ -> _,
                h: DF.Df (?v ++ [Calv ?ea]) (?ea::?T) (?w ++ [Call ?a])
              |- DF.Df (?v ++ Calv ?ea:: ?v2 ++ Retv ?eb:: _) ?T (?w ++Call ?a :: ?w2++ Ret ?b:: _)
              =>
                assert (DF.Df (v ++ [Calv ea] ++ v2) (ea::T) (w++[Call a]++w2))
                ; pose (H _ _ _ h) as _e
                ; do 2 rewrite <- app_assoc in _e
                ; [apply _e|]
                ; clear _e
                ; [match goal with
                  | |- ∃ _, VEndWith (?v++[Calv (MatCalE _ _ ?L2 _ _)]) _ /\ _ =>
                    exists L2; getAnd; eauto
                  end |]
              end;
              try tryResolveEnd;
              try match goal with
                | h: VBeginWith (?x ++ _) ?L,
                H: VBeginWithS ?x _ _ |- VBeginWith ?x ?L =>
                  apply (VListBeginSame _ _ _ h)
                  ; destruct x
                  ; inversion H
                  ; breakAll
                  ; try discriminate
              end;
              
              match goal with
              | H: forall _ _ _, _ -> _,
              h: DF.Df (?v ++ [Calv ?ea] ++ ?v2) (?ea::?T) (?w ++ [Call ?a] ++ ?w2)
              |-  DF.Df (?v ++ Calv ?ea:: ?v2 ++ Retv ?eb:: _) ?T (?w ++Call ?a :: ?w2++ Ret ?b:: _) =>
                assert (DF.Df (v ++ [Calv ea] ++ v2 ++ [Retv eb]) (T) (w++[Call a]++w2 ++ [Ret b]))
              end;
              repeat rewrite app_assoc;

              match goal with
              | h: Dm ?L ?w ?v |- _ =>
                assert (w!=[]) as _h
                by (destruct w; simpl in *; discriminate; eauto using nil_cons)
                ; pose (ForwardSmallStep.Core.L5_2 _ _ _ h _h)
                ; breakAll
              end;

              [match goal with
                | h: VEndWith ?x ?Lx |- _ =>
                apply (DF.V_Ret) with (L:=Lx); eauto
              end|];
              
              try match goal with
              | h: VEndWith ?x ?Lx |- VEndWith (?v++?x) ?Lx =>
                apply (VListEndSame2 _ v _ h)
              end;

              repeat rewrite <- app_assoc; eauto;

              match goal with
              | H: forall _ _ _, _ -> _,
                h: DF.Df (?v ++ [Calv ?ea] ++ ?v2 ++ [Retv ?eb]) ?T (?w ++ [Call ?a] ++ ?w2++ [Ret ?b])
              |-  DF.Df (?v ++ Calv ?ea:: ?v2 ++ Retv ?eb:: _) ?T (?w ++Call ?a :: ?w2++ Ret ?b:: _) =>
                pose (H _ _ _ h) as _e 
                ; repeat rewrite <- app_assoc in _e
                ; apply _e
                ; clear _e
              end;

              match goal with
              | |- ∃ _, VEndWith (_ ++ _ ++ _ ++ [Retv (MatRetE _ _ _ _ ?Lx)]) _ /\ _ =>
                exists Lx
                ; split; eauto
              end;
              repeat rewrite app_assoc;
              [tryResolveEnd|];
              
              match goal with
              | h: VBeginWithS ?x _ _,
                h2: VBeginWithS (?x++_) _ _ |- VBeginWith ?x ?L =>
                destruct x
                ; inversion h
                ; breakAll; subst; try discriminate
                ; inversion h2; breakAll; subst; eauto
                ; simpl in *; simplList; tryResolveBegin
              end.
            
            complex5.
            

            repeat selectBranch4.
            repeat (getAnd + (do 7 eexists) + 
              constructor 3 + rmRetDv + breakAnd + breakOr + complex5
              + breakEx + simplList); 
              auto; subst.
            
            repeat selectBranch4.


            repeat selectBranch4.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr + complex5
              + breakEx + simplList); 
              auto; subst.
            
            repeat selectBranch4.

            repeat (getAnd + complex5 +
            (instant2; simpl; repeat rewrite <- app_assoc;
              auto) + 
            addEx + 
            solveBeginSA + consMat); auto. 

            repeat (getAnd + complex5 + 
            (instant2; simpl; repeat rewrite <- app_assoc;
              auto) + 
            addEx + 
            solveBeginSA + consMat); auto.


            match goal with 
            | |- Dm ?x (?a :: ?v1 ++ ?b :: ?v2 :: ?v3)
              (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)::
                ?v4 ++ ?vb :: ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2::v3) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.
          }


          1:{
            rewrite H16.

            (* inversion H9; breakDirect;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            subst. *)

            right.
            right.
            repeat addEx.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr + complex5
              + breakEx + simplList); 
              auto; subst.
            right.
            right.
            right.

            repeat addEx.
            
            split.

            Ltac instant4 := 
            match goal with 
            | |- [?v1]++?v2++[?v3]++?v4++[?vb]++?v5 
                  = _ ++ [?vb] ++ _ => 
              instantiate (1:=v5)
              ; instantiate (1:=[v1]++v2++[v3]++v4)
            | |- ?v1::?v2++[?v3]++?v4++[?vb]++?v5::?v6 
                  = _ ++ [?vb] ++ _ => 
              instantiate (1:=v5::v6)
              ; instantiate (1:=[v1]++v2++[v3]++v4)
            end.

            repeat (getAnd + complex5 +
              (instant4; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            repeat (getAnd + complex5 +
              (instant4; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            match goal with 
            | |- Dm ?x ([?a] ++ ?v1 ++ [?b] ++ ?v2)
              ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)] ++
                ?v4 ++ [?vb] ++ ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.

            complex4.

            right.


            inversion H21;
            inversion H18;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            try simplList;
            subst.


            all: repeat (getAnd + addEx + 
            constructor 1 + rmRetDv + breakAnd + breakOr); 
            eauto.
          }
        }
      }





      (* V_Cal_c, directly from V_Cal_a *)
      1: {
        
        repeat (breakAnd + breakOr + breakEx + simplList);
          subst;
          try invMat;
          try discriminate;
          try rmPendMat.

        1: {
          (* w1=v1=w2=v2=[] *)
          
          left.
          
          (* inversion HvTw; subst; *)
          repeat (getAnd + addEx + constructor 3 + 
            (instant; auto)); 
          auto.

          repeat (consMat + constructor + rmEDv); auto.
          mergeBeginW.
        }

        (* 1:{
          admit.
        } *)
        1:{ (* w1=i+, v2 ≠ [] *)

          right; right.

          rewrite H5.
          
          inversion H9; subst;
            repeat (getAnd + addEx + 
            constructor 3 + rmRetDv + breakAnd + breakOr); 
            auto.

          all: repeat selectBranch3.


          repeat (getAnd + simpl + 
            (instant; simpl;
            repeat rewrite <- app_assoc; auto) + addEx + 
            solveBeginSA + consMat); auto.
            
          repeat (getAnd + simpl + 
            (instant; simpl;
            repeat rewrite <- app_assoc; auto) + addEx + 
            solveBeginSA + consMat); auto.
            
          mergeBeginW.
          


          all: repeat (getAnd + simpl + complex3 +
            (instant; simpl;
            repeat rewrite <- app_assoc; auto) + addEx + 
            solveBeginSA + consMat); auto.


          all: try match goal with 
          |  |- Dm _ _ _ => 
            mergeBeginW
          end.
          

          all: try 
            (* consider the Db ind *)
          match goal with 
            | h: Db ?v ?t ?u, 
            h2: BreakDV ?v ?t ?u |- BreakDV _ _ _ => 
            inversion h2;
            breakDirect
            end;
            
            repeat (breakEx + breakAnd + breakOr +
            discriminate + rmPendMat + simplList + subst);
            try discriminate;
            try rmEDv;
            try rmBeginMRet;
            auto.

          all: 
            (* The last two branches *)
            try inversion H18; subst; eauto;
            inversion H17;
            repeat breakEx; subst; try (simplList; subst).

          all: try (right; (do 3 eexists); getAnd; eauto; getAnd; eauto; subst;
              constructor; ((eexists [] + exists x4); simpl; eauto; fail)).


          all: try (left; (do 7 eexists); getAnd; eauto; getAnd; eauto; subst;
              constructor; ((eexists [] + exists x4); simpl; eauto; fail)).

          right. exists x16. do 2 eexists; eauto.
          
          getAnd; eauto; eauto; subst; constructor; eauto.
          constructor. eexists x4, x8. eauto.

        }

      1:{ (* w1=i+, v2 ≠ [] *)
          rewrite H5.
          inversion H10; breakDirect;
          repeat (breakAnd + breakOr + breakEx + simplList);
          subst;
          try invMat;
          try discriminate;
          try rmBeginMRetS;
          try rmPendMat.

          4:{
            rewrite H16.

            (* inversion H9; breakDirect;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            subst. *)

            right.
            right.
            repeat addEx.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst.
            right.
            right.
            right.

            repeat addEx.
            
            split.

            repeat (getAnd +
              (instant3; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            repeat (getAnd +
              (instant3; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            match goal with 
            | |- Dm ?x ([?a] ++ ?v1 ++ [?b] ++ ?v2)
              ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)] ++
                ?v4 ++ [?vb] ++ ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.

            complex4.

            left.
            repeat (getAnd +
            (instant3; simpl; repeat rewrite <- app_assoc;
              auto) + 
            addEx + 
            solveBeginSA + consMat); auto.
          }

          1:{
            left;
            repeat (getAnd + addEx + constructor 3 + 
            (instant; auto)); 
            auto;
            repeat (consMat + constructor + rmEDv); auto;
            mergeBeginW.
            all: mergeBeginW.
          }

          1:{
            right; left;
            repeat (getAnd + addEx + constructor 3 + 
            (instant; auto)); 
            auto;
            repeat (consMat + constructor + rmEDv); auto;
            mergeBeginW.
            all: mergeBeginW.
          }


          1:{
            inversion H10; breakDirect;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            subst.

            repeat selectBranch4.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst.
            
            repeat selectBranch4.

            repeat (getAnd +
              (instant2; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            repeat (getAnd +
              (instant2; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            match goal with 
            | |- Dm ?x (?a :: ?v1 ++ ?b :: ?v2 :: ?v3)
              (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)::
                ?v4 ++ ?vb :: ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2::v3) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            repeat mergeV; subst; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.

            complex5.


            repeat selectBranch4.
            repeat (getAnd + (do 7 eexists) + 
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst.



            repeat selectBranch4.


            repeat selectBranch4.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst.
            
            repeat selectBranch4.

            repeat (getAnd +
            (instant2; simpl; repeat rewrite <- app_assoc;
              auto) + 
            addEx + 
            solveBeginSA + consMat); auto.

            repeat (getAnd +
            (instant2; simpl; repeat rewrite <- app_assoc;
              auto) + 
            addEx + 
            solveBeginSA + consMat); auto.

            match goal with 
            | |- Dm ?x (?a :: ?v1 ++ ?b :: ?v2 :: ?v3)
              (Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)::
                ?v4 ++ ?vb :: ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2::v3) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.
            complex5.
          }

          (* Start Here! *)

          1:{
            rewrite H16.

            (* inversion H9; breakDirect;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            subst. *)

            right.
            right.
            repeat addEx.
            repeat (getAnd + addEx + 
              constructor 3 + rmRetDv + breakAnd + breakOr
              + breakEx + simplList); 
              auto; subst.
            right.
            right.
            right.

            repeat addEx.
            
            split.


            repeat (getAnd +
              (instant4; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            repeat (getAnd +
              (instant4; simpl; repeat rewrite <- app_assoc;
                auto) + 
              addEx + 
              solveBeginSA + consMat); auto.

            match goal with 
            | |- Dm ?x ([?a] ++ ?v1 ++ [?b] ++ ?v2)
              ([Calv (MatCalE ?x ?x0 ?x1 ?x2 ?x3)] ++
                ?v4 ++ [?vb] ++ ?v5) => 
              apply (DMat x x0 x2 x1 x3 v1 (v2) (v4) v5)
            end; auto.
            mergeBeginW; auto.

            match goal with 
            | h: VBeginWithS (?v ++ _) ?L _,
              h2: VBeginWithS (?v) ?L1 _
            |- Dm ?L _ _ => 
              inversion h;
              inversion h2;
              repeat (breakEx + breakAnd);
              subst;
              simpl in *;
              simplList;
              subst; auto  
            end.

            complex4.

            right.

            inversion H21;
            inversion H18;
            repeat (breakAnd + breakOr + breakEx + simplList);
            subst;
            try invMat;
            try discriminate;
            try rmPendMat;
            try rmBeginMRetS;
            try simplList;
            subst.

            all: repeat (getAnd + addEx + 
            constructor 1 + rmRetDv + breakAnd + breakOr); 
            eauto.
          }
        }
      }



      (* V_Ret_Pnd_S *)
      1: {
        right; left.
        all: repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

        constructor; repeat eexists; auto.
        constructor. 

        constructor 4; repeat eexists; auto.
        constructor; auto.
        constructor; auto.
      }

      
      (* V_Ret_Pnd_bot *)
      1: {
        inversion IHHvTw;
        repeat (breakAnd + breakOr + breakEx + simplList);
        subst;
        try invMat;
        try discriminate;
        try rmPendMat;
        try rmBeginMRetS;
        try simplList;
        subst.

        1:{
          right; left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          constructor; repeat eexists; auto.
          constructor. 

          constructor 4; repeat eexists; auto.
          constructor; auto.
          clear H6.
          mergeBegins.
          auto.
        }

        1:{
          right; left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          constructor; repeat eexists; auto.

          constructor 4; repeat eexists; auto.
          constructor; auto.
          clear H6.
          mergeBegins.
          auto.
        }
        1:{
          right; left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          constructor; repeat eexists; auto.

          constructor 4; repeat eexists; auto.
          constructor; auto.
          clear H6.
          mergeBegins.
          auto.
        }
        1:{
          right; left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          constructor; repeat eexists; auto.

          constructor 4; repeat eexists; auto.
          constructor; auto.
          clear H6.
          mergeBegins.
          auto.
        }
      }
      
      (* V_Ret_Pnd *)
      1: {
        inversion IHHvTw;
        repeat (breakAnd + breakOr + breakEx + simplList);
        subst;
        try invMat;
        try discriminate;
        try rmPendMat;
        try rmBeginMRetS;
        try simplList;
        subst.

        right; left.
        repeat (getAnd + addEx + 
        rmRetDv + breakAnd + breakOr); 
        eauto.

        constructor; repeat eexists; auto.

        constructor 4; repeat eexists; auto.
        constructor; auto.
        clear H6.
        mergeBegins.
        auto.
      }

      (* V_Ret_S *)
      1: {

        right.
        right.
        repeat (getAnd + addEx + 
        rmRetDv + breakAnd + breakOr); 
        eauto.
      }

      (* V_Ret_bot *)
      (* 1:{
        admit.
      } *)
      1: {
        inversion IHHvTw;
        repeat (breakAnd + breakOr + breakEx + simplList);
        subst;
        try invMat;
        try discriminate;
        try rmPendMat;
        try rmBeginMRetS;
        try simplList;
        subst.

        1:{

          right; right.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          right.
          left.

          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          constructor; intros.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          right.
          inversion HvTw; subst;
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          Ltac rmBW :=
          match goal with 
          | 
            h: VBeginWith _ _
          |- _ => 
            inversion h;
            clear h
          end.

          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.

          (* Ltac instant5 :=
            match goal with 
            |  |- [_]=[_]++_ => 
              instantiate (1:=[])
            end. *)

          all: 
          try (constructor; repeat eexists; simpl; eauto; 
            fail).
        }

        1:{

          right; right.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          right.
          left.

          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          constructor; intros.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          right.
          inversion HvTw; subst;
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.

          (* Ltac instant5 :=
            match goal with 
            |  |- [_]=[_]++_ => 
              instantiate (1:=[])
            end. *)

          all: 
          try (constructor; repeat eexists; simpl; eauto; 
            fail).
        }

        1:{

          right; right.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          right.
          left.

          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          constructor; intros.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          right.
          inversion HvTw; subst;
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.

          (* Ltac instant5 :=
            match goal with 
            |  |- [_]=[_]++_ => 
              instantiate (1:=[])
            end. *)

          all: 
          try (constructor; repeat eexists; simpl; eauto; 
            fail).
        }

        1:{

          right; right.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          right.
          left.

          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          constructor; intros.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          right.
          inversion HvTw; subst;
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.

          (* Ltac instant5 :=
            match goal with 
            |  |- [_]=[_]++_ => 
              instantiate (1:=[])
            end. *)

          all: 
          try (constructor; repeat eexists; simpl; eauto; 
            fail).
        }
      }

      (* V_Ret_b1 *)
      (* 1: {
        admit.
      } *)
      1: {
        inversion IHHvTw;
        repeat (breakAnd + breakOr + breakEx + simplList);
        subst;
        try invMat;
        try discriminate;
        try rmPendMat;
        try rmBeginMRetS;
        try simplList;
        subst.

        1:{

          right; right.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          right.
          left.

          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          constructor; intros.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          right.
          left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.
          right.

          inversion HvTw; subst;
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
          eauto.

          (* Takes some time < 30s *)
          all: repeat rmBW;
            repeat (breakEx + simplList); 
            subst;
            eauto.

          all: 
          try (constructor; repeat eexists; simpl; eauto; 
            fail).
        }
      }


      (* V_Ret_b2_b *)
      1: {
        repeat (breakAnd + breakOr + breakEx + simplList);
        subst;
        try invMat;
        try discriminate;
        try rmPendMat;
        try rmBeginMRetS;
        try simplList;
        subst.

        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.



        1:{
          inversion HvTw; subst;
          constructor; intro h;
          inversion h; subst;
          right;
          right;
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr); 
          eauto;
          rmEDv.
        }
        

        left.

        repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
        subst;
        eauto.


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          left.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.

          left.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
        }
        
        left.

        repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
        subst;
        eauto.


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.


        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          left.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.


          inversion HvTw; subst;
          inversion H15;
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.

          all: try (
            right;
            repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
            eauto;
            fail).
        }
        
        left.

        repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
        subst;
        eauto.


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          left.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
        }
        
        left.
        inversion HvTw; subst;
        repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
        eauto;
        subst.


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          right.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.

          left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.
        }

        
        left.
        inversion HvTw; subst;
        repeat (getAnd + (do 7 eexists) + 
          rmRetDv + breakAnd + breakOr); 
        eauto;
        subst.


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.


        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          right.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.

          right.
          inversion H10; subst;
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.
        }

        
        left.
        inversion HvTw; subst;
        repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr); 
        eauto;
        subst.
      }


      (* V_Ret_b2_c *)
      1:{
        repeat (breakAnd + breakOr + breakEx + simplList);
        subst;
        try invMat;
        try discriminate;
        try rmPendMat;
        try rmBeginMRetS;
        try simplList;
        subst.


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          left.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
        }
        
        right.

        inversion H8; subst;
        repeat (getAnd + addEx + breakEx+
          rmRetDv + breakAnd + breakOr); 
        eauto;
        subst.

        (* Ltac rmBW :=
          match goal with 
          | 
            h: VBeginWith _ _
          |- _ => 
            inversion h;
            clear h
          end. *)

        1:{ 

          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.
          
          all: try (simpl in H1; inversion H1; subst;
          constructor; repeat eexists; fail).
        }


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          right.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.

          left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.
        }
        
        right.

        1:{ 
          inversion H7; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.


          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.
          
          all: inversion HvTw; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.

          all: try (simpl in H2; inversion H2; subst;
          constructor; repeat eexists; fail).
        }


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          right.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.

          right.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.
        }
        
        right.
        repeat (getAnd + addEx + 
        rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.


          inversion H7; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.


          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.
          
          all: inversion HvTw; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.

          all: try (simpl in H1; inversion H1; subst;
          constructor; repeat eexists; fail).
      }


      (* V_Ret_b2_a *)
      1:{
        repeat (breakAnd + breakOr + breakEx + simplList);
        subst;
        try invMat;
        try discriminate;
        try rmPendMat;
        try rmBeginMRetS;
        try simplList;
        subst.


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          left.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
        }
        
        right.

        
        1:{ 
          inversion H8; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.

          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.
          
          all: try (simpl in H1; inversion H1; subst;
          constructor; repeat eexists; fail).
        }


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          right.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.

          left.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.
        }
        
        right.

        1:{ 
          inversion H7; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.


          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.
          
          all: inversion HvTw; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.

          all: try (simpl in H2; inversion H2; subst;
          constructor; repeat eexists; fail).
        }


        right; right;
        exists L, a, L1, b, L2;
        eexists;
        eexists;
        repeat (getAnd; eauto);
        right;
        left.

        repeat (getAnd + addEx +
          rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.

        1:{
          constructor; intro h.
          right;
          right.
          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          eauto.
          right;
          right;
          right.

          repeat (getAnd + addEx + 
            rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.

          right.
          repeat (getAnd + addEx + 
          rmRetDv + breakAnd + breakOr);
          simpl;
          eauto.
        }
        
        right.
        repeat (getAnd + addEx + 
        rmRetDv + breakAnd + breakOr);
        simpl;
        eauto.


          inversion H7; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.


          (* Takes some time < 30s *)
          all: repeat rmBW;
          repeat (breakEx + simplList); 
          subst;
          eauto.
          
          all: inversion HvTw; subst;
          repeat (getAnd + addEx + breakEx+
            rmRetDv + breakAnd + breakOr); 
          eauto;
          subst.

          all: try (simpl in H1; inversion H1; subst;
          constructor; repeat eexists; fail).
      }

    Qed.
    (* end hide *)

    (** [SoundV]: the soundness of the backward small-step derivation
        [Db] means that [Dv] indicates the big-step derivation [Dm],
        under certain conditions.  *)
    Theorem SoundV: ∀ v T w Lv Le, 
      Db v T w 
      -> VBeginWith v Lv 
      -> VEndWith v Le 
      -> in_rules (Le, Alt_Epsilon) P 
      -> (T=[] \/ ∃ L1 b L2 T', T=(PndRetE L1 b L2)::T')
      -> Dm Lv w v.
    (* begin hide *)
    Proof.
      intros.
      breakOr.

      1:{
        pose (L4_2 v T w) as h.
        inversion h;
        breakDirect;
        subst;
        repeat (breakAnd + breakEx + breakOr);
        try match goal with 
        | h: VBeginWith ?v _, h2: VBeginWith ?v _ |- _ => 
          inversion h; inversion h2;
          repeat (breakAnd + breakEx); subst;
          simplList; subst
        end;
        auto.
        all: try discriminate.
      }

      pose (L4_2 v T w) as h.
      inversion h;
      breakDirect;
      subst;
      repeat (breakAnd + breakEx + breakOr);
      try match goal with 
      | h: VBeginWith ?v _, h2: VBeginWith ?v _ |- _ => 
      inversion h; inversion h2;
      repeat (breakAnd + breakEx); subst;
      simplList; subst
      end;
      auto.

      all: 
      subst;
      try discriminate.
    Qed.

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

    (** [L4_3]: Lemma 4.3 shows the big-step derivation [Dm]
      satisfies [BreakDV] when the start nonterminal belongs to V0. *)
    Lemma L4_3: ∀ L v w,
      Dm L w v
      -> (∃ vv, L=V0 vv)
      -> w ≠ []
      -> Db v [] w /\
        ∀ v2 T2 w2 L1 a L2 b L3, 
          (Db (Retv (MatRetE L1 a L2 b L3)::v2) T2 w2
          -> Db (v++Retv (MatRetE L1 a L2 b L3)::v2) T2 (w++w2)).
    (* begin hide *)
    Proof.
      intros.
      dependent induction H.
      contradiction.
      1:{
        breakEx; subst.
        destruct (A_VPG_Linear _ _ _ H); eauto; subst.
        repeat (breakEx + breakAnd); subst; discriminate.
      }

      1:{
        destruct w'.
        inversion H0; subst.

        split.
        constructor; auto.
        intros.
        inversion H4; constructor; subst; auto.

        breakEx; subst.
        destruct (A_VPG_Linear _ _ _ H); eauto; subst.
        repeat (breakEx + breakAnd); subst.
        inversion H1; subst.

        destruct IHDm; eauto using nil_cons.

        split; auto.
        inversion H3; constructor; subst; auto.

        all: try (
          inversion H0;
          (constructor 1 +
          constructor 2 +
          constructor 3 +
          constructor 4); simpl; repeat eexists; fail).

        intros.

        
        inversion H0;
        inversion H5;
        subst; simpl.
        all: try contraVPG.

        all: constructor; auto.
        all: try (
          (constructor 1 +
          constructor 2 +
          constructor 3 +
          constructor 4); simpl; repeat eexists; fail).

        all: apply H4.
        all: constructor; auto.
      }

      1:{
        breakEx; subst.
        destruct (A_VPG_Linear _ _ _ H); eauto; subst.
        repeat (breakEx + breakAnd); subst; discriminate.
      }

      1:{
        destruct (A_VPG_Match _ _ _ _ _ H).
        destruct w1;
        destruct w2.

        1:{
          Ltac invEmpDm :=
          match goal with
          | h: Dm _ [] _ |- _ =>
            inversion h
            ; clear h
            ; subst
          end.
          repeat invEmpDm.

          simpl in *.

          repeat breakEx; subst.
          repeat (split + constructor); auto.

          inversion H0; subst.

          all:try (repeat (constructor + split); auto; fail).

          all: match goal with
          | h: Db _ _ _ |- _ =>
            inversion h
            ; subst
          end;
          constructor; auto; subst.
        }


        1:{
            match goal with
            | h: Dm _ (_::_) _ |- _ =>
              inversion h
              ; clear h
              ; subst
            end;
            simpl in *;
            repeat breakEx; subst.

            1:{
              inversion H0; subst; auto.
              simpl in *.

              (* Get the ind *)
              destruct H5; eauto.
              destruct IHDm2;
              eauto using nil_cons.

              split; constructor; auto.
              constructor; auto.
              
              try ((constructor 1 +
              constructor 2 +
              constructor 3)
              ; repeat eexists; fail).

              inversion H6;
              constructor; auto; subst.

              all: try ((constructor 1 +
              constructor 2 +
              constructor 3)
              ; repeat eexists; fail).

              all: apply H5; auto.
            }

            1:{

              inversion H0; subst; auto.
              simpl in *.

              (* Get the ind *)
              destruct H5; eauto.
              destruct IHDm2;
              eauto using nil_cons.

              split; constructor; auto.
              constructor; auto.
              
              try ((constructor 1 +
              constructor 2 +
              constructor 3)
              ; repeat eexists; fail).

              inversion H6;
              constructor; auto; subst.

              all: try ((constructor 1 +
              constructor 2 +
              constructor 3)
              ; repeat eexists; fail).

              all: apply H5; auto.
            }

            1:{
              (* Get the ind *)
              destruct H5; eauto.
              destruct IHDm2;
              eauto using nil_cons.
              (* The axiom rejects this case. *)
              subst.
              contraVPG.
            }

            1:{
              inversion H0; subst; auto.
              simpl in *.

              (* Get the ind *)
              destruct H5; eauto.
              destruct IHDm2;
              eauto using nil_cons.

              split; constructor; auto.
              constructor; auto.
              
              try ((constructor 1 +
              constructor 2 +
              constructor 3)
              ; repeat eexists; fail).

              inversion H6;
              constructor; auto; subst.

              all: try ((constructor 1 +
              constructor 2 +
              constructor 3)
              ; repeat eexists; fail).

              all: apply H5; auto.
            }


            all: match goal with
            | h: Db _ _ _ |- _ =>
              inversion h
              ; subst
            end;
            constructor; auto; subst.
        }

        1:{
            match goal with
            | h: Dm _ [] _ |- _ =>
              inversion h
              ; clear h
              ; subst
            end.
            match goal with
            | h: Dm _ (_::_) _ |- _ =>
              inversion h
              ; clear h
              ; subst
            end;
            simpl in *;
            repeat breakEx; subst.

            1:{
              (* H9 is rejected by axioms *)
              contraVPG.
            }

            1:{

              (* Get the ind *)
              destruct H5; eauto.
              destruct IHDm1;
              eauto using nil_cons.

              split; constructor; auto.
              try ((constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4)
              ; repeat eexists; fail).


              inversion H11;
              try (constructor; auto; subst; fail).
              

              repeat match goal with
              |  |- Db _ _ _ =>
                constructor; auto
              end.

              all: subst;
                try (apply H2;
                match goal with
                |  |- Db _ _ _ =>
                  constructor; auto
                end).

              try ((constructor 1 +
                constructor 2 +
                constructor 3 +
                constructor 4)
                ; repeat eexists; fail).

              repeat rewrite <- app_assoc.
              apply H2.
              inversion H4; subst; constructor; auto.
            }

            1:{
              (* H9 is rejected by axioms *)
              contraVPG.
            }

            1:{

              (* Get the ind *)
              destruct H5; eauto.
              destruct IHDm1;
              eauto using nil_cons.

              split; constructor; auto.
              try ((constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4)
              ; repeat eexists; fail).

              apply H2; auto.
              try (constructor; auto; subst; fail).
              
              try ((constructor 1 +
                constructor 2 +
                constructor 3 +
                constructor 4)
                ; repeat eexists; fail).

              pose (H2 (Retv (MatRetE L1 a1 L0 b1 L5) :: v2) ((MatRetE (V0 x0) a (V0 x) b L2 :: T2)) 
                ([Ret b]++ w1) (V0 x0) a (V0 x) b L2).

              repeat rewrite <- app_assoc in *.
              simpl in *.
              apply d.

              inversion H4; subst;
              constructor; auto.
            }
        }

        1:{

          (* Get the ind *)
          destruct H5; eauto.
          destruct IHDm1;
          destruct IHDm2;
          eauto using nil_cons.

          inversion H0;
          simpl in *;
          repeat breakEx; subst.

          1:{
            (* H13 is rejected by axioms *)
            contraVPG.
          }

          1:{
            split; constructor; auto;
            try ((constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4)
            ; repeat eexists; fail).
            apply H7.
            constructor; auto.

            inversion H1;
            try ((constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4)
            ; repeat eexists; fail).

            pose (H7 (pt2++Retv (MatRetE L1 a0 L2 b0 L0) :: v2) 
              (MatRetE (V0 x1) a (V0 x0) b (V0 x) :: T2)
              (Ret b :: s0 :: w2 ++ w0)).
            simpl in *.
            repeat rewrite <- app_assoc.
            apply d.
            clear d.


            inversion H1; subst.
            1:{
              (* H11 is rejected by the axiom *)
              contraVPG.
            }

            1:{
              inversion H2;
              subst;
              constructor;
              auto;

              try ((constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4)
              ; repeat eexists; fail).
            }

            1:{
              (* H11 is rejected by the axiom *)
              contraVPG.
            }


            1:{
              inversion H2;
              subst;
              constructor;
              auto;

              try ((constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4)
              ; repeat eexists; fail).
            }
          }

          1:{
            (* H13 is rejected by axioms *)
            contraVPG.
          }

          1:{
            split; constructor; auto;
            try ((constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4)
            ; repeat eexists; fail).
            apply H7.
            constructor; auto.

            inversion H1;
            try ((constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4)
            ; repeat eexists; fail).

            pose (H7 (pt2++Retv (MatRetE L1 a1 L2 b1 L0) :: v2) 
              (MatRetE (V0 x1) a (V0 x0) b (V0 x) :: T2)
              (Ret b :: s0 :: w2 ++ w1) (V0 x1) a (V0 x0) b (V0 x)).
            repeat rewrite <- app_assoc in *.
            simpl in *.
            repeat rewrite <- app_assoc in *.
            simpl in *.
            apply d.
            clear d.


            inversion H1; subst.
            1:{
              (* H11 is rejected by the axiom *)
              contraVPG.
            }

            1:{
              inversion H2;
              subst;
              constructor;
              auto;

              try ((constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4)
              ; repeat eexists; fail).
            }

            1:{
              (* H11 is rejected by the axiom *)
              contraVPG.
            }


            1:{
              inversion H2;
              subst;
              constructor;
              auto;

              try ((constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4)
              ; repeat eexists; fail).
            }
          }
        } 
      }
    Qed.
    (* end hide *)

    (** [CompleteM]: the completeness of the backward small-step
        derivation [Db] means that each big-step derivation [Dm] is a
        [Db], as long as the string is not empty. *)
    Theorem CompleteM: ∀ L w v, 
      Dm L w v
      -> w ≠ []
      -> ∃ T, PendT T /\ Db v T w.
    (* begin hide *)
    Proof.
      intros.
      induction H.
      try contradiction.

      1:{
        destruct w'.
        inversion H1; subst.
        exists [].
        split. constructor.
        apply V_Cal_Pnd_S; auto.

        destruct L1.
        exists [].
        destruct (L4_3 (V0 v) pt' (s::w')); eauto using nil_cons;
        constructor; auto.
        constructor; auto.
        constructor; auto.

        inversion H1; subst;
        try rmEDv;
        (constructor 1 +
        constructor 2 +
        constructor 3 +
        constructor 4); simpl; repeat eexists; fail.
        

        match goal with
        | h: ?v::?u ≠ [] -> ?h2 |- _ =>
          assert (h2) by (apply h;
            auto using nil_cons)
        end;
        repeat (breakEx + breakAnd).

        destruct x.

        2:{
          destruct r.
          2:{
            (* impossible since v is in V1 *)
            rmPendMat.
          }

          exists x.
          pose V_Cal_b1.
          split. 
          inversion H3.
          repeat (breakEx + breakAnd).
          simplList; auto.
          
          apply V_Cal_b1 with (b:=b) (L2:=L0) (L3:=L1); auto.
          inversion H1; subst; try rmEDv;
          (constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4); simpl; repeat eexists; fail.
        }


        exists [].
        split; constructor; auto.
        inversion H1; subst; try rmEDv;
        (constructor 1 +
          constructor 2 +
          constructor 3 +
          constructor 4); simpl; repeat eexists; fail.
      }

      1:{
        destruct w'.
        inversion H1; subst.
        exists [].
        constructor; auto.
        constructor; auto.
        constructor; auto.

        match goal with
        | h: ?v::?u ≠ [] -> ?h2 |- _ =>
          assert (h2) by (apply h;
            auto using nil_cons)
        end;
        repeat (breakEx + breakAnd).

        exists x.
        inversion H1; subst;
        inversion H2; subst;
        constructor; auto;
        constructor; auto.
        all: try (
          match goal with
          |  |- VBeginWith _ _ =>
            (constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4); simpl; repeat eexists; fail
          end).

        all: constructor; auto.
      }

      1:{
        destruct w'.
        inversion H1; subst.
        exists [(PndRetE L b L1)].
        constructor; auto.
        constructor; auto.
        repeat eexists.
        constructor; auto.
        constructor; auto.

        match goal with
        | h: ?v::?u ≠ [] -> ?h2 |- _ =>
          assert (h2) by (apply h;
            auto using nil_cons)
        end;
        repeat (breakEx + breakAnd).

        exists (PndRetE L b L1::x).
        destruct x.
        inversion H1; subst;
        inversion H2; subst.
        all: split.
        all: try (constructor; auto; repeat eexists; constructor; auto; fail).
        all: try (constructor; auto).
        all: try (
          match goal with
          |  |- VBeginWith _ _ =>
            (constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4); simpl; repeat eexists; fail
          end).

        constructor; auto.
        constructor; auto.
        constructor; auto.
        repeat eexists; auto.

        inversion H3.
        repeat (breakEx + breakAnd); simplList; subst.

        constructor; auto.

        inversion H1; 
          match goal with
          |  |- VBeginWith _ _ =>
            (constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4); simpl; repeat eexists; fail
          end.
      }

      1:{
        destruct w1;
        destruct w2.

        1:{
          inversion H1; inversion H2; subst.
          exists [].
          split.
          constructor; auto.
          constructor; auto.
          constructor; auto.
        }

        1:{
          inversion H1; subst.
          match goal with
          | h: ?v::?u ≠ [] -> ?h2 |- _ =>
            assert (h2) by (apply h;
              auto using nil_cons)
          end;
          repeat (breakEx + breakAnd).
          exists x.
          split; auto.
          constructor; auto.
          simpl.
          inversion H4; subst.

          all: try match goal with
          | h: PendT ?x |- _ =>
            inversion h
            ; repeat (breakEx + breakAnd)
            ; subst
          end.

          all: try (constructor; auto);
          try match goal with
          |  |- VBeginWith _ _ =>
            inversion H2;
            (constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4); simpl; repeat eexists; fail
          end.

          all: discriminate.
        }

        1:{
          inversion H2; subst.
          match goal with
          | h: ?v::?u ≠ [] -> ?h2 |- _ =>
            assert (h2) by (apply h;
              auto using nil_cons)
          end;
          repeat (breakEx + breakAnd).

          exists [].
          split; auto.
          constructor; auto.
          destruct (L4_3 _ _ _ H1).
          destruct (A_VPG_Match _ _ _ _ _ H);
          repeat (breakAnd + breakEx); subst.
          eauto.
          auto using nil_cons.
          simpl.

          match goal with
          |  |- Db (_::?v1++[Retv ?v2]) [] (_::?s1::?s2++?s3) =>
            assert (Db (v1++[Retv v2]) [v2] (s1::s2++s3))
          end.
          apply H7; constructor; auto.


          inversion H8; subst; simpl; constructor; auto.
          all: inversion H1; subst; simpl in *;simplList; subst.

          all: try match goal with
            |  |- VBeginWith _ _ =>
              (constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4); simpl; repeat eexists; fail
            end.
          
          constructor; auto.
          constructor; auto.
          constructor; auto.

          destruct (A_VPG_Match _ _ _ _ _ H);
          repeat (breakAnd + breakEx); subst.
          contraVPG.
          
          constructor; auto.
          constructor; auto.
          constructor; auto.
        }


        1:{
          destruct (L4_3 _ _ _ H1).
          destruct (A_VPG_Match _ _ _ _ _ H);
          repeat (breakAnd + breakEx); subst.
          eauto.
          auto using nil_cons.

          do 2 match goal with
          | h: ?v::?u ≠ [] -> ?h2 |- _ =>
            assert (h2) by (apply h;
              auto using nil_cons)
            ; clear h
          end;
          repeat (breakEx + breakAnd).

          exists (x0).
          split; auto.

          inversion H6; subst; simpl.

          all: try (inversion H1; subst;
            match goal with
            | h2: in_rules (_, Alt_Match _ _ ?L _) _,
              h: in_rules (?L, Alt_Linear (Call _) _) _ |- _ =>
              destruct (A_VPG_Match _ _ _ _ _ h2);
              repeat (breakAnd + breakEx); subst; contraVPG
            | h2: in_rules (_, Alt_Match _ _ ?L _) _,
              h: in_rules (?L, Alt_Linear (Ret _) _) _ |- _ =>
              destruct (A_VPG_Match _ _ _ _ _ h2);
              repeat (breakAnd + breakEx); subst; contraVPG
            end).

          all: constructor;
          try match goal with
          |  |- VBeginWith _ _ =>
            inversion H1;
            (constructor 1 +
            constructor 2 +
            constructor 3 +
            constructor 4); simpl; repeat eexists; fail
          end.

          all: apply H4.
          
          inversion H5; subst;
          inversion H2; subst.
          
          all: inversion H8; repeat (breakAnd + breakEx); subst.
          all: constructor; auto;
            try match goal with
            |  |- VBeginWith _ _ =>
              inversion H1;
              inversion H2;
              (constructor 1 +
              constructor 2 +
              constructor 3 +
              constructor 4); simpl; repeat eexists; fail
            end.

          all: try congruence.
        }
      }
    Qed.
    (* end hide *)

  End Core.
End BackwardSmallStep.