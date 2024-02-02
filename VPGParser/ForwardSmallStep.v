(** This file verifies the properties of the forward small-step relation
    [Df v I w]. The relation [Df] formalizes how a single parse tree is
    extended in a _forward_ way during running the parser PDA. "Forward"
    here means that the tree is extended from the rule that derives the
    first symbol of the input string to the rule that derives the last
    symbol. *)

Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Extraction.
Require Import Arith_base String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import Coq.Unicode.Utf8_core.
Require Import Lia.

Require Import Def.
Require Import Misc.
Require Import Tac.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Import Misc.Basic.
Import Misc.vpg.

Module ForwardSmallStep(G:VPG).

  (* begin hide *)

  Module Tac := Tac(G).

  Module Def := Tac.Def.

  Include Def.
  Include Def.DF.
  Include Def.DM.
  Include Tac.Tacs.

  Ltac tryResolveEnd :=
    match goal with
    | |- VEndWith (?x++_) _ =>
      try_resolve_end_with x
    end.

  Ltac resolveEndWith :=
    match goal with
    | h:VEndWith (?v++?e::?v') ?L |- VEndWith (?e::?v') ?L =>
      assert ((e::v') != []) as _HnotNil by eauto using nil_cons
      ; destruct (exists_last _HnotNil) as [? _s]
      ; destruct _s as [? _h]
      ; rewrite _h in *
      ; clear _h _HnotNil
      ; repeat rewrite app_assoc in h
      ; inversion h; breakAll; subst
      ; tac_inj
      ; subst
      ; tryResolveEnd
    end.


  (* end hide *)


  Module Df2.

    (* begin hide *)
    Lemma VListEndSame3: ∀ v v1 v2 L, 
        (v != []) ->
        VEndWith (v1++v) L -> VEndWith (v2++v) L.
    Proof.
        intros.
        inversion H0
        ; breakAll
        ; subst.

        all: match goal with
        | h: ?v != [] |- _ =>
          destruct (exists_last h) as [_x _s]
          ; destruct _s
        end;

        subst;
        rewrite app_assoc in H1;
        tac_inj;
        subst;
        try_resolve_end_with (v2++_x).
    Qed.
    (* end hide *)

    (** [L_Df_unique]: this lemma shows that a parse tree [v] derives
        only one string. *)
    Lemma L_Df_unique: ∀ v T1 w1 T2 w2, (Df v T1 w1)->(Df v T2 w2)->
        (T1=T2) /\ (w1=w2).
    (* begin hide *)
    Proof.
        intros.
        generalize dependent T1.
        generalize dependent w1.
        induction H0; intros w1 T1 Hw1; inversion Hw1; subst.

        all: split; auto.
        all: tac_inj; subst; try tac_df.

        all: match goal with
        | h: _ _ = _ _ |- _ =>
            inversion h
            ; clear h
            ; subst
        end.

        all: try match goal with
        | h: Df ?v ?T ?w  |- _ =>
            destruct (IHDf w T h)
            ; subst
            ; auto
        end.

        all: try discriminate.

        all: simplList; auto.
    Qed.
    (* end hide *)

    (** [L_Df_uniqueT]: this lemma shows that the stacks of the parse
        trees of the same string have the same length. *)
    Lemma L_Df_uniqueT: ∀ v1 v2 T1 T2 w, (Df v1 T1 w)->(Df v2 T2 w)->
    (List.length T1 = List.length T2).
    (* begin hide *)
    Proof.
        intros.
        generalize dependent T1.
        generalize dependent v1.
        induction H0; intros v1 T1 Hv1; inversion Hv1; subst; auto.

        all: tac_inj; subst; try tac_df.

        all: try match goal with
                | h: _ _ = _ _ |- _ =>
                    inversion h
                    ; clear h
                    ; subst
                end.

        all: repeat constructor.

        all: try match goal with
        | h: Df ?v ?T ?w  |- _ =>
            pose (IHDf v T h) as _H
            ; inversion _H
            ; subst
            ; auto
        end.

        all: simpl; eauto.
    Qed.
    (* end hide *)
    
    (** [L_Df_uniqueV]: this lemma shows that the parse trees of the
        same string have the same length. *)
    Lemma L_Df_uniqueV: ∀ v1 v2 T1 T2 w, (Df v1 T1 w)->(Df v2 T2 w)->
    (length v1 = length v2).
    (* begin hide *)
    Proof.
        intros.
        generalize dependent T1.
        generalize dependent v1.
        induction H0; intros v1 T1 Hv1; inversion Hv1; subst; auto.

        all: tac_inj; subst; try tac_df.

        all: try match goal with
                | h: _ _ = _ _ |- _ =>
                    inversion h
                    ; clear h
                    ; subst
                end.

        (* all: repeat constructor. *)

        all: try match goal with
        | h: Df ?v ?T ?w  |- _ =>
            pose (IHDf v T h) as _H
            ; inversion _H
            ; subst
            ; auto
        end.

        all: match goal with
        | |- length (?u ++ [?r]) = length (?v ++ [?t]) =>
            pose (last_length u r) 
            ; pose (last_length v t) 
        end;
        rewrite e;
        rewrite e0.


        all: simpl; eauto.

    Qed.
    (* end hide *)

    (** [L_Df_vw]: this lemma shows that for the parse tree [v] of a
        string [w], their lengths are equal. *)
    Lemma L_Df_vw: ∀ v T w, (Df v T w)->
    (length v = length w).
    (* begin hide *)
    Proof.
      intros.
      induction H; eauto;

      match goal with
      | |- length (?v++[?e]) = length (?w++[?i]) =>
        rewrite (app_length v [e])
        ; rewrite (app_length w [i])
        ; rewrite IHDf
        ; eauto
      end.
    Qed.
    (* end hide *)

    (** [L_DF_Local]: this lemma shows that we can split a parse tree
        into two parts and replace the first part. More specifically, if
        we have the parse tree [v++[e]++v2] of the string [w1++w2],
        where [v] is of [w1], then we can replace [v] with [v1], as long
        as [v1] have the same stack of [v], and [v1] is of [w1]. *)
    Lemma L_DF_Local: ∀ v v1 e T w1, 
      (Df (v++[e]) T w1)
      -> (Df (v1++[e]) T w1) 
      -> ∀ v2 T2 w2, (Df (v++[e]++v2) T2 (w1++w2)) 
      -> (Df (v1++[e]++v2) T2 (w1++w2)).
    (* begin hide *)
    Proof.
        intros v v1 e T w1 H1 H2 v2.

        induction v2 using @rev_ind.
        1:{
            intros.
            simpl in *.
            inversion H; 
            tac_inj; subst.

            destruct w1; try tac_df;
            simplList; tac_inj; subst.

            all: try (assert (v1=[]) by (
                inversion H1; inversion H2; tac_inj; subst; auto;
                tac_inj; subst; try tac_df); subst).

            all: try ((apply V_S_Pln) + (apply V_Pln) + (apply V_S_Pnd_Cal) + 
                (apply V_Pnd_Cal) + (apply V_S_Cal) + (apply V_Cal) + 
                (apply V_S_Pen_Ret) + (apply V_Pnd_Ret_bot) + 
                (apply V_Pnd_Ret) + (apply V_Ret)); eauto.


            all: try (
                match goal with
                |  |- VEndWith _ _ =>
                    inversion H2;
                    breakAll; subst;

                    inversion H1;
                    tac_inj; subst;

                    try match goal with
                    | h: VEndWith [] _ |- _ =>
                    inversion h
                    ; breakAll
                    ; try discriminate
                    ; tac_inj
                    ; try discriminate
                    end;
                    try tac_df;

                    match goal with
                    | h: _ _ = _ _ |- _ =>
                        inversion h
                    end;
                    subst;
                    auto;
                    try tac_df
                end
                ).

            Ltac mergeUniqueDf :=
            match goal with
            | h: Df ?x ?T ?w, h2: Df ?x ?T' ?w' |- _ =>
                destruct (L_Df_unique x _ _ _ _ h h2) as [_H1 _H2]
                ; subst
                ; rewrite <- _H2 in *
                ; clear _H2
            end.

            all: try (mergeUniqueDf;
                subst;
                inversion H2; subst; auto;
                try (tac_inj; subst; try tac_df; auto)).

            all: try (inversion a0; subst; eauto).

            1:{
                inversion a0; subst.
                eauto.
                repeat rmDirect.

                match goal with
                | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
                    pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
                    inversion _H
                end.
            }

            all: match goal with
            | h: _ _ = _ _ |- _ =>
                inversion h
                ; clear h
                ; subst
                ; repeat rmDirect
            end;
            auto.

        }

        1:{
            intros.
            destruct w2.
            (* w2 = [] is impossible *)
            1:{
                rewrite app_nil_r in H.
                do 2 rewrite app_assoc in H.
                pose (L_Df_uniqueV _ _ _ _ _ H1 H).
                Ltac shrink :=
                match goal with
                | h: length (?v++[?r]) = length (?v2++[?t]) |- _ =>
                    pose (app_length v [r])
                    ; pose (app_length v2 [t])
                end.
                shrink.
                rewrite e1 in e0.
                rewrite e2 in e0.
                clear e1 e2.
                simpl in e0.

                rewrite <- app_assoc in e0.
                pose (app_length v ([e]++v2)).
                rewrite e1 in e0.
                clear e1.
                rewrite Arith_prebase.plus_assoc_reverse_stt in e0.

                pose Nat.add_cancel_l.

                match goal with 
                | h: ?x + ?y = ?x + ?z |- _ =>
                destruct (Nat.add_cancel_l y z x) as [e1 _]
                end.
                rmDirect.

                match goal with 
                | h: 1 = ?x + 1 |- _ => 
                symmetry in h;
                destruct (Nat.eq_add_1 _ _ h);
                breakAll
                end.

                easy.
                  
                

                destruct (length_zero_iff_nil ([e] ++ v2)).
                rmDirect.
                discriminate.
            }
            1:{
                assert ((s::w2) != []) as HnotNil. eauto using nil_cons.
                destruct (exists_last HnotNil).
                destruct s0.
                rewrite e0 in *.
                clear e0.

                inversion H.
                subst.

                all: tac_inj; subst.
                all: try tac_df.

                all: simpl in IHv2.
                all: pose (IHv2 _ _ H7).

                all: repeat rewrite app_assoc.
                all: try ((apply V_S_Pln) + (apply V_Pln) + (apply V_S_Pnd_Cal) + 
                (apply V_Pnd_Cal) + (apply V_S_Cal) + (apply V_Cal) + 
                (apply V_S_Pen_Ret) + (apply V_Pnd_Ret_bot) + 
                (apply V_Pnd_Ret with (t:=t)) + (apply V_Ret with (L:=L))); eauto.
                (* apply V_Pln *)
                (* repeat rewrite <- app_assoc *)
                (* ; eauto. *)

                all: rewrite <- app_assoc; simpl.

                all: try match goal with
                | h: VEndWith (?v++?e::?v2) ?L |- VEndWith (?v1++?e::?v2) ?L =>
                    apply (VListEndSame3 (e::v2) v v1)
                    ; eauto using nil_cons
                end; auto.
            }
        }
        
    Qed.
    (* end hide *)

    (** [L_DF_Local2]: this lemma shows that we can concatenate two
        parse trees, as long as the first parse tree has empty stack,
        and the two parse trees shares the same nonterminal at their
        ends. *)
    Lemma L_DF_Local2: ∀ v v1 w1 E, 
        (Df v [] w1)
        -> (Df v1 [] w1)
        -> (VEndWith v E) 
        -> (VEndWith v1 E) 
        -> ∀ v2 T2 w2, (Df (v++v2) T2 (w1++w2)) 
        -> (Df (v1++v2) T2 (w1++w2)).
    (* begin hide *)
    Proof.
        intros v v1 w1 E H1 H2 HE1 HE2 v2.

        induction v2 using @rev_ind.
        1:{
            intros.
            simpl in *.
            inversion H; 
            tac_inj; subst.

            destruct w1; try tac_df;
            simplList; tac_inj; subst.

            all: rewrite app_nil_r in *; auto.

            all: mergeUniqueDf; subst; auto.

            all: discriminate.
        }

        1:{
            intros.
            destruct w2.
            (* w2 = [] is impossible *)
            1:{
                rewrite app_nil_r in H.
                pose (L_Df_uniqueV _ _ _ _ _ H1 H).
                match goal with
                | h: length _ = length (?v++?v2++[?t]) |- _ =>
                    pose (app_length (v) (v2++[t]))
                end.
                rewrite e0 in e. clear e0.

                match goal with
                | h: ?v = ?v + ?w |- _ =>
                  pose (Nat.add_cancel_l 0 w v) as _h 
                  ; rewrite (Nat.add_0_r) in _h
                  ; destruct _h
                  ; rmDirect
                end.

                symmetry in H4.
                destruct (length_zero_iff_nil (v2 ++ [x])).
                rmDirect.
                tac_inj.
            }
            1:{
                assert ((s::w2) != []) as HnotNil. eauto using nil_cons.
                destruct (exists_last HnotNil).
                destruct s0.
                rewrite e in *.
                clear e.

                inversion H;
                subst.

                all: tac_inj; subst.
                all: try tac_df.

                all: simpl in IHv2.
                all: pose (IHv2 _ _ H7).

                all: repeat rewrite app_assoc.
                all: try ((apply V_S_Pln) + (apply V_Pln) + (apply V_S_Pnd_Cal) + 
                (apply V_Pnd_Cal) + (apply V_S_Cal) + (apply V_Cal) + 
                (apply V_S_Pen_Ret) + (apply V_Pnd_Ret_bot) + 
                (apply V_Pnd_Ret with (t:=t)) + (apply V_Ret with (L:=L))); eauto.

                pose (VListEndSame2).
                all: destruct v2.
                all: try (rewrite app_nil_r in *; mergeEnds; auto).

                all: match goal with
                | h: VEndWith (?v ++ ?v2 :: ?v3) ?L |- 
                    VEndWith (?v1 ++ ?v2 :: ?v3) ?L =>
                    apply (VListEndSame3 (v2::v3) v)
                    ; eauto using nil_cons
                end.

            }
        }

    Qed.
    (* end hide *)
  End Df2.

  (** The module [Core] provides the core lemmas used in the correctness
    proof *)
  Module Core.
    Import LEN_WF.
    Import Df2.
    Import Tac.
    
    (** [L4_1]: Lemma 4.1 shows that when we concatenate two parse trees
        using Lemma [L_DF_Local2], the stack does not change. *)
    Lemma L4_1: ∀ v1 v2 w1 w2 T,
      (Df v1 [] w1) ->
      (Df v2 T w2) ->
      (∃ Lu, VEndWith v1 Lu /\ VBeginWith v2 Lu) ->
      (Df (v1++v2) T (w1++w2)).
    (* begin hide *)
    Proof.
      intros v1 v2 w1 w2 T Hv1 Hv2 HConnect.

      induction Hv2;
      destruct HConnect as [Lu [HEnd HBegin]].

      all: try (extractHead).
      all: try match goal with 
      | h: (exists _, _) -> ?H |- _ => 
        assert (H) as Ind
        by (apply IHHv2; exists Lu;
        split; auto)
      end.
      all: try pose (VListEndSame2 _ v1 _ H) as HEnd2.
      all: try pose (VListEndSame2 _ v1 _ H0) as HEnd2.
      10:{

        (* get ind *)
        pose V_Ret.
        pose (V_Ret _ _ _ _ _ _ _ _ _ HEnd2 H0 Ind) as HDv.

        repeat rewrite app_assoc.
        apply HDv.
      }

      9: {
        (* get ind *)
        pose V_Ret.
        pose (V_Pnd_Ret _ _ _ _ _ _ _ H HEnd2 Ind) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      8: {
        pose (V_Pnd_Ret_bot _ _ _ _ _ H HEnd2 Ind) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      7:{
        (* fix mergeBegin *)

        mergeBegin.
        
        pose (V_Pnd_Ret_bot _ _ _ v1 w1 H HEnd Hv1) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      6: {
        pose (V_Cal _ _ _ _ _ _ _ _ H HEnd2 Ind) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      5: {
        mergeBegin.
        pose (V_Cal _ _ _ _ _ _ _ _ H HEnd Hv1) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      4: {
        pose (V_Pnd_Cal _ _ _ _ _ _ H HEnd2 Ind) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      3: {
        mergeBegin.
        pose (V_Pnd_Cal _ _ _ _ _ _ H HEnd Hv1) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      2: {
        pose (V_Pln _ _ _ _ _ _ H HEnd2 Ind) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }

      1:{
        mergeBegin.
        pose (V_Pln _ _ _ _ _ _  H HEnd Hv1) as HDv.
        repeat rewrite app_assoc.
        apply HDv.
      }
    Qed.


    Ltac extendEnd :=
      match goal with 
      | H: VEndWith ?v ?Lu,
        Ind: Df (?ea::?v) _ _ |- _ =>
        pose (VListEndSame2 _ [ea] _ H) as HEnd
      end.
    (* end hide *)

    (** [L4_3]: Lemma 4.3 shows that we can concatenate two parse trees
        if the stack of the first parse tree is a pending rule.. *)
    Lemma L4_3: ∀ _Lu a L v T w,
      Df [Calv (PndCalE _Lu a L)] [(PndCalE _Lu a L)] [Call a] ->
      Df v T w -> 
      VBeginWith v L ->
      ((
        Df (Calv (PndCalE _Lu a L)::v) T (Call a::w) 
        \/
        Df (Calv (PndCalE _Lu a L)::v) 
          (T++[(PndCalE _Lu a L)]) 
          (Call a::w))).
    (* begin hide *)
    Proof.
      intros Lu a L v T w Ha Hv HCnc.
      induction Hv.

      all: try extractHead.
      all: try match goal with 
      | h: ?H1 -> ?H,
        hh:?H1
      |- _ => 
        pose (h hh) as Ind
      end.
      all: try mergeBegin.

      1:{
        right.
        refine (V_Pln _ _ _ _ _ _ H _ Ha).
        apply EndA1.
        exists [], a, Lu. eauto.
      }

      1:{
        (* split; intro HT; try contradiction. *)

        (* destruct Ind as [HInd _]. *)
        (* pose (HInd HT) as Ind. *)
        destruct Ind.
        left.
        refine (V_Pln _ _ _ _ _ _ H _ H1).

        extendEnd. eauto.
        right.
        refine (V_Pln _ _ _ _ _ _ H _ H1).
        extendEnd. eauto.
      }

      1:{
        (* split; intro HT; try contradiction. inversion HT. *)
        right.
        refine (V_Pnd_Cal _ _ _ _ _ _ H _ Ha).
        apply EndA1.
        exists [], a, Lu. eauto.
      }

      1:{
        (* split; intro HT; try contradiction. inversion HT. *)
        
        destruct T.
        destruct Ind.
        left.
        refine (V_Pnd_Cal _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
        right.
        refine (V_Pnd_Cal _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.

        destruct Ind.

        left.
        refine (V_Pnd_Cal _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
        right.
        refine (V_Pnd_Cal _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
      }

      1:{
        right.
        refine (V_Cal _ _ _ _ _ _ _ _ H _ Ha).
        apply EndA1.

        exists [], a, Lu. eauto.
      }

      1:{
        destruct Ind.
        left.
        refine (V_Cal _ _ _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
        right.
        refine (V_Cal _ _ _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
      }

      1:{

        left.
        pose V_Pnd_Ret_bot.
        refine (V_Pnd_Ret _ _ _ _ _ _ _ H _ Ha).
        apply EndA1.

        exists [], a, Lu. eauto.
      }

      1:{
        destruct Ind.
        left.
        refine (V_Pnd_Ret_bot _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
        left.
        refine (V_Pnd_Ret _ _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
      }

      1:{
        destruct Ind.
        left.
        refine (V_Pnd_Ret _ _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
        right.
        refine (V_Pnd_Ret _ _ _ _ _ _ _ H _ H1).
        extendEnd.
        eauto.
      }

      1:{
        destruct Ind.
        left.
        refine (V_Ret _ _ _ _ _ _ _ _ _ _ H0 H1).
        extendEnd.
        eauto.
        right.
        refine (V_Ret _ _ _ _ _ _ _ _ _ _ H0 H1).
        extendEnd.
        eauto.
      }
    Qed.

    Lemma LSameEnd: ∀ {A} (x:list A) a y z t, x++[a]=y++t::z ->
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

    Lemma LSameEnd2: ∀ {x:Type} (l1: list x) l2 l3 a, (l1++l2=l3++[a])->
      (l2 != [])->
      ∃ l, l2=l++[a].
    Proof.
      intros x l1 l2 l3 a h1 h2.
      destruct l2. contradiction.
      symmetry in h1.
      pose (LSameEnd l3 a l1 _ _ h1). 
      destruct e.
      exists x1.
      auto.
    Qed.

    Lemma LSameEnd3: ∀ {x:Type} t t1 (l1: list x) l2 a, (t::t1::l1=l2++[a])->
      ∃ l, t1::l1=l++[a].
    Proof.
      intros.
      apply (LSameEnd2 [t] (t1::l1) l2 a H).
      eauto using nil_cons.
    Qed.

    Lemma LSingleEnd: ∀ {A} (x:list A) a b, x++[a]=[b] ->
      (x=[])/\(a=b).
    Proof.
      intros.
      apply (app_inj_tail _ [] _ _ H).
    Qed.

    Lemma LAppLast2: ∀ {A} (x:list A) y z, x++y++z=x++(y++z).
    Proof.
      auto.
    Qed.
    (* end hide *)

    (** [LCallStack]: this lemma show that if a parse tree ends with a
        call rule, then its stack is not empty. *)
    Lemma LCallStack: ∀ v _v va T w,
      (v = _v ++ [Calv va]) ->
      (Df v T w) ->
      (T != []).
    (* begin hide *)
    Proof.
      intros.
      destruct H0.
      
      all: try (symmetry in H; destruct (LSingleEnd _ _ _ H) as [x H2]; inversion H2).
      all: try (destruct (app_inj_tail _ _ _ _ H) as [y H4]; inversion H4).
      all: try easy.
    Qed.

    Lemma LSingleList: ∀ {A} (x:A) y, x=y -> [x]=[y].
    Proof.
    intros.
    subst.
    auto.
    Qed.
    (* end hide *)

    (* [VConnect]: this lemma shows that if we split a parse tree into
      two parse trees, then they share the same nonterminal at their
      ends. *)
    Lemma VConnect: ∀ v T w , Df v T w ->
      (∀ v1 v2 Lv1 Lv2, v=v1++v2 -> 
        v1 != [] -> v2 != [] -> 
        VEndWith v1 Lv1 -> VBeginWith v2 Lv2 -> 
        Lv1=Lv2).
    (* begin hide *)
    Proof.
      intros v T w H.
      induction H.
      all: intros v1 v2 Lv1 Lv2 Hsplit Hv1Emp Hv2Emp Hv1End Hv2Begin.

      (* remove the single cases *)
      all: try 
      match goal with 
      | Hsplit: [?v] = ?v1 ++ ?v2, Hv1Emp: ?v1 != [], Hv2Emp: ?v2 != [] |- _ =>
        destruct v1;
        destruct v2; try contradiction;
        inversion Hsplit
        ; pose (app_cons_not_nil v1 v2 v0)
        ; contradiction
      end.

      (* v2 must != 0 *)
      all: destruct v2; try contradiction.
      
      (* v2 and v has the same end *)
      all:
      match goal with 
      | (* IHDv: ∀ _, _, *)
        Hsplit: ?v ++ [?ve] = ?v1 ++ ?t::?v2,
        Hv2Emp: ?t::?v2 != [] |- _ => 
        (* auto *)
        destruct (LSameEnd _ _ _ _ _ Hsplit) as [v2pre Hv2Split]
        (* ; auto *)
        ; rewrite Hv2Split in Hsplit
        ; rewrite app_assoc in Hsplit
        ; assert (v=v1 ++ v2pre) as Hvsplit2
          by (apply (app_inj_tail_iff v (v1++v2pre) ve ve); auto)
      end.
      
      (* v2 could be single *)
      all: destruct v2pre.

      (* If v2pre=[] *)
      all: try
        match goal with 
        | hvsplit2: ?v = ?v1++[],
          Hv2Split: ?t::?v2 = [] ++ [?ve],
          Hv2Begin: VBeginWith (?t::?v2) ?Lv2,
          HvEnd: VEndWith ?v ?L,
          Hv1End: VEndWith ?v1 ?Lv1
        |- _ =>
          rewrite app_nil_r in hvsplit2
          ; simpl in Hv2Split
          ; rewrite Hv2Split in Hv2Begin
          ; rewrite Hvsplit2 in HvEnd
          ; pose (VEndSameEq _ _ _ HvEnd Hv1End) as HLLuu1
        end.

      (* 9:{ *)

      Ltac extractBegin :=
        match goal with 
        | Hv2Begin: VBeginWith [_ (_ ?L ?_i ?_Lu2)] ?L2 |- _ =>
          assert (L=L2) as HLLuu2
            by (
              inversion Hv2Begin;
              repeat (breakEx);
              repeat (simplList); auto)
        | Hv2Begin: VBeginWith [_ (_ ?L ?_i ?_Lu2 _ _)] ?L2 |- _ =>
          assert (L=L2) as HLLuu2
            by (
              inversion Hv2Begin;
              repeat (breakEx);
              repeat (simplList); auto)
          end.

      all: try
        extractBegin.
      (* } *)

      all: try (rewrite HLLuu2 in HLLuu1; auto).

      (* If v2pre != [] *)

      all: try
      match goal with 
      | IHDv: ∀ _, _,
        Hvsplit2: ?v = ?v1 ++ ?t :: ?v2pre
      |- _ =>
        apply (IHDv v1 (t::v2pre) Lv1 Lv2)
        ; eauto using nil_cons
      end.

      all: try 
      match goal with 
      | Hv2Begin: VBeginWith ?v ?Lu,
        H2: ?v = ?v1++?v2
      |- 
        VBeginWith ?v1 ?Lu
      =>
        apply (VListBeginSame _ v2)
        ; rewrite H2 in Hv2Begin
        ; eauto using nil_cons
      end.

      (* v2 does not begin with RetMat *)
      all: try
      match goal with 
      | Hv2Begin: VBeginWith [Retv (MatRetE ?L1 ?a ?L2 ?b ?L3)] ?Lv2 |- _ =>
        inversion Hv2Begin
        ; repeat breakEx
        ; discriminate
      end.

    Qed.

    Lemma VHasHead: ∀ v T w, Df v T w ->
      ∃ L, VBeginWith v L.
    Proof.
      intros.
      induction H.
      exists L. apply BeginC. exists [], c, L1. auto.
      all: repeat breakEx.

      Ltac solve := match goal with 
      | H:VBeginWith ?v ?L2 |- 
        VBeginWith (?v ++ ?ev) ?L2
      => 
        apply (VListBeginSame2 _ ev _ H)
      end.
      all: try (exists x; solve).
      exists L. apply BeginA1. exists [], a, (L1). auto.

      exists L. apply BeginA2. exists [], a, b, (L1), L2. auto.
      exists L. apply BeginB. exists [], (b), (L1). auto.
    Qed.

    Lemma VHasEnd: ∀ v T w, Df v T w ->
      ∃ L, VEndWith v L.
    Proof.
      intros.
      inversion H;
      subst.
      1,2,3,4,5,6,7,8,9 :exists L1.

      1,2,3,4,5: constructor;
      (exists [] + exists v0);
      repeat eexists;
      fail.

      1,2,3,4: constructor;
      (exists [] + exists v0);
      repeat eexists;
      fail.

      exists L3.
      apply EndB2.
      repeat eexists.
    Qed.
    (* end hide *)

    (** [Breaking]: the invariant of the forward small-step relation [Df
      v T w]. The invariant [Breaking] shows that based on the stack
      [T], we can split the parse tree [v] to [v=v1++[r]++v2], where
      [v1] satisfies [Df] and [v2] satisfies the big-step derivation
      [Dm]. Further, when the stack [T] is empty, the big-step
      derivation can be extended to [v]. *)
    Inductive Breaking : 
    (list VE) -> list CalEdge -> list symbol -> Prop :=
    | BS : ∀ v T w,
        (Df v T w ->
        ( T=[] ->
          (∃ Lv L,
          ((VBeginWith v Lv) /\
          (VEndWith v L) /\
          (∀ w' v',
          (Dm L w' v' ->
          Dm Lv (w++w') (v++v')))))
        ) /\
        ( T != [] ->
          (∃ T' v1 v2 w1 w2 a _Lua La,
          ( (
                T=(PndCalE _Lua a La)::T' /\
                v=v1++[Calv (PndCalE _Lua a La)]++v2 /\
                w=w1++[Call a]++w2 /\
                (w1 != [] -> Df v1 T' w1) /\
                (w1 != [] -> Breaking v1 T' w1) /\
                (w1=[]  -> v1=[]) /\
                (w1=[]  -> T'=[]) /\

                in_rules (_Lua, Alt_Linear (Call a) La) P /\
                ( ∀ L Lv w' v' ,
                    VBeginWith v Lv ->
                    VEndWith v L ->
                    Dm L w' v' ->
                    Dm La (w2++w') (v2++v') /\
                    Dm Lv (w++w') (v++v') 
                )
              )
              \/
              (
                ∃ b la2,
                T=(MatCalE _Lua a La b la2)::T' /\
                v=v1++[Calv (MatCalE _Lua a La b la2)]++v2 /\
                w=w1++[Call a]++w2 /\
                (w1 != [] -> Df v1 T' w1) /\
                (w1 != [] -> Breaking v1 T' w1) /\
                (w1=[]  -> v1=[]) /\
                (w1=[]  -> T'=[]) /\

                in_rules (_Lua, Alt_Match (a) (b)  La la2) P /\
                (∀ v2e, VEndWith v2 v2e -> ∃ _v2e, v2e=V0 _v2e) /\
                ( ∀ L Lv w' v' ,
                    VBeginWith v Lv->
                    VEndWith v L ->
                    Dm L w' v' ->
                    Dm La (w2++w') (v2++v')
                )
              )
            )
        )))
        -> Breaking v T w.


    (* begin hide *)
    Ltac getBreak :=
      match goal with
      | Hw1NotEmpBreak: ?c::?w != [] -> Breaking _ _ _ |- _ =>
        assert (c::w != []) as _Hnot by eauto using nil_cons
        ; pose (Hw1NotEmpBreak _Hnot) as HBreak
      end.
    (* end hide *)

    (** [L4_2]: Lemma 4.2 shows that the forward small-step derivation
      satisfies the invariant [Breaking]. *)
    Lemma L4_2: ∀ v T w, Breaking v T w.
    (* begin hide *)
    Proof.
      constructor.
      intros HvTw.
      induction HvTw.

      (* The linear cases *)
      1: {
        split; intro HTEmp; try contradiction.

        exists L, L1.

        split. apply BeginC. exists [], c, (L1). auto.
        split. apply EndC. exists [], (c), L. auto.
        intros w' v' HDm.

        constructor; auto.
      }
    
      1:{
        split; intro HTEmp.
        1: destruct IHHvTw as [IHHvTw _h]; clear _h. 
        2: destruct IHHvTw as [_h IHHvTw]; clear _h.

        pose (IHHvTw HTEmp);
        repeat (breakEx + breakAnd).

        exists x, L1.

        split.
        apply (VListBeginSame2 _ _ _ H1).
        split.
        constructor; repeat eexists.
        intros.
        repeat rewrite <- app_assoc.
        apply e.

        mergeEnds.
        constructor; auto.

        (* T != [] *)

        pose (IHHvTw HTEmp);
        repeat (breakEx + breakAnd + breakOr);
        subst.
        
        (* For pending rules *)
        1:{
          exists x, x0, (x1 ++ [Plnv (PlnE L c L1)]), x2, (x3 ++ [Plain c]).
          exists x4, x5, x6.
          left.

          split; auto.
          split; auto.
          repeat rewrite -> app_assoc; auto.
          split; auto.
          repeat rewrite -> app_assoc; auto.
          split; auto.
          split; auto.
          split; auto.
          split; auto.
          split; auto.

          intros.
          
          
          destruct (H1 L Lv ([Plain c] ++ w') ([Plnv (PlnE L c L1)] ++ v')).
                  
          apply (VListBeginSame _ _ _ H2).
          eauto using app_cons_not_nil.

          auto.
          constructor; auto.
          assert (L1=L0).
          1:{
            inversion H3;
            repeat breakEx;
            destruct (app_inj_tail _ _ _ _ H10);
            inversion H14; auto.
          }
          subst; auto.

          split; auto;
          
          repeat rewrite <- app_assoc;
          auto.
          repeat rewrite <- app_assoc in H11.
          auto.
        }

        (* For mathing rules *)
        exists x, x0, (x1 ++ [Plnv (PlnE L c L1)]), x2, (x3 ++ [Plain c]).
        exists x4, x5, x6.
        right.
        exists x7, x8.

        split; auto.
        split; auto.
        repeat rewrite -> app_assoc; auto.
        split; auto.
        repeat rewrite -> app_assoc; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        1:{
          intros.

          assert (v2e=L1).
          1:{
            inversion H2;
            repeat (breakEx);
            destruct (app_inj_tail _ _ _ _ H3);
            inversion H13; auto.
          }

          subst.

          destruct x1.
          destruct (A_VPG_Match _ _ _ _ _ H9).

          assert (L=x6).
          1:{
            inversion H0;
            repeat (breakEx);
            destruct (app_inj_tail _ _ _ _ H11);
            inversion H15; auto.
          }
          subst.

          destruct (A_VPG_Linear _ _ _ H); auto.
          repeat (breakEx + breakAnd).
          eauto.


          assert (v :: x1 != []) as notnil.
          eauto using nil_cons.
    
          destruct (exists_last notnil).
          destruct s.
          rewrite e in *.
    
          destruct (H10 L).
          apply (VListEndSame2).
          1:{
            inversion H0;
            repeat breakEx;
            do 2 rewrite  app_assoc in H3;
            destruct (app_inj_tail _ _ _ _ H3);
            subst;
            (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
            exists []; repeat eexists; fail.
          }
    
          subst.
    
          destruct (A_VPG_Linear _ _ _ H).
          eauto.

          repeat (breakEx + breakAnd).
          eauto.
        }
        intros.
        
        repeat rewrite <- app_assoc.

        apply (H1 L Lv ([Plain c] ++ w') ([Plnv (PlnE L c L1)] ++ v')).
                
        apply (VListBeginSame _ _ _ H2).
        eauto using app_cons_not_nil.

        auto.
        constructor; auto.
        assert (L1=L0).
        1:{
          inversion H3;
          repeat breakEx;
          destruct (app_inj_tail _ _ _ _ H11);
          inversion H15; auto.
        }
        subst; auto.
      }

      (* i=Call, case 1 *)
      1:{
        split; intros.
        inversion H0.
        exists [], [], [], [], [], (a), L, L1.
        left.

        split; auto.
        split; auto.
        split; auto.
        split; auto.
        intros; contradiction.
        split; try contradiction.
        split; auto.
        split; auto.
        split; auto.
        intros.

        assert (L1=L0).
        1:{
          inversion H2;
          repeat breakEx;
          subst;
          destruct (app_inj_tail [] _ _ _ H4);
          inversion H6; auto.
        }
        subst.

        split; auto.

        mergeBegin.
        constructor; auto.
      }

      (* NOTE i=Call 2 *)
      1:{
        split; intros.
        inversion H1.
        exists T, v, [], w, [], (a), L, L1.

        left.

        split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.

        1:{
          intro.
          constructor; intros.
          destruct T;
          breakAnd;
          rmDirect.
          rmDirect.
          split; intros.
          eauto.
          contradiction.
          split; intros.
          discriminate.
          auto.
        }

        pose (L_Dv_w _ _ _ HvTw).

        split; auto. intro. contradiction.
        split; auto. intro. contradiction.
        split; auto. 

        intros.


        assert (L1=L0).
        1:{
          inversion H3;
          repeat breakEx;
          subst;
          destruct (app_inj_tail _ _ _ _ H5);
          inversion H7; auto.
        }
        subst.

        split; auto.

        destruct T.

        1:{
          destruct IHHvTw as [Ind _].
          rmEmpRefl.

          repeat (breakEx + breakAnd).

          mergeBegins2.

          repeat rewrite <- app_assoc.
          apply Ind.

          mergeEnds.

          apply DLa; auto.
        }

        (* T != [] *)
        destruct IHHvTw as [_ Ind].
        destruct Ind; auto using nil_cons.

        repeat (breakEx + breakAnd + breakOr + simplList).
        subst.

        destruct (H5 L Lv ([Call a] ++ w') ([Calv (PndCalE L a L0)] ++ v')).
        refine (VListBeginSame _ _ _ H2 _).
        eauto using app_cons_not_nil.
        auto.

        constructor; auto.

        repeat rewrite app_assoc in *;
        auto.

        (* This case is not possible *)
        subst.

        destruct x1.
        1: {
          assert (L=x6).
          1:{
            inversion H0;
            repeat (breakEx); subst;
            destruct (app_inj_tail _ _ _ _ H6);
            inversion H8;
            auto.
          }
          subst.

          destruct (A_VPG_Match _ _ _ _ _ H13).
          destruct H6. subst.
          destruct (A_VPG_Linear _ _ _ H ).
          eauto.
          repeat (breakEx + breakAnd).
          discriminate.
        }

        assert (v :: x1 != []) as notnil.
        eauto using nil_cons.

        destruct (exists_last notnil).
        destruct s.
        rewrite e in *.

        destruct (H14 L).
        1:{
          inversion H0;
          repeat (breakEx); subst;
          repeat rewrite -> app_assoc in H6;
          destruct (app_inj_tail _ _ _ _ H6);
          inversion H8;
          (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
          exists x9; repeat eexists; fail.
        }
        destruct (A_VPG_Linear _ _ _ H ).
        eauto.

        repeat (breakEx + breakAnd).
        discriminate.
      }

      (* i=Call Mat Single *)
      1:{
        split; intros.
        inversion H0.
        exists [], [], [], [], [], (a), (L), L1.

        right.
        exists b, L2.

        split; auto.
        split; auto.
        split; auto.
        split; auto.
        intro; easy.
        split.
        intro; easy.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        intros. inversion H1; repeat breakEx;
        match goal with 
        | h: [] = ?x ++ [?e] |- _ =>
          pose (app_cons_not_nil x [] e);
          contradiction
        end.

        intros.

        assert (L1=L0).
        1:{
          inversion H2;
          repeat breakEx;
          subst;
          destruct (app_inj_tail [] _ _ _ H4);
          inversion H6; auto.
        }
        subst.
        auto.
      }

      (* i=Call Mat *)
      1:{
        split; intros.
        inversion H1.
        exists T, v, [], w, [], (a), (L), L1.
        right.
        exists b, L2.

        split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        1:{
          intro.
          constructor; intros.
          destruct T;
          breakAnd;
          rmDirect.
          rmDirect.
          split; intros.
          eauto.
          contradiction.
          split; intros.
          discriminate.
          auto.
        }


        pose (L_Dv_w _ _ _ HvTw).

        split; auto. intro. contradiction.
        split; auto. intro. contradiction.
        split; auto. 

        split; auto.

        intros.

        (* VEndWith [] _ *)
        inversion H2;
        repeat (breakEx);
        match goal with 
        | h: [] = ?x ++ [?r] |- _ =>
          assert ([] != x ++ [r]);
          eauto using app_cons_not_nil;
          contradiction
        end.

        intros.

        assert (L1=L0).
        1:{
          inversion H3;
          repeat breakEx;
          subst;
          destruct (app_inj_tail _ _ _ _ H5);
          inversion H7; auto.
        }
        subst.
        auto.
      }

      (* i=Ret 1 *)
      1:{
        split; intros;
        try contradiction.
        exists L, L1.

        split. apply BeginB. exists [], b, L1. auto.
        split. apply EndB1. exists [], b, L. auto.

        intros w' v' HDm.

        constructor; auto.
      }

      (* i=Ret 2 *)
      1:{
        split; intros;
        try contradiction.

        match goal with 
        | |- 
          ∃ Lv L, VBeginWith (?v++[?ve]) ?_Lu /\ VEndWith (?v++[?ve]) ?_LuEnd /\ _
        => 
          destruct (VHasHead _ _ _ HvTw) as [LvHead HVHead];
          match ve with 
          | _ (_ _ _ ?L3) => exists LvHead, L3
          end
        end.

        split. apply VListBeginSame2. auto.
        split. apply VListEndSame2. apply EndB1. exists [], (b), (L). auto.

        intros w' v' HDm.

        destruct IHHvTw as [IHHvTw _h]; clear _h.
        rmEmpRefl.

        repeat (breakEx + breakAnd).


        mergeBegins.
        repeat rewrite <- app_assoc.
        apply IHHvTw.

        mergeEnds.

        apply DLb; auto.
      }

      (* Pnd Ret is similar to Mat Ret *)
      1: {
        split.
        intro HTEmp.

        all: destruct IHHvTw as [_h IHHvTw];
        clear _h. 

        (* find v ends *)
        match goal with 
        | |- 
          ∃ Lv L, VBeginWith (?v++[?ve]) ?_Lu /\ 
          VEndWith (?v++[?ve]) ?_LuEnd /\ _
        => 
          destruct (VHasHead _ _ _ HvTw) as [LvHead HVHead];
          match ve with 
          | _ (_ _ _ (?L3)) => exists LvHead, L3
          end
        end.

        split.
        (* begin with the same *)
        match goal with 
        | Hv2Begin: VBeginWith ?v ?Lu
        |- 
          VBeginWith (?v++?vv) ?Lu
        =>
          apply (VListBeginSame2 _ _ _ Hv2Begin)
        end.
        
        split.
        apply (VListEndSame2).
        apply EndB1. exists [], (b), (L). auto.

        (* pose the Ind *)
        match goal with 
        | IHHvTw: ?t::?T != [] -> ∃ _, _ 
        |- _ =>
          assert (t::T != []) as HtTNotEmp by (eauto using nil_cons; eauto) 
          ; pose (IHHvTw HtTNotEmp) as Ind
          ; destruct Ind as [T' [v1 [v2 [w1 [w2 [a0 [_Lua [La Ind]]]]]]]]
        end.

        intros.

        destruct Ind.
        1:{
          clear IHHvTw.
          repeat breakAnd.

          destruct (H2 L LvHead ([Ret b] ++ w') ([Retv (PndRetE L b L1)] ++ v')).
          auto.
          auto.

          constructor; auto.
          repeat rewrite <- app_assoc.
          auto.
        }

        repeat (breakAnd + breakEx).

        subst.

        destruct v2.
        1: {
          assert (L=La).
          1:{
            inversion H0;
            repeat (breakEx); subst;
            destruct (app_inj_tail _ _ _ _ H4);
            inversion H12;
            auto.
          }
          subst.

          destruct (A_VPG_Match _ _ _ _ _ H10).
          destruct H4. subst.
          destruct (A_VPG_Linear _ _ _ H ).
          eauto.
          repeat (breakEx + breakAnd).
          discriminate.
        }

        assert (v :: v2 != []) as notnil.
        eauto using nil_cons.

        destruct (exists_last notnil).
        destruct s.
        rewrite e in *.

        destruct (H11 L).
        1:{
          inversion H0;
          repeat (breakEx); subst;
          repeat rewrite -> app_assoc in H4;
          destruct (app_inj_tail _ _ _ _ H4);
          inversion H12;
          (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
          exists x1; repeat eexists; fail.
        }
        destruct (A_VPG_Linear _ _ _ H ).
        eauto.

        repeat (breakEx + breakAnd).
        discriminate.


        (* T != empty *)

        destruct IHHvTw.
        eauto using nil_cons.

        intros.

        destruct T.
        contradiction.


        repeat (breakAnd + breakOr + breakEx).

        1:{
          destruct x2.
          1:{
            rmEmpRefl.
            rmEmpRefl.
            subst.
            discriminate.
          }
          rmEmpConsInfer.
          rmEmpConsInfer.

          rename H1 into outP.

          rmDirect.
          rmDirect.

          
          (* destruct the breaking *)
          destruct H1.

          match goal with
          | h: ?h2 -> _, g:?h2 |- _ =>
            destruct (h g)
            ; clear h
          end.

          simplList.
          subst.

          match goal with 
          | h: ?v::?s != [] -> _ |- _ =>
            assert (v::s != []) as _H2 by eauto using nil_cons
            ; pose (h _H2) as d3
          end.

          repeat (breakAnd + breakOr + breakEx).
          1:{
            simplList; subst.
            exists x, x0.
            exists (((x7) ++ [Calv (PndCalE x5 x4 x6)] ++ x1) ++ [Retv (PndRetE L b L1)]).
            exists x8, ((x9) ++ [Call x4] ++ x3 ++ [Ret b]).
            exists x10, x11, x12.

            left.

            split; auto.
            split; auto.
            repeat rewrite <- app_assoc; auto.

            split; auto.
            repeat rewrite <- app_assoc; auto.

            split; auto.
            split; auto.
            split; auto.
            split; auto.
            split; auto.
            intros.
            rename H1 into inP.

            destruct (inP x5 Lv ([Call x4] ++ x3 ++ [Ret b] ++ w') 
              ([Calv (PndCalE x5 x4 x6)] ++ x1 ++ 
              [Retv (PndRetE L b L1)] ++ v')).

            rewrite <- app_assoc in H3.
            apply (VListBeginSame _ _ _ H3).
            eauto using app_cons_not_nil.

            1:{
              pose (VConnect _ _ _ HvTw (x0 ++ 
              [Calv (PndCalE x11 x10 x12)] ++ x7)
              ([Calv (PndCalE x5 x4 x6)] ++ x1)  ).
              
              destruct x7.

              1:{
                destruct (e x12 x5);
                eauto using app_cons_not_nil, nil_cons;
                simpl.

                apply EndA1.
                repeat eexists.

                apply BeginA1.
                repeat eexists.

                apply (VListEndSame2).
                apply EndA1.
                exists [].
                repeat eexists.
              }

              assert (v :: x7 != []) as notnil.
              eauto using nil_cons.
        
              destruct (exists_last notnil).
              destruct s0.
              rewrite e0 in *.

              
              destruct (VHasEnd _ _ _ H7).
              
              destruct (VConnect _ _ _ HvTw 
              (x0 ++ [Calv (PndCalE x11 x10 x12)] ++ x13 ++ [x14])
                ([Calv (PndCalE x5 x4 x6)] ++ x1) x15 x5);
              eauto using app_cons_not_nil, nil_cons.

              apply BeginA1. repeat eexists.            
            }

            (* Build the sequence of derivation *)

            constructor; auto.

            apply outP with (L:=L) (Lv:=Lv).

            apply (VListBeginSame _ _ _ H3).
            eauto using app_cons_not_nil.

            auto.

            constructor; auto.

            assert (L1=L0) as HLLuu2.
            1:{
              inversion H4;
              repeat (breakEx);
              repeat (simplList);
              destruct (app_inj_tail _ _ _ _ H1);
              inversion H18;
              auto.
            }

            subst; auto.

            repeat rewrite <- app_assoc in *.
            split; auto.
          }

          (* Not possible *)
          (* Using VConnect *)
          (* Two cases *)

          
          pose (VConnect _ _ _ HvTw v0 ([Calv (PndCalE x5 x4 x6)] ++ x1) 
          ) as HC.

          destruct x7.
          subst.

          assert (x12 = x5).
          apply (HC x12 x5); 
          eauto using app_cons_not_nil, nil_cons.

          apply EndA2.
          exists x0. repeat eexists.
          apply BeginA1. repeat eexists.

          subst.
          destruct (A_VPG_Match _ _ _ _ _ H14).
          destruct (A_VPG_Linear _ _ _ H10); auto.
          repeat (breakEx + breakAnd).
          discriminate.
          subst.

          assert (v :: x7 != []) as notnil.
          eauto using nil_cons.
    
          destruct (exists_last notnil).
          destruct s0.
          rewrite e in *.

          destruct (VHasEnd _ _ _ H7).
    
          assert (x17=x5).
          apply (HC x17 x5); 
          eauto using app_cons_not_nil, nil_cons.
          apply BeginA1. repeat eexists.
          subst.

          destruct (H15 x5).
          apply (VListEndSame2).
          
          1:{
            inversion H4;
            repeat breakEx;
            do 2 rewrite  app_assoc in H5;
            destruct (app_inj_tail _ _ _ _ H5);
            subst;
            (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
            exists []; repeat eexists; fail.
          }
          subst.

          destruct (A_VPG_Linear _ _ _ H10).
          eauto.
    
          repeat (breakEx + breakAnd).
          discriminate.

        }

        (* This is not possible *)
        destruct x1;
        subst.

        assert (L = x6).
        1:{
          inversion H0;
          repeat breakEx;
          destruct (app_inj_tail _ _ _ _ H4);
          inversion H14.
          subst. auto.
        }
        subst.

        destruct (A_VPG_Match _ _ _ _ _ H10).
        destruct (A_VPG_Linear _ _ _ H); auto.
        repeat (breakEx + breakAnd).
        discriminate.


        assert (v0 :: x1 != []) as notnil.
        eauto using nil_cons.

        destruct (exists_last notnil).
        destruct s.
        rewrite e in *.

        destruct (H11 L).
        apply (VListEndSame2).
        1:{
          inversion H0;
          repeat breakEx;
          do 2 rewrite  app_assoc in H4;
          destruct (app_inj_tail _ _ _ _ H4);
          subst;
          (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
          exists []; repeat eexists; fail.
        }

        subst.

        destruct (A_VPG_Linear _ _ _ H).
        eauto.

        repeat (breakEx + breakAnd).
        discriminate.

      } 

      (* Mat Ret *)
      1: {
        split.
        intro HTEmp.

        all: destruct IHHvTw as [_h IHHvTw];
        clear _h. 

        (* find v ends *)
        match goal with 
        | |- 
          ∃ Lv L, VBeginWith (?v++[?ve]) ?_Lu /\ 
          VEndWith (?v++[?ve]) ?_LuEnd /\ _
        => 
          destruct (VHasHead _ _ _ HvTw) as [LvHead HVHead];
          match ve with 
          | _ (_ _ _ (?L3)) => exists LvHead, L3
          end
        end.

        split.
        (* begin with the same *)
        match goal with 
        | Hv2Begin: VBeginWith ?v ?Lu
        |- 
          VBeginWith (?v++?vv) ?Lu
        =>
          apply (VListBeginSame2 _ _ _ Hv2Begin)
        end.
        
        split.
        apply (VListEndSame2).
        apply EndB2. exists [], a, (b), (L1), L2. auto.

        (* pose the Ind *)
        match goal with 
        | IHHvTw: ?t::?T != [] -> ∃ _, _ 
        |- _ =>
          assert (t::T != []) as HtTNotEmp by (eauto using nil_cons; eauto) 
          ; pose (IHHvTw HtTNotEmp) as Ind
          ; destruct Ind as [T' [v1 [v2 [w1 [w2 [a0 [_Lua [La Ind]]]]]]]]
        end.

        intros.

        destruct Ind.
        1:{
          repeat breakAnd.
          discriminate.
        }

        repeat (breakAnd + breakEx).
        simplList.
        subst.

        (* First get the ...<awb> part *)
        assert (Dm _Lua ([Call a0] ++ w2 ++ [Ret x] ++ w')
          ([Calv (MatCalE _Lua a0 La x x0)] ++ v2 ++ [Retv (MatRetE _Lua a0 La x x0)] ++ v'))
        as Dm2.
        1:{
          constructor; auto.
          pose (H2 L LvHead [] []).
          do 2 rewrite app_nil_r in d.
          apply d.
          auto.
          auto.
          constructor; auto.
        }

        (* Consider w1 *)
        destruct w1.

        1:{
          (* w1 = [] *)
          rmEmpRefl.
          rmEmpRefl.
          subst.
          repeat rewrite <- app_assoc.
          simpl in *.

          assert (_Lua = LvHead).
          1:{
            inversion HVHead;
            repeat breakEx;
            simplList;
            auto.
          }
          
          subst.
          apply Dm2.
        }

        rmDirect.
        rmDirect.

        inversion H4.

        1:{
          clear IHHvTw.

          rmDirect.
          repeat (breakAnd + breakOr + breakEx).
          rmDirect.
          rmDirect.
          subst.
          repeat (breakAnd + breakOr + breakEx).
          assert (LvHead = x1).
          1:{
            inversion HVHead;
            inversion H5;
            repeat (breakAnd + breakOr + breakEx);
            subst;
            inversion H7; auto.
          }
          subst.

          repeat rewrite <- app_assoc.
          apply H13.

          assert (x2=_Lua).
          1:{
            apply (VConnect _ _ _ HvTw v1 
              ([Calv (MatCalE _Lua a0 La x x0)] ++ v2)
              x2 _Lua);
            eauto using nil_cons.
            apply (L_Dv_v _ _ _ H3).
            apply BeginA2.
            repeat eexists.
          }

          subst; auto.
        }

        intros.

        rmDirect.
        repeat (breakAnd + breakOr + breakEx).
        discriminate.

        simplList; subst.

        destruct x.
        contradiction.

        assert (x2 != []).
        1:{
          destruct x2.
          repeat rmDirect.
          subst.
          contradiction.
          auto.
        }
        rmDirect.
        rmDirect.

        match goal with 
        | h: Breaking _ _ _ |- _ => 
          destruct h
        end.

        rmDirect.

        repeat (breakAnd + breakOr + breakEx).
        rmDirect.
        repeat (breakAnd + breakOr + breakEx).

        1:{
          (* PndRet *)
          subst.
          exists x0, (x2).
          exists (x9 ++
          [Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1 ++
            [Retv (MatRetE x5 x4 x6 x7 x8)]).
          exists x10, (x11 ++ [Call x4] ++ x3 ++ [Ret x7]).
          exists x12, x13, x14.

          left.

          split; auto.
          split; auto.
          repeat rewrite app_assoc.
          split; auto.
          repeat rewrite app_assoc.
          split; auto.
          split; auto.
          split; auto.
          split; auto.
          split; auto.
          split; auto.

          intros.

          destruct (H6 x5 Lv ([Call x4] ++ x3 ++ [Ret x7] ++ w')
            ([Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1 ++
            [Retv (MatRetE x5 x4 x6 x7 x8)] ++ v')).

          do 2 rewrite <- app_assoc in H7.

          pose (VListBeginSame _ _ _ H7).
          rewrite <- app_assoc in v.
          apply v.
          eauto using app_cons_not_nil.

          pose (VConnect _ _ _ HvTw
            (x2 ++ [Calv (PndCalE x13 x12 x14)] ++ x9) 
            ([Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1)) as HC.

          (* Consider x9 *)
          destruct x9.
          1:{
            destruct (HC x14 x5);
            eauto using app_cons_not_nil, nil_cons.
            apply EndA1. repeat eexists.
            apply BeginA2. repeat eexists.
            apply EndA1. repeat eexists.
          }

          assert (v :: x9 != []) as notnil.
          eauto using nil_cons.
    
          destruct (exists_last notnil).
          destruct s.
          rewrite e in *.

          destruct (VHasEnd _ _ _ H5).

          destruct (HC x17 x5);
          eauto using app_cons_not_nil, nil_cons.
          apply BeginA2. repeat eexists.


          constructor;
          eauto.

          1:{
            pose (H2 L Lv [] []).
            do 2 rewrite app_nil_r in d.
            apply d.

            repeat rewrite app_assoc.
            apply (VListBeginSame _ _ _ H7).
            repeat rewrite <- app_assoc.
            eauto using app_cons_not_nil.
            auto.

            constructor; auto.
          }

          assert (x8 = L0).
          1:{
            inversion H12;
            repeat (breakEx); subst;
            destruct (app_inj_tail _ _ _ _ H19);
            inversion H21;
            auto.
          }
          subst; auto.


          repeat rewrite <- app_assoc in *.
          split; auto.
        }

        subst.
        exists x0, (x2).
        exists (x9 ++
        [Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1 ++ 
          [Retv (MatRetE x5 x4 x6 x7 x8)]).
        exists x10, (x11 ++ [Call x4] ++ x3 ++ [Ret x7]).
        exists x12, x13, x14.

        right.
        exists x15, x16.

        split; auto.
        split; auto.
        repeat rewrite app_assoc.
        split; auto.
        repeat rewrite app_assoc.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.
        split; auto.

        intros.

        split; auto.
        intros.

        assert (v2e = x8).
        1:{
          inversion H7;
          repeat (breakEx); subst;
          destruct (app_inj_tail _ _ _ _ H12);
          inversion H20;
          auto.
        }
        subst; auto.

        pose (VConnect _ _ _ HvTw
        (x2 ++ [Calv (MatCalE x13 x12 x14 x15 x16)] ++ x9) 
        ([Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1)) as HC.

        (* consider x9 *)
        1:{
          destruct x9.
          assert (x14=x5).
          apply (HC x14 x5);
          eauto using app_cons_not_nil, nil_cons.
          apply EndA2. repeat eexists.
          apply BeginA2. repeat eexists.
          subst.
          
          destruct (A_VPG_Match _ _ _ _ _ H18).
          destruct H12. subst.
          destruct (A_VPG_Match _ _ _ _ _ H10).

          apply H20. eauto.

          assert (v :: x9 != []) as notnil.
          eauto using nil_cons.
    
          destruct (exists_last notnil).
          destruct s.
          rewrite e in *.

          destruct (VHasEnd _ _ _ H5).

          assert (x19=x5).

          apply (HC x19 x5);
          eauto using app_cons_not_nil, nil_cons.
          apply BeginA2. repeat eexists.

          subst.
          destruct (H19 x5).
          1:{
            inversion H12;
            repeat (breakEx); subst;
            repeat rewrite -> app_assoc in H13;
            destruct (app_inj_tail _ _ _ _ H13);
            subst;
            (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
            exists x17; repeat eexists; fail.
          }
          destruct (A_VPG_Match _ _ _ _ _ H10).
          apply H21.

          eauto.

        }

        intros.
        repeat rewrite <- app_assoc.

        apply (H6 x5 Lv).
        do 2 rewrite <- app_assoc in H7.

        pose (VListBeginSame _ _ _ H7).
        rewrite <- app_assoc in v.
        apply v.
        eauto using app_cons_not_nil.

        (* consider x9 *)
        pose (VConnect _ _ _ HvTw
        (x2 ++ [Calv (MatCalE x13 x12 x14 x15 x16)] ++ x9) 
        ([Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1)) as HC.
        1:{
          destruct x9.
          assert (x14=x5).
          apply (HC x14 x5);
          eauto using app_cons_not_nil, nil_cons.
          apply EndA2. repeat eexists.
          apply BeginA2. repeat eexists.
          subst.
          
          apply EndA2. repeat eexists.


          assert (v :: x9 != []) as notnil.
          eauto using nil_cons.
    
          destruct (exists_last notnil).
          destruct s.
          rewrite e in *.

          destruct (VHasEnd _ _ _ H5).

          assert (x19=x5).

          apply (HC x19 x5);
          eauto using app_cons_not_nil, nil_cons.
          apply BeginA2. repeat eexists.

          subst.
          auto.
        }

        constructor; auto.

        pose (H2 L Lv [] []).
        do 2 rewrite app_nil_r in d.
        apply d.
        auto.


        pose (VListBeginSame _ _ _ H7).
        repeat rewrite <- app_assoc in v.
        repeat rewrite <- app_assoc.
        apply v.
        eauto using app_cons_not_nil, nil_cons.
        auto.
        pose H.

        constructor; auto.

        assert (L0 = x8).
        1:{
          inversion H12;
          repeat (breakEx); subst;
          repeat rewrite -> app_assoc in H20;
          destruct (app_inj_tail _ _ _ _ H20);
          subst;
          inversion H22.
          auto.
        }

        subst; auto.
      }

    Qed.
    (* end hide *)

    (** [SoundV]: the soundness of the forward small-step derivation
        [Df] means that [Df] indicates the big-step derivation [Dm],
        under certain conditions.  *)
    Theorem SoundV: ∀ v T w Lv L, 
      Df v T w ->
      VBeginWith v Lv ->
      VEndWith v L ->
      in_rules (L, Alt_Epsilon) P ->
      (T=[] \/ ∃ L1 b L2 T', T=(PndCalE L1 b L2)::T') ->
      Dm Lv w v.
    (* begin hide *)
    Proof.
      intros.
      pose (L4_2 v T w).
      breakOr.
      
      inversion b.
      rmDirect.
      breakAnd.
      subst.
      rmDirect.
      rmDirect.
      repeat (breakEx + breakAnd + breakOr).

      mergeBegins.
      mergeEnds.

      assert (Dm x0 [] []) as InnDm by (constructor; auto).

      pose (H3 [] [] InnDm). 
      repeat rewrite app_nil_r in d.
      apply d.


      inversion b.
      rmDirect.
      breakAnd.
      repeat (breakEx + breakAnd + breakOr).
      subst.
      rmDirect.
      repeat (breakEx + breakAnd + breakOr).
      simplList.
      subst.

      destruct (H3 L Lv [] []); auto.
      constructor; auto.
      repeat rewrite app_nil_r in H6. auto.

      discriminate.
    Qed.
    (* end hide *)

    (** [VConnectTrue]: this lemma shows that if a parse tree starts
      with a nonterminal in V0, then the same parse tree also ends with
      a nonterminal in V0. *)
    Lemma VConnectTrue: ∀ v T w , Df v T w ->
      ∀ L, VBeginWith v (V0 L) ->
      (∀ v1 v2, 
        v=v1++v2 -> 
        v1 != [] -> 
        ∃ Lv1, VEndWith v1 (V0 Lv1)).
    (* begin hide *)
    Proof.
      intros v T w H.
      induction H; intros Lv HBegin v1 v2 Hsplit Hv1Emp.

      all: destruct v1; try contradiction.
      all: try mergeBegin.

      1:{
        inversion Hsplit.
        symmetry in H2.
        destruct (app_eq_nil _ _ H2) as [v1Emp v2Emp].
        subst.

        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).

        exists x.
        subst.
        apply EndC. exists [], x0, (V0 Lv). 
        auto.
      }

      1:{
        extractHead.

        destruct v2.

        (* v2 = [] *)
        pose (IHDf Lv HvHead v []).
        destruct e. eauto using app_nil_r. apply (L_Dv_v _ _ _ H1).
        mergeEnds.

        rewrite app_nil_r in Hsplit.

        match goal with 
        | 
          (* IHDv: ∀ _, _, *)
          Hsplit: ?v ++ [?ve] = ?t::?v2,
          Hv2Emp: ?t::?v2 != [] |- _ => 
          (* auto *)
          destruct (LSameEnd _ _ [] _ _ Hsplit) as [v2pre Hv2Split]
          ; rewrite Hv2Split in Hsplit
        end.
        rewrite Hv2Split.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).

        exists x0.
        subst.
        apply EndC. exists v2pre. repeat eexists.

        (* v2 != [] *)
        assert (v2::v3 != []) by eauto using nil_cons.
        match goal with 
        | 
          (* IHDv: ∀ _, _, *)
          Hsplit: ?v ++ [?ve] = ?v1 ++ ?t::?v2,
          Hv2Emp: ?t::?v2 != [] |- _ => 
          destruct (LSameEnd _ _ _ _ _ Hsplit) as [v2pre Hv2Split]
          (* ; auto *)
          ; rewrite Hv2Split in Hsplit
          ; rewrite app_assoc in Hsplit
          ; assert (v=v1 ++ v2pre) as Hvsplit2
            by (apply (app_inj_tail_iff v (v1++v2pre) ve ve); auto)
        end.

        pose (IHDf Lv HvHead (v0::v1) v2pre).
        destruct e. eauto using app_nil_r. auto. 
        exists x. auto.
      }

      1:{

        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.

        (* extractHead.
        pose (IHDv Lv HvHead v []).
        destruct e. eauto using app_nil_r. apply (L_Dv_v _ _ _ H1).
        mergeEnds. 
        inversion H4. *)
      }
      
      1:{
        extractHead.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).

        destruct (IHDf Lv HvHead v []); eauto using app_nil_r.
        apply (L_Dv_v _ _ _ H1).
        mergeEnds.
        eauto.
        repeat (breakEx + breakAnd).

        discriminate.
      }

      1:{
        inversion Hsplit.
        subst.

        symmetry in H2.
        pose (app_eq_nil _ _  H2).
        repeat (breakEx + breakAnd).
        subst.

        destruct (A_VPG_Match _ _ _ _ _ H).
        repeat (breakEx + breakAnd).
        subst.

        exists x.

        (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
        exists []; repeat eexists; fail.
      }

      1:{
        destruct (A_VPG_Match _ _ _ _ _ H).
        repeat (breakEx + breakAnd).
        subst.

        destruct v2.
        rewrite app_nil_r in Hsplit.
        rewrite <- Hsplit in *.

        exists x.

        (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
        exists v; repeat eexists; fail.


        assert (v2 :: v3 != []) as notnil.
        eauto using nil_cons.

        destruct (exists_last notnil).
        destruct s.
        rewrite e in *.

        rewrite app_assoc in Hsplit.
        destruct (app_inj_tail _ _ _ _ Hsplit).

        extractHead.

        apply (IHDf Lv HvHead (v0 :: v1) x0); auto.
      }

      1:{
        extractBegin.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        extractHead.
        pose (IHDf Lv HvHead v []).
        destruct e. eauto using app_nil_r. apply (L_Dv_v _ _ _ H1).
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate. 
      }

      1:{
        extractHead.
        pose (IHDf Lv HvHead v []).
        destruct e. eauto using app_nil_r. apply (L_Dv_v _ _ _ H1).
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate. 
      }

      1:{

        extractHead.

        (* assert (in_rules (L1, Alt_Match (a) (b)  L2 L3) P). *)
        pose (L4_2 v (MatCalE L1 a L2 b L3 :: T) w).
        inversion b0.
        rmDirect.
        breakAnd.
        rmDirect.
        repeat (breakEx + breakAnd + breakOr).
        discriminate.
        simplList. subst. auto. 

        destruct (A_VPG_Match _ _ _ _ _ H14).
        clear H3.
        repeat (breakEx + breakAnd).
        subst.

        destruct v2.
        rewrite app_nil_r in Hsplit.
        rewrite <- Hsplit in *.

        destruct x0.

        assert (x5=V0 Lv).
        1:{
          inversion HvHead;
          repeat breakEx;
          inversion H3; auto.
        }
        subst.

        destruct H4; eauto. subst.

        exists x0.

        (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
        exists (([] ++ [Calv (MatCalE (V0 Lv) x4 x6 x7 (vpg.V0 x0))] ++ x1)); 
        repeat eexists; fail.

        destruct (IHDf Lv HvHead (v :: x0) ([Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1))
        ; eauto using nil_cons.

        assert (V0 x9=x5).
        1:{
          apply (VConnect _ _ _ H1 (v :: x0) ([Calv (MatCalE x5 x4 x6 x7 x8)] ++ x1)
            (V0 x9) x5)
          ; eauto using nil_cons.

          apply BeginA2.
          repeat eexists.
        }
        subst.

        destruct H4; eauto. subst.
        
        exists x5.

        (apply EndC+ apply EndA1 + apply EndA2 + apply EndB1 + apply EndB2);
        exists ((v :: x0) ++ [Calv (MatCalE (V0 x9) x4 x6 x7 (vpg.V0 x5))] ++ x1); 
        repeat eexists; fail.

        assert (v :: v2 != []) as notnil.
        eauto using nil_cons.

        destruct (exists_last notnil).
        destruct s.
        rewrite e in *.

        repeat rewrite app_assoc in Hsplit.
        destruct (app_inj_tail _ _ _ _ Hsplit).

        rewrite <- app_assoc in H3.
        rewrite H3 in *.

        destruct (IHDf Lv HvHead (v0 :: v1) x9)
        ; eauto using nil_cons.
      }

    Qed.
    (* end hide *)

    (** [L4_4]: Lemma 4.4 shows that we can concatenate two parse trees,
      if the first one has a stack containing only one matching rule,
      and the two trees share the same nonterminal at their ends. *)
    Lemma L4_4: ∀ a L v T w L1 L2 b,
      (Df [Calv (MatCalE L a L1 b L2)] 
        [(MatCalE L a L1 b L2)] 
        [Call a]) ->
      (Df v T w) ->
      (VBeginWith v L1) ->
      Df (Calv (MatCalE L a L1 b L2)::v) 
        (T++[(MatCalE L a L1 b L2)]) 
        (Call a::w).
    (* begin hide *)
    Proof.
      intros a L v T w L1 L2 b Ha Hv HCnc.
      assert (in_rules (L, Alt_Match (a) (b)  L1 L2) P) as Hmat.

      1:{
        inversion Ha;
        try (pose (app_inj_tail _ [] _ _ H);
          breakAnd;
          discriminate
          );
        auto.
      }



      destruct (A_VPG_Match _ _ _ _ _ Hmat).
      breakEx.
      rename H into HL1.

      induction Hv.


      (* match goal with 
      | h: VBeginWith (?v++?_v) ?L,
        Hv: Df ?v _ _
      |- _ =>
        pose (VListBeginSame _ _v _ h (L_Dv_v _ _ _ Hv)) as HvHead
      end. *)

      all: try extractHead.
      all: try match goal with 
      | h: ?H1 -> ?H,
        hh:?H1
      |- _ => 
        pose (h hh) as Ind
      end.
      all: try mergeBegin.

      1:{
        refine (V_Pln _ _ _ _ _ _ H _ Ha).
        apply EndA2.
        exists []. repeat eexists.
      }

      1:{
        (* split; intro HT; try contradiction. *)

        (* destruct Ind as [HInd _]. *)
        (* pose (HInd HT) as Ind. *)
        refine (V_Pln _ _ _ _ _ _ H _ Ind).
        extendEnd. eauto.
      }

      1:{
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }


      1:{
        subst.
        destruct (VConnectTrue _ _ _ Hv _ HvHead v []); eauto using app_nil_r, L_Dv_v.
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        refine (V_Cal _ _ _ _ _ _ _ _ H _ Ha).
        apply EndA2. exists []; repeat eexists.
      }

      1:{
        refine (V_Cal _ _ _ _ _ _ _ _ H _ Ind).
        apply (VListEndSame2 _ [Calv (MatCalE L a L1 b L2)] _ H1).
      }

      1:{
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        subst.
        destruct (VConnectTrue _ _ _ Hv _ HvHead v []); eauto using app_nil_r, L_Dv_v.
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        subst.
        destruct (VConnectTrue _ _ _ Hv _ HvHead v []); eauto using app_nil_r, L_Dv_v.
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        pose V_Ret.
        refine (V_Ret _ _ _ _ _ _ _ _ _ _ H1 Ind).
        apply (VListEndSame2 _ [Calv (MatCalE L a L1 b L2)] _ H).
      }
    Qed.
    (* end hide *)

    (** [L4_5]: Lemma 4.5 shows that we can concatenate two parse trees,
        if the first one has a stack with a matching rule as its top,
        and the two trees share the same nonterminal at their ends. *)
    Lemma L4_5: ∀ a L v T w L1 L2 b v0 T0 w0,
      (Df (v0++[Calv (MatCalE L a L1 b L2)]) 
        (MatCalE L a L1 b L2::T0) (w0++[Call a])) 
        -> (Df v T w) 
        -> (VBeginWith v L1) 
        -> Df (v0++Calv (MatCalE L a L1 b L2)::v) 
            (T++[(MatCalE L a L1 b L2)]++T0) 
            (w0++Call a::w).
    (* begin hide *)
    Proof.
      intros a L v T w L1 L2 b v0 T0 w0 Ha Hv HCnc.
      assert (in_rules (L, Alt_Match (a) (b)  L1 L2) P) as Hmat.

      1:{
        inversion Ha;
        try (pose (app_inj_tail _ [] _ _ H);
          breakAnd;
          discriminate
          );
        auto;
        tac_inj.
      }

      destruct (A_VPG_Match _ _ _ _ _ Hmat).
      breakEx.
      rename H into HL1.

      induction Hv.


      (* match goal with 
      | h: VBeginWith (?v++?_v) ?L,
        Hv: Df ?v _ _
      |- _ =>
        pose (VListBeginSame _ _v _ h (L_Dv_v _ _ _ Hv)) as HvHead
      end. *)

      all: try extractHead.
      all: try match goal with 
      | h: ?H1 -> ?H,
        hh:?H1
      |- _ => 
        pose (h hh) as Ind
      end.
      all: try mergeBegin.

      1:{
        simpl.
        pose V_Pln.
        specialize d with (1:=H) (3:=Ha).

        simpl.
        repeat rewrite <- app_assoc in d.
        apply d.
        apply EndA2.
        exists v0. repeat eexists.
      }



      1:{
        (* split; intro HT; try contradiction. *)

        (* destruct Ind as [HInd _]. *)
        (* pose (HInd HT) as Ind. *)
        pose V_Pln.
        specialize d with (1:=H) (3:=Ind).

        repeat rewrite <- app_assoc in d.
        apply d.
        inversion H1; repeat (breakEx + breakAnd); subst;
        rewrite app_comm_cons;
        rewrite app_assoc;
        tryResolveEnd.
      }

      1:{
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }


      1:{
        subst.
        destruct (VConnectTrue _ _ _ Hv _ HvHead v []); eauto using app_nil_r, L_Dv_v.
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        pose V_Cal.
        specialize d with (1:=H) (3:=Ha).
        repeat rewrite <- app_assoc in d.
        apply d.
        tryResolveEnd.
      }

      1:{
        pose V_Cal.
        specialize d with (1:=H) (3:=Ind).
        repeat rewrite <- app_assoc in d.
        apply d.
        inversion H1; repeat (breakEx + breakAnd); subst;
        rewrite app_comm_cons;
        rewrite app_assoc;
        tryResolveEnd.
      }

      1:{
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        subst.
        destruct (VConnectTrue _ _ _ Hv _ HvHead v []); eauto using app_nil_r, L_Dv_v.
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        subst.
        destruct (VConnectTrue _ _ _ Hv _ HvHead v []); eauto using app_nil_r, L_Dv_v.
        mergeEnds.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
      }

      1:{
        pose V_Ret.
        specialize d with (2:=H1) (3:=Ind).
        repeat rewrite <- app_assoc in d.
        apply d.
        inversion H; repeat (breakEx + breakAnd); subst;
        rewrite app_comm_cons;
        rewrite app_assoc;
        tryResolveEnd.
      }
    Qed.

    Lemma L5_1: ∀ Lu w v, Dm Lu w v -> 
      w != [] ->
      VBeginWith v Lu.
    Proof.
      intros Lu w v Hm.
      induction Hm; intro Hw.
      contradiction.

      apply BeginA1. exists pt', (a), (L1); auto.
      apply BeginC. exists pt', (c), (L1); auto.
      apply BeginB. exists pt', (b), (L1); auto.
      apply BeginA2.
      repeat eexists.
    Qed.

    Lemma L5_2: ∀ Lu w v, Dm Lu w v -> 
      w != [] ->
      ∃ L, VEndWith v L /\ in_rules (L, Alt_Epsilon) P.
    Proof.
      intros Lu w v Hm.
      induction Hm; intros Hw.
      contradiction.

      1:{
        destruct w'.

        inversion Hm; subst.
        exists L1.
        split; auto.
        apply EndA1. exists [], (a), (L); auto.

        rmIndtT.
        destruct Ind as [L0 [Ind1 Ind2]].
        exists L0.
        split; auto.
        match goal with 
        | H: VEndWith ?v ?Lu 
        |- 
        VEndWith (?ea::?v) _ 
        => 
          pose (VListEndSame2 _ [ea] _ H) as HEnd
        end.
        auto.
      }

      1:{
        destruct w'.

        inversion Hm; subst.
        exists L1.
        split; auto.
        apply EndC. exists [], c, L; auto.

        rmIndtT.
        destruct Ind as [L0 [Ind1 Ind2]].
        exists L0.
        split; auto.
        match goal with 
        | H: VEndWith ?v ?Lu 
        |- 
        VEndWith (?ea::?v) _ 
        => 
          pose (VListEndSame2 _ [ea] _ H) as HEnd
        end.
        auto.
      }

      1:{
        destruct w'.

        inversion Hm; subst.
        exists L1.
        split; auto.
        apply EndB1. exists [], (b), (L); auto.

        rmIndtT.
        destruct Ind as [L0 [Ind1 Ind2]].
        exists L0.
        split; auto.
        match goal with 
        | H: VEndWith ?v ?Lu 
        |- 
        VEndWith (?ea::?v) _ 
        => 
          pose (VListEndSame2 _ [ea] _ H) as HEnd
        end.
        auto.
      }

      1:{
        destruct w2.

        inversion Hm2; subst.
        exists L2.
        split; auto.
        rewrite app_nil_r.
        apply EndB2. exists ([Calv (MatCalE L a L1 b L2)] ++ pt1).
        repeat eexists.

        rmIndtT.
        destruct Ind as [L0 [Ind1 Ind2]].
        exists L0.
        split; auto.
        match goal with 
        | H: VEndWith ?v ?Lu 
        |- 
        VEndWith (?ea++?ea2++?ea3++?v) _ 
        => 
          pose (VListEndSame2 _ (ea++ea2++ea3) _ H) as HEnd
        end.
        repeat rewrite <- app_assoc in HEnd.
        apply HEnd.
      }
      
    Qed.
    (* end hide *)
    
    (** [CompleteM]: the completeness of the forward small-step
        derivation [Df] means that each big-step derivation [Dm] is a
        [Df], as long as the string is not empty. *)
    Theorem CompleteM: ∀ Lu w v, 
      Dm (Lu) w v ->
      w != [] ->
      (∃ T, Df v T w /\ (∀ L, Lu=V0 L -> T=[]) /\ 
        (T=[] \/ exists L1 a L2 T', T=(PndCalE L1 a L2)::T')).
    (* begin hide *)
    Proof.
      intros Lu w v Hm Hw.

      induction Hm.
      contradiction.

      1:{
        destruct w'.
        inversion Hm. subst.
        pose (V_S_Pnd_Cal _ _ _ H).
        exists [PndCalE L a L1].

        split; auto.
        split; auto.
        intros.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
        right. eauto.


        destruct IHHm. eauto using nil_cons.
        rename x into T.
        pose (V_S_Pnd_Cal _ _ _ H) as Hea.
        breakAnd.

        pose (L4_3 _ _ _ _ _ _ Hea H1) as Hi.
        destruct Hi.

        apply (L5_1 _ _ _ Hm). eauto using nil_cons.
        exists T.
        split; auto.
        split; auto.
        intros.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
        1:{
          breakAll.
          left; eauto.
          right; eauto.
        }

        exists (T++[PndCalE L a L1]). 
        split; auto.
        split; auto.
        intros.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
        right.
        breakAll; subst.
        simpl.
        eauto.
        simpl.      
        eauto.
      }

      1:{
        destruct w'.
        inversion Hm. subst.
        exists [].
        split; auto.
        constructor; auto.


        destruct IHHm. eauto using nil_cons.
        exists x. 

        pose (L5_1 _ _ _ Hm).
        assert ( VBeginWith pt' (L1)). apply v. eauto using nil_cons.

        pose (V_S_Pln _ _ _ H) as Ei.
        pose (L4_1).
        split; auto.
        breakAnd.
        apply (L4_1 _ _ _ _ _ Ei H2).
        exists (L1).
        split. 
        apply EndC. exists [], (c), L. auto. auto.

        split; auto.
        intros.
        breakAnd.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        apply (H6 x0). auto.

        breakAll.
        left; auto.
        right; eauto.
      }

      1:{
        destruct w'.
        inversion Hm. subst.
        exists [].
        split; auto.
        constructor; auto.


        destruct IHHm. eauto using nil_cons.

        pose (L5_1 _ _ _ Hm).
        assert ( VBeginWith pt' (L1)). apply v. eauto using nil_cons.

        pose (V_S_Pen_Ret _ _ _ H) as Ei.
        breakAnd.
        pose (L4_1 _ _ _ _ _ Ei H2).
        exists x.
        split; auto.
        apply d.
        exists (L1).
        split. 
        apply EndB1. exists [], (b), L; auto. auto.

        split; auto.
        intros.
        destruct (A_VPG_Linear _ _ _ H); eauto.
        repeat (breakEx + breakAnd).
        discriminate.
        breakAll.
        left; auto.
        right; eauto.
      }

      1:{
        pose (V_S_Cal _ _ _ _ _ H) as Eea.
        destruct w1.
        1:{
          inversion Hm1.
          subst.
          assert (Df ([Calv (MatCalE L a (L1) b L2)] ++ 
            [Retv (MatRetE L a (L1) (b) (L2))]) []
          ([Call a] ++ [Ret b])) as Hab.
          1:{
            pose V_Ret.
            apply (d L1 a); auto.
            apply EndA2.
            exists []; eauto.
            repeat eexists.
          }

          destruct w2.
          1:{
            inversion Hm2; subst.
            
            exists []; auto.
          }

          rmDirect.
          repeat (breakEx + breakAnd).

          exists x.
          split; auto.

          apply (L4_1 _ _ _ _ _ Hab H2).
          exists (L2). 
          split; auto.
          apply EndB2. 
          exists [Calv (MatCalE L a L1 b L2)].
          eauto. auto.

          apply (L5_1 _ _ _ Hm2). 
          eauto using nil_cons.

          split; auto.
          intros.
          destruct (A_VPG_Match _ _ _ _ _ H).
          
          repeat (breakEx + breakAnd).
          destruct H6. eauto.
          apply (H3 x1). auto.
        }

        (* assert (Df pt1 [] (s :: w1)). *)
        rmDirect.
        repeat (breakEx + breakAnd).
        assert (x = []).
        1:{
          destruct (A_VPG_Match _ _ _ _ _ H).
          
          repeat (breakEx + breakAnd).
          apply (H2 x0). auto.
        }
        subst.
        
        assert (VBeginWith pt1 (L1)).
        apply (L5_1 _ _ _ Hm1).
        eauto using nil_cons.
        
        (* pose (L4_4 _ _ _ _ _ _ Eea H0 H1). *)


        assert (Df ([Calv (MatCalE L a L1 b L2)] ++
          pt1 ++ [Retv (MatRetE L a L1 b L2)] ) []
          (Call a :: s :: w1 ++ [Ret b])) as Hab.
        1:{
          (* pose (VConnectTrue _ _ _ H0 L1 H1 pt1 [] ). *)

          (* assert (exists Lv1 : vpg_var, VEndWith pt1 (Lv1)) as HPt1True.
          apply e;
          eauto using app_nil_r, L_Dv_v.
          inversion HPt1True. *)

          (* extendEnd. *)
          destruct (L5_2 _ _ _ Hm1).
          eauto using nil_cons.
          breakAnd.

          rewrite app_assoc.
          apply (V_Ret x a b L L1 L2 ([Calv (MatCalE L a L1 b L2)] ++ pt1)
          (Call a :: s :: w1) []).

          apply (VListEndSame2 _ _ _ H5).
          auto.

          pose (L4_4).

          apply (L4_4 _ _ pt1 [] (s :: w1) _ _ _ Eea);
          auto.
        }

        destruct w2.

        inversion Hm2. subst.
        exists [].
        split; auto.

        rmDirect.
        repeat (breakEx + breakAnd).
        
        
        pose (L4_1).
        exists x.
        split; auto.
        pose (L4_1 _ _ _ _ _ Hab H5).
        simpl.
        simpl in d0.
        simpl.
        do 2 rewrite <- app_assoc in d0.
        apply d0.

        exists L2.
        split; eauto.

        apply EndB2. exists (Calv (MatCalE L a L1 b L2) :: pt1).
        repeat eexists.

        inversion Hm2;
        (apply BeginC+ apply BeginA1 + apply BeginA2 + apply BeginB);
        try (exists pt'); repeat eexists; fail.

        split; eauto.
        intros.
        destruct (A_VPG_Match _ _ _ _ _ H).
        repeat (breakEx + breakAnd).
        destruct H9; eauto.
      }
    Qed.
    (* end hide *)

  End Core.


  (** The module [DFX] verifies properties of the extended forward
    small-step derivation [Dfx]. *)
  Module DFX.
    Import LEN_WF.
    Import DEF.
    Import Df2.
    Import DM.
    Import Tac.


    (* begin hide *)
    Ltac cmp_len :=
      match goal with
      | |- len ?v (?v ++ [?e]) =>
        unfold len
        ; rewrite (last_length v e)
        ; eauto
      end.

    Ltac simplSym :=
      match goal with
      | h: Plain _ = Plain _ |- _ =>
        inversion h
        ; subst
      | h: Ret _ = Ret _ |- _ =>
        inversion h
        ; subst
      | h: Call _ = Call _ |- _ =>
        inversion h
        ; subst
      end.  
    (* end hide *)

    (** [DFX_df]: this lemma shows [Dfx] indicates [Df]. *)
    Lemma DFX_df: ∀ v, ∀ T w v1 v2 w1 w2, 
      Dfx v T w v1 v2 w1 w2 ->
      Df v T w.
    (* begin hide *)
    Proof.
      intro v.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      inversion H0; simpl; eauto; subst.
      all: try (constructor; eauto; fail).
      
      pose (H v0).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H4 _ _ _ _ _ _ H3).
      constructor; eauto.


      pose (H v1).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H4 _ _ _ _ _ _ H3).
      constructor; eauto.


      pose (H v1).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H4 _ _ _ _ _ _ H3).
      constructor; eauto.


      pose (H v0).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H4 _ _ _ _ _ _ H3).
      constructor; eauto.


      pose (H v0).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H4 _ _ _ _ _ _ H3).
      apply V_Pnd_Ret with (t:=t); eauto.

      pose (H v0).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H5 _ _ _ _ _ _ H3).
      apply V_Pnd_Ret with (t:=t); eauto.


      pose (H v0).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H4 _ _ _ _ _ _ H3).
      apply V_Ret with (L:=L); eauto.

      pose (H v0).
      breakInfer.
      tac_app.
      cmp_len.
      pose (H5 _ _ _ _ _ _ H3).
      apply V_Ret with (L:=L); eauto.
    Qed.

    Lemma DFX_ww: ∀ v, ∀ T w v1 v2 w1 w2, 
      Dfx v T w v1 v2 w1 w2 ->
      (length w1) <= (length w).
    Proof.
      intros.
      induction H; simpl; eauto.

      all: try match goal with
      | |- length (?w1) <= length (?w++[?i]) =>
        rewrite (app_length w [i])
        ; apply Nat.le_trans with (m:=length w)
        ; lia
      end.

      all: lia.
    Qed.

    Lemma DFX_v: ∀ v, ∀ T w v1 v2 w1 w2, 
      Dfx v T w v1 v2 w1 w2 ->
      (T=[] /\ v=v2) \/ (∃t T', T=t::T' /\ v = v1++[Calv t]++v2).
    Proof.
      intro v.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      inversion H0; simpl; eauto; subst.

      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H4 _ _ _ _ _ _ H3).
        breakAll; subst.
        left.
        split; eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        eauto.
        }

      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H5 _ _ _ _ _ _ H3).

        pose (H v3).
        breakInfer.
        tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
          h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
          unfold len
          ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
          ; pose (L_Df_vw _ _ _ _h) as _h2
          ; rewrite _h2
          ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
          ; rewrite (app_length v1 [e])
          ; rewrite (L_Df_vw _ _ _ _h')
          ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.
          
          destruct (Nat.lt_succ_r (length w3) (length w0)) as [_ h].
          rmDirect.
          
          simpl in *.
          lia.
        }

        pose (H6 _ _ _ _ _ _ H4).

        breakAll; subst; try discriminate.
        left.
        split; eauto.
        simplList; subst.
        simpl.
        repeat rewrite <- app_assoc.
        eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        simplList.
        eauto.
      }

      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H5 _ _ _ _ _ _ H3).

        pose (H v3).
        breakInfer.
        tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
          h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
          unfold len
          ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
          ; pose (L_Df_vw _ _ _ _h) as _h2
          ; rewrite _h2
          ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
          ; rewrite (app_length v1 [e])
          ; rewrite (L_Df_vw _ _ _ _h')
          ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.
          
          destruct (Nat.lt_succ_r (length w3) (length w0)) as [_ h].
          rmDirect.
          
          simpl in *.
          lia.
        }

        pose (H6 _ _ _ _ _ _ H4).

        breakAll; subst; try discriminate.
        left.
        split; eauto.
        simplList; subst.
        simpl.
        repeat rewrite <- app_assoc.
        eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        simplList.
        eauto.
      }
    Qed.

    Lemma DFX_w: ∀ v, ∀ T w v1 v2 w1 w2, 
      Dfx v T w v1 v2 w1 w2 ->
      (T=[] /\ w=w2) \/ (∃t T', T=t::T' /\ w = w1++[getSym t]++w2).
    Proof.
      intro v.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      inversion H0; simpl; eauto; subst.

      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H4 _ _ _ _ _ _ H3).
        breakAll; subst.
        left.
        split; eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        eauto.
        }



      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H5 _ _ _ _ _ _ H3).

        pose (H v3).
        breakInfer.
        tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
          h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
          unfold len
          ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
          ; pose (L_Df_vw _ _ _ _h) as _h2
          ; rewrite _h2
          ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
          ; rewrite (app_length v1 [e])
          ; rewrite (L_Df_vw _ _ _ _h')
          ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.
          
          destruct (Nat.lt_succ_r (length w3) (length w0)) as [_ h].
          rmDirect.
          
          simpl in *.
          lia.
        }

        pose (H6 _ _ _ _ _ _ H4).

        breakAll; subst; try discriminate.
        left.
        split; eauto.
        simplList; subst.
        simpl.
        repeat rewrite <- app_assoc.
        eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        simplList.
        eauto.
      }

      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H5 _ _ _ _ _ _ H3).

        pose (H v3).
        breakInfer.
        tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
          h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
          unfold len
          ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
          ; pose (L_Df_vw _ _ _ _h) as _h2
          ; rewrite _h2
          ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
          ; rewrite (app_length v1 [e])
          ; rewrite (L_Df_vw _ _ _ _h')
          ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.
          
          destruct (Nat.lt_succ_r (length w3) (length w0)) as [_ h].
          rmDirect.
          
          simpl in *.
          lia.
        }

        pose (H6 _ _ _ _ _ _ H4).

        breakAll; subst; try discriminate.
        left.
        split; eauto.
        simplList; subst.
        simpl.
        repeat rewrite <- app_assoc.
        eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        simplList.
        eauto.
      }

    Qed.

    Lemma DFX_w2: ∀ v, ∀ T w v1 v2 w1 w2, 
      Dfx v T w v1 v2 w1 w2 ->
      (T=[] /\ w=w2 /\ w1=[]) 
      \/ 
      (∃t T', T=t::T' /\ w = w1++[getSym t]++w2).
    Proof.
      intro v.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      inversion H0; simpl; eauto; subst.

      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H4 _ _ _ _ _ _ H3).
        breakAll; subst.
        left.
        split; eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        eauto.
        }



      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H5 _ _ _ _ _ _ H3).

        pose (H v3).
        breakInfer.
        tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
          h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
          unfold len
          ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
          ; pose (L_Df_vw _ _ _ _h) as _h2
          ; rewrite _h2
          ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
          ; rewrite (app_length v1 [e])
          ; rewrite (L_Df_vw _ _ _ _h')
          ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.
          
          destruct (Nat.lt_succ_r (length w3) (length w0)) as [_ h].
          rmDirect.
          
          simpl in *.
          lia.
        }

        pose (H6 _ _ _ _ _ _ H4).

        breakAll; subst; try discriminate.
        left.
        split; eauto.
        simplList; subst.
        simpl.
        repeat rewrite <- app_assoc.
        eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        simplList.
        eauto.
      }

      1:{
        pose (H v0).
        breakInfer.
        tac_app.
        cmp_len.
        pose (H5 _ _ _ _ _ _ H3).

        pose (H v3).
        breakInfer.
        tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
          h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
          unfold len
          ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
          ; pose (L_Df_vw _ _ _ _h) as _h2
          ; rewrite _h2
          ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
          ; rewrite (app_length v1 [e])
          ; rewrite (L_Df_vw _ _ _ _h')
          ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.
          
          destruct (Nat.lt_succ_r (length w3) (length w0)) as [_ h].
          rmDirect.
          
          simpl in *.
          lia.
        }

        pose (H6 _ _ _ _ _ _ H4).

        breakAll; subst; try discriminate.
        left.
        split; eauto.
        simplList; subst.
        simpl.
        repeat rewrite <- app_assoc.
        eauto.
        right.
        do 2 eexists.
        split; eauto.
        repeat rewrite <- app_assoc.
        simplList.
        eauto.
      }

    Qed.

    Ltac eq_len :=
      match goal with
      | h1: Dfx ?v _ _ _ _ _ _,
        h2: Dfx ?v1 _ _ _ _ _ _ |- 
        length ?v = length ?v1 =>
        pose (DFX_df _ _ _ _ _ _ _ h1) as _h1
        ; pose (DFX_df _ _ _ _ _ _ _ h2) as _h2
        ; apply (L_Df_uniqueV _ _ _ _ _ _h1 _h2)
      end.


    Lemma DFX_len_vw: ∀ v, ∀ T w v1 v2 w1 w2, 
      Dfx v T w v1 v2 w1 w2 ->
      (length v1=length w1 /\ length v2=length w2).
    Proof.
      intro.
      induction v using (well_founded_ind (len_wf _)).
      intros.

      inversion H0; subst.

      all: split; auto.

      all: try ((pose (H v0)+pose (H v1)); breakInfer; try (tac_app; cmp_len)
      ; match goal with
        | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
          h2: Dfx _ _ _ _ _ _ _ |- _ =>
          destruct (h _ _ _ _ _ _ h2)
          ; auto
        end).

      Ltac breakLenPlus :=
        match goal with
        | |- length (?w1 ++ ?i1) = length (?w++?i) =>
          rewrite (app_length w i)
          ; rewrite (app_length w1 i1)
          ; subst
          ; auto
        | |- _ + length (?w1 ++ ?i1) = _ + length (?w++?i) =>
          rewrite (app_length w i)
          ; rewrite (app_length w1 i1)
          ; subst
          ; auto
        | |- _ + length (?w1 ++ ?i1) + _ = _ + length (?w++?i) + _=>
          rewrite (app_length w i)
          ; rewrite (app_length w1 i1)
          ; subst
          ; auto
        | |- _ + (_ + length (?w1 ++ ?i1)) = _ + (_ + length (?w++?i)) =>
          rewrite (app_length w i)
          ; rewrite (app_length w1 i1)
          ; subst
          ; auto
        end.


      all: try breakLenPlus.

      (* all: try do 2 rewrite app_assoc. *)

      all: try (
      match goal with
      | h: Dfx _ _ _ _ _ _ _ |- _ =>
        pose (DFX_v _ _ _ _ _ _ _ h)
        ; pose (DFX_w _ _ _ _ _ _ _ h)
        ; breakAll
        ; subst
        ; eauto
        ; try discriminate
        ; repeat breakLenPlus
      end; fail).

      1:{
        pose (DFX_df _ _ _ _ _ _ _ H3).
        rewrite (L_Df_vw _ _ _ d).
        simpl;
        lia.
      }


      1:{
        pose (H v3).

        breakInfer; try tac_app.
        1:{
          pose (DFX_ww _ _ _ _ _ _ _ H3).
          pose (DFX_df _ _ _ _ _ _ _ H3).
          pose (L_Df_vw _ _ _ d).

          unfold len.
          match goal with
          | |- length _ < length (?w ++ ?w') =>
            rewrite (app_length w w')
          end.
          rewrite e.
          simpl.
          lia.
        }

        destruct (H8 _ _ _ _ _ _ H4); auto.
      }
      
      1:{
        pose (H v3).

        breakInfer; try tac_app.
        1:{
          pose (DFX_ww _ _ _ _ _ _ _ H3).
          pose (DFX_df _ _ _ _ _ _ _ H3).
          pose (L_Df_vw _ _ _ d).

          unfold len.
          match goal with
          | |- length _ < length (?w ++ ?w') =>
            rewrite (app_length w w')
          end.
          rewrite e.
          simpl.
          lia.
        }

        destruct (H8 _ _ _ _ _ _ H4); auto.
        match goal with
        | |- _ + length (?v ++ ?v') = _ + length (?w++?w') =>
          rewrite (app_length v v')
          ; rewrite (app_length w w')
          ; subst
          ; auto
        end.

        breakLenPlus.

      }


      1:{
        pose (DFX_df _ _ _ _ _ _ _ H3).
        rewrite (L_Df_vw _ _ _ d).
        simpl;
        lia.
      }

      1:{
        pose (H v3).

        breakInfer; try tac_app.
        1:{
          pose (DFX_ww _ _ _ _ _ _ _ H3).
          pose (DFX_df _ _ _ _ _ _ _ H3).
          pose (L_Df_vw _ _ _ d).

          unfold len.
          match goal with
          | |- length _ < length (?w ++ ?w') =>
            rewrite (app_length w w')
          end.
          rewrite e.
          simpl.
          lia.
        }

        destruct (H8 _ _ _ _ _ _ H4); auto.
      }
      
      1:{
        pose (H v3).

        breakInfer; try tac_app.
        1:{
          pose (DFX_ww _ _ _ _ _ _ _ H3).
          pose (DFX_df _ _ _ _ _ _ _ H3).
          pose (L_Df_vw _ _ _ d).

          unfold len.
          match goal with
          | |- length _ < length (?w ++ ?w') =>
            rewrite (app_length w w')
          end.
          rewrite e.
          simpl.
          lia.
        }

        destruct (H8 _ _ _ _ _ _ H4); auto.
        match goal with
        | |- _ + length (?v ++ ?v') = _ + length (?w++?w') =>
          rewrite (app_length v v')
          ; rewrite (app_length w w')
          ; subst
          ; auto
        end.

        breakLenPlus.
      }
    Qed.


    Lemma DFX_len_w: ∀ v v', length v=length v' -> 
        ∀ T w v1 v2 w1 w2, Dfx v T w v1 v2 w1 w2 -> 
        ∀ T' v1' v2' w1' w2', Dfx v' T' w v1' v2' w1' w2' -> 
        (w1=w1') /\ (w2=w2').
    Proof.
      intro.
      induction v using (well_founded_ind (len_wf _)).

      intros.

      inversion H1; inversion H2; subst; eauto.

      all: tac_inj; subst;
      try match goal with
      | h: Dfx _ _ [] _ _ _ _ |- _ =>
        inversion h
        ; tac_inj
      end.

      all: try discriminate.

      all: eauto.


      all: match goal with
      | h: forall y, len y _ -> _,
        h1: Dfx (?v++_) _ _ _ _ _ _,
        h2: Dfx (?v'++_) _ _ _ _ _ _
        |- _ =>
        pose (h v)
      end.

      all: (breakInfer; try (tac_app; cmp_len)).

      all: match goal with
      | h: forall y, _ = _ -> _,
        h1: Dfx (?v++_) _ _ _ _ _ _,
        h2: Dfx (?v'++_) _ _ _ _ _ _
        |- _ =>
        pose (h v')
      end.
      
      all: breakInfer; try (tac_app; eq_len).

      all: match goal with
      | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
        h1: Dfx ?v _ _ _ _ _ _,
        h2: Dfx ?v1 _ _ _ _ _ _ |- _ =>
        destruct (h _ _ _ _ _ _ h1 _ _ _ _ _ h2)
        ; subst
      end.

      simplSym; split; eauto.

      all: try (
        match goal with
        | h: Dfx _ [] ?w _ _ _ _,
          h2: Dfx _ (?t::_) ?w _ _ _ _
        |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h);
          pose (DFX_df _ _ _ _ _ _ _ h2)
        end;
        
        match goal with
        | h: Df ?v ?T ?w, h2: Df ?v2 ?T2 ?w |- _ =>
            pose (L_Df_uniqueT _ _ _ _ _ h h2) as _H;
            inversion _H
        end).

      pose (DFX_len_vw).

      Ltac getLength0 :=
        match goal with
        | h: length ?v = length [] |- _ =>
          destruct v; try discriminate
        end.


      all: try match goal with
      | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
        h1: Dfx _ [?t] ?w [] _ _ _,
        h2: Dfx _ _ ?w ?v1 _ _ _, 
        h3: Dfx ?v1 _ _ _ _ _ _ |- _ =>
        destruct (DFX_len_vw _ _ _ _ _ _ _ h1)
        ; destruct (DFX_len_vw _ _ _ _ _ _ _ h2)
        ; match goal with
          | h: length [] = length ?v,
            h1: length ?v1 = length ?v
          |- _ =>
            rewrite <- h in h1
            ; getLength0
          end
        ; pose (DFX_df _ _ _ _ _ _ _ h3)
        ; tac_df
      end.

      all: try (assert (getSym t=getSym t0) as Ht by 
        (match goal with
        | h: Dfx ?v (_::_) _ _ _ _ _,
          h1: Dfx ?v1 (_::_) _ _ _ _ _
        |- _ =>
          pose (DFX_w _ _ _ _ _ _ _ h) as _h
          ; pose (DFX_w _ _ _ _ _ _ _ h1) as _h'
        end;
        breakAll; subst; try discriminate; do 2 simplList; subst;
        match goal with
        | h: ?w1++[_]++?w2 = ?w1++[_]++?w2 |- _ =>
          pose (app_inv_head _ _ _ h)
          ; simplList
          ; eauto
        end)
        ; rewrite Ht).

      all: try (rewrite a).
      all: try (split; eauto; fail).


      1:{
        pose (H v3).
        breakInfer. tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
            h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
            unfold len
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
            ; pose (L_Df_vw _ _ _ _h) as _h2
            ; rewrite _h2
            ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
            ; rewrite (app_length v1 [e])
            ; rewrite (L_Df_vw _ _ _ _h')
            ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.

          destruct (Nat.lt_succ_r (length w6) (length w0)) as [_ h].
          rmDirect.

          simpl in *.
          lia.
        }
        pose (H9 v6).
        breakInfer. tac_app.
        (* 这里是因为两个Dfx都是w6 *)
        eq_len.
        pose (H10 _ _ _ _ _ _ H6 _ _ _ _ _ H17).
        breakAnd; subst.

        split; eauto.
      }

      1:{
        pose (H v3).
        breakInfer. tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
            h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
            unfold len
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
            ; pose (L_Df_vw _ _ _ _h) as _h2
            ; rewrite _h2
            ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
            ; rewrite (app_length v1 [e])
            ; rewrite (L_Df_vw _ _ _ _h')
            ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.

          destruct (Nat.lt_succ_r (length w6) (length w0)) as [_ h].
          rmDirect.

          simpl in *.
          lia.
        }
        pose (H9 v6).
        breakInfer. tac_app.
        (* 这里是因为两个Dfx都是w6 *)
        eq_len.
        pose (H10 _ _ _ _ _ _ H6 _ _ _ _ _ H17).
        breakAnd; subst.

        split; eauto.

        simplSym; subst; eauto.

        assert (getSym t=Call a) as Ht.
        1:{
          match goal with
          | h: Dfx ?v (_::_) _ _ _ _ _,
            h1: Dfx ?v1 (_::_) _ _ _ _ _
          |- _ =>
            pose (DFX_w _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_w _ _ _ _ _ _ _ h1) as _h'
          end.

          breakAll; subst; try discriminate; do 2 simplList; subst.
          match goal with
          | h: ?w1++[_]++?w2 = ?w1++[_]++?w2 |- _ =>
            pose (app_inv_head _ _ _ H11)
            ; simplList
            ; eauto
          end.
        }
        rewrite Ht.
        eauto.
      }

      1:{
        pose (H v3).
        breakInfer. tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
            h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
            unfold len
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
            ; pose (L_Df_vw _ _ _ _h) as _h2
            ; rewrite _h2
            ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
            ; rewrite (app_length v1 [e])
            ; rewrite (L_Df_vw _ _ _ _h')
            ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.

          destruct (Nat.lt_succ_r (length w6) (length w0)) as [_ h].
          rmDirect.

          simpl in *.
          lia.
        }
        pose (H9 v6).
        breakInfer. tac_app.
        (* 这里是因为两个Dfx都是w6 *)
        eq_len.
        pose (H10 _ _ _ _ _ _ H6 _ _ _ _ _ H17).
        breakAnd; subst.

        split; eauto.

        simplSym; subst; eauto.

        assert (Call a=getSym t) as Ht.
        1:{
          match goal with
          | h: Dfx ?v (_::_) _ _ _ _ _,
            h1: Dfx ?v1 (_::_) _ _ _ _ _
          |- _ =>
            pose (DFX_w _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_w _ _ _ _ _ _ _ h1) as _h'
          end.

          breakAll; subst; try discriminate; do 2 simplList; subst.
          match goal with
          | h: ?w1++[_]++?w2 = ?w1++[_]++?w2 |- _ =>
            pose (app_inv_head _ _ _ H11)
            ; simplList
            ; eauto
          end.
        }
        rewrite Ht.
        eauto.
      }

      1:{
        pose (H v3).
        breakInfer. tac_app.
        1:{
          match goal with
          | h: Dfx ?v _ _ _ _ _ _,
            h1: Dfx ?v1 _ _ _ _ _ _
          |- len ?v (?v1++[?e]) =>
            unfold len
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h
            ; pose (L_Df_vw _ _ _ _h) as _h2
            ; rewrite _h2
            ; pose (DFX_df _ _ _ _ _ _ _ h1) as _h'
            ; rewrite (app_length v1 [e])
            ; rewrite (L_Df_vw _ _ _ _h')
            ; pose (DFX_ww _ _ _ _ _ _ _ h1)
          end.

          destruct (Nat.lt_succ_r (length w6) (length w0)) as [_ h].
          rmDirect.

          simpl in *.
          lia.
        }
        pose (H9 v6).
        breakInfer. tac_app.
        (* 这里是因为两个Dfx都是w6 *)
        eq_len.
        pose (H10 _ _ _ _ _ _ H6 _ _ _ _ _ H17).
        breakAnd; subst.

        split; eauto.

        simplSym; subst; eauto.

        assert (Call a=Call a0) as Ht.
        1:{
          match goal with
          | h: Dfx ?v (_::_) _ _ _ _ _,
            h1: Dfx ?v1 (_::_) _ _ _ _ _
          |- _ =>
            pose (DFX_w _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_w _ _ _ _ _ _ _ h1) as _h'
          end.

          breakAll; subst; try discriminate; do 2 simplList; subst.
          match goal with
          | h: ?w1++[_]++?w2 = ?w1++[_]++?w2 |- _ =>
            pose (app_inv_head _ _ _ H11)
            ; simplList
            ; eauto
          end.
        }
        rewrite Ht.
        eauto.
      }

    Qed.
    

    Lemma DFX_len_v: ∀ v v', length v=length v' -> 
      ∀ T w v1 v2 w1 w2, Dfx v T w v1 v2 w1 w2 -> 
      ∀ T' v1' v2' w1' w2', Dfx v' T' w v1' v2' w1' w2' -> 
      (length v1=length v1') /\ (length v2=length v2').
    Proof.
      intros.
      match goal with
      | H: length _ = length _,
        h: Dfx _ _ _ _ _ _ _,
        h2: Dfx _ _ _ _ _ _ _
      |- _ =>
        pose (DFX_len_w _ _ H _ _ _ _ _ _ h _ _ _ _ _ h2)
      end.
      breakAnd; subst.

      destruct (DFX_len_vw _ _ _ _ _ _ _ H0).
      destruct (DFX_len_vw _ _ _ _ _ _ _ H1).

      rewrite H2.
      rewrite H3.
      split; auto.
    Qed.

    Lemma DFX_df_rule1: ∀ v, ∀ T w v1 v2 w1 w2, 
      ∀ L1 a L2,
      Dfx v (PndCalE L1 a L2::T) w v1 v2 w1 w2 ->
      in_rules (L1, Alt_Linear (Call a) L2) P.
    Proof.
      intros.
      dependent induction H; eauto.
    Qed.

    Lemma DFX_df_rule2: ∀ v, ∀ T w v1 v2 w1 w2, 
      ∀ L1 a L2 b L3,
      Dfx v (MatCalE L1 a L2 b L3 ::T) w v1 v2 w1 w2 ->
      in_rules (L1, Alt_Match a b L2 L3) P.
    Proof.
      intros.
      dependent induction H; eauto.
    Qed.

    Ltac getDf :=
      match goal with
      | h: Dfx ?v ?T ?w _ _ _ _ |- _ =>
        pose (DFX_df _ _ _ _ _ _ _ h)
      end.

    Ltac getDfx_v :=
      match goal with
      | h: Dfx ?v ?T ?w _ _ _ _ |- _ =>
        pose (DFX_v _ _ _ _ _ _ _ h)
      end.

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

    Ltac resolveBeginWith :=
      match goal with
      | h: VBeginWith ((?e::?v)++_) ?L |- _ =>
        simpl in h
        ; inversion h
        ; breakAll; subst
        ; simplList
        ; tryResolveBegin
      | h: VBeginWith ((?e::?v)) ?L |- _ =>
        simpl in h
        ; inversion h
        ; breakAll; subst
        ; simplList
        ; subst
        ; simpl
        ; tryResolveBegin
      end.
    
    Ltac getInd :=
      match goal with
      | h: forall _, len _ _ -> _, 
        h2: Dfx ?v _ _ _ _ _ _|- _ =>
        pose (h v) as _h
        ; breakInfer
        ; [tac_app; cmp_len | ]
        ; clear _h
      end.

    Ltac getLastInd :=
      getInd;
      match goal with
      | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
        H: Dfx _ _ _ _ _ _ _ |- _ =>
        destruct (h _ _ _ _ _ _ H)
        ; clear h
        ; breakAll
        ; subst
      end.


    Ltac cmp_len2 :=
      match goal with
      | h: Dfx ?v _ _ ?v1 _ _ _
      |- len ?v1 (?v ++ _) =>
        destruct (DFX_v _ _ _ _ _ _ _ h)
        ; breakAll; try discriminate
        ; subst
        ; repeat rewrite <- app_assoc
        ; unfold len
        ; match goal with
        | |- length _ < length (?e ++ ?v) =>
          rewrite app_length
        end
        (* ; rewrite (last_length v e) *)
        ; simpl; lia
      end.

    Ltac syncEmpW :=
      match goal with
      | h: Dfx _ _ _ _ [] _ ?w2 |- _ =>
        destruct (DFX_len_vw _ _ _ _ _ _ _ h) as [_ _h]
        ; inversion _h as [_h2]
        ; symmetry in _h2
        ; destruct (length_zero_iff_nil w2) as [_h3 _]
        ; rmDirect
        ; clear _h _h2
      | h: Dfx _ _ _ [] _ ?w2 _ |- _ =>
        destruct (DFX_len_vw _ _ _ _ _ _ _ h) as [_h _]
        ; inversion _h as [_h2]
        ; symmetry in _h2
        ; destruct (length_zero_iff_nil w2) as [_h3 _]
        ; rmDirect
        ; clear _h _h2
      end.


    Lemma DFX_df_sub: ∀ v, ∀ T w v1 v2 w1 w2, 
      Dfx v T w v1 v2 w1 w2 ->
      ( T=[] /\ Df v2 [] w2 ) \/
      ( ∃ t T', T=t::T' /\ (v1 != [] -> Df v1 T' w1)
                        /\ (v2 != [] -> Df v2 [] w2)
                        /\ (∀ v' T' w' Lv, Df v' T' w' -> (VBeginWith v2 Lv) ->
                            (VEndWith v' Lv) -> Df (v'++v2) T' (w'++w2)) ).
    Proof.
      intro.
      induction v using (well_founded_ind (len_wf _)).

      intros.
      inversion H0; subst.

      all: try (
        left;
        split; auto;
        constructor; auto; fail
      ).

      1:{

        getLastInd.

        left.

        split; eauto.
        constructor; eauto.
        (* 因为v0是L, 然后Df v4 *)
        Ltac solveEndWith :=
        match goal with
        | h: Dfx ?v _ _ ?v1 ?v2 _ _ |- VEndWith ?v2 ?L =>
          destruct (DFX_v _ _ _ _ _ _ _ h)
          ; breakAll
          ; subst
          ; eauto
          ; try discriminate
        end.
        solveEndWith.

        right.
        do 2 eexists.
        split; eauto.
        split; eauto.
        split; eauto.
        intros.

        destruct v4.
        
        syncEmpW; subst.
        constructor; eauto.
        rmDirect.
        constructor; eauto.
        solveEndWith.

        rewrite app_assoc in H2.


        resolveEndWith.

        intros.

        do 2 rewrite app_assoc.

        destruct v4.

        syncEmpW; subst.
        assert (L=Lv).
        1:{
          simpl in *.
          inversion H8; breakAll; simpl in *; simplList; subst; eauto.
        }
        subst.
        rewrite app_nil_r; eauto.
        constructor; eauto.
        rewrite app_nil_r; eauto.

        constructor; eauto.

        Ltac solveEndWith2 :=
          match goal with
          | h: Dfx ?v _ _ ?v1 ?v2 _ _,
            h2: VEndWith ?v ?L |- VEndWith (_++?v2) ?L =>
            destruct (DFX_v _ _ _ _ _ _ _ h)
            ; breakAll
            ; subst
            ; eauto
            ; try discriminate
            ; repeat rewrite app_assoc in h2
          end.
        solveEndWith2.

        Ltac resolveEndWith2 :=
          match goal with
          | h:VEndWith (?v++?e::?v') ?L |- VEndWith (_ ++ ?e::?v') ?L =>
            assert ((e::v') != []) as _HnotNil by eauto using nil_cons
            ; destruct (exists_last _HnotNil) as [? _s]
            ; destruct _s as [? _h]
            ; rewrite _h in *
            ; clear _h _HnotNil
            ; repeat rewrite app_assoc in h
            ; inversion h; breakAll; subst
            ; tac_inj
            ; subst
            ; repeat rewrite app_assoc
            ; tryResolveEnd
          end.
          resolveEndWith2.


        apply H5 with (Lv:=Lv); eauto.



        resolveBeginWith.
      }

      1:{
        right.
        do 2 eexists.
        split; eauto.
        split; eauto.
        intros; contradiction.
        split; eauto.
        intros; contradiction.
        intros.
        do 2 rewrite app_nil_r.
        eauto.
      }

      1:{
        (* v+PndCal *)
        right.
        do 2 eexists.
        split; eauto.

        match goal with
        | h: Dfx ?v ?T ?w _ _ _ _ |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h)
        end.

        split; eauto.
        split; intros. contradiction.
        do 2 rewrite app_nil_r.
        eauto.
      }

      1:{
        (* MatCal *)
        right.
        do 2 eexists.
        split; eauto.

        match goal with
        | h: Dfx ?v ?T ?w _ _ _ _ |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h)
        end.

        split; intros. contradiction.
        split; intros. contradiction.
        do 2 rewrite app_nil_r.
        eauto.
      }

      1:{
        (* v+PndCal *)
        right.
        do 2 eexists.
        split; eauto.

        match goal with
        | h: Dfx ?v ?T ?w _ _ _ _ |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h)
        end.

        split; eauto.
        split; intros. contradiction.
        do 2 rewrite app_nil_r.
        eauto.
      }

      1:{
        left;
        split; auto;
        constructor; auto;
        match goal with
        | h: Dfx ?v ?T ?w _ _ _ _ |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h)
        end.
        eauto.
      }

      4:{
        (* 先对sub dfx用一下IH *)
        match goal with
        | h: forall _, len _ _ -> _ |- _ =>
          pose (h v3)
        end.
        breakInfer. tac_app.


        cmp_len2.
        
        match goal with
        | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
          H: Dfx _ _ _ _ _ _ _ |- _ =>
          pose (h _ _ _ _ _ _ H)
        end.

        (* 在对前一步的v用一下IH *)
        match goal with
        | h: forall _, len _ _ -> _ |- _ =>
          pose (h v0)
        end.
        breakInfer. tac_app.
        cmp_len.
        match goal with
        | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
          H: Dfx v0 _ _ _ _ _ _ |- _ =>
          pose (h _ _ _ _ _ _ H)
        end.

        (* 先把<awb>搞出来 *)
        match goal with
        |  |- (_ /\ (Df (_++[?ea]++?v++[?eb]) [] (_++[?a]++?w++[?b]))) \/ _ =>
            assert (Df ([ea] ++ v++[eb]) [] ([a]++w++[b]))
        end.

        (* >>> *)
        1:{
          do 2 rewrite app_assoc.
          
          (* 需要知道是谁在结尾 *)
          destruct v4.
          syncEmpW; subst.
          repeat rewrite app_nil_r.

          1:{
            (* v4=[] *)
            apply V_Ret with (L:=L); auto.
            match goal with
            | h: Dfx v0 _ _ _ _ _ _ |- _ =>
              destruct (DFX_v _ _ _ _ _ _ _ h)
              ; breakAll
              ; try discriminate
              ; simpl in *
              ; simplList
              ; subst
            end;
            assert (L2=L);
            match goal with
            | h: VEndWith _ _ |- _ =>
                inversion h
                ; breakAll
                ; subst
                ; tac_inj
                ; subst
                ; match goal with
                | h: Calv _=Calv _ |- _ =>
                  inversion h
                end
                ; eauto
            end;
            subst;
            try_resolve_end.
            constructor; eauto.

            Ltac resolveRule :=
              match goal with
              | h:Dfx _ (MatCalE ?L1 ?a ?L2 ?b ?L3::_) _ _ _ _ _
              |- in_rules (?L1, Alt_Match ?a ?b ?L2 ?L3) P =>
                apply (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ h)
              | h:Dfx _ [PndCalE ?L1 ?a ?L2] _ _ _ _ _
              |- in_rules (?L1, Alt_Linear (Call ?a) ?L2) P =>
                apply (DFX_df_rule1 _ _ _ _ _ _ _ _ _ _ h)
              | h:Dfx _ (PndCalE ?L1 ?a ?L2::_) _ _ _ _ _
              |- in_rules (?L1, Alt_Linear (Call ?a) ?L2) P =>
                apply (DFX_df_rule1 _ _ _ _ _ _ _ _ _ _ h)
              end.

            resolveRule.
          }

          apply V_Ret with (L:=L); auto.
        
          solveEndWith2;
          resolveEndWith2.

          breakOr. 
          breakAll; try discriminate.
          repeat (breakEx + breakAnd).

          apply H7 with (Lv:=L2); eauto.
          constructor; eauto.
          resolveRule.

          (* 分离 VBeginWith (v :: v4) L2 *)
          1:{
            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.

            (* 这个得用分离定理 *)
            1: {
              match goal with
              | h: Dfx _ _ _ _ (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
              end.

              (* unify *)
              all: match goal with
              | h: Df _ _ _ |- _ =>
                  repeat rewrite app_assoc in h
              end;
              match goal with
              | h: Df ((?v0 ++ ?v) ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0) (v++v3) L2 L') as _h2
              end;
              match goal with
              | h:VBeginWith _ ?L |- VBeginWith _ ?L' =>
                assert (L'=L)
              end;
              [apply _h2 |];
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VBeginWith ?v ?L |- VBeginWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                    ; tryResolveBegin
                end).
            }
          }
          try_resolve_end.
        }
        (* <<< *)

        breakAll; try discriminate.

        (* T=[] *)
        1:{
          left.
          split; auto.
          simplList; subst.

          apply (Core.L4_1); eauto.

          exists L1.
          split; auto.

          (* v12和v3同尾, v1=v3+[Cal]+_, 用分离定理, 和上面类似 *)
          1:{
            

            (* 分离 VEndWith v12 L1 *)
            1:{
              match goal with
              | h: Df ?v _ _ |- VEndWith ?v _ =>
                destruct (Core.VHasEnd _ _ _ h)
              end.
              match goal with
              | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
              end.


              match goal with
              | h: Df (?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v) (v1) L' L1) as _h2
              end;
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).

              rewrite app_assoc in _h1.
              match goal with
              | h: Df (?v0++?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0++v) (v1) L' L1) as _h2
              end.
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).
              rewrite <- app_assoc.
              eauto using app_cons_not_nil.
              match goal with
              | h:VEndWith ?v ?L |- VEndWith (?v'++?v) ?L =>
                inversion h; breakAll; subst
                ; tac_inj
                ; repeat rewrite app_assoc
                ; tryResolveEnd
              end.
            }
          }

          match goal with
          |  |- VBeginWith (_ ++ ?v) _ =>
            try_resolve_begin_with v
          end.
        }

        (* T != [] *)
        1:{
          right.
          do 2 eexists.
          split; eauto.
          split; eauto.
          simplList; subst.
          split; intros.

          (* 这里destruct两个v *)
          destruct v12.
          syncEmpW.
          subst.
          repeat rewrite app_assoc.
          simpl; eauto.

          1:{
            rmDirect.
            repeat rewrite <- app_assoc.
            apply (Core.L4_1); eauto.
            exists L1.
            split; eauto.

            (* 分离 VEndWith (v :: v12) L1 *)
            1:{
              match goal with
              | h: Df ?v _ _ |- VEndWith ?v _ =>
                destruct (Core.VHasEnd _ _ _ h)
              end.

              match goal with
              | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (DFX_v _ _ _ _ _ _ _ h) as _h
                ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
                ; breakAll
                ; match goal with
                  | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                    rewrite h2 in h1
                  end
              end.


              match goal with
              | h: Df (?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v) (v1) L' L1) as _h2
              end;
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).

              rewrite app_assoc in _h1.
              match goal with
              | h: Df (?v0++?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0++v) (v1) L' L1) as _h2
              end.
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).
              match goal with
              | h:VEndWith ?v ?L |- VEndWith (?v'++?v) ?L =>
                inversion h
                ; breakAll; subst
                ; match goal with
                  | h: v = _ |- _ =>
                    rewrite h
                  end
                ; tac_inj
                ; repeat rewrite app_assoc
                ; tryResolveEnd
              end.
            }

            match goal with
            |  |- VBeginWith (_ ++ ?v) _ =>
              try_resolve_begin_with v
            end.
          }

          (* forall v'T'w' *)

          match goal with
          | h: forall _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v2) _ _,
            h2: VEndWith ?v1 ?Lv,
            h3: Df ?v1 ?T ?w1
            |- Df (?v1++?v2++_) ?T (?w1++?w2++_) =>
            assert (Df (v1++v2) T (w1++w2))
          end.
          1:{
            destruct v12.
            syncEmpW; subst.
            do 2 rewrite app_nil_r; eauto.

            match goal with
            | h: forall _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v2) _ _,
              h2: VEndWith ?v1 ?Lv,
              h3: Df ?v1 ?T ?w1
              |- Df (?v1++?v2) ?T (?w1++_) =>
              apply (h v1 T w1 Lv); eauto
            end.
            tryResolveBegin.
            resolveBeginWith.
          }
          repeat rewrite app_assoc.
          destruct v4.
          syncEmpW; subst.

          (* 有点复杂... *)
          1:{
            apply V_Ret with (L:=L2); eauto.
            rewrite app_nil_r.
            tryResolveEnd.
            (* rule *)
            eauto.
            1:{
              simpl in H7.
              inversion H7;
              match goal with
              | h: _ ++ [_] = [?e;Retv ?v] |- _ =>
                assert ([e; Retv v]=[e]++[Retv v]) as _h by eauto
                ; rewrite _h in h
                ; tac_inj
              end.
              assert (L2=L0).
              1:{
                subst.
                inversion H20; breakAll; subst; tac_inj; simplList; eauto.
                inversion a2; subst; eauto.
              }
              subst; eauto.
            }
            do 2 rewrite app_nil_r.
            constructor; eauto.
            (* rule *)

            resolveRule.

            (* 分离 VEndWith (v' ++ v12) L1 *)
            1:{
              destruct v12.
              syncEmpW.
              rewrite app_nil_r in *.

              assert (Lv=L1).
              1:{
                inversion H13; breakAll; simpl in *; simplList; subst; eauto.
              }
              subst; eauto.

              match goal with
              | h: Df ?v _ _ |- VEndWith ?v _ =>
                destruct (Core.VHasEnd _ _ _ h)
              end.

              match goal with
              | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
                h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
                pose (DFX_v _ _ _ _ _ _ _ h) as _h
                ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
                ; breakAll
                ; match goal with
                  | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                    rewrite h2 in h1
                  end
              end.


              match goal with
              | h: Df (?v ++ ?v1) _ _,
                h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
                pose (Core.VConnect _ _ _ h (v) (v1) L' L1) as _h2
              end;
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                eauto using nil_cons +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).
              
              solveEndWith.

              

              rewrite app_assoc in _h1.
              match goal with
              | h: Df (?v0++?v ++ ?v1) _ _,
                h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
                pose (Core.VConnect _ _ _ h (v0++v) (v1) L' L1) as _h2
              end.
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).
              
              refine (VListEndSame3 _ _ _ _ _ H18).
              eauto using nil_cons.
            }

          }

          apply V_Ret with (L:=L); auto.

          solveEndWith2; resolveEndWith2.

          match goal with
          | h: forall _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v2) _ _
            |- Df (?v1++?v2) ?T (?w1++_) =>
            apply (h v1 T w1 L2); eauto
          end.
          
          constructor; eauto.
          (* rule *)
          resolveRule.

          (* 分离End 2; VEndWith (v' ++ v12) L1; repeat 1 *)
          1:{
            destruct v12.
            syncEmpW.
            rewrite app_nil_r in *.

            assert (Lv=L1).
            1:{
              inversion H13; breakAll; simpl in *; simplList; subst; eauto.
            }
            subst; eauto.

            match goal with
            | h: Df ?v _ _ |- VEndWith ?v _ =>
                destruct (Core.VHasEnd _ _ _ h)
            end.

            match goal with
            | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
              h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
            end.


            match goal with
            | h: Df (?v ++ ?v1) _ _,
              h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
              pose (Core.VConnect _ _ _ h (v) (v1) L' L1) as _h2
            end;
            match goal with
            | h:VEndWith _ ?L |- VEndWith _ ?L' =>
              assert (L=L')
            end;
            [apply _h2 |]; eauto;
            repeat ((rewrite app_assoc; eauto) +
              eauto using app_cons_not_nil +
              eauto using nil_cons +
              tryResolveEnd +
              subst +
              match goal with
              | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                inversion h1
                ; breakAll; subst
                ; match goal with
                  | h: v = _ |- _ =>
                    rewrite h
                    ; rewrite <- app_assoc
                  end
              end +
              (rewrite <- app_assoc
              ; tryResolveBegin) +
              match goal with
              | h: Df ?v _ _ |- ?v != [] =>
                apply (L_Dv_v _ _ _ h)
              end).
            
            solveEndWith.

            

            rewrite app_assoc in _h1.
            match goal with
            | h: Df (?v0++?v ++ ?v1) _ _,
              h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
              pose (Core.VConnect _ _ _ h (v0++v) (v1) L' L1) as _h2
            end.
            match goal with
            | h:VEndWith _ ?L |- VEndWith _ ?L' =>
              assert (L=L')
            end;
            [apply _h2 |]; eauto;
            repeat ((rewrite app_assoc; eauto) +
              eauto using app_cons_not_nil +
              tryResolveEnd +
              subst +
              match goal with
              | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                inversion h1
                ; breakAll; subst
                ; match goal with
                  | h: v = _ |- _ =>
                    rewrite h
                    ; rewrite <- app_assoc
                  end
              end +
              (rewrite <- app_assoc
              ; tryResolveBegin) +
              match goal with
              | h: Df ?v _ _ |- ?v != [] =>
                apply (L_Dv_v _ _ _ h)
              end).
            
            refine (VListEndSame3 _ _ _ _ _ H18).
            eauto using nil_cons.
          }
          (* 分离 VBeginWith (v :: v4) L2 *)
          1:{
            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.

            (* 这个得用分离定理 *)
            1: {
              match goal with
              | h: Dfx _ _ _ _ (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
              end.

              (* unify *)
              all: match goal with
              | h: Df _ _ _ |- _ =>
                  repeat rewrite app_assoc in h
              end;
              match goal with
              | h: Df ((?v0 ++ ?v) ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0) (v++v3) L2 L') as _h2
              end;
              match goal with
              | h:VBeginWith _ ?L |- VBeginWith _ ?L' =>
                assert (L'=L)
              end;
              [apply _h2 |];
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VBeginWith ?v ?L |- VBeginWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                    ; tryResolveBegin
                end).
            }
          }

          tryResolveEnd.
        }
      }

      2:{
        (* 先对sub dfx用一下IH *)
        match goal with
        | h: forall _, len _ _ -> _ |- _ =>
          pose (h v3)
        end.
        breakInfer. tac_app. cmp_len2.
        match goal with
        | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
          H: Dfx _ _ _ _ _ _ _ |- _ =>
          pose (h _ _ _ _ _ _ H)
        end.

        (* 在对前一步的v用一下IH *)
        match goal with
        | h: forall _, len _ _ -> _ |- _ =>
          pose (h v0)
        end.
        breakInfer. tac_app. cmp_len.
        match goal with
        | h: forall _ _ _ _ _ _, Dfx _ _ _ _ _ _ _ -> _,
          H: Dfx v0 _ _ _ _ _ _ |- _ =>
          pose (h _ _ _ _ _ _ H)
        end.

        destruct t.
        2:{
          (* t <> matcal, 因为t::w4以L结尾, 用connect true定理 *)
          match goal with
          | h: Dfx _ _ _ _ (_ ++ [_] ++ _ ++ [_]) _ _ |- _ =>
            pose (DFX_v _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
            ; breakAll
            ; match goal with
              | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                rewrite h2 in h1
              end
            ; try discriminate
          end.

          
          1:{
            exfalso.
            destruct v4.
            1:{

              match goal with
              | h: Df (?v1 ++ [?v] ++ [] ++ [?v2]) _ _ |- _ =>
                pose (Core.VConnect _ _ _ h (v1++[v]) ([v2]) L2 L) as _h
                ; assert (L2 = L)
              end.
              apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
                eauto using nil_cons).

              tryResolveEnd.
              tryResolveBegin.
              clear _h _h1.

              subst.

              pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.

              
              destruct (A_VPG_Match _ _ _ _ _ _h).
              destruct (A_VPG_Linear _ _ _ H1); eauto.
              breakAll.
              discriminate.
            }

            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasEnd _ _ _ h)
            end.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VEndWith ?v ?L2 |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]++v) v3 L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).

            refine (VListEndSame2 _ _ _ H12).
            tryResolveBegin.
            subst.

            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.
            clear _h.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VBeginWith ?v ?L |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]) (v++v3) L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).
            tryResolveEnd.

            refine (VListBeginSame2 _ _ _ H14).
            subst.
            clear _h.


            pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.
            destruct (A_VPG_Match _ _ _ _ _ _h).
            breakAll; subst.


            match goal with
            | h: Df ?v _ _, h1: VBeginWith ?v (V0 ?L) |- _ =>
              pose (Core.VConnectTrue _ _ _ h L h1 (v) [])
            end.
            breakInfer. tac_app. eauto using app_nil_r.
            breakInfer. tac_app. eauto using nil_cons.
            breakAll; subst.

            mergeEnds.
            
            destruct (A_VPG_Linear _ _ _ H1); eauto.
            breakAll. discriminate.
          }

          (* Repeat 1 *)
          1:{
            exfalso.
            destruct v4.
            1:{

              match goal with
              | h: Df (?v1 ++ [?v] ++ [] ++ [?v2]) _ _ |- _ =>
                pose (Core.VConnect _ _ _ h (v1++[v]) ([v2]) L2 L) as _h
                ; assert (L2 = L)
              end.
              apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
                eauto using nil_cons).

              tryResolveEnd.
              tryResolveBegin.
              clear _h _h1.

              subst.

              pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.

              
              destruct (A_VPG_Match _ _ _ _ _ _h).
              destruct (A_VPG_Linear _ _ _ H1); eauto.
              breakAll.
              discriminate.
            }

            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasEnd _ _ _ h)
            end.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VEndWith ?v ?L2 |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]++v) v3 L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).

            refine (VListEndSame2 _ _ _ H12).
            tryResolveBegin.
            subst.

            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.
            clear _h.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VBeginWith ?v ?L |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]) (v++v3) L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).
            tryResolveEnd.

            refine (VListBeginSame2 _ _ _ H14).
            subst.
            clear _h.


            pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.
            destruct (A_VPG_Match _ _ _ _ _ _h).
            breakAll; subst.


            match goal with
            | h: Df ?v _ _, h1: VBeginWith ?v (V0 ?L) |- _ =>
              pose (Core.VConnectTrue _ _ _ h L h1 (v) [])
            end.
            breakInfer. tac_app. eauto using app_nil_r.
            breakInfer. tac_app. eauto using nil_cons.
            breakAll; subst.

            mergeEnds.
            
            destruct (A_VPG_Linear _ _ _ H1); eauto.
            breakAll. discriminate.
          }

          1:{
            do 2 rewrite app_assoc in _h1.
            exfalso.
            destruct v4.
            1:{

              match goal with
              | h: Df (?v1 ++ [?v] ++ [] ++ [?v2]) _ _ |- _ =>
                pose (Core.VConnect _ _ _ h (v1++[v]) ([v2]) L2 L) as _h
                ; assert (L2 = L)
              end.
              apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
                eauto using nil_cons).

              tryResolveEnd.
              tryResolveBegin.
              clear _h _h1.

              subst.

              pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.

              
              destruct (A_VPG_Match _ _ _ _ _ _h).
              destruct (A_VPG_Linear _ _ _ H1); eauto.
              breakAll.
              discriminate.
            }

            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasEnd _ _ _ h)
            end.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VEndWith ?v ?L2 |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]++v) v3 L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).

            refine (VListEndSame2 _ _ _ H12).
            tryResolveBegin.
            subst.

            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.
            clear _h.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VBeginWith ?v ?L |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]) (v++v3) L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).
            tryResolveEnd.

            refine (VListBeginSame2 _ _ _ H14).
            subst.
            clear _h.


            pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.
            destruct (A_VPG_Match _ _ _ _ _ _h).
            breakAll; subst.


            match goal with
            | h: Df ?v _ _, h1: VBeginWith ?v (V0 ?L) |- _ =>
              pose (Core.VConnectTrue _ _ _ h L h1 (v) [])
            end.
            breakInfer. tac_app. eauto using app_nil_r.
            breakInfer. tac_app. eauto using nil_cons.
            breakAll; subst.

            mergeEnds.
            
            destruct (A_VPG_Linear _ _ _ H1); eauto.
            breakAll. discriminate.
          }

          1:{
            do 2 rewrite app_assoc in _h1.
            exfalso.
            destruct v4.
            1:{

              match goal with
              | h: Df (?v1 ++ [?v] ++ [] ++ [?v2]) _ _ |- _ =>
                pose (Core.VConnect _ _ _ h (v1++[v]) ([v2]) L2 L) as _h
                ; assert (L2 = L)
              end.
              apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
                eauto using nil_cons).

              tryResolveEnd.
              tryResolveBegin.
              clear _h _h1.

              subst.

              pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.

              
              destruct (A_VPG_Match _ _ _ _ _ _h).
              destruct (A_VPG_Linear _ _ _ H1); eauto.
              breakAll.
              discriminate.
            }

            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasEnd _ _ _ h)
            end.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VEndWith ?v ?L2 |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]++v) v3 L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).

            refine (VListEndSame2 _ _ _ H12).
            tryResolveBegin.
            subst.

            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.
            clear _h.

            match goal with
            | h: Df (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h2: VBeginWith ?v ?L |- _ =>
              pose (Core.VConnect _ _ _ h (v1++[v2]) (v++v3) L2 L) as _h
              ; assert (L2=L)
            end.
            apply _h; repeat (rewrite app_assoc+rewrite app_nil_r+simpl+eauto using app_cons_not_nil +
              eauto using nil_cons).
            tryResolveEnd.

            refine (VListBeginSame2 _ _ _ H14).
            subst.
            clear _h.


            pose (DFX_df_rule2 _ _ _ _ _ _ _ _ _ _ _ _ H3) as _h.
            destruct (A_VPG_Match _ _ _ _ _ _h).
            breakAll; subst.


            match goal with
            | h: Df ?v _ _, h1: VBeginWith ?v (V0 ?L) |- _ =>
              pose (Core.VConnectTrue _ _ _ h L h1 (v) [])
            end.
            breakInfer. tac_app. eauto using app_nil_r.
            breakInfer. tac_app. eauto using nil_cons.
            breakAll; subst.

            mergeEnds.
            
            destruct (A_VPG_Linear _ _ _ H1); eauto.
            breakAll. discriminate.
          }
        }

        match goal with
        |  |- _ /\ Df ?v ?T ?w \/ _ =>
            assert (Df v T w)
        end.
        1:{
          (* breakAll; try discriminate; simplList; subst. *)

          match goal with
          | 
            |- Df (?v1++[Calv ?v2]++_) [] (?w1++?w2++_) =>
            assert (Df (v1++[Calv v2]) [v2] (w1++w2))
          end.
          1:{
            breakAll; try discriminate; simplList; subst.
            
            constructor; eauto.
            resolveRule.
            (* 分离定理 VEndWith v12 L0 *)
            1:{
              match goal with
              | h: Df ?v _ _ |- VEndWith ?v _ =>
                destruct (Core.VHasEnd _ _ _ h)
              end.
              match goal with
              | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
              end.


              match goal with
              | h: Df (?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v) (v1) L' L0) as _h2
              end;
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).

              rewrite app_assoc in _h1.
              match goal with
              | h: Df (?v0++?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0++v) (v1) L' L0) as _h2
              end.
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).
              rewrite <- app_assoc.
              eauto using app_cons_not_nil.
              match goal with
              | h:VEndWith ?v ?L |- VEndWith (?v'++?v) ?L =>
                inversion h; breakAll; subst
                ; tac_inj
                ; repeat rewrite app_assoc
                ; tryResolveEnd
              end.
            }
            
            destruct v12.
            syncEmpW; subst.
            constructor; eauto.
            resolveRule.

            rmDirect.
            constructor; eauto.
            resolveRule.
            
            (* 分离定理 VEndWith v12 L0; Vairant *)
            1:{
              match goal with
              | h: Df ?v _ _ |- VEndWith ?v _ =>
                destruct (Core.VHasEnd _ _ _ h)
              end.
              match goal with
              | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
              end.


              match goal with
              | h: Df (?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v) (v1) L' L0) as _h2
              end;
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).

              rewrite app_assoc in _h1.
              match goal with
              | h: Df (?v0++?v ++ ?v1) _ _,
                h1: VEndWith ?v ?L' |- VEndWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0++v) (v1) L' L0) as _h2
              end.
              match goal with
              | h:VEndWith _ ?L |- VEndWith _ ?L' =>
                assert (L=L')
              end;
              [apply _h2 |]; eauto;
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                end +
                (rewrite <- app_assoc
                ; tryResolveBegin) +
                match goal with
                | h: Df ?v _ _ |- ?v != [] =>
                  apply (L_Dv_v _ _ _ h)
                end).
              rewrite <- app_assoc.
              eauto using app_cons_not_nil.
              rewrite app_assoc.
              
              refine (VListEndSame2 _ _ _ H12 ).
            }
            
          }

          match goal with
          | h: Df ?v [?t] ?w |- Df (_ ++ _ ++ ?v' ++ _) [] (_ ++ _ ++ ?w' ++ _) =>
            assert (Df (v++v') [t] (w++w'))
          end.
          1:{

            (* 需要知道是谁在结尾 *)
            destruct v4.
            syncEmpW; subst.
            repeat rewrite app_nil_r; eauto.


            breakAll; try discriminate; simplList; subst;

            match goal with
            | h: forall _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v2) _ _,
              h3: Df ?v1 ?T ?w1
              |- Df (?v1++?v2) ?T (?w1++_) =>
              (* 注意! L2不是variable *)
              apply (h v1 T w1 L2); 
              eauto
            end.

          (* 分离 VBeginWith v4 L2 *)
          1:{
            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.

            (* 这个得用分离定理 *)
            1: {
              match goal with
              | h: Dfx _ _ _ _ (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
              end.

              (* unify *)
              all: match goal with
              | h: Df _ _ _ |- _ =>
                  repeat rewrite app_assoc in h
              end;
              match goal with
              | h: Df ((?v0 ++ ?v) ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0) (v++v3) L2 L') as _h2
              end;
              match goal with
              | h:VBeginWith _ ?L |- VBeginWith _ ?L' =>
                assert (L'=L)
              end;
              [apply _h2 |];
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VBeginWith ?v ?L |- VBeginWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                    ; tryResolveBegin
                end).
            }
          }
          tryResolveEnd.
          (* 分离 VBeginWith; repeat 1 *)
          1:{
            rmDirect.
            match goal with
            | h: Df ?v _ _ |- _ =>
              destruct (Core.VHasHead _ _ _ h)
            end.

            (* 这个得用分离定理 *)
            1: {
              match goal with
              | h: Dfx _ _ _ _ (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
              end.

              (* unify *)
              all: match goal with
              | h: Df _ _ _ |- _ =>
                  repeat rewrite app_assoc in h
              end;
              match goal with
              | h: Df ((?v0 ++ ?v) ++ ?v3) _ _,
                h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
                pose (Core.VConnect _ _ _ h (v0) (v++v3) L2 L') as _h2
              end;
              match goal with
              | h:VBeginWith _ ?L |- VBeginWith _ ?L' =>
                assert (L'=L)
              end;
              [apply _h2 |];
              repeat ((rewrite app_assoc; eauto) +
                eauto using app_cons_not_nil +
                tryResolveEnd +
                subst +
                match goal with
                | h1: VBeginWith ?v ?L |- VBeginWith (?v++?x) ?L =>
                  inversion h1
                  ; breakAll; subst
                  ; match goal with
                    | h: v = _ |- _ =>
                      rewrite h
                      ; rewrite <- app_assoc
                    end
                    ; tryResolveBegin
                end).
            }
          }
          tryResolveEnd.
          }

          repeat rewrite app_assoc.
          match goal with
          | h: Df ?v [?t1] ?w |- Df (?v++?v1) [] (?w++?w1) =>
            apply (V_Pnd_Ret) with (t:=t1)
            ; eauto
          end.

          (* 分离 VEndWith ((v12 ++ [Calv (PndCalE L0 a L2)]) ++ v4) L *)
          1:{
            match goal with
            | h: Df ?v _ _ |- VEndWith ?v _ =>
                destruct (Core.VHasEnd _ _ _ h)
            end.

            repeat rewrite app_assoc in H0.

            match goal with
            | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
              h1: VEndWith (?v) ?L' |- VEndWith (?v) ?L =>
              pose (DFX_v _ _ _ _ _ _ _ h) as _h
              ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
              ; breakAll
              ; try discriminate
              ; match goal with
                | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                  rewrite h2 in h1
                end
            end.


            1,2 : match goal with
            | h: Df (?v ++ ?v1) _ _,
              h1: VEndWith (?v) ?L' |- VEndWith (?v) ?L =>
              pose (Core.VConnect _ _ _ h (v) (v1) L' L) as _h2
            end;
            match goal with
            | h:VEndWith _ ?L |- VEndWith _ ?L' =>
              assert (L=L')
            end;
            [apply _h2 |]; eauto;
            repeat ((rewrite app_assoc; eauto) +
              eauto using app_cons_not_nil +
              eauto using nil_cons +
              tryResolveEnd +
              subst +
              match goal with
              | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                inversion h1
                ; breakAll; subst
                ; match goal with
                  | h: v = _ |- _ =>
                    rewrite h
                    ; rewrite <- app_assoc
                  end
              end +
              (repeat rewrite <- app_assoc
              ; try_resolve_begin) +
              match goal with
              | h: Df ?v _ _ |- ?v != [] =>
                apply (L_Dv_v _ _ _ h)
              end).

            
            match goal with
            | h: Df (?v1 ++ ?v2 ++ ?v ++ ?v3) _ _,
              h1: VEndWith (?v) ?L' |- VEndWith (?v) ?L =>
              pose (Core.VConnect _ _ _ h (v1 ++ v2 ++v) (v3) L' L) as _h2
            end.
            match goal with
            | h:VEndWith _ ?L |- VEndWith _ ?L' =>
              assert (L=L')
            end;
            [apply _h2 |]; eauto;
            repeat ((rewrite app_assoc; eauto) +
              eauto using app_cons_not_nil +
              eauto using nil_cons +
              tryResolveEnd +
              subst +
              match goal with
              | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                inversion h1
                ; breakAll; subst
                ; match goal with
                  | h: v = _ |- _ =>
                    rewrite h
                    ; rewrite <- app_assoc
                  end
              end +
              (repeat rewrite <- app_assoc
              ; try_resolve_begin) +
              match goal with
              | h: Df ?v _ _ |- ?v != [] =>
                apply (L_Dv_v _ _ _ h)
              end).

            destruct v1; simpl; eauto using nil_cons.
            repeat rewrite <- app_assoc.
            repeat rewrite <- app_assoc in H9.
            rewrite app_assoc.

            refine (VListEndSame2 _ _ _ H9).


            (* repeat above *)
            match goal with
            | h: Df (?v1 ++ ?v2 ++ ?v ++ ?v3) _ _,
              h1: VEndWith (?v) ?L' |- VEndWith (?v) ?L =>
              pose (Core.VConnect _ _ _ h (v1 ++ v2 ++v) (v3) L' L) as _h2
            end.
            match goal with
            | h:VEndWith _ ?L |- VEndWith _ ?L' =>
              assert (L=L')
            end;
            [apply _h2 |]; eauto;
            repeat ((rewrite app_assoc; eauto) +
              eauto using app_cons_not_nil +
              eauto using nil_cons +
              tryResolveEnd +
              subst +
              match goal with
              | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
                inversion h1
                ; breakAll; subst
                ; match goal with
                  | h: v = _ |- _ =>
                    rewrite h
                    ; rewrite <- app_assoc
                  end
              end +
              (repeat rewrite <- app_assoc
              ; try_resolve_begin) +
              match goal with
              | h: Df ?v _ _ |- ?v != [] =>
                apply (L_Dv_v _ _ _ h)
              end).

            destruct v1; simpl; eauto using nil_cons.
            repeat rewrite <- app_assoc.
            repeat rewrite <- app_assoc in H9.
            rewrite app_assoc.

            refine (VListEndSame2 _ _ _ H9).
          }
        }

        breakAll; try discriminate; simplList; subst.

        left; eauto.
        right; eauto.
        do 2 eexists.
        split; eauto.
        split; eauto.
        split; eauto.

        intros.

        (* >>> *)
        match goal with
        | h: forall _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v2) _ _,
          h2: VEndWith ?v1 ?Lv,
          h3: Df ?v1 ?T ?w1
          |- Df (?v1++?v2++_) ?T (?w1++?w2++_) =>
          assert (Df (v1++v2) T (w1++w2))
        end.
        1:{
          destruct v12.
          syncEmpW; subst.
          do 2 rewrite app_nil_r; eauto.

          match goal with
          | h: forall _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v2) _ _,
            h2: VEndWith ?v1 ?Lv,
            h3: Df ?v1 ?T ?w1
            |- Df (?v1++?v2) ?T (?w1++_) =>
            apply (h v1 T w1 Lv); eauto
          end.
          (* 分离 VBeginWith (v :: v12) Lv *)
          resolveBeginWith.
        }

        repeat rewrite app_assoc.
        destruct v4.
        syncEmpW; subst.

        (* 有点复杂... *)
        apply V_Pnd_Ret with (t:=(PndCalE L0 a L2)).
        (* rule *)
        eauto.
        (* 分离 VEndWith (((v' ++ v12) ++ [Calv (PndCalE L0 a L2)]) ++ []) L *)
        1:{

          repeat rewrite <- app_assoc.
          match goal with
          | h: Dfx _ _ _ _ (_ ++ ?v ++ ?v2) _ _ |- VEndWith (_++_++?v) ?L =>
            pose (DFX_v _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
            ; breakAll
            ; match goal with
              | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                rewrite h2 in h1
              end
            ; try discriminate
          end.

          rewrite app_nil_r.


          match goal with
          | h: Df (?v1 ++ ?v2 ++ ?v3 ++ ?v ++ [] ++ ?v5) _ _ |- VEndWith (_++_++?v) ?L =>
            pose (Core.VConnect _ _ _ h (v1++v2++v3++v) (v5) L2 L) as _h2
          end.

          assert (L2=L);
          [apply _h2 |]; eauto;
          repeat (
            (simpl; rewrite <- app_assoc; eauto) +
            eauto using app_cons_not_nil +
            eauto using nil_cons +
            tryResolveEnd +
            subst +
            match goal with
            | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
              inversion h1
              ; breakAll; subst
              ; match goal with
                | h: v = _ |- _ =>
                  rewrite h
                  ; rewrite <- app_assoc
                end
            end +
            (rewrite <- app_assoc
            ; tryResolveBegin) +
            match goal with
            | h: Df ?v _ _ |- ?v != [] =>
              apply (L_Dv_v _ _ _ h)
            end).
            
          repeat rewrite app_assoc.
          tryResolveEnd.
          try_resolve_begin.
          repeat rewrite app_assoc.
          tryResolveEnd.
        }

        do 2 rewrite app_nil_r.
        constructor; eauto.
        (* rules *)
        resolveRule.
        (* 分离定理貌似 *)
        1:{
          destruct v12.
          syncEmpW.
          rewrite app_nil_r in *.

          assert (Lv=L0).
          1:{
            inversion H13; breakAll; simpl in *; simplList; subst; eauto.
          }
          subst; eauto.

          match goal with
          | h: Df ?v _ _ |- VEndWith ?v _ =>
            destruct (Core.VHasEnd _ _ _ h)
          end.

          match goal with
          | h: Dfx _ _ _ _ (?v ++ ?v2) _ _,
            h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
            pose (DFX_v _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
            ; breakAll
            ; match goal with
              | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                rewrite h2 in h1
              end
          end.


          match goal with
          | h: Df (?v ++ ?v1) _ _,
            h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
            pose (Core.VConnect _ _ _ h (v) (v1) L' L0) as _h2
          end;
          match goal with
          | h:VEndWith _ ?L |- VEndWith _ ?L' =>
            assert (L=L')
          end;
          [apply _h2 |]; eauto;
          repeat ((rewrite app_assoc; eauto) +
            eauto using app_cons_not_nil +
            eauto using nil_cons +
            tryResolveEnd +
            subst +
            match goal with
            | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
              inversion h1
              ; breakAll; subst
              ; match goal with
                | h: v = _ |- _ =>
                  rewrite h
                  ; rewrite <- app_assoc
                end
            end +
            (rewrite <- app_assoc
            ; tryResolveBegin) +
            match goal with
            | h: Df ?v _ _ |- ?v != [] =>
              apply (L_Dv_v _ _ _ h)
            end).
          
          solveEndWith.

          

          rewrite app_assoc in _h1.
          match goal with
          | h: Df (?v0++?v ++ ?v1) _ _,
            h1: VEndWith (_++?v) ?L' |- VEndWith (_++?v) ?L =>
            pose (Core.VConnect _ _ _ h (v0++v) (v1) L' L0) as _h2
          end.
          match goal with
          | h:VEndWith _ ?L |- VEndWith _ ?L' =>
            assert (L=L')
          end;
          [apply _h2 |]; eauto;
          repeat ((rewrite app_assoc; eauto) +
            eauto using app_cons_not_nil +
            tryResolveEnd +
            subst +
            match goal with
            | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
              inversion h1
              ; breakAll; subst
              ; match goal with
                | h: v = _ |- _ =>
                  rewrite h
                  ; rewrite <- app_assoc
                end
            end +
            (rewrite <- app_assoc
            ; tryResolveBegin) +
            match goal with
            | h: Df ?v _ _ |- ?v != [] =>
              apply (L_Dv_v _ _ _ h)
            end).
          
          refine (VListEndSame3 _ _ _ _ _ H18).
          eauto using nil_cons.
        }

        apply V_Pnd_Ret with (t:=(PndCalE L0 a L2)).

        eauto.
        (* 分离定理貌似 *)
        1:{
          rmDirect.

          match goal with
          | h: Df ?v _ _ |- _ =>
            destruct (Core.VHasEnd _ _ _ h)
          end.

          repeat rewrite <- app_assoc.
          match goal with
          | h: Dfx _ _ _ _ (_ ++ _ ++ ?v ++ _) _ _ |- VEndWith (_++_++_++?v) ?L =>
            pose (DFX_v _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
            ; breakAll
            ; match goal with
              | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                rewrite h2 in h1
              end
            ; try discriminate
          end.


          match goal with
          | h: Df (?v1 ++ ?v2 ++ ?v3 ++ ?v4 ++ ?v ++ ?v5) _ _ |- VEndWith (_++_++_++?v) ?L =>
            pose (Core.VConnect _ _ _ h (v1++v2++v3++v4++v) (v5) x L) as _h2
          end.

          assert (x=L).
          apply _h2; eauto;
          repeat (
            (simpl; rewrite <- app_assoc; eauto) +
            eauto using app_cons_not_nil +
            eauto using nil_cons +
            tryResolveEnd +
            subst +
            match goal with
            | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
              inversion h1
              ; breakAll; subst
              ; match goal with
                | h: v = _ |- _ =>
                  rewrite h
                  ; rewrite <- app_assoc
                end
            end +
            (rewrite <- app_assoc
            ; tryResolveBegin) +
            match goal with
            | h: Df ?v _ _ |- ?v != [] =>
              apply (L_Dv_v _ _ _ h)
            end).
            
          repeat rewrite app_assoc.
          refine (VListEndSame2 _ _ _ H11).
          try_resolve_begin.
          subst.
          repeat rewrite app_assoc.
          refine (VListEndSame2 _ _ _ H11).
        }

        match goal with
        | h: forall _ _ _ _, _ -> _ -> _ -> Df (_ ++ ?v2) _ _
          |- Df (?v1++?v2) ?T (?w1++_) =>
          apply (h v1 T w1 L2); eauto
        end.
        
        constructor; eauto.
        resolveRule.

        (* 分离定理貌似 *)
        1:{
          destruct v12.
          syncEmpW; subst.
          rewrite app_nil_r; eauto.
          assert (Lv = L0).
          1:{
            inversion H13; breakAll; subst; eauto; simpl in *; simplList; eauto.
          }
          subst; eauto.
          rmDirect.

          match goal with
          | h: Dfx _ _ _ _ (?v ++ _) _ _ |- VEndWith (_++?v) ?L =>
            pose (DFX_v _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
            ; breakAll
            ; match goal with
              | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                rewrite h2 in h1
              end
            ; try discriminate
          end.

          rmDirect.
          match goal with
          | h: Df ?v _ _ |- VEndWith ?v _ =>
            destruct (Core.VHasEnd _ _ _ h)
          end.
          match goal with
          | h: Df (?v1 ++ ?v2 ++ ?v ++ ?v5) _ _ |- VEndWith (_++?v) ?L =>
            pose (Core.VConnect _ _ _ h (v1++v2++v) (v5) x3 L) as _h2
          end.

          assert (x3=L0).
          apply _h2; eauto;
          repeat (
            (simpl; rewrite <- app_assoc; eauto) +
            eauto using app_cons_not_nil +
            eauto using nil_cons +
            tryResolveEnd +
            subst +
            match goal with
            | h1: VEndWith ?v ?L |- VEndWith (?v++?x) ?L =>
              inversion h1
              ; breakAll; subst
              ; match goal with
                | h: v = _ |- _ =>
                  rewrite h
                  ; rewrite <- app_assoc
                end
            end +
            (rewrite <- app_assoc
            ; tryResolveBegin) +
            match goal with
            | h: Df ?v _ _ |- ?v != [] =>
              apply (L_Dv_v _ _ _ h)
            end).
            
          repeat rewrite app_assoc.
          refine (VListEndSame3 _ _ _ _ _ H15).
          eauto using nil_cons.
          simpl.
          tryResolveBegin.
          subst. eauto.
        }
        (* 分离定理貌似 H7 *)
        1:{
          rmDirect.
          match goal with
          | h: Df ?v _ _ |- _ =>
            destruct (Core.VHasHead _ _ _ h)
          end.

          (* 分离 *)
          1: {
            match goal with
            | h: Dfx _ _ _ _ (?v1 ++ [?v2] ++ ?v ++ ?v3) _ _,
              h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
            pose (DFX_v _ _ _ _ _ _ _ h) as _h
            ; pose (DFX_df _ _ _ _ _ _ _ h) as _h1
            ; breakAll
            ; match goal with
              | h1: Df ?v0 _ _, h2: ?v0=_ |- _ =>
                rewrite h2 in h1
              end
            end.

            (* unify *)
            all: match goal with
            | h: Df _ _ _ |- _ =>
                repeat rewrite app_assoc in h
            end;
            match goal with
            | h: Df ((?v0 ++ ?v) ++ ?v3) _ _,
              h1: VBeginWith ?v ?L' |- VBeginWith ?v ?L =>
              pose (Core.VConnect _ _ _ h (v0) (v++v3) L2 L') as _h2
            end;
            match goal with
            | h:VBeginWith _ ?L |- VBeginWith _ ?L' =>
              assert (L'=L)
            end;
            [apply _h2 |];
            repeat ((rewrite app_assoc; eauto) +
              eauto using app_cons_not_nil +
              tryResolveEnd +
              subst +
              match goal with
              | h1: VBeginWith ?v ?L |- VBeginWith (?v++?x) ?L =>
                inversion h1
                ; breakAll; subst
                ; match goal with
                  | h: v = _ |- _ =>
                    rewrite h
                    ; rewrite <- app_assoc
                  end
                  ; tryResolveBegin
              end).
          }
        }

        tryResolveEnd.
        (* <<< *)
      }

      1:{
        left.
        split; auto.
        apply V_Pnd_Ret with (t:=t); eauto.
        match goal with
        | h: Dfx _ _ _ _ _ _ _ |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h) as _h
        end.
        eauto.
      }

      1:{
        left.
        split; auto.
        apply V_Ret with (L:=L); eauto.
        match goal with
        | h: Dfx _ _ _ _ _ _ _ |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h) as _h
        end.
        eauto.
      }

    Qed.

    Ltac tac_invalid_dfx :=
      match goal with
      | h: Dfx [] _ _ _ _ _ _ |- _ =>
          pose (DFX_df _ _ _ _ _ _ _ h)
          ; tac_df
      end.

    Lemma DF_dfx_nohead: ∀ v, ∀ t T w, 
      ∀ v2 w1 w2, Dfx v (t::T) w [] v2 w1 w2 -> T=[].
    Proof.
      intro v.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      inversion H0; simpl; eauto; subst; try tac_invalid_dfx.

      pose (H v0);
      breakInfer;
      [tac_app; cmp_len |].
      pose (H4 _ _ _ _ _ _ H3); eauto.
      
      pose (H v1);
      breakInfer;
      [tac_app; cmp_len2 |].
      pose (H5 _ _ _ _ _ _ H4); eauto.


      pose (H v1);
      breakInfer;
      [tac_app; cmp_len2 |].
      pose (H5 _ _ _ _ _ _ H4); eauto.
    Qed.
    (* end hide *)

    (** [DF_dfx]: this lemma shows [Df] also indicates [Dfx]. *)
    Lemma DF_dfx: ∀ v, ∀ T w, 
      Df v T w ->
      ∃ v1 v2 w1 w2, Dfx v T w v1 v2 w1 w2.
    (* begin hide *)
    Proof.
      intro v.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      inversion H0; simpl; eauto; subst.

      all: try (do 4 eexists; constructor; eauto; fail).

      pose (H v0);
      breakInfer;
      [tac_app; cmp_len |];
      destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]];
      do 4 eexists;
      constructor; eauto.

      pose (H v0);
      breakInfer;
      [tac_app; cmp_len |];
      destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]];
      do 4 eexists.
      apply Vx_Pnd_Cal with (v1:=x1) (v2:=x2) (w1:=x3) (w2:=x4); eauto.

      pose (H v0);
      breakInfer;
      [tac_app; cmp_len |];
      destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]];
      do 4 eexists.
      apply Vx_Cal with (v1:=x1) (v2:=x2) (w1:=x3) (w2:=x4); eauto.

      pose (H v0);
      breakInfer;
      [tac_app; cmp_len |];
      destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]];
      do 4 eexists.
      apply Vx_Pnd_Ret_bot with (v1:=x1) (v2:=x2) (w1:=x3) (w2:=x4); eauto.
      
      pose (H v0);
      breakInfer;
      [tac_app; cmp_len |];
      destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]].

      pose (DFX_df_sub _ _ _ _ _ _ _ h).
      breakAll; try discriminate.
      simplList; subst.

      1:{
        destruct x1;
        try syncEmpW; subst;
        destruct x2;
        try syncEmpW; subst.

        all:try match goal with
        | h: Dfx _ _ _ [] _ _ _ |- _ =>
          rewrite (DF_dfx_nohead _ _ _ _ _ _ _ h) in *
          ; rewrite (DF_dfx_nohead _ _ _ _ _ _ _ h) in h
        end.
        
        do 4 eexists. 
        apply (Vx_Pnd_Ret_nohead) with (t:=x) (v2:=[]) (w1:=[]) (w2:=[]); eauto.

        do 4 eexists. 
        apply (Vx_Pnd_Ret_nohead) with (t:=x) (v2:=v::x2) (w1:=[]) (w2:=x4); eauto.


        pose (H (v::x1));
        breakInfer;
        [tac_app; cmp_len2 |];
        destruct (H7 _ _ H6) as [x1' [x2' [x3' [x4' h']]]].
        (* exists x1',x2',x3',x4'. *)
        do 4 eexists. 

        apply Vx_Pnd_Ret with (t:=x) (v1:=v::x1) (w1:=x3); eauto.

        rmDirect.
        rmDirect.
        pose (H (v::x1));
        breakInfer;
        [tac_app; cmp_len2 |];
        destruct (H7 _ _ H8) as [x1' [x2' [x3' [x4' h']]]].
        (* exists x1',x2',x3',x4'. *)
        do 4 eexists. 

        apply Vx_Pnd_Ret with (t:=x) (v1:=v::x1) (w1:=x3); eauto.
      }


      pose (H v0);
      breakInfer;
      [tac_app; cmp_len |];
      destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]].

      pose (DFX_df_sub _ _ _ _ _ _ _ h).
      breakAll; try discriminate.
      simplList; subst.

      1:{
        destruct x1;
        try syncEmpW; subst;
        destruct x2;
        try syncEmpW; subst.

        all:try match goal with
        | h: Dfx _ _ _ [] _ _ _ |- _ =>
          rewrite (DF_dfx_nohead _ _ _ _ _ _ _ h) in *
          ; rewrite (DF_dfx_nohead _ _ _ _ _ _ _ h) in h
        end.
        
        do 4 eexists. 
        apply (Vx_Ret_nohead) with (L:=L) (v2:=[]) (w1:=[]) (w2:=[]); eauto.

        do 4 eexists. 
        apply (Vx_Ret_nohead) with (L:=L) (v2:=v::x2) (w1:=[]) (w2:=x4); eauto.


        pose (H (v::x1));
        breakInfer;
        [tac_app; cmp_len2 |];
        destruct (H7 _ _ H6) as [x1' [x2' [x3' [x4' h']]]].
        (* exists x1',x2',x3',x4'. *)
        do 4 eexists. 

        apply Vx_Ret with (L:=L) (v1:=v::x1) (w1:=x3); eauto.

        rmDirect.
        rmDirect.
        pose (H (v::x1));
        breakInfer;
        [tac_app; cmp_len2 |];
        destruct (H7 _ _ H8) as [x1' [x2' [x3' [x4' h']]]].
        (* exists x1',x2',x3',x4'. *)
        do 4 eexists. 

        apply Vx_Ret with (L:=L) (v1:=v::x1) (w1:=x3); eauto.
      }
    Qed.
    (* end hide *)

  End DFX.

  Module Split.
    Import LEN_WF.
    Import DFX.

    Ltac cmp_len :=
      match goal with
      | |- len ?v (?v ++ ?e) =>
        unfold len
        ; rewrite (app_length v e)
        ; eauto
      end.

    (** [DF_SPLIT]: this lemma shows that we can split a parse tree into
        two parts, and the first parts still satisfies [Df], as long as
        it is nonempty.  *)
    Lemma DF_SPLIT: ∀ v T w, Df v T w -> 
      ∀ v1 v2, v=v1++v2 -> v1 != [] -> ∃ T1 w1, Df v1 T1 w1.
    (* begin hide *)
    Proof.
      intro.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      destruct v1. contradiction.
      clear H2.
      inversion H0; subst;
      try simplList; tac_inj; subst;
      eauto.

      all: destruct v2; try rewrite app_nil_r in *; eauto.
      all: assert (v::v2 <> []) as notnil by eauto using nil_cons.
      all: destruct (exists_last notnil);
        destruct s;
        rewrite e in *;
        clear e notnil;
        rewrite app_assoc in *; tac_inj; subst.


      all: match goal with
      | h: Df (?v++?v') ?T ?w |- _ =>
        refine (H _ _ _ _ h v v' _ _); eauto
      end.
      
      all: try (cmp_len; simpl; lia).
      all: eauto using nil_cons.
    Qed.
    (* end hide *)

    (** [DF_SPLIT2]: this lemma shows that we can split a parse tree
        into two parts, and the first parts still satisfies [Df], as
        long as it is nonempty, and the string can be split accordingly.
        *)
    Lemma DF_SPLIT2: ∀ v T w, Df v T w -> 
      ∀ v1 v2, v=v1++v2 -> v1 != [] -> 
      ∃ T1 w1, Df v1 T1 w1 /\ ∃ w2, w1++w2=w.
    (* begin hide *)
    Proof.
      intro.
      induction v using (well_founded_ind (len_wf _)).
      intros.
      destruct v1. contradiction.
      clear H2.
      inversion H0; subst;
      try simplList; tac_inj; subst;
      eauto.

      all: try (simpl in *; do 2 eexists; split; eauto;
      eexists; simpl; eauto; fail).

      all: destruct v2; try rewrite app_nil_r in *; eauto.

      all: assert (v0::v1 <> []) as notnil by eauto using nil_cons.
      all: destruct (exists_last notnil);
        destruct s;
        rewrite e in *;
        clear e notnil;
        try rewrite app_assoc in *; tac_inj; subst.

      all: try match goal with
      | h: Df ?v ?T ?w |- ∃ _ _, Df ?v _ _ /\ _ =>
      exists T,w; split; eauto
      end.

      all: try (exists []; rewrite app_nil_r; eauto; fail).

      
      all: assert (v::v2 <> []) as notnil by eauto using nil_cons.
      all: destruct (exists_last notnil);
        destruct s;
        rewrite e in *;
        clear e notnil;
        try rewrite app_assoc in *; tac_inj; subst.

      all: match goal with
      | h: Df (?v++?v') ?T ?w |- _ =>
        specialize H with (2:=h) (v1:=v) (v2:=v'); eauto
      end.

      all: match goal with
      | h:len _ _ -> _ -> _ -> ?g |- _ =>
      assert g; [apply h; eauto using app_cons_not_nil |]
      end
      ; try (cmp_len; simpl; lia).
      all: breakAll; subst.
      all: try match goal with
      | h: Df ?v ?T ?w |- ∃ _ _, Df ?v _ _ /\ _ =>
      exists T,w; split; eauto
      end.
      all: eexists; rewrite <- app_assoc; eauto.
    Qed.
    (* end hide *)

  End Split.
End ForwardSmallStep.
