(** This file shows the relations between the backward small-step
  relation [Db] and the extended backward small-step relation [Dbx]. *)

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

Require Import Lia.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.


Require Import Misc.
Import vpg.

Require Import Def.
Require Import BackwardSmallStep.


Module DBX(G:VPG).

    Module BackwardSmallStep := BackwardSmallStep(G).

    Import BackwardSmallStep.
    Import BackwardSmallStep.ForwardSmallStep.Def.
    Import BackwardSmallStep.ForwardSmallStep.Def.DB.
    Import BackwardSmallStep.ForwardSmallStep.Tac.Tacs.

    Import LEN_WF.

    (* begin hide *)

    Ltac cmp_len :=
        match goal with
        | |- len ?v ([?e]++?v) =>
          unfold len
          ; pose (last_length v e)
          ; eauto
        | |- len ?v (?e::?v) =>
          unfold len
          ; pose (last_length v e)
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

    (** [DBX_db]: this lemmas shows [Dbx] indicates [Db]. *)
    Lemma DBX_db: ∀ v, ∀ T w v1 v2 w1 w2, 
        Dbx v T w v1 v2 w1 w2 ->
        Db v T w.
    (* begin hide *)
    Proof.

        intro v.
        induction v using (well_founded_ind (len_wf _)).
        intros.
        inversion H0; simpl; eauto; subst.
        all: try (constructor; eauto; fail).

        Ltac appInd v0 :=
            match goal with
            | h: forall _, _ -> _, h2: Dbx v0 _ _ _ _ _ _ |- _ =>
                pose (h _ _ _ _ _ _ h2)
            end.
    
        all: try (pose (H v0);
            breakInfer;
            [tac_app;cmp_len |];
            (appInd v0);
            try constructor; eauto; fail).

        all: try (pose (H v0);
            breakInfer;
            [tac_app;cmp_len |];
            (appInd v0)).

        apply V_Cal_b1 with (L2:=L2) (b:=b) (L3:=L3); eauto.

        all: try (pose (H v2);
            breakInfer;
            [tac_app; cmp_len|];
            (appInd v2);
            try constructor; eauto).

        apply V_Cal_b1 with (L2:=L2) (b:=b) (L3:=L3); eauto.
        constructor; eauto.
        apply H with (2:=H2).
        unfold len.
        simpl. lia.
    Qed.
    (* end hide *)

    (* begin hide *)
    Lemma DBX_ww: ∀ v, ∀ T w v1 v2 w1 w2, 
    Dbx v T w v1 v2 w1 w2 ->
    (length w2) <= (length w).
    Proof.
        intros.
        induction H; simpl; eauto;
        try simpl in IHDbx; eauto; try lia;
        eauto using (Nat.le_trans).
    Qed.


    Lemma DBX_v: ∀ v, ∀ T w v1 v2 w1 w2, 
        Dbx v T w v1 v2 w1 w2 ->
        (T=[] /\ v=v1 /\ v2=[]) \/ (∃t T', T=t::T' /\ v = v1++[Retv t]++v2).
    Proof.
        intro v.
        induction v using (well_founded_ind (len_wf _)).
        intros.
        inversion H0; simpl; eauto; subst.

        all: try (
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; subst;
            (left + right);
            try split; eauto;
            try do 2 eexists;
            split; eauto; fail).

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.

            pose (H v4);
            breakInfer;
            [tac_app  |].
            pose app_length.
            match goal with
            |  |- len ?v (?x::?y++?z) =>
                pose (app_length (x::y) z) as d
                ; simpl in d
                (* ; rewrite <- app_assoc in d *)
                ; unfold len
                ; simpl in d
                ; simpl
                ; rewrite d
                ; lia
            end.

            match goal with
            | h: forall _, _ -> _, h2: Dbx v4 _ _ _ _ _ _ |- _ =>
                pose (h _ _ _ _ _ _ h2)
            end.

            appInd v4;
            unfold len. 
            breakAll; try discriminate; simpl in *; subst; eauto.

            right.
            try do 2 eexists; split; eauto.
            simpl; rewrite <- app_assoc; eauto.

            right.
            rewrite H7.
            try do 2 eexists; split; eauto.
            simpl; repeat rewrite <- app_assoc; simpl; eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.

            pose (H v3);
            breakInfer;
            [tac_app  |].

            unfold len; simpl. lia.

            appInd v3;
            unfold len. 
            breakAll; try discriminate; simpl in *; subst; eauto.
        }

        (* copy above *)
        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.

            pose (H v4);
            breakInfer;
            [tac_app  |].
            pose app_length.
            match goal with
            |  |- len ?v (?x::?y++?z::?w) =>
                pose (app_length (x::y++[z]) w) as d
                ; simpl in d
                ; rewrite <- app_assoc in d
                ; unfold len
                ; simpl in d
                ; simpl
                ; rewrite d
                ; lia
            end.
            appInd v4;
            unfold len. 
            breakAll; try discriminate; simpl in *; subst; eauto.

            right.
            try do 2 eexists; split; eauto.
            simpl; rewrite <- app_assoc; eauto.
        }

        (* copy above *)
        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.



            pose (H v4);
            breakInfer;
            [tac_app  |].
            pose app_length.
            match goal with
            |  |- len ?v (?x::?y++?z::?w) =>
                pose (app_length (x::y++[z]) w) as d
                ; simpl in d
                ; rewrite <- app_assoc in d
                ; unfold len
                ; simpl in d
                ; simpl
                ; rewrite d
                ; lia
            end.
            appInd v4;
            unfold len. 
            breakAll; try discriminate; simpl in *; subst; eauto.

            right.
            try do 2 eexists; split; eauto.
            simpl; rewrite <- app_assoc; eauto.
        }

    Qed.

    Lemma DBX_w: ∀ v, ∀ T w v1 v2 w1 w2, 
        Dbx v T w v1 v2 w1 w2 ->
        (T=[] /\ w=w1 /\ w2=[]) \/ (∃t T', T=t::T' /\ w = w1++[getSym t]++w2).
    Proof.
        intro v.
        induction v using (well_founded_ind (len_wf _)).
        intros.
        inversion H0; simpl; eauto; subst.

        all: try (
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; subst;
            (left + right);
            try split; eauto;
            try do 2 eexists;
            split; eauto; fail).

        all: try (pose (H v0);
        breakInfer;
        [tac_app; cmp_len |];
        appInd v0;
        breakAll; try discriminate; simpl in *; simplList; subst; eauto;
        (left + right);
            try split; eauto;
            try do 2 eexists;
            split; eauto; fail).

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *;  subst; eauto.
            right.
            try do 2 eexists;
            split; eauto.
            rewrite H5; eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; subst; eauto.


            right.
            try do 2 eexists; split; eauto.
            rewrite H5; eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.

            pose (H v4);
            breakInfer;
            [tac_app  |].

            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- len ?v _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.
            match goal with
            |  |- len ?v (?x::?y++?z::?w) =>
                pose (app_length (x::y++[z]) w) as d
                ; simpl in d
                ; rewrite <- app_assoc in d
                ; unfold len
                ; simpl in d
                ; simpl
                ; rewrite d
                ; lia
            end.
            appInd v4;
            unfold len. 
            breakAll; try discriminate; simpl in *; subst; eauto.

            right.
            try do 2 eexists; split; eauto.
            simpl; rewrite <- app_assoc; eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.
            simplList; subst.

            pose (H v3);
            breakInfer;
            [tac_app  |].

            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- len ?v _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.

            unfold len; simpl; lia.

            appInd v3.
            breakAll; try discriminate; simpl in *; subst; eauto.
        }

        (* copy above *)
        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.

            pose (H v4);
            breakInfer;
            [tac_app  |].

            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- len ?v _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.
            match goal with
            |  |- len ?v (?x::?y++?z::?w) =>
                pose (app_length (x::y++[z]) w) as d
                ; simpl in d
                ; rewrite <- app_assoc in d
                ; unfold len
                ; simpl in d
                ; simpl
                ; rewrite d
                ; lia
            end.
            appInd v4;
            unfold len. 
            breakAll; try discriminate; simpl in *; subst; eauto.
            try ((left + right);
                try split; eauto;
                rewrite H5; eauto;
                try do 2 eexists;
                split; eauto; fail).

            right.
            try do 2 eexists; split; eauto.
            rewrite H5.
            simpl; rewrite <- app_assoc; eauto.
        }

        (* copy above *)
        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0;
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.

            pose (H v4);
            breakInfer;
            [tac_app  |].

            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- len ?v _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; try discriminate; simpl in *; simplList; subst; eauto.
            match goal with
            |  |- len ?v (?x::?y++?z::?w) =>
                pose (app_length (x::y++[z]) w) as d
                ; simpl in d
                ; rewrite <- app_assoc in d
                ; unfold len
                ; simpl in d
                ; simpl
                ; rewrite d
                ; lia
            end.
            appInd v4;
            unfold len. 
            breakAll; try discriminate; simpl in *; subst; eauto.
            try ((left + right);
                try split; eauto;
                rewrite H5; eauto;
                try do 2 eexists;
                split; eauto; fail).

            right.
            try do 2 eexists; split; eauto.
            rewrite H5.
            simpl; rewrite <- app_assoc; eauto.
        }
    Qed.


    Lemma L_Db_uniqueV: ∀ v1 v2 T1 T2 w, (Db v1 T1 w)->(Db v2 T2 w)->
    (length v1 = length v2).
    Proof.
        intros.
        generalize dependent T1.
        generalize dependent v1.
        induction H0; intros v1 T1 Hv1; inversion Hv1; subst; auto.

        all: try match goal with
        | h: Db ?v ?T ?w  |- _ =>
            pose (IHDb v T h) as _H
            ; inversion _H
            ; subst
            ; auto
        end.

        all: try (simpl; lia).

        all: try match goal with
        | h: Db _ _ [] |- _ =>
           inversion h
        end.
    Qed.

    Lemma L_Db_vw: ∀ v T w, (Db v T w)->
    (length v = length w).
    Proof.
      intros.
      induction H; eauto.
      all: try (simpl in *; lia).
    Qed.

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
        | |- _ <  length (?w++?i) =>
            rewrite (app_length w i)
            ; subst
            ; auto
        | |- _ < _ + length (?w++?i) =>
            rewrite (app_length w i)
            ; subst
            ; auto
        | |- _ < _+ _ + length (?w++?i) =>
            rewrite (app_length w i)
            ; subst
            ; auto
        | |- _ < _ + _+ _ + length (?w++?i) =>
            rewrite (app_length w i)
            ; subst
            ; auto
        end.

    Ltac getAnd :=
        match goal with 
        | |- _ /\ _ => 
          split
        end.

    Lemma DBX_sub_dbx: ∀ v, ∀ T w v1 v2 w1 w2, 
        Dbx v T w v1 v2 w1 w2 ->
        ((v2=[] /\ w2=[] /\ (T=[] \/ ∃t, T=[t])) \/ 
        (∃ t T2 v21 v22 w21 w22, T=t::T2 
            /\ Dbx v2 T2 w2 v21 v22 w21 w22)).
    Proof.
        intro v.
        induction v using (well_founded_ind (len_wf _)).
        intros.
        inversion H0; simpl; eauto; subst.

        
        all: try (left; getAnd; eauto; fail).

        all: try (pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
                appInd v0;
                breakAll; subst; try discriminate; try simplList; subst;
            ((left; eauto; fail) +
                (right; eauto;
                do 5 eexists; eauto; fail))).

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0.
            breakAll; subst; try discriminate; try simplList; subst.
            match goal with
            | h: Dbx [] _ _ _ _ _ _  |- _ =>
                inversion h
            end.

            pose (H v4);
            breakInfer;
            [tac_app |].
            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; subst; try discriminate.

            unfold len.
            repeat (breakLenPlus + rewrite Nat.add_assoc); simpl. lia.
            match goal with
            | h1: Dbx v4 _ _ _ _ _ _, h2: Dbx v4 _ _ _ _ _ _ |- _ =>
                clear h2
            end.
            appInd v4;
            breakAll; subst;
            
            (left + right);
            try split; eauto;
            repeat eexists; eauto; fail.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0.
            breakAll; subst; try discriminate; try simplList; subst.
            match goal with
            | h: Dbx [] _ _ _ _ _ _  |- _ =>
                inversion h
            end.

            pose (H v3);
            breakInfer;
            [tac_app |].
            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; subst; try discriminate.

            unfold len.
            repeat (breakLenPlus + rewrite Nat.add_assoc); simpl. 
            match goal with
            | h1: Dbx v3 _ _ _ _ _ _, h2: Dbx v3 _ _ _ _ _ _ |- _ =>
                clear h2
            end.
            appInd v3;
            breakAll; subst;
            
            (left + right);
            try split; eauto;
            repeat eexists; eauto; fail.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0.
            breakAll; subst; try discriminate; try simplList; subst.
            match goal with
            | h: Dbx [] _ _ _ _ _ _  |- _ =>
                inversion h
            end.

            pose (H v4);
            breakInfer;
            [tac_app |].
            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; subst; try discriminate.

            unfold len.
            repeat (breakLenPlus + rewrite Nat.add_assoc); simpl. lia.
            match goal with
            | h1: Dbx v4 _ _ _ _ _ _, h2: Dbx v4 _ _ _ _ _ _ |- _ =>
                clear h2
            end.
            appInd v4;
            breakAll; subst;
            
            (left + right);
            try split; eauto;
            repeat eexists; eauto; fail.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |];
            appInd v0.
            breakAll; subst; try discriminate; try simplList; subst.
            match goal with
            | h: Dbx [] _ _ _ _ _ _  |- _ =>
                inversion h
            end.

            pose (H v4);
            breakInfer;
            [tac_app |].
            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
            end.
            breakAll; subst; try discriminate.

            unfold len.
            repeat (breakLenPlus + rewrite Nat.add_assoc); simpl. lia.
            match goal with
            | h1: Dbx v4 _ _ _ _ _ _, h2: Dbx v4 _ _ _ _ _ _ |- _ =>
                clear h2
            end.
            appInd v4;
            breakAll; subst;
            
            (left + right);
            try split; eauto;
            repeat eexists; eauto; fail.
        }

        all: try (right; do 6 eexists; eauto; fail).
    Qed.
    
    Lemma DBX_len_vw: ∀ v, ∀ T w v1 v2 w1 w2, 
        Dbx v T w v1 v2 w1 w2 ->
        (length v = length w /\ length v1=length w1 /\ length v2=length w2).
    (* begin hide *)
    Proof.
        intro.
        induction v using (well_founded_ind (len_wf _)).
        intros.

        inversion H0; subst.

        all: split; eauto.

        all: try ((pose (H v0) + pose (H v4)); breakInfer; try (tac_app; cmp_len)
        ; match goal with
            | h: forall _ _ _ _ _ _, Dbx _ _ _ _ _ _ _ -> _,
                h2: Dbx _ _ _ _ _ _ _ |- _ =>
                destruct (h _ _ _ _ _ _ h2)
                ; auto
            | h: forall _ _ _ _ _ _, Dbx _ _ _ _ _ _ _ -> _,
                h2: Dbx _ _ _ _ _ _ _, 
                h3: Dbx _ _ _ _ _ _ _ |- _ =>
                destruct (h _ _ _ _ _ _ h2)
                ; destruct (h _ _ _ _ _ _ h3)
                ; auto
         end).

        all: try (simpl; lia).



        all: repeat breakLenPlus.

        (* all: try do 2 rewrite app_assoc. *)

        all: simpl.

        all: try (
        match goal with
        | h: Dbx _ _ _ _ _ _ _ |- _ =>
            pose (DBX_v _ _ _ _ _ _ _ h)
            ; pose (DBX_w _ _ _ _ _ _ _ h)
            ; breakAll
            ; subst
            ; eauto
            ; try discriminate
            ; repeat breakLenPlus
        end; fail).

        1:{

            match goal with
            | h: Dbx v4 _ _ _ _ _ _ |- _ =>
            pose (H v4)
            end.
            breakInfer; [tac_app|].
            match goal with
            | h: Dbx v0 _ _ _ _ _ _ |- _ =>
            pose (DBX_v _ _ _ _ _ _ _ h)
            ; pose (DBX_w _ _ _ _ _ _ _ h)
            ; breakAll
            ; subst
            ; eauto
            ; try discriminate
            ; repeat breakLenPlus
            end.
            unfold len.
            
            repeat (breakLenPlus + rewrite Nat.add_assoc); simpl; lia.

            match goal with
            | h: forall _, _ -> _, h2: Dbx v4 _ _ _ _ _ _ |- _ =>
               destruct (h _ _ _ _ _ _ h2)
            end.
            
            breakAll.
            split; eauto.

            match goal with
            | |- S (length (?w1 ++ ?i1)) = S (length (?w++?i)) =>
                rewrite (app_length w i)
                ; rewrite (app_length w1 i1)
                ; subst
                ; auto
            end.
            simpl; lia.
        }

        all: try (match goal with
            | h: Dbx ?v4 _ _ _ _ _ _,
              h2: _ =_ /\ length ?v4 = _ |- _ =>
            pose (H v4)
            end;
            breakInfer; [tac_app|];
            match goal with
            | h: Dbx ?v0 _ _ _ _ _ _, h2: length ?v0=_ |- _ =>
            pose (DBX_v _ _ _ _ _ _ _ h)
            ; pose (DBX_w _ _ _ _ _ _ _ h)
            ; breakAll
            ; subst
            ; eauto
            ; try discriminate
            ; repeat breakLenPlus
            end;
            unfold len;

            [try (repeat (breakLenPlus + rewrite Nat.add_assoc); simpl; lia)|];

            match goal with
            | h: forall _, _ -> _, h2: Dbx ?v4 _ _ _ _ _ _ |- _ =>
               destruct (h _ _ _ _ _ _ h2)
            end;
            
            breakAll;
            split; eauto;

            match goal with
            | |- S (length (?w1 ++ ?i1)) = S (length (?w++?i)) =>
                rewrite (app_length w i)
                ; rewrite (app_length w1 i1)
                ; subst
                ; auto
            end;
            simpl; lia).



        all: try (match goal with
            | h: Dbx ?v2 _ _ _ _ _ _ |- _ =>
            pose (H v2)
            end;
            breakInfer; [tac_app; cmp_len|];


            match goal with
            | h: forall _, _ -> _, h2: Dbx ?v2 _ _ _ _ _ _ |- _ =>
               destruct (h _ _ _ _ _ _ h2)
            end;

            simpl in *; lia).
    Qed.
    (* end hide *)

    (* end hide *)

    (** [DB_dbx]: this lemmas shows [Db] also indicates [Dbx]. *)
    Lemma DB_dbx: ∀ v, ∀ T w, 
        Db v T w ->
        ∃ v1 v2 w1 w2, Dbx v T w v1 v2 w1 w2.
    (* begin hide *)
    Proof.
        intro v.
        induction v using (well_founded_ind (len_wf _)).
        intros.
        inversion H0; simpl; eauto; subst.

        all: try (do 4 eexists; constructor; eauto; fail).

        all: try (pose (H v0);
        breakInfer;
        [tac_app; cmp_len |];
        match goal with
        | h: ∀ _ _, _ -> _, h2: Db _ _ _ |- _ =>
           destruct (h _ _ h2) as [x1 [x2 [x3 [x4 _h]]]]
        end;
        do 4 eexists;
        constructor; eauto; inversion _h; subst; eauto; fail).

        pose (H v0);
        breakInfer;
        [tac_app; cmp_len |];
        destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]];
        do 4 eexists.
        apply Vb_Cal_Pnd_bot with (v1:=x1) (w1:=x3); eauto.

        (* 说明x2=x4=[] *)
        pose (DBX_v _ _ _ _ _ _ _ h);
        pose (DBX_w _ _ _ _ _ _ _ h);
        breakAll; try discriminate; subst; eauto.

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            destruct (H4 _ _ H3) as [x1 [x2 [x3 [x4 h]]]].

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
                ; simplList; subst
            end.

            1:{
                inversion h; subst; eauto;
                do 4 eexists;

                apply Vb_Cal_b1_emp with (1:=H1) (2:=H2) (3:=h).
            }

            pose Vb_Cal_b1.
            specialize d with (1:=H1) (3:=h) (4:=H5).
            do 4 eexists;
            apply d; eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
                ; simplList; subst
            end.

            inversion h; subst; eauto;
            do 4 eexists;
            apply Vb_Cal_b2_b_emp with (2:=h); eauto.

            inversion h; subst; eauto;
            do 4 eexists;
            apply Vb_Cal_b2_b with (2:=h); eauto.
        }


        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
                ; simplList; subst
            end.

            inversion h; subst; eauto;
            do 4 eexists;
            apply Vb_Cal_b2_a_emp with (2:=h); eauto.

            inversion h; subst; eauto;
            do 4 eexists;
            apply Vb_Cal_b2_a with (2:=h); eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
                ; simplList; subst
            end.

            inversion h; subst; eauto;
            do 4 eexists;
            apply Vb_Cal_b2_c_emp with (2:=h); eauto.

            inversion h; subst; eauto;
            do 4 eexists;
            apply Vb_Cal_b2_c with (2:=h); eauto.
        }


        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
                ; pose (DBX_w _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; eauto
                ; try discriminate
                ; repeat breakLenPlus
            end.

            do 4 eexists;
            apply Vb_Ret_Pnd_bot; eauto.
        }


        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
                ; pose (DBX_w _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; eauto
                ; try discriminate
                ; repeat simplList; subst
                ; repeat breakLenPlus
            end.

            all: do 4 eexists;
            apply Vb_Ret_Pnd with (3:=h); eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
                ; pose (DBX_w _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; eauto
                ; try discriminate
                ; repeat simplList; subst
                ; repeat breakLenPlus
            end.

            do 4 eexists.
            apply Vb_Ret_bot; eauto.
        }


        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
                ; pose (DBX_w _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; eauto
                ; try discriminate
                ; repeat simplList; subst
                ; repeat breakLenPlus
            end.

            do 4 eexists.
            apply Vb_Ret_b1 with (3:=h); eauto.
            do 4 eexists.
            apply Vb_Ret_b1 with (3:=h); eauto.
        }


        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
                ; pose (DBX_w _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; eauto
                ; try discriminate
                ; repeat simplList; subst
                ; repeat breakLenPlus
            end.

            do 4 eexists.
            apply Vb_Ret_b2_b with (2:=h); eauto.
            do 4 eexists.
            apply Vb_Ret_b2_b with (2:=h); eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
                ; pose (DBX_w _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; eauto
                ; try discriminate
                ; repeat simplList; subst
                ; repeat breakLenPlus
            end.

            do 4 eexists.
            apply Vb_Ret_b2_c with (3:=h); eauto.
            do 4 eexists.
            apply Vb_Ret_b2_c with (3:=h); eauto.
        }

        1:{
            pose (H v0);
            breakInfer;
            [tac_app; cmp_len |].
            match goal with
            | H: ∀ _ _, Db ?v _ _ -> _, h2: Db ?v _ _ |- _ =>
               destruct (H _ _ h2) as [x1 [x2 [x3 [x4 h]]]]
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_sub_dbx _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; try discriminate
            end.

            match goal with
            | h: Dbx _ _ _ _ _ _ _ |- _ =>
                pose (DBX_v _ _ _ _ _ _ _ h)
                ; pose (DBX_w _ _ _ _ _ _ _ h)
                ; breakAll
                ; subst
                ; eauto
                ; try discriminate
                ; repeat simplList; subst
                ; repeat breakLenPlus
            end.

            do 4 eexists.
            apply Vb_Ret_b2_a with (3:=h); eauto.
            do 4 eexists.
            apply Vb_Ret_b2_a with (3:=h); eauto.
        }
    Qed.
    (* end hide *)

    (** [L_split_db]: this lemmas shows we can split a parse tree in
      [Db] into two parts, and the second part still satisfies [Db]. *)
    Lemma L_split_db: ∀ v t w,
        Db v t w ->
        ∀ v1 v2 w1 w2,
        (v=v1++v2) ->
        (w=w1++w2) ->
        (length w2 = length v2) ->
        (w2 != []) ->
        (∃ t, Db v2 t w2).
    (* begin hide *)
    Proof.
        intros v.
        induction v; intros.
        inversion H.
        simpl in *; subst; eauto.

        assert (length w1=length v1).
        1:{
        match goal with
        | h: Db ?v ?T ?w |- _ => 
            pose (L_Db_vw v T w H) as e
        end.
        rewrite H0 in e.
        do 2 rewrite app_length in e.
        rewrite H2 in e.
        lia.
        }

        destruct w2; try easy.

        inversion H; subst; try simplList; tac_inj; subst.


        all: try (
        match goal with
        | h:[_] = ?w++_::_ |- _ =>
        destruct w; simpl in h; tac_inj; simplList; subst; simpl in *
        end;
        try match goal with
        | h:1 = length ?v |- _ =>
            destruct v; try easy; destruct v; try easy; simpl in h; tac_inj; subst
        end
        ; eauto
        ; rmInvalidList).


        all: destruct w1; simpl in *; simplList; subst;
        [match goal with
        | h: 0 = length ?v |- _ =>
        destruct v; simpl in *; try lia; rmDirect
        end;
        subst; addEx; eauto |].
        

        all: destruct v1; simpl in *; try lia; simplList; subst.

        all: try (apply (IHv _ _ H9 v1 v2 w1 (s::w2)); eauto).
        all: try (apply (IHv _ _ H10 v1 v2 w1 (s::w2)); eauto).

    Qed.
    (* end hide *)

End DBX.
