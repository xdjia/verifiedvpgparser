(** This file builds ordered types for the VPG symbols and rules, so
  that we can declare their sets. *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

Require Import Monad.
Require Import Lia.

Require Import Coq.Unicode.Utf8_core.
Notation "x != y" := (x <> y) (at level 70) : type_scope.

Module String_as_OT := Update_OT OrderedTypeEx.String_as_OT.

(* begin hide *)

Definition cost_compare_str := 1.
Opaque cost_compare_str.

Definition compare_str := String_as_OT.compare.
Program Definition compare_str' x y
    :{! res !:! comparison !<! c !>! c = cost_compare_str /\ 
        res = compare_str x y !}
    := += cost_compare_str; <== compare_str x y.

Definition cost_eq_str := 1.
Opaque cost_compare_str.
Definition eq_str x y :=
    match compare_str x y with 
    | Eq => true
    | _ => false 
    end.
Lemma L_eq_str: ∀ x y, eq_str x y = String.eqb x y.
Proof.
    intros.
    unfold eq_str.
    unfold compare_str.
    destruct_with_eqn (String_as_OT.compare x y);
    destruct (String_as_OT.compare_spec x y); try easy; subst.
    all: symmetry.
    apply String.eqb_refl.
    all: rewrite eqb_neq; unfold not; intro; subst;
    destruct (String_as_OT.lt_strorder);
    unfold Irreflexive in *;
    unfold complement in *;
    unfold Reflexive in *;
    apply StrictOrder_Irreflexive with y; auto.
Qed.

Program Definition eq_str' x y
    :{! res !:! bool !<! c !>! c = cost_eq_str /\ 
        res = eq_str x y !}
    := += cost_eq_str; <== eq_str x y.

(* end hide *)

(** The module [Basic] declares components of well-matched VPG. *)
Module Basic.
    (* begin hide *)
    Global Hint Resolve string_dec : misc.
    (* end hide *)

    (** [terminal]: terminals without tagging. *)
    Definition terminal := string.
    (** [variable]: nonterminals for well-matched VPGs. *)
    Definition variable := string.
    (** [word]: a string of terminals; used by the recognizer. *)
    Definition word := list terminal.

    (* begin hide *)
    Module terminal_as_OT <: OrderedType.
        Definition t := terminal.
        
        Definition eq := String_as_OT.eq.
        Definition eq_equiv := String_as_OT.eq_equiv.
        Definition terminal_dec : ∀ t1 t2 : terminal,
         {t1 = t2} + {t1 != t2}.
        Proof. eauto with misc. Qed.
        Definition eq_dec := terminal_dec.

        Definition lt := String_as_OT.lt.
        Definition lt_strorder := String_as_OT.lt_strorder.
        Definition lt_compat := String_as_OT.lt_compat.

        Definition compare_spec := String_as_OT.compare_spec.
        Definition compare := compare_str.
    End terminal_as_OT.
    Module terminal_set := MSetList.Make terminal_as_OT.

    Module variable_as_OT <: OrderedType.
        Definition t := variable.
        
        Definition eq := String_as_OT.eq.
        Definition eq_equiv := String_as_OT.eq_equiv.
        Definition variable_dec : ∀ t1 t2 : variable, {t1 = t2} + {t1 != t2}.
        Proof. eauto with misc. Qed.
        Global Hint Resolve variable_dec : misc.

        Definition eq_dec := variable_dec.

        Definition lt := String_as_OT.lt.
        Definition lt_strorder := String_as_OT.lt_strorder.
        Definition lt_compat := String_as_OT.lt_compat.

        Definition compare_spec := String_as_OT.compare_spec.
        Definition compare := compare_str.
    End variable_as_OT.

    Module variable_set := MSetList.Make variable_as_OT.

    Definition in_t_set := terminal_set.In.
    Definition in_v_set := variable_set.In.
    Definition in_t_setb := terminal_set.In.
    Definition in_v_setb := variable_set.mem.
    (* end hide *)
End Basic.

Module vpg.
    Import Basic.

    (** [symbol]: a call, plain or retun symbol. *)
    Inductive symbol :=
    | Call (t:terminal)
    | Plain (t:terminal)
    | Ret (t:terminal).

    (** [vpg_var]: a nonterminal belongs to either [V0] or [V1]. *)
    Inductive vpg_var :=
    | V0 (v:variable)
    | V1 (v:variable).

    (* begin hide *)
    Module symbol_as_OT <: OrderedType.
        Definition t := symbol.

        Definition eq := @eq symbol.
        Local Instance eq_equiv : Equivalence eq.
        split; unfold eq.
        intros s; induction s; simpl; auto.
        eauto with misc.
        unfold Transitive. apply eq_trans.
        Qed.

        Definition symbol_dec : ∀ c1 c2 : symbol, {c1 = c2} + {c1 != c2}.
        Proof. decide equality; eauto with misc. Qed.

        Global Hint Resolve symbol_dec : misc.

        Definition eq_dec := symbol_dec.
        

        Definition lt x y := 
            match x, y with 
            | Call _, Plain _ => True  
            | Call _, Ret _ => True  
            | Plain _, Ret _ => True  
            | Call x, Call y
            | Plain x, Plain y
            | Ret x, Ret y
                => String_as_OT.lt x y
            | _, _ => False
            end.
        
        Local Instance lt_strorder : StrictOrder lt.
        Proof.
            split; unfold lt.
            pose (String_as_OT.lt_strorder) as p;
            inversion p.
            intros s t; destruct s;
            pose (StrictOrder_Irreflexive t0 t); eauto with misc.

            pose (String_as_OT.lt_strorder) as p;
            inversion p.
            intros x y z; destruct x; destruct y; destruct z; eauto with misc; intros; eauto with misc;
            contradiction.
        Qed.
        
        Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
        Proof.
            unfold Proper, eq, lt; split; 
            destruct x; destruct x0; destruct y; destruct y0;
            eauto with misc; intro h; try (contradiction); 
            inversion H; inversion H0; subst; eauto with misc.
        Qed.

        Definition compare x y : comparison :=
            match x, y with 
            | Call x, Call y => compare_str x y
            | Plain x, Plain y => compare_str x y
            | Ret x, Ret y => compare_str x y
            | Call _, Plain _ => Lt
            | Call _, Ret _ => Lt
            | Plain _, Ret _ => Lt
            | _, _ => Gt
            end.
        

        Definition cost_compare_branch1 := 1.
        Definition cost_compare_branch2 := 1.
        Definition cost_compare_branch3 := 1.
        Definition cost_compare_branch4 := 1.
        Definition cost_compare_branch5 := 1.
        Definition cost_compare_branch6 := 1.
        Definition cost_compare_branch7 := 1.
        Opaque cost_compare_branch1.
        Opaque cost_compare_branch2.
        Opaque cost_compare_branch3.
        Opaque cost_compare_branch4.
        Opaque cost_compare_branch5.
        Opaque cost_compare_branch6.
        Opaque cost_compare_branch7.

        Definition cost_compare x y := 
            match x, y with 
            | Call x, Call y =>
                cost_compare_branch1 + cost_eq_str
            | Plain x, Plain y =>
                cost_compare_branch2 + cost_eq_str
            | Ret x, Ret y =>
                cost_compare_branch3 + cost_eq_str
            | Call _, Plain _ =>
                cost_compare_branch4
            | Call _, Ret _ =>
                cost_compare_branch5
            | Plain _, Ret _ =>
                cost_compare_branch6
            | _, _ =>
                cost_compare_branch7
            end.

        Lemma bound_cost_compare: ∃ k, ∀ s1 s2, 
            symbol_as_OT.cost_compare s1 s2 <= k.
          Proof.
            exists (cost_eq_str+symbol_as_OT.cost_compare_branch1+
            symbol_as_OT.cost_compare_branch2+symbol_as_OT.cost_compare_branch3+symbol_as_OT.cost_compare_branch4+
            symbol_as_OT.cost_compare_branch5+symbol_as_OT.cost_compare_branch6+symbol_as_OT.cost_compare_branch7).
            intros.
            unfold symbol_as_OT.cost_compare.
            destruct s1; destruct s2; lia.
          Qed.
        
        Program Definition compare' x y 
        :{! res !:! _ !<! c !>! c = cost_compare x y /\ 
            res = compare x y !}
        :=
            match x as x', y as y' return 
                (x=x')->(y=y')->
                {! res !:! _ !<! c !>! c = cost_compare x y /\ 
                res = compare x y !}
            with 
            | Call x, Call y =>
                fun hyp1 hyp2 =>
                out <- compare_str' x y;
                += cost_compare_branch1;
                <== out
            | Plain x, Plain y =>
                fun hyp1 hyp2 =>
                out <- compare_str' x y;
                += cost_compare_branch2;
                <== out
            | Ret x, Ret y =>
                fun hyp1 hyp2 =>
                out <- compare_str' x y;
                += cost_compare_branch3;
                <== out
            | Call _, Plain _ =>
                fun hyp1 hyp2 =>
                += cost_compare_branch4;
                <== Lt
            | Call _, Ret _ =>
                fun hyp1 hyp2 =>
                += cost_compare_branch5;
                <== Lt
            | Plain _, Ret _ =>
                fun hyp1 hyp2 =>
                += cost_compare_branch6;
                <== Lt
            | _, _ =>
                fun hyp1 hyp2 =>
                += cost_compare_branch7;
                <== Gt
            end (eq_refl x) (eq_refl y).

        Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
        Proof.
            intros x y;
            case_eq (compare x y);
            destruct x; destruct y;
            intro h; unfold compare in h; unfold compare_str in *;
            pose (String_as_OT.compare_spec t0 t1);
            inversion c; subst;
            try (
            constructor;
            try (reflexivity);
            rewrite h in H;
            inversion H; inversion h);
            try (inversion h);
            eauto with misc.
        Qed.
    End symbol_as_OT.

    Module symbol_set := MSetList.Make symbol_as_OT.

    Definition in_symbolb := symbol_set.mem.
    Definition in_symbol  := symbol_set.In.

    Module vpg_var_as_OT <: OrderedType.
        Definition t := vpg_var.
        
        Definition eq := @eq vpg_var.
        Local Instance eq_equiv : Equivalence eq.
        split; unfold eq.
        intros s; induction s; simpl; auto.
        eauto with misc.
        unfold Transitive. apply eq_trans.
        Qed.

        Definition vpg_var_dec : ∀ c1 c2 : vpg_var, {c1 = c2} + {c1 != c2}.
        Proof. decide equality; eauto with misc. Qed.

        Global Hint Resolve vpg_var_dec : misc.

        Definition eq_dec := vpg_var_dec.
        

        Definition lt (x y: vpg_var) := 
            match x, y with 
            | V0 _, V1 _ => True 
            | V0 x, V0 y
            | V1 x, V1 y => variable_as_OT.lt x y
            | _, _ => False
            end.
        
        Local Instance lt_strorder : StrictOrder lt.
        Proof.
            split; unfold lt.
            pose (variable_as_OT.lt_strorder) as p;
            inversion p.
            intros s t. destruct s;
            pose (StrictOrder_Irreflexive v); eauto with misc.

            pose (variable_as_OT.lt_strorder) as p;
            inversion p.
            intros x y z; destruct x; destruct y; destruct z; eauto with misc; intros; eauto with misc;
            try (pose (StrictOrder_Transitive v v0 v1 H H0); eauto with misc; 
            contradiction); try (contradiction).
        Qed.
        
        Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
        Proof.
            unfold Proper, eq, lt; split; 
            destruct x; destruct x0; destruct y; destruct y0;
            eauto with misc; intro h; try (contradiction); 
            inversion H; inversion H0; subst; eauto with misc.
        Qed.

        Definition compare (x y:vpg_var) : comparison :=
            match x, y with 
            | V0 _, V1 _ => Lt 
            | V0 x, V0 y
            | V1 x, V1 y
                => variable_as_OT.compare x y
            | _, _ => Gt
            end.

        Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
        Proof.
            intros x y;
            case_eq (compare x y);
            destruct x; destruct y;
            intro h; unfold compare in h;
            constructor;
            pose (variable_as_OT.compare_spec v v0) as c;
            assert (variable_as_OT.compare = String_as_OT.compare);
            eauto with misc;
            rewrite <- H in c;
            try (rewrite h in c;
            inversion c; subst; reflexivity;
            inversion h);
            try (inversion h);
            try (rewrite h in c; inversion c;
                unfold lt; eauto with misc
                );

            try (unfold lt; eauto with misc).
        Qed.
    End vpg_var_as_OT.

    Module vpg_var_set := MSetList.Make vpg_var_as_OT.

    Definition in_vpg_var_setb := vpg_var_set.mem.
    Definition in_vpg_var_set  := vpg_var_set.In.
    (* end hide *)

    (** [vword]: similar to [word], but is a list of VPG symbols.  *)
    Definition vword := list symbol.
        
    (** [alt]: three kinds of VPG rule body. *)
    Inductive alt :=
    | Alt_Epsilon
    | Alt_Linear (t:symbol) (v:vpg_var)
    | Alt_Match (t1 t2:terminal) (v1 v2:vpg_var).

    (** begin hide *)
    Module sot := Compare2EqBool(symbol_as_OT).
    Definition eqs := sot.eqb.
    Module vot := Compare2EqBool(variable_as_OT).
    Definition eqv := vot.eqb.
    Module vvot := Compare2EqBool(vpg_var_as_OT).

    Definition compare_sym := symbol_as_OT.compare.
    Definition compare_sym' := symbol_as_OT.compare'.

    Definition cost_eqs_branch1 := 1.
    Definition cost_eqs_branch2 := 1.
    Opaque cost_eqs_branch1. 
    Opaque cost_eqs_branch2.

    (* end hide *)

    (** [cost_eqs]: the cost to compare two symbols; viewed as constant.
      *)
    Definition cost_eqs s1 s2 :=
        symbol_as_OT.cost_compare s1 s2 +
        match compare_sym s1 s2 with
        | Eq => cost_eqs_branch1
        | _ => cost_eqs_branch2
        end.

    (** [bound_cost_eqs]: the cost to compare two symbols is bounded. *)
    Lemma bound_cost_eqs: ∃ k, ∀ s1 s2, cost_eqs s1 s2 <= k.
    Proof.
        destruct symbol_as_OT.bound_cost_compare as [k h].
        exists (k+cost_eqs_branch1+cost_eqs_branch2).
        intros.
        unfold cost_eqs.
        pose (h s1 s2).
        destruct (compare_sym s1 s2); lia.
    Qed.

    (** [eqs']: the monadic function to compare symbols with running
        time info. *)
    Program Definition eqs' s1 s2 
        :{! y !:! _ !<! c !>! c = cost_eqs s1 s2 /\ y = eqs s1 s2 !}
        :=
        out <- compare_sym' s1 s2;
        out <- match out as out' return (out=out')->
        {! y !:! _ !<! c !>! 
            c = match out with
            | Eq => cost_eqs_branch1
            | _ => cost_eqs_branch2
            end
             /\ y = eqs s1 s2 !}
        with
        | Eq =>
            fun hyp =>
            += cost_eqs_branch1;
            <== true
        | _ =>
            fun hyp =>
            += cost_eqs_branch2;
            <== false
        end (eq_refl out);
        <== out.

    Next Obligation.
        rewrite hyp. split; auto. 
        symmetry.
        apply (sot.eqb_eq).
        destruct (symbol_as_OT.compare_spec s1 s2); try easy.
    Defined.

    (* begin hide *)

    Next Obligation.
        rewrite hyp. split; auto. 
        destruct (symbol_as_OT.compare_spec s1 s2); try easy.
        destruct_with_eqn (eqs s1 s2); auto.
        destruct (sot.eqb_eq s1 s2).
        specialize H0 with (1:=Heqb).
        subst.
        destruct (symbol_as_OT.lt_strorder).
        unfold Irreflexive in *;
        unfold complement in *;
        unfold Reflexive in *.
        specialize StrictOrder_Irreflexive with s2; auto.
    Defined.

    Next Obligation.
        destruct (symbol_as_OT.compare_spec s1 s2); try easy.
        destruct_with_eqn (eqs s1 s2); auto.
        destruct (sot.eqb_eq s1 s2).
        specialize H0 with (1:=Heqb).
        subst.
        destruct (symbol_as_OT.lt_strorder).
        unfold Irreflexive in *;
        unfold complement in *;
        unfold Reflexive in *.
        specialize StrictOrder_Irreflexive with s2; auto.
    Defined.

    Next Obligation.
        split; auto.
        unfold cost_eqs.
        unfold compare_sym.
        destruct (symbol_as_OT.compare s1 s2); auto.
    Defined.


    Section eqvv.
        Definition cost_compare_vv_branch1 := 1.
        Definition cost_compare_vv_branch2 := 1.
        Definition cost_compare_vv_branch3 := 1.

        Opaque cost_compare_vv_branch1.
        Opaque cost_compare_vv_branch2.
        Opaque cost_compare_vv_branch3.

        Definition cost_compare_vv x y :=
        match x, y with
        | V0 _, V1 _ => cost_compare_vv_branch1
        | V0 x, V0 y
        | V1 x, V1 y =>
        cost_compare_str + cost_compare_vv_branch2
        | _, _ => cost_compare_vv_branch3
        end.

        Lemma bound_cost_compare_vv: ∃ k, ∀ x y,
            cost_compare_vv x y <= k.
        Proof.
            exists (
                cost_compare_str 
            + cost_compare_vv_branch1
            + cost_compare_vv_branch2
            + cost_compare_vv_branch3).
            intros. 
            destruct x; destruct y; simpl; lia.
        Qed.
        

        Program Definition compare_vv' x y 
        :{! res !:! _ !<! c !>! c = cost_compare_vv x y    
        /\ res = vpg_var_as_OT.compare x y !}
        :=
        match x as x', y as y' return
            (x=x')->(y=y')->
            {! res !:! _ !<! c !>! c = cost_compare_vv x y    
            /\ res = vpg_var_as_OT.compare x y !}
        with
        | V0 _, V1 _ => 
            fun hyp1 hyp2 =>
            += cost_compare_vv_branch1; <== Lt
        | V0 x, V0 y
        | V1 x, V1 y => 
            fun hyp1 hyp2 =>
            += cost_compare_vv_branch2;
            += cost_compare_str;
            <== compare_str x y
        | _, _ => 
            fun hyp1 hyp2 =>
            += cost_compare_vv_branch3;
            <== Gt
        end (eq_refl x) (eq_refl y).
        
        Definition eqvv a b := 
        match vpg_var_as_OT.compare a b with
        | Eq => true
        | _ => false
        end.

        Definition cost_eqvv_branch1 := 1.
        Definition cost_eqvv_branch2 := 1.
        Opaque cost_eqvv_branch1.
        Opaque cost_eqvv_branch2.

        Definition cost_eqvv a b :=
        cost_compare_vv a b +
        match vpg_var_as_OT.compare a b with
        | Eq => cost_eqvv_branch1
        | _ => cost_eqvv_branch2
        end.

        Opaque cost_compare_vv.
        Lemma bound_cost_eqvv: ∃ k, ∀ x y,
            cost_eqvv x y <= k.
        Proof.
            destruct (bound_cost_compare_vv) as [k ?].
            exists (k
                + cost_compare_str
                + cost_eqvv_branch1
                + cost_eqvv_branch2).
            intros.
            specialize H with x y. 
            destruct x; destruct y; unfold cost_eqvv; simpl;
            destruct (variable_as_OT.compare v v0 ); lia.
        Qed.

        Program Definition eqvv' a b
        :{! res !:! _ !<! c !>! c = cost_eqvv a b
        /\ res = eqvv a b !}
        :=
        r <- compare_vv' a b;
        out <- match r as r' return (r=r')->
        {! res !:! _ !<! c !>! 
            c = match vpg_var_as_OT.compare a b with
            | Eq => cost_eqvv_branch1
            | _ => cost_eqvv_branch2
            end
            /\ res = eqvv a b !}
        with
        | Eq => 
        fun hyp =>
            += cost_eqvv_branch1;
            <== true
        | _ => 
        fun hyp =>
            += cost_eqvv_branch2;
            <== false
        end (eq_refl r);
        <== out.

        Next Obligation.
        rewrite hyp.
        split; eauto.
        unfold eqvv.
        unfold vpg_var_as_OT.compare in hyp.
        destruct a;
        destruct b;
        simpl;
        try rewrite hyp; auto;
        inversion hyp.
        Defined.

        Next Obligation.
        rewrite hyp.
        split; eauto.
        unfold eqvv.
        unfold vpg_var_as_OT.compare in hyp.
        destruct a;
        destruct b;
        simpl;
        try rewrite hyp; auto;
        inversion hyp.
        Defined.

        Next Obligation.
        rewrite hyp.
        split; eauto.
        unfold eqvv.
        unfold vpg_var_as_OT.compare in hyp.
        destruct a;
        destruct b;
        simpl;
        try rewrite hyp; auto;
        inversion hyp.
        Defined.

        Next Obligation.
        unfold cost_eqvv.
        split; eauto.
        destruct a;
        destruct b;
        simpl;
        try rewrite hyp; auto;
        destruct (variable_as_OT.compare v v0); easy.
        Defined.

    End eqvv.

    Lemma vv_lt_irefl : ∀ (v:vpg_var),
        vpg_var_as_OT.lt v v -> False.
    Proof.
        pose (vpg_var_as_OT.lt_strorder).
        inversion s.
        unfold Irreflexive in StrictOrder_Irreflexive.
        unfold Reflexive in StrictOrder_Irreflexive.
        intro v.
        pose (StrictOrder_Irreflexive v).
        eauto with misc.
    Qed.
    Global Hint Resolve vv_lt_irefl : misc.

    Lemma vv_lt_trans : ∀ (v1 v2 v3:vpg_var),
    vpg_var_as_OT.lt v1 v2 -> 
    vpg_var_as_OT.lt v2 v3 -> 
    vpg_var_as_OT.lt v1 v3.
    Proof.
        pose (vpg_var_as_OT.lt_strorder).
        inversion s.
        unfold Transitive in StrictOrder_Transitive.
        eauto with misc.
    Qed.
    Global Hint Resolve vv_lt_trans : misc.

    Lemma sym_lt_irefl : ∀ (v:symbol),
    symbol_as_OT.lt v v -> False.
    Proof.
        pose (symbol_as_OT.lt_strorder).
        inversion s.
        unfold Irreflexive in StrictOrder_Irreflexive.
        unfold Reflexive in StrictOrder_Irreflexive.
        intro v.
        pose (StrictOrder_Irreflexive v).
        eauto with misc.
    Qed.
    Global Hint Resolve sym_lt_irefl : misc.

    Lemma sym_lt_itrefl : ∀ (v1 v2:symbol),
    symbol_as_OT.lt v1 v2 ->
    symbol_as_OT.lt v2 v1 ->
    False.
    Proof.
        pose (symbol_as_OT.lt_strorder).
        inversion s.
        unfold Irreflexive in StrictOrder_Irreflexive.
        unfold Reflexive in StrictOrder_Irreflexive.
        intro v.
        pose (StrictOrder_Irreflexive v).
        eauto with misc.
    Qed.
    Global Hint Resolve sym_lt_irefl : misc.

    Lemma sym_lt_neq : ∀ (u v:symbol),
    symbol_as_OT.lt u v -> (eqs u v = false).
    Proof.
        intros u v h.
        case_eq (eqs u v); intro p.
        pose (sot.eqb_eq u v) as i.
        destruct i.
        pose (H p). rewrite e in h.
        pose (sym_lt_irefl v h). contradiction. reflexivity.
    Qed.
    Global Hint Resolve sym_lt_neq : misc.

    Lemma sym_lt_trans : ∀ (v1 v2 v3:symbol),
    symbol_as_OT.lt v1 v2 -> 
    symbol_as_OT.lt v2 v3 -> 
    symbol_as_OT.lt v1 v3.
    Proof.
        pose (symbol_as_OT.lt_strorder).
        inversion s.
        unfold Transitive in StrictOrder_Transitive.
        eauto with misc.
    Qed.
    Global Hint Resolve sym_lt_trans : misc.

    Lemma sym_lt_eqbeq : ∀ (v1 v2:symbol),
    eqs v1 v2 = true -> 
    v1 = v2.
    Proof.
        intros v1 v2.
        pose (sot.eqb_eq v1 v2) as i.
        destruct i.
        eauto with misc.
    Qed.
    Global Hint Resolve sym_lt_eqbeq : misc.

    Lemma sym_eq_trans : ∀ (v1 v2 v3:symbol),
    eqs v1 v2 = true -> 
    eqs v2 v3 = true -> 
    v1 = v3.
    Proof.
        intros v1 v2 v3 h1 h2.
        pose (sym_lt_eqbeq _ _ h1).
        pose (sym_lt_eqbeq _ _ h2).
        rewrite e. assumption.
    Qed.
    Global Hint Resolve sym_eq_trans : misc.

    Lemma sym_eq_transb : ∀ (v1 v2 v3:symbol),
    eqs v1 v2 = true -> 
    eqs v2 v3 = true -> 
    eqs v1 v3 = true.
    Proof.
        intros v1 v2 v3 h1 h2.
        pose (sym_lt_eqbeq _ _ h1).
        pose (sym_lt_eqbeq _ _ h2).
        rewrite e. assumption.
    Qed.
    Global Hint Resolve sym_eq_transb : misc.

    Lemma vv_lt_eqbeq : ∀ (v1 v2:vpg_var),
    eqvv v1 v2 = true -> 
    v1 = v2.
    Proof.
        intros v1 v2.
        pose (vvot.eqb_eq v1 v2) as i.
        destruct i.
        eauto with misc.
    Qed.
    Global Hint Resolve vv_lt_eqbeq : misc.

    Lemma vv_eq_trans : ∀ (v1 v2 v3:vpg_var),
    eqvv v1 v2 = true -> 
    eqvv v2 v3 = true -> 
    eqvv v1 v3 = true.
    Proof.
        intros v1 v2 v3 h1 h2.
        pose (vv_lt_eqbeq _ _ h1).
        pose (vv_lt_eqbeq _ _ h2).
        rewrite e. assumption.
    Qed.
    Global Hint Resolve vv_eq_trans : misc.

    Lemma vv_lt_itrefl : ∀ (v1 v2 : vpg_var),
    vpg_var_as_OT.lt v1 v2 -> 
    vpg_var_as_OT.lt v2 v1 -> 
    False.
    Proof.
        intros v1 v2 h1 h2.
        pose (vv_lt_trans _ _ _ h1 h2).
        pose (vv_lt_irefl _ l).
        assumption.
    Qed.
    Global Hint Resolve vv_lt_itrefl : misc.


    Lemma vv_cmp_eq : ∀ t0 t1,
        vpg_var_as_OT.compare t0 t1 = Eq ->
        t0 = t1.
    Proof.
        intros t0 t1 h.
        pose (vpg_var_as_OT.compare_spec t0 t1) as c.
        rewrite h in c;
        inversion c.
        assert (t0 = t1); eauto with misc;
        subst; reflexivity.
    Qed.
    Global Hint Resolve vv_cmp_eq : misc.

    Lemma vv_cmp_lt : ∀ t0 t1,
        vpg_var_as_OT.compare t0 t1 = Lt ->
        vpg_var_as_OT.lt t0 t1.
    Proof.
        intros t0 t1 h.
        pose (vpg_var_as_OT.compare_spec t0 t1) as c.
        rewrite h in c;
        inversion c. assumption.
    Qed.
    Global Hint Resolve vv_cmp_lt : misc.

    Lemma sym_cmp_lt : ∀ t0 t1,
        symbol_as_OT.compare t0 t1 = Lt ->
        symbol_as_OT.lt t0 t1.
    Proof.
        intros t0 t1 h.
        pose (symbol_as_OT.compare_spec t0 t1) as c.
        rewrite h in c;
        inversion c. assumption.
    Qed.
    Global Hint Resolve sym_cmp_lt : misc.

    Lemma str_cmp_lt : ∀ t0 t1,
        compare_str t0 t1 = Lt ->
        String_as_OT.lt t0 t1.
    Proof.
        intros t0 t1 h.
        pose (String_as_OT.compare_spec t0 t1) as c.
        unfold compare_str in *.
        rewrite h in c;
        inversion c. assumption.
    Qed.

    Lemma sym_cmp_eq : ∀ t0 t1,
    symbol_as_OT.compare t0 t1 = Eq ->
    t0 = t1.
    Proof.
        intros t0 t1 h.
        pose (symbol_as_OT.compare_spec t0 t1) as c.
        rewrite h in c;
        inversion c.
        assert (t0 = t1); eauto with misc;
        subst; reflexivity.
    Qed.

    Lemma str_cmp_eq : ∀ t0 t1,
    compare_str t0 t1 = Eq ->
    t0 = t1.
    Proof.
        intros t0 t1 h.
        pose (String_as_OT.compare_spec t0 t1) as c.
        unfold compare_str in *.

        rewrite h in c;
        inversion c.
        assert (t0 = t1); eauto with misc;
        subst; reflexivity.
    Qed.

    Lemma sym_cmp_lt' : ∀ t0 t1,
        symbol_as_OT.lt t0 t1 ->
        symbol_as_OT.compare t0 t1 = Lt.
    Proof.
        intros t0 t1 h.
        pose (symbol_as_OT.compare_spec t0 t1) as c.
        inversion c. 
        3: {
            pose (sym_lt_itrefl _ _ h H0).
            contradiction.
        }

        assert (t0 = t1); eauto with misc; subst.
        pose (sym_lt_irefl t1 h). contradiction.

        reflexivity.
    Qed.
    Global Hint Resolve sym_cmp_lt' : misc.

    Lemma vv_cmp_lt' : ∀ t0 t1,
        vpg_var_as_OT.lt t0 t1 ->
        vpg_var_as_OT.compare t0 t1 = Lt.
    Proof.
        intros t0 t1 h.
        pose (vpg_var_as_OT.compare_spec t0 t1) as c.
        inversion c. 
        3: {
            pose (vv_lt_itrefl _ _ h H0).
            contradiction.
        }

        assert (t0 = t1); eauto with misc; subst.
        pose (vv_lt_irefl t1 h). contradiction.

        reflexivity.
    Qed.
    Global Hint Resolve vv_cmp_lt' : misc.

    Lemma sym_lt_gt : ∀ v v0,
        symbol_as_OT.compare v v0 = Gt ->
        symbol_as_OT.compare v0 v = Lt.
    Proof.
        intros v v0 h.

        pose (symbol_as_OT.compare_spec v0 v) as c.
        inversion c.

        assert (v0 = v); eauto with misc; subst;
        rewrite h in H; inversion H.

        reflexivity.
        
        pose (sym_cmp_lt' _ _ H0).
        rewrite e in h. inversion h.
    Qed.
    Global Hint Resolve sym_lt_gt : misc.

    Lemma vv_lt_gt : ∀ v v0,
        vpg_var_as_OT.compare v v0 = Gt ->
        vpg_var_as_OT.compare v0 v = Lt.
    Proof.
        intros v v0 h.

        pose (vpg_var_as_OT.compare_spec v0 v) as c.
        inversion c.

        assert (v0 = v); eauto with misc; subst;
        rewrite h in H; inversion H.

        reflexivity.
        
        pose (vv_cmp_lt' _ _ H0).
        rewrite e in h. inversion h.
    Qed.
    Global Hint Resolve vv_lt_gt : misc.

    Module alt_as_OT <: OrderedType.
        Definition t := alt.
        
        Definition eq := @eq alt.
        Local Instance eq_equiv : Equivalence eq.
        split; unfold eq.
        intros s; induction s; simpl; auto.
        eauto with misc.
        unfold Transitive. apply eq_trans.
        Qed.

        Definition alt_dec : ∀ c1 c2 : alt, {c1 = c2} + {c1 != c2}.
        Proof. decide equality; eauto with misc. Qed.
        Definition eq_dec := alt_dec.
        

        Definition lt (x y: alt) := 
            match x, y with 
            | Alt_Epsilon, Alt_Linear _ _ 
            | Alt_Epsilon, Alt_Match _ _ _ _ 
            | Alt_Linear _ _, Alt_Match _ _ _ _ => True 
            | Alt_Linear t1 v1, Alt_Linear t2 v2 =>
                if negb (eqs t1 t2) then 
                    symbol_as_OT.lt t1 t2
                else 
                    vpg_var_as_OT.lt v1 v2
            | Alt_Match t1 t2 v1 v2, Alt_Match t1' t2' v1' v2' => 
                if negb (String.eqb t1 t1') then String_as_OT.lt t1 t1' else 
                if negb (String.eqb t2 t2') then String_as_OT.lt t2 t2' else 
                if negb (eqvv v1 v1') then vpg_var_as_OT.lt v1 v1' else 
                    vpg_var_as_OT.lt v2 v2'
            | _, _ => False
            end.

        Global Hint Resolve OrderedTypeEx.String_as_OT.lt_not_eq : misc.

        Local Instance lt_strorder : StrictOrder lt.
        Proof.
            split; unfold lt. 
            1: {
                intros s t; destruct s; try (contradiction).

                destruct_with_eqn (eqs t0 t0).
                simpl in t.
                eauto with misc.

                destruct (sot.eqb_eq t0 t0) as [_ H].
                assert (eqs t0 t0 = true).
                apply H; auto.
                rewrite H0 in Heqb.
                discriminate.

                destruct_with_eqn (String.eqb t1 t1);
                destruct_with_eqn (String.eqb t2 t2);
                destruct_with_eqn (eqvv v1 v1);
                simpl in t.
                eauto with misc.

                Ltac eqvv_refl x := 
                    assert (eqvv x x=true) by
                    (apply (vvot.eqb_eq x x); eauto).
                    
                Ltac resolveBool :=
                    match goal with
                    | h: ?g=true, x:?g=false |- _ =>
                        rewrite h in x; discriminate
                    end.

                Ltac resolveVV :=
                    match goal with
                    | h: eqvv ?v ?v = false |- _ =>
                        eqvv_refl v
                    | h: vpg_var_as_OT.lt ?t ?t |- _ =>
                        destruct (vpg_var_as_OT.lt_strorder) as [tacH _]
                        ;  pose (tacH t)
                        ; contradiction
                    end.

                Ltac resolveStr :=
                    match goal with
                    | h: String.eqb ?x ?x = false |- _ =>
                        assert (String.eqb x x=true) by
                        (apply (String.eqb_eq x x); eauto)
                    end.

                all: try (resolveVV;
                resolveBool).

                all: try resolveStr.

                all: resolveBool.
            }

            Ltac f1 :=
                match goal with 
                | [h : context [ negb (eqs  ?u ?v) ] |- _] => 
                    let g := fresh "g" in
                    case_eq (eqs  u v); intro g; rewrite g in h; simpl in h
                | [h : context [ negb (eqvv  ?u ?v) ] |- _] => 
                    let g := fresh "g" in
                    case_eq (eqvv  u v); intro g; rewrite g in h; simpl in h
                | [h: eqs ?u ?v = true, g: eqs ?v ?w = true |- context [negb (eqs ?u ?w)]] =>
                    let q := fresh "q" in
                    assert (eqs u w=true) as q by eapply (sym_eq_transb u v w h g);
                    rewrite q; simpl; clear q
                | [h: vpg_var_as_OT.lt ?u ?v, g: vpg_var_as_OT.lt ?v ?w |- vpg_var_as_OT.lt ?u ?w] =>
                    eapply (vv_lt_trans u v w h g)
                | |- context [negb (eqs ?u ?v)] => 
                    let g := fresh "g" in
                    case_eq (eqs u v); intro g
                | |- context [negb (eqvv ?u ?v)] => 
                    let g := fresh "g" in
                    case_eq (eqvv u v); intro g
                | |- context [ (negb false) ] => simpl
                | |- context [ (negb true) ] => simpl
                end.

            intros s t z; destruct s; destruct t; destruct z.
            all: try contradiction; intros; eauto with misc;
            repeat f1.

            Ltac trans_s :=
            match goal with
            | h: eqs ?x ?y = true |- _ =>
                pose (sot.eqb_eq x y) as i; destruct i as [q1 _]; 
                pose (q1 h) as e; rewrite e in *;
                clear e; clear q1; clear h
            end.

            Ltac resolveS :=
                match goal with
                | h: eqs ?x ?x = false |- _ =>
                    assert (eqs x x=true) by
                    (apply (sot.eqb_eq x x); eauto)
                | h: String.eqb ?x ?x = false |- _ =>
                    assert (String.eqb x x=true) by
                    (apply (String.eqb_eq x x); eauto)
                | h: symbol_as_OT.lt ?t ?t |- _ =>
                    destruct (symbol_as_OT.lt_strorder) as [tacH _]
                    ;  pose (tacH t)
                    ; contradiction
                | h: String_as_OT.lt ?t ?t |- _ =>
                    destruct (String_as_OT.lt_strorder) as [tacH _]
                    ;  pose (tacH t)
                    ; contradiction
                end.


            all: try (repeat trans_s;
                try resolveS;
                try resolveBool;
                auto; fail).
            
            Ltac app_lt_trans :=
                match goal with
                | H: symbol_as_OT.lt ?t0 ?t1,
                    H0: symbol_as_OT.lt ?t1 ?t2 |- _ =>
                    destruct (symbol_as_OT.lt_strorder) as [_ h]
                    ; pose (h t0 t1 t2 H H0)
                | H: String_as_OT.lt ?t0 ?t1,
                    H0: String_as_OT.lt ?t1 ?t2 |- _ =>
                    destruct (String_as_OT.lt_strorder) as [_ h]
                    ; pose (h t0 t1 t2 H H0)
                end.


            Ltac rmDirect :=
                match goal with 
                | h: ?v::?s != [] -> ?g |- _ =>
                  assert (g) by 
                   (apply h
                  ; eauto using nil_cons)
                  ; clear h
                | h1:?h -> ?v, g:?h |- _ =>
                    assert v by auto using h1
                    ; clear h1
                | h: [] != [] -> _ |- _ =>
                  clear h
                | h: [] = [] -> ?g |- _ => 
                  assert g by (apply h; auto)
                  ; clear h
                end.

            
            Ltac eqvv_True :=
                match goal with 
                | h: eqvv ?v ?u = true |- _ =>
                    pose (vv_lt_eqbeq v u h) as eqvv_True_e
                    ; rewrite eqvv_True_e in *
                    ; clear eqvv_True_e
                    ; clear h
                end.

            Ltac eqstr_True :=
                match goal with 
                | h: String.eqb ?v ?u = true |- _ =>
                    destruct (String.eqb_eq v u) as [_H _]
                    ; pose (_H h) as e
                    ; rewrite e in *
                    ; clear e
                    ; clear h
                    ; clear _H
                end.
    

            Ltac eqs_True :=
                match goal with 
                | h: eqs ?s1 ?s2 = true |- _ =>
                    destruct (sot.eqb_eq s1 s2)
                    ; rmDirect
                    ; clear h
                end.

            all: try app_lt_trans.
            all: try (eqs_True; subst; resolveS).
            all: try auto.

            repeat eqvv_True.

            all: do 2 try (match goal with
            |  |- if (negb (?g)) then _ else _ =>
                destruct_with_eqn (g)
            end; simpl).

            all: do 4 try (match goal with
            | h:if (negb (?g)) then _ else _ |- _ =>
                destruct_with_eqn (g)
                ; simpl in h
            end; simpl).

            all: repeat (eqstr_True; simpl).

            

            all: try match goal with
            | H: vpg_var_as_OT.lt ?t0 ?t1,
                H0: vpg_var_as_OT.lt ?t1 ?t2 |- _ =>
                destruct (vpg_var_as_OT.lt_strorder) as [_ h]
                ; pose (h t0 t1 t2 H H0)
            end; auto.

            all: try app_lt_trans.
            all: try resolveS; try resolveBool; auto.

            all: repeat eqvv_True;
            try resolveVV;
            try resolveBool; auto.
        Qed.
        
        Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
        Proof.
            unfold Proper, eq, lt; split; 
            destruct x; destruct x0; destruct y; destruct y0;
            eauto with misc; intro h; try (contradiction); 
            inversion H; inversion H0; subst; eauto with misc.
        Qed.

        Definition compare (x y:alt) : comparison :=
            match x, y with 
            | Alt_Epsilon, Alt_Linear _ _ 
            | Alt_Epsilon, Alt_Match _ _ _ _ 
            | Alt_Linear _ _, Alt_Match _ _ _ _ => Lt 
            | Alt_Linear t1 v1, Alt_Linear t2 v2 =>
                if negb (eqs t1 t2) then 
                symbol_as_OT.compare t1 t2
                else 
                vpg_var_as_OT.compare v1 v2
            | Alt_Match t1 t2 v1 v2, Alt_Match t1' t2' v1' v2' => 
                if negb (String.eqb t1 t1') then compare_str t1 t1' else 
                if negb (String.eqb t2 t2') then compare_str t2 t2' else 
                if negb (eqvv v1 v1') then vpg_var_as_OT.compare v1 v1' else 
                    vpg_var_as_OT.compare v2 v2'
            | Alt_Epsilon, Alt_Epsilon => Eq
            | _, _ => Gt
            end.

        Lemma sot_cmp_eq : ∀ t0 t1,
            symbol_as_OT.compare t0 t1 = Eq ->
            t0 = t1.
        Proof.
            intros t0 t1 h.
            pose (symbol_as_OT.compare_spec t0 t1) as c.
            rewrite h in c;
            inversion c.
            assert (t0 = t1); eauto with misc;
            subst; reflexivity.
        Qed.
        Global Hint Resolve sot_cmp_eq : misc.


        Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
        Proof.

            Ltac f_rename2 := 
                match goal with 
                | [h: vpg_var_as_OT.compare ?u ?v = Eq |- _] => 
                    let i := fresh "i" in
                    let c := fresh "c" in
                    assert (u=v) as i; pose (vpg_var_as_OT.compare_spec u v) as c; 
                    rewrite h in c; inversion c; eauto with misc; rewrite i in *; clear i h
                | [h: vpg_var_as_OT.compare ?u ?v = Lt |- _] => 
                    let i := fresh "i" in
                    let c := fresh "c" in
                    assert (vpg_var_as_OT.lt u v) as i; pose (vpg_var_as_OT.compare_spec u v) as c; 
                    rewrite h in c; inversion c; eauto with misc; clear h c
                | [h: symbol_as_OT.compare ?u ?v = Eq |- _] => 
                    let i := fresh "i" in
                    let c := fresh "c" in
                    assert (u=v) as i; pose (symbol_as_OT.compare_spec u v) as c; 
                    rewrite h in c; inversion c; eauto with misc; rewrite i in *; clear i h
                | [h: symbol_as_OT.compare ?u ?v = Lt |- _] => 
                    let i := fresh "i" in
                    let c := fresh "c" in
                    assert (symbol_as_OT.lt u v) as i; pose (symbol_as_OT.compare_spec u v) as c; 
                    rewrite h in c; inversion c; eauto with misc; clear h c
                end.

            intros x y;
            case_eq (compare x y);
            destruct x; destruct y;
            intro h; unfold compare in h;
            constructor;
            try (reflexivity);
            try (inversion h; clear H0).

            all: repeat (match goal with
                | h:(if (negb (?g)) then _ else _) = _ |- _ =>
                    destruct_with_eqn (g)
                    ; simpl in h
                end; simpl);
                repeat eqs_True; repeat eqstr_True; repeat eqvv_True; subst.

            Ltac resolve_Eq :=
                match goal with
                | h: vpg_var_as_OT.compare ?v ?v0 = Eq |- _ =>
                    pose (vv_cmp_eq v v0 h) as e
                    ; rewrite e in *
                | h: symbol_as_OT.compare ?v ?v0 = Eq |- _ =>
                    pose (sym_cmp_eq v v0 h) as e
                    ; rewrite e in *
                | h: compare_str ?v ?v0 = Eq |- _ =>
                    pose (str_cmp_eq v v0 h) as e
                    ; rewrite e in *
                end.
            
            all: try resolve_Eq;
            unfold eq; auto.

            all: try (f_rename2 + resolveS+ resolveVV; resolveBool).


            all: repeat (match goal with
                | |- (if (negb (?g)) then _ else _) =>
                    destruct_with_eqn (g)
                    ; simpl in h
                end; simpl);
                repeat eqs_True; repeat eqstr_True; repeat eqvv_True; subst.

            all: eauto with misc.
            all: try (f_rename2 + resolveS+ resolveVV; resolveBool).

            all: try easy.

            all: try match goal with
            | h: compare_str ?t1 ?t2 = Lt |- _ =>
                apply (str_cmp_lt t1 t2 h)
            end.

            all: try discriminate.

            all: unfold compare_str in *.


            destruct (String_as_OT.compare_spec t2 t3); try discriminate; auto.
            destruct (String_as_OT.compare_spec t1 t0); try discriminate; auto.

        Qed.

    End alt_as_OT.

    Lemma alt_lt_irefl : ∀ (v:alt),
        alt_as_OT.lt v v -> False.
    Proof.
        pose (alt_as_OT.lt_strorder).
        inversion s.
        unfold Irreflexive in StrictOrder_Irreflexive.
        unfold Reflexive in StrictOrder_Irreflexive.
        intro v.
        pose (StrictOrder_Irreflexive v).
        eauto with misc.
    Qed.
    Global Hint Resolve alt_lt_irefl : misc.

    Lemma alt_lt_itrefl : ∀ (v1 v2:alt),
    alt_as_OT.lt v1 v2 ->
    alt_as_OT.lt v2 v1 ->
    False.
    Proof.
        pose (alt_as_OT.lt_strorder).
        inversion s.
        unfold Irreflexive in StrictOrder_Irreflexive.
        unfold Reflexive in StrictOrder_Irreflexive.
        intro v.
        pose (StrictOrder_Irreflexive v).
        eauto with misc.
    Qed.
    Global Hint Resolve alt_lt_irefl : misc.

    Lemma alt_lt_trans : ∀ (v1 v2 v3:alt),
        alt_as_OT.lt v1 v2 -> 
        alt_as_OT.lt v2 v3 -> 
        alt_as_OT.lt v1 v3.
    Proof.
        pose (alt_as_OT.lt_strorder).
        inversion s.
        unfold Transitive in StrictOrder_Transitive.
        eauto with misc.
    Qed.
    Global Hint Resolve alt_lt_trans : misc.

    Lemma alt_cmp_eq : ∀ t0 t1,
        alt_as_OT.compare t0 t1 = Eq ->
        t0 = t1.
    Proof.
        intros t0 t1 h.
        pose (alt_as_OT.compare_spec t0 t1) as c.
        rewrite h in c;
        inversion c.
        assert (t0 = t1); eauto with misc;
        subst; reflexivity.
    Qed.
    Global Hint Resolve alt_cmp_eq : misc.

    Lemma alt_cmp_lt : ∀ t0 t1,
        alt_as_OT.compare t0 t1 = Lt ->
        alt_as_OT.lt t0 t1.
    Proof.
        intros t0 t1 h.
        pose (alt_as_OT.compare_spec t0 t1) as c.
        rewrite h in c;
        inversion c. assumption.
    Qed.
    Global Hint Resolve alt_cmp_lt : misc.


    Lemma alt_cmp_lt' : ∀ t0 t1,
        alt_as_OT.lt t0 t1 ->
        alt_as_OT.compare t0 t1 = Lt.
    Proof.
        intros t0 t1 h.
        pose (alt_as_OT.compare_spec t0 t1) as c.
        inversion c. 
        3: {
            pose (alt_lt_itrefl _ _ h H0).
            contradiction.
        }

        assert (t0 = t1); eauto with misc; subst.
        pose (alt_lt_irefl t1 h). contradiction.

        reflexivity.
    Qed.
    Global Hint Resolve alt_cmp_lt' : misc.

    Lemma alt_lt_gt : ∀ v v0,
        alt_as_OT.compare v v0 = Gt ->
        alt_as_OT.compare v0 v = Lt.
    Proof.
        intros v v0 h.

        pose (alt_as_OT.compare_spec v0 v) as c.
        inversion c.

        assert (v0 = v); eauto with misc; subst;
        rewrite h in H; inversion H.

        reflexivity.
        
        pose (alt_cmp_lt' _ _ H0).
        rewrite e in h. inversion h.
    Qed.
    Global Hint Resolve alt_lt_gt : misc.

    (* end hide *)

    (** [rule]: a VPG rule. *)
    Definition rule := (vpg_var * alt) % type.

    (* begin hide *)

    Module rule_as_OT <: OrderedType.
        Definition t := rule.
        
        Definition eq := @eq rule.
        Local Instance eq_equiv : Equivalence eq.
        split; unfold eq.
        intros s; induction s; simpl; auto.
        eauto with misc.
        unfold Transitive. apply eq_trans.
        Qed.

        Global Hint Resolve alt_as_OT.alt_dec : misc.
        Definition rule_dec : ∀ c1 c2 : rule, {c1 = c2} + {c1 != c2}.
        Proof. decide equality; eauto with misc. Qed.
        Global Hint Resolve rule_dec : misc.

        Definition eq_dec := rule_dec.
        

        Definition lt (x y: rule) := 
            match x, y with 
            | (vpg_var, alt), (vpg_var', alt') => 
                if negb (eqvv vpg_var vpg_var') 
                then vpg_var_as_OT.lt vpg_var vpg_var'
                else alt_as_OT.lt alt alt'
            end.
        
        Global Hint Resolve vvot.eqb_eq : misc.
        Local Instance lt_strorder : StrictOrder lt.
        Proof.
            split; unfold lt.
            intros s t. 
            destruct s.
            assert (eqvv v v=true); eauto with misc.
            apply (vvot.eqb_eq v v). eauto with misc.
            rewrite H in t; simpl in t.
            pose (alt_lt_irefl _ t). contradiction.

            intros x y z h1 h2.

            destruct x. destruct y. destruct z.

            case_eq (eqvv v v0); intros h; rewrite h in h1; simpl in h1;
            case_eq (eqvv v0 v1); intros g; rewrite g in h2; simpl in h2.
            assert (v = v0); eauto with misc;
            rewrite H; rewrite g; simpl.
            apply (alt_lt_trans _ _ _ h1 h2).

            assert (v = v0); eauto with misc;
            rewrite H; rewrite g; simpl; assumption.

            assert (v0 = v1); eauto with misc.
            rewrite <- H; rewrite h; simpl; assumption.

            
            case_eq (eqvv v v1); intros w; simpl.
            assert (v = v1); eauto with misc; rewrite H in h1.
            pose (vv_lt_itrefl _ _ h1 h2). contradiction.
            apply (vv_lt_trans _ _ _ h1 h2).
        Qed.
        
        Local Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
        Proof.
            unfold Proper, eq, lt; split; 
            destruct x; destruct x0; destruct y; destruct y0;
            eauto with misc; intro h; try (contradiction); 
            inversion H; inversion H0; subst; eauto with misc.
        Qed.

        Definition compare (x y:rule) : comparison :=
            match x, y with 
            | (vpg_var, alt), (vpg_var', alt') => 
                if negb (eqvv vpg_var vpg_var') 
                then vpg_var_as_OT.compare vpg_var vpg_var'
                else alt_as_OT.compare alt alt'
            end.

        Lemma compare_spec : ∀ x y, CompSpec eq lt x y (compare x y).
        Proof.
            intros x y;
            case_eq (compare x y);
            destruct x; destruct y;
            intro h; unfold compare in h;
            constructor.

            case_eq (eqvv v v0); intros g; rewrite g in h; simpl in h.
            assert (v = v0); eauto with misc; subst.
            pose (alt_cmp_eq _ _ h); rewrite e; reflexivity.
            assert (eqvv v0 v0= true).
            apply (vvot.eqb_eq). eauto with misc.
            pose (vv_cmp_eq _ _ h). rewrite e in g.
            rewrite g in H. inversion H.

            unfold lt.

            case_eq (eqvv v v0); intros g; rewrite g in h; simpl in *.

            apply (alt_cmp_lt _ _ h).
            apply (vv_cmp_lt _ _ h).

            unfold lt.
            case_eq (eqvv v v0); intros g; rewrite g in h; simpl in *;
            case_eq (eqvv v0 v); intros w; simpl.

            pose (alt_lt_gt _ _ h).
            apply (alt_cmp_lt _ _ e).

            assert (v = v0); eauto with misc.
            rewrite H; subst; rewrite w in g; inversion g.

            assert (v0 = v); eauto with misc.
            rewrite H in g; subst; rewrite w in g; inversion g.

            pose (vv_lt_gt _ _ h).
            apply (vv_cmp_lt _ _ e).
        Qed.
    End rule_as_OT.

    Module rot := Compare2EqBool(rule_as_OT).

    (* end hide *)

    (** [rules]: a list of VPG rules (P). *)
    Definition rules : Type := list rule.

    (** [in_rules]: whether a rule is in a list of rules. *)
    Definition in_rules (r:rule):= List.In r.
End vpg.