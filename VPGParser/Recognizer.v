Require Import Coq.Lists.List.
Import ListNotations.
Require Extraction.
Require Import Arith String.
Require Import Structures.Orders.
Require Import Ltac.
From Coq Require Import MSets MSets.MSetProperties MSets.MSetEqProperties.
From Coq Require Structures.OrderedTypeEx Structures.OrdersFacts.
Require Import Coq.Classes.RelationClasses.

Require Misc.

(* Open Scope string_scope. *)

(* Extraction Misc.vpl_parsetree.PT2. *)

Module vpg_parser.
    Import Misc.Basic.
    Import Misc.vpg.
    (* Import Misc.vpl_parsetree. *)


    Definition vv : Type := (vpg_var * vpg_var) % type.

    Module vv_as_OT <: OrderedType.
        Definition t := vv.
        
        Definition eq := @eq vv.
        Instance eq_equiv : Equivalence eq.
        split; unfold eq.
        intros s; induction s; simpl; auto.
        eauto.
        unfold Transitive. apply eq_trans.
        Qed.

        Hint Resolve alt_as_OT.alt_dec : veriv.
        Hint Resolve vpg_var_as_OT.vpg_var_dec : veriv.
        Definition vv_dec : forall c1 c2 : vv, {c1 = c2} + {c1 <> c2}.
        Proof. decide equality; eauto with veriv. Qed.
        (* Hint Resolve vv_dec : core. *)

        Definition eq_dec := vv_dec.
        
        Definition lt (x y: vv) := 
            match x, y with 
            | (v1, v2), (v1', v2') => 
                if negb (eqvv v1 v1') 
                then vpg_var_as_OT.lt v1 v1'
                else vpg_var_as_OT.lt v2 v2'
            end.
        
        Hint Resolve vvot.eqb_eq : veriv.

        Instance lt_strorder : StrictOrder lt.
        Proof.
            split; unfold lt.
            intros s t. 
            destruct s.
            assert (eqvv v v=true); eauto.
            apply (vvot.eqb_eq v v). eauto.
            rewrite H in t; simpl in t.
            pose (vv_lt_irefl _ t). contradiction.

            intros x y z h1 h2.

            destruct x. destruct y. destruct z.

            case_eq (eqvv v v1); intros h; rewrite h in h1; simpl in h1;
            case_eq (eqvv v1 v3); intros g; rewrite g in h2; simpl in h2.
            assert (v = v1). apply vvot.eqb_eq. apply h.
            rewrite H; rewrite g; simpl.
            apply (vv_lt_trans _ _ _ h1 h2).

            assert (v=v1). apply vvot.eqb_eq. apply h.
            assert (eqvv v v3=false).
            rewrite <- H in g. assumption.

            rewrite H0. simpl. rewrite <- H in h2. assumption.
            
            assert (v1 = v3). apply vvot.eqb_eq. eauto.
            rewrite <- H; rewrite h; simpl; assumption.

            
            case_eq (eqvv v v3); intros w; simpl.
            assert (v = v3). apply vvot.eqb_eq. eauto. rewrite H in h1.
            pose (vv_lt_itrefl _ _ h1 h2). contradiction.
            apply (vv_lt_trans _ _ _ h1 h2).
        Qed.
        
        Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
        Proof.
            unfold Proper, eq, lt; split; 
            destruct x; destruct x0; destruct y; destruct y0;
            eauto; intro h; try (contradiction); 
            inversion H; inversion H0; subst; eauto.
        Qed.

        Definition compare (x y:vv) : comparison :=
            match x, y with 
            | (v1, v2), (v1', v2') => 
                if negb (eqvv v1 v1') 
                then vpg_var_as_OT.compare v1 v1'
                else vpg_var_as_OT.compare v2 v2'
            end.

        Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
        Proof.
            intros x y;
            case_eq (compare x y);
            destruct x; destruct y;
            intro h; unfold compare in h;
            constructor.

            case_eq (eqvv v v1); intros g; rewrite g in h; simpl in h.
            assert (v = v1). apply vvot.eqb_eq. eauto. subst.
            pose (vv_cmp_eq _ _ h); rewrite e; reflexivity.
            assert (eqvv v1 v1= true).
            apply (vvot.eqb_eq). eauto.
            pose (vv_cmp_eq _ _ h). rewrite e in g.
            rewrite g in H. inversion H.

            unfold lt.

            case_eq (eqvv v v1); intros g; rewrite g in h; simpl in *.

            apply (vv_cmp_lt _ _ h).
            apply (vv_cmp_lt _ _ h).

            unfold lt.
            case_eq (eqvv v v1); intros g; rewrite g in h; simpl in *;
            case_eq (eqvv v1 v); intros w; simpl.

            pose (vv_lt_gt _ _ h).
            apply (vv_cmp_lt _ _ e).

            assert (v = v1). apply vvot.eqb_eq. eauto.
            rewrite H; subst; rewrite w in g; inversion g.

            assert (v1 = v). apply vvot.eqb_eq. eauto.
            rewrite H in g; subst; rewrite w in g; inversion g.

            pose (vv_lt_gt _ _ h).
            apply (vv_cmp_lt _ _ e).
        Qed.
    End vv_as_OT.

    (** NOTE Build the MSet module *)
    (* NOTE S *)
    Module state := MSetList.Make vv_as_OT.

    Module wot := Compare2EqBool(vv_as_OT).
    Definition eqw := wot.eqb.

    Module p_state := WPropertiesOn vv_as_OT state.
    Module peq_state := WEqPropertiesOn vv_as_OT state.

    Lemma state_eq_trans : forall s s' s'',
        state.eq s s' ->
        state.eq s' s'' ->
        state.eq s s''.
    Proof.
        intros s s' s'' h1 h2.
        unfold state.eq in *.
        unfold state.Equal in *.
        intro.
        pose (h1 a).
        pose (h2 a).
        split;
        destruct i0;
        destruct i;
        eauto.
    Qed.

    Lemma state_eq_sym : forall s s',
        state.eq s s' ->
        state.eq s' s.
    Proof.
        intros s s' h.
        unfold state.eq in *.
        unfold state.Equal in *.
        intro.
        pose (h a).
        split;
        destruct i;
        eauto.
    Qed.

    (* Lemma rules_eq_trans : forall s s' s'',
        rules.eq s s' ->
        rules.eq s' s'' ->
        rules.eq s s''.
    Proof.
        intros s s' s'' h1 h2.
        unfold rules.eq in *.
        unfold rules.Equal in *.
        intro.
        pose (h1 a).
        pose (h2 a).
        split;
        destruct i0;
        destruct i;
        eauto.
    Qed.

    Lemma rules_eq_sym : forall s s',
        rules.eq s s' ->
        rules.eq s' s.
    Proof.
        intros s s' h.
        unfold rules.eq in *.
        unfold rules.Equal in *.
        intro.
        pose (h a).
        split;
        destruct i;
        eauto.
    Qed. *)

    (* NOTE T *)
    Definition stack : Type := list (state.t * symbol).

    Definition empty_state := state.empty.

    Definition add_state := state.add.
    Definition in_stateb := state.mem.
    Definition in_state  := state.In.

    (* Section delta_c.
        Definition fcp c u (v:vpg_var) (r:rule) (S':state.t) : state.t :=
            let (v',alt) := r in
            if eqvv v v' then 
                match alt with 
                | Alt_Linear t v' => 
                    if eqs t c then add_state (u, v') S' 
                    else S'
                | _ => S'
                end
            else S'.
        
        Lemma Proper_fcp : forall c u v, 
            Proper (eq ==> state.eq ==> state.eq) (fcp (Plain c) u v).
        Proof.
            intros c u v.
            unfold Proper.
            split; intro h.
            
            unfold state.eq in H0;
            unfold state.Equal in H0.
    
            rewrite H in h;
            unfold fcp in *;
            destruct y;
            destruct a0;
            case_eq (eqvv v v0); intro g; rewrite g in h;
            try (apply H0; assumption);
    
            case_eq (eqs t (Plain c)); intro w; rewrite w in h.
    
            apply add_state_spec.
            pose (add_state_spec x0 (u,v1) a) as i.
            destruct i.
            pose (H1 h).
            inversion o.
            eauto.
            destruct (H0 a).
            pose (H4 H3).
            eauto.
    
            apply H0; eauto.

            unfold state.eq in H0;
            unfold state.Equal in H0.
    
            rewrite <- H in h;
            unfold fcp in *;
            destruct x;
            destruct a0;
            case_eq (eqvv v v0); intro g; rewrite g in h;
            try (apply H0; assumption);
    
            case_eq (eqs t (Plain c)); intro w; rewrite w in h.
    
            apply add_state_spec.
            pose (add_state_spec y0 (u,v1) a) as i.
            destruct i.
            pose (H1 h).
            inversion o.
            eauto.
            destruct (H0 a).
            pose (H5 H3).
            eauto.
    
            apply H0; eauto.
        Qed.
    
        Lemma Trans_fcp : forall c u v,
            transpose state.eq (fcp (Plain c) u v).
        Proof.
            intros a u v.
    
            unfold transpose;
            intros x y;
            unfold fcp;
            destruct x; destruct y;
            destruct a0; destruct a1;
            case_eq (eqvv v v0); intro h2;
            eauto;
            try (intro z; apply (p_state.equal_refl));
            case_eq (eqs t (Plain a)); intros h z;
            try (

                case_eq (eqvv v v1); intro g;
                apply (p_state.equal_refl);
                
                case_eq (eqs t (Plain a)); intros h' z;
                case_eq (eqvv v v1); intro g;
                case_eq (eqs t0 (Plain a)); intro k;
                
                try (apply (p_add_state_add _));
                try (apply (p_state.equal_refl))
            ).

            case_eq (eqvv v v1); intro g;
            case_eq (eqs t0 (Plain a)); intro k;
            try (apply (p_add_state_add _));
            apply (p_state.equal_refl).
        Qed.
    
        Lemma Prop1_fcp : forall w u a,
            forall r, (
            forall i,
            state.eq
                (fcp (Plain a) u w r i)
                (state.union 
                    (fcp (Plain a) u w r empty_state)
                    i)).
        Proof.
            intros w u a r i.
            unfold fcp.
            destruct r.
            assert (state.Empty empty_state) as hemp.
            1: {
                eauto.
            }
            case_eq (eqvv w v); intro h.
    
            1: {
                destruct a0.
                
                pose (@p_state.empty_union_1 empty_state i hemp) as e.
                apply e.
                
                case_eq (eqs t (Plain a)); intro p.
                pose (p_state.singleton_equal_add (u,v0)) as e.
                (* pose (p_state.union_equal_2 ). *)
                pose (@p_state.union_equal_2 i (state.singleton (u, v0)) (add_state (u, v0) state.empty) e) as e0.
                (* pose (p_add_state_union_singleton). *)
                pose (p_add_state_union_singleton i (u, v0)) as e1.
                pose (p_state.union_sym i (state.singleton (u, v0))) as e2.
    
                pose (state_eq_trans _ _ _ e0 e2) as e3.
                pose (state_eq_sym _ _ e3) as e4.
                pose (state_eq_trans _ _ _ e1 e4) as e5.
                eauto.
    
                pose (@p_state.empty_union_1 empty_state i hemp) as e.
                apply e.
    
                pose (@p_state.empty_union_1 empty_state i hemp) as e.
                apply e.
            }
    
            pose (@p_state.empty_union_1 empty_state i hemp) as e.
            apply e.
        Qed.

        (* ANCHOR fold 1 S: one var *)
        Definition fcf a (vv: vv) (P:rules.t) S' :=
            let (u, v) := vv in
            rules.fold (fcp a u v) P S'.

        (* ANCHOR Prop f *)
        Lemma f_f_prop1 :
            forall S' P a u v b v1 v2,
            in_rules (v, Alt_Match (Call a) (Ret b) v1 v2) P ->
            in_state (v1,v1) (fcf (Call a) (u,v) P S').
        Proof.
            intros S' P a u v b v1 v2 Hinr.
            unfold fcf.

            set (f := f_p (Call a) v).

            pose (Proper_f_p a v) as H.

            pose (Trans_f_p a v) as H0.

            pose (@p_rules.remove_fold_1 state.t state.eq _ f _ H0 S' P (v, Alt_Match (Call a) (Ret b) v1 v2) Hinr) as p.
            
    End delta_c. *)
    
    Definition delta_c (P: rules) (S: state.t) (c:symbol) : state.t := 
        let fold_S (vv: vv) S' :=
            let (context_v, v) := vv in 
            let fold_P (rule: rule) (S':state.t) :=
                let (v,alt) := rule in
                    if eqvv v context_v then 
                        match alt with 
                        | Alt_Linear t' v' => 
                            if eqs t' c then add_state (context_v, v') S'
                            else S'
                        | _ => S'
                        end 
                    else S'
            in
            rules.fold fold_P P S'
        in
        state.fold fold_S S empty_state.

    (* ANCHOR fold 1 P: one rule *)
    Definition f_p a (v:vpg_var) (r:rule) (S':state.t) : state.t :=
        let (v',alt) := r in
        if eqvv v v' then 
            match alt with 
            | Alt_Match t1 t2 v1 v2 => 
                if eqs t1 a then add_state (v1, v1) S'
                else S'
            | Alt_Linear t v' => 
                if eqs t a then add_state (v', v') S' 
                else S'
            | _ => S'
            end
        else S'.

    Lemma Proper_f_p : forall a v, 
        Proper (eq ==> state.eq ==> state.eq) (f_p (Call a) v).
    Proof.
        intros a v.
        unfold Proper.
        split; intro h.
        
        unfold state.eq in H0;
        unfold state.Equal in H0.

        rewrite H in h.
        unfold f_p in *.
        destruct y;
        destruct a1;
        case_eq (eqvv v v0); intro g; rewrite g in h;
        try (apply H0; assumption).

        case_eq (eqs t (Call a)); intro w; rewrite w in h.

        apply add_state_spec.
        pose (add_state_spec x0 (v1,v1) a0) as i.
        destruct i.
        pose (H1 h).
        inversion o.
        eauto.
        destruct (H0 a0).
        pose (H4 H3).
        eauto.

        apply H0; eauto.

        case_eq (eqs t1 (Call a)); intro w; rewrite w in h.
        apply add_state_spec.
        pose (add_state_spec x0 (v1,v1) a0) as i.
        destruct i.
        pose (H1 h).
        inversion o.
        eauto.
        destruct (H0 a0).
        pose (H4 H3).
        eauto.

        apply H0; eauto.

        rewrite H.

        unfold f_p in *.
        destruct y.
        destruct a1.
        case_eq (eqvv v v0); intro g; rewrite g in h.

        apply (H0 a0); eauto.
        apply (H0 a0); eauto.

        case_eq (eqvv v v0); intro g; rewrite g in h.
        case_eq (eqs t (Call a)); intro w; rewrite w in h.

        apply add_state_spec.
        pose (add_state_spec y0 (v1,v1) a0) as i.
        destruct i.
        pose (H1 h).
        inversion o.
        eauto.
        destruct (H0 a0).
        pose (H5 H3).
        eauto.

        apply H0; eauto.
        apply H0; eauto.

        case_eq (eqvv v v0); intro g; rewrite g in h.
        case_eq (eqs t1 (Call a)); intro w; rewrite w in h.

        apply add_state_spec.
        pose (add_state_spec y0 (v1,v1) a0) as i.
        destruct i.
        pose (H1 h).
        inversion o.
        eauto.
        destruct (H0 a0).
        pose (H5 H3).
        eauto.

        apply H0; eauto.
        apply H0; eauto.
    Qed.

    Lemma Trans_f_p : forall a v,
        transpose state.eq (f_p (Call a) v).
    Proof.
        intros a v.

        unfold transpose.
        intros x y.
        unfold f_p.
        destruct x; destruct y;
        destruct a0; destruct a1;
        case_eq (eqvv v v0); intro h1;
        case_eq (eqvv v v1); intro h2;
        eauto;
        try (apply (p_state.equal_refl));
        try (
            case_eq (eqs t (Call a)); intros h z;
            apply (p_state.equal_refl (add_state (v4, v4) z)) );
        try (
            case_eq (eqs t (Call a)); intros h z;
            apply (p_state.equal_refl _) );
        intro z';
        try (
            case_eq (eqs t1 (Call a)); intros h z;
            apply (p_state.equal_refl _) );
        try (
            case_eq (eqs t (Call a)); intros;
            case_eq (eqs t0 (Call a)); intros;
            apply (p_add_state_add _)
        );
        try (

            case_eq (eqs t (Call a)); intros;
            case_eq (eqs t0 (Call a)); intros;
            try (apply (p_add_state_add _));
            try (apply (p_state.equal_refl _))
        );
        try (
            case_eq (eqs t (Call a)); intros;
            case_eq (eqs t1 (Call a)); intros;
            try (apply (p_add_state_add _));
            try (apply (p_state.equal_refl _))
        ).
        case_eq (eqs t1 (Call a)); intros;
        case_eq (eqs t0 (Call a)); intros;
        try (apply (p_add_state_add _));
        try (apply (p_state.equal_refl _)).
    
    Qed.

    Lemma Prop1_f_p : forall w a,
        forall r, (
        forall i,
        state.eq
            (f_p (Call a) w r i)
            (state.union 
                (f_p (Call a) w r empty_state)
                i)).
    Proof.
        intros w a r i.
        unfold f_p.
        destruct r.
        assert (state.Empty empty_state) as hemp.
        1: {
            eauto.
        }
        case_eq (eqvv w v); intro h.

        1: {
            destruct a0.
            
            pose (@p_state.empty_union_1 empty_state i hemp) as e.
            apply e.
            
            case_eq (eqs t (Call a)); intro p.
            pose (p_state.singleton_equal_add (v0,v0)) as e.
            (* pose (p_state.union_equal_2 ). *)
            pose (@p_state.union_equal_2 i (state.singleton (v0, v0)) (add_state (v0, v0) state.empty) e) as e0.
            (* pose (p_add_state_union_singleton). *)
            pose (p_add_state_union_singleton i (v0, v0)) as e1.
            pose (p_state.union_sym i (state.singleton (v0, v0))) as e2.

            pose (state_eq_trans _ _ _ e0 e2) as e3.
            pose (state_eq_sym _ _ e3) as e4.
            pose (state_eq_trans _ _ _ e1 e4) as e5.
            eauto.

            eauto.

            pose (@p_state.empty_union_1 empty_state i hemp) as e.
            apply e.

            case_eq (eqs t1 (Call a)); intro g.
            pose (p_state.singleton_equal_add (v1,v1)) as e.
            (* pose (p_state.union_equal_2 ). *)
            pose (@p_state.union_equal_2 i (state.singleton (v1, v1)) (add_state (v1, v1) state.empty) e) as e0.
            (* pose (p_add_state_union_singleton). *)
            pose (p_add_state_union_singleton i (v1, v1)) as e1.
            pose (p_state.union_sym i (state.singleton (v1, v1))) as e2.

            pose (state_eq_trans _ _ _ e0 e2) as e3.
            pose (state_eq_sym _ _ e3) as e4.
            pose (state_eq_trans _ _ _ e1 e4) as e5.
            eauto.

            pose (@p_state.empty_union_1 empty_state i hemp) as e.
            apply e.
        }

        pose (@p_state.empty_union_1 empty_state i hemp) as e.
        apply e.
    Qed.

    (* ANCHOR fold 1 S: one var *)
    Definition f_f a (vv: vv) (P:rules.t) S' :=
        let (_, v) := vv in
        rules.fold (f_p a v) P S'.

    (* ANCHOR Prop f *)
    Lemma f_f_prop1 :
        forall S' P a u v b v1 v2,
        in_rules (v, Alt_Match (Call a) (Ret b) v1 v2) P ->
        in_state (v1,v1) (f_f (Call a) (u,v) P S').
    Proof.
        intros S' P a u v b v1 v2 Hinr.
        unfold f_f.

        set (f := f_p (Call a) v).

        pose (Proper_f_p a v) as H.

        pose (Trans_f_p a v) as H0.

        pose (@p_rules.remove_fold_1 state.t state.eq _ f _ H0 S' P (v, Alt_Match (Call a) (Ret b) v1 v2) Hinr) as p.
        
        unfold state.eq in p.
        unfold state.Equal in p.
        apply p.

        unfold f;
        unfold f_p.

        assert (eqvv v v=true). apply (vvot.eqb_eq v v). eauto.
        rewrite H1. 
        assert (eqs (Call a) (Call a) = true). pose (sot.eqb_eq (Call a) (Call a)).
        destruct i. apply H3. eauto.
        rewrite H2. fold f.

        apply (add_state_spec). eauto.
    Qed.

    Lemma f_f_prop2 :
    forall S' P a u v v1,
    in_rules (v, Alt_Linear (Call a) v1) P ->
    in_state (v1,v1) (f_f (Call a) (u,v) P S').
    Proof.
        intros S' P a u v v1 Hinr.
        unfold f_f.

        set (f := f_p (Call a) v).

        pose (Proper_f_p a v) as H.

        pose (Trans_f_p a v) as H0.

        pose (@p_rules.remove_fold_1 state.t state.eq _ f _ H0 S' P (v, Alt_Linear (Call a) v1) Hinr) as p.
        
        unfold state.eq in p.
        unfold state.Equal in p.
        apply p.

        unfold f;
        unfold f_p.

        assert (eqvv v v=true). apply (vvot.eqb_eq v v). eauto.
        rewrite H1. 
        assert (eqs (Call a) (Call a) = true). pose (sot.eqb_eq (Call a) (Call a)).
        destruct i. apply H3. eauto.
        rewrite H2. fold f.

        apply (add_state_spec). eauto.
    Qed.

    Lemma rules_add_eq : forall e s' s'',
        rules.eq s' s'' ->
        rules.eq
        (rules.add e s')
        (rules.add e s'').
    Proof.
        intros e s' s'' h.
        unfold rules.eq.
        unfold rules.Equal.
        intro a.
        split; intro g.

        1: {
            pose (rules.add_spec s' e a).
            destruct i. pose (H g).
            destruct o. rewrite H1. 
            apply (rules.add_spec).
            eauto.

            apply (rules.add_spec s'' e a).

            unfold rules.eq in h.
            unfold rules.Equal in h.
            destruct (h a).
            pose (H2 H1).
            eauto.
        }

        rename s' into s'2.
        rename s'' into s'.
        rename s'2 into s''.


        pose (rules.add_spec s' e a).
        destruct i. pose (H g).
        destruct o. rewrite H1. 
        apply (rules.add_spec).
        eauto.

        apply (rules.add_spec s'' e a).

        unfold rules.eq in h.
        unfold rules.Equal in h.
        destruct (h a).
        pose (H3 H1).
        eauto.
    Qed.

    Lemma rules_In_eq : forall e s' s'',
        rules.eq s' s'' ->
        (rules.In e s' <->
        rules.In e s'').
    Proof.
        intros e s' s'' h.
        split; intro g.
        pose (p_rules.subset_equal h).
        pose (p_rules.in_subset g s). eauto.

        pose (p_rules.subset_equal (rules_eq_sym _ _ h)).
        pose (p_rules.in_subset g s). eauto.
    Qed.

    Lemma state_add_eq : forall e s' s'',
    state.eq s' s'' ->
    state.eq
    (add_state e s')
    (add_state e s'').
    Proof.
        intros e s' s'' h.
        unfold state.eq.
        unfold state.Equal.
        intro a.
        split; intro g.

        1: {
            pose (add_state_spec s' e a).
            destruct i. pose (H g).
            destruct o. rewrite H1. 
            apply (add_state_spec).
            eauto.

            apply (add_state_spec s'' e a).

            unfold state.eq in h.
            unfold state.Equal in h.
            destruct (h a).
            pose (H2 H1).
            eauto.
        }

        rename s' into s'2.
        rename s'' into s'.
        rename s'2 into s''.


        pose (add_state_spec s' e a).
        destruct i. pose (H g).
        destruct o. rewrite H1. 
        apply (add_state_spec).
        eauto.

        apply (add_state_spec s'' e a).

        unfold state.eq in h.
        unfold state.Equal in h.
        destruct (h a).
        pose (H3 H1).
        eauto.
    Qed.

    Lemma state_In_eq : forall e s' s'',
        state.eq s' s'' ->
        (in_state e s' <->
        in_state e s'').
    Proof.
        intros e s' s'' h.
        split; intro g.
        pose (p_state.subset_equal h).
        pose (p_in_state_subset g s). eauto.

        pose (p_state.subset_equal (state_eq_sym _ _ h)).
        pose (p_in_state_subset g s). eauto.
    Qed.

    Lemma Prop1_f_f : 
        forall rs, 
        forall r i u v a,
        ~ rules.In r rs ->
        state.eq
            (f_f (Call a) (u,v) (rules.add r rs) i)
            (state.union 
                (f_f (Call a) (u,v) rs empty_state)
                (f_p (Call a) v r i)).
    Proof.
        (* NOTE *)
        set (P := fun rs => 
            forall r i u v a,
            ~ rules.In r rs ->
            state.eq
                (f_f (Call a) (u,v) (rules.add r rs) i)
                (state.union 
                    (f_f (Call a) (u,v) rs empty_state)
                    (f_p (Call a) v r i))).

        apply (@p_rules.set_induction P).
        2: {
            intros s s' hp rx hnotin hadd.
            unfold P.
            intros r i u v a hnotin'.
         
            unfold P in hp.

            case_eq (eqr rx r); intro h.
            1: {
                pose (rot.eqb_eq rx r) as eqbeq.
                destruct eqbeq.
                pose (H h) as eq. clear H0.

                rewrite eq in hnotin.
                rewrite eq in hadd.

                pose (hadd r) as hr.
                assert (rules.In r s').
                1: {
                    apply hr.
                    eauto.
                }
                contradiction.
            }

            unfold f_f.
            pose (Trans_f_p a v) as dt.
            (* unfold transpose in dt. *)
            pose (Proper_f_p a v) as df.

            set (P' := rules.remove rx (rules.add r s')).
            pose (p_rules.fold_2).
            assert (p_rules.Add rx P' (rules.add r s')) as hadd'.
            1: {
                unfold P'.
                set (e':=rules.add r s').
                apply (p_rules.Add_Equal).

                assert (rules.In rx (rules.add r s')).
                1: {
                    pose (hadd rx) as i0.
                    destruct i0.
                    assert (rules.In rx s'); eauto.
                    pose (p_rules.in_subset).
                    assert (rules.Subset s' (rules.add r s')). 
                    1: {
                        apply (p_rules.subset_add_2).
                        apply (p_rules.subset_equal).
                        apply (p_rules.equal_refl).
                    }
                    apply (p_rules.in_subset H1 H2).
                }
                pose (p_rules.add_remove H).
                unfold e'.
                pose (rules_eq_sym _ _ e).
                eauto.
            }

            assert (~ rules.In rx P') as Hnotin. 
            1: {
                unfold P'. 
                unfold not.
                (* if remove then notin *)
                intro q.
                pose (rules.remove_spec (rules.add r s') rx rx).
                destruct i0.
                pose (H q).
                destruct a0.
                contradiction.
            }


            assert (rules.In rx (rules.add r s')) as Hin. 
            1: {
                pose (hadd rx) as i0.
                destruct i0.
                assert (rules.In rx s'); eauto.
                pose (p_rules.in_subset).
                assert (rules.Subset s' (rules.add r s')). 
                1: {
                    apply (p_rules.subset_add_2).
                    apply (p_rules.subset_equal).
                    apply (p_rules.equal_refl).
                }
                apply (p_rules.in_subset H1 H2).
            }

            (* f(S'+r,i)=p(rx, f(S'+r,i)) *)
            pose (p_rules.remove_fold_1 state.eq_equiv df dt i Hin) as _start_goal.
            pose (state_eq_sym _ _ _start_goal) as start_goal.

            pose (Prop1_f_p v a rx (rules.fold (f_p (Call a) v) (rules.remove rx (rules.add r s')) i)) as mid2.

            pose (state_eq_trans _ _ _  start_goal mid2) as mid3.

            unfold f_f in *.
            assert (~rules.In r s) as H.
            1: {
              unfold not; intro H.
              assert (rules.In r s').
              apply (p_rules.in_subset H).
              assert (rules.Subset s s).
              apply (p_rules.subset_refl).
              pose (p_rules.subset_add_2 rx H0).
              pose (p_rules.Add_Equal rx s s') as q.
              destruct q. pose (H1 hadd).
              pose (p_rules.subset_equal (rules_eq_sym _ _ e)).
              apply (p_rules.subset_trans s0 s1).
              contradiction.
            }
            
            assert (rules.eq (rules.add r s) (rules.remove rx (rules.add r s'))) as mid4.
            1: {
              pose (p_rules.Add_Equal rx s s') as q.
              destruct q. pose (H0 hadd).
              pose (p_rules.add_add s r rx).

              pose (rules_add_eq r s' (rules.add rx s) e).
              pose (rules_eq_trans _ _ _ e1 e0).

              pose (p_rules.Equal_remove rx e2).
              
              assert (~rules.In rx (rules.add r s)) as Hnotin'.
              1: {
                unfold not; intro m.

                pose (rules.add_spec s r rx).
                destruct i0.
                pose (H2 m).
                destruct o. 
                rewrite H4 in h.
                pose (rot.eqb_eq r r).
                assert (rot.eqb r r = true).
                apply i0.
                eauto. 
                unfold eqr in h.
                rewrite H5 in h.
                inversion h.
                contradiction.
            }

            pose (p_rules.remove_add Hnotin').

            pose (rules_eq_trans _ _ _ e3 e4).

            apply (rules_eq_sym _ _ e5).
            }


            pose (rules_eq_sym _ _ mid4) as mid4'.
            pose (p_rules.fold_equal state.eq_equiv df dt i mid4') as feq.

            pose (p_state.union_equal_2 (f_p (Call a) v rx empty_state) feq) as eq'.
            unfold f_f in eq'.

            pose (state_eq_trans _ _ _ mid3 eq') as mid5.

            assert (~rules.In r s) as H'.
            (* NOTE Just a copy from the above; should be removed *)
            1: {
            unfold not; intro H'.
            assert (rules.In r s').
            apply (p_rules.in_subset H').
            assert (rules.Subset s s).
            apply (p_rules.subset_refl).
            pose (p_rules.subset_add_2 rx H0).
            pose (p_rules.Add_Equal rx s s') as q.
            destruct q. pose (H1 hadd).
            pose (p_rules.subset_equal (rules_eq_sym _ _ e)).
            apply (p_rules.subset_trans s0 s1).
            contradiction.
            }

            pose (hp r i u v a H') as ind.
            pose (p_state.union_equal_2 (f_p (Call a) v rx empty_state) ind) as eq.

            pose (state_eq_trans _ _ _ mid5 eq) as mid6.


            pose (p_state.union_sym (f_p (Call a) v rx empty_state) (state.union (rules.fold (f_p (Call a) v) s empty_state)
            (f_p (Call a) v r i))) as union_sym.

            pose (state_eq_trans _ _ _ mid6 union_sym) as mid7.

            pose (p_state.union_sym (rules.fold (f_p (Call a) v) s empty_state)
            (f_p (Call a) v r i)) as sym2.

            pose (p_state.union_equal_1 (f_p (Call a) v rx empty_state) sym2) as sym2'.

            pose (state_eq_trans _ _ _ mid7 sym2') as mid8.


            pose (p_state.union_assoc 
            (f_p (Call a) v r i)
            (rules.fold (f_p (Call a) v) s empty_state)
            (f_p (Call a) v rx empty_state)
            ) as mid_assc.
            pose (state_eq_trans _ _ _ mid8 mid_assc) as mid9.

            pose (hp rx empty_state u v a hnotin) as ind'.

            pose (state_eq_sym _ _ ind') as sym.

            pose (p_state.union_equal_2 (f_p (Call a) v r i) sym) as mid10. 

            pose (state_eq_trans _ _ _ mid9 mid10).

            assert (rules.eq (rules.add rx s) s') as eqrxss.
            1: {
                pose (p_rules.Add_Equal rx s s').
                destruct i0.
                pose (H0 hadd).
                apply (rules_eq_sym _ _ e0).
            }

            pose (p_rules.fold_equal state.eq_equiv df dt empty_state eqrxss) as eqeq.

            pose (p_state.union_equal_2 (f_p (Call a) v r i) eqeq) as mid_eq.

            pose (state_eq_trans _ _ _ e mid_eq) as mid11.

            pose (p_state.union_sym  (f_p (Call a) v r i)
            (rules.fold (f_p (Call a) v) s' empty_state)) as sym3.

            pose (state_eq_trans _ _ _ mid11 sym3).

            assumption.
        }

        (* the empty case *)
        unfold P.
        intros s hemp r i u v a hin.
        unfold f_f.

        assert (rules.eq s rules.empty).
        1: {
            apply (p_rules.empty_is_empty_1 hemp).
        }

        pose (p_rules.fold_empty (f_p (Call a) v) empty_state).
        pose (Trans_f_p a v) as dt.
        (* unfold transpose in dt. *)
        pose (Proper_f_p a v) as df.
        pose (p_rules.fold_equal state.eq_equiv df dt empty_state H) as goal_eq.
        rewrite e in goal_eq.
        rewrite goal_eq.

        assert (state.Empty empty_state) as semp. eauto.
        pose (p_state.empty_union_1 (f_p (Call a) v r i) semp) as unionemp.
        rewrite unionemp.

        pose (rules_add_eq r s rules.empty H) as eq.

        pose (p_rules.fold_add state.eq_equiv df dt i hin) as fadd.

        pose (p_rules.fold_equal state.eq_equiv df dt i H) as feq.

        pose (p_rules.fold_empty (f_p (Call a) v) i) as eqi.
        rewrite eqi in feq.

        (* NOTE can rewrite eq *)
        rewrite feq in fadd.
        assumption.
    Qed.

    Lemma Prop2_f_f : forall w a P i,
        state.eq
            (f_f (Call a) w P i)
            (state.union 
                (f_f (Call a) w P empty_state)
                i).
    Proof.
        intros w a P i.

        Check rules.eq.
        unfold f_f; destruct w.
        set (f:=(f_p (Call a) v0)).
        case_eq (rules.is_empty P); intro h.
        pose (rules.is_empty_spec P) as ise; destruct ise.
        pose (H h).
        pose (p_rules.fold_empty f empty_state).
        pose (p_rules.empty_is_empty_1 e).

        pose (Trans_f_p a v0) as dt.
        (* unfold transpose in dt. *)
        pose (Proper_f_p a v0) as df.
        
        pose (p_rules.fold_equal state.eq_equiv df dt empty_state e1) as feq.
        unfold f in e0.
        rewrite e0 in feq.

        pose (p_rules.fold_equal state.eq_equiv df dt i e1) as feq'.
        unfold f.
        rewrite feq'. 
        pose (p_rules.fold_empty f i).
        unfold f in e2.
        rewrite e2.
        rewrite feq.

        (* NOTE just a copy from above *)
        assert (state.Empty empty_state) as hemp.
        1: {
            eauto.
        }

        pose (p_state.empty_union_1 i hemp).
        rewrite e3.

        eauto.

        pose (peq_rules.choose_mem_3 P h).
        inversion s.
        destruct H.
        pose (peq_rules.add_equal P x H0).

        pose (rules.equal_spec (rules.add x P) P).
        destruct i0.
        pose (H1 e).

        set (S := rules.remove x (rules.add x P)).
        assert (~rules.In x S).
        1: {
            pose (rules.remove_spec (rules.add x P) x x).
            unfold not; intro g.
            destruct i0.
            pose (H3 g).
            destruct a0.
            contradiction.
        }

        pose (Prop1_f_f S x i v0 v0 a H3) as e1.
        unfold f_f in e1.

        (* NOTE add remove equal *)
        assert (rules.eq (rules.add x S) P).
        1: {
            unfold S.
            (* NOTE x in add x *)
            assert (rules.In x (rules.add x P)).
            1: {
                apply (rules.add_spec P x x).
                eauto.
            }
            pose (p_rules.add_remove H4).
            rewrite e2.
            eauto.
        }

        pose (Trans_f_p a v0) as dt.
        (* unfold transpose in dt. *)
        pose (Proper_f_p a v0) as df.
        
        pose (p_rules.fold_equal state.eq_equiv df dt i H4) as feq.

        rewrite feq in e1.

        unfold f.

        (* expand e1 *)

        pose (Prop1_f_p v0 a x i).
        rewrite e2 in e1.

        (* rearrange e1 *)

        pose (p_state.union_assoc (rules.fold (f_p (Call a) v0) S empty_state)
        (f_p (Call a) v0 x empty_state) i) as assc.
        rewrite <- assc in e1.

        clear assc e2.

        pose (Prop1_f_f S x empty_state v0 v0 a H3) as e2.
        unfold f_f in e2.
        rewrite <- e2 in e1.
        clear e2.

        pose (p_rules.fold_equal state.eq_equiv df dt empty_state H4) as feq'.
        rewrite feq' in e1.
        assumption.
    Qed.

    (* ANCHOR fold S *)
    Definition delta_a (P: rules.t) (S: state.t) (a:symbol) : state.t :=
        state.fold (flip (f_f a) P) S empty_state.

    (* Lemma fold_trans : forall f s s' i,
        Proper (eq ==> state.eq ==> state.eq) f ->
        transpose state.eq f ->
        state.eq (rules.fold f s' (rules.fold f s i))
        (rules.fold f s (rules.fold f s' i)).
    Proof.
        intros f s s' i fp ft.

        pose (@p_rules.fold_union_inter state.t state.eq _ f fp ft i s s') as p.
        pose (state_eq_sym _ _ p) as p'.

        pose (p_rules.union_sym s s') as u1.

        pose (p_rules.fold_equal state.eq_equiv fp ft (rules.fold f (rules.inter s s') i) u1) as pu.

        pose (state_eq_trans _ _ _ p' pu) as p1.

        pose (p_rules.inter_sym s s') as i1. 

        pose (p_rules.fold_equal state.eq_equiv fp ft i i1) as pi.

        pose (p_rules.fold_init fp (rules.union s' s) pi) as p3.

        pose (state_eq_trans _ _ _ p1 p3) as p4.

        pose (@p_rules.fold_union_inter state.t state.eq _ f fp ft i s' s) as q.

        pose (state_eq_trans _ _ _ p4 q) as q2.
        pose (state_eq_sym _ _ q2). assumption.

    Qed. *)

    (* ANCHOR delta *)
    Lemma delta_a_prop1 :
        forall S P a u v b v1 v2,
        in_state (u,v) S ->
        in_rules (v, Alt_Match (Call a) (Ret b) v1 v2) P ->
        in_state (v1,v1) (delta_a P S (Call a)).
    Proof.
        intros S P a u v b v1 v2 hinS hinP.
        unfold delta_a.

        (* Definition flip' {A B C D} (f : A -> B -> C -> D) P vv S := f vv P S. *)
        
        set (f := flip (f_f (Call a)) P).

        pose (f_f_prop1 empty_state P a u v b v1 v2 hinP).

        assert (Proper (eq ==> state.eq ==> state.eq) f) as  fp.
        1: {
            unfold Proper.
            split; intro h;
            unfold f in *;
            unfold flip in *;
            unfold f_f in *.
            rewrite <- H;
            destruct x.

            pose (Proper_f_p a v3) as df.

            pose (p_rules.fold_init df P H0).
            apply e. assumption.

            rewrite H; destruct y.
            pose (Proper_f_p a v3) as df.

            pose (p_rules.fold_init df P H0).
            apply e. assumption.
        }

        assert (transpose state.eq f) as ft.
        1: {
            unfold transpose.
            intros x y z.
            
            unfold f; unfold flip.
            
            pose (Prop2_f_f x a P (f_f (Call a) y P z)) as e.
            rewrite e.

            pose (Prop2_f_f y a P z) as e1.
            rewrite e1.

            clear e e1.
            pose (Prop2_f_f y a P (f_f (Call a) x P z)) as e.
            rewrite e.

            pose (Prop2_f_f x a P z) as e1.
            rewrite e1.
            
            clear e e1.
            pose (p_state.union_assoc (f_f (Call a) x P empty_state)
            (f_f (Call a) y P empty_state) z) as e.

            rewrite <- e.

            pose (p_state.union_sym (f_f (Call a) x P empty_state)
            (f_f (Call a) y P empty_state)) as e1.
            rewrite e1.

            pose (p_state.union_assoc (f_f (Call a) y P empty_state)
            (f_f (Call a) x P empty_state) z).

            rewrite e0.

            apply (p_state.equal_refl).

        }

        pose (@p_state.remove_fold_1 state.t state.eq _ f _ ft empty_state S (u,v) hinS) as p.
        rewrite <- p.

        unfold f; unfold flip.
        pose (Prop2_f_f (u,v) a P (state.fold (fun y : vv => f_f (Call a) y P) 
        (state.remove (u, v) S) empty_state)).
        rewrite e.

        assert (in_state (v1, v1) (f_f (Call a) (u, v) P empty_state)).
        1: {
            pose (f_f_prop1 empty_state P a u v b v1 v2 hinP).
            assumption.
        }

        pose (@p_state.union_subset_1 (f_f (Call a) (u, v) P empty_state)  (state.fold (fun y : vv => f_f (Call a) y P) 
        (state.remove (u, v) S) empty_state)).

        pose (p_in_state_subset H s).
        assumption.
    Qed.

    Lemma delta_a_prop2 :
        forall S P a u v v1,
        in_state (u,v) S ->
        in_rules (v, Alt_Linear (Call a) v1) P ->
        in_state (v1,v1) (delta_a P S (Call a)).
    Proof.
        intros S P a u v v1 hinS hinP.
        unfold delta_a.

        (* Definition flip' {A B C D} (f : A -> B -> C -> D) P vv S := f vv P S. *)
        
        set (f := flip (f_f (Call a)) P).

        pose (f_f_prop2 empty_state P a u v v1 hinP).

        assert (Proper (eq ==> state.eq ==> state.eq) f) as  fp.
        1: {
            unfold Proper.
            split; intro h;
            unfold f in *;
            unfold flip in *;
            unfold f_f in *.
            rewrite <- H;
            destruct x.

            pose (Proper_f_p a v2) as df.

            pose (p_rules.fold_init df P H0).
            apply e. assumption.

            rewrite H; destruct y.
            pose (Proper_f_p a v2) as df.

            pose (p_rules.fold_init df P H0).
            apply e. assumption.
        }

        assert (transpose state.eq f) as ft.
        1: {
            unfold transpose.
            intros x y z.
            
            unfold f; unfold flip.
            
            pose (Prop2_f_f x a P (f_f (Call a) y P z)) as e.
            rewrite e.

            pose (Prop2_f_f y a P z) as e1.
            rewrite e1.

            clear e e1.
            pose (Prop2_f_f y a P (f_f (Call a) x P z)) as e.
            rewrite e.

            pose (Prop2_f_f x a P z) as e1.
            rewrite e1.
            
            clear e e1.
            pose (p_state.union_assoc (f_f (Call a) x P empty_state)
            (f_f (Call a) y P empty_state) z) as e.

            rewrite <- e.

            pose (p_state.union_sym (f_f (Call a) x P empty_state)
            (f_f (Call a) y P empty_state)) as e1.
            rewrite e1.

            pose (p_state.union_assoc (f_f (Call a) y P empty_state)
            (f_f (Call a) x P empty_state) z).

            rewrite e0.

            apply (p_state.equal_refl).

        }

        pose (@p_state.remove_fold_1 state.t state.eq _ f _ ft empty_state S (u,v) hinS) as p.
        rewrite <- p.

        unfold f; unfold flip.
        pose (Prop2_f_f (u,v) a P (state.fold (fun y : vv => f_f (Call a) y P) 
        (state.remove (u, v) S) empty_state)).
        rewrite e.

        assert (in_state (v1, v1) (f_f (Call a) (u, v) P empty_state)).
        1: {
            pose (f_f_prop2 empty_state P a u v v1 hinP).
            assumption.
        }

        pose (@p_state.union_subset_1 (f_f (Call a) (u, v) P empty_state)  (state.fold (fun y : vv => f_f (Call a) y P) 
        (state.remove (u, v) S) empty_state)).

        pose (p_in_state_subset H s).
        assumption.
    Qed.

    Definition is_eps_v P v := 
        rules.mem (v, Alt_Epsilon) P.

    Definition has_eps_state (P:rules.t) S := 
        let has_eps (vv: vv) : bool :=
            let (_, v) := vv in 
            let f r :=
                match r with
                | (v', Alt_Epsilon) => eqvv v' v
                | _ => false 
                end
            in
            rules.exists_ f P
        in
        state.exists_ has_eps S.

    Section delta_b.

        Definition fbp u v a b v1 (r':rule) (i:state.t) := 
            match r' with
            | (v', Alt_Match a' b' v1' v2) =>
                if (eqvv v v') && (eqvv v1 v1') &&
                    (eqs a a') && (eqs b b')
                then add_state (u, v2) i
                else i
            | _ => i
            end.
        
        Lemma Proper_fbp : forall u v a b v1 , 
        Proper (eq ==> state.eq ==> state.eq) (fbp u v (Call a) (Ret b) v1).
        Proof.
            intros u v a b v1.
            unfold Proper.
            split; intro h;
            
            unfold state.eq in H0;
            unfold state.Equal in H0.

            rewrite H in h.
            unfold fbp in *.

            destruct y;
            destruct a1;
            destruct (H0 a0).
            pose (H1 h); assumption.
            pose (H1 h); assumption. 

            destruct (eqvv v v0 && eqvv v1 v2 && eqs (Call a) t1 && eqs (Ret b) t2).
            pose (state_add_eq (u,v3) x0 y0 H0) as e.
            rewrite <- e. assumption.

            pose (H1 h). assumption.
            
            destruct (H0 a0).

            unfold fbp in *;
            destruct y;
            destruct x;
            destruct a1;
            destruct a2;
            try (pose (H2 h); assumption);
            try (inversion H).
            subst.

            destruct (eqvv v v0 && eqvv v1 v3 && eqs (Call a) t1 &&
            eqs (Ret b) t2).

            pose (state_add_eq (u,v4) x0 y0 H0).
            rewrite e. assumption.
            pose (state_In_eq a0 x0 y0 H0).
            rewrite i. assumption.
        Qed.

        Lemma Trans_fbp : forall u v a b v1, 
            transpose state.eq (fbp u v (Call a) (Ret b) v1).
        Proof.
            intros u v a b v1.

            unfold transpose.
            intros x y.
            unfold fbp.
            destruct x; destruct y.
            destruct a0; destruct a1;
            (* case_eq (eqvv v v0); intro h1; *)
            (* case_eq (eqvv v v1); intro h2; *)
            try (apply (p_state.equal_refl));
            try (
                intro z;
                apply (p_state.equal_refl)
            ).

            Ltac eqeq :=
                match goal with 
                | h : eqvv ?x ?y = true |- _ => 
                    assert (x=y) as H by (apply vvot.eqb_eq; assumption); rewrite H; clear h H
                end.

            Ltac eqeqs :=
                match goal with 
                | h : eqs ?x ?y = true |- _ => 
                    assert (x=y) as H by (apply sot.eqb_eq; assumption); rewrite H; clear h H
                end.

            case_eq (eqvv v0 v2); intro h1.
            case_eq (eqvv v3 v5); intro h2.
            repeat eqeq.
            case_eq (eqs t1 t0); intro h1.
            case_eq (eqs t2 t3); intro h2.
            repeat eqeqs.

            destruct (eqvv v v2 && eqvv v1 v5 && eqs (Call a) t0 && eqs (Ret b) t3). intro z.
            pose (p_add_state_add z (u, v4) (u, v6)) as e.
            rewrite e. clear e. 
            apply (p_state.equal_refl).
            apply (p_state.equal_refl).
            intro z.

            repeat eqeqs.

            destruct (eqvv v v2 && eqvv v1 v5 && eqs (Call a) t0 && eqs (Ret b) t2).
            destruct (eqvv v v2 && eqvv v1 v5 && eqs (Call a) t0 && eqs (Ret b) t3).

            pose (p_add_state_add z (u, v4) (u, v6)) as e.
            rewrite e. clear e. 
            apply (p_state.equal_refl).
            apply (p_state.equal_refl).

            apply (p_state.equal_refl).

            intro z.

            destruct (eqvv v v2 && eqvv v1 v5 && eqs (Call a) t1 && eqs (Ret b) t2).
            destruct (eqvv v v2 && eqvv v1 v5 && eqs (Call a) t0 && eqs (Ret b) t3).
            pose (p_add_state_add z (u, v4) (u, v6)) as e.
            rewrite e. clear e. 
            apply (p_state.equal_refl).
            apply (p_state.equal_refl).

            apply (p_state.equal_refl).

            intro z.

            destruct (eqvv v v0 && eqvv v1 v3 && eqs (Call a) t1 && eqs (Ret b) t2).
            destruct (eqvv v v2 && eqvv v1 v5 && eqs (Call a) t0 && eqs (Ret b) t3).
            pose (p_add_state_add z (u, v4) (u, v6)) as e.
            rewrite e. clear e. 
            apply (p_state.equal_refl).
            apply (p_state.equal_refl).

            apply (p_state.equal_refl).

            intro z.

            destruct (eqvv v v0 && eqvv v1 v3 && eqs (Call a) t1 && eqs (Ret b) t2).
            destruct (eqvv v v2 && eqvv v1 v5 && eqs (Call a) t0 && eqs (Ret b) t3).
            pose (p_add_state_add z (u, v4) (u, v6)) as e.
            rewrite e. clear e. 
            apply (p_state.equal_refl).
            apply (p_state.equal_refl).

            apply (p_state.equal_refl).
        Qed.

        Lemma Prop_fbp : forall u v a b v1 r' i,
            state.eq 
                (fbp u v a b v1 r' i)
                (state.union (fbp u v a b v1 r' empty_state) i).
        Proof.
            intros u v a b v1 r' i.
            unfold fbp.
            destruct r'.
            destruct a0;

            try (
                assert (state.Empty empty_state) as hemp;
                eauto;
                pose (@p_state.empty_union_1 empty_state i hemp) as e; rewrite e;eauto
            ).

            destruct (eqvv v v0 && eqvv v1 v2 && eqs a t1 && eqs b t2).
            
            (* NOTE separate it as a lemma: v+i=(v+empty)+i *)
            pose (p_state.singleton_equal_add (u, v3)) as e.
            (* pose (p_state.union_equal_2 ). *)
            pose (@p_state.union_equal_2 i (state.singleton (u, v3)) (add_state (u, v3) state.empty) e) as e0.
            (* pose (p_add_state_union_singleton). *)
            pose (p_add_state_union_singleton i (u, v3)) as e1.
            pose (p_state.union_sym i (state.singleton (u, v3))) as e2.

            pose (state_eq_trans _ _ _ e0 e2) as e3.
            pose (state_eq_sym _ _ e3) as e4.
            pose (state_eq_trans _ _ _ e1 e4) as e5.
            eauto.

            assert (state.Empty empty_state) as hemp;
            eauto;
            pose (@p_state.empty_union_1 empty_state i hemp) as e'; rewrite e';eauto.

        Qed.

        Definition fbf rs v1 a b (vv:state.elt) i := 
            let (u, v) := vv in
            rules.fold (fbp u v a b v1) rs i.

        Lemma Prop_fbf :
            forall S' P v a b u v1 v2,
            in_rules (v, Alt_Match (Call a) (Ret b) v1 v2) P ->
            in_state (u,v2) (fbf P v1 (Call a) (Ret b) (u,v) S').
        Proof.
            intros S' P v a b u v1 v2 Hinr.
            unfold fbf.
    
            
            pose (Proper_fbp u v a b v1) as H.
            pose (Trans_fbp u v a b v1) as H0.

            (* set (f := fbp v (Call a) (Ret b) u v1). *)
    
            pose (@p_rules.remove_fold_1 state.t state.eq _ (fbp u v (Call a) (Ret b) v1) _ H0 S' P (v, Alt_Match (Call a) (Ret b) v1 v2) Hinr) as p.
            
            apply p.
    
            (* unfold f; *)
            unfold fbp.
    
            assert (eqvv v v=true). apply (vvot.eqb_eq v v). eauto. rewrite H1. clear H1.
            assert (eqvv v1 v1=true). apply (vvot.eqb_eq v1 v1). eauto. rewrite H1. clear H1.
            
            assert (eqs (Call a) (Call a) = true). pose (sot.eqb_eq (Call a) (Call a)).
            destruct i. apply H2. eauto.
            rewrite H1. clear H1.
            assert (eqs (Ret b) (Ret b) = true). pose (sot.eqb_eq (Ret b) (Ret b)).
            destruct i. apply H2. eauto.
            rewrite H1. 
            (* fold f. *)
    
            apply (add_state_spec). eauto.
        Qed.

        Lemma Prop1_fbf : forall rs v a b u v1 r i,
            ~ rules.In r rs ->
            state.eq 
                (fbf (rules.add r rs) v1 (Call a) (Ret b) (u,v) i)
                (state.union 
                    (fbf rs v1 (Call a) (Ret b) (u,v) empty_state) 
                    (fbp u v (Call a) (Ret b) v1 r i)).
        Proof.
            set (P := fun rs => 
            forall v a b u v1 r i,
            ~ rules.In r rs ->
            state.eq 
                (fbf (rules.add r rs) v1 (Call a) (Ret b) (u,v) i)
                (state.union 
                    (fbf rs v1 (Call a) (Ret b) (u,v) empty_state) 
                    (fbp u v (Call a) (Ret b) v1 r i))).

            apply (@p_rules.set_induction P).

            2: {
                intros s s' hp rx hnotin hadd.
                unfold P.
                intros v a b u v1 r i hnotin'.
             
                unfold P in hp.
                case_eq (eqr rx r); intro h.
                1: {
                    pose (rot.eqb_eq rx r) as eqbeq.
                    destruct eqbeq.
                    pose (H h) as eq. clear H0.
    
                    rewrite eq in hnotin.
                    rewrite eq in hadd.
    
                    pose (hadd r) as hr.
                    assert (rules.In r s').
                    1: {
                        apply hr.
                        eauto.
                    }
                    contradiction.
                }

                unfold fbf.
                pose (Trans_fbp u v a b v1) as dt.
                (* unfold transpose in dt. *)
                pose (Proper_fbp u v a b v1) as df.

                set (P' := rules.remove rx (rules.add r s')).
                pose (p_rules.fold_2).
                assert (p_rules.Add rx P' (rules.add r s')) as hadd'.
                1: {
                    unfold P'.
                    set (e':=rules.add r s').
                    apply (p_rules.Add_Equal).

                    assert (rules.In rx (rules.add r s')).
                    1: {
                        pose (hadd rx) as i0.
                        destruct i0.
                        assert (rules.In rx s'); eauto.
                        pose (p_rules.in_subset).
                        assert (rules.Subset s' (rules.add r s')). 
                        1: {
                            apply (p_rules.subset_add_2).
                            apply (p_rules.subset_equal).
                            apply (p_rules.equal_refl).
                        }
                        apply (p_rules.in_subset H1 H2).
                    }
                    pose (p_rules.add_remove H).
                    unfold e'.
                    pose (rules_eq_sym _ _ e).
                    eauto.
                }

                assert (~ rules.In rx P') as Hnotin. 
                1: {
                    unfold P'. 
                    unfold not.
                    (* if remove then notin *)
                    intro q.
                    pose (rules.remove_spec (rules.add r s') rx rx).
                    destruct i0.
                    pose (H q).
                    destruct a0.
                    contradiction.
                }

                assert (rules.In rx (rules.add r s')) as Hin. 
                1: {
                    pose (hadd rx) as i0.
                    destruct i0.
                    assert (rules.In rx s'); eauto.
                    pose (p_rules.in_subset).
                    assert (rules.Subset s' (rules.add r s')). 
                    1: {
                        apply (p_rules.subset_add_2).
                        apply (p_rules.subset_equal).
                        apply (p_rules.equal_refl).
                    }
                    apply (p_rules.in_subset H1 H2).
                }

                (* f(S'+r,i)=p(rx, f(S'+r,i)) *)
                pose (p_rules.remove_fold_1 state.eq_equiv df dt i Hin) as _start_goal.
                pose (state_eq_sym _ _ _start_goal) as start_goal.

                pose (Prop_fbp u v (Call a) (Ret b) v1 rx  (rules.fold (fbp u v (Call a) (Ret b) v1)
                (rules.remove rx (rules.add r s')) i)) as mid2.

                pose (state_eq_trans _ _ _  start_goal mid2) as mid3.

                unfold fbf in *.
                assert (~rules.In r s) as H.
                1: {
                  unfold not; intro H.
                  assert (rules.In r s').
                  apply (p_rules.in_subset H).
                  assert (rules.Subset s s).
                  apply (p_rules.subset_refl).
                  pose (p_rules.subset_add_2 rx H0).
                  pose (p_rules.Add_Equal rx s s') as q.
                  destruct q. pose (H1 hadd).
                  pose (p_rules.subset_equal (rules_eq_sym _ _ e)).
                  apply (p_rules.subset_trans s0 s1).
                  contradiction.
                }

                assert (rules.eq (rules.add r s) (rules.remove rx (rules.add r s'))) as mid4.
                1: {
                  pose (p_rules.Add_Equal rx s s') as q.
                  destruct q. pose (H0 hadd).
                  pose (p_rules.add_add s r rx).
    
                  pose (rules_add_eq r s' (rules.add rx s) e).
                  pose (rules_eq_trans _ _ _ e1 e0).
    
                  pose (p_rules.Equal_remove rx e2).
                  
                  assert (~rules.In rx (rules.add r s)) as Hnotin'.
                  1: {
                    unfold not; intro m.
    
                    pose (rules.add_spec s r rx).
                    destruct i0.
                    pose (H2 m).
                    destruct o. 
                    rewrite H4 in h.
                    pose (rot.eqb_eq r r).
                    assert (rot.eqb r r = true).
                    apply i0.
                    eauto. 
                    unfold eqr in h.
                    rewrite H5 in h.
                    inversion h.
                    contradiction.
                }
    
                pose (p_rules.remove_add Hnotin').
    
                pose (rules_eq_trans _ _ _ e3 e4).
    
                apply (rules_eq_sym _ _ e5).
                }
    
    
                pose (rules_eq_sym _ _ mid4) as mid4'.
                pose (p_rules.fold_equal state.eq_equiv df dt i mid4') as feq.
    
                pose (p_state.union_equal_2 (fbp u v (Call a) (Ret b) v1 rx empty_state) feq) as eq'.
                unfold fbf in eq'.
    
                pose (state_eq_trans _ _ _ mid3 eq') as mid5.
    
                assert (~rules.In r s) as H'.
                (* NOTE Just a copy from the above; should be removed *)
                1: {
                unfold not; intro H'.
                assert (rules.In r s').
                apply (p_rules.in_subset H').
                assert (rules.Subset s s).
                apply (p_rules.subset_refl).
                pose (p_rules.subset_add_2 rx H0).
                pose (p_rules.Add_Equal rx s s') as q.
                destruct q. pose (H1 hadd).
                pose (p_rules.subset_equal (rules_eq_sym _ _ e)).
                apply (p_rules.subset_trans s0 s1).
                contradiction.
                }
    
                pose (hp v a b u v1 r i H') as ind.
                pose (p_state.union_equal_2 (fbp u v (Call a) (Ret b) v1 rx empty_state) ind) as eq.
    
                pose (state_eq_trans _ _ _ mid5 eq) as mid6.
    
    
                pose (p_state.union_sym (fbp u v (Call a) (Ret b) v1 rx empty_state) (state.union (rules.fold (fbp u v (Call a) (Ret b) v1 ) s empty_state)
                (fbp u v (Call a) (Ret b) v1  r i))) as union_sym.
    
                pose (state_eq_trans _ _ _ mid6 union_sym) as mid7.
    
                pose (p_state.union_sym (rules.fold (fbp u v (Call a) (Ret b) v1) s empty_state)
                (fbp u v (Call a) (Ret b) v1 r i)) as sym2.
    
                pose (p_state.union_equal_1 (fbp u v (Call a) (Ret b) v1 rx empty_state) sym2) as sym2'.
    
                pose (state_eq_trans _ _ _ mid7 sym2') as mid8.
    
    
                pose (p_state.union_assoc 
                (fbp u v (Call a) (Ret b) v1 r i)
                (rules.fold (fbp u v (Call a) (Ret b) v1) s empty_state)
                (fbp u v (Call a) (Ret b) v1 rx empty_state)) as mid_assc.
                pose (state_eq_trans _ _ _ mid8 mid_assc) as mid9.
    
                pose (hp v a b u v1 rx empty_state hnotin) as ind'.
    
                pose (state_eq_sym _ _ ind') as sym.
    
                pose (p_state.union_equal_2 (fbp u v (Call a) (Ret b) v1 r i) sym) as mid10. 
    
                pose (state_eq_trans _ _ _ mid9 mid10).
    
                assert (rules.eq (rules.add rx s) s') as eqrxss.
                1: {
                    pose (p_rules.Add_Equal rx s s').
                    destruct i0.
                    pose (H0 hadd).
                    apply (rules_eq_sym _ _ e0).
                }
    
                pose (p_rules.fold_equal state.eq_equiv df dt empty_state eqrxss) as eqeq.
    
                pose (p_state.union_equal_2 (fbp u v (Call a) (Ret b) v1 r i) eqeq) as mid_eq.
    
                pose (state_eq_trans _ _ _ e mid_eq) as mid11.
    
                pose (p_state.union_sym
                (fbp u v (Call a) (Ret b) v1 r i)
                (rules.fold (fbp u v (Call a) (Ret b) v1) s' empty_state) ) as sym3.
    
                pose (state_eq_trans _ _ _ mid11 sym3).
    
                assumption.
            }

            (* the empty case *)
            unfold P.
            intros s hemp v a b u v1 r i hnotin.
            unfold fbf.

            assert (rules.eq s rules.empty).
            1: {
                apply (p_rules.empty_is_empty_1 hemp).
            }

            pose (p_rules.fold_empty (fbp u v (Call a) (Ret b) v1) empty_state).
            pose (Trans_fbp u v a b v1) as dt.
            (* unfold transpose in dt. *)
            pose (Proper_fbp u v a b v1) as df.
            pose (p_rules.fold_equal state.eq_equiv df dt empty_state H) as goal_eq.
            rewrite e in goal_eq.
            rewrite goal_eq.

            assert (state.Empty empty_state) as semp. eauto.
            pose (p_state.empty_union_1 (fbp u v (Call a) (Ret b) v1 r i) semp) as unionemp.
            rewrite unionemp.

            pose (rules_add_eq r s rules.empty H) as eq.

            pose (p_rules.fold_add state.eq_equiv df dt i hnotin) as fadd.

            pose (p_rules.fold_equal state.eq_equiv df dt i H) as feq.

            pose (p_rules.fold_empty (fbp u v (Call a) (Ret b) v1) i) as eqi.
            rewrite eqi in feq.

            (* NOTE can rewrite eq *)
            rewrite feq in fadd.
            assumption.
        Qed.

        Lemma Prop2_fbf : forall P v1 a b w i,
        state.eq
            (fbf P v1 (Call a) (Ret b) w i)
            (state.union 
                (fbf P v1 (Call a) (Ret b) w empty_state)
                i).
        Proof.
            intros P v1 a b w i.

            unfold fbf; destruct w as [u v].
            set (f:=(fbp u v (Call a) (Ret b) v1)).
            case_eq (rules.is_empty P); intro h.
            pose (rules.is_empty_spec P) as ise; destruct ise.
            pose (H h).
            pose (p_rules.fold_empty f empty_state).
            pose (p_rules.empty_is_empty_1 e).

            pose (Trans_fbp u v a b v1) as dt.
            (* unfold transpose in dt. *)
            pose (Proper_fbp u v a b v1) as df.
            
            pose (p_rules.fold_equal state.eq_equiv df dt empty_state e1) as feq.
            unfold f in e0.
            rewrite e0 in feq.

            pose (p_rules.fold_equal state.eq_equiv df dt i e1) as feq'.
            unfold f.
            rewrite feq'. 
            pose (p_rules.fold_empty f i).
            unfold f in e2.
            rewrite e2.
            rewrite feq.

            (* NOTE just a copy from above *)
            assert (state.Empty empty_state) as hemp.
            1: {
                eauto.
            }

            pose (p_state.empty_union_1 i hemp).
            rewrite e3.

            eauto.

            pose (peq_rules.choose_mem_3 P h).
            inversion s.
            destruct H.
            pose (peq_rules.add_equal P x H0).

            pose (rules.equal_spec (rules.add x P) P).
            destruct i0.
            pose (H1 e).

            set (S := rules.remove x (rules.add x P)).
            assert (~rules.In x S).
            1: {
                pose (rules.remove_spec (rules.add x P) x x).
                unfold not; intro g.
                destruct i0.
                pose (H3 g).
                destruct a0.
                contradiction.
            }

            pose (Prop1_fbf) as ee.

            pose (Prop1_fbf S v a b u v1 x i H3) as e1.
            unfold fbf in e1.

            (* NOTE add remove equal *)
            assert (rules.eq (rules.add x S) P).
            1: {
                unfold S.
                (* NOTE x in add x *)
                assert (rules.In x (rules.add x P)).
                1: {
                    apply (rules.add_spec P x x).
                    eauto.
                }
                pose (p_rules.add_remove H4).
                rewrite e2.
                eauto.
            }

            pose (Trans_fbp u v a b v1) as dt.
            (* unfold transpose in dt. *)
            pose (Proper_fbp u v a b v1) as df.
            
            pose (p_rules.fold_equal state.eq_equiv df dt i H4) as feq.

            rewrite feq in e1.

            unfold f.

            (* expand e1 *)

            pose (Prop_fbp u v (Call a) (Ret b) v1 x i).

            rewrite e2 in e1.

            (* rearrange e1 *)

            pose (p_state.union_assoc (rules.fold (fbp u v (Call a) (Ret b) v1) S empty_state)
            (fbp u v (Call a) (Ret b) v1 x empty_state) i) as assc.
            rewrite <- assc in e1.

            clear assc e2.

            pose (Prop1_fbf S v a b u v1 x empty_state H3) as e2.
            unfold fbf in e2.
            rewrite <- e2 in e1.
            clear e2.

            pose (p_rules.fold_equal state.eq_equiv df dt empty_state H4) as feq'.
            rewrite feq' in e1.
            assumption.
        Qed.

        Lemma Proper_fbf : forall P v1 a b,
        Proper (eq ==> state.eq ==> state.eq) (fbf P v1 (Call a) (Ret b)).
        Proof.
            intros P v1 a b.
            unfold Proper.
            split; intro h;
            
            unfold state.eq in H0;
            unfold state.Equal in H0;
            pose (Prop2_fbf P v1 a b x x0) as px;
            pose (Prop2_fbf P v1 a b y y0) as py.

            rewrite py.
            rewrite px in h.
            clear px py.
            unfold fbf in *. destruct y. destruct x.
            inversion H. subst.
            rename v into u.
            rename v0 into v.
            pose (p_state.union_equal_2 (rules.fold (fbp u v (Call a) (Ret b) v1) P empty_state)
            H0) as e.
            rewrite e in h.
            assumption.

            rewrite px.
            rewrite py in h.
            clear py px.
            unfold fbf in *. destruct y. destruct x.
            inversion H. subst.
            rename v into u.
            rename v0 into v.
            pose (p_state.union_equal_2  (rules.fold (fbp u v (Call a) (Ret b) v1) P empty_state)
            H0) as e.
            rewrite <- e in h.
            assumption.
        Qed.

        Lemma Trans_fbf : forall P v a b, 
            transpose state.eq (fbf P v (Call a) (Ret b)).
        Proof.
            intros P v a b.

            unfold transpose.
            intros x y z.

            pose (Prop2_fbf P v a b x (fbf P v (Call a) (Ret b) y z)) as e.
            rewrite e.

            pose (Prop2_fbf P v a b y z) as e1.
            rewrite e1.

            clear e e1.
            pose (Prop2_fbf P v a b y (fbf P v (Call a) (Ret b) x z)) as e.
            rewrite e.

            pose (Prop2_fbf P v a b x z) as e1.
            rewrite e1.
            
            clear e e1.
            pose (p_state.union_assoc (fbf P v (Call a) (Ret b) x empty_state)
            (fbf P v (Call a) (Ret b) y empty_state) z) as e.

            rewrite <- e.

            pose (p_state.union_sym (fbf P v (Call a) (Ret b) x empty_state)
            (fbf P v (Call a) (Ret b) y empty_state)) as e1.
            rewrite e1.

            pose (p_state.union_assoc (fbf P v (Call a) (Ret b) y empty_state)
            (fbf P v (Call a) (Ret b) x empty_state) z).

            rewrite e0.

            apply (p_state.equal_refl).
        Qed.

        Definition fbg P v a b S1 i := state.fold (fbf P v a b) S1 i.

        Lemma Prop1_fbg : forall S1 rs v a b w i,
            ~ in_state w S1 ->
            state.eq 
                (fbg rs v (Call a) (Ret b) (add_state w S1) i)
                (state.union 
                    (fbg rs v (Call a) (Ret b) S1 empty_state) 
                    (fbf rs v (Call a) (Ret b) w i)).
        Proof.
            set (P := fun S1 => 
            forall rs v a b w i,
            ~ in_state w S1 ->
            state.eq 
                (fbg rs v (Call a) (Ret b) (add_state w S1) i)
                (state.union 
                    (fbg rs v (Call a) (Ret b) S1 empty_state) 
                    (fbf rs v (Call a) (Ret b) w i))).

            apply (@p_state.set_induction P).

            2: {
                intros s s' hp wx hnotin hadd.
                unfold P.
                intros rs v a b w i hnotin'.
             
                unfold P in hp.
                case_eq (eqw wx w); intro h.
                1: {
                    pose (wot.eqb_eq wx w) as eqbeq.
                    destruct eqbeq.
                    pose (H h) as eq. clear H0.
    
                    rewrite eq in hnotin.
                    rewrite eq in hadd.
    
                    pose (hadd w) as hr.
                    assert (in_state w s').
                    1: {
                        apply hr.
                        eauto.
                    }
                    contradiction.
                }

                unfold fbg.
                pose (Trans_fbf rs v a b) as dt.
                (* unfold transpose in dt. *)
                pose (Proper_fbf rs v a b) as df.

                set (P' := state.remove wx (add_state w s')).
                pose (p_state.fold_2).
                assert (p_add_state wx P' (add_state w s')) as hadd'.
                1: {
                    unfold P'.
                    set (e':=add_state w s').
                    apply (p_add_state_Equal).

                    assert (in_state wx (add_state w s')).
                    1: {
                        pose (hadd wx) as i0.
                        destruct i0.
                        assert (in_state wx s'); eauto.
                        pose (p_in_state_subset).
                        assert (state.Subset s' (add_state w s')). 
                        1: {
                            apply (p_state.subset_add_2).
                            apply (p_state.subset_equal).
                            apply (p_state.equal_refl).
                        }
                        apply (p_in_state_subset H1 H2).
                    }
                    pose (p_add_state_remove H).
                    unfold e'.
                    pose (state_eq_sym _ _ e).
                    eauto.
                }

                assert (~ in_state wx P') as Hnotin. 
                1: {
                    unfold P'. 
                    unfold not.
                    (* if remove then notin *)
                    intro q.
                    pose (state.remove_spec (add_state w s') wx wx).
                    destruct i0.
                    pose (H q).
                    destruct a0.
                    contradiction.
                }

                assert (in_state wx (add_state w s')) as Hin. 
                1: {
                    pose (hadd wx) as i0.
                    destruct i0.
                    assert (in_state wx s'); eauto.
                    pose (p_in_state_subset).
                    assert (state.Subset s' (add_state w s')). 
                    1: {
                        apply (p_state.subset_add_2).
                        apply (p_state.subset_equal).
                        apply (p_state.equal_refl).
                    }
                    apply (p_in_state_subset H1 H2).
                }

                (* f(S'+w,i)=p(wx, f(S'+w,i)) *)
                pose (p_state.remove_fold_1 state.eq_equiv df dt i Hin) as _start_goal.
                pose (state_eq_sym _ _ _start_goal) as start_goal.


                pose (Prop2_fbf rs v a b wx (state.fold (fbf rs v (Call a) (Ret b))
                (state.remove wx (add_state w s')) i)) as mid2.

                pose (state_eq_trans _ _ _  start_goal mid2) as mid3.

                unfold fbg in *.
                assert (~in_state w s) as H.
                1: {
                  unfold not; intro H.
                  assert (in_state w s').
                  apply (p_in_state_subset H).
                  assert (state.Subset s s).
                  apply (p_state.subset_refl).
                  pose (p_state.subset_add_2 wx H0).
                  pose (p_add_state_Equal wx s s') as q.
                  destruct q. pose (H1 hadd).
                  pose (p_state.subset_equal (state_eq_sym _ _ e)).
                  apply (p_state.subset_trans s0 s1).
                  contradiction.
                }

                assert (state.eq (add_state w s) (state.remove wx (add_state w s'))) as mid4.
                1: {
                  pose (p_add_state_Equal wx s s') as q.
                  destruct q. pose (H0 hadd).
                  pose (p_add_state_add s w wx).
    
                  pose (state_add_eq w s' (add_state wx s) e).
                  pose (state_eq_trans _ _ _ e1 e0).
    
                  pose (p_state.Equal_remove wx e2).
                  
                  assert (~in_state wx (add_state w s)) as Hnotin'.
                  1: {
                    unfold not; intro m.
    
                    pose (add_state_spec s w wx).
                    destruct i0.
                    pose (H2 m).
                    destruct o. 
                    rewrite H4 in h.
                    pose (wot.eqb_eq w w).
                    assert (wot.eqb w w = true).
                    apply i0.
                    eauto. 
                    unfold eqw in h.
                    rewrite H5 in h.
                    inversion h.
                    contradiction.
                }
    
                pose (p_state.remove_add Hnotin').
    
                pose (state_eq_trans _ _ _ e3 e4).
    
                apply (state_eq_sym _ _ e5).
                }
    
    
                pose (state_eq_sym _ _ mid4) as mid4'.
                pose (p_state.fold_equal state.eq_equiv df dt i mid4') as feq.
    
                pose (p_state.union_equal_2 (fbf rs v (Call a) (Ret b) wx empty_state) feq) as eq'.
                unfold fbg in eq'.
    
                pose (state_eq_trans _ _ _ mid3 eq') as mid5.
    
                assert (~in_state w s) as H'.
                (* NOTE Just a copy from the above; should be removed *)
                1: {
                unfold not; intro H'.
                assert (in_state w s').
                apply (p_in_state_subset H').
                assert (state.Subset s s).
                apply (p_state.subset_refl).
                pose (p_state.subset_add_2 wx H0).
                pose (p_add_state_Equal wx s s') as q.
                destruct q. pose (H1 hadd).
                pose (p_state.subset_equal (state_eq_sym _ _ e)).
                apply (p_state.subset_trans s0 s1).
                contradiction.
                }
    
                pose (hp rs v a b w i H') as ind.
                pose (p_state.union_equal_2 (fbf rs v (Call a) (Ret b) wx empty_state) ind) as eq.
    
                pose (state_eq_trans _ _ _ mid5 eq) as mid6.
    
    
                pose (p_state.union_sym (fbf rs v (Call a) (Ret b) wx empty_state)  (state.union (state.fold (fbf rs v (Call a) (Ret b)) s empty_state)
                (fbf rs v (Call a) (Ret b) w i))) as union_sym.
    
                pose (state_eq_trans _ _ _ mid6 union_sym) as mid7.
    
                pose (p_state.union_sym (state.fold (fbf rs v (Call a) (Ret b)) s empty_state)
                (fbf rs v (Call a) (Ret b) w i)) as sym2.
    
                pose (p_state.union_equal_1 (fbf rs v (Call a) (Ret b) wx empty_state) sym2) as sym2'.
    
                pose (state_eq_trans _ _ _ mid7 sym2') as mid8.
    
    
                pose (p_state.union_assoc 
                (fbf rs v (Call a) (Ret b) w i)
                (state.fold (fbf rs v (Call a) (Ret b)) s empty_state)
                (fbf rs v (Call a) (Ret b) wx empty_state)) as mid_assc.
                pose (state_eq_trans _ _ _ mid8 mid_assc) as mid9.
    
                pose (hp rs v a b wx empty_state hnotin) as ind'.
    
                pose (state_eq_sym _ _ ind') as sym.
    
                pose (p_state.union_equal_2 (fbf rs v (Call a) (Ret b) w i) sym) as mid10. 
    
                pose (state_eq_trans _ _ _ mid9 mid10).
    
                assert (state.eq (add_state wx s) s') as eqrxss.
                1: {
                    pose (p_add_state_Equal wx s s').
                    destruct i0.
                    pose (H0 hadd).
                    apply (state_eq_sym _ _ e0).
                }
    
                pose (p_state.fold_equal state.eq_equiv df dt empty_state eqrxss) as eqeq.
    
                pose (p_state.union_equal_2 (fbf rs v (Call a) (Ret b) w i) eqeq) as mid_eq.
    
                pose (state_eq_trans _ _ _ e mid_eq) as mid11.
    
                pose (p_state.union_sym
                (fbf rs v (Call a) (Ret b) w i)
                (state.fold (fbf rs v (Call a) (Ret b)) s' empty_state) ) as sym3.
    
                pose (state_eq_trans _ _ _ mid11 sym3).
    
                assumption.
            }

            (* the empty case *)
            unfold P.
            intros s hemp rs v a b w i hnotin.
            unfold fbg.

            assert (state.eq s state.empty).
            1: {
                apply (p_state.empty_is_empty_1 hemp).
            }

            pose (p_state.fold_empty (fbf rs v (Call a) (Ret b)) empty_state).
            pose (Trans_fbf rs v a b) as dt.
            (* unfold transpose in dt. *)
            pose (Proper_fbf rs v a b) as df.
            pose (p_state.fold_equal state.eq_equiv df dt empty_state H) as goal_eq.
            rewrite e in goal_eq.
            rewrite goal_eq.

            assert (state.Empty empty_state) as semp. eauto.
            pose (p_state.empty_union_1 (fbf rs v (Call a) (Ret b) w i) semp) as unionemp.
            rewrite unionemp.

            pose (state_add_eq w s state.empty H) as eq.

            pose (p_state.fold_add state.eq_equiv df dt i hnotin) as fadd.

            pose (p_state.fold_equal state.eq_equiv df dt i H) as feq.

            pose (p_state.fold_empty (fbf rs v (Call a) (Ret b)) i) as eqi.
            rewrite eqi in feq.

            (* NOTE can rewrite eq *)
            rewrite feq in fadd.
            assumption.
        Qed.

        Lemma Prop2_fbg : forall S1 P v a b i,
        state.eq
            (fbg P v (Call a) (Ret b) S1 i)
            (state.union 
                (fbg P v (Call a) (Ret b) S1 empty_state)
                i).
        Proof.
            intros S1 P v a b i.

            unfold fbg. 
            set (f:=(fbf P v (Call a) (Ret b))).
            case_eq (state.is_empty S1); intro h.
            pose (state.is_empty_spec S1) as ise; destruct ise.
            pose (H h).
            pose (p_state.fold_empty f empty_state).
            pose (p_state.empty_is_empty_1 e).

            pose (Trans_fbf P v a b) as dt.
            (* unfold transpose in dt. *)
            pose (Proper_fbf P v a b) as df.
            
            pose (p_state.fold_equal state.eq_equiv df dt empty_state e1) as feq.
            unfold f in e0.
            rewrite e0 in feq.

            pose (p_state.fold_equal state.eq_equiv df dt i e1) as feq'.
            unfold f.
            rewrite feq'. 
            pose (p_state.fold_empty f i).
            unfold f in e2.
            rewrite e2.
            rewrite feq.

            (* NOTE just a copy from above *)
            assert (state.Empty empty_state) as hemp.
            1: {
                eauto.
            }

            pose (p_state.empty_union_1 i hemp).
            rewrite e3.

            eauto.

            pose (peq_state.choose_mem_3 S1 h).
            inversion s.
            destruct H.
            pose (peq_add_state_equal S1 x H0).

            pose (state.equal_spec (add_state x S1) S1).
            destruct i0.
            pose (H1 e).

            set (S := state.remove x (add_state x S1)).
            assert (~in_state x S).
            1: {
                pose (state.remove_spec (add_state x S1) x x).
                unfold not; intro g.
                destruct i0.
                pose (H3 g).
                destruct a0.
                contradiction.
            }

            pose (Prop1_fbg) as ee.

            pose (Prop1_fbg S P v a b x i H3) as e1.
            unfold fbg in e1.

            (* NOTE add remove equal *)
            assert (state.eq (add_state x S) S1).
            1: {
                unfold S.
                (* NOTE x in add x *)
                assert (in_state x (add_state x S1)).
                1: {
                    apply (add_state_spec S1 x x).
                    eauto.
                }
                pose (p_add_state_remove H4).
                rewrite e2.
                eauto.
            }

            pose (Trans_fbf P v a b) as dt.
            (* unfold transpose in dt. *)
            pose (Proper_fbf P v a b) as df.
            
            pose (p_state.fold_equal state.eq_equiv df dt i H4) as feq.

            rewrite feq in e1.

            unfold f.

            (* expand e1 *)

            pose (Prop2_fbf P v a b x i).

            rewrite e2 in e1.

            (* rearrange e1 *)

            pose (p_state.union_assoc (state.fold (fbf P v (Call a) (Ret b)) S empty_state)
             (fbf P v (Call a) (Ret b) x empty_state) i) as assc.
            rewrite <- assc in e1.

            clear assc e2.

            pose (Prop1_fbg S P v a b x empty_state H3) as e2.
            unfold fbg in e2.
            rewrite <- e2 in e1.
            clear e2.

            pose (p_state.fold_equal state.eq_equiv df dt empty_state H4) as feq'.
            rewrite feq' in e1.
            assumption.
        Qed.

        Lemma Prop_fbg :
        forall S1 P u v v1 v2 a b i,
        in_state (u,v) S1 ->
        in_rules (v, Alt_Match (Call a) (Ret b) v1 v2) P ->
        in_state (u,v2) (fbg P v1 (Call a) (Ret b) S1 i).
        Proof.
            intros S1 P u v v1 v2 a b i HinS1 Hinr.
            unfold fbg.
            
            pose (Trans_fbf P v1 a b) as dt.
            pose (Proper_fbf P v1 a b) as df.

            (* set (f := fbp v (Call a) (Ret b) u v1). *)

            pose (@p_state.remove_fold_1 state.t state.eq _ (fbf P v1 (Call a) (Ret b)) _ dt i S1 (u, v) HinS1) as p.
            rewrite <- p. clear p.

            pose (Prop2_fbf P v1 a b (u,v) (state.fold (fbf P v1 (Call a) (Ret b)) (state.remove (u, v) S1) i)) as e.
            rewrite e. clear e.
            pose (Prop_fbf empty_state P v a b u v1 v2 Hinr) as p.
            
            pose (@p_state.union_subset_1 
                (fbf P v1 (Call a) (Ret b) (u, v) empty_state)
                (state.fold (fbf P v1 (Call a) (Ret b)) (state.remove (u, v) S1) i)).
    
            pose (p_in_state_subset p s).
            assumption.
        Qed.

        Definition fbh P a b S1 (vv:state.elt) i:= 
            let (v1, ve) := vv in
            if (is_eps_v P ve) then 
                fbg P v1 a b S1 i
            else i.

        Lemma Proper_fbh : forall P a b S1, 
        Proper (eq ==> state.eq ==> state.eq) (fbh P (Call a) (Ret b) S1).
        Proof.
            intros P a b S1.
            unfold Proper.
            split; intro h;
            
            unfold state.eq in H0;
            unfold state.Equal in H0.

            rewrite H in h.
            unfold fbh in *.

            destruct y.
            case_eq (is_eps_v P v0); intro g; rewrite g in h.

            pose (Prop2_fbg S1 P v a b x0) as px;
            pose (Prop2_fbg S1 P v a b y0) as py.

            rewrite py.
            rewrite px in h.
            clear px py.
            pose (p_state.union_equal_2  (fbg P v (Call a) (Ret b) S1 empty_state)
            H0) as e.
            rewrite e in h.
            assumption.

            apply (state_In_eq a0 x0 y0 H0). 
            assumption.

            rewrite <- H in h.
            unfold fbh in *.

            destruct x.
            case_eq (is_eps_v P v0); intro g; rewrite g in h.
            pose (Prop2_fbg S1 P v a b x0) as px;
            pose (Prop2_fbg S1 P v a b y0) as py.

            rewrite px.
            rewrite py in h.
            clear px py.
            pose (p_state.union_equal_2  (fbg P v (Call a) (Ret b) S1 empty_state)
            H0) as e.
            rewrite <- e in h.
            assumption.

            apply (state_In_eq a0 x0 y0 H0). 
            assumption.
        Qed.

        Lemma Trans_fbh : forall P a b S1, 
        transpose state.eq (fbh P (Call a) (Ret b) S1).
        Proof.
            intros P a b S1.

            unfold transpose.
            intros x y z.
            unfold fbh. destruct x; destruct y.

            case_eq (is_eps_v P v0); intro h.
            case_eq (is_eps_v P v2); intro g.

            pose (Prop2_fbg S1 P v a b (fbg P v1 (Call a) (Ret b) S1 z)) as e.
            rewrite e.

            pose (Prop2_fbg S1 P v1 a b z) as e1.
            rewrite e1.

            clear e e1.
            pose (Prop2_fbg S1 P v1 a b (fbg P v (Call a) (Ret b) S1 z)) as e.
            rewrite e.

            pose (Prop2_fbg S1 P v a b z) as e1.
            rewrite e1.
            
            clear e e1.
            pose (p_state.union_assoc (fbg P v (Call a) (Ret b) S1 empty_state)
            (fbg P v1 (Call a) (Ret b) S1 empty_state) z) as e.

            rewrite <- e.

            pose (p_state.union_sym (fbg P v (Call a) (Ret b) S1 empty_state)
            (fbg P v1 (Call a) (Ret b) S1 empty_state)) as e1.
            rewrite e1.

            pose (p_state.union_assoc (fbg P v1 (Call a) (Ret b) S1 empty_state)
            (fbg P v (Call a) (Ret b) S1 empty_state) z).

            rewrite e0.

            apply (p_state.equal_refl).
            apply (p_state.equal_refl).

            case_eq (is_eps_v P v2); intro g.
            apply (p_state.equal_refl).
            apply (p_state.equal_refl).
        Qed.

        Lemma Prop2_fbh : forall P a b S1 w i,
        state.eq
            (fbh P (Call a) (Ret b) S1 w i)
            (state.union 
                (fbh P (Call a) (Ret b) S1 w empty_state)
                i).
        Proof.
            intros P a b S1 w i.

            unfold fbh.
            destruct w.
            case_eq (is_eps_v P v0); intro h.

            pose (Prop2_fbg S1 P v a b i).
            assumption.

            (* NOTE just a copy from above *)
            assert (state.Empty empty_state) as hemp.
            1: {
                eauto.
            }

            pose (p_state.empty_union_1 i hemp).
            rewrite e. eauto.
        Qed.

        Definition db P a b S S1 := state.fold (fbh P a b S1) S empty_state.

        Lemma delta_b_prop1 :
        forall P S S1 a u v ve b v1 v2,
            in_state (v1,ve) S ->
            in_state (u,v) S1 ->
            is_eps_v P ve = true ->
            in_rules (v, Alt_Match (Call a) (Ret b) v1 v2) P ->
            in_state (u,v2) (db P (Call a) (Ret b) S S1).
        Proof.
            intros P S S1 a u v ve b v1 v2 hinS hinS1 hiseps hinP.

            unfold db.

            pose (Trans_fbh P a b S1) as dt.
            pose (Proper_fbh P a b S1) as df.

            pose (p_state.remove_fold_1 state.eq_equiv df dt empty_state hinS) as e.

            rewrite <- e. clear e.

            pose (Prop2_fbh P a b S1 (v1,ve) (state.fold (fbh P (Call a) (Ret b) S1) (state.remove (v1, ve) S)
            empty_state)) as e.
            rewrite e. clear e.

            unfold fbh.
            rewrite hiseps.

            pose (Prop_fbg S1 P u v v1 v2 a b empty_state hinS1 hinP).
            
            pose (@p_state.union_subset_1 
            (fbg P v1 (Call a) (Ret b) S1 empty_state)
            (state.fold
               (fun (vv0 : state.elt) (i0 : state.t) =>
                let (v0, ve0) := vv0 in
                if is_eps_v P ve0 then fbg P v0 (Call a) (Ret b) S1 i0 else i0)
               (state.remove (v1, ve) S) empty_state)).

            pose (p_in_state_subset i s).
            assumption.
        Qed.
        
    End delta_b.
        

    Definition delta_b (P: rules.t) (S: state.t) (b:symbol) (S1:state.t) (a:symbol) : state.t := 
        db P a b S S1.

    Definition delta_b' (P: rules.t) (S: state.t) (b:symbol) : state.t := 
        let fold_S (vv: vv) S' :=
            let (context_v, v) := vv in 
            let fold_P (rule: vpg.rule) (S':state.t) : state.t :=
                let (v,alt) := rule in
                    if eqvv v context_v then 
                        match alt with 
                        | Alt_Linear t v' => 
                            if eqs t b then add_state (v, v') S' 
                            else S'
                        | _ => S'
                        end 
                    else S'
            in
            rules.fold fold_P P S'
        in 
        state.fold fold_S S empty_state.

    
    Definition delta P (c:symbol) (S:state.t) (t:option (state.t*symbol)) :=
        let id := fun T => T in
        let default := (empty_state, id) in
        match c with 
        | Call _ => (delta_a P S c, fun T => (S, c)::T)
        | Plain _ => (delta_c P S c, id)
        | Ret _ => 
            match t with 
            | None => (delta_b' P S c, id)
            | Some t => 
                let (S1,a) := t in
                (delta_b P S c S1 a, fun T => match T with [] => [] | t::T' => T' end)
            end
        end.

    Fixpoint recognize P word S (T:stack) :=
        match word with 
        | nil => (S, T)
        | c::word' =>
            let t := 
                match T with 
                | nil => None
                | t::_ => Some t
                end
            in
            let (S', f) := delta P c S t in 
            recognize P word' S' (f T)
        end.

    (* Lemma recog_prop1 : forall P S T u v a b v1 v2,
        in_state (u,v) S ->
        in_rules (v, Alt_Match (Call a) (Ret b) v1 v2) P ->
        let () = recognize  *)

    Fixpoint is_open_stack P (T:stack) :=
        match T with 
        | nil => True 
        | (State, a)::T' => is_open_stack P T' /\
        exists u v ve, (in_state (u,v) State /\ rules.In (v,Alt_Linear a ve) P)
        (* (has_eps_state P State = true) *)
        end.

    Definition is_accepted P (S:state.t) (T:stack) :=
        (has_eps_state P S=true) /\
        match T with 
        | nil => True 
        | (State,_)::T' => is_open_stack P T' /\
        (has_eps_state P State = true)
        end.

End vpg_parser.


Module recognizer_property.
    Import Misc.Basic.
    Import Misc.vpg.
    Import vpg_parser.
    Import Misc.vpl_parsetree.
    Import Misc.basic_tree.

    Lemma V0_V0_Linear: forall g, 
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
    forall v v_ t v', (v = V0 v_) -> (in_rules (v, Alt_Linear t v') P) -> (exists v'_, v'=V0 v'_)
    end.
    Proof.
        intro g. destruct g. intros.
        subst v.
        induction v'.
        eauto.
        1: {
            pose (p_inP (V0 v_, (Alt_Linear (t) (V1 v))) H0).
        contradiction.
        }
    Qed.

    Lemma V0_V0_Match: forall g, 
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
    forall v v_ t1 t2 v1 v2, (v = V0 v_) -> (in_rules (v,Alt_Match t1 t2 v1 v2) P) -> (exists v2_, v2=V0 v2_)
    end.
    Proof.
        intro g. destruct g. intros.
        subst v.
        induction v2.
        eauto.
        1: {
            pose (p_inP (V0 v_, (Alt_Match t1 t2 v1 (V1 v))) H0).
            destruct v1; destruct t1 ;destruct t2; repeat contradiction.
            }
    Qed.

    Lemma V0t0: forall g, 
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ p_inP =>
    forall v v_ t v', (v = V0 v_) -> (in_rules (v,Alt_Linear t v') P) -> (exists t_, t=Plain t_)
    end.
    Proof.
        intro g. destruct g. intros.
        assert (exists v'_, v'=V0 v'_).
        apply (V0_V0_Linear (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v v_ t v' H H0).
        destruct H1. subst.
        induction t.
        1: {
            pose (p_inP (V0 v_, (Alt_Linear (Call t) (V0 x))) H0).
            contradiction.
        }
        eauto.
        1: {
            pose (p_inP (V0 v_, (Alt_Linear (Ret t) (V0 x))) H0).
            contradiction.
        }
    Qed.

    Lemma cc: forall g c1 c2 S T,
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
    let (S',T') := recognize P [c1;c2] S T in
    let (S1,T1) := recognize P [c1] S T  in
    let (S2,T2) := recognize P [c2] S1 T1 in
    (S',T') = (S2,T2)
    end.
    Proof.
        intro g; destruct g; intros.
        destruct c1; destruct c2; simpl; try reflexivity; destruct T; try destruct p; try reflexivity.

        destruct (
            match match T with
            | [] => None
            | t2 :: _ => Some t2
            end with
            | Some t2 =>
                let (S1, a) := t2 in
                (delta_b P (delta_b P S (Ret t) t1 s) (Ret t0) S1 a,
                fun T0 : list (state.t * symbol) =>
                match T0 with
                | [] => []
                | _ :: T'0 => T'0
                end)
            | None =>
                (delta_b' P (delta_b P S (Ret t) t1 s) (Ret t0),
                fun T0 : list (state.t * symbol) => T0)
            end
        ).

        reflexivity.
    Qed.


    Lemma WcW: forall g w c w2 S T,
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
    (w=(c :: w2) % list)-> 
    let (S',T') := recognize P w S T in
    let (S1,T1) := recognize P [c] S T in
    let (S2,T2) := recognize P w2 S1 T1 in
    (S',T') = (S2,T2)
    end.
    Proof.
        intro g. destruct g. intros.
        generalize dependent S.
        generalize dependent T.

        intros T S.
        rewrite H.
        simpl.
        destruct (
        match c with
        | Call _ =>
            (delta_a P S c, fun T0 : list (state.t * symbol) => (S, c) :: T0)
        | Plain _ => (delta_c P S c, fun T0 : list (state.t * symbol) => T0)
        | Ret _ =>
            match match T with
                    | [] => None
                    | t :: _ => Some t
                    end with
            | Some t =>
                let (S1, a0) := t in
                (delta_b P S c S1 a0,
                fun T0 : list (state.t * symbol) =>
                match T0 with
                | [] => []
                | _ :: T' => T'
                end)
            | None => (delta_b' P S c, fun T0 : list (state.t * symbol) => T0)
            end
        end
        ).

        destruct (
            delta P c S match T with
                | [] => None
                | t :: _ => Some t
                end
        ).

        destruct (recognize P w2 t0 (l0 T)).

        reflexivity.

    Qed.


    Lemma WWW: forall g w1 w w2 S T S' T' S1 T1 S2 T2,
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
    (w = (w1 ++ w2) % list)-> 
    (S',T') = recognize P w S T    ->
    (S1,T1) = recognize P w1 S T   ->
    (S2,T2) = recognize P w2 S1 T1 ->
    (S',T') = (S2,T2)
    end.
    Proof.
        intro g. 
        (* pose (WcW g). *)
        destruct g. intro w1.
        induction w1; intros.
        1: {
            simpl recognize in H1.
            simpl app in H; subst.
            inversion H1; subst.
            rewrite H0. rewrite H2. reflexivity.
        }
        1: {
            rewrite H in H0.
            simpl recognize in *.
             destruct (
                 match a with
                 | Call _ =>
                     (delta_a P S a, fun T0 : list (state.t * symbol) => (S, a) :: T0)
                 | Plain _ => (delta_c P S a, fun T0 : list (state.t * symbol) => T0)
                 | Ret _ =>
                     match match T with
                         | [] => None
                         | t :: _ => Some t
                         end with
                     | Some t =>
                         let (S1, a0) := t in
                         (delta_b P S a S1 a0,
                         fun T0 : list (state.t * symbol) =>
                         match T0 with
                         | [] => []
                         | _ :: T' => T'
                         end)
                     | None => (delta_b' P S a, fun T0 : list (state.t * symbol) => T0)
                     end
                 end 
             ).

            assert ((w1 ++ w2)%list = (w1 ++ w2)%list) as id.
            1: {
                reflexivity.
            }

            destruct (
                delta P a S match T with
                    | [] => None
                    | t :: _ => Some t
                    end
            ).

            pose (IHw1 (w1 ++ w2)%list w2 t0 (l0 T) S' T' S1 T1 S2 T2 id H0 H1 H2).
            assumption.
        }
    Qed.

    (* recognize always returns (S,T) *)
    Lemma exST:
        forall P S T w,
        exists S1 T1,
        (S1, T1) = recognize P w S T.
    Proof.
        intros P S T w.
        generalize dependent S.
        generalize dependent T.
        
        induction w.
        simpl.
        eauto.
        simpl.
        destruct a; intros T S.
        apply (IHw ((S, Call t) :: T) (delta_a P S (Call t))).
        apply (IHw T (delta_c P S (Plain t))).
        destruct T.
        apply (IHw [] (delta_b' P S (Ret t))).
        destruct p.
        apply (IHw T (delta_b P S (Ret t) t0 s)).
    Qed.

    Lemma exST_dt:
    forall P c S t,
    exists S1 f,
    (S1, f) = delta P c S t.
    Proof.
        intros P c S t.
        destruct c.
        simpl delta.
        eauto.
        simpl delta.
        eauto.
        simpl delta.
        destruct t.
        destruct p.
        eauto.
        eauto.
    Qed.
        
    Lemma T0Tw: forall (g:vpg) (S:state.t) (T:stack) (S':state.t) (T':stack),
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
    forall (v:vpg_var) (w:vword) (pt:(PT2 P v w)), 
        (exists v_, v = V0 v_) -> 
        (S',T') = recognize P w S T ->
        T' = T
    end.
    Proof.
        intros. 
        pose (WWW g) as y.
        pose (V0_V0_Match g) as y0.
        destruct g. intros.
        pose (exST P) as pex.
        
        generalize dependent S.
        generalize dependent T.
        generalize dependent S'.
        generalize dependent T'.
        induction pt; intros T' S' T S H1.
        
        1: {
            simpl recognize in H1. inversion H1. reflexivity.
        }
        1: {
            assert (exists v'_, v'=V0 v'_).
            1: {
                destruct H as [v_].
                apply (V0_V0_Linear (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v v_ t v' H i).
            }

            assert (exists t_, t=Plain t_).
            1: {
                destruct H as [v_].
                apply (V0t0 (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v v_ t v' H i).
            }

            unfold recognize in H1. simpl. fold recognize in H1.
            inversion H2; subst.
            unfold delta in H1. 
            pose (IHpt H0 T' S' T (delta_c P S (Plain x)) H1).
            assumption.
        }
        1: {
            rename i into H0.
            assert (exists t1_ : terminal, t1 = Call t1_) as callt1.
            1: {
                pose (p_inP (v, Alt_Match t1 t2 v1 v2) H0).
                destruct t1; destruct t2; eauto; contradiction.
            }
            assert (exists t2_ : terminal, t2 = Ret t2_) as rett2.
            1: {
                pose (p_inP (v, Alt_Match t1 t2 v1 v2) H0).
                destruct t1; destruct t2; eauto; try contradiction.  
            }
            inversion callt1 as [a]; inversion rett2 as [b]; subst.
            assert (exists v1_ : terminal, v1 = V0 v1_) as v0v1.
            1: {
                destruct v1; eauto.
                pose (p_inP (v, Alt_Match (Call a) (Ret b) (V1 v0) v2) H0).
                inversion H; subst.
                contradiction.
            }
            assert (exists v2_ : terminal, v2 = V0 v2_) as v0v2.
            1: {
                destruct H as [v_].
                pose (V0_V0_Match (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v v_ (Call a) (Ret b) v1 v2 H H0).
                assumption.
            }

            assert ((w1 ++ Ret b :: w2)%list = (w1 ++ Ret b :: w2)%list) as f1.
            1: {
                reflexivity.
            }

            assert (
                forall S' T' S1 T1,
                (S', T') =
                    recognize P w1 
                    (delta_a P S (Call a)) ((S, Call a) :: T) ->
                (S1, T1) =
                    recognize P [Ret b]
                    S' T' ->
                T1 = T
            ) as awb.
            1:{
                intros.

                pose (IHpt1 v0v1 T'0 S'0 ((S, Call a) :: T) (delta_a P S (Call a)) H2) as ind1.
                rewrite ind1 in H3.
                simpl recognize in H3.
                inversion H3.
                reflexivity.                
            }

            pose (pex S T [Call a]) as exa.
            destruct exa as [Sa [Ta Hwa]].

            pose (pex Sa Ta w1) as exw.
            destruct exw as [Sa_w [Ta_w Ha_w]].

            pose (pex Sa Ta ((w1 ++ [Ret b])%list)) as exawb.
            destruct exawb as [Sa_wb [Ta_wb Ha_wb]].

            pose (pex Sa_w Ta_w [Ret b]) as exb.
            destruct exb as [Sa_w_b [Ta_w_b Ha_w_b]].

            pose (pex Sa_w_b Ta_w_b w2) as exb.
            destruct exb as [Sa_w_b_w [Ta_w_b_w Ha_w_b_w]].

            assert ((Sa_w_b, Ta_w_b) = (Sa_wb, Ta_wb)) as w_b_eq_wb.
            1: {
                assert ((w1 ++ [Ret b])%list = (w1 ++ [Ret b])%list) as id'.
                reflexivity.
                pose (y w1 (w1 ++ [Ret b])%list [Ret b] (delta_a P S (Call a)) ((S, Call a) :: T) Sa_wb Ta_wb 
                Sa_w Ta_w Sa_w_b Ta_w_b) as ww.
                assert ((Sa_wb, Ta_wb) = (Sa_w_b, Ta_w_b)).
                1: {
                    apply ww.
                    assumption.
                    rewrite Ha_wb;inversion Hwa; subst; reflexivity.
                    rewrite Ha_w; inversion Hwa; subst; reflexivity.
                    rewrite Ha_w_b; inversion Hwa; subst; reflexivity.
                    }
                inversion H2;reflexivity.
            }

            (** T_{wb} = T *)
            assert (Ta_wb = T) as l_Ta_wb_eq_T.
            1:{
                inversion w_b_eq_wb.
                rewrite <- H4.
                apply (awb Sa_w Ta_w Sa_w_b Ta_w_b).
                rewrite Ha_w; inversion Hwa; subst; reflexivity.
                rewrite Ha_w_b; reflexivity.
            }

            simpl recognize in H1.

            assert (
                Ta_w_b_w = Ta_w_b
            ) as g1.
            1: {
                eauto.
            }

            assert (
                Ta_w_b_w = T
            ).
            1: {
                rewrite g1.
                inversion w_b_eq_wb.
                assumption.
            }

            assert ((w1 ++ Ret b :: w2)= (w1 ++ [Ret b] ++ w2)) % list as g2.
            1: {
                eauto.
            }

            assert ((S',T')=(Sa_w_b_w,Ta_w_b_w)).
            1: {
                pose (pex Sa_w Ta_w ([Ret b] ++ w2)) % list as exbw.
                destruct exbw as [Sa_w_bw [Ta_w_bw Ha_w_bw]].
                
                pose (y w1 (w1 ++ [Ret b] ++ w2) ([Ret b] ++ w2) Sa Ta S' T' Sa_w Ta_w Sa_w_bw Ta_w_bw) % list.

                assert ((Sa,Ta)=((delta_a P S (Call a)), ((S, Call a) :: T))) as pa.
                1: {
                    rewrite Hwa. simpl. reflexivity.
                }

                assert ((S', T') = (Sa_w_bw, Ta_w_bw)) as g3.
                1: {
                    apply e.
                    reflexivity.
                    rewrite g2 in H1.
                    rewrite H1.
                    inversion pa; subst.
                    eauto. 
                    rewrite Ha_w.
                    eauto.
                    rewrite Ha_w_bw.
                    eauto.
                }
                rewrite g3.
                eauto.
            }
            inversion H3.
            assumption.
        }

    Qed.

    Lemma STT'V0 : forall (g:vpg) (S:state.t) (T:stack) (T1:stack) (S':state.t) (T':stack) (S'':state.t) (T'':stack),
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
        forall (v:vpg_var) (w:vword) (pt:(PT2 P v w)), 
            (exists v_, v = V0 v_) -> 
            (S',T') = recognize P w S T ->
            (S'',T'') = recognize P w S T1 ->
            S' = S''
    end.
    Proof.
        intros.
        pose (WWW g) as y.
        pose (V0_V0_Match g) as y0.
        pose (V0_V0_Linear g) as v0v0l.

        pose (V0t0 g) as V0t0.
        pose (T0Tw g) as t0tw.

        destruct g. intros.
        pose (exST P) as pex.
        
        generalize dependent S.
        generalize dependent T.
        generalize dependent T1.
        generalize dependent S'.
        generalize dependent T'.
        generalize dependent S''.
        generalize dependent T''.
        induction pt; intros T' S' T S H1.
        
        1: {
            intros.
            simpl recognize in *.
            inversion H0.
            inversion H2.
            reflexivity.
        }
        1: {
            intros.

            assert (exists v'_, v' = V0 v'_) as v0v'.
            1: {
                inversion H.
                apply (v0v0l _ _ _ _ H3 i).
            }

            simpl recognize in *.
            unfold delta in *.

            inversion H.
            pose (V0t0 v x t v' H3 i).
            destruct e.
            rewrite H4 in *.

            (* pose (exST_dt P t S0 match T0 with
            | [] => None
            | t :: _ => Some t
            end).
            inversion e as [S1 [f G]].
            rewrite <- G in H0. clear e G.

            pose (exST_dt P t S0 match H1 with
            | [] => None
            | t :: _ => Some t
            end).
            inversion e as [S1' [f' G]].
            rewrite <- G in H2. clear e G. *)

            pose (IHpt v0v' T' S' T S H1 T0 (delta_c P S0 (Plain x0)) H0 H2). assumption.
        }
        1: {
            intros T0 S0.
            rename i into H0.
            assert (exists t1_ : terminal, t1 = Call t1_) as callt1.
            1: {
                pose (p_inP (v, Alt_Match t1 t2 v1 v2) H0).
                destruct t1; destruct t2; eauto; contradiction.
            }
            assert (exists t2_ : terminal, t2 = Ret t2_) as rett2.
            1: {
                pose (p_inP (v, Alt_Match t1 t2 v1 v2) H0).
                destruct t1; destruct t2; eauto; try contradiction.  
            }
            inversion callt1 as [a]; inversion rett2 as [b]; subst.
            assert (exists v1_ : terminal, v1 = V0 v1_) as v0v1.
            1: {
                destruct v1; eauto.
                pose (p_inP (v, Alt_Match (Call a) (Ret b) (V1 v0) v2) H0).
                inversion H; subst.
                contradiction.
            }
            assert (exists v2_ : terminal, v2 = V0 v2_) as v0v2.
            1: {
                destruct H as [v_].
                pose (V0_V0_Match (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v v_ (Call a) (Ret b) v1 v2 H H0).
                assumption.
            }

            simpl recognize.

            (* Needed *)
            assert ((w1 ++ Ret b :: w2)%list = (w1 ++ Ret b :: w2)%list) as f1.
            1: {
                reflexivity.
            }

            set (Sa := delta_a P S0 (Call a)).
            set (Ta1 := (S0, Call a) :: T0).
            set (Ta2 := (S0, Call a) :: H1).

            intros h1 h2.

            pose (pex Sa Ta1 w1) as exw.
            destruct exw as [Sa_w1 [Ta_w1 Ha_w1]].

            pose (pex Sa_w1 Ta_w1 (Ret b::w2)) as exb.
            destruct exb as [Sa_w_bw1 [Ta_w_bw1 Ha_w_bw1]].

            pose (y w1 (w1 ++ Ret b :: w2) (Ret b :: w2) Sa Ta1 S T Sa_w1 Ta_w1 Sa_w_bw1 Ta_w_bw1 f1 h1 Ha_w1 Ha_w_bw1)%list as ww1.

            pose (pex Sa Ta2 w1) as exw.
            destruct exw as [Sa_w2 [Ta_w2 Ha_w2]].

            pose (pex Sa_w2 Ta_w2 (Ret b::w2)) as exb.
            destruct exb as [Sa_w_bw2 [Ta_w_bw2 Ha_w_bw2]].

            pose (y w1 (w1 ++ Ret b :: w2) (Ret b :: w2) Sa Ta2 S' T' Sa_w2 Ta_w2 Sa_w_bw2 Ta_w_bw2 f1 h2 Ha_w2 Ha_w_bw2)%list as ww2.

            pose (IHpt1 v0v1 Ta_w2 Sa_w2 Ta_w1 Sa_w1 Ta2 Ta1 Sa Ha_w1 Ha_w2).
            inversion ww1.
            inversion ww2.
            clear ww1 ww2 H3 H4 H5 H6.

            rewrite e in Ha_w_bw1. clear e.

            pose (t0tw Sa Ta1 Sa_w1 Ta_w1 v1 w1 pt1 v0v1 Ha_w1) as e0.
            rewrite e0 in Ha_w_bw1. clear e0.

            pose (t0tw Sa Ta2 Sa_w2 Ta_w2 v1 w1 pt1 v0v1 Ha_w2) as e0.
            rewrite e0 in Ha_w_bw2. clear e0.

            unfold recognize in Ha_w_bw1; fold recognize in Ha_w_bw1. unfold Ta1 in Ha_w_bw1.
            unfold recognize in Ha_w_bw2; fold recognize in Ha_w_bw2. unfold Ta2 in Ha_w_bw2.

            destruct (delta P (Ret b) Sa_w2 (Some (S0, Call a))).

            pose (IHpt2 v0v2 Ta_w_bw2 Sa_w_bw2 Ta_w_bw1 Sa_w_bw1 (l ((S0, Call a) :: H1)) (l ((S0, Call a) :: T0)) t Ha_w_bw1 Ha_w_bw2).
            assumption.
        }
    Qed.

End recognizer_property.


Module recognizer_correctness.
    Import Misc.Basic.
    (* Import cfg. *)
    Import Misc.vpg.
    Import Misc.vpl_parsetree.
    (* Import vpg_to_cfg. *)
    Import Misc.basic_tree.
    Import vpg_recognizer.
    Import recognizer_property.

    (* Definition expt v w g (pt:PT2 v w) :=
        match pt with 
        | PT2_Eps _ _ _ => False 
        | PT2_Linear _ _ _ _ _ _ _ => False
        | PT2_Matching _ _ _ _ _ _ _ _ _ _ _ => True
        end. *)

    (* ANCHOR new induction *)
    Lemma well_matched_ind : forall (g:vpg),
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
        forall v w (pt: PT2 P v w) S T u,
            (exists v_, v = V0 v_) -> 
            in_state (u,v) S ->
            is_open_stack P T ->
            let (Sw,Tw) := (recognize P w S T) in
            (exists ve, is_eps_v P ve=true /\ in_state (u,ve) Sw) /\
            (is_open_stack P Tw)
    end.
    Proof.
        intro g. 
        pose (WWW g) as www.
        pose (T0Tw g) as T0Tw.
        pose (STT'V0 g) as stt'v0.


        destruct g.
        intros v w pt.
        pose (exST P) as pex.

        induction pt.
        3: {
            intros S T u hv0 hinS hopenT.
            rename i into hinr.

            (* replace call t1 and call t2 *)
            assert (exists t1_ : terminal, t1 = Call t1_) as callt1.
            1: {
                pose (p_inP (v, Alt_Match t1 t2 v1 v2) hinr).
                eauto. 
                destruct t1; destruct t2; eauto; contradiction.
            }
            assert (exists t2_ : terminal, t2 = Ret t2_) as rett2.
            1: {
                pose (p_inP (v, Alt_Match t1 t2 v1 v2) hinr).
                eauto. 
                destruct t1; destruct t2; eauto; try contradiction.  
            }
            inversion callt1 as [a]; inversion rett2 as [b]; subst. clear callt1 rett2.

            (* (v1,v1)\in Sa *)
            pose (delta_a_prop1 S P a u v b v1 v2 hinS hinr) as hv1da.

            pose (pex S T [Call a]) as exa.
            inversion exa as [Sa [Ta Ha]].
            clear exa.

            assert (in_state (v1,v1) Sa) as Hpt1v1in.
            1: {
                unfold recognize in Ha.
                destruct T;
                unfold delta in Ha;
                inversion Ha;
                assumption.
            }

            assert (exists v1_ : terminal, v1 = V0 v1_) as v0v1.
            1: {
                destruct v1; eauto.
                pose (p_inP (v, Alt_Match (Call a) (Ret b) (V1 v0) v2) hinr).
                inversion y; subst.
            }

            (* Ind on w1 *)
            pose (IHpt1 Sa T v1 v0v1 Hpt1v1in hopenT) as ind1.

            pose (pex Sa T w1) as exa.
            inversion exa as [Sa_w' [Tw Ha_w']].
            clear exa.

            rewrite <- Ha_w' in ind1. 
            destruct ind1 as [ind1S ind1T].

            pose (pex Sa Ta w1) as exa.
            inversion exa as [Sa_w [Ta_w Ha_w]].
            clear exa.


            assert (Sa_w' = Sa_w).
            1: {
                apply (stt'v0 Sa T Ta Sa_w' Tw Sa_w Ta_w v1 w1 pt1 v0v1 Ha_w' Ha_w).
            }

            (* Ta_wb is open because Ta_w=Ta & Ta_wb=T *)
            pose (T0Tw Sa Ta Sa_w Ta_w v1 w1 pt1) as hTa_wb.
            assert (Ta_w = Ta) as hTaEqTa_w.
            1: {
                apply hTa_wb.

                assumption.
                assumption.
            }

            (* Tawb=T *)
            pose (pex Sa_w Ta_w [Ret b]) as exa.
            inversion exa as [Sa_w_b [Ta_w_b Ha_w_b]].
            clear exa.

            assert (Ta_w_b = T) as hTawbEqT.
            1: {
                rewrite hTa_wb in Ha_w_b.
                unfold recognize in Ha_w_b.

                (* Ta is not [] *)
                unfold recognize in Ha.
                destruct T.
                1: {
                    unfold delta in Ha.
                    inversion Ha.
                    rewrite H2 in Ha_w_b.
                    unfold delta in Ha_w_b.
                    inversion Ha_w_b.
                    reflexivity.
                }
                1: {
                    unfold delta in Ha.
                    inversion Ha.
                    unfold delta in Ha_w_b.
                    rewrite H2 in Ha_w_b.
                    inversion Ha_w_b.
                    reflexivity.
                }

                assumption.
                assumption.
            }

            assert (in_state (u,v2) Sa_w_b).
            1: {
                inversion ind1S as [ve G].
                destruct G.

                rewrite H in H1.

                pose (delta_b_prop1 P Sa_w S a u v ve b v1 v2 H1 hinS H0 hinr).
                unfold recognize in Ha_w_b.

                rewrite hTaEqTa_w in Ha_w_b.

                (* Ta is not [] *)
                unfold recognize in Ha.
                destruct T.
                1: {
                    unfold delta in Ha.
                    inversion Ha.
                    rewrite H4 in Ha_w_b.
                    unfold delta in Ha_w_b.
                    inversion Ha_w_b.
                    unfold delta_b in H5.
                    assumption.
                }
                1: {
                    unfold delta in Ha.
                    inversion Ha.
                    unfold delta in Ha_w_b.
                    rewrite H4 in Ha_w_b.
                    inversion Ha_w_b.
                    unfold delta_b in H5.
                    assumption.
                }
            }

            rewrite <- hTawbEqT in hopenT.

            assert (exists v2_ : terminal, v2 = V0 v2_) as v0v2.
            1: {
                inversion hv0.
                pose (V0_V0_Match (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v x (Call a) (Ret b) v1 v2 H1 hinr).
                assumption.
            }

            pose (IHpt2 Sa_w_b Ta_w_b u v0v2 H0 hopenT) as prefinal.

            pose (pex S T ([Call a] ++ w1 ++ [Ret b] ++ w2)%list) as exa.
            inversion exa as [Sf [Tf Hf]].
            clear exa.

            rewrite <- Hf.

            pose (pex Sa_w_b Ta_w_b w2) as exa.
            inversion exa as [Sa_w_b_w [Ta_w_b_w Ha_w_b_w]].
            clear exa.
            rewrite <- Ha_w_b_w in prefinal.
            
            assert ((Sf,Tf)=(Sa_w_b_w,Ta_w_b_w)).
            (* full version proof *)
            1: {
                assert (([Call a] ++ w1 ++ [Ret b] ++ w2)%list = (([Call a] ++ w1 ++ [Ret b]) ++ w2)%list) as f1.
                1: {
                    apply (List.app_assoc ([Call a] ++ w1) [Ret b] w2)%list.
                }


                pose (pex S T ([Call a] ++ w1 ++ [Ret b])%list) as exa.
                inversion exa as [Sawb [Tawb Hawb]].
                clear exa.

                pose (pex Sawb Tawb w2) as exa.
                inversion exa as [Sawb_w [Tawb_w Hawb_w]].
                clear exa.

                pose (www ([Call a] ++ w1 ++ [Ret b]) ([Call a] ++ w1 ++ [Ret b] ++ w2) w2 S T Sf Tf Sawb Tawb Sawb_w Tawb_w f1 Hf Hawb Hawb_w) % list as H_f_awb_w.

                (* Step 1 *)
                rewrite H_f_awb_w. clear H_f_awb_w.


                pose (pex S T ([Call a] ++ w1)%list) as exa.
                inversion exa as [Saw [Taw Haw]].
                clear exa.

                pose (pex Saw Taw [Ret b]) as exa.
                inversion exa as [Saw_b [Taw_b Haw_b]].
                clear exa.

                assert (([Call a] ++ w1 ++ [Ret b])%list = (([Call a] ++ w1) ++ [Ret b])%list) as f2.
                1: {
                    apply (List.app_assoc [Call a] w1 [Ret b])%list.
                }

                pose (www ([Call a] ++ w1) ([Call a] ++ w1 ++ [Ret b]) [Ret b] S T Sawb Tawb Saw Taw Saw_b Taw_b f2 Hawb Haw Haw_b) % list as H_f_aw_b.
                inversion H_f_aw_b.
                rewrite H2 in Hawb_w.
                rewrite H3 in Hawb_w.
                clear H2 H3.


                assert (([Call a] ++ w1)%list = (([Call a] ++ w1))%list) as f3.
                1: {
                    eauto.
                }

                pose (www ([Call a]) ([Call a] ++ w1) w1 S T Saw Taw Sa Ta Sa_w Ta_w f3 Haw Ha Ha_w) % list as H_f_a_w.
                inversion H_f_a_w. clear H_f_a_w. clear H_f_aw_b.
                rewrite H2 in Haw_b.
                rewrite H3 in Haw_b.
                clear H2 H3.

                rewrite <- Ha_w_b in Haw_b.
                inversion Haw_b.
                rewrite H2 in Hawb_w.
                rewrite H3 in Hawb_w.
                clear H2 H3.
                rewrite <- Ha_w_b_w in Hawb_w.
                inversion Hawb_w.
                reflexivity.
            }
            inversion H1.
            assumption.
        }

        1: {
            intros S T u hin hopenT.
            simpl recognize.
            simpl (S,T).
            simpl.

            split.
            
            exists v.
            split.
            unfold is_eps_v.

            pose (rules.mem_spec P (v, Alt_Epsilon)) as hm.
            destruct hm.
            pose (H1 i). assumption.
            assumption.
            assumption.
        }

        1: {
            intros S T u hin hopenT.
            
            simpl recognize.
            assert (exists t_, t=Plain t_).
            1: {
                destruct hin as [v_].
                apply (V0t0 (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v v_ t v' H i).
            }
            inversion H.
            rewrite H0. clear H0.

            destruct T.
            simpl delta.
            simpl; intro.

            apply (IHpt (delta_c P S (Plain x)) []).
            assert (exists v'_, v'=V0 v'_).
            1: {
                destruct H as [v_].
                inversion hin.
                apply (V0_V0_Linear (Cons_VPG Σ V P L0 p_in_V_Σ p_inP) v x0 t v' H1).
                assumption.
            }
            assumption.

            2: {
                eauto.
            }

            (* NOTE The last case is left for lemmas of delta_l; can be constructed like delta_a *)
            
    Admitted.

    Theorem recognizer_correctness: forall (g:vpg),
    match g with 
    | Cons_VPG Σ V P L0 p_in_V_Σ prules =>
    let S0 := state.singleton (L0, L0) in
    let T0 := [] in
        forall w (pt:(PT2 P L0 w)), 
        (exists v_, L0 = V0 v_) -> 
        let (Se, Te) := (recognize P w S0 T0) in
        (exists ve, is_eps_v P ve=true /\ state.In (L0, ve) Se) /\ (is_open_stack P Te)
    end.
    Proof.
        intro g. pose (well_matched_ind g) as HInd. destruct g.
        intros S0 T0 w pt Hex.

        assert (state.In (L0, L0) S0) as hin.
        1: {
            pose (state.singleton_spec (L0,L0) (L0,L0)) as i.
            destruct i. eauto.
        }

        assert (is_open_stack P T0) as hisopen.
        1: {
            simpl. easy.
        }

        pose (HInd L0 w pt S0 T0 L0 Hex hin hisopen) as y.
        pose (exST P) as pex.
        pose (pex S0 T0 w) as exa.
        inversion exa as [Se [Te H]].
        rewrite <- H in y.
        rewrite <- H.
        destruct y as [Hve HopenT].
        split.

        unfold has_eps_state.
        assumption.
        assumption.
    Qed.

End recognizer_correctness.
