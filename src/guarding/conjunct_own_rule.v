From iris.algebra Require Export cmra.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.

From iris.algebra Require Import auth.

From iris.proofmode Require Export tactics.

Section ConjunctOwnRule.

Context {Σ: gFunctors}.
Context `{i : !inG Σ A}.
Implicit Types a : A.

Context `{Disc : CmraDiscrete A}.

Definition project (x: iResUR Σ) (γ: gname) : option A :=
  match (x (inG_id i) !! γ) with
  | Some t => Some (cmra_transport (eq_sym inG_prf) (own.inG_fold t))
  | None => None
  end.

Lemma valid_project (x: iResUR Σ) (γ: gname) (n: nat) :
    ✓{n} x -> ✓{n} (project x γ).
Proof.
  intros.
  unfold project.
  destruct (x (inG_id i) !! γ) eqn:p.
  - apply cmra_transport_validN.
    rewrite <- own.inG_unfold_validN.
    setoid_rewrite own.inG_unfold_fold.
    enough (✓{n} Some o); trivial.
    rewrite <- p.
    enough (✓{n} (x (inG_id i))). { trivial. }
    trivial.
  - unfold validN. unfold cmra_validN. unfold optionR. unfold option_validN_instance.
    trivial.
Qed.

Lemma some_op_equiv (a b c : A)
  : a ≡ b ⋅ c -> Some a ≡ Some b ⋅ Some c.
Proof. intros. setoid_rewrite H. trivial. Qed.

Lemma project_op (x y: iResUR Σ) γ :
    project (x ⋅ y) γ ≡ project x γ ⋅ project y γ.
Proof.
  unfold project.
  rewrite lookup_op.
  destruct (x (inG_id i) !! γ) eqn:p1; destruct (y (inG_id i) !! γ) eqn:p2.
  - rewrite p1. rewrite p2.
      replace (Some o ⋅ Some o0) with (Some (o ⋅ o0)) by trivial.
      apply some_op_equiv.
      setoid_rewrite <- cmra_transport_op.
      f_equiv.
      unfold own.inG_fold.
      apply cmra_morphism_op.
      typeclasses eauto.
  - rewrite p1. rewrite p2. trivial.
      (*replace (Some o ⋅ None) with (Some o) by trivial. trivial.*)
  - rewrite p1. rewrite p2. trivial.
      (*replace (None ⋅ Some o) with (Some o) by trivial. trivial.*)
  - rewrite p1. rewrite p2. trivial.
Qed.

Lemma project_iRes_singleton (x: A) (γ: gname)
  : project (own.iRes_singleton γ x) γ ≡ Some x.
Proof.
  unfold project, own.iRes_singleton.
  setoid_rewrite discrete_fun_lookup_singleton.
  rewrite lookup_singleton.
  f_equiv.
  setoid_rewrite own.inG_fold_unfold.
  rewrite cmra_transport_trans eq_trans_sym_inv_r /=.
  trivial.
Qed.

Lemma discrete_equiv (a b : A) (n: nat)
  : a ≡{n}≡ b -> a ≡ b.
Proof using A Disc.
  intros.
  apply (discrete n). { typeclasses eauto. }
  apply dist_le with (n := n); trivial.
Qed.

Lemma discrete_equiv_opt (a b : option A) (n: nat)
  : a ≡{n}≡ b -> a ≡ b.
Proof using A Disc.
  intro H.
  destruct a, b.
  - setoid_replace c with c0; trivial. apply (discrete_equiv _ _ n).
    inversion H. trivial.
  - inversion H.
  - inversion H.
  - trivial.
Qed.

Lemma proper_project_equiv_n (n: nat) : Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) project.
Proof.
  unfold Proper, "==>". intros x y H γ γ0 s0. unfold project. subst γ0.
  assert (x (inG_id i) !! γ ≡{n}≡ y (inG_id i) !! γ) as M.
  {
      enough (x (inG_id i) ≡{n}≡ y (inG_id i)).
      { trivial. }
      trivial.
  }
  destruct (x (inG_id i) !! γ);
  destruct (y (inG_id i) !! γ).
  - assert (o ≡{n}≡ o0) as Q.
    + unfold "≡" in M. unfold ofe_equiv, optionO, option_equiv in M.
          inversion M. trivial.
    + setoid_rewrite Q. trivial.
  - inversion M.
  - inversion M.
  - trivial.
Qed.

Instance proper_iRes_singleton_equiv_equiv_n (n: nat) : Proper ((=) ==> (≡) ==> (≡{n}≡))
    (@own.iRes_singleton Σ A i).
Proof.
  unfold Proper, "==>". intros γ γ0 e x y H. subst γ0.
  unfold own.iRes_singleton. 
  f_equiv.
  apply: singletonM_proper.
  setoid_rewrite H.
  trivial.
Qed.

(* copied from iris basic_logic/lib/own.v *)
Lemma iRes_singleton_op γ a1 a2 :
  own.iRes_singleton γ (a1 ⋅ a2) ≡ own.iRes_singleton γ a1 ⋅ own.iRes_singleton γ a2. 
Proof.
  rewrite /own.iRes_singleton discrete_fun_singleton_op singleton_op cmra_transport_op.
  f_equiv. apply: singletonM_proper. apply (cmra_morphism_op _). 
Qed.

(*
Lemma iRes_singleton_opq
    own.iRes_singleton γ (x ⋅? project a γ) ≡ own.iRes_singleton γ x ⋅ 
    *)

(*Lemma iRes_singleton_project included*)

Lemma iRes_incl_from_proj γ x w n :
  project w γ ≡ Some x ->
      own.iRes_singleton γ x ≼{n} w.
Proof.
  intro p.
  unfold project in p.
  destruct (w (inG_id i) !! γ) eqn:e.
  - assert ((cmra_transport (eq_sym inG_prf) (own.inG_fold o)) ≡ x) as X.
    { unfold "≡", ofe_equiv, optionO, option_equiv in p. inversion p. trivial. }
    unfold includedN.
    unfold own.iRes_singleton.
    exists (discrete_fun_insert 
        (inG_id i)
        (delete γ (w (inG_id i)))
        w).
    apply equiv_dist.
    intros x'.
    have h : Decision (inG_id i = x') by solve_decision. destruct h.
    + setoid_rewrite discrete_fun_lookup_op. subst x'.
      setoid_rewrite discrete_fun_lookup_singleton.
      setoid_rewrite discrete_fun_lookup_insert.
      intro γ0.
      have h1 : Decision (γ = γ0) by solve_decision. destruct h1.
      * subst γ0. rewrite lookup_op. rewrite lookup_delete.
        rewrite lookup_singleton. rewrite e.
        unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
        f_equiv.
        setoid_rewrite <- X.
        rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
        setoid_rewrite own.inG_unfold_fold. trivial.
      * rewrite lookup_op. rewrite lookup_delete_ne; trivial.
        rewrite lookup_singleton_ne; trivial.
        unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
        destruct (w (inG_id i) !! γ0) eqn:s.
        ++ rewrite s. trivial.
        ++ rewrite s. trivial.
    + setoid_rewrite discrete_fun_lookup_op.
      setoid_rewrite discrete_fun_lookup_singleton_ne; trivial.
      setoid_rewrite discrete_fun_lookup_insert_ne; trivial.
      symmetry.
      apply ucmra_unit_left_id.
  - inversion p.
Qed.

Lemma uPred_ownM_andsep_to_sepand (x y: iResUR Σ) (P : iProp Σ)
  (cond: ∀ n (p1 p2 : iResUR Σ) , (✓{n} (p1 ⋅ p2)) -> (x ≼{n} p1 ⋅ p2) -> (y ≼{n} p1) ->
      ∃ m , y ⋅ m ≡{n}≡ p1 /\ x ≼{n} m ⋅ p2)
  : (uPred_ownM x ∧ (uPred_ownM y ∗ P)) ⊢ (uPred_ownM y ∗ (uPred_ownM x ∧ P)).
Proof.
  uPred.unseal.
  split.
  intros n p val t.
  unfold uPred_holds, upred.uPred_and_def in t.
  destruct t as [tx s].
  unfold uPred_holds, upred.uPred_ownM_def in tx.
  unfold uPred_holds, upred.uPred_sep_def in s.
  destruct s as [p1 [p2 [eq [ty tp]]]].
  unfold uPred_holds, upred.uPred_ownM_def in ty.
  
  unfold uPred_holds, upred.uPred_sep_def.
  
  assert (✓{n} (p1 ⋅ p2)) as val2. { setoid_rewrite <- eq. trivial. }
  assert (x ≼{n} (p1 ⋅ p2)) as incl2. { setoid_rewrite <- eq. trivial. }
  
  have k := cond n p1 p2 val2 incl2 ty.
  destruct k as [m [ym xle]].
  
  exists y. exists (m ⋅ p2).
  
  split.
  { setoid_rewrite eq. setoid_rewrite <- ym. rewrite cmra_assoc. trivial. }
  split.
  { unfold uPred_holds, upred.uPred_ownM_def. trivial. }
  unfold uPred_holds, upred.uPred_and_def. split.
  { unfold uPred_holds, upred.uPred_ownM_def. trivial. }
  apply (uPred_mono _ _ n n p2); trivial.
  unfold includedN. exists m. rewrite cmra_comm. trivial.
Qed.

(*Lemma isRes_singleton_incl_from_dotquestionmark  γ (x: A) (m: option A) n j
  (cond1 : own.iRes_singleton γ (x ⋅? m) ≼{n} j)
  : own.iRes_singleton γ x ≼{n} j.
Proof.
  destruct m.
  { replace (x ⋅? Some c) with (x ⋅ c) in cond1 by trivial.
    generalize cond1.
    rewrite iRes_singleton_op.
    intro X.
    unfold includedN in X. destruct X as [z X].
    unfold includedN. exists (own.iRes_singleton γ c ⋅ z). 
    setoid_rewrite X. symmetry. rewrite cmra_assoc. trivial.
  }
  replace (x ⋅? None) with x in cond1 by trivial.
    unfold includedN in cond1. destruct cond1 as [z X].
    unfold includedN. exists z. 
    trivial.
Qed.*)

Lemma none_dot (a: option A) : None ⋅ a = a.
  Proof. destruct a; trivial. Qed.
  
Lemma dot_none (a: option A) : a ⋅ None = a.
  Proof. destruct a; trivial. Qed.
  
Lemma some_dot_some (a b: A) : (Some a) ⋅ (Some b) = (Some (a ⋅ b)).
  Proof. trivial. Qed.

Lemma le_stuff (a b c d : iResUR Σ) n
  (t : a ⋅ b ≼{n} c)
  : a ≼{n} d ⋅ c.
Proof.
  destruct t as [z t]. exists (b ⋅ z ⋅ d). setoid_rewrite t.
  setoid_replace (d ⋅ (a ⋅ b ⋅ z)) with ((a ⋅ b ⋅ z) ⋅ d) by (apply cmra_comm).
  setoid_replace (a ⋅ ((b ⋅ z) ⋅ d)) with ((a ⋅ (b ⋅ z)) ⋅ d) by (apply cmra_assoc).
  setoid_replace (a ⋅ (b ⋅ z)) with (a ⋅ b ⋅ z) by (apply cmra_assoc).
  trivial.
Qed.
  
Lemma le_stuff2 (a c d : iResUR Σ) n
  (t : a ≼{n} c)
  : a ≼{n} d ⋅ c.
Proof.
  destruct t as [z t]. exists (z ⋅ d). setoid_rewrite t.
  setoid_replace (d ⋅ (a ⋅ z)) with ((a ⋅ z) ⋅ d) by (apply cmra_comm).
  setoid_rewrite <- cmra_assoc. trivial.
Qed.

Lemma incl_l (b b' c: iResUR Σ) n
  (t: b ≼{n} b') : b ⋅ c ≼{n} b' ⋅ c.
Proof.
  destruct t as [z t]. exists z. setoid_rewrite t.
  setoid_replace (b ⋅ z ⋅ c) with (b ⋅ (z ⋅ c)) by (symmetry; apply cmra_assoc).
  setoid_replace (b ⋅ c ⋅ z) with (b ⋅ (c ⋅ z)) by (symmetry; apply cmra_assoc).
  setoid_replace (c ⋅ z) with (z ⋅ c) by (apply cmra_comm). trivial.
Qed.

Lemma incl_r (b b' c: iResUR Σ) n
  (t: b ≼{n} b') : c ⋅ b ≼{n} c ⋅ b'.
Proof.
  destruct t as [z t]. exists z. setoid_rewrite t. rewrite cmra_assoc. trivial.
Qed.
  
Lemma incl_stuff3 (a b c b' c' : iResUR Σ) n
      (i1: a ≼{n} b ⋅ c) (i2: b ≼{n} b') (i3: c ≼{n} c')
      : (a ≼{n} b' ⋅ c').
Proof.
  eapply cmra_includedN_trans. { apply i1. }
  apply (cmra_includedN_trans _ (b ⋅ c) (b ⋅ c') (b' ⋅ c')).
  - apply incl_r; trivial. - apply incl_l; trivial.
Qed.
      
Lemma incl_stuff4 (a b b' c' : iResUR Σ) n
      (i1: a ≼{n} b) (i2: b ≼{n} b')
      : (a ≼{n} b' ⋅ c').
Proof.
  eapply cmra_includedN_trans. { apply i1. }
  apply (cmra_includedN_trans _ b b' (b' ⋅ c')); trivial.
  exists c'. trivial.
Qed.
  
Lemma discrete_fun_insert_incl_iRes_singleton n (m: A) (p1: iResUR Σ) (γ: gname) :
      (own.iRes_singleton γ m) ≼{n}
  discrete_fun_insert (inG_id i)
            (<[γ:=own.inG_unfold (cmra_transport inG_prf m)]> (p1 (inG_id i))) p1.
Proof.
    exists (discrete_fun_insert 
        (inG_id i)
        (delete γ (p1 (inG_id i)))
        p1).
    apply equiv_dist.
    intros x'.
    have h : Decision (inG_id i = x') by solve_decision. destruct h.
    + setoid_rewrite discrete_fun_lookup_op. subst x'.
      setoid_rewrite discrete_fun_lookup_singleton.
      setoid_rewrite discrete_fun_lookup_insert.
      intro γ0.
      have h1 : Decision (γ = γ0) by solve_decision. destruct h1.
      * subst γ0. rewrite lookup_op. rewrite lookup_delete.
          rewrite lookup_insert.
        rewrite op_None_right_id.
        rewrite lookup_singleton. trivial.
      * rewrite lookup_insert_ne; trivial. 
        rewrite lookup_op.
        rewrite lookup_singleton_ne; trivial. rewrite op_None_left_id.
        rewrite lookup_delete_ne; trivial.
    + setoid_rewrite discrete_fun_lookup_op.
      setoid_rewrite discrete_fun_lookup_singleton_ne; trivial.
      setoid_rewrite discrete_fun_lookup_insert_ne; trivial.
      symmetry.
      apply ucmra_unit_left_id.
Qed.
            
Lemma Some_incl_Some_Some_to_iRes_singleton_incl (a b c : A) n γ
            (sincl: Some a ≼{n} Some b ⋅ Some c) :
            (own.iRes_singleton γ a ≼{n} own.iRes_singleton γ b ⋅ own.iRes_singleton γ c).
Proof.
  rewrite <- iRes_singleton_op. destruct sincl as [z sincl]. destruct z.
  + rewrite some_dot_some in sincl. rewrite some_dot_some in sincl. inversion sincl.
    exists (own.iRes_singleton γ c0). rewrite <- iRes_singleton_op.
    unfold own.iRes_singleton. f_equiv. apply: singletonM_proper. setoid_rewrite H1. trivial.
  + rewrite some_dot_some in sincl. rewrite dot_none in sincl. inversion sincl.
    exists ε. rewrite ucmra_unit_right_id.
    unfold own.iRes_singleton. f_equiv. apply: singletonM_proper. setoid_rewrite H1. trivial.
Qed.
            
Lemma Some_incl_Some_None_to_iRes_singleton_incl (a b : A) n γ
            (sincl: Some a ≼{n} Some b ⋅ None) :
            (own.iRes_singleton γ a ≼{n} own.iRes_singleton γ b).
Proof.
  destruct sincl as [z sincl]. rewrite dot_none in sincl. destruct z.
  + rewrite some_dot_some in sincl. inversion sincl. exists (own.iRes_singleton γ c).
    rewrite <- iRes_singleton_op. unfold own.iRes_singleton. f_equiv. apply: singletonM_proper.
    setoid_rewrite H1. trivial.
  + rewrite dot_none in sincl. inversion sincl. exists ε. rewrite ucmra_unit_right_id.
    unfold own.iRes_singleton. f_equiv. apply: singletonM_proper. setoid_rewrite H1. trivial.
Qed.

Lemma andsep_to_sepand γ (x y: A) (P : iProp Σ)
  (cond: ∀ n (p1 : A) (p2 r1 r2 : option A) , (✓ (p1 ⋅? p2))
      -> (x ⋅? r1 ≡ p1 ⋅? p2)
      -> (y ⋅? r2 ≡ p1)
      -> ∃ (m: option A) , y ⋅? m ≡ p1 /\ Some x ≼{n} m ⋅ p2)
  : (own γ x ∧ (own γ y ∗ P)) ⊢ (own γ y ∗ (own γ x ∧ P)).
Proof using A Disc i Σ.
  rewrite own.own_eq. unfold own.own_def. apply uPred_ownM_andsep_to_sepand.
  intros n p1 p2 val incl1 incl2.
  
  unfold includedN in incl1. destruct incl1 as [z1 incl1].
  unfold includedN in incl2. destruct incl2 as [z2 incl2].
  
  assert (project (p1 ⋅ p2) γ ≡{n}≡ project (own.iRes_singleton γ x ⋅ z1) γ) as X.
    { apply proper_project_equiv_n; trivial. }
    
  assert (project p1 γ ≡{n}≡ project (own.iRes_singleton γ y ⋅ z2) γ) as Y.
    { apply proper_project_equiv_n; trivial. }
  
  setoid_rewrite project_op in X.
  setoid_rewrite project_iRes_singleton in X.
  
  setoid_rewrite project_op in Y.
  setoid_rewrite project_iRes_singleton in Y.
  
  replace (Some x ⋅ project z1 γ) with (Some (x ⋅? project z1 γ)) in X.
  2: { unfold "⋅?". destruct (project z1 γ); trivial. }
  
  replace (Some y ⋅ project z2 γ) with (Some (y ⋅? project z2 γ)) in Y.
  2: { unfold "⋅?". destruct (project z2 γ); trivial. }
  
  destruct (project p1 γ) eqn:p1eqn. 2: { inversion Y. }
  
  inversion Y.
  
  replace (Some c ⋅ project p2 γ) with (Some (c ⋅? project p2 γ)) in X.
  2: { unfold "⋅?". destruct (project p2 γ); trivial. }
  inversion X.
  
  assert (✓ (c ⋅? project p2 γ)) as val2. {
    have vp := valid_project _ γ _ val.
    setoid_rewrite project_op in vp.
    setoid_rewrite p1eqn in vp.
    replace (Some c ⋅ project p2 γ) with (Some (c ⋅? project p2 γ)) in vp.
    - unfold includedN in vp. rewrite <- cmra_discrete_valid_iff in vp. trivial.
    - destruct (project p2 γ); trivial.
  }
  
  symmetry in H4. have eq1 := discrete_equiv _ _ _ H4.
  symmetry in H1. have eq2 := discrete_equiv _ _ _ H1.
  have cond0 := cond n c (project p2 γ) (project z1 γ) (project z2 γ) val2 eq1 eq2.
  destruct cond0 as [m [req_eq res_incl]].
  destruct m as [m|].
  2: {
    exists z2. split.
      + symmetry. apply incl2.
      + unfold includedN in res_incl. destruct res_incl as [z res_incl]. destruct z.
        * rewrite none_dot in res_incl. rewrite some_dot_some in res_incl.
          have ri' := discrete_equiv_opt _ _ _ res_incl.
          have t := iRes_incl_from_proj γ (x ⋅ c0) p2 n ri'.
          setoid_rewrite iRes_singleton_op in t.
          eapply le_stuff. apply t.
        * rewrite none_dot in res_incl. rewrite dot_none in res_incl.
          have ri' := discrete_equiv_opt _ _ _ res_incl.
          have t := iRes_incl_from_proj γ x p2 n ri'.
          eapply le_stuff2. apply t.
  }
  exists ((discrete_fun_insert (inG_id i) (<[ γ := own.inG_unfold (cmra_transport inG_prf m) ]>
      (p1 (inG_id i))) p1)).
  split.
  - apply equiv_dist.
    intros x'.
    have h : Decision (inG_id i = x') by solve_decision. destruct h.
    + setoid_rewrite discrete_fun_lookup_op. subst x'.
      setoid_rewrite discrete_fun_lookup_singleton.
      setoid_rewrite discrete_fun_lookup_insert.
      intro γ0.
      have h1 : Decision (γ = γ0) by solve_decision. destruct h1.
      * subst γ0. rewrite lookup_op. rewrite lookup_insert. rewrite lookup_insert.
        unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
        unfold project in p1eqn.
        destruct (p1 (inG_id i) !! γ) eqn:p1eqn'; try discriminate.
        inversion p1eqn.
        rewrite p1eqn'. f_equiv.
        rewrite <- (cmra_morphism_op _).
        rewrite <- cmra_transport_op.
        simpl in req_eq. setoid_rewrite req_eq. setoid_rewrite <- H6.
        rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
        setoid_rewrite own.inG_unfold_fold. 
        trivial.
      * rewrite lookup_op. rewrite lookup_insert_ne; trivial.
        rewrite lookup_insert_ne; trivial.
        rewrite lookup_empty.
        rewrite op_None_left_id.
        trivial.
    + setoid_rewrite discrete_fun_lookup_op.
      setoid_rewrite discrete_fun_lookup_singleton_ne; trivial.
      setoid_rewrite discrete_fun_lookup_insert_ne; trivial.
      apply ucmra_unit_left_id.
  - have ineq1 := discrete_fun_insert_incl_iRes_singleton n m p1 γ.
    destruct (project p2 γ) eqn:p2eqn.
    + assert (project p2 γ ≡ Some c0) as p2eqn'. { rewrite p2eqn. trivial. }
      have ineq2 := iRes_incl_from_proj γ c0 p2 n p2eqn'.
      have ineq3 := Some_incl_Some_Some_to_iRes_singleton_incl _ _ _ _ γ res_incl.
      apply (incl_stuff3 _ _ _ _ _ _ ineq3 ineq1 ineq2).
    + have ineq3 := Some_incl_Some_None_to_iRes_singleton_incl _ _ _ γ res_incl.
      apply (incl_stuff4 _ _ _ _ _ ineq3 ineq1).
Qed.
  
End ConjunctOwnRule.

Section ConjunctOwnRuleU.

Context {Σ: gFunctors}.
Context {A: ucmra}.
Context `{i : !inG Σ A}.
Implicit Types a : A.
Context `{Disc : CmraDiscrete A}.

Lemma incl_opq (x: A) (a: option A)
  : x ≼ x ⋅? a.
Proof.
  destruct a.
  - unfold "⋅?". unfold "≼". exists u. trivial.
  - unfold "⋅?". unfold "≼". exists ε. symmetry. apply ucmra_unit_right_id.
Qed.

Definition opt_to_unital (x: option A) := match x with Some x' => x' | None => ε end.
Lemma q_dot_equiv (x: A) (w: option A) : (x ⋅? w) ≡ (x ⋅ opt_to_unital w).
Proof.
  destruct w; trivial. unfold opt_to_unital. rewrite ucmra_unit_right_id. trivial.
Qed.

Lemma andsep_to_sepand_ucmra γ (x y: A) (P : iProp Σ)
  (cond: ∀ (p1 p2 r1 r2 : A) , (✓ (p1 ⋅ p2))
      -> (x ⋅ r1 ≡ p1 ⋅ p2)
      -> (y ⋅ r2 ≡ p1)
      -> ∃ (m: A) , y ⋅ m ≡ p1 /\ x ≼ m ⋅ p2)
  : (own γ x ∧ (own γ y ∗ P)) ⊢ (own γ y ∗ (own γ x ∧ P)).
Proof using A Disc i Σ.
  apply andsep_to_sepand.
  intros n p1 p2 r1 r2 val eq1 eq2.
  setoid_rewrite q_dot_equiv in val.
  setoid_rewrite q_dot_equiv in eq1.
  setoid_rewrite q_dot_equiv in eq2.
  have cond0 := cond p1 (opt_to_unital p2) (opt_to_unital r1) (opt_to_unital r2) val eq1 eq2.
  destruct cond0 as [m [cond1 cond2]]. exists (Some m).
  unfold "⋅?".
  split; trivial.
  destruct p2.
  - unfold opt_to_unital in cond2.
    unfold included in cond2. destruct cond2 as [z cond2].
    unfold includedN. exists (Some z). 
    unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
    setoid_rewrite cond2. trivial.
  - unfold opt_to_unital in cond2.
    unfold included in cond2. destruct cond2 as [z cond2].
    unfold includedN. exists (Some z). 
    unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
    generalize cond2.
    rewrite ucmra_unit_right_id.
    intro cond2'.
    setoid_rewrite cond2'. trivial.
Qed.

End ConjunctOwnRuleU.

