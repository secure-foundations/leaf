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
  | Some t => Some (cmra_transport (eq_sym inG_prf) (inG_fold t))
  | None => None
  end.

Lemma valid_project (x: iResUR Σ) (γ: gname) (n: nat) :
    ✓{n} x -> ✓{n} (project x γ).
Proof.
  intros.
  unfold project.
  destruct (x (inG_id i) !! γ) eqn:p.
  - apply cmra_transport_validN.
    rewrite <- inG_unfold_validN.
    setoid_rewrite inG_unfold_fold.
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
      unfold inG_fold.
      apply cmra_morphism_op.
      typeclasses eauto.
  - rewrite p1. rewrite p2. trivial.
      (*replace (Some o ⋅ None) with (Some o) by trivial. trivial.*)
  - rewrite p1. rewrite p2. trivial.
      (*replace (None ⋅ Some o) with (Some o) by trivial. trivial.*)
  - rewrite p1. rewrite p2. trivial.
Qed.

Lemma project_iRes_singleton (x: A) (γ: gname)
  : project (iRes_singleton γ x) γ ≡ Some x.
Proof.
  unfold project, iRes_singleton.
  setoid_rewrite discrete_fun_lookup_singleton.
  rewrite lookup_singleton.
  f_equiv.
  setoid_rewrite inG_fold_unfold.
  rewrite cmra_transport_trans eq_trans_sym_inv_r /=.
  trivial.
Qed.

Lemma some_op_equiv2 (a b : A) (c: option A) (n: nat)
  : Some a ≡{n}≡ Some b ⋅ c -> a ≡{n}≡ b ⋅? c.
Proof. intros. unfold "⋅?". destruct c.
  - inversion H. trivial.
  - inversion H. trivial.
Qed.

Lemma discrete_equiv (a b : A) (n: nat)
  : a ≡{n}≡ b -> a ≡ b.
Proof using A Disc.
  intros.
  apply discrete. { typeclasses eauto. }
  apply dist_le with (n0 := n); trivial. lia.
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
    (@iRes_singleton Σ A i).
Proof.
  unfold Proper, "==>". intros γ γ0 e x y H. subst γ0.
  unfold iRes_singleton. 
  f_equiv.
  apply: singletonM_proper.
  setoid_rewrite H.
  trivial.
Qed.

Lemma None_Some_contra (x: A) (y: option A) (n: nat)
  (k: None ≡{n}≡ Some x ⋅ y) : False.
Proof.
  (*have k := discrete_equiv2 _ _ _ t.*)
  destruct y.
  - unfold "⋅" in k. unfold optionR in k. unfold cmra_op in k. unfold option_op_instance in k.
      unfold union_with in k. unfold option_union_with in k. inversion k.
  - unfold "⋅" in k. unfold optionR in k. unfold cmra_op in k. unfold option_op_instance in k.
      unfold union_with in k. unfold option_union_with in k. inversion k.
Qed.

Lemma and_own γ (x y: A)
  : (own γ x ∧ own γ y) ⊢ 
  ((⌜ ∃ z , ✓ z ∧ (∃ t , z ≡ x ⋅? t) ∧ (∃ t , z ≡ y ⋅? t) ⌝) : iProp Σ).
Proof using A Disc i Σ.
  uPred.unseal.
  split.
  intros n x0 val aoo.
  unfold uPred_pure_def. unfold uPred_holds.
  rewrite own_eq in aoo.
  unfold own_def in aoo.
  unfold uPred_holds in aoo. unfold uPred_and_def in aoo.
  destruct aoo as [o1 o2].
  rewrite uPred_ownM_eq in o1.
  rewrite uPred_ownM_eq in o2.
  unfold uPred_holds in o1. unfold uPred_ownM_def in o1.
  unfold uPred_holds in o2. unfold uPred_ownM_def in o2.
  
  destruct (project x0 γ) eqn:p.
  - exists c. split.
    { rewrite (cmra_discrete_valid_iff n).
        enough (✓{n} Some c) by trivial. rewrite <- p. apply valid_project. trivial.
    }
    split.
    {
      unfold includedN in o1.
      destruct o1 as [t o1]. exists (project t γ).
      unfold included.
      apply (discrete_equiv _ _ n).
      apply some_op_equiv2. rewrite <- p.
      setoid_rewrite <- (project_iRes_singleton x γ).
      setoid_rewrite <- project_op.
      apply proper_project_equiv_n; trivial.
    }
    {
      unfold includedN in o2.
      destruct o2 as [t o2]. exists (project t γ).
      unfold included.
      apply (discrete_equiv _ _ n).
      apply some_op_equiv2. rewrite <- p.
      setoid_rewrite <- (project_iRes_singleton y γ).
      setoid_rewrite <- project_op.
      apply proper_project_equiv_n; trivial.
    }
  - unfold includedN in o1.
      destruct o1 as [t o1].
      assert (project x0 γ ≡{n}≡ project (iRes_singleton γ x) γ ⋅ project t γ) as R.
      { setoid_rewrite <- project_op. apply proper_project_equiv_n; trivial. }
      setoid_rewrite project_iRes_singleton in R.
      rewrite p in R.
      have j := None_Some_contra _ _ _ R.
      contradiction.
Qed.

Lemma proj_op γ x (w a : iResUR Σ) n
  (eq: w ≡{n}≡ iRes_singleton γ x ⋅ a)
  : project w γ ≡{n}≡ Some (x ⋅? project a γ).
Proof.
  assert (project w γ ≡{n}≡ project (iRes_singleton γ x ⋅ a) γ) as X. {
    apply proper_project_equiv_n; trivial.
  }
  setoid_rewrite X.
  setoid_rewrite project_op.
  setoid_rewrite project_iRes_singleton.
  destruct (project a γ); trivial.
Qed.

(* copied from iris basic_logic/lib/own.v *)
Lemma iRes_singleton_op γ a1 a2 :
  iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2. 
Proof.
  rewrite /iRes_singleton discrete_fun_singleton_op singleton_op cmra_transport_op.
  f_equiv. apply: singletonM_proper. apply (cmra_morphism_op _). 
Qed.

(*
Lemma iRes_singleton_opq
    iRes_singleton γ (x ⋅? project a γ) ≡ iRes_singleton γ x ⋅ 
    *)

(*Lemma iRes_singleton_project included*)

Lemma iRes_incl_from_proj γ x w n :
  project w γ ≡ Some x ->
      iRes_singleton γ x ≼{n} w.
Proof.
  intro p.
  unfold project in p.
  destruct (w (inG_id i) !! γ) eqn:e.
  - assert ((cmra_transport (eq_sym inG_prf) (inG_fold o)) ≡ x) as X.
    { unfold "≡", ofe_equiv, optionO, option_equiv in p. inversion p. trivial. }
    unfold includedN.
    unfold iRes_singleton.
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
        setoid_rewrite inG_unfold_fold. trivial.
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

Lemma iRes_singleton_incl (a b : A) γ n :
  a ≼ b ->
  iRes_singleton γ a ≼{n} iRes_singleton γ b.
Proof.
  intro x.
  unfold "≼" in x. destruct x as [z x].
  assert (iRes_singleton γ b ≡{n}≡ iRes_singleton γ (a ⋅ z)) as X.
  {
    apply proper_iRes_singleton_equiv_equiv_n; trivial.
  }
  setoid_rewrite X.
  setoid_rewrite iRes_singleton_op.
  unfold includedN.
  exists (iRes_singleton γ z).
  trivial.
Qed.

Lemma and_own2 γ (x y z: A)
  (cond: ∀ (a b : option A) , x ⋅? a ≡ y ⋅? b -> ✓(x ⋅? a) -> ∃ (c: option A) , x ⋅? a ≡ z ⋅? c)
  : (own γ x ∧ own γ y) ⊢ own γ z.
Proof using A Disc i Σ.
  uPred.unseal.
  
  split.
  intros n w valx uh.
  
  unfold uPred_holds, uPred_and_def in uh. destruct uh as [xh yh].
  
  rewrite own_eq in xh. unfold own_def in xh.
  rewrite uPred_ownM_eq in xh.
  unfold uPred_holds, uPred_ownM_def in xh.
  unfold includedN in xh. destruct xh as [a xh].
  
  rewrite own_eq in yh. unfold own_def in yh.
  rewrite uPred_ownM_eq in yh.
  unfold uPred_holds, uPred_ownM_def in yh.
  unfold includedN in yh. destruct yh as [b yh].
  
  have eq1 := proj_op γ x w a n xh.
  have eq2 := proj_op γ y w b n yh.
  assert (x ⋅? project a γ ≡ y ⋅? project b γ) as xa_yb. {
      apply (discrete_equiv _ _ n).
      setoid_rewrite eq1 in eq2.
      inversion eq2. trivial.
  }
  
  assert (✓ (x ⋅? project a γ)) as val.
  {
    rewrite (cmra_discrete_valid_iff n).
    enough (✓{n} Some ((x ⋅? project a γ))) by trivial.
    setoid_rewrite <- eq1.
    apply valid_project.
    trivial.
  }
  
  have cond0 := cond (project a γ) (project b γ) xa_yb val.
  destruct cond0 as [c cond0].
  
  rewrite own_eq. unfold own_def.
  rewrite uPred_ownM_eq.
  unfold uPred_holds, uPred_ownM_def.
  
  assert (iRes_singleton γ (x ⋅? project a γ) ≼{n} w) as incl1.
  { apply iRes_incl_from_proj. apply (discrete_equiv_opt _ _ n). trivial. }
  
  destruct c.
  + assert (
      iRes_singleton γ z
      ≼{n}
      iRes_singleton γ (x ⋅? project a γ)
    ) as incl2.
    {
      apply iRes_singleton_incl.
      unfold "⋅?" in cond0 at 2.
      unfold "≼".
      exists c.
      trivial.
    }
    eapply cmra_includedN_trans. { apply incl2. } apply incl1.
  + unfold "⋅?" in cond0 at 2.
    assert (
      iRes_singleton γ (x ⋅? project a γ)
      ≡{n}≡
      iRes_singleton γ z
    ) as X. { 
      apply proper_iRes_singleton_equiv_equiv_n; trivial.
    }
    setoid_rewrite <- X.
    trivial.
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

Lemma and_own2_ucmra γ (x y z: A)
  (cond: ∀ w , ✓ w -> x ≼ w -> y ≼ w -> z ≼ w)
  : (own γ x ∧ own γ y) ⊢ (own γ z).
Proof using A Disc i Σ.
  iIntros "t".
  iDestruct (and_own2 γ x y z with "t") as "t".
  {
    intros a b H val.
    assert (x ≼ x ⋅? a) as xxz. { apply incl_opq. }
    assert (y ≼ x ⋅? a) as yxz. { setoid_rewrite H. apply incl_opq. }
    have c := cond (x ⋅? a) val xxz yxz.
    unfold "≼" in c. destruct c as [r c].
    exists (Some r).
    unfold "⋅?" at 2. trivial.
  }
  iFrame.
Qed.

End ConjunctOwnRuleU.
