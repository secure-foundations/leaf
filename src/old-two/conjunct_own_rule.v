From iris.algebra Require Export cmra.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.

From iris.algebra Require Import auth.

Section ConjunctOwnRule.

Context {Σ: gFunctors}.
Context `{i : !inG Σ A}.
Implicit Types a : A.

Lemma stuff (x y: A) (𝛾: gname)  :
    ((▷ (x ≡ y)) : iProp Σ) ⊢ □ (▷ (x ≡ y)).
Proof.
  iIntros.
    
Context `{Disc : CmraDiscrete A}.

Definition project (x: iResUR Σ) (𝛾: gname) : option A :=
  match (x (inG_id i) !! 𝛾) with
  | Some t => Some (cmra_transport (eq_sym inG_prf) (inG_fold t))
  | None => None
  end.

Lemma valid_project (x: iResUR Σ) (𝛾: gname) (n: nat) :
    ✓{n} x -> ✓{n} (project x 𝛾).
Proof.
  intros.
  unfold project.
  destruct (x (inG_id i) !! 𝛾) eqn:p.
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

Lemma project_iRes_singleton (x: A) (𝛾: gname)
  : project (iRes_singleton 𝛾 x) 𝛾 ≡ Some x.
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

Lemma proper_project_equiv_n 𝛾 (n: nat) : Proper ((≡{n}≡) ==> (≡{n}≡)) (λ x , project x 𝛾).
Proof.
  unfold Proper, "==>". intros. unfold project.
  assert (x (inG_id i) !! 𝛾 ≡{n}≡ y (inG_id i) !! 𝛾) as M.
  {
      enough (x (inG_id i) ≡{n}≡ y (inG_id i)).
      { trivial. }
      trivial.
  }
  destruct (x (inG_id i) !! 𝛾);
  destruct (y (inG_id i) !! 𝛾).
  - assert (o ≡{n}≡ o0) as Q.
    + unfold "≡" in M. unfold ofe_equiv, optionO, option_equiv in M.
          inversion M. trivial.
    + setoid_rewrite Q. trivial.
  - inversion M.
  - inversion M.
  - trivial.
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

Lemma and_own 𝛾 (x y: A)
  : (own 𝛾 x ∧ own 𝛾 y) ⊢ 
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
  
  destruct (project x0 𝛾) eqn:p.
  - exists c. split.
    { rewrite (cmra_discrete_valid_iff n).
        enough (✓{n} Some c) by trivial. rewrite <- p. apply valid_project. trivial.
    }
    split.
    {
      unfold includedN in o1.
      destruct o1 as [t o1]. exists (project t 𝛾).
      unfold included.
      apply (discrete_equiv _ _ n).
      apply some_op_equiv2. rewrite <- p.
      setoid_rewrite <- (project_iRes_singleton x 𝛾).
      setoid_rewrite <- project_op.
      apply proper_project_equiv_n. trivial.
    }
    {
      unfold includedN in o2.
      destruct o2 as [t o2]. exists (project t 𝛾).
      unfold included.
      apply (discrete_equiv _ _ n).
      apply some_op_equiv2. rewrite <- p.
      setoid_rewrite <- (project_iRes_singleton y 𝛾).
      setoid_rewrite <- project_op.
      apply proper_project_equiv_n. trivial.
    }
  - unfold includedN in o1.
      destruct o1 as [t o1].
      assert (project x0 𝛾 ≡{n}≡ project (iRes_singleton 𝛾 x) 𝛾 ⋅ project t 𝛾) as R.
      { setoid_rewrite <- project_op. apply proper_project_equiv_n. trivial. }
      setoid_rewrite project_iRes_singleton in R.
      rewrite p in R.
      have j := None_Some_contra _ _ _ R.
      contradiction.
Qed.
  
End ConjunctOwnRule.
