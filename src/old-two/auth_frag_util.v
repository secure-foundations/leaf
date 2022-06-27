From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

Require Import Two.own_updates2.

Section AuthFragUtil.

Context {C : ucmra}.
Context {Σ: gFunctors}.
Context {m: inG Σ (authUR C)}.

Program Definition helper_nPred  (x x' z : C) (t: auth C) : nPred :=
    {| nPred_holds n := ∃ p ,
        t ≡{n}≡ ● (x' ⋅ p) ⋅ ◯ x' /\ x ⋅ p ≡{n}≡ z |}.
Next Obligation.
  intros. simpl. simpl in H.
  destruct H. exists x0.
  intuition.
  - apply dist_le with (n := n1); trivial.
  - apply dist_le with (n := n1); trivial.
Qed.

Lemma is_frag_if_val n (z x : C) c
    : ✓{n} (● z ⋅ ◯ x ⋅ c) -> ∃ y , c = ◯ y. Admitted.
    
Lemma get_remainder_to_auth2 n (z x : C)
    : ✓{n} (● z ⋅ ◯ x) → ∃ x1 , z ≡{n}≡ x ⋅ x1. Admitted.
    
Lemma get_remainder_to_auth3 n (z x x0 : C)
    : ✓{n} (● z ⋅ ◯ x ⋅ ◯ x0) → ∃ x1 , z ≡{n}≡ x ⋅ x0 ⋅ x1. Admitted.

Lemma valid_auth3_frag2 n (x x0 x1 : C)
    (isv: ✓{n} (x ⋅ x0 ⋅ x1))
    : ✓{n} (● (x ⋅ x0 ⋅ x1) ⋅ ◯ x ⋅ ◯ x0). Admitted.
    
Lemma valid_auth2_frag1 n (x x0 : C)
    (isv: ✓{n} (x ⋅ x0))
    : ✓{n} (● (x ⋅ x0) ⋅ ◯ x). Admitted.
    
Lemma valid_of_valid_auth_dot_stuff n (x : C) stuff1
    : ✓{n} (● x ⋅ stuff1) -> ✓{n}(x). Admitted.
    
Lemma valid_of_valid_auth_dot_stuff2 n (x : C) stuff1 stuff2
    : ✓{n} (● x ⋅ stuff1 ⋅ stuff2) -> ✓{n}(x). Admitted.

Lemma update_ex_n_auth_frag (x x' z : C)
  (cond: ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y))
  : update_ex_n (● z ⋅ ◯ x) (helper_nPred x x' z).
Proof using C m Σ.
  unfold update_ex_n.
  intros.
  destruct mz.
  - unfold "⋅?" in *.
      have j := is_frag_if_val _ _ _ _ H. destruct j. subst c.
      have r := get_remainder_to_auth3 _ _ _ _ H. destruct r.
      setoid_rewrite H0 in H.
      exists (● (x' ⋅ x0 ⋅ x1) ⋅ ◯ x').
      unfold nPred_holds, helper_nPred.
      split.
      {
        exists (x0 ⋅ x1). split; trivial.
        - rewrite (assoc op). trivial.
        - rewrite (assoc op). trivial.
      }
      { 
        apply valid_auth3_frag2.
        rewrite <- (assoc op).
        apply cond.
        rewrite (assoc op).
        apply (valid_of_valid_auth_dot_stuff2 _ _ _ _ H).
      }
  - unfold "⋅?" in *.
      have r := get_remainder_to_auth2 _ _ _ H. destruct r.
      setoid_rewrite H0 in H. rename x0 into x1.
      exists (● (x' ⋅ x1) ⋅ ◯ x').
      unfold nPred_holds, helper_nPred.
      split.
      {
        exists x1. split; trivial.
      }
      { 
        apply valid_auth2_frag1.
        apply cond.
        apply (valid_of_valid_auth_dot_stuff _ _ _ H).
      }
Qed.

Definition nondet_auth_update_helper (𝛾: gname) (x x' z : C)
  (cond: ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y)) :
    own 𝛾 (● z ⋅ ◯ x) ==∗
    ∃ t , uPred_of_nPred (helper_nPred x x' z t) ∗ own 𝛾 t.
Proof.
  apply own_updatePN.
  apply update_ex_n_auth_frag. trivial.
Qed.

Definition helper_nPred_entail (x x' z : C) (t: auth C)
    : (uPred_of_nPred (helper_nPred x x' z t) : iProp Σ)
      ⊢ (∃ p , t ≡ ● (x' ⋅ p) ⋅ ◯ x' ∗ x ⋅ p ≡ z) % I.
Proof.
  split. intros.
  unfold uPred_holds, uPred_of_nPred in H0.
  unfold nPred_holds, helper_nPred in H0.
  uPred.unseal.
  unfold uPred_holds, uPred_exist_def.
  destruct H0. destruct H0.
  exists x1.
  unfold uPred_holds, uPred_sep_def.
  exists ε, x0.
  split.
  { rewrite left_id. reflexivity. }
  split.
  { 
    unfold uPred_holds, uPred_internal_eq_def. trivial.
  }
  { 
    unfold uPred_holds, uPred_internal_eq_def. trivial.
  }
Qed.


Definition nondet_auth_update (𝛾: gname) (x x' z : C)
  (cond: ∀ y n , ✓{n}(x ⋅ y) → ✓{n}(x' ⋅ y)) :
    own 𝛾 (● z ⋅ ◯ x) ==∗
    ∃ p , own 𝛾 (● (x' ⋅ p) ⋅ ◯ x') ∗ (z ≡ x ⋅ p).
Proof.
  iIntros "O".
  iMod (nondet_auth_update_helper 𝛾 x x' with "O") as (t) "[un O]".
    { trivial. }
  iDestruct (helper_nPred_entail with "un") as (p) "[t_eq z_eq]".
  iModIntro.
  iExists p.
  iFrame.
  iRewrite "z_eq".
  iRewrite "t_eq" in "O".
  iFrame.
  done.
Qed.

End AuthFragUtil.
