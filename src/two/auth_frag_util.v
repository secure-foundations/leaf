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

Require Import Two.conjunct_own_rule.

Section AuthFragUtil.

Context {C : ucmra}.
Context {Σ: gFunctors}.
Context {m: inG Σ (authUR C)}.
Context `{Disc : CmraDiscrete C}.

Lemma auth_inved_conjure_frag γ (p q: C)
    (cond: p ⋅ q ≡ p)
    : own γ (● p) ==∗ own γ (● p) ∗ own γ (◯ q).
Admitted.

Lemma own_sep_auth_incll γ (p1 p2 state : C)
    (cond: ∀ z , p1 ⋅ z ≡ state -> ✓ (p2 ⋅ z))
    : own γ (◯ p1) ∗ own γ (● state) ⊢
        (∃ z , ⌜ p1 ⋅ z ≡ state ⌝ ∗ own γ (◯ p2) ∗ own γ (● (p2 ⋅ z)))%I.
Admitted.

Lemma auth_frag_conjunct (x y : C) (γ : gname)
    : own γ (● x) ∧ own γ (◯ y) ⊢ ⌜ y ≼ x ⌝.
Proof.
Admitted.
(*
  iIntros "x".
  iDestruct (and_own with "x") as "%e".
  destruct e as [z [val [[t1 l1] [t2 l2]]]].
  setoid_rewrite l1 in l2.
  iPureIntro.
  
  apply auth_both_valid_discrete.
  
  destruct t2.
    - rename c into t2.
      assert (∃ l , (● x) ⋅ l ≡ t2) as exl.
      {
        unfold "⋅?" in l2. destruct t1.
        + destruct c, t2. unfold "●" in l2. unfold "◯" in l2.
          unfold "●V" in l2. unfold "◯V" in l2.
          unfold "⋅", viewR in l2.
      }
  
  destruct t1, t2.
  - unfold "⋅?" in l2.
      destruct c, c0.
      *)

End AuthFragUtil.
