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

From iris.base_logic.lib Require Export invariants.

From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export fancy_updates_from_vs.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export wsat.

From iris.bi Require Import derived_laws.

Section SeparableAnd.

Context {Σ: gFunctors}.

(*
Lemma lemma0 x (P : iProp Σ)
  : (P ⊢ uPred_ownM x) ->
      P ⊢ (
          (uPred_ownM x)
          ∗ 
          ((uPred_ownM x) -∗ P)
      ).
Proof.
  uPred.unseal.
  intro H.
  split.
  intros n x0 val t.
  destruct H.
  unfold uPred_holds. unfold uPred_sep_def. intros.
  have h := uPred_in_entails n x0 val t.
  unfold uPred_holds in h. unfold uPred_ownM_def in h.
  unfold includedN in h. destruct h as [z h].
  exists x. exists z.
  split.
  { trivial. }
  split.
  { unfold uPred_holds. unfold uPred_ownM_def. trivial. }
  { unfold uPred_holds. unfold uPred_wand_def. intros n' x' incl val2 uh.
      unfold uPred_holds in uh.
      unfold uPred_ownM_def in uh.
      unfold includedN in uh. destruct uh as [w j].
      setoid_rewrite j.
      apply uPred_mono with (n1 := n) (x1 := x0); trivial.
      assert (z ⋅ (x ⋅ w) ≡ (z ⋅ x) ⋅ w) as associ. { apply cmra_assoc. }
      setoid_rewrite associ.
      assert ((z ⋅ x) ≡ (x ⋅ z)) as commu. { apply cmra_comm. }
      setoid_rewrite commu.
      unfold includedN. exists w.
      apply dist_le with (n0 := n); trivial.
      setoid_rewrite h.
      trivial.
  } 
Qed.
*)

Lemma uPred_ownM_separates_out x (P : iProp Σ)
  : (P -∗ uPred_ownM x) ∗ P ⊢ (
          (uPred_ownM x)
          ∗ 
          ((uPred_ownM x) -∗ P)
      ).
Proof.
  uPred.unseal.
  split.
  intros n x0 val t.
  
  unfold uPred_holds, uPred_sep_def in t.
  destruct t as [x1 [x2 [sum [t1 t2]]]].
  
  unfold uPred_holds, uPred_wand_def in t1.
  
  assert (✓{n} (x1 ⋅ x2)) as val_12. { setoid_rewrite <- sum. trivial. }
  assert (n ≤ n) as nle by trivial.
  have t11 := t1 n x2 nle val_12 t2.
  
  unfold uPred_holds in t11. unfold uPred_ownM_def in t11.
  unfold includedN in t11. destruct t11 as [z h].
  
  unfold uPred_holds. unfold uPred_sep_def.
  exists x. exists z.
  
  assert (uPred_holds P n x0) as ux0. {
    eapply uPred_mono. { apply t2. }
    { setoid_rewrite sum. unfold includedN. exists x1.
        rewrite cmra_comm. trivial. }
    trivial.
  }
  
  split.
  { setoid_rewrite sum. trivial. }
  split.
  { unfold uPred_holds. unfold uPred_ownM_def. trivial. }
  { unfold uPred_holds. unfold uPred_wand_def. intros n' x' incl val2 uh.
      unfold uPred_holds in uh.
      unfold uPred_ownM_def in uh.
      unfold includedN in uh. destruct uh as [w j].
      setoid_rewrite j.
      apply uPred_mono with (n1 := n) (x1 := x0); trivial.
      assert (z ⋅ (x ⋅ w) ≡ (z ⋅ x) ⋅ w) as associ. { apply cmra_assoc. }
      setoid_rewrite associ.
      assert ((z ⋅ x) ≡ (x ⋅ z)) as commu. { apply cmra_comm. }
      setoid_rewrite commu.
      unfold includedN. exists w.
      apply dist_le with (n0 := n); trivial.
      setoid_rewrite sum.
      setoid_rewrite h.
      trivial.
  } 
Qed.

Context `{i : !inG Σ A}.

Lemma own_separates_out γ (x: A) (P : iProp Σ)
  : (P -∗ own γ x) ∗ P ⊢ (
          own γ x ∗ (own γ x -∗ P)
      ).
Proof.
  rewrite own_eq. unfold own_def.
  apply uPred_ownM_separates_out.
Qed.


End SeparableAnd.
