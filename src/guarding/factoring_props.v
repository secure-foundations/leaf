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

From iris.bi Require Import derived_laws_later.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export wsat.

From iris.bi Require Import derived_laws.

Require Import guarding.internal.factoring_upred.

Section Factoring.

Context {Σ: gFunctors}.

(* For the "Point Proposition" formulation from the paper *)
Definition point_prop (P: iProp Σ) := ∃ x , (P ≡ uPred_ownM x).

Global Instance point_prop_proper :
    Proper ((≡) ==> (↔)) point_prop.
Proof.
  solve_proper.
Qed.

Lemma point_prop_True : point_prop True.
Proof.
  unfold point_prop in *.
  exists (ε). 
  iIntros. iSplit. { iIntros "T". iDestruct (uPred.ownM_unit with "T") as "T". iFrame. }
  iIntros "T". done.
Qed.


(* PointProp-Sep *)

Lemma point_prop_sep (P Q: iProp Σ)
  (a: point_prop P) (b: point_prop Q)  : point_prop (P ∗ Q).
Proof.
  unfold point_prop in *. destruct a as [x a]. destruct b as [y b].
  exists (x ⋅ y). setoid_rewrite a. setoid_rewrite b.
  rewrite uPred.ownM_op. trivial.
Qed.

Lemma point_prop_big_sepS `{!EqDecision X, !Countable X} (S : gset X) (P : X → iProp Σ)
    (x_point : ∀ (x: X) , x ∈ S → point_prop (P x))
    : point_prop ([∗ set] x ∈ S , P x).
Proof.
  induction S as [|x T ? IH] using set_ind_L. 
  - rewrite big_sepS_empty. apply point_prop_True.
  - rewrite big_sepS_union.
    + apply point_prop_sep.
      * rewrite big_sepS_singleton. apply x_point. set_solver.
      * apply IH. intros y yT. apply x_point. set_solver.
    + set_solver.
Qed.

Context `{i : !inG Σ A}.

Lemma own_separates_out γ (x: A) (P : iProp Σ)
  : (P -∗ own γ x) ∗ P ⊢ (
          own γ x ∗ (own γ x -∗ P)
      ).
Proof.
  rewrite own.own_eq. unfold own.own_def.
  apply uPred_ownM_separates_out.
Qed.

Lemma own_separates_out_except0 γ (x: A) (P : iProp Σ)
  : (P -∗ ◇ own γ x) ∗ P ⊢ (
          ◇ own γ x ∗ (own γ x -∗ P)
      ).
Proof.
  rewrite own.own_eq. unfold own.own_def.
  apply uPred_ownM_separates_out_except0.
Qed.

(* PointProp-Own *)

Lemma point_prop_own γ (x: A) : point_prop (own γ x).
Proof.
  rewrite own.own_eq. unfold own.own_def. unfold point_prop.
  exists (own.iRes_singleton γ x). trivial.
Qed.

Lemma own_separates_out_point (P : iProp Σ) (Q: iProp Σ)
  (point: point_prop Q)
  : (P -∗ Q) ∗ P ⊢ (
          Q ∗ (Q -∗ P)
      ).
Proof.
  unfold point_prop in point. destruct point as [x point]. setoid_rewrite point.
  apply uPred_ownM_separates_out.
Qed.

Lemma own_separates_out_except0_point (P : iProp Σ) (Q: iProp Σ)
    (point: point_prop Q)
  : (P -∗ ◇ Q) ∗ P ⊢ (
          ◇ Q ∗ (Q -∗ P)
      ).
Proof.
  unfold point_prop in point. destruct point as [x point]. setoid_rewrite point.
  apply uPred_ownM_separates_out_except0.
Qed.

Lemma own_separates_out_except0_point_later (P : iProp Σ) (Q: iProp Σ) (n: nat)
    (point: point_prop Q)
  : (P -∗ ▷^n ◇ Q) ∗ P ⊢ (
          ▷^n (◇ Q ∗ (Q -∗ P))
      ).
Proof.
  unfold point_prop in point. destruct point as [x point]. setoid_rewrite point.
  apply uPred_ownM_separates_out_except0_later.
Qed.

End Factoring.
