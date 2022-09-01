From iris.algebra Require Import proofmode_classes.
From iris.proofmode Require Import classes.
From iris.base_logic Require Export derived.
From iris.prelude Require Import options.

Import base_logic.bi.uPred.

(* Setup of the proof mode *)
Section class_instances.
Context {M : ucmra}.
Implicit Types P Q R : uPred M.

Global Instance into_pure_cmra_valid `{!CmraDiscrete A} (a : A) :
  @IntoPure (uPredI M) (✓ a) (✓ a).
Proof. by rewrite /IntoPure discrete_valid. Qed.

Global Instance from_pure_cmra_valid {A : cmra} (a : A) :
  @FromPure (uPredI M) false (✓ a) (✓ a).
Proof.
  rewrite /FromPure /=. eapply bi.pure_elim=> // ?.
  rewrite -uPred.cmra_valid_intro //.
Qed.

Global Instance from_sep_ownM (a b1 b2 : M) :
  IsOp a b1 b2 →
  FromSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /FromSep -ownM_op -is_op. Qed.
Global Instance from_sep_ownM_core_id (a b1 b2 : M) :
  IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
  FromAnd (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  intros ? H. rewrite /FromAnd (is_op a) ownM_op.
  destruct H; by rewrite bi.persistent_and_sep.
Qed.

Global Instance into_and_ownM p (a b1 b2 : M) :
  IsOp a b1 b2 → IntoAnd p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof.
  intros. apply bi.intuitionistically_if_mono. by rewrite (is_op a) ownM_op bi.sep_and.
Qed.

Global Instance into_sep_ownM (a b1 b2 : M) :
  IsOp a b1 b2 → IntoSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2).
Proof. intros. by rewrite /IntoSep (is_op a) ownM_op. Qed.
End class_instances.
