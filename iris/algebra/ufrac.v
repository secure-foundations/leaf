(** This file provides an "unbounded" version of the fractional camera whose
elements are in the interval (0,..) instead of (0,1]. *)
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

(** Since the standard (0,1] fractional camera [frac] is used more often, we
define [ufrac] through a [Definition] instead of a [Notation]. That way, Coq
infers the [frac] camera by default when using the [Qp] type. *)
Definition ufrac := Qp.

Section ufrac.
  Implicit Types p q : ufrac.

  Canonical Structure ufracO := leibnizO ufrac.

  Local Instance ufrac_valid_instance : Valid ufrac := λ x, True.
  Local Instance ufrac_pcore_instance : PCore ufrac := λ _, None.
  Local Instance ufrac_op_instance : Op ufrac := λ x y, (x + y)%Qp.

  Lemma ufrac_op p q : p ⋅ q = (p + q)%Qp.
  Proof. done. Qed.
  Lemma ufrac_included p q : p ≼ q ↔ (p < q)%Qp.
  Proof. by rewrite Qp_lt_sum. Qed.

  Corollary ufrac_included_weak p q : p ≼ q → (p ≤ q)%Qp.
  Proof. rewrite ufrac_included. apply Qp_lt_le_incl. Qed.

  Definition ufrac_ra_mixin : RAMixin ufrac.
  Proof. split; try apply _; try done. Qed.
  Canonical Structure ufracR := discreteR ufrac ufrac_ra_mixin.

  Global Instance ufrac_cmra_discrete : CmraDiscrete ufracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance ufrac_cancelable q : Cancelable q.
  Proof. intros n p1 p2 _. apply (inj (Qp_add q)). Qed.
  Global Instance ufrac_id_free q : IdFree q.
  Proof. intros p _. apply Qp_add_id_free. Qed.

  Global Instance is_op_ufrac q : IsOp' q (q/2)%Qp (q/2)%Qp.
  Proof. by rewrite /IsOp' /IsOp ufrac_op Qp_div_2. Qed.
End ufrac.
