(** This file provides a construction to lift a PROP-level binary relation to
its reflexive transitive closure. *)
From iris.bi.lib Require Export fixpoint.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.

(* The sections add extra BI assumptions, which is only picked up with "Type"*. *)
Set Default Proof Using "Type*".

Definition bi_rtc_pre `{!BiInternalEq PROP}
    {A : ofe} (R : A → A → PROP)
    (x2 : A) (rec : A → PROP) (x1 : A) : PROP :=
  <affine> (x1 ≡ x2) ∨ ∃ x', R x1 x' ∗ rec x'.

Global Instance bi_rtc_pre_mono `{!BiInternalEq PROP}
    {A : ofe} (R : A → A → PROP) `{NonExpansive2 R} (x : A) :
  BiMonoPred (bi_rtc_pre R x).
Proof.
  constructor; [|solve_proper].
  iIntros (rec1 rec2) "#H". iIntros (x1) "[Hrec | Hrec]".
  { by iLeft. }
  iRight.
  iDestruct "Hrec" as (x') "[HP Hrec]".
  iDestruct ("H" with "Hrec") as "Hrec". eauto with iFrame.
Qed.

Definition bi_rtc `{!BiInternalEq PROP}
    {A : ofe} (R : A → A → PROP) (x1 x2 : A) : PROP :=
  bi_least_fixpoint (bi_rtc_pre R x2) x1.

Global Instance: Params (@bi_rtc) 3 := {}.
Typeclasses Opaque bi_rtc.

Global Instance bi_rtc_ne `{!BiInternalEq PROP} {A : ofe} (R : A → A → PROP) :
  NonExpansive2 (bi_rtc R).
Proof.
  intros n x1 x2 Hx y1 y2 Hy. rewrite /bi_rtc Hx. f_equiv=> rec z.
  solve_proper.
Qed.

Global Instance bi_rtc_proper `{!BiInternalEq PROP} {A : ofe} (R : A → A → PROP)
  : Proper ((≡) ==> (≡) ==> (⊣⊢)) (bi_rtc R).
Proof. apply ne_proper_2. apply _. Qed.

Section bi_rtc.
  Context `{!BiInternalEq PROP}.
  Context {A : ofe}.
  Context (R : A → A → PROP) `{NonExpansive2 R}.

  Lemma bi_rtc_unfold (x1 x2 : A) :
    bi_rtc R x1 x2 ≡ bi_rtc_pre R x2 (λ x1, bi_rtc R x1 x2) x1.
  Proof. by rewrite /bi_rtc; rewrite -least_fixpoint_unfold. Qed.

  Lemma bi_rtc_strong_ind_l x2 Φ :
    NonExpansive Φ →
    □ (∀ x1, <affine> (x1 ≡ x2) ∨ (∃ x', R x1 x' ∗ (Φ x' ∧ bi_rtc R x' x2)) -∗ Φ x1) -∗
    ∀ x1, bi_rtc R x1 x2 -∗ Φ x1.
 Proof.
    iIntros (?) "#IH". rewrite /bi_rtc.
    by iApply (least_fixpoint_strong_ind (bi_rtc_pre R x2) with "IH").
  Qed.

  Lemma bi_rtc_ind_l x2 Φ :
    NonExpansive Φ →
    □ (∀ x1, <affine> (x1 ≡ x2) ∨ (∃ x', R x1 x' ∗ Φ x') -∗ Φ x1) -∗
    ∀ x1, bi_rtc R x1 x2 -∗ Φ x1.
  Proof.
    iIntros (?) "#IH". rewrite /bi_rtc.
    by iApply (least_fixpoint_ind (bi_rtc_pre R x2) with "IH").
  Qed.

  Lemma bi_rtc_refl x : ⊢ bi_rtc R x x.
  Proof. rewrite bi_rtc_unfold. by iLeft. Qed.

  Lemma bi_rtc_l x1 x2 x3 : R x1 x2 -∗ bi_rtc R x2 x3 -∗ bi_rtc R x1 x3.
  Proof.
    iIntros "H1 H2".
    iEval (rewrite bi_rtc_unfold /bi_rtc_pre). iRight.
    iExists x2. iFrame.
  Qed.

  Lemma bi_rtc_once x1 x2 : R x1 x2 -∗ bi_rtc R x1 x2.
  Proof. iIntros "H". iApply (bi_rtc_l with "H"). iApply bi_rtc_refl. Qed.

  Lemma bi_rtc_trans x1 x2 x3 : bi_rtc R x1 x2 -∗ bi_rtc R x2 x3 -∗ bi_rtc R x1 x3.
  Proof.
    iRevert (x1).
    iApply bi_rtc_ind_l.
    { solve_proper. }
    iIntros "!>" (x1) "[H | H] H2".
    { by iRewrite "H". }
    iDestruct "H" as (x') "[H IH]".
    iApply (bi_rtc_l with "H").
    by iApply "IH".
  Qed.

End bi_rtc.
