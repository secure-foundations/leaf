From iris.proofmode Require Import tactics.
From iris.si_logic Require Import bi.

Section si_logic_tests.
  Implicit Types P Q R : siProp.

  Lemma test_everything_persistent P : P -∗ P.
  Proof. by iIntros "#HP". Qed.

  Lemma test_everything_affine P : P -∗ True.
  Proof. by iIntros "_". Qed.

  Lemma test_iIntro_impl P Q R : ⊢ P → Q ∧ R → P ∧ R.
  Proof. iIntros "#HP #[HQ HR]". auto. Qed.

  Lemma test_iApply_impl_1 P Q R : ⊢ P → (P → Q) → Q.
  Proof. iIntros "HP HPQ". by iApply "HPQ". Qed.

  Lemma test_iApply_impl_2 P Q R : ⊢ P → (P → Q) → Q.
  Proof. iIntros "#HP #HPQ". by iApply "HPQ". Qed.
End si_logic_tests.
