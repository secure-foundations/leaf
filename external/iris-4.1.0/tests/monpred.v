From stdpp Require Import strings.
From iris.base_logic Require Import bi.
From iris.bi Require Import embedding monpred.

Section tests_unseal.
  Context {I : biIndex} (M : ucmra).

  Local Notation monPred := (monPred I (uPredI M)).

  Check "monPred_unseal_test_1".
  Lemma monPred_unseal_test_1 P Q (R : monPred) :
    ⎡ P ∗ Q ⎤ ∗ R ⊣⊢ False.
  Proof.
    intros. split=> i. monPred.unseal.
    (** Make sure [∗] on uPred is not unfolded *)
    Show.
  Abort.

  Check "monPred_unseal_test_2".
  Lemma monPred_unseal_test_2 P Q (R : monPred) :
    ⎡ P ∗ Q ⎤ ∗ R ⊣⊢ False.
  Restart.
    uPred.unseal.
    (** Make sure [∗] on monPred is not unfolded *)
    Show.
  Abort.
End tests_unseal.
