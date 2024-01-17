From iris.bi Require Import lib.fixpoint.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

Section fixpoint.
  Context {PROP : bi} `{!BiInternalEq PROP}
    {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.

  Definition L := bi_least_fixpoint F.
  Definition G := bi_greatest_fixpoint F.

  (* Make sure the lemmas [iApply] without having to repeat the induction
  predicate [Φ]. See https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/967
  for details. *)
  Lemma ind_test (a : A) :
    ∀ x, L x -∗ x ≡ a.
  Proof.
    iApply (least_fixpoint_ind F); first by solve_proper. Undo.
    iApply (least_fixpoint_ind_wf F); first by solve_proper. Undo.
  Abort.

  Lemma coind_test (a : A) :
    ∀ x, x ≡ a -∗ G x.
  Proof.
    iApply (greatest_fixpoint_coind F); first by solve_proper. Undo.
    iApply (greatest_fixpoint_paco F); first by solve_proper. Undo.
  Abort.

End fixpoint.
