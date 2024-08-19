From stdpp Require Import tactics strings.
Unset Mangle Names.

Check "eunify_test".
Lemma eunify_test : ∀ x y, 0 < S x + y.
Proof.
  intros x y.
  (* Test that Ltac matching fails, otherwise this test is pointless *)
  Fail
    match goal with
    | |- 0 < S _ => idtac
    end.
  (* [eunify] succeeds *)
  match goal with
  | |- 0 < ?x => eunify x (S _)
  end.
  match goal with
  | |- 0 < ?x => let y := open_constr:(_) in eunify x (S y); idtac y
  end.
  lia.
Qed.

Check "eunify_test_evars".
Lemma eunify_test_evars : ∃ x y, 0 < S x + y.
Proof.
  eexists _, _.
  (* Test that Ltac matching fails, otherwise this test is pointless *)
  Fail
    match goal with
    | |- 0 < S _ => idtac
    end.
  (* [eunify] succeeds even if the goal contains evars *)
  match goal with
  | |- 0 < ?x => eunify x (S _)
  end.
  (* Let's try to use [eunify] to instantiate the first evar *)
  match goal with
  | |- 0 < ?x => eunify x (1 + _)
  end.
  (* And the other evar *)
  match goal with
  | |- 0 < ?x => eunify x 2
  end.
  lia.
Qed.
