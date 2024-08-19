From iris.algebra Require Import gset.

Lemma test_op (X Y : gset nat) : X ⊆ Y → X ⋅ Y = Y.
Proof. set_solver. Qed.
Lemma test_included (X Y : gset nat) : X ≼ Y → X ∪ Y = Y ∧ X ∩ Y = X.
Proof. set_solver. Qed.

Lemma test_disj_included (X Y : gset nat) : GSet X ≼ GSet Y → X ∪ Y = Y ∧ X ∩ Y = X.
Proof. set_solver. Qed.
Lemma test_disj_equiv n : GSet (∅ : gset nat) ≡ GSet {[n]} → False.
Proof. set_solver. Qed.
Lemma test_disj_eq n : GSet (∅ : gset nat) = GSet {[n]} → False.
Proof. set_solver. Qed.
Lemma test_disj_valid (X Y : gset nat) : ✓ (GSet X ⋅ GSet Y) → X ∩ Y = ∅.
Proof. set_solver. Qed.
