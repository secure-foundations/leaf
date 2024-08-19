From stdpp Require Import fin.

Definition f n m (p : fin n) := m < p.

Lemma test : f 47 13 32.
Proof. vm_compute. lia. Qed.
