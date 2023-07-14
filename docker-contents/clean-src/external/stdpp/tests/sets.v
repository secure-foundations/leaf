From stdpp Require Import sets.

Lemma foo `{Set_ A C} (x : A) (X Y : C) : x ∈ X ∩ Y → x ∈ X.
Proof. intros Hx. set_unfold in Hx. tauto. Qed.
