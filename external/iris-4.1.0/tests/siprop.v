From stdpp Require Import strings.
From iris.si_logic Require Import bi.
Unset Mangle Names.

Check "unseal_test".
Lemma unseal_test (P Q : siProp) (Φ : nat → siProp) :
  P ∧ ▷ Q ∧ (∃ x, Φ x) ⊣⊢ ∃ x, P ∗ ▷ Q ∧ emp ∨ Φ x.
Proof.
  siProp.unseal.
  Show.
Abort.

(** Make sure that [siProp]s are parsed in [bi_scope]. *)
Definition test : siProp := ▷ True.
Definition testI : siPropI := ▷ True.
