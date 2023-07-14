(* This is just an integration file for [iris_staging.algebra.list];
both should be stabilized together. *)
From iris.algebra Require Import cmra.
From iris.staging.algebra Require Import list monotone.
From iris.base_logic Require Import bi derived.
From iris.prelude Require Import options.

Section upred.
Context {M : ucmra}.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

Section list_cmra.
  Context {A : ucmra}.
  Implicit Types l : list A.

  Lemma list_validI l : ✓ l ⊣⊢ ∀ i, ✓ (l !! i).
  Proof. uPred.unseal; constructor=> n x ?. apply list_lookup_validN. Qed.
End list_cmra.

Section monotone.
  Lemma monotone_equivI {A : ofe} (R : relation A)
        `{!(∀ n : nat, Proper (dist n ==> dist n ==> iff) R)}
        `{!Reflexive R} `{!AntiSymm (≡) R} a b :
    principal R a ≡ principal R b ⊣⊢ (a ≡ b).
  Proof.
    uPred.unseal. do 2 split; intros ?.
    - exact: principal_injN.
    - exact: principal_ne.
  Qed.
End monotone.
End upred.
