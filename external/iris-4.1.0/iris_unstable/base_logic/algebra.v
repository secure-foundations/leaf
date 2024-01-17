(** This is just an integration file for [iris_staging.algebra.list];
both should be stabilized together. *)
From iris.algebra Require Import cmra.
From iris.unstable.algebra Require Import list.
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
End upred.
