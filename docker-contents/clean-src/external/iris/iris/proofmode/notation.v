From stdpp Require Export strings.
From iris.proofmode Require Import coq_tactics environments.
From iris.prelude Require Import options.

Declare Scope proof_scope.
Delimit Scope proof_scope with env.
Global Arguments Envs _ _%proof_scope _%proof_scope _.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _%proof_scope _%string _%I.

Notation "" := Enil (only printing) : proof_scope.
Notation "Γ H : P" := (Esnoc Γ (INamed H) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  '[' P ']' '//'", only printing) : proof_scope.
Notation "Γ '_' : P" := (Esnoc Γ (IAnon _) P%I)
  (at level 1, P at level 200,
   left associativity, format "Γ '_'  :  '[' P ']' '//'", only printing) : proof_scope.

Notation "Γ '--------------------------------------' □ Δ '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Γ Δ _) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Δ '--------------------------------------' ∗ '//' Q '//'", only printing) :
  stdpp_scope.
Notation "Δ '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Enil Δ _) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Δ '--------------------------------------' ∗ '//' Q '//'", only printing) : stdpp_scope.
Notation "Γ '--------------------------------------' □ Q" :=
  (envs_entails (Envs Γ Enil _) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Q '//'", only printing)  : stdpp_scope.
Notation "'--------------------------------------' ∗ Q" := (envs_entails (Envs Enil Enil _) Q%I)
  (at level 1, Q at level 200, format "'--------------------------------------' ∗ '//' Q '//'", only printing) : stdpp_scope.
