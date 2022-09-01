From iris.algebra Require Export auth excl updates.
From iris.algebra Require Import local_updates.
From iris.prelude Require Import options.

(** Authoritative CMRA where the fragment is exclusively owned.
This is effectively a single "ghost variable" with two views, the frament [◯E a]
and the authority [●E a]. *)

Definition excl_authR (A : ofe) : cmra :=
  authR (optionUR (exclR A)).
Definition excl_authUR (A : ofe) : ucmra :=
  authUR (optionUR (exclR A)).

Definition excl_auth_auth {A : ofe} (a : A) : excl_authR A :=
  ● (Some (Excl a)).
Definition excl_auth_frag {A : ofe} (a : A) : excl_authR A :=
  ◯ (Some (Excl a)).

Typeclasses Opaque excl_auth_auth excl_auth_frag.

Global Instance: Params (@excl_auth_auth) 1 := {}.
Global Instance: Params (@excl_auth_frag) 2 := {}.

Notation "●E a" := (excl_auth_auth a) (at level 10).
Notation "◯E a" := (excl_auth_frag a) (at level 10).

Section excl_auth.
  Context {A : ofe}.
  Implicit Types a b : A.

  Global Instance excl_auth_auth_ne : NonExpansive (@excl_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance excl_auth_auth_proper : Proper ((≡) ==> (≡)) (@excl_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance excl_auth_frag_ne : NonExpansive (@excl_auth_frag A).
  Proof. solve_proper. Qed.
  Global Instance excl_auth_frag_proper : Proper ((≡) ==> (≡)) (@excl_auth_frag A).
  Proof. solve_proper. Qed.

  Global Instance excl_auth_auth_discrete a : Discrete a → Discrete (●E a).
  Proof. intros; apply auth_auth_discrete; [apply Some_discrete|]; apply _. Qed.
  Global Instance excl_auth_frag_discrete a : Discrete a → Discrete (◯E a).
  Proof. intros; apply auth_frag_discrete, Some_discrete; apply _. Qed.

  Lemma excl_auth_validN n a : ✓{n} (●E a ⋅ ◯E a).
  Proof. by rewrite auth_both_validN. Qed.
  Lemma excl_auth_valid a : ✓ (●E a ⋅ ◯E a).
  Proof. intros. by apply auth_both_valid_2. Qed.

  Lemma excl_auth_agreeN n a b : ✓{n} (●E a ⋅ ◯E b) → a ≡{n}≡ b.
  Proof.
    rewrite auth_both_validN /= => -[Hincl Hvalid].
    move: Hincl=> /Some_includedN_exclusive /(_ I) ?. by apply (inj Excl).
  Qed.
  Lemma excl_auth_agree a b : ✓ (●E a ⋅ ◯E b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=> n. by apply excl_auth_agreeN, cmra_valid_validN.
  Qed.
  Lemma excl_auth_agree_L `{!LeibnizEquiv A} a b : ✓ (●E a ⋅ ◯E b) → a = b.
  Proof. intros. by apply leibniz_equiv, excl_auth_agree. Qed.

  Lemma excl_auth_frag_validN_op_1_l n a b : ✓{n} (◯E a ⋅ ◯E b) → False.
  Proof. by rewrite -auth_frag_op auth_frag_validN. Qed.
  Lemma excl_auth_frag_valid_op_1_l a b : ✓ (◯E a ⋅ ◯E b) → False.
  Proof. by rewrite -auth_frag_op auth_frag_valid. Qed.

  Lemma excl_auth_update a b a' : ●E a ⋅ ◯E b ~~> ●E a' ⋅ ◯E a'.
  Proof.
    intros. by apply auth_update, option_local_update, exclusive_local_update.
  Qed.
End excl_auth.
