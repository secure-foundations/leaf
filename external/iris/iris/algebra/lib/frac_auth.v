From iris.algebra Require Export frac auth updates local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

(** Authoritative CMRA where the NON-authoritative parts can be fractional.
  This CMRA allows the original non-authoritative element [◯ a] to be split into
  fractional parts [◯F{q} a]. Using [◯F a ≡ ◯F{1} a] is in effect the same as
  using the original [◯ a]. Currently, however, this CMRA hides the ability to
  split the authoritative part into fractions.
*)

Definition frac_authR (A : cmra) : cmra :=
  authR (optionUR (prodR fracR A)).
Definition frac_authUR (A : cmra) : ucmra :=
  authUR (optionUR (prodR fracR A)).

Definition frac_auth_auth {A : cmra} (x : A) : frac_authR A :=
  ● (Some (1%Qp,x)).
Definition frac_auth_frag {A : cmra} (q : frac) (x : A) : frac_authR A :=
  ◯ (Some (q,x)).

Typeclasses Opaque frac_auth_auth frac_auth_frag.

Global Instance: Params (@frac_auth_auth) 1 := {}.
Global Instance: Params (@frac_auth_frag) 2 := {}.

Notation "●F a" := (frac_auth_auth a) (at level 10).
Notation "◯F{ q } a" := (frac_auth_frag q a) (at level 10, format "◯F{ q }  a").
Notation "◯F a" := (frac_auth_frag 1 a) (at level 10).

Section frac_auth.
  Context {A : cmra}.
  Implicit Types a b : A.

  Global Instance frac_auth_auth_ne : NonExpansive (@frac_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_auth_proper : Proper ((≡) ==> (≡)) (@frac_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_frag_ne q : NonExpansive (@frac_auth_frag A q).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_frag_proper q : Proper ((≡) ==> (≡)) (@frac_auth_frag A q).
  Proof. solve_proper. Qed.

  Global Instance frac_auth_auth_discrete a : Discrete a → Discrete (●F a).
  Proof. intros; apply auth_auth_discrete; [apply Some_discrete|]; apply _. Qed.
  Global Instance frac_auth_frag_discrete q a : Discrete a → Discrete (◯F{q} a).
  Proof. intros; apply auth_frag_discrete, Some_discrete; apply _. Qed.

  Lemma frac_auth_validN n a : ✓{n} a → ✓{n} (●F a ⋅ ◯F a).
  Proof. by rewrite auth_both_validN. Qed.
  Lemma frac_auth_valid a : ✓ a → ✓ (●F a ⋅ ◯F a).
  Proof. intros. by apply auth_both_valid_2. Qed.

  Lemma frac_auth_agreeN n a b : ✓{n} (●F a ⋅ ◯F b) → a ≡{n}≡ b.
  Proof.
    rewrite auth_both_validN /= => -[Hincl Hvalid].
    by move: Hincl=> /Some_includedN_exclusive /(_ Hvalid ) [??].
  Qed.
  Lemma frac_auth_agree a b : ✓ (●F a ⋅ ◯F b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=> n. by apply frac_auth_agreeN, cmra_valid_validN.
  Qed.
  Lemma frac_auth_agree_L `{!LeibnizEquiv A} a b : ✓ (●F a ⋅ ◯F b) → a = b.
  Proof. intros. by apply leibniz_equiv, frac_auth_agree. Qed.

  Lemma frac_auth_includedN n q a b : ✓{n} (●F a ⋅ ◯F{q} b) → Some b ≼{n} Some a.
  Proof. by rewrite auth_both_validN /= => -[/Some_pair_includedN [_ ?] _]. Qed.
  Lemma frac_auth_included `{CmraDiscrete A} q a b :
    ✓ (●F a ⋅ ◯F{q} b) → Some b ≼ Some a.
  Proof. by rewrite auth_both_valid_discrete /= => -[/Some_pair_included [_ ?] _]. Qed.
  Lemma frac_auth_includedN_total `{CmraTotal A} n q a b :
    ✓{n} (●F a ⋅ ◯F{q} b) → b ≼{n} a.
  Proof. intros. by eapply Some_includedN_total, frac_auth_includedN. Qed.
  Lemma frac_auth_included_total `{CmraDiscrete A, CmraTotal A} q a b :
    ✓ (●F a ⋅ ◯F{q} b) → b ≼ a.
  Proof. intros. by eapply Some_included_total, frac_auth_included. Qed.

  Lemma frac_auth_auth_validN n a : ✓{n} (●F a) ↔ ✓{n} a.
  Proof.
    rewrite auth_auth_dfrac_validN Some_validN. split.
    - by intros [?[]].
    - intros. by split.
  Qed.
  Lemma frac_auth_auth_valid a : ✓ (●F a) ↔ ✓ a.
  Proof. rewrite !cmra_valid_validN. by setoid_rewrite frac_auth_auth_validN. Qed.

  Lemma frac_auth_frag_validN n q a : ✓{n} (◯F{q} a) ↔ (q ≤ 1)%Qp ∧ ✓{n} a.
  Proof. by rewrite /frac_auth_frag auth_frag_validN. Qed.
  Lemma frac_auth_frag_valid q a : ✓ (◯F{q} a) ↔ (q ≤ 1)%Qp ∧ ✓ a.
  Proof. by rewrite /frac_auth_frag auth_frag_valid. Qed.

  Lemma frac_auth_frag_op q1 q2 a1 a2 : ◯F{q1+q2} (a1 ⋅ a2) ≡ ◯F{q1} a1 ⋅ ◯F{q2} a2.
  Proof. done. Qed.

  Lemma frac_auth_frag_validN_op_1_l n q a b : ✓{n} (◯F{1} a ⋅ ◯F{q} b) → False.
  Proof. rewrite -frac_auth_frag_op frac_auth_frag_validN=> -[/Qp_not_add_le_l []]. Qed.
  Lemma frac_auth_frag_valid_op_1_l q a b : ✓ (◯F{1} a ⋅ ◯F{q} b) → False.
  Proof. rewrite -frac_auth_frag_op frac_auth_frag_valid=> -[/Qp_not_add_le_l []]. Qed.

  Global Instance frac_auth_is_op (q q1 q2 : frac) (a a1 a2 : A) :
    IsOp q q1 q2 → IsOp a a1 a2 → IsOp' (◯F{q} a) (◯F{q1} a1) (◯F{q2} a2).
  Proof. by rewrite /IsOp' /IsOp=> /leibniz_equiv_iff -> ->. Qed.

  Global Instance frac_auth_is_op_core_id (q q1 q2 : frac) (a  : A) :
    CoreId a → IsOp q q1 q2 → IsOp' (◯F{q} a) (◯F{q1} a) (◯F{q2} a).
  Proof.
    rewrite /IsOp' /IsOp=> ? /leibniz_equiv_iff ->.
    by rewrite -frac_auth_frag_op -core_id_dup.
  Qed.

  Lemma frac_auth_update q a b a' b' :
    (a,b) ~l~> (a',b') → ●F a ⋅ ◯F{q} b ~~> ●F a' ⋅ ◯F{q} b'.
  Proof.
    intros. by apply auth_update, option_local_update, prod_local_update_2.
  Qed.

  Lemma frac_auth_update_1 a b a' : ✓ a' → ●F a ⋅ ◯F b ~~> ●F a' ⋅ ◯F a'.
  Proof.
    intros. by apply auth_update, option_local_update, exclusive_local_update.
  Qed.
End frac_auth.
