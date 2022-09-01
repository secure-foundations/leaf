From iris.algebra Require Export frac agree updates local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

Definition frac_agreeR (A : ofe) : cmra := prodR fracR (agreeR A).

Definition to_frac_agree {A : ofe} (q : frac) (a : A) : frac_agreeR A :=
  (q, to_agree a).

Section lemmas.
  Context {A : ofe}.
  Implicit Types (q : frac) (a : A).

  Global Instance to_frac_agree_ne q : NonExpansive (@to_frac_agree A q).
  Proof. solve_proper. Qed.
  Global Instance to_frac_agree_proper q : Proper ((≡) ==> (≡)) (@to_frac_agree A q).
  Proof. solve_proper. Qed.

  Global Instance to_frac_agree_exclusive a : Exclusive (to_frac_agree 1 a).
  Proof. apply _. Qed.
  Global Instance to_frac_discrete a : Discrete a → Discrete (to_frac_agree 1 a).
  Proof. apply _. Qed.
  Global Instance to_frac_injN n : Inj2 (dist n) (dist n) (dist n) (@to_frac_agree A).
  Proof. by intros q1 a1 q2 a2 [??%(inj to_agree)]. Qed.
  Global Instance to_frac_inj : Inj2 (≡) (≡) (≡) (@to_frac_agree A).
  Proof. by intros q1 a1 q2 a2 [??%(inj to_agree)]. Qed.

  Lemma frac_agree_op q1 q2 a :
    to_frac_agree (q1 + q2) a ≡ to_frac_agree q1 a ⋅ to_frac_agree q2 a.
  Proof. rewrite /to_frac_agree -pair_op agree_idemp //. Qed.

  Lemma frac_agree_op_valid q1 a1 q2 a2 :
    ✓ (to_frac_agree q1 a1 ⋅ to_frac_agree q2 a2) →
    (q1 + q2 ≤ 1)%Qp ∧ a1 ≡ a2.
  Proof.
    intros [Hq Ha]%pair_valid. simpl in *. split; first done.
    apply to_agree_op_inv. done.
  Qed.
  Lemma frac_agree_op_valid_L `{!LeibnizEquiv A} q1 a1 q2 a2 :
    ✓ (to_frac_agree q1 a1 ⋅ to_frac_agree q2 a2) →
    (q1 + q2 ≤ 1)%Qp ∧ a1 = a2.
  Proof. unfold_leibniz. apply frac_agree_op_valid. Qed.
  Lemma frac_agree_op_validN q1 a1 q2 a2 n :
    ✓{n} (to_frac_agree q1 a1 ⋅ to_frac_agree q2 a2) →
    (q1 + q2 ≤ 1)%Qp ∧ a1 ≡{n}≡ a2.
  Proof.
    intros [Hq Ha]%pair_validN. simpl in *. split; first done.
    apply to_agree_op_invN. done.
  Qed.

  Lemma frac_agree_included q1 a1 q2 a2 :
    to_frac_agree q1 a1 ≼ to_frac_agree q2 a2 ↔
    (q1 < q2)%Qp ∧ a1 ≡ a2.
  Proof. by rewrite pair_included frac_included to_agree_included. Qed.
  Lemma frac_agree_included_L `{!LeibnizEquiv A} q1 a1 q2 a2 :
    to_frac_agree q1 a1 ≼ to_frac_agree q2 a2 ↔
    (q1 < q2)%Qp ∧ a1 = a2.
  Proof. unfold_leibniz. apply frac_agree_included. Qed.
  Lemma frac_agree_includedN q1 a1 q2 a2 n :
    to_frac_agree q1 a1 ≼{n} to_frac_agree q2 a2 ↔
    (q1 < q2)%Qp ∧ a1 ≡{n}≡ a2.
  Proof.
    by rewrite pair_includedN -cmra_discrete_included_iff
               frac_included to_agree_includedN.
  Qed.

  (** No frame-preserving update lemma needed -- use [cmra_update_exclusive] with
  the above [Exclusive] instance. *)

End lemmas.

Typeclasses Opaque to_frac_agree.
