From iris.algebra Require Export dfrac agree updates local_updates.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

Definition dfrac_agreeR (A : ofe) : cmra := prodR dfracR (agreeR A).

Definition to_dfrac_agree {A : ofe} (d : dfrac) (a : A) : dfrac_agreeR A :=
  (d, to_agree a).
Global Instance: Params (@to_dfrac_agree) 2 := {}.
(** To make it easier to work with the [Qp] version of this, we also provide
    [to_frac_agree] and appropriate lemmas. *)
Definition to_frac_agree {A : ofe} (q : Qp) (a : A) : dfrac_agreeR A :=
  to_dfrac_agree (DfracOwn q) a.
Global Instance: Params (@to_frac_agree) 2 := {}.

Section lemmas.
  Context {A : ofe}.
  Implicit Types (q : Qp) (d : dfrac) (a : A).

  Global Instance to_dfrac_agree_ne d : NonExpansive (@to_dfrac_agree A d).
  Proof. solve_proper. Qed.
  Global Instance to_dfrac_agree_proper d : Proper ((≡) ==> (≡)) (@to_dfrac_agree A d).
  Proof. solve_proper. Qed.

  Global Instance to_dfrac_agree_exclusive a :
    Exclusive (to_dfrac_agree (DfracOwn 1) a).
  Proof. apply _. Qed.
  Global Instance to_dfrac_agree_discrete d a : Discrete a → Discrete (to_dfrac_agree d a).
  Proof. apply _. Qed.
  Global Instance to_dfrac_agree_injN n : Inj2 (dist n) (dist n) (dist n) (@to_dfrac_agree A).
  Proof. by intros d1 a1 d2 a2 [??%(inj to_agree)]. Qed.
  Global Instance to_dfrac_agree_inj : Inj2 (≡) (≡) (≡) (@to_dfrac_agree A).
  Proof. by intros d1 a1 d2 a2 [??%(inj to_agree)]. Qed.

  Lemma dfrac_agree_op d1 d2 a :
    to_dfrac_agree (d1 ⋅ d2) a ≡ to_dfrac_agree d1 a ⋅ to_dfrac_agree d2 a.
  Proof. rewrite /to_dfrac_agree -pair_op agree_idemp //. Qed.
  Lemma frac_agree_op q1 q2 a :
    to_frac_agree (q1 + q2) a ≡ to_frac_agree q1 a ⋅ to_frac_agree q2 a.
  Proof. rewrite -dfrac_agree_op. done. Qed.

  Lemma dfrac_agree_op_valid d1 a1 d2 a2 :
    ✓ (to_dfrac_agree d1 a1 ⋅ to_dfrac_agree d2 a2) ↔
    ✓ (d1 ⋅ d2) ∧ a1 ≡ a2.
  Proof.
    rewrite /to_dfrac_agree -pair_op pair_valid to_agree_op_valid. done.
  Qed.
  Lemma dfrac_agree_op_valid_L `{!LeibnizEquiv A} d1 a1 d2 a2 :
    ✓ (to_dfrac_agree d1 a1 ⋅ to_dfrac_agree d2 a2) ↔
    ✓ (d1 ⋅ d2) ∧ a1 = a2.
  Proof. unfold_leibniz. apply dfrac_agree_op_valid. Qed.
  Lemma dfrac_agree_op_validN d1 a1 d2 a2 n :
    ✓{n} (to_dfrac_agree d1 a1 ⋅ to_dfrac_agree d2 a2) ↔
    ✓ (d1 ⋅ d2) ∧ a1 ≡{n}≡ a2.
  Proof.
    rewrite /to_dfrac_agree -pair_op pair_validN to_agree_op_validN. done.
  Qed.

  Lemma frac_agree_op_valid q1 a1 q2 a2 :
    ✓ (to_frac_agree q1 a1 ⋅ to_frac_agree q2 a2) ↔
    (q1 + q2 ≤ 1)%Qp ∧ a1 ≡ a2.
  Proof. apply dfrac_agree_op_valid. Qed.
  Lemma frac_agree_op_valid_L `{!LeibnizEquiv A} q1 a1 q2 a2 :
    ✓ (to_frac_agree q1 a1 ⋅ to_frac_agree q2 a2) ↔
    (q1 + q2 ≤ 1)%Qp ∧ a1 = a2.
  Proof. apply dfrac_agree_op_valid_L. Qed.
  Lemma frac_agree_op_validN q1 a1 q2 a2 n :
    ✓{n} (to_frac_agree q1 a1 ⋅ to_frac_agree q2 a2) ↔
    (q1 + q2 ≤ 1)%Qp ∧ a1 ≡{n}≡ a2.
  Proof. apply dfrac_agree_op_validN. Qed.

  Lemma dfrac_agree_included d1 a1 d2 a2 :
    to_dfrac_agree d1 a1 ≼ to_dfrac_agree d2 a2 ↔
    (d1 ≼ d2) ∧ a1 ≡ a2.
  Proof. by rewrite pair_included to_agree_included. Qed.
  Lemma dfrac_agree_included_L `{!LeibnizEquiv A} d1 a1 d2 a2 :
    to_dfrac_agree d1 a1 ≼ to_dfrac_agree d2 a2 ↔
    (d1 ≼ d2) ∧ a1 = a2.
  Proof. unfold_leibniz. apply dfrac_agree_included. Qed.
  Lemma dfrac_agree_includedN d1 a1 d2 a2 n :
    to_dfrac_agree d1 a1 ≼{n} to_dfrac_agree d2 a2 ↔
    (d1 ≼ d2) ∧ a1 ≡{n}≡ a2.
  Proof.
    by rewrite pair_includedN -cmra_discrete_included_iff
               to_agree_includedN.
  Qed.

  Lemma frac_agree_included q1 a1 q2 a2 :
    to_frac_agree q1 a1 ≼ to_frac_agree q2 a2 ↔
    (q1 < q2)%Qp ∧ a1 ≡ a2.
  Proof. by rewrite dfrac_agree_included dfrac_own_included. Qed.
  Lemma frac_agree_included_L `{!LeibnizEquiv A} q1 a1 q2 a2 :
    to_frac_agree q1 a1 ≼ to_frac_agree q2 a2 ↔
    (q1 < q2)%Qp ∧ a1 = a2.
  Proof. by rewrite dfrac_agree_included_L dfrac_own_included. Qed.
  Lemma frac_agree_includedN q1 a1 q2 a2 n :
    to_frac_agree q1 a1 ≼{n} to_frac_agree q2 a2 ↔
    (q1 < q2)%Qp ∧ a1 ≡{n}≡ a2.
  Proof. by rewrite dfrac_agree_includedN dfrac_own_included. Qed.

  (** While [cmra_update_exclusive] takes care of most updates, it is not sufficient
      for this one since there is no abstraction-preserving way to rewrite
      [to_dfrac_agree d1 v1 ⋅ to_dfrac_agree d2 v2] into something simpler. *)
  Lemma dfrac_agree_update_2 d1 d2 a1 a2 a' :
    d1 ⋅ d2 = DfracOwn 1 →
    to_dfrac_agree d1 a1 ⋅ to_dfrac_agree d2 a2 ~~>
    to_dfrac_agree d1 a' ⋅ to_dfrac_agree d2 a'.
  Proof.
    intros Hq. rewrite -pair_op Hq.
    apply cmra_update_exclusive.
    rewrite dfrac_agree_op_valid Hq //.
  Qed.
  Lemma frac_agree_update_2 q1 q2 a1 a2 a' :
    (q1 + q2 = 1)%Qp →
    to_frac_agree q1 a1 ⋅ to_frac_agree q2 a2 ~~>
    to_frac_agree q1 a' ⋅ to_frac_agree q2 a'.
  Proof. intros Hq. apply dfrac_agree_update_2. rewrite dfrac_op_own Hq //. Qed.

  Lemma dfrac_agree_persist d a :
    to_dfrac_agree d a ~~> to_dfrac_agree DfracDiscarded a.
  Proof.
    rewrite /to_dfrac_agree. apply prod_update; last done.
    simpl. apply dfrac_discard_update.
  Qed.

End lemmas.

Definition dfrac_agreeRF (F : oFunctor) : rFunctor :=
  prodRF (constRF dfracR) (agreeRF F).

Global Instance dfrac_agreeRF_contractive F :
  oFunctorContractive F → rFunctorContractive (dfrac_agreeRF F).
Proof. apply _. Qed.

Global Typeclasses Opaque to_dfrac_agree.
(* [to_frac_agree] is deliberately transparent to reuse the [to_dfrac_agree] instances *)
