(** This file provides the unbounded fractional authoritative camera: a version
of the fractional authoritative camera that can be used with fractions [> 1].

Most of the reasoning principles for this version of the fractional
authoritative cameras are the same as for the original version. There are two
difference:

- We get the additional rule that can be used to allocate a "surplus", i.e.
  if we have the authoritative element we can always increase its fraction
  and allocate a new fragment.

  <<<
  ✓ (a ⋅ b) → ●U{p} a ~~> ●U{p + q} (a ⋅ b) ⋅ ◯U{q} b
  >>>

- We no longer have the [◯U{1} a] is the exclusive fragmental element (cf.
  [frac_auth_frag_validN_op_1_l]).
*)
From iris.algebra Require Export auth frac updates local_updates.
From iris.algebra Require Import ufrac proofmode_classes.
From iris.prelude Require Import options.

Definition ufrac_authR (A : cmra) : cmra :=
  authR (optionUR (prodR ufracR A)).
Definition ufrac_authUR (A : cmra) : ucmra :=
  authUR (optionUR (prodR ufracR A)).

(** Note in the signature of [ufrac_auth_auth] and [ufrac_auth_frag] we use
[q : Qp] instead of [q : ufrac]. This way, the API does not expose that [ufrac]
is used internally. This is quite important, as there are two canonical camera
instances with carrier [Qp], namely [fracR] and [ufracR]. When writing things
like [ufrac_auth_auth q a ∧ ✓ q] we want Coq to infer the type of [q] as [Qp]
such that the [✓] of the default [fracR] camera is used, and not the [✓] of
the [ufracR] camera. *)
Definition ufrac_auth_auth {A : cmra} (q : Qp) (x : A) : ufrac_authR A :=
  ● (Some (q : ufracR,x)).
Definition ufrac_auth_frag {A : cmra} (q : Qp) (x : A) : ufrac_authR A :=
  ◯ (Some (q : ufracR,x)).

Typeclasses Opaque ufrac_auth_auth ufrac_auth_frag.

Global Instance: Params (@ufrac_auth_auth) 2 := {}.
Global Instance: Params (@ufrac_auth_frag) 2 := {}.

Notation "●U{ q } a" := (ufrac_auth_auth q a) (at level 10, format "●U{ q }  a").
Notation "◯U{ q } a" := (ufrac_auth_frag q a) (at level 10, format "◯U{ q }  a").

Section ufrac_auth.
  Context {A : cmra}.
  Implicit Types a b : A.

  Global Instance ufrac_auth_auth_ne q : NonExpansive (@ufrac_auth_auth A q).
  Proof. solve_proper. Qed.
  Global Instance ufrac_auth_auth_proper q : Proper ((≡) ==> (≡)) (@ufrac_auth_auth A q).
  Proof. solve_proper. Qed.
  Global Instance ufrac_auth_frag_ne q : NonExpansive (@ufrac_auth_frag A q).
  Proof. solve_proper. Qed.
  Global Instance ufrac_auth_frag_proper q : Proper ((≡) ==> (≡)) (@ufrac_auth_frag A q).
  Proof. solve_proper. Qed.

  Global Instance ufrac_auth_auth_discrete q a : Discrete a → Discrete (●U{q} a).
  Proof. intros. apply auth_auth_discrete; [apply Some_discrete|]; apply _. Qed.
  Global Instance ufrac_auth_frag_discrete q a : Discrete a → Discrete (◯U{q} a).
  Proof. intros. apply auth_frag_discrete; apply Some_discrete; apply _. Qed.

  Lemma ufrac_auth_validN n a p : ✓{n} a → ✓{n} (●U{p} a ⋅ ◯U{p} a).
  Proof. by rewrite auth_both_validN. Qed.
  Lemma ufrac_auth_valid p a : ✓ a → ✓ (●U{p} a ⋅ ◯U{p} a).
  Proof. intros. by apply auth_both_valid_2. Qed.

  Lemma ufrac_auth_agreeN n p a b : ✓{n} (●U{p} a ⋅ ◯U{p} b) → a ≡{n}≡ b.
  Proof.
    rewrite auth_both_validN=> -[/Some_includedN [[_ ? //]|Hincl] _].
    move: Hincl=> /pair_includedN=> -[/ufrac_included Hincl _].
    by destruct (irreflexivity (<)%Qp p).
  Qed.
  Lemma ufrac_auth_agree p a b : ✓ (●U{p} a ⋅ ◯U{p} b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=> n. by eapply ufrac_auth_agreeN, cmra_valid_validN.
  Qed.
  Lemma ufrac_auth_agree_L `{!LeibnizEquiv A} p a b : ✓ (●U{p} a ⋅ ◯U{p} b) → a = b.
  Proof. intros. by eapply leibniz_equiv, ufrac_auth_agree. Qed.

  Lemma ufrac_auth_includedN n p q a b : ✓{n} (●U{p} a ⋅ ◯U{q} b) → Some b ≼{n} Some a.
  Proof. by rewrite auth_both_validN=> -[/Some_pair_includedN [_ ?] _]. Qed.
  Lemma ufrac_auth_included `{CmraDiscrete A} q p a b :
    ✓ (●U{p} a ⋅ ◯U{q} b) → Some b ≼ Some a.
  Proof. rewrite auth_both_valid_discrete=> -[/Some_pair_included [_ ?] _] //. Qed.
  Lemma ufrac_auth_includedN_total `{CmraTotal A} n q p a b :
    ✓{n} (●U{p} a ⋅ ◯U{q} b) → b ≼{n} a.
  Proof. intros. by eapply Some_includedN_total, ufrac_auth_includedN. Qed.
  Lemma ufrac_auth_included_total `{CmraDiscrete A, CmraTotal A} q p a b :
    ✓ (●U{p} a ⋅ ◯U{q} b) → b ≼ a.
  Proof. intros. by eapply Some_included_total, ufrac_auth_included. Qed.

  Lemma ufrac_auth_auth_validN n q a : ✓{n} (●U{q} a) ↔ ✓{n} a.
  Proof.
    rewrite auth_auth_dfrac_validN Some_validN. split.
    - by intros [?[]].
    - intros. by split.
  Qed.
  Lemma ufrac_auth_auth_valid q a : ✓ (●U{q} a) ↔ ✓ a.
  Proof. rewrite !cmra_valid_validN. by setoid_rewrite ufrac_auth_auth_validN. Qed.

  Lemma ufrac_auth_frag_validN n q a : ✓{n} (◯U{q} a) ↔ ✓{n} a.
  Proof.
    rewrite auth_frag_validN. split.
    - by intros [??].
    - by split.
  Qed.
  Lemma ufrac_auth_frag_valid q a : ✓ (◯U{q} a) ↔ ✓ a.
  Proof.
    rewrite auth_frag_valid. split.
    - by intros [??].
    - by split.
  Qed.

  Lemma ufrac_auth_frag_op q1 q2 a1 a2 : ◯U{q1+q2} (a1 ⋅ a2) ≡ ◯U{q1} a1 ⋅ ◯U{q2} a2.
  Proof. done. Qed.

  Global Instance ufrac_auth_is_op q q1 q2 a a1 a2 :
    IsOp q q1 q2 → IsOp a a1 a2 → IsOp' (◯U{q} a) (◯U{q1} a1) (◯U{q2} a2).
  Proof. by rewrite /IsOp' /IsOp=> /leibniz_equiv_iff -> ->. Qed.

  Global Instance ufrac_auth_is_op_core_id q q1 q2 a :
    CoreId a → IsOp q q1 q2 → IsOp' (◯U{q} a) (◯U{q1} a) (◯U{q2} a).
  Proof.
    rewrite /IsOp' /IsOp=> ? /leibniz_equiv_iff ->.
    by rewrite -ufrac_auth_frag_op -core_id_dup.
  Qed.

  Lemma ufrac_auth_update p q a b a' b' :
    (a,b) ~l~> (a',b') → ●U{p} a ⋅ ◯U{q} b ~~> ●U{p} a' ⋅ ◯U{q} b'.
  Proof.
    intros. apply: auth_update.
    apply: option_local_update. by apply: prod_local_update_2.
  Qed.

  Lemma ufrac_auth_update_surplus p q a b :
   ✓ (a ⋅ b) → ●U{p} a ~~> ●U{p + q} (a ⋅ b) ⋅ ◯U{q} b.
  Proof.
    intros Hconsistent. apply: auth_update_alloc.
    intros n m; simpl; intros [Hvalid1 Hvalid2] Heq.
    split.
    - split; by apply cmra_valid_validN.
    - rewrite pair_op Some_op Heq comm.
      destruct m; simpl; [rewrite left_id | rewrite right_id]; done.
  Qed.
End ufrac_auth.
