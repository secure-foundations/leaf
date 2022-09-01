From iris.algebra Require Export auth.
From iris.algebra Require Import numbers updates.
From iris.prelude Require Import options.

(** Authoritative CMRA over [max_nat]. The authoritative element is a
monotonically increasing [nat], while a fragment is a lower bound. *)

Definition mono_nat   := auth max_natUR.
Definition mono_natR  := authR max_natUR.
Definition mono_natUR := authUR max_natUR.

(** [mono_nat_auth] is the authoritative element. The definition includes the
fragment at the same value so that lemma [mono_nat_included], which states that
[mono_nat_lb n ≼ mono_nat_auth q n], does not require a frame-preserving
update. *)
Definition mono_nat_auth (q : Qp) (n : nat) : mono_nat :=
  ●{#q} MaxNat n ⋅ ◯ MaxNat n.
Definition mono_nat_lb (n : nat) : mono_nat := ◯ MaxNat n.

Section mono_nat.
  Implicit Types (n : nat).

  Global Instance mono_nat_lb_core_id n : CoreId (mono_nat_lb n).
  Proof. apply _. Qed.

  Lemma mono_nat_auth_frac_op q1 q2 n :
    mono_nat_auth q1 n ⋅ mono_nat_auth q2 n ≡ mono_nat_auth (q1 + q2) n.
  Proof.
    rewrite /mono_nat_auth -dfrac_op_own auth_auth_dfrac_op.
    rewrite (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mono_nat_lb_op n1 n2 :
    mono_nat_lb n1 ⋅ mono_nat_lb n2 = mono_nat_lb (n1 `max` n2).
  Proof. rewrite -auth_frag_op max_nat_op //. Qed.

  Lemma mono_nat_auth_lb_op q n :
    mono_nat_auth q n ≡ mono_nat_auth q n ⋅ mono_nat_lb n.
  Proof.
    rewrite /mono_nat_auth /mono_nat_lb.
    rewrite -!assoc -auth_frag_op max_nat_op.
    rewrite Nat.max_id //.
  Qed.

  (** rephrasing of [mono_nat_lb_op] useful for weakening a fragment to a
  smaller lower-bound *)
  Lemma mono_nat_lb_op_le_l n n' :
    n' ≤ n →
    mono_nat_lb n = mono_nat_lb n' ⋅ mono_nat_lb n.
  Proof. intros. rewrite mono_nat_lb_op Nat.max_r //. Qed.

  Lemma mono_nat_auth_frac_valid q n : ✓ mono_nat_auth q n ↔ (q ≤ 1)%Qp.
  Proof.
    rewrite /mono_nat_auth auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma mono_nat_auth_valid n : ✓ mono_nat_auth 1 n.
  Proof. by apply auth_both_valid. Qed.

  Lemma mono_nat_auth_frac_op_valid q1 q2 n1 n2 :
    ✓ (mono_nat_auth q1 n1 ⋅ mono_nat_auth q2 n2) ↔ (q1 + q2 ≤ 1)%Qp ∧ n1 = n2.
  Proof.
    rewrite /mono_nat_auth (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid. naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      by apply auth_both_dfrac_valid_discrete.
  Qed.
  Lemma mono_nat_auth_op_valid n1 n2 :
    ✓ (mono_nat_auth 1 n1 ⋅ mono_nat_auth 1 n2) ↔ False.
  Proof. rewrite mono_nat_auth_frac_op_valid. naive_solver. Qed.

  Lemma mono_nat_both_frac_valid q n m :
    ✓ (mono_nat_auth q n ⋅ mono_nat_lb m) ↔ (q ≤ 1)%Qp ∧ m ≤ n.
  Proof.
    rewrite /mono_nat_auth /mono_nat_lb -assoc -auth_frag_op.
    rewrite auth_both_dfrac_valid_discrete max_nat_included /=.
    naive_solver lia.
  Qed.
  Lemma mono_nat_both_valid n m :
    ✓ (mono_nat_auth 1 n ⋅ mono_nat_lb m) ↔ m ≤ n.
  Proof. rewrite mono_nat_both_frac_valid. naive_solver. Qed.

  Lemma mono_nat_lb_mono n1 n2 : n1 ≤ n2 → mono_nat_lb n1 ≼ mono_nat_lb n2.
  Proof. intros. by apply auth_frag_mono, max_nat_included. Qed.

  Lemma mono_nat_included q n : mono_nat_lb n ≼ mono_nat_auth q n.
  Proof. apply cmra_included_r. Qed.

  Lemma mono_nat_update {n} n' :
    n ≤ n' →
    mono_nat_auth 1 n ~~> mono_nat_auth 1 n'.
  Proof.
    intros. rewrite /mono_nat_auth /mono_nat_lb.
    by apply auth_update, max_nat_local_update.
  Qed.
End mono_nat.

Typeclasses Opaque mono_nat_auth mono_nat_lb.
