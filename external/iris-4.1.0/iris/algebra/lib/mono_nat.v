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
[mono_nat_lb n ≼ mono_nat_auth dq n], holds. Without this trick, a
frame-preserving update lemma would be required instead. *)
Definition mono_nat_auth (dq : dfrac) (n : nat) : mono_nat :=
  ●{dq} MaxNat n ⋅ ◯ MaxNat n.
Definition mono_nat_lb (n : nat) : mono_nat := ◯ MaxNat n.

Notation "●MN dq a" := (mono_nat_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "●MN dq  a").
Notation "◯MN a" := (mono_nat_lb a) (at level 20).

Section mono_nat.
  Implicit Types (n : nat).

  Global Instance mono_nat_lb_core_id n : CoreId (◯MN n).
  Proof. apply _. Qed.
  Global Instance mono_nat_auth_core_id l : CoreId (●MN□ l).
  Proof. apply _. Qed.

  Lemma mono_nat_auth_dfrac_op dq1 dq2 n :
    ●MN{dq1 ⋅ dq2} n ≡ ●MN{dq1} n ⋅ ●MN{dq2} n.
  Proof.
    rewrite /mono_nat_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mono_nat_lb_op n1 n2 :
    ◯MN (n1 `max` n2) = ◯MN n1 ⋅ ◯MN n2.
  Proof. rewrite -auth_frag_op max_nat_op //. Qed.

  Lemma mono_nat_auth_lb_op dq n :
    ●MN{dq} n ≡ ●MN{dq} n ⋅ ◯MN n.
  Proof.
    rewrite /mono_nat_auth /mono_nat_lb.
    rewrite -!assoc -auth_frag_op max_nat_op.
    rewrite Nat.max_id //.
  Qed.

  Global Instance mono_nat_auth_dfrac_is_op dq dq1 dq2 n :
    IsOp dq dq1 dq2 → IsOp' (●MN{dq} n) (●MN{dq1} n) (●MN{dq2} n).
  Proof. rewrite /IsOp' /IsOp=> ->. rewrite mono_nat_auth_dfrac_op //. Qed.
  Global Instance mono_nat_lb_max_is_op n n1 n2 :
    IsOp (MaxNat n) (MaxNat n1) (MaxNat n2) → IsOp' (◯MN n) (◯MN n1) (◯MN n2).
  Proof. rewrite /IsOp' /IsOp /mono_nat_lb=> ->. done. Qed.

  (** rephrasing of [mono_nat_lb_op] useful for weakening a fragment to a
  smaller lower-bound *)
  Lemma mono_nat_lb_op_le_l n n' :
    n' ≤ n →
    ◯MN n = ◯MN n' ⋅ ◯MN n.
  Proof. intros. rewrite -mono_nat_lb_op Nat.max_r //. Qed.

  Lemma mono_nat_auth_dfrac_valid dq n : (✓ ●MN{dq} n) ↔ ✓ dq.
  Proof.
    rewrite /mono_nat_auth auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma mono_nat_auth_valid n : ✓ ●MN n.
  Proof. by apply auth_both_valid. Qed.

  Lemma mono_nat_auth_dfrac_op_valid dq1 dq2 n1 n2 :
    ✓ (●MN{dq1} n1 ⋅ ●MN{dq2} n2) ↔ ✓ (dq1 ⋅ dq2) ∧ n1 = n2.
  Proof.
    rewrite /mono_nat_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid. naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      by apply auth_both_dfrac_valid_discrete.
  Qed.
  Lemma mono_nat_auth_op_valid n1 n2 :
    ✓ (●MN n1 ⋅ ●MN n2) ↔ False.
  Proof. rewrite mono_nat_auth_dfrac_op_valid. naive_solver. Qed.

  Lemma mono_nat_both_dfrac_valid dq n m :
    ✓ (●MN{dq} n ⋅ ◯MN m) ↔ ✓ dq ∧ m ≤ n.
  Proof.
    rewrite /mono_nat_auth /mono_nat_lb -assoc -auth_frag_op.
    rewrite auth_both_dfrac_valid_discrete max_nat_included /=.
    naive_solver lia.
  Qed.
  Lemma mono_nat_both_valid n m :
    ✓ (●MN n ⋅ ◯MN m) ↔ m ≤ n.
  Proof. rewrite mono_nat_both_dfrac_valid dfrac_valid_own. naive_solver. Qed.

  Lemma mono_nat_lb_mono n1 n2 : n1 ≤ n2 → ◯MN n1 ≼ ◯MN n2.
  Proof. intros. by apply auth_frag_mono, max_nat_included. Qed.

  Lemma mono_nat_included dq n : ◯MN n ≼ ●MN{dq} n.
  Proof. apply cmra_included_r. Qed.

  Lemma mono_nat_update {n} n' :
    n ≤ n' → ●MN n ~~> ●MN n'.
  Proof.
    intros. rewrite /mono_nat_auth /mono_nat_lb.
    by apply auth_update, max_nat_local_update.
  Qed.

  Lemma mono_nat_auth_persist n dq :
    ●MN{dq} n ~~> ●MN□ n.
  Proof.
    intros. rewrite /mono_nat_auth /mono_nat_lb.
    eapply cmra_update_op_proper; last done.
    eapply auth_update_auth_persist.
  Qed.
End mono_nat.

Global Typeclasses Opaque mono_nat_auth mono_nat_lb.
