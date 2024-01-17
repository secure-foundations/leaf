From iris.algebra Require Export auth.
From iris.algebra Require Import numbers updates.
From iris.prelude Require Import options.

(** Authoritative CMRA over [max_Z]. The authoritative element is a
monotonically increasing [Z], while a fragment is a lower bound. *)

Definition mono_Z   := auth (option max_ZR).
Definition mono_ZR  := authR (optionUR max_ZR).
Definition mono_ZUR := authUR (optionUR max_ZR).

(** [mono_Z_auth] is the authoritative element. The definition includes the
fragment at the same value so that lemma [mono_Z_included], which states that
[mono_Z_lb n ≼ mono_Z_auth dq n], holds. Without this trick, a frame-preserving
update lemma would be required instead. *)
Definition mono_Z_auth (dq : dfrac) (n : Z) : mono_Z :=
  ●{dq} (Some (MaxZ n)) ⋅ ◯ (Some (MaxZ n)).
Definition mono_Z_lb (n : Z) : mono_Z := ◯ (Some (MaxZ n)).

Notation "●MZ dq a" := (mono_Z_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "●MZ dq  a").
Notation "◯MZ a" := (mono_Z_lb a) (at level 20).

Section mono_Z.
  Implicit Types (n : Z).

  Local Open Scope Z_scope.

  Global Instance mono_Z_lb_core_id n : CoreId (◯MZ n).
  Proof. apply _. Qed.
  Global Instance mono_Z_auth_core_id l : CoreId (●MZ□ l).
  Proof. apply _. Qed.

  Lemma mono_Z_auth_dfrac_op dq1 dq2 n :
    ●MZ{dq1 ⋅ dq2} n ≡ ●MZ{dq1} n ⋅ ●MZ{dq2} n.
  Proof.
    rewrite /mono_Z_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mono_Z_lb_op n1 n2 :
    ◯MZ (n1 `max` n2) = ◯MZ n1 ⋅ ◯MZ n2.
  Proof. rewrite -auth_frag_op -Some_op max_Z_op //. Qed.

  Lemma mono_Z_auth_lb_op dq n :
    ●MZ{dq} n ≡ ●MZ{dq} n ⋅ ◯MZ n.
  Proof.
    rewrite /mono_Z_auth /mono_Z_lb.
    rewrite -!assoc -auth_frag_op -Some_op max_Z_op.
    rewrite Z.max_id //.
  Qed.

  Global Instance mono_Z_auth_dfrac_is_op dq dq1 dq2 n :
    IsOp dq dq1 dq2 → IsOp' (●MZ{dq} n) (●MZ{dq1} n) (●MZ{dq2} n).
  Proof. rewrite /IsOp' /IsOp=> ->. rewrite mono_Z_auth_dfrac_op //. Qed.
  Global Instance mono_Z_lb_max_is_op n n1 n2 :
    IsOp (MaxZ n) (MaxZ n1) (MaxZ n2) → IsOp' (◯MZ n) (◯MZ n1) (◯MZ n2).
  Proof. rewrite /IsOp' /IsOp /mono_Z_lb=> ->. done. Qed.

  (** rephrasing of [mono_Z_lb_op] useful for weakening a fragment to a
  smaller lower-bound *)
  Lemma mono_Z_lb_op_le_l n n' :
    n' ≤ n →
    ◯MZ n = ◯MZ n' ⋅ ◯MZ n.
  Proof. intros. rewrite -mono_Z_lb_op Z.max_r //. Qed.

  Lemma mono_Z_auth_dfrac_valid dq n : (✓ ●MZ{dq} n) ↔ ✓ dq.
  Proof.
    rewrite /mono_Z_auth auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma mono_Z_auth_valid n : ✓ ●MZ n.
  Proof. by apply auth_both_valid. Qed.

  Lemma mono_Z_auth_dfrac_op_valid dq1 dq2 n1 n2 :
    ✓ (●MZ{dq1} n1 ⋅ ●MZ{dq2} n2) ↔ ✓ (dq1 ⋅ dq2) ∧ n1 = n2.
  Proof.
    rewrite /mono_Z_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid. naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      by apply auth_both_dfrac_valid_discrete.
  Qed.
  Lemma mono_Z_auth_op_valid n1 n2 :
    ✓ (●MZ n1 ⋅ ●MZ n2) ↔ False.
  Proof. rewrite mono_Z_auth_dfrac_op_valid. naive_solver. Qed.

  Lemma mono_Z_both_dfrac_valid dq n m :
    ✓ (●MZ{dq} n ⋅ ◯MZ m) ↔ ✓ dq ∧ m ≤ n.
  Proof.
    rewrite /mono_Z_auth /mono_Z_lb -assoc -auth_frag_op.
    rewrite auth_both_dfrac_valid_discrete Some_included_total max_Z_included /=.
    naive_solver lia.
  Qed.
  Lemma mono_Z_both_valid n m :
    ✓ (●MZ n ⋅ ◯MZ m) ↔ m ≤ n.
  Proof. rewrite mono_Z_both_dfrac_valid dfrac_valid_own. naive_solver. Qed.

  Lemma mono_Z_lb_mono n1 n2 : n1 ≤ n2 → ◯MZ n1 ≼ ◯MZ n2.
  Proof.
    intros. by apply auth_frag_mono, Some_included_total, max_Z_included.
  Qed.

  Lemma mono_Z_included dq n : ◯MZ n ≼ ●MZ{dq} n.
  Proof. apply: cmra_included_r. Qed.

  Lemma mono_Z_update {n} n' :
    n ≤ n' → ●MZ n ~~> ●MZ n'.
  Proof.
    intros. rewrite /mono_Z_auth /mono_Z_lb.
    by apply auth_update, option_local_update, max_Z_local_update.
  Qed.

  Lemma mono_Z_auth_persist n dq :
    ●MZ{dq} n ~~> ●MZ□ n.
  Proof.
    intros. rewrite /mono_Z_auth /mono_Z_lb.
    eapply cmra_update_op_proper; last done.
    eapply auth_update_auth_persist.
  Qed.
End mono_Z.

Global Typeclasses Opaque mono_Z_auth mono_Z_lb.
