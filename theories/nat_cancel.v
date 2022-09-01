From stdpp Require Import numbers.
From stdpp Require Import options.

(** The class [NatCancel m n m' n'] is a simple canceler for natural numbers
implemented using type classes.

Input: [m], [n]; output: [m'], [n'].

It turns an equality [n = m] into an equality [n' = m'] by canceling out terms
that appear on both sides of the equality. We provide instances to handle the
following connectives over natural numbers:

  n := 0 | t | n + m | S m

Here, [t] represents arbitrary terms that do not fit the grammar. The instances
the class perform a depth-first traversal (from left to right) through [n] and
try to cancel each leaf in [m]. This implies that the shape of the original
expressions [n] and [m] are preserved as much as possible. For example,
canceling:

  S (S m2) + (k1 + (S k2 + k3)) + n1 = 2 + S ((n1 + S n2) + S (S m1 + m2))

Results in:

  k1 + (k2 + k3) = S (n2 + S (S m1))

The instances are setup up so that canceling is performed in two stages.

- In the first stage, using the class [NatCancelL], it traverses [m] w.r.t. [S]
  and [+].
- In the second stage, for each leaf (i.e. a constant or arbitrary term)
  obtained by the traversal in stage 1, it uses the class [NatCancelR] to
  cancel the leaf in [n].

Be warned: Since the canceler is implemented using type classes it should only
be used it either of the inputs is relatively small. For bigger inputs, an
approach based on reflection would be better, but for small inputs, the overhead
of reification will probably not be worth it. *)

Class NatCancel (m n m' n' : nat) := nat_cancel : m' + n = m + n'.
Global Hint Mode NatCancel ! ! - - : typeclass_instances.

Module nat_cancel.
  Class NatCancelL (m n m' n' : nat) := nat_cancel_l : m' + n = m + n'.
  Global Hint Mode NatCancelL ! ! - - : typeclass_instances.
  Class NatCancelR (m n m' n' : nat) := nat_cancel_r : NatCancelL m n m' n'.
  Global Hint Mode NatCancelR ! ! - - : typeclass_instances.
  Global Existing Instance nat_cancel_r | 100.

  (** The implementation of the canceler is highly non-deterministic, but since
  it will always succeed, no backtracking will ever be performed. In order to
  avoid issues like:

    https://gitlab.mpi-sws.org/FP/iris-coq/issues/153

  we wrap the entire canceler in the [NoBackTrack] class. *)
  Global Instance nat_cancel_start m n m' n' :
    TCNoBackTrack (NatCancelL m n m' n') → NatCancel m n m' n'.
  Proof. by intros [?]. Qed.

  Class MakeNatS (n1 n2 m : nat) := make_nat_S : m = n1 + n2.
  Global Instance make_nat_S_0_l n : MakeNatS 0 n n.
  Proof. done. Qed.
  Global Instance make_nat_S_1 n : MakeNatS 1 n (S n).
  Proof. done. Qed.

  Class MakeNatPlus (n1 n2 m : nat) := make_nat_plus : m = n1 + n2.
  Global Instance make_nat_plus_0_l n : MakeNatPlus 0 n n.
  Proof. done. Qed.
  Global Instance make_nat_plus_0_r n : MakeNatPlus n 0 n.
  Proof. unfold MakeNatPlus. by rewrite Nat.add_0_r. Qed.
  Global Instance make_nat_plus_default n1 n2 : MakeNatPlus n1 n2 (n1 + n2) | 100.
  Proof. done. Qed.

  Global Instance nat_cancel_leaf_here m : NatCancelR m m 0 0 | 0.
  Proof. by unfold NatCancelR, NatCancelL. Qed.
  Global Instance nat_cancel_leaf_else m n : NatCancelR m n m n | 100.
  Proof. by unfold NatCancelR. Qed.
  Global Instance nat_cancel_leaf_plus m m' m'' n1 n2 n1' n2' n1'n2' :
    NatCancelR m n1 m' n1' → NatCancelR m' n2 m'' n2' →
    MakeNatPlus n1' n2' n1'n2' → NatCancelR m (n1 + n2) m'' n1'n2' | 2.
  Proof. unfold NatCancelR, NatCancelL, MakeNatPlus. lia. Qed.
  Global Instance nat_cancel_leaf_S_here m n m' n' :
    NatCancelR m n m' n' → NatCancelR (S m) (S n) m' n' | 3.
  Proof. unfold NatCancelR, NatCancelL. lia. Qed.
  Global Instance nat_cancel_leaf_S_else m n m' n' :
    NatCancelR m n m' n' → NatCancelR m (S n) m' (S n') | 4.
  Proof. unfold NatCancelR, NatCancelL. lia. Qed.

  (** The instance [nat_cancel_S_both] is redundant, but may reduce proof search
  quite a bit, e.g. when canceling constants in constants. *)
  Global Instance nat_cancel_S_both m n m' n' :
    NatCancelL m n m' n' → NatCancelL (S m) (S n) m' n' | 1.
  Proof. unfold NatCancelL. lia. Qed.
  Global Instance nat_cancel_plus m1 m2 m1' m2' m1'm2' n n' n'' :
    NatCancelL m1 n m1' n' → NatCancelL m2 n' m2' n'' →
    MakeNatPlus m1' m2' m1'm2' → NatCancelL (m1 + m2) n m1'm2' n'' | 2.
  Proof. unfold NatCancelL, MakeNatPlus. lia. Qed.
  Global Instance nat_cancel_S m m' m'' Sm' n n' n'' :
    NatCancelL m n m' n' → NatCancelR 1 n' m'' n'' →
    MakeNatS m'' m' Sm' → NatCancelL (S m) n Sm' n'' | 3.
  Proof. unfold NatCancelR, NatCancelL, MakeNatS. lia. Qed.
End nat_cancel.
