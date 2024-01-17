From stdpp Require Import pretty.
From Coq Require Import Ascii.

Section N.
  Local Open Scope N_scope.

  Lemma pretty_N_0 : pretty 0 = "0".
  Proof. reflexivity. Qed.
  Lemma pretty_N_1 : pretty 1 = "1".
  Proof. reflexivity. Qed.
  Lemma pretty_N_9 : pretty 9 = "9".
  Proof. reflexivity. Qed.
  Lemma pretty_N_10 : pretty 10 = "10".
  Proof. reflexivity. Qed.
  Lemma pretty_N_100 : pretty 100 = "100".
  Proof. reflexivity. Qed.
  Lemma pretty_N_123456789 : pretty 123456789 = "123456789".
  Proof. reflexivity. Qed.
End N.

(** Minimized version of:

  https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Stack.20overflow.20in.20Qed.2E

Fixed by making the [wp_guard] in [pretty_N_go] proportional to the
size of the input so that it blocks in case the input is an open term. *)
Lemma test_no_stack_overflow p n :
  get n (pretty (N.pos p)) ≠ Some "_"%char →
  get (S n) ("-" +:+ pretty (N.pos p)) ≠ Some "_"%char.
Proof. intros Hlem. apply Hlem. Qed.

Section nat.
  Local Open Scope nat_scope.

  Lemma pretty_nat_0 : pretty 0 = "0".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_1 : pretty 1 = "1".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_9 : pretty 9 = "9".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_10 : pretty 10 = "10".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_100 : pretty 100 = "100".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_1234 : pretty 1234 = "1234".
  Proof. reflexivity. Qed.
End nat.

Section Z.
  Local Open Scope Z_scope.

  Lemma pretty_Z_0 : pretty 0 = "0".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_1 : pretty 1 = "1".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_9 : pretty 9 = "9".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_10 : pretty 10 = "10".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_100 : pretty 100 = "100".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_123456789 : pretty 123456789 = "123456789".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_1 : pretty (-1) = "-1".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_9 : pretty (-9) = "-9".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_10 : pretty (-10) = "-10".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_100 : pretty (-100) = "-100".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_123456789 : pretty (-123456789) = "-123456789".
  Proof. reflexivity. Qed.
End Z.