From iris.prelude Require Import options.
From stdpp Require Import numbers.
Require Import coq_tricks.Deex.

Inductive Parity :=
| Even : nat -> Parity
| Odd : nat -> Parity.

Fixpoint parity (n: nat) : Parity :=
  match n with
  | 0 => Even 0
  | S 0 => Odd 0
  | S (S i) => match parity i with
      | Even k => Even (k + 1)
      | Odd k => Odd (k + 1)
      end
  end.

Definition even_get (n: nat) : option nat :=
    match parity n with Even k => Some k | Odd _ => None end.
    
Definition odd_get (n: nat) : option nat :=
    match parity n with Odd k => Some k | Even _ => None end.
    
Lemma parity_2i (i: nat) : parity (2*i) = Even i.
Proof. induction i.
 - simpl. trivial.
 - replace (2 * S i) with (S (S (2 * i))) by lia.
   unfold parity in *. rewrite IHi. f_equal. lia.
Qed.

Lemma parity_2i_1 (i: nat) : parity (2*i + 1) = Odd i.
Proof. induction i.
 - simpl. trivial.
 - replace (2 * S i + 1) with (S (S (2 * i + 1))) by lia.
   unfold parity in *. rewrite IHi. f_equal. lia.
Qed.

Lemma even_or_odd (i: nat) : (∃ k , i = 2*k) \/ (∃ k , i = 2*k + 1).
Proof. induction i.
  - left. exists 0. lia.
  - destruct IHi.
    + right. deex. exists k. lia.
    + left. deex. exists (k+1). lia.
Qed.
