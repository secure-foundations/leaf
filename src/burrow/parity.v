From iris.prelude Require Import options.
From stdpp Require Import numbers.
Require Import coq_tricks.Deex.

Inductive Parity :=
| Even : nat -> Parity
| Odd : nat -> Parity.

Fixpoint parity (n: nat) : Parity :=
  match n with
  | 0 => Even 0
  | S i => match parity i with
      | Even k => Odd k
      | Odd k => Even (k + 1)
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

Lemma eq_0_of_parity0 (y: nat)
  : parity y = parity 0 -> y = 0.
Proof.
  intros. destruct y; trivial. exfalso. unfold parity in H. destruct y.
  - discriminate. - fold parity in H. destruct (parity y). * inversion H. lia.
    * discriminate.
Qed.
  
Lemma eq_of_parity_eq (x : nat)
  : ∀ y , parity x = parity y -> x = y.
Proof. induction x; destruct y.
  - trivial.
  - symmetry. apply eq_0_of_parity0. symmetry. trivial.
  - apply eq_0_of_parity0.
  - intro. f_equal. apply IHx. 
      unfold parity in H. fold parity in H.
      destruct (parity x), (parity y).
      * inversion H. subst. trivial.
      * discriminate.
      * discriminate.
      * inversion H. subst. replace n with n0 by lia. trivial.
Qed.

Lemma eq_of_even_get_eq (x y : nat)
  : (even_get x = even_get y) -> (even_get x ≠ None) -> x = y.
Proof. unfold even_get.
  destruct (parity x) eqn:a; destruct (parity y) eqn:b.
  - intros. inversion H. subst. apply eq_of_parity_eq. rewrite a, b. trivial.
  - intro. discriminate.
  - intro. discriminate.
  - intros. contradiction.
Qed.
  
Lemma eq_of_odd_get_eq (x y : nat)
  : (odd_get x = odd_get y) -> (odd_get x ≠ None) -> x = y. 
Proof.  unfold odd_get.
  destruct (parity x) eqn:a; destruct (parity y) eqn:b.
  - intros. contradiction.
  - intros. contradiction.
  - intros. discriminate.
  - intros. inversion H. subst. apply eq_of_parity_eq. rewrite a, b. trivial.
Qed.

