From stdpp Require Import propset.

Lemma diagonal : {[ (a,b) : nat * nat | a = b ]} ≡ (λ x, (x,x)) <$> ⊤.
Proof. set_unfold. intros []. naive_solver. Qed.

Lemma diagonal2 : {[ (a,b) | a =@{nat} b ]} ≡ {[ x | x.1 = x.2 ]}.
Proof. set_unfold. intros []. naive_solver. Qed.

Lemma firstis42 : {[ (x, _) : nat * nat | x = 42 ]} ≡ (42,.) <$> ⊤.
Proof. set_unfold. intros []. naive_solver. Qed.

Inductive foo := Foo (n : nat).

Definition set_of_positive_foos : {[ Foo x | x ≠ 0 ]} ≡ Foo <$> (Pos.to_nat <$> ⊤).
Proof.
  set_unfold. intros [[]]; naive_solver by (rewrite SuccNat2Pos.id_succ || lia).
Qed.

Lemma simple_pattern_does_not_match : {[ x : nat | x = x]} = PropSet (λ x, x = x).
Proof. exact eq_refl. Qed.
