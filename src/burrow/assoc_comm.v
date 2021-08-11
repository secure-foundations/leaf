From stdpp Require Import base.
From iris.algebra Require Export cmra.

Section CommAssocTac.

Context {M: Type}.
Context `{!Op M}.
Context `{!Equiv M}.
Context `{!Assoc (≡) (op: M -> M -> M)}.
Context `{!Comm (≡) (op: M -> M -> M)}.
Context `{!Transitive ((≡) : M -> M -> Prop)}.
Context `{!Symmetric ((≡) : M -> M -> Prop)}.
Context `{!Reflexive ((≡) : M -> M -> Prop)}.
Context `{!Proper ((≡) ==> (≡) ==> (≡)) (op: M -> M -> M)}.


Lemma do_comm (a b : M)
  : (a ⋅ b) ≡ (b ⋅ a). Admitted.
  
Lemma do_assoc (a b c : M)
  : (a ⋅ (b ⋅ c)) ≡ ((a ⋅ b) ⋅ c). Admitted.

Lemma comm2 (a b c : M)
  : (a ⋅ b) ⋅ c ≡ (a ⋅ c) ⋅ b.
  Admitted.
  
Lemma from_r (a b x : M)
  : a ≡ b -> (a ⋅ x) ≡ (b ⋅ x). Admitted.
  
Lemma from_1 (a b x : M)
  : a ≡ b -> (x ⋅ a) ≡ (b ⋅ x).
Proof. intro. setoid_rewrite H. apply do_comm. Qed.

Lemma from_2_r (a b a1 b1 x : M)
  : (a1 ⋅ a) ≡ (b1 ⋅ b) -> ((a1 ⋅ x) ⋅ a) ≡ ((b1 ⋅ b) ⋅ x).
Admitted.

Lemma from_2_l (a b a1 b1 x : M)
  : (a1 ⋅ a) ≡ (b1 ⋅ b) -> ((x ⋅ a1) ⋅ a) ≡ ((b1 ⋅ b) ⋅ x).
Admitted.

Lemma from_3_r (a b a1 b1 a2 b2 x : M)
  : ((a2 ⋅ a1) ⋅ a) ≡ ((b2 ⋅ b1) ⋅ b) -> ((a2 ⋅ x) ⋅ a1) ⋅ a ≡ ((b2 ⋅ b1) ⋅ b) ⋅ x.
Admitted.

Lemma from_3_l (a b a1 b1 a2 b2 x : M)
  : ((a2 ⋅ a1) ⋅ a) ≡ ((b2 ⋅ b1) ⋅ b) -> ((x ⋅ a2) ⋅ a1) ⋅ a ≡ ((b2 ⋅ b1) ⋅ b) ⋅ x.
Admitted.

Lemma from_4_r (a b a1 b1 a2 b2 a3 b3 x : M)
  : a3 ⋅ a2 ⋅ a1 ⋅ a ≡ a3 ⋅ b2 ⋅ b1 ⋅ b
    -> a3 ⋅ x ⋅ a2 ⋅ a1 ⋅ a ≡ b3 ⋅ b2 ⋅ b1 ⋅ b ⋅ x.
Admitted.

Lemma from_4_l (a b a1 b1 a2 b2 a3 b3 x : M)
  : a3 ⋅ a2 ⋅ a1 ⋅ a ≡ a3 ⋅ b2 ⋅ b1 ⋅ b
    -> x ⋅ a3 ⋅ a2 ⋅ a1 ⋅ a ≡ b3 ⋅ b2 ⋅ b1 ⋅ b ⋅ x.
Admitted.

Lemma from_5_l (a b a1 b1 a2 b2 a3 b3 a4 a5 x : M)
  : a4 ⋅ a3 ⋅ a2 ⋅ a1 ⋅ a ≡ a4 ⋅ a3 ⋅ b2 ⋅ b1 ⋅ b
    -> a4 ⋅ x ⋅ a3 ⋅ a2 ⋅ a1 ⋅ a ≡ a4 ⋅ b3 ⋅ b2 ⋅ b1 ⋅ b ⋅ x.
Admitted.

Lemma from_5_r (a b a1 b1 a2 b2 a3 b3 a4 a5 x : M)
  : a4 ⋅ a3 ⋅ a2 ⋅ a1 ⋅ a ≡ a4 ⋅ a3 ⋅ b2 ⋅ b1 ⋅ b
    -> x ⋅ a4 ⋅ a3 ⋅ a2 ⋅ a1 ⋅ a ≡ a4 ⋅ b3 ⋅ b2 ⋅ b1 ⋅ b ⋅ x.
Admitted.

End CommAssocTac.

Ltac solve_assoc_comm :=
  repeat (setoid_rewrite do_assoc); trivial;
  repeat (
    try apply from_r; trivial;
    try apply do_comm; trivial;
    try apply from_1; trivial;
    try apply from_2_l; trivial;
    try apply from_2_r; trivial;
    try apply from_3_l; trivial;
    try apply from_3_r; trivial;
    try apply from_4_l; trivial;
    try apply from_4_r; trivial;
    try apply from_5_r; trivial;
    try apply from_5_r; trivial
  ).
  
(*Lemma abcde_state (a b c d e : M)
  : a ⋅ b ⋅ (c ⋅ (d ⋅ e)) ≡ a ⋅ d ⋅ (b ⋅ c ⋅ e).
Proof. solve_assoc_comm.*)


  
(*Lemma test (a b c d e : M)
  : a ⋅ (b ⋅ c) ⋅ (d ⋅ e) ≡ (b ⋅ e) ⋅ ((c ⋅ d) ⋅ a). 
Proof. solve_assoc_comm. *)

