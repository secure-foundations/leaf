From stdpp.unstable Require Import bitblast.

Local Open Scope Z_scope.

Goal ∀ x a k,
  Z.land x (Z.land (Z.ones k) (Z.ones k) ≪ a) =
  Z.land (Z.land (x ≫ a) (Z.ones k)) (Z.ones k) ≪ a.
Proof. intros. bitblast. Qed.

Goal ∀ i,
  1 ≪ i = Z.land (Z.ones 1) (Z.ones 1) ≪ i.
Proof. intros. bitblast. Qed.

Goal ∀ N k,
  0 ≤ k ≤ N → Z.ones N ≫ (N - k) = Z.ones k.
Proof. intros. bitblast. Qed.

Goal ∀ z,
  Z.land z (-1) = z.
Proof. intros. bitblast. Qed.

Goal ∀ z,
  Z.land z 0x20000 = 0 →
  Z.land (z ≫ 17) (Z.ones 1) = 0.
Proof.
  intros ? Hz. bitblast as n.
  by bitblast Hz with (n + 17).
Qed.

Goal ∀ z, 0 ≤ z < 2 ^ 64 →
   Z.land z 0xfff0000000000007 = 0 ↔ z < 2 ^ 52 ∧ z `mod` 8 = 0.
Proof.
  intros z ?. split.
  - intros Hx. split.
    + apply Z.bounded_iff_bits_nonneg; [lia..|]. intros n ?. bitblast.
      by bitblast Hx with n.
    + bitblast as n. by bitblast Hx with n.
  - intros [H1 H2]. bitblast as n. by bitblast H2 with n.
Qed.
