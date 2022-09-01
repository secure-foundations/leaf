(** This file collects some trivial facts on the Coq types [nat] and [N] for
natural numbers, and the type [Z] for integers. It also declares some useful
notations. *)
From Coq Require Export EqdepFacts PArith NArith ZArith NPeano.
From Coq Require Import QArith Qcanon.
From stdpp Require Export base decidable option.
From stdpp Require Import options.
Local Open Scope nat_scope.

Global Instance comparison_eq_dec : EqDecision comparison.
Proof. solve_decision. Defined.

(** * Notations and properties of [nat] *)
Global Arguments minus !_ !_ / : assert.
Global Arguments Nat.max : simpl nomatch.

Typeclasses Opaque lt.

Reserved Notation "x ≤ y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y ≤ z ≤ z'"
  (at level 70, y at next level, z at next level).

Infix "≤" := le : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat : nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%nat : nat_scope.
Notation "(≤)" := le (only parsing) : nat_scope.
Notation "(<)" := lt (only parsing) : nat_scope.

Infix "`div`" := Nat.div (at level 35) : nat_scope.
Infix "`mod`" := Nat.modulo (at level 35) : nat_scope.
Infix "`max`" := Nat.max (at level 35) : nat_scope.
Infix "`min`" := Nat.min (at level 35) : nat_scope.

Global Instance nat_eq_dec: EqDecision nat := eq_nat_dec.
Global Instance nat_le_dec: RelDecision le := le_dec.
Global Instance nat_lt_dec: RelDecision lt := lt_dec.
Global Instance nat_inhabited: Inhabited nat := populate 0%nat.
Global Instance S_inj: Inj (=) (=) S.
Proof. by injection 1. Qed.
Global Instance nat_le_po: PartialOrder (≤).
Proof. repeat split; repeat intro; auto with lia. Qed.
Global Instance nat_le_total: Total (≤).
Proof. repeat intro; lia. Qed.

Global Instance nat_le_pi: ∀ x y : nat, ProofIrrel (x ≤ y).
Proof.
  assert (∀ x y (p : x ≤ y) y' (q : x ≤ y'),
    y = y' → eq_dep nat (le x) y p y' q) as aux.
  { fix FIX 3. intros x ? [|y p] ? [|y' q].
    - done.
    - clear FIX. intros; exfalso; auto with lia.
    - clear FIX. intros; exfalso; auto with lia.
    - injection 1. intros Hy. by case (FIX x y p y' q Hy). }
  intros x y p q.
  by apply (Eqdep_dec.eq_dep_eq_dec (λ x y, decide (x = y))), aux.
Qed.
Global Instance nat_lt_pi: ∀ x y : nat, ProofIrrel (x < y).
Proof. unfold lt. apply _. Qed.

Lemma nat_le_sum (x y : nat) : x ≤ y ↔ ∃ z, y = x + z.
Proof. split; [exists (y - x); lia | intros [z ->]; lia]. Qed.

Lemma Nat_lt_succ_succ n : n < S (S n).
Proof. auto with arith. Qed.
Lemma Nat_mul_split_l n x1 x2 y1 y2 :
  x2 < n → y2 < n → x1 * n + x2 = y1 * n + y2 → x1 = y1 ∧ x2 = y2.
Proof.
  intros Hx2 Hy2 E. cut (x1 = y1); [intros; subst;lia |].
  revert y1 E. induction x1; simpl; intros [|?]; simpl; auto with lia.
Qed.
Lemma Nat_mul_split_r n x1 x2 y1 y2 :
  x1 < n → y1 < n → x1 + x2 * n = y1 + y2 * n → x1 = y1 ∧ x2 = y2.
Proof. intros. destruct (Nat_mul_split_l n x2 x1 y2 y1); auto with lia. Qed.

Notation lcm := Nat.lcm.
Notation divide := Nat.divide.
Notation "( x | y )" := (divide x y) : nat_scope.
Global Instance Nat_divide_dec : RelDecision Nat.divide.
Proof.
  refine (λ x y, cast_if (decide (lcm x y = y))); by rewrite Nat.divide_lcm_iff.
Defined.
Global Instance: PartialOrder divide.
Proof.
  repeat split; try apply _. intros ??. apply Nat.divide_antisym_nonneg; lia.
Qed.
Global Hint Extern 0 (_ | _) => reflexivity : core.
Lemma Nat_divide_ne_0 x y : (x | y) → y ≠ 0 → x ≠ 0.
Proof. intros Hxy Hy ->. by apply Hy, Nat.divide_0_l. Qed.

Lemma Nat_iter_S {A} n (f: A → A) x : Nat.iter (S n) f x = f (Nat.iter n f x).
Proof. done. Qed.
Lemma Nat_iter_S_r {A} n (f: A → A) x : Nat.iter (S n) f x = Nat.iter n f (f x).
Proof. induction n; by f_equal/=. Qed.
Lemma Nat_iter_add {A} n1 n2 (f : A → A) x :
  Nat.iter (n1 + n2) f x = Nat.iter n1 f (Nat.iter n2 f x).
Proof. induction n1; by f_equal/=. Qed.
Lemma Nat_iter_mul {A} n1 n2 (f : A → A) x :
  Nat.iter (n1 * n2) f x = Nat.iter n1 (Nat.iter n2 f) x.
Proof.
  intros. induction n1 as [|n1 IHn1]; [done|].
  simpl. by rewrite Nat_iter_add, IHn1.
Qed.

Lemma Nat_iter_ind {A} (P : A → Prop) f x k :
  P x → (∀ y, P y → P (f y)) → P (Nat.iter k f x).
Proof. induction k; simpl; auto. Qed.


(** * Notations and properties of [positive] *)
Local Open Scope positive_scope.

Typeclasses Opaque Pos.le.
Typeclasses Opaque Pos.lt.

Infix "≤" := Pos.le : positive_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : positive_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : positive_scope.
Notation "(≤)" := Pos.le (only parsing) : positive_scope.
Notation "(<)" := Pos.lt (only parsing) : positive_scope.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Global Arguments Pos.of_nat : simpl never.
Global Arguments Pmult : simpl never.

Global Instance positive_eq_dec: EqDecision positive := Pos.eq_dec.
Global Instance positive_le_dec: RelDecision Pos.le.
Proof. refine (λ x y, decide ((x ?= y) ≠ Gt)). Defined.
Global Instance positive_lt_dec: RelDecision Pos.lt.
Proof. refine (λ x y, decide ((x ?= y) = Lt)). Defined.
Global Instance positive_le_total: Total Pos.le.
Proof. repeat intro; lia. Qed.

Global Instance positive_inhabited: Inhabited positive := populate 1.

Global Instance maybe_xO : Maybe xO := λ p, match p with p~0 => Some p | _ => None end.
Global Instance maybe_xI : Maybe xI := λ p, match p with p~1 => Some p | _ => None end.
Global Instance xO_inj : Inj (=) (=) (~0).
Proof. by injection 1. Qed.
Global Instance xI_inj : Inj (=) (=) (~1).
Proof. by injection 1. Qed.

(** Since [positive] represents lists of bits, we define list operations
on it. These operations are in reverse, as positives are treated as snoc
lists instead of cons lists. *)
Fixpoint Papp (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => (Papp p1 p2)~0
  | p2~1 => (Papp p1 p2)~1
  end.
Infix "++" := Papp : positive_scope.
Notation "(++)" := Papp (only parsing) : positive_scope.
Notation "( p ++.)" := (Papp p) (only parsing) : positive_scope.
Notation "(.++ q )" := (λ p, Papp p q) (only parsing) : positive_scope.

Fixpoint Preverse_go (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => Preverse_go (p1~0) p2
  | p2~1 => Preverse_go (p1~1) p2
  end.
Definition Preverse : positive → positive := Preverse_go 1.

Global Instance Papp_1_l : LeftId (=) 1 (++).
Proof. intros p. by induction p; intros; f_equal/=. Qed.
Global Instance Papp_1_r : RightId (=) 1 (++).
Proof. done. Qed.
Global Instance Papp_assoc : Assoc (=) (++).
Proof. intros ?? p. by induction p; intros; f_equal/=. Qed.
Global Instance Papp_inj p : Inj (=) (=) (.++ p).
Proof. intros ???. induction p; simplify_eq; auto. Qed.

Lemma Preverse_go_app p1 p2 p3 :
  Preverse_go p1 (p2 ++ p3) = Preverse_go p1 p3 ++ Preverse_go 1 p2.
Proof.
  revert p3 p1 p2.
  cut (∀ p1 p2 p3, Preverse_go (p2 ++ p3) p1 = p2 ++ Preverse_go p3 p1).
  { by intros go p3; induction p3; intros p1 p2; simpl; auto; rewrite <-?go. }
  intros p1; induction p1 as [p1 IH|p1 IH|]; intros p2 p3; simpl; auto.
  - apply (IH _ (_~1)).
  - apply (IH _ (_~0)).
Qed.
Lemma Preverse_app p1 p2 : Preverse (p1 ++ p2) = Preverse p2 ++ Preverse p1.
Proof. unfold Preverse. by rewrite Preverse_go_app. Qed.
Lemma Preverse_xO p : Preverse (p~0) = (1~0) ++ Preverse p.
Proof Preverse_app p (1~0).
Lemma Preverse_xI p : Preverse (p~1) = (1~1) ++ Preverse p.
Proof Preverse_app p (1~1).

Lemma Preverse_involutive p :
  Preverse (Preverse p) = p.
Proof.
  induction p as [p IH|p IH|]; simpl.
  - by rewrite Preverse_xI, Preverse_app, IH.
  - by rewrite Preverse_xO, Preverse_app, IH.
  - reflexivity.
Qed.

Global Instance Preverse_inj : Inj (=) (=) Preverse.
Proof.
  intros p q eq.
  rewrite <- (Preverse_involutive p).
  rewrite <- (Preverse_involutive q).
  by rewrite eq.
Qed.

Fixpoint Plength (p : positive) : nat :=
  match p with 1 => 0%nat | p~0 | p~1 => S (Plength p) end.
Lemma Papp_length p1 p2 : Plength (p1 ++ p2) = (Plength p2 + Plength p1)%nat.
Proof. by induction p2; f_equal/=. Qed.

Lemma Plt_sum (x y : positive) : x < y ↔ ∃ z, y = x + z.
Proof.
  split.
  - exists (y - x)%positive. symmetry. apply Pplus_minus. lia.
  - intros [z ->]. lia.
Qed.

(** Duplicate the bits of a positive, i.e. 1~0~1 -> 1~0~0~1~1 and
    1~1~0~0 -> 1~1~1~0~0~0~0 *)
Fixpoint Pdup (p : positive) : positive :=
  match p with
  | 1 => 1
  | p'~0 => (Pdup p')~0~0
  | p'~1 => (Pdup p')~1~1
  end.

Lemma Pdup_app p q :
  Pdup (p ++ q) = Pdup p ++ Pdup q.
Proof.
  revert p.
  induction q as [p IH|p IH|]; intros q; simpl.
  - by rewrite IH.
  - by rewrite IH.
  - reflexivity.
Qed.

Lemma Pdup_suffix_eq p q s1 s2 :
  s1~1~0 ++ Pdup p = s2~1~0 ++ Pdup q → p = q.
Proof.
  revert q.
  induction p as [p IH|p IH|]; intros [q|q|] eq; simplify_eq/=.
  - by rewrite (IH q).
  - by rewrite (IH q).
  - reflexivity.
Qed.

Global Instance Pdup_inj : Inj (=) (=) Pdup.
Proof.
  intros p q eq.
  apply (Pdup_suffix_eq _ _ 1 1).
  by rewrite eq.
Qed.

Lemma Preverse_Pdup p :
  Preverse (Pdup p) = Pdup (Preverse p).
Proof.
  induction p as [p IH|p IH|]; simpl.
  - rewrite 3!Preverse_xI.
    rewrite (assoc_L (++)).
    rewrite IH.
    rewrite Pdup_app.
    reflexivity.
  - rewrite 3!Preverse_xO.
    rewrite (assoc_L (++)).
    rewrite IH.
    rewrite Pdup_app.
    reflexivity.
  - reflexivity.
Qed.

Local Close Scope positive_scope.

(** * Notations and properties of [N] *)
Typeclasses Opaque N.le.
Typeclasses Opaque N.lt.

Infix "≤" := N.le : N_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%N : N_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%N : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.
Notation "(<)" := N.lt (only parsing) : N_scope.

Infix "`div`" := N.div (at level 35) : N_scope.
Infix "`mod`" := N.modulo (at level 35) : N_scope.
Infix "`max`" := N.max (at level 35) : N_scope.
Infix "`min`" := N.min (at level 35) : N_scope.

Global Arguments N.add : simpl never.

Global Instance Npos_inj : Inj (=) (=) Npos.
Proof. by injection 1. Qed.

Global Instance N_eq_dec: EqDecision N := N.eq_dec.
Global Program Instance N_le_dec : RelDecision N.le := λ x y,
  match N.compare x y with Gt => right _ | _ => left _ end.
Solve Obligations with naive_solver.
Global Program Instance N_lt_dec : RelDecision N.lt := λ x y,
  match N.compare x y with Lt => left _ | _ => right _ end.
Solve Obligations with naive_solver.
Global Instance N_inhabited: Inhabited N := populate 1%N.
Global Instance N_lt_pi x y : ProofIrrel (x < y)%N.
Proof. unfold N.lt. apply _. Qed.

Global Instance N_le_po: PartialOrder (≤)%N.
Proof.
  repeat split; red; [apply N.le_refl | apply N.le_trans | apply N.le_antisymm].
Qed.
Global Instance N_le_total: Total (≤)%N.
Proof. repeat intro; lia. Qed.

Global Hint Extern 0 (_ ≤ _)%N => reflexivity : core.

(** * Notations and properties of [Z] *)
Local Open Scope Z_scope.

Typeclasses Opaque Z.le.
Typeclasses Opaque Z.lt.

Infix "≤" := Z.le : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Z_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Notation "(<)" := Z.lt (only parsing) : Z_scope.

Infix "`div`" := Z.div (at level 35) : Z_scope.
Infix "`mod`" := Z.modulo (at level 35) : Z_scope.
Infix "`quot`" := Z.quot (at level 35) : Z_scope.
Infix "`rem`" := Z.rem (at level 35) : Z_scope.
Infix "≪" := Z.shiftl (at level 35) : Z_scope.
Infix "≫" := Z.shiftr (at level 35) : Z_scope.
Infix "`max`" := Z.max (at level 35) : Z_scope.
Infix "`min`" := Z.min (at level 35) : Z_scope.

Global Instance Zpos_inj : Inj (=) (=) Zpos.
Proof. by injection 1. Qed.
Global Instance Zneg_inj : Inj (=) (=) Zneg.
Proof. by injection 1. Qed.

Global Instance Z_of_nat_inj : Inj (=) (=) Z.of_nat.
Proof. intros n1 n2. apply Nat2Z.inj. Qed.

Global Instance Z_eq_dec: EqDecision Z := Z.eq_dec.
Global Instance Z_le_dec: RelDecision Z.le := Z_le_dec.
Global Instance Z_lt_dec: RelDecision Z.lt := Z_lt_dec.
Global Instance Z_ge_dec: RelDecision Z.ge := Z_ge_dec.
Global Instance Z_gt_dec: RelDecision Z.gt := Z_gt_dec.
Global Instance Z_inhabited: Inhabited Z := populate 1.
Global Instance Z_lt_pi x y : ProofIrrel (x < y).
Proof. unfold Z.lt. apply _. Qed.

Global Instance Z_le_po : PartialOrder (≤).
Proof.
  repeat split; red; [apply Z.le_refl | apply Z.le_trans | apply Z.le_antisymm].
Qed.
Global Instance Z_le_total: Total Z.le.
Proof. repeat intro; lia. Qed.

Lemma Z_pow_pred_r n m : 0 < m → n * n ^ (Z.pred m) = n ^ m.
Proof.
  intros. rewrite <-Z.pow_succ_r, Z.succ_pred; [done|]. by apply Z.lt_le_pred.
Qed.
Lemma Z_quot_range_nonneg k x y : 0 ≤ x < k → 0 < y → 0 ≤ x `quot` y < k.
Proof.
  intros [??] ?.
  destruct (decide (y = 1)); subst; [rewrite Z.quot_1_r; auto |].
  destruct (decide (x = 0)); subst; [rewrite Z.quot_0_l; auto with lia |].
  split; [apply Z.quot_pos; lia|].
  trans x; auto. apply Z.quot_lt; lia.
Qed.

Global Arguments Z.pred : simpl never.
Global Arguments Z.succ : simpl never.
Global Arguments Z.of_nat : simpl never.
Global Arguments Z.to_nat : simpl never.
Global Arguments Z.mul : simpl never.
Global Arguments Z.add : simpl never.
Global Arguments Z.sub : simpl never.
Global Arguments Z.opp : simpl never.
Global Arguments Z.pow : simpl never.
Global Arguments Z.div : simpl never.
Global Arguments Z.modulo : simpl never.
Global Arguments Z.quot : simpl never.
Global Arguments Z.rem : simpl never.
Global Arguments Z.shiftl : simpl never.
Global Arguments Z.shiftr : simpl never.
Global Arguments Z.gcd : simpl never.
Global Arguments Z.lcm : simpl never.
Global Arguments Z.min : simpl never.
Global Arguments Z.max : simpl never.
Global Arguments Z.lor : simpl never.
Global Arguments Z.land : simpl never.
Global Arguments Z.lxor : simpl never.
Global Arguments Z.lnot : simpl never.
Global Arguments Z.square : simpl never.
Global Arguments Z.abs : simpl never.

Lemma Z_to_nat_neq_0_pos x : Z.to_nat x ≠ 0%nat → 0 < x.
Proof. by destruct x. Qed.
Lemma Z_to_nat_neq_0_nonneg x : Z.to_nat x ≠ 0%nat → 0 ≤ x.
Proof. by destruct x. Qed.
Lemma Z_mod_pos x y : 0 < y → 0 ≤ x `mod` y.
Proof. apply Z.mod_pos_bound. Qed.

Global Hint Resolve Z.lt_le_incl : zpos.
Global Hint Resolve Z.add_nonneg_pos Z.add_pos_nonneg Z.add_nonneg_nonneg : zpos.
Global Hint Resolve Z.mul_nonneg_nonneg Z.mul_pos_pos : zpos.
Global Hint Resolve Z.pow_pos_nonneg Z.pow_nonneg: zpos.
Global Hint Resolve Z_mod_pos Z.div_pos : zpos.
Global Hint Extern 1000 => lia : zpos.

Lemma Z_to_nat_nonpos x : x ≤ 0 → Z.to_nat x = 0%nat.
Proof. destruct x; simpl; auto using Z2Nat.inj_neg. by intros []. Qed.
Lemma Z2Nat_inj_pow (x y : nat) : Z.of_nat (x ^ y) = (Z.of_nat x) ^ (Z.of_nat y).
Proof.
  induction y as [|y IH]; [by rewrite Z.pow_0_r, Nat.pow_0_r|].
  by rewrite Nat.pow_succ_r, Nat2Z.inj_succ, Z.pow_succ_r,
    Nat2Z.inj_mul, IH by auto with zpos.
Qed.
Lemma Nat2Z_divide n m : (Z.of_nat n | Z.of_nat m) ↔ (n | m)%nat.
Proof.
  split.
  - rewrite <-(Nat2Z.id m) at 2; intros [i ->]; exists (Z.to_nat i).
    destruct (decide (0 ≤ i)%Z).
    { by rewrite Z2Nat.inj_mul, Nat2Z.id by lia. }
    by rewrite !Z_to_nat_nonpos by auto using Z.mul_nonpos_nonneg with lia.
  - intros [i ->]. exists (Z.of_nat i). by rewrite Nat2Z.inj_mul.
Qed.
Lemma Z2Nat_divide n m :
  0 ≤ n → 0 ≤ m → (Z.to_nat n | Z.to_nat m)%nat ↔ (n | m).
Proof. intros. by rewrite <-Nat2Z_divide, !Z2Nat.id by done. Qed.
Lemma Nat2Z_inj_div x y : Z.of_nat (x `div` y) = (Z.of_nat x) `div` (Z.of_nat y).
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.div_unique with (Z.of_nat $ x `mod` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Lemma Nat2Z_inj_mod x y : Z.of_nat (x `mod` y) = (Z.of_nat x) `mod` (Z.of_nat y).
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.mod_unique with (Z.of_nat $ x `div` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Lemma Z2Nat_inj_div x y :
  0 ≤ x → 0 ≤ y →
  Z.to_nat (x `div` y) = (Z.to_nat x `div` Z.to_nat y)%nat.
Proof.
  intros. destruct (decide (y = Z.of_nat 0%nat)); [by subst; destruct x|].
  pose proof (Z.div_pos x y).
  apply (inj Z.of_nat). by rewrite Nat2Z_inj_div, !Z2Nat.id by lia.
Qed.
Lemma Z2Nat_inj_mod x y :
  0 ≤ x → 0 ≤ y →
  Z.to_nat (x `mod` y) = (Z.to_nat x `mod` Z.to_nat y)%nat.
Proof.
  intros. destruct (decide (y = Z.of_nat 0%nat)); [by subst; destruct x|].
  pose proof (Z_mod_pos x y).
  apply (inj Z.of_nat). by rewrite Nat2Z_inj_mod, !Z2Nat.id by lia.
Qed.
Lemma Z_succ_pred_induction y (P : Z → Prop) :
  P y →
  (∀ x, y ≤ x → P x → P (Z.succ x)) →
  (∀ x, x ≤ y → P x → P (Z.pred x)) →
  (∀ x, P x).
Proof. intros H0 HS HP. by apply (Z.order_induction' _ _ y). Qed.
Lemma Zmod_in_range q a c :
  q * c ≤ a < (q + 1) * c →
  a `mod` c = a - q * c.
Proof. intros ?. symmetry. apply Z.mod_unique_pos with q; lia. Qed.

Lemma Z_ones_spec n m:
  0 ≤ m → 0 ≤ n →
  Z.testbit (Z.ones n) m = bool_decide (m < n).
Proof.
  intros. case_bool_decide.
  - by rewrite Z.ones_spec_low by lia.
  - by rewrite Z.ones_spec_high by lia.
Qed.

Lemma Z_bounded_iff_bits_nonneg k n :
  0 ≤ k → 0 ≤ n →
  n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = false.
Proof.
  intros. destruct (decide (n = 0)) as [->|].
  { naive_solver eauto using Z.bits_0, Z.pow_pos_nonneg with lia. }
  split.
  { intros Hb%Z.log2_lt_pow2 l Hl; [|lia]. apply Z.bits_above_log2; lia. }
  intros Hl. apply Z.nle_gt; intros ?.
  assert (Z.testbit n (Z.log2 n) = false) as Hbit.
  { apply Hl, Z.log2_le_pow2; lia. }
  by rewrite Z.bit_log2 in Hbit by lia.
Qed.

(* Goals of the form [0 ≤ n ≤ 2^k] appear often. So we also define the
derived version [Z_bounded_iff_bits_nonneg'] that does not require
proving [0 ≤ n] twice in that case. *)
Lemma Z_bounded_iff_bits_nonneg' k n :
  0 ≤ k → 0 ≤ n →
  0 ≤ n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = false.
Proof. intros ??. rewrite <-Z_bounded_iff_bits_nonneg; lia. Qed.

Lemma Z_bounded_iff_bits k n :
  0 ≤ k →
  -2^k ≤ n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = bool_decide (n < 0).
Proof.
  intros Hk.
  case_bool_decide; [ | rewrite <-Z_bounded_iff_bits_nonneg; lia].
  assert(n = - Z.abs n)%Z as -> by lia.
  split.
  { intros [? _] l Hl.
    rewrite Z.bits_opp, negb_true_iff by lia.
    apply Z_bounded_iff_bits_nonneg with k; lia. }
  intros Hbit. split.
  - rewrite <-Z.opp_le_mono, <-Z.lt_pred_le.
    apply Z_bounded_iff_bits_nonneg; [lia..|]. intros l Hl.
    rewrite <-negb_true_iff, <-Z.bits_opp by lia.
    by apply Hbit.
  - etrans; [|apply Z.pow_pos_nonneg]; lia.
Qed.


Local Close Scope Z_scope.

(** * Injectivity of casts *)
Global Instance N_of_nat_inj: Inj (=) (=) N.of_nat := Nat2N.inj.
Global Instance nat_of_N_inj: Inj (=) (=) N.to_nat := N2Nat.inj.
Global Instance nat_of_pos_inj: Inj (=) (=) Pos.to_nat := Pos2Nat.inj.
Global Instance pos_of_Snat_inj: Inj (=) (=) Pos.of_succ_nat := SuccNat2Pos.inj.
Global Instance Z_of_N_inj: Inj (=) (=) Z.of_N := N2Z.inj.
(* Add others here. *)

(** * Notations and properties of [Qc] *)
Typeclasses Opaque Qcle.
Typeclasses Opaque Qclt.

Local Open Scope Qc_scope.
Delimit Scope Qc_scope with Qc.
Notation "1" := (Q2Qc 1) : Qc_scope.
Notation "2" := (1+1) : Qc_scope.
Notation "- 1" := (Qcopp 1) : Qc_scope.
Notation "- 2" := (Qcopp 2) : Qc_scope.
Infix "≤" := Qcle : Qc_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Qc_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Qc_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Qc_scope.
Notation "(≤)" := Qcle (only parsing) : Qc_scope.
Notation "(<)" := Qclt (only parsing) : Qc_scope.

Global Hint Extern 1 (_ ≤ _) => reflexivity || discriminate : core.
Global Arguments Qred : simpl never.

Lemma inject_Z_Qred n : Qred (inject_Z n) = inject_Z n.
Proof. apply Qred_identity; auto using Z.gcd_1_r. Qed.
Definition Qc_of_Z (n : Z) : Qc := Qcmake _ (inject_Z_Qred n).

Global Instance Qc_eq_dec: EqDecision Qc := Qc_eq_dec.
Global Program Instance Qc_le_dec: RelDecision Qcle := λ x y,
  if Qclt_le_dec y x then right _ else left _.
Next Obligation. intros x y; apply Qclt_not_le. Qed.
Next Obligation. done. Qed.
Global Program Instance Qc_lt_dec: RelDecision Qclt := λ x y,
  if Qclt_le_dec x y then left _ else right _.
Next Obligation. done. Qed.
Next Obligation. intros x y; apply Qcle_not_lt. Qed.
Global Instance Qc_lt_pi x y : ProofIrrel (x < y).
Proof. unfold Qclt. apply _. Qed.

Global Instance Qc_le_po: PartialOrder (≤).
Proof.
  repeat split; red; [apply Qcle_refl | apply Qcle_trans | apply Qcle_antisym].
Qed.
Global Instance Qc_lt_strict: StrictOrder (<).
Proof.
  split; red; [|apply Qclt_trans].
  intros x Hx. by destruct (Qclt_not_eq x x).
Qed.
Global Instance Qc_le_total: Total Qcle.
Proof. intros x y. destruct (Qclt_le_dec x y); auto using Qclt_le_weak. Qed.

Lemma Qcmult_0_l x : 0 * x = 0.
Proof. ring. Qed.
Lemma Qcmult_0_r x : x * 0 = 0.
Proof. ring. Qed.
Lemma Qcplus_diag x : (x + x)%Qc = (2 * x)%Qc.
Proof. ring. Qed.
Lemma Qcle_ngt (x y : Qc) : x ≤ y ↔ ¬y < x.
Proof. split; auto using Qcle_not_lt, Qcnot_lt_le. Qed.
Lemma Qclt_nge (x y : Qc) : x < y ↔ ¬y ≤ x.
Proof. split; auto using Qclt_not_le, Qcnot_le_lt. Qed.
Lemma Qcplus_le_mono_l (x y z : Qc) : x ≤ y ↔ z + x ≤ z + y.
Proof.
  split; intros.
  - by apply Qcplus_le_compat.
  - replace x with ((0 - z) + (z + x)) by ring.
    replace y with ((0 - z) + (z + y)) by ring.
    by apply Qcplus_le_compat.
Qed.
Lemma Qcplus_le_mono_r (x y z : Qc) : x ≤ y ↔ x + z ≤ y + z.
Proof. rewrite !(Qcplus_comm _ z). apply Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_l (x y z : Qc) : x < y ↔ z + x < z + y.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_r (x y z : Qc) : x < y ↔ x + z < y + z.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_r. Qed.
Global Instance Qcopp_inj : Inj (=) (=) Qcopp.
Proof.
  intros x y H. by rewrite <-(Qcopp_involutive x), H, Qcopp_involutive.
Qed.
Global Instance Qcplus_inj_r z : Inj (=) (=) (Qcplus z).
Proof.
  intros x y H. by apply (anti_symm (≤));rewrite (Qcplus_le_mono_l _ _ z), H.
Qed.
Global Instance Qcplus_inj_l z : Inj (=) (=) (λ x, x + z).
Proof.
  intros x y H. by apply (anti_symm (≤)); rewrite (Qcplus_le_mono_r _ _ z), H.
Qed.
Lemma Qcplus_pos_nonneg (x y : Qc) : 0 < x → 0 ≤ y → 0 < x + y.
Proof.
  intros. apply Qclt_le_trans with (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonneg_pos (x y : Qc) : 0 ≤ x → 0 < y → 0 < x + y.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_pos_nonneg. Qed.
Lemma Qcplus_pos_pos (x y : Qc) : 0 < x → 0 < y → 0 < x + y.
Proof. auto using Qcplus_pos_nonneg, Qclt_le_weak. Qed.
Lemma Qcplus_nonneg_nonneg (x y : Qc) : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
Proof.
  intros. trans (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_neg_nonpos (x y : Qc) : x < 0 → y ≤ 0 → x + y < 0.
Proof.
  intros. apply Qcle_lt_trans with (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonpos_neg (x y : Qc) : x ≤ 0 → y < 0 → x + y < 0.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_neg_nonpos. Qed.
Lemma Qcplus_neg_neg (x y : Qc) : x < 0 → y < 0 → x + y < 0.
Proof. auto using Qcplus_nonpos_neg, Qclt_le_weak. Qed.
Lemma Qcplus_nonpos_nonpos (x y : Qc) : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
Proof.
  intros. trans (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcmult_le_mono_nonneg_l x y z : 0 ≤ z → x ≤ y → z * x ≤ z * y.
Proof. intros. rewrite !(Qcmult_comm z). by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_nonneg_r x y z : 0 ≤ z → x ≤ y → x * z ≤ y * z.
Proof. intros. by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_pos_l x y z : 0 < z → x ≤ y ↔ z * x ≤ z * y.
Proof.
  split; auto using Qcmult_le_mono_nonneg_l, Qclt_le_weak.
  rewrite !Qcle_ngt, !(Qcmult_comm z).
  intuition auto using Qcmult_lt_compat_r.
Qed.
Lemma Qcmult_le_mono_pos_r x y z : 0 < z → x ≤ y ↔ x * z ≤ y * z.
Proof. rewrite !(Qcmult_comm _ z). by apply Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_l x y z : 0 < z → x < y ↔ z * x < z * y.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_r x y z : 0 < z → x < y ↔ x * z < y * z.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_r. Qed.
Lemma Qcmult_pos_pos x y : 0 < x → 0 < y → 0 < x * y.
Proof.
  intros. apply Qcle_lt_trans with (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_lt_mono_pos_r.
Qed.
Lemma Qcmult_nonneg_nonneg x y : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof.
  intros. trans (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_le_mono_nonneg_r.
Qed.

Lemma Qcinv_pos x : 0 < x → 0 < /x.
Proof.
  intros. assert (0 ≠ x) by (by apply Qclt_not_eq).
  by rewrite (Qcmult_lt_mono_pos_r _ _ x), Qcmult_0_l, Qcmult_inv_l by done.
Qed.

Lemma Z2Qc_inj_0 : Qc_of_Z 0 = 0.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj_1 : Qc_of_Z 1 = 1.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj_2 : Qc_of_Z 2 = 2.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj n m : Qc_of_Z n = Qc_of_Z m → n = m.
Proof. by injection 1. Qed.
Lemma Z2Qc_inj_iff n m : Qc_of_Z n = Qc_of_Z m ↔ n = m.
Proof. split; [ auto using Z2Qc_inj | by intros -> ]. Qed.
Lemma Z2Qc_inj_le n m : (n ≤ m)%Z ↔ Qc_of_Z n ≤ Qc_of_Z m.
Proof. by rewrite Zle_Qle. Qed.
Lemma Z2Qc_inj_lt n m : (n < m)%Z ↔ Qc_of_Z n < Qc_of_Z m.
Proof. by rewrite Zlt_Qlt. Qed.
Lemma Z2Qc_inj_add n m : Qc_of_Z (n + m) = Qc_of_Z n + Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_plus. Qed.
Lemma Z2Qc_inj_mul n m : Qc_of_Z (n * m) = Qc_of_Z n * Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_mult. Qed.
Lemma Z2Qc_inj_opp n : Qc_of_Z (-n) = -Qc_of_Z n.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_opp. Qed.
Lemma Z2Qc_inj_sub n m : Qc_of_Z (n - m) = Qc_of_Z n - Qc_of_Z m.
Proof.
  apply Qc_is_canon; simpl.
  by rewrite !Qred_correct, <-inject_Z_opp, <-inject_Z_plus.
Qed.
Local Close Scope Qc_scope.

(** * Positive rationals *)
Declare Scope Qp_scope.
Delimit Scope Qp_scope with Qp.

Record Qp := mk_Qp { Qp_to_Qc : Qc ; Qp_prf : (0 < Qp_to_Qc)%Qc }.
Add Printing Constructor Qp.
Bind Scope Qp_scope with Qp.
Global Arguments Qp_to_Qc _%Qp : assert.

Local Open Scope Qp_scope.

Lemma Qp_to_Qc_inj_iff p q : Qp_to_Qc p = Qp_to_Qc q ↔ p = q.
Proof.
  split; [|by intros ->].
  destruct p, q; intros; simplify_eq/=; f_equal; apply (proof_irrel _).
Qed.
Global Instance Qp_eq_dec : EqDecision Qp.
Proof.
  refine (λ p q, cast_if (decide (Qp_to_Qc p = Qp_to_Qc q)));
    by rewrite <-Qp_to_Qc_inj_iff.
Defined.

Definition Qp_add (p q : Qp) : Qp :=
  let 'mk_Qp p Hp := p in let 'mk_Qp q Hq := q in
  mk_Qp (p + q) (Qcplus_pos_pos _ _ Hp Hq).
Global Arguments Qp_add : simpl never.

Definition Qp_sub (p q : Qp) : option Qp :=
  let 'mk_Qp p Hp := p in let 'mk_Qp q Hq := q in
  let pq := (p - q)%Qc in
  guard (0 < pq)%Qc as Hpq; Some (mk_Qp pq Hpq).
Global Arguments Qp_sub : simpl never.

Definition Qp_mul (p q : Qp) : Qp :=
  let 'mk_Qp p Hp := p in let 'mk_Qp q Hq := q in
  mk_Qp (p * q) (Qcmult_pos_pos _ _ Hp Hq).
Global Arguments Qp_mul : simpl never.

Definition Qp_inv (q : Qp) : Qp :=
  let 'mk_Qp q Hq := q return _ in
  mk_Qp (/ q)%Qc (Qcinv_pos _ Hq).
Global Arguments Qp_inv : simpl never.

Definition Qp_div (p q : Qp) : Qp := Qp_mul p (Qp_inv q).
Typeclasses Opaque Qp_div.
Global Arguments Qp_div : simpl never.

Infix "+" := Qp_add : Qp_scope.
Infix "-" := Qp_sub : Qp_scope.
Infix "*" := Qp_mul : Qp_scope.
Notation "/ q" := (Qp_inv q) : Qp_scope.
Infix "/" := Qp_div : Qp_scope.

Lemma Qp_to_Qc_inj_add p q : (Qp_to_Qc (p + q) = Qp_to_Qc p + Qp_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.
Lemma Qp_to_Qc_inj_mul p q : (Qp_to_Qc (p * q) = Qp_to_Qc p * Qp_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.

Program Definition pos_to_Qp (n : positive) : Qp := mk_Qp (Qc_of_Z $ Z.pos n) _.
Next Obligation. intros n. by rewrite <-Z2Qc_inj_0, <-Z2Qc_inj_lt. Qed.
Global Arguments pos_to_Qp : simpl never.

Notation "1" := (pos_to_Qp 1) : Qp_scope.
Notation "2" := (pos_to_Qp 2) : Qp_scope.
Notation "3" := (pos_to_Qp 3) : Qp_scope.
Notation "4" := (pos_to_Qp 4) : Qp_scope.

Definition Qp_le (p q : Qp) : Prop :=
  let 'mk_Qp p _ := p in let 'mk_Qp q _ := q in (p ≤ q)%Qc.
Definition Qp_lt (p q : Qp) : Prop :=
  let 'mk_Qp p _ := p in let 'mk_Qp q _ := q in (p < q)%Qc.

Infix "≤" := Qp_le : Qp_scope.
Infix "<" := Qp_lt : Qp_scope.
Notation "p ≤ q ≤ r" := (p ≤ q ∧ q ≤ r) : Qp_scope.
Notation "p ≤ q < r" := (p ≤ q ∧ q < r) : Qp_scope.
Notation "p < q < r" := (p < q ∧ q < r) : Qp_scope.
Notation "p < q ≤ r" := (p < q ∧ q ≤ r) : Qp_scope.
Notation "p ≤ q ≤ r ≤ r'" := (p ≤ q ∧ q ≤ r ∧ r ≤ r') : Qp_scope.
Notation "(≤)" := Qp_le (only parsing) : Qp_scope.
Notation "(<)" := Qp_lt (only parsing) : Qp_scope.

Global Hint Extern 0 (_ ≤ _)%Qp => reflexivity : core.

Lemma Qp_to_Qc_inj_le p q : p ≤ q ↔ (Qp_to_Qc p ≤ Qp_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.
Lemma Qp_to_Qc_inj_lt p q : p < q ↔ (Qp_to_Qc p < Qp_to_Qc q)%Qc.
Proof. by destruct p, q. Qed.

Global Instance Qp_le_dec : RelDecision (≤).
Proof.
  refine (λ p q, cast_if (decide (Qp_to_Qc p ≤ Qp_to_Qc q)%Qc));
    by rewrite Qp_to_Qc_inj_le.
Qed.
Global Instance Qp_lt_dec : RelDecision (<).
Proof.
  refine (λ p q, cast_if (decide (Qp_to_Qc p < Qp_to_Qc q)%Qc));
    by rewrite Qp_to_Qc_inj_lt.
Qed.
Global Instance Qp_lt_pi p q : ProofIrrel (p < q).
Proof. destruct p, q; apply _. Qed.

Definition Qp_max (q p : Qp) : Qp := if decide (q ≤ p) then p else q.
Definition Qp_min (q p : Qp) : Qp := if decide (q ≤ p) then q else p.

Infix "`max`" := Qp_max : Qp_scope.
Infix "`min`" := Qp_min : Qp_scope.

Global Instance Qp_inhabited : Inhabited Qp := populate 1.

Global Instance Qp_add_assoc : Assoc (=) Qp_add.
Proof. intros [p ?] [q ?] [r ?]; apply Qp_to_Qc_inj_iff, Qcplus_assoc. Qed.
Global Instance Qp_add_comm : Comm (=) Qp_add.
Proof. intros [p ?] [q ?]; apply Qp_to_Qc_inj_iff, Qcplus_comm. Qed.
Global Instance Qp_add_inj_r p : Inj (=) (=) (Qp_add p).
Proof.
  destruct p as [p ?].
  intros [q1 ?] [q2 ?]. rewrite <-!Qp_to_Qc_inj_iff; simpl. apply (inj (Qcplus p)).
Qed.
Global Instance Qp_add_inj_l p : Inj (=) (=) (λ q, q + p).
Proof.
  destruct p as [p ?].
  intros [q1 ?] [q2 ?]. rewrite <-!Qp_to_Qc_inj_iff; simpl. apply (inj (λ q, q + p)%Qc).
Qed.

Global Instance Qp_mul_assoc : Assoc (=) Qp_mul.
Proof. intros [p ?] [q ?] [r ?]. apply Qp_to_Qc_inj_iff, Qcmult_assoc. Qed.
Global Instance Qp_mul_comm : Comm (=) Qp_mul.
Proof. intros [p ?] [q ?]; apply Qp_to_Qc_inj_iff, Qcmult_comm. Qed.
Global Instance Qp_mul_inj_r p : Inj (=) (=) (Qp_mul p).
Proof.
  destruct p as [p ?]. intros [q1 ?] [q2 ?]. rewrite <-!Qp_to_Qc_inj_iff; simpl.
  intros Hpq.
  apply (anti_symm Qcle); apply (Qcmult_le_mono_pos_l _ _ p); by rewrite ?Hpq.
Qed.
Global Instance Qp_mul_inj_l p : Inj (=) (=) (λ q, q * p).
Proof.
  intros q1 q2 Hpq. apply (inj (Qp_mul p)). by rewrite !(comm_L Qp_mul p).
Qed.

Lemma Qp_mul_add_distr_l p q r : p * (q + r) = p * q + p * r.
Proof. destruct p, q, r; by apply Qp_to_Qc_inj_iff, Qcmult_plus_distr_r. Qed.
Lemma Qp_mul_add_distr_r p q r : (p + q) * r = p * r + q * r.
Proof. destruct p, q, r; by apply Qp_to_Qc_inj_iff, Qcmult_plus_distr_l. Qed.
Lemma Qp_mul_1_l p : 1 * p = p.
Proof. destruct p; apply Qp_to_Qc_inj_iff, Qcmult_1_l. Qed.
Lemma Qp_mul_1_r p : p * 1 = p.
Proof. destruct p; apply Qp_to_Qc_inj_iff, Qcmult_1_r. Qed.

Lemma Qp_1_1 : 1 + 1 = 2.
Proof. compute_done. Qed.
Lemma Qp_add_diag p : p + p = 2 * p.
Proof. by rewrite <-Qp_1_1, Qp_mul_add_distr_r, !Qp_mul_1_l. Qed.

Lemma Qp_mul_inv_l p : /p * p = 1.
Proof.
  destruct p as [p ?]; apply Qp_to_Qc_inj_iff; simpl.
  by rewrite Qcmult_inv_l, Z2Qc_inj_1 by (by apply not_symmetry, Qclt_not_eq).
Qed.
Lemma Qp_mul_inv_r p : p * /p = 1.
Proof. by rewrite (comm_L Qp_mul), Qp_mul_inv_l. Qed.
Lemma Qp_inv_mul_distr p q : /(p * q) = /p * /q.
Proof.
  apply (inj (Qp_mul (p * q))).
  rewrite Qp_mul_inv_r, (comm_L Qp_mul p), <-(assoc_L _), (assoc_L Qp_mul p).
  by rewrite Qp_mul_inv_r, Qp_mul_1_l, Qp_mul_inv_r.
Qed.
Lemma Qp_inv_involutive p : / /p = p.
Proof.
  rewrite <-(Qp_mul_1_l (/ /p)), <-(Qp_mul_inv_r p), <-(assoc_L _).
  by rewrite Qp_mul_inv_r, Qp_mul_1_r.
Qed.
Global Instance Qp_inv_inj : Inj (=) (=) Qp_inv.
Proof.
  intros p1 p2 Hp. apply (inj (Qp_mul (/p1))).
  by rewrite Qp_mul_inv_l, Hp, Qp_mul_inv_l.
Qed.
Lemma Qp_inv_1 : /1 = 1.
Proof. compute_done. Qed.
Lemma Qp_inv_half_half : /2 + /2 = 1.
Proof. compute_done. Qed.
Lemma Qp_inv_quarter_quarter : /4 + /4 = /2.
Proof. compute_done. Qed.

Lemma Qp_div_diag p : p / p = 1.
Proof. apply Qp_mul_inv_r. Qed.
Lemma Qp_mul_div_l p q : (p / q) * q = p.
Proof. unfold Qp_div. by rewrite <-(assoc_L _), Qp_mul_inv_l, Qp_mul_1_r. Qed.
Lemma Qp_mul_div_r p q : q * (p / q) = p.
Proof. by rewrite (comm_L Qp_mul q), Qp_mul_div_l. Qed.
Lemma Qp_div_add_distr p q r : (p + q) / r = p / r + q / r.
Proof. apply Qp_mul_add_distr_r. Qed.
Lemma Qp_div_div p q r : (p / q) / r = p / (q * r).
Proof. unfold Qp_div. by rewrite Qp_inv_mul_distr, (assoc_L _). Qed.
Lemma Qp_div_mul_cancel_l p q r : (r * p) / (r * q) = p / q.
Proof.
  rewrite <-Qp_div_div. f_equiv. unfold Qp_div.
  by rewrite (comm_L Qp_mul r), <-(assoc_L _), Qp_mul_inv_r, Qp_mul_1_r.
Qed.
Lemma Qp_div_mul_cancel_r p q r : (p * r) / (q * r) = p / q.
Proof. by rewrite <-!(comm_L Qp_mul r), Qp_div_mul_cancel_l. Qed.
Lemma Qp_div_1 p : p / 1 = p.
Proof. by rewrite <-(Qp_mul_1_r (p / 1)), Qp_mul_div_l. Qed.
Lemma Qp_div_2 p : p / 2 + p / 2 = p.
Proof.
  rewrite <-Qp_div_add_distr, Qp_add_diag.
  rewrite <-(Qp_mul_1_r 2) at 2. by rewrite Qp_div_mul_cancel_l, Qp_div_1.
Qed.
Lemma Qp_div_2_mul p q : p / (2 * q) + p / (2 * q) = p / q.
Proof. by rewrite <-Qp_div_add_distr, Qp_add_diag, Qp_div_mul_cancel_l. Qed.
Lemma Qp_half_half : 1 / 2 + 1 / 2 = 1.
Proof. compute_done. Qed.
Lemma Qp_quarter_quarter : 1 / 4 + 1 / 4 = 1 / 2.
Proof. compute_done. Qed.
Lemma Qp_quarter_three_quarter : 1 / 4 + 3 / 4 = 1.
Proof. compute_done. Qed.
Lemma Qp_three_quarter_quarter : 3 / 4 + 1 / 4 = 1.
Proof. compute_done. Qed.
Global Instance Qp_div_inj_r p : Inj (=) (=) (Qp_div p).
Proof. unfold Qp_div; apply _. Qed.
Global Instance Qp_div_inj_l p : Inj (=) (=) (λ q, q / p)%Qp.
Proof. unfold Qp_div; apply _. Qed.

Global Instance Qp_le_po : PartialOrder (≤)%Qp.
Proof.
  split; [split|].
  - intros p. by apply Qp_to_Qc_inj_le.
  - intros p q r. rewrite !Qp_to_Qc_inj_le. by etrans.
  - intros p q. rewrite !Qp_to_Qc_inj_le, <-Qp_to_Qc_inj_iff. apply Qcle_antisym.
Qed.
Global Instance Qp_lt_strict : StrictOrder (<)%Qp.
Proof.
  split.
  - intros p ?%Qp_to_Qc_inj_lt. by apply (irreflexivity (<)%Qc (Qp_to_Qc p)).
  - intros p q r. rewrite !Qp_to_Qc_inj_lt. by etrans.
Qed.
Global Instance Qp_le_total: Total (≤)%Qp.
Proof. intros p q. rewrite !Qp_to_Qc_inj_le. apply (total Qcle). Qed.

Lemma Qp_lt_le_incl p q : p < q → p ≤ q.
Proof. rewrite Qp_to_Qc_inj_lt, Qp_to_Qc_inj_le. apply Qclt_le_weak. Qed.
Lemma Qp_le_lteq p q : p ≤ q ↔ p < q ∨ p = q.
Proof.
  rewrite Qp_to_Qc_inj_lt, Qp_to_Qc_inj_le, <-Qp_to_Qc_inj_iff. split.
  - intros [?| ->]%Qcle_lt_or_eq; auto.
  - intros [?| ->]; auto using Qclt_le_weak.
Qed.
Lemma Qp_lt_ge_cases p q : {p < q} + {q ≤ p}.
Proof.
  refine (cast_if (Qclt_le_dec (Qp_to_Qc p) (Qp_to_Qc q)%Qc));
    [by apply Qp_to_Qc_inj_lt|by apply Qp_to_Qc_inj_le].
Defined.
Lemma Qp_le_lt_trans p q r : p ≤ q → q < r → p < r.
Proof. rewrite !Qp_to_Qc_inj_lt, Qp_to_Qc_inj_le. apply Qcle_lt_trans. Qed.
Lemma Qp_lt_le_trans p q r : p < q → q ≤ r → p < r.
Proof. rewrite !Qp_to_Qc_inj_lt, Qp_to_Qc_inj_le. apply Qclt_le_trans. Qed.

Lemma Qp_le_ngt p q : p ≤ q ↔ ¬q < p.
Proof.
  rewrite !Qp_to_Qc_inj_lt, Qp_to_Qc_inj_le.
  split; auto using Qcle_not_lt, Qcnot_lt_le.
Qed.
Lemma Qp_lt_nge p q : p < q ↔ ¬q ≤ p.
Proof.
  rewrite !Qp_to_Qc_inj_lt, Qp_to_Qc_inj_le.
  split; auto using Qclt_not_le, Qcnot_le_lt.
Qed.

Lemma Qp_add_le_mono_l p q r : p ≤ q ↔ r + p ≤ r + q.
Proof. rewrite !Qp_to_Qc_inj_le. destruct p, q, r; apply Qcplus_le_mono_l. Qed.
Lemma Qp_add_le_mono_r p q r : p ≤ q ↔ p + r ≤ q + r.
Proof. rewrite !(comm_L Qp_add _ r). apply Qp_add_le_mono_l. Qed.
Lemma Qp_add_le_mono q p n m : q ≤ n → p ≤ m → q + p ≤ n + m.
Proof. intros. etrans; [by apply Qp_add_le_mono_l|by apply Qp_add_le_mono_r]. Qed.

Lemma Qp_add_lt_mono_l p q r : p < q ↔ r + p < r + q.
Proof. by rewrite !Qp_lt_nge, <-Qp_add_le_mono_l. Qed.
Lemma Qp_add_lt_mono_r p q r : p < q ↔ p + r < q + r.
Proof. by rewrite !Qp_lt_nge, <-Qp_add_le_mono_r. Qed.
Lemma Qp_add_lt_mono q p n m : q < n → p < m → q + p < n + m.
Proof. intros. etrans; [by apply Qp_add_lt_mono_l|by apply Qp_add_lt_mono_r]. Qed.

Lemma Qp_mul_le_mono_l p q r : p ≤ q ↔ r * p ≤ r * q.
Proof.
  rewrite !Qp_to_Qc_inj_le. destruct p, q, r; by apply Qcmult_le_mono_pos_l.
Qed.
Lemma Qp_mul_le_mono_r p q r : p ≤ q ↔ p * r ≤ q * r.
Proof. rewrite !(comm_L Qp_mul _ r). apply Qp_mul_le_mono_l. Qed.
Lemma Qp_mul_le_mono q p n m : q ≤ n → p ≤ m → q * p ≤ n * m.
Proof. intros. etrans; [by apply Qp_mul_le_mono_l|by apply Qp_mul_le_mono_r]. Qed.

Lemma Qp_mul_lt_mono_l p q r : p < q ↔ r * p < r * q.
Proof.
  rewrite !Qp_to_Qc_inj_lt. destruct p, q, r; by apply Qcmult_lt_mono_pos_l.
Qed.
Lemma Qp_mul_lt_mono_r p q r : p < q ↔ p * r < q * r.
Proof. rewrite !(comm_L Qp_mul _ r). apply Qp_mul_lt_mono_l. Qed.
Lemma Qp_mul_lt_mono q p n m : q < n → p < m → q * p < n * m.
Proof. intros. etrans; [by apply Qp_mul_lt_mono_l|by apply Qp_mul_lt_mono_r]. Qed.

Lemma Qp_lt_add_l p q : p < p + q.
Proof.
  destruct p as [p ?], q as [q ?]. apply Qp_to_Qc_inj_lt; simpl.
  rewrite <- (Qcplus_0_r p) at 1. by rewrite <-Qcplus_lt_mono_l.
Qed.
Lemma Qp_lt_add_r p q : q < p + q.
Proof. rewrite (comm_L Qp_add). apply Qp_lt_add_l. Qed.

Lemma Qp_not_add_le_l p q : ¬(p + q ≤ p).
Proof. apply Qp_lt_nge, Qp_lt_add_l. Qed.
Lemma Qp_not_add_le_r p q : ¬(p + q ≤ q).
Proof. apply Qp_lt_nge, Qp_lt_add_r. Qed.

Lemma Qp_add_id_free q p : q + p ≠ q.
Proof. intro Heq. apply (Qp_not_add_le_l q p). by rewrite Heq. Qed.

Lemma Qp_le_add_l p q : p ≤ p + q.
Proof. apply Qp_lt_le_incl, Qp_lt_add_l. Qed.
Lemma Qp_le_add_r p q : q ≤ p + q.
Proof. apply Qp_lt_le_incl, Qp_lt_add_r. Qed.

Lemma Qp_sub_Some p q r : p - q = Some r ↔ p = q + r.
Proof.
  destruct p as [p Hp], q as [q Hq], r as [r Hr].
  unfold Qp_sub, Qp_add; simpl; rewrite <-Qp_to_Qc_inj_iff; simpl. split.
  - intros; simplify_option_eq. unfold Qcminus.
    by rewrite (Qcplus_comm p), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
  - intros ->. unfold Qcminus.
    rewrite <-Qcplus_assoc, (Qcplus_comm r), Qcplus_assoc.
    rewrite Qcplus_opp_r, Qcplus_0_l. simplify_option_eq; [|done].
    f_equal. by apply Qp_to_Qc_inj_iff.
Qed.
Lemma Qp_lt_sum p q : p < q ↔ ∃ r, q = p + r.
Proof.
  destruct p as [p Hp], q as [q Hq]. rewrite Qp_to_Qc_inj_lt; simpl.
  split.
  - intros Hlt%Qclt_minus_iff. exists (mk_Qp (q - p) Hlt).
    apply Qp_to_Qc_inj_iff; simpl. unfold Qcminus.
    by rewrite (Qcplus_comm q), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
  - intros [[r ?] ?%Qp_to_Qc_inj_iff]; simplify_eq/=.
    rewrite <-(Qcplus_0_r p) at 1. by apply Qcplus_lt_mono_l.
Qed.

Lemma Qp_sub_None p q : p - q = None ↔ p ≤ q.
Proof.
  rewrite Qp_le_ngt, Qp_lt_sum, eq_None_not_Some.
  by setoid_rewrite <-Qp_sub_Some.
Qed.
Lemma Qp_sub_diag p : p - p = None.
Proof. by apply Qp_sub_None. Qed.
Lemma Qp_add_sub p q : (p + q) - q = Some p.
Proof. apply Qp_sub_Some. by rewrite (comm_L Qp_add). Qed.

Lemma Qp_inv_lt_mono p q : p < q ↔ /q < /p.
Proof.
  revert p q. cut (∀ p q, p < q → / q < / p).
  { intros help p q. split; [apply help|]. intros.
    rewrite <-(Qp_inv_involutive p), <-(Qp_inv_involutive q). by apply help. }
  intros p q Hpq. apply (Qp_mul_lt_mono_l _ _ q). rewrite Qp_mul_inv_r.
  apply (Qp_mul_lt_mono_r _ _ p). rewrite <-(assoc_L _), Qp_mul_inv_l.
  by rewrite Qp_mul_1_l, Qp_mul_1_r.
Qed.
Lemma Qp_inv_le_mono p q : p ≤ q ↔ /q ≤ /p.
Proof. by rewrite !Qp_le_ngt, Qp_inv_lt_mono. Qed.

Lemma Qp_div_le_mono_l p q r : q ≤ p ↔ r / p ≤ r / q.
Proof. unfold Qp_div. by rewrite <-Qp_mul_le_mono_l, Qp_inv_le_mono. Qed.
Lemma Qp_div_le_mono_r p q r : p ≤ q ↔ p / r ≤ q / r.
Proof. apply Qp_mul_le_mono_r. Qed.
Lemma Qp_div_lt_mono_l p q r : q < p ↔ r / p < r / q.
Proof. unfold Qp_div. by rewrite <-Qp_mul_lt_mono_l, Qp_inv_lt_mono. Qed.
Lemma Qp_div_lt_mono_r p q r : p < q ↔ p / r < q / r.
Proof. apply Qp_mul_lt_mono_r. Qed.

Lemma Qp_div_lt p q : 1 < q → p / q < p.
Proof. by rewrite (Qp_div_lt_mono_l _ _ p), Qp_div_1. Qed.
Lemma Qp_div_le p q : 1 ≤ q → p / q ≤ p.
Proof. by rewrite (Qp_div_le_mono_l _ _ p), Qp_div_1. Qed.

Lemma Qp_lower_bound q1 q2 : ∃ q q1' q2', q1 = q + q1' ∧ q2 = q + q2'.
Proof.
  revert q1 q2. cut (∀ q1 q2 : Qp, q1 ≤ q2 →
    ∃ q q1' q2', q1 = q + q1' ∧ q2 = q + q2').
  { intros help q1 q2.
    destruct (Qp_lt_ge_cases q2 q1) as [Hlt|Hle]; eauto.
    destruct (help q2 q1) as (q&q1'&q2'&?&?); eauto using Qp_lt_le_incl. }
  intros q1 q2 Hq. exists (q1 / 2)%Qp, (q1 / 2)%Qp.
  assert (q1 / 2 < q2) as [q2' ->]%Qp_lt_sum.
  { eapply Qp_lt_le_trans, Hq. by apply Qp_div_lt. }
  eexists; split; [|done]. by rewrite Qp_div_2.
Qed.

Lemma Qp_lower_bound_lt q1 q2 : ∃ q : Qp, q < q1 ∧ q < q2.
Proof.
  destruct (Qp_lower_bound q1 q2) as (qmin & q1' & q2' & [-> ->]).
  exists qmin. split; eapply Qp_lt_sum; eauto.
Qed.

Lemma Qp_cross_split a b c d :
  a + b = c + d →
  ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d.
Proof.
  intros H. revert a b c d H. cut (∀ a b c d : Qp,
    a < c → a + b = c + d →
    ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d)%Qp.
  { intros help a b c d Habcd.
    destruct (Qp_lt_ge_cases a c) as [?|[?| ->]%Qp_le_lteq].
    - auto.
    - destruct (help c d a b); [done..|]. naive_solver.
    - apply (inj (Qp_add a)) in Habcd as ->.
      destruct (Qp_lower_bound a d) as (q&a'&d'&->&->).
      exists a', q, q, d'. repeat split; done || by rewrite (comm_L Qp_add). }
  intros a b c d [e ->]%Qp_lt_sum. rewrite <-(assoc_L _). intros ->%(inj (Qp_add a)).
  destruct (Qp_lower_bound a d) as (q&a'&d'&->&->).
  eexists a', q, (q + e)%Qp, d'; split_and?; [by rewrite (comm_L Qp_add)|..|done].
  - by rewrite (assoc_L _), (comm_L Qp_add e).
  - by rewrite (assoc_L _), (comm_L Qp_add a').
Qed.

Lemma Qp_bounded_split p r : ∃ q1 q2 : Qp, q1 ≤ r ∧ p = q1 + q2.
Proof.
  destruct (Qp_lt_ge_cases r p) as [[q ->]%Qp_lt_sum|?].
  { by exists r, q. }
  exists (p / 2)%Qp, (p / 2)%Qp; split.
  + trans p; [|done]. by apply Qp_div_le.
  + by rewrite Qp_div_2.
Qed.

Lemma Qp_max_spec q p : (q < p ∧ q `max` p = p) ∨ (p ≤ q ∧ q `max` p = q).
Proof.
  unfold Qp_max.
  destruct (decide (q ≤ p)) as [[?| ->]%Qp_le_lteq|?]; [by auto..|].
  right. split; [|done]. by apply Qp_lt_le_incl, Qp_lt_nge.
Qed.

Lemma Qp_max_spec_le q p : (q ≤ p ∧ q `max` p = p) ∨ (p ≤ q ∧ q `max` p = q).
Proof. destruct (Qp_max_spec q p) as [[?%Qp_lt_le_incl?]|]; [left|right]; done. Qed.

Global Instance Qp_max_assoc : Assoc (=) Qp_max.
Proof.
  intros q p o. unfold Qp_max. destruct (decide (q ≤ p)), (decide (p ≤ o));
    try by rewrite ?decide_True by (by etrans).
  rewrite decide_False by done.
  by rewrite decide_False by (apply Qp_lt_nge; etrans; by apply Qp_lt_nge).
Qed.
Global Instance Qp_max_comm : Comm (=) Qp_max.
Proof.
  intros q p.
  destruct (Qp_max_spec_le q p) as [[?->]|[?->]],
    (Qp_max_spec_le p q) as [[?->]|[?->]]; done || by apply (anti_symm (≤)).
Qed.

Lemma Qp_max_id q : q `max` q = q.
Proof. by destruct (Qp_max_spec q q) as [[_->]|[_->]]. Qed.

Lemma Qp_le_max_l q p : q ≤ q `max` p.
Proof. unfold Qp_max. by destruct (decide (q ≤ p)). Qed.
Lemma Qp_le_max_r q p : p ≤ q `max` p.
Proof. rewrite (comm_L Qp_max q). apply Qp_le_max_l. Qed.

Lemma Qp_max_add q p : q `max` p ≤ q + p.
Proof.
  unfold Qp_max.
  destruct (decide (q ≤ p)); [apply Qp_le_add_r|apply Qp_le_add_l].
Qed.

Lemma Qp_max_lub_l q p o : q `max` p ≤ o → q ≤ o.
Proof. unfold Qp_max. destruct (decide (q ≤ p)); [by etrans|done]. Qed.
Lemma Qp_max_lub_r q p o : q `max` p ≤ o → p ≤ o.
Proof. rewrite (comm _ q). apply Qp_max_lub_l. Qed.

Lemma Qp_min_spec q p : (q < p ∧ q `min` p = q) ∨ (p ≤ q ∧ q `min` p = p).
Proof.
  unfold Qp_min.
  destruct (decide (q ≤ p)) as [[?| ->]%Qp_le_lteq|?]; [by auto..|].
  right. split; [|done]. by apply Qp_lt_le_incl, Qp_lt_nge.
Qed.

Lemma Qp_min_spec_le q p : (q ≤ p ∧ q `min` p = q) ∨ (p ≤ q ∧ q `min` p = p).
Proof. destruct (Qp_min_spec q p) as [[?%Qp_lt_le_incl ?]|]; [left|right]; done. Qed.

Global Instance Qp_min_assoc : Assoc (=) Qp_min.
Proof.
  intros q p o. unfold Qp_min.
  destruct (decide (q ≤ p)), (decide (p ≤ o)); eauto using decide_False.
  - by rewrite !decide_True by (by etrans).
  - by rewrite decide_False by (apply Qp_lt_nge; etrans; by apply Qp_lt_nge).
Qed.
Global Instance Qp_min_comm : Comm (=) Qp_min.
Proof.
  intros q p.
  destruct (Qp_min_spec_le q p) as [[?->]|[?->]],
    (Qp_min_spec_le p q) as [[? ->]|[? ->]]; done || by apply (anti_symm (≤)).
Qed.

Lemma Qp_min_id q : q `min` q = q.
Proof. by destruct (Qp_min_spec q q) as [[_->]|[_->]]. Qed.
Lemma Qp_le_min_r q p : q `min` p ≤ p.
Proof. by destruct (Qp_min_spec_le q p) as [[?->]|[?->]]. Qed.

Lemma Qp_le_min_l p q : p `min` q ≤ p.
Proof. rewrite (comm_L Qp_min p). apply Qp_le_min_r. Qed.

Lemma Qp_min_l_iff q p : q `min` p = q ↔ q ≤ p.
Proof.
  destruct (Qp_min_spec_le q p) as [[?->]|[?->]]; [done|].
  split; [by intros ->|]. intros. by apply (anti_symm (≤)).
Qed.
Lemma Qp_min_r_iff q p : q `min` p = p ↔ p ≤ q.
Proof. rewrite (comm_L Qp_min q). apply Qp_min_l_iff. Qed.

Lemma pos_to_Qp_1 : pos_to_Qp 1 = 1.
Proof. compute_done. Qed.
Lemma pos_to_Qp_inj n m : pos_to_Qp n = pos_to_Qp m → n = m.
Proof. by injection 1. Qed.
Lemma pos_to_Qp_inj_iff n m : pos_to_Qp n = pos_to_Qp m ↔ n = m.
Proof. split; [apply pos_to_Qp_inj|by intros ->]. Qed.
Lemma pos_to_Qp_inj_le n m : (n ≤ m)%positive ↔ pos_to_Qp n ≤ pos_to_Qp m.
Proof. rewrite Qp_to_Qc_inj_le; simpl. by rewrite <-Z2Qc_inj_le. Qed.
Lemma pos_to_Qp_inj_lt n m : (n < m)%positive ↔ pos_to_Qp n < pos_to_Qp m.
Proof. by rewrite Pos.lt_nle, Qp_lt_nge, <-pos_to_Qp_inj_le. Qed.
Lemma pos_to_Qp_add x y : pos_to_Qp x + pos_to_Qp y = pos_to_Qp (x + y).
Proof. apply Qp_to_Qc_inj_iff; simpl. by rewrite Pos2Z.inj_add, Z2Qc_inj_add. Qed.
Lemma pos_to_Qp_mul x y : pos_to_Qp x * pos_to_Qp y = pos_to_Qp (x * y).
Proof. apply Qp_to_Qc_inj_iff; simpl. by rewrite Pos2Z.inj_mul, Z2Qc_inj_mul. Qed.

Local Close Scope Qp_scope.

(** * Helper for working with accessing lists with wrap-around
    See also [rotate] and [rotate_take] in [list.v] *)
(** [rotate_nat_add base offset len] computes [(base + offset) `mod`
len]. This is useful in combination with the [rotate] function on
lists, since the index [i] of [rotate n l] corresponds to the index
[rotate_nat_add n i (length i)] of the original list. The definition
uses [Z] for consistency with [rotate_nat_sub]. **)
Definition rotate_nat_add (base offset len : nat) : nat :=
  Z.to_nat ((Z.of_nat base + Z.of_nat offset) `mod` Z.of_nat len)%Z.
(** [rotate_nat_sub base offset len] is the inverse of [rotate_nat_add
base offset len]. The definition needs to use modulo on [Z] instead of
on nat since otherwise we need the sidecondition [base < len] on
[rotate_nat_sub_add]. **)
Definition rotate_nat_sub (base offset len : nat) : nat :=
  Z.to_nat ((Z.of_nat len + Z.of_nat offset - Z.of_nat base) `mod` Z.of_nat len)%Z.

Lemma rotate_nat_add_add_mod base offset len:
  rotate_nat_add base offset len =
  rotate_nat_add (base `mod` len) offset len.
Proof. unfold rotate_nat_add. by rewrite Nat2Z_inj_mod, Zplus_mod_idemp_l. Qed.

Lemma rotate_nat_add_alt base offset len:
  base < len → offset < len →
  rotate_nat_add base offset len =
  if decide (base + offset < len) then base + offset else base + offset - len.
Proof.
  unfold rotate_nat_add. intros ??. case_decide.
  - rewrite Z.mod_small by lia. by rewrite <-Nat2Z.inj_add, Nat2Z.id.
  - rewrite (Zmod_in_range 1) by lia.
    by rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-Nat2Z.inj_sub,Nat2Z.id by lia.
Qed.
Lemma rotate_nat_sub_alt base offset len:
  base < len → offset < len →
  rotate_nat_sub base offset len =
  if decide (offset < base) then len + offset - base else offset - base.
Proof.
  unfold rotate_nat_sub. intros ??. case_decide.
  - rewrite Z.mod_small by lia.
    by rewrite <-Nat2Z.inj_add, <-Nat2Z.inj_sub, Nat2Z.id by lia.
  - rewrite (Zmod_in_range 1) by lia.
    rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_add_0 base len :
  base < len → rotate_nat_add base 0 len = base.
Proof.
  intros ?. unfold rotate_nat_add.
  rewrite Z.mod_small by lia. by rewrite Z.add_0_r, Nat2Z.id.
Qed.
Lemma rotate_nat_sub_0 base len :
  base < len → rotate_nat_sub base base len = 0.
Proof. intros ?. rewrite rotate_nat_sub_alt by done. case_decide; lia. Qed.

Lemma rotate_nat_add_lt base offset len :
  0 < len → rotate_nat_add base offset len < len.
Proof.
  unfold rotate_nat_add. intros ?.
  pose proof (Nat.mod_upper_bound (base + offset) len).
  rewrite Z2Nat_inj_mod, Z2Nat.inj_add, !Nat2Z.id; lia.
Qed.
Lemma rotate_nat_sub_lt base offset len :
  0 < len → rotate_nat_sub base offset len < len.
Proof.
  unfold rotate_nat_sub. intros ?.
  pose proof (Z_mod_lt (Z.of_nat len + Z.of_nat offset - Z.of_nat base) (Z.of_nat len)).
  apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia.
Qed.

Lemma rotate_nat_add_sub base len offset:
  offset < len →
  rotate_nat_add base (rotate_nat_sub base offset len) len = offset.
Proof.
  intros ?. unfold rotate_nat_add, rotate_nat_sub.
  rewrite Z2Nat.id by (apply Z_mod_pos; lia). rewrite Zplus_mod_idemp_r.
  replace (Z.of_nat base + (Z.of_nat len + Z.of_nat offset - Z.of_nat base))%Z
    with (Z.of_nat len + Z.of_nat offset)%Z by lia.
  rewrite (Zmod_in_range 1) by lia.
  rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_sub_add base len offset:
  offset < len →
  rotate_nat_sub base (rotate_nat_add base offset len) len = offset.
Proof.
  intros ?. unfold rotate_nat_add, rotate_nat_sub.
  rewrite Z2Nat.id by (apply Z_mod_pos; lia).
  assert (∀ n, (Z.of_nat len + n - Z.of_nat base) = ((Z.of_nat len - Z.of_nat base) + n))%Z
    as -> by naive_solver lia.
  rewrite Zplus_mod_idemp_r.
  replace (Z.of_nat len - Z.of_nat base + (Z.of_nat base + Z.of_nat offset))%Z with
    (Z.of_nat len + Z.of_nat offset)%Z by lia.
  rewrite (Zmod_in_range 1) by lia.
  rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_add_add base offset len n:
  0 < len →
  rotate_nat_add base (offset + n) len =
  (rotate_nat_add base offset len + n) `mod` len.
Proof.
  intros ?. unfold rotate_nat_add.
  rewrite !Z2Nat_inj_mod, !Z2Nat.inj_add, !Nat2Z.id by lia.
  by rewrite plus_assoc, Nat.add_mod_idemp_l by lia.
Qed.

Lemma rotate_nat_add_S base offset len:
  0 < len →
  rotate_nat_add base (S offset) len =
  S (rotate_nat_add base offset len) `mod` len.
Proof. intros ?. by rewrite <-Nat.add_1_r, rotate_nat_add_add, Nat.add_1_r. Qed.
