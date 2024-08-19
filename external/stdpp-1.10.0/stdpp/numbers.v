(** This file provides various tweaks and extensions to Coq's theory of numbers
(natural numbers [nat] and [N], positive numbers [positive], integers [Z], and
rationals [Qc]). In addition, this file defines a new type of positive rational
numbers [Qp], which is used extensively in Iris to represent fractional
permissions.

The organization of this file follows mostly Coq's standard library.

- We put all results in modules. For example, the module [Nat] collects the
  results for type [nat]. Since the Coq stdlib already defines a module [Nat],
  our module [Nat] exports Coq's module so that our module [Nat] contains the
  union of the results from the Coq stdlib and std++.
- We follow the naming convention of Coq's "numbers" library to prefer
  [succ]/[add]/[sub]/[mul] over [S]/[plus]/[minus]/[mult].
- One typically does not [Import] modules such as [Nat], and refers to the
  results using [Nat.lem]. As a consequence, all [Hint]s [Instance]s in the modules in
  this file are [Global] and not [Export]. Other things like [Arguments] are outside
  the modules, since for them [Global] works like [Export].

The results for [Qc] are not yet in a module. This is in part because they
still follow the old/non-module style in Coq's standard library. See also
https://gitlab.mpi-sws.org/iris/stdpp/-/issues/147. *)

From Coq Require Export EqdepFacts PArith NArith ZArith.
From Coq Require Import QArith Qcanon.
From stdpp Require Export base decidable option.
From stdpp Require Import well_founded.
From stdpp Require Import options.
Local Open Scope nat_scope.

Global Instance comparison_eq_dec : EqDecision comparison.
Proof. solve_decision. Defined.

(** * Notations and properties of [nat] *)
Global Arguments Nat.sub !_ !_ / : assert.
Global Arguments Nat.max : simpl nomatch.

(** We do not make [Nat.lt] since it is an alias for [lt], which contains the
actual definition that we want to make opaque. *)
Global Typeclasses Opaque lt.

Reserved Notation "x ≤ y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y ≤ z ≤ z'"
  (at level 70, y at next level, z at next level).

Infix "≤" := le : nat_scope.
(** We do *not* add notation for [≥] mapping to [ge], and we do also not use the
[>] notation from the Coq standard library. Using such notations leads to
annoying problems: if you have [x < y] in the context and need [y > x] for some
lemma, [assumption] won't work because [x < y] and [y > x] are not
definitionally equal. It is just generally frustrating to deal with this
mismatch, and much preferable to state logically equivalent things in syntactically
equal ways.

As an alternative, we could define [>] and [≥] as [parsing only] notation that
maps to [<] and [≤], respectively (similar to math-comp). This would change the
notation for [<] from the Coq standard library to something that is not
definitionally equal, so we avoid that as well.

This concern applies to all number types: [nat], [N], [Z], [positive], [Qc] and
[Qp]. *)
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

(** TODO: Consider removing these notations to avoid populting the global
scope? *)
Notation lcm := Nat.lcm.
Notation divide := Nat.divide.
Notation "( x | y )" := (divide x y) : nat_scope.

Module Nat.
  Export PeanoNat.Nat.

  Global Instance add_assoc' : Assoc (=) Nat.add := Nat.add_assoc.
  Global Instance add_comm' : Comm (=) Nat.add := Nat.add_comm.
  Global Instance add_left_id : LeftId (=) 0 Nat.add := Nat.add_0_l.
  Global Instance add_right_id : RightId (=) 0 Nat.add := Nat.add_0_r.

  Global Instance sub_right_id : RightId (=) 0 Nat.sub := Nat.sub_0_r.

  Global Instance mul_assoc' : Assoc (=) Nat.mul := Nat.mul_assoc.
  Global Instance mul_comm' : Comm (=) Nat.mul := Nat.mul_comm.
  Global Instance mul_left_id : LeftId (=) 1 Nat.mul := Nat.mul_1_l.
  Global Instance mul_right_id : RightId (=) 1 Nat.mul := Nat.mul_1_r.
  Global Instance mul_left_absorb : LeftAbsorb (=) 0 Nat.mul := Nat.mul_0_l.
  Global Instance mul_right_absorb : RightAbsorb (=) 0 Nat.mul := Nat.mul_0_r.

  Global Instance div_right_id : RightId (=) 1 Nat.div := Nat.div_1_r.

  Global Instance eq_dec: EqDecision nat := eq_nat_dec.
  Global Instance le_dec: RelDecision le := le_dec.
  Global Instance lt_dec: RelDecision lt := lt_dec.
  Global Instance inhabited: Inhabited nat := populate 0.

  Global Instance succ_inj: Inj (=) (=) Nat.succ.
  Proof. by injection 1. Qed.

  Global Instance le_po: PartialOrder (≤).
  Proof. repeat split; repeat intro; auto with lia. Qed.
  Global Instance le_total: Total (≤).
  Proof. repeat intro; lia. Qed.

  Global Instance le_pi: ∀ x y : nat, ProofIrrel (x ≤ y).
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
  Global Instance lt_pi: ∀ x y : nat, ProofIrrel (x < y).
  Proof. unfold Peano.lt. apply _. Qed.

  (** Given a measure/size [f : B → nat], you can do induction on the size of
  [b : B] using [induction (lt_wf_0_projected f b)]. *)
  Lemma lt_wf_0_projected {B} (f : B → nat) : well_founded (λ x y, f x < f y).
  Proof. by apply (wf_projected (<) f), lt_wf_0. Qed.

  Lemma le_sum (x y : nat) : x ≤ y ↔ ∃ z, y = x + z.
  Proof. split; [exists (y - x); lia | intros [z ->]; lia]. Qed.

  (** This is similar to but slightly different than Coq's
      [add_sub : ∀ n m : nat, n + m - m = n]. *)
  Lemma add_sub' n m : n + m - n = m.
  Proof. lia. Qed.
  Lemma le_add_sub n m : n ≤ m → m = n + (m - n).
  Proof. lia. Qed.

  (** Cancellation for multiplication. Coq's stdlib has these lemmas for [Z],
  but those for [nat] are missing. We use the naming scheme of Coq's stdlib. *)
  Lemma mul_reg_l n m p : p ≠ 0 → p * n = p * m → n = m.
  Proof.
    pose proof (Z.mul_reg_l (Z.of_nat n) (Z.of_nat m) (Z.of_nat p)). lia.
  Qed.
  Lemma mul_reg_r n m p : p ≠ 0 → n * p = m * p → n = m.
  Proof. rewrite <-!(Nat.mul_comm p). apply mul_reg_l. Qed.

  Lemma lt_succ_succ n : n < S (S n).
  Proof. auto with arith. Qed.
  Lemma mul_split_l n x1 x2 y1 y2 :
    x2 < n → y2 < n → x1 * n + x2 = y1 * n + y2 → x1 = y1 ∧ x2 = y2.
  Proof.
    intros Hx2 Hy2 E. cut (x1 = y1); [intros; subst;lia |].
    revert y1 E. induction x1; simpl; intros [|?]; simpl; auto with lia.
  Qed.
  Lemma mul_split_r n x1 x2 y1 y2 :
    x1 < n → y1 < n → x1 + x2 * n = y1 + y2 * n → x1 = y1 ∧ x2 = y2.
  Proof. intros. destruct (mul_split_l n x2 x1 y2 y1); auto with lia. Qed.

  Global Instance divide_dec : RelDecision Nat.divide.
  Proof.
    refine (λ x y, cast_if (decide (lcm x y = y))); by rewrite Nat.divide_lcm_iff.
  Defined.
  Global Instance divide_po : PartialOrder divide.
  Proof.
    repeat split; try apply _. intros ??. apply Nat.divide_antisym; lia.
  Qed.
  Global Hint Extern 0 (_ | _) => reflexivity : core.

  Lemma divide_ne_0 x y : (x | y) → y ≠ 0 → x ≠ 0.
  Proof. intros Hxy Hy ->. by apply Hy, Nat.divide_0_l. Qed.

  Lemma iter_succ {A} n (f: A → A) x : Nat.iter (S n) f x = f (Nat.iter n f x).
  Proof. done. Qed.
  Lemma iter_succ_r {A} n (f: A → A) x : Nat.iter (S n) f x = Nat.iter n f (f x).
  Proof. induction n; by f_equal/=. Qed.
  Lemma iter_add {A} n1 n2 (f : A → A) x :
    Nat.iter (n1 + n2) f x = Nat.iter n1 f (Nat.iter n2 f x).
  Proof. induction n1; by f_equal/=. Qed.
  Lemma iter_mul {A} n1 n2 (f : A → A) x :
    Nat.iter (n1 * n2) f x = Nat.iter n1 (Nat.iter n2 f) x.
  Proof.
    intros. induction n1 as [|n1 IHn1]; [done|].
    simpl. by rewrite iter_add, IHn1.
  Qed.

  Lemma iter_ind {A} (P : A → Prop) f x k :
    P x → (∀ y, P y → P (f y)) → P (Nat.iter k f x).
  Proof. induction k; simpl; auto. Qed.

  (** FIXME: Coq 8.17 deprecated some lemmas in https://github.com/coq/coq/pull/16203.
  We cannot use the intended replacements since we support Coq 8.16. We also do
  not want to disable [deprecated-syntactic-definition] everywhere, so instead
  we provide non-deprecated duplicates of those deprecated lemmas that we need
  in std++ and Iris. *)
  Local Set Warnings "-deprecated-syntactic-definition".
  Lemma add_mod_idemp_l a b n : n ≠ 0 → (a mod n + b) mod n = (a + b) mod n.
  Proof. auto using add_mod_idemp_l. Qed.
  Lemma div_lt_upper_bound a b q : b ≠ 0 → a < b * q → a / b < q.
  Proof. auto using div_lt_upper_bound. Qed.
End Nat.

(** * Notations and properties of [positive] *)
Local Open Scope positive_scope.

Global Typeclasses Opaque Pos.le.
Global Typeclasses Opaque Pos.lt.

Infix "≤" := Pos.le : positive_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : positive_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : positive_scope.
Notation "(≤)" := Pos.le (only parsing) : positive_scope.
Notation "(<)" := Pos.lt (only parsing) : positive_scope.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.
Infix "`max`" := Pos.max : positive_scope.
Infix "`min`" := Pos.min : positive_scope.

Global Arguments Pos.pred : simpl never.
Global Arguments Pos.succ : simpl never.
Global Arguments Pos.of_nat : simpl never.
Global Arguments Pos.to_nat : simpl never.
Global Arguments Pos.mul : simpl never.
Global Arguments Pos.add : simpl never.
Global Arguments Pos.sub : simpl never.
Global Arguments Pos.pow : simpl never.
Global Arguments Pos.shiftl : simpl never.
Global Arguments Pos.shiftr : simpl never.
Global Arguments Pos.gcd : simpl never.
Global Arguments Pos.min : simpl never.
Global Arguments Pos.max : simpl never.
Global Arguments Pos.lor : simpl never.
Global Arguments Pos.land : simpl never.
Global Arguments Pos.lxor : simpl never.
Global Arguments Pos.square : simpl never.

Module Pos.
  Export BinPos.Pos.

  Global Instance add_assoc' : Assoc (=) Pos.add := Pos.add_assoc.
  Global Instance add_comm' : Comm (=) Pos.add := Pos.add_comm.

  Global Instance mul_assoc' : Assoc (=) Pos.mul := Pos.mul_assoc.
  Global Instance mul_comm' : Comm (=) Pos.mul := Pos.mul_comm.
  Global Instance mul_left_id : LeftId (=) 1 Pos.mul := Pos.mul_1_l.
  Global Instance mul_right_id : RightId (=) 1 Pos.mul := Pos.mul_1_r.

  Global Instance eq_dec: EqDecision positive := Pos.eq_dec.
  Global Instance le_dec: RelDecision Pos.le.
  Proof. refine (λ x y, decide ((x ?= y) ≠ Gt)). Defined.
  Global Instance lt_dec: RelDecision Pos.lt.
  Proof. refine (λ x y, decide ((x ?= y) = Lt)). Defined.
  Global Instance le_total: Total Pos.le.
  Proof. repeat intro; lia. Qed.

  Global Instance inhabited: Inhabited positive := populate 1.

  Global Instance maybe_xO : Maybe xO := λ p, match p with p~0 => Some p | _ => None end.
  Global Instance maybe_xI : Maybe xI := λ p, match p with p~1 => Some p | _ => None end.
  Global Instance xO_inj : Inj (=) (=) (~0).
  Proof. by injection 1. Qed.
  Global Instance xI_inj : Inj (=) (=) (~1).
  Proof. by injection 1. Qed.

  (** Since [positive] represents lists of bits, we define list operations
  on it. These operations are in reverse, as positives are treated as snoc
  lists instead of cons lists. *)
  Fixpoint app (p1 p2 : positive) : positive :=
    match p2 with
    | 1 => p1
    | p2~0 => (app p1 p2)~0
    | p2~1 => (app p1 p2)~1
    end.

  Module Import app_notations.
    Infix "++" := app : positive_scope.
    Notation "(++)" := app (only parsing) : positive_scope.
    Notation "( p ++.)" := (app p) (only parsing) : positive_scope.
    Notation "(.++ q )" := (λ p, app p q) (only parsing) : positive_scope.
  End app_notations.

  Fixpoint reverse_go (p1 p2 : positive) : positive :=
    match p2 with
    | 1 => p1
    | p2~0 => reverse_go (p1~0) p2
    | p2~1 => reverse_go (p1~1) p2
    end.
  Definition reverse : positive → positive := reverse_go 1.

  Global Instance app_1_l : LeftId (=) 1 (++).
  Proof. intros p. by induction p; intros; f_equal/=. Qed.
  Global Instance app_1_r : RightId (=) 1 (++).
  Proof. done. Qed.
  Global Instance app_assoc : Assoc (=) (++).
  Proof. intros ?? p. by induction p; intros; f_equal/=. Qed.
  Global Instance app_inj p : Inj (=) (=) (.++ p).
  Proof. intros ???. induction p; simplify_eq; auto. Qed.

  Lemma reverse_go_app p1 p2 p3 :
    reverse_go p1 (p2 ++ p3) = reverse_go p1 p3 ++ reverse_go 1 p2.
  Proof.
    revert p3 p1 p2.
    cut (∀ p1 p2 p3, reverse_go (p2 ++ p3) p1 = p2 ++ reverse_go p3 p1).
    { by intros go p3; induction p3; intros p1 p2; simpl; auto; rewrite <-?go. }
    intros p1; induction p1 as [p1 IH|p1 IH|]; intros p2 p3; simpl; auto.
    - apply (IH _ (_~1)).
    - apply (IH _ (_~0)).
  Qed.
  Lemma reverse_app p1 p2 : reverse (p1 ++ p2) = reverse p2 ++ reverse p1.
  Proof. unfold reverse. by rewrite reverse_go_app. Qed.
  Lemma reverse_xO p : reverse (p~0) = (1~0) ++ reverse p.
  Proof. apply (reverse_app p (1~0)). Qed.
  Lemma reverse_xI p : reverse (p~1) = (1~1) ++ reverse p.
  Proof. apply (reverse_app p (1~1)). Qed.

  Lemma reverse_involutive p : reverse (reverse p) = p.
  Proof.
    induction p as [p IH|p IH|]; simpl.
    - by rewrite reverse_xI, reverse_app, IH.
    - by rewrite reverse_xO, reverse_app, IH.
    - reflexivity.
  Qed.

  Global Instance reverse_inj : Inj (=) (=) reverse.
  Proof.
    intros p q eq.
    rewrite <-(reverse_involutive p).
    rewrite <-(reverse_involutive q).
    by rewrite eq.
  Qed.

  Fixpoint length (p : positive) : nat :=
    match p with 1 => 0%nat | p~0 | p~1 => S (length p) end.
  Lemma app_length p1 p2 : length (p1 ++ p2) = (length p2 + length p1)%nat.
  Proof. by induction p2; f_equal/=. Qed.

  Lemma lt_sum (x y : positive) : x < y ↔ ∃ z, y = x + z.
  Proof.
    split.
    - exists (y - x)%positive. symmetry. apply Pplus_minus. lia.
    - intros [z ->]. lia.
  Qed.

  (** Duplicate the bits of a positive, i.e. 1~0~1 -> 1~0~0~1~1 and
      1~1~0~0 -> 1~1~1~0~0~0~0 *)
  Fixpoint dup (p : positive) : positive :=
    match p with
    | 1 => 1
    | p'~0 => (dup p')~0~0
    | p'~1 => (dup p')~1~1
    end.

  Lemma dup_app p q :
    dup (p ++ q) = dup p ++ dup q.
  Proof.
    revert p.
    induction q as [p IH|p IH|]; intros q; simpl.
    - by rewrite IH.
    - by rewrite IH.
    - reflexivity.
  Qed.

  Lemma dup_suffix_eq p q s1 s2 :
    s1~1~0 ++ dup p = s2~1~0 ++ dup q → p = q.
  Proof.
    revert q.
    induction p as [p IH|p IH|]; intros [q|q|] eq; simplify_eq/=.
    - by rewrite (IH q).
    - by rewrite (IH q).
    - reflexivity.
  Qed.

  Global Instance dup_inj : Inj (=) (=) dup.
  Proof.
    intros p q eq.
    apply (dup_suffix_eq _ _ 1 1).
    by rewrite eq.
  Qed.

  Lemma reverse_dup p :
    reverse (dup p) = dup (reverse p).
  Proof.
    induction p as [p IH|p IH|]; simpl.
    - rewrite 3!reverse_xI.
      rewrite (assoc_L (++)).
      rewrite IH.
      rewrite dup_app.
      reflexivity.
    - rewrite 3!reverse_xO.
      rewrite (assoc_L (++)).
      rewrite IH.
      rewrite dup_app.
      reflexivity.
    - reflexivity.
  Qed.
End Pos.

Export Pos.app_notations.

Local Close Scope positive_scope.

(** * Notations and properties of [N] *)
Local Open Scope N_scope.

Global Typeclasses Opaque N.le.
Global Typeclasses Opaque N.lt.

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

Global Arguments N.pred : simpl never.
Global Arguments N.succ : simpl never.
Global Arguments N.of_nat : simpl never.
Global Arguments N.to_nat : simpl never.
Global Arguments N.mul : simpl never.
Global Arguments N.add : simpl never.
Global Arguments N.sub : simpl never.
Global Arguments N.pow : simpl never.
Global Arguments N.div : simpl never.
Global Arguments N.modulo : simpl never.
Global Arguments N.shiftl : simpl never.
Global Arguments N.shiftr : simpl never.
Global Arguments N.gcd : simpl never.
Global Arguments N.lcm : simpl never.
Global Arguments N.min : simpl never.
Global Arguments N.max : simpl never.
Global Arguments N.lor : simpl never.
Global Arguments N.land : simpl never.
Global Arguments N.lxor : simpl never.
Global Arguments N.lnot : simpl never.
Global Arguments N.square : simpl never.

Global Hint Extern 0 (_ ≤ _)%N => reflexivity : core.

Module N.
  Export BinNat.N.

  Global Instance add_assoc' : Assoc (=) N.add := N.add_assoc.
  Global Instance add_comm' : Comm (=) N.add := N.add_comm.
  Global Instance add_left_id : LeftId (=) 0 N.add := N.add_0_l.
  Global Instance add_right_id : RightId (=) 0 N.add := N.add_0_r.

  Global Instance sub_right_id : RightId (=) 0 N.sub := N.sub_0_r.

  Global Instance mul_assoc' : Assoc (=) N.mul := N.mul_assoc.
  Global Instance mul_comm' : Comm (=) N.mul := N.mul_comm.
  Global Instance mul_left_id : LeftId (=) 1 N.mul := N.mul_1_l.
  Global Instance mul_right_id : RightId (=) 1 N.mul := N.mul_1_r.
  Global Instance mul_left_absorb : LeftAbsorb (=) 0 N.mul := N.mul_0_l.
  Global Instance mul_right_absorb : RightAbsorb (=) 0 N.mul := N.mul_0_r.

  Global Instance div_right_id : RightId (=) 1 N.div := N.div_1_r.

  Global Instance pos_inj : Inj (=) (=) N.pos.
  Proof. by injection 1. Qed.

  Global Instance eq_dec : EqDecision N := N.eq_dec.
  Global Program Instance le_dec : RelDecision N.le := λ x y,
    match N.compare x y with Gt => right _ | _ => left _ end.
  Solve Obligations with naive_solver.
  Global Program Instance lt_dec : RelDecision N.lt := λ x y,
    match N.compare x y with Lt => left _ | _ => right _ end.
  Solve Obligations with naive_solver.
  Global Instance inhabited : Inhabited N := populate 1%N.
  Global Instance lt_pi x y : ProofIrrel (x < y)%N.
  Proof. unfold N.lt. apply _. Qed.

  Global Instance le_po : PartialOrder (≤)%N.
  Proof.
    repeat split; red; [apply N.le_refl | apply N.le_trans | apply N.le_antisymm].
  Qed.
  Global Instance le_total : Total (≤)%N.
  Proof. repeat intro; lia. Qed.

  Lemma lt_wf_0_projected {B} (f : B → N) : well_founded (λ x y, f x < f y).
  Proof. by apply (wf_projected (<) f), lt_wf_0. Qed.

  (** FIXME: Coq 8.17 deprecated some lemmas in https://github.com/coq/coq/pull/16203.
  We cannot use the intended replacements since we support Coq 8.16. We also do
  not want to disable [deprecated-syntactic-definition] everywhere, so instead
  we provide non-deprecated duplicates of those deprecated lemmas that we need
  in std++ and Iris. *)
  Local Set Warnings "-deprecated-syntactic-definition".
  Lemma add_mod_idemp_l a b n : n ≠ 0 → (a mod n + b) mod n = (a + b) mod n.
  Proof. auto using add_mod_idemp_l. Qed.
  Lemma div_lt_upper_bound a b q : b ≠ 0 → a < b * q → a / b < q.
  Proof. auto using div_lt_upper_bound. Qed.
End N.

Local Close Scope N_scope.

(** * Notations and properties of [Z] *)
Local Open Scope Z_scope.

Global Typeclasses Opaque Z.le.
Global Typeclasses Opaque Z.lt.

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

Module Z.
  Export BinInt.Z.

  Global Instance add_assoc' : Assoc (=) Z.add := Z.add_assoc.
  Global Instance add_comm' : Comm (=) Z.add := Z.add_comm.
  Global Instance add_left_id : LeftId (=) 0 Z.add := Z.add_0_l.
  Global Instance add_right_id : RightId (=) 0 Z.add := Z.add_0_r.

  Global Instance sub_right_id : RightId (=) 0 Z.sub := Z.sub_0_r.

  Global Instance mul_assoc' : Assoc (=) Z.mul := Z.mul_assoc.
  Global Instance mul_comm' : Comm (=) Z.mul := Z.mul_comm.
  Global Instance mul_left_id : LeftId (=) 1 Z.mul := Z.mul_1_l.
  Global Instance mul_right_id : RightId (=) 1 Z.mul := Z.mul_1_r.
  Global Instance mul_left_absorb : LeftAbsorb (=) 0 Z.mul := Z.mul_0_l.
  Global Instance mul_right_absorb : RightAbsorb (=) 0 Z.mul := Z.mul_0_r.

  Global Instance div_right_id : RightId (=) 1 Z.div := Z.div_1_r.

  Global Instance pos_inj : Inj (=) (=) Z.pos.
  Proof. by injection 1. Qed.
  Global Instance neg_inj : Inj (=) (=) Z.neg.
  Proof. by injection 1. Qed.

  Global Instance eq_dec: EqDecision Z := Z.eq_dec.
  Global Instance le_dec: RelDecision Z.le := Z_le_dec.
  Global Instance lt_dec: RelDecision Z.lt := Z_lt_dec.
  Global Instance ge_dec: RelDecision Z.ge := Z_ge_dec.
  Global Instance gt_dec: RelDecision Z.gt := Z_gt_dec.
  Global Instance inhabited: Inhabited Z := populate 1.
  Global Instance lt_pi x y : ProofIrrel (x < y).
  Proof. unfold Z.lt. apply _. Qed.

  Global Instance le_po : PartialOrder (≤).
  Proof.
    repeat split; red; [apply Z.le_refl | apply Z.le_trans | apply Z.le_antisymm].
  Qed.
  Global Instance le_total: Total Z.le.
  Proof. repeat intro; lia. Qed.

  Lemma lt_wf_projected {B} (f : B → Z) z : well_founded (λ x y, z ≤ f x < f y).
  Proof. by apply (wf_projected (λ x y, z ≤ x < y) f), lt_wf. Qed.

  Lemma pow_pred_r n m : 0 < m → n * n ^ (Z.pred m) = n ^ m.
  Proof.
    intros. rewrite <-Z.pow_succ_r, Z.succ_pred; [done|]. by apply Z.lt_le_pred.
  Qed.
  Lemma quot_range_nonneg k x y : 0 ≤ x < k → 0 < y → 0 ≤ x `quot` y < k.
  Proof.
    intros [??] ?.
    destruct (decide (y = 1)); subst; [rewrite Z.quot_1_r; auto |].
    destruct (decide (x = 0)); subst; [rewrite Z.quot_0_l; auto with lia |].
    split; [apply Z.quot_pos; lia|].
    trans x; auto. apply Z.quot_lt; lia.
  Qed.

  Lemma mod_pos x y : 0 < y → 0 ≤ x `mod` y.
  Proof. apply Z.mod_pos_bound. Qed.

  Global Hint Resolve Z.lt_le_incl : zpos.
  Global Hint Resolve Z.add_nonneg_pos Z.add_pos_nonneg Z.add_nonneg_nonneg : zpos.
  Global Hint Resolve Z.mul_nonneg_nonneg Z.mul_pos_pos : zpos.
  Global Hint Resolve Z.pow_pos_nonneg Z.pow_nonneg: zpos.
  Global Hint Resolve Z.mod_pos Z.div_pos : zpos.
  Global Hint Extern 1000 => lia : zpos.

  Lemma succ_pred_induction y (P : Z → Prop) :
    P y →
    (∀ x, y ≤ x → P x → P (Z.succ x)) →
    (∀ x, x ≤ y → P x → P (Z.pred x)) →
    (∀ x, P x).
  Proof. intros H0 HS HP. by apply (Z.order_induction' _ _ y). Qed.
  Lemma mod_in_range q a c :
    q * c ≤ a < (q + 1) * c →
    a `mod` c = a - q * c.
  Proof. intros ?. symmetry. apply Z.mod_unique_pos with q; lia. Qed.

  Lemma ones_spec n m:
    0 ≤ m → 0 ≤ n →
    Z.testbit (Z.ones n) m = bool_decide (m < n).
  Proof.
    intros. case_bool_decide.
    - by rewrite Z.ones_spec_low by lia.
    - by rewrite Z.ones_spec_high by lia.
  Qed.

  Lemma bounded_iff_bits_nonneg k n :
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
  Lemma bounded_iff_bits_nonneg' k n :
    0 ≤ k → 0 ≤ n →
    0 ≤ n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = false.
  Proof. intros ??. rewrite <-bounded_iff_bits_nonneg; lia. Qed.

  Lemma bounded_iff_bits k n :
    0 ≤ k →
    -2^k ≤ n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = bool_decide (n < 0).
  Proof.
    intros Hk.
    case_bool_decide; [ | rewrite <-bounded_iff_bits_nonneg; lia].
    assert(n = - Z.abs n)%Z as -> by lia.
    split.
    { intros [? _] l Hl.
      rewrite Z.bits_opp, negb_true_iff by lia.
      apply bounded_iff_bits_nonneg with k; lia. }
    intros Hbit. split.
    - rewrite <-Z.opp_le_mono, <-Z.lt_pred_le.
      apply bounded_iff_bits_nonneg; [lia..|]. intros l Hl.
      rewrite <-negb_true_iff, <-Z.bits_opp by lia.
      by apply Hbit.
    - etrans; [|apply Z.pow_pos_nonneg]; lia.
  Qed.

  Lemma add_nocarry_lor a b :
    Z.land a b = 0 →
    a + b = Z.lor a b.
  Proof. intros ?. rewrite <-Z.lxor_lor by done. by rewrite Z.add_nocarry_lxor. Qed.

  Lemma opp_lnot a : -a - 1 = Z.lnot a.
  Proof. pose proof (Z.add_lnot_diag a). lia. Qed.
End Z.

Module Nat2Z.
  Export Znat.Nat2Z.

  Global Instance inj' : Inj (=) (=) Z.of_nat.
  Proof. intros n1 n2. apply Nat2Z.inj. Qed.

  Lemma divide n m : (Z.of_nat n | Z.of_nat m) ↔ (n | m)%nat.
  Proof.
    split.
    - rewrite <-(Nat2Z.id m) at 2; intros [i ->]; exists (Z.to_nat i). lia.
    - intros [i ->]. exists (Z.of_nat i). by rewrite Nat2Z.inj_mul.
  Qed.
  Lemma inj_div x y : Z.of_nat (x `div` y) = (Z.of_nat x) `div` (Z.of_nat y).
  Proof.
    destruct (decide (y = 0%nat)); [by subst; destruct x |].
    apply Z.div_unique with (Z.of_nat $ x `mod` y)%nat.
    { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
      apply Nat.mod_bound_pos; lia. }
    by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
  Qed.
  Lemma inj_mod x y : Z.of_nat (x `mod` y) = (Z.of_nat x) `mod` (Z.of_nat y).
  Proof.
    destruct (decide (y = 0%nat)); [by subst; destruct x |].
    apply Z.mod_unique with (Z.of_nat $ x `div` y)%nat.
    { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
      apply Nat.mod_bound_pos; lia. }
    by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
  Qed.
End Nat2Z.

Module Z2Nat.
  Export Znat.Z2Nat.

  Lemma neq_0_pos x : Z.to_nat x ≠ 0%nat → 0 < x.
  Proof. by destruct x. Qed.
  Lemma neq_0_nonneg x : Z.to_nat x ≠ 0%nat → 0 ≤ x.
  Proof. by destruct x. Qed.
  Lemma nonpos x : x ≤ 0 → Z.to_nat x = 0%nat.
  Proof. destruct x; simpl; auto using Z2Nat.inj_neg. by intros []. Qed.

  Lemma inj_pow (x y : nat) : Z.of_nat (x ^ y) = (Z.of_nat x) ^ (Z.of_nat y).
  Proof.
    induction y as [|y IH]; [by rewrite Z.pow_0_r, Nat.pow_0_r|].
    by rewrite Nat.pow_succ_r, Nat2Z.inj_succ, Z.pow_succ_r,
      Nat2Z.inj_mul, IH by auto with zpos.
  Qed.

  Lemma divide n m :
    0 ≤ n → 0 ≤ m → (Z.to_nat n | Z.to_nat m)%nat ↔ (n | m).
  Proof. intros. by rewrite <-Nat2Z.divide, !Z2Nat.id by done. Qed.

  Lemma inj_div x y :
    0 ≤ x → 0 ≤ y →
    Z.to_nat (x `div` y) = (Z.to_nat x `div` Z.to_nat y)%nat.
  Proof.
    intros. destruct (decide (y = Z.of_nat 0%nat)); [by subst; destruct x|].
    pose proof (Z.div_pos x y).
    apply (base.inj Z.of_nat). by rewrite Nat2Z.inj_div, !Z2Nat.id by lia.
  Qed.
  Lemma inj_mod x y :
    0 ≤ x → 0 ≤ y →
    Z.to_nat (x `mod` y) = (Z.to_nat x `mod` Z.to_nat y)%nat.
  Proof.
    intros. destruct (decide (y = Z.of_nat 0%nat)); [by subst; destruct x|].
    pose proof (Z.mod_pos x y).
    apply (base.inj Z.of_nat). by rewrite Nat2Z.inj_mod, !Z2Nat.id by lia.
  Qed.
End Z2Nat.

(** ** [bool_to_Z] *)
Definition bool_to_Z (b : bool) : Z :=
  if b then 1 else 0.

Lemma bool_to_Z_bound b : 0 ≤ bool_to_Z b < 2.
Proof. destruct b; simpl; lia. Qed.
Lemma bool_to_Z_eq_0 b : bool_to_Z b = 0 ↔ b = false.
Proof. destruct b; naive_solver. Qed.
Lemma bool_to_Z_neq_0 b : bool_to_Z b ≠ 0 ↔ b = true.
Proof. destruct b; naive_solver. Qed.
Lemma bool_to_Z_spec b n : Z.testbit (bool_to_Z b) n = bool_decide (n = 0) && b.
Proof. by destruct b, n. Qed.

Local Close Scope Z_scope.


(** * Injectivity of casts *)
Module Nat2N.
  Export Nnat.Nat2N.
  Global Instance inj' : Inj (=) (=) N.of_nat := Nat2N.inj.
End Nat2N.

Module N2Nat.
  Export Nnat.N2Nat.
  Global Instance inj' : Inj (=) (=) N.to_nat := N2Nat.inj.
End N2Nat.

Module Pos2Nat.
  Export Pnat.Pos2Nat.
  Global Instance inj' : Inj (=) (=) Pos.to_nat := Pos2Nat.inj.
End Pos2Nat.

Module SuccNat2Pos.
  Export Pnat.SuccNat2Pos.
  Global Instance inj' : Inj (=) (=) Pos.of_succ_nat := SuccNat2Pos.inj.
End SuccNat2Pos.

Module N2Z.
  Export Znat.N2Z.
  Global Instance inj' : Inj (=) (=) Z.of_N := N2Z.inj.
End N2Z.

(* Add others here. *)

(** * Notations and properties of [Qc] *)
Global Typeclasses Opaque Qcle.
Global Typeclasses Opaque Qclt.

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

Global Instance Qcplus_assoc' : Assoc (=) Qcplus := Qcplus_assoc.
Global Instance Qcplus_comm' : Comm (=) Qcplus := Qcplus_comm.
Global Instance Qcplus_left_id : LeftId (=) 0 Qcplus := Qcplus_0_l.
Global Instance Qcplus_right_id : RightId (=) 0 Qcplus := Qcplus_0_r.

Global Instance Qcminus_right_id : RightId (=) 0 Qcminus.
Proof. unfold RightId. intros. ring. Qed.

Global Instance Qcmult_assoc' : Assoc (=) Qcmult := Qcmult_assoc.
Global Instance Qcmult_comm' : Comm (=) Qcmult := Qcmult_comm.
Global Instance Qcmult_left_id : LeftId (=) 1 Qcmult := Qcmult_1_l.
Global Instance Qcmult_right_id : RightId (=) 1 Qcmult := Qcmult_1_r.
Global Instance Qcmult_left_absorb : LeftAbsorb (=) 0 Qcmult := Qcmult_0_l.
Global Instance Qcmult_right_absorb : RightAbsorb (=) 0 Qcmult := Qcmult_0_r.

Global Instance Qcdiv_right_id : RightId (=) 1 Qcdiv.
Proof. intros x. rewrite <-(Qcmult_1_l (x / 1)), Qcmult_div_r; done. Qed.

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

Program Definition pos_to_Qp (n : positive) : Qp := mk_Qp (Qc_of_Z $ Z.pos n) _.
Next Obligation. intros n. by rewrite <-Z2Qc_inj_0, <-Z2Qc_inj_lt. Qed.
Global Arguments pos_to_Qp : simpl never.

Local Open Scope Qp_scope.

Module Qp.
  Lemma to_Qc_inj_iff p q : Qp_to_Qc p = Qp_to_Qc q ↔ p = q.
  Proof.
    split; [|by intros ->].
    destruct p, q; intros; simplify_eq/=; f_equal; apply (proof_irrel _).
  Qed.
  Global Instance eq_dec : EqDecision Qp.
  Proof.
    refine (λ p q, cast_if (decide (Qp_to_Qc p = Qp_to_Qc q)));
      by rewrite <-to_Qc_inj_iff.
  Defined.

  Definition add (p q : Qp) : Qp :=
    let 'mk_Qp p Hp := p in let 'mk_Qp q Hq := q in
    mk_Qp (p + q) (Qcplus_pos_pos _ _ Hp Hq).
  Global Arguments add : simpl never.

  Definition sub (p q : Qp) : option Qp :=
    let 'mk_Qp p Hp := p in let 'mk_Qp q Hq := q in
    let pq := (p - q)%Qc in
    Hpq ← guard (0 < pq)%Qc; Some (mk_Qp pq Hpq).
  Global Arguments sub : simpl never.

  Definition mul (p q : Qp) : Qp :=
    let 'mk_Qp p Hp := p in let 'mk_Qp q Hq := q in
    mk_Qp (p * q) (Qcmult_pos_pos _ _ Hp Hq).
  Global Arguments mul : simpl never.

  Definition inv (q : Qp) : Qp :=
    let 'mk_Qp q Hq := q return _ in
    mk_Qp (/ q)%Qc (Qcinv_pos _ Hq).
  Global Arguments inv : simpl never.

  Definition div (p q : Qp) : Qp := mul p (inv q).
  Global Typeclasses Opaque div.
  Global Arguments div : simpl never.

  Definition le (p q : Qp) : Prop :=
    let 'mk_Qp p _ := p in let 'mk_Qp q _ := q in (p ≤ q)%Qc.
  Definition lt (p q : Qp) : Prop :=
    let 'mk_Qp p _ := p in let 'mk_Qp q _ := q in (p < q)%Qc.

  Lemma to_Qc_inj_add p q : Qp_to_Qc (add p q) = (Qp_to_Qc p + Qp_to_Qc q)%Qc.
  Proof. by destruct p, q. Qed.
  Lemma to_Qc_inj_mul p q : Qp_to_Qc (mul p q) = (Qp_to_Qc p * Qp_to_Qc q)%Qc.
  Proof. by destruct p, q. Qed.
  Lemma to_Qc_inj_le p q : le p q ↔ (Qp_to_Qc p ≤ Qp_to_Qc q)%Qc.
  Proof. by destruct p, q. Qed.
  Lemma to_Qc_inj_lt p q : lt p q ↔ (Qp_to_Qc p < Qp_to_Qc q)%Qc.
  Proof. by destruct p, q. Qed.

  Global Instance le_dec : RelDecision le.
  Proof.
    refine (λ p q, cast_if (decide (Qp_to_Qc p ≤ Qp_to_Qc q)%Qc));
      by rewrite to_Qc_inj_le.
  Qed.
  Global Instance lt_dec : RelDecision lt.
  Proof.
    refine (λ p q, cast_if (decide (Qp_to_Qc p < Qp_to_Qc q)%Qc));
      by rewrite to_Qc_inj_lt.
  Qed.
  Global Instance lt_pi p q : ProofIrrel (lt p q).
  Proof. destruct p, q; apply _. Qed.

  Definition max (q p : Qp) : Qp := if decide (le q p) then p else q.
  Definition min (q p : Qp) : Qp := if decide (le q p) then q else p.

  Module Import notations.
    Infix "+" := add : Qp_scope.
    Infix "-" := sub : Qp_scope.
    Infix "*" := mul : Qp_scope.
    Notation "/ q" := (inv q) : Qp_scope.
    Infix "/" := div : Qp_scope.

    Notation "1" := (pos_to_Qp 1) : Qp_scope.
    Notation "2" := (pos_to_Qp 2) : Qp_scope.
    Notation "3" := (pos_to_Qp 3) : Qp_scope.
    Notation "4" := (pos_to_Qp 4) : Qp_scope.

    Infix "≤" := le : Qp_scope.
    Infix "<" := lt : Qp_scope.
    Notation "p ≤ q ≤ r" := (p ≤ q ∧ q ≤ r) : Qp_scope.
    Notation "p ≤ q < r" := (p ≤ q ∧ q < r) : Qp_scope.
    Notation "p < q < r" := (p < q ∧ q < r) : Qp_scope.
    Notation "p < q ≤ r" := (p < q ∧ q ≤ r) : Qp_scope.
    Notation "p ≤ q ≤ r ≤ r'" := (p ≤ q ∧ q ≤ r ∧ r ≤ r') : Qp_scope.
    Notation "(≤)" := le (only parsing) : Qp_scope.
    Notation "(<)" := lt (only parsing) : Qp_scope.

    Infix "`max`" := max : Qp_scope.
    Infix "`min`" := min : Qp_scope.
  End notations.

  Global Hint Extern 0 (_ ≤ _)%Qp => reflexivity : core.

  Global Instance inhabited : Inhabited Qp := populate 1.

  Global Instance add_assoc : Assoc (=) add.
  Proof. intros [p ?] [q ?] [r ?]; apply to_Qc_inj_iff, Qcplus_assoc. Qed.
  Global Instance add_comm : Comm (=) add.
  Proof. intros [p ?] [q ?]; apply to_Qc_inj_iff, Qcplus_comm. Qed.
  Global Instance add_inj_r p : Inj (=) (=) (add p).
  Proof.
    destruct p as [p ?].
    intros [q1 ?] [q2 ?]. rewrite <-!to_Qc_inj_iff; simpl. apply (inj (Qcplus p)).
  Qed.
  Global Instance add_inj_l p : Inj (=) (=) (λ q, q + p).
  Proof.
    destruct p as [p ?].
    intros [q1 ?] [q2 ?]. rewrite <-!to_Qc_inj_iff; simpl. apply (inj (λ q, q + p)%Qc).
  Qed.

  Global Instance mul_assoc : Assoc (=) mul.
  Proof. intros [p ?] [q ?] [r ?]. apply Qp.to_Qc_inj_iff, Qcmult_assoc. Qed.
  Global Instance mul_comm : Comm (=) mul.
  Proof. intros [p ?] [q ?]; apply Qp.to_Qc_inj_iff, Qcmult_comm. Qed.
  Global Instance mul_inj_r p : Inj (=) (=) (mul p).
  Proof.
    destruct p as [p ?]. intros [q1 ?] [q2 ?]. rewrite <-!Qp.to_Qc_inj_iff; simpl.
    intros Hpq.
    apply (anti_symm Qcle); apply (Qcmult_le_mono_pos_l _ _ p); by rewrite ?Hpq.
  Qed.
  Global Instance mul_inj_l p : Inj (=) (=) (λ q, q * p).
  Proof.
    intros q1 q2 Hpq. apply (inj (mul p)). by rewrite !(comm_L mul p).
  Qed.

  Lemma mul_add_distr_l p q r : p * (q + r) = p * q + p * r.
  Proof. destruct p, q, r; by apply Qp.to_Qc_inj_iff, Qcmult_plus_distr_r. Qed.
  Lemma mul_add_distr_r p q r : (p + q) * r = p * r + q * r.
  Proof. destruct p, q, r; by apply Qp.to_Qc_inj_iff, Qcmult_plus_distr_l. Qed.
  Lemma mul_1_l p : 1 * p = p.
  Proof. destruct p; apply Qp.to_Qc_inj_iff, Qcmult_1_l. Qed.
  Lemma mul_1_r p : p * 1 = p.
  Proof. destruct p; apply Qp.to_Qc_inj_iff, Qcmult_1_r. Qed.
  Global Instance mul_left_id : LeftId (=) 1 mul := mul_1_l.
  Global Instance mul_right_id : RightId (=) 1 mul := mul_1_r.

  Lemma add_1_1 : 1 + 1 = 2.
  Proof. compute_done. Qed.
  Lemma add_diag p : p + p = 2 * p.
  Proof. by rewrite <-add_1_1, mul_add_distr_r, !mul_1_l. Qed.

  Lemma mul_inv_l p : /p * p = 1.
  Proof.
    destruct p as [p ?]; apply Qp.to_Qc_inj_iff; simpl.
    by rewrite Qcmult_inv_l, Z2Qc_inj_1 by (by apply not_symmetry, Qclt_not_eq).
  Qed.
  Lemma mul_inv_r p : p * /p = 1.
  Proof. by rewrite (comm_L mul), mul_inv_l. Qed.
  Lemma inv_mul_distr p q : /(p * q) = /p * /q.
  Proof.
    apply (inj (mul (p * q))).
    rewrite mul_inv_r, (comm_L mul p), <-(assoc_L _), (assoc_L mul p).
    by rewrite mul_inv_r, mul_1_l, mul_inv_r.
  Qed.
  Lemma inv_involutive p : / /p = p.
  Proof.
    rewrite <-(mul_1_l (/ /p)), <-(mul_inv_r p), <-(assoc_L _).
    by rewrite mul_inv_r, mul_1_r.
  Qed.
  Global Instance inv_inj : Inj (=) (=) inv.
  Proof.
    intros p1 p2 Hp. apply (inj (mul (/p1))).
    by rewrite mul_inv_l, Hp, mul_inv_l.
  Qed.
  Lemma inv_1 : /1 = 1.
  Proof. compute_done. Qed.
  Lemma inv_half_half : /2 + /2 = 1.
  Proof. compute_done. Qed.
  Lemma inv_quarter_quarter : /4 + /4 = /2.
  Proof. compute_done. Qed.

  Lemma div_diag p : p / p = 1.
  Proof. apply mul_inv_r. Qed.
  Lemma mul_div_l p q : (p / q) * q = p.
  Proof. unfold div. by rewrite <-(assoc_L _), mul_inv_l, mul_1_r. Qed.
  Lemma mul_div_r p q : q * (p / q) = p.
  Proof. by rewrite (comm_L mul q), mul_div_l. Qed.
  Lemma div_add_distr p q r : (p + q) / r = p / r + q / r.
  Proof. apply mul_add_distr_r. Qed.
  Lemma div_div p q r : (p / q) / r = p / (q * r).
  Proof. unfold div. by rewrite inv_mul_distr, (assoc_L _). Qed.
  Lemma div_mul_cancel_l p q r : (r * p) / (r * q) = p / q.
  Proof.
    rewrite <-div_div. f_equiv. unfold div.
    by rewrite (comm_L mul r), <-(assoc_L _), mul_inv_r, mul_1_r.
  Qed.
  Lemma div_mul_cancel_r p q r : (p * r) / (q * r) = p / q.
  Proof. by rewrite <-!(comm_L mul r), div_mul_cancel_l. Qed.
  Lemma div_1 p : p / 1 = p.
  Proof. by rewrite <-(mul_1_r (p / 1)), mul_div_l. Qed.
  Lemma div_2 p : p / 2 + p / 2 = p.
  Proof.
    rewrite <-div_add_distr, add_diag.
    rewrite <-(mul_1_r 2) at 2. by rewrite div_mul_cancel_l, div_1.
  Qed.
  Lemma div_2_mul p q : p / (2 * q) + p / (2 * q) = p / q.
  Proof. by rewrite <-div_add_distr, add_diag, div_mul_cancel_l. Qed.
  Global Instance div_right_id : RightId (=) 1 div := div_1.

  Lemma half_half : 1 / 2 + 1 / 2 = 1.
  Proof. compute_done. Qed.
  Lemma quarter_quarter : 1 / 4 + 1 / 4 = 1 / 2.
  Proof. compute_done. Qed.
  Lemma quarter_three_quarter : 1 / 4 + 3 / 4 = 1.
  Proof. compute_done. Qed.
  Lemma three_quarter_quarter : 3 / 4 + 1 / 4 = 1.
  Proof. compute_done. Qed.

  Global Instance div_inj_r p : Inj (=) (=) (div p).
  Proof. unfold div; apply _. Qed.
  Global Instance div_inj_l p : Inj (=) (=) (λ q, q / p)%Qp.
  Proof. unfold div; apply _. Qed.

  Global Instance le_po : PartialOrder (≤).
  Proof.
    split; [split|].
    - intros p. by apply to_Qc_inj_le.
    - intros p q r. rewrite !to_Qc_inj_le. by etrans.
    - intros p q. rewrite !to_Qc_inj_le, <-to_Qc_inj_iff. apply Qcle_antisym.
  Qed.
  Global Instance lt_strict : StrictOrder (<).
  Proof.
    split.
    - intros p ?%to_Qc_inj_lt. by apply (irreflexivity (<)%Qc (Qp_to_Qc p)).
    - intros p q r. rewrite !to_Qc_inj_lt. by etrans.
  Qed.
  Global Instance le_total: Total (≤).
  Proof. intros p q. rewrite !to_Qc_inj_le. apply (total Qcle). Qed.

  Lemma lt_le_incl p q : p < q → p ≤ q.
  Proof. rewrite to_Qc_inj_lt, to_Qc_inj_le. apply Qclt_le_weak. Qed.
  Lemma le_lteq p q : p ≤ q ↔ p < q ∨ p = q.
  Proof.
    rewrite to_Qc_inj_lt, to_Qc_inj_le, <-Qp.to_Qc_inj_iff. split.
    - intros [?| ->]%Qcle_lt_or_eq; auto.
    - intros [?| ->]; auto using Qclt_le_weak.
  Qed.
  Lemma lt_ge_cases p q : {p < q} + {q ≤ p}.
  Proof.
    refine (cast_if (Qclt_le_dec (Qp_to_Qc p) (Qp_to_Qc q)%Qc));
      [by apply to_Qc_inj_lt|by apply to_Qc_inj_le].
  Defined.
  Lemma le_lt_trans p q r : p ≤ q → q < r → p < r.
  Proof. rewrite !to_Qc_inj_lt, to_Qc_inj_le. apply Qcle_lt_trans. Qed.
  Lemma lt_le_trans p q r : p < q → q ≤ r → p < r.
  Proof. rewrite !to_Qc_inj_lt, to_Qc_inj_le. apply Qclt_le_trans. Qed.

  Lemma le_ngt p q : p ≤ q ↔ ¬q < p.
  Proof.
    rewrite !to_Qc_inj_lt, to_Qc_inj_le.
    split; auto using Qcle_not_lt, Qcnot_lt_le.
  Qed.
  Lemma lt_nge p q : p < q ↔ ¬q ≤ p.
  Proof.
    rewrite !to_Qc_inj_lt, to_Qc_inj_le.
    split; auto using Qclt_not_le, Qcnot_le_lt.
  Qed.

  Lemma add_le_mono_l p q r : p ≤ q ↔ r + p ≤ r + q.
  Proof. rewrite !to_Qc_inj_le. destruct p, q, r; apply Qcplus_le_mono_l. Qed.
  Lemma add_le_mono_r p q r : p ≤ q ↔ p + r ≤ q + r.
  Proof. rewrite !(comm_L add _ r). apply add_le_mono_l. Qed.
  Lemma add_le_mono q p n m : q ≤ n → p ≤ m → q + p ≤ n + m.
  Proof. intros. etrans; [by apply add_le_mono_l|by apply add_le_mono_r]. Qed.

  Lemma add_lt_mono_l p q r : p < q ↔ r + p < r + q.
  Proof. by rewrite !lt_nge, <-add_le_mono_l. Qed.
  Lemma add_lt_mono_r p q r : p < q ↔ p + r < q + r.
  Proof. by rewrite !lt_nge, <-add_le_mono_r. Qed.
  Lemma add_lt_mono q p n m : q < n → p < m → q + p < n + m.
  Proof. intros. etrans; [by apply add_lt_mono_l|by apply add_lt_mono_r]. Qed.

  Lemma mul_le_mono_l p q r : p ≤ q ↔ r * p ≤ r * q.
  Proof.
    rewrite !to_Qc_inj_le. destruct p, q, r; by apply Qcmult_le_mono_pos_l.
  Qed.
  Lemma mul_le_mono_r p q r : p ≤ q ↔ p * r ≤ q * r.
  Proof. rewrite !(comm_L mul _ r). apply mul_le_mono_l. Qed.
  Lemma mul_le_mono q p n m : q ≤ n → p ≤ m → q * p ≤ n * m.
  Proof. intros. etrans; [by apply mul_le_mono_l|by apply mul_le_mono_r]. Qed.

  Lemma mul_lt_mono_l p q r : p < q ↔ r * p < r * q.
  Proof.
    rewrite !to_Qc_inj_lt. destruct p, q, r; by apply Qcmult_lt_mono_pos_l.
  Qed.
  Lemma mul_lt_mono_r p q r : p < q ↔ p * r < q * r.
  Proof. rewrite !(comm_L mul _ r). apply mul_lt_mono_l. Qed.
  Lemma mul_lt_mono q p n m : q < n → p < m → q * p < n * m.
  Proof. intros. etrans; [by apply mul_lt_mono_l|by apply mul_lt_mono_r]. Qed.

  Lemma lt_add_l p q : p < p + q.
  Proof.
    destruct p as [p ?], q as [q ?]. apply to_Qc_inj_lt; simpl.
    rewrite <- (Qcplus_0_r p) at 1. by rewrite <-Qcplus_lt_mono_l.
  Qed.
  Lemma lt_add_r p q : q < p + q.
  Proof. rewrite (comm_L add). apply lt_add_l. Qed.

  Lemma not_add_le_l p q : ¬(p + q ≤ p).
  Proof. apply lt_nge, lt_add_l. Qed.
  Lemma not_add_le_r p q : ¬(p + q ≤ q).
  Proof. apply lt_nge, lt_add_r. Qed.

  Lemma add_id_free q p : q + p ≠ q.
  Proof. intro Heq. apply (not_add_le_l q p). by rewrite Heq. Qed.

  Lemma le_add_l p q : p ≤ p + q.
  Proof. apply lt_le_incl, lt_add_l. Qed.
  Lemma le_add_r p q : q ≤ p + q.
  Proof. apply lt_le_incl, lt_add_r. Qed.

  Lemma sub_Some p q r : p - q = Some r ↔ p = q + r.
  Proof.
    destruct p as [p Hp], q as [q Hq], r as [r Hr].
    unfold sub, add; simpl; rewrite <-Qp.to_Qc_inj_iff; simpl. split.
    - intros; simplify_option_eq. unfold Qcminus.
      by rewrite (Qcplus_comm p), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
    - intros ->. unfold Qcminus.
      rewrite <-Qcplus_assoc, (Qcplus_comm r), Qcplus_assoc.
      rewrite Qcplus_opp_r, Qcplus_0_l. simplify_option_eq; [|done].
      f_equal. by apply Qp.to_Qc_inj_iff.
  Qed.
  Lemma lt_sum p q : p < q ↔ ∃ r, q = p + r.
  Proof.
    destruct p as [p Hp], q as [q Hq]. rewrite to_Qc_inj_lt; simpl.
    split.
    - intros Hlt%Qclt_minus_iff. exists (mk_Qp (q - p) Hlt).
      apply Qp.to_Qc_inj_iff; simpl. unfold Qcminus.
      by rewrite (Qcplus_comm q), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
    - intros [[r ?] ?%Qp.to_Qc_inj_iff]; simplify_eq/=.
      rewrite <-(Qcplus_0_r p) at 1. by apply Qcplus_lt_mono_l.
  Qed.

  Lemma sub_None p q : p - q = None ↔ p ≤ q.
  Proof.
    rewrite le_ngt, lt_sum, eq_None_not_Some.
    by setoid_rewrite <-sub_Some.
  Qed.
  Lemma sub_diag p : p - p = None.
  Proof. by apply sub_None. Qed.
  Lemma add_sub p q : (p + q) - q = Some p.
  Proof. apply sub_Some. by rewrite (comm_L add). Qed.

  Lemma inv_lt_mono p q : p < q ↔ /q < /p.
  Proof.
    revert p q. cut (∀ p q, p < q → / q < / p).
    { intros help p q. split; [apply help|]. intros.
      rewrite <-(inv_involutive p), <-(inv_involutive q). by apply help. }
    intros p q Hpq. apply (mul_lt_mono_l _ _ q). rewrite mul_inv_r.
    apply (mul_lt_mono_r _ _ p). rewrite <-(assoc_L _), mul_inv_l.
    by rewrite mul_1_l, mul_1_r.
  Qed.
  Lemma inv_le_mono p q : p ≤ q ↔ /q ≤ /p.
  Proof. by rewrite !le_ngt, inv_lt_mono. Qed.

  Lemma div_le_mono_l p q r : q ≤ p ↔ r / p ≤ r / q.
  Proof. unfold div. by rewrite <-mul_le_mono_l, inv_le_mono. Qed.
  Lemma div_le_mono_r p q r : p ≤ q ↔ p / r ≤ q / r.
  Proof. apply mul_le_mono_r. Qed.
  Lemma div_lt_mono_l p q r : q < p ↔ r / p < r / q.
  Proof. unfold div. by rewrite <-mul_lt_mono_l, inv_lt_mono. Qed.
  Lemma div_lt_mono_r p q r : p < q ↔ p / r < q / r.
  Proof. apply mul_lt_mono_r. Qed.

  Lemma div_lt p q : 1 < q → p / q < p.
  Proof. by rewrite (div_lt_mono_l _ _ p), div_1. Qed.
  Lemma div_le p q : 1 ≤ q → p / q ≤ p.
  Proof. by rewrite (div_le_mono_l _ _ p), div_1. Qed.

  Lemma lower_bound q1 q2 : ∃ q q1' q2', q1 = q + q1' ∧ q2 = q + q2'.
  Proof.
    revert q1 q2. cut (∀ q1 q2 : Qp, q1 ≤ q2 →
      ∃ q q1' q2', q1 = q + q1' ∧ q2 = q + q2').
    { intros help q1 q2.
      destruct (lt_ge_cases q2 q1) as [Hlt|Hle]; eauto.
      destruct (help q2 q1) as (q&q1'&q2'&?&?); eauto using lt_le_incl. }
    intros q1 q2 Hq. exists (q1 / 2)%Qp, (q1 / 2)%Qp.
    assert (q1 / 2 < q2) as [q2' ->]%lt_sum.
    { eapply lt_le_trans, Hq. by apply div_lt. }
    eexists; split; [|done]. by rewrite div_2.
  Qed.

  Lemma lower_bound_lt q1 q2 : ∃ q : Qp, q < q1 ∧ q < q2.
  Proof.
    destruct (lower_bound q1 q2) as (qmin & q1' & q2' & [-> ->]).
    exists qmin. split; eapply lt_sum; eauto.
  Qed.

  Lemma cross_split a b c d :
    a + b = c + d →
    ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d.
  Proof.
    intros H. revert a b c d H. cut (∀ a b c d : Qp,
      a < c → a + b = c + d →
      ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d)%Qp.
    { intros help a b c d Habcd.
      destruct (lt_ge_cases a c) as [?|[?| ->]%le_lteq].
      - auto.
      - destruct (help c d a b); [done..|]. naive_solver.
      - apply (inj (add a)) in Habcd as ->.
        destruct (lower_bound a d) as (q&a'&d'&->&->).
        exists a', q, q, d'. repeat split; done || by rewrite (comm_L add). }
    intros a b c d [e ->]%lt_sum. rewrite <-(assoc_L _). intros ->%(inj (add a)).
    destruct (lower_bound a d) as (q&a'&d'&->&->).
    eexists a', q, (q + e)%Qp, d'; split_and?; [by rewrite (comm_L add)|..|done].
    - by rewrite (assoc_L _), (comm_L add e).
    - by rewrite (assoc_L _), (comm_L add a').
  Qed.

  Lemma bounded_split p r : ∃ q1 q2 : Qp, q1 ≤ r ∧ p = q1 + q2.
  Proof.
    destruct (lt_ge_cases r p) as [[q ->]%lt_sum|?].
    { by exists r, q. }
    exists (p / 2)%Qp, (p / 2)%Qp; split.
    + trans p; [|done]. by apply div_le.
    + by rewrite div_2.
  Qed.

  Lemma max_spec q p : (q < p ∧ q `max` p = p) ∨ (p ≤ q ∧ q `max` p = q).
  Proof.
    unfold max.
    destruct (decide (q ≤ p)) as [[?| ->]%le_lteq|?]; [by auto..|].
    right. split; [|done]. by apply lt_le_incl, lt_nge.
  Qed.

  Lemma max_spec_le q p : (q ≤ p ∧ q `max` p = p) ∨ (p ≤ q ∧ q `max` p = q).
  Proof. destruct (max_spec q p) as [[?%lt_le_incl?]|]; [left|right]; done. Qed.

  Global Instance max_assoc : Assoc (=) max.
  Proof.
    intros q p o. unfold max. destruct (decide (q ≤ p)), (decide (p ≤ o));
      try by rewrite ?decide_True by (by etrans).
    rewrite decide_False by done.
    by rewrite decide_False by (apply lt_nge; etrans; by apply lt_nge).
  Qed.
  Global Instance max_comm : Comm (=) max.
  Proof.
    intros q p.
    destruct (max_spec_le q p) as [[?->]|[?->]],
      (max_spec_le p q) as [[?->]|[?->]]; done || by apply (anti_symm (≤)).
  Qed.

  Lemma max_id q : q `max` q = q.
  Proof. by destruct (max_spec q q) as [[_->]|[_->]]. Qed.

  Lemma le_max_l q p : q ≤ q `max` p.
  Proof. unfold max. by destruct (decide (q ≤ p)). Qed.
  Lemma le_max_r q p : p ≤ q `max` p.
  Proof. rewrite (comm_L max q). apply le_max_l. Qed.

  Lemma max_add q p : q `max` p ≤ q + p.
  Proof.
    unfold max.
    destruct (decide (q ≤ p)); [apply le_add_r|apply le_add_l].
  Qed.

  Lemma max_lub_l q p o : q `max` p ≤ o → q ≤ o.
  Proof. unfold max. destruct (decide (q ≤ p)); [by etrans|done]. Qed.
  Lemma max_lub_r q p o : q `max` p ≤ o → p ≤ o.
  Proof. rewrite (comm _ q). apply max_lub_l. Qed.

  Lemma min_spec q p : (q < p ∧ q `min` p = q) ∨ (p ≤ q ∧ q `min` p = p).
  Proof.
    unfold min.
    destruct (decide (q ≤ p)) as [[?| ->]%le_lteq|?]; [by auto..|].
    right. split; [|done]. by apply lt_le_incl, lt_nge.
  Qed.

  Lemma min_spec_le q p : (q ≤ p ∧ q `min` p = q) ∨ (p ≤ q ∧ q `min` p = p).
  Proof. destruct (min_spec q p) as [[?%lt_le_incl ?]|]; [left|right]; done. Qed.

  Global Instance min_assoc : Assoc (=) min.
  Proof.
    intros q p o. unfold min.
    destruct (decide (q ≤ p)), (decide (p ≤ o)); eauto using decide_False.
    - by rewrite !decide_True by (by etrans).
    - by rewrite decide_False by (apply lt_nge; etrans; by apply lt_nge).
  Qed.
  Global Instance min_comm : Comm (=) min.
  Proof.
    intros q p.
    destruct (min_spec_le q p) as [[?->]|[?->]],
      (min_spec_le p q) as [[? ->]|[? ->]]; done || by apply (anti_symm (≤)).
  Qed.

  Lemma min_id q : q `min` q = q.
  Proof. by destruct (min_spec q q) as [[_->]|[_->]]. Qed.
  Lemma le_min_r q p : q `min` p ≤ p.
  Proof. by destruct (min_spec_le q p) as [[?->]|[?->]]. Qed.

  Lemma le_min_l p q : p `min` q ≤ p.
  Proof. rewrite (comm_L min p). apply le_min_r. Qed.

  Lemma min_l_iff q p : q `min` p = q ↔ q ≤ p.
  Proof.
    destruct (min_spec_le q p) as [[?->]|[?->]]; [done|].
    split; [by intros ->|]. intros. by apply (anti_symm (≤)).
  Qed.
  Lemma min_r_iff q p : q `min` p = p ↔ p ≤ q.
  Proof. rewrite (comm_L min q). apply min_l_iff. Qed.
End Qp.

Export Qp.notations.

Lemma pos_to_Qp_1 : pos_to_Qp 1 = 1.
Proof. compute_done. Qed.
Lemma pos_to_Qp_inj n m : pos_to_Qp n = pos_to_Qp m → n = m.
Proof. by injection 1. Qed.
Lemma pos_to_Qp_inj_iff n m : pos_to_Qp n = pos_to_Qp m ↔ n = m.
Proof. split; [apply pos_to_Qp_inj|by intros ->]. Qed.
Lemma pos_to_Qp_inj_le n m : (n ≤ m)%positive ↔ pos_to_Qp n ≤ pos_to_Qp m.
Proof. rewrite Qp.to_Qc_inj_le; simpl. by rewrite <-Z2Qc_inj_le. Qed.
Lemma pos_to_Qp_inj_lt n m : (n < m)%positive ↔ pos_to_Qp n < pos_to_Qp m.
Proof. by rewrite Pos.lt_nle, Qp.lt_nge, <-pos_to_Qp_inj_le. Qed.
Lemma pos_to_Qp_add x y : pos_to_Qp x + pos_to_Qp y = pos_to_Qp (x + y).
Proof. apply Qp.to_Qc_inj_iff; simpl. by rewrite Pos2Z.inj_add, Z2Qc_inj_add. Qed.
Lemma pos_to_Qp_mul x y : pos_to_Qp x * pos_to_Qp y = pos_to_Qp (x * y).
Proof. apply Qp.to_Qc_inj_iff; simpl. by rewrite Pos2Z.inj_mul, Z2Qc_inj_mul. Qed.

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
Proof. unfold rotate_nat_add. by rewrite Nat2Z.inj_mod, Zplus_mod_idemp_l. Qed.

Lemma rotate_nat_add_alt base offset len:
  base < len → offset < len →
  rotate_nat_add base offset len =
  if decide (base + offset < len) then base + offset else base + offset - len.
Proof.
  unfold rotate_nat_add. intros ??. case_decide.
  - rewrite Z.mod_small by lia. by rewrite <-Nat2Z.inj_add, Nat2Z.id.
  - rewrite (Z.mod_in_range 1) by lia.
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
  - rewrite (Z.mod_in_range 1) by lia.
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
  rewrite Z2Nat.inj_mod, Z2Nat.inj_add, !Nat2Z.id; lia.
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
  rewrite Z2Nat.id by (apply Z.mod_pos; lia). rewrite Zplus_mod_idemp_r.
  replace (Z.of_nat base + (Z.of_nat len + Z.of_nat offset - Z.of_nat base))%Z
    with (Z.of_nat len + Z.of_nat offset)%Z by lia.
  rewrite (Z.mod_in_range 1) by lia.
  rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_sub_add base len offset:
  offset < len →
  rotate_nat_sub base (rotate_nat_add base offset len) len = offset.
Proof.
  intros ?. unfold rotate_nat_add, rotate_nat_sub.
  rewrite Z2Nat.id by (apply Z.mod_pos; lia).
  assert (∀ n, (Z.of_nat len + n - Z.of_nat base) = ((Z.of_nat len - Z.of_nat base) + n))%Z
    as -> by naive_solver lia.
  rewrite Zplus_mod_idemp_r.
  replace (Z.of_nat len - Z.of_nat base + (Z.of_nat base + Z.of_nat offset))%Z with
    (Z.of_nat len + Z.of_nat offset)%Z by lia.
  rewrite (Z.mod_in_range 1) by lia.
  rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_add_add base offset len n:
  0 < len →
  rotate_nat_add base (offset + n) len =
  (rotate_nat_add base offset len + n) `mod` len.
Proof.
  intros ?. unfold rotate_nat_add.
  rewrite !Z2Nat.inj_mod, !Z2Nat.inj_add, !Nat2Z.id by lia.
  by rewrite Nat.add_assoc, Nat.add_mod_idemp_l by lia.
Qed.

Lemma rotate_nat_add_S base offset len:
  0 < len →
  rotate_nat_add base (S offset) len =
  S (rotate_nat_add base offset len) `mod` len.
Proof. intros ?. by rewrite <-Nat.add_1_r, rotate_nat_add_add, Nat.add_1_r. Qed.
