(** Basic tests for atctics that don't import anything else
(and hence can be run even when nothing else even builds. *)
From Coq Require Import String.
From stdpp Require Import tactics.

Local Unset Mangle Names. (* for stable goal printing *)
Local Open Scope string_scope.

Goal ∀ P1 P2 P3 P4 (P: Prop),
  P1 ∨ (Is_true (P2 || P3)) ∨ P4 →
  (P1 → P) →
  (P2 → P) →
  (P3 → P) →
  (P4 → P) →
  P.
Proof.
  intros * HH X1 X2 X3 X4.
  destruct_or? HH; [ exact (X1 HH) | exact (X2 HH) | exact (X3 HH) | exact (X4 HH) ].
Qed.

Goal ∀ P1 P2 P3 P4 (P: Prop),
  P1 ∨ P2 →
  P3 ∨ P4 →
  (P1 → P3 → P) →
  (P1 → P4 → P) →
  (P2 → P3 → P) →
  (P2 → P4 → P) →
  P.
Proof.
  intros * HH1 HH2 X1 X2 X3 X4.
  destruct_or?; [ exact (X1 HH1 HH2) | exact (X3 HH1 HH2) | exact (X2 HH1 HH2) | exact (X4 HH1 HH2) ].
Qed.

Goal ∀ P1 P2 P3 P4 (P: Prop),
  id (P1 ∨ P2) →
  id (P3 ∨ P4) →
  (P1 → P3 → P) →
  (P1 → P4 → P) →
  (P2 → P3 → P) →
  (P2 → P4 → P) →
  P.
Proof.
  intros * HH1 HH2 X1 X2 X3 X4.
  Fail progress destruct_or?.
  Fail progress destruct_or!.
  destruct_or! HH1; destruct_or! HH2;
  [ exact (X1 HH1 HH2) | exact (X2 HH1 HH2) | exact (X3 HH1 HH2) | exact (X4 HH1 HH2) ].
Qed.

Goal ∀ P1 P2 P3 P4,
  P1 ∧ (Is_true (P2 && P3)) ∧ P4 →
  P1 ∧ P2 ∧ P3.
Proof.
  intros * HH. split_and!; [ destruct_and? HH; assumption | destruct_and?; assumption | ].
  destruct_and?. Fail destruct_and!. assumption.
Qed.

(** Tests for [case_match] *)
Goal ∀ n : nat, match n with | 0 => n = 0 | S n' => n = S n' end.
Proof.
  intros. by case_match.
Restart. Proof.
  intros. by case_match eqn:Heq; revert Heq. (* [revert Heq] checks that [Heq] exists *)
Qed.

Goal ∀ n m : nat, match n with | 0 => m = 0 | S n' => m = S n' end → n = m.
Proof.
  intros. by case_match.
Restart. Proof.
  intros. by case_match eqn:Heq; revert Heq. (* [revert Heq] checks that [Heq] exists *)
Qed.

(** Tests for [select] tactics *)
Goal ∀ (n : nat), ∃ m : nat, True.
Proof. intros ?. rename select nat into m. exists m. done. Qed.

Goal ∀ (P : nat → Prop), P 3 → P 4 → P 4.
Proof. intros P **. rename select (P _) into HP4. apply HP4. Qed.

Goal ∀ P Q : Prop, True ∨ True → P ∨ Q → Q ∨ P.
Proof.
  intros P Q ??.
  (* should select the last hypothesis *)
  destruct select (_ ∨ _); by constructor.
Restart. Proof.
  intros P Q ??.
  (* should select the last hypothesis *)
  destruct select (_ ∨ _) as [H1|H2].
  - right. exact H1.
  - left. exact H2.
Restart. Proof.
  intros P Q ??.
  (* should select the last hypothesis *)
  inv select (_ ∨ _); by constructor.
Restart. Proof.
  intros P Q ??.
  (* should select the last hypothesis *)
  inv select (_ ∨ _) as [H1|H2].
  - right. exact H1.
  - left. exact H2.
Restart. Proof.
  intros P Q ??.
  (* should select the last hypothesis *)
  inversion select (_ ∨ _); by constructor.
Restart. Proof.
  intros P Q ??.
  (* should select the last hypothesis *)
  inversion select (_ ∨ _) as [H1|H2].
  - right. exact H1.
  - left. exact H2.
Qed.

(** [mk_evar] works on things that coerce to types. *)
(** This is a feature when we have packed structures, for example Iris's [ofe]
(fields other than the carrier omitted). *)
Structure ofe := Ofe { ofe_car :> Type }.
Goal ∀ A : ofe, True.
intros A.
let x := mk_evar A in idtac.
Abort.
(** More surprisingly, it also works for other coercions into a
universe, like [Is_true : bool → Prop]. *)
Goal True.
let x := mk_evar true in idtac.
Abort.

(** get_head tests. *)
Lemma test_get_head (f : nat → nat → nat → nat) : True.
Proof.
  let f' := get_head (f 0 1 2) in unify f f'.
  let f' := get_head f in unify f f'.
Abort.

(** inv tests *)
Inductive even : nat → Prop :=
  | Even0 : even 0
  | Even2 n : even n → even (S (S n)).
Lemma inv_test_1 n : even (2 + n) → even n.
Proof. intros H. inv H as [|? H']. Show. done. Qed.
Lemma inv_test_2 (a b c d : nat) : a ≠ c → (a, b) = (c, d) → False.
Proof.
  (* Test taken from https://github.com/coq/coq/issues/2465 *)
  intros DIFF EQ. inv EQ. (* Thanks to the simplify_eq this solves the goal. *)
Qed.
Check "inv_test_num".
Lemma inv_test_num n : True → even (2 + n) → even n.
Proof.
  (* Make sure we do the same thing as [inversion_clear] when there are
  other hypotheses before the one we invert. *)
  inversion_clear 2 as [|? H']. Show.
Restart. Proof.
  inv 2 as [|? H']. Show. done.
Qed.

(** o-tactic tests *)
Check "otest".
Lemma otest (P Q R : nat → Prop)
  (HPQR1 : ∀ m n, P n → Q m → R (n + m))
  (HPQR2 : ∀ m n, P n → Q m → R (n + m) ∧ R 2)
  (HP0 : P 0)
  (HP1 : P 1)
  (HQ : Q 5) : R 6.
Proof.
  (** Imagine we couldn't [apply] since the goal is still very different, we
  need forward reasoning. Also we don't have proof terms for [P n] and [Q m] but
  a short proof script can solve them. [n] needs to be specified, but [m] is
  huge and we don't want to specify it. What do we do? The "o" family of tactics
  for working with "o"pen terms helps. *)
  opose proof (HPQR1 _ (S _) _ _) as HR; [exact HP1|exact HQ|]. exact HR.
Restart. Proof.
  (** We can have fewer [_]. *)
  opose proof (HPQR1 _ (S _) _) as HR; [exact HP1|]. exact (HR HQ).
Restart. Proof.
  (** And even fewer. *)
  opose proof (HPQR1 _ (S _)) as HR. exact (HR HP1 HQ).
Restart. Proof.
  (** The [*] variant automatically adds [_]. *)
  opose proof* (HPQR1 _ (S _)) as HR; [exact HP1|exact HQ|]. exact HR.
Restart. Proof.
  (** Same deal for [generalize]. *)
  ogeneralize (HPQR1 _ 1). intros HR. exact (HR HP1 HQ).
Restart. Proof.
  ogeneralize (HPQR1 _ 1 _); [exact HP1|]. intros HR. exact (HR HQ).
Restart. Proof.
  ogeneralize* (HPQR1 _ 1); [exact HP1|exact HQ|]. intros HR. exact HR.
Restart. Proof.
  (** [odestruct] also automatically adds subgoals until there is something
  to destruct, as usual. Note that [edestruct] wouldn't help here,
  it just complains that it cannot infer the placeholder. *)
  Fail edestruct (HPQR2 _ 1).
  odestruct (HPQR2 _ 1) as [HR1 HR2]; [exact HP1|exact HQ|]. exact HR1.
Restart. Proof.
  (** [ospecialize] is like [opose proof] but it reuses the name.
  It only works on local assumptions. *)
  Fail ospecialize (plus 0 0).
  ospecialize (HPQR1 _ 1 _); [exact HP1|]. exact (HPQR1 HQ).
Restart. Proof.
  ospecialize (HPQR1 _ 1). exact (HPQR1 HP1 HQ).
Restart. Proof.
  ospecialize* (HPQR1 _ 1); [exact HP1|exact HQ|]. exact HPQR1.
Qed.

(** Make sure [∀] also get auto-instantiated by the [*] variant. *)
Lemma o_tactic_with_forall (P Q R : nat → Prop) :
  P 1 → Q 1 → (∀ n, P n → Q n → R n) → R 1.
Proof.
  intros HP HQ HR.
  ospecialize* HR; [exact HP|exact HQ|exact HR].
Restart. Proof.
  intros HP HQ HR.
  opose proof* HR as HR'; [exact HP|exact HQ|exact HR'].
Qed.

(* Like [inversion], this does *not* clear. *)
Check "oinversion_test1".
Lemma oinversion_test1 n : even (2 + n) → even n.
Proof. intros H. oinversion H as [|n' Hn' EQ]. Show. done. Qed.

Lemma oinv_test1 : ~(∀ n, even n).
Proof. intros H. oinv (H 1). Qed.
(* Ensure we clear the [H] if appropriate. *)
Check "oinv_test2".
Lemma oinv_test2 n : even (2 + n) → even n.
Proof.
  intros H. oinv H as [|? H']. Show. done.
Restart. Proof.
  oinv 1 as [|? H']. Show. done.
Qed.
Lemma oinv_test_num (P : Prop) n :
  P → (P → even (2 + n)) → even n.
Proof.
  intros HP. oinv 1.
  { exact HP. }
  done.
Qed.

(** Some tests for f_equiv. *)
(* Similar to [f_equal], it should solve goals by [reflexivity]. *)
Lemma test_f_equiv_refl {A} (R : relation A) `{!Equivalence R} x :
  R x x.
Proof. f_equiv. Qed.

(* And immediately solve sub-goals by reflexivity *)
Lemma test_f_equiv_refl_nested {A} (R : relation A) `{!Equivalence R} g x y z :
  Proper (R ==> R ==> R) g →
  R y z →
  R (g x y) (g x z).
Proof. intros ? Hyz. f_equiv. apply Hyz. Qed.

(* Ensure we can handle [flip]. *)
Lemma f_equiv_flip {A} (R : relation A) `{!PreOrder R} (f : A → A) :
  Proper (R ==> R) f → Proper (flip R ==> flip R) f.
Proof. intros ? ?? EQ. f_equiv. exact EQ. Qed.

Section f_equiv.
  Context `{!Equiv A, !Equiv B, !SubsetEq A}.

  Lemma f_equiv1 (fn : A → B) (x1 x2 : A) :
    Proper ((≡) ==> (≡)) fn →
    x1 ≡ x2 →
    fn x1 ≡ fn x2.
  Proof. intros. f_equiv. assumption. Qed.

  Lemma f_equiv2 (fn : A → B) (x1 x2 : A) :
    Proper ((⊆) ==> (≡)) fn →
    x1 ⊆ x2 →
    fn x1 ≡ fn x2.
  Proof. intros. f_equiv. assumption. Qed.

  (* Ensure that we prefer the ≡. *)
  Lemma f_equiv3 (fn : A → B) (x1 x2 : A) :
    Proper ((≡) ==> (≡)) fn →
    Proper ((⊆) ==> (≡)) fn →
    x1 ≡ x2 →
    fn x1 ≡ fn x2.
  Proof.
    (* The Coq tactic prefers the ⊆. *)
    intros. Morphisms.f_equiv. Fail assumption.
  Restart. Proof.
    intros. f_equiv. assumption.
  Qed.
End f_equiv.

(** Some tests for solve_proper (also testing f_equiv indirectly). *)

(** Test case for #161 *)
Lemma test_solve_proper_const {A} (R : relation A) `{!Equivalence R} x :
  Proper (R ==> R) (λ _, x).
Proof. solve_proper. Qed.

Lemma solve_proper_flip {A} (R : relation A) `{!PreOrder R} (f : A → A) :
  Proper (R ==> R) f → Proper (flip R ==> flip R) f.
Proof. solve_proper. Qed.

(* Test that [solve_proper_finish] uses [eassumption].
Think of [R] being Iris's [dist]. *)
Lemma solve_proper_finish_evar {A} (R : nat → relation A) (x y : A) :
  R 0 x y → ∃ n, R n x y.
Proof. intros. eexists. solve_proper. Qed.

(** This is a more realistic version of the previous test, showing how such
goals can arise for real. Needs to involve a subrelation so that the
[eassumption] in [solve_proper_finish] doesn't already do the whole job, i.e.,
we need the right mode for [SolveProperSubrelation]. *)
Lemma solve_proper_finish_evar' {A} (R1 R2 : nat → relation A) (f : A → nat) :
  (∀ n, subrelation (R2 n) (R1 n)) →
  (∀ n, Proper (R1 n ==> eq) f) →
  ∀ n, Proper (R2 n ==> eq) (λ x, S (f x)).
Proof.
  intros Hsub Hf. solve_proper_core ltac:(fun _ => eapply Hf || f_equiv).
Qed.

Definition option_rel {A} (R : relation A) (mx my : option A) :=
  match mx, my with
  | Some x, Some y => R x y
  | None, None => True
  | _, _ => False
  end.
Arguments option_rel : simpl never.
Lemma solve_proper_convertible {A} (R : relation A) (x y : A) :
  R x y → (option_rel R) (Some x) (Some y).
Proof.
  (* This needs [solve_proper] to use an assumption that doesn't syntactically
  seem to be about the same variables, but actually up to conversion it exactly
  matches the goal. *)
  intros R'. solve_proper.
Qed.

Section tests.
  Context {A B : Type} `{!Equiv A, !Equiv B}.
  Context (foo : A → A) (bar : A → B) (baz : B → A → A).
  Context `{!Proper ((≡) ==> (≡)) foo,
            !Proper ((≡) ==> (≡)) bar,
            !Proper ((≡) ==> (≡) ==> (≡)) baz}.

  Definition test1 (x : A) := baz (bar (foo x)) x.
  Goal Proper ((≡) ==> (≡)) test1.
  Proof. solve_proper. Qed.

  Definition test2 (b : bool) (x : A) :=
    if b then bar (foo x) else bar x.
  Goal ∀ b, Proper ((≡) ==> (≡)) (test2 b).
  Proof. solve_proper. Qed.

  Definition test3 (f : nat → A) :=
    baz (bar (f 0)) (f 2).
  Goal Proper (pointwise_relation nat (≡) ==> (≡)) test3.
  Proof. solve_proper. Qed.

  (* We mirror [discrete_fun] from Iris to have an equivalence on a function
  space. *)
  Definition discrete_fun {A} (B : A → Type) `{!∀ x, Equiv (B x)} := ∀ x : A, B x.
  Local Instance discrete_fun_equiv  {A} {B : A → Type} `{!∀ x, Equiv (B x)} :
      Equiv (discrete_fun B) :=
    λ f g, ∀ x, f x ≡ g x.
  Notation "A -d> B" :=
    (@discrete_fun A (λ _, B) _) (at level 99, B at level 200, right associativity).
  Definition test4 x (f : A -d> A) := f x.
  Goal ∀ x, Proper ((≡) ==> (≡)) (test4 x).
  Proof. solve_proper. Qed.

  Lemma test_subrelation1 (P Q : Prop) :
    Proper ((↔) ==> impl) id.
  Proof. solve_proper. Qed.

End tests.

(** The following tests are inspired by Iris's [ofe] structure (here, simplified
to just a type an arbitrary relation), and the discrete function space [A -d> B]
on a Type [A] and OFE [B]. The tests occur when proving [Proper]s for
higher-order functions, which typically occurs while defining functions using
Iris's [fixpoint] operator. *)
Record setoid :=
  Setoid { setoid_car :> Type; setoid_equiv : relation setoid_car }.
Arguments setoid_equiv {_} _ _.

Definition myfun (A : Type) (B : setoid) := A → B.
Definition myfun_equiv {A B} : relation (myfun A B) :=
  pointwise_relation _ setoid_equiv.
Definition myfunS (A : Type) (B : setoid) := Setoid (myfun A B) myfun_equiv.

Section setoid_tests.
  Context {A : setoid} (f : A → A) (h : A → A → A).
  Context `{!Proper (setoid_equiv ==> setoid_equiv) f,
            !Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) h}.

  Definition setoid_test1 (rec : myfunS nat A) : myfunS nat A :=
    λ n, h (f (rec n)) (rec n).
  Goal Proper (setoid_equiv ==> setoid_equiv) setoid_test1.
  Proof. solve_proper. Qed.

  Definition setoid_test2 (rec : myfunS nat (myfunS nat A)) : myfunS nat A :=
    λ n, h (f (rec n n)) (rec n n).
  Goal Proper (setoid_equiv ==> setoid_equiv) setoid_test2.
  Proof. solve_proper. Qed.

  Definition setoid_test3 (rec : myfunS nat A) : myfunS nat (myfunS nat A) :=
    λ n m, h (f (rec n)) (rec m).
  Goal Proper (setoid_equiv ==> setoid_equiv) setoid_test3.
  Proof. solve_proper. Qed.
End setoid_tests.

(** Regression tests for [naive_solver].
Requires a bunch of other tactics to work so it comes last in this file. *)
Lemma naive_solver_issue_115 (P : nat → Prop) (x : nat) :
  (∀ x', P x' → x' = 10) → P x → x + 1 = 11.
Proof. naive_solver. Qed.
