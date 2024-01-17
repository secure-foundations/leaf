From Coq Require Export Ascii.
From stdpp Require Export strings.
From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
From Ltac2 Require Ltac2.

(** * Utility definitions used by the proofmode *)

(** ** N-ary tactics *)
(** Ltac1 does not provide primitives to manipulate lists (e.g., [ident_list],
[simple_intropattern_list]), needed for [iIntros], [iDestruct], etc. We can do
that in Ltac2. For most proofmode tactics we only need to iterate over a list
(either in forward or backward direction). The Ltac1 tactics [ltac1_list_iter]
and [ltac1_list_rev_iter] allow us to do that while encapsulating the Ltac2
code. These tactics can be used as:

  Ltac _iTactic xs :=
    ltac1_list_iter ltac:(fun x => /* stuff */) xs.
  Tactic Notation "iTactic" "(" ne_ident_list(xs) ")" :=
    _iTactic xs.

It is important to note that given one n-ary [Tactic Notation] we cannot call
another n-ary [Tactic Notation]. For example, the following does NOT work:

  Tactic Notation "iAnotherTactic" "(" ne_ident_list(xs) ")" :=
    /* stuff */
    iTactic (xs).

Because of this reason, as already shown above, we typically provide an [Ltac]
called [_iTactic] (note the underscore to mark it is "private"), and define the
[Tactic Notation] as a wrapper, allowing us to write:

  Tactic Notation "iAnotherTactic" "(" ne_ident_list(xs) ")" :=
    /* stuff */
    _iTactic xs.
*)

Ltac2 of_ltac1_list l := Option.get (Ltac1.to_list l).

Ltac ltac1_list_iter tac l :=
  let go := ltac2:(tac l |- List.iter (ltac1:(tac x |- tac x) tac)
                                      (of_ltac1_list l)) in
  go tac l.

Ltac ltac1_list_rev_iter tac l :=
  let go := ltac2:(tac l |- List.iter (ltac1:(tac x |- tac x) tac)
                                      (List.rev (of_ltac1_list l))) in
  go tac l.

(** Since the Ltac1-Ltac2 API only supports unit-returning functions, there is
no nice way to produce an empty list in ltac1. We therefore often define a
special version [_iTactic0] for the empty list. This version can be created
using [with_ltac1_nil]:

  Ltac _iTactic0 := with_ltac1_nil ltac:(fun xs => _iTactic xs)
*)
Ltac with_ltac1_nil tac :=
  let go := ltac2:(tac |- ltac1:(tac l |- tac l) tac (Ltac1.of_list [])) in
  go tac.

(* Directions of rewrites *)
Inductive direction := Left | Right.

Local Open Scope lazy_bool_scope.

(* Some specific versions of operations on strings, booleans, positive for the
proof mode. We need those so that we can make [cbv] unfold just them, but not
the actual operations that may appear in users' proofs. *)

Lemma lazy_andb_true (b1 b2 : bool) : b1 &&& b2 = true ↔ b1 = true ∧ b2 = true.
Proof. destruct b1, b2; intuition congruence. Qed.

Definition negb (b : bool) : bool := if b then false else true.
Lemma negb_true b : negb b = true ↔ b = false.
Proof. by destruct b. Qed.

Fixpoint Pos_succ (x : positive) : positive :=
  match x with
  | (p~1)%positive => ((Pos_succ p)~0)%positive
  | (p~0)%positive => (p~1)%positive
  | 1%positive => 2%positive
  end.

Definition beq (b1 b2 : bool) : bool :=
  match b1, b2 with
  | false, false | true, true => true
  | _, _ => false
  end.

Definition ascii_beq (x y : ascii) : bool :=
  let 'Ascii x1 x2 x3 x4 x5 x6 x7 x8 := x in
  let 'Ascii y1 y2 y3 y4 y5 y6 y7 y8 := y in
  beq x1 y1 &&& beq x2 y2 &&& beq x3 y3 &&& beq x4 y4 &&&
    beq x5 y5 &&& beq x6 y6 &&& beq x7 y7 &&& beq x8 y8.

Fixpoint string_beq (s1 s2 : string) : bool :=
  match s1, s2 with
  | "", "" => true
  | String a1 s1, String a2 s2 => ascii_beq a1 a2 &&& string_beq s1 s2
  | _, _ => false
  end.

Lemma beq_true b1 b2 : beq b1 b2 = true ↔ b1 = b2.
Proof. destruct b1, b2; simpl; intuition congruence. Qed.

Lemma ascii_beq_true x y : ascii_beq x y = true ↔ x = y.
Proof.
  destruct x, y; rewrite /= !lazy_andb_true !beq_true. intuition congruence.
Qed.

Lemma string_beq_true s1 s2 : string_beq s1 s2 = true ↔ s1 = s2.
Proof.
  revert s2. induction s1 as [|x s1 IH]=> -[|y s2] //=.
  rewrite lazy_andb_true ascii_beq_true IH. intuition congruence.
Qed.

Lemma string_beq_reflect s1 s2 : reflect (s1 = s2) (string_beq s1 s2).
Proof. apply iff_reflect. by rewrite string_beq_true. Qed.

Module Export ident.
Inductive ident :=
  | IAnon : positive → ident
  | INamed :> string → ident.
End ident.

Global Instance maybe_IAnon : Maybe IAnon := λ i,
  match i with IAnon n => Some n | _ => None end.
Global Instance maybe_INamed : Maybe INamed := λ i,
  match i with INamed s => Some s | _ => None end.

Global Instance beq_eq_dec : EqDecision ident.
Proof. solve_decision. Defined.

Definition positive_beq := Eval compute in Pos.eqb.

Lemma positive_beq_true x y : positive_beq x y = true ↔ x = y.
Proof. apply Pos.eqb_eq. Qed.

Definition ident_beq (i1 i2 : ident) : bool :=
  match i1, i2 with
  | IAnon n1, IAnon n2 => positive_beq n1 n2
  | INamed s1, INamed s2 => string_beq s1 s2
  | _, _ => false
  end.

Lemma ident_beq_true i1 i2 : ident_beq i1 i2 = true ↔ i1 = i2.
Proof.
  destruct i1, i2; rewrite /= ?string_beq_true ?positive_beq_true; naive_solver.
Qed.

Lemma ident_beq_reflect i1 i2 : reflect (i1 = i2) (ident_beq i1 i2).
Proof. apply iff_reflect. by rewrite ident_beq_true. Qed.

(** Copies of some functions on [list] and [option] for better reduction control. *)
Fixpoint pm_app {A} (l1 l2 : list A) : list A :=
  match l1 with [] => l2 | x :: l1 => x :: pm_app l1 l2 end.

Definition pm_option_bind {A B} (f : A → option B) (mx : option A) : option B :=
  match mx with Some x => f x | None => None end.
Global Arguments pm_option_bind {_ _} _ !_ /.

Definition pm_from_option {A B} (f : A → B) (y : B) (mx : option A) : B :=
  match mx with None => y | Some x => f x end.
Global Arguments pm_from_option {_ _} _ _ !_ /.

Definition pm_option_fun {A B} (f : option (A → B)) (x : A) : option B :=
  match f with None => None | Some f => Some (f x) end.
Global Arguments pm_option_fun {_ _} !_ _ /.

(* Can't write [id] here as that would not reduce. *)
Notation pm_default := (pm_from_option (λ x, x)).
