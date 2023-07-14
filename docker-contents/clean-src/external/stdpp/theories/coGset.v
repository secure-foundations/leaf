(** This file implements the type [coGset A] of finite/cofinite sets
of elements of any countable type [A].

Note that [coGset positive] cannot represent all elements of [coPset]
(e.g., [coPset_suffixes], [coPset_l], and [coPset_r] construct
infinite sets that cannot be represented). *)
From stdpp Require Export sets countable.
From stdpp Require Import decidable finite gmap coPset.
From stdpp Require Import options.

(* Pick up extra assumptions from section parameters. *)
Set Default Proof Using "Type*".

Inductive coGset `{Countable A} :=
  | FinGSet (X : gset A)
  | CoFinGset (X : gset A).
Global Arguments coGset _ {_ _} : assert.

Global Instance coGset_eq_dec `{Countable A} : EqDecision (coGset A).
Proof. solve_decision. Defined.
Global Instance coGset_countable `{Countable A} : Countable (coGset A).
Proof.
  apply (inj_countable'
    (λ X, match X with FinGSet X => inl X | CoFinGset X => inr X end)
    (λ s, match s with inl X => FinGSet X | inr X => CoFinGset X end)).
  by intros [].
Qed.

Section coGset.
  Context `{Countable A}.

  Global Instance coGset_elem_of : ElemOf A (coGset A) := λ x X,
    match X with FinGSet X => x ∈ X | CoFinGset X => x ∉ X end.
  Global Instance coGset_empty : Empty (coGset A) := FinGSet ∅.
  Global Instance coGset_top : Top (coGset A) := CoFinGset ∅.
  Global Instance coGset_singleton : Singleton A (coGset A) := λ x,
    FinGSet {[x]}.
  Global Instance coGset_union : Union (coGset A) := λ X Y,
    match X, Y with
    | FinGSet X, FinGSet Y => FinGSet (X ∪ Y)
    | CoFinGset X, CoFinGset Y => CoFinGset (X ∩ Y)
    | FinGSet X, CoFinGset Y => CoFinGset (Y ∖ X)
    | CoFinGset X, FinGSet Y => CoFinGset (X ∖ Y)
    end.
  Global Instance coGset_intersection : Intersection (coGset A) := λ X Y,
    match X, Y with
    | FinGSet X, FinGSet Y => FinGSet (X ∩ Y)
    | CoFinGset X, CoFinGset Y => CoFinGset (X ∪ Y)
    | FinGSet X, CoFinGset Y => FinGSet (X ∖ Y)
    | CoFinGset X, FinGSet Y => FinGSet (Y ∖ X)
    end.
  Global Instance coGset_difference : Difference (coGset A) := λ X Y,
    match X, Y with
    | FinGSet X, FinGSet Y => FinGSet (X ∖ Y)
    | CoFinGset X, CoFinGset Y => FinGSet (Y ∖ X)
    | FinGSet X, CoFinGset Y => FinGSet (X ∩ Y)
    | CoFinGset X, FinGSet Y => CoFinGset (X ∪ Y)
    end.

  Global Instance coGset_set : TopSet A (coGset A).
  Proof.
    split; [split; [split| |]|].
    - by intros ??.
    - intros x y. unfold elem_of, coGset_elem_of; simpl.
      by rewrite elem_of_singleton.
    - intros [X|X] [Y|Y] x; unfold elem_of, coGset_elem_of, coGset_union; simpl.
      + set_solver.
      + by rewrite not_elem_of_difference, (comm (∨)).
      + by rewrite not_elem_of_difference.
      + by rewrite not_elem_of_intersection.
    - intros [] [];
      unfold elem_of, coGset_elem_of, coGset_intersection; set_solver.
    - intros [X|X] [Y|Y] x;
      unfold elem_of, coGset_elem_of, coGset_difference; simpl.
      + set_solver.
      + rewrite elem_of_intersection. destruct (decide (x ∈ Y)); tauto.
      + set_solver.
      + rewrite elem_of_difference. destruct (decide (x ∈ Y)); tauto.
    - done.
  Qed.
End coGset.

Global Instance coGset_elem_of_dec `{Countable A} : RelDecision (∈@{coGset A}) :=
  λ x X,
  match X with
  | FinGSet X => decide_rel elem_of x X
  | CoFinGset X => not_dec (decide_rel elem_of x X)
  end.

Section infinite.
  Context `{Countable A, Infinite A}.

  Global Instance coGset_leibniz : LeibnizEquiv (coGset A).
  Proof.
    intros [X|X] [Y|Y]; rewrite set_equiv;
    unfold elem_of, coGset_elem_of; simpl; intros HXY.
    - f_equal. by apply leibniz_equiv.
    - by destruct (exist_fresh (X ∪ Y)) as [? [? ?%HXY]%not_elem_of_union].
    - by destruct (exist_fresh (X ∪ Y)) as [? [?%HXY ?]%not_elem_of_union].
    - f_equal. apply leibniz_equiv; intros x. by apply not_elem_of_iff.
  Qed.

  Global Instance coGset_equiv_dec : RelDecision (≡@{coGset A}).
  Proof.
    refine (λ X Y, cast_if (decide (X = Y))); abstract (by fold_leibniz).
  Defined.

  Global Instance coGset_disjoint_dec : RelDecision (##@{coGset A}).
  Proof.
    refine (λ X Y, cast_if (decide (X ∩ Y = ∅)));
      abstract (by rewrite disjoint_intersection_L).
  Defined.

  Global Instance coGset_subseteq_dec : RelDecision (⊆@{coGset A}).
  Proof.
    refine (λ X Y, cast_if (decide (X ∪ Y = Y)));
      abstract (by rewrite subseteq_union_L).
  Defined.

  Definition coGset_finite (X : coGset A) : bool :=
    match X with FinGSet _ => true | CoFinGset _ => false end.
  Lemma coGset_finite_spec X : set_finite X ↔ coGset_finite X.
  Proof.
    destruct X as [X|X];
    unfold set_finite, elem_of at 1, coGset_elem_of; simpl.
    - split; [done|intros _]. exists (elements X). set_solver.
    - split; [intros [Y HXY]%(pred_finite_set(C:=gset A))|done].
      by destruct (exist_fresh (X ∪ Y)) as [? [?%HXY ?]%not_elem_of_union].
  Qed.
  Global Instance coGset_finite_dec (X : coGset A) : Decision (set_finite X).
  Proof.
    refine (cast_if (decide (coGset_finite X)));
      abstract (by rewrite coGset_finite_spec).
  Defined.
End infinite.

(** * Pick elements from infinite sets *)
Definition coGpick `{Countable A, Infinite A} (X : coGset A) : A :=
  fresh (match X with FinGSet _ => ∅ | CoFinGset X => X end).

Lemma coGpick_elem_of `{Countable A, Infinite A} (X : coGset A) :
  ¬set_finite X → coGpick X ∈ X.
Proof.
  unfold coGpick.
  destruct X as [X|X]; rewrite coGset_finite_spec; simpl; [done|].
  by intros _; apply is_fresh.
Qed.

(** * Conversion to and from gset *)
Definition coGset_to_gset `{Countable A} (X : coGset A) : gset A :=
  match X with FinGSet X => X | CoFinGset _ => ∅ end.
Definition gset_to_coGset `{Countable A} : gset A → coGset A := FinGSet.

Section to_gset.
  Context `{Countable A}.

  Lemma elem_of_gset_to_coGset (X : gset A) x : x ∈ gset_to_coGset X ↔ x ∈ X.
  Proof. done. Qed.

  Context `{Infinite A}.

  Lemma elem_of_coGset_to_gset (X : coGset A) x :
    set_finite X → x ∈ coGset_to_gset X ↔ x ∈ X.
  Proof. rewrite coGset_finite_spec. by destruct X. Qed.
  Lemma gset_to_coGset_finite (X : gset A) : set_finite (gset_to_coGset X).
  Proof. by rewrite coGset_finite_spec. Qed.
End to_gset.

(** * Conversion to coPset *)
Definition coGset_to_coPset (X : coGset positive) : coPset :=
  match X with
  | FinGSet X => gset_to_coPset X
  | CoFinGset X => ⊤ ∖ gset_to_coPset X
  end.
Lemma elem_of_coGset_to_coPset X x : x ∈ coGset_to_coPset X ↔ x ∈ X.
Proof.
  destruct X as [X|X]; simpl.
  - by rewrite elem_of_gset_to_coPset.
  - by rewrite elem_of_difference, elem_of_gset_to_coPset, (left_id True (∧)).
Qed.

(** * Inefficient conversion to arbitrary sets with a top element *)
(** This shows that, when [A] is countable, [coGset A] is initial
among sets with [∪], [∩], [∖], [∅], [{[_]}], and [⊤]. *)
Definition coGset_to_top_set `{Countable A, Empty C, Singleton A C, Union C,
    Top C, Difference C} (X : coGset A) : C :=
  match X with
  | FinGSet X => list_to_set (elements X)
  | CoFinGset X => ⊤ ∖ list_to_set (elements X)
  end.
Lemma elem_of_coGset_to_top_set `{Countable A, TopSet A C} X x :
  x ∈@{C} coGset_to_top_set X ↔ x ∈ X.
Proof. destruct X; set_solver. Qed.

(** * Domain of finite maps *)
Global Instance coGset_dom `{Countable K} {A} : Dom (gmap K A) (coGset K) := λ m,
  gset_to_coGset (dom _ m).
Global Instance coGset_dom_spec `{Countable K} : FinMapDom K (gmap K) (coGset K).
Proof.
  split; try apply _. intros B m i. unfold dom, coGset_dom.
  by rewrite elem_of_gset_to_coGset, elem_of_dom.
Qed.

Typeclasses Opaque coGset_elem_of coGset_empty coGset_top coGset_singleton.
Typeclasses Opaque coGset_union coGset_intersection coGset_difference.
Typeclasses Opaque coGset_dom.
