(** This file collects general purpose definitions and theorems on lists that
are not in the Coq standard library. *)
From Coq Require Export Permutation.
From stdpp Require Export numbers base option.
From stdpp Require Import options.

Global Arguments length {_} _ : assert.
Global Arguments cons {_} _ _ : assert.
Global Arguments app {_} _ _ : assert.

Global Instance: Params (@length) 1 := {}.
Global Instance: Params (@cons) 1 := {}.
Global Instance: Params (@app) 1 := {}.

(** [head] and [tail] are defined as [parsing only] for [hd_error] and [tl] in
the Coq standard library. We redefine these notations to make sure they also
pretty print properly. *)
Notation head := hd_error.
Notation tail := tl.

Notation take := firstn.
Notation drop := skipn.

Global Arguments head {_} _ : assert.
Global Arguments tail {_} _ : assert.

Global Arguments take {_} !_ !_ / : assert.
Global Arguments drop {_} !_ !_ / : assert.

Global Instance: Params (@head) 1 := {}.
Global Instance: Params (@tail) 1 := {}.
Global Instance: Params (@take) 1 := {}.
Global Instance: Params (@drop) 1 := {}.
Global Instance: Params (@Forall) 1 := {}.
Global Instance: Params (@Exists) 1 := {}.
Global Instance: Params (@NoDup) 1 := {}.

Global Arguments Permutation {_} _ _ : assert.
Global Arguments Forall_cons {_} _ _ _ _ _ : assert.

Notation "(::)" := cons (only parsing) : list_scope.
Notation "( x ::.)" := (cons x) (only parsing) : list_scope.
Notation "(.:: l )" := (λ x, cons x l) (only parsing) : list_scope.
Notation "(++)" := app (only parsing) : list_scope.
Notation "( l ++.)" := (app l) (only parsing) : list_scope.
Notation "(.++ k )" := (λ l, app l k) (only parsing) : list_scope.

Infix "≡ₚ" := Permutation (at level 70, no associativity) : stdpp_scope.
Notation "(≡ₚ)" := Permutation (only parsing) : stdpp_scope.
Notation "( x ≡ₚ.)" := (Permutation x) (only parsing) : stdpp_scope.
Notation "(.≡ₚ x )" := (λ y, y ≡ₚ x) (only parsing) : stdpp_scope.
Notation "(≢ₚ)" := (λ x y, ¬x ≡ₚ y) (only parsing) : stdpp_scope.
Notation "x ≢ₚ y":= (¬x ≡ₚ y) (at level 70, no associativity) : stdpp_scope.
Notation "( x ≢ₚ.)" := (λ y, x ≢ₚ y) (only parsing) : stdpp_scope.
Notation "(.≢ₚ x )" := (λ y, y ≢ₚ x) (only parsing) : stdpp_scope.

Infix "≡ₚ@{ A }" :=
  (@Permutation A) (at level 70, no associativity, only parsing) : stdpp_scope.
Notation "(≡ₚ@{ A } )" := (@Permutation A) (only parsing) : stdpp_scope.

Global Instance maybe_cons {A} : Maybe2 (@cons A) := λ l,
  match l with x :: l => Some (x,l) | _ => None end.

(** * Definitions *)
(** Setoid equality lifted to lists *)
Inductive list_equiv `{Equiv A} : Equiv (list A) :=
  | nil_equiv : [] ≡ []
  | cons_equiv x y l k : x ≡ y → l ≡ k → x :: l ≡ y :: k.
Global Existing Instance list_equiv.

(** The operation [l !! i] gives the [i]th element of the list [l], or [None]
in case [i] is out of bounds. *)
Global Instance list_lookup {A} : Lookup nat A (list A) :=
  fix go i l {struct l} : option A := let _ : Lookup _ _ _ := @go in
  match l with
  | [] => None | x :: l => match i with 0 => Some x | S i => l !! i end
  end.

(** The operation [l !!! i] is a total version of the lookup operation
[l !! i]. *)
Global Instance list_lookup_total `{!Inhabited A} : LookupTotal nat A (list A) :=
  fix go i l {struct l} : A := let _ : LookupTotal _ _ _ := @go in
  match l with
  | [] => inhabitant
  | x :: l => match i with 0 => x | S i => l !!! i end
  end.

(** The operation [alter f i l] applies the function [f] to the [i]th element
of [l]. In case [i] is out of bounds, the list is returned unchanged. *)
Global Instance list_alter {A} : Alter nat A (list A) := λ f,
  fix go i l {struct l} :=
  match l with
  | [] => []
  | x :: l => match i with 0 => f x :: l | S i => x :: go i l end
  end.

(** The operation [<[i:=x]> l] overwrites the element at position [i] with the
value [x]. In case [i] is out of bounds, the list is returned unchanged. *)
Global Instance list_insert {A} : Insert nat A (list A) :=
  fix go i y l {struct l} := let _ : Insert _ _ _ := @go in
  match l with
  | [] => []
  | x :: l => match i with 0 => y :: l | S i => x :: <[i:=y]>l end
  end.
Fixpoint list_inserts {A} (i : nat) (k l : list A) : list A :=
  match k with
  | [] => l
  | y :: k => <[i:=y]>(list_inserts (S i) k l)
  end.
Global Instance: Params (@list_inserts) 1 := {}.

(** The operation [delete i l] removes the [i]th element of [l] and moves
all consecutive elements one position ahead. In case [i] is out of bounds,
the list is returned unchanged. *)
Global Instance list_delete {A} : Delete nat (list A) :=
  fix go (i : nat) (l : list A) {struct l} : list A :=
  match l with
  | [] => []
  | x :: l => match i with 0 => l | S i => x :: @delete _ _ go i l end
  end.

(** The function [option_list o] converts an element [Some x] into the
singleton list [[x]], and [None] into the empty list [[]]. *)
Definition option_list {A} : option A → list A := option_rect _ (λ x, [x]) [].
Global Instance: Params (@option_list) 1 := {}.
Global Instance maybe_list_singleton {A} : Maybe (λ x : A, [x]) := λ l,
  match l with [x] => Some x | _ => None end.

(** The function [filter P l] returns the list of elements of [l] that
satisfies [P]. The order remains unchanged. *)
Global Instance list_filter {A} : Filter A (list A) :=
  fix go P _ l := let _ : Filter _ _ := @go in
  match l with
  | [] => []
  | x :: l => if decide (P x) then x :: filter P l else filter P l
  end.

(** The function [list_find P l] returns the first index [i] whose element
satisfies the predicate [P]. *)
Definition list_find {A} P `{∀ x, Decision (P x)} : list A → option (nat * A) :=
  fix go l :=
  match l with
  | [] => None
  | x :: l => if decide (P x) then Some (0,x) else prod_map S id <$> go l
  end.
Global Instance: Params (@list_find) 3 := {}.

(** The function [replicate n x] generates a list with length [n] of elements
with value [x]. *)
Fixpoint replicate {A} (n : nat) (x : A) : list A :=
  match n with 0 => [] | S n => x :: replicate n x end.
Global Instance: Params (@replicate) 2 := {}.

(** The function [rotate n l] rotates the list [l] by [n], e.g., [rotate 1
[x0; x1; ...; xm]] becomes [x1; ...; xm; x0]. Rotating by a multiple of
[length l] is the identity function. **)
Definition rotate {A} (n : nat) (l : list A) : list A :=
  drop (n `mod` length l) l ++ take (n `mod` length l) l.
Global Instance: Params (@rotate) 2 := {}.

(** The function [rotate_take s e l] returns the range between the
indices [s] (inclusive) and [e] (exclusive) of [l]. If [e ≤ s], all
elements after [s] and before [e] are returned. *)
Definition rotate_take {A} (s e : nat) (l : list A) : list A :=
  take (rotate_nat_sub s e (length l)) (rotate s l).
Global Instance: Params (@rotate_take) 3 := {}.

(** The function [reverse l] returns the elements of [l] in reverse order. *)
Definition reverse {A} (l : list A) : list A := rev_append l [].
Global Instance: Params (@reverse) 1 := {}.

(** The function [last l] returns the last element of the list [l], or [None]
if the list [l] is empty. *)
Fixpoint last {A} (l : list A) : option A :=
  match l with [] => None | [x] => Some x | _ :: l => last l end.
Global Instance: Params (@last) 1 := {}.
Global Arguments last : simpl nomatch.

(** The function [resize n y l] takes the first [n] elements of [l] in case
[length l ≤ n], and otherwise appends elements with value [x] to [l] to obtain
a list of length [n]. *)
Fixpoint resize {A} (n : nat) (y : A) (l : list A) : list A :=
  match l with
  | [] => replicate n y
  | x :: l => match n with 0 => [] | S n => x :: resize n y l end
  end.
Global Arguments resize {_} !_ _ !_ : assert.
Global Instance: Params (@resize) 2 := {}.

(** The function [reshape k l] transforms [l] into a list of lists whose sizes
are specified by [k]. In case [l] is too short, the resulting list will be
padded with empty lists. In case [l] is too long, it will be truncated. *)
Fixpoint reshape {A} (szs : list nat) (l : list A) : list (list A) :=
  match szs with
  | [] => [] | sz :: szs => take sz l :: reshape szs (drop sz l)
  end.
Global Instance: Params (@reshape) 2 := {}.

Definition sublist_lookup {A} (i n : nat) (l : list A) : option (list A) :=
  guard (i + n ≤ length l); Some (take n (drop i l)).
Definition sublist_alter {A} (f : list A → list A)
    (i n : nat) (l : list A) : list A :=
  take i l ++ f (take n (drop i l)) ++ drop (i + n) l.

(** Functions to fold over a list. We redefine [foldl] with the arguments in
the same order as in Haskell. *)
Notation foldr := fold_right.
Definition foldl {A B} (f : A → B → A) : A → list B → A :=
  fix go a l := match l with [] => a | x :: l => go (f a x) l end.

(** The monadic operations. *)
Global Instance list_ret: MRet list := λ A x, x :: @nil A.
Global Instance list_fmap : FMap list := λ A B f,
  fix go (l : list A) := match l with [] => [] | x :: l => f x :: go l end.
Global Instance list_omap : OMap list := λ A B f,
  fix go (l : list A) :=
  match l with
  | [] => []
  | x :: l => match f x with Some y => y :: go l | None => go l end
  end.
Global Instance list_bind : MBind list := λ A B f,
  fix go (l : list A) := match l with [] => [] | x :: l => f x ++ go l end.
Global Instance list_join: MJoin list :=
  fix go A (ls : list (list A)) : list A :=
  match ls with [] => [] | l :: ls => l ++ @mjoin _ go _ ls end.

Definition mapM `{MBind M, MRet M} {A B} (f : A → M B) : list A → M (list B) :=
  fix go l :=
  match l with [] => mret [] | x :: l => y ← f x; k ← go l; mret (y :: k) end.
Global Instance: Params (@mapM) 5 := {}.

(** We define stronger variants of the map function that allow the mapped
function to use the index of the elements. *)
Fixpoint imap {A B} (f : nat → A → B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: l => f 0 x :: imap (f ∘ S) l
  end.
Global Instance: Params (@imap) 2 := {}.

Definition zipped_map {A B} (f : list A → list A → A → B) :
    list A → list A → list B := fix go l k :=
  match k with
  | [] => []
  | x :: k => f l k x :: go (x :: l) k
  end.
Global Instance: Params (@zipped_map) 2 := {}.

Fixpoint imap2 {A B C} (f : nat → A → B → C) (l : list A) (k : list B) : list C :=
  match l, k with
  | [], _ | _, [] => []
  | x :: l, y :: k => f 0 x y :: imap2 (f ∘ S) l k
  end.
Global Instance: Params (@imap2) 3 := {}.

Inductive zipped_Forall {A} (P : list A → list A → A → Prop) :
    list A → list A → Prop :=
  | zipped_Forall_nil l : zipped_Forall P l []
  | zipped_Forall_cons l k x :
     P l k x → zipped_Forall P (x :: l) k → zipped_Forall P l (x :: k).
Global Arguments zipped_Forall_nil {_ _} _ : assert.
Global Arguments zipped_Forall_cons {_ _} _ _ _ _ _ : assert.

(** The function [mask f βs l] applies the function [f] to elements in [l] at
positions that are [true] in [βs]. *)
Fixpoint mask {A} (f : A → A) (βs : list bool) (l : list A) : list A :=
  match βs, l with
  | β :: βs, x :: l => (if β then f x else x) :: mask f βs l
  | _, _ => l
  end.

(** The function [permutations l] yields all permutations of [l]. *)
Fixpoint interleave {A} (x : A) (l : list A) : list (list A) :=
  match l with
  | [] => [[x]]| y :: l => (x :: y :: l) :: ((y ::.) <$> interleave x l)
  end.
Fixpoint permutations {A} (l : list A) : list (list A) :=
  match l with [] => [[]] | x :: l => permutations l ≫= interleave x end.

(** The predicate [suffix] holds if the first list is a suffix of the second.
The predicate [prefix] holds if the first list is a prefix of the second. *)
Definition suffix {A} : relation (list A) := λ l1 l2, ∃ k, l2 = k ++ l1.
Definition prefix {A} : relation (list A) := λ l1 l2, ∃ k, l2 = l1 ++ k.
Infix "`suffix_of`" := suffix (at level 70) : stdpp_scope.
Infix "`prefix_of`" := prefix (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ `prefix_of` _) => reflexivity : core.
Global Hint Extern 0 (_ `suffix_of` _) => reflexivity : core.

Section prefix_suffix_ops.
  Context `{EqDecision A}.

  Definition max_prefix : list A → list A → list A * list A * list A :=
    fix go l1 l2 :=
    match l1, l2 with
    | [], l2 => ([], l2, [])
    | l1, [] => (l1, [], [])
    | x1 :: l1, x2 :: l2 =>
      if decide_rel (=) x1 x2
      then prod_map id (x1 ::.) (go l1 l2) else (x1 :: l1, x2 :: l2, [])
    end.
  Definition max_suffix (l1 l2 : list A) : list A * list A * list A :=
    match max_prefix (reverse l1) (reverse l2) with
    | (k1, k2, k3) => (reverse k1, reverse k2, reverse k3)
    end.
  Definition strip_prefix (l1 l2 : list A) := (max_prefix l1 l2).1.2.
  Definition strip_suffix (l1 l2 : list A) := (max_suffix l1 l2).1.2.
End prefix_suffix_ops.

(** A list [l1] is a sublist of [l2] if [l2] is obtained by removing elements
from [l1] without changing the order. *)
Inductive sublist {A} : relation (list A) :=
  | sublist_nil : sublist [] []
  | sublist_skip x l1 l2 : sublist l1 l2 → sublist (x :: l1) (x :: l2)
  | sublist_cons x l1 l2 : sublist l1 l2 → sublist l1 (x :: l2).
Infix "`sublist_of`" := sublist (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ `sublist_of` _) => reflexivity : core.

(** A list [l2] submseteq a list [l1] if [l2] is obtained by removing elements
from [l1] while possiblity changing the order. *)
Inductive submseteq {A} : relation (list A) :=
  | submseteq_nil : submseteq [] []
  | submseteq_skip x l1 l2 : submseteq l1 l2 → submseteq (x :: l1) (x :: l2)
  | submseteq_swap x y l : submseteq (y :: x :: l) (x :: y :: l)
  | submseteq_cons x l1 l2 : submseteq l1 l2 → submseteq l1 (x :: l2)
  | submseteq_trans l1 l2 l3 : submseteq l1 l2 → submseteq l2 l3 → submseteq l1 l3.
Infix "⊆+" := submseteq (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ ⊆+ _) => reflexivity : core.

(** Removes [x] from the list [l]. The function returns a [Some] when the
removal succeeds and [None] when [x] is not in [l]. *)
Fixpoint list_remove `{EqDecision A} (x : A) (l : list A) : option (list A) :=
  match l with
  | [] => None
  | y :: l => if decide (x = y) then Some l else (y ::.) <$> list_remove x l
  end.

(** Removes all elements in the list [k] from the list [l]. The function returns
a [Some] when the removal succeeds and [None] some element of [k] is not in [l]. *)
Fixpoint list_remove_list `{EqDecision A} (k : list A) (l : list A) : option (list A) :=
  match k with
  | [] => Some l | x :: k => list_remove x l ≫= list_remove_list k
  end.

Inductive Forall3 {A B C} (P : A → B → C → Prop) :
     list A → list B → list C → Prop :=
  | Forall3_nil : Forall3 P [] [] []
  | Forall3_cons x y z l k k' :
     P x y z → Forall3 P l k k' → Forall3 P (x :: l) (y :: k) (z :: k').

(** Set operations on lists *)
Global Instance list_subseteq {A} : SubsetEq (list A) := λ l1 l2, ∀ x, x ∈ l1 → x ∈ l2.

Section list_set.
  Context `{dec : EqDecision A}.
  Global Instance elem_of_list_dec : RelDecision (∈@{list A}).
  Proof using Type*.
   refine (
    fix go x l :=
    match l return Decision (x ∈ l) with
    | [] => right _
    | y :: l => cast_if_or (decide (x = y)) (go x l)
    end); clear go dec; subst; try (by constructor); abstract by inversion 1.
  Defined.
  Fixpoint remove_dups (l : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x l then remove_dups l else x :: remove_dups l
    end.
  Fixpoint list_difference (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then list_difference l k else x :: list_difference l k
    end.
  Definition list_union (l k : list A) : list A := list_difference l k ++ k.
  Fixpoint list_intersection (l k : list A) : list A :=
    match l with
    | [] => []
    | x :: l =>
      if decide_rel (∈) x k
      then x :: list_intersection l k else list_intersection l k
    end.
  Definition list_intersection_with (f : A → A → option A) :
    list A → list A → list A := fix go l k :=
    match l with
    | [] => []
    | x :: l => foldr (λ y,
        match f x y with None => id | Some z => (z ::.) end) (go l k) k
    end.
End list_set.

(** These next functions allow to efficiently encode lists of positives (bit
strings) into a single positive and go in the other direction as well. This is
for example used for the countable instance of lists and in namespaces.
 The main functions are [positives_flatten] and [positives_unflatten]. *)
Fixpoint positives_flatten_go (xs : list positive) (acc : positive) : positive :=
  match xs with
  | [] => acc
  | x :: xs => positives_flatten_go xs (acc~1~0 ++ Pos.reverse (Pos.dup x))
  end.

(** Flatten a list of positives into a single positive by duplicating the bits
of each element, so that:

- [0 -> 00]
- [1 -> 11]

and then separating each element with [10]. *)
Definition positives_flatten (xs : list positive) : positive :=
  positives_flatten_go xs 1.

Fixpoint positives_unflatten_go
        (p : positive)
        (acc_xs : list positive)
        (acc_elm : positive)
  : option (list positive) :=
  match p with
  | 1 => Some acc_xs
  | p'~0~0 => positives_unflatten_go p' acc_xs (acc_elm~0)
  | p'~1~1 => positives_unflatten_go p' acc_xs (acc_elm~1)
  | p'~1~0 => positives_unflatten_go p' (acc_elm :: acc_xs) 1
  | _ => None
  end%positive.

(** Unflatten a positive into a list of positives, assuming the encoding
used by [positives_flatten]. *)
Definition positives_unflatten (p : positive) : option (list positive) :=
  positives_unflatten_go p [] 1.

(** * Basic tactics on lists *)
(** The tactic [discriminate_list] discharges a goal if it submseteq
a list equality involving [(::)] and [(++)] of two lists that have a different
length as one of its hypotheses. *)
Tactic Notation "discriminate_list" hyp(H) :=
  apply (f_equal length) in H;
  repeat (csimpl in H || rewrite app_length in H); exfalso; lia.
Tactic Notation "discriminate_list" :=
  match goal with H : _ =@{list _} _ |- _ => discriminate_list H end.

(** The tactic [simplify_list_eq] simplifies hypotheses involving
equalities on lists using injectivity of [(::)] and [(++)]. Also, it simplifies
lookups in singleton lists. *)
Lemma app_inj_1 {A} (l1 k1 l2 k2 : list A) :
  length l1 = length k1 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof. revert k1. induction l1; intros [|??]; naive_solver. Qed.
Lemma app_inj_2 {A} (l1 k1 l2 k2 : list A) :
  length l2 = length k2 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof.
  intros ? Hl. apply app_inj_1; auto.
  apply (f_equal length) in Hl. rewrite !app_length in Hl. lia.
Qed.
Ltac simplify_list_eq :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : _ ++ _ = _ ++ _ |- _ => first
    [ apply app_inv_head in H | apply app_inv_tail in H
    | apply app_inj_1 in H; [destruct H|done]
    | apply app_inj_2 in H; [destruct H|done] ]
  | H : [?x] !! ?i = Some ?y |- _ =>
    destruct i; [change (Some x = Some y) in H | discriminate]
  end.

(** * General theorems *)
Section general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

Global Instance cons_eq_inj : Inj2 (=) (=) (=) (@cons A).
Proof. by injection 1. Qed.

Global Instance: ∀ k, Inj (=) (=) (k ++.).
Proof. intros ???. apply app_inv_head. Qed.
Global Instance: ∀ k, Inj (=) (=) (.++ k).
Proof. intros ???. apply app_inv_tail. Qed.
Global Instance: Assoc (=) (@app A).
Proof. intros ???. apply app_assoc. Qed.
Global Instance: LeftId (=) [] (@app A).
Proof. done. Qed.
Global Instance: RightId (=) [] (@app A).
Proof. intro. apply app_nil_r. Qed.

Lemma app_nil l1 l2 : l1 ++ l2 = [] ↔ l1 = [] ∧ l2 = [].
Proof. split; [apply app_eq_nil|]. by intros [-> ->]. Qed.
Lemma app_singleton l1 l2 x :
  l1 ++ l2 = [x] ↔ l1 = [] ∧ l2 = [x] ∨ l1 = [x] ∧ l2 = [].
Proof. split; [apply app_eq_unit|]. by intros [[-> ->]|[-> ->]]. Qed.
Lemma cons_middle x l1 l2 : l1 ++ x :: l2 = l1 ++ [x] ++ l2.
Proof. done. Qed.
Lemma list_eq l1 l2 : (∀ i, l1 !! i = l2 !! i) → l1 = l2.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] H.
  - done.
  - discriminate (H 0).
  - discriminate (H 0).
  - f_equal; [by injection (H 0)|]. apply (IH _ $ λ i, H (S i)).
Qed.
Global Instance list_eq_dec {dec : EqDecision A} : EqDecision (list A) :=
  list_eq_dec dec.
Global Instance list_eq_nil_dec l : Decision (l = []).
Proof. by refine match l with [] => left _ | _ => right _ end. Defined.
Lemma list_singleton_reflect l :
  option_reflect (λ x, l = [x]) (length l ≠ 1) (maybe (λ x, [x]) l).
Proof. by destruct l as [|? []]; constructor. Defined.

Lemma list_eq_Forall2 l1 l2 : l1 = l2 ↔ Forall2 eq l1 l2.
Proof.
  split.
  - intros <-. induction l1; eauto using Forall2.
  - induction 1; naive_solver.
Qed.

Definition nil_length : length (@nil A) = 0 := eq_refl.
Definition cons_length x l : length (x :: l) = S (length l) := eq_refl.
Lemma nil_or_length_pos l : l = [] ∨ length l ≠ 0.
Proof. destruct l; simpl; auto with lia. Qed.
Lemma nil_length_inv l : length l = 0 → l = [].
Proof. by destruct l. Qed.
Lemma lookup_cons_ne_0 l x i : i ≠ 0 → (x :: l) !! i = l !! pred i.
Proof. by destruct i. Qed.
Lemma lookup_total_cons_ne_0 `{!Inhabited A} l x i :
  i ≠ 0 → (x :: l) !!! i = l !!! pred i.
Proof. by destruct i. Qed.
Lemma lookup_nil i : @nil A !! i = None.
Proof. by destruct i. Qed.
Lemma lookup_total_nil `{!Inhabited A} i : @nil A !!! i = inhabitant.
Proof. by destruct i. Qed.
Lemma lookup_tail l i : tail l !! i = l !! S i.
Proof. by destruct l. Qed.
Lemma lookup_total_tail `{!Inhabited A} l i : tail l !!! i = l !!! S i.
Proof. by destruct l. Qed.
Lemma lookup_lt_Some l i x : l !! i = Some x → i < length l.
Proof. revert i. induction l; intros [|?] ?; naive_solver auto with arith. Qed.
Lemma lookup_lt_is_Some_1 l i : is_Some (l !! i) → i < length l.
Proof. intros [??]; eauto using lookup_lt_Some. Qed.
Lemma lookup_lt_is_Some_2 l i : i < length l → is_Some (l !! i).
Proof. revert i. induction l; intros [|?] ?; naive_solver auto with lia. Qed.
Lemma lookup_lt_is_Some l i : is_Some (l !! i) ↔ i < length l.
Proof. split; auto using lookup_lt_is_Some_1, lookup_lt_is_Some_2. Qed.
Lemma lookup_ge_None l i : l !! i = None ↔ length l ≤ i.
Proof. rewrite eq_None_not_Some, lookup_lt_is_Some. lia. Qed.
Lemma lookup_ge_None_1 l i : l !! i = None → length l ≤ i.
Proof. by rewrite lookup_ge_None. Qed.
Lemma lookup_ge_None_2 l i : length l ≤ i → l !! i = None.
Proof. by rewrite lookup_ge_None. Qed.

Lemma list_eq_same_length l1 l2 n :
  length l2 = n → length l1 = n →
  (∀ i x y, i < n → l1 !! i = Some x → l2 !! i = Some y → x = y) → l1 = l2.
Proof.
  intros <- Hlen Hl; apply list_eq; intros i. destruct (l2 !! i) as [x|] eqn:Hx.
  - destruct (lookup_lt_is_Some_2 l1 i) as [y Hy].
    { rewrite Hlen; eauto using lookup_lt_Some. }
    rewrite Hy; f_equal; apply (Hl i); eauto using lookup_lt_Some.
  - by rewrite lookup_ge_None, Hlen, <-lookup_ge_None.
Qed.

Lemma nth_lookup l i d : nth i l d = default d (l !! i).
Proof. revert i. induction l as [|x l IH]; intros [|i]; simpl; auto. Qed.
Lemma nth_lookup_Some l i d x : l !! i = Some x → nth i l d = x.
Proof. rewrite nth_lookup. by intros ->. Qed.
Lemma nth_lookup_or_length l i d : {l !! i = Some (nth i l d)} + {length l ≤ i}.
Proof.
  rewrite nth_lookup. destruct (l !! i) eqn:?; eauto using lookup_ge_None_1.
Qed.

Lemma list_lookup_total_alt `{!Inhabited A} l i :
  l !!! i = default inhabitant (l !! i).
Proof. revert i. induction l; intros []; naive_solver. Qed.
Lemma list_lookup_total_correct `{!Inhabited A} l i x :
  l !! i = Some x → l !!! i = x.
Proof. rewrite list_lookup_total_alt. by intros ->. Qed.
Lemma list_lookup_lookup_total `{!Inhabited A} l i :
  is_Some (l !! i) → l !! i = Some (l !!! i).
Proof. rewrite list_lookup_total_alt; by intros [x ->]. Qed.
Lemma list_lookup_lookup_total_lt `{!Inhabited A} l i :
  i < length l → l !! i = Some (l !!! i).
Proof. intros ?. by apply list_lookup_lookup_total, lookup_lt_is_Some_2. Qed.
Lemma list_lookup_alt `{!Inhabited A} l i x :
  l !! i = Some x ↔ i < length l ∧ l !!! i = x.
Proof.
  naive_solver eauto using list_lookup_lookup_total_lt,
    list_lookup_total_correct, lookup_lt_Some.
Qed.

Lemma lookup_app l1 l2 i :
  (l1 ++ l2) !! i =
    match l1 !! i with Some x => Some x | None => l2 !! (i - length l1) end.
Proof. revert i. induction l1 as [|x l1 IH]; intros [|i]; naive_solver. Qed.
Lemma lookup_app_l l1 l2 i : i < length l1 → (l1 ++ l2) !! i = l1 !! i.
Proof. rewrite lookup_app. by intros [? ->]%lookup_lt_is_Some. Qed.
Lemma lookup_total_app_l `{!Inhabited A} l1 l2 i :
  i < length l1 → (l1 ++ l2) !!! i = l1 !!! i.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_app_l. Qed.
Lemma lookup_app_l_Some l1 l2 i x : l1 !! i = Some x → (l1 ++ l2) !! i = Some x.
Proof. rewrite lookup_app. by intros ->. Qed.
Lemma lookup_app_r l1 l2 i :
  length l1 ≤ i → (l1 ++ l2) !! i = l2 !! (i - length l1).
Proof. rewrite lookup_app. by intros ->%lookup_ge_None. Qed.
Lemma lookup_total_app_r `{!Inhabited A} l1 l2 i :
  length l1 ≤ i → (l1 ++ l2) !!! i = l2 !!! (i - length l1).
Proof. intros. by rewrite !list_lookup_total_alt, lookup_app_r. Qed.
Lemma lookup_app_Some l1 l2 i x :
  (l1 ++ l2) !! i = Some x ↔
    l1 !! i = Some x ∨ length l1 ≤ i ∧ l2 !! (i - length l1) = Some x.
Proof.
  rewrite lookup_app. destruct (l1 !! i) eqn:Hi.
  - apply lookup_lt_Some in Hi. naive_solver lia.
  - apply lookup_ge_None in Hi. naive_solver lia.
Qed.

Lemma lookup_cons x l i :
  (x :: l) !! i =
    match i with 0 => Some x | S i => l !! i end.
Proof. reflexivity. Qed.
Lemma lookup_cons_Some x l i y :
  (x :: l) !! i = Some y ↔
    (i = 0 ∧ x = y) ∨ (1 ≤ i ∧ l !! (i - 1) = Some y).
Proof.
  rewrite lookup_cons. destruct i as [|i].
  - naive_solver lia.
  - replace (S i - 1) with i by lia. naive_solver lia.
Qed.

Lemma list_lookup_singleton x i :
  [x] !! i =
    match i with 0 => Some x | S _ => None end.
Proof. reflexivity. Qed.
Lemma list_lookup_singleton_Some x i y :
  [x] !! i = Some y ↔ i = 0 ∧ x = y.
Proof. rewrite lookup_cons_Some. naive_solver. Qed.

Lemma lookup_snoc_Some x l i y :
  (l ++ [x]) !! i = Some y ↔
    (i < length l ∧ l !! i = Some y) ∨ (i = length l ∧ x = y).
Proof.
  rewrite lookup_app_Some, list_lookup_singleton_Some.
  naive_solver auto using lookup_lt_is_Some_1 with lia.
Qed.

Lemma list_lookup_middle l1 l2 x n :
  n = length l1 → (l1 ++ x :: l2) !! n = Some x.
Proof. intros ->. by induction l1. Qed.
Lemma list_lookup_total_middle `{!Inhabited A} l1 l2 x n :
  n = length l1 → (l1 ++ x :: l2) !!! n = x.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_middle. Qed.

Lemma list_insert_alter l i x : <[i:=x]>l = alter (λ _, x) i l.
Proof. by revert i; induction l; intros []; intros; f_equal/=. Qed.
Lemma alter_length f l i : length (alter f i l) = length l.
Proof. revert i. by induction l; intros [|?]; f_equal/=. Qed.
Lemma insert_length l i x : length (<[i:=x]>l) = length l.
Proof. revert i. by induction l; intros [|?]; f_equal/=. Qed.
Lemma list_lookup_alter f l i : alter f i l !! i = f <$> l !! i.
Proof.
  revert i.
  induction l as [|?? IHl]; [done|].
  intros [|i]; [done|]. apply (IHl i).
Qed.
Lemma list_lookup_total_alter `{!Inhabited A} f l i :
  i < length l → alter f i l !!! i = f (l !!! i).
Proof.
  intros [x Hx]%lookup_lt_is_Some_2.
  by rewrite !list_lookup_total_alt, list_lookup_alter, Hx.
Qed.
Lemma list_lookup_alter_ne f l i j : i ≠ j → alter f i l !! j = l !! j.
Proof. revert i j. induction l; [done|]. intros [] []; naive_solver. Qed.
Lemma list_lookup_total_alter_ne `{!Inhabited A} f l i j :
  i ≠ j → alter f i l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_alter_ne. Qed.

Lemma list_lookup_insert l i x : i < length l → <[i:=x]>l !! i = Some x.
Proof. revert i. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma list_lookup_total_insert `{!Inhabited A} l i x :
  i < length l → <[i:=x]>l !!! i = x.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_insert. Qed.
Lemma list_lookup_insert_ne l i j x : i ≠ j → <[i:=x]>l !! j = l !! j.
Proof. revert i j. induction l; [done|]. intros [] []; naive_solver. Qed.
Lemma list_lookup_total_insert_ne `{!Inhabited A} l i j x :
  i ≠ j → <[i:=x]>l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_insert_ne. Qed.
Lemma list_lookup_insert_Some l i x j y :
  <[i:=x]>l !! j = Some y ↔
    i = j ∧ x = y ∧ j < length l ∨ i ≠ j ∧ l !! j = Some y.
Proof.
  destruct (decide (i = j)) as [->|];
    [split|rewrite list_lookup_insert_ne by done; tauto].
  - intros Hy. assert (j < length l).
    { rewrite <-(insert_length l j x); eauto using lookup_lt_Some. }
    rewrite list_lookup_insert in Hy by done; naive_solver.
  - intros [(?&?&?)|[??]]; rewrite ?list_lookup_insert; naive_solver.
Qed.
Lemma list_insert_commute l i j x y :
  i ≠ j → <[i:=x]>(<[j:=y]>l) = <[j:=y]>(<[i:=x]>l).
Proof. revert i j. by induction l; intros [|?] [|?] ?; f_equal/=; auto. Qed.
Lemma list_insert_id' l i x : (i < length l → l !! i = Some x) → <[i:=x]>l = l.
Proof. revert i. induction l; intros [|i] ?; f_equal/=; naive_solver lia. Qed.
Lemma list_insert_id l i x : l !! i = Some x → <[i:=x]>l = l.
Proof. intros ?. by apply list_insert_id'. Qed.
Lemma list_insert_ge l i x : length l ≤ i → <[i:=x]>l = l.
Proof. revert i. induction l; intros [|i] ?; f_equal/=; auto with lia. Qed.
Lemma list_insert_insert l i x y : <[i:=x]> (<[i:=y]> l) = <[i:=x]> l.
Proof. revert i. induction l; intros [|i]; f_equal/=; auto. Qed.

Lemma list_lookup_other l i x :
  length l ≠ 1 → l !! i = Some x → ∃ j y, j ≠ i ∧ l !! j = Some y.
Proof.
  intros. destruct i, l as [|x0 [|x1 l]]; simplify_eq/=.
  - by exists 1, x1.
  - by exists 0, x0.
Qed.

Lemma alter_app_l f l1 l2 i :
  i < length l1 → alter f i (l1 ++ l2) = alter f i l1 ++ l2.
Proof. revert i. induction l1; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma alter_app_r f l1 l2 i :
  alter f (length l1 + i) (l1 ++ l2) = l1 ++ alter f i l2.
Proof. revert i. induction l1; intros [|?]; f_equal/=; auto. Qed.
Lemma alter_app_r_alt f l1 l2 i :
  length l1 ≤ i → alter f i (l1 ++ l2) = l1 ++ alter f (i - length l1) l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply alter_app_r.
Qed.
Lemma list_alter_id f l i : (∀ x, f x = x) → alter f i l = l.
Proof. intros ?. revert i. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma list_alter_ext f g l k i :
  (∀ x, l !! i = Some x → f x = g x) → l = k → alter f i l = alter g i k.
Proof. intros H ->. revert i H. induction k; intros [|?] ?; f_equal/=; auto. Qed.
Lemma list_alter_compose f g l i :
  alter (f ∘ g) i l = alter f i (alter g i l).
Proof. revert i. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma list_alter_commute f g l i j :
  i ≠ j → alter f i (alter g j l) = alter g j (alter f i l).
Proof. revert i j. induction l; intros [|?][|?] ?; f_equal/=; auto with lia. Qed.
Lemma insert_app_l l1 l2 i x :
  i < length l1 → <[i:=x]>(l1 ++ l2) = <[i:=x]>l1 ++ l2.
Proof. revert i. induction l1; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma insert_app_r l1 l2 i x : <[length l1+i:=x]>(l1 ++ l2) = l1 ++ <[i:=x]>l2.
Proof. revert i. induction l1; intros [|?]; f_equal/=; auto. Qed.
Lemma insert_app_r_alt l1 l2 i x :
  length l1 ≤ i → <[i:=x]>(l1 ++ l2) = l1 ++ <[i - length l1:=x]>l2.
Proof.
  intros. assert (i = length l1 + (i - length l1)) as Hi by lia.
  rewrite Hi at 1. by apply insert_app_r.
Qed.

Lemma delete_middle l1 l2 x : delete (length l1) (l1 ++ x :: l2) = l1 ++ l2.
Proof. induction l1; f_equal/=; auto. Qed.
Lemma length_delete l i :
  is_Some (l !! i) → length (delete i l) = length l - 1.
Proof.
  rewrite lookup_lt_is_Some. revert i.
  induction l as [|x l IH]; intros [|i] ?; simpl in *; [lia..|].
  rewrite IH by lia. lia.
Qed.
Lemma lookup_delete_lt l i j : j < i → delete i l !! j = l !! j.
Proof. revert i j; induction l; intros [] []; naive_solver eauto with lia. Qed.
Lemma lookup_total_delete_lt `{!Inhabited A} l i j :
  j < i → delete i l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_delete_lt. Qed.
Lemma lookup_delete_ge l i j : i ≤ j → delete i l !! j = l !! S j.
Proof. revert i j; induction l; intros [] []; naive_solver eauto with lia. Qed.
Lemma lookup_total_delete_ge `{!Inhabited A} l i j :
  i ≤ j → delete i l !!! j = l !!! S j.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_delete_ge. Qed.

Lemma inserts_length l i k : length (list_inserts i k l) = length l.
Proof.
  revert i. induction k; intros ?; csimpl; rewrite ?insert_length; auto.
Qed.
Lemma list_lookup_inserts l i k j :
  i ≤ j < i + length k → j < length l →
  list_inserts i k l !! j = k !! (j - i).
Proof.
  revert i j. induction k as [|y k IH]; csimpl; intros i j ??; [lia|].
  destruct (decide (i = j)) as [->|].
  { by rewrite list_lookup_insert, Nat.sub_diag
      by (rewrite inserts_length; lia). }
  rewrite list_lookup_insert_ne, IH by lia.
  by replace (j - i) with (S (j - S i)) by lia.
Qed.
Lemma list_lookup_total_inserts `{!Inhabited A} l i k j :
  i ≤ j < i + length k → j < length l →
  list_inserts i k l !!! j = k !!! (j - i).
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_inserts. Qed.
Lemma list_lookup_inserts_lt l i k j :
  j < i → list_inserts i k l !! j = l !! j.
Proof.
  revert i j. induction k; intros i j ?; csimpl;
    rewrite ?list_lookup_insert_ne by lia; auto with lia.
Qed.
Lemma list_lookup_total_inserts_lt `{!Inhabited A}l i k j :
  j < i → list_inserts i k l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_inserts_lt. Qed.
Lemma list_lookup_inserts_ge l i k j :
  i + length k ≤ j → list_inserts i k l !! j = l !! j.
Proof.
  revert i j. induction k; csimpl; intros i j ?;
    rewrite ?list_lookup_insert_ne by lia; auto with lia.
Qed.
Lemma list_lookup_total_inserts_ge `{!Inhabited A} l i k j :
  i + length k ≤ j → list_inserts i k l !!! j = l !!! j.
Proof. intros. by rewrite !list_lookup_total_alt, list_lookup_inserts_ge. Qed.
Lemma list_lookup_inserts_Some l i k j y :
  list_inserts i k l !! j = Some y ↔
    (j < i ∨ i + length k ≤ j) ∧ l !! j = Some y ∨
    i ≤ j < i + length k ∧ j < length l ∧ k !! (j - i) = Some y.
Proof.
  destruct (decide (j < i)).
  { rewrite list_lookup_inserts_lt by done; intuition lia. }
  destruct (decide (i + length k ≤ j)).
  { rewrite list_lookup_inserts_ge by done; intuition lia. }
  split.
  - intros Hy. assert (j < length l).
    { rewrite <-(inserts_length l i k); eauto using lookup_lt_Some. }
    rewrite list_lookup_inserts in Hy by lia. intuition lia.
  - intuition. by rewrite list_lookup_inserts by lia.
Qed.
Lemma list_insert_inserts_lt l i j x k :
  i < j → <[i:=x]>(list_inserts j k l) = list_inserts j k (<[i:=x]>l).
Proof.
  revert i j. induction k; intros i j ?; simpl;
    rewrite 1?list_insert_commute by lia; auto with f_equal.
Qed.
Lemma list_inserts_app_l l1 l2 l3 i :
  list_inserts i (l1 ++ l2) l3 = list_inserts (length l1 + i) l2 (list_inserts i l1 l3).
Proof.
  revert i; induction l1 as [|x l1 IH]; [done|].
  intro i. simpl. rewrite IH, Nat.add_succ_r. apply list_insert_inserts_lt. lia.
Qed.
Lemma list_inserts_app_r l1 l2 l3 i :
  list_inserts (length l2 + i) l1 (l2 ++ l3) = l2 ++ list_inserts i l1 l3.
Proof.
  revert i; induction l1 as [|x l1 IH]; [done|].
  intros i. simpl. by rewrite plus_n_Sm, IH, insert_app_r.
Qed.
Lemma list_inserts_nil l1 i : list_inserts i l1 [] = [].
Proof.
  revert i; induction l1 as [|x l1 IH]; [done|].
  intro i. simpl. by rewrite IH.
Qed.
Lemma list_inserts_cons l1 l2 i x :
  list_inserts (S i) l1 (x :: l2) = x :: list_inserts i l1 l2.
Proof.
  revert i; induction l1 as [|y l1 IH]; [done|].
  intro i. simpl. by rewrite IH.
Qed.
Lemma list_inserts_0_r l1 l2 l3 :
  length l1 = length l2 → list_inserts 0 l1 (l2 ++ l3) = l1 ++ l3.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] ?; simplify_eq/=; [done|].
  rewrite list_inserts_cons. simpl. by rewrite IH.
Qed.
Lemma list_inserts_0_l l1 l2 l3 :
  length l1 = length l3 → list_inserts 0 (l1 ++ l2) l3 = l1.
Proof.
  revert l3. induction l1 as [|x l1 IH]; intros [|z l3] ?; simplify_eq/=.
  { by rewrite list_inserts_nil. }
  rewrite list_inserts_cons. simpl. by rewrite IH.
Qed.

(** ** Properties of the [reverse] function *)
Lemma reverse_nil : reverse [] =@{list A} [].
Proof. done. Qed.
Lemma reverse_singleton x : reverse [x] = [x].
Proof. done. Qed.
Lemma reverse_cons l x : reverse (x :: l) = reverse l ++ [x].
Proof. unfold reverse. by rewrite <-!rev_alt. Qed.
Lemma reverse_snoc l x : reverse (l ++ [x]) = x :: reverse l.
Proof. unfold reverse. by rewrite <-!rev_alt, rev_unit. Qed.
Lemma reverse_app l1 l2 : reverse (l1 ++ l2) = reverse l2 ++ reverse l1.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_app_distr. Qed.
Lemma reverse_length l : length (reverse l) = length l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_length. Qed.
Lemma reverse_involutive l : reverse (reverse l) = l.
Proof. unfold reverse. rewrite <-!rev_alt. apply rev_involutive. Qed.
Lemma reverse_lookup l i :
  i < length l →
  reverse l !! i = l !! (length l - S i).
Proof.
  revert i. induction l as [|x l IH]; simpl; intros i Hi; [done|].
  rewrite reverse_cons.
  destruct (decide (i = length l)); subst.
  + by rewrite list_lookup_middle, Nat.sub_diag by by rewrite reverse_length.
  + rewrite lookup_app_l by (rewrite reverse_length; lia).
    rewrite IH by lia.
    by assert (length l - i = S (length l - S i)) as -> by lia.
Qed.
Lemma reverse_lookup_Some l i x :
  reverse l !! i = Some x ↔ l !! (length l - S i) = Some x ∧ i < length l.
Proof.
  split.
  - destruct (decide (i < length l)); [ by rewrite reverse_lookup|].
    rewrite lookup_ge_None_2; [done|]. rewrite reverse_length. lia.
  - intros [??]. by rewrite reverse_lookup.
Qed.
Global Instance: Inj (=) (=) (@reverse A).
Proof.
  intros l1 l2 Hl.
  by rewrite <-(reverse_involutive l1), <-(reverse_involutive l2), Hl.
Qed.

(** ** Properties of the [elem_of] predicate *)
Lemma not_elem_of_nil x : x ∉ [].
Proof. by inversion 1. Qed.
Lemma elem_of_nil x : x ∈ [] ↔ False.
Proof. intuition. by destruct (not_elem_of_nil x). Qed.
Lemma elem_of_nil_inv l : (∀ x, x ∉ l) → l = [].
Proof. destruct l; [done|]. by edestruct 1; constructor. Qed.
Lemma elem_of_not_nil x l : x ∈ l → l ≠ [].
Proof. intros ? ->. by apply (elem_of_nil x). Qed.
Lemma elem_of_cons l x y : x ∈ y :: l ↔ x = y ∨ x ∈ l.
Proof. by split; [inversion 1; subst|intros [->|?]]; constructor. Qed.
Lemma not_elem_of_cons l x y : x ∉ y :: l ↔ x ≠ y ∧ x ∉ l.
Proof. rewrite elem_of_cons. tauto. Qed.
Lemma elem_of_app l1 l2 x : x ∈ l1 ++ l2 ↔ x ∈ l1 ∨ x ∈ l2.
Proof.
  induction l1 as [|y l1 IH]; simpl.
  - rewrite elem_of_nil. naive_solver.
  - rewrite !elem_of_cons, IH. naive_solver.
Qed.
Lemma not_elem_of_app l1 l2 x : x ∉ l1 ++ l2 ↔ x ∉ l1 ∧ x ∉ l2.
Proof. rewrite elem_of_app. tauto. Qed.
Lemma elem_of_list_singleton x y : x ∈ [y] ↔ x = y.
Proof. rewrite elem_of_cons, elem_of_nil. tauto. Qed.
Lemma elem_of_reverse_2 x l : x ∈ l → x ∈ reverse l.
Proof.
  induction 1; rewrite reverse_cons, elem_of_app,
    ?elem_of_list_singleton; intuition.
Qed.
Lemma elem_of_reverse x l : x ∈ reverse l ↔ x ∈ l.
Proof.
  split; auto using elem_of_reverse_2.
  intros. rewrite <-(reverse_involutive l). by apply elem_of_reverse_2.
Qed.

Lemma elem_of_list_lookup_1 l x : x ∈ l → ∃ i, l !! i = Some x.
Proof.
  induction 1 as [|???? IH]; [by exists 0 |].
  destruct IH as [i ?]; auto. by exists (S i).
Qed.
Lemma elem_of_list_lookup_total_1 `{!Inhabited A} l x :
  x ∈ l → ∃ i, i < length l ∧ l !!! i = x.
Proof.
  intros [i Hi]%elem_of_list_lookup_1.
  eauto using lookup_lt_Some, list_lookup_total_correct.
Qed.
Lemma elem_of_list_lookup_2 l i x : l !! i = Some x → x ∈ l.
Proof.
  revert i. induction l; intros [|i] ?; simplify_eq/=; constructor; eauto.
Qed.
Lemma elem_of_list_lookup_total_2 `{!Inhabited A} l i :
  i < length l → l !!! i ∈ l.
Proof. intros. by eapply elem_of_list_lookup_2, list_lookup_lookup_total_lt. Qed.
Lemma elem_of_list_lookup l x : x ∈ l ↔ ∃ i, l !! i = Some x.
Proof. firstorder eauto using elem_of_list_lookup_1, elem_of_list_lookup_2. Qed.
Lemma elem_of_list_lookup_total `{!Inhabited A} l x :
  x ∈ l ↔ ∃ i, i < length l ∧ l !!! i = x.
Proof.
  naive_solver eauto using elem_of_list_lookup_total_1, elem_of_list_lookup_total_2.
Qed.
Lemma elem_of_list_split_length l i x :
  l !! i = Some x → ∃ l1 l2, l = l1 ++ x :: l2 ∧ i = length l1.
Proof.
  revert i; induction l as [|y l IH]; intros [|i] Hl; simplify_eq/=.
  - exists []; eauto.
  - destruct (IH _ Hl) as (?&?&?&?); simplify_eq/=.
    eexists (y :: _); eauto.
Qed.
Lemma elem_of_list_split l x : x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2.
Proof.
  intros [? (?&?&?&_)%elem_of_list_split_length]%elem_of_list_lookup_1; eauto.
Qed.
Lemma elem_of_list_split_l `{EqDecision A} l x :
  x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2 ∧ x ∉ l1.
Proof.
  induction 1 as [x l|x y l ? IH].
  { exists [], l. rewrite elem_of_nil. naive_solver. }
  destruct (decide (x = y)) as [->|?].
  - exists [], l. rewrite elem_of_nil. naive_solver.
  - destruct IH as (l1 & l2 & -> & ?).
    exists (y :: l1), l2. rewrite elem_of_cons. naive_solver.
Qed.
Lemma elem_of_list_split_r `{EqDecision A} l x :
  x ∈ l → ∃ l1 l2, l = l1 ++ x :: l2 ∧ x ∉ l2.
Proof.
  induction l as [|y l IH] using rev_ind.
  { by rewrite elem_of_nil. }
  destruct (decide (x = y)) as [->|].
  - exists l, []. rewrite elem_of_nil. naive_solver.
  - rewrite elem_of_app, elem_of_list_singleton. intros [?| ->]; try done.
    destruct IH as (l1 & l2 & -> & ?); auto.
    exists l1, (l2 ++ [y]).
    rewrite elem_of_app, elem_of_list_singleton, <-(assoc_L (++)). naive_solver.
Qed.
Lemma list_elem_of_insert l i x : i < length l → x ∈ <[i:=x]>l.
Proof. intros. by eapply elem_of_list_lookup_2, list_lookup_insert. Qed.
Lemma nth_elem_of l i d : i < length l → nth i l d ∈ l.
Proof.
  intros; eapply elem_of_list_lookup_2.
  destruct (nth_lookup_or_length l i d); [done | by lia].
Qed.

Lemma not_elem_of_app_cons_inv_l x y l1 l2 k1 k2 :
  x ∉ k1 → y ∉ l1 →
  l1 ++ x :: l2 = k1 ++ y :: k2 →
  l1 = k1 ∧ x = y ∧ l2 = k2.
Proof.
  revert k1. induction l1 as [|x' l1 IH]; intros [|y' k1] Hx Hy ?; simplify_eq/=;
    try apply not_elem_of_cons in Hx as [??];
    try apply not_elem_of_cons in Hy as [??]; naive_solver.
Qed.
Lemma not_elem_of_app_cons_inv_r x y l1 l2 k1 k2 :
  x ∉ k2 → y ∉ l2 →
  l1 ++ x :: l2 = k1 ++ y :: k2 →
  l1 = k1 ∧ x = y ∧ l2 = k2.
Proof.
  intros. destruct (not_elem_of_app_cons_inv_l x y (reverse l2) (reverse l1)
    (reverse k2) (reverse k1)); [..|naive_solver].
  - by rewrite elem_of_reverse.
  - by rewrite elem_of_reverse.
  - rewrite <-!reverse_snoc, <-!reverse_app, <-!(assoc_L (++)). by f_equal.
Qed.

(** ** Properties of the [NoDup] predicate *)
Lemma NoDup_nil : NoDup (@nil A) ↔ True.
Proof. split; constructor. Qed.
Lemma NoDup_cons x l : NoDup (x :: l) ↔ x ∉ l ∧ NoDup l.
Proof. split; [by inversion 1|]. intros [??]. by constructor. Qed.
Lemma NoDup_cons_1_1 x l : NoDup (x :: l) → x ∉ l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_cons_1_2 x l : NoDup (x :: l) → NoDup l.
Proof. rewrite NoDup_cons. by intros [??]. Qed.
Lemma NoDup_singleton x : NoDup [x].
Proof. constructor; [apply not_elem_of_nil | constructor]. Qed.
Lemma NoDup_app l k : NoDup (l ++ k) ↔ NoDup l ∧ (∀ x, x ∈ l → x ∉ k) ∧ NoDup k.
Proof.
  induction l; simpl.
  - rewrite NoDup_nil. setoid_rewrite elem_of_nil. naive_solver.
  - rewrite !NoDup_cons.
    setoid_rewrite elem_of_cons. setoid_rewrite elem_of_app. naive_solver.
Qed.
Lemma NoDup_lookup l i j x :
  NoDup l → l !! i = Some x → l !! j = Some x → i = j.
Proof.
  intros Hl. revert i j. induction Hl as [|x' l Hx Hl IH].
  { intros; simplify_eq. }
  intros [|i] [|j] ??; simplify_eq/=; eauto with f_equal;
    exfalso; eauto using elem_of_list_lookup_2.
Qed.
Lemma NoDup_alt l :
  NoDup l ↔ ∀ i j x, l !! i = Some x → l !! j = Some x → i = j.
Proof.
  split; eauto using NoDup_lookup.
  induction l as [|x l IH]; intros Hl; constructor.
  - rewrite elem_of_list_lookup. intros [i ?].
    opose proof* (Hl (S i) 0); by auto.
  - apply IH. intros i j x' ??. by apply (inj S), (Hl (S i) (S j) x').
Qed.

Section no_dup_dec.
  Context `{!EqDecision A}.
  Global Instance NoDup_dec: ∀ l, Decision (NoDup l) :=
    fix NoDup_dec l :=
    match l return Decision (NoDup l) with
    | [] => left NoDup_nil_2
    | x :: l =>
      match decide_rel (∈) x l with
      | left Hin => right (λ H, NoDup_cons_1_1 _ _ H Hin)
      | right Hin =>
        match NoDup_dec l with
        | left H => left (NoDup_cons_2 _ _ Hin H)
        | right H => right (H ∘ NoDup_cons_1_2 _ _)
        end
      end
    end.
  Lemma elem_of_remove_dups l x : x ∈ remove_dups l ↔ x ∈ l.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_cons; intuition (simplify_eq; auto).
  Qed.
  Lemma NoDup_remove_dups l : NoDup (remove_dups l).
  Proof.
    induction l; simpl; repeat case_decide; try constructor; auto.
    by rewrite elem_of_remove_dups.
  Qed.
End no_dup_dec.

(** ** Set operations on lists *)
Section list_set.
  Lemma elem_of_list_intersection_with f l k x :
    x ∈ list_intersection_with f l k ↔ ∃ x1 x2,
        x1 ∈ l ∧ x2 ∈ k ∧ f x1 x2 = Some x.
  Proof.
    split.
    - induction l as [|x1 l IH]; simpl; [by rewrite elem_of_nil|].
      intros Hx. setoid_rewrite elem_of_cons.
      cut ((∃ x2, x2 ∈ k ∧ f x1 x2 = Some x)
           ∨ x ∈ list_intersection_with f l k); [naive_solver|].
      clear IH. revert Hx. generalize (list_intersection_with f l k).
      induction k; simpl; [by auto|].
      case_match; setoid_rewrite elem_of_cons; naive_solver.
    - intros (x1&x2&Hx1&Hx2&Hx). induction Hx1 as [x1 l|x1 ? l ? IH]; simpl.
      + generalize (list_intersection_with f l k).
        induction Hx2; simpl; [by rewrite Hx; left |].
        case_match; simpl; try setoid_rewrite elem_of_cons; auto.
      + generalize (IH Hx). clear Hx IH Hx2.
        generalize (list_intersection_with f l k).
        induction k; simpl; intros; [done|].
        case_match; simpl; rewrite ?elem_of_cons; auto.
  Qed.

  Context `{!EqDecision A}.
  Lemma elem_of_list_difference l k x : x ∈ list_difference l k ↔ x ∈ l ∧ x ∉ k.
  Proof.
    split; induction l; simpl; try case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma NoDup_list_difference l k : NoDup l → NoDup (list_difference l k).
  Proof.
    induction 1; simpl; try case_decide.
    - constructor.
    - done.
    - constructor; [|done]. rewrite elem_of_list_difference; intuition.
  Qed.
  Lemma elem_of_list_union l k x : x ∈ list_union l k ↔ x ∈ l ∨ x ∈ k.
  Proof.
    unfold list_union. rewrite elem_of_app, elem_of_list_difference.
    intuition. case (decide (x ∈ k)); intuition.
  Qed.
  Lemma NoDup_list_union l k : NoDup l → NoDup k → NoDup (list_union l k).
  Proof.
    intros. apply NoDup_app. repeat split.
    - by apply NoDup_list_difference.
    - intro. rewrite elem_of_list_difference. intuition.
    - done.
  Qed.
  Lemma elem_of_list_intersection l k x :
    x ∈ list_intersection l k ↔ x ∈ l ∧ x ∈ k.
  Proof.
    split; induction l; simpl; repeat case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; intuition congruence.
  Qed.
  Lemma NoDup_list_intersection l k : NoDup l → NoDup (list_intersection l k).
  Proof.
    induction 1; simpl; try case_decide.
    - constructor.
    - constructor; [|done]. rewrite elem_of_list_intersection; intuition.
    - done.
  Qed.
End list_set.

(** ** Properties of the [last] function *)
Lemma last_nil : last [] =@{option A} None.
Proof. done. Qed.
Lemma last_singleton x : last [x] = Some x.
Proof. done. Qed.
Lemma last_cons_cons x1 x2 l : last (x1 :: x2 :: l) = last (x2 :: l).
Proof. done. Qed.
Lemma last_app_cons l1 l2 x :
  last (l1 ++ x :: l2) = last (x :: l2).
Proof. induction l1 as [|y [|y' l1] IHl]; done. Qed.
Lemma last_snoc x l : last (l ++ [x]) = Some x.
Proof. induction l as [|? []]; simpl; auto. Qed.
Lemma last_None l : last l = None ↔ l = [].
Proof.
  split; [|by intros ->].
  induction l as [|x1 [|x2 l] IH]; naive_solver.
Qed.
Lemma last_Some l x : last l = Some x ↔ ∃ l', l = l' ++ [x].
Proof.
  split.
  - destruct l as [|x' l'] using rev_ind; [done|].
    rewrite last_snoc. naive_solver.
  - intros [l' ->]. by rewrite last_snoc.
Qed.
Lemma last_is_Some l : is_Some (last l) ↔ l ≠ [].
Proof. rewrite <-not_eq_None_Some, last_None. naive_solver. Qed.
Lemma last_app l1 l2 :
  last (l1 ++ l2) = match last l2 with Some y => Some y | None => last l1 end.
Proof.
  destruct l2 as [|x l2 _] using rev_ind.
  - by rewrite (right_id_L _ (++)).
  - by rewrite (assoc_L (++)), !last_snoc.
Qed.
Lemma last_cons x l :
  last (x :: l) = match last l with Some y => Some y | None => Some x end.
Proof. by apply (last_app [x]). Qed.
Lemma last_cons_Some_ne x y l :
  x ≠ y → last (x :: l) = Some y → last l = Some y.
Proof. rewrite last_cons. destruct (last l); naive_solver. Qed.
Lemma last_lookup l : last l = l !! pred (length l).
Proof. by induction l as [| ?[]]. Qed.
Lemma last_reverse l : last (reverse l) = head l.
Proof. destruct l as [|x l]; simpl; by rewrite ?reverse_cons, ?last_snoc. Qed.
Lemma last_Some_elem_of l x :
  last l = Some x → x ∈ l.
Proof.
  rewrite last_Some. intros [l' ->]. apply elem_of_app. right.
  by apply elem_of_list_singleton.
Qed.

(** ** Properties of the [head] function *)
Lemma head_nil : head [] =@{option A} None.
Proof. done. Qed.
Lemma head_cons x l : head (x :: l) = Some x.
Proof. done. Qed.

Lemma head_None l : head l = None ↔ l = [].
Proof. split; [|by intros ->]. by destruct l. Qed.
Lemma head_Some l x : head l = Some x ↔ ∃ l', l = x :: l'.
Proof. split; [destruct l as [|x' l]; naive_solver | by intros [l' ->]]. Qed.
Lemma head_is_Some l : is_Some (head l) ↔ l ≠ [].
Proof. rewrite <-not_eq_None_Some, head_None. naive_solver. Qed.

Lemma head_snoc x l :
  head (l ++ [x]) = match head l with Some y => Some y | None => Some x end.
Proof. by destruct l. Qed.
Lemma head_snoc_snoc x1 x2 l :
  head (l ++ [x1; x2]) = head (l ++ [x1]).
Proof. by destruct l. Qed.
Lemma head_lookup l : head l = l !! 0.
Proof. by destruct l. Qed.

Lemma head_reverse l : head (reverse l) = last l.
Proof. by rewrite <-last_reverse, reverse_involutive. Qed.
Lemma head_Some_elem_of l x :
  head l = Some x → x ∈ l.
Proof. rewrite head_Some. intros [l' ->]. left. Qed.

(** ** Properties of the [take] function *)
Definition take_drop i l : take i l ++ drop i l = l := firstn_skipn i l.
Lemma take_drop_middle l i x :
  l !! i = Some x → take i l ++ x :: drop (S i) l = l.
Proof.
  revert i x. induction l; intros [|?] ??; simplify_eq/=; f_equal; auto.
Qed.
Lemma take_0 l : take 0 l = [].
Proof. reflexivity. Qed.
Lemma take_nil n : take n [] =@{list A} [].
Proof. by destruct n. Qed.
Lemma take_S_r l n x : l !! n = Some x → take (S n) l = take n l ++ [x].
Proof. revert n. induction l; intros []; naive_solver eauto with f_equal. Qed.
Lemma take_ge l n : length l ≤ n → take n l = l.
Proof. revert n. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.

(** [take_app] is the most general lemma for [take] and [app]. Below that we
establish a number of useful corollaries. *)
Lemma take_app l k n : take n (l ++ k) = take n l ++ take (n - length l) k.
Proof. apply firstn_app. Qed.

Lemma take_app_ge l k n :
  length l ≤ n → take n (l ++ k) = l ++ take (n - length l) k.
Proof. intros. by rewrite take_app, take_ge. Qed.
Lemma take_app_le l k n : n ≤ length l → take n (l ++ k) = take n l.
Proof.
  intros. by rewrite take_app, (proj2 (Nat.sub_0_le _ _)), take_0, (right_id _ _).
Qed.
Lemma take_app_add l k m :
  take (length l + m) (l ++ k) = l ++ take m k.
Proof. rewrite take_app, take_ge by lia. repeat f_equal; lia. Qed.
Lemma take_app_add' l k n m :
  n = length l → take (n + m) (l ++ k) = l ++ take m k.
Proof. intros ->. apply take_app_add. Qed.
Lemma take_app_length l k : take (length l) (l ++ k) = l.
Proof. by rewrite take_app, take_ge, Nat.sub_diag, take_0, (right_id _ _). Qed.
Lemma take_app_length' l k n : n = length l → take n (l ++ k) = l.
Proof. intros ->. by apply take_app_length. Qed.
Lemma take_app3_length l1 l2 l3 : take (length l1) ((l1 ++ l2) ++ l3) = l1.
Proof. by rewrite <-(assoc_L (++)), take_app_length. Qed.
Lemma take_app3_length' l1 l2 l3 n :
  n = length l1 → take n ((l1 ++ l2) ++ l3) = l1.
Proof. intros ->. by apply take_app3_length. Qed.

Lemma take_take l n m : take n (take m l) = take (min n m) l.
Proof. revert n m. induction l; intros [|?] [|?]; f_equal/=; auto. Qed.
Lemma take_idemp l n : take n (take n l) = take n l.
Proof. by rewrite take_take, Nat.min_id. Qed.
Lemma take_length l n : length (take n l) = min n (length l).
Proof. revert n. induction l; intros [|?]; f_equal/=; done. Qed.
Lemma take_length_le l n : n ≤ length l → length (take n l) = n.
Proof. rewrite take_length. apply Nat.min_l. Qed.
Lemma take_length_ge l n : length l ≤ n → length (take n l) = length l.
Proof. rewrite take_length. apply Nat.min_r. Qed.
Lemma take_drop_commute l n m : take n (drop m l) = drop m (take (m + n) l).
Proof.
  revert n m. induction l; intros [|?][|?]; simpl; auto using take_nil with lia.
Qed.

Lemma lookup_take l n i : i < n → take n l !! i = l !! i.
Proof. revert n i. induction l; intros [|n] [|i] ?; simpl; auto with lia. Qed.
Lemma lookup_total_take `{!Inhabited A} l n i : i < n → take n l !!! i = l !!! i.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_take. Qed.
Lemma lookup_take_ge l n i : n ≤ i → take n l !! i = None.
Proof. revert n i. induction l; intros [|?] [|?] ?; simpl; auto with lia. Qed.
Lemma lookup_total_take_ge `{!Inhabited A} l n i : n ≤ i → take n l !!! i = inhabitant.
Proof. intros. by rewrite list_lookup_total_alt, lookup_take_ge. Qed.
Lemma lookup_take_Some l n i a : take n l !! i = Some a ↔ l !! i = Some a ∧ i < n.
Proof.
  split.
  - destruct (decide (i < n)).
    + rewrite lookup_take; naive_solver.
    + rewrite lookup_take_ge; [done|lia].
  - intros [??]. by rewrite lookup_take.
Qed.

Lemma elem_of_take x n l : x ∈ take n l ↔ ∃ i, l !! i = Some x ∧ i < n.
Proof.
  rewrite elem_of_list_lookup. setoid_rewrite lookup_take_Some. naive_solver.
Qed.

Lemma take_alter f l n i : n ≤ i → take n (alter f i l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  - by rewrite !lookup_take_ge.
  - by rewrite !lookup_take, !list_lookup_alter_ne by lia.
Qed.
Lemma take_insert l n i x : n ≤ i → take n (<[i:=x]>l) = take n l.
Proof.
  intros. apply list_eq. intros j. destruct (le_lt_dec n j).
  - by rewrite !lookup_take_ge.
  - by rewrite !lookup_take, !list_lookup_insert_ne by lia.
Qed.
Lemma take_insert_lt l n i x : i < n → take n (<[i:=x]>l) = <[i:=x]>(take n l).
Proof.
  revert l i. induction n as [|? IHn]; auto; simpl.
  intros [|] [|] ?; auto; simpl. by rewrite IHn by lia.
Qed.

(** ** Properties of the [drop] function *)
Lemma drop_0 l : drop 0 l = l.
Proof. done. Qed.
Lemma drop_nil n : drop n [] =@{list A} [].
Proof. by destruct n. Qed.
Lemma drop_S l x n :
  l !! n = Some x → drop n l = x :: drop (S n) l.
Proof. revert n. induction l; intros []; naive_solver. Qed.
Lemma drop_length l n : length (drop n l) = length l - n.
Proof. revert n. by induction l; intros [|i]; f_equal/=. Qed.
Lemma drop_ge l n : length l ≤ n → drop n l = [].
Proof. revert n. induction l; intros [|?]; simpl in *; auto with lia. Qed.
Lemma drop_all l : drop (length l) l = [].
Proof. by apply drop_ge. Qed.
Lemma drop_drop l n1 n2 : drop n1 (drop n2 l) = drop (n2 + n1) l.
Proof. revert n2. induction l; intros [|?]; simpl; rewrite ?drop_nil; auto. Qed.

(** [drop_app] is the most general lemma for [drop] and [app]. Below we prove a
number of useful corollaries. *)
Lemma drop_app l k n : drop n (l ++ k) = drop n l ++ drop (n - length l) k.
Proof. apply skipn_app. Qed.

Lemma drop_app_ge l k n :
  length l ≤ n → drop n (l ++ k) = drop (n - length l) k.
Proof. intros. by rewrite drop_app, drop_ge. Qed.
Lemma drop_app_le l k n :
  n ≤ length l → drop n (l ++ k) = drop n l ++ k.
Proof. intros. by rewrite drop_app, (proj2 (Nat.sub_0_le _ _)), drop_0. Qed.
Lemma drop_app_add l k m :
  drop (length l + m) (l ++ k) = drop m k.
Proof. rewrite drop_app, drop_ge by lia. simpl. f_equal; lia. Qed.
Lemma drop_app_add' l k n m :
  n = length l → drop (n + m) (l ++ k) = drop m k.
Proof. intros ->. apply drop_app_add. Qed.
Lemma drop_app_length l k : drop (length l) (l ++ k) = k.
Proof. by rewrite drop_app_le, drop_all. Qed.
Lemma drop_app_length' l k n : n = length l → drop n (l ++ k) = k.
Proof. intros ->. by apply drop_app_length. Qed.
Lemma drop_app3_length l1 l2 l3 :
  drop (length l1) ((l1 ++ l2) ++ l3) = l2 ++ l3.
Proof. by rewrite <-(assoc_L (++)), drop_app_length. Qed.
Lemma drop_app3_length' l1 l2 l3 n :
  n = length l1 → drop n ((l1 ++ l2) ++ l3) = l2 ++ l3.
Proof. intros ->. apply drop_app3_length. Qed.

Lemma lookup_drop l n i : drop n l !! i = l !! (n + i).
Proof. revert n i. induction l; intros [|i] ?; simpl; auto. Qed.
Lemma lookup_total_drop `{!Inhabited A} l n i : drop n l !!! i = l !!! (n + i).
Proof. by rewrite !list_lookup_total_alt, lookup_drop. Qed.
Lemma drop_alter f l n i : i < n → drop n (alter f i l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_alter_ne by lia.
Qed.
Lemma drop_insert_le l n i x : n ≤ i → drop n (<[i:=x]>l) = <[i-n:=x]>(drop n l).
Proof. revert i n. induction l; intros [] []; naive_solver lia. Qed.
Lemma drop_insert_gt l n i x : i < n → drop n (<[i:=x]>l) = drop n l.
Proof.
  intros. apply list_eq. intros j.
  by rewrite !lookup_drop, !list_lookup_insert_ne by lia.
Qed.
Lemma delete_take_drop l i : delete i l = take i l ++ drop (S i) l.
Proof. revert i. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma take_take_drop l n m : take n l ++ take m (drop n l) = take (n + m) l.
Proof. revert n m. induction l; intros [|?] [|?]; f_equal/=; auto. Qed.
Lemma drop_take_drop l n m : n ≤ m → drop n (take m l) ++ drop m l = drop n l.
Proof.
  revert n m. induction l; intros [|?] [|?] ?;
    f_equal/=; auto using take_drop with lia.
Qed.
Lemma insert_take_drop l i x :
  i < length l →
  <[i:=x]> l = take i l ++ x :: drop (S i) l.
Proof.
  intros Hi.
  rewrite <-(take_drop_middle (<[i:=x]> l) i x).
  2:{ by rewrite list_lookup_insert. }
  rewrite take_insert by done.
  rewrite drop_insert_gt by lia.
  done.
Qed.

(** ** Interaction between the [take]/[drop]/[reverse] functions *)
Lemma take_reverse l n : take n (reverse l) = reverse (drop (length l - n) l).
Proof. unfold reverse; rewrite <-!rev_alt. apply firstn_rev. Qed.
Lemma drop_reverse l n : drop n (reverse l) = reverse (take (length l - n) l).
Proof. unfold reverse; rewrite <-!rev_alt. apply skipn_rev. Qed.
Lemma reverse_take l n : reverse (take n l) = drop (length l - n) (reverse l).
Proof.
  rewrite drop_reverse. destruct (decide (n ≤ length l)).
  - repeat f_equal; lia.
  - by rewrite !take_ge by lia.
Qed.
Lemma reverse_drop l n : reverse (drop n l) = take (length l - n) (reverse l).
Proof.
  rewrite take_reverse. destruct (decide (n ≤ length l)).
  - repeat f_equal; lia.
  - by rewrite !drop_ge by lia.
Qed.

(** ** Other lemmas that use [take]/[drop] in their proof. *)
Lemma app_eq_inv l1 l2 k1 k2 :
  l1 ++ l2 = k1 ++ k2 →
  (∃ k, l1 = k1 ++ k ∧ k2 = k ++ l2) ∨ (∃ k, k1 = l1 ++ k ∧ l2 = k ++ k2).
Proof.
  intros Hlk. destruct (decide (length l1 < length k1)).
  - right. rewrite <-(take_drop (length l1) k1), <-(assoc_L _) in Hlk.
    apply app_inj_1 in Hlk as [Hl1 Hl2]; [|rewrite take_length; lia].
    exists (drop (length l1) k1). by rewrite Hl1 at 1; rewrite take_drop.
  - left. rewrite <-(take_drop (length k1) l1), <-(assoc_L _) in Hlk.
    apply app_inj_1 in Hlk as [Hk1 Hk2]; [|rewrite take_length; lia].
    exists (drop (length k1) l1). by rewrite <-Hk1 at 1; rewrite take_drop.
Qed.

(** ** Properties of the [replicate] function *)
Lemma replicate_length n x : length (replicate n x) = n.
Proof. induction n; simpl; auto. Qed.
Lemma lookup_replicate n x y i :
  replicate n x !! i = Some y ↔ y = x ∧ i < n.
Proof.
  split.
  - revert i. induction n; intros [|?]; naive_solver auto with lia.
  - intros [-> Hi]. revert i Hi.
    induction n; intros [|?]; naive_solver auto with lia.
Qed.
Lemma elem_of_replicate n x y : y ∈ replicate n x ↔ y = x ∧ n ≠ 0.
Proof.
  rewrite elem_of_list_lookup, Nat.neq_0_lt_0.
  setoid_rewrite lookup_replicate; naive_solver eauto with lia.
Qed.
Lemma lookup_replicate_1 n x y i :
  replicate n x !! i = Some y → y = x ∧ i < n.
Proof. by rewrite lookup_replicate. Qed.
Lemma lookup_replicate_2 n x i : i < n → replicate n x !! i = Some x.
Proof. by rewrite lookup_replicate. Qed.
Lemma lookup_total_replicate_2 `{!Inhabited A} n x i :
  i < n → replicate n x !!! i = x.
Proof. intros. by rewrite list_lookup_total_alt, lookup_replicate_2. Qed.
Lemma lookup_replicate_None n x i : n ≤ i ↔ replicate n x !! i = None.
Proof.
  rewrite eq_None_not_Some, Nat.le_ngt. split.
  - intros Hin [x' Hx']; destruct Hin. rewrite lookup_replicate in Hx'; tauto.
  - intros Hx ?. destruct Hx. exists x; auto using lookup_replicate_2.
Qed.
Lemma insert_replicate x n i : <[i:=x]>(replicate n x) = replicate n x.
Proof. revert i. induction n; intros [|?]; f_equal/=; auto. Qed.
Lemma insert_replicate_lt x y n i :
  i < n →
  <[i:=y]>(replicate n x) = replicate i x ++ y :: replicate (n - S i) x.
Proof.
  revert i. induction n as [|n IH]; intros [|i] Hi; simpl; [lia..| |].
  - by rewrite Nat.sub_0_r.
  - by rewrite IH by lia.
Qed.
Lemma elem_of_replicate_inv x n y : x ∈ replicate n y → x = y.
Proof. induction n; simpl; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.
Lemma replicate_S n x : replicate (S n) x = x :: replicate n x.
Proof. done. Qed.
Lemma replicate_S_end n x : replicate (S n) x = replicate n x ++ [x].
Proof. induction n; f_equal/=; auto. Qed.
Lemma replicate_add n m x :
  replicate (n + m) x = replicate n x ++ replicate m x.
Proof. induction n; f_equal/=; auto. Qed.
Lemma replicate_cons_app n x :
  x :: replicate n x = replicate n x ++ [x].
Proof. induction n; f_equal/=; eauto.  Qed.
Lemma take_replicate n m x : take n (replicate m x) = replicate (min n m) x.
Proof. revert m. by induction n; intros [|?]; f_equal/=. Qed.
Lemma take_replicate_add n m x : take n (replicate (n + m) x) = replicate n x.
Proof. by rewrite take_replicate, min_l by lia. Qed.
Lemma drop_replicate n m x : drop n (replicate m x) = replicate (m - n) x.
Proof. revert m. by induction n; intros [|?]; f_equal/=. Qed.
Lemma drop_replicate_add n m x : drop n (replicate (n + m) x) = replicate m x.
Proof. rewrite drop_replicate. f_equal. lia. Qed.
Lemma replicate_as_elem_of x n l :
  replicate n x = l ↔ length l = n ∧ ∀ y, y ∈ l → y = x.
Proof.
  split; [intros <-; eauto using elem_of_replicate_inv, replicate_length|].
  intros [<- Hl]. symmetry. induction l as [|y l IH]; f_equal/=.
  - apply Hl. by left.
  - apply IH. intros ??. apply Hl. by right.
Qed.
Lemma reverse_replicate n x : reverse (replicate n x) = replicate n x.
Proof.
  symmetry. apply replicate_as_elem_of.
  rewrite reverse_length, replicate_length. split; auto.
  intros y. rewrite elem_of_reverse. by apply elem_of_replicate_inv.
Qed.
Lemma replicate_false βs n : length βs = n → replicate n false =.>* βs.
Proof. intros <-. by induction βs; simpl; constructor. Qed.
Lemma tail_replicate x n : tail (replicate n x) = replicate (pred n) x.
Proof. by destruct n. Qed.
Lemma head_replicate_Some x n : head (replicate n x) = Some x ↔ 0 < n.
Proof. destruct n; naive_solver lia. Qed.

(** ** Properties of the [resize] function *)
Lemma resize_spec l n x : resize n x l = take n l ++ replicate (n - length l) x.
Proof. revert n. induction l; intros [|?]; f_equal/=; auto. Qed.
Lemma resize_0 l x : resize 0 x l = [].
Proof. by destruct l. Qed.
Lemma resize_nil n x : resize n x [] = replicate n x.
Proof. rewrite resize_spec. rewrite take_nil. f_equal/=. lia. Qed.
Lemma resize_ge l n x :
  length l ≤ n → resize n x l = l ++ replicate (n - length l) x.
Proof. intros. by rewrite resize_spec, take_ge. Qed.
Lemma resize_le l n x : n ≤ length l → resize n x l = take n l.
Proof.
  intros. rewrite resize_spec, (proj2 (Nat.sub_0_le _ _)) by done.
  simpl. by rewrite (right_id_L [] (++)).
Qed.
Lemma resize_all l x : resize (length l) x l = l.
Proof. intros. by rewrite resize_le, take_ge. Qed.
Lemma resize_all_alt l n x : n = length l → resize n x l = l.
Proof. intros ->. by rewrite resize_all. Qed.
Lemma resize_add l n m x :
  resize (n + m) x l = resize n x l ++ resize m x (drop n l).
Proof.
  revert n m. induction l; intros [|?] [|?]; f_equal/=; auto.
  - by rewrite Nat.add_0_r, (right_id_L [] (++)).
  - by rewrite replicate_add.
Qed.
Lemma resize_add_eq l n m x :
  length l = n → resize (n + m) x l = l ++ replicate m x.
Proof. intros <-. by rewrite resize_add, resize_all, drop_all, resize_nil. Qed.
Lemma resize_app_le l1 l2 n x :
  n ≤ length l1 → resize n x (l1 ++ l2) = resize n x l1.
Proof.
  intros. by rewrite !resize_le, take_app_le by (rewrite ?app_length; lia).
Qed.
Lemma resize_app l1 l2 n x : n = length l1 → resize n x (l1 ++ l2) = l1.
Proof. intros ->. by rewrite resize_app_le, resize_all. Qed.
Lemma resize_app_ge l1 l2 n x :
  length l1 ≤ n → resize n x (l1 ++ l2) = l1 ++ resize (n - length l1) x l2.
Proof.
  intros. rewrite !resize_spec, take_app_ge, (assoc_L (++)) by done.
  do 2 f_equal. rewrite app_length. lia.
Qed.
Lemma resize_length l n x : length (resize n x l) = n.
Proof. rewrite resize_spec, app_length, replicate_length, take_length. lia. Qed.
Lemma resize_replicate x n m : resize n x (replicate m x) = replicate n x.
Proof. revert m. induction n; intros [|?]; f_equal/=; auto. Qed.
Lemma resize_resize l n m x : n ≤ m → resize n x (resize m x l) = resize n x l.
Proof.
  revert n m. induction l; simpl.
  - intros. by rewrite !resize_nil, resize_replicate.
  - intros [|?] [|?] ?; f_equal/=; auto with lia.
Qed.
Lemma resize_idemp l n x : resize n x (resize n x l) = resize n x l.
Proof. by rewrite resize_resize. Qed.
Lemma resize_take_le l n m x : n ≤ m → resize n x (take m l) = resize n x l.
Proof. revert n m. induction l; intros [|?][|?] ?; f_equal/=; auto with lia. Qed.
Lemma resize_take_eq l n x : resize n x (take n l) = resize n x l.
Proof. by rewrite resize_take_le. Qed.
Lemma take_resize l n m x : take n (resize m x l) = resize (min n m) x l.
Proof.
  revert n m. induction l; intros [|?][|?]; f_equal/=; auto using take_replicate.
Qed.
Lemma take_resize_le l n m x : n ≤ m → take n (resize m x l) = resize n x l.
Proof. intros. by rewrite take_resize, Nat.min_l. Qed.
Lemma take_resize_eq l n x : take n (resize n x l) = resize n x l.
Proof. intros. by rewrite take_resize, Nat.min_l. Qed.
Lemma take_resize_add l n m x : take n (resize (n + m) x l) = resize n x l.
Proof. by rewrite take_resize, min_l by lia. Qed.
Lemma drop_resize_le l n m x :
  n ≤ m → drop n (resize m x l) = resize (m - n) x (drop n l).
Proof.
  revert n m. induction l; simpl.
  - intros. by rewrite drop_nil, !resize_nil, drop_replicate.
  - intros [|?] [|?] ?; simpl; try case_match; auto with lia.
Qed.
Lemma drop_resize_add l n m x :
  drop n (resize (n + m) x l) = resize m x (drop n l).
Proof. rewrite drop_resize_le by lia. f_equal. lia. Qed.
Lemma lookup_resize l n x i : i < n → i < length l → resize n x l !! i = l !! i.
Proof.
  intros ??. destruct (decide (n < length l)).
  - by rewrite resize_le, lookup_take by lia.
  - by rewrite resize_ge, lookup_app_l by lia.
Qed.
Lemma lookup_total_resize `{!Inhabited A} l n x i :
  i < n → i < length l → resize n x l !!! i = l !!! i.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_resize. Qed.
Lemma lookup_resize_new l n x i :
  length l ≤ i → i < n → resize n x l !! i = Some x.
Proof.
  intros ??. rewrite resize_ge by lia.
  replace i with (length l + (i - length l)) by lia.
  by rewrite lookup_app_r, lookup_replicate_2 by lia.
Qed.
Lemma lookup_total_resize_new `{!Inhabited A} l n x i :
  length l ≤ i → i < n → resize n x l !!! i = x.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_resize_new. Qed.
Lemma lookup_resize_old l n x i : n ≤ i → resize n x l !! i = None.
Proof. intros ?. apply lookup_ge_None_2. by rewrite resize_length. Qed.
Lemma lookup_total_resize_old `{!Inhabited A} l n x i :
  n ≤ i → resize n x l !!! i = inhabitant.
Proof. intros. by rewrite !list_lookup_total_alt, lookup_resize_old. Qed.

(** ** Properties of the [rotate] function *)
Lemma rotate_replicate n1 n2 x:
  rotate n1 (replicate n2 x) = replicate n2 x.
Proof.
  unfold rotate. rewrite drop_replicate, take_replicate, <-replicate_add.
  f_equal. lia.
Qed.

Lemma rotate_length l n:
  length (rotate n l) = length l.
Proof. unfold rotate. rewrite app_length, drop_length, take_length. lia. Qed.

Lemma lookup_rotate_r l n i:
  i < length l →
  rotate n l !! i = l !! rotate_nat_add n i (length l).
Proof.
  intros Hlen. pose proof (Nat.mod_upper_bound n (length l)) as ?.
  unfold rotate. rewrite rotate_nat_add_add_mod, rotate_nat_add_alt by lia.
  remember (n `mod` length l) as n'.
  case_decide.
  - by rewrite lookup_app_l, lookup_drop by (rewrite drop_length; lia).
  - rewrite lookup_app_r, lookup_take, drop_length by (rewrite drop_length; lia).
    f_equal. lia.
Qed.

Lemma lookup_rotate_r_Some l n i x:
  rotate n l !! i = Some x ↔
  l !! rotate_nat_add n i (length l) = Some x ∧ i < length l.
Proof.
  split.
  - intros Hl. pose proof (lookup_lt_Some _ _ _ Hl) as Hlen.
    rewrite rotate_length in Hlen. by rewrite <-lookup_rotate_r.
  - intros [??]. by rewrite lookup_rotate_r.
Qed.

Lemma lookup_rotate_l l n i:
  i < length l → rotate n l !! rotate_nat_sub n i (length l) = l !! i.
Proof.
  intros ?. rewrite lookup_rotate_r, rotate_nat_add_sub;[done..|].
  apply rotate_nat_sub_lt. lia.
Qed.

Lemma elem_of_rotate l n x:
  x ∈ rotate n l ↔ x ∈ l.
Proof.
  unfold rotate. rewrite <-(take_drop (n `mod` length l) l) at 5.
  rewrite !elem_of_app. naive_solver.
Qed.

Lemma rotate_insert_l l n i x:
  i < length l →
  rotate n (<[rotate_nat_add n i (length l):=x]> l) = <[i:=x]> (rotate n l).
Proof.
  intros Hlen. pose proof (Nat.mod_upper_bound n (length l)) as ?. unfold rotate.
  rewrite insert_length, rotate_nat_add_add_mod, rotate_nat_add_alt by lia.
  remember (n `mod` length l) as n'.
  case_decide.
  - rewrite take_insert, drop_insert_le, insert_app_l
      by (rewrite ?drop_length; lia). do 2 f_equal. lia.
  - rewrite take_insert_lt, drop_insert_gt, insert_app_r_alt, drop_length
      by (rewrite ?drop_length; lia). do 2 f_equal. lia.
Qed.

Lemma rotate_insert_r l n i x:
  i < length l →
  rotate n (<[i:=x]> l) = <[rotate_nat_sub n i (length l):=x]> (rotate n l).
Proof.
  intros ?. rewrite <-rotate_insert_l, rotate_nat_add_sub;[done..|].
  apply rotate_nat_sub_lt. lia.
Qed.

(** ** Properties of the [rotate_take] function *)
Lemma rotate_take_insert l s e i x:
  i < length l →
  rotate_take s e (<[i:=x]>l) =
  if decide (rotate_nat_sub s i (length l) < rotate_nat_sub s e (length l)) then
    <[rotate_nat_sub s i (length l):=x]> (rotate_take s e l) else rotate_take s e l.
Proof.
  intros ?. unfold rotate_take. rewrite rotate_insert_r, insert_length by done.
  case_decide; [rewrite take_insert_lt | rewrite take_insert]; naive_solver lia.
Qed.

Lemma rotate_take_add l b i :
  i < length l →
  rotate_take b (rotate_nat_add b i (length l)) l = take i (rotate b l).
Proof. intros ?. unfold rotate_take. by rewrite rotate_nat_sub_add. Qed.

(** ** Properties of the [reshape] function *)
Lemma reshape_length szs l : length (reshape szs l) = length szs.
Proof. revert l. by induction szs; intros; f_equal/=. Qed.
End general_properties.

Section more_general_properties.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

(** ** Properties of [sublist_lookup] and [sublist_alter] *)
Lemma sublist_lookup_length l i n k :
  sublist_lookup i n l = Some k → length k = n.
Proof.
  unfold sublist_lookup; intros; simplify_option_eq.
  rewrite take_length, drop_length; lia.
Qed.
Lemma sublist_lookup_all l n : length l = n → sublist_lookup 0 n l = Some l.
Proof.
  intros. unfold sublist_lookup; case_option_guard; [|lia].
  by rewrite take_ge by (rewrite drop_length; lia).
Qed.
Lemma sublist_lookup_Some l i n :
  i + n ≤ length l → sublist_lookup i n l = Some (take n (drop i l)).
Proof. by unfold sublist_lookup; intros; simplify_option_eq. Qed.
Lemma sublist_lookup_Some' l i n l' :
  sublist_lookup i n l = Some l' ↔ l' = take n (drop i l) ∧ i + n ≤ length l.
Proof. unfold sublist_lookup. case_option_guard; naive_solver lia. Qed.
Lemma sublist_lookup_None l i n :
  length l < i + n → sublist_lookup i n l = None.
Proof. by unfold sublist_lookup; intros; simplify_option_eq by lia. Qed.
Lemma sublist_eq l k n :
  (n | length l) → (n | length k) →
  (∀ i, sublist_lookup (i * n) n l = sublist_lookup (i * n) n k) → l = k.
Proof.
  revert l k. assert (∀ l i,
    n ≠ 0 → (n | length l) → ¬n * i `div` n + n ≤ length l → length l ≤ i).
  { intros l i ? [j ->] Hjn. apply Nat.nlt_ge; contradict Hjn.
    rewrite <-Nat.mul_succ_r, (Nat.mul_comm n).
    apply Nat.mul_le_mono_r, Nat.le_succ_l, Nat.div_lt_upper_bound; lia. }
  intros l k Hl Hk Hlookup. destruct (decide (n = 0)) as [->|].
  { by rewrite (nil_length_inv l),
      (nil_length_inv k) by eauto using Nat.divide_0_l. }
  apply list_eq; intros i. specialize (Hlookup (i `div` n)).
  rewrite (Nat.mul_comm _ n) in Hlookup.
  unfold sublist_lookup in *; simplify_option_eq;
    [|by rewrite !lookup_ge_None_2 by auto].
  apply (f_equal (.!! i `mod` n)) in Hlookup.
  by rewrite !lookup_take, !lookup_drop, <-!Nat.div_mod in Hlookup
    by (auto using Nat.mod_upper_bound with lia).
Qed.
Lemma sublist_eq_same_length l k j n :
  length l = j * n → length k = j * n →
  (∀ i,i < j → sublist_lookup (i * n) n l = sublist_lookup (i * n) n k) → l = k.
Proof.
  intros Hl Hk ?. destruct (decide (n = 0)) as [->|].
  { by rewrite (nil_length_inv l), (nil_length_inv k) by lia. }
  apply sublist_eq with n; [by exists j|by exists j|].
  intros i. destruct (decide (i < j)); [by auto|].
  assert (∀ m, m = j * n → m < i * n + n).
  { intros ? ->. replace (i * n + n) with (S i * n) by lia.
    apply Nat.mul_lt_mono_pos_r; lia. }
  by rewrite !sublist_lookup_None by auto.
Qed.
Lemma sublist_lookup_reshape l i n m :
  0 < n → length l = m * n →
  reshape (replicate m n) l !! i = sublist_lookup (i * n) n l.
Proof.
  intros Hn Hl. unfold sublist_lookup.  apply option_eq; intros x; split.
  - intros Hx. case_option_guard as Hi.
    { f_equal. clear Hi. revert i l Hl Hx.
      induction m as [|m IH]; intros [|i] l ??; simplify_eq/=; auto.
      rewrite <-drop_drop. apply IH; rewrite ?drop_length; auto with lia. }
    destruct Hi. rewrite Hl, <-Nat.mul_succ_l.
    apply Nat.mul_le_mono_r, Nat.le_succ_l. apply lookup_lt_Some in Hx.
    by rewrite reshape_length, replicate_length in Hx.
  - intros Hx. case_option_guard as Hi; simplify_eq/=.
    revert i l Hl Hi. induction m as [|m IH]; [auto with lia|].
    intros [|i] l ??; simpl; [done|]. rewrite <-drop_drop.
    rewrite IH; rewrite ?drop_length; auto with lia.
Qed.
Lemma sublist_lookup_compose l1 l2 l3 i n j m :
  sublist_lookup i n l1 = Some l2 → sublist_lookup j m l2 = Some l3 →
  sublist_lookup (i + j) m l1 = Some l3.
Proof.
  unfold sublist_lookup; intros; simplify_option_eq;
    repeat match goal with
    | H : _ ≤ length _ |- _ => rewrite take_length, drop_length in H
    end; rewrite ?take_drop_commute, ?drop_drop, ?take_take,
      ?Nat.min_l, Nat.add_assoc by lia; auto with lia.
Qed.
Lemma sublist_alter_length f l i n k :
  sublist_lookup i n l = Some k → length (f k) = n →
  length (sublist_alter f i n l) = length l.
Proof.
  unfold sublist_alter, sublist_lookup. intros Hk ?; simplify_option_eq.
  rewrite !app_length, Hk, !take_length, !drop_length; lia.
Qed.
Lemma sublist_lookup_alter f l i n k :
  sublist_lookup i n l = Some k → length (f k) = n →
  sublist_lookup i n (sublist_alter f i n l) = f <$> sublist_lookup i n l.
Proof.
  unfold sublist_lookup. intros Hk ?. erewrite sublist_alter_length by eauto.
  unfold sublist_alter; simplify_option_eq.
  by rewrite Hk, drop_app_length', take_app_length' by (rewrite ?take_length; lia).
Qed.
Lemma sublist_lookup_alter_ne f l i j n k :
  sublist_lookup j n l = Some k → length (f k) = n → i + n ≤ j ∨ j + n ≤ i →
  sublist_lookup i n (sublist_alter f j n l) = sublist_lookup i n l.
Proof.
  unfold sublist_lookup. intros Hk Hi ?. erewrite sublist_alter_length by eauto.
  unfold sublist_alter; simplify_option_eq; f_equal; rewrite Hk.
  apply list_eq; intros ii.
  destruct (decide (ii < length (f k))); [|by rewrite !lookup_take_ge by lia].
  rewrite !lookup_take, !lookup_drop by done. destruct (decide (i + ii < j)).
  { by rewrite lookup_app_l, lookup_take by (rewrite ?take_length; lia). }
  rewrite lookup_app_r by (rewrite take_length; lia).
  rewrite take_length_le, lookup_app_r, lookup_drop by lia. f_equal; lia.
Qed.
Lemma sublist_alter_all f l n : length l = n → sublist_alter f 0 n l = f l.
Proof.
  intros <-. unfold sublist_alter; simpl.
  by rewrite drop_all, (right_id_L [] (++)), take_ge.
Qed.
Lemma sublist_alter_compose f g l i n k :
  sublist_lookup i n l = Some k → length (f k) = n → length (g k) = n →
  sublist_alter (f ∘ g) i n l = sublist_alter f i n (sublist_alter g i n l).
Proof.
  unfold sublist_alter, sublist_lookup. intros Hk ??; simplify_option_eq.
  by rewrite !take_app_length', drop_app_length', !(assoc_L (++)), drop_app_length',
    take_app_length' by (rewrite ?app_length, ?take_length, ?Hk; lia).
Qed.

(** ** Properties of the [mask] function *)
Lemma mask_nil f βs : mask f βs [] =@{list A} [].
Proof. by destruct βs. Qed.
Lemma mask_length f βs l : length (mask f βs l) = length l.
Proof. revert βs. induction l; intros [|??]; f_equal/=; auto. Qed.
Lemma mask_true f l n : length l ≤ n → mask f (replicate n true) l = f <$> l.
Proof. revert n. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.
Lemma mask_false f l n : mask f (replicate n false) l = l.
Proof. revert l. induction n; intros [|??]; f_equal/=; auto. Qed.
Lemma mask_app f βs1 βs2 l :
  mask f (βs1 ++ βs2) l
  = mask f βs1 (take (length βs1) l) ++ mask f βs2 (drop (length βs1) l).
Proof. revert l. induction βs1;intros [|??]; f_equal/=; auto using mask_nil. Qed.
Lemma mask_app_2 f βs l1 l2 :
  mask f βs (l1 ++ l2)
  = mask f (take (length l1) βs) l1 ++ mask f (drop (length l1) βs) l2.
Proof. revert βs. induction l1; intros [|??]; f_equal/=; auto. Qed.
Lemma take_mask f βs l n : take n (mask f βs l) = mask f (take n βs) (take n l).
Proof. revert n βs. induction l; intros [|?] [|[] ?]; f_equal/=; auto. Qed.
Lemma drop_mask f βs l n : drop n (mask f βs l) = mask f (drop n βs) (drop n l).
Proof.
  revert n βs. induction l; intros [|?] [|[] ?]; f_equal/=; auto using mask_nil.
Qed.
Lemma sublist_lookup_mask f βs l i n :
  sublist_lookup i n (mask f βs l)
  = mask f (take n (drop i βs)) <$> sublist_lookup i n l.
Proof.
  unfold sublist_lookup; rewrite mask_length; simplify_option_eq; auto.
  by rewrite drop_mask, take_mask.
Qed.
Lemma mask_mask f g βs1 βs2 l :
  (∀ x, f (g x) = f x) → βs1 =.>* βs2 →
  mask f βs2 (mask g βs1 l) = mask f βs2 l.
Proof.
  intros ? Hβs. revert l. by induction Hβs as [|[] []]; intros [|??]; f_equal/=.
Qed.
Lemma lookup_mask f βs l i :
  βs !! i = Some true → mask f βs l !! i = f <$> l !! i.
Proof.
  revert i βs. induction l; intros [] [] ?; simplify_eq/=; f_equal; auto.
Qed.
Lemma lookup_mask_notin f βs l i :
  βs !! i ≠ Some true → mask f βs l !! i = l !! i.
Proof.
  revert i βs. induction l; intros [] [|[]] ?; simplify_eq/=; auto.
Qed.

(** ** Properties of the [Permutation] predicate *)
Lemma Permutation_nil_r l : l ≡ₚ [] ↔ l = [].
Proof. split; [by intro; apply Permutation_nil | by intros ->]. Qed.
Lemma Permutation_singleton_r l x : l ≡ₚ [x] ↔ l = [x].
Proof. split; [by intro; apply Permutation_length_1_inv | by intros ->]. Qed.
Lemma Permutation_nil_l l : [] ≡ₚ l ↔ [] = l.
Proof. by rewrite (symmetry_iff (≡ₚ)), Permutation_nil_r. Qed.
Lemma Permutation_singleton_l l x : [x] ≡ₚ l ↔ [x] = l.
Proof. by rewrite (symmetry_iff (≡ₚ)), Permutation_singleton_r. Qed.

Lemma Permutation_skip x l l' : l ≡ₚ l' → x :: l ≡ₚ x :: l'.
Proof. apply perm_skip. Qed.
Lemma Permutation_swap x y l : y :: x :: l ≡ₚ x :: y :: l.
Proof. apply perm_swap. Qed.
Lemma Permutation_singleton_inj x y : [x] ≡ₚ [y] → x = y.
Proof. apply Permutation_length_1. Qed.

Global Instance length_Permutation_proper : Proper ((≡ₚ) ==> (=)) (@length A).
Proof. induction 1; simpl; auto with lia. Qed.
Global Instance elem_of_Permutation_proper x : Proper ((≡ₚ) ==> iff) (x ∈.).
Proof. induction 1; rewrite ?elem_of_nil, ?elem_of_cons; intuition. Qed.
Global Instance NoDup_Permutation_proper: Proper ((≡ₚ) ==> iff) (@NoDup A).
Proof.
  induction 1 as [|x l k Hlk IH | |].
  - by rewrite !NoDup_nil.
  - by rewrite !NoDup_cons, IH, Hlk.
  - rewrite !NoDup_cons, !elem_of_cons. intuition.
  - intuition.
Qed.

Global Instance app_Permutation_comm : Comm (≡ₚ) (@app A).
Proof.
  intros l1. induction l1 as [|x l1 IH]; intros l2; simpl.
  - by rewrite (right_id_L [] (++)).
  - rewrite Permutation_middle, IH. simpl. by rewrite Permutation_middle.
Qed.

Global Instance cons_Permutation_inj_r x : Inj (≡ₚ) (≡ₚ) (x ::.).
Proof. red. eauto using Permutation_cons_inv. Qed.
Global Instance app_Permutation_inj_r k : Inj (≡ₚ) (≡ₚ) (k ++.).
Proof.
  induction k as [|x k IH]; intros l1 l2; simpl; auto.
  intros. by apply IH, (inj (x ::.)).
Qed.
Global Instance cons_Permutation_inj_l k : Inj (=) (≡ₚ) (.:: k).
Proof.
  intros x1 x2 Hperm. apply Permutation_singleton_inj.
  apply (inj (k ++.)). by rewrite !(comm (++) k).
Qed.
Global Instance app_Permutation_inj_l k : Inj (≡ₚ) (≡ₚ) (.++ k).
Proof. intros l1 l2. rewrite !(comm (++) _ k). by apply (inj (k ++.)). Qed.

Lemma replicate_Permutation n x l : replicate n x ≡ₚ l → replicate n x = l.
Proof.
  intros Hl. apply replicate_as_elem_of. split.
  - by rewrite <-Hl, replicate_length.
  - intros y. rewrite <-Hl. by apply elem_of_replicate_inv.
Qed.
Lemma reverse_Permutation l : reverse l ≡ₚ l.
Proof.
  induction l as [|x l IH]; [done|].
  by rewrite reverse_cons, (comm (++)), IH.
Qed.
Lemma delete_Permutation l i x : l !! i = Some x → l ≡ₚ x :: delete i l.
Proof.
  revert i; induction l as [|y l IH]; intros [|i] ?; simplify_eq/=; auto.
  by rewrite Permutation_swap, <-(IH i).
Qed.
Lemma elem_of_Permutation l x : x ∈ l ↔ ∃ k, l ≡ₚ x :: k.
Proof.
  split.
  - intros [i ?]%elem_of_list_lookup. eexists. by apply delete_Permutation.
  - intros [k ->]. by left.
Qed.

Lemma Permutation_cons_inv_r l k x :
  k ≡ₚ x :: l → ∃ k1 k2, k = k1 ++ x :: k2 ∧ l ≡ₚ k1 ++ k2.
Proof.
  intros Hk. assert (∃ i, k !! i = Some x) as [i Hi].
  { apply elem_of_list_lookup. rewrite Hk, elem_of_cons; auto. }
  exists (take i k), (drop (S i) k). split.
  - by rewrite take_drop_middle.
  - rewrite <-delete_take_drop. apply (inj (x ::.)).
    by rewrite <-Hk, <-(delete_Permutation k) by done.
Qed.
Lemma Permutation_cons_inv_l l k x :
  x :: l ≡ₚ k → ∃ k1 k2, k = k1 ++ x :: k2 ∧ l ≡ₚ k1 ++ k2.
Proof. by intros ?%(symmetry_iff (≡ₚ))%Permutation_cons_inv_r. Qed.

Lemma Permutation_cross_split (la lb lc ld : list A) :
  la ++ lb ≡ₚ lc ++ ld →
  ∃ lac lad lbc lbd,
    lac ++ lad ≡ₚ la ∧ lbc ++ lbd ≡ₚ lb ∧ lac ++ lbc ≡ₚ lc ∧ lad ++ lbd ≡ₚ ld.
Proof.
  revert lc ld.
  induction la as [|x la IH]; simpl; intros lc ld Hperm.
  { exists [], [], lc, ld. by rewrite !(right_id_L [] (++)). }
  assert (x ∈ lc ++ ld)
    as [[lc' Hlc]%elem_of_Permutation|[ld' Hld]%elem_of_Permutation]%elem_of_app.
  { rewrite <-Hperm, elem_of_cons. auto. }
  - rewrite Hlc in Hperm. simpl in Hperm. apply (inj (x ::.)) in Hperm.
    apply IH in Hperm as (lac&lad&lbc&lbd&Ha&Hb&Hc&Hd).
    exists (x :: lac), lad, lbc, lbd; simpl. by rewrite Ha, Hb, Hc, Hd.
  - rewrite Hld, <-Permutation_middle in Hperm. apply (inj (x ::.)) in Hperm.
    apply IH in Hperm as (lac&lad&lbc&lbd&Ha&Hb&Hc&Hd).
    exists lac, (x :: lad), lbc, lbd; simpl.
    by rewrite <-Permutation_middle, Ha, Hb, Hc, Hd.
Qed.

Lemma Permutation_inj l1 l2 :
  Permutation l1 l2 ↔
    length l1 = length l2 ∧
    ∃ f : nat → nat, Inj (=) (=) f ∧ ∀ i, l1 !! i = l2 !! f i.
Proof.
  split.
  - intros Hl; split; [by apply Permutation_length|].
    induction Hl as [|x l1 l2 _ [f [??]]|x y l|l1 l2 l3 _ [f [? Hf]] _ [g [? Hg]]].
    + exists id; split; [apply _|done].
    + exists (λ i, match i with 0 => 0 | S i => S (f i) end); split.
      * by intros [|i] [|j] ?; simplify_eq/=.
      * intros [|i]; simpl; auto.
    + exists (λ i, match i with 0 => 1 | 1 => 0 | _ => i end); split.
      * intros [|[|i]] [|[|j]]; congruence.
      * by intros [|[|i]].
    + exists (g ∘ f); split; [apply _|]. intros i; simpl. by rewrite <-Hg, <-Hf.
  - intros (Hlen & f & Hf & Hl). revert l2 f Hlen Hf Hl.
    induction l1 as [|x l1 IH]; intros l2 f Hlen Hf Hl; [by destruct l2|].
    rewrite (delete_Permutation l2 (f 0) x) by (by rewrite <-Hl).
    pose (g n := let m := f (S n) in if lt_eq_lt_dec m (f 0) then m else m - 1).
    apply Permutation_skip, (IH _ g).
    + rewrite length_delete by (rewrite <-Hl; eauto); simpl in *; lia.
    + unfold g. intros i j Hg.
      repeat destruct (lt_eq_lt_dec _ _) as [[?|?]|?]; simplify_eq/=; try lia.
      apply (inj S), (inj f); lia.
    + intros i. unfold g. destruct (lt_eq_lt_dec _ _) as [[?|?]|?].
      * by rewrite lookup_delete_lt, <-Hl.
      * simplify_eq.
      * rewrite lookup_delete_ge, <-Nat.sub_succ_l by lia; simpl.
        by rewrite Nat.sub_0_r, <-Hl.
Qed.

(** ** Properties of the [filter] function *)
Section filter.
  Context (P : A → Prop) `{∀ x, Decision (P x)}.
  Local Arguments filter {_ _ _} _ {_} !_ /.

  Lemma filter_nil : filter P [] = [].
  Proof. done. Qed.
  Lemma filter_cons x l :
    filter P (x :: l) = if decide (P x) then x :: filter P l else filter P l.
  Proof. done. Qed.
  Lemma filter_cons_True x l : P x → filter P (x :: l) = x :: filter P l.
  Proof. intros. by rewrite filter_cons, decide_True. Qed.
  Lemma filter_cons_False x l : ¬P x → filter P (x :: l) = filter P l.
  Proof. intros. by rewrite filter_cons, decide_False. Qed.

  Lemma filter_app l1 l2 : filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
  Proof.
    induction l1 as [|x l1 IH]; simpl; [done| ].
    case_decide; [|done].
    by rewrite IH.
  Qed.

  Lemma elem_of_list_filter l x : x ∈ filter P l ↔ P x ∧ x ∈ l.
  Proof.
    induction l; simpl; repeat case_decide;
      rewrite ?elem_of_nil, ?elem_of_cons; naive_solver.
  Qed.
  Lemma NoDup_filter l : NoDup l → NoDup (filter P l).
  Proof.
    induction 1; simpl; repeat case_decide;
      rewrite ?NoDup_nil, ?NoDup_cons, ?elem_of_list_filter; tauto.
  Qed.

  Global Instance filter_Permutation : Proper ((≡ₚ) ==> (≡ₚ)) (filter P).
  Proof. induction 1; repeat (simpl; repeat case_decide); by econstructor. Qed.

  Lemma filter_length l : length (filter P l) ≤ length l.
  Proof. induction l; simpl; repeat case_decide; simpl; lia. Qed.
  Lemma filter_length_lt l x : x ∈ l → ¬P x → length (filter P l) < length l.
  Proof.
    intros [k ->]%elem_of_Permutation ?; simpl.
    rewrite decide_False, Nat.lt_succ_r by done. apply filter_length.
  Qed.
  Lemma filter_nil_not_elem_of l x : filter P l = [] → P x → x ∉ l.
  Proof. induction 3; simplify_eq/=; case_decide; naive_solver. Qed.
  Lemma filter_reverse l : filter P (reverse l) = reverse (filter P l).
  Proof.
    induction l as [|x l IHl]; [done|].
    rewrite reverse_cons, filter_app, IHl, !filter_cons.
    case_decide; [by rewrite reverse_cons|by rewrite filter_nil, app_nil_r].
  Qed.

  Lemma filter_app_complement l : filter P l ++ filter (λ x, ¬P x) l ≡ₚ l.
  Proof.
    induction l as [|x l IH]; simpl; [done|]. case_decide.
    - rewrite decide_False by naive_solver. simpl. by rewrite IH.
    - rewrite decide_True by done. by rewrite <-Permutation_middle, IH.
  Qed.
End filter.

Lemma list_filter_iff (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ x, P1 x ↔ P2 x) →
  filter P1 l = filter P2 l.
Proof.
  intros HPiff. induction l as [|a l IH]; [done|].
  destruct (decide (P1 a)).
  - rewrite !filter_cons_True by naive_solver. by rewrite IH.
  - rewrite !filter_cons_False by naive_solver. by rewrite IH.
Qed.

Lemma list_filter_filter (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  filter P1 (filter P2 l) = filter (λ a, P1 a ∧ P2 a) l.
Proof.
  induction l as [|x l IH]; [done|].
  rewrite !filter_cons. case (decide (P2 x)) as [HP2|HP2].
  - rewrite filter_cons, IH. apply decide_ext. naive_solver.
  - rewrite IH. symmetry. apply decide_False. by intros [_ ?].
Qed.

Lemma list_filter_filter_l (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ x, P1 x → P2 x) →
  filter P1 (filter P2 l) = filter P1 l.
Proof.
  intros HPimp. rewrite list_filter_filter.
  apply list_filter_iff. naive_solver.
Qed.

Lemma list_filter_filter_r (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  (∀ x, P2 x → P1 x) →
  filter P1 (filter P2 l) = filter P2 l.
Proof.
  intros HPimp. rewrite list_filter_filter.
  apply list_filter_iff. naive_solver.
Qed.

(** ** Properties of the [prefix] and [suffix] predicates *)
Global Instance: PartialOrder (@prefix A).
Proof.
  split; [split|].
  - intros ?. eexists []. by rewrite (right_id_L [] (++)).
  - intros ???[k1->] [k2->]. exists (k1 ++ k2). by rewrite (assoc_L (++)).
  - intros l1 l2 [k1 ?] [[|x2 k2] ->]; [|discriminate_list].
    by rewrite (right_id_L _ _).
Qed.
Lemma prefix_nil l : [] `prefix_of` l.
Proof. by exists l. Qed.
Lemma prefix_nil_inv l : l `prefix_of` [] → l = [].
Proof. intros [k ?]. by destruct l. Qed.
Lemma prefix_nil_not x l : ¬x :: l `prefix_of` [].
Proof. by intros [k ?]. Qed.
Lemma prefix_cons x l1 l2 : l1 `prefix_of` l2 → x :: l1 `prefix_of` x :: l2.
Proof. intros [k ->]. by exists k. Qed.
Lemma prefix_cons_alt x y l1 l2 :
  x = y → l1 `prefix_of` l2 → x :: l1 `prefix_of` y :: l2.
Proof. intros ->. apply prefix_cons. Qed.
Lemma prefix_cons_inv_1 x y l1 l2 : x :: l1 `prefix_of` y :: l2 → x = y.
Proof. by intros [k ?]; simplify_eq/=. Qed.
Lemma prefix_cons_inv_2 x y l1 l2 :
  x :: l1 `prefix_of` y :: l2 → l1 `prefix_of` l2.
Proof. intros [k ?]; simplify_eq/=. by exists k. Qed.
Lemma prefix_app k l1 l2 : l1 `prefix_of` l2 → k ++ l1 `prefix_of` k ++ l2.
Proof. intros [k' ->]. exists k'. by rewrite (assoc_L (++)). Qed.
Lemma prefix_app_alt k1 k2 l1 l2 :
  k1 = k2 → l1 `prefix_of` l2 → k1 ++ l1 `prefix_of` k2 ++ l2.
Proof. intros ->. apply prefix_app. Qed.
Lemma prefix_app_inv k l1 l2 :
  k ++ l1 `prefix_of` k ++ l2 → l1 `prefix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite <-(assoc_L (++)) in E. by simplify_list_eq.
Qed.
Lemma prefix_app_l l1 l2 l3 : l1 ++ l3 `prefix_of` l2 → l1 `prefix_of` l2.
Proof. intros [k ->]. exists (l3 ++ k). by rewrite (assoc_L (++)). Qed.
Lemma prefix_app_r l1 l2 l3 : l1 `prefix_of` l2 → l1 `prefix_of` l2 ++ l3.
Proof. intros [k ->]. exists (k ++ l3). by rewrite (assoc_L (++)). Qed.
Lemma prefix_take l n : take n l `prefix_of` l.
Proof. rewrite <-(take_drop n l) at 2. apply prefix_app_r. done. Qed.
Lemma prefix_lookup_lt l1 l2 i :
  i < length l1 → l1 `prefix_of` l2 → l1 !! i = l2 !! i.
Proof. intros ? [? ->]. by rewrite lookup_app_l. Qed.
Lemma prefix_lookup_Some l1 l2 i x :
  l1 !! i = Some x → l1 `prefix_of` l2 → l2 !! i = Some x.
Proof. intros ? [k ->]. rewrite lookup_app_l; eauto using lookup_lt_Some. Qed.
Lemma prefix_length l1 l2 : l1 `prefix_of` l2 → length l1 ≤ length l2.
Proof. intros [? ->]. rewrite app_length. lia. Qed.
Lemma prefix_snoc_not l x : ¬l ++ [x] `prefix_of` l.
Proof. intros [??]. discriminate_list. Qed.
Lemma elem_of_prefix l1 l2 x :
  x ∈ l1 → l1 `prefix_of` l2 → x ∈ l2.
Proof. intros Hin [l' ->]. apply elem_of_app. by left. Qed.
(* [prefix] is not a total order, but [l1] and [l2] are always comparable if
  they are both prefixes of some [l3]. *)
Lemma prefix_weak_total l1 l2 l3 :
  l1 `prefix_of` l3 → l2 `prefix_of` l3 → l1 `prefix_of` l2 ∨ l2 `prefix_of` l1.
Proof.
  intros [k1 H1] [k2 H2]. rewrite H2 in H1.
  apply app_eq_inv in H1 as [(k&?&?)|(k&?&?)]; [left|right]; exists k; eauto.
Qed.
Global Instance: PartialOrder (@suffix A).
Proof.
  split; [split|].
  - intros ?. by eexists [].
  - intros ???[k1->] [k2->]. exists (k2 ++ k1). by rewrite (assoc_L (++)).
  - intros l1 l2 [k1 ?] [[|x2 k2] ->]; [done|discriminate_list].
Qed.
Global Instance prefix_dec `{!EqDecision A} : RelDecision prefix :=
  fix go l1 l2 :=
  match l1, l2  with
  | [], _ => left (prefix_nil _)
  | _, [] => right (prefix_nil_not _ _)
  | x :: l1, y :: l2 =>
    match decide_rel (=) x y with
    | left Hxy =>
      match go l1 l2 with
      | left Hl1l2 => left (prefix_cons_alt _ _ _ _ Hxy Hl1l2)
      | right Hl1l2 => right (Hl1l2 ∘ prefix_cons_inv_2 _ _ _ _)
      end
    | right Hxy => right (Hxy ∘ prefix_cons_inv_1 _ _ _ _)
    end
  end.
Lemma prefix_not_elem_of_app_cons_inv x y l1 l2 k1 k2 :
  x ∉ k1 → y ∉ l1 →
  (l1 ++ x :: l2) `prefix_of` (k1 ++ y :: k2) →
  l1 = k1 ∧ x = y ∧ l2 `prefix_of` k2.
Proof.
  intros Hin1 Hin2 [k Hle]. rewrite <-(assoc_L (++)) in Hle.
  apply not_elem_of_app_cons_inv_l in Hle; [|done..]. unfold prefix. naive_solver.
Qed.

Lemma prefix_length_eq l1 l2 :
  l1 `prefix_of` l2 → length l2 ≤ length l1 → l1 = l2.
Proof.
  intros Hprefix Hlen. assert (length l1 = length l2).
  { apply prefix_length in Hprefix. lia. }
  eapply list_eq_same_length with (length l1); [done..|].
  intros i x y _ ??. assert (l2 !! i = Some x) by eauto using prefix_lookup_Some.
  congruence.
Qed.

Section prefix_ops.
  Context `{!EqDecision A}.
  Lemma max_prefix_fst l1 l2 :
    l1 = (max_prefix l1 l2).2 ++ (max_prefix l1 l2).1.1.
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; f_equal/=; auto.
  Qed.
  Lemma max_prefix_fst_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1, k2, k3) → l1 = k3 ++ k1.
  Proof.
    intros. pose proof (max_prefix_fst l1 l2).
    by destruct (max_prefix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_prefix_fst_prefix l1 l2 : (max_prefix l1 l2).2 `prefix_of` l1.
  Proof. eexists. apply max_prefix_fst. Qed.
  Lemma max_prefix_fst_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1, k2, k3) → k3 `prefix_of` l1.
  Proof. eexists. eauto using max_prefix_fst_alt. Qed.
  Lemma max_prefix_snd l1 l2 :
    l2 = (max_prefix l1 l2).2 ++ (max_prefix l1 l2).1.2.
  Proof.
    revert l2. induction l1; intros [|??]; simpl;
      repeat case_decide; f_equal/=; auto.
  Qed.
  Lemma max_prefix_snd_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1, k2, k3) → l2 = k3 ++ k2.
  Proof.
    intro. pose proof (max_prefix_snd l1 l2).
    by destruct (max_prefix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_prefix_snd_prefix l1 l2 : (max_prefix l1 l2).2 `prefix_of` l2.
  Proof. eexists. apply max_prefix_snd. Qed.
  Lemma max_prefix_snd_prefix_alt l1 l2 k1 k2 k3 :
    max_prefix l1 l2 = (k1,k2,k3) → k3 `prefix_of` l2.
  Proof. eexists. eauto using max_prefix_snd_alt. Qed.
  Lemma max_prefix_max l1 l2 k :
    k `prefix_of` l1 → k `prefix_of` l2 → k `prefix_of` (max_prefix l1 l2).2.
  Proof.
    intros [l1' ->] [l2' ->]. by induction k; simpl; repeat case_decide;
      simpl; auto using prefix_nil, prefix_cons.
  Qed.
  Lemma max_prefix_max_alt l1 l2 k1 k2 k3 k :
    max_prefix l1 l2 = (k1,k2,k3) →
    k `prefix_of` l1 → k `prefix_of` l2 → k `prefix_of` k3.
  Proof.
    intro. pose proof (max_prefix_max l1 l2 k).
    by destruct (max_prefix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_prefix_max_snoc l1 l2 k1 k2 k3 x1 x2 :
    max_prefix l1 l2 = (x1 :: k1, x2 :: k2, k3) → x1 ≠ x2.
  Proof.
    intros Hl ->. destruct (prefix_snoc_not k3 x2).
    eapply max_prefix_max_alt; eauto.
    - rewrite (max_prefix_fst_alt _ _ _ _ _ Hl).
      apply prefix_app, prefix_cons, prefix_nil.
    - rewrite (max_prefix_snd_alt _ _ _ _ _ Hl).
      apply prefix_app, prefix_cons, prefix_nil.
  Qed.
End prefix_ops.

Lemma prefix_suffix_reverse l1 l2 :
  l1 `prefix_of` l2 ↔ reverse l1 `suffix_of` reverse l2.
Proof.
  split; intros [k E]; exists (reverse k).
  - by rewrite E, reverse_app.
  - by rewrite <-(reverse_involutive l2), E, reverse_app, reverse_involutive.
Qed.
Lemma suffix_prefix_reverse l1 l2 :
  l1 `suffix_of` l2 ↔ reverse l1 `prefix_of` reverse l2.
Proof. by rewrite prefix_suffix_reverse, !reverse_involutive. Qed.
Lemma suffix_nil l : [] `suffix_of` l.
Proof. exists l. by rewrite (right_id_L [] (++)). Qed.
Lemma suffix_nil_inv l : l `suffix_of` [] → l = [].
Proof. by intros [[|?] ?]; simplify_list_eq. Qed.
Lemma suffix_cons_nil_inv x l : ¬x :: l `suffix_of` [].
Proof. by intros [[] ?]. Qed.
Lemma suffix_snoc l1 l2 x :
  l1 `suffix_of` l2 → l1 ++ [x] `suffix_of` l2 ++ [x].
Proof. intros [k ->]. exists k. by rewrite (assoc_L (++)). Qed.
Lemma suffix_snoc_alt x y l1 l2 :
  x = y → l1 `suffix_of` l2 → l1 ++ [x] `suffix_of` l2 ++ [y].
Proof. intros ->. apply suffix_snoc. Qed.
Lemma suffix_app l1 l2 k : l1 `suffix_of` l2 → l1 ++ k `suffix_of` l2 ++ k.
Proof. intros [k' ->]. exists k'. by rewrite (assoc_L (++)). Qed.
Lemma suffix_app_alt l1 l2 k1 k2 :
  k1 = k2 → l1 `suffix_of` l2 → l1 ++ k1 `suffix_of` l2 ++ k2.
Proof. intros ->. apply suffix_app. Qed.
Lemma suffix_snoc_inv_1 x y l1 l2 :
  l1 ++ [x] `suffix_of` l2 ++ [y] → x = y.
Proof. intros [k' E]. rewrite (assoc_L (++)) in E. by simplify_list_eq. Qed.
Lemma suffix_snoc_inv_2 x y l1 l2 :
  l1 ++ [x] `suffix_of` l2 ++ [y] → l1 `suffix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite (assoc_L (++)) in E. by simplify_list_eq.
Qed.
Lemma suffix_app_inv l1 l2 k :
  l1 ++ k `suffix_of` l2 ++ k → l1 `suffix_of` l2.
Proof.
  intros [k' E]. exists k'. rewrite (assoc_L (++)) in E. by simplify_list_eq.
Qed.
Lemma suffix_cons_l l1 l2 x : x :: l1 `suffix_of` l2 → l1 `suffix_of` l2.
Proof. intros [k ->]. exists (k ++ [x]). by rewrite <-(assoc_L (++)). Qed.
Lemma suffix_app_l l1 l2 l3 : l3 ++ l1 `suffix_of` l2 → l1 `suffix_of` l2.
Proof. intros [k ->]. exists (k ++ l3). by rewrite <-(assoc_L (++)). Qed.
Lemma suffix_cons_r l1 l2 x : l1 `suffix_of` l2 → l1 `suffix_of` x :: l2.
Proof. intros [k ->]. by exists (x :: k). Qed.
Lemma suffix_app_r l1 l2 l3 : l1 `suffix_of` l2 → l1 `suffix_of` l3 ++ l2.
Proof. intros [k ->]. exists (l3 ++ k). by rewrite (assoc_L (++)). Qed.
Lemma suffix_drop l n : drop n l `suffix_of` l.
Proof. rewrite <-(take_drop n l) at 2. apply suffix_app_r. done. Qed.
Lemma suffix_cons_inv l1 l2 x y :
  x :: l1 `suffix_of` y :: l2 → x :: l1 = y :: l2 ∨ x :: l1 `suffix_of` l2.
Proof.
  intros [[|? k] E]; [by left|]. right. simplify_eq/=. by apply suffix_app_r.
Qed.
Lemma suffix_lookup_lt l1 l2 i :
  i < length l1 →
  l1 `suffix_of` l2 →
  l1 !! i = l2 !! (i + (length l2 - length l1)).
Proof.
  intros Hi [k ->]. rewrite app_length, lookup_app_r by lia. f_equal; lia.
Qed.
Lemma suffix_lookup_Some l1 l2 i x :
  l1 !! i = Some x →
  l1 `suffix_of` l2 →
  l2 !! (i + (length l2 - length l1)) = Some x.
Proof. intros. by rewrite <-suffix_lookup_lt by eauto using lookup_lt_Some. Qed.
Lemma suffix_length l1 l2 : l1 `suffix_of` l2 → length l1 ≤ length l2.
Proof. intros [? ->]. rewrite app_length. lia. Qed.
Lemma suffix_cons_not x l : ¬x :: l `suffix_of` l.
Proof. intros [??]. discriminate_list. Qed.
Lemma elem_of_suffix l1 l2 x :
  x ∈ l1 → l1 `suffix_of` l2 → x ∈ l2.
Proof. intros Hin [l' ->]. apply elem_of_app. by right. Qed.
(* [suffix] is not a total order, but [l1] and [l2] are always comparable if
  they are both suffixes of some [l3]. *)
Lemma suffix_weak_total l1 l2 l3 :
  l1 `suffix_of` l3 → l2 `suffix_of` l3 → l1 `suffix_of` l2 ∨ l2 `suffix_of` l1.
Proof.
  intros [k1 Hl1] [k2 Hl2]. rewrite Hl1 in Hl2.
  apply app_eq_inv in Hl2 as [(k&?&?)|(k&?&?)]; [left|right]; exists k; eauto.
Qed.
Global Instance suffix_dec `{!EqDecision A} : RelDecision (@suffix A).
Proof.
  refine (λ l1 l2, cast_if (decide_rel prefix (reverse l1) (reverse l2)));
   abstract (by rewrite suffix_prefix_reverse).
Defined.
Lemma suffix_not_elem_of_app_cons_inv x y l1 l2 k1 k2 :
  x ∉ k2 → y ∉ l2 →
  (l1 ++ x :: l2) `suffix_of` (k1 ++ y :: k2) →
  l1 `suffix_of` k1 ∧ x = y ∧ l2 = k2.
Proof.
  intros Hin1 Hin2 [k Hle]. rewrite (assoc_L (++)) in Hle.
  apply not_elem_of_app_cons_inv_r in Hle; [|done..]. unfold suffix. naive_solver.
Qed.

Lemma suffix_length_eq l1 l2 :
  l1 `suffix_of` l2 → length l2 ≤ length l1 → l1 = l2.
Proof.
  intros. apply (inj reverse), prefix_length_eq.
  - by apply suffix_prefix_reverse.
  - by rewrite !reverse_length.
Qed.

Section max_suffix.
  Context `{!EqDecision A}.

  Lemma max_suffix_fst l1 l2 :
    l1 = (max_suffix l1 l2).1.1 ++ (max_suffix l1 l2).2.
  Proof.
    rewrite <-(reverse_involutive l1) at 1.
    rewrite (max_prefix_fst (reverse l1) (reverse l2)). unfold max_suffix.
    destruct (max_prefix (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    by rewrite reverse_app.
  Qed.
  Lemma max_suffix_fst_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1, k2, k3) → l1 = k1 ++ k3.
  Proof.
    intro. pose proof (max_suffix_fst l1 l2).
    by destruct (max_suffix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_suffix_fst_suffix l1 l2 : (max_suffix l1 l2).2 `suffix_of` l1.
  Proof. eexists. apply max_suffix_fst. Qed.
  Lemma max_suffix_fst_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1, k2, k3) → k3 `suffix_of` l1.
  Proof. eexists. eauto using max_suffix_fst_alt. Qed.
  Lemma max_suffix_snd l1 l2 :
    l2 = (max_suffix l1 l2).1.2 ++ (max_suffix l1 l2).2.
  Proof.
    rewrite <-(reverse_involutive l2) at 1.
    rewrite (max_prefix_snd (reverse l1) (reverse l2)). unfold max_suffix.
    destruct (max_prefix (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    by rewrite reverse_app.
  Qed.
  Lemma max_suffix_snd_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1,k2,k3) → l2 = k2 ++ k3.
  Proof.
    intro. pose proof (max_suffix_snd l1 l2).
    by destruct (max_suffix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_suffix_snd_suffix l1 l2 : (max_suffix l1 l2).2 `suffix_of` l2.
  Proof. eexists. apply max_suffix_snd. Qed.
  Lemma max_suffix_snd_suffix_alt l1 l2 k1 k2 k3 :
    max_suffix l1 l2 = (k1,k2,k3) → k3 `suffix_of` l2.
  Proof. eexists. eauto using max_suffix_snd_alt. Qed.
  Lemma max_suffix_max l1 l2 k :
    k `suffix_of` l1 → k `suffix_of` l2 → k `suffix_of` (max_suffix l1 l2).2.
  Proof.
    generalize (max_prefix_max (reverse l1) (reverse l2)).
    rewrite !suffix_prefix_reverse. unfold max_suffix.
    destruct (max_prefix (reverse l1) (reverse l2)) as ((?&?)&?); simpl.
    rewrite reverse_involutive. auto.
  Qed.
  Lemma max_suffix_max_alt l1 l2 k1 k2 k3 k :
    max_suffix l1 l2 = (k1, k2, k3) →
    k `suffix_of` l1 → k `suffix_of` l2 → k `suffix_of` k3.
  Proof.
    intro. pose proof (max_suffix_max l1 l2 k).
    by destruct (max_suffix l1 l2) as [[]?]; simplify_eq.
  Qed.
  Lemma max_suffix_max_snoc l1 l2 k1 k2 k3 x1 x2 :
    max_suffix l1 l2 = (k1 ++ [x1], k2 ++ [x2], k3) → x1 ≠ x2.
  Proof.
    intros Hl ->. destruct (suffix_cons_not x2 k3).
    eapply max_suffix_max_alt; eauto.
    - rewrite (max_suffix_fst_alt _ _ _ _ _ Hl).
      by apply (suffix_app [x2]), suffix_app_r.
    - rewrite (max_suffix_snd_alt _ _ _ _ _ Hl).
      by apply (suffix_app [x2]), suffix_app_r.
  Qed.
End max_suffix.

(** ** Properties of the [sublist] predicate *)
Lemma sublist_length l1 l2 : l1 `sublist_of` l2 → length l1 ≤ length l2.
Proof. induction 1; simpl; auto with arith. Qed.
Lemma sublist_nil_l l : [] `sublist_of` l.
Proof. induction l; try constructor; auto. Qed.
Lemma sublist_nil_r l : l `sublist_of` [] ↔ l = [].
Proof. split; [by inversion 1|]. intros ->. constructor. Qed.
Lemma sublist_app l1 l2 k1 k2 :
  l1 `sublist_of` l2 → k1 `sublist_of` k2 → l1 ++ k1 `sublist_of` l2 ++ k2.
Proof. induction 1; simpl; try constructor; auto. Qed.
Lemma sublist_inserts_l k l1 l2 : l1 `sublist_of` l2 → l1 `sublist_of` k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma sublist_inserts_r k l1 l2 : l1 `sublist_of` l2 → l1 `sublist_of` l2 ++ k.
Proof. induction 1; simpl; try constructor; auto using sublist_nil_l. Qed.
Lemma sublist_cons_r x l k :
  l `sublist_of` x :: k ↔ l `sublist_of` k ∨ ∃ l', l = x :: l' ∧ l' `sublist_of` k.
Proof. split; [inversion 1; eauto|]. intros [?|(?&->&?)]; constructor; auto. Qed.
Lemma sublist_cons_l x l k :
  x :: l `sublist_of` k ↔ ∃ k1 k2, k = k1 ++ x :: k2 ∧ l `sublist_of` k2.
Proof.
  split.
  - intros Hlk. induction k as [|y k IH]; inversion Hlk.
    + eexists [], k. by repeat constructor.
    + destruct IH as (k1&k2&->&?); auto. by exists (y :: k1), k2.
  - intros (k1&k2&->&?). by apply sublist_inserts_l, sublist_skip.
Qed.
Lemma sublist_app_r l k1 k2 :
  l `sublist_of` k1 ++ k2 ↔
    ∃ l1 l2, l = l1 ++ l2 ∧ l1 `sublist_of` k1 ∧ l2 `sublist_of` k2.
Proof.
  split.
  - revert l k2. induction k1 as [|y k1 IH]; intros l k2; simpl.
    { eexists [], l. by repeat constructor. }
    rewrite sublist_cons_r. intros [?|(l' & ? &?)]; subst.
    + destruct (IH l k2) as (l1&l2&?&?&?); trivial; subst.
      exists l1, l2. auto using sublist_cons.
    + destruct (IH l' k2) as (l1&l2&?&?&?); trivial; subst.
      exists (y :: l1), l2. auto using sublist_skip.
  - intros (?&?&?&?&?); subst. auto using sublist_app.
Qed.
Lemma sublist_app_l l1 l2 k :
  l1 ++ l2 `sublist_of` k ↔
    ∃ k1 k2, k = k1 ++ k2 ∧ l1 `sublist_of` k1 ∧ l2 `sublist_of` k2.
Proof.
  split.
  - revert l2 k. induction l1 as [|x l1 IH]; intros l2 k; simpl.
    { eexists [], k. by repeat constructor. }
    rewrite sublist_cons_l. intros (k1 & k2 &?&?); subst.
    destruct (IH l2 k2) as (h1 & h2 &?&?&?); trivial; subst.
    exists (k1 ++ x :: h1), h2. rewrite <-(assoc_L (++)).
    auto using sublist_inserts_l, sublist_skip.
  - intros (?&?&?&?&?); subst. auto using sublist_app.
Qed.
Lemma sublist_app_inv_l k l1 l2 : k ++ l1 `sublist_of` k ++ l2 → l1 `sublist_of` l2.
Proof.
  induction k as [|y k IH]; simpl; [done |].
  rewrite sublist_cons_r. intros [Hl12|(?&?&?)]; [|simplify_eq; eauto].
  rewrite sublist_cons_l in Hl12. destruct Hl12 as (k1&k2&Hk&?).
  apply IH. rewrite Hk. eauto using sublist_inserts_l, sublist_cons.
Qed.
Lemma sublist_app_inv_r k l1 l2 : l1 ++ k `sublist_of` l2 ++ k → l1 `sublist_of` l2.
Proof.
  revert l1 l2. induction k as [|y k IH]; intros l1 l2.
  { by rewrite !(right_id_L [] (++)). }
  intros. opose proof* (IH (l1 ++ [_]) (l2 ++ [_])) as Hl12.
  { by rewrite <-!(assoc_L (++)). }
  rewrite sublist_app_l in Hl12. destruct Hl12 as (k1&k2&E&?&Hk2).
  destruct k2 as [|z k2] using rev_ind; [inversion Hk2|].
  rewrite (assoc_L (++)) in E; simplify_list_eq.
  eauto using sublist_inserts_r.
Qed.
Global Instance: PartialOrder (@sublist A).
Proof.
  split; [split|].
  - intros l. induction l; constructor; auto.
  - intros l1 l2 l3 Hl12. revert l3. induction Hl12.
    + auto using sublist_nil_l.
    + intros ?. rewrite sublist_cons_l. intros (?&?&?&?); subst.
      eauto using sublist_inserts_l, sublist_skip.
    + intros ?. rewrite sublist_cons_l. intros (?&?&?&?); subst.
      eauto using sublist_inserts_l, sublist_cons.
  - intros l1 l2 Hl12 Hl21. apply sublist_length in Hl21.
    induction Hl12 as [| |??? Hl12]; f_equal/=; auto with arith.
    apply sublist_length in Hl12. lia.
Qed.
Lemma sublist_take l i : take i l `sublist_of` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_r. Qed.
Lemma sublist_drop l i : drop i l `sublist_of` l.
Proof. rewrite <-(take_drop i l) at 2. by apply sublist_inserts_l. Qed.
Lemma sublist_delete l i : delete i l `sublist_of` l.
Proof. revert i. by induction l; intros [|?]; simpl; constructor. Qed.
Lemma sublist_foldr_delete l is : foldr delete l is `sublist_of` l.
Proof.
  induction is as [|i is IH]; simpl; [done |].
  trans (foldr delete l is); auto using sublist_delete.
Qed.
Lemma sublist_alt l1 l2 : l1 `sublist_of` l2 ↔ ∃ is, l1 = foldr delete l2 is.
Proof.
  split; [|intros [is ->]; apply sublist_foldr_delete].
  intros Hl12. cut (∀ k, ∃ is, k ++ l1 = foldr delete (k ++ l2) is).
  { intros help. apply (help []). }
  induction Hl12 as [|x l1 l2 _ IH|x l1 l2 _ IH]; intros k.
  - by eexists [].
  - destruct (IH (k ++ [x])) as [is His]. exists is.
    by rewrite <-!(assoc_L (++)) in His.
  - destruct (IH k) as [is His]. exists (is ++ [length k]).
    rewrite fold_right_app. simpl. by rewrite delete_middle.
Qed.
Lemma Permutation_sublist l1 l2 l3 :
  l1 ≡ₚ l2 → l2 `sublist_of` l3 → ∃ l4, l1 `sublist_of` l4 ∧ l4 ≡ₚ l3.
Proof.
  intros Hl1l2. revert l3.
  induction Hl1l2 as [|x l1 l2 ? IH|x y l1|l1 l1' l2 ? IH1 ? IH2].
  - intros l3. by exists l3.
  - intros l3. rewrite sublist_cons_l. intros (l3'&l3''&?&?); subst.
    destruct (IH l3'') as (l4&?&Hl4); auto. exists (l3' ++ x :: l4).
    split.
    + by apply sublist_inserts_l, sublist_skip.
    + by rewrite Hl4.
  - intros l3. rewrite sublist_cons_l. intros (l3'&l3''&?& Hl3); subst.
    rewrite sublist_cons_l in Hl3. destruct Hl3 as (l5'&l5''&?& Hl5); subst.
    exists (l3' ++ y :: l5' ++ x :: l5''). split.
    + by do 2 apply sublist_inserts_l, sublist_skip.
    + by rewrite !Permutation_middle, Permutation_swap.
  - intros l3 ?. destruct (IH2 l3) as (l3'&?&?); trivial.
    destruct (IH1 l3') as (l3'' &?&?); trivial. exists l3''.
    split; [done|]. etrans; eauto.
Qed.
Lemma sublist_Permutation l1 l2 l3 :
  l1 `sublist_of` l2 → l2 ≡ₚ l3 → ∃ l4, l1 ≡ₚ l4 ∧ l4 `sublist_of` l3.
Proof.
  intros Hl1l2 Hl2l3. revert l1 Hl1l2.
  induction Hl2l3 as [|x l2 l3 ? IH|x y l2|l2 l2' l3 ? IH1 ? IH2].
  - intros l1. by exists l1.
  - intros l1. rewrite sublist_cons_r. intros [?|(l1'&l1''&?)]; subst.
    { destruct (IH l1) as (l4&?&?); trivial.
      exists l4. split.
      - done.
      - by constructor. }
    destruct (IH l1') as (l4&?&Hl4); auto. exists (x :: l4).
    split; [ by constructor | by constructor ].
  - intros l1. rewrite sublist_cons_r. intros [Hl1|(l1'&l1''&Hl1)]; subst.
    { exists l1. split; [done|]. rewrite sublist_cons_r in Hl1.
      destruct Hl1 as [?|(l1'&?&?)]; subst; by repeat constructor. }
    rewrite sublist_cons_r in Hl1. destruct Hl1 as [?|(l1''&?&?)]; subst.
    + exists (y :: l1'). by repeat constructor.
    + exists (x :: y :: l1''). by repeat constructor.
  - intros l1 ?. destruct (IH1 l1) as (l3'&?&?); trivial.
    destruct (IH2 l3') as (l3'' &?&?); trivial. exists l3''.
    split; [|done]. etrans; eauto.
Qed.

(** Properties of the [submseteq] predicate *)
Lemma submseteq_length l1 l2 : l1 ⊆+ l2 → length l1 ≤ length l2.
Proof. induction 1; simpl; auto with lia. Qed.
Lemma submseteq_nil_l l : [] ⊆+ l.
Proof. induction l; constructor; auto. Qed.
Lemma submseteq_nil_r l : l ⊆+ [] ↔ l = [].
Proof.
  split; [|intros ->; constructor].
  intros Hl. apply submseteq_length in Hl. destruct l; simpl in *; auto with lia.
Qed.
Global Instance: PreOrder (@submseteq A).
Proof.
  split.
  - intros l. induction l; constructor; auto.
  - red. apply submseteq_trans.
Qed.
Lemma Permutation_submseteq l1 l2 : l1 ≡ₚ l2 → l1 ⊆+ l2.
Proof. induction 1; econstructor; eauto. Qed.
Lemma sublist_submseteq l1 l2 : l1 `sublist_of` l2 → l1 ⊆+ l2.
Proof. induction 1; constructor; auto. Qed.
Lemma submseteq_Permutation l1 l2 : l1 ⊆+ l2 → ∃ k, l2 ≡ₚ l1 ++ k.
Proof.
  induction 1 as
    [|x y l ? [k Hk]| |x l1 l2 ? [k Hk]|l1 l2 l3 ? [k Hk] ? [k' Hk']].
  - by eexists [].
  - exists k. by rewrite Hk.
  - eexists []. rewrite (right_id_L [] (++)). by constructor.
  - exists (x :: k). by rewrite Hk, Permutation_middle.
  - exists (k ++ k'). by rewrite Hk', Hk, (assoc_L (++)).
Qed.

Global Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (@submseteq A).
Proof.
  intros l1 l2 ? k1 k2 ?. split; intros.
  - trans l1; [by apply Permutation_submseteq|].
    trans k1; [done|]. by apply Permutation_submseteq.
  - trans l2; [by apply Permutation_submseteq|].
    trans k2; [done|]. by apply Permutation_submseteq.
Qed.

Lemma submseteq_length_Permutation l1 l2 :
  l1 ⊆+ l2 → length l2 ≤ length l1 → l1 ≡ₚ l2.
Proof.
  intros Hsub Hlen. destruct (submseteq_Permutation l1 l2) as [[|??] Hk]; auto.
  - by rewrite Hk, (right_id_L [] (++)).
  - rewrite Hk, app_length in Hlen. simpl in *; lia.
Qed.

Global Instance: AntiSymm (≡ₚ) (@submseteq A).
Proof.
  intros l1 l2 ??.
  apply submseteq_length_Permutation; auto using submseteq_length.
Qed.

Lemma elem_of_submseteq l k x : x ∈ l → l ⊆+ k → x ∈ k.
Proof. intros ? [l' ->]%submseteq_Permutation. apply elem_of_app; auto. Qed.
Lemma lookup_submseteq l k i x :
  l !! i = Some x →
  l ⊆+ k →
  ∃ j, k !! j = Some x.
Proof.
  intros Hsub Hlook.
  eapply elem_of_list_lookup_1, elem_of_submseteq;
    eauto using elem_of_list_lookup_2.
Qed.

Lemma submseteq_take l i : take i l ⊆+ l.
Proof. auto using sublist_take, sublist_submseteq. Qed.
Lemma submseteq_drop l i : drop i l ⊆+ l.
Proof. auto using sublist_drop, sublist_submseteq. Qed.
Lemma submseteq_delete l i : delete i l ⊆+ l.
Proof. auto using sublist_delete, sublist_submseteq. Qed.
Lemma submseteq_foldr_delete l is : foldr delete l is `sublist_of` l.
Proof. auto using sublist_foldr_delete, sublist_submseteq. Qed.
Lemma submseteq_sublist_l l1 l3 : l1 ⊆+ l3 ↔ ∃ l2, l1 `sublist_of` l2 ∧ l2 ≡ₚ l3.
Proof.
  split.
  { intros Hl13. elim Hl13; clear l1 l3 Hl13.
    - by eexists [].
    - intros x l1 l3 ? (l2&?&?). exists (x :: l2). by repeat constructor.
    - intros x y l. exists (y :: x :: l). by repeat constructor.
    - intros x l1 l3 ? (l2&?&?). exists (x :: l2). by repeat constructor.
    - intros l1 l3 l5 ? (l2&?&?) ? (l4&?&?).
      destruct (Permutation_sublist l2 l3 l4) as (l3'&?&?); trivial.
      exists l3'. split; etrans; eauto. }
  intros (l2&?&?).
  trans l2; auto using sublist_submseteq, Permutation_submseteq.
Qed.
Lemma submseteq_sublist_r l1 l3 :
  l1 ⊆+ l3 ↔ ∃ l2, l1 ≡ₚ l2 ∧ l2 `sublist_of` l3.
Proof.
  rewrite submseteq_sublist_l.
  split; intros (l2&?&?); eauto using sublist_Permutation, Permutation_sublist.
Qed.
Lemma submseteq_inserts_l k l1 l2 : l1 ⊆+ l2 → l1 ⊆+ k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma submseteq_inserts_r k l1 l2 : l1 ⊆+ l2 → l1 ⊆+ l2 ++ k.
Proof. rewrite (comm (++)). apply submseteq_inserts_l. Qed.
Lemma submseteq_skips_l k l1 l2 : l1 ⊆+ l2 → k ++ l1 ⊆+ k ++ l2.
Proof. induction k; try constructor; auto. Qed.
Lemma submseteq_skips_r k l1 l2 : l1 ⊆+ l2 → l1 ++ k ⊆+ l2 ++ k.
Proof. rewrite !(comm (++) _ k). apply submseteq_skips_l. Qed.
Lemma submseteq_app l1 l2 k1 k2 : l1 ⊆+ l2 → k1 ⊆+ k2 → l1 ++ k1 ⊆+ l2 ++ k2.
Proof. trans (l1 ++ k2); auto using submseteq_skips_l, submseteq_skips_r. Qed.
Lemma submseteq_cons_r x l k :
  l ⊆+ x :: k ↔ l ⊆+ k ∨ ∃ l', l ≡ₚ x :: l' ∧ l' ⊆+ k.
Proof.
  split.
  - rewrite submseteq_sublist_r. intros (l'&E&Hl').
    rewrite sublist_cons_r in Hl'. destruct Hl' as [?|(?&?&?)]; subst.
    + left. rewrite E. eauto using sublist_submseteq.
    + right. eauto using sublist_submseteq.
  - intros [?|(?&E&?)]; [|rewrite E]; by constructor.
Qed.
Lemma submseteq_cons_l x l k : x :: l ⊆+ k ↔ ∃ k', k ≡ₚ x :: k' ∧ l ⊆+ k'.
Proof.
  split.
  - rewrite submseteq_sublist_l. intros (l'&Hl'&E).
    rewrite sublist_cons_l in Hl'. destruct Hl' as (k1&k2&?&?); subst.
    exists (k1 ++ k2). split; eauto using submseteq_inserts_l, sublist_submseteq.
    by rewrite Permutation_middle.
  - intros (?&E&?). rewrite E. by constructor.
Qed.
Lemma submseteq_app_r l k1 k2 :
  l ⊆+ k1 ++ k2 ↔ ∃ l1 l2, l ≡ₚ l1 ++ l2 ∧ l1 ⊆+ k1 ∧ l2 ⊆+ k2.
Proof.
  split.
  - rewrite submseteq_sublist_r. intros (l'&E&Hl').
    rewrite sublist_app_r in Hl'. destruct Hl' as (l1&l2&?&?&?); subst.
    exists l1, l2. eauto using sublist_submseteq.
  - intros (?&?&E&?&?). rewrite E. eauto using submseteq_app.
Qed.
Lemma submseteq_app_l l1 l2 k :
  l1 ++ l2 ⊆+ k ↔ ∃ k1 k2, k ≡ₚ k1 ++ k2 ∧ l1 ⊆+ k1 ∧ l2 ⊆+ k2.
Proof.
  split.
  - rewrite submseteq_sublist_l. intros (l'&Hl'&E).
    rewrite sublist_app_l in Hl'. destruct Hl' as (k1&k2&?&?&?); subst.
    exists k1, k2. split; [done|]. eauto using sublist_submseteq.
  - intros (?&?&E&?&?). rewrite E. eauto using submseteq_app.
Qed.
Lemma submseteq_app_inv_l l1 l2 k : k ++ l1 ⊆+ k ++ l2 → l1 ⊆+ l2.
Proof.
  induction k as [|y k IH]; simpl; [done |]. rewrite submseteq_cons_l.
  intros (?&E%(inj (cons y))&?). apply IH. by rewrite E.
Qed.
Lemma submseteq_app_inv_r l1 l2 k : l1 ++ k ⊆+ l2 ++ k → l1 ⊆+ l2.
Proof. rewrite <-!(comm (++) k). apply submseteq_app_inv_l. Qed.
Lemma submseteq_cons_middle x l k1 k2 : l ⊆+ k1 ++ k2 → x :: l ⊆+ k1 ++ x :: k2.
Proof. rewrite <-Permutation_middle. by apply submseteq_skip. Qed.
Lemma submseteq_app_middle l1 l2 k1 k2 :
  l2 ⊆+ k1 ++ k2 → l1 ++ l2 ⊆+ k1 ++ l1 ++ k2.
Proof.
  rewrite !(assoc (++)), (comm (++) k1 l1), <-(assoc_L (++)).
  by apply submseteq_skips_l.
Qed.
Lemma submseteq_middle l k1 k2 : l ⊆+ k1 ++ l ++ k2.
Proof. by apply submseteq_inserts_l, submseteq_inserts_r. Qed.

Lemma NoDup_submseteq l k : NoDup l → (∀ x, x ∈ l → x ∈ k) → l ⊆+ k.
Proof.
  intros Hl. revert k. induction Hl as [|x l Hx ? IH].
  { intros k Hk. by apply submseteq_nil_l. }
  intros k Hlk. destruct (elem_of_list_split k x) as (l1&l2&?); subst.
  { apply Hlk. by constructor. }
  rewrite <-Permutation_middle. apply submseteq_skip, IH.
  intros y Hy. rewrite elem_of_app.
  specialize (Hlk y). rewrite elem_of_app, !elem_of_cons in Hlk.
  by destruct Hlk as [?|[?|?]]; subst; eauto.
Qed.
Lemma NoDup_Permutation l k : NoDup l → NoDup k → (∀ x, x ∈ l ↔ x ∈ k) → l ≡ₚ k.
Proof.
  intros. apply (anti_symm submseteq); apply NoDup_submseteq; naive_solver.
Qed.

Lemma submseteq_insert l1 l2 i j x y :
  l1 !! i = Some x →
  l2 !! j = Some x →
  l1 ⊆+ l2 →
  (<[i := y]> l1) ⊆+ (<[j := y]> l2).
Proof.
  intros ?? Hsub.
  rewrite !insert_take_drop,
    <-!Permutation_middle by eauto using lookup_lt_Some.
  rewrite <-(take_drop_middle l1 i x), <-(take_drop_middle l2 j x),
    <-!Permutation_middle in Hsub by done.
  by apply submseteq_skip, (submseteq_app_inv_l _ _ [x]).
Qed.

Lemma singleton_submseteq_l l x :
  [x] ⊆+ l ↔ x ∈ l.
Proof.
  split.
  - intros Hsub. eapply elem_of_submseteq; [|done].
    apply elem_of_list_singleton. done.
  - intros (l1&l2&->)%elem_of_list_split.
    apply submseteq_cons_middle, submseteq_nil_l.
Qed.
Lemma singleton_submseteq x y :
  [x] ⊆+ [y] ↔ x = y.
Proof. rewrite singleton_submseteq_l. apply elem_of_list_singleton. Qed.

Section submseteq_dec.
  Context `{!EqDecision A}.

  Lemma list_remove_Permutation l1 l2 k1 x :
    l1 ≡ₚ l2 → list_remove x l1 = Some k1 →
    ∃ k2, list_remove x l2 = Some k2 ∧ k1 ≡ₚ k2.
  Proof.
    intros Hl. revert k1. induction Hl
      as [|y l1 l2 ? IH|y1 y2 l|l1 l2 l3 ? IH1 ? IH2]; simpl; intros k1 Hk1.
    - done.
    - case_decide; simplify_eq; eauto.
      destruct (list_remove x l1) as [l|] eqn:?; simplify_eq.
      destruct (IH l) as (?&?&?); simplify_option_eq; eauto.
    - simplify_option_eq; eauto using Permutation_swap.
    - destruct (IH1 k1) as (k2&?&?); trivial.
      destruct (IH2 k2) as (k3&?&?); trivial.
      exists k3. split; eauto. by trans k2.
  Qed.
  Lemma list_remove_Some l k x : list_remove x l = Some k → l ≡ₚ x :: k.
  Proof.
    revert k. induction l as [|y l IH]; simpl; intros k ?; [done |].
    simplify_option_eq; auto. by rewrite Permutation_swap, <-IH.
  Qed.
  Lemma list_remove_Some_inv l k x :
    l ≡ₚ x :: k → ∃ k', list_remove x l = Some k' ∧ k ≡ₚ k'.
  Proof.
    intros. destruct (list_remove_Permutation (x :: k) l k x) as (k'&?&?).
    - done.
    - simpl; by case_decide.
    - by exists k'.
  Qed.
  Lemma list_remove_list_submseteq l1 l2 :
    l1 ⊆+ l2 ↔ is_Some (list_remove_list l1 l2).
  Proof.
    split.
    - revert l2. induction l1 as [|x l1 IH]; simpl.
      { intros l2 _. by exists l2. }
      intros l2. rewrite submseteq_cons_l. intros (k&Hk&?).
      destruct (list_remove_Some_inv l2 k x) as (k2&?&Hk2); trivial.
      simplify_option_eq. apply IH. by rewrite <-Hk2.
    - intros [k Hk]. revert l2 k Hk.
      induction l1 as [|x l1 IH]; simpl; intros l2 k.
      { intros. apply submseteq_nil_l. }
      destruct (list_remove x l2) as [k'|] eqn:?; intros; simplify_eq.
      rewrite submseteq_cons_l. eauto using list_remove_Some.
  Qed.
  Global Instance submseteq_dec : RelDecision (submseteq : relation (list A)).
  Proof using Type*.
   refine (λ l1 l2, cast_if (decide (is_Some (list_remove_list l1 l2))));
    abstract (rewrite list_remove_list_submseteq; tauto).
  Defined.
  Global Instance Permutation_dec : RelDecision (≡ₚ@{A}).
  Proof using Type*.
    refine (λ l1 l2, cast_if_and
      (decide (l1 ⊆+ l2)) (decide (length l2 ≤ length l1)));
      [by apply submseteq_length_Permutation
      |abstract (intros He; by rewrite He in *)..].
  Defined.
End submseteq_dec.

(** ** Properties of the [Forall] and [Exists] predicate *)
Lemma Forall_Exists_dec (P Q : A → Prop) (dec : ∀ x, {P x} + {Q x}) :
  ∀ l, {Forall P l} + {Exists Q l}.
Proof.
 refine (
  fix go l :=
  match l return {Forall P l} + {Exists Q l} with
  | [] => left _
  | x :: l => cast_if_and (dec x) (go l)
  end); clear go; intuition.
Defined.

(** Export the Coq stdlib constructors under different names,
because we use [Forall_nil] and [Forall_cons] for a version with a biimplication. *)
Definition Forall_nil_2 := @Forall_nil A.
Definition Forall_cons_2 := @Forall_cons A.
Global Instance Forall_proper:
  Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Forall A).
Proof. split; subst; induction 1; constructor; by firstorder auto. Qed.
Global Instance Exists_proper:
  Proper (pointwise_relation _ (↔) ==> (=) ==> (↔)) (@Exists A).
Proof. split; subst; induction 1; constructor; by firstorder auto. Qed.

Section Forall_Exists.
  Context (P : A → Prop).

  Lemma Forall_forall l : Forall P l ↔ ∀ x, x ∈ l → P x.
  Proof.
    split; [induction 1; inversion 1; subst; auto|].
    intros Hin; induction l as [|x l IH]; constructor; [apply Hin; constructor|].
    apply IH. intros ??. apply Hin. by constructor.
  Qed.
  Lemma Forall_nil : Forall P [] ↔ True.
  Proof. done. Qed.
  Lemma Forall_cons_1 x l : Forall P (x :: l) → P x ∧ Forall P l.
  Proof. by inversion 1. Qed.
  Lemma Forall_cons x l : Forall P (x :: l) ↔ P x ∧ Forall P l.
  Proof. split; [by inversion 1|]. intros [??]. by constructor. Qed.
  Lemma Forall_singleton x : Forall P [x] ↔ P x.
  Proof. rewrite Forall_cons, Forall_nil; tauto. Qed.
  Lemma Forall_app_2 l1 l2 : Forall P l1 → Forall P l2 → Forall P (l1 ++ l2).
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall_app l1 l2 : Forall P (l1 ++ l2) ↔ Forall P l1 ∧ Forall P l2.
  Proof.
    split; [induction l1; inversion 1; intuition|].
    intros [??]; auto using Forall_app_2.
  Qed.
  Lemma Forall_true l : (∀ x, P x) → Forall P l.
  Proof. intros ?. induction l; auto. Defined.
  Lemma Forall_impl (Q : A → Prop) l :
    Forall P l → (∀ x, P x → Q x) → Forall Q l.
  Proof. intros H ?. induction H; auto. Defined.
  Lemma Forall_iff l (Q : A → Prop) :
    (∀ x, P x ↔ Q x) → Forall P l ↔ Forall Q l.
  Proof. intros H. apply Forall_proper. { red; apply H. } done. Qed.
  Lemma Forall_not l : length l ≠ 0 → Forall (not ∘ P) l → ¬Forall P l.
  Proof. by destruct 2; inversion 1. Qed.
  Lemma Forall_and {Q} l : Forall (λ x, P x ∧ Q x) l ↔ Forall P l ∧ Forall Q l.
  Proof.
    split; [induction 1; constructor; naive_solver|].
    intros [Hl Hl']; revert Hl'; induction Hl; inversion_clear 1; auto.
  Qed.
  Lemma Forall_and_l {Q} l : Forall (λ x, P x ∧ Q x) l → Forall P l.
  Proof. rewrite Forall_and; tauto. Qed.
  Lemma Forall_and_r {Q} l : Forall (λ x, P x ∧ Q x) l → Forall Q l.
  Proof. rewrite Forall_and; tauto. Qed.
  Lemma Forall_delete l i : Forall P l → Forall P (delete i l).
  Proof. intros H. revert i. by induction H; intros [|i]; try constructor. Qed.

  Lemma Forall_lookup l : Forall P l ↔ ∀ i x, l !! i = Some x → P x.
  Proof.
    rewrite Forall_forall. setoid_rewrite elem_of_list_lookup. naive_solver.
  Qed.
  Lemma Forall_lookup_total `{!Inhabited A} l :
    Forall P l ↔ ∀ i, i < length l → P (l !!! i).
  Proof. rewrite Forall_lookup. setoid_rewrite list_lookup_alt. naive_solver. Qed.
  Lemma Forall_lookup_1 l i x : Forall P l → l !! i = Some x → P x.
  Proof. rewrite Forall_lookup. eauto. Qed.
  Lemma Forall_lookup_total_1 `{!Inhabited A} l i :
    Forall P l → i < length l → P (l !!! i).
  Proof. rewrite Forall_lookup_total. eauto. Qed.
  Lemma Forall_lookup_2 l : (∀ i x, l !! i = Some x → P x) → Forall P l.
  Proof. by rewrite Forall_lookup. Qed.
  Lemma Forall_lookup_total_2 `{!Inhabited A} l :
    (∀ i, i < length l → P (l !!! i)) → Forall P l.
  Proof. by rewrite Forall_lookup_total. Qed.
  Lemma Forall_nth d l : Forall P l ↔ ∀ i, i < length l → P (nth i l d).
  Proof.
    rewrite Forall_lookup. split.
    - intros Hl ? [x Hl']%lookup_lt_is_Some_2.
      rewrite (nth_lookup_Some _ _ _ _ Hl'). by eapply Hl.
    - intros Hl i x Hl'. specialize (Hl _ (lookup_lt_Some _ _ _ Hl')).
      by rewrite (nth_lookup_Some _ _ _ _ Hl') in Hl.
  Qed.

  Lemma Forall_reverse l : Forall P (reverse l) ↔ Forall P l.
  Proof.
    induction l as [|x l IH]; simpl; [done|].
    rewrite reverse_cons, Forall_cons, Forall_app, Forall_singleton. naive_solver.
  Qed.
  Lemma Forall_tail l : Forall P l → Forall P (tail l).
  Proof. destruct 1; simpl; auto. Qed.
  Lemma Forall_alter f l i :
    Forall P l → (∀ x, l !! i = Some x → P x → P (f x)) → Forall P (alter f i l).
  Proof.
    intros Hl. revert i. induction Hl; simpl; intros [|i]; constructor; auto.
  Qed.
  Lemma Forall_alter_inv f l i :
    Forall P (alter f i l) → (∀ x, l !! i = Some x → P (f x) → P x) → Forall P l.
  Proof.
    revert i. induction l; intros [|?]; simpl;
      inversion_clear 1; constructor; eauto.
  Qed.
  Lemma Forall_insert l i x : Forall P l → P x → Forall P (<[i:=x]>l).
  Proof. rewrite list_insert_alter; auto using Forall_alter. Qed.
  Lemma Forall_inserts l i k :
    Forall P l → Forall P k → Forall P (list_inserts i k l).
  Proof.
    intros Hl Hk; revert i.
    induction Hk; simpl; auto using Forall_insert.
  Qed.
  Lemma Forall_replicate n x : P x → Forall P (replicate n x).
  Proof. induction n; simpl; constructor; auto. Qed.
  Lemma Forall_replicate_eq n (x : A) : Forall (x =.) (replicate n x).
  Proof using -(P). induction n; simpl; constructor; auto. Qed.
  Lemma Forall_take n l : Forall P l → Forall P (take n l).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall_drop n l : Forall P l → Forall P (drop n l).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall_resize n x l : P x → Forall P l → Forall P (resize n x l).
  Proof.
    intros ? Hl. revert n.
    induction Hl; intros [|?]; simpl; auto using Forall_replicate.
  Qed.
  Lemma Forall_resize_inv n x l :
    length l ≤ n → Forall P (resize n x l) → Forall P l.
  Proof. intros ?. rewrite resize_ge, Forall_app by done. by intros []. Qed.
  Lemma Forall_sublist_lookup l i n k :
    sublist_lookup i n l = Some k → Forall P l → Forall P k.
  Proof.
    unfold sublist_lookup. intros; simplify_option_eq.
    auto using Forall_take, Forall_drop.
  Qed.
  Lemma Forall_sublist_alter f l i n k :
    Forall P l → sublist_lookup i n l = Some k → Forall P (f k) →
    Forall P (sublist_alter f i n l).
  Proof.
    unfold sublist_alter, sublist_lookup. intros; simplify_option_eq.
    auto using Forall_app_2, Forall_drop, Forall_take.
  Qed.
  Lemma Forall_sublist_alter_inv f l i n k :
    sublist_lookup i n l = Some k →
    Forall P (sublist_alter f i n l) → Forall P (f k).
  Proof.
    unfold sublist_alter, sublist_lookup. intros ?; simplify_option_eq.
    rewrite !Forall_app; tauto.
  Qed.
  Lemma Forall_reshape l szs : Forall P l → Forall (Forall P) (reshape szs l).
  Proof.
    revert l. induction szs; simpl; auto using Forall_take, Forall_drop.
  Qed.
  Lemma Forall_rev_ind (Q : list A → Prop) :
    Q [] → (∀ x l, P x → Forall P l → Q l → Q (l ++ [x])) →
    ∀ l, Forall P l → Q l.
  Proof.
    intros ?? l. induction l using rev_ind; auto.
    rewrite Forall_app, Forall_singleton; intros [??]; auto.
  Qed.

  Lemma Exists_exists l : Exists P l ↔ ∃ x, x ∈ l ∧ P x.
  Proof.
    split.
    - induction 1 as [x|y ?? [x [??]]]; exists x; by repeat constructor.
    - intros [x [Hin ?]]. induction l; [by destruct (not_elem_of_nil x)|].
      inversion Hin; subst; [left|right]; auto.
  Qed.
  Lemma Exists_inv x l : Exists P (x :: l) → P x ∨ Exists P l.
  Proof. inversion 1; intuition trivial. Qed.
  Lemma Exists_app l1 l2 : Exists P (l1 ++ l2) ↔ Exists P l1 ∨ Exists P l2.
  Proof.
    split.
    - induction l1; inversion 1; intuition.
    - intros [H|H]; [induction H | induction l1]; simpl; intuition.
  Qed.
  Lemma Exists_impl (Q : A → Prop) l :
    Exists P l → (∀ x, P x → Q x) → Exists Q l.
  Proof. intros H ?. induction H; auto. Defined.

  Lemma Exists_not_Forall l : Exists (not ∘ P) l → ¬Forall P l.
  Proof. induction 1; inversion_clear 1; contradiction. Qed.
  Lemma Forall_not_Exists l : Forall (not ∘ P) l → ¬Exists P l.
  Proof. induction 1; inversion_clear 1; contradiction. Qed.

  Lemma Forall_list_difference `{!EqDecision A} l k :
    Forall P l → Forall P (list_difference l k).
  Proof.
    rewrite !Forall_forall.
    intros ? x; rewrite elem_of_list_difference; naive_solver.
  Qed.
  Lemma Forall_list_union `{!EqDecision A} l k :
    Forall P l → Forall P k → Forall P (list_union l k).
  Proof. intros. apply Forall_app; auto using Forall_list_difference. Qed.
  Lemma Forall_list_intersection `{!EqDecision A} l k :
    Forall P l → Forall P (list_intersection l k).
  Proof.
    rewrite !Forall_forall.
    intros ? x; rewrite elem_of_list_intersection; naive_solver.
  Qed.

  Context {dec : ∀ x, Decision (P x)}.
  Lemma not_Forall_Exists l : ¬Forall P l → Exists (not ∘ P) l.
  Proof using Type*. intro. by destruct (Forall_Exists_dec P (not ∘ P) dec l). Qed.
  Lemma not_Exists_Forall l : ¬Exists P l → Forall (not ∘ P) l.
  Proof using Type*.
    by destruct (Forall_Exists_dec (not ∘ P) P
        (λ x : A, swap_if (decide (P x))) l).
  Qed.
  Global Instance Forall_dec l : Decision (Forall P l) :=
    match Forall_Exists_dec P (not ∘ P) dec l with
    | left H => left H
    | right H => right (Exists_not_Forall _ H)
    end.
  Global Instance Exists_dec l : Decision (Exists P l) :=
    match Forall_Exists_dec (not ∘ P) P (λ x, swap_if (decide (P x))) l with
    | left H => right (Forall_not_Exists _ H)
    | right H => left H
    end.
End Forall_Exists.

Global Instance Forall_Permutation :
  Proper (pointwise_relation _ (↔) ==> (≡ₚ) ==> (↔)) (@Forall A).
Proof.
  intros P1 P2 HP l1 l2 Hl. rewrite !Forall_forall.
  apply forall_proper; intros x. by rewrite Hl, (HP x).
Qed.
Global Instance Exists_Permutation :
  Proper (pointwise_relation _ (↔) ==> (≡ₚ) ==> (↔)) (@Exists A).
Proof.
  intros P1 P2 HP l1 l2 Hl. rewrite !Exists_exists.
  f_equiv; intros x. by rewrite Hl, (HP x).
Qed.

Lemma head_filter_Some P `{!∀ x : A, Decision (P x)} l x :
  head (filter P l) = Some x →
  ∃ l1 l2, l = l1 ++ x :: l2 ∧ Forall (λ z, ¬P z) l1.
Proof.
  intros Hl. induction l as [|x' l IH]; [done|].
  rewrite filter_cons in Hl. case_decide; simplify_eq/=.
  - exists [], l. repeat constructor.
  - destruct IH as (l1&l2&->&?); [done|].
    exists (x' :: l1), l2. by repeat constructor.
Qed.
Lemma last_filter_Some P `{!∀ x : A, Decision (P x)} l x :
  last (filter P l) = Some x →
  ∃ l1 l2, l = l1 ++ x :: l2 ∧ Forall (λ z, ¬P z) l2.
Proof.
  rewrite <-(reverse_involutive (filter P l)), last_reverse, <-filter_reverse.
  intros (l1&l2&Heq&Hl)%head_filter_Some.
  exists (reverse l2), (reverse l1).
  rewrite <-(reverse_involutive l), Heq, reverse_app, reverse_cons, <-(assoc_L (++)).
  split; [done|by apply Forall_reverse].
Qed.

Lemma list_exist_dec P l :
  (∀ x, Decision (P x)) → Decision (∃ x, x ∈ l ∧ P x).
Proof.
  refine (λ _, cast_if (decide (Exists P l))); by rewrite <-Exists_exists.
Defined.
Lemma list_forall_dec P l :
  (∀ x, Decision (P x)) → Decision (∀ x, x ∈ l → P x).
Proof.
  refine (λ _, cast_if (decide (Forall P l))); by rewrite <-Forall_forall.
Defined.

Lemma forallb_True (f : A → bool) xs : forallb f xs ↔ Forall f xs.
Proof.
  split.
  - induction xs; naive_solver.
  - induction 1; naive_solver.
Qed.
Lemma existb_True (f : A → bool) xs : existsb f xs ↔ Exists f xs.
Proof.
  split.
  - induction xs; naive_solver.
  - induction 1; naive_solver.
Qed.

Lemma replicate_as_Forall (x : A) n l :
  replicate n x = l ↔ length l = n ∧ Forall (x =.) l.
Proof. rewrite replicate_as_elem_of, Forall_forall. naive_solver. Qed.
Lemma replicate_as_Forall_2 (x : A) n l :
  length l = n → Forall (x =.) l → replicate n x = l.
Proof. by rewrite replicate_as_Forall. Qed.
End more_general_properties.

Lemma Forall_swap {A B} (Q : A → B → Prop) l1 l2 :
  Forall (λ y, Forall (Q y) l1) l2 ↔ Forall (λ x, Forall (flip Q x) l2) l1.
Proof. repeat setoid_rewrite Forall_forall. simpl. split; eauto. Qed.

(** ** Properties of the [Forall2] predicate *)
Lemma Forall_Forall2_diag {A} (Q : A → A → Prop) l :
  Forall (λ x, Q x x) l → Forall2 Q l l.
Proof. induction 1; constructor; auto. Qed.

Lemma Forall2_forall `{Inhabited A} B C (Q : A → B → C → Prop) l k :
  Forall2 (λ x y, ∀ z, Q z x y) l k ↔ ∀ z, Forall2 (Q z) l k.
Proof.
  split; [induction 1; constructor; auto|].
  intros Hlk. induction (Hlk inhabitant) as [|x y l k _ _ IH]; constructor.
  - intros z. by oinversion Hlk.
  - apply IH. intros z. by oinversion Hlk.
Qed.

Lemma Forall2_same_length {A B} (l : list A) (k : list B) :
  Forall2 (λ _ _, True) l k ↔ length l = length k.
Proof.
  split; [by induction 1; f_equal/=|].
  revert k. induction l; intros [|??] ?; simplify_eq/=; auto.
Qed.

Lemma Forall2_Forall {A} P (l1 l2 : list A) :
  Forall2 P l1 l2 → Forall (uncurry P) (zip l1 l2).
Proof. induction 1; constructor; auto. Qed.

(** Export the Coq stdlib constructors under a different name,
because we use [Forall2_nil] and [Forall2_cons] for a version with a biimplication. *)
Definition Forall2_nil_2 := @Forall2_nil.
Definition Forall2_cons_2 := @Forall2_cons.
Section Forall2.
  Context {A B} (P : A → B → Prop).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma Forall2_length l k : Forall2 P l k → length l = length k.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall2_length_l l k n : Forall2 P l k → length l = n → length k = n.
  Proof. intros ? <-; symmetry. by apply Forall2_length. Qed.
  Lemma Forall2_length_r l k n : Forall2 P l k → length k = n → length l = n.
  Proof. intros ? <-. by apply Forall2_length. Qed.

  Lemma Forall2_true l k : (∀ x y, P x y) → length l = length k → Forall2 P l k.
  Proof. rewrite <-Forall2_same_length. induction 2; naive_solver. Qed.
  Lemma Forall2_flip l k : Forall2 (flip P) k l ↔ Forall2 P l k.
  Proof. split; induction 1; constructor; auto. Qed.
  Lemma Forall2_transitive {C} (Q : B → C → Prop) (R : A → C → Prop) l k lC :
    (∀ x y z, P x y → Q y z → R x z) →
    Forall2 P l k → Forall2 Q k lC → Forall2 R l lC.
  Proof. intros ? Hl. revert lC. induction Hl; inversion_clear 1; eauto. Qed.
  Lemma Forall2_impl (Q : A → B → Prop) l k :
    Forall2 P l k → (∀ x y, P x y → Q x y) → Forall2 Q l k.
  Proof. intros H ?. induction H; auto. Defined.
  Lemma Forall2_unique l k1 k2 :
    Forall2 P l k1 → Forall2 P l k2 →
    (∀ x y1 y2, P x y1 → P x y2 → y1 = y2) → k1 = k2.
  Proof.
    intros H. revert k2. induction H; inversion_clear 1; intros; f_equal; eauto.
  Qed.

  Lemma Forall_Forall2_l l k :
    length l = length k → Forall (λ x, ∀ y, P x y) l → Forall2 P l k.
  Proof. rewrite <-Forall2_same_length. induction 1; inversion 1; auto. Qed.
  Lemma Forall_Forall2_r l k :
    length l = length k → Forall (λ y, ∀ x, P x y) k → Forall2 P l k.
  Proof. rewrite <-Forall2_same_length. induction 1; inversion 1; auto. Qed.

  Lemma Forall2_Forall_l (Q : A → Prop) l k :
    Forall2 P l k → Forall (λ y, ∀ x, P x y → Q x) k → Forall Q l.
  Proof. induction 1; inversion_clear 1; eauto. Qed.
  Lemma Forall2_Forall_r (Q : B → Prop) l k :
    Forall2 P l k → Forall (λ x, ∀ y, P x y → Q y) l → Forall Q k.
  Proof. induction 1; inversion_clear 1; eauto. Qed.

  Lemma Forall2_nil_inv_l k : Forall2 P [] k → k = [].
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_inv_r l : Forall2 P l [] → l = [].
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil : Forall2 P [] [] ↔ True.
  Proof. done. Qed.

  Lemma Forall2_cons_1 x l y k :
    Forall2 P (x :: l) (y :: k) → P x y ∧ Forall2 P l k.
  Proof. by inversion 1. Qed.
  Lemma Forall2_cons_inv_l x l k :
    Forall2 P (x :: l) k → ∃ y k', P x y ∧ Forall2 P l k' ∧ k = y :: k'.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_inv_r l k y :
    Forall2 P l (y :: k) → ∃ x l', P x y ∧ Forall2 P l' k ∧ l = x :: l'.
  Proof. inversion 1; subst; eauto. Qed.
  Lemma Forall2_cons_nil_inv x l : Forall2 P (x :: l) [] → False.
  Proof. by inversion 1. Qed.
  Lemma Forall2_nil_cons_inv y k : Forall2 P [] (y :: k) → False.
  Proof. by inversion 1. Qed.

  Lemma Forall2_cons x l y k :
    Forall2 P (x :: l) (y :: k) ↔ P x y ∧ Forall2 P l k.
  Proof.
    split; [by apply Forall2_cons_1|]. intros []. by apply Forall2_cons_2.
  Qed.

  Lemma Forall2_app_l l1 l2 k :
    Forall2 P l1 (take (length l1) k) → Forall2 P l2 (drop (length l1) k) →
    Forall2 P (l1 ++ l2) k.
  Proof. intros. rewrite <-(take_drop (length l1) k). by apply Forall2_app. Qed.
  Lemma Forall2_app_r l k1 k2 :
    Forall2 P (take (length k1) l) k1 → Forall2 P (drop (length k1) l) k2 →
    Forall2 P l (k1 ++ k2).
  Proof. intros. rewrite <-(take_drop (length k1) l). by apply Forall2_app. Qed.
  Lemma Forall2_app_inv l1 l2 k1 k2 :
    length l1 = length k1 →
    Forall2 P (l1 ++ l2) (k1 ++ k2) → Forall2 P l1 k1 ∧ Forall2 P l2 k2.
  Proof.
    rewrite <-Forall2_same_length. induction 1; inversion 1; naive_solver.
  Qed.
  Lemma Forall2_app_inv_l l1 l2 k :
    Forall2 P (l1 ++ l2) k ↔
      ∃ k1 k2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ k = k1 ++ k2.
  Proof.
    split; [|intros (?&?&?&?&->); by apply Forall2_app].
    revert k. induction l1; inversion 1; naive_solver.
  Qed.
  Lemma Forall2_app_inv_r l k1 k2 :
    Forall2 P l (k1 ++ k2) ↔
      ∃ l1 l2, Forall2 P l1 k1 ∧ Forall2 P l2 k2 ∧ l = l1 ++ l2.
  Proof.
    split; [|intros (?&?&?&?&->); by apply Forall2_app].
    revert l. induction k1; inversion 1; naive_solver.
  Qed.

  Lemma Forall2_tail l k : Forall2 P l k → Forall2 P (tail l) (tail k).
  Proof. destruct 1; simpl; auto. Qed.
  Lemma Forall2_take l k n : Forall2 P l k → Forall2 P (take n l) (take n k).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.
  Lemma Forall2_drop l k n : Forall2 P l k → Forall2 P (drop n l) (drop n k).
  Proof. intros Hl. revert n. induction Hl; intros [|?]; simpl; auto. Qed.

  Lemma Forall2_lookup l k :
    Forall2 P l k ↔ ∀ i, option_Forall2 P (l !! i) (k !! i).
  Proof.
    split; [induction 1; intros [|?]; simpl; try constructor; eauto|].
    revert k. induction l as [|x l IH]; intros [| y k] H.
    - done.
    - oinversion (H 0).
    - oinversion (H 0).
    - constructor; [by oinversion (H 0)|]. apply (IH _ $ λ i, H (S i)).
  Qed.
  Lemma Forall2_lookup_lr l k i x y :
    Forall2 P l k → l !! i = Some x → k !! i = Some y → P x y.
  Proof. rewrite Forall2_lookup; intros H; destruct (H i); naive_solver. Qed.
  Lemma Forall2_lookup_l l k i x :
    Forall2 P l k → l !! i = Some x → ∃ y, k !! i = Some y ∧ P x y.
  Proof. rewrite Forall2_lookup; intros H; destruct (H i); naive_solver. Qed.
  Lemma Forall2_lookup_r l k i y :
    Forall2 P l k → k !! i = Some y → ∃ x, l !! i = Some x ∧ P x y.
  Proof. rewrite Forall2_lookup; intros H; destruct (H i); naive_solver. Qed.
  Lemma Forall2_same_length_lookup_2 l k :
    length l = length k →
    (∀ i x y, l !! i = Some x → k !! i = Some y → P x y) → Forall2 P l k.
  Proof.
    rewrite <-Forall2_same_length. intros Hl Hlookup.
    induction Hl as [|?????? IH]; constructor; [by apply (Hlookup 0)|].
    apply IH. apply (λ i, Hlookup (S i)).
  Qed.
  Lemma Forall2_same_length_lookup l k :
    Forall2 P l k ↔
      length l = length k ∧
      (∀ i x y, l !! i = Some x → k !! i = Some y → P x y).
  Proof.
    naive_solver eauto using Forall2_length,
      Forall2_lookup_lr, Forall2_same_length_lookup_2.
  Qed.

  Lemma Forall2_alter_l f l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P (f x) y) →
    Forall2 P (alter f i l) k.
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_alter_r f l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P x (f y)) →
    Forall2 P l (alter f i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_alter f g l k i :
    Forall2 P l k →
    (∀ x y, l !! i = Some x → k !! i = Some y → P x y → P (f x) (g y)) →
    Forall2 P (alter f i l) (alter g i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.

  Lemma Forall2_insert l k x y i :
    Forall2 P l k → P x y → Forall2 P (<[i:=x]> l) (<[i:=y]> k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; constructor; auto. Qed.
  Lemma Forall2_inserts l k l' k' i :
    Forall2 P l k → Forall2 P l' k' →
    Forall2 P (list_inserts i l' l) (list_inserts i k' k).
  Proof. intros ? H. revert i. induction H; eauto using Forall2_insert. Qed.

  Lemma Forall2_delete l k i :
    Forall2 P l k → Forall2 P (delete i l) (delete i k).
  Proof. intros Hl. revert i. induction Hl; intros [|]; simpl; intuition. Qed.
  Lemma Forall2_option_list mx my :
    option_Forall2 P mx my → Forall2 P (option_list mx) (option_list my).
  Proof. destruct 1; by constructor. Qed.

  Lemma Forall2_filter Q1 Q2 `{∀ x, Decision (Q1 x), ∀ y, Decision (Q2 y)} l k:
    (∀ x y, P x y → Q1 x ↔ Q2 y) →
    Forall2 P l k → Forall2 P (filter Q1 l) (filter Q2 k).
  Proof.
    intros HP; induction 1 as [|x y l k]; unfold filter; simpl; auto.
    simplify_option_eq by (by rewrite <-(HP x y)); repeat constructor; auto.
  Qed.

  Lemma Forall2_replicate_l k n x :
    length k = n → Forall (P x) k → Forall2 P (replicate n x) k.
  Proof. intros <-. induction 1; simpl; auto. Qed.
  Lemma Forall2_replicate_r l n y :
    length l = n → Forall (flip P y) l → Forall2 P l (replicate n y).
  Proof. intros <-. induction 1; simpl; auto. Qed.
  Lemma Forall2_replicate n x y :
    P x y → Forall2 P (replicate n x) (replicate n y).
  Proof. induction n; simpl; constructor; auto. Qed.

  Lemma Forall2_rotate n l k :
    Forall2 P l k → Forall2 P (rotate n l) (rotate n k).
  Proof.
    intros HAll. unfold rotate. rewrite (Forall2_length _ _ HAll).
    eauto using Forall2_app, Forall2_take, Forall2_drop.
  Qed.
  Lemma Forall2_rotate_take s e l k :
    Forall2 P l k → Forall2 P (rotate_take s e l) (rotate_take s e k).
  Proof.
    intros HAll. unfold rotate_take. rewrite (Forall2_length _ _ HAll).
    eauto using Forall2_take, Forall2_rotate.
  Qed.

  Lemma Forall2_reverse l k : Forall2 P l k → Forall2 P (reverse l) (reverse k).
  Proof.
    induction 1; rewrite ?reverse_nil, ?reverse_cons; eauto using Forall2_app.
  Qed.
  Lemma Forall2_last l k : Forall2 P l k → option_Forall2 P (last l) (last k).
  Proof. induction 1 as [|????? []]; simpl; repeat constructor; auto. Qed.

  Lemma Forall2_resize l k x y n :
    P x y → Forall2 P l k → Forall2 P (resize n x l) (resize n y k).
  Proof.
    intros. rewrite !resize_spec, (Forall2_length l k) by done.
    auto using Forall2_app, Forall2_take, Forall2_replicate.
  Qed.
  Lemma Forall2_resize_l l k x y n m :
    P x y → Forall (flip P y) l →
    Forall2 P (resize n x l) k → Forall2 P (resize m x l) (resize m y k).
  Proof.
    intros. destruct (decide (m ≤ n)).
    { rewrite <-(resize_resize l m n) by done. by apply Forall2_resize. }
    intros. assert (n = length k); subst.
    { by rewrite <-(Forall2_length (resize n x l) k), resize_length. }
    rewrite (Nat.le_add_sub (length k) m), !resize_add,
      resize_all, drop_all, resize_nil by lia.
    auto using Forall2_app, Forall2_replicate_r,
      Forall_resize, Forall_drop, resize_length.
  Qed.
  Lemma Forall2_resize_r l k x y n m :
    P x y → Forall (P x) k →
    Forall2 P l (resize n y k) → Forall2 P (resize m x l) (resize m y k).
  Proof.
    intros. destruct (decide (m ≤ n)).
    { rewrite <-(resize_resize k m n) by done. by apply Forall2_resize. }
    assert (n = length l); subst.
    { by rewrite (Forall2_length l (resize n y k)), resize_length. }
    rewrite (Nat.le_add_sub (length l) m), !resize_add,
      resize_all, drop_all, resize_nil by lia.
    auto using Forall2_app, Forall2_replicate_l,
      Forall_resize, Forall_drop, resize_length.
  Qed.
  Lemma Forall2_resize_r_flip l k x y n m :
    P x y → Forall (P x) k →
    length k = m → Forall2 P l (resize n y k) → Forall2 P (resize m x l) k.
  Proof.
    intros ?? <- ?. rewrite <-(resize_all k y) at 2.
    apply Forall2_resize_r with n; auto using Forall_true.
  Qed.

  Lemma Forall2_sublist_lookup_l l k n i l' :
    Forall2 P l k → sublist_lookup n i l = Some l' →
    ∃ k', sublist_lookup n i k = Some k' ∧ Forall2 P l' k'.
  Proof.
    unfold sublist_lookup. intros Hlk Hl.
    exists (take i (drop n k)); simplify_option_eq.
    - auto using Forall2_take, Forall2_drop.
    - apply Forall2_length in Hlk; lia.
  Qed.
  Lemma Forall2_sublist_lookup_r l k n i k' :
    Forall2 P l k → sublist_lookup n i k = Some k' →
    ∃ l', sublist_lookup n i l = Some l' ∧ Forall2 P l' k'.
  Proof.
    intro. unfold sublist_lookup.
    erewrite Forall2_length by eauto; intros; simplify_option_eq.
    eauto using Forall2_take, Forall2_drop.
  Qed.
  Lemma Forall2_sublist_alter f g l k i n l' k' :
    Forall2 P l k → sublist_lookup i n l = Some l' →
    sublist_lookup i n k = Some k' → Forall2 P (f l') (g k') →
    Forall2 P (sublist_alter f i n l) (sublist_alter g i n k).
  Proof.
    intro. unfold sublist_alter, sublist_lookup.
    erewrite Forall2_length by eauto; intros; simplify_option_eq.
    auto using Forall2_app, Forall2_drop, Forall2_take.
  Qed.
  Lemma Forall2_sublist_alter_l f l k i n l' k' :
    Forall2 P l k → sublist_lookup i n l = Some l' →
    sublist_lookup i n k = Some k' → Forall2 P (f l') k' →
    Forall2 P (sublist_alter f i n l) k.
  Proof.
    intro. unfold sublist_lookup, sublist_alter.
    erewrite <-Forall2_length by eauto; intros; simplify_option_eq.
    apply Forall2_app_l;
      rewrite ?take_length_le by lia; auto using Forall2_take.
    apply Forall2_app_l; erewrite Forall2_length, take_length,
      drop_length, <-Forall2_length, Nat.min_l by eauto with lia; [done|].
    rewrite drop_drop; auto using Forall2_drop.
  Qed.

  Global Instance Forall2_dec `{dec : ∀ x y, Decision (P x y)} :
    RelDecision (Forall2 P).
  Proof.
   refine (
    fix go l k : Decision (Forall2 P l k) :=
    match l, k with
    | [], [] => left _
    | x :: l, y :: k => cast_if_and (decide (P x y)) (go l k)
    | _, _ => right _
    end); clear dec go; abstract first [by constructor | by inversion 1].
  Defined.
End Forall2.

Section Forall2_proper.
  Context  {A} (R : relation A).

  Global Instance: Reflexive R → Reflexive (Forall2 R).
  Proof. intros ? l. induction l; by constructor. Qed.
  Global Instance: Symmetric R → Symmetric (Forall2 R).
  Proof. intros. induction 1; constructor; auto. Qed.
  Global Instance: Transitive R → Transitive (Forall2 R).
  Proof. intros ????. apply Forall2_transitive. by apply @transitivity. Qed.
  Global Instance: Equivalence R → Equivalence (Forall2 R).
  Proof. split; apply _. Qed.
  Global Instance: PreOrder R → PreOrder (Forall2 R).
  Proof. split; apply _. Qed.
  Global Instance: AntiSymm (=) R → AntiSymm (=) (Forall2 R).
  Proof. induction 2; inversion_clear 1; f_equal; auto. Qed.

  Global Instance: Proper (R ==> Forall2 R ==> Forall2 R) (::).
  Proof. by constructor. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R ==> Forall2 R) (++).
  Proof. repeat intro. by apply Forall2_app. Qed.
  Global Instance: Proper (Forall2 R ==> (=)) length.
  Proof. repeat intro. eauto using Forall2_length. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R) tail.
  Proof. repeat intro. eauto using Forall2_tail. Qed.
  Global Instance: ∀ n, Proper (Forall2 R ==> Forall2 R) (take n).
  Proof. repeat intro. eauto using Forall2_take. Qed.
  Global Instance: ∀ n, Proper (Forall2 R ==> Forall2 R) (drop n).
  Proof. repeat intro. eauto using Forall2_drop. Qed.

  Global Instance: ∀ i, Proper (Forall2 R ==> option_Forall2 R) (lookup i).
  Proof. repeat intro. by apply Forall2_lookup. Qed.
  Global Instance:
    Proper ((R ==> R) ==> (=) ==> Forall2 R ==> Forall2 R) (alter (M:=list A)).
  Proof. repeat intro. subst. eauto using Forall2_alter. Qed.
  Global Instance: ∀ i, Proper (R ==> Forall2 R ==> Forall2 R) (insert i).
  Proof. repeat intro. eauto using Forall2_insert. Qed.
  Global Instance: ∀ i,
    Proper (Forall2 R ==> Forall2 R ==> Forall2 R) (list_inserts i).
  Proof. repeat intro. eauto using Forall2_inserts. Qed.
  Global Instance: ∀ i, Proper (Forall2 R ==> Forall2 R) (delete i).
  Proof. repeat intro. eauto using Forall2_delete. Qed.

  Global Instance: Proper (option_Forall2 R ==> Forall2 R) option_list.
  Proof. repeat intro. eauto using Forall2_option_list. Qed.
  Global Instance: ∀ P `{∀ x, Decision (P x)},
    Proper (R ==> iff) P → Proper (Forall2 R ==> Forall2 R) (filter P).
  Proof. repeat intro; eauto using Forall2_filter. Qed.

  Global Instance: ∀ n, Proper (R ==> Forall2 R) (replicate n).
  Proof. repeat intro. eauto using Forall2_replicate. Qed.
  Global Instance: ∀ n, Proper (Forall2 R ==> Forall2 R) (rotate n).
  Proof. repeat intro. eauto using Forall2_rotate. Qed.
  Global Instance: ∀ s e, Proper (Forall2 R ==> Forall2 R) (rotate_take s e).
  Proof. repeat intro. eauto using Forall2_rotate_take. Qed.
  Global Instance: Proper (Forall2 R ==> Forall2 R) reverse.
  Proof. repeat intro. eauto using Forall2_reverse. Qed.
  Global Instance: Proper (Forall2 R ==> option_Forall2 R) last.
  Proof. repeat intro. eauto using Forall2_last. Qed.
  Global Instance: ∀ n, Proper (R ==> Forall2 R ==> Forall2 R) (resize n).
  Proof. repeat intro. eauto using Forall2_resize. Qed.
End Forall2_proper.

Section Forall3.
  Context {A B C} (P : A → B → C → Prop).
  Local Hint Extern 0 (Forall3 _ _ _ _) => constructor : core.

  Lemma Forall3_app l1 l2 k1 k2 k1' k2' :
    Forall3 P l1 k1 k1' → Forall3 P l2 k2 k2' →
    Forall3 P (l1 ++ l2) (k1 ++ k2) (k1' ++ k2').
  Proof. induction 1; simpl; auto. Qed.
  Lemma Forall3_cons_inv_l x l k k' :
    Forall3 P (x :: l) k k' → ∃ y k2 z k2',
      k = y :: k2 ∧ k' = z :: k2' ∧ P x y z ∧ Forall3 P l k2 k2'.
  Proof. inversion_clear 1; naive_solver. Qed.
  Lemma Forall3_app_inv_l l1 l2 k k' :
    Forall3 P (l1 ++ l2) k k' → ∃ k1 k2 k1' k2',
     k = k1 ++ k2 ∧ k' = k1' ++ k2' ∧ Forall3 P l1 k1 k1' ∧ Forall3 P l2 k2 k2'.
  Proof.
    revert k k'. induction l1 as [|x l1 IH]; simpl; inversion_clear 1.
    - by repeat eexists; eauto.
    - by repeat eexists; eauto.
    - edestruct IH as (?&?&?&?&?&?&?&?); eauto; naive_solver.
  Qed.
  Lemma Forall3_cons_inv_m l y k k' :
    Forall3 P l (y :: k) k' → ∃ x l2 z k2',
      l = x :: l2 ∧ k' = z :: k2' ∧ P x y z ∧ Forall3 P l2 k k2'.
  Proof. inversion_clear 1; naive_solver. Qed.
  Lemma Forall3_app_inv_m l k1 k2 k' :
    Forall3 P l (k1 ++ k2) k' → ∃ l1 l2 k1' k2',
     l = l1 ++ l2 ∧ k' = k1' ++ k2' ∧ Forall3 P l1 k1 k1' ∧ Forall3 P l2 k2 k2'.
  Proof.
    revert l k'. induction k1 as [|x k1 IH]; simpl; inversion_clear 1.
    - by repeat eexists; eauto.
    - by repeat eexists; eauto.
    - edestruct IH as (?&?&?&?&?&?&?&?); eauto; naive_solver.
  Qed.
  Lemma Forall3_cons_inv_r l k z k' :
    Forall3 P l k (z :: k') → ∃ x l2 y k2,
      l = x :: l2 ∧ k = y :: k2 ∧ P x y z ∧ Forall3 P l2 k2 k'.
  Proof. inversion_clear 1; naive_solver. Qed.
  Lemma Forall3_app_inv_r l k k1' k2' :
    Forall3 P l k (k1' ++ k2') → ∃ l1 l2 k1 k2,
      l = l1 ++ l2 ∧ k = k1 ++ k2 ∧ Forall3 P l1 k1 k1' ∧ Forall3 P l2 k2 k2'.
  Proof.
    revert l k. induction k1' as [|x k1' IH]; simpl; inversion_clear 1.
    - by repeat eexists; eauto.
    - by repeat eexists; eauto.
    - edestruct IH as (?&?&?&?&?&?&?&?); eauto; naive_solver.
  Qed.
  Lemma Forall3_impl (Q : A → B → C → Prop) l k k' :
    Forall3 P l k k' → (∀ x y z, P x y z → Q x y z) → Forall3 Q l k k'.
  Proof. intros Hl ?; induction Hl; auto. Defined.
  Lemma Forall3_length_lm l k k' : Forall3 P l k k' → length l = length k.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall3_length_lr l k k' : Forall3 P l k k' → length l = length k'.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall3_lookup_lmr l k k' i x y z :
    Forall3 P l k k' →
    l !! i = Some x → k !! i = Some y → k' !! i = Some z → P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ???; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_lookup_l l k k' i x :
    Forall3 P l k k' → l !! i = Some x →
    ∃ y z, k !! i = Some y ∧ k' !! i = Some z ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_lookup_m l k k' i y :
    Forall3 P l k k' → k !! i = Some y →
    ∃ x z, l !! i = Some x ∧ k' !! i = Some z ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_lookup_r l k k' i z :
    Forall3 P l k k' → k' !! i = Some z →
    ∃ x y, l !! i = Some x ∧ k !! i = Some y ∧ P x y z.
  Proof.
    intros H. revert i. induction H; intros [|?] ?; simplify_eq/=; eauto.
  Qed.
  Lemma Forall3_alter_lm f g l k k' i :
    Forall3 P l k k' →
    (∀ x y z, l !! i = Some x → k !! i = Some y → k' !! i = Some z →
      P x y z → P (f x) (g y) z) →
    Forall3 P (alter f i l) (alter g i k) k'.
  Proof. intros Hl. revert i. induction Hl; intros [|]; auto. Qed.
End Forall3.

(** ** Properties of [subseteq] *)
Section subseteq.
Context {A : Type}.
Implicit Types x y z : A.
Implicit Types l k : list A.

Global Instance list_subseteq_po : PreOrder (⊆@{list A}).
Proof. split; firstorder. Qed.
Lemma list_subseteq_nil l : [] ⊆ l.
Proof. intros x. by rewrite elem_of_nil. Qed.
Lemma list_nil_subseteq l : l ⊆ [] → l = [].
Proof.
  intro Hl. destruct l as [|x l1]; [done|]. exfalso.
  rewrite <-(elem_of_nil x).
  apply Hl, elem_of_cons. by left.
Qed.
Lemma list_subseteq_skip x l1 l2 : l1 ⊆ l2 → x :: l1 ⊆ x :: l2.
Proof.
  intros Hin y Hy%elem_of_cons.
  destruct Hy as [-> | Hy]; [by left|]. right. by apply Hin.
Qed.
Lemma list_subseteq_cons x l1 l2 : l1 ⊆ l2 → l1 ⊆ x :: l2.
Proof. intros Hin y Hy. right. by apply Hin. Qed.
Lemma list_subseteq_app_l l1 l2 l : l1 ⊆ l2 → l1 ⊆ l2 ++ l.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_app. naive_solver. Qed.
Lemma list_subseteq_app_r l1 l2 l : l1 ⊆ l2 → l1 ⊆ l ++ l2.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_app. naive_solver. Qed.

Lemma list_subseteq_app_iff_l l1 l2 l :
  l1 ++ l2 ⊆ l ↔ l1 ⊆ l ∧ l2 ⊆ l.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_app. naive_solver. Qed.
Lemma list_subseteq_cons_iff x l1 l2 :
  x :: l1 ⊆ l2 ↔ x ∈ l2 ∧ l1 ⊆ l2.
Proof. unfold subseteq, list_subseteq. setoid_rewrite elem_of_cons. naive_solver. Qed.

Lemma list_delete_subseteq i l : delete i l ⊆ l.
Proof.
  revert i. induction l as [|x l IHl]; intros i; [done|].
  destruct i as [|i];
    [by apply list_subseteq_cons|by apply list_subseteq_skip].
Qed.
Lemma list_filter_subseteq P `{!∀ x : A, Decision (P x)} l :
  filter P l ⊆ l.
Proof.
  induction l as [|x l IHl]; [done|]. rewrite filter_cons.
  destruct (decide (P x));
    [by apply list_subseteq_skip|by apply list_subseteq_cons].
Qed.
Lemma subseteq_drop n l : drop n l ⊆ l.
Proof. rewrite <-(take_drop n l) at 2. apply list_subseteq_app_r. done. Qed.
Lemma subseteq_take n l : take n l ⊆ l.
Proof. rewrite <-(take_drop n l) at 2. apply list_subseteq_app_l. done. Qed.

Global Instance list_subseteq_Permutation:
  Proper ((≡ₚ) ==> (≡ₚ) ==> (↔)) (⊆@{list A}) .
Proof.
  intros l1 l2 Hl k1 k2 Hk. apply forall_proper; intros x. by rewrite Hl, Hk.
Qed.

Global Program Instance list_subseteq_dec `{!EqDecision A} : RelDecision (⊆@{list A}) :=
  λ xs ys, cast_if (decide (Forall (λ x, x ∈ ys) xs)).
Next Obligation. intros ???. by rewrite Forall_forall. Qed.
Next Obligation. intros ???. by rewrite Forall_forall. Qed.
End subseteq.

(** Setoids *)
Section setoid.
  Context `{Equiv A}.
  Implicit Types l k : list A.

  Lemma list_equiv_Forall2 l k : l ≡ k ↔ Forall2 (≡) l k.
  Proof. split; induction 1; constructor; auto. Qed.
  Lemma list_equiv_lookup l k : l ≡ k ↔ ∀ i, l !! i ≡ k !! i.
  Proof.
    rewrite list_equiv_Forall2, Forall2_lookup.
    by setoid_rewrite option_equiv_Forall2.
  Qed.

  Global Instance list_equivalence :
    Equivalence (≡@{A}) → Equivalence (≡@{list A}).
  Proof.
    split.
    - intros l. by apply list_equiv_Forall2.
    - intros l k; rewrite !list_equiv_Forall2; by intros.
    - intros l1 l2 l3; rewrite !list_equiv_Forall2; intros; by trans l2.
  Qed.
  Global Instance list_leibniz `{!LeibnizEquiv A} : LeibnizEquiv (list A).
  Proof. induction 1; f_equal; fold_leibniz; auto. Qed.

  Global Instance cons_proper : Proper ((≡) ==> (≡) ==> (≡@{list A})) cons.
  Proof. by constructor. Qed.
  Global Instance app_proper : Proper ((≡) ==> (≡) ==> (≡@{list A})) app.
  Proof. induction 1; intros ???; simpl; try constructor; auto. Qed.
  Global Instance length_proper : Proper ((≡@{list A}) ==> (=)) length.
  Proof. induction 1; f_equal/=; auto. Qed.
  Global Instance tail_proper : Proper ((≡@{list A}) ==> (≡)) tail.
  Proof. destruct 1; try constructor; auto. Qed.
  Global Instance take_proper n : Proper ((≡@{list A}) ==> (≡)) (take n).
  Proof. induction n; destruct 1; constructor; auto. Qed.
  Global Instance drop_proper n : Proper ((≡@{list A}) ==> (≡)) (drop n).
  Proof. induction n; destruct 1; simpl; try constructor; auto. Qed.
  Global Instance list_lookup_proper i : Proper ((≡@{list A}) ==> (≡)) (lookup i).
  Proof. induction i; destruct 1; simpl; try constructor; auto. Qed.
  Global Instance list_lookup_total_proper `{!Inhabited A} i :
    Proper (≡@{A}) inhabitant →
    Proper ((≡@{list A}) ==> (≡)) (lookup_total i).
  Proof. intros ?. induction i; destruct 1; simpl; auto. Qed.
  Global Instance list_alter_proper :
    Proper (((≡) ==> (≡)) ==> (=) ==> (≡) ==> (≡@{list A})) alter.
  Proof.
    intros f1 f2 Hf i ? <-. induction i; destruct 1; constructor; eauto.
  Qed.
  Global Instance list_insert_proper i :
    Proper ((≡) ==> (≡) ==> (≡@{list A})) (insert i).
  Proof. intros ???; induction i; destruct 1; constructor; eauto. Qed.
  Global Instance list_inserts_proper i :
    Proper ((≡) ==> (≡) ==> (≡@{list A})) (list_inserts i).
  Proof.
    intros k1 k2 Hk; revert i.
    induction Hk; intros ????; simpl; try f_equiv; naive_solver.
  Qed.
  Global Instance list_delete_proper i :
    Proper ((≡) ==> (≡@{list A})) (delete i).
  Proof. induction i; destruct 1; try constructor; eauto. Qed.
  Global Instance option_list_proper : Proper ((≡) ==> (≡@{list A})) option_list.
  Proof. destruct 1; repeat constructor; auto. Qed.
  Global Instance list_filter_proper P `{∀ x, Decision (P x)} :
    Proper ((≡) ==> iff) P → Proper ((≡) ==> (≡@{list A})) (filter P).
  Proof. intros ???. rewrite !list_equiv_Forall2. by apply Forall2_filter. Qed.
  Global Instance replicate_proper n : Proper ((≡@{A}) ==> (≡)) (replicate n).
  Proof. induction n; constructor; auto. Qed.
  Global Instance rotate_proper n : Proper ((≡@{list A}) ==> (≡)) (rotate n).
  Proof. intros ??. rewrite !list_equiv_Forall2. by apply Forall2_rotate. Qed.
  Global Instance rotate_take_proper s e : Proper ((≡@{list A}) ==> (≡)) (rotate_take s e).
  Proof. intros ??. rewrite !list_equiv_Forall2. by apply Forall2_rotate_take. Qed.
  Global Instance reverse_proper : Proper ((≡) ==> (≡@{list A})) reverse.
  Proof.
    induction 1; rewrite ?reverse_cons; simpl; [constructor|].
    apply app_proper; repeat constructor; auto.
  Qed.
  Global Instance last_proper : Proper ((≡) ==> (≡)) (@last A).
  Proof. induction 1 as [|????? []]; simpl; repeat constructor; auto. Qed.
  Global Instance resize_proper n : Proper ((≡) ==> (≡) ==> (≡@{list A})) (resize n).
  Proof.
    induction n; destruct 2; simpl; repeat (constructor || f_equiv); auto.
  Qed.

  Global Instance cons_equiv_inj : Inj2 (≡) (≡) (≡) (@cons A).
  Proof. inversion 1; auto. Qed.

  Lemma nil_equiv_eq l : l ≡ [] ↔ l = [].
  Proof. split; [by inversion_clear 1|intros ->; constructor]. Qed.
  Lemma cons_equiv_eq l x k : l ≡ x :: k ↔ ∃ x' k', l = x' :: k' ∧ x' ≡ x ∧ k' ≡ k.
  Proof. split; [inversion 1; naive_solver|naive_solver (by constructor)]. Qed.
  Lemma list_singleton_equiv_eq l x : l ≡ [x] ↔ ∃ x', l = [x'] ∧ x' ≡ x.
  Proof. rewrite cons_equiv_eq. setoid_rewrite nil_equiv_eq. naive_solver. Qed.
  Lemma app_equiv_eq l k1 k2 :
    l ≡ k1 ++ k2 ↔ ∃ k1' k2', l = k1' ++ k2' ∧ k1' ≡ k1 ∧ k2' ≡ k2.
  Proof.
    split; [|intros (?&?&->&?&?); by f_equiv].
    setoid_rewrite list_equiv_Forall2. rewrite Forall2_app_inv_r. naive_solver.
  Qed.

  Lemma equiv_Permutation l1 l2 l3 :
    l1 ≡ l2 → l2 ≡ₚ l3 → ∃ l2', l1 ≡ₚ l2' ∧ l2' ≡ l3.
  Proof.
    intros Hequiv Hperm. revert l1 Hequiv.
    induction Hperm as [|x l2 l3 _ IH|x y l2|l2 l3 l4 _ IH1 _ IH2]; intros l1.
    - intros ?. by exists l1.
    - intros (x'&l2'&->&?&(l2''&?&?)%IH)%cons_equiv_eq.
      exists (x' :: l2''). by repeat constructor.
    - intros (y'&?&->&?&(x'&l2'&->&?&?)%cons_equiv_eq)%cons_equiv_eq.
      exists (x' :: y' :: l2'). by repeat constructor.
    - intros (l2'&?&(l3'&?&?)%IH2)%IH1. exists l3'. split; [by etrans|done].
  Qed.

  Lemma Permutation_equiv `{!Equivalence (≡@{A})} l1 l2 l3 :
    l1 ≡ₚ l2 → l2 ≡ l3 → ∃ l2', l1 ≡ l2' ∧ l2' ≡ₚ l3.
  Proof.
    intros Hperm%symmetry Hequiv%symmetry.
    destruct (equiv_Permutation _ _  _ Hequiv Hperm) as (l2'&?&?).
    by exists l2'.
  Qed.
End setoid.

(** * Properties of the [find] function *)
Section find.
  Context {A} (P : A → Prop) `{∀ x, Decision (P x)}.

  Lemma list_find_Some l i x  :
    list_find P l = Some (i,x) ↔
      l !! i = Some x ∧ P x ∧ ∀ j y, l !! j = Some y → j < i → ¬P y.
  Proof.
    revert i. induction l as [|y l IH]; intros i; csimpl; [naive_solver|].
    case_decide.
    - split; [naive_solver lia|]. intros (Hi&HP&Hlt).
      destruct i as [|i]; simplify_eq/=; [done|].
      destruct (Hlt 0 y); naive_solver lia.
    - split.
      + intros ([i' x']&Hl&?)%fmap_Some; simplify_eq/=.
        apply IH in Hl as (?&?&Hlt). split_and!; [done..|].
        intros [|j] ?; naive_solver lia.
      + intros (?&?&Hlt). destruct i as [|i]; simplify_eq/=; [done|].
        rewrite (proj2 (IH i)); [done|]. split_and!; [done..|].
        intros j z ???. destruct (Hlt (S j) z); naive_solver lia.
  Qed.

  Lemma list_find_elem_of l x : x ∈ l → P x → is_Some (list_find P l).
  Proof.
    induction 1 as [|x y l ? IH]; intros; simplify_option_eq; eauto.
    by destruct IH as [[i x'] ->]; [|exists (S i, x')].
  Qed.

  Lemma list_find_None l :
    list_find P l = None ↔ Forall (λ x, ¬P x) l.
  Proof.
    rewrite eq_None_not_Some, Forall_forall. split.
    - intros Hl x Hx HP. destruct Hl. eauto using list_find_elem_of.
    - intros HP [[i x] (?%elem_of_list_lookup_2&?&?)%list_find_Some]; naive_solver.
  Qed.

  Lemma list_find_app_None l1 l2 :
    list_find P (l1 ++ l2) = None ↔ list_find P l1 = None ∧ list_find P l2 = None.
  Proof. by rewrite !list_find_None, Forall_app. Qed.

  Lemma list_find_app_Some l1 l2 i x :
    list_find P (l1 ++ l2) = Some (i,x) ↔
      list_find P l1 = Some (i,x) ∨
      length l1 ≤ i ∧ list_find P l1 = None ∧ list_find P l2 = Some (i - length l1,x).
  Proof.
    split.
    - intros ([?|[??]]%lookup_app_Some&?&Hleast)%list_find_Some.
      + left. apply list_find_Some; eauto using lookup_app_l_Some.
      + right. split; [lia|]. split.
        { apply list_find_None, Forall_lookup. intros j z ??.
          assert (j < length l1) by eauto using lookup_lt_Some.
          naive_solver eauto using lookup_app_l_Some with lia. }
        apply list_find_Some. split_and!; [done..|].
        intros j z ??. eapply (Hleast (length l1 + j)); [|lia].
        by rewrite lookup_app_r, Nat.add_sub' by lia.
    - intros [(?&?&Hleast)%list_find_Some|(?&Hl1&(?&?&Hleast)%list_find_Some)].
      + apply list_find_Some. split_and!; [by auto using lookup_app_l_Some..|].
        assert (i < length l1) by eauto using lookup_lt_Some.
        intros j y ?%lookup_app_Some; naive_solver eauto with lia.
      + rewrite list_find_Some, lookup_app_Some. split_and!; [by auto..|].
        intros j y [?|?]%lookup_app_Some ?; [|naive_solver auto with lia].
        by eapply (Forall_lookup_1 (not ∘ P) l1); [by apply list_find_None|..].
  Qed.
  Lemma list_find_app_l l1 l2 i x:
    list_find P l1 = Some (i, x) → list_find P (l1 ++ l2) = Some (i, x).
  Proof. rewrite list_find_app_Some. auto. Qed.
  Lemma list_find_app_r l1 l2:
    list_find P l1 = None →
    list_find P (l1 ++ l2) = prod_map (λ x, x + length l1) id <$> list_find P l2.
  Proof.
    intros. apply option_eq; intros [j y]. rewrite list_find_app_Some. split.
    - intros [?|(?&?&->)]; naive_solver auto with f_equal lia.
    - intros ([??]&->&?)%fmap_Some; naive_solver auto with f_equal lia.
  Qed.

  Lemma list_find_insert_Some l i j x y :
    list_find P (<[i:=x]> l) = Some (j,y) ↔
      (j < i ∧ list_find P l = Some (j,y)) ∨
      (i = j ∧ x = y ∧ j < length l ∧ P x ∧ ∀ k z, l !! k = Some z → k < i → ¬P z) ∨
      (i < j ∧ ¬P x ∧ list_find P l = Some (j,y) ∧ ∀ z, l !! i = Some z → ¬P z) ∨
      (∃ z, i < j ∧ ¬P x ∧ P y ∧ P z ∧ l !! i = Some z ∧ l !! j = Some y ∧
            ∀ k z, l !! k = Some z → k ≠ i → k < j → ¬P z).
   Proof.
     split.
     - intros ([(->&->&?)|[??]]%list_lookup_insert_Some&?&Hleast)%list_find_Some.
       { right; left. split_and!; [done..|]. intros k z ??.
         apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia. }
       assert (j < i ∨ i < j) as [?|?] by lia.
       { left. rewrite list_find_Some. split_and!; [by auto..|]. intros k z ??.
         apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia. }
       right; right. assert (j < length l) by eauto using lookup_lt_Some.
       destruct (lookup_lt_is_Some_2 l i) as [z ?]; [lia|].
       destruct (decide (P z)).
       { right. exists z. split_and!; [done| |done..|].
         + apply (Hleast i); [|done]. by rewrite list_lookup_insert by lia.
         + intros k z' ???.
           apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia. }
       left. split_and!; [done|..|naive_solver].
       + apply (Hleast i); [|done]. by rewrite list_lookup_insert by lia.
       + apply list_find_Some. split_and!; [by auto..|]. intros k z' ??.
         destruct (decide (k = i)) as [->|]; [naive_solver|].
         apply (Hleast k); [|lia]. by rewrite list_lookup_insert_ne by lia.
     - intros [[? Hl]|[(->&->&?&?&Hleast)|[(?&?&Hl&Hnot)|(z&?&?&?&?&?&?&?Hleast)]]];
         apply list_find_Some.
       + apply list_find_Some in Hl as (?&?&Hleast).
         rewrite list_lookup_insert_ne by lia. split_and!; [done..|].
         intros k z [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
       + rewrite list_lookup_insert by done. split_and!; [by auto..|].
         intros k z [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
       + apply list_find_Some in Hl as (?&?&Hleast).
         rewrite list_lookup_insert_ne by lia. split_and!; [done..|].
         intros k z [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
       + rewrite list_lookup_insert_ne by lia. split_and!; [done..|].
         intros k z' [(->&->&?)|[??]]%list_lookup_insert_Some; eauto with lia.
  Qed.

  Lemma list_find_fmap {B : Type} (f : B → A) (l : list B) :
    list_find P (f <$> l) = prod_map id f <$> list_find (P ∘ f) l.
  Proof.
    induction l as [|x l IH]; [done|]; csimpl. (* csimpl re-folds fmap *)
    case_decide; [done|].
    rewrite IH. by destruct (list_find (P ∘ f) l).
  Qed.

  Lemma list_find_ext (Q : A → Prop) `{∀ x, Decision (Q x)} l :
    (∀ x, P x ↔ Q x) →
    list_find P l = list_find Q l.
  Proof.
    intros HPQ. induction l as [|x l IH]; simpl; [done|].
    by rewrite (decide_ext (P x) (Q x)), IH by done.
  Qed.
End find.

(** * Properties of the monadic operations *)
Lemma list_fmap_id {A} (l : list A) : id <$> l = l.
Proof. induction l; f_equal/=; auto. Qed.

Global Instance list_fmap_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B})) fmap.
Proof. induction 2; csimpl; constructor; auto. Qed.

Section fmap.
  Context {A B : Type} (f : A → B).
  Implicit Types l : list A.

  Lemma list_fmap_compose {C} (g : B → C) l : g ∘ f <$> l = g <$> (f <$> l).
  Proof. induction l; f_equal/=; auto. Qed.

  Lemma list_fmap_inj_1 f' l x :
    f <$> l = f' <$> l → x ∈ l → f x = f' x.
  Proof. intros Hf Hin. induction Hin; naive_solver. Qed.

  Definition fmap_nil : f <$> [] = [] := eq_refl.
  Definition fmap_cons x l : f <$> x :: l = f x :: (f <$> l) := eq_refl.

  Lemma list_fmap_singleton x : f <$> [x] = [f x].
  Proof. reflexivity. Qed.
  Lemma fmap_app l1 l2 : f <$> l1 ++ l2 = (f <$> l1) ++ (f <$> l2).
  Proof. by induction l1; f_equal/=. Qed.
  Lemma fmap_snoc l x : f <$> l ++ [x] = (f <$> l) ++ [f x].
  Proof. rewrite fmap_app, list_fmap_singleton. done. Qed.
  Lemma fmap_nil_inv k :  f <$> k = [] → k = [].
  Proof. by destruct k. Qed.
  Lemma fmap_cons_inv y l k :
    f <$> l = y :: k → ∃ x l', y = f x ∧ k = f <$> l' ∧ l = x :: l'.
  Proof. intros. destruct l; simplify_eq/=; eauto. Qed.
  Lemma fmap_app_inv l k1 k2 :
    f <$> l = k1 ++ k2 → ∃ l1 l2, k1 = f <$> l1 ∧ k2 = f <$> l2 ∧ l = l1 ++ l2.
  Proof.
    revert l. induction k1 as [|y k1 IH]; simpl; [intros l ?; by eexists [],l|].
    intros [|x l] ?; simplify_eq/=.
    destruct (IH l) as (l1&l2&->&->&->); [done|]. by exists (x :: l1), l2.
  Qed.
  Lemma fmap_option_list mx :
    f <$> (option_list mx) = option_list (f <$> mx).
  Proof. by destruct mx. Qed.

  Lemma list_fmap_alt l :
    f <$> l = omap (λ x, Some (f x)) l.
  Proof. induction l; simplify_eq/=; done. Qed.

  Lemma fmap_length l : length (f <$> l) = length l.
  Proof. by induction l; f_equal/=. Qed.
  Lemma fmap_reverse l : f <$> reverse l = reverse (f <$> l).
  Proof.
    induction l as [|?? IH]; csimpl; by rewrite ?reverse_cons, ?fmap_app, ?IH.
  Qed.
  Lemma fmap_tail l : f <$> tail l = tail (f <$> l).
  Proof. by destruct l. Qed.
  Lemma fmap_last l : last (f <$> l) = f <$> last l.
  Proof. induction l as [|? []]; simpl; auto. Qed.
  Lemma fmap_replicate n x :  f <$> replicate n x = replicate n (f x).
  Proof. by induction n; f_equal/=. Qed.
  Lemma fmap_take n l : f <$> take n l = take n (f <$> l).
  Proof. revert n. by induction l; intros [|?]; f_equal/=. Qed.
  Lemma fmap_drop n l : f <$> drop n l = drop n (f <$> l).
  Proof. revert n. by induction l; intros [|?]; f_equal/=. Qed.
  Lemma fmap_resize n x l : f <$> resize n x l = resize n (f x) (f <$> l).
  Proof.
    revert n. induction l; intros [|?]; f_equal/=; auto using fmap_replicate.
  Qed.
  Lemma const_fmap (l : list A) (y : B) :
    (∀ x, f x = y) → f <$> l = replicate (length l) y.
  Proof. intros; induction l; f_equal/=; auto. Qed.
  Lemma list_lookup_fmap l i : (f <$> l) !! i = f <$> (l !! i).
  Proof. revert i. induction l; intros [|n]; by try revert n. Qed.
  Lemma list_lookup_fmap_Some l i x :
    (f <$> l) !! i =  Some x ↔ ∃ y, l !! i = Some y ∧ x = f y.
  Proof. by rewrite list_lookup_fmap, fmap_Some. Qed.
  Lemma list_lookup_total_fmap `{!Inhabited A, !Inhabited B} l i :
    i < length l → (f <$> l) !!! i = f (l !!! i).
  Proof.
    intros [x Hx]%lookup_lt_is_Some_2.
    by rewrite !list_lookup_total_alt, list_lookup_fmap, Hx.
  Qed.
  Lemma list_lookup_fmap_inv l i x :
    (f <$> l) !! i = Some x → ∃ y, x = f y ∧ l !! i = Some y.
  Proof.
    intros Hi. rewrite list_lookup_fmap in Hi.
    destruct (l !! i) eqn:?; simplify_eq/=; eauto.
  Qed.
  Lemma list_fmap_insert l i x: f <$> <[i:=x]>l = <[i:=f x]>(f <$> l).
  Proof. revert i. by induction l; intros [|i]; f_equal/=. Qed.
  Lemma list_alter_fmap (g : A → A) (h : B → B) l i :
    Forall (λ x, f (g x) = h (f x)) l → f <$> alter g i l = alter h i (f <$> l).
  Proof. intros Hl. revert i. by induction Hl; intros [|i]; f_equal/=. Qed.
  Lemma list_fmap_delete l i : f <$> (delete i l) = delete i (f <$> l).
  Proof.
    revert i. induction l; intros i; destruct i; csimpl; eauto.
    naive_solver congruence.
  Qed.

  Lemma elem_of_list_fmap_1 l x : x ∈ l → f x ∈ f <$> l.
  Proof. induction 1; csimpl; rewrite elem_of_cons; intuition. Qed.
  Lemma elem_of_list_fmap_1_alt l x y : x ∈ l → y = f x → y ∈ f <$> l.
  Proof. intros. subst. by apply elem_of_list_fmap_1. Qed.
  Lemma elem_of_list_fmap_2 l x : x ∈ f <$> l → ∃ y, x = f y ∧ y ∈ l.
  Proof.
    induction l as [|y l IH]; simpl; inversion_clear 1.
    - exists y. split; [done | by left].
    - destruct IH as [z [??]]; [done|]. exists z. split; [done | by right].
  Qed.
  Lemma elem_of_list_fmap l x : x ∈ f <$> l ↔ ∃ y, x = f y ∧ y ∈ l.
  Proof.
    naive_solver eauto using elem_of_list_fmap_1_alt, elem_of_list_fmap_2.
  Qed.
  Lemma elem_of_list_fmap_2_inj `{!Inj (=) (=) f} l x : f x ∈ f <$> l → x ∈ l.
  Proof.
    intros (y, (E, I))%elem_of_list_fmap_2. by rewrite (inj f) in I.
  Qed.
  Lemma elem_of_list_fmap_inj `{!Inj (=) (=) f} l x : f x ∈ f <$> l ↔ x ∈ l.
  Proof.
    naive_solver eauto using elem_of_list_fmap_1, elem_of_list_fmap_2_inj.
  Qed.

  Lemma list_fmap_inj R1 R2 :
    Inj R1 R2 f → Inj (Forall2 R1) (Forall2 R2) (fmap f).
  Proof.
    intros ? l1. induction l1; intros [|??]; inversion 1; constructor; auto.
  Qed.
  Global Instance list_fmap_eq_inj : Inj (=) (=) f → Inj (=@{list A}) (=) (fmap f).
  Proof. intros ?%list_fmap_inj ?? ?%list_eq_Forall2%(inj _). by apply list_eq_Forall2. Qed.
  Global Instance list_fmap_equiv_inj `{!Equiv A, !Equiv B} :
    Inj (≡) (≡) f → Inj (≡@{list A}) (≡) (fmap f).
  Proof.
    intros ?%list_fmap_inj ?? ?%list_equiv_Forall2%(inj _).
    by apply list_equiv_Forall2.
  Qed.

  (** A version of [NoDup_fmap_2] that does not require [f] to be injective for
      *all* inputs. *)
  Lemma NoDup_fmap_2_strong l :
    (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) →
    NoDup l →
    NoDup (f <$> l).
  Proof.
    intros Hinj. induction 1 as [|x l ?? IH]; simpl; constructor.
    - intros [y [Hxy ?]]%elem_of_list_fmap.
      apply Hinj in Hxy; [by subst|by constructor..].
    - apply IH. clear- Hinj.
      intros x' y Hx' Hy. apply Hinj; by constructor.
  Qed.

  Lemma NoDup_fmap_1 l : NoDup (f <$> l) → NoDup l.
  Proof.
    induction l; simpl; inversion_clear 1; constructor; auto.
    rewrite elem_of_list_fmap in *. naive_solver.
  Qed.
  Lemma NoDup_fmap_2 `{!Inj (=) (=) f} l : NoDup l → NoDup (f <$> l).
  Proof. apply NoDup_fmap_2_strong. intros ?? _ _. apply (inj f). Qed.
  Lemma NoDup_fmap `{!Inj (=) (=) f} l : NoDup (f <$> l) ↔ NoDup l.
  Proof. split; auto using NoDup_fmap_1, NoDup_fmap_2. Qed.

  Global Instance fmap_sublist: Proper (sublist ==> sublist) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.
  Global Instance fmap_submseteq: Proper (submseteq ==> submseteq) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.
  Global Instance fmap_Permutation: Proper ((≡ₚ) ==> (≡ₚ)) (fmap f).
  Proof. induction 1; simpl; econstructor; eauto. Qed.

  Lemma Forall_fmap_ext_1 (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l → fmap f l = fmap g l.
  Proof. by induction 1; f_equal/=. Qed.
  Lemma Forall_fmap_ext (g : A → B) (l : list A) :
    Forall (λ x, f x = g x) l ↔ fmap f l = fmap g l.
  Proof.
    split; [auto using Forall_fmap_ext_1|].
    induction l; simpl; constructor; simplify_eq; auto.
  Qed.
  Lemma Forall_fmap (P : B → Prop) l : Forall P (f <$> l) ↔ Forall (P ∘ f) l.
  Proof. split; induction l; inversion_clear 1; constructor; auto. Qed.
  Lemma Exists_fmap (P : B → Prop) l : Exists P (f <$> l) ↔ Exists (P ∘ f) l.
  Proof. split; induction l; inversion 1; constructor; by auto. Qed.

  Lemma Forall2_fmap_l {C} (P : B → C → Prop) l k :
    Forall2 P (f <$> l) k ↔ Forall2 (P ∘ f) l k.
  Proof.
    split; revert k; induction l; inversion_clear 1; constructor; auto.
  Qed.
  Lemma Forall2_fmap_r {C} (P : C → B → Prop) k l :
    Forall2 P k (f <$> l) ↔ Forall2 (λ x, P x ∘ f) k l.
  Proof.
    split; revert k; induction l; inversion_clear 1; constructor; auto.
  Qed.
  Lemma Forall2_fmap_1 {C D} (g : C → D) (P : B → D → Prop) l k :
    Forall2 P (f <$> l) (g <$> k) → Forall2 (λ x1 x2, P (f x1) (g x2)) l k.
  Proof. revert k; induction l; intros [|??]; inversion_clear 1; auto. Qed.
  Lemma Forall2_fmap_2 {C D} (g : C → D) (P : B → D → Prop) l k :
    Forall2 (λ x1 x2, P (f x1) (g x2)) l k → Forall2 P (f <$> l) (g <$> k).
  Proof. induction 1; csimpl; auto. Qed.
  Lemma Forall2_fmap {C D} (g : C → D) (P : B → D → Prop) l k :
    Forall2 P (f <$> l) (g <$> k) ↔ Forall2 (λ x1 x2, P (f x1) (g x2)) l k.
  Proof. split; auto using Forall2_fmap_1, Forall2_fmap_2. Qed.

  Lemma list_fmap_bind {C} (g : B → list C) l : (f <$> l) ≫= g = l ≫= g ∘ f.
  Proof. by induction l; f_equal/=. Qed.
End fmap.

Section ext.
  Context {A B : Type}.
  Implicit Types l : list A.

  Lemma list_fmap_ext (f g : A → B) l :
    (∀ i x, l !! i = Some x → f x = g x) → f <$> l = g <$> l.
  Proof.
    intros Hfg. apply list_eq; intros i. rewrite !list_lookup_fmap.
    destruct (l !! i) eqn:?; f_equal/=; eauto.
  Qed.
  Lemma list_fmap_equiv_ext `{!Equiv B} (f g : A → B) l :
    (∀ i x, l !! i = Some x → f x ≡ g x) → f <$> l ≡ g <$> l.
  Proof.
    intros Hl. apply list_equiv_lookup; intros i. rewrite !list_lookup_fmap.
    destruct (l !! i) eqn:?; simpl; constructor; eauto.
  Qed.
End ext.

Lemma list_alter_fmap_mono {A} (f : A → A) (g : A → A) l i :
  Forall (λ x, f (g x) = g (f x)) l → f <$> alter g i l = alter g i (f <$> l).
Proof. auto using list_alter_fmap. Qed.
Lemma NoDup_fmap_fst {A B} (l : list (A * B)) :
  (∀ x y1 y2, (x,y1) ∈ l → (x,y2) ∈ l → y1 = y2) → NoDup l → NoDup (l.*1).
Proof.
  intros Hunique. induction 1 as [|[x1 y1] l Hin Hnodup IH]; csimpl; constructor.
  - rewrite elem_of_list_fmap.
    intros [[x2 y2] [??]]; simpl in *; subst. destruct Hin.
    rewrite (Hunique x2 y1 y2); rewrite ?elem_of_cons; auto.
  - apply IH. intros. eapply Hunique; rewrite ?elem_of_cons; eauto.
Qed.

Global Instance list_omap_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B})) omap.
Proof.
  intros f1 f2 Hf. induction 1 as [|x1 x2 l1 l2 Hx Hl]; csimpl; [constructor|].
  destruct (Hf _ _ Hx); by repeat f_equiv.
Qed.

Section omap.
  Context {A B : Type} (f : A → option B).
  Implicit Types l : list A.

  Lemma list_fmap_omap {C} (g : B → C) l :
    g <$> omap f l = omap (λ x, g <$> (f x)) l.
  Proof.
    induction l as [|x y IH]; [done|]. csimpl.
    destruct (f x); csimpl; [|done]. by f_equal.
  Qed.
  Lemma list_omap_ext {A'} (g : A' → option B) l1 (l2 : list A') :
    Forall2 (λ a b, f a = g b) l1 l2 →
    omap f l1 = omap g l2.
  Proof.
    induction 1 as [|x y l l' Hfg ? IH]; [done|].
    csimpl. rewrite Hfg. destruct (g y); [|done]. by f_equal.
  Qed.
  Lemma elem_of_list_omap l y : y ∈ omap f l ↔ ∃ x, x ∈ l ∧ f x = Some y.
  Proof.
    split.
    - induction l as [|x l]; csimpl; repeat case_match; inversion 1; subst;
        setoid_rewrite elem_of_cons; naive_solver.
    - intros (x&Hx&?). by induction Hx; csimpl; repeat case_match;
        simplify_eq; try constructor; auto.
  Qed.
  Global Instance omap_Permutation : Proper ((≡ₚ) ==> (≡ₚ)) (omap f).
  Proof. induction 1; simpl; repeat case_match; econstructor; eauto. Qed.

  Lemma omap_app l1 l2 :
    omap f (l1 ++ l2) = omap f l1 ++ omap f l2.
  Proof. induction l1; csimpl; repeat case_match; naive_solver congruence. Qed.
  Lemma omap_option_list mx :
    omap f (option_list mx) = option_list (mx ≫= f).
  Proof. by destruct mx. Qed.
End omap.

Global Instance list_bind_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B})) mbind.
Proof. induction 2; csimpl; constructor || f_equiv; auto. Qed.

Section bind.
  Context {A B : Type} (f : A → list B).

  Lemma list_bind_ext (g : A → list B) l1 l2 :
    (∀ x, f x = g x) → l1 = l2 → l1 ≫= f = l2 ≫= g.
  Proof. intros ? <-. by induction l1; f_equal/=. Qed.
  Lemma Forall_bind_ext (g : A → list B) (l : list A) :
    Forall (λ x, f x = g x) l → l ≫= f = l ≫= g.
  Proof. by induction 1; f_equal/=. Qed.
  Global Instance bind_sublist: Proper (sublist ==> sublist) (mbind f).
  Proof.
    induction 1; simpl; auto;
      [by apply sublist_app|by apply sublist_inserts_l].
  Qed.
  Global Instance bind_submseteq: Proper (submseteq ==> submseteq) (mbind f).
  Proof.
    induction 1; csimpl; auto.
    - by apply submseteq_app.
    - by rewrite !(assoc_L (++)), (comm (++) (f _)).
    - by apply submseteq_inserts_l.
    - etrans; eauto.
  Qed.
  Global Instance bind_Permutation: Proper ((≡ₚ) ==> (≡ₚ)) (mbind f).
  Proof.
    induction 1; csimpl; auto.
    - by f_equiv.
    - by rewrite !(assoc_L (++)), (comm (++) (f _)).
    - etrans; eauto.
  Qed.
  Lemma bind_cons x l : (x :: l) ≫= f = f x ++ l ≫= f.
  Proof. done. Qed.
  Lemma bind_singleton x : [x] ≫= f = f x.
  Proof. csimpl. by rewrite (right_id_L _ (++)). Qed.
  Lemma bind_app l1 l2 : (l1 ++ l2) ≫= f = (l1 ≫= f) ++ (l2 ≫= f).
  Proof. by induction l1; csimpl; rewrite <-?(assoc_L (++)); f_equal. Qed.
  Lemma elem_of_list_bind (x : B) (l : list A) :
    x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
  Proof.
    split.
    - induction l as [|y l IH]; csimpl; [inversion 1|].
      rewrite elem_of_app. intros [?|?].
      + exists y. split; [done | by left].
      + destruct IH as [z [??]]; [done|]. exists z. split; [done | by right].
    - intros [y [Hx Hy]]. induction Hy; csimpl; rewrite elem_of_app; intuition.
  Qed.
  Lemma Forall_bind (P : B → Prop) l :
    Forall P (l ≫= f) ↔ Forall (Forall P ∘ f) l.
  Proof.
    split.
    - induction l; csimpl; rewrite ?Forall_app; constructor; csimpl; intuition.
    - induction 1; csimpl; rewrite ?Forall_app; auto.
  Qed.
  Lemma Forall2_bind {C D} (g : C → list D) (P : B → D → Prop) l1 l2 :
    Forall2 (λ x1 x2, Forall2 P (f x1) (g x2)) l1 l2 →
    Forall2 P (l1 ≫= f) (l2 ≫= g).
  Proof. induction 1; csimpl; auto using Forall2_app. Qed.
  Lemma NoDup_bind l :
    (∀ x1 x2 y, x1 ∈ l → x2 ∈ l → y ∈ f x1 → y ∈ f x2 → x1 = x2) →
    (∀ x, x ∈ l → NoDup (f x)) → NoDup l → NoDup (l ≫= f).
  Proof.
    intros Hinj Hf. induction 1 as [|x l ?? IH]; csimpl; [constructor|].
    apply NoDup_app. split_and!.
    - eauto 10 using elem_of_list_here.
    - intros y ? (x'&?&?)%elem_of_list_bind.
      destruct (Hinj x x' y); auto using elem_of_list_here, elem_of_list_further.
    - eauto 10 using elem_of_list_further.
  Qed.
End bind.

Global Instance list_join_proper `{!Equiv A} :
  Proper ((≡) ==> (≡@{list A})) mjoin.
Proof. induction 1; simpl; [constructor|solve_proper]. Qed.

Section ret_join.
  Context {A : Type}.

  Lemma list_join_bind (ls : list (list A)) : mjoin ls = ls ≫= id.
  Proof. by induction ls; f_equal/=. Qed.
  Global Instance join_Permutation : Proper ((≡ₚ@{list A}) ==> (≡ₚ)) mjoin.
  Proof. intros ?? E. by rewrite !list_join_bind, E. Qed.
  Lemma elem_of_list_ret (x y : A) : x ∈ @mret list _ A y ↔ x = y.
  Proof. apply elem_of_list_singleton. Qed.
  Lemma elem_of_list_join (x : A) (ls : list (list A)) :
    x ∈ mjoin ls ↔ ∃ l : list A, x ∈ l ∧ l ∈ ls.
  Proof. by rewrite list_join_bind, elem_of_list_bind. Qed.
  Lemma join_nil (ls : list (list A)) : mjoin ls = [] ↔ Forall (.= []) ls.
  Proof.
    split; [|by induction 1 as [|[|??] ?]].
    by induction ls as [|[|??] ?]; constructor; auto.
  Qed.
  Lemma join_nil_1 (ls : list (list A)) : mjoin ls = [] → Forall (.= []) ls.
  Proof. by rewrite join_nil. Qed.
  Lemma join_nil_2 (ls : list (list A)) : Forall (.= []) ls → mjoin ls = [].
  Proof. by rewrite join_nil. Qed.
  Lemma Forall_join (P : A → Prop) (ls: list (list A)) :
    Forall (Forall P) ls → Forall P (mjoin ls).
  Proof. induction 1; simpl; auto using Forall_app_2. Qed.
  Lemma Forall2_join {B} (P : A → B → Prop) ls1 ls2 :
    Forall2 (Forall2 P) ls1 ls2 → Forall2 P (mjoin ls1) (mjoin ls2).
  Proof. induction 1; simpl; auto using Forall2_app. Qed.
End ret_join.

Global Instance mapM_proper `{!Equiv A, !Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{option (list B)})) mapM.
Proof.
  induction 2; csimpl; repeat (f_equiv || constructor || intro || auto).
Qed.

Section mapM.
  Context {A B : Type} (f : A → option B).

  Lemma mapM_ext (g : A → option B) l : (∀ x, f x = g x) → mapM f l = mapM g l.
  Proof. intros Hfg. by induction l as [|?? IHl]; simpl; rewrite ?Hfg, ?IHl. Qed.

  Lemma Forall2_mapM_ext (g : A → option B) l k :
    Forall2 (λ x y, f x = g y) l k → mapM f l = mapM g k.
  Proof. induction 1 as [|???? Hfg ? IH]; simpl; [done|]. by rewrite Hfg, IH. Qed.
  Lemma Forall_mapM_ext (g : A → option B) l :
    Forall (λ x, f x = g x) l → mapM f l = mapM g l.
  Proof. induction 1 as [|?? Hfg ? IH]; simpl; [done|]. by rewrite Hfg, IH. Qed.

  Lemma mapM_Some_1 l k : mapM f l = Some k → Forall2 (λ x y, f x = Some y) l k.
  Proof.
    revert k. induction l as [|x l]; intros [|y k]; simpl; try done.
    - destruct (f x); simpl; [|discriminate]. by destruct (mapM f l).
    - destruct (f x) eqn:?; intros; simplify_option_eq; auto.
  Qed.
  Lemma mapM_Some_2 l k : Forall2 (λ x y, f x = Some y) l k → mapM f l = Some k.
  Proof.
    induction 1 as [|???? Hf ? IH]; simpl; [done |].
    rewrite Hf. simpl. by rewrite IH.
  Qed.
  Lemma mapM_Some l k : mapM f l = Some k ↔ Forall2 (λ x y, f x = Some y) l k.
  Proof. split; auto using mapM_Some_1, mapM_Some_2. Qed.
  Lemma mapM_length l k : mapM f l = Some k → length l = length k.
  Proof. intros. by eapply Forall2_length, mapM_Some_1. Qed.
  Lemma mapM_None_1 l : mapM f l = None → Exists (λ x, f x = None) l.
  Proof.
    induction l as [|x l IH]; simpl; [done|].
    destruct (f x) eqn:?; simpl; eauto. by destruct (mapM f l); eauto.
  Qed.
  Lemma mapM_None_2 l : Exists (λ x, f x = None) l → mapM f l = None.
  Proof.
    induction 1 as [x l Hx|x l ? IH]; simpl; [by rewrite Hx|].
    by destruct (f x); simpl; rewrite ?IH.
  Qed.
  Lemma mapM_None l : mapM f l = None ↔ Exists (λ x, f x = None) l.
  Proof. split; auto using mapM_None_1, mapM_None_2. Qed.
  Lemma mapM_is_Some_1 l : is_Some (mapM f l) → Forall (is_Some ∘ f) l.
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (not_Exists_Forall _).
  Qed.
  Lemma mapM_is_Some_2 l : Forall (is_Some ∘ f) l → is_Some (mapM f l).
  Proof.
    unfold compose. setoid_rewrite <-not_eq_None_Some.
    rewrite mapM_None. apply (Forall_not_Exists _).
  Qed.
  Lemma mapM_is_Some l : is_Some (mapM f l) ↔ Forall (is_Some ∘ f) l.
  Proof. split; auto using mapM_is_Some_1, mapM_is_Some_2. Qed.

  Lemma mapM_fmap_Forall_Some (g : B → A) (l : list B) :
    Forall (λ x, f (g x) = Some x) l → mapM f (g <$> l) = Some l.
  Proof. by induction 1; simpl; simplify_option_eq. Qed.
  Lemma mapM_fmap_Some (g : B → A) (l : list B) :
    (∀ x, f (g x) = Some x) → mapM f (g <$> l) = Some l.
  Proof. intros. by apply mapM_fmap_Forall_Some, Forall_true. Qed.

  Lemma mapM_fmap_Forall2_Some_inv (g : B → A) (l : list A) (k : list B) :
    mapM f l = Some k → Forall2 (λ x y, f x = Some y → g y = x) l k → g <$> k = l.
  Proof. induction 2; simplify_option_eq; naive_solver. Qed.
  Lemma mapM_fmap_Some_inv (g : B → A) (l : list A) (k : list B) :
    mapM f l = Some k → (∀ x y, f x = Some y → g y = x) → g <$> k = l.
  Proof. eauto using mapM_fmap_Forall2_Some_inv, Forall2_true, mapM_length. Qed.
End mapM.

Lemma imap_const {A B} (f : A → B) l : imap (const f) l = f <$> l.
Proof. induction l; f_equal/=; auto. Qed.

Global Instance imap_proper `{!Equiv A, !Equiv B} :
  Proper (pointwise_relation _ ((≡) ==> (≡)) ==> (≡@{list A}) ==> (≡@{list B}))
         imap.
Proof.
  intros f f' Hf l l' Hl. revert f f' Hf.
  induction Hl as [|x1 x2 l1 l2 ?? IH]; intros f f' Hf; simpl; constructor.
  - by apply Hf.
  - apply IH. intros i y y' ?; simpl. by apply Hf.
Qed.

Section imap.
  Context {A B : Type} (f : nat → A → B).

  Lemma imap_ext g l :
    (∀ i x, l !! i = Some x → f i x = g i x) → imap f l = imap g l.
  Proof. revert f g; induction l as [|x l IH]; intros; f_equal/=; eauto. Qed.

  Lemma imap_nil : imap f [] = [].
  Proof. done. Qed.
  Lemma imap_app l1 l2 :
    imap f (l1 ++ l2) = imap f l1 ++ imap (λ n, f (length l1 + n)) l2.
  Proof.
    revert f. induction l1 as [|x l1 IH]; intros f; f_equal/=.
    by rewrite IH.
  Qed.
  Lemma imap_cons x l : imap f (x :: l) = f 0 x :: imap (f ∘ S) l.
  Proof. done. Qed.

  Lemma imap_fmap {C} (g : C → A) l : imap f (g <$> l) = imap (λ n, f n ∘ g) l.
  Proof. revert f. induction l; intros; f_equal/=; eauto. Qed.
  Lemma fmap_imap {C} (g : B → C) l : g <$> imap f l = imap (λ n, g ∘ f n) l.
  Proof. revert f. induction l; intros; f_equal/=; eauto. Qed.

  Lemma list_lookup_imap l i : imap f l !! i = f i <$> l !! i.
  Proof.
    revert f i. induction l as [|x l IH]; intros f [|i]; f_equal/=; auto.
    by rewrite IH.
  Qed.
  Lemma list_lookup_imap_Some l i x :
    imap f l !! i = Some x ↔ ∃ y, l !! i = Some y ∧ x = f i y.
  Proof. by rewrite list_lookup_imap, fmap_Some. Qed.
  Lemma list_lookup_total_imap `{!Inhabited A, !Inhabited B} l i :
    i < length l → imap f l !!! i = f i (l !!! i).
  Proof.
    intros [x Hx]%lookup_lt_is_Some_2.
    by rewrite !list_lookup_total_alt, list_lookup_imap, Hx.
  Qed.

  Lemma imap_length l : length (imap f l) = length l.
  Proof. revert f. induction l; simpl; eauto. Qed.

  Lemma elem_of_lookup_imap_1 l x :
    x ∈ imap f l → ∃ i y, x = f i y ∧ l !! i = Some y.
  Proof.
    intros [i Hin]%elem_of_list_lookup. rewrite list_lookup_imap in Hin.
    simplify_option_eq; naive_solver.
  Qed.
  Lemma elem_of_lookup_imap_2 l x i : l !! i = Some x → f i x ∈ imap f l.
  Proof.
    intros Hl. rewrite elem_of_list_lookup.
    exists i. by rewrite list_lookup_imap, Hl.
  Qed.
  Lemma elem_of_lookup_imap l x :
    x ∈ imap f l ↔ ∃ i y, x = f i y ∧ l !! i = Some y.
  Proof. naive_solver eauto using elem_of_lookup_imap_1, elem_of_lookup_imap_2. Qed.
End imap.

(** ** Properties of the [permutations] function *)
Section permutations.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l : list A.

  Lemma interleave_cons x l : x :: l ∈ interleave x l.
  Proof. destruct l; simpl; rewrite elem_of_cons; auto. Qed.
  Lemma interleave_Permutation x l l' : l' ∈ interleave x l → l' ≡ₚ x :: l.
  Proof.
    revert l'. induction l as [|y l IH]; intros l'; simpl.
    - rewrite elem_of_list_singleton. by intros ->.
    - rewrite elem_of_cons, elem_of_list_fmap. intros [->|[? [-> H]]]; [done|].
      rewrite (IH _ H). constructor.
  Qed.
  Lemma permutations_refl l : l ∈ permutations l.
  Proof.
    induction l; simpl; [by apply elem_of_list_singleton|].
    apply elem_of_list_bind. eauto using interleave_cons.
  Qed.
  Lemma permutations_skip x l l' :
    l ∈ permutations l' → x :: l ∈ permutations (x :: l').
  Proof. intro. apply elem_of_list_bind; eauto using interleave_cons. Qed.
  Lemma permutations_swap x y l : y :: x :: l ∈ permutations (x :: y :: l).
  Proof.
    simpl. apply elem_of_list_bind. exists (y :: l). split; simpl.
    - destruct l; csimpl; rewrite !elem_of_cons; auto.
    - apply elem_of_list_bind. simpl.
      eauto using interleave_cons, permutations_refl.
  Qed.
  Lemma permutations_nil l : l ∈ permutations [] ↔ l = [].
  Proof. simpl. by rewrite elem_of_list_singleton. Qed.
  Lemma interleave_interleave_toggle x1 x2 l1 l2 l3 :
    l1 ∈ interleave x1 l2 → l2 ∈ interleave x2 l3 → ∃ l4,
      l1 ∈ interleave x2 l4 ∧ l4 ∈ interleave x1 l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { rewrite !elem_of_list_singleton. intros ? ->. exists [x1].
      change (interleave x2 [x1]) with ([[x2; x1]] ++ [[x1; x2]]).
      by rewrite (comm (++)), elem_of_list_singleton. }
    rewrite elem_of_cons, elem_of_list_fmap.
    intros Hl1 [? | [l2' [??]]]; simplify_eq/=.
    - rewrite !elem_of_cons, elem_of_list_fmap in Hl1.
      destruct Hl1 as [? | [? | [l4 [??]]]]; subst.
      + exists (x1 :: y :: l3). csimpl. rewrite !elem_of_cons. tauto.
      + exists (x1 :: y :: l3). csimpl. rewrite !elem_of_cons. tauto.
      + exists l4. simpl. rewrite elem_of_cons. auto using interleave_cons.
    - rewrite elem_of_cons, elem_of_list_fmap in Hl1.
      destruct Hl1 as [? | [l1' [??]]]; subst.
      + exists (x1 :: y :: l3). csimpl.
        rewrite !elem_of_cons, !elem_of_list_fmap.
        split; [| by auto]. right. right. exists (y :: l2').
        rewrite elem_of_list_fmap. naive_solver.
      + destruct (IH l1' l2') as [l4 [??]]; auto. exists (y :: l4). simpl.
        rewrite !elem_of_cons, !elem_of_list_fmap. naive_solver.
  Qed.
  Lemma permutations_interleave_toggle x l1 l2 l3 :
    l1 ∈ permutations l2 → l2 ∈ interleave x l3 → ∃ l4,
      l1 ∈ interleave x l4 ∧ l4 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|y l3 IH]; intros l1 l2; simpl.
    { rewrite elem_of_list_singleton. intros Hl1 ->. eexists [].
      by rewrite elem_of_list_singleton. }
    rewrite elem_of_cons, elem_of_list_fmap.
    intros Hl1 [? | [l2' [? Hl2']]]; simplify_eq/=.
    - rewrite elem_of_list_bind in Hl1.
      destruct Hl1 as [l1' [??]]. by exists l1'.
    - rewrite elem_of_list_bind in Hl1. setoid_rewrite elem_of_list_bind.
      destruct Hl1 as [l1' [??]]. destruct (IH l1' l2') as (l1''&?&?); auto.
      destruct (interleave_interleave_toggle y x l1 l1' l1'') as (?&?&?); eauto.
  Qed.
  Lemma permutations_trans l1 l2 l3 :
    l1 ∈ permutations l2 → l2 ∈ permutations l3 → l1 ∈ permutations l3.
  Proof.
    revert l1 l2. induction l3 as [|x l3 IH]; intros l1 l2; simpl.
    - rewrite !elem_of_list_singleton. intros Hl1 ->; simpl in *.
      by rewrite elem_of_list_singleton in Hl1.
    - rewrite !elem_of_list_bind. intros Hl1 [l2' [Hl2 Hl2']].
      destruct (permutations_interleave_toggle x l1 l2 l2') as [? [??]]; eauto.
  Qed.
  Lemma permutations_Permutation l l' : l' ∈ permutations l ↔ l ≡ₚ l'.
  Proof.
    split.
    - revert l'. induction l; simpl; intros l''.
      + rewrite elem_of_list_singleton. by intros ->.
      + rewrite elem_of_list_bind. intros [l' [Hl'' ?]].
        rewrite (interleave_Permutation _ _ _ Hl''). constructor; auto.
    - induction 1; eauto using permutations_refl,
        permutations_skip, permutations_swap, permutations_trans.
  Qed.
End permutations.

(** ** Properties of the folding functions *)
(** Note that [foldr] has much better support, so when in doubt, it should be
preferred over [foldl]. *)
Definition foldr_app := @fold_right_app.

Lemma foldr_cons {A B} (f : B → A → A) (a : A) l x :
  foldr f a (x :: l) = f x (foldr f a l).
Proof. done. Qed.
Lemma foldr_snoc {A B} (f : B → A → A) (a : A) l x :
  foldr f a (l ++ [x]) = foldr f (f x a) l.
Proof. rewrite foldr_app. done. Qed.

Lemma foldr_fmap {A B C} (f : B → A → A) x (l : list C) g :
  foldr f x (g <$> l) = foldr (λ b a, f (g b) a) x l.
Proof. induction l; f_equal/=; auto. Qed.
Lemma foldr_ext {A B} (f1 f2 : B → A → A) x1 x2 l1 l2 :
  (∀ b a, f1 b a = f2 b a) → l1 = l2 → x1 = x2 → foldr f1 x1 l1 = foldr f2 x2 l2.
Proof. intros Hf -> ->. induction l2 as [|x l2 IH]; f_equal/=; by rewrite Hf, IH. Qed.

Lemma foldr_permutation {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (b : B) `{Hf : !∀ x, Proper (R ==> R) (f x)} (l1 l2 : list A) :
  (∀ j1 a1 j2 a2 b,
    j1 ≠ j2 → l1 !! j1 = Some a1 → l1 !! j2 = Some a2 →
    R (f a1 (f a2 b)) (f a2 (f a1 b))) →
  l1 ≡ₚ l2 → R (foldr f b l1) (foldr f b l2).
Proof.
  intros Hf'. induction 1 as [|x l1 l2 _ IH|x y l|l1 l2 l3 Hl12 IH _ IH']; simpl.
  - done.
  - apply Hf, IH; eauto.
  - apply (Hf' 0 _ 1); eauto.
  - etrans; [eapply IH, Hf'|].
    apply IH'; intros j1 a1 j2 a2 b' ???.
    symmetry in Hl12; apply Permutation_inj in Hl12 as [_ (g&?&Hg)].
    apply (Hf' (g j1) _ (g j2)); [naive_solver|by rewrite <-Hg..].
Qed.
Lemma foldr_permutation_proper {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (b : B) `{!∀ x, Proper (R ==> R) (f x)}
    (Hf : ∀ a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((≡ₚ) ==> R) (foldr f b).
Proof. intros l1 l2 Hl. apply foldr_permutation; auto. Qed.
Global Instance foldr_permutation_proper' {A} (R : relation A) `{!PreOrder R}
    (f : A → A → A) (a : A) `{!∀ a, Proper (R ==> R) (f a), !Assoc R f, !Comm R f} :
  Proper ((≡ₚ) ==> R) (foldr f a).
Proof.
  apply (foldr_permutation_proper R f); [solve_proper|].
  assert (Proper (R ==> R ==> R) f).
  { intros a1 a2 Ha b1 b2 Hb. by rewrite Hb, (comm f a1), Ha, (comm f). }
  intros a1 a2 b.
  by rewrite (assoc f), (comm f _ b), (assoc f), (comm f b), (comm f _ a2).
Qed.
Lemma foldr_cons_permute {A} (R : relation A) `{!PreOrder R}
    (f : A → A → A) (a : A)
    `{!∀ a, Proper (R ==> R) (f a), !Assoc R f, !Comm R f} x l :
  R (foldr f a (x :: l)) (foldr f (f x a) l).
Proof.
  rewrite <-foldr_snoc.
  eapply foldr_permutation_proper'; [done..|].
  rewrite Permutation_app_comm. done.
Qed.
Lemma foldr_cons_permute_eq {A} (f : A → A → A) (a : A)
    `{!Assoc (=) f, !Comm (=) f} x l :
  foldr f a (x :: l) = foldr f (f x a) l.
Proof. eapply (foldr_cons_permute eq); apply _. Qed.

Lemma foldr_comm_acc_strong {A B} (R : relation B) `{!PreOrder R}
    (f : A → B → B) (g : B → B) b l :
  (∀ x, Proper (R ==> R) (f x)) →
  (∀ x y, x ∈ l → R (f x (g y)) (g (f x y))) →
  R (foldr f (g b) l) (g (foldr f b l)).
Proof.
  intros ? Hcomm. induction l as [|x l IH]; simpl; [done|].
  rewrite <-Hcomm by eauto using elem_of_list_here.
  by rewrite IH by eauto using elem_of_list_further.
Qed.
Lemma foldr_comm_acc {A} (f : A → A → A) (g : A → A) (a : A) l :
  (∀ x y, f x (g y) = g (f x y)) →
  foldr f (g a) l = g (foldr f a l).
Proof. intros. apply (foldr_comm_acc_strong _); [solve_proper|done]. Qed.

Lemma foldl_app {A B} (f : A → B → A) (l k : list B) (a : A) :
  foldl f a (l ++ k) = foldl f (foldl f a l) k.
Proof. revert a. induction l; simpl; auto. Qed.
Lemma foldl_snoc {A B} (f : A → B → A) (a : A) l x :
  foldl f a (l ++ [x]) = f (foldl f a l) x.
Proof. rewrite foldl_app. done. Qed.
Lemma foldl_fmap {A B C} (f : A → B → A) x (l : list C) g :
  foldl f x (g <$> l) = foldl (λ a b, f a (g b)) x l.
Proof. revert x. induction l; f_equal/=; auto. Qed.

(** ** Properties of the [zip_with] and [zip] functions *)
Global Instance zip_with_proper `{!Equiv A, !Equiv B, !Equiv C} :
  Proper (((≡) ==> (≡) ==> (≡)) ==>
          (≡@{list A}) ==> (≡@{list B}) ==> (≡@{list C})) zip_with.
Proof.
  intros f1 f2 Hf. induction 1; destruct 1; simpl; [constructor..|].
  f_equiv; [|by auto]. by apply Hf.
Qed.

Section zip_with.
  Context {A B C : Type} (f : A → B → C).
  Implicit Types x : A.
  Implicit Types y : B.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma zip_with_nil_r l : zip_with f l [] = [].
  Proof. by destruct l. Qed.
  Lemma zip_with_app l1 l2 k1 k2 :
    length l1 = length k1 →
    zip_with f (l1 ++ l2) (k1 ++ k2) = zip_with f l1 k1 ++ zip_with f l2 k2.
  Proof. rewrite <-Forall2_same_length. induction 1; f_equal/=; auto. Qed.
  Lemma zip_with_app_l l1 l2 k :
    zip_with f (l1 ++ l2) k
    = zip_with f l1 (take (length l1) k) ++ zip_with f l2 (drop (length l1) k).
  Proof.
    revert k. induction l1; intros [|??]; f_equal/=; auto. by destruct l2.
  Qed.
  Lemma zip_with_app_r l k1 k2 :
    zip_with f l (k1 ++ k2)
    = zip_with f (take (length k1) l) k1 ++ zip_with f (drop (length k1) l) k2.
  Proof. revert l. induction k1; intros [|??]; f_equal/=; auto. Qed.
  Lemma zip_with_flip l k : zip_with (flip f) k l = zip_with f l k.
  Proof. revert k. induction l; intros [|??]; f_equal/=; auto. Qed.
  Lemma zip_with_ext (g : A → B → C) l1 l2 k1 k2 :
    (∀ x y, f x y = g x y) → l1 = l2 → k1 = k2 →
    zip_with f l1 k1 = zip_with g l2 k2.
  Proof. intros ? <-<-. revert k1. by induction l1; intros [|??]; f_equal/=. Qed.
  Lemma Forall_zip_with_ext_l (g : A → B → C) l k1 k2 :
    Forall (λ x, ∀ y, f x y = g x y) l → k1 = k2 →
    zip_with f l k1 = zip_with g l k2.
  Proof. intros Hl <-. revert k1. by induction Hl; intros [|??]; f_equal/=. Qed.
  Lemma Forall_zip_with_ext_r (g : A → B → C) l1 l2 k :
    l1 = l2 → Forall (λ y, ∀ x, f x y = g x y) k →
    zip_with f l1 k = zip_with g l2 k.
  Proof. intros <- Hk. revert l1. by induction Hk; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_fmap_l {D} (g : D → A) lD k :
    zip_with f (g <$> lD) k = zip_with (λ z, f (g z)) lD k.
  Proof. revert k. by induction lD; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_fmap_r {D} (g : D → B) l kD :
    zip_with f l (g <$> kD) = zip_with (λ x z, f x (g z)) l kD.
  Proof. revert kD. by induction l; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_nil_inv l k : zip_with f l k = [] → l = [] ∨ k = [].
  Proof. destruct l, k; intros; simplify_eq/=; auto. Qed.
  Lemma zip_with_cons_inv l k z lC :
    zip_with f l k = z :: lC →
    ∃ x y l' k', z = f x y ∧ lC = zip_with f l' k' ∧ l = x :: l' ∧ k = y :: k'.
  Proof. intros. destruct l, k; simplify_eq/=; repeat eexists. Qed.
  Lemma zip_with_app_inv l k lC1 lC2 :
    zip_with f l k = lC1 ++ lC2 →
    ∃ l1 k1 l2 k2, lC1 = zip_with f l1 k1 ∧ lC2 = zip_with f l2 k2 ∧
      l = l1 ++ l2 ∧ k = k1 ++ k2 ∧ length l1 = length k1.
  Proof.
    revert l k. induction lC1 as [|z lC1 IH]; simpl.
    { intros l k ?. by eexists [], [], l, k. }
    intros [|x l] [|y k] ?; simplify_eq/=.
    destruct (IH l k) as (l1&k1&l2&k2&->&->&->&->&?); [done |].
    exists (x :: l1), (y :: k1), l2, k2; simpl; auto with congruence.
  Qed.
  Lemma zip_with_inj `{!Inj2 (=) (=) (=) f} l1 l2 k1 k2 :
    length l1 = length k1 → length l2 = length k2 →
    zip_with f l1 k1 = zip_with f l2 k2 → l1 = l2 ∧ k1 = k2.
  Proof.
    rewrite <-!Forall2_same_length. intros Hl. revert l2 k2.
    induction Hl; intros ?? [] ?; f_equal; naive_solver.
  Qed.
  Lemma zip_with_length l k :
    length (zip_with f l k) = min (length l) (length k).
  Proof. revert k. induction l; intros [|??]; simpl; auto with lia. Qed.
  Lemma zip_with_length_l l k :
    length l ≤ length k → length (zip_with f l k) = length l.
  Proof. rewrite zip_with_length; lia. Qed.
  Lemma zip_with_length_l_eq l k :
    length l = length k → length (zip_with f l k) = length l.
  Proof. rewrite zip_with_length; lia. Qed.
  Lemma zip_with_length_r l k :
    length k ≤ length l → length (zip_with f l k) = length k.
  Proof. rewrite zip_with_length; lia. Qed.
  Lemma zip_with_length_r_eq l k :
    length k = length l → length (zip_with f l k) = length k.
  Proof. rewrite zip_with_length; lia. Qed.
  Lemma zip_with_length_same_l P l k :
    Forall2 P l k → length (zip_with f l k) = length l.
  Proof. induction 1; simpl; auto. Qed.
  Lemma zip_with_length_same_r P l k :
    Forall2 P l k → length (zip_with f l k) = length k.
  Proof. induction 1; simpl; auto. Qed.
  Lemma lookup_zip_with l k i :
    zip_with f l k !! i = (x ← l !! i; y ← k !! i; Some (f x y)).
  Proof.
    revert k i. induction l; intros [|??] [|?]; f_equal/=; auto.
    by destruct (_ !! _).
  Qed.
  Lemma lookup_total_zip_with `{!Inhabited A, !Inhabited B, !Inhabited C} l k i :
    i < length l → i < length k → zip_with f l k !!! i = f (l !!! i) (k !!! i).
  Proof.
    intros [x Hx]%lookup_lt_is_Some_2 [y Hy]%lookup_lt_is_Some_2.
    by rewrite !list_lookup_total_alt, lookup_zip_with, Hx, Hy.
  Qed.
  Lemma lookup_zip_with_Some l k i z :
    zip_with f l k !! i = Some z
    ↔ ∃ x y, z = f x y ∧ l !! i = Some x ∧ k !! i = Some y.
  Proof. rewrite lookup_zip_with. destruct (l !! i), (k !! i); naive_solver. Qed.
  Lemma insert_zip_with l k i x y :
    <[i:=f x y]>(zip_with f l k) = zip_with f (<[i:=x]>l) (<[i:=y]>k).
  Proof. revert i k. induction l; intros [|?] [|??]; f_equal/=; auto. Qed.
  Lemma fmap_zip_with_l (g : C → A) l k :
    (∀ x y, g (f x y) = x) → length l ≤ length k → g <$> zip_with f l k = l.
  Proof. revert k. induction l; intros [|??] ??; f_equal/=; auto with lia. Qed.
  Lemma fmap_zip_with_r (g : C → B) l k :
    (∀ x y, g (f x y) = y) → length k ≤ length l → g <$> zip_with f l k = k.
  Proof. revert l. induction k; intros [|??] ??; f_equal/=; auto with lia. Qed.
  Lemma zip_with_zip l k : zip_with f l k = uncurry f <$> zip l k.
  Proof. revert k. by induction l; intros [|??]; f_equal/=. Qed.
  Lemma zip_with_fst_snd lk : zip_with f (lk.*1) (lk.*2) = uncurry f <$> lk.
  Proof. by induction lk as [|[]]; f_equal/=. Qed.
  Lemma zip_with_replicate n x y :
    zip_with f (replicate n x) (replicate n y) = replicate n (f x y).
  Proof. by induction n; f_equal/=. Qed.
  Lemma zip_with_replicate_l n x k :
    length k ≤ n → zip_with f (replicate n x) k = f x <$> k.
  Proof. revert n. induction k; intros [|?] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_replicate_r n y l :
    length l ≤ n → zip_with f l (replicate n y) = flip f y <$> l.
  Proof. revert n. induction l; intros [|?] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_replicate_r_eq n y l :
    length l = n → zip_with f l (replicate n y) = flip f y <$> l.
  Proof. intros; apply zip_with_replicate_r; lia. Qed.
  Lemma zip_with_take n l k :
    take n (zip_with f l k) = zip_with f (take n l) (take n k).
  Proof. revert n k. by induction l; intros [|?] [|??]; f_equal/=. Qed.
  Lemma zip_with_drop n l k :
    drop n (zip_with f l k) = zip_with f (drop n l) (drop n k).
  Proof.
    revert n k. induction l; intros [] []; f_equal/=; auto using zip_with_nil_r.
  Qed.
  Lemma zip_with_take_l' n l k :
    length l `min` length k ≤ n → zip_with f (take n l) k = zip_with f l k.
  Proof. revert n k. induction l; intros [] [] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_take_l l k :
    zip_with f (take (length k) l) k = zip_with f l k.
  Proof. apply zip_with_take_l'; lia. Qed.
  Lemma zip_with_take_r' n l k :
    length l `min` length k ≤ n → zip_with f l (take n k) = zip_with f l k.
  Proof. revert n k. induction l; intros [] [] ?; f_equal/=; auto with lia. Qed.
  Lemma zip_with_take_r l k :
    zip_with f l (take (length l) k) = zip_with f l k.
  Proof. apply zip_with_take_r'; lia. Qed.
  Lemma zip_with_take_both' n1 n2 l k :
    length l `min` length k ≤ n1 → length l `min` length k ≤ n2 →
    zip_with f (take n1 l) (take n2 k) = zip_with f l k.
  Proof.
    intros.
    rewrite zip_with_take_l'; [apply zip_with_take_r' | rewrite take_length]; lia.
  Qed.
  Lemma zip_with_take_both l k :
    zip_with f (take (length k) l) (take (length l) k) = zip_with f l k.
  Proof. apply zip_with_take_both'; lia. Qed.
  Lemma Forall_zip_with_fst (P : A → Prop) (Q : C → Prop) l k :
    Forall P l → Forall (λ y, ∀ x, P x → Q (f x y)) k →
    Forall Q (zip_with f l k).
  Proof. intros Hl. revert k. induction Hl; destruct 1; simpl in *; auto. Qed.
  Lemma Forall_zip_with_snd (P : B → Prop) (Q : C → Prop) l k :
    Forall (λ x, ∀ y, P y → Q (f x y)) l → Forall P k →
    Forall Q (zip_with f l k).
  Proof. intros Hl. revert k. induction Hl; destruct 1; simpl in *; auto. Qed.

  Lemma elem_of_lookup_zip_with_1 l k (z : C) :
    z ∈ zip_with f l k → ∃ i x y, z = f x y ∧ l !! i = Some x ∧ k !! i = Some y.
  Proof.
    intros [i Hin]%elem_of_list_lookup. rewrite lookup_zip_with in Hin.
    simplify_option_eq; naive_solver.
  Qed.

  Lemma elem_of_lookup_zip_with_2 l k x y (z : C) i :
    l !! i = Some x → k !! i = Some y → f x y ∈ zip_with f l k.
  Proof.
    intros Hl Hk. rewrite elem_of_list_lookup.
    exists i. by rewrite lookup_zip_with, Hl, Hk.
  Qed.

  Lemma elem_of_lookup_zip_with l k (z : C) :
    z ∈ zip_with f l k ↔ ∃ i x y, z = f x y ∧ l !! i = Some x ∧ k !! i = Some y.
  Proof.
    naive_solver eauto using
                 elem_of_lookup_zip_with_1, elem_of_lookup_zip_with_2.
  Qed.

  Lemma elem_of_zip_with l k (z : C) :
    z ∈ zip_with f l k → ∃ x y, z = f x y ∧ x ∈ l ∧ y ∈ k.
  Proof.
    intros ?%elem_of_lookup_zip_with.
    naive_solver eauto using elem_of_list_lookup_2.
  Qed.

End zip_with.

Lemma zip_with_diag {A C} (f : A → A → C) l :
  zip_with f l l = (λ x, f x x) <$> l.
Proof. induction l as [|?? IH]; [done|]. simpl. rewrite IH. done. Qed.

Lemma zip_with_sublist_alter {A B} (f : A → B → A) g l k i n l' k' :
  length l = length k →
  sublist_lookup i n l = Some l' → sublist_lookup i n k = Some k' →
  length (g l') = length k' → zip_with f (g l') k' = g (zip_with f l' k') →
  zip_with f (sublist_alter g i n l) k = sublist_alter g i n (zip_with f l k).
Proof.
  unfold sublist_lookup, sublist_alter. intros Hlen; rewrite Hlen.
  intros ?? Hl' Hk'. simplify_option_eq.
  by rewrite !zip_with_app_l, !zip_with_drop, Hl', drop_drop, !zip_with_take,
    !take_length_le, Hk' by (rewrite ?drop_length; auto with lia).
Qed.

Section zip.
  Context {A B : Type}.
  Implicit Types l : list A.
  Implicit Types k : list B.

  Lemma fst_zip l k : length l ≤ length k → (zip l k).*1 = l.
  Proof. by apply fmap_zip_with_l. Qed.
  Lemma snd_zip l k : length k ≤ length l → (zip l k).*2 = k.
  Proof. by apply fmap_zip_with_r. Qed.
  Lemma zip_fst_snd (lk : list (A * B)) : zip (lk.*1) (lk.*2) = lk.
  Proof. by induction lk as [|[]]; f_equal/=. Qed.
  Lemma Forall2_fst P l1 l2 k1 k2 :
    length l2 = length k2 → Forall2 P l1 k1 →
    Forall2 (λ x y, P (x.1) (y.1)) (zip l1 l2) (zip k1 k2).
  Proof.
    rewrite <-Forall2_same_length. intros Hlk2 Hlk1. revert l2 k2 Hlk2.
    induction Hlk1; intros ?? [|??????]; simpl; auto.
  Qed.
  Lemma Forall2_snd P l1 l2 k1 k2 :
    length l1 = length k1 → Forall2 P l2 k2 →
    Forall2 (λ x y, P (x.2) (y.2)) (zip l1 l2) (zip k1 k2).
  Proof.
    rewrite <-Forall2_same_length. intros Hlk1 Hlk2. revert l1 k1 Hlk1.
    induction Hlk2; intros ?? [|??????]; simpl; auto.
  Qed.

  Lemma elem_of_zip_l x1 x2 l k :
    (x1, x2) ∈ zip l k → x1 ∈ l.
  Proof. intros ?%elem_of_zip_with. naive_solver. Qed.

  Lemma elem_of_zip_r x1 x2 l k :
    (x1, x2) ∈ zip l k → x2 ∈ k.
  Proof. intros ?%elem_of_zip_with. naive_solver. Qed.
End zip.

Lemma zip_diag {A} (l : list A) :
  zip l l = (λ x, (x, x)) <$> l.
Proof. apply zip_with_diag. Qed.

Lemma elem_of_zipped_map {A B} (f : list A → list A → A → B) l k x :
  x ∈ zipped_map f l k ↔
    ∃ k' k'' y, k = k' ++ [y] ++ k'' ∧ x = f (reverse k' ++ l) k'' y.
Proof.
  split.
  - revert l. induction k as [|z k IH]; simpl; intros l; inversion_clear 1.
    { by eexists [], k, z. }
    destruct (IH (z :: l)) as (k'&k''&y&->&->); [done |].
    eexists (z :: k'), k'', y. by rewrite reverse_cons, <-(assoc_L (++)).
  - intros (k'&k''&y&->&->). revert l. induction k' as [|z k' IH]; [by left|].
    intros l; right. by rewrite reverse_cons, <-!(assoc_L (++)).
Qed.
Section zipped_list_ind.
  Context {A} (P : list A → list A → Prop).
  Context (Pnil : ∀ l, P l []) (Pcons : ∀ l k x, P (x :: l) k → P l (x :: k)).
  Fixpoint zipped_list_ind l k : P l k :=
    match k with
    | [] => Pnil _ | x :: k => Pcons _ _ _ (zipped_list_ind (x :: l) k)
    end.
End zipped_list_ind.
Lemma zipped_Forall_app {A} (P : list A → list A → A → Prop) l k k' :
  zipped_Forall P l (k ++ k') → zipped_Forall P (reverse k ++ l) k'.
Proof.
  revert l. induction k as [|x k IH]; simpl; [done |].
  inversion_clear 1. rewrite reverse_cons, <-(assoc_L (++)). by apply IH.
Qed.

Lemma TCForall_Forall {A} (P : A → Prop) xs : TCForall P xs ↔ Forall P xs.
Proof. split; induction 1; constructor; auto. Qed.

Global Instance TCForall_app {A} (P : A → Prop) xs ys :
  TCForall P xs → TCForall P ys → TCForall P (xs ++ ys).
Proof. rewrite !TCForall_Forall. apply Forall_app_2. Qed.

Lemma TCForall2_Forall2 {A B} (P : A → B → Prop) xs ys :
  TCForall2 P xs ys ↔ Forall2 P xs ys.
Proof. split; induction 1; constructor; auto. Qed.

Lemma TCExists_Exists {A} (P : A → Prop) l : TCExists P l ↔ Exists P l.
Proof. split; induction 1; constructor; solve [auto]. Qed.

Section positives_flatten_unflatten.
  Local Open Scope positive_scope.

  Lemma positives_flatten_go_app xs acc :
    positives_flatten_go xs acc = acc ++ positives_flatten_go xs 1.
  Proof.
    revert acc.
    induction xs as [|x xs IH]; intros acc; simpl.
    - reflexivity.
    - rewrite IH.
      rewrite (IH (6 ++ _)).
      rewrite 2!(assoc_L (++)).
      reflexivity.
  Qed.

  Lemma positives_unflatten_go_app p suffix xs acc :
    positives_unflatten_go (suffix ++ Pos.reverse (Pos.dup p)) xs acc =
    positives_unflatten_go suffix xs (acc ++ p).
  Proof.
    revert suffix acc.
    induction p as [p IH|p IH|]; intros acc suffix; simpl.
    - rewrite 2!Pos.reverse_xI.
      rewrite 2!(assoc_L (++)).
      rewrite IH.
      reflexivity.
    - rewrite 2!Pos.reverse_xO.
      rewrite 2!(assoc_L (++)).
      rewrite IH.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma positives_unflatten_flatten_go suffix xs acc :
    positives_unflatten_go (suffix ++ positives_flatten_go xs 1) acc 1 =
    positives_unflatten_go suffix (xs ++ acc) 1.
  Proof.
    revert suffix acc.
    induction xs as [|x xs IH]; intros suffix acc; simpl.
    - reflexivity.
    - rewrite positives_flatten_go_app.
      rewrite (assoc_L (++)).
      rewrite IH.
      rewrite (assoc_L (++)).
      rewrite positives_unflatten_go_app.
      simpl.
      rewrite (left_id_L 1 (++)).
      reflexivity.
  Qed.

  Lemma positives_unflatten_flatten xs :
    positives_unflatten (positives_flatten xs) = Some xs.
  Proof.
    unfold positives_flatten, positives_unflatten.
    replace (positives_flatten_go xs 1)
      with (1 ++ positives_flatten_go xs 1)
      by apply (left_id_L 1 (++)).
    rewrite positives_unflatten_flatten_go.
    simpl.
    rewrite (right_id_L [] (++)%list).
    reflexivity.
  Qed.

  Lemma positives_flatten_app xs ys :
    positives_flatten (xs ++ ys) = positives_flatten xs ++ positives_flatten ys.
  Proof.
    unfold positives_flatten.
    revert ys.
    induction xs as [|x xs IH]; intros ys; simpl.
    - rewrite (left_id_L 1 (++)).
      reflexivity.
    - rewrite positives_flatten_go_app, (positives_flatten_go_app xs).
      rewrite IH.
      rewrite (assoc_L (++)).
      reflexivity.
  Qed.

  Lemma positives_flatten_cons x xs :
    positives_flatten (x :: xs)
    = 1~1~0 ++ Pos.reverse (Pos.dup x) ++ positives_flatten xs.
  Proof.
    change (x :: xs) with ([x] ++ xs)%list.
    rewrite positives_flatten_app.
    rewrite (assoc_L (++)).
    reflexivity.
  Qed.

  Lemma positives_flatten_suffix (l k : list positive) :
    l `suffix_of` k → ∃ q, positives_flatten k = q ++ positives_flatten l.
  Proof.
    intros [l' ->].
    exists (positives_flatten l').
    apply positives_flatten_app.
  Qed.

  Lemma positives_flatten_suffix_eq p1 p2 (xs ys : list positive) :
    length xs = length ys →
    p1 ++ positives_flatten xs = p2 ++ positives_flatten ys →
    xs = ys.
  Proof.
    revert p1 p2 ys; induction xs as [|x xs IH];
      intros p1 p2 [|y ys] ?; simplify_eq/=; auto.
    rewrite !positives_flatten_cons, !(assoc _); intros Hl.
    assert (xs = ys) as <- by eauto; clear IH; f_equal.
    apply (inj (.++ positives_flatten xs)) in Hl.
    rewrite 2!Pos.reverse_dup in Hl.
    apply (Pos.dup_suffix_eq _ _ p1 p2) in Hl.
    by apply (inj Pos.reverse).
  Qed.
End positives_flatten_unflatten.

(** * Reflection over lists *)
(** We define a simple data structure [rlist] to capture a syntactic
representation of lists consisting of constants, applications and the nil list.
Note that we represent [(x ::.)] as [rapp (rnode [x])]. For now, we abstract
over the type of constants, but later we use [nat]s and a list representing
a corresponding environment. *)
Inductive rlist (A : Type) :=
  rnil : rlist A | rnode : A → rlist A | rapp : rlist A → rlist A → rlist A.
Global Arguments rnil {_} : assert.
Global Arguments rnode {_} _ : assert.
Global Arguments rapp {_} _ _ : assert.

Module rlist.
Fixpoint to_list {A} (t : rlist A) : list A :=
  match t with
  | rnil => [] | rnode l => [l] | rapp t1 t2 => to_list t1 ++ to_list t2
  end.
Notation env A := (list (list A)) (only parsing).
Definition eval {A} (E : env A) : rlist nat → list A :=
  fix go t :=
  match t with
  | rnil => []
  | rnode i => default [] (E !! i)
  | rapp t1 t2 => go t1 ++ go t2
  end.

(** A simple quoting mechanism using type classes. [QuoteLookup E1 E2 x i]
means: starting in environment [E1], look up the index [i] corresponding to the
constant [x]. In case [x] has a corresponding index [i] in [E1], the original
environment is given back as [E2]. Otherwise, the environment [E2] is extended
with a binding [i] for [x]. *)
Section quote_lookup.
  Context {A : Type}.
  Class QuoteLookup (E1 E2 : list A) (x : A) (i : nat) := {}.
  Global Instance quote_lookup_here E x : QuoteLookup (x :: E) (x :: E) x 0 := {}.
  Global Instance quote_lookup_end x : QuoteLookup [] [x] x 0 := {}.
  Global Instance quote_lookup_further E1 E2 x i y :
    QuoteLookup E1 E2 x i → QuoteLookup (y :: E1) (y :: E2) x (S i) | 1000 := {}.
End quote_lookup.

Section quote.
  Context {A : Type}.
  Class Quote (E1 E2 : env A) (l : list A) (t : rlist nat) := {}.
  Global Instance quote_nil E1 : Quote E1 E1 [] rnil := {}.
  Global Instance quote_node E1 E2 l i:
    QuoteLookup E1 E2 l i → Quote E1 E2 l (rnode i) | 1000 := {}.
  Global Instance quote_cons E1 E2 E3 x l i t :
    QuoteLookup E1 E2 [x] i →
    Quote E2 E3 l t → Quote E1 E3 (x :: l) (rapp (rnode i) t) := {}.
  Global Instance quote_app E1 E2 E3 l1 l2 t1 t2 :
    Quote E1 E2 l1 t1 → Quote E2 E3 l2 t2 → Quote E1 E3 (l1 ++ l2) (rapp t1 t2) := {}.
End quote.

Section eval.
  Context {A} (E : env A).

  Lemma eval_alt t : eval E t = to_list t ≫= default [] ∘ (E !!.).
  Proof.
    induction t; csimpl.
    - done.
    - by rewrite (right_id_L [] (++)).
    - rewrite bind_app. by f_equal.
  Qed.
  Lemma eval_eq t1 t2 : to_list t1 = to_list t2 → eval E t1 = eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
  Lemma eval_Permutation t1 t2 :
    to_list t1 ≡ₚ to_list t2 → eval E t1 ≡ₚ eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
  Lemma eval_submseteq t1 t2 :
    to_list t1 ⊆+ to_list t2 → eval E t1 ⊆+ eval E t2.
  Proof. intros Ht. by rewrite !eval_alt, Ht. Qed.
End eval.
End rlist.

(** * Tactics *)
Ltac quote_Permutation :=
  match goal with
  | |- ?l1 ≡ₚ ?l2 =>
    match type of (_ : rlist.Quote [] _ l1 _) with rlist.Quote _ ?E2 _ ?t1 =>
    match type of (_ : rlist.Quote E2 _ l2 _) with rlist.Quote _ ?E3 _ ?t2 =>
      change (rlist.eval E3 t1 ≡ₚ rlist.eval E3 t2)
    end end
  end.
Ltac solve_Permutation :=
  quote_Permutation; apply rlist.eval_Permutation;
  compute_done.

Ltac quote_submseteq :=
  match goal with
  | |- ?l1 ⊆+ ?l2 =>
    match type of (_ : rlist.Quote [] _ l1 _) with rlist.Quote _ ?E2 _ ?t1 =>
    match type of (_ : rlist.Quote E2 _ l2 _) with rlist.Quote _ ?E3 _ ?t2 =>
      change (rlist.eval E3 t1 ⊆+ rlist.eval E3 t2)
    end end
  end.
Ltac solve_submseteq :=
  quote_submseteq; apply rlist.eval_submseteq;
  compute_done.

Ltac decompose_elem_of_list := repeat
  match goal with
  | H : ?x ∈ [] |- _ => by destruct (not_elem_of_nil x)
  | H : _ ∈ _ :: _ |- _ => apply elem_of_cons in H; destruct H
  | H : _ ∈ _ ++ _ |- _ => apply elem_of_app in H; destruct H
  end.
Ltac solve_length :=
  simplify_eq/=;
  repeat (rewrite fmap_length || rewrite app_length);
  repeat match goal with
  | H : _ =@{list _} _ |- _ => apply (f_equal length) in H
  | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
  | H : context[length (_ <$> _)] |- _ => rewrite fmap_length in H
  end; done || congruence.
Ltac simplify_list_eq ::= repeat
  match goal with
  | _ => progress simplify_eq/=
  | H : [?x] !! ?i = Some ?y |- _ =>
    destruct i; [change (Some x = Some y) in H | discriminate]
  | H : _ <$> _ = [] |- _ => apply fmap_nil_inv in H
  | H : [] = _ <$> _ |- _ => symmetry in H; apply fmap_nil_inv in H
  | H : zip_with _ _ _ = [] |- _ => apply zip_with_nil_inv in H; destruct H
  | H : [] = zip_with _ _ _ |- _ => symmetry in H
  | |- context [(_ ++ _) ++ _] => rewrite <-(assoc_L (++))
  | H : context [(_ ++ _) ++ _] |- _ => rewrite <-(assoc_L (++)) in H
  | H : context [_ <$> (_ ++ _)] |- _ => rewrite fmap_app in H
  | |- context [_ <$> (_ ++ _)]  => rewrite fmap_app
  | |- context [_ ++ []] => rewrite (right_id_L [] (++))
  | H : context [_ ++ []] |- _ => rewrite (right_id_L [] (++)) in H
  | |- context [take _ (_ <$> _)] => rewrite <-fmap_take
  | H : context [take _ (_ <$> _)] |- _ => rewrite <-fmap_take in H
  | |- context [drop _ (_ <$> _)] => rewrite <-fmap_drop
  | H : context [drop _ (_ <$> _)] |- _ => rewrite <-fmap_drop in H
  | H : _ ++ _ = _ ++ _ |- _ =>
    repeat (rewrite <-app_comm_cons in H || rewrite <-(assoc_L (++)) in H);
    apply app_inj_1 in H; [destruct H|solve_length]
  | H : _ ++ _ = _ ++ _ |- _ =>
    repeat (rewrite app_comm_cons in H || rewrite (assoc_L (++)) in H);
    apply app_inj_2 in H; [destruct H|solve_length]
  | |- context [zip_with _ (_ ++ _) (_ ++ _)] =>
    rewrite zip_with_app by solve_length
  | |- context [take _ (_ ++ _)] => rewrite take_app_length' by solve_length
  | |- context [drop _ (_ ++ _)] => rewrite drop_app_length' by solve_length
  | H : context [zip_with _ (_ ++ _) (_ ++ _)] |- _ =>
    rewrite zip_with_app in H by solve_length
  | H : context [take _ (_ ++ _)] |- _ =>
    rewrite take_app_length' in H by solve_length
  | H : context [drop _ (_ ++ _)] |- _ =>
    rewrite drop_app_length' in H by solve_length
  | H : ?l !! ?i = _, H2 : context [(_ <$> ?l) !! ?i] |- _ =>
     rewrite list_lookup_fmap, H in H2
  end.
Ltac decompose_Forall_hyps :=
  repeat match goal with
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall _ (_ ++ _) |- _ => rewrite Forall_app in H; destruct H
  | H : Forall2 _ [] [] |- _ => clear H
  | H : Forall2 _ (_ :: _) [] |- _ => destruct (Forall2_cons_nil_inv _ _ _ H)
  | H : Forall2 _ [] (_ :: _) |- _ => destruct (Forall2_nil_cons_inv _ _ _ H)
  | H : Forall2 _ [] ?k |- _ => apply Forall2_nil_inv_l in H
  | H : Forall2 _ ?l [] |- _ => apply Forall2_nil_inv_r in H
  | H : Forall2 _ (_ :: _) (_ :: _) |- _ =>
    apply Forall2_cons_1 in H; destruct H
  | H : Forall2 _ (_ :: _) ?k |- _ =>
    let k_hd := fresh k "_hd" in let k_tl := fresh k "_tl" in
    apply Forall2_cons_inv_l in H; destruct H as (k_hd&k_tl&?&?&->);
    rename k_tl into k
  | H : Forall2 _ ?l (_ :: _) |- _ =>
    let l_hd := fresh l "_hd" in let l_tl := fresh l "_tl" in
    apply Forall2_cons_inv_r in H; destruct H as (l_hd&l_tl&?&?&->);
    rename l_tl into l
  | H : Forall2 _ (_ ++ _) ?k |- _ =>
    let k1 := fresh k "_1" in let k2 := fresh k "_2" in
    apply Forall2_app_inv_l in H; destruct H as (k1&k2&?&?&->)
  | H : Forall2 _ ?l (_ ++ _) |- _ =>
    let l1 := fresh l "_1" in let l2 := fresh l "_2" in
    apply Forall2_app_inv_r in H; destruct H as (l1&l2&?&?&->)
  | _ => progress simplify_eq/=
  | H : Forall3 _ _ (_ :: _) _ |- _ =>
    apply Forall3_cons_inv_m in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : Forall2 _ (_ :: _) ?k |- _ =>
    apply Forall2_cons_inv_l in H; destruct H as (?&?&?&?&?)
  | H : Forall2 _ ?l (_ :: _) |- _ =>
    apply Forall2_cons_inv_r in H; destruct H as (?&?&?&?&?)
  | H : Forall2 _ (_ ++ _) (_ ++ _) |- _ =>
    apply Forall2_app_inv in H; [destruct H|solve_length]
  | H : Forall2 _ ?l (_ ++ _) |- _ =>
    apply Forall2_app_inv_r in H; destruct H as (?&?&?&?&?)
  | H : Forall2 _ (_ ++ _) ?k |- _ =>
    apply Forall2_app_inv_l in H; destruct H as (?&?&?&?&?)
  | H : Forall3 _ _ (_ ++ _) _ |- _ =>
    apply Forall3_app_inv_m in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : Forall ?P ?l, H1 : ?l !! _ = Some ?x |- _ =>
    (* to avoid some stupid loops, not fool proof *)
    unless (P x) by auto using Forall_app_2, Forall_nil_2;
    let E := fresh in
    assert (P x) as E by (apply (Forall_lookup_1 P _ _ _ H H1)); lazy beta in E
  | H : Forall2 ?P ?l ?k |- _ =>
    match goal with
    | H1 : l !! ?i = Some ?x, H2 : k !! ?i = Some ?y |- _ =>
      unless (P x y) by done; let E := fresh in
      assert (P x y) as E by (by apply (Forall2_lookup_lr P l k i x y));
      lazy beta in E
    | H1 : l !! ?i = Some ?x |- _ =>
      try (match goal with _ : k !! i = Some _ |- _ => fail 2 end);
      destruct (Forall2_lookup_l P _ _ _ _ H H1) as (?&?&?)
    | H2 : k !! ?i = Some ?y |- _ =>
      try (match goal with _ : l !! i = Some _ |- _ => fail 2 end);
      destruct (Forall2_lookup_r P _ _ _ _ H H2) as (?&?&?)
    end
  | H : Forall3 ?P ?l ?l' ?k |- _ =>
    lazymatch goal with
    | H1:l !! ?i = Some ?x, H2:l' !! ?i = Some ?y, H3:k !! ?i = Some ?z |- _ =>
      unless (P x y z) by done; let E := fresh in
      assert (P x y z) as E by (by apply (Forall3_lookup_lmr P l l' k i x y z));
      lazy beta in E
    | H1 : l !! _ = Some ?x |- _ =>
      destruct (Forall3_lookup_l P _ _ _ _ _ H H1) as (?&?&?&?&?)
    | H2 : l' !! _ = Some ?y |- _ =>
      destruct (Forall3_lookup_m P _ _ _ _ _ H H2) as (?&?&?&?&?)
    | H3 : k !! _ = Some ?z |- _ =>
      destruct (Forall3_lookup_r P _ _ _ _ _ H H3) as (?&?&?&?&?)
    end
  end.
Ltac list_simplifier :=
  simplify_eq/=;
  repeat match goal with
  | _ => progress decompose_Forall_hyps
  | _ => progress simplify_list_eq
  | H : _ <$> _ = _ :: _ |- _ =>
    apply fmap_cons_inv in H; destruct H as (?&?&?&?&?)
  | H : _ :: _ = _ <$> _ |- _ => symmetry in H
  | H : _ <$> _ = _ ++ _ |- _ =>
    apply fmap_app_inv in H; destruct H as (?&?&?&?&?)
  | H : _ ++ _ = _ <$> _ |- _ => symmetry in H
  | H : zip_with _ _ _ = _ :: _ |- _ =>
    apply zip_with_cons_inv in H; destruct H as (?&?&?&?&?&?&?&?)
  | H : _ :: _ = zip_with _ _ _ |- _ => symmetry in H
  | H : zip_with _ _ _ = _ ++ _ |- _ =>
    apply zip_with_app_inv in H; destruct H as (?&?&?&?&?&?&?&?&?)
  | H : _ ++ _ = zip_with _ _ _ |- _ => symmetry in H
  end.
Ltac decompose_Forall := repeat
  match goal with
  | |- Forall _ _ => by apply Forall_true
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor
  | |- Forall _ (_ ++ _) => apply Forall_app_2
  | |- Forall _ (_ <$> _) => apply Forall_fmap
  | |- Forall _ (_ ≫= _) => apply Forall_bind
  | |- Forall2 _ _ _ => apply Forall_Forall2_diag
  | |- Forall2 _ [] [] => constructor
  | |- Forall2 _ (_ :: _) (_ :: _) => constructor
  | |- Forall2 _ (_ ++ _) (_ ++ _) => first
    [ apply Forall2_app; [by decompose_Forall |]
    | apply Forall2_app; [| by decompose_Forall]]
  | |- Forall2 _ (_ <$> _) _ => apply Forall2_fmap_l
  | |- Forall2 _ _ (_ <$> _) => apply Forall2_fmap_r
  | _ => progress decompose_Forall_hyps
  | H : Forall _ (_ <$> _) |- _ => rewrite Forall_fmap in H
  | H : Forall _ (_ ≫= _) |- _ => rewrite Forall_bind in H
  | |- Forall _ _ =>
    apply Forall_lookup_2; intros ???; progress decompose_Forall_hyps
  | |- Forall2 _ _ _ =>
    apply Forall2_same_length_lookup_2; [solve_length|];
    intros ?????; progress decompose_Forall_hyps
  end.

(** The [simplify_suffix] tactic removes [suffix] hypotheses that are
tautologies, and simplifies [suffix] hypotheses involving [(::)] and
[(++)]. *)
Ltac simplify_suffix := repeat
  match goal with
  | H : suffix (_ :: _) _ |- _ => destruct (suffix_cons_not _ _ H)
  | H : suffix (_ :: _) [] |- _ => apply suffix_nil_inv in H
  | H : suffix (_ ++ _) (_ ++ _) |- _ => apply suffix_app_inv in H
  | H : suffix (_ :: _) (_ :: _) |- _ =>
    destruct (suffix_cons_inv _ _ _ _ H); clear H
  | H : suffix ?x ?x |- _ => clear H
  | H : suffix ?x (_ :: ?x) |- _ => clear H
  | H : suffix ?x (_ ++ ?x) |- _ => clear H
  | _ => progress simplify_eq/=
  end.

(** The [solve_suffix] tactic tries to solve goals involving [suffix]. It
uses [simplify_suffix] to simplify hypotheses and tries to solve [suffix]
conclusions. This tactic either fails or proves the goal. *)
Ltac solve_suffix := by intuition (repeat
  match goal with
  | _ => done
  | _ => progress simplify_suffix
  | |- suffix [] _ => apply suffix_nil
  | |- suffix _ _ => reflexivity
  | |- suffix _ (_ :: _) => apply suffix_cons_r
  | |- suffix _ (_ ++ _) => apply suffix_app_r
  | H : suffix _ _ → False |- _ => destruct H
  end).
