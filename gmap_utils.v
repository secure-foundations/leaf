From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

From stdpp Require Import gmap.
Require Import CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import fin_sets.
From stdpp Require Import list.

Lemma gset_easy_induct `{EqDecision A, Countable A} {B}
  (R : B -> Prop)
  (s: gset A)
  (fn : A -> B -> B)
  (u : B)
  (R_u : R u)
  (ind: ∀ a b , R b -> R (fn a b))
  : R (set_fold fn u s).
Proof.
  unfold set_fold. unfold "∘". induction (elements s).
  - unfold foldr. trivial.
  - unfold foldr. apply ind. apply IHl.
Qed.

Lemma gset_relate `{EqDecision A, Countable A} {B} {C}
  (R : B -> C -> Prop)
  (s: gset A)
  (fn1 : A -> B -> B)
  (fn2 : A -> C -> C)
  (u1 : B)
  (u2: C)
  (R_u1_u2 : R u1 u2)
  (pro: ∀ a b c , R b c -> R (fn1 a b) (fn2 a c))
  : R (set_fold fn1 u1 s) (set_fold fn2 u2 s).
Proof.
  unfold set_fold. unfold "∘". induction (elements s).
  - unfold foldr. trivial.
  - unfold foldr. apply pro. apply IHl.
Qed.

(*Lemma set_fold_rearrange `{EqDecision A, Countable A}
  (x: A)
  (Y: gset A)
  (u: A)
  (fn : A -> A -> A)
  (assoc : ∀ a b c , fn a (fn b c) = fn (fn a b) c)
  (is_unit : ∀ a , fn u a = a)
  : set_fold fn x Y = fn (set_fold fn u Y) x.
Proof.
  unfold set_fold. unfold "∘". induction (elements Y).
     - unfold foldr. symmetry. apply is_unit.
     - unfold foldr. rewrite <- assoc. f_equal.*)
  

Lemma minus_union_eq  `{EqDecision A, Countable A}
  (s1: gset A)
  (s2: gset A)
  (sub : s1 ⊆ s2)
  : (s2 ∖ s1) ∪ s1 = s2.
Proof. apply set_eq. split.
  - rewrite elem_of_union. rewrite elem_of_difference. intros. destruct H0.
    + destruct H0. trivial.
    + unfold "⊆" in sub. unfold set_subseteq_instance in sub. apply sub. trivial.
  - rewrite elem_of_union. rewrite elem_of_difference. intros. 
    destruct (decide (x ∈ s1)).
    + right. trivial.
    + left. split; trivial.
Qed.
 
(*Lemma gset_subset_assoc `{EqDecision A, Countable A}
  (s1: gset A)
  (s2: gset A)
  (fn : A -> A -> A)
  (u : A)
  (sub : s1 ⊆ s2)
  (assoc : ∀ a b c , fn a (fn b c) = fn (fn a b) c)
  (comm : ∀ a b , fn a b = fn b a)
  (is_unit : ∀ a , fn a u = a)
  : exists k , set_fold fn u s2 = fn (set_fold fn u s1) k.
Proof.
  exists (set_fold fn u (s2 ∖ s1)). (* not normal backslash *)
  rewrite <- set_fold_rearrange.
    - replace (set_fold fn u s2) with (set_fold fn u 
        ((s2 ∖ s1) ∪ s1)).
        + apply set_fold_disj_union.
          * unfold Comm. apply comm.
          * unfold Assoc. apply assoc.
          * apply disjoint_difference_l1. unfold "⊆". unfold set_subseteq_instance. intros. trivial.
        + rewrite minus_union_eq; trivial.
   - apply assoc.
   - apply is_unit.
Qed.*)

(*Lemma gset_subset_relate `{EqDecision A, Countable A} {B} {C}
  (R : B -> C -> Prop)
  (s1: gset A)
  (s2: gset A)
  (fn1 : A -> B -> B)
  (fn2 : A -> C -> C)
  (u1 : B)
  (u2: C)
  (R_u1_u1 : R u1 u2)
  (sub: s1 ⊆ s2)
  (pro: ∀ a b c , R b c -> R (fn1 a b) (fn2 a c))
  (pro_single: ∀ a b c , R b c -> R b (fn2 a c))
  : R (set_fold fn1 u1 s1) (set_fold fn2 u2 s2).
Proof.
  replace (set_fold fn2 u2 s2) with (set_fold fn2 u2 ((s2 ∖ s1) ∪ s1)).
  - replace (set_fold fn2 u2 (s2 ∖ s1 ∪ s1)) with 
              (set_fold fn2 (set_fold fn2 u2 (s2 ∖ s1) ) s1).
              Focus 2.
              symmetry. apply set_fold_disj_union.
Qed.*)

(*Lemma gset_subset_relate `{EqDecision A, Countable A} {B} {C}
  (R : B -> C -> Prop)
  (s1: gset A)
  (s2: gset A)
  (fn1 : A -> B -> B)
  (fn2 : A -> C -> C)
  (u1 : B)
  (u2: C)
  (R_u1_u1 : R u1 u2)
  (sub: s1 ⊆ s2)
  (pro: ∀ a b c , R b c -> R (fn1 a b) (fn2 a c))
  (pro_single: ∀ a b c , R b c -> R b (fn2 a c))
  : R (set_fold fn1 u1 s1) (set_fold fn2 u2 s2).
Proof.
  generalize sub. clear sub. generalize s2. clear s2.
  have h := (P := λ foldRes X , s1 ⊆ X -> R (set_fold fn1 u1 s1) foldRes).
Qed.
*)

(*Print elements_disj_union.
Lemma set_fold_disj_union `{EqDecision A, Countable A} {B}
    (f : A → B → B) (b : B) (X Y : gset A) : 
  (*Comm (=) f →
  Assoc (=) f →*)
  X ## Y →
  set_fold f b (X ∪ Y) = set_fold f (set_fold f b X) Y.                                              
Proof.
  intros Hdisj. unfold set_fold; simpl.
  apply foldr_permutation.
  rewrite elements_disj_union.
  by rewrite elements_disj_union. <- foldr_app, (comm (++)).
Qed.
*)

Lemma gset_subset_relate `{EqDecision A, Countable A} {B} {C}
  (R : B -> C -> Prop)
  (s1: gset A)
  (s2: gset A)
  (fn1 : A -> B -> B)
  (fn2 : A -> C -> C)
  (u1 : B)
  (u2: C)
  (R_u1_u2 : R u1 u2)
  (sub: s1 ⊆ s2)
  (pro: ∀ a b c , R b c -> R (fn1 a b) (fn2 a c))
  (pro_single: ∀ a b c , R b c -> R b (fn2 a c))
  (comm: ∀ (a1 a2 : A) (c : C), fn2 a1 (fn2 a2 c) = fn2 a2 (fn2 a1 c))
  : R (set_fold fn1 u1 s1) (set_fold fn2 u2 s2).
Proof.
  (*generalize sub. clear sub. generalize s2. clear s2.
  have h := (P := λ foldRes X , s1 ⊆ X -> R (set_fold fn1 u1 s1) foldRes).*)
  have t := foldr_permutation_proper (=) fn2 u2 comm (elements s2)
      (elements (s2 ∖ s1) ++ elements s1).
  unfold set_fold. simpl. rewrite t.
    - induction (elements (s2 ∖ s1)).
      + simpl.
        have l := gset_relate R s1 fn1 fn2 u1 u2 R_u1_u2 pro. unfold set_fold in l. simpl in l.  apply l. apply EqDecision0.
      + simpl. apply pro_single. trivial.
    - have k := minus_union_eq s1 s2 sub.
      replace (elements s2) with (elements (s2 ∖ s1 ∪ s1)).
        * apply elements_disj_union. unfold "##". unfold set_disjoint_instance.
          intro. rewrite elem_of_difference. intros. destruct H0. contradiction.
        * rewrite k. trivial.
Qed.

Lemma gset_nat_upper_bound (s: gset nat)
    : ∃ n , ∀ m , m ∈ s -> m < n.
Proof.
  generalize s.
  apply set_ind with (P := λ t : (gset nat), ∃ n , ∀ m , m ∈ t -> m < n).
  - unfold Proper, equiv, "==>", iff.  unfold set_equiv_instance. intros. split; intros; destruct H0.
    + exists x0. intros. apply H0. unfold set_equiv_instance in H. rewrite H. trivial.
    + exists x0. intros. apply H0. unfold set_equiv_instance in H. rewrite <- H. trivial.
  - exists 0. intro. rewrite elem_of_empty. contradiction.
  - intros. destruct H0. exists (max x0 (x + 1)). intro. rewrite elem_of_union.
        rewrite elem_of_singleton.
      intros. destruct H1.
        + lia.
        + have ineq := H0 m H1. lia.
Qed.

Lemma set_fold_equiv_funcs `{EqDecision A, Countable A} {B} (f g : A -> B -> B) (u: B) (s: gset A)
  (equiv: ∀ x y , f x y = g x y) : (set_fold f u s) = (set_fold g u s).
Proof. apply (gset_relate (=)).
  - trivial.
  - intros. rewrite H0. apply equiv.
Qed.

Inductive multiset (A: Type) `{EqDecision A, Countable A} :=
  | MS : gmap A nat -> multiset A.

Definition multiset_add_merge (a b: option nat) : option nat :=
  match (a, b) with
    | (Some n, Some m) => Some (n + m + 1)
    | (None, t) => t
    | (t, None) => t
  end.

Definition multiset_add `{EqDecision A, Countable A} (x y: multiset A) : multiset A :=
  match (x, y) with
    | (MS _ x0, MS _ y0) => 
      MS A (merge multiset_add_merge x0 y0)
  end.

Definition multiset_le `{EqDecision A, Countable A} (x0 y0: multiset A) : Prop :=
  match (x0, y0) with
    | (MS _ x, MS _ y) => 
      ∀ k n , x !! k = Some n -> match y !! k with | None => False | Some m => n <= m end
  end.
  
Instance multiset_lifetime `{EqDecision A, Countable A} : EqDecision (multiset A). Admitted.

Instance multiset_le_dec `{EqDecision A, Countable A} (x y : multiset A) : Decision (multiset_le x y). Admitted.

Lemma multiset_le_transitive `{EqDecision A, Countable A} (x y z: multiset A)
  (le1 : multiset_le x y) (le2 : multiset_le y z) : multiset_le x z. Admitted.
  
Lemma multiset_add_comm `{EqDecision A, Countable A} (x y: multiset A) :
  multiset_add x y = multiset_add y x. Admitted.
  
Lemma multiset_add_assoc `{EqDecision A, Countable A} (x y z: multiset A) :
  multiset_add x (multiset_add y z) = multiset_add (multiset_add x y) z. Admitted.

Definition multiset_no_dupes `{EqDecision A, Countable A} (x : multiset A) :=
  match x with
    | (MS _ x) => map_fold (λ k a b , a = 0 /\ b) True x
  end.
