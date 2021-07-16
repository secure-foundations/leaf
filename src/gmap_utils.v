From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

From stdpp Require Import gmap.
Require Import Burrow.CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import fin_sets.
From stdpp Require Import list.
Require Import coq_tricks.Deex.

Lemma set_easy_induct `{Elements A T} {B}
  (R : B -> Prop)
  (s: T)
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

Lemma set_relate `{Elements A T} {B} {C}
  (R : B -> C -> Prop)
  (s: T)
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
     
(* this was a local instance in stdpp for some reason *)
Global Instance elem_of_dec `{FinSet A T} : RelDecision (∈@{T}) | 100.
Proof.
  refine (λ x X, cast_if (decide_rel (∈) x (elements X)));
    by rewrite <-(elem_of_elements _). 
Defined.
  
Lemma minus_union_eq  `{FinSet A T}
  (s1: T)
  (s2: T)
  (sub : s1 ⊆ s2)
  : (s2 ∖ s1) ∪ s1 ≡ s2.
Proof. unfold "≡". split.
  - rewrite elem_of_union. rewrite elem_of_difference. intros. destruct H7.
    + destruct_ands. trivial.
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

Lemma set_subset_relate `{FinSet A T} {B} {C}
  (R : B -> C -> Prop)
  (s1: T)
  (s2: T)
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
        have l := set_relate R s1 fn1 fn2 u1 u2 R_u1_u2 pro. unfold set_fold in l. simpl in l.  apply l.
      + simpl. apply pro_single. trivial.
    - assert (s2 ≡ (s2 ∖ s1) ∪ s1) by (rewrite minus_union_eq; trivial).
      assert (elements s2 ≡ₚ elements ((s2 ∖ s1) ∪ s1)) by 
        (setoid_rewrite <- H7; trivial).
      rewrite H8.
      apply elements_disj_union. unfold "##". unfold set_disjoint_instance.
          intro. rewrite elem_of_difference. intros. destruct_ands. contradiction.
Qed.

Lemma set_nat_upper_bound `{FinSet nat T} (s: T)
    : ∃ n , ∀ m , m ∈ s -> m < n.
Proof.
  generalize s.
  apply set_ind with (P := λ t : T, ∃ n , ∀ m , m ∈ t -> m < n).
  - unfold Proper, equiv, "==>", iff.  unfold set_equiv_instance. intros. split; intros; destruct H8.
    + exists x0. intros. apply H8. unfold set_equiv_instance in H7. rewrite H7. trivial.
    + exists x0. intros. apply H8. unfold set_equiv_instance in H7. rewrite <- H7. trivial.
  - exists 0. intro. rewrite elem_of_empty. contradiction.
  - intros. destruct H8. exists (max x0 (x + 1)). intro. rewrite elem_of_union.
        rewrite elem_of_singleton.
      intros. destruct H9.
        + lia.
        + have ineq := H8 m H9. lia.
Qed.

Lemma set_fold_equiv_funcs `{FinSet A T} {B} (f g : A -> B -> B) (u: B) (s: T)
  (equiv: ∀ x y , f x y = g x y) : (set_fold f u s) = (set_fold g u s).
Proof. apply (set_relate (=)).
  - trivial.
  - intros. rewrite H7. apply equiv.
Qed.

Inductive multiset (A: Type) `{EqDecision A, Countable A} :=
  | MS : gmap A nat -> multiset A.

Definition empty_multiset {A} `{EqDecision A, Countable A} : multiset A := MS A ∅.

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
  
(*Definition multiset_le_fold_fn `{EqDecision A, Countable A} (k: A) (a : nat) (b : Prop) :=
  match y !! k with | Some a' => a <= a' /\ b | None => False end*)

Definition multiset_le `{EqDecision A, Countable A} (x y: multiset A) : Prop :=
  match (x, y) with
    | (MS _ x, MS _ y) =>
      forall k , match x !! k, y !! k with
        | None, None => True
        | Some a, None => False
        | None, Some b => True
        | Some a, Some b => a <= b
      end
  end.

Definition multiset_le_as_fold `{EqDecision A, Countable A} (x y: multiset A) : Prop :=
  match (x, y) with
    | (MS _ x, MS _ y) =>
      map_fold (λ k a b , match y !! k with | Some a' => a <= a' /\ b | None => False end)
        True x
  end.
  
Lemma gmap_easy_induct `{EqDecision K, Countable K} {A B}
  (R : B -> Prop)
  (s: gmap K A)
  (fn : K -> A -> B -> B)
  (u : B)
  (R_u : R u)
  (ind: ∀ k a b , s !! k = Some a -> R b -> R (fn k a b))
  : R (map_fold fn u s).
Proof.
  unfold map_fold, "∘".
  assert (∀ i x , (i,x) ∈ map_to_list s -> s !! i = Some x).
   - intros. rewrite <- elem_of_map_to_list. trivial.
   - generalize H0. clear H0. generalize (map_to_list s). induction l.
    + intro. unfold foldr. trivial.
    + intro. cbn [foldr]. unfold curry. unfold Datatypes.uncurry. destruct a. apply ind.
      * apply H0. unfold "∈". apply elem_of_list_here.
      * unfold curry in IHl. unfold Datatypes.uncurry in IHl. apply IHl.
          intros. apply H0. apply elem_of_list_further. trivial.
Qed.

Lemma gmap_induct_with_elem `{EqDecision K, Countable K} {A B}
  (R : B -> Prop)
  (s: gmap K A)
  (fn : K -> A -> B -> B)
  (u : B)
  (key: K) (val: A)
  (key_in_s : s !! key = Some val)
  (R_key : ∀ b , R (fn key val b))
  (ind: ∀ k a b , R b -> R (fn k a b))
  : R (map_fold fn u s).
Proof.
  unfold map_fold, "∘".
  assert ((key, val) ∈ map_to_list s).
   - rewrite elem_of_map_to_list. trivial.
   - generalize H0. generalize (map_to_list s). induction l.
      + intros. inversion H1.
      + intro. destruct a. inversion H1.
        * cbn [foldr]. unfold curry. unfold Datatypes.uncurry. rewrite <- H4. rewrite <- H5. apply R_key.
        * cbn [foldr]. unfold curry in *. unfold Datatypes.uncurry in *.
            apply ind. apply IHl. trivial.
Qed.

Lemma multiset_le_defn_eq `{EqDecision A, Countable A} (x y: multiset A)
  : multiset_le x y <-> multiset_le_as_fold x y.
Proof. split.
 - unfold multiset_le, multiset_le_as_fold. intro. destruct x, y.
    apply gmap_easy_induct with (R := λ x, x); trivial.
      intros. have t := H0 k. rewrite H1 in t. destruct (g0 !! k).
       + split; trivial.
       + trivial.
 - unfold multiset_le, multiset_le_as_fold. intro. destruct x, y.
   + intro. assert (exists lk , lk = g !! k). * exists (g !! k). trivial.
   * destruct H1. rewrite <- H1. destruct x.
     -- enough ((match g0 !! k with | Some b => n > b | None => True end) -> False).
      ** destruct (g0 !! k). *** lia. *** apply H2. trivial.
      ** intro. generalize H0. clear H0. apply gmap_induct_with_elem with (key := k) (val := n).
        *** rewrite <- H1. trivial.
        *** intros. destruct (g0 !! k). **** lia. **** trivial.
        *** intros. destruct (g0 !! k0); crush.
     -- destruct (g0 !! k); trivial.
Qed.
  
Instance eqdec_multiset `{EqDecision A, Countable A} : EqDecision (multiset A). 
  solve_decision. Defined.

Instance multiset_le_as_fold_dec `{EqDecision A, Countable A} (x y : multiset A) : Decision (multiset_le_as_fold x y).
  unfold multiset_le_as_fold.
  destruct x, y.
  unfold map_fold. unfold "∘". generalize (map_to_list g).
  induction l.
  * unfold foldr. solve_decision.
  * unfold foldr. unfold curry. unfold Datatypes.uncurry. destruct a.
      destruct (g0 !! a); solve_decision.
Defined.

Instance multiset_le_dec `{EqDecision A, Countable A} (x y : multiset A) : Decision (multiset_le x y).
  unfold Decision.
  have h := @multiset_le_as_fold_dec A EqDecision0 EqDecision1 H x y.
  unfold Decision in *. destruct h.
  * left. rewrite multiset_le_defn_eq. trivial.
  * right. rewrite multiset_le_defn_eq. trivial.
Qed.

Lemma multiset_le_transitive `{EqDecision A, Countable A} (x y z: multiset A)
  (le1 : multiset_le x y) (le2 : multiset_le y z) : multiset_le x z.
Proof.
  unfold multiset_le in *. destruct x; destruct y. destruct z. intro.
    have j1 := le1 k. clear le1.
    have j2 := le2 k. clear le2.
    destruct (g !! k); destruct (g0 !! k); destruct (g1 !! k); lia.
Qed.

(*Instance inst_diagnone_multiset_add_merge : DiagNone multiset_add_merge. unfold DiagNone, multiset_add_merge. trivial. Defined.*)
    
Lemma multiset_add_comm `{EqDecision A, Countable A} (x y: multiset A) :
  multiset_add x y = multiset_add y x.
Proof.
  unfold multiset_add in *. destruct x; destruct y. f_equal.
    apply map_eq. intro.
    rewrite lookup_merge. rewrite lookup_merge.
    unfold multiset_add_merge, diag_None. destruct (g !! i), (g0 !! i); trivial. f_equal. lia.
Qed.
  
Lemma multiset_add_assoc `{EqDecision A, Countable A} (x y z: multiset A) :
  multiset_add x (multiset_add y z) = multiset_add (multiset_add x y) z.
Proof.
  unfold multiset_add in *. destruct x; destruct y; destruct z. f_equal.
    apply map_eq. intro.
    repeat (rewrite lookup_merge).
    unfold multiset_add_merge, diag_None. destruct (g !! i), (g0 !! i), (g1 !! i); trivial. f_equal. lia.
Qed.

Definition multiset_no_dupes `{EqDecision A, Countable A} (x : multiset A) :=
  match x with
    | (MS _ x) => map_fold (λ k a b , a = 0 /\ b) True x
  end.

Lemma empty_add_empty_eq_empty `{EqDecision A, Countable A}
    : multiset_add empty_multiset empty_multiset = empty_multiset (A:=A). Admitted.

Definition multiset_in `{EqDecision A, Countable A} (x : multiset A) y :=
  match x with
    | (MS _ x) => x !! y ≠ None
  end.
