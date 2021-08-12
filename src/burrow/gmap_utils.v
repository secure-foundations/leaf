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

Lemma set_fold_add_1_element `{FinSet A T} {B}
  (s: T)
  (fn: A -> B -> B)
  (x: A)
  (x_not_in_s: x ∉ s)
  (u: B)
  (fn_assoc: ∀ a1 a2 b , fn a1 (fn a2 b) = fn a2 (fn a1 b))
  : set_fold fn u (s ∪ {[x]}) = fn x (set_fold fn u s).
Proof.
  unfold set_fold, "∘".
  enough (fn x (foldr fn u (elements s)) = (foldr fn u (x :: elements s))).
  - rewrite H7.
    apply foldr_permutation.
    + typeclasses eauto.
    + intro. unfold Proper, "==>". intros. subst. trivial.
    + intros. apply fn_assoc.
    + setoid_replace (s ∪ {[x]}) with ({[x]} ∪ s).
      * apply elements_union_singleton. trivial.
      * set_solver.
  - unfold foldr. trivial.
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

Lemma set_relate3 `{Elements A T} {B} {C} {D}
  (R : B -> C -> D -> Prop)
  (s: T)
  (fn1 : A -> B -> B)
  (fn2 : A -> C -> C)
  (fn3 : A -> D -> D)
  (u1 : B)
  (u2 : C)
  (u3 : D)
  (R_u1_u2_u3 : R u1 u2 u3)
  (pro: ∀ a b c d , R b c d -> R (fn1 a b) (fn2 a c) (fn3 a d))
  : R (set_fold fn1 u1 s) (set_fold fn2 u2 s) (set_fold fn3 u3 s).
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
  Comm (=) f →
  Assoc (=) f →
  X ## Y →
  set_fold f b (X ∪ Y) = set_fold f (set_fold f b X) Y.                                              
Proof.
  intros Hdisj. unfold set_fold; simpl.
  apply foldr_permutation.
  rewrite elements_disj_union.
  by rewrite elements_disj_union. <- foldr_app, (comm (++)).
Qed.*)

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

Lemma set_subset_relate_general `{FinSet A T} {B} {C}
  (R : B -> C -> Prop)
  (Rel : C -> C -> Prop)
  (po: PreOrder Rel)
  (s1: T)
  (s2: T)
  (fn1 : A -> B -> B)
  (fn2 : A -> C -> C)
  (proper: (∀ x : A, Proper (Rel ==> Rel) (fn2 x)))
  (proper2: (∀ b : B, Proper (Rel ==> flip impl) (R b)))
  (u1 : B)
  (u2: C)
  (R_u1_u2 : R u1 u2)
  (sub: s1 ⊆ s2)
  (pro: ∀ a b c , R b c -> R (fn1 a b) (fn2 a c))
  (pro_single: ∀ a b c , R b c -> R b (fn2 a c))
  (comm: ∀ (a1 a2 : A) (c : C), Rel (fn2 a1 (fn2 a2 c)) (fn2 a2 (fn2 a1 c)))
  : R (set_fold fn1 u1 s1) (set_fold fn2 u2 s2).
Proof.
  (*generalize sub. clear sub. generalize s2. clear s2.
  have h := (P := λ foldRes X , s1 ⊆ X -> R (set_fold fn1 u1 s1) foldRes).*)
  have t0 := foldr_permutation_proper (Rel) fn2 u2 comm (elements s2)
      (elements (s2 ∖ s1) ++ elements s1).
  have t := t0 po proper.
  unfold set_fold. simpl. setoid_rewrite t.
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

Lemma rewrite_map_as_insertion `{Countable K} {V} (y: gmap K V) i c
  (y_i : y !! i = Some c) : ∃ y', y = <[i:=c]> y' /\ y' !! i = None.
Proof.
  exists (delete i y). split.
  - rewrite insert_delete; trivial.
  - apply lookup_delete.
Qed.

Lemma merge_assign `{!EqDecision K, !Countable K} {V}
    (z:V) op (i:K) (x y:V) (m m' : gmap K V)
    (xyz : Some z = op (Some x) (Some y))
  : merge op (<[i:=x]> m) (<[i:=y]> m') = <[i:=z]> (merge op m m').
Proof.
  apply map_eq. intro. rewrite lookup_merge. unfold diag_None.
  have heq : Decision (i = i0) by solve_decision. destruct heq.
  - rewrite e. rewrite lookup_insert. rewrite lookup_insert. rewrite lookup_insert.
      rewrite xyz. trivial.
  - repeat (rewrite lookup_insert_ne; trivial). rewrite lookup_merge.
    unfold diag_None. trivial.
Qed.

Lemma merge_assign2 `{!EqDecision K, !Countable K} {V}
    op (i:K) (x:V) (m m' : gmap K V)
    (xyz : op (Some x) None = Some x)
    (i_not_in_m : m' !! i = None)
  : merge op (<[i:=x]> m) m' = <[i:=x]> (merge op m m').
Proof.
  apply map_eq. intro. rewrite lookup_merge. unfold diag_None.
  have heq : Decision (i = i0) by solve_decision. destruct heq.
  - rewrite e. rewrite lookup_insert. rewrite lookup_insert.
    rewrite e in i_not_in_m. rewrite i_not_in_m. trivial.
  - repeat (rewrite lookup_insert_ne; trivial). rewrite lookup_merge.
      unfold diag_None. trivial.
Qed.


Lemma map_fold_merge `{EqDecision K, Countable K} `{!Equiv B} {V}
    {tr: Transitive Equiv0}
    {rf: Reflexive Equiv0}
    {sy: Symmetric Equiv0}
  (big_op: B -> B -> B)
  (small_op: option V -> option V -> option V)
  (u: B)
  (a: gmap K V)
  (b: gmap K V)
  (u_is_unit: ∀ t, big_op u t ≡ t)
  (small_op_none_some: ∀ v, small_op None (Some v) = Some v)
  (small_op_some_none: ∀ v, small_op (Some v) None = Some v)
  (small_op_some_some: ∀ v w, ∃ z , small_op (Some v) (Some w) = Some z)
  (fn: K -> V -> B -> B)
  (fn_proper: ∀ k v , Proper ((≡) ==> (≡)) (fn k v))
  (big_op_proper: Proper ((≡) ==> (≡) ==> (≡)) big_op)
  (fn_assoc: ∀ k1 v1 k2 v2 y ,
      fn k1 v1 (fn k2 v2 y) ≡ fn k2 v2 (fn k1 v1 y))
  (big_op_fn: ∀ i x y z t s ,
      small_op (Some x) (Some y) = Some z ->
      big_op (fn i x t) (fn i y s) ≡ fn i z (big_op t s))
  (big_op_fn1: ∀ i x t s ,
      big_op (fn i x t) s ≡ fn i x (big_op t s))
  : big_op (map_fold fn u a) (map_fold fn u b) ≡ map_fold fn u (merge small_op a b).
Proof.
  generalize b. clear b.
  apply map_ind with (P := λ ak , ∀ b,
      big_op (map_fold fn u ak) (map_fold fn u b) ≡ map_fold fn u (merge small_op ak b)).
  - intro. rewrite map_fold_empty.
    setoid_rewrite u_is_unit.
    assert (merge small_op ∅ b = b).
    + apply map_eq. intros. rewrite lookup_merge. rewrite lookup_empty.
        unfold diag_None. destruct (b !! i). * apply small_op_none_some.
        * trivial.
    + rewrite H0. trivial.
  - intros.
    assert (∀ x m, m!!i = None -> map_fold fn u (<[i:=x]> m) ≡ fn i x (map_fold fn u m)) as equiv1.
    + intros. apply map_fold_insert with (R := (≡)).
      * apply Build_PreOrder; typeclasses eauto.
      * typeclasses eauto.
      * intros. apply fn_assoc.
      * trivial.
    + setoid_rewrite equiv1; trivial.
      destruct (b !! i) eqn:b_i.
      * assert (exists b' , b' !! i = None /\ <[i:=v]>b' = b).
        -- exists (delete i b). split. ++ apply lookup_delete. ++ rewrite insert_delete; trivial.
        -- deex. destruct_ands. subst b.
            intros. setoid_rewrite equiv1; trivial.
            have ss := small_op_some_some x v. deex.
            rewrite (merge_assign z).
            ++ setoid_rewrite equiv1; trivial.
              ** setoid_rewrite <- H1. apply big_op_fn. trivial.
              ** rewrite lookup_merge. rewrite H0. rewrite H2. unfold diag_None. trivial.
            ++ symmetry. trivial.
      * rewrite merge_assign2.
        -- setoid_rewrite equiv1; trivial.
         ++ rewrite <- H1. apply big_op_fn1.
         ++ rewrite lookup_merge. rewrite H0. rewrite b_i. unfold diag_None. trivial.
        -- apply small_op_some_none.
        -- trivial.
Qed.
  
 (* unfold map_fold. unfold curry. unfold Datatypes.uncurry. unfold "∘". *)

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
    | (MS _ x) => ∀ i , match x !! i with Some 0 => True | None => True | _ => False end
  end.

Lemma empty_add_empty_eq_empty `{EqDecision A, Countable A}
    : multiset_add empty_multiset empty_multiset = empty_multiset (A:=A).
Proof.
  unfold empty_multiset, multiset_add. f_equal. apply map_eq. intro.
    rewrite lookup_merge. rewrite lookup_empty. unfold diag_None. trivial. Qed.

Definition multiset_in `{EqDecision A, Countable A} (x : multiset A) y :=
  match x with
    | (MS _ x) => x !! y ≠ None
  end.
  
Lemma multiset_add_empty (a : multiset nat) :
  multiset_add a empty_multiset = a.
Proof. unfold empty_multiset, multiset_add. destruct a. f_equal. apply map_eq. intro.
    rewrite lookup_merge. rewrite lookup_empty. unfold diag_None. destruct (g !! i); trivial.
Qed.
  
Lemma multiset_add_empty_left (a : multiset nat) :
  multiset_add empty_multiset a = a.
Proof. unfold empty_multiset, multiset_add. destruct a. f_equal. apply map_eq. intro.
    rewrite lookup_merge. rewrite lookup_empty. unfold diag_None. destruct (g !! i); trivial.
Qed.

Lemma multiset_le_add `{EqDecision A, Countable A} (a b: multiset A) : multiset_le a (multiset_add a b).
Proof. unfold multiset_le. destruct a, b. unfold multiset_add. intro.
  rewrite lookup_merge. unfold diag_None. unfold multiset_add_merge.
    destruct (g !! k); destruct (g0 !! k); lia.
Qed.

Lemma multiset_le_add_right `{EqDecision A, Countable A} (a b: multiset A) : multiset_le a (multiset_add b a).
Proof. unfold multiset_le. destruct a, b. unfold multiset_add. intro.
  rewrite lookup_merge. unfold diag_None. unfold multiset_add_merge.
    destruct (g !! k); destruct (g0 !! k); lia.
Qed.

Lemma multiset_add_chain_included (a b c d : multiset nat) :
  multiset_le a (multiset_add (multiset_add (multiset_add a b) c) d).
Proof. unfold multiset_le. destruct a, b, c, d. unfold multiset_add. intro.
  repeat (rewrite lookup_merge). unfold diag_None. unfold multiset_add_merge.
    destruct (g !! k); destruct (g0 !! k); destruct (g1 !! k); destruct (g2 !! k); lia.
Qed.

Lemma multiset_le_refl `{EqDecision A, Countable A} (x: multiset A)
  : multiset_le x x.
Proof. unfold multiset_le. destruct x. intro. destruct (g !! k); lia. Qed.

Definition lt_singleton (n: nat) : multiset nat := MS nat {[ n := 0 ]}.

Lemma multiset_in_lt_singleton x : multiset_in (lt_singleton x) x.
Proof. unfold multiset_in, lt_singleton. rewrite lookup_singleton. crush. Qed.

Definition max_ltunit_in_lt (lt: multiset nat) : nat :=
  match lt with
  | MS _ y => map_fold (λ k v b , max k b) 0 y
  end.
  
Lemma max_ltunit_in_lt_ge (lt: multiset nat) k :
  multiset_in lt k -> k ≤ max_ltunit_in_lt lt.
Proof. intro. unfold max_ltunit_in_lt.
  destruct lt.
  unfold multiset_in in H. destruct (g !! k) eqn:t.
  - apply gmap_induct_with_elem with (key := k) (val := n); trivial.
    + intros. lia.
    + intros. lia.
  - contradiction.
Qed.

Lemma multiset_no_dupes_of_add_larger_elem lt y
  (mnd : multiset_no_dupes lt)
  (larger: y > max_ltunit_in_lt lt)
  : multiset_no_dupes (multiset_add (lt_singleton y) lt).
Proof.
  unfold lt_singleton, multiset_no_dupes, multiset_add. destruct lt. intro.
  rewrite lookup_merge. unfold diag_None.
  have h : Decision (y = i) by solve_decision. destruct h.
  - subst y. rewrite lookup_singleton. unfold multiset_add_merge.
    destruct (g !! i) eqn:ab; trivial.
    assert (i ≤ max_ltunit_in_lt (MS nat g)).
    + apply max_ltunit_in_lt_ge. unfold multiset_in. crush.
    + lia.
  - rewrite lookup_singleton_ne; trivial. unfold multiset_add_merge.
    unfold multiset_no_dupes in mnd.
    have t := mnd i.
    destruct (g !! i); trivial.
Qed.
    
Lemma multiset_no_dupes_empty {A} `{Countable A} : multiset_no_dupes
    (empty_multiset : multiset A).
Proof. unfold multiset_no_dupes, empty_multiset. intro. rewrite lookup_empty. trivial. Qed.

Lemma multiset_no_dupes_of_multiset_no_dupes_add (a b: multiset nat)
  (mnd : multiset_no_dupes (multiset_add a b))
  : multiset_no_dupes b.
Proof. unfold multiset_no_dupes, multiset_add in *. destruct a, b. intro.
  have h := mnd i. rewrite lookup_merge in h. unfold diag_None, multiset_add_merge in h.
    destruct (g !! i), (g0 !! i); trivial. destruct n0; trivial.
    replace (n + S n0 + 1) with (S (n + n0 + 1)) in h by lia.
    contradiction.
Qed.

Lemma not_le_of_nonempty (lt a b: multiset nat)
  (lt_nonempty : lt ≠ empty_multiset)
  (mnd : multiset_no_dupes (multiset_add lt (multiset_add a b)))
       : ¬ multiset_le lt b.
Proof. intro. apply lt_nonempty.
  unfold multiset_le, multiset_no_dupes, multiset_add, empty_multiset in *.
  destruct lt, a, b.
  apply f_equal. apply map_eq. intro. rewrite lookup_empty.
  have t := H i. have s := mnd i. clear H. clear mnd.
  rewrite lookup_merge in s. unfold diag_None, multiset_add_merge in s.
  rewrite lookup_merge in s. unfold diag_None in *.
  destruct (g !! i), (g0 !! i), (g1 !! i); trivial.
  - replace (n + (n0 + n1 + 1) + 1) with (S (n + n0 + n1 + 1)) in s by lia.
    contradiction.
  - replace (n + n0 + 1) with (S (n + n0)) in s by lia. contradiction.
  - replace (n + n0 + 1) with (S (n + n0)) in s by lia. contradiction.
  - contradiction.
Qed.
