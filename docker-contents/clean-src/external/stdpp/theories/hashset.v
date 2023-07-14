(** This file implements finite set using hash maps. Hash sets are represented
using radix-2 search trees. Each hash bucket is thus indexed using an binary
integer of type [Z], and contains an unordered list without duplicates. *)
From stdpp Require Export fin_maps listset.
From stdpp Require Import zmap.
From stdpp Require Import options.

Record hashset {A} (hash : A → Z) := Hashset {
  hashset_car : Zmap (list A);
  hashset_prf :
    map_Forall (λ n l, Forall (λ x, hash x = n) l ∧ NoDup l) hashset_car
}.
Global Arguments Hashset {_ _} _ _ : assert.
Global Arguments hashset_car {_ _} _ : assert.

Section hashset.
Context `{EqDecision A} (hash : A → Z).

Global Instance hashset_elem_of: ElemOf A (hashset hash) := λ x m, ∃ l,
  hashset_car m !! hash x = Some l ∧ x ∈ l.

Global Program Instance hashset_empty: Empty (hashset hash) := Hashset ∅ _.
Next Obligation. by intros n X; simpl_map. Qed.
Global Program Instance hashset_singleton: Singleton A (hashset hash) := λ x,
  Hashset {[ hash x := [x] ]} _.
Next Obligation.
  intros x n l [<- <-]%lookup_singleton_Some.
  rewrite Forall_singleton; auto using NoDup_singleton.
Qed.
Global Program Instance hashset_union: Union (hashset hash) := λ m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  Hashset (union_with (λ l k, Some (list_union l k)) m1 m2) _.
Next Obligation.
  intros _ _ m1 Hm1 m2 Hm2 n l'; rewrite lookup_union_with_Some.
  intros [[??]|[[??]|(l&k&?&?&?)]]; simplify_eq/=; auto.
  split; [apply Forall_list_union|apply NoDup_list_union];
    first [by eapply Hm1; eauto | by eapply Hm2; eauto].
Qed.
Global Program Instance hashset_intersection: Intersection (hashset hash) := λ m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  Hashset (intersection_with (λ l k,
    let l' := list_intersection l k in guard (l' ≠ []); Some l') m1 m2) _.
Next Obligation.
  intros _ _ m1 Hm1 m2 Hm2 n l'. rewrite lookup_intersection_with_Some.
  intros (?&?&?&?&?); simplify_option_eq.
  split; [apply Forall_list_intersection|apply NoDup_list_intersection];
    first [by eapply Hm1; eauto | by eapply Hm2; eauto].
Qed.
Global Program Instance hashset_difference: Difference (hashset hash) := λ m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  Hashset (difference_with (λ l k,
    let l' := list_difference l k in guard (l' ≠ []); Some l') m1 m2) _.
Next Obligation.
  intros _ _ m1 Hm1 m2 Hm2 n l'. rewrite lookup_difference_with_Some.
  intros [[??]|(?&?&?&?&?)]; simplify_option_eq; auto.
  split; [apply Forall_list_difference|apply NoDup_list_difference];
    first [by eapply Hm1; eauto | by eapply Hm2; eauto].
Qed.
Global Instance hashset_elements: Elements A (hashset hash) := λ m,
  map_to_list (hashset_car m) ≫= snd.

Global Instance hashset_fin_set : FinSet A (hashset hash).
Proof.
  split; [split; [split| |]| |].
  - intros ? (?&?&?); simplify_map_eq/=.
  - unfold elem_of, hashset_elem_of, singleton, hashset_singleton; simpl.
    intros x y. setoid_rewrite lookup_singleton_Some. split.
    { by intros (?&[? <-]&?); decompose_elem_of_list. }
    intros ->; eexists [y]. by rewrite elem_of_list_singleton.
  - unfold elem_of, hashset_elem_of, union, hashset_union.
    intros [m1 Hm1] [m2 Hm2] x; simpl; setoid_rewrite lookup_union_with_Some.
    split.
    { intros (?&[[]|[[]|(l&k&?&?&?)]]&Hx); simplify_eq/=; eauto.
      rewrite elem_of_list_union in Hx; destruct Hx; eauto. }
    intros [(l&?&?)|(k&?&?)].
    + destruct (m2 !! hash x) as [k|]; eauto.
      exists (list_union l k). rewrite elem_of_list_union. naive_solver.
    + destruct (m1 !! hash x) as [l|]; eauto 6.
      exists (list_union l k). rewrite elem_of_list_union. naive_solver.
  - unfold elem_of, hashset_elem_of, intersection, hashset_intersection.
    intros [m1 ?] [m2 ?] x; simpl.
    setoid_rewrite lookup_intersection_with_Some. split.
    { intros (?&(l&k&?&?&?)&Hx); simplify_option_eq.
      rewrite elem_of_list_intersection in Hx; naive_solver. }
    intros [(l&?&?) (k&?&?)]. assert (x ∈ list_intersection l k)
      by (by rewrite elem_of_list_intersection).
    exists (list_intersection l k); split; [exists l, k|]; split_and?; auto.
    by rewrite option_guard_True by eauto using elem_of_not_nil.
  - unfold elem_of, hashset_elem_of, intersection, hashset_intersection.
    intros [m1 ?] [m2 ?] x; simpl.
    setoid_rewrite lookup_difference_with_Some. split.
    { intros (l'&[[??]|(l&k&?&?&?)]&Hx); simplify_option_eq;
        rewrite ?elem_of_list_difference in Hx; naive_solver. }
    intros [(l&?&?) Hm2]; destruct (m2 !! hash x) as [k|] eqn:?; eauto.
    destruct (decide (x ∈ k)); [destruct Hm2; eauto|].
    assert (x ∈ list_difference l k) by (by rewrite elem_of_list_difference).
    exists (list_difference l k); split; [right; exists l,k|]; split_and?; auto.
    by rewrite option_guard_True by eauto using elem_of_not_nil.
  - unfold elem_of at 2, hashset_elem_of, elements, hashset_elements.
    intros [m Hm] x; simpl. setoid_rewrite elem_of_list_bind. split.
    { intros ([n l]&Hx&Hn); simpl in *; rewrite elem_of_map_to_list in Hn.
      cut (hash x = n); [intros <-; eauto|].
      eapply (Forall_forall (λ x, hash x = n) l); eauto. eapply Hm; eauto. }
    intros (l&?&?). exists (hash x, l); simpl. by rewrite elem_of_map_to_list.
  - unfold elements, hashset_elements. intros [m Hm]; simpl.
    rewrite map_Forall_to_list in Hm. generalize (NoDup_fst_map_to_list m).
    induction Hm as [|[n l] m' [??] Hm];
      csimpl; inversion_clear 1 as [|?? Hn]; [constructor|].
    apply NoDup_app; split_and?; eauto.
    setoid_rewrite elem_of_list_bind; intros x ? ([n' l']&?&?); simpl in *.
    assert (hash x = n ∧ hash x = n') as [??]; subst.
    { split; [eapply (Forall_forall (λ x, hash x = n) l); eauto|].
      eapply (Forall_forall (λ x, hash x = n') l'); eauto.
      rewrite Forall_forall in Hm. eapply (Hm (_,_)); eauto. }
    destruct Hn; rewrite elem_of_list_fmap; exists (hash x, l'); eauto.
Qed.
End hashset.

Typeclasses Opaque hashset_elem_of.

Section remove_duplicates.
Context `{EqDecision A} (hash : A → Z).

Definition remove_dups_fast (l : list A) : list A :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
     let n : Z := Z.of_nat (length l) in
     elements (foldr (λ x, ({[ x ]} ∪.)) ∅ l :
       hashset (λ x, hash x `mod` (2 * n))%Z)
  end.
Lemma elem_of_remove_dups_fast l x : x ∈ remove_dups_fast l ↔ x ∈ l.
Proof.
  destruct l as [|x1 [|x2 l]]; try reflexivity.
  unfold remove_dups_fast; generalize (x1 :: x2 :: l); clear l; intros l.
  generalize (λ x, hash x `mod` (2 * Z.of_nat (length l)))%Z; intros f.
  rewrite elem_of_elements; split.
  - revert x. induction l as [|y l IH]; intros x; simpl.
    { by rewrite elem_of_empty. }
    rewrite elem_of_union, elem_of_singleton. intros [->|]; [left|right]; eauto.
  - induction 1; set_solver.
Qed.
Lemma NoDup_remove_dups_fast l : NoDup (remove_dups_fast l).
Proof.
  unfold remove_dups_fast; destruct l as [|x1 [|x2 l]].
  - apply NoDup_nil_2.
  - apply NoDup_singleton.
  - apply NoDup_elements.
Qed.
Definition listset_normalize (X : listset A) : listset A :=
  let (l) := X in Listset (remove_dups_fast l).
Lemma listset_normalize_correct X : listset_normalize X ≡ X.
Proof.
  destruct X as [l]. apply set_equiv; intro; apply elem_of_remove_dups_fast.
Qed.
End remove_duplicates.
