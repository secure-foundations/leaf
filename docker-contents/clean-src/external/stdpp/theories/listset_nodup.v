(** This file implements finite as unordered lists without duplicates.
Although this implementation is slow, it is very useful as decidable equality
is the only constraint on the carrier set. *)
From stdpp Require Export sets list.
From stdpp Require Import options.

Record listset_nodup A := ListsetNoDup {
  listset_nodup_car : list A; listset_nodup_prf : NoDup listset_nodup_car
}.
Global Arguments ListsetNoDup {_} _ _ : assert.
Global Arguments listset_nodup_car {_} _ : assert.
Global Arguments listset_nodup_prf {_} _ : assert.

Section list_set.
Context `{EqDecision A}.
Notation C := (listset_nodup A).

Global Instance listset_nodup_elem_of: ElemOf A C := λ x l, x ∈ listset_nodup_car l.
Global Instance listset_nodup_empty: Empty C := ListsetNoDup [] (@NoDup_nil_2 _).
Global Instance listset_nodup_singleton: Singleton A C := λ x,
  ListsetNoDup [x] (NoDup_singleton x).
Global Instance listset_nodup_union: Union C :=
  λ '(ListsetNoDup l Hl) '(ListsetNoDup k Hk),
    ListsetNoDup _ (NoDup_list_union _ _ Hl Hk).
Global Instance listset_nodup_intersection: Intersection C :=
  λ '(ListsetNoDup l Hl) '(ListsetNoDup k Hk),
    ListsetNoDup _ (NoDup_list_intersection _ k Hl).
Global Instance listset_nodup_difference: Difference C :=
  λ '(ListsetNoDup l Hl) '(ListsetNoDup k Hk),
    ListsetNoDup _ (NoDup_list_difference _ k Hl).

Local Instance listset_nodup_set: Set_ A C.
Proof.
  split; [split | | ].
  - by apply not_elem_of_nil.
  - by apply elem_of_list_singleton.
  - intros [??] [??] ?. apply elem_of_list_union.
  - intros [??] [??] ?. apply elem_of_list_intersection.
  - intros [??] [??] ?. apply elem_of_list_difference.
Qed.

Global Instance listset_nodup_elems: Elements A C := listset_nodup_car.
Global Instance listset_nodup_fin_set: FinSet A C.
Proof. split; [apply _|done|]. by intros [??]. Qed.
End list_set.
