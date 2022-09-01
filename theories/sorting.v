(** Merge sort. Adapted from the implementation of Hugo Herbelin in the Coq
standard library, but without using the module system. *)
From Coq Require Export Sorted.
From stdpp Require Export orders list.
From stdpp Require Import options.

Section merge_sort.
  Context {A} (R : relation A) `{∀ x y, Decision (R x y)}.

  Fixpoint list_merge (l1 : list A) : list A → list A :=
    fix list_merge_aux l2 :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x1 :: l1, x2 :: l2 =>
       if decide (R x1 x2) then x1 :: list_merge l1 (x2 :: l2)
       else x2 :: list_merge_aux l2
    end.
  Global Arguments list_merge !_ !_ / : assert.

  Local Notation stack := (list (option (list A))).
  Fixpoint merge_list_to_stack (st : stack) (l : list A) : stack :=
    match st with
    | [] => [Some l]
    | None :: st => Some l :: st
    | Some l' :: st => None :: merge_list_to_stack st (list_merge l' l)
    end.
  Fixpoint merge_stack (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack st
    | Some l :: st => list_merge l (merge_stack st)
    end.
  Fixpoint merge_sort_aux (st : stack) (l : list A) : list A :=
    match l with
    | [] => merge_stack st
    | x :: l => merge_sort_aux (merge_list_to_stack st [x]) l
    end.
  Definition merge_sort : list A → list A := merge_sort_aux [].
End merge_sort.

(** Helper definition for [Sorted_reverse] below *)
Inductive TlRel {A} (R : relation A) (a : A) : list A → Prop :=
  | TlRel_nil : TlRel R a []
  | TlRel_cons b l : R b a → TlRel R a (l ++ [b]).

(** ** Properties of the [Sorted] and [StronglySorted] predicate *)
Section sorted.
  Context {A} (R : relation A).

  Lemma elem_of_StronglySorted_app l1 l2 x1 x2 :
    StronglySorted R (l1 ++ l2) → x1 ∈ l1 → x2 ∈ l2 → R x1 x2.
  Proof.
    induction l1 as [|x1' l1 IH]; simpl; [by rewrite elem_of_nil|].
    intros [? Hall]%StronglySorted_inv [->|?]%elem_of_cons ?; [|by auto].
    rewrite Forall_app, !Forall_forall in Hall. naive_solver.
  Qed.
  Lemma StronglySorted_app_inv_l l1 l2 :
    StronglySorted R (l1 ++ l2) → StronglySorted R l1.
  Proof.
    induction l1 as [|x1' l1 IH]; simpl;
      [|inversion_clear 1]; decompose_Forall; constructor; auto.
  Qed.
  Lemma StronglySorted_app_inv_r l1 l2 :
    StronglySorted R (l1 ++ l2) → StronglySorted R l2.
  Proof.
    induction l1 as [|x1' l1 IH]; simpl;
      [|inversion_clear 1]; decompose_Forall; auto.
  Qed.

  Lemma Sorted_StronglySorted `{!Transitive R} l :
    Sorted R l → StronglySorted R l.
  Proof. by apply Sorted.Sorted_StronglySorted. Qed.
  Lemma StronglySorted_unique `{!AntiSymm (=) R} l1 l2 :
    StronglySorted R l1 → StronglySorted R l2 → l1 ≡ₚ l2 → l1 = l2.
  Proof.
    intros Hl1; revert l2. induction Hl1 as [|x1 l1 ? IH Hx1]; intros l2 Hl2 E.
    { symmetry. by apply Permutation_nil. }
    destruct Hl2 as [|x2 l2 ? Hx2].
    { by apply Permutation_nil_r in E. }
    assert (x1 = x2); subst.
    { rewrite Forall_forall in Hx1, Hx2.
      assert (x2 ∈ x1 :: l1) as Hx2' by (by rewrite E; left).
      assert (x1 ∈ x2 :: l2) as Hx1' by (by rewrite <-E; left).
      inversion Hx1'; inversion Hx2'; simplify_eq; auto. }
    f_equal. by apply IH, (inj (x2 ::.)).
  Qed.
  Lemma Sorted_unique `{!Transitive R, !AntiSymm (=) R} l1 l2 :
    Sorted R l1 → Sorted R l2 → l1 ≡ₚ l2 → l1 = l2.
  Proof. auto using StronglySorted_unique, Sorted_StronglySorted. Qed.

  Global Instance HdRel_dec x `{∀ y, Decision (R x y)} l :
    Decision (HdRel R x l).
  Proof.
   refine
    match l with
    | [] => left _
    | y :: l => cast_if (decide (R x y))
    end; abstract first [by constructor | by inversion 1].
  Defined.
  Global Instance Sorted_dec `{∀ x y, Decision (R x y)} : ∀ l,
    Decision (Sorted R l).
  Proof.
   refine
    (fix go l :=
    match l return Decision (Sorted R l) with
    | [] => left _
    | x :: l => cast_if_and (decide (HdRel R x l)) (go l)
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.
  Global Instance StronglySorted_dec `{∀ x y, Decision (R x y)} : ∀ l,
    Decision (StronglySorted R l).
  Proof.
   refine
    (fix go l :=
    match l return Decision (StronglySorted R l) with
    | [] => left _
    | x :: l => cast_if_and (decide (Forall (R x) l)) (go l)
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.

  Section fmap.
    Context {B} (f : A → B).
    Lemma HdRel_fmap (R1 : relation A) (R2 : relation B) x l :
      (∀ y, R1 x y → R2 (f x) (f y)) → HdRel R1 x l → HdRel R2 (f x) (f <$> l).
    Proof. destruct 2; constructor; auto. Qed.
    Lemma Sorted_fmap (R1 : relation A) (R2 : relation B) l :
      (∀ x y, R1 x y → R2 (f x) (f y)) → Sorted R1 l → Sorted R2 (f <$> l).
    Proof. induction 2; simpl; constructor; eauto using HdRel_fmap. Qed.
    Lemma StronglySorted_fmap (R1 : relation A) (R2 : relation B) l :
      (∀ x y, R1 x y → R2 (f x) (f y)) →
      StronglySorted R1 l → StronglySorted R2 (f <$> l).
    Proof.
      induction 2; csimpl; constructor;
        rewrite ?Forall_fmap; eauto using Forall_impl.
    Qed.
  End fmap.

  Lemma HdRel_reverse l x : HdRel R x l → TlRel (flip R) x (reverse l).
  Proof. destruct 1; rewrite ?reverse_cons; by constructor. Qed.

  Lemma Sorted_snoc l x : Sorted R l → TlRel R x l → Sorted R (l ++ [x]).
  Proof.
    induction 1 as [|y l Hsort IH Hhd]; intros Htl; simpl.
    { repeat constructor. }
    constructor.
    - apply IH. inversion Htl as [|? [|??]]; simplify_list_eq; by constructor.
    - destruct Hhd; constructor; [|done].
      inversion Htl as [|? [|??]]; by try discriminate_list.
  Qed.
End sorted.

Lemma Sorted_reverse {A} (R : relation A) l :
  Sorted R l → Sorted (flip R) (reverse l).
Proof.
  induction 1; rewrite ?reverse_nil, ?reverse_cons;
    auto using Sorted_snoc, HdRel_reverse.
Qed.

(** ** Correctness of merge sort *)
Section merge_sort_correct.
  Context  {A} (R : relation A) `{∀ x y, Decision (R x y)}.

  Lemma list_merge_nil_l l2 : list_merge R [] l2 = l2.
  Proof. by destruct l2. Qed.
  Lemma list_merge_nil_r l1 : list_merge R l1 [] = l1.
  Proof. by destruct l1. Qed.
  Lemma list_merge_cons x1 x2 l1 l2 :
    list_merge R (x1 :: l1) (x2 :: l2) =
      if decide (R x1 x2) then x1 :: list_merge R l1 (x2 :: l2)
      else x2 :: list_merge R (x1 :: l1) l2.
  Proof. done. Qed.
  Lemma HdRel_list_merge x l1 l2 :
    HdRel R x l1 → HdRel R x l2 → HdRel R x (list_merge R l1 l2).
  Proof.
    destruct 1 as [|x1 l1 IH1], 1 as [|x2 l2 IH2];
      rewrite ?list_merge_cons; simpl; repeat case_decide; auto.
  Qed.
  Lemma Sorted_list_merge `{!Total R} l1 l2 :
    Sorted R l1 → Sorted R l2 → Sorted R (list_merge R l1 l2).
  Proof.
    intros Hl1. revert l2. induction Hl1 as [|x1 l1 IH1];
      induction 1 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide;
      repeat match goal with H : ¬R _ _ |- _ => apply total_not in H end;
      constructor; eauto using HdRel_list_merge, HdRel_cons.
  Qed.
  Lemma merge_Permutation l1 l2 : list_merge R l1 l2 ≡ₚ l1 ++ l2.
  Proof.
    revert l2. induction l1 as [|x1 l1 IH1]; intros l2;
      induction l2 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide; auto.
    - by rewrite (right_id_L [] (++)).
    - by rewrite IH2, Permutation_middle.
  Qed.

  Local Notation stack := (list (option (list A))).
  Inductive merge_stack_Sorted : stack → Prop :=
    | merge_stack_Sorted_nil : merge_stack_Sorted []
    | merge_stack_Sorted_cons_None st :
       merge_stack_Sorted st → merge_stack_Sorted (None :: st)
    | merge_stack_Sorted_cons_Some l st :
       Sorted R l → merge_stack_Sorted st → merge_stack_Sorted (Some l :: st).
  Fixpoint merge_stack_flatten (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack_flatten st
    | Some l :: st => l ++ merge_stack_flatten st
    end.

  Lemma Sorted_merge_list_to_stack `{!Total R} st l :
    merge_stack_Sorted st → Sorted R l →
    merge_stack_Sorted (merge_list_to_stack R st l).
  Proof.
    intros Hst. revert l.
    induction Hst; repeat constructor; naive_solver auto using Sorted_list_merge.
  Qed.
  Lemma merge_list_to_stack_Permutation st l :
    merge_stack_flatten (merge_list_to_stack R st l) ≡ₚ
      l ++ merge_stack_flatten st.
  Proof.
    revert l. induction st as [|[l'|] st IH]; intros l; simpl; auto.
    by rewrite IH, merge_Permutation, (assoc_L _), (comm (++) l).
  Qed.
  Lemma Sorted_merge_stack `{!Total R} st :
    merge_stack_Sorted st → Sorted R (merge_stack R st).
  Proof. induction 1; simpl; auto using Sorted_list_merge. Qed.
  Lemma merge_stack_Permutation st : merge_stack R st ≡ₚ merge_stack_flatten st.
  Proof.
    induction st as [|[] ? IH]; intros; simpl; auto.
    by rewrite merge_Permutation, IH.
  Qed.
  Lemma Sorted_merge_sort_aux `{!Total R} st l :
    merge_stack_Sorted st → Sorted R (merge_sort_aux R st l).
  Proof.
    revert st. induction l; simpl;
      auto using Sorted_merge_stack, Sorted_merge_list_to_stack.
  Qed.
  Lemma merge_sort_aux_Permutation st l :
    merge_sort_aux R st l ≡ₚ merge_stack_flatten st ++ l.
  Proof.
    revert st. induction l as [|?? IH]; simpl; intros.
    - by rewrite (right_id_L [] (++)), merge_stack_Permutation.
    - rewrite IH, merge_list_to_stack_Permutation; simpl.
      by rewrite Permutation_middle.
  Qed.
  Lemma Sorted_merge_sort `{!Total R} l : Sorted R (merge_sort R l).
  Proof. apply Sorted_merge_sort_aux. by constructor. Qed.
  Lemma merge_sort_Permutation l : merge_sort R l ≡ₚ l.
  Proof. unfold merge_sort. by rewrite merge_sort_aux_Permutation. Qed.
  Lemma StronglySorted_merge_sort `{!Transitive R, !Total R} l :
    StronglySorted R (merge_sort R l).
  Proof. auto using Sorted_StronglySorted, Sorted_merge_sort. Qed.
End merge_sort_correct.
