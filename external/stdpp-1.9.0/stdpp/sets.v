(** This file collects definitions and theorems on sets. Most
importantly, it implements some tactics to automatically solve goals involving
sets. *)
From stdpp Require Export orders list list_numbers.
From stdpp Require Import finite.
From stdpp Require Import options.

(* FIXME: This file needs a 'Proof Using' hint, but they need to be set
locally (or things moved out of sections) as no default works well enough. *)
Unset Default Proof Using.

(* Higher precedence to make sure these instances are not used for other types
with an [ElemOf] instance, such as lists. *)
Global Instance set_equiv_instance `{ElemOf A C} : Equiv C | 20 := λ X Y,
  ∀ x, x ∈ X ↔ x ∈ Y.
Global Instance set_subseteq_instance `{ElemOf A C} : SubsetEq C | 20 := λ X Y,
  ∀ x, x ∈ X → x ∈ Y.
Global Instance set_disjoint_instance `{ElemOf A C} : Disjoint C | 20 := λ X Y,
  ∀ x, x ∈ X → x ∈ Y → False.
Global Typeclasses Opaque set_equiv_instance set_subseteq_instance set_disjoint_instance.

(** * Setoids *)
Section setoids_simple.
  Context `{SemiSet A C}.

  Global Instance set_equiv_equivalence : Equivalence (≡@{C}).
  Proof.
    split.
    - done.
    - intros X Y ? x. by symmetry.
    - intros X Y Z ?? x; by trans (x ∈ Y).
  Qed.
  Global Instance singleton_proper : Proper ((=) ==> (≡@{C})) singleton.
  Proof. apply _. Qed.
  Global Instance elem_of_proper : Proper ((=) ==> (≡) ==> iff) (∈@{C}) | 5.
  Proof. by intros x ? <- X Y. Qed.
  Global Instance disjoint_proper: Proper ((≡) ==> (≡) ==> iff) (##@{C}).
  Proof.
    intros X1 X2 HX Y1 Y2 HY; apply forall_proper; intros x. by rewrite HX, HY.
  Qed.
  Global Instance union_proper : Proper ((≡) ==> (≡) ==> (≡@{C})) union.
  Proof. intros X1 X2 HX Y1 Y2 HY x. rewrite !elem_of_union. f_equiv; auto. Qed.
  Global Instance union_list_proper: Proper ((≡) ==> (≡@{C})) union_list.
  Proof. by induction 1; simpl; try apply union_proper. Qed.
  Global Instance subseteq_proper : Proper ((≡@{C}) ==> (≡@{C}) ==> iff) (⊆).
  Proof.
    intros X1 X2 HX Y1 Y2 HY. apply forall_proper; intros x. by rewrite HX, HY.
  Qed.
  Global Instance subset_proper : Proper ((≡@{C}) ==> (≡@{C}) ==> iff) (⊂).
  Proof. solve_proper. Qed.
End setoids_simple.

Section setoids.
  Context `{Set_ A C}.

  (** * Setoids *)
  Global Instance intersection_proper :
    Proper ((≡) ==> (≡) ==> (≡@{C})) intersection.
  Proof.
    intros X1 X2 HX Y1 Y2 HY x. by rewrite !elem_of_intersection, HX, HY.
  Qed.
  Global Instance difference_proper :
     Proper ((≡) ==> (≡) ==> (≡@{C})) difference.
  Proof.
    intros X1 X2 HX Y1 Y2 HY x. by rewrite !elem_of_difference, HX, HY.
  Qed.
End setoids.

Section setoids_monad.
  Context `{MonadSet M}.

  Global Instance set_fmap_proper {A B} :
    Proper (pointwise_relation _ (=) ==> (≡) ==> (≡)) (@fmap M _ A B).
  Proof.
    intros f1 f2 Hf X1 X2 HX x. rewrite !elem_of_fmap. f_equiv; intros z.
    by rewrite HX, Hf.
  Qed.
  Global Instance set_bind_proper {A B} :
    Proper (pointwise_relation _ (≡) ==> (≡) ==> (≡)) (@mbind M _ A B).
  Proof.
    intros f1 f2 Hf X1 X2 HX x. rewrite !elem_of_bind. f_equiv; intros z.
    by rewrite HX, (Hf z).
  Qed.
  Global Instance set_join_proper {A} :
    Proper ((≡) ==> (≡)) (@mjoin M _ A).
  Proof.
    intros X1 X2 HX x. rewrite !elem_of_join. f_equiv; intros z. by rewrite HX.
  Qed.
End setoids_monad.

(** * Tactics *)
(** The tactic [set_unfold] transforms all occurrences of [(∪)], [(∩)], [(∖)],
[(<$>)], [∅], [{[_]}], [(≡)], and [(⊆)] into logically equivalent propositions
involving just [∈]. For example, [A → x ∈ X ∪ ∅] becomes [A → x ∈ X ∨ False].

This transformation is implemented using type classes instead of setoid
rewriting to ensure that we traverse each term at most once and to be able to
deal with occurences of the set operations under binders. *)
Class SetUnfold (P Q : Prop) := { set_unfold : P ↔ Q }.
Global Arguments set_unfold _ _ {_} : assert.
Global Hint Mode SetUnfold + - : typeclass_instances.

(** The class [SetUnfoldElemOf] is a more specialized version of [SetUnfold]
for propositions of the shape [x ∈ X] to improve performance. *)
Class SetUnfoldElemOf `{ElemOf A C} (x : A) (X : C) (Q : Prop) :=
  { set_unfold_elem_of : x ∈ X ↔ Q }.
Global Arguments set_unfold_elem_of {_ _ _} _ _ _ {_} : assert.
Global Hint Mode SetUnfoldElemOf + + + - + - : typeclass_instances.

Global Instance set_unfold_elem_of_default `{ElemOf A C} (x : A) (X : C) :
  SetUnfoldElemOf x X (x ∈ X) | 1000.
Proof. done. Qed.
Global Instance set_unfold_elem_of_set_unfold `{ElemOf A C} (x : A) (X : C) Q :
  SetUnfoldElemOf x X Q → SetUnfold (x ∈ X) Q.
Proof. by destruct 1; constructor. Qed.

Class SetUnfoldSimpl (P Q : Prop) := { set_unfold_simpl : SetUnfold P Q }.
Global Hint Extern 0 (SetUnfoldSimpl _ _) => csimpl; constructor : typeclass_instances.

Global Instance set_unfold_default P : SetUnfold P P | 1000. done. Qed.
Definition set_unfold_1 `{SetUnfold P Q} : P → Q := proj1 (set_unfold P Q).
Definition set_unfold_2 `{SetUnfold P Q} : Q → P := proj2 (set_unfold P Q).

Lemma set_unfold_impl P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P → Q) (P' → Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_and P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P ∧ Q) (P' ∧ Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_or P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P ∨ Q) (P' ∨ Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_iff P Q P' Q' :
  SetUnfold P P' → SetUnfold Q Q' → SetUnfold (P ↔ Q) (P' ↔ Q').
Proof. constructor. by rewrite (set_unfold P P'), (set_unfold Q Q'). Qed.
Lemma set_unfold_not P P' : SetUnfold P P' → SetUnfold (¬P) (¬P').
Proof. constructor. by rewrite (set_unfold P P'). Qed.
Lemma set_unfold_forall {A} (P P' : A → Prop) :
  (∀ x, SetUnfold (P x) (P' x)) → SetUnfold (∀ x, P x) (∀ x, P' x).
Proof. constructor. naive_solver. Qed.
Lemma set_unfold_exist {A} (P P' : A → Prop) :
  (∀ x, SetUnfold (P x) (P' x)) → SetUnfold (∃ x, P x) (∃ x, P' x).
Proof. constructor. naive_solver. Qed.

(* Avoid too eager application of the above instances (and thus too eager
unfolding of type class transparent definitions). *)
Global Hint Extern 0 (SetUnfold (_ → _) _) =>
  class_apply set_unfold_impl : typeclass_instances.
Global Hint Extern 0 (SetUnfold (_ ∧ _) _) =>
  class_apply set_unfold_and : typeclass_instances.
Global Hint Extern 0 (SetUnfold (_ ∨ _) _) =>
  class_apply set_unfold_or : typeclass_instances.
Global Hint Extern 0 (SetUnfold (_ ↔ _) _) =>
  class_apply set_unfold_iff : typeclass_instances.
Global Hint Extern 0 (SetUnfold (¬ _) _) =>
  class_apply set_unfold_not : typeclass_instances.
Global Hint Extern 1 (SetUnfold (∀ _, _) _) =>
  class_apply set_unfold_forall : typeclass_instances.
Global Hint Extern 0 (SetUnfold (∃ _, _) _) =>
  class_apply set_unfold_exist : typeclass_instances.

Section set_unfold_simple.
  Context `{SemiSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Global Instance set_unfold_empty x : SetUnfoldElemOf x (∅ : C) False.
  Proof. constructor. split; [|done]. apply not_elem_of_empty. Qed.
  Global Instance set_unfold_singleton x y : SetUnfoldElemOf x ({[ y ]} : C) (x = y).
  Proof. constructor; apply elem_of_singleton. Qed.
  Global Instance set_unfold_union x X Y P Q :
    SetUnfoldElemOf x X P → SetUnfoldElemOf x Y Q →
    SetUnfoldElemOf x (X ∪ Y) (P ∨ Q).
  Proof.
    intros ??; constructor.
    by rewrite elem_of_union,
      (set_unfold_elem_of x X P), (set_unfold_elem_of x Y Q).
  Qed.
  Global Instance set_unfold_equiv_same X : SetUnfold (X ≡ X) True | 1.
  Proof. done. Qed.
  Global Instance set_unfold_equiv_empty_l X (P : A → Prop) :
    (∀ x, SetUnfoldElemOf x X (P x)) → SetUnfold (∅ ≡ X) (∀ x, ¬P x) | 5.
  Proof.
    intros ?; constructor. unfold equiv, set_equiv_instance.
    pose proof (not_elem_of_empty (C:=C)); naive_solver.
  Qed.
  Global Instance set_unfold_equiv_empty_r (P : A → Prop) X :
    (∀ x, SetUnfoldElemOf x X (P x)) → SetUnfold (X ≡ ∅) (∀ x, ¬P x) | 5.
  Proof.
    intros ?; constructor. unfold equiv, set_equiv_instance.
    pose proof (not_elem_of_empty (C:=C)); naive_solver.
  Qed.
  Global Instance set_unfold_equiv (P Q : A → Prop) X Y :
    (∀ x, SetUnfoldElemOf x X (P x)) → (∀ x, SetUnfoldElemOf x Y (Q x)) →
    SetUnfold (X ≡ Y) (∀ x, P x ↔ Q x) | 10.
  Proof. constructor. apply forall_proper; naive_solver. Qed.
  Global Instance set_unfold_subseteq (P Q : A → Prop) X Y :
    (∀ x, SetUnfoldElemOf x X (P x)) → (∀ x, SetUnfoldElemOf x Y (Q x)) →
    SetUnfold (X ⊆ Y) (∀ x, P x → Q x).
  Proof. constructor. apply forall_proper; naive_solver. Qed.
  Global Instance set_unfold_subset (P Q : A → Prop) X Y :
    (∀ x, SetUnfoldElemOf x X (P x)) → (∀ x, SetUnfoldElemOf x Y (Q x)) →
    SetUnfold (X ⊂ Y) ((∀ x, P x → Q x) ∧ ¬∀ x, Q x → P x).
  Proof.
    constructor. unfold strict.
    repeat f_equiv; apply forall_proper; naive_solver.
  Qed.
  Global Instance set_unfold_disjoint (P Q : A → Prop) X Y :
    (∀ x, SetUnfoldElemOf x X (P x)) → (∀ x, SetUnfoldElemOf x Y (Q x)) →
    SetUnfold (X ## Y) (∀ x, P x → Q x → False).
  Proof. constructor. unfold disjoint, set_disjoint_instance. naive_solver. Qed.

  Context `{!LeibnizEquiv C}.
  Global Instance set_unfold_equiv_same_L X : SetUnfold (X = X) True | 1.
  Proof. done. Qed.
  Global Instance set_unfold_equiv_empty_l_L X (P : A → Prop) :
    (∀ x, SetUnfoldElemOf x X (P x)) → SetUnfold (∅ = X) (∀ x, ¬P x) | 5.
  Proof. constructor. unfold_leibniz. by apply set_unfold_equiv_empty_l. Qed.
  Global Instance set_unfold_equiv_empty_r_L (P : A → Prop) X :
    (∀ x, SetUnfoldElemOf x X (P x)) → SetUnfold (X = ∅) (∀ x, ¬P x) | 5.
  Proof. constructor. unfold_leibniz. by apply set_unfold_equiv_empty_r. Qed.
  Global Instance set_unfold_equiv_L (P Q : A → Prop) X Y :
    (∀ x, SetUnfoldElemOf x X (P x)) → (∀ x, SetUnfoldElemOf x Y (Q x)) →
    SetUnfold (X = Y) (∀ x, P x ↔ Q x) | 10.
  Proof. constructor. unfold_leibniz. by apply set_unfold_equiv. Qed.
End set_unfold_simple.

Section set_unfold.
  Context `{Set_ A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Global Instance set_unfold_intersection x X Y P Q :
    SetUnfoldElemOf x X P → SetUnfoldElemOf x Y Q →
    SetUnfoldElemOf x (X ∩ Y) (P ∧ Q).
  Proof.
    intros ??; constructor. rewrite elem_of_intersection.
    by rewrite (set_unfold_elem_of x X P), (set_unfold_elem_of x Y Q).
  Qed.
  Global Instance set_unfold_difference x X Y P Q :
    SetUnfoldElemOf x X P → SetUnfoldElemOf x Y Q →
    SetUnfoldElemOf x (X ∖ Y) (P ∧ ¬Q).
  Proof.
    intros ??; constructor. rewrite elem_of_difference.
    by rewrite (set_unfold_elem_of x X P), (set_unfold_elem_of x Y Q).
  Qed.
End set_unfold.

Global Instance set_unfold_top `{TopSet A C} (x : A) :
  SetUnfoldElemOf x (⊤ : C) True.
Proof. constructor. split; [done|intros; apply elem_of_top']. Qed.

Section set_unfold_monad.
  Context `{MonadSet M}.

  Global Instance set_unfold_ret {A} (x y : A) :
    SetUnfoldElemOf x (mret (M:=M) y) (x = y).
  Proof. constructor; apply elem_of_ret. Qed.
  Global Instance set_unfold_bind {A B} (f : A → M B) X (P Q : A → Prop) x :
    (∀ y, SetUnfoldElemOf y X (P y)) → (∀ y, SetUnfoldElemOf x (f y) (Q y)) →
    SetUnfoldElemOf x (X ≫= f) (∃ y, Q y ∧ P y).
  Proof. constructor. rewrite elem_of_bind; naive_solver. Qed.
  Global Instance set_unfold_fmap {A B} (f : A → B) (X : M A) (P : A → Prop) x :
    (∀ y, SetUnfoldElemOf y X (P y)) →
    SetUnfoldElemOf x (f <$> X) (∃ y, x = f y ∧ P y).
  Proof. constructor. rewrite elem_of_fmap; naive_solver. Qed.
  Global Instance set_unfold_join {A} (X : M (M A)) (P : M A → Prop) x :
    (∀ Y, SetUnfoldElemOf Y X (P Y)) →
    SetUnfoldElemOf x (mjoin X) (∃ Y, x ∈ Y ∧ P Y).
  Proof. constructor. rewrite elem_of_join; naive_solver. Qed.
End set_unfold_monad.

Section set_unfold_list.
  Context {A : Type}.
  Implicit Types x : A.
  Implicit Types l : list A.

  Global Instance set_unfold_nil x : SetUnfoldElemOf x [] False.
  Proof. constructor; apply elem_of_nil. Qed.
  Global Instance set_unfold_cons x y l P :
    SetUnfoldElemOf x l P → SetUnfoldElemOf x (y :: l) (x = y ∨ P).
  Proof. constructor. by rewrite elem_of_cons, (set_unfold_elem_of x l P). Qed.
  Global Instance set_unfold_app x l k P Q :
    SetUnfoldElemOf x l P → SetUnfoldElemOf x k Q →
    SetUnfoldElemOf x (l ++ k) (P ∨ Q).
  Proof.
    intros ??; constructor.
    by rewrite elem_of_app, (set_unfold_elem_of x l P), (set_unfold_elem_of x k Q).
  Qed.
  Global Instance set_unfold_included l k (P Q : A → Prop) :
    (∀ x, SetUnfoldElemOf x l (P x)) → (∀ x, SetUnfoldElemOf x k (Q x)) →
    SetUnfold (l ⊆ k) (∀ x, P x → Q x).
  Proof.
    constructor; unfold subseteq, list_subseteq.
    apply forall_proper; naive_solver.
  Qed.

  Global Instance set_unfold_reverse x l P :
    SetUnfoldElemOf x l P → SetUnfoldElemOf x (reverse l) P.
  Proof. constructor. by rewrite elem_of_reverse, (set_unfold_elem_of x l P). Qed.

  Global Instance set_unfold_list_fmap {B} (f : A → B) l P y :
    (∀ x, SetUnfoldElemOf x l (P x)) →
    SetUnfoldElemOf y (f <$> l) (∃ x, y = f x ∧ P x).
  Proof.
    constructor. rewrite elem_of_list_fmap. f_equiv; intros x.
    by rewrite (set_unfold_elem_of x l (P x)).
  Qed.
  Global Instance set_unfold_rotate x l P n:
    SetUnfoldElemOf x l P → SetUnfoldElemOf x (rotate n l) P.
  Proof. constructor. by rewrite elem_of_rotate, (set_unfold_elem_of x l P). Qed.

  Global Instance set_unfold_list_bind {B} (f : A → list B) l P Q y :
    (∀ x, SetUnfoldElemOf x l (P x)) → (∀ x, SetUnfoldElemOf y (f x) (Q x)) →
    SetUnfoldElemOf y (l ≫= f) (∃ x, Q x ∧ P x).
  Proof. constructor. rewrite elem_of_list_bind. naive_solver. Qed.
End set_unfold_list.

Tactic Notation "set_unfold" :=
  let rec unfold_hyps :=
    try match goal with
    | H : ?P |- _ =>
       lazymatch type of P with
       | Prop =>
         apply set_unfold_1 in H; revert H;
         first [unfold_hyps; intros H | intros H; fail 1]
       | _ => fail
       end
    end in
  apply set_unfold_2; unfold_hyps; csimpl in *.

Tactic Notation "set_unfold" "in" ident(H) :=
  let P := type of H in
  lazymatch type of P with
  | Prop => apply set_unfold_1 in H
  | _ => fail "hypothesis" H "is not a proposition"
  end.

(** Since [firstorder] already fails or loops on very small goals generated by
[set_solver], we use the [naive_solver] tactic as a substitute. *)
Tactic Notation "set_solver" "by" tactic3(tac) :=
  try fast_done;
  intros; setoid_subst;
  set_unfold;
  intros; setoid_subst;
  try match goal with |- _ ∈ _ => apply dec_stable end;
  naive_solver tac.
Tactic Notation "set_solver" "-" hyp_list(Hs) "by" tactic3(tac) :=
  clear Hs; set_solver by tac.
Tactic Notation "set_solver" "+" hyp_list(Hs) "by" tactic3(tac) :=
  clear -Hs; set_solver by tac.
Tactic Notation "set_solver" := set_solver by eauto.
Tactic Notation "set_solver" "-" hyp_list(Hs) := clear Hs; set_solver.
Tactic Notation "set_solver" "+" hyp_list(Hs) := clear -Hs; set_solver.

Global Hint Extern 1000 (_ ∉ _) => set_solver : set_solver.
Global Hint Extern 1000 (_ ∈ _) => set_solver : set_solver.
Global Hint Extern 1000 (_ ⊆ _) => set_solver : set_solver.


(** * Sets with [∪], [∅] and [{[_]}] *)
Section semi_set.
  Context `{SemiSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.
  Implicit Types Xs Ys : list C.

  (** Equality *)
  Lemma set_equiv X Y : X ≡ Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
  Proof. set_solver. Qed.
  Lemma set_equiv_subseteq X Y : X ≡ Y ↔ X ⊆ Y ∧ Y ⊆ X.
  Proof. set_solver. Qed.
  Global Instance singleton_equiv_inj : Inj (=) (≡@{C}) singleton.
  Proof. unfold Inj. set_solver. Qed.
  Global Instance singleton_inj `{!LeibnizEquiv C} : Inj (=) (=@{C}) singleton.
  Proof. unfold Inj. set_solver. Qed.

  (** Subset relation *)
  Global Instance set_subseteq_antisymm: AntiSymm (≡) (⊆@{C}).
  Proof. intros ??. set_solver. Qed.

  Global Instance set_subseteq_preorder: PreOrder (⊆@{C}).
  Proof. split; [by intros ??|]. intros ???; set_solver. Qed.

  Lemma subseteq_union X Y : X ⊆ Y ↔ X ∪ Y ≡ Y.
  Proof. set_solver. Qed.
  Lemma subseteq_union_1 X Y : X ⊆ Y → X ∪ Y ≡ Y.
  Proof. by rewrite subseteq_union. Qed.
  Lemma subseteq_union_2 X Y : X ∪ Y ≡ Y → X ⊆ Y.
  Proof. by rewrite subseteq_union. Qed.

  Lemma union_subseteq_l X Y : X ⊆ X ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_subseteq_l' X X' Y : X ⊆ X' → X ⊆ X' ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_subseteq_r X Y : Y ⊆ X ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_subseteq_r' X Y Y' : Y ⊆ Y' → Y ⊆ X ∪ Y'.
  Proof. set_solver. Qed.
  Lemma union_least X Y Z : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z.
  Proof. set_solver. Qed.

  Lemma elem_of_subseteq X Y : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y.
  Proof. done. Qed.
  Lemma elem_of_subset X Y : X ⊂ Y ↔ (∀ x, x ∈ X → x ∈ Y) ∧ ¬(∀ x, x ∈ Y → x ∈ X).
  Proof. set_solver. Qed.
  Lemma elem_of_weaken x X Y : x ∈ X → X ⊆ Y → x ∈ Y.
  Proof. set_solver. Qed.

  Lemma not_elem_of_weaken x X Y : x ∉ Y → X ⊆ Y → x ∉ X.
  Proof. set_solver. Qed.

  (** Union *)
  Lemma union_subseteq X Y Z : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z.
  Proof. set_solver. Qed.
  Lemma not_elem_of_union x X Y : x ∉ X ∪ Y ↔ x ∉ X ∧ x ∉ Y.
  Proof. set_solver. Qed.
  Lemma elem_of_union_l x X Y : x ∈ X → x ∈ X ∪ Y.
  Proof. set_solver. Qed.
  Lemma elem_of_union_r x X Y : x ∈ Y → x ∈ X ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_mono_l X Y1 Y2 : Y1 ⊆ Y2 → X ∪ Y1 ⊆ X ∪ Y2.
  Proof. set_solver. Qed.
  Lemma union_mono_r X1 X2 Y : X1 ⊆ X2 → X1 ∪ Y ⊆ X2 ∪ Y.
  Proof. set_solver. Qed.
  Lemma union_mono X1 X2 Y1 Y2 : X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∪ Y1 ⊆ X2 ∪ Y2.
  Proof. set_solver. Qed.

  Global Instance union_idemp : IdemP (≡@{C}) (∪).
  Proof. intros X. set_solver. Qed.
  Global Instance union_empty_l : LeftId (≡@{C}) ∅ (∪).
  Proof. intros X. set_solver. Qed.
  Global Instance union_empty_r : RightId (≡@{C}) ∅ (∪).
  Proof. intros X. set_solver. Qed.
  Global Instance union_comm : Comm (≡@{C}) (∪).
  Proof. intros X Y. set_solver. Qed.
  Global Instance union_assoc : Assoc (≡@{C}) (∪).
  Proof. intros X Y Z. set_solver. Qed.

  Lemma empty_union X Y : X ∪ Y ≡ ∅ ↔ X ≡ ∅ ∧ Y ≡ ∅.
  Proof. set_solver. Qed.

  Lemma union_cancel_l X Y Z : Z ## X → Z ## Y → Z ∪ X ≡ Z ∪ Y → X ≡ Y.
  Proof. set_solver. Qed.
  Lemma union_cancel_r X Y Z : X ## Z → Y ## Z → X ∪ Z ≡ Y ∪ Z → X ≡ Y.
  Proof. set_solver. Qed.

  (** Empty *)
  Lemma empty_subseteq X : ∅ ⊆ X.
  Proof. set_solver. Qed.
  Lemma elem_of_equiv_empty X : X ≡ ∅ ↔ ∀ x, x ∉ X.
  Proof. set_solver. Qed.
  Lemma elem_of_empty x : x ∈@{C} ∅ ↔ False.
  Proof. set_solver. Qed.
  Lemma equiv_empty X : X ⊆ ∅ → X ≡ ∅.
  Proof. set_solver. Qed.
  Lemma union_positive_l X Y : X ∪ Y ≡ ∅ → X ≡ ∅.
  Proof. set_solver. Qed.
  Lemma union_positive_l_alt X Y : X ≢ ∅ → X ∪ Y ≢ ∅.
  Proof. set_solver. Qed.
  Lemma non_empty_inhabited x X : x ∈ X → X ≢ ∅.
  Proof. set_solver. Qed.

  (** Singleton *)
  Lemma elem_of_singleton_1 x y : x ∈@{C} {[y]} → x = y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_singleton_2 x y : x = y → x ∈@{C} {[y]}.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma elem_of_subseteq_singleton x X : x ∈ X ↔ {[ x ]} ⊆ X.
  Proof. set_solver. Qed.
  Lemma non_empty_singleton x : {[ x ]} ≢@{C} ∅.
  Proof. set_solver. Qed.
  Lemma not_elem_of_singleton x y : x ∉@{C} {[ y ]} ↔ x ≠ y.
  Proof. by rewrite elem_of_singleton. Qed.
  Lemma not_elem_of_singleton_1 x y : x ∉@{C} {[ y ]} → x ≠ y.
  Proof. apply not_elem_of_singleton. Qed.
  Lemma not_elem_of_singleton_2 x y : x ≠ y → x ∉@{C} {[ y ]}.
  Proof. apply not_elem_of_singleton. Qed.

  Lemma singleton_subseteq_l x X : {[ x ]} ⊆ X ↔ x ∈ X.
  Proof. set_solver. Qed.
  Lemma singleton_subseteq x y : {[ x ]} ⊆@{C} {[ y ]} ↔ x = y.
  Proof. set_solver. Qed.

  (** Disjointness *)
  Lemma elem_of_disjoint X Y : X ## Y ↔ ∀ x, x ∈ X → x ∈ Y → False.
  Proof. done. Qed.

  Global Instance disjoint_sym : Symmetric (##@{C}).
  Proof. intros X Y. set_solver. Qed.
  Lemma disjoint_empty_l Y : ∅ ## Y.
  Proof. set_solver. Qed.
  Lemma disjoint_empty_r X : X ## ∅.
  Proof. set_solver. Qed.
  Lemma disjoint_singleton_l x Y : {[ x ]} ## Y ↔ x ∉ Y.
  Proof. set_solver. Qed.
  Lemma disjoint_singleton_r y X : X ## {[ y ]} ↔ y ∉ X.
  Proof. set_solver. Qed.
  Lemma disjoint_union_l X1 X2 Y : X1 ∪ X2 ## Y ↔ X1 ## Y ∧ X2 ## Y.
  Proof. set_solver. Qed.
  Lemma disjoint_union_r X Y1 Y2 : X ## Y1 ∪ Y2 ↔ X ## Y1 ∧ X ## Y2.
  Proof. set_solver. Qed.

  (** Big unions *)
  Lemma elem_of_union_list Xs x : x ∈ ⋃ Xs ↔ ∃ X, X ∈ Xs ∧ x ∈ X.
  Proof.
    split.
    - induction Xs; simpl; intros HXs; [by apply elem_of_empty in HXs|].
      setoid_rewrite elem_of_cons. apply elem_of_union in HXs. naive_solver.
    - intros [X [Hx]]. induction Hx; simpl; [by apply elem_of_union_l |].
      intros. apply elem_of_union_r; auto.
  Qed.

  Lemma union_list_nil : ⋃ @nil C = ∅.
  Proof. done. Qed.
  Lemma union_list_cons X Xs : ⋃ (X :: Xs) = X ∪ ⋃ Xs.
  Proof. done. Qed.
  Lemma union_list_singleton X : ⋃ [X] ≡ X.
  Proof. simpl. by rewrite (right_id ∅ _). Qed.
  Lemma union_list_app Xs1 Xs2 : ⋃ (Xs1 ++ Xs2) ≡ ⋃ Xs1 ∪ ⋃ Xs2.
  Proof.
    induction Xs1 as [|X Xs1 IH]; simpl; [by rewrite (left_id ∅ _)|].
    by rewrite IH, (assoc _).
  Qed.
  Lemma union_list_reverse Xs : ⋃ (reverse Xs) ≡ ⋃ Xs.
  Proof.
    induction Xs as [|X Xs IH]; simpl; [done |].
    by rewrite reverse_cons, union_list_app,
      union_list_singleton, (comm _), IH.
  Qed.
  Lemma union_list_mono Xs Ys : Xs ⊆* Ys → ⋃ Xs ⊆ ⋃ Ys.
  Proof. induction 1; simpl; auto using union_mono. Qed.

  Lemma empty_union_list Xs : ⋃ Xs ≡ ∅ ↔ Forall (.≡ ∅) Xs.
  Proof.
    split.
    - induction Xs; simpl; rewrite ?empty_union; intuition.
    - induction 1 as [|?? E1 ? E2]; simpl; [done|]. by apply empty_union.
  Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    Lemma set_eq X Y : X = Y ↔ ∀ x, x ∈ X ↔ x ∈ Y.
    Proof. unfold_leibniz. apply set_equiv. Qed.
    Lemma set_eq_subseteq X Y : X = Y ↔ X ⊆ Y ∧ Y ⊆ X.
    Proof. unfold_leibniz. apply set_equiv_subseteq. Qed.

    (** Subset relation *)
    Global Instance set_subseteq_partialorder : PartialOrder (⊆@{C}).
    Proof. split; [apply _|]. intros ??. unfold_leibniz. apply (anti_symm _). Qed.

    Lemma subseteq_union_L X Y : X ⊆ Y ↔ X ∪ Y = Y.
    Proof. unfold_leibniz. apply subseteq_union. Qed.
    Lemma subseteq_union_1_L X Y : X ⊆ Y → X ∪ Y = Y.
    Proof. unfold_leibniz. apply subseteq_union_1. Qed.
    Lemma subseteq_union_2_L X Y : X ∪ Y = Y → X ⊆ Y.
    Proof. unfold_leibniz. apply subseteq_union_2. Qed.

    (** Union *)
    Global Instance union_idemp_L : IdemP (=@{C}) (∪).
    Proof. intros ?. unfold_leibniz. apply (idemp _). Qed.
    Global Instance union_empty_l_L : LeftId (=@{C}) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (left_id _ _). Qed.
    Global Instance union_empty_r_L : RightId (=@{C}) ∅ (∪).
    Proof. intros ?. unfold_leibniz. apply (right_id _ _). Qed.
    Global Instance union_comm_L : Comm (=@{C}) (∪).
    Proof. intros ??. unfold_leibniz. apply (comm _). Qed.
    Global Instance union_assoc_L : Assoc (=@{C}) (∪).
    Proof. intros ???. unfold_leibniz. apply (assoc _). Qed.

    Lemma empty_union_L X Y : X ∪ Y = ∅ ↔ X = ∅ ∧ Y = ∅.
    Proof. unfold_leibniz. apply empty_union. Qed.

    Lemma union_cancel_l_L X Y Z : Z ## X → Z ## Y → Z ∪ X = Z ∪ Y → X = Y.
    Proof. unfold_leibniz. apply union_cancel_l. Qed.
    Lemma union_cancel_r_L X Y Z : X ## Z → Y ## Z → X ∪ Z = Y ∪ Z → X = Y.
    Proof. unfold_leibniz. apply union_cancel_r. Qed.

    (** Empty *)
    Lemma elem_of_equiv_empty_L X : X = ∅ ↔ ∀ x, x ∉ X.
    Proof. unfold_leibniz. apply elem_of_equiv_empty. Qed.
    Lemma equiv_empty_L X : X ⊆ ∅ → X = ∅.
    Proof. unfold_leibniz. apply equiv_empty. Qed.
    Lemma union_positive_l_L X Y : X ∪ Y = ∅ → X = ∅.
    Proof. unfold_leibniz. apply union_positive_l. Qed.
    Lemma union_positive_l_alt_L X Y : X ≠ ∅ → X ∪ Y ≠ ∅.
    Proof. unfold_leibniz. apply union_positive_l_alt. Qed.
    Lemma non_empty_inhabited_L x X : x ∈ X → X ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_inhabited. Qed.

    (** Singleton *)
    Lemma non_empty_singleton_L x : {[ x ]} ≠@{C} ∅.
    Proof. unfold_leibniz. apply non_empty_singleton. Qed.

    (** Big unions *)
    Lemma union_list_singleton_L X : ⋃ [X] = X.
    Proof. unfold_leibniz. apply union_list_singleton. Qed.
    Lemma union_list_app_L Xs1 Xs2 : ⋃ (Xs1 ++ Xs2) = ⋃ Xs1 ∪ ⋃ Xs2.
    Proof. unfold_leibniz. apply union_list_app. Qed.
    Lemma union_list_reverse_L Xs : ⋃ (reverse Xs) = ⋃ Xs.
    Proof. unfold_leibniz. apply union_list_reverse. Qed.

    Lemma empty_union_list_L Xs : ⋃ Xs = ∅ ↔ Forall (.= ∅) Xs.
    Proof. unfold_leibniz. apply empty_union_list. Qed.
  End leibniz.

  Lemma not_elem_of_iff `{!RelDecision (∈@{C})} X Y x :
    (x ∈ X ↔ x ∈ Y) ↔ (x ∉ X ↔ x ∉ Y).
  Proof. destruct (decide (x ∈ X)), (decide (x ∈ Y)); tauto. Qed.

  Section dec.
    Context `{!RelDecision (≡@{C})}.

    Lemma set_subseteq_inv X Y : X ⊆ Y → X ⊂ Y ∨ X ≡ Y.
    Proof. destruct (decide (X ≡ Y)); [by right|left;set_solver]. Qed.
    Lemma set_not_subset_inv X Y : X ⊄ Y → X ⊈ Y ∨ X ≡ Y.
    Proof. destruct (decide (X ≡ Y)); [by right|left;set_solver]. Qed.

    Lemma non_empty_union X Y : X ∪ Y ≢ ∅ ↔ X ≢ ∅ ∨ Y ≢ ∅.
    Proof. destruct (decide (X ≡ ∅)); set_solver. Qed.
    Lemma non_empty_union_list Xs : ⋃ Xs ≢ ∅ → Exists (.≢ ∅) Xs.
    Proof. rewrite empty_union_list. apply (not_Forall_Exists _). Qed.
  End dec.

  Section dec_leibniz.
    Context `{!RelDecision (≡@{C}), !LeibnizEquiv C}.

    Lemma set_subseteq_inv_L X Y : X ⊆ Y → X ⊂ Y ∨ X = Y.
    Proof. unfold_leibniz. apply set_subseteq_inv. Qed.
    Lemma set_not_subset_inv_L X Y : X ⊄ Y → X ⊈ Y ∨ X = Y.
    Proof. unfold_leibniz. apply set_not_subset_inv. Qed.

    Lemma non_empty_union_L X Y : X ∪ Y ≠ ∅ ↔ X ≠ ∅ ∨ Y ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_union. Qed.
    Lemma non_empty_union_list_L Xs : ⋃ Xs ≠ ∅ → Exists (.≠ ∅) Xs.
    Proof. unfold_leibniz. apply non_empty_union_list. Qed.
  End dec_leibniz.
End semi_set.


(** * Sets with [∪], [∩], [∖], [∅] and [{[_]}] *)
Section set.
  Context `{Set_ A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  (** Intersection *)
  Lemma subseteq_intersection X Y : X ⊆ Y ↔ X ∩ Y ≡ X.
  Proof. set_solver. Qed.
  Lemma subseteq_intersection_1 X Y : X ⊆ Y → X ∩ Y ≡ X.
  Proof. apply subseteq_intersection. Qed.
  Lemma subseteq_intersection_2 X Y : X ∩ Y ≡ X → X ⊆ Y.
  Proof. apply subseteq_intersection. Qed.

  Lemma intersection_subseteq_l X Y : X ∩ Y ⊆ X.
  Proof. set_solver. Qed.
  Lemma intersection_subseteq_r X Y : X ∩ Y ⊆ Y.
  Proof. set_solver. Qed.
  Lemma intersection_greatest X Y Z : Z ⊆ X → Z ⊆ Y → Z ⊆ X ∩ Y.
  Proof. set_solver. Qed.

  Lemma intersection_mono_l X Y1 Y2 : Y1 ⊆ Y2 → X ∩ Y1 ⊆ X ∩ Y2.
  Proof. set_solver. Qed.
  Lemma intersection_mono_r X1 X2 Y : X1 ⊆ X2 → X1 ∩ Y ⊆ X2 ∩ Y.
  Proof. set_solver. Qed.
  Lemma intersection_mono X1 X2 Y1 Y2 :
    X1 ⊆ X2 → Y1 ⊆ Y2 → X1 ∩ Y1 ⊆ X2 ∩ Y2.
  Proof. set_solver. Qed.

  Global Instance intersection_idemp : IdemP (≡@{C}) (∩).
  Proof. intros X; set_solver. Qed.
  Global Instance intersection_comm : Comm (≡@{C}) (∩).
  Proof. intros X Y; set_solver. Qed.
  Global Instance intersection_assoc : Assoc (≡@{C}) (∩).
  Proof. intros X Y Z; set_solver. Qed.
  Global Instance intersection_empty_l : LeftAbsorb (≡@{C}) ∅ (∩).
  Proof. intros X; set_solver. Qed.
  Global Instance intersection_empty_r: RightAbsorb (≡@{C}) ∅ (∩).
  Proof. intros X; set_solver. Qed.

  Lemma intersection_singletons x : {[x]} ∩ {[x]} ≡@{C} {[x]}.
  Proof. set_solver. Qed.

  Lemma union_intersection_l X Y Z : X ∪ (Y ∩ Z) ≡ (X ∪ Y) ∩ (X ∪ Z).
  Proof. set_solver. Qed.
  Lemma union_intersection_r X Y Z : (X ∩ Y) ∪ Z ≡ (X ∪ Z) ∩ (Y ∪ Z).
  Proof. set_solver. Qed.
  Lemma intersection_union_l X Y Z : X ∩ (Y ∪ Z) ≡ (X ∩ Y) ∪ (X ∩ Z).
  Proof. set_solver. Qed.
  Lemma intersection_union_r X Y Z : (X ∪ Y) ∩ Z ≡ (X ∩ Z) ∪ (Y ∩ Z).
  Proof. set_solver. Qed.

  (** Difference *)
  Lemma difference_twice X Y : (X ∖ Y) ∖ Y ≡ X ∖ Y.
  Proof. set_solver. Qed.
  Lemma subseteq_empty_difference X Y : X ⊆ Y → X ∖ Y ≡ ∅.
  Proof. set_solver. Qed.
  Lemma difference_diag X : X ∖ X ≡ ∅.
  Proof. set_solver. Qed.
  Lemma difference_empty X : X ∖ ∅ ≡ X.
  Proof. set_solver. Qed.
  Lemma difference_union_distr_l X Y Z : (X ∪ Y) ∖ Z ≡ X ∖ Z ∪ Y ∖ Z.
  Proof. set_solver. Qed.
  Lemma difference_union_distr_r X Y Z : Z ∖ (X ∪ Y) ≡ (Z ∖ X) ∩ (Z ∖ Y).
  Proof. set_solver. Qed.
  Lemma difference_intersection_distr_l X Y Z : (X ∩ Y) ∖ Z ≡ X ∖ Z ∩ Y ∖ Z.
  Proof. set_solver. Qed.
  Lemma difference_disjoint X Y : X ## Y → X ∖ Y ≡ X.
  Proof. set_solver. Qed.
  Lemma subset_difference_elem_of x X : x ∈ X → X ∖ {[ x ]} ⊂ X.
  Proof. set_solver. Qed.
  Lemma difference_difference_l X Y Z : (X ∖ Y) ∖ Z ≡ X ∖ (Y ∪ Z).
  Proof. set_solver. Qed.

  Lemma difference_mono X1 X2 Y1 Y2 :
    X1 ⊆ X2 → Y2 ⊆ Y1 → X1 ∖ Y1 ⊆ X2 ∖ Y2.
  Proof. set_solver. Qed.
  Lemma difference_mono_l X Y1 Y2 : Y2 ⊆ Y1 → X ∖ Y1 ⊆ X ∖ Y2.
  Proof. set_solver. Qed.
  Lemma difference_mono_r X1 X2 Y : X1 ⊆ X2 → X1 ∖ Y ⊆ X2 ∖ Y.
  Proof. set_solver. Qed.

  Lemma subseteq_difference_r X Y1 Y2 :
    X ## Y2 → X ⊆ Y1 → X ⊆ Y1 ∖ Y2.
  Proof. set_solver. Qed.
  Lemma subseteq_difference_l X1 X2 Y : X1 ⊆ Y → X1 ∖ X2 ⊆ Y.
  Proof. set_solver. Qed.

  (** Disjointness *)
  Lemma disjoint_intersection X Y : X ## Y ↔ X ∩ Y ≡ ∅.
  Proof. set_solver. Qed.
  Lemma disjoint_difference_l1 X1 X2 Y : Y ⊆ X2 → X1 ∖ X2 ## Y.
  Proof. set_solver. Qed.
  Lemma disjoint_difference_l2 X1 X2 Y : X1 ## Y → X1 ∖ X2 ## Y.
  Proof. set_solver. Qed.
  Lemma disjoint_difference_r1 X Y1 Y2 : X ⊆ Y2 → X ## Y1 ∖ Y2.
  Proof. set_solver. Qed.
  Lemma disjoint_difference_r2 X Y1 Y2 : X ## Y1 → X ## Y1 ∖ Y2.
  Proof. set_solver. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    (** Intersection *)
    Lemma subseteq_intersection_L X Y : X ⊆ Y ↔ X ∩ Y = X.
    Proof. unfold_leibniz. apply subseteq_intersection. Qed.
    Lemma subseteq_intersection_1_L X Y : X ⊆ Y → X ∩ Y = X.
    Proof. unfold_leibniz. apply subseteq_intersection_1. Qed.
    Lemma subseteq_intersection_2_L X Y : X ∩ Y = X → X ⊆ Y.
    Proof. unfold_leibniz. apply subseteq_intersection_2. Qed.

    Global Instance intersection_idemp_L : IdemP (=@{C}) (∩).
    Proof. intros ?. unfold_leibniz. apply (idemp _). Qed.
    Global Instance intersection_comm_L : Comm (=@{C}) (∩).
    Proof. intros ??. unfold_leibniz. apply (comm _). Qed.
    Global Instance intersection_assoc_L : Assoc (=@{C}) (∩).
    Proof. intros ???. unfold_leibniz. apply (assoc _). Qed.
    Global Instance intersection_empty_l_L: LeftAbsorb (=@{C}) ∅ (∩).
    Proof. intros ?. unfold_leibniz. apply (left_absorb _ _). Qed.
    Global Instance intersection_empty_r_L: RightAbsorb (=@{C}) ∅ (∩).
    Proof. intros ?. unfold_leibniz. apply (right_absorb _ _). Qed.

    Lemma intersection_singletons_L x : {[x]} ∩ {[x]} =@{C} {[x]}.
    Proof. unfold_leibniz. apply intersection_singletons. Qed.

    Lemma union_intersection_l_L X Y Z : X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z).
    Proof. unfold_leibniz; apply union_intersection_l. Qed.
    Lemma union_intersection_r_L X Y Z : (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z).
    Proof. unfold_leibniz; apply union_intersection_r. Qed.
    Lemma intersection_union_l_L X Y Z : X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z).
    Proof. unfold_leibniz; apply intersection_union_l. Qed.
    Lemma intersection_union_r_L X Y Z : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z).
    Proof. unfold_leibniz; apply intersection_union_r. Qed.

    (** Difference *)
    Lemma difference_twice_L X Y : (X ∖ Y) ∖ Y = X ∖ Y.
    Proof. unfold_leibniz. apply difference_twice. Qed.
    Lemma subseteq_empty_difference_L X Y : X ⊆ Y → X ∖ Y = ∅.
    Proof. unfold_leibniz. apply subseteq_empty_difference. Qed.
    Lemma difference_diag_L X : X ∖ X = ∅.
    Proof. unfold_leibniz. apply difference_diag. Qed.
    Lemma difference_empty_L X : X ∖ ∅ = X.
    Proof. unfold_leibniz. apply difference_empty. Qed.
    Lemma difference_union_distr_l_L X Y Z : (X ∪ Y) ∖ Z = X ∖ Z ∪ Y ∖ Z.
    Proof. unfold_leibniz. apply difference_union_distr_l. Qed.
    Lemma difference_union_distr_r_L X Y Z : Z ∖ (X ∪ Y) = (Z ∖ X) ∩ (Z ∖ Y).
    Proof. unfold_leibniz. apply difference_union_distr_r. Qed.
    Lemma difference_intersection_distr_l_L X Y Z :
      (X ∩ Y) ∖ Z = X ∖ Z ∩ Y ∖ Z.
    Proof. unfold_leibniz. apply difference_intersection_distr_l. Qed.
    Lemma difference_disjoint_L X Y : X ## Y → X ∖ Y = X.
    Proof. unfold_leibniz. apply difference_disjoint. Qed.
    Lemma difference_difference_l_L X Y Z : (X ∖ Y) ∖ Z = X ∖ (Y ∪ Z).
    Proof. unfold_leibniz. apply difference_difference_l. Qed.

    (** Disjointness *)
    Lemma disjoint_intersection_L X Y : X ## Y ↔ X ∩ Y = ∅.
    Proof. unfold_leibniz. apply disjoint_intersection. Qed.
  End leibniz.

  Section dec.
    Context `{!RelDecision (∈@{C})}.

    Lemma not_elem_of_intersection x X Y : x ∉ X ∩ Y ↔ x ∉ X ∨ x ∉ Y.
    Proof. rewrite elem_of_intersection. destruct (decide (x ∈ X)); tauto. Qed.
    Lemma not_elem_of_difference x X Y : x ∉ X ∖ Y ↔ x ∉ X ∨ x ∈ Y.
    Proof. rewrite elem_of_difference. destruct (decide (x ∈ Y)); tauto. Qed.
    Lemma union_difference X Y : X ⊆ Y → Y ≡ X ∪ Y ∖ X.
    Proof.
      intros ? x; split; rewrite !elem_of_union, elem_of_difference; [|intuition].
      destruct (decide (x ∈ X)); intuition.
    Qed.
    Lemma union_difference_singleton x Y : x ∈ Y → Y ≡ {[x]} ∪ Y ∖ {[x]}.
    Proof. intros ?. apply union_difference. set_solver. Qed.
    Lemma difference_union X Y : X ∖ Y ∪ Y ≡ X ∪ Y.
    Proof.
      intros x. rewrite !elem_of_union; rewrite elem_of_difference.
      split; [ | destruct (decide (x ∈ Y)) ]; intuition.
    Qed.
    Lemma difference_difference_r X Y Z : X ∖ (Y ∖ Z) ≡ (X ∖ Y) ∪ (X ∩ Z).
    Proof. intros x. destruct (decide (x ∈ Z)); set_solver. Qed.

    Lemma subseteq_disjoint_union X Y : X ⊆ Y ↔ ∃ Z, Y ≡ X ∪ Z ∧ X ## Z.
    Proof.
      split; [|set_solver].
      exists (Y ∖ X); split; [auto using union_difference|set_solver].
    Qed.
    Lemma non_empty_difference X Y : X ⊂ Y → Y ∖ X ≢ ∅.
    Proof. intros [HXY1 HXY2] Hdiff. destruct HXY2. set_solver. Qed.
    Lemma empty_difference_subseteq X Y : X ∖ Y ≡ ∅ → X ⊆ Y.
    Proof. set_solver. Qed.
    Lemma singleton_union_difference X Y x :
      {[x]} ∪ (X ∖ Y) ≡ ({[x]} ∪ X) ∖ (Y ∖ {[x]}).
    Proof. intro y; destruct (decide (y ∈@{C} {[x]})); set_solver. Qed.
  End dec.

  Section dec_leibniz.
    Context `{!RelDecision (∈@{C}), !LeibnizEquiv C}.

    Lemma union_difference_L X Y : X ⊆ Y → Y = X ∪ Y ∖ X.
    Proof. unfold_leibniz. apply union_difference. Qed.
    Lemma union_difference_singleton_L x Y : x ∈ Y → Y = {[x]} ∪ Y ∖ {[x]}.
    Proof. unfold_leibniz. apply union_difference_singleton. Qed.
    Lemma difference_union_L X Y : X ∖ Y ∪ Y = X ∪ Y.
    Proof. unfold_leibniz. apply difference_union. Qed.
    Lemma non_empty_difference_L X Y : X ⊂ Y → Y ∖ X ≠ ∅.
    Proof. unfold_leibniz. apply non_empty_difference. Qed.
    Lemma empty_difference_subseteq_L X Y : X ∖ Y = ∅ → X ⊆ Y.
    Proof. unfold_leibniz. apply empty_difference_subseteq. Qed.
    Lemma subseteq_disjoint_union_L X Y : X ⊆ Y ↔ ∃ Z, Y = X ∪ Z ∧ X ## Z.
    Proof. unfold_leibniz. apply subseteq_disjoint_union. Qed.
    Lemma singleton_union_difference_L X Y x :
      {[x]} ∪ (X ∖ Y) = ({[x]} ∪ X) ∖ (Y ∖ {[x]}).
    Proof. unfold_leibniz. apply singleton_union_difference. Qed.
    Lemma difference_difference_r_L X Y Z : X ∖ (Y ∖ Z) = (X ∖ Y) ∪ (X ∩ Z).
    Proof. unfold_leibniz. apply difference_difference_r. Qed.

  End dec_leibniz.
End set.


(** * Sets with [∪], [∩], [∖], [∅], [{[_]}], and [⊤] *)
Section top_set.
  Context `{TopSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.

  Lemma elem_of_top x : x ∈@{C} ⊤ ↔ True.
  Proof. split; [done|intros; apply elem_of_top']. Qed.
  Lemma top_subseteq X : X ⊆ ⊤.
  Proof. intros x. by rewrite elem_of_top. Qed.
End top_set.


(** * Conversion of option and list *)
Section option_and_list_to_set.
  Context `{SemiSet A C}.
  Implicit Types l : list A.

  Lemma elem_of_option_to_set (x : A) mx: x ∈ option_to_set (C:=C) mx ↔ mx = Some x.
  Proof. destruct mx; set_solver. Qed.
  Lemma not_elem_of_option_to_set (x : A) mx: x ∉ option_to_set (C:=C) mx ↔ mx ≠ Some x.
  Proof. by rewrite elem_of_option_to_set. Qed.

  Lemma elem_of_list_to_set (x : A) l : x ∈ list_to_set (C:=C) l ↔ x ∈ l.
  Proof.
    split.
    - induction l; simpl; [by rewrite elem_of_empty|].
      rewrite elem_of_union,elem_of_singleton; intros [->|?]; constructor; auto.
    - induction 1; simpl; rewrite elem_of_union, elem_of_singleton; auto.
  Qed.
  Lemma not_elem_of_list_to_set (x : A) l : x ∉ list_to_set (C:=C) l ↔ x ∉ l.
  Proof. by rewrite elem_of_list_to_set. Qed.

  Global Instance set_unfold_option_to_set (mx : option A) x :
    SetUnfoldElemOf x (option_to_set (C:=C) mx) (mx = Some x).
  Proof. constructor; apply elem_of_option_to_set. Qed.
  Global Instance set_unfold_list_to_set (l : list A) x P :
    SetUnfoldElemOf x l P → SetUnfoldElemOf x (list_to_set (C:=C) l) P.
  Proof. constructor. by rewrite elem_of_list_to_set, (set_unfold (x ∈ l) P). Qed.

  Lemma list_to_set_nil : list_to_set [] =@{C} ∅.
  Proof. done. Qed.
  Lemma list_to_set_cons x l : list_to_set (x :: l) =@{C} {[ x ]} ∪ list_to_set l.
  Proof. done. Qed.
  Lemma list_to_set_app l1 l2 : list_to_set (l1 ++ l2) ≡@{C} list_to_set l1 ∪ list_to_set l2.
  Proof. set_solver. Qed.
  Lemma list_to_set_singleton x : list_to_set [x] ≡@{C} {[ x ]}.
  Proof. set_solver. Qed.
  Lemma list_to_set_snoc l x : list_to_set (l ++ [x]) ≡@{C} list_to_set l ∪ {[ x ]}.
  Proof. set_solver. Qed.
  Global Instance list_to_set_perm : Proper ((≡ₚ) ==> (≡)) (list_to_set (C:=C)).
  Proof. induction 1; set_solver. Qed.

  Section leibniz.
    Context `{!LeibnizEquiv C}.

    Lemma list_to_set_app_L l1 l2 :
      list_to_set (l1 ++ l2) =@{C} list_to_set l1 ∪ list_to_set l2.
    Proof. set_solver. Qed.
    Global Instance list_to_set_perm_L : Proper ((≡ₚ) ==> (=)) (list_to_set (C:=C)).
    Proof. induction 1; set_solver. Qed.
  End leibniz.
End option_and_list_to_set.

(** * Finite types to sets. *)
Definition fin_to_set (A : Type) `{Singleton A C, Empty C, Union C, Finite A} : C :=
  list_to_set (enum A).

Section fin_to_set.
  Context `{SemiSet A C, Finite A}.
  Implicit Types a : A.

  Lemma elem_of_fin_to_set a : a ∈@{C} fin_to_set A.
  Proof. apply elem_of_list_to_set, elem_of_enum. Qed.

  Global Instance set_unfold_fin_to_set a :
    SetUnfoldElemOf (C:=C) a (fin_to_set A) True.
  Proof. constructor. split; auto using elem_of_fin_to_set. Qed.
End fin_to_set.

(** * Guard *)
Global Instance set_guard `{MonadSet M} : MGuard M :=
  λ P dec A x, match dec with left H => x H | _ => ∅ end.

Section set_monad_base.
  Context `{MonadSet M}.

  Lemma elem_of_guard `{Decision P} {A} (x : A) (X : M A) :
    (x ∈ guard P; X) ↔ P ∧ x ∈ X.
  Proof.
    unfold mguard, set_guard; simpl; case_match;
      rewrite ?elem_of_empty; naive_solver.
  Qed.
  Lemma elem_of_guard_2 `{Decision P} {A} (x : A) (X : M A) :
    P → x ∈ X → x ∈ guard P; X.
  Proof. by rewrite elem_of_guard. Qed.
  Lemma guard_empty `{Decision P} {A} (X : M A) : (guard P; X) ≡ ∅ ↔ ¬P ∨ X ≡ ∅.
  Proof.
    rewrite !elem_of_equiv_empty; setoid_rewrite elem_of_guard.
    destruct (decide P); naive_solver.
  Qed.
  Global Instance set_unfold_guard `{Decision P} {A} (x : A) (X : M A) Q :
    SetUnfoldElemOf x X Q → SetUnfoldElemOf x (guard P; X) (P ∧ Q).
  Proof. constructor. by rewrite elem_of_guard, (set_unfold (x ∈ X) Q). Qed.
  Lemma bind_empty {A B} (f : A → M B) X :
    X ≫= f ≡ ∅ ↔ X ≡ ∅ ∨ ∀ x, x ∈ X → f x ≡ ∅.
  Proof. set_solver. Qed.
End set_monad_base.


(** * Quantifiers *)
Definition set_Forall `{ElemOf A C} (P : A → Prop) (X : C) := ∀ x, x ∈ X → P x.
Definition set_Exists `{ElemOf A C} (P : A → Prop) (X : C) := ∃ x, x ∈ X ∧ P x.

Section quantifiers.
  Context `{SemiSet A C} (P : A → Prop).
  Implicit Types X Y : C.

  Global Instance set_unfold_set_Forall X (QX QP : A → Prop) :
    (∀ x, SetUnfoldElemOf x X (QX x)) →
    (∀ x, SetUnfold (P x) (QP x)) →
    SetUnfold (set_Forall P X) (∀ x, QX x → QP x).
  Proof.
    intros HX HP; constructor. unfold set_Forall. apply forall_proper; intros x.
    by rewrite (set_unfold (x ∈ X) _), (set_unfold (P x) _).
  Qed.
  Global Instance set_unfold_set_Exists X (QX QP : A → Prop) :
    (∀ x, SetUnfoldElemOf x X (QX x)) →
    (∀ x, SetUnfold (P x) (QP x)) →
    SetUnfold (set_Exists P X) (∃ x, QX x ∧ QP x).
  Proof.
    intros HX HP; constructor. unfold set_Exists. f_equiv; intros x.
    by rewrite (set_unfold (x ∈ X) _), (set_unfold (P x) _).
  Qed.

  Lemma set_Forall_empty : set_Forall P (∅ : C).
  Proof. set_solver. Qed.
  Lemma set_Forall_singleton x : set_Forall P ({[ x ]} : C) ↔ P x.
  Proof. set_solver. Qed.
  Lemma set_Forall_union X Y :
    set_Forall P X → set_Forall P Y → set_Forall P (X ∪ Y).
  Proof. set_solver. Qed.
  Lemma set_Forall_union_inv_1 X Y : set_Forall P (X ∪ Y) → set_Forall P X.
  Proof. set_solver. Qed.
  Lemma set_Forall_union_inv_2 X Y : set_Forall P (X ∪ Y) → set_Forall P Y.
  Proof. set_solver. Qed.
  Lemma set_Forall_list_to_set l : set_Forall P (list_to_set (C:=C) l) ↔ Forall P l.
  Proof. rewrite Forall_forall. set_solver. Qed.

  Lemma set_Exists_empty : ¬set_Exists P (∅ : C).
  Proof. set_solver. Qed.
  Lemma set_Exists_singleton x : set_Exists P ({[ x ]} : C) ↔ P x.
  Proof. set_solver. Qed.
  Lemma set_Exists_union_1 X Y : set_Exists P X → set_Exists P (X ∪ Y).
  Proof. set_solver. Qed.
  Lemma set_Exists_union_2 X Y : set_Exists P Y → set_Exists P (X ∪ Y).
  Proof. set_solver. Qed.
  Lemma set_Exists_union_inv X Y :
    set_Exists P (X ∪ Y) → set_Exists P X ∨ set_Exists P Y.
  Proof. set_solver. Qed.
  Lemma set_Exists_list_to_set l : set_Exists P (list_to_set (C:=C) l) ↔ Exists P l.
  Proof. rewrite Exists_exists. set_solver. Qed.
End quantifiers.

Section more_quantifiers.
  Context `{SemiSet A C}.
  Implicit Types X : C.

  Lemma set_Forall_impl (P Q : A → Prop) X :
    set_Forall P X → (∀ x, P x → Q x) → set_Forall Q X.
  Proof. set_solver. Qed.
  Lemma set_Exists_impl (P Q : A → Prop) X :
    set_Exists P X → (∀ x, P x → Q x) → set_Exists Q X.
  Proof. set_solver. Qed.
End more_quantifiers.

(** * Properties of implementations of sets that form a monad *)
Section set_monad.
  Context `{MonadSet M}.

  Global Instance set_fmap_mono {A B} :
    Proper (pointwise_relation _ (=) ==> (⊆) ==> (⊆)) (@fmap M _ A B).
  Proof. intros f g ? X Y ?; set_solver by eauto. Qed.
  Global Instance set_bind_mono {A B} :
    Proper (pointwise_relation _ (⊆) ==> (⊆) ==> (⊆)) (@mbind M _ A B).
  Proof. unfold respectful, pointwise_relation; intros f g Hfg X Y ?. set_solver. Qed.
  Global Instance set_join_mono {A} :
    Proper ((⊆) ==> (⊆)) (@mjoin M _ A).
  Proof. intros X Y ?; set_solver. Qed.

  Lemma set_bind_singleton {A B} (f : A → M B) x : {[ x ]} ≫= f ≡ f x.
  Proof. set_solver. Qed.
  Lemma set_guard_True {A} `{Decision P} (X : M A) : P → (guard P; X) ≡ X.
  Proof. set_solver. Qed.
  Lemma set_fmap_compose {A B C} (f : A → B) (g : B → C) (X : M A) :
    g ∘ f <$> X ≡ g <$> (f <$> X).
  Proof. set_solver. Qed.
  Lemma elem_of_fmap_1 {A B} (f : A → B) (X : M A) (y : B) :
    y ∈ f <$> X → ∃ x, y = f x ∧ x ∈ X.
  Proof. set_solver. Qed.
  Lemma elem_of_fmap_2 {A B} (f : A → B) (X : M A) (x : A) :
    x ∈ X → f x ∈ f <$> X.
  Proof. set_solver. Qed.
  Lemma elem_of_fmap_2_alt {A B} (f : A → B) (X : M A) (x : A) (y : B) :
    x ∈ X → y = f x → y ∈ f <$> X.
  Proof. set_solver. Qed.

  Lemma elem_of_mapM {A B} (f : A → M B) l k :
    l ∈ mapM f k ↔ Forall2 (λ x y, x ∈ f y) l k.
  Proof.
    split.
    - revert l. induction k; set_solver by eauto.
    - induction 1; set_solver.
  Qed.
  Lemma set_mapM_length {A B} (f : A → M B) l k :
    l ∈ mapM f k → length l = length k.
  Proof. revert l; induction k; set_solver by eauto. Qed.
  Lemma elem_of_mapM_fmap {A B} (f : A → B) (g : B → M A) l k :
    Forall (λ x, ∀ y, y ∈ g x → f y = x) l → k ∈ mapM g l → fmap f k = l.
  Proof. intros Hl. revert k. induction Hl; set_solver. Qed.
  Lemma elem_of_mapM_Forall {A B} (f : A → M B) (P : B → Prop) l k :
    l ∈ mapM f k → Forall (λ x, ∀ y, y ∈ f x → P y) k → Forall P l.
  Proof. rewrite elem_of_mapM. apply Forall2_Forall_l. Qed.
  Lemma elem_of_mapM_Forall2_l {A B C} (f : A → M B) (P: B → C → Prop) l1 l2 k :
    l1 ∈ mapM f k → Forall2 (λ x y, ∀ z, z ∈ f x → P z y) k l2 →
    Forall2 P l1 l2.
  Proof.
    rewrite elem_of_mapM. intros Hl1. revert l2.
    induction Hl1; inversion_clear 1; constructor; auto.
  Qed.
End set_monad.

(** Finite sets *)
Definition pred_finite {A} (P : A → Prop) := ∃ xs : list A, ∀ x, P x → x ∈ xs.
Definition set_finite `{ElemOf A B} (X : B) := pred_finite (.∈ X).

Definition pred_infinite {A} (P : A → Prop) := ∀ xs : list A, ∃ x, P x ∧ x ∉ xs.
Definition set_infinite `{ElemOf A C} (X : C) := pred_infinite (.∈ X).

Section pred_finite_infinite.
  Lemma pred_finite_impl {A} (P Q : A → Prop) :
    pred_finite P → (∀ x, Q x → P x) → pred_finite Q.
  Proof. unfold pred_finite. set_solver. Qed.

  Lemma pred_infinite_impl {A} (P Q : A → Prop) :
    pred_infinite P → (∀ x, P x → Q x) → pred_infinite Q.
  Proof. unfold pred_infinite. set_solver. Qed.

  (** If [f] is surjective onto [P], then pre-composing with [f] preserves
  infinity. *)
  Lemma pred_infinite_surj {A B} (P : B → Prop) (f : A → B) :
    (∀ x, P x → ∃ y, f y = x) →
    pred_infinite P → pred_infinite (P ∘ f).
  Proof.
    intros Hf HP xs. destruct (HP (f <$> xs)) as [x [HPx Hx]].
    destruct (Hf _ HPx) as [y Hf']. exists y. split.
    - simpl. rewrite Hf'. done.
    - intros Hy. apply Hx. apply elem_of_list_fmap. eauto.
  Qed.

  Lemma pred_not_infinite_finite {A} (P : A → Prop) :
    pred_infinite P → pred_finite P → False.
  Proof. intros Hinf [xs ?]. destruct (Hinf xs). set_solver. Qed.

  Lemma pred_infinite_True `{Infinite A} : pred_infinite (λ _: A, True).
  Proof.
    intros xs. exists (fresh xs). split; [done|]. apply infinite_is_fresh.
  Qed.

  Lemma pred_finite_lt n : pred_finite (flip lt n).
  Proof.
    exists (seq 0 n); intros i Hi. apply (elem_of_list_lookup_2 _ i).
    by rewrite lookup_seq.
  Qed.
  Lemma pred_infinite_lt n : pred_infinite (lt n).
  Proof.
    intros l. exists (S (n `max` max_list l)). split; [lia| ].
    intros H%max_list_elem_of_le; lia.
  Qed.

  Lemma pred_finite_le n : pred_finite (flip le n).
  Proof. eapply pred_finite_impl; [apply (pred_finite_lt (S n))|]; naive_solver lia. Qed.
  Lemma pred_infinite_le n : pred_infinite (le n).
  Proof. eapply pred_infinite_impl; [apply (pred_infinite_lt (S n))|]; naive_solver lia. Qed.
End pred_finite_infinite.

Section set_finite_infinite.
  Context `{SemiSet A C}.
  Implicit Types X Y : C.

  Lemma set_not_infinite_finite X : set_infinite X → set_finite X → False.
  Proof. apply pred_not_infinite_finite. Qed.

  Global Instance set_finite_subseteq :
    Proper (flip (⊆) ==> impl) (@set_finite A C _).
  Proof. intros X Y HX ?. eapply pred_finite_impl; set_solver. Qed.
  Global Instance set_finite_proper : Proper ((≡) ==> iff) (@set_finite A C _).
  Proof. intros X Y HX; apply exist_proper. by setoid_rewrite HX. Qed.

  Lemma empty_finite : set_finite (∅ : C).
  Proof. by exists []; intros ?; rewrite elem_of_empty. Qed.
  Lemma singleton_finite (x : A) : set_finite ({[ x ]} : C).
  Proof. exists [x]; intros y ->%elem_of_singleton; left. Qed.
  Lemma union_finite X Y : set_finite X → set_finite Y → set_finite (X ∪ Y).
  Proof.
    intros [lX ?] [lY ?]; exists (lX ++ lY); intros x.
    rewrite elem_of_union, elem_of_app; naive_solver.
  Qed.
  Lemma union_finite_inv_l X Y : set_finite (X ∪ Y) → set_finite X.
  Proof. intros [l ?]; exists l; set_solver. Qed.
  Lemma union_finite_inv_r X Y : set_finite (X ∪ Y) → set_finite Y.
  Proof. intros [l ?]; exists l; set_solver. Qed.
  Lemma list_to_set_finite l : set_finite (list_to_set (C:=C) l).
  Proof. exists l. intros x. by rewrite elem_of_list_to_set. Qed.

  Global Instance set_infinite_subseteq :
    Proper ((⊆) ==> impl) (@set_infinite A C _).
  Proof. intros X Y HX ?. eapply pred_infinite_impl; set_solver. Qed.
  Global Instance set_infinite_proper : Proper ((≡) ==> iff) (@set_infinite A C _).
  Proof. intros X Y HX; apply forall_proper. by setoid_rewrite HX. Qed.

  Lemma union_infinite_l X Y : set_infinite X → set_infinite (X ∪ Y).
  Proof. intros Hinf xs. destruct (Hinf xs). set_solver. Qed.
  Lemma union_infinite_r X Y : set_infinite Y → set_infinite (X ∪ Y).
  Proof. intros Hinf xs. destruct (Hinf xs). set_solver. Qed.
End set_finite_infinite.

Section more_finite.
  Context `{Set_ A C}.
  Implicit Types X Y : C.

  Lemma intersection_finite_l X Y : set_finite X → set_finite (X ∩ Y).
  Proof. intros [l ?]; exists l; intros x [??]%elem_of_intersection; auto. Qed.
  Lemma intersection_finite_r X Y : set_finite Y → set_finite (X ∩ Y).
  Proof. intros [l ?]; exists l; intros x [??]%elem_of_intersection; auto. Qed.
  Lemma difference_finite X Y : set_finite X → set_finite (X ∖ Y).
  Proof. intros [l ?]; exists l; intros x [??]%elem_of_difference; auto. Qed.
  Lemma difference_finite_inv X Y `{∀ x, Decision (x ∈ Y)} :
    set_finite Y → set_finite (X ∖ Y) → set_finite X.
  Proof.
    intros [l ?] [k ?]; exists (l ++ k).
    intros x ?; destruct (decide (x ∈ Y)); rewrite elem_of_app; set_solver.
  Qed.

  Lemma difference_infinite X Y :
    set_infinite X → set_finite Y → set_infinite (X ∖ Y).
  Proof. intros Hinf [xs ?] xs'. destruct (Hinf (xs ++ xs')). set_solver. Qed.
End more_finite.

Lemma top_infinite `{TopSet A C, Infinite A} : set_infinite (⊤ : C).
Proof.
  intros xs. exists (fresh xs). split; [set_solver|]. apply infinite_is_fresh.
Qed.

(** This formulation of finiteness is stronger than [pred_finite]: when equality
    is decidable, it is equivalent to the predicate being finite AND decidable. *)
Lemma dec_pred_finite_alt {A} (P : A → Prop) `{!∀ x, Decision (P x)} :
  pred_finite P ↔ ∃ xs : list A, ∀ x, P x ↔ x ∈ xs.
Proof.
  split; intros [xs ?].
  - exists (filter P xs). intros x. rewrite elem_of_list_filter. naive_solver.
  - exists xs. naive_solver.
Qed.

Lemma finite_sig_pred_finite {A} (P : A → Prop) `{Finite (sig P)} :
  pred_finite P.
Proof.
  exists (proj1_sig <$> enum _). intros x px.
  apply elem_of_list_fmap_1_alt with (x ↾ px); [apply elem_of_enum|]; done.
Qed.

Lemma pred_finite_arg2 {A B} (P : A → B → Prop) x :
  pred_finite (uncurry P) → pred_finite (P x).
Proof.
  intros [xys ?]. exists (xys.*2). intros y ?.
  apply elem_of_list_fmap_1_alt with (x, y); by auto.
Qed.

Lemma pred_finite_arg1 {A B} (P : A → B → Prop) y :
  pred_finite (uncurry P) → pred_finite (flip P y).
Proof.
  intros [xys ?]. exists (xys.*1). intros x ?.
  apply elem_of_list_fmap_1_alt with (x, y); by auto.
Qed.

(** Sets of sequences of natural numbers *)
(* The set [seq_seq start len] of natural numbers contains the sequence
[start, start + 1, ..., start + (len-1)]. *)
Fixpoint set_seq `{Singleton nat C, Union C, Empty C} (start len : nat) : C :=
  match len with
  | O => ∅
  | S len' => {[ start ]} ∪ set_seq (S start) len'
  end.

Section set_seq.
  Context `{SemiSet nat C}.
  Implicit Types start len x : nat.

  Lemma elem_of_set_seq start len x :
    x ∈ set_seq (C:=C) start len ↔ start ≤ x < start + len.
  Proof.
    revert start. induction len as [|len IH]; intros start; simpl.
    - rewrite elem_of_empty. lia.
    - rewrite elem_of_union, elem_of_singleton, IH. lia.
  Qed.
  Global Instance set_unfold_seq start len x :
    SetUnfoldElemOf x (set_seq (C:=C) start len) (start ≤ x < start + len).
  Proof. constructor; apply elem_of_set_seq. Qed.

  Lemma set_seq_len_pos n start len : n ∈ set_seq (C:=C) start len → 0 < len.
  Proof. rewrite elem_of_set_seq. lia. Qed.

  Lemma set_seq_subseteq start1 len1 start2 len2 :
    0 < len1 →
    set_seq (C:=C) start1 len1 ⊆ set_seq (C:=C) start2 len2 ↔
      start2 ≤ start1 ∧ start1 + len1 ≤ start2 + len2.
  Proof.
    intros Hlen. set_unfold. split.
    - intros Hx. pose proof (Hx start1). pose proof (Hx (start1 + len1 - 1)). lia.
    - intros Heq x. lia.
  Qed.

  Lemma set_seq_subseteq_len_gt start1 len1 start2 len2 :
    set_seq (C:=C) start1 len1 ⊆ set_seq (C:=C) start2 len2 → len1 ≤ len2.
  Proof.
    destruct len1 as [|len1].
    - set_unfold. lia.
    - rewrite set_seq_subseteq; lia.
  Qed.

  Lemma set_seq_add_disjoint start len1 len2 :
    set_seq (C:=C) start len1 ## set_seq (start + len1) len2.
  Proof. set_solver by lia. Qed.
  Lemma set_seq_add start len1 len2 :
    set_seq (C:=C) start (len1 + len2)
    ≡ set_seq start len1 ∪ set_seq (start + len1) len2.
  Proof. set_solver by lia. Qed.
  Lemma set_seq_add_L `{!LeibnizEquiv C} start len1 len2 :
    set_seq (C:=C) start (len1 + len2)
    = set_seq start len1 ∪ set_seq (start + len1) len2.
  Proof. unfold_leibniz. apply set_seq_add. Qed.

  Lemma set_seq_S_start_disjoint start len :
    {[ start ]} ## set_seq (C:=C) (S start) len.
  Proof. set_solver by lia. Qed.
  Lemma set_seq_S_start start len :
    set_seq (C:=C) start (S len) ≡ {[ start ]} ∪ set_seq (S start) len.
  Proof. set_solver by lia. Qed.

  Lemma set_seq_S_end_disjoint start len :
    {[ start + len ]} ## set_seq (C:=C) start len.
  Proof. set_solver by lia. Qed.
  Lemma set_seq_S_end_union start len :
    set_seq start (S len) ≡@{C} {[ start + len ]} ∪ set_seq start len.
  Proof. set_solver by lia. Qed.
  Lemma set_seq_S_end_union_L `{!LeibnizEquiv C} start len :
    set_seq start (S len) =@{C} {[ start + len ]} ∪ set_seq start len.
  Proof. unfold_leibniz. apply set_seq_S_end_union. Qed.

  Lemma list_to_set_seq start len :
    list_to_set (seq start len) =@{C} set_seq start len.
  Proof. revert start; induction len; intros; f_equal/=; auto. Qed.

  Lemma set_seq_finite start len : set_finite (set_seq (C:=C) start len).
  Proof.
    exists (seq start len); intros x. rewrite <-list_to_set_seq. set_solver.
  Qed.
End set_seq.

(** Mimimal elements *)
Definition minimal `{ElemOf A C} (R : relation A) (x : A) (X : C) : Prop :=
  ∀ y, y ∈ X → R y x → R x y.
Global Instance: Params (@minimal) 5 := {}.
Global Typeclasses Opaque minimal.

Section minimal.
  Context `{SemiSet A C} {R : relation A}.
  Implicit Types X Y : C.

  Global Instance minimal_proper x : Proper ((≡@{C}) ==> iff) (minimal R x).
  Proof. intros X X' y; unfold minimal; set_solver. Qed.

  Lemma minimal_anti_symm_1 `{!AntiSymm (=) R} X x y :
    minimal R x X → y ∈ X → R y x → x = y.
  Proof. intros Hmin ??. apply (anti_symm _); auto. Qed.
  Lemma minimal_anti_symm `{!AntiSymm (=) R} X x :
    minimal R x X ↔ ∀ y, y ∈ X → R y x → x = y.
  Proof. unfold minimal; naive_solver eauto using minimal_anti_symm_1. Qed.

  Lemma minimal_strict_1 `{!StrictOrder R} X x y :
    minimal R x X → y ∈ X → ¬R y x.
  Proof. intros Hmin ??. destruct (irreflexivity R x); trans y; auto. Qed.
  Lemma minimal_strict `{!StrictOrder R} X x :
    minimal R x X ↔ ∀ y, y ∈ X → ¬R y x.
  Proof. unfold minimal; split; [eauto using minimal_strict_1|naive_solver]. Qed.

  Lemma empty_minimal x : minimal R x (∅ : C).
  Proof. unfold minimal; set_solver. Qed.
  Lemma singleton_minimal x : minimal R x ({[ x ]} : C).
  Proof. unfold minimal; set_solver. Qed.
  Lemma singleton_minimal_not_above y x : ¬R y x → minimal R x ({[ y ]} : C).
  Proof. unfold minimal; set_solver. Qed.
  Lemma union_minimal X Y x :
    minimal R x X → minimal R x Y → minimal R x (X ∪ Y).
  Proof. unfold minimal; set_solver. Qed.
  Lemma minimal_subseteq X Y x : minimal R x X → Y ⊆ X → minimal R x Y.
  Proof. unfold minimal; set_solver. Qed.

  Lemma minimal_weaken `{!Transitive R} X x x' :
    minimal R x X → R x' x → minimal R x' X.
  Proof.
    intros Hmin ? y ??. trans x; [done|]. by eapply (Hmin y), transitivity.
  Qed.
End minimal.
