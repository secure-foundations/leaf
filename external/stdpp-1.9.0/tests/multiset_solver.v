From stdpp Require Import gmultiset sets.

Section test.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  Lemma test_eq_1 x y X : {[+ x; y +]} ⊎ X = {[+ y; x +]} ⊎ X.
  Proof. multiset_solver. Qed.
  Lemma test_eq_2 x y z X Y :
    {[+ z +]} ⊎ X = {[+ y +]} ⊎ Y →
    {[+ x; z +]} ⊎ X = {[+ y; x +]} ⊎ Y.
  Proof. multiset_solver. Qed.
  Lemma test_eq_3 x :
    {[+ x; x +]} =@{gmultiset _} 2 *: {[+ x +]}.
  Proof. multiset_solver. Qed.
  Lemma test_eq_4 x y :
    {[+ x; y; x +]} =@{gmultiset _} 2 *: {[+ x +]} ⊎ {[+ y +]}.
  Proof. multiset_solver. Qed.

  Lemma test_neq_1 x y X : {[+ x; y +]} ⊎ X ≠ ∅.
  Proof. multiset_solver. Qed.
  Lemma test_neq_2 x : {[+ x +]} ⊎ ∅ ≠@{gmultiset A} ∅.
  Proof. multiset_solver. Qed.
  Lemma test_neq_3 X x : X ⊎ ∅ = {[+ x +]} → X ⊎ ∅ ≠@{gmultiset A} ∅.
  Proof. multiset_solver. Qed.
  Lemma test_neq_4 x y : {[+ x +]} ∖ {[+ y +]} ≠@{gmultiset A} ∅ → x ≠ y.
  Proof. multiset_solver. Qed.
  Lemma test_neq_5 x y Y : y ∈ Y → {[+ x +]} ∖ Y ≠ ∅ → x ≠ y.
  Proof. multiset_solver. Qed.

  Lemma test_multiplicity_1 x X Y :
    2 < multiplicity x X → X ⊆ Y → 1 < multiplicity x Y.
  Proof. multiset_solver. Qed.
  Lemma test_multiplicity_2 x X :
    2 < multiplicity x X → {[+ x; x; x +]} ⊆ X.
  Proof. multiset_solver. Qed.
  Lemma test_multiplicity_3 x X :
    multiplicity x X < 3 → {[+ x; x; x +]} ⊈ X.
  Proof. multiset_solver. Qed.
  Lemma test_multiplicity_4 x X :
    2 < multiplicity x X → 3 *: {[+ x +]} ⊆ X.
  Proof. multiset_solver. Qed.
  Lemma test_multiplicity_5 x X :
    multiplicity x X < 3 → 3 *: {[+ x +]} ⊈ X.
  Proof. multiset_solver. Qed.

  Lemma test_elem_of_1 x X : x ∈ X ↔ {[+ x +]} ⊎ ∅ ⊆ X.
  Proof. multiset_solver. Qed.
  Lemma test_elem_of_2 x X : x ∈ X ↔ {[+ x +]} ∪ ∅ ⊆ X.
  Proof. multiset_solver. Qed.
  Lemma test_elem_of_3 x y X : x ≠ y → x ∈ X → y ∈ X → {[+ x; y +]} ⊆ X.
  Proof. multiset_solver. Qed.
  Lemma test_elem_of_4 x y X Y : x ≠ y → x ∈ X → y ∈ Y → {[+ x; y +]} ⊆ X ∪ Y.
  Proof. multiset_solver. Qed.
  Lemma test_elem_of_5 x y X Y : x ≠ y → x ∈ X → y ∈ Y → {[+ x +]} ⊆ (X ∪ Y) ∖ {[+ y +]}.
  Proof. multiset_solver. Qed.
  Lemma test_elem_of_6 x y X : {[+ x; y +]} ⊆ X → x ∈ X ∧ y ∈ X.
  Proof. multiset_solver. Qed.

  (** Tests where the goals do not involve the multiset connectives *)
  Lemma test_goal_1 x y X : {[+ x +]} ∪ X ⊆ {[+ y +]} → x = y.
  Proof. multiset_solver. Qed.
  Lemma test_goal_2 x y X : {[+ x +]} ∪ X ⊆ {[+ y +]} → [x] = [y].
  Proof. multiset_solver. Qed.
  Lemma test_goal_3 x y X l :
    {[+ x +]} ∪ X ⊆ {[+ y +]} → [x] `suffix_of` l ++ [y].
  Proof.
    (* [multiset_solver] will first substitute [x]/[y], and then [eauto] is used
    on the leaf. *)
    multiset_solver by eauto using suffix_app_r.
  Qed.

  Lemma test_big_1 x1 x2 x3 x4 :
    {[+ x1; x2; x3; x4; x4 +]} ⊆@{gmultiset A} {[+ x1; x1; x2; x3; x4; x4 +]}.
  Proof. multiset_solver. Qed.
  Lemma test_big_2 x1 x2 x3 x4 X :
    2 ≤ multiplicity x4 X →
    {[+ x1; x2; x3; x4; x4 +]} ⊆@{gmultiset A} {[+ x1; x1; x2; x3 +]} ⊎ X.
  Proof. multiset_solver. Qed.
  Lemma test_big_3 x1 x2 x3 x4 X :
    4 ≤ multiplicity x4 X →
    {[+ x1; x2; x3; x4; x4 +]} ⊎ {[+ x1; x2; x3; x4; x4 +]}
    ⊆@{gmultiset A} {[+ x1; x1; x2; x3 +]} ⊎ {[+ x1; x1; x2; x3 +]} ⊎ X.
  Proof. multiset_solver. Qed.
  Lemma test_big_4 x1 x2 x3 x4 x5 x6 x7 x8 x9 :
    {[+ x1; x2; x3; x4; x4 +]} ⊎ {[+ x5; x6; x7; x8; x8; x9 +]}
    ⊆@{gmultiset A}
      {[+ x1; x1; x2; x3; x4; x4 +]} ⊎ {[+ x5; x5; x6; x7; x9; x8; x8 +]}.
  Proof. multiset_solver. Qed.
  Lemma test_big_5 x1 x2 x3 x4 x5 x6 x7 x8 x9 :
    2 *: {[+ x1; x2; x4 +]} ⊎ 2 *: {[+ x5; x6; x7; x8; x8; x9 +]}
    ⊆@{gmultiset A}
      {[+ x1; x1; x2; x3; x4; x4; x2 +]} ⊎ 3 *: {[+ x5; x5; x6; x7; x9; x8; x8 +]}.
  Proof. multiset_solver. Qed.

  Lemma test_firstorder_1 (P : A → Prop) x X :
    P x ∧ (∀ y, y ∈ X → P y) ↔ (∀ y, y ∈ {[+ x +]} ⊎ X → P y).
  Proof. multiset_solver. Qed.
End test.
