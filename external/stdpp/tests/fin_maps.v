From stdpp Require Import fin_maps fin_map_dom.

Section map_disjoint.
  Context `{FinMap K M}.

  Lemma solve_map_disjoint_singleton_1 {A} (m1 m2 : M A) i x :
    m1 ##ₘ <[i:=x]> m2 → {[ i:= x ]} ∪ m2 ##ₘ m1 ∧ m2 ##ₘ ∅.
  Proof. intros. solve_map_disjoint. Qed.

  Lemma solve_map_disjoint_singleton_2 {A} (m1 m2 : M A) i x :
    m2 !! i = None → m1 ##ₘ {[ i := x ]} ∪ m2 → m2 ##ₘ <[i:=x]> m1 ∧ m1 !! i = None.
  Proof. intros. solve_map_disjoint. Qed.
End map_disjoint.

Section map_dom.
  Context `{FinMapDom K M D}.

  Lemma set_solver_dom_subseteq {A} (i j : K) (x y : A) :
    {[i; j]} ⊆ dom D (<[i:=x]> (<[j:=y]> (∅ : M A))).
  Proof. set_solver. Qed.

  Lemma set_solver_dom_disjoint {A} (X : D) : dom D (∅ : M A) ## X.
  Proof. set_solver. Qed.
End map_dom.
