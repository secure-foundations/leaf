(** This file provides an axiomatization of the domain function of finite
maps. We provide such an axiomatization, instead of implementing the domain
function in a generic way, to allow more efficient implementations. *)
From stdpp Require Export sets fin_maps.
From stdpp Require Import options.

(* Pick up extra assumptions from section parameters. *)
Set Default Proof Using "Type*".

Class FinMapDom K M D `{∀ A, Dom (M A) D, FMap M,
    ∀ A, Lookup K A (M A), ∀ A, Empty (M A), ∀ A, PartialAlter K A (M A),
    OMap M, Merge M, ∀ A, FinMapToList K A (M A), EqDecision K,
    ElemOf K D, Empty D, Singleton K D,
    Union D, Intersection D, Difference D} := {
  finmap_dom_map :> FinMap K M;
  finmap_dom_set :> Set_ K D;
  elem_of_dom {A} (m : M A) i : i ∈ dom D m ↔ is_Some (m !! i)
}.

Section fin_map_dom.
Context `{FinMapDom K M D}.

Lemma lookup_lookup_total_dom `{!Inhabited A} (m : M A) i :
  i ∈ dom D m → m !! i = Some (m !!! i).
Proof. rewrite elem_of_dom. apply lookup_lookup_total. Qed.

Lemma dom_imap_subseteq {A B} (f: K → A → option B) (m: M A) :
  dom D (map_imap f m) ⊆ dom D m.
Proof.
  intros k. rewrite 2!elem_of_dom, map_lookup_imap.
  destruct 1 as [?[?[Eq _]]%bind_Some]. by eexists.
Qed.
Lemma dom_imap {A B} (f: K → A → option B) (m: M A) X :
  (∀ i, i ∈ X ↔ ∃ x, m !! i = Some x ∧ is_Some (f i x)) →
  dom D (map_imap f m) ≡ X.
Proof.
  intros HX k. rewrite elem_of_dom, HX, map_lookup_imap.
  unfold is_Some. setoid_rewrite bind_Some. naive_solver.
Qed.

Lemma elem_of_dom_2 {A} (m : M A) i x : m !! i = Some x → i ∈ dom D m.
Proof. rewrite elem_of_dom; eauto. Qed.
Lemma not_elem_of_dom {A} (m : M A) i : i ∉ dom D m ↔ m !! i = None.
Proof. by rewrite elem_of_dom, eq_None_not_Some. Qed.
Lemma subseteq_dom {A} (m1 m2 : M A) : m1 ⊆ m2 → dom D m1 ⊆ dom D m2.
Proof.
  rewrite map_subseteq_spec.
  intros ??. rewrite !elem_of_dom. inversion 1; eauto.
Qed.
Lemma subset_dom {A} (m1 m2 : M A) : m1 ⊂ m2 → dom D m1 ⊂ dom D m2.
Proof.
  intros [Hss1 Hss2]; split; [by apply subseteq_dom |].
  contradict Hss2. rewrite map_subseteq_spec. intros i x Hi.
  specialize (Hss2 i). rewrite !elem_of_dom in Hss2.
  destruct Hss2; eauto. by simplify_map_eq.
Qed.

Lemma dom_filter {A} (P : K * A → Prop) `{!∀ x, Decision (P x)} (m : M A) X :
  (∀ i, i ∈ X ↔ ∃ x, m !! i = Some x ∧ P (i, x)) →
  dom D (filter P m) ≡ X.
Proof.
  intros HX i. rewrite elem_of_dom, HX.
  unfold is_Some. by setoid_rewrite map_filter_lookup_Some.
Qed.
Lemma dom_filter_subseteq {A} (P : K * A → Prop) `{!∀ x, Decision (P x)} (m : M A):
  dom D (filter P m) ⊆ dom D m.
Proof. apply subseteq_dom, map_filter_subseteq. Qed.

Lemma dom_empty {A} : dom D (@empty (M A) _) ≡ ∅.
Proof.
  intros x. rewrite elem_of_dom, lookup_empty, <-not_eq_None_Some. set_solver.
Qed.
Lemma dom_empty_inv {A} (m : M A) : dom D m ≡ ∅ → m = ∅.
Proof.
  intros E. apply map_empty. intros. apply not_elem_of_dom.
  rewrite E. set_solver.
Qed.
Lemma dom_alter {A} f (m : M A) i : dom D (alter f i m) ≡ dom D m.
Proof.
  apply set_equiv; intros j; rewrite !elem_of_dom; unfold is_Some.
  destruct (decide (i = j)); simplify_map_eq/=; eauto.
  destruct (m !! j); naive_solver.
Qed.
Lemma dom_insert {A} (m : M A) i x : dom D (<[i:=x]>m) ≡ {[ i ]} ∪ dom D m.
Proof.
  apply set_equiv. intros j. rewrite elem_of_union, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_insert_Some.
  destruct (decide (i = j)); set_solver.
Qed.
Lemma dom_insert_lookup {A} (m : M A) i x :
  is_Some (m !! i) → dom D (<[i:=x]>m) ≡ dom D m.
Proof.
  intros Hindom. assert (i ∈ dom D m) by by apply elem_of_dom.
  rewrite dom_insert. set_solver.
Qed.
Lemma dom_insert_subseteq {A} (m : M A) i x : dom D m ⊆ dom D (<[i:=x]>m).
Proof. rewrite (dom_insert _). set_solver. Qed.
Lemma dom_insert_subseteq_compat_l {A} (m : M A) i x X :
  X ⊆ dom D m → X ⊆ dom D (<[i:=x]>m).
Proof. intros. trans (dom D m); eauto using dom_insert_subseteq. Qed.
Lemma dom_singleton {A} (i : K) (x : A) : dom D ({[i := x]} : M A) ≡ {[ i ]}.
Proof. rewrite <-insert_empty, dom_insert, dom_empty; set_solver. Qed.
Lemma dom_delete {A} (m : M A) i : dom D (delete i m) ≡ dom D m ∖ {[ i ]}.
Proof.
  apply set_equiv. intros j. rewrite elem_of_difference, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_delete_Some. set_solver.
Qed.
Lemma delete_partial_alter_dom {A} (m : M A) i f :
  i ∉ dom D m → delete i (partial_alter f i m) = m.
Proof. rewrite not_elem_of_dom. apply delete_partial_alter. Qed.
Lemma delete_insert_dom {A} (m : M A) i x :
  i ∉ dom D m → delete i (<[i:=x]>m) = m.
Proof. rewrite not_elem_of_dom. apply delete_insert. Qed.
Lemma map_disjoint_dom {A} (m1 m2 : M A) : m1 ##ₘ m2 ↔ dom D m1 ## dom D m2.
Proof.
  rewrite map_disjoint_spec, elem_of_disjoint.
  setoid_rewrite elem_of_dom. unfold is_Some. naive_solver.
Qed.
Lemma map_disjoint_dom_1 {A} (m1 m2 : M A) : m1 ##ₘ m2 → dom D m1 ## dom D m2.
Proof. apply map_disjoint_dom. Qed.
Lemma map_disjoint_dom_2 {A} (m1 m2 : M A) : dom D m1 ## dom D m2 → m1 ##ₘ m2.
Proof. apply map_disjoint_dom. Qed.
Lemma dom_union {A} (m1 m2 : M A) : dom D (m1 ∪ m2) ≡ dom D m1 ∪ dom D m2.
Proof.
  apply set_equiv. intros i. rewrite elem_of_union, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_union_Some_raw.
  destruct (m1 !! i); naive_solver.
Qed.
Lemma dom_intersection {A} (m1 m2: M A) : dom D (m1 ∩ m2) ≡ dom D m1 ∩ dom D m2.
Proof.
  apply set_equiv. intros i. rewrite elem_of_intersection, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_intersection_Some. naive_solver.
Qed.
Lemma dom_difference {A} (m1 m2 : M A) : dom D (m1 ∖ m2) ≡ dom D m1 ∖ dom D m2.
Proof.
  apply set_equiv. intros i. rewrite elem_of_difference, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_difference_Some.
  destruct (m2 !! i); naive_solver.
Qed.
Lemma dom_fmap {A B} (f : A → B) (m : M A) : dom D (f <$> m) ≡ dom D m.
Proof.
  apply set_equiv. intros i.
  rewrite !elem_of_dom, lookup_fmap, <-!not_eq_None_Some.
  destruct (m !! i); naive_solver.
Qed.
Lemma dom_finite {A} (m : M A) : set_finite (dom D m).
Proof.
  induction m using map_ind; rewrite ?dom_empty, ?dom_insert.
  - by apply empty_finite.
  - apply union_finite; [apply singleton_finite|done].
Qed.
Global Instance dom_proper `{!Equiv A} : Proper ((≡@{M A}) ==> (≡)) (dom D).
Proof.
  intros m1 m2 EQm. apply set_equiv. intros i.
  rewrite !elem_of_dom, EQm. done.
Qed.
Lemma dom_list_to_map {A} (l : list (K * A)) :
  dom D (list_to_map l : M A) ≡ list_to_set l.*1.
Proof.
  induction l as [|?? IH].
  - by rewrite dom_empty.
  - simpl. by rewrite dom_insert, IH.
Qed.

Lemma dom_singleton_inv {A} (m : M A) i :
  dom D m ≡ {[i]} → ∃ x, m = {[i := x]}.
Proof.
  intros Hdom. assert (is_Some (m !! i)) as [x ?].
  { apply (elem_of_dom (D:=D)); set_solver. }
  exists x. apply map_eq; intros j.
  destruct (decide (i = j)); simplify_map_eq; [done|].
  apply not_elem_of_dom. set_solver.
Qed.

Lemma dom_map_zip_with {A B C} (f : A → B → C) (ma : M A) (mb : M B) :
  dom D (map_zip_with f ma mb) ≡ dom D ma ∩ dom D mb.
Proof.
  rewrite set_equiv. intros x.
  rewrite elem_of_intersection, !elem_of_dom, map_lookup_zip_with.
  destruct (ma !! x), (mb !! x); rewrite !is_Some_alt; naive_solver.
Qed.

Lemma dom_union_inv `{!RelDecision (∈@{D})} {A} (m : M A) (X1 X2 : D) :
  X1 ## X2 →
  dom D m ≡ X1 ∪ X2 →
  ∃ m1 m2, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ dom D m1 ≡ X1 ∧ dom D m2 ≡ X2.
Proof.
  intros.
  exists (filter (λ '(k,x), k ∈ X1) m), (filter (λ '(k,x), k ∉ X1) m).
  assert (filter (λ '(k, _), k ∈ X1) m ##ₘ filter (λ '(k, _), k ∉ X1) m).
  { apply map_disjoint_filter_complement. }
  split_and!; [|done| |].
  - apply map_eq; intros i. apply option_eq; intros x.
    rewrite lookup_union_Some, !map_filter_lookup_Some by done.
    destruct (decide (i ∈ X1)); naive_solver.
  - apply dom_filter; intros i; split; [|naive_solver].
    intros. assert (is_Some (m !! i)) as [x ?] by (apply (elem_of_dom (D:=D)); set_solver).
    naive_solver.
  - apply dom_filter; intros i; split.
    + intros. assert (is_Some (m !! i)) as [x ?] by (apply (elem_of_dom (D:=D)); set_solver).
      naive_solver.
    + intros (x&?&?). apply dec_stable; intros ?.
      assert (m !! i = None) by (apply not_elem_of_dom; set_solver).
      naive_solver.
Qed.

Lemma dom_kmap `{!Elements K D, !FinSet K D, FinMapDom K2 M2 D2}
    {A} (f : K → K2) `{!Inj (=) (=) f} (m : M A) :
  dom D2 (kmap (M2:=M2) f m) ≡ set_map f (dom D m).
Proof.
  apply set_equiv. intros i.
  rewrite !elem_of_dom, (lookup_kmap_is_Some _), elem_of_map.
  by setoid_rewrite elem_of_dom.
Qed.

(** If [D] has Leibniz equality, we can show an even stronger result.  This is a
common case e.g. when having a [gmap K A] where the key [K] has Leibniz equality
(and thus also [gset K], the usual domain) but the value type [A] does not. *)
Global Instance dom_proper_L `{!Equiv A, !LeibnizEquiv D} :
  Proper ((≡@{M A}) ==> (=)) (dom D) | 0.
Proof. intros ???. unfold_leibniz. by apply dom_proper. Qed.

Section leibniz.
  Context `{!LeibnizEquiv D}.
  Lemma dom_filter_L {A} (P : K * A → Prop) `{!∀ x, Decision (P x)} (m : M A) X :
    (∀ i, i ∈ X ↔ ∃ x, m !! i = Some x ∧ P (i, x)) →
    dom D (filter P m) = X.
  Proof. unfold_leibniz. apply dom_filter. Qed.
  Lemma dom_empty_L {A} : dom D (@empty (M A) _) = ∅.
  Proof. unfold_leibniz; apply dom_empty. Qed.
  Lemma dom_empty_inv_L {A} (m : M A) : dom D m = ∅ → m = ∅.
  Proof. by intros; apply dom_empty_inv; unfold_leibniz. Qed.
  Lemma dom_alter_L {A} f (m : M A) i : dom D (alter f i m) = dom D m.
  Proof. unfold_leibniz; apply dom_alter. Qed.
  Lemma dom_insert_L {A} (m : M A) i x : dom D (<[i:=x]>m) = {[ i ]} ∪ dom D m.
  Proof. unfold_leibniz; apply dom_insert. Qed.
  Lemma dom_insert_lookup_L {A} (m : M A) i x :
    is_Some (m !! i) → dom D (<[i:=x]>m) = dom D m.
  Proof. unfold_leibniz; apply dom_insert_lookup. Qed.
  Lemma dom_singleton_L {A} (i : K) (x : A) : dom D ({[i := x]} : M A) = {[ i ]}.
  Proof. unfold_leibniz; apply dom_singleton. Qed.
  Lemma dom_delete_L {A} (m : M A) i : dom D (delete i m) = dom D m ∖ {[ i ]}.
  Proof. unfold_leibniz; apply dom_delete. Qed.
  Lemma dom_union_L {A} (m1 m2 : M A) : dom D (m1 ∪ m2) = dom D m1 ∪ dom D m2.
  Proof. unfold_leibniz; apply dom_union. Qed.
  Lemma dom_intersection_L {A} (m1 m2 : M A) :
    dom D (m1 ∩ m2) = dom D m1 ∩ dom D m2.
  Proof. unfold_leibniz; apply dom_intersection. Qed.
  Lemma dom_difference_L {A} (m1 m2 : M A) : dom D (m1 ∖ m2) = dom D m1 ∖ dom D m2.
  Proof. unfold_leibniz; apply dom_difference. Qed.
  Lemma dom_fmap_L {A B} (f : A → B) (m : M A) : dom D (f <$> m) = dom D m.
  Proof. unfold_leibniz; apply dom_fmap. Qed.
  Lemma dom_imap_L {A B} (f: K → A → option B) (m: M A) X :
    (∀ i, i ∈ X ↔ ∃ x, m !! i = Some x ∧ is_Some (f i x)) →
    dom D (map_imap f m) = X.
  Proof. unfold_leibniz; apply dom_imap. Qed.
  Lemma dom_list_to_map_L {A} (l : list (K * A)) :
    dom D (list_to_map l : M A) = list_to_set l.*1.
  Proof. unfold_leibniz. apply dom_list_to_map. Qed.
  Lemma dom_singleton_inv_L {A} (m : M A) i :
    dom D m = {[i]} → ∃ x, m = {[i := x]}.
  Proof. unfold_leibniz. apply dom_singleton_inv. Qed.
  Lemma dom_map_zip_with_L {A B C} (f : A → B → C) (ma : M A) (mb : M B) :
    dom D (map_zip_with f ma mb) = dom D ma ∩ dom D mb.
  Proof. unfold_leibniz. apply dom_map_zip_with. Qed.
  Lemma dom_union_inv_L `{!RelDecision (∈@{D})} {A} (m : M A) (X1 X2 : D) :
    X1 ## X2 →
    dom D m = X1 ∪ X2 →
    ∃ m1 m2, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ dom D m1 = X1 ∧ dom D m2 = X2.
  Proof. unfold_leibniz. apply dom_union_inv. Qed.
End leibniz.

Lemma dom_kmap_L `{!Elements K D, !FinSet K D, FinMapDom K2 M2 D2}
    `{!LeibnizEquiv D2} {A} (f : K → K2) `{!Inj (=) (=) f} (m : M A) :
  dom D2 (kmap (M2:=M2) f m) = set_map f (dom D m).
Proof. unfold_leibniz. by apply dom_kmap. Qed.

(** * Set solver instances *)
Global Instance set_unfold_dom_empty {A} i : SetUnfoldElemOf i (dom D (∅:M A)) False.
Proof. constructor. by rewrite dom_empty, elem_of_empty. Qed.
Global Instance set_unfold_dom_alter {A} f i j (m : M A) Q :
  SetUnfoldElemOf i (dom D m) Q →
  SetUnfoldElemOf i (dom D (alter f j m)) Q.
Proof. constructor. by rewrite dom_alter, (set_unfold_elem_of _ (dom _ _) _). Qed.
Global Instance set_unfold_dom_insert {A} i j x (m : M A) Q :
  SetUnfoldElemOf i (dom D m) Q →
  SetUnfoldElemOf i (dom D (<[j:=x]> m)) (i = j ∨ Q).
Proof.
  constructor. by rewrite dom_insert, elem_of_union,
    (set_unfold_elem_of _ (dom _ _) _), elem_of_singleton.
Qed.
Global Instance set_unfold_dom_delete {A} i j (m : M A) Q :
  SetUnfoldElemOf i (dom D m) Q →
  SetUnfoldElemOf i (dom D (delete j m)) (Q ∧ i ≠ j).
Proof.
  constructor. by rewrite dom_delete, elem_of_difference,
    (set_unfold_elem_of _ (dom _ _) _), elem_of_singleton.
Qed.
Global Instance set_unfold_dom_singleton {A} i j x :
  SetUnfoldElemOf i (dom D ({[ j := x ]} : M A)) (i = j).
Proof. constructor. by rewrite dom_singleton, elem_of_singleton. Qed.
Global Instance set_unfold_dom_union {A} i (m1 m2 : M A) Q1 Q2 :
  SetUnfoldElemOf i (dom D m1) Q1 → SetUnfoldElemOf i (dom D m2) Q2 →
  SetUnfoldElemOf i (dom D (m1 ∪ m2)) (Q1 ∨ Q2).
Proof.
  constructor. by rewrite dom_union, elem_of_union,
    !(set_unfold_elem_of _ (dom _ _) _).
Qed.
Global Instance set_unfold_dom_intersection {A} i (m1 m2 : M A) Q1 Q2 :
  SetUnfoldElemOf i (dom D m1) Q1 → SetUnfoldElemOf i (dom D m2) Q2 →
  SetUnfoldElemOf i (dom D (m1 ∩ m2)) (Q1 ∧ Q2).
Proof.
  constructor. by rewrite dom_intersection, elem_of_intersection,
    !(set_unfold_elem_of _ (dom _ _) _).
Qed.
Global Instance set_unfold_dom_difference {A} i (m1 m2 : M A) Q1 Q2 :
  SetUnfoldElemOf i (dom D m1) Q1 → SetUnfoldElemOf i (dom D m2) Q2 →
  SetUnfoldElemOf i (dom D (m1 ∖ m2)) (Q1 ∧ ¬Q2).
Proof.
  constructor. by rewrite dom_difference, elem_of_difference,
    !(set_unfold_elem_of _ (dom _ _) _).
Qed.
Global Instance set_unfold_dom_fmap {A B} (f : A → B) i (m : M A) Q :
  SetUnfoldElemOf i (dom D m) Q →
  SetUnfoldElemOf i (dom D (f <$> m)) Q.
Proof. constructor. by rewrite dom_fmap, (set_unfold_elem_of _ (dom _ _) _). Qed.
End fin_map_dom.

Lemma dom_seq `{FinMapDom nat M D} {A} start (xs : list A) :
  dom D (map_seq start (M:=M A) xs) ≡ set_seq start (length xs).
Proof.
  revert start. induction xs as [|x xs IH]; intros start; simpl.
  - by rewrite dom_empty.
  - by rewrite dom_insert, IH.
Qed.
Lemma dom_seq_L `{FinMapDom nat M D, !LeibnizEquiv D} {A} start (xs : list A) :
  dom D (map_seq (M:=M A) start xs) = set_seq start (length xs).
Proof. unfold_leibniz. apply dom_seq. Qed.

Global Instance set_unfold_dom_seq `{FinMapDom nat M D} {A} start (xs : list A) i :
  SetUnfoldElemOf i (dom D (map_seq start (M:=M A) xs)) (start ≤ i < start + length xs).
Proof. constructor. by rewrite dom_seq, elem_of_set_seq. Qed.
