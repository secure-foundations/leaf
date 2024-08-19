(** Finite maps associate data to keys. This file defines an interface for
finite maps and collects some theory on it. Most importantly, it proves useful
induction principles for finite maps and implements the tactic
[simplify_map_eq] to simplify goals involving finite maps. *)
From Coq Require Import Permutation.
From stdpp Require Export relations orders vector fin_sets.
From stdpp Require Import options.

(* FIXME: This file needs a 'Proof Using' hint, but they need to be set
locally (or things moved out of sections) as no default works well enough. *)
Unset Default Proof Using.

(** * Axiomatization of finite maps *)
(** We require Leibniz equality of finite maps to be extensional, i.e., to enjoy
[(∀ i, m1 !! i = m2 !! i) → m1 = m2]. This is a very useful property as it
avoids the need for setoid rewriting in proof. However, it comes at the cost of
restricting what map implementations we support. Since Coq does not have
quotient types, it rules out balanced search trees (AVL, red-black, etc.). We
do provide a reasonably efficient implementation of binary tries (see [gmap]
and [Pmap]). *)

(** Finiteness is axiomatized through a fold operation [map_fold f b m], which
folds a function [f] over each element of the map [m]. The order in which the
elements are passed to [f] is unspecified. *)

Class MapFold K A M := map_fold B : (K → A → B → B) → B → M → B.
Global Arguments map_fold {_ _ _ _ _} _ _ _.
Global Hint Mode MapFold - - ! : typeclass_instances.
Global Hint Mode MapFold ! - - : typeclass_instances.

(** Make sure that [map_fold] (and definitions based on it) are not unfolded
too eagerly by unification. See [only_evens_Some] in [tests/pmap_gmap] for an
example. We use level 1 because it is the least level for which the test works. *)
Global Strategy 1 [map_fold].

(** Finite map implementations are required to implement the [merge] function
which enables us to give a generic implementation of [union_with],
[intersection_with], and [difference_with].

The function [diag_None f] is used in the specification and lemmas of [merge f].
It lifts a function [f : option A → option B → option C] by returning
[None] if both arguments are [None], to make sure that in [merge f m1 m2], the
function [f] can only operate on elements that are in the domain of either [m1]
or [m2]. *)
Definition diag_None {A B C} (f : option A → option B → option C)
    (mx : option A) (my : option B) : option C :=
  match mx, my with None, None => None | _, _ => f mx my end.

(** We need the [insert] operation as part of the [map_fold_ind] rule in the
[FinMap] interface. Hence we define it before the other derived operations. *)
Global Instance map_insert `{PartialAlter K A M} : Insert K A M :=
  λ i x, partial_alter (λ _, Some x) i.

Class FinMap K M `{FMap M, ∀ A, Lookup K A (M A), ∀ A, Empty (M A), ∀ A,
    PartialAlter K A (M A), OMap M, Merge M, ∀ A, MapFold K A (M A),
    EqDecision K} := {
  map_eq {A} (m1 m2 : M A) : (∀ i, m1 !! i = m2 !! i) → m1 = m2;
  lookup_empty {A} i : (∅ : M A) !! i = None;
  lookup_partial_alter {A} f (m : M A) i :
    partial_alter f i m !! i = f (m !! i);
  lookup_partial_alter_ne {A} f (m : M A) i j :
    i ≠ j → partial_alter f i m !! j = m !! j;
  lookup_fmap {A B} (f : A → B) (m : M A) i : (f <$> m) !! i = f <$> m !! i;
  lookup_omap {A B} (f : A → option B) (m : M A) i :
    omap f m !! i = m !! i ≫= f;
  lookup_merge {A B C} (f : option A → option B → option C) (m1 : M A) (m2 : M B) i :
    merge f m1 m2 !! i = diag_None f (m1 !! i) (m2 !! i);
  map_fold_ind {A B} (P : B → M A → Prop) (f : K → A → B → B) (b : B) :
    P b ∅ →
    (∀ i x m r, m !! i = None → P r m → P (f i x r) (<[i:=x]> m)) →
    ∀ m, P (map_fold f b m) m
}.

(** * Derived operations *)
(** All of the following functions are defined in a generic way for arbitrary
finite map implementations. These generic implementations do not cause a
significant performance loss, which justifies including them in the finite map
interface as primitive operations. *)
Global Instance map_alter `{PartialAlter K A M} : Alter K A M :=
  λ f, partial_alter (fmap f).
Global Instance map_delete `{PartialAlter K A M} : Delete K M :=
  partial_alter (λ _, None).
Global Instance map_singleton `{PartialAlter K A M, Empty M} :
  SingletonM K A M := λ i x, <[i:=x]> ∅.

Definition list_to_map `{Insert K A M, Empty M} : list (K * A) → M :=
  fold_right (λ p, <[p.1:=p.2]>) ∅.

Global Instance map_size `{MapFold K A M} : Size M :=
  map_fold (λ _ _, S) 0.
Definition map_to_list `{MapFold K A M} : M → list (K * A) :=
  map_fold (λ i x, ((i,x) ::.)) [].

Definition map_to_set `{MapFold K A M,
    Singleton B C, Empty C, Union C} (f : K → A → B) (m : M) : C :=
  list_to_set (uncurry f <$> map_to_list m).
Definition set_to_map `{Elements B C, Insert K A M, Empty M}
    (f : B → K * A) (X : C) : M :=
  list_to_map (f <$> elements X).

Global Instance map_union_with `{Merge M} {A} : UnionWith A (M A) :=
  λ f, merge (union_with f).
Global Instance map_intersection_with `{Merge M} {A} : IntersectionWith A (M A) :=
  λ f, merge (intersection_with f).
Global Instance map_difference_with `{Merge M} {A} : DifferenceWith A (M A) :=
  λ f, merge (difference_with f).

(** Higher precedence to make sure it's not used for other types with a [Lookup]
instance, such as lists. *)
Global Instance map_equiv `{∀ A, Lookup K A (M A), Equiv A} : Equiv (M A) | 20 :=
  λ m1 m2, ∀ i, m1 !! i ≡ m2 !! i.

Definition map_Forall `{Lookup K A M} (P : K → A → Prop) : M → Prop :=
  λ m, ∀ i x, m !! i = Some x → P i x.

Definition map_Exists `{Lookup K A M} (P : K → A → Prop) : M → Prop :=
  λ m, ∃ i x, m !! i = Some x ∧ P i x.

Definition map_relation `{∀ A, Lookup K A (M A)} {A B} (R : A → B → Prop)
    (P : A → Prop) (Q : B → Prop) (m1 : M A) (m2 : M B) : Prop := ∀ i,
  option_relation R P Q (m1 !! i) (m2 !! i).
Definition map_included `{∀ A, Lookup K A (M A)} {A}
  (R : relation A) : relation (M A) := map_relation R (λ _, False) (λ _, True).
Definition map_agree `{∀ A, Lookup K A (M A)} {A} : relation (M A) :=
  map_relation (=) (λ _, True) (λ _, True).
Definition map_disjoint `{∀ A, Lookup K A (M A)} {A} : relation (M A) :=
  map_relation (λ _ _, False) (λ _, True) (λ _, True).
Infix "##ₘ" := map_disjoint (at level 70) : stdpp_scope.
Global Hint Extern 0 (_ ##ₘ _) => symmetry; eassumption : core.
Notation "( m ##ₘ.)" := (map_disjoint m) (only parsing) : stdpp_scope.
Notation "(.##ₘ m )" := (λ m2, m2 ##ₘ m) (only parsing) : stdpp_scope.
Global Instance map_subseteq `{∀ A, Lookup K A (M A)} {A} : SubsetEq (M A) :=
  map_included (=).

(** The union of two finite maps only has a meaningful definition for maps
that are disjoint. However, as working with partial functions is inconvenient
in Coq, we define the union as a total function. In case both finite maps
have a value at the same index, we take the value of the first map. *)
Global Instance map_union `{Merge M} {A} : Union (M A) := union_with (λ x _, Some x).
Global Instance map_intersection `{Merge M} {A} : Intersection (M A) :=
  intersection_with (λ x _, Some x).

(** The difference operation removes all values from the first map whose
index contains a value in the second map as well. *)
Global Instance map_difference `{Merge M} {A} : Difference (M A) :=
  difference_with (λ _ _, None).

(** A stronger variant of map that allows the mapped function to use the index
of the elements. Implemented by conversion to lists, so not very efficient. *)
Definition map_imap `{∀ A, Insert K A (M A), ∀ A, Empty (M A),
    ∀ A, MapFold K A (M A)} {A B} (f : K → A → option B) (m : M A) : M B :=
  list_to_map (omap (λ ix, (fst ix ,.) <$> uncurry f ix) (map_to_list m)).

(** Given a function [f : K1 → K2], the function [kmap f] turns a maps with
keys of type [K1] into a map with keys of type [K2]. The function [kmap f]
is only well-behaved if [f] is injective, as otherwise it could map multiple
entries into the same entry. All lemmas about [kmap f] thus have the premise
[Inj (=) (=) f]. *)
Definition kmap `{∀ A, Insert K2 A (M2 A), ∀ A, Empty (M2 A),
    ∀ A, MapFold K1 A (M1 A)} {A} (f : K1 → K2) (m : M1 A) : M2 A :=
  list_to_map (fmap (prod_map f id) (map_to_list m)).

(* The zip operation on maps combines two maps key-wise. The keys of resulting
map correspond to the keys that are in both maps. *)
Definition map_zip_with `{Merge M} {A B C} (f : A → B → C) : M A → M B → M C :=
  merge (λ mx my,
    match mx, my with Some x, Some y => Some (f x y) | _, _ => None end).
Notation map_zip := (map_zip_with pair).

Global Instance map_filter
    `{MapFold K A M, Insert K A M, Empty M} : Filter (K * A) M :=
  λ P _, map_fold (λ k v m, if decide (P (k,v)) then <[k := v]>m else m) ∅.

Fixpoint map_seq `{Insert nat A M, Empty M} (start : nat) (xs : list A) : M :=
  match xs with
  | [] => ∅
  | x :: xs => <[start:=x]> (map_seq (S start) xs)
  end.

Fixpoint map_seqZ `{Insert Z A M, Empty M} (start : Z) (xs : list A) : M :=
  match xs with
  | [] => ∅
  | x :: xs => <[start:=x]> (map_seqZ (Z.succ start) xs)
  end.

Global Instance map_lookup_total `{!Lookup K A (M A), !Inhabited A} :
  LookupTotal K A (M A) | 20 := λ i m, default inhabitant (m !! i).
Global Typeclasses Opaque map_lookup_total.

(** Given a finite map [m : M] with keys [K] and values [A], the image [map_img m]
gives a finite set containing with the values [A] of [m]. The type of [map_img]
is generic to support different map and set implementations. A possible instance
is [SA:=gset A]. *)
Definition map_img `{MapFold K A M,
  Singleton A SA, Empty SA, Union SA} : M → SA := map_to_set (λ _ x, x).
Global Typeclasses Opaque map_img.

(** Given a finite map [m] with keys [K] and values [A], the preimage
[map_preimg m] gives a finite map with keys [A] and values being sets of [K].
The type of [map_preimg] is very generic to support different map and set
implementations. A possible instance is [MKA:=gmap K A], [MASK:=gmap A (gset K)],
and [SK:=gset K]. *)
Definition map_preimg `{MapFold K A MKA, Empty MASK,
    PartialAlter A SK MASK, Empty SK, Singleton K SK, Union SK}
    (m : MKA) : MASK :=
  map_fold (λ i, partial_alter (λ mX, Some $ {[ i ]} ∪ default ∅ mX)) ∅ m.
Global Typeclasses Opaque map_preimg.

Definition map_compose `{OMap MA, Lookup B C MB}
  (m : MB) (n : MA B) : MA C := omap (m !!.) n.

Infix "∘ₘ" := map_compose (at level 65, right associativity) : stdpp_scope.
Notation "(∘ₘ)" := map_compose (only parsing) : stdpp_scope.
Notation "( m ∘ₘ.)" := (map_compose m) (only parsing) : stdpp_scope.
Notation "(.∘ₘ m )" := (λ n, map_compose n m) (only parsing) : stdpp_scope.

(** * Theorems *)
Section theorems.
Context `{FinMap K M}.

(** ** General properties *)
Lemma map_eq_iff {A} (m1 m2 : M A) : m1 = m2 ↔ ∀ i, m1 !! i = m2 !! i.
Proof. split; [by intros ->|]. apply map_eq. Qed.
Lemma map_subseteq_spec {A} (m1 m2 : M A) :
  m1 ⊆ m2 ↔ ∀ i x, m1 !! i = Some x → m2 !! i = Some x.
Proof.
  unfold subseteq, map_subseteq, map_relation. split; intros Hm i;
    specialize (Hm i); destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Global Instance map_included_preorder {A} (R : relation A) :
  PreOrder R → PreOrder (map_included R : relation (M A)).
Proof.
  split; [intros m i; by destruct (m !! i); simpl|].
  intros m1 m2 m3 Hm12 Hm23 i; specialize (Hm12 i); specialize (Hm23 i).
  destruct (m1 !! i), (m2 !! i), (m3 !! i); simplify_eq/=;
    done || etrans; eauto.
Qed.
Global Instance map_subseteq_po {A} : PartialOrder (⊆@{M A}).
Proof.
  split; [apply _|].
  intros m1 m2; rewrite !map_subseteq_spec.
  intros; apply map_eq; intros i; apply option_eq; naive_solver.
Qed.
Lemma lookup_total_alt `{!Inhabited A} (m : M A) i :
  m !!! i = default inhabitant (m !! i).
Proof. reflexivity. Qed.
Lemma lookup_total_correct `{!Inhabited A} (m : M A) i x :
  m !! i = Some x → m !!! i = x.
Proof. rewrite lookup_total_alt. by intros ->. Qed.
Lemma lookup_lookup_total `{!Inhabited A} (m : M A) i :
  is_Some (m !! i) → m !! i = Some (m !!! i).
Proof. intros [x Hx]. by rewrite (lookup_total_correct m i x). Qed.
Lemma lookup_weaken {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some x.
Proof. rewrite !map_subseteq_spec. auto. Qed.
Lemma lookup_weaken_is_Some {A} (m1 m2 : M A) i :
  is_Some (m1 !! i) → m1 ⊆ m2 → is_Some (m2 !! i).
Proof. inv 1. eauto using lookup_weaken. Qed.
Lemma lookup_weaken_None {A} (m1 m2 : M A) i :
  m2 !! i = None → m1 ⊆ m2 → m1 !! i = None.
Proof.
  rewrite map_subseteq_spec, !eq_None_not_Some.
  intros Hm2 Hm [??]; destruct Hm2; eauto.
Qed.
Lemma lookup_weaken_inv {A} (m1 m2 : M A) i x y :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some y → x = y.
Proof. intros Hm1 ? Hm2. eapply lookup_weaken in Hm1; eauto. congruence. Qed.
Lemma lookup_ne {A} (m : M A) i j : m !! i ≠ m !! j → i ≠ j.
Proof. congruence. Qed.
Lemma map_empty {A} (m : M A) : m = ∅ ↔ ∀ i, m !! i = None.
Proof.
  split.
  - intros -> i. by rewrite lookup_empty.
  - intros Hm. apply map_eq. intros i. by rewrite Hm, lookup_empty.
Qed.
Lemma lookup_empty_is_Some {A} i : ¬is_Some ((∅ : M A) !! i).
Proof. rewrite lookup_empty. by inv 1. Qed.
Lemma lookup_empty_Some {A} i (x : A) : ¬(∅ : M A) !! i = Some x.
Proof. by rewrite lookup_empty. Qed.
Lemma lookup_total_empty `{!Inhabited A} i : (∅ : M A) !!! i = inhabitant.
Proof. by rewrite lookup_total_alt, lookup_empty. Qed.
Lemma map_subset_empty {A} (m : M A) : m ⊄ ∅.
Proof.
  intros [_ []]. rewrite map_subseteq_spec. intros ??. by rewrite lookup_empty.
Qed.
Lemma map_empty_subseteq {A} (m : M A) : ∅ ⊆ m.
Proof. apply map_subseteq_spec. intros k v []%lookup_empty_Some. Qed.

(** [NoDup_map_to_list] and [NoDup_map_to_list] need to be proved mutually,
hence a [Local] helper lemma. *)
Local Lemma map_to_list_spec {A} (m : M A) :
  NoDup (map_to_list m) ∧ (∀ i x, (i,x) ∈ map_to_list m ↔ m !! i = Some x).
Proof.
  apply (map_fold_ind (λ l m,
    NoDup l ∧ ∀ i x, (i,x) ∈ l ↔ m !! i = Some x)); clear m.
  { split; [constructor|]. intros i x. by rewrite elem_of_nil, lookup_empty. }
  intros i x m l ? [IH1 IH2]. split; [constructor; naive_solver|].
  intros j y. rewrite elem_of_cons, IH2.
  unfold insert, map_insert. destruct (decide (i = j)) as [->|].
  - rewrite lookup_partial_alter. naive_solver.
  - rewrite lookup_partial_alter_ne by done. naive_solver.
Qed.
Lemma NoDup_map_to_list {A} (m : M A) : NoDup (map_to_list m).
Proof. apply map_to_list_spec. Qed.
Lemma elem_of_map_to_list {A} (m : M A) i x :
  (i,x) ∈ map_to_list m ↔ m !! i = Some x.
Proof. apply map_to_list_spec. Qed.

Lemma map_subset_alt {A} (m1 m2 : M A) :
  m1 ⊂ m2 ↔ m1 ⊆ m2 ∧ ∃ i, m1 !! i = None ∧ is_Some (m2 !! i).
Proof.
  rewrite strict_spec_alt. split.
  - intros [? Heq]; split; [done|].
    destruct (decide (Exists (λ ix, m1 !! ix.1 = None) (map_to_list m2)))
      as [[[i x] [?%elem_of_map_to_list ?]]%Exists_exists
         |Hm%(not_Exists_Forall _)]; [eauto|].
    destruct Heq; apply (anti_symm (⊆)), map_subseteq_spec; [done|intros i x Hi].
    assert (is_Some (m1 !! i)) as [x' ?].
    { by apply not_eq_None_Some,
        (proj1 (Forall_forall _ _) Hm (i,x)), elem_of_map_to_list. }
    by rewrite <-(lookup_weaken_inv m1 m2 i x' x).
  - intros [? (i&?&x&?)]; split; [done|]. congruence.
Qed.

(** ** Properties of the [partial_alter] operation *)
Lemma partial_alter_ext {A} (f g : option A → option A) (m : M A) i :
  (∀ x, m !! i = x → f x = g x) → partial_alter f i m = partial_alter g i m.
Proof.
  intros. apply map_eq; intros j. by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne; auto.
Qed.
Lemma partial_alter_compose {A} f g (m : M A) i:
  partial_alter (f ∘ g) i m = partial_alter f i (partial_alter g i m).
Proof.
  intros. apply map_eq. intros ii. by destruct (decide (i = ii)) as [->|?];
    rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne.
Qed.
Lemma partial_alter_commute {A} f g (m : M A) i j :
  i ≠ j → partial_alter f i (partial_alter g j m) =
    partial_alter g j (partial_alter f i m).
Proof.
  intros. apply map_eq; intros jj. destruct (decide (jj = j)) as [->|?].
  { by rewrite lookup_partial_alter_ne,
      !lookup_partial_alter, lookup_partial_alter_ne. }
  destruct (decide (jj = i)) as [->|?].
  - by rewrite lookup_partial_alter,
     !lookup_partial_alter_ne, lookup_partial_alter by congruence.
  - by rewrite !lookup_partial_alter_ne by congruence.
Qed.
Lemma partial_alter_self_alt {A} (m : M A) i x :
  x = m !! i → partial_alter (λ _, x) i m = m.
Proof.
  intros. apply map_eq. intros ii. by destruct (decide (i = ii)) as [->|];
    rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne.
Qed.
Lemma partial_alter_self {A} (m : M A) i : partial_alter (λ _, m !! i) i m = m.
Proof. by apply partial_alter_self_alt. Qed.
Lemma partial_alter_subseteq {A} f (m : M A) i :
  m !! i = None → m ⊆ partial_alter f i m.
Proof.
  rewrite map_subseteq_spec. intros Hi j x Hj.
  rewrite lookup_partial_alter_ne; congruence.
Qed.
Lemma partial_alter_subset {A} f (m : M A) i :
  m !! i = None → is_Some (f (m !! i)) → m ⊂ partial_alter f i m.
Proof.
  intros Hi Hfi. apply map_subset_alt; split; [by apply partial_alter_subseteq|].
  exists i. by rewrite lookup_partial_alter.
Qed.
Lemma lookup_partial_alter_Some {A} (f : option A → option A) (m : M A) i j x :
  partial_alter f i m !! j = Some x ↔
    (i = j ∧ f (m !! i) = Some x) ∨ (i ≠ j ∧ m !! j = Some x).
Proof.
  destruct (decide (i = j)); subst.
  - rewrite lookup_partial_alter. naive_solver.
  - rewrite lookup_partial_alter_ne; naive_solver.
Qed.
Lemma lookup_total_partial_alter {A} `{Inhabited A}
    (f : option A → option A) (m : M A) i:
  partial_alter f i m !!! i = default inhabitant (f (m !! i)).
Proof. by rewrite lookup_total_alt, lookup_partial_alter. Qed.

(** ** Properties of the [alter] operation *)
Lemma lookup_alter {A} (f : A → A) (m : M A) i : alter f i m !! i = f <$> m !! i.
Proof. unfold alter. apply lookup_partial_alter. Qed.
Lemma lookup_alter_ne {A} (f : A → A) (m : M A) i j :
  i ≠ j → alter f i m !! j = m !! j.
Proof. unfold alter. apply lookup_partial_alter_ne. Qed.
Lemma alter_ext {A} (f g : A → A) (m : M A) i :
  (∀ x, m !! i = Some x → f x = g x) → alter f i m = alter g i m.
Proof. intro. apply partial_alter_ext. intros [x|] ?; f_equal/=; auto. Qed.
Lemma alter_compose {A} (f g : A → A) (m : M A) i:
  alter (f ∘ g) i m = alter f i (alter g i m).
Proof.
  unfold alter, map_alter. rewrite <-partial_alter_compose.
  apply partial_alter_ext. by intros [?|].
Qed.
Lemma alter_commute {A} (f g : A → A) (m : M A) i j :
  i ≠ j → alter f i (alter g j m) = alter g j (alter f i m).
Proof. apply partial_alter_commute. Qed.
Lemma alter_insert {A} (m : M A) i f x :
  alter f i (<[i := x]> m) = <[i := f x]> m.
Proof.
  unfold alter, insert, map_alter, map_insert.
  by rewrite <-partial_alter_compose.
Qed.
Lemma alter_insert_ne {A} (m : M A) i j f x :
  i ≠ j →
  alter f i (<[j := x]> m) = <[j := x]> (alter f i m).
Proof. intros. symmetry. by apply partial_alter_commute. Qed.
Lemma lookup_alter_Some {A} (f : A → A) (m : M A) i j y :
  alter f i m !! j = Some y ↔
    (i = j ∧ ∃ x, m !! j = Some x ∧ y = f x) ∨ (i ≠ j ∧ m !! j = Some y).
Proof.
  destruct (decide (i = j)) as [->|?].
  - rewrite lookup_alter. naive_solver (simplify_option_eq; eauto).
  - rewrite lookup_alter_ne by done. naive_solver.
Qed.
Lemma lookup_alter_None {A} (f : A → A) (m : M A) i j :
  alter f i m !! j = None ↔ m !! j = None.
Proof.
  by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_alter, ?fmap_None, ?lookup_alter_ne.
Qed.
Lemma lookup_alter_is_Some {A} (f : A → A) (m : M A) i j :
  is_Some (alter f i m !! j) ↔ is_Some (m !! j).
Proof. by rewrite <-!not_eq_None_Some, lookup_alter_None. Qed.
Lemma alter_id {A} (f : A → A) (m : M A) i :
  (∀ x, m !! i = Some x → f x = x) → alter f i m = m.
Proof.
  intros Hi; apply map_eq; intros j; destruct (decide (i = j)) as [->|?].
  { rewrite lookup_alter; destruct (m !! j); f_equal/=; auto. }
  by rewrite lookup_alter_ne by done.
Qed.
Lemma alter_mono {A} f (m1 m2 : M A) i : m1 ⊆ m2 → alter f i m1 ⊆ alter f i m2.
Proof.
  rewrite !map_subseteq_spec. intros ? j x.
  rewrite !lookup_alter_Some. naive_solver.
Qed.
Lemma alter_strict_mono {A} f (m1 m2 : M A) i :
  m1 ⊂ m2 → alter f i m1 ⊂ alter f i m2.
Proof.
  rewrite !map_subset_alt.
  intros [? (j&?&?)]; split; auto using alter_mono.
  exists j. by rewrite lookup_alter_None, lookup_alter_is_Some.
Qed.

(** ** Properties of the [delete] operation *)
Lemma lookup_delete {A} (m : M A) i : delete i m !! i = None.
Proof. apply lookup_partial_alter. Qed.
Lemma lookup_total_delete `{!Inhabited A} (m : M A) i :
  delete i m !!! i = inhabitant.
Proof. by rewrite lookup_total_alt, lookup_delete. Qed.
Lemma lookup_delete_ne {A} (m : M A) i j : i ≠ j → delete i m !! j = m !! j.
Proof. apply lookup_partial_alter_ne. Qed.
Lemma lookup_total_delete_ne `{!Inhabited A} (m : M A) i j :
  i ≠ j → delete i m !!! j = m !!! j.
Proof. intros. by rewrite lookup_total_alt, lookup_delete_ne. Qed.
Lemma lookup_delete_Some {A} (m : M A) i j y :
  delete i m !! j = Some y ↔ i ≠ j ∧ m !! j = Some y.
Proof.
  split.
  - destruct (decide (i = j)) as [->|?];
      rewrite ?lookup_delete, ?lookup_delete_ne; intuition congruence.
  - intros [??]. by rewrite lookup_delete_ne.
Qed.
Lemma lookup_delete_is_Some {A} (m : M A) i j :
  is_Some (delete i m !! j) ↔ i ≠ j ∧ is_Some (m !! j).
Proof. unfold is_Some; setoid_rewrite lookup_delete_Some; naive_solver. Qed.
Lemma lookup_delete_None {A} (m : M A) i j :
  delete i m !! j = None ↔ i = j ∨ m !! j = None.
Proof.
  destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_delete, ?lookup_delete_ne; tauto.
Qed.
Lemma delete_empty {A} i : delete i ∅ =@{M A} ∅.
Proof. rewrite <-(partial_alter_self ∅) at 2. by rewrite lookup_empty. Qed.
Lemma delete_commute {A} (m : M A) i j :
  delete i (delete j m) = delete j (delete i m).
Proof.
  destruct (decide (i = j)) as [->|]; [done|]. by apply partial_alter_commute.
Qed.
Lemma delete_notin {A} (m : M A) i : m !! i = None → delete i m = m.
Proof.
  intros. apply map_eq. intros j. by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_delete, ?lookup_delete_ne.
Qed.
Lemma delete_idemp {A} (m : M A) i :
  delete i (delete i m) = delete i m.
Proof. by setoid_rewrite <-partial_alter_compose. Qed.
Lemma delete_partial_alter {A} (m : M A) i f :
  m !! i = None → delete i (partial_alter f i m) = m.
Proof.
  intros. unfold delete, map_delete. rewrite <-partial_alter_compose.
  unfold compose. by apply partial_alter_self_alt.
Qed.
Lemma delete_insert {A} (m : M A) i x :
  m !! i = None → delete i (<[i:=x]>m) = m.
Proof. apply delete_partial_alter. Qed.
Lemma delete_insert_delete {A} (m : M A) i x :
  delete i (<[i:=x]>m) = delete i m.
Proof. by setoid_rewrite <-partial_alter_compose. Qed.
Lemma delete_insert_ne {A} (m : M A) i j x :
  i ≠ j → delete i (<[j:=x]>m) = <[j:=x]>(delete i m).
Proof. intro. by apply partial_alter_commute. Qed.
Lemma delete_alter {A} (m : M A) i f :
  delete i (alter f i m) = delete i m.
Proof.
  unfold delete, alter, map_delete, map_alter.
  by rewrite <-partial_alter_compose.
Qed.
Lemma delete_alter_ne {A} (m : M A) i j f :
  i ≠ j → delete i (alter f j m) = alter f j (delete i m).
Proof. intro. by apply partial_alter_commute. Qed.
Lemma delete_subseteq {A} (m : M A) i : delete i m ⊆ m.
Proof.
  rewrite !map_subseteq_spec. intros j x. rewrite lookup_delete_Some. tauto.
Qed.
Lemma delete_subset {A} (m : M A) i : is_Some (m !! i) → delete i m ⊂ m.
Proof.
  intros [x ?]; apply map_subset_alt; split; [apply delete_subseteq|].
  exists i. rewrite lookup_delete; eauto.
Qed.
Lemma delete_mono {A} (m1 m2 : M A) i : m1 ⊆ m2 → delete i m1 ⊆ delete i m2.
Proof.
  rewrite !map_subseteq_spec. intros ? j x.
  rewrite !lookup_delete_Some. intuition eauto.
Qed.

(** ** Properties of the [insert] operation *)
Lemma lookup_insert {A} (m : M A) i x : <[i:=x]>m !! i = Some x.
Proof. unfold insert. apply lookup_partial_alter. Qed.
Lemma lookup_total_insert `{!Inhabited A} (m : M A) i x : <[i:=x]>m !!! i = x.
Proof. by rewrite lookup_total_alt, lookup_insert. Qed.
Lemma lookup_insert_rev {A}  (m : M A) i x y : <[i:=x]>m !! i = Some y → x = y.
Proof. rewrite lookup_insert. congruence. Qed.
Lemma lookup_insert_ne {A} (m : M A) i j x : i ≠ j → <[i:=x]>m !! j = m !! j.
Proof. unfold insert. apply lookup_partial_alter_ne. Qed.
Lemma lookup_total_insert_ne `{!Inhabited A} (m : M A) i j x :
  i ≠ j → <[i:=x]>m !!! j = m !!! j.
Proof. intros. by rewrite lookup_total_alt, lookup_insert_ne. Qed.
Lemma insert_insert {A} (m : M A) i x y : <[i:=x]>(<[i:=y]>m) = <[i:=x]>m.
Proof. unfold insert, map_insert. by rewrite <-partial_alter_compose. Qed.
Lemma insert_commute {A} (m : M A) i j x y :
  i ≠ j → <[i:=x]>(<[j:=y]>m) = <[j:=y]>(<[i:=x]>m).
Proof. apply partial_alter_commute. Qed.
Lemma lookup_insert_Some {A} (m : M A) i j x y :
  <[i:=x]>m !! j = Some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ m !! j = Some y).
Proof.
  split.
  - destruct (decide (i = j)) as [->|?];
      rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
  - intros [[-> ->]|[??]]; [apply lookup_insert|]. by rewrite lookup_insert_ne.
Qed.
Lemma lookup_insert_is_Some {A} (m : M A) i j x :
  is_Some (<[i:=x]>m !! j) ↔ i = j ∨ i ≠ j ∧ is_Some (m !! j).
Proof. unfold is_Some; setoid_rewrite lookup_insert_Some; naive_solver. Qed.
Lemma lookup_insert_is_Some' {A} (m : M A) i j x :
  is_Some (<[i:=x]>m !! j) ↔ i = j ∨ is_Some (m !! j).
Proof. rewrite lookup_insert_is_Some. destruct (decide (i=j)); naive_solver. Qed.
Lemma lookup_insert_None {A} (m : M A) i j x :
  <[i:=x]>m !! j = None ↔ m !! j = None ∧ i ≠ j.
Proof.
  split; [|by intros [??]; rewrite lookup_insert_ne].
  destruct (decide (i = j)) as [->|];
    rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
Qed.
Lemma insert_id {A} (m : M A) i x : m !! i = Some x → <[i:=x]>m = m.
Proof.
  intros; apply map_eq; intros j; destruct (decide (i = j)) as [->|];
    by rewrite ?lookup_insert, ?lookup_insert_ne by done.
Qed.
Lemma insert_included {A} R `{!Reflexive R} (m : M A) i x :
  (∀ y, m !! i = Some y → R y x) → map_included R m (<[i:=x]>m).
Proof.
  intros ? j; destruct (decide (i = j)) as [->|].
  - rewrite lookup_insert. destruct (m !! j); simpl; eauto.
  - rewrite lookup_insert_ne by done. by destruct (m !! j); simpl.
Qed.
Lemma insert_empty {A} i (x : A) : <[i:=x]> ∅ =@{M A} {[i := x]}.
Proof. done. Qed.
Lemma insert_non_empty {A} (m : M A) i x : <[i:=x]>m ≠ ∅.
Proof.
  intros Hi%(f_equal (.!! i)). by rewrite lookup_insert, lookup_empty in Hi.
Qed.
Lemma insert_delete_insert {A} (m : M A) i x : <[i:=x]>(delete i m) = <[i:=x]> m.
Proof. symmetry; apply (partial_alter_compose (λ _, Some x)). Qed.
Lemma insert_delete {A} (m : M A) i x :
  m !! i = Some x → <[i:=x]> (delete i m) = m.
Proof. intros. rewrite insert_delete_insert, insert_id; done. Qed.

Lemma insert_subseteq {A} (m : M A) i x : m !! i = None → m ⊆ <[i:=x]>m.
Proof. apply partial_alter_subseteq. Qed.
Lemma insert_subset {A} (m : M A) i x : m !! i = None → m ⊂ <[i:=x]>m.
Proof. intro. apply partial_alter_subset; eauto. Qed.
Lemma insert_mono {A} (m1 m2 : M A) i x : m1 ⊆ m2 → <[i:=x]> m1 ⊆ <[i:=x]>m2.
Proof.
  rewrite !map_subseteq_spec.
  intros Hm j y. rewrite !lookup_insert_Some. naive_solver.
Qed.
Lemma insert_subseteq_r {A} (m1 m2 : M A) i x :
  m1 !! i = None → m1 ⊆ m2 → m1 ⊆ <[i:=x]>m2.
Proof.
  intros. trans (<[i:=x]> m1); eauto using insert_subseteq, insert_mono.
Qed.
Lemma insert_subseteq_l {A} (m1 m2 : M A) i x :
  m2 !! i = Some x → m1 ⊆ m2 → <[i:=x]> m1 ⊆ m2.
Proof.
  intros Hi Hincl. etrans; [apply insert_mono, Hincl|]. by rewrite insert_id.
Qed.

Lemma insert_delete_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊆ m2 → m1 ⊆ delete i m2.
Proof.
  rewrite !map_subseteq_spec. intros Hi Hix j y Hj.
  destruct (decide (i = j)) as [->|]; [congruence|].
  rewrite lookup_delete_ne by done.
  apply Hix; by rewrite lookup_insert_ne by done.
Qed.
Lemma delete_insert_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → delete i m1 ⊆ m2 → m1 ⊆ <[i:=x]> m2.
Proof.
  rewrite !map_subseteq_spec.
  intros Hix Hi j y Hj. destruct (decide (i = j)) as [->|?].
  - rewrite lookup_insert. congruence.
  - rewrite lookup_insert_ne by done. apply Hi. by rewrite lookup_delete_ne.
Qed.
Lemma insert_delete_subset {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 → m1 ⊂ delete i m2.
Proof.
  intros ? [Hm12 Hm21]; split; [eauto using insert_delete_subseteq|].
  contradict Hm21. apply delete_insert_subseteq; auto.
  eapply lookup_weaken, Hm12. by rewrite lookup_insert.
Qed.
Lemma insert_subset_inv {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 →
  ∃ m2', m2 = <[i:=x]>m2' ∧ m1 ⊂ m2' ∧ m2' !! i = None.
Proof.
  intros Hi Hm1m2. exists (delete i m2). split_and?.
  - rewrite insert_delete; [done|].
    eapply lookup_weaken, strict_include; eauto. by rewrite lookup_insert.
  - eauto using insert_delete_subset.
  - by rewrite lookup_delete.
Qed.

(** ** Properties of the singleton maps *)
Lemma lookup_singleton_Some {A} i j (x y : A) :
  ({[i := x]} : M A) !! j = Some y ↔ i = j ∧ x = y.
Proof.
  rewrite <-insert_empty,lookup_insert_Some, lookup_empty; intuition congruence.
Qed.
Lemma lookup_singleton_None {A} i j (x : A) :
  ({[i := x]} : M A) !! j = None ↔ i ≠ j.
Proof. rewrite <-insert_empty,lookup_insert_None, lookup_empty; tauto. Qed.
Lemma lookup_singleton {A} i (x : A) : ({[i := x]} : M A) !! i = Some x.
Proof. by rewrite lookup_singleton_Some. Qed.
Lemma lookup_total_singleton `{!Inhabited A} i (x : A) :
  ({[i := x]} : M A) !!! i = x.
Proof. by rewrite lookup_total_alt, lookup_singleton. Qed.
Lemma lookup_singleton_ne {A} i j (x : A) :
  i ≠ j → ({[i := x]} : M A) !! j = None.
Proof. by rewrite lookup_singleton_None. Qed.
Lemma lookup_total_singleton_ne `{!Inhabited A} i j (x : A) :
  i ≠ j → ({[i := x]} : M A) !!! j = inhabitant.
Proof. intros. by rewrite lookup_total_alt, lookup_singleton_ne. Qed.

Global Instance map_singleton_inj {A} : Inj2 (=) (=) (=) (singletonM (M:=M A)).
Proof.
  intros i1 x1 i2 x2 Heq%(f_equal (lookup i1)).
  rewrite lookup_singleton in Heq. destruct (decide (i1 = i2)) as [->|].
  - rewrite lookup_singleton in Heq. naive_solver.
  - rewrite lookup_singleton_ne in Heq by done. naive_solver.
Qed.

Lemma map_non_empty_singleton {A} i (x : A) : {[i := x]} ≠@{M A} ∅.
Proof.
  intros Hix. apply (f_equal (.!! i)) in Hix.
  by rewrite lookup_empty, lookup_singleton in Hix.
Qed.
Lemma insert_singleton {A} i (x y : A) : <[i:=y]> {[i := x]} =@{M A} {[i := y]}.
Proof.
  unfold singletonM, map_singleton, insert, map_insert.
  by rewrite <-partial_alter_compose.
Qed.
Lemma alter_singleton {A} (f : A → A) i x :
  alter f i {[i := x]} =@{M A} {[i := f x]}.
Proof.
  intros. apply map_eq. intros i'. destruct (decide (i = i')) as [->|?].
  - by rewrite lookup_alter, !lookup_singleton.
  - by rewrite lookup_alter_ne, !lookup_singleton_ne.
Qed.
Lemma alter_singleton_ne {A} (f : A → A) i j x :
  i ≠ j → alter f i {[j := x]}=@{M A} {[j := x]}.
Proof.
  intros. apply map_eq; intros i'. by destruct (decide (i = i')) as [->|?];
    rewrite ?lookup_alter, ?lookup_singleton_ne, ?lookup_alter_ne by done.
Qed.
Lemma singleton_non_empty {A} i (x : A) : {[i:=x]} ≠@{M A} ∅.
Proof. apply insert_non_empty. Qed.
Lemma delete_singleton {A} i (x : A) : delete i {[i := x]} =@{M A} ∅.
Proof. setoid_rewrite <-partial_alter_compose. apply delete_empty. Qed.
Lemma delete_singleton_ne {A} i j (x : A) :
  i ≠ j → delete i {[j := x]} =@{M A} {[j := x]}.
Proof. intro. apply delete_notin. by apply lookup_singleton_ne. Qed.

Lemma map_singleton_subseteq_l {A} i (x : A) (m : M A) :
  {[i := x]} ⊆ m ↔ m !! i = Some x.
Proof.
  rewrite map_subseteq_spec. setoid_rewrite lookup_singleton_Some. naive_solver.
Qed.
Lemma map_singleton_subseteq {A} i j (x y : A) :
  {[i := x]} ⊆@{M A} {[j := y]} ↔ i = j ∧ x = y.
Proof.
  rewrite map_subseteq_spec. setoid_rewrite lookup_singleton_Some. naive_solver.
Qed.

(** ** Properties of the map operations *)
Global Instance map_fmap_inj {A B} (f : A → B) :
  Inj (=) (=) f → Inj (=@{M A}) (=@{M B}) (fmap f).
Proof.
  intros ? m1 m2 Hm. apply map_eq; intros i.
  apply (inj (fmap (M:=option) f)). by rewrite <-!lookup_fmap, Hm.
Qed.

Lemma lookup_fmap_Some {A B} (f : A → B) (m : M A) i y :
  (f <$> m) !! i = Some y ↔ ∃ x, f x = y ∧ m !! i = Some x.
Proof. rewrite lookup_fmap, fmap_Some. naive_solver. Qed.
Lemma lookup_omap_Some {A B} (f : A → option B) (m : M A) i y :
  omap f m !! i = Some y ↔ ∃ x, f x = Some y ∧ m !! i = Some x.
Proof. rewrite lookup_omap, bind_Some. naive_solver. Qed.
Lemma lookup_omap_id_Some {A} (m : M (option A)) i x :
  omap id m !! i = Some x ↔ m !! i = Some (Some x).
Proof. rewrite lookup_omap_Some. naive_solver. Qed.

Lemma fmap_empty {A B} (f : A → B) : f <$> ∅ =@{M B} ∅.
Proof. apply map_empty; intros i. by rewrite lookup_fmap, lookup_empty. Qed.
Lemma omap_empty {A B} (f : A → option B) : omap f ∅ =@{M B} ∅.
Proof. apply map_empty; intros i. by rewrite lookup_omap, lookup_empty. Qed.

Lemma fmap_empty_iff {A B} (f : A → B) m : f <$> m =@{M B} ∅ ↔ m = ∅.
Proof.
  split; [|intros ->; by rewrite fmap_empty].
  intros Hm. apply map_eq; intros i. generalize (f_equal (lookup i) Hm).
  by rewrite lookup_fmap, !lookup_empty, fmap_None.
Qed.
Lemma fmap_empty_inv {A B} (f : A → B) m : f <$> m =@{M B} ∅ → m = ∅.
Proof. apply fmap_empty_iff. Qed.

Lemma fmap_insert {A B} (f: A → B) (m : M A) i x :
  f <$> <[i:=x]>m = <[i:=f x]>(f <$> m).
Proof.
  apply map_eq; intros i'; destruct (decide (i' = i)) as [->|].
  - by rewrite lookup_fmap, !lookup_insert.
  - by rewrite lookup_fmap, !lookup_insert_ne, lookup_fmap by done.
Qed.
Lemma omap_insert {A B} (f : A → option B) (m : M A) i x :
  omap f (<[i:=x]>m) =
    (match f x with Some y => <[i:=y]> | None => delete i end) (omap f m).
Proof.
  intros; apply map_eq; intros i'; destruct (decide (i' = i)) as [->|].
  - rewrite lookup_omap, !lookup_insert. destruct (f x) as [y|] eqn:Hx; simpl.
    + by rewrite lookup_insert.
    + by rewrite lookup_delete, Hx.
  - rewrite lookup_omap, !lookup_insert_ne by done.
    destruct (f x) as [y|] eqn:Hx; simpl.
    + by rewrite lookup_insert_ne, lookup_omap by done.
    + by rewrite lookup_delete_ne, lookup_omap by done.
Qed.
Lemma omap_insert_Some {A B} (f : A → option B) (m : M A) i x y :
  f x = Some y → omap f (<[i:=x]>m) = <[i:=y]>(omap f m).
Proof. intros Hx. by rewrite omap_insert, Hx. Qed.
Lemma omap_insert_None {A B} (f : A → option B) (m : M A) i x :
  f x = None → omap f (<[i:=x]>m) = delete i (omap f m).
Proof. intros Hx. by rewrite omap_insert, Hx. Qed.

Lemma fmap_delete {A B} (f: A → B) (m : M A) i :
  f <$> delete i m = delete i (f <$> m).
Proof.
  apply map_eq; intros i'; destruct (decide (i' = i)) as [->|].
  - by rewrite lookup_fmap, !lookup_delete.
  - by rewrite lookup_fmap, !lookup_delete_ne, lookup_fmap by done.
Qed.
Lemma omap_delete {A B} (f: A → option B) (m : M A) i :
  omap f (delete i m) = delete i (omap f m).
Proof.
  apply map_eq; intros i'; destruct (decide (i' = i)) as [->|].
  - by rewrite lookup_omap, !lookup_delete.
  - by rewrite lookup_omap, !lookup_delete_ne, lookup_omap by done.
Qed.

Lemma map_fmap_singleton {A B} (f : A → B) i x :
  f <$> {[i := x]} =@{M B} {[i := f x]}.
Proof.
  by unfold singletonM, map_singleton; rewrite fmap_insert, fmap_empty.
Qed.
Lemma map_fmap_singleton_inv {A B} (f : A → B) (m : M A) i y :
  f <$> m = {[i := y]} → ∃ x, y = f x ∧ m = {[ i := x ]}.
Proof.
  intros Hm. pose proof (f_equal (.!! i) Hm) as Hmi.
  rewrite lookup_fmap, lookup_singleton, fmap_Some in Hmi.
  destruct Hmi as (x&?&->). exists x. split; [done|].
  apply map_eq; intros j. destruct (decide (i = j)) as[->|?].
  - by rewrite lookup_singleton.
  - rewrite lookup_singleton_ne by done.
    apply (fmap_None f). by rewrite <-lookup_fmap, Hm, lookup_singleton_ne.
Qed.

Lemma omap_singleton {A B} (f : A → option B) i x :
  omap f {[ i := x ]} =@{M B} match f x with Some y => {[ i:=y ]} | None => ∅ end.
Proof.
  rewrite <-insert_empty, omap_insert, omap_empty. destruct (f x) as [y|]; simpl.
  - by rewrite insert_empty.
  - by rewrite delete_empty.
Qed.
Lemma omap_singleton_Some {A B} (f : A → option B) i x y :
  f x = Some y → omap f {[ i := x ]} =@{M B} {[ i := y ]}.
Proof. intros Hx. by rewrite omap_singleton, Hx. Qed.
Lemma omap_singleton_None {A B} (f : A → option B) i x :
  f x = None → omap f {[ i := x ]} =@{M B} ∅.
Proof. intros Hx. by rewrite omap_singleton, Hx. Qed.

Lemma map_fmap_id {A} (m : M A) : id <$> m = m.
Proof. apply map_eq; intros i; by rewrite lookup_fmap, option_fmap_id. Qed.
Lemma map_fmap_compose {A B C} (f : A → B) (g : B → C) (m : M A) :
  g ∘ f <$> m = g <$> (f <$> m).
Proof. apply map_eq; intros i; by rewrite !lookup_fmap,option_fmap_compose. Qed.
Lemma map_fmap_ext {A B} (f1 f2 : A → B) (m : M A) :
  (∀ i x, m !! i = Some x → f1 x = f2 x) → f1 <$> m = f2 <$> m.
Proof.
  intros Hi; apply map_eq; intros i; rewrite !lookup_fmap.
  by destruct (m !! i) eqn:?; simpl; erewrite ?Hi by eauto.
Qed.
Lemma omap_ext {A B} (f1 f2 : A → option B) (m : M A) :
  (∀ i x, m !! i = Some x → f1 x = f2 x) → omap f1 m = omap f2 m.
Proof.
  intros Hi; apply map_eq; intros i; rewrite !lookup_omap.
  by destruct (m !! i) eqn:?; simpl; erewrite ?Hi by eauto.
Qed.

Lemma map_fmap_omap {A B C} (f : A → option B) (g : B → C) (m : M A) :
  g <$> omap f m = omap (λ x, g <$> f x) m.
Proof.
  apply map_eq. intros i.
  rewrite !lookup_fmap, !lookup_omap. destruct (m !! i); done.
Qed.

Lemma map_fmap_alt {A B} (f : A → B) (m : M A) :
  f <$> m = omap (λ x, Some (f x)) m.
Proof.
  apply map_eq. intros i.
  rewrite lookup_fmap, lookup_omap. destruct (m !! i); done.
Qed.

Lemma map_fmap_mono {A B} (f : A → B) (m1 m2 : M A) :
  m1 ⊆ m2 → f <$> m1 ⊆ f <$> m2.
Proof.
  rewrite !map_subseteq_spec; intros Hm i x.
  rewrite !lookup_fmap, !fmap_Some. naive_solver.
Qed.
Lemma map_fmap_strict_mono {A B} (f : A → B) (m1 m2 : M A) :
  m1 ⊂ m2 → f <$> m1 ⊂ f <$> m2.
Proof.
  rewrite !map_subset_alt.
  intros [? (j&?&?)]; split; auto using map_fmap_mono.
  exists j. by rewrite !lookup_fmap, fmap_None, fmap_is_Some.
Qed.
Lemma map_omap_mono {A B} (f : A → option B) (m1 m2 : M A) :
  m1 ⊆ m2 → omap f m1 ⊆ omap f m2.
Proof.
  rewrite !map_subseteq_spec; intros Hm i x.
  rewrite !lookup_omap, !bind_Some. naive_solver.
Qed.

(** ** Properties of conversion to lists *)
Lemma elem_of_map_to_list' {A} (m : M A) ix :
  ix ∈ map_to_list m ↔ m !! ix.1 = Some (ix.2).
Proof. destruct ix as [i x]. apply elem_of_map_to_list. Qed.
Lemma map_to_list_unique {A} (m : M A) i x y :
  (i,x) ∈ map_to_list m → (i,y) ∈ map_to_list m → x = y.
Proof. rewrite !elem_of_map_to_list. congruence. Qed.
Lemma NoDup_fst_map_to_list {A} (m : M A) : NoDup ((map_to_list m).*1).
Proof. eauto using NoDup_fmap_fst, map_to_list_unique, NoDup_map_to_list. Qed.
Lemma elem_of_list_to_map_1' {A} (l : list (K * A)) i x :
  (∀ y, (i,y) ∈ l → x = y) → (i,x) ∈ l → (list_to_map l : M A) !! i = Some x.
Proof.
  induction l as [|[j y] l IH]; csimpl; [by rewrite elem_of_nil|].
  setoid_rewrite elem_of_cons.
  intros Hdup [?|?]; simplify_eq; [by rewrite lookup_insert|].
  destruct (decide (i = j)) as [->|].
  - rewrite lookup_insert; f_equal; eauto using eq_sym.
  - rewrite lookup_insert_ne by done; eauto.
Qed.
Lemma elem_of_list_to_map_1 {A} (l : list (K * A)) i x :
  NoDup (l.*1) → (i,x) ∈ l → (list_to_map l : M A) !! i = Some x.
Proof.
  intros ? Hx; apply elem_of_list_to_map_1'; eauto using NoDup_fmap_fst.
  intros y; revert Hx. rewrite !elem_of_list_lookup; intros [i' Hi'] [j' Hj'].
  cut (i' = j'); [naive_solver|]. apply NoDup_lookup with (l.*1) i;
    by rewrite ?list_lookup_fmap, ?Hi', ?Hj'.
Qed.
Lemma elem_of_list_to_map_2 {A} (l : list (K * A)) i x :
  (list_to_map l : M A) !! i = Some x → (i,x) ∈ l.
Proof.
  induction l as [|[j y] l IH]; simpl; [by rewrite lookup_empty|].
  rewrite elem_of_cons. destruct (decide (i = j)) as [->|];
    rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
Qed.
Lemma elem_of_list_to_map' {A} (l : list (K * A)) i x :
  (∀ x', (i,x) ∈ l → (i,x') ∈ l → x = x') →
  (i,x) ∈ l ↔ (list_to_map l : M A) !! i = Some x.
Proof. split; auto using elem_of_list_to_map_1', elem_of_list_to_map_2. Qed.
Lemma elem_of_list_to_map {A} (l : list (K * A)) i x :
  NoDup (l.*1) → (i,x) ∈ l ↔ (list_to_map l : M A) !! i = Some x.
Proof. split; auto using elem_of_list_to_map_1, elem_of_list_to_map_2. Qed.

Lemma not_elem_of_list_to_map_1 {A} (l : list (K * A)) i :
  i ∉ l.*1 → (list_to_map l : M A) !! i = None.
Proof.
  rewrite elem_of_list_fmap, eq_None_not_Some. intros Hi [x ?]; destruct Hi.
  exists (i,x); simpl; auto using elem_of_list_to_map_2.
Qed.
Lemma not_elem_of_list_to_map_2 {A} (l : list (K * A)) i :
  (list_to_map l : M A) !! i = None → i ∉ l.*1.
Proof.
  induction l as [|[j y] l IH]; csimpl; [rewrite elem_of_nil; tauto|].
  rewrite elem_of_cons. destruct (decide (i = j)); simplify_eq.
  - by rewrite lookup_insert.
  - by rewrite lookup_insert_ne; intuition.
Qed.
Lemma not_elem_of_list_to_map {A} (l : list (K * A)) i :
  i ∉ l.*1 ↔ (list_to_map l : M A) !! i = None.
Proof. red; auto using not_elem_of_list_to_map_1,not_elem_of_list_to_map_2. Qed.
Lemma list_to_map_proper {A} (l1 l2 : list (K * A)) :
  NoDup (l1.*1) → l1 ≡ₚ l2 → (list_to_map l1 : M A) = list_to_map l2.
Proof.
  intros ? Hperm. apply map_eq. intros i. apply option_eq. intros x.
  by rewrite <-!elem_of_list_to_map; rewrite <-?Hperm.
Qed.
Lemma list_to_map_inj {A} (l1 l2 : list (K * A)) :
  NoDup (l1.*1) → NoDup (l2.*1) →
  (list_to_map l1 : M A) = list_to_map l2 → l1 ≡ₚ l2.
Proof.
  intros ?? Hl1l2. apply NoDup_Permutation; [by eauto using NoDup_fmap_1..|].
  intros [i x]. by rewrite !elem_of_list_to_map, Hl1l2.
Qed.
Lemma list_to_map_to_list {A} (m : M A) : list_to_map (map_to_list m) = m.
Proof.
  apply map_eq. intros i. apply option_eq. intros x.
  by rewrite <-elem_of_list_to_map, elem_of_map_to_list
    by auto using NoDup_fst_map_to_list.
Qed.
Lemma map_to_list_to_map {A} (l : list (K * A)) :
  NoDup (l.*1) → map_to_list (list_to_map l) ≡ₚ l.
Proof. auto using list_to_map_inj, NoDup_fst_map_to_list, list_to_map_to_list. Qed.
Lemma map_to_list_inj {A} (m1 m2 : M A) :
  map_to_list m1 ≡ₚ map_to_list m2 → m1 = m2.
Proof.
  intros. rewrite <-(list_to_map_to_list m1), <-(list_to_map_to_list m2).
  auto using list_to_map_proper, NoDup_fst_map_to_list.
Qed.
Lemma list_to_map_flip {A} (m1 : M A) l2 :
  map_to_list m1 ≡ₚ l2 → m1 = list_to_map l2.
Proof.
  intros. rewrite <-(list_to_map_to_list m1).
  auto using list_to_map_proper, NoDup_fst_map_to_list.
Qed.

Lemma list_to_map_nil {A} : list_to_map [] =@{M A} ∅.
Proof. done. Qed.
Lemma list_to_map_cons {A} (l : list (K * A)) i x :
  list_to_map ((i, x) :: l) =@{M A} <[i:=x]>(list_to_map l).
Proof. done. Qed.
Lemma list_to_map_snoc {A} (l : list (K * A)) i x :
  i ∉ l.*1 → list_to_map (l ++ [(i, x)]) =@{M A} <[i:=x]>(list_to_map l).
Proof.
  induction l as [|[k y] l IH]; [done|]. csimpl.
  intros [Hneq Hni]%not_elem_of_cons.
  by rewrite (IH Hni), insert_commute by done.
Qed.
Lemma list_to_map_fmap {A B} (f : A → B) l :
  list_to_map (prod_map id f <$> l) = f <$> (list_to_map l : M A).
Proof.
  induction l as [|[i x] l IH]; csimpl; rewrite ?fmap_empty; auto.
  rewrite <-list_to_map_cons; simpl. by rewrite IH, <-fmap_insert.
Qed.

Lemma map_to_list_empty {A} : map_to_list ∅ = @nil (K * A).
Proof.
  apply elem_of_nil_inv. intros [i x].
  rewrite elem_of_map_to_list. apply lookup_empty_Some.
Qed.
Lemma map_to_list_insert {A} (m : M A) i x :
  m !! i = None → map_to_list (<[i:=x]>m) ≡ₚ (i,x) :: map_to_list m.
Proof.
  intros. apply list_to_map_inj; csimpl.
  - apply NoDup_fst_map_to_list.
  - constructor; [|by auto using NoDup_fst_map_to_list].
    rewrite elem_of_list_fmap. intros [[??] [? Hlookup]]; subst; simpl in *.
    rewrite elem_of_map_to_list in Hlookup. congruence.
  - by rewrite !list_to_map_to_list.
Qed.
Lemma map_to_list_singleton {A} i (x : A) :
  map_to_list ({[i:=x]} : M A) = [(i,x)].
Proof.
  apply Permutation_singleton_r. unfold singletonM, map_singleton.
  by rewrite map_to_list_insert, map_to_list_empty by eauto using lookup_empty.
Qed.
Lemma map_to_list_delete {A} (m : M A) i x :
  m !! i = Some x → (i,x) :: map_to_list (delete i m) ≡ₚ map_to_list m.
Proof.
  intros. rewrite <-map_to_list_insert by (by rewrite lookup_delete).
  by rewrite insert_delete.
Qed.

Lemma map_to_list_submseteq {A} (m1 m2 : M A) :
  m1 ⊆ m2 → map_to_list m1 ⊆+ map_to_list m2.
Proof.
  intros; apply NoDup_submseteq; [by eauto using NoDup_map_to_list|].
  intros [i x]. rewrite !elem_of_map_to_list; eauto using lookup_weaken.
Qed.
Lemma map_to_list_fmap {A B} (f : A → B) (m : M A) :
  map_to_list (f <$> m) ≡ₚ prod_map id f <$> map_to_list m.
Proof.
  assert (NoDup ((prod_map id f <$> map_to_list m).*1)).
  { erewrite <-list_fmap_compose, (list_fmap_ext _ fst) by done.
    apply NoDup_fst_map_to_list. }
  rewrite <-(list_to_map_to_list m) at 1.
  by rewrite <-list_to_map_fmap, map_to_list_to_map.
Qed.

Lemma map_to_list_empty_iff {A} (m : M A) : map_to_list m = [] ↔ m = ∅.
Proof.
  split.
  - rewrite <-Permutation_nil_r, <-map_to_list_empty. apply map_to_list_inj.
  - intros ->. apply map_to_list_empty.
Qed.

Lemma map_to_list_insert_inv {A} (m : M A) l i x :
  map_to_list m ≡ₚ (i,x) :: l → m = <[i:=x]>(list_to_map l).
Proof.
  intros Hperm. apply map_to_list_inj.
  assert (i ∉ l.*1 ∧ NoDup (l.*1)) as [].
  { rewrite <-NoDup_cons. change (NoDup (((i,x)::l).*1)). rewrite <-Hperm.
    auto using NoDup_fst_map_to_list. }
  rewrite Hperm, map_to_list_insert, map_to_list_to_map;
    auto using not_elem_of_list_to_map_1.
Qed.

Lemma map_to_list_length {A} (m : M A) :
  length (map_to_list m) = size m.
Proof.
  apply (map_fold_ind (λ n m, length (map_to_list m) = n)); clear m.
  { by rewrite map_to_list_empty. }
  intros i x m n ? IH. by rewrite map_to_list_insert, <-IH by done.
Qed.

Lemma map_choose {A} (m : M A) : m ≠ ∅ → ∃ i x, m !! i = Some x.
Proof.
  rewrite <-map_to_list_empty_iff.
  intros Hemp. destruct (map_to_list m) as [|[i x] l] eqn:Hm; [done|].
  exists i, x. rewrite <-elem_of_map_to_list, Hm. by left.
Qed.

Global Instance map_eq_dec_empty {A} (m : M A) : Decision (m = ∅) | 20.
Proof.
  refine (cast_if (decide (map_to_list m = [])));
    by rewrite <-?map_to_list_empty_iff.
Defined.

Lemma map_choose_or_empty {A} (m : M A) : (∃ i x, m !! i = Some x) ∨ m = ∅.
Proof. destruct (decide (m = ∅)); [right|left]; auto using map_choose. Qed.

(** Properties of the imap function *)
Lemma map_lookup_imap {A B} (f : K → A → option B) (m : M A) i :
  map_imap f m !! i = m !! i ≫= f i.
Proof.
  unfold map_imap; destruct (m !! i ≫= f i) as [y|] eqn:Hi; simpl.
  - destruct (m !! i) as [x|] eqn:?; simplify_eq/=.
    apply elem_of_list_to_map_1'.
    { intros y'; rewrite elem_of_list_omap; intros ([i' x']&Hi'&?).
      by rewrite elem_of_map_to_list in Hi'; simplify_option_eq. }
    apply elem_of_list_omap; exists (i,x); split;
      [by apply elem_of_map_to_list|by simplify_option_eq].
  - apply not_elem_of_list_to_map; rewrite elem_of_list_fmap.
    intros ([i' x]&->&Hi'); simplify_eq/=.
    rewrite elem_of_list_omap in Hi'; destruct Hi' as ([j y]&Hj&?).
    rewrite elem_of_map_to_list in Hj; simplify_option_eq.
Qed.

Lemma map_imap_Some {A} (m : M A) : map_imap (λ _, Some) m = m.
Proof.
  apply map_eq. intros i. rewrite map_lookup_imap. by destruct (m !! i).
Qed.

Lemma map_imap_insert {A B} (f : K → A → option B) i x (m : M A) :
  map_imap f (<[i:=x]> m) =
    (match f i x with Some y => <[i:=y]> | None => delete i end) (map_imap f m).
Proof.
  destruct (f i x) as [y|] eqn:Hw; simpl.
  - apply map_eq. intros k. rewrite map_lookup_imap.
    destruct (decide (k = i)) as [->|Hk_not_i].
    + by rewrite lookup_insert, lookup_insert.
    + rewrite !lookup_insert_ne by done.
      by rewrite map_lookup_imap.
  - apply map_eq. intros k. rewrite map_lookup_imap.
    destruct (decide (k = i)) as [->|Hk_not_i].
    + by rewrite lookup_insert, lookup_delete.
    + rewrite lookup_insert_ne, lookup_delete_ne by done.
      by rewrite map_lookup_imap.
Qed.
Lemma map_imap_insert_Some {A B} (f : K → A → option B) i x (m : M A) y :
  f i x = Some y → map_imap f (<[i:=x]> m) = <[i:=y]> (map_imap f m).
Proof. intros Hi. by rewrite map_imap_insert, Hi. Qed.
Lemma map_imap_insert_None {A B} (f : K → A → option B) i x (m : M A) :
  f i x = None → map_imap f (<[i:=x]> m) = delete i (map_imap f m).
Proof. intros Hi. by rewrite map_imap_insert, Hi. Qed.

Lemma map_imap_delete {A B} (f : K → A → option B) (m : M A) (i : K) :
  map_imap f (delete i m) = delete i (map_imap f m).
Proof.
  apply map_eq. intros k. rewrite map_lookup_imap.
  destruct (decide (k = i)) as [->|Hk_not_i].
  - by rewrite !lookup_delete.
  - rewrite !lookup_delete_ne by done.
    by rewrite map_lookup_imap.
Qed.

Lemma map_imap_ext {A1 A2 B} (f1 : K → A1 → option B)
    (f2 : K → A2 → option B) (m1 : M A1) (m2 : M A2) :
  (∀ k, f1 k <$> (m1 !! k) = f2 k <$> (m2 !! k)) →
  map_imap f1 m1 = map_imap f2 m2.
Proof.
  intros HExt. apply map_eq. intros i. rewrite !map_lookup_imap.
  specialize (HExt i). destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.

Lemma map_imap_compose {A1 A2 B} (f1 : K → A1 → option B)
    (f2 : K → A2 → option A1) (m : M A2) :
  map_imap f1 (map_imap f2 m) = map_imap (λ k x, f2 k x ≫= f1 k) m.
Proof.
  apply map_eq. intros i. rewrite !map_lookup_imap. by destruct (m !! i).
Qed.

Lemma map_imap_empty {A B} (f : K → A → option B) :
  map_imap f ∅ =@{M B} ∅.
Proof. unfold map_imap. by rewrite map_to_list_empty. Qed.

(** ** Properties of the size operation *)
Lemma map_size_empty {A} : size (∅ : M A) = 0.
Proof. by rewrite <-map_to_list_length, map_to_list_empty. Qed.
Lemma map_size_empty_iff {A} (m : M A) : size m = 0 ↔ m = ∅.
Proof.
  by rewrite <-map_to_list_length, length_zero_iff_nil, map_to_list_empty_iff.
Qed.
Lemma map_size_empty_inv {A} (m : M A) : size m = 0 → m = ∅.
Proof. apply map_size_empty_iff. Qed.
Lemma map_size_non_empty_iff {A} (m : M A) : size m ≠ 0 ↔ m ≠ ∅.
Proof. by rewrite map_size_empty_iff. Qed.

Lemma map_size_singleton {A} i (x : A) : size ({[ i := x ]} : M A) = 1.
Proof. by rewrite <-map_to_list_length, map_to_list_singleton. Qed.

Lemma map_size_ne_0_lookup {A} (m : M A) :
  size m ≠ 0 ↔ ∃ i, is_Some (m !! i).
Proof.
  rewrite map_size_non_empty_iff. split.
  - intros Hsz. apply map_choose. intros Hemp. done.
  - intros [i [k Hi]] ->. rewrite lookup_empty in Hi. done.
Qed.
Lemma map_size_ne_0_lookup_1 {A} (m : M A) :
  size m ≠ 0 → ∃ i, is_Some (m !! i).
Proof. intros. by eapply map_size_ne_0_lookup. Qed.
Lemma map_size_ne_0_lookup_2 {A} (m : M A) i :
  is_Some (m !! i) → size m ≠ 0.
Proof. intros. eapply map_size_ne_0_lookup. eauto. Qed.

Lemma map_size_insert {A} i x (m : M A) :
  size (<[i:=x]> m) = (match m !! i with Some _ => id | None => S end) (size m).
Proof.
  destruct (m !! i) as [y|] eqn:?; simpl.
  - rewrite <-(insert_id m i y) at 2 by done. rewrite <-!(insert_delete_insert m).
    rewrite <-!map_to_list_length.
    by rewrite !map_to_list_insert by (by rewrite lookup_delete).
  - by rewrite <-!map_to_list_length, map_to_list_insert.
Qed.
Lemma map_size_insert_Some {A} i x (m : M A) :
  is_Some (m !! i) → size (<[i:=x]> m) = size m.
Proof. intros [y Hi]. by rewrite map_size_insert, Hi. Qed.
Lemma map_size_insert_None {A} i x (m : M A) :
  m !! i = None → size (<[i:=x]> m) = S (size m).
Proof. intros Hi. by rewrite map_size_insert, Hi. Qed.

Lemma map_size_delete {A} i (m : M A) :
  size (delete i m) = (match m !! i with Some _ => pred | None => id end) (size m).
Proof.
  destruct (m !! i) as [y|] eqn:?; simpl.
  - by rewrite <-!map_to_list_length, <-(map_to_list_delete m).
  - by rewrite delete_notin.
Qed.
Lemma map_size_delete_Some {A} i (m : M A) :
  is_Some (m !! i) → size (delete i m) = pred (size m).
Proof. intros [y Hi]. by rewrite map_size_delete, Hi. Qed.
Lemma map_size_delete_None {A} i (m : M A) :
  m !! i = None → size (delete i m) = size m.
Proof. intros Hi. by rewrite map_size_delete, Hi. Qed.

Lemma map_size_fmap {A B} (f : A -> B) (m : M A) : size (f <$> m) = size m.
Proof.
  intros. by rewrite <-!map_to_list_length, map_to_list_fmap, fmap_length.
Qed.

Lemma map_size_list_to_map {A} (l : list (K * A)) :
  NoDup l.*1 →
  size (list_to_map l : M A) = length l.
Proof.
  induction l; csimpl; inv 1; simplify_eq/=; [by rewrite map_size_empty|].
  rewrite map_size_insert_None by eauto using not_elem_of_list_to_map_1.
  eauto with f_equal.
Qed.

Lemma map_subseteq_size_eq {A} (m1 m2 : M A) :
  m1 ⊆ m2 → size m2 ≤ size m1 → m1 = m2.
Proof.
  intros. apply map_to_list_inj, submseteq_length_Permutation.
  - by apply map_to_list_submseteq.
  - by rewrite !map_to_list_length.
Qed.

Lemma map_subseteq_size {A} (m1 m2 : M A) : m1 ⊆ m2 → size m1 ≤ size m2.
Proof.
  intros. rewrite <-!map_to_list_length.
  by apply submseteq_length, map_to_list_submseteq.
Qed.

Lemma map_subset_size {A} (m1 m2 : M A) : m1 ⊂ m2 → size m1 < size m2.
Proof.
  intros [Hm12 Hm21]. apply Nat.le_neq. split.
  - by apply map_subseteq_size.
  - intros Hsize. destruct Hm21.
    apply reflexive_eq, symmetry, map_subseteq_size_eq; auto with lia.
Qed.

(** ** Induction principles *)
Lemma map_wf {A} : well_founded (⊂@{M A}).
Proof. apply (wf_projected (<) size); auto using map_subset_size, lt_wf. Qed.

Lemma map_ind {A} (P : M A → Prop) :
  P ∅ → (∀ i x m, m !! i = None → P m → P (<[i:=x]>m)) → ∀ m, P m.
Proof.
  intros ? Hins m. induction (map_wf m) as [m _ IH].
  destruct (map_choose_or_empty m) as [(i&x&?)| ->]; [|done].
  rewrite <-(insert_delete m i x) by done.
  apply Hins; [by rewrite lookup_delete|]. by apply IH, delete_subset.
Qed.

(** ** Properties of conversion from sets *)
Section set_to_map.
  Context {A : Type} `{FinSet B C}.

  Lemma lookup_set_to_map (f : B → K * A) (Y : C) i x :
    (∀ y y', y ∈ Y → y' ∈ Y → (f y).1 = (f y').1 → y = y') →
    (set_to_map f Y : M A) !! i = Some x ↔ ∃ y, y ∈ Y ∧ f y = (i,x).
  Proof.
    intros Hinj. assert (∀ x',
      (i, x) ∈ f <$> elements Y → (i, x') ∈ f <$> elements Y → x = x').
    { intros x'. intros (y&Hx&Hy)%elem_of_list_fmap (y'&Hx'&Hy')%elem_of_list_fmap.
      rewrite elem_of_elements in Hy, Hy'.
      cut (y = y'); [congruence|]. apply Hinj; auto. by rewrite <-Hx, <-Hx'. }
    unfold set_to_map; rewrite <-elem_of_list_to_map' by done.
    rewrite elem_of_list_fmap. setoid_rewrite elem_of_elements; naive_solver.
  Qed.
End set_to_map.

Lemma lookup_set_to_map_id `{FinSet (K * A) C} (X : C) i x :
  (∀ i y y', (i,y) ∈ X → (i,y') ∈ X → y = y') →
  (set_to_map id X : M A) !! i = Some x ↔ (i,x) ∈ X.
Proof.
  intros. etrans; [apply lookup_set_to_map|naive_solver].
  intros [] [] ???; simplify_eq/=; eauto with f_equal.
Qed.

Section map_to_set.
  Context {A : Type} `{SemiSet B C}.

  Lemma elem_of_map_to_set (f : K → A → B) (m : M A) (y : B) :
    y ∈ map_to_set (C:=C) f m ↔ ∃ i x, m !! i = Some x ∧ f i x = y.
  Proof.
    unfold map_to_set; simpl.
    rewrite elem_of_list_to_set, elem_of_list_fmap. split.
    - intros ([i x] & ? & ?%elem_of_map_to_list); eauto.
    - intros (i&x&?&?). exists (i,x). by rewrite elem_of_map_to_list.
  Qed.
  Lemma map_to_set_empty (f : K → A → B) :
    map_to_set f (∅ : M A) = (∅ : C).
  Proof. unfold map_to_set; simpl. by rewrite map_to_list_empty. Qed.
  Lemma map_to_set_insert (f : K → A → B)(m : M A) i x :
    m !! i = None →
    map_to_set f (<[i:=x]>m) ≡@{C} {[f i x]} ∪ map_to_set f m.
  Proof.
    intros. unfold map_to_set; simpl. by rewrite map_to_list_insert.
  Qed.
  Lemma map_to_set_insert_L `{!LeibnizEquiv C} (f : K → A → B) (m : M A) i x :
    m !! i = None →
    map_to_set f (<[i:=x]>m) =@{C} {[f i x]} ∪ map_to_set f m.
  Proof. unfold_leibniz. apply map_to_set_insert. Qed.
End map_to_set.

Lemma elem_of_map_to_set_pair `{SemiSet (K * A) C} (m : M A) i x :
  (i,x) ∈@{C} map_to_set pair m ↔ m !! i = Some x.
Proof. rewrite elem_of_map_to_set. naive_solver. Qed.

(** ** The fold operation *)
Lemma map_fold_foldr {A B} (R : relation B) `{!PreOrder R} (l : list (K * A))
    (f : K → A → B → B) (b : B) m :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  map_to_list m ≡ₚ l →
  R (map_fold f b m) (foldr (uncurry f) b l).
Proof.
  intros Hf_proper. revert l. apply (map_fold_ind (λ r m, ∀ l,
    (∀ j1 j2 z1 z2 y,
      j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
      R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
    map_to_list m ≡ₚ l →
    R r (foldr (uncurry f) b l))); clear m.
  { intros [|x l] _; simpl; [done|].
    by rewrite map_to_list_empty, Permutation_nil_l. }
  intros i x m r ? IH l Hf Hl. rewrite map_to_list_insert in Hl by done.
  etrans; [|apply (foldr_permutation R), Hl]; simpl.
  - f_equiv. apply IH; [|done]. intros j1 j2 z1 z2 y ???.
    apply Hf; [done|rewrite lookup_insert_Some; naive_solver..].
  - intros []; apply _.
  - intros j1 [k1 y1] j2 [k2 y2] c Hj Hj1 Hj2. apply Hf.
    + intros ->. eapply Hj, (NoDup_lookup ((i,x) :: map_to_list m).*1).
      * csimpl. apply NoDup_cons_2, NoDup_fst_map_to_list.
        intros ([??]&?&?%elem_of_map_to_list)%elem_of_list_fmap; naive_solver.
      * by rewrite list_lookup_fmap, Hj1.
      * by rewrite list_lookup_fmap, Hj2.
    + apply elem_of_map_to_list. rewrite map_to_list_insert by done.
      by eapply elem_of_list_lookup_2.
    + apply elem_of_map_to_list. rewrite map_to_list_insert by done.
      by eapply elem_of_list_lookup_2.
Qed.

Lemma map_fold_empty {A B} (f : K → A → B → B) (b : B) :
  map_fold f b ∅ = b.
Proof.
  apply (map_fold_foldr _ []); [solve_proper|..].
  - intros j1 j2 z1 z2 y. by rewrite !lookup_empty.
  - by rewrite map_to_list_empty.
Qed.

Lemma map_fold_singleton {A B} (f : K → A → B → B) (b : B) i x :
  map_fold f b {[i:=x]} = f i x b.
Proof.
  apply (map_fold_foldr _ [(i,x)]); [solve_proper|..].
  - intros j1 j2 z1 z2 y ?. rewrite !lookup_singleton_Some. naive_solver.
  - by rewrite map_to_list_singleton.
Qed.

Lemma map_fold_insert {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  m !! i = None →
  R (map_fold f b (<[i:=x]> m)) (f i x (map_fold f b m)).
Proof.
  intros Hf_proper Hf Hi. trans (f i x (foldr (uncurry f) b (map_to_list m))).
  - apply (map_fold_foldr _ ((i,x) :: map_to_list m)); [solve_proper|done|].
    by rewrite map_to_list_insert by done.
  - f_equiv. apply (map_fold_foldr (flip R)); [solve_proper| |done].
    intros j1 j2 z1 z2 y ???.
    apply Hf; rewrite ?lookup_insert_Some; naive_solver.
Qed.

Lemma map_fold_insert_L {A B} (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  m !! i = None →
  map_fold f b (<[i:=x]> m) = f i x (map_fold f b m).
Proof. apply map_fold_insert; apply _. Qed.

Lemma map_fold_delete {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  m !! i = Some x →
  R (map_fold f b m) (f i x (map_fold f b (delete i m))).
Proof.
  intros Hf_proper Hf Hi.
  rewrite <-map_fold_insert; [|done|done| |].
  - rewrite insert_delete; done.
  - intros j1 j2 z1 z2 y. rewrite insert_delete_insert, insert_id by done. auto.
  - rewrite lookup_delete; done.
Qed.

Lemma map_fold_delete_L {A B} (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  m !! i = Some x →
  map_fold f b m = f i x (map_fold f b (delete i m)).
Proof. apply map_fold_delete; apply _. Qed.

(** This lemma for commuting [g] in/out of a [map_fold] requires [g] to be
[Proper] (second premise) and [f] to be associative/commutative (third premise).
Those requirements do not show up for the equivalent lemmas on sets/multisets
because their fold operation is defined in terms of [foldr] on lists, so we know
that both folds ([set_fold f (g x) m] and [set_fold f x m]) happen in the same
order. The [map_fold_ind] principle does not guarantee this happens for
[map_fold] too. *)
Lemma map_fold_comm_acc_strong {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (g : B → B) (x : B) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  Proper (R ==> R) g →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  (∀ j z y, m !! j = Some z → R (f j z (g y)) (g (f j z y))) →
  R (map_fold f (g x) m) (g (map_fold f x m)).
Proof.
  intros ? ? Hf Hg.
  apply (map_fold_ind (λ z m,
    (∀ j1 j2 z1 z2 y,
      j1 ≠ j2 → m !! j1 = Some z1 → m !! j2 = Some z2 →
      R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
    (∀ j z y, m !! j = Some z → R (f j z (g y)) (g (f j z y))) →
    R (map_fold f (g x) m) (g z)));
     [by rewrite map_fold_empty| |apply Hf|apply Hg].
  intros i x' m' r Hx' IH Hfm' Hgm'.
  rewrite map_fold_insert by (apply _ || done).
  rewrite <-Hgm' by (by rewrite lookup_insert). f_equiv. apply IH.
  - intros j1 j2 z1 z2 y Hjs Hl1 Hl2.
    apply Hfm'; [done|rewrite lookup_insert_Some; naive_solver..].
  - intros j z y Hj.
    apply Hgm'. rewrite lookup_insert_ne by naive_solver. done.
Qed.

Lemma map_fold_comm_acc {A} (f : K → A → A → A) (g : A → A) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y, f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  (∀ j z y, f j z (g y) = g (f j z y)) →
  map_fold f (g x) m = g (map_fold f x m).
Proof.
  intros. apply (map_fold_comm_acc_strong _); [solve_proper|solve_proper|done..].
Qed.

(** ** Properties of the [map_Forall] predicate *)
Section map_Forall.
  Context {A} (P : K → A → Prop).
  Implicit Types m : M A.

  Lemma map_Forall_to_list m : map_Forall P m ↔ Forall (uncurry P) (map_to_list m).
  Proof.
    rewrite Forall_forall. split.
    - intros Hforall [i x]. rewrite elem_of_map_to_list. by apply (Hforall i x).
    - intros Hforall i x. rewrite <-elem_of_map_to_list. by apply (Hforall (i,x)).
  Qed.
  Lemma map_Forall_empty : map_Forall P (∅ : M A).
  Proof. intros i x. by rewrite lookup_empty. Qed.
  Lemma map_Forall_impl (Q : K → A → Prop) m :
    map_Forall P m → (∀ i x, P i x → Q i x) → map_Forall Q m.
  Proof. unfold map_Forall; naive_solver. Qed.
  Lemma map_Forall_insert_1_1 m i x : map_Forall P (<[i:=x]>m) → P i x.
  Proof. intros Hm. by apply Hm; rewrite lookup_insert. Qed.
  Lemma map_Forall_insert_1_2 m i x :
    m !! i = None → map_Forall P (<[i:=x]>m) → map_Forall P m.
  Proof.
    intros ? Hm j y ?; apply Hm. by rewrite lookup_insert_ne by congruence.
  Qed.
  Lemma map_Forall_insert_2 m i x :
    P i x → map_Forall P m → map_Forall P (<[i:=x]>m).
  Proof. intros ?? j y; rewrite lookup_insert_Some; naive_solver. Qed.
  Lemma map_Forall_insert m i x :
    m !! i = None → map_Forall P (<[i:=x]>m) ↔ P i x ∧ map_Forall P m.
  Proof.
    naive_solver eauto using map_Forall_insert_1_1,
      map_Forall_insert_1_2, map_Forall_insert_2.
  Qed.
  Lemma map_Forall_singleton (i : K) (x : A) :
    map_Forall P ({[i := x]} : M A) ↔ P i x.
  Proof.
    unfold map_Forall. setoid_rewrite lookup_singleton_Some. naive_solver.
  Qed.
  Lemma map_Forall_delete m i : map_Forall P m → map_Forall P (delete i m).
  Proof. intros Hm j x; rewrite lookup_delete_Some. naive_solver. Qed.
  Lemma map_Forall_lookup m :
    map_Forall P m ↔ ∀ i x, m !! i = Some x → P i x.
  Proof. done. Qed.
  Lemma map_Forall_lookup_1 m i x :
    map_Forall P m → m !! i = Some x → P i x.
  Proof. intros ?. by apply map_Forall_lookup. Qed.
  Lemma map_Forall_lookup_2 m :
    (∀ i x, m !! i = Some x → P i x) → map_Forall P m.
  Proof. intros ?. by apply map_Forall_lookup. Qed.
  Lemma map_Forall_fmap {B} (f : B → A) (m : M B) :
    map_Forall P (f <$> m) ↔ map_Forall (λ k, (P k ∘ f)) m.
  Proof.
    unfold map_Forall. setoid_rewrite lookup_fmap.
    setoid_rewrite fmap_Some. naive_solver.
  Qed.

  Lemma map_Forall_foldr_delete m is :
    map_Forall P m → map_Forall P (foldr delete m is).
  Proof. induction is; eauto using map_Forall_delete. Qed.
  Lemma map_Forall_ind (Q : M A → Prop) :
    Q ∅ →
    (∀ m i x, m !! i = None → P i x → map_Forall P m → Q m → Q (<[i:=x]>m)) →
    ∀ m, map_Forall P m → Q m.
  Proof.
    intros Hnil Hinsert m. induction m using map_ind; auto.
    rewrite map_Forall_insert by done; intros [??]; eauto.
  Qed.

  Context `{∀ i x, Decision (P i x)}.
  Global Instance map_Forall_dec m : Decision (map_Forall P m).
  Proof.
    refine (cast_if (decide (Forall (uncurry P) (map_to_list m))));
      by rewrite map_Forall_to_list.
  Defined.
  Lemma map_not_Forall (m : M A) :
    ¬map_Forall P m ↔ ∃ i x, m !! i = Some x ∧ ¬P i x.
  Proof.
    split; [|intros (i&x&?&?) Hm; specialize (Hm i x); tauto].
    rewrite map_Forall_to_list. intros Hm.
    apply (not_Forall_Exists _), Exists_exists in Hm.
    destruct Hm as ([i x]&?&?). exists i, x. by rewrite <-elem_of_map_to_list.
  Qed.
End map_Forall.

(** ** Properties of the [map_Exists] predicate *)
Section map_Exists.
  Context {A} (P : K → A → Prop).
  Implicit Types m : M A.

  Lemma map_Exists_to_list m : map_Exists P m ↔ Exists (uncurry P) (map_to_list m).
  Proof.
    rewrite Exists_exists. split.
    - intros [? [? [? ?]]]. eexists (_, _). by rewrite elem_of_map_to_list.
    - intros [[??] [??]]. eexists _, _. by rewrite <-elem_of_map_to_list.
  Qed.
  Lemma map_Exists_empty : ¬ map_Exists P (∅ : M A).
  Proof. intros [?[?[Hm ?]]]. by rewrite lookup_empty in Hm. Qed.
  Lemma map_Exists_impl (Q : K → A → Prop) m :
    map_Exists P m → (∀ i x, P i x → Q i x) → map_Exists Q m.
  Proof. unfold map_Exists; naive_solver. Qed.
  Lemma map_Exists_insert_1 m i x :
    map_Exists P (<[i:=x]>m) → P i x ∨ map_Exists P m.
  Proof. intros [j[y[?%lookup_insert_Some ?]]]. unfold map_Exists. naive_solver. Qed.
  Lemma map_Exists_insert_2_1 m i x : P i x → map_Exists P (<[i:=x]>m).
  Proof. intros Hm. exists i, x. by rewrite lookup_insert. Qed.
  Lemma map_Exists_insert_2_2 m i x :
    m !! i = None → map_Exists P m → map_Exists P (<[i:=x]>m).
  Proof.
    intros Hm [j[y[??]]]. exists j, y. by rewrite lookup_insert_ne by congruence.
  Qed.
  Lemma map_Exists_insert m i x :
    m !! i = None → map_Exists P (<[i:=x]>m) ↔ P i x ∨ map_Exists P m.
  Proof.
    naive_solver eauto using map_Exists_insert_1,
      map_Exists_insert_2_1, map_Exists_insert_2_2.
  Qed.
  Lemma map_Exists_singleton (i : K) (x : A) :
    map_Exists P ({[i := x]} : M A) ↔ P i x.
  Proof.
    unfold map_Exists. setoid_rewrite lookup_singleton_Some. naive_solver.
  Qed.
  Lemma map_Exists_delete m i : map_Exists P (delete i m) → map_Exists P m.
  Proof.
    intros [j [y [Hm ?]]]. rewrite lookup_delete_Some in Hm.
    unfold map_Exists. naive_solver.
  Qed.
  Lemma map_Exists_lookup m :
    map_Exists P m ↔ ∃ i x, m !! i = Some x ∧ P i x.
  Proof. done. Qed.
  Lemma map_Exists_lookup_1 m :
    map_Exists P m → ∃ i x, m !! i = Some x ∧ P i x.
  Proof. by rewrite map_Exists_lookup. Qed.
  Lemma map_Exists_lookup_2 m i x :
    m !! i = Some x → P i x → map_Exists P m.
  Proof. rewrite map_Exists_lookup. by eauto. Qed.
  Lemma map_Exists_foldr_delete m is :
    map_Exists P (foldr delete m is) → map_Exists P m.
  Proof. induction is; eauto using map_Exists_delete. Qed.

  Lemma map_Exists_ind (Q : M A → Prop) :
    (∀ i x, P i x → Q {[ i := x ]}) →
    (∀ m i x, m !! i = None → map_Exists P m → Q m → Q (<[i:=x]>m)) →
    ∀ m, map_Exists P m → Q m.
  Proof.
    intros Hsingleton Hinsert m Hm. induction m as [|i x m Hi IH] using map_ind.
    { by destruct map_Exists_empty. }
    apply map_Exists_insert in Hm as [?|?]; [|by eauto..].
    clear IH. induction m as [|j y m Hj IH] using map_ind; [by eauto|].
    apply lookup_insert_None in Hi as [??].
    rewrite insert_commute by done. apply Hinsert.
    - by apply lookup_insert_None.
    - apply map_Exists_insert; by eauto.
    - eauto.
  Qed.

  Lemma map_not_Exists (m : M A) :
    ¬map_Exists P m ↔ map_Forall (λ i x, ¬ P i x) m.
  Proof. unfold map_Exists, map_Forall; naive_solver. Qed.

  Context `{∀ i x, Decision (P i x)}.
  Global Instance map_Exists_dec m : Decision (map_Exists P m).
  Proof.
    refine (cast_if (decide (Exists (uncurry P) (map_to_list m))));
      by rewrite map_Exists_to_list.
  Defined.
End map_Exists.

(** ** The filter operation *)
Section map_lookup_filter.
  Context {A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.
  Implicit Types m : M A.

  Lemma map_lookup_filter m i :
    filter P m !! i = x ← m !! i; guard (P (i,x));; Some x.
  Proof.
    revert m i. apply (map_fold_ind (λ m1 m2,
      ∀ i, m1 !! i = x ← m2 !! i; guard (P (i,x));; Some x)); intros i.
    { by rewrite lookup_empty. }
    intros y m m' Hm IH j. case (decide (j = i))as [->|?].
    - case_decide.
      + rewrite !lookup_insert. simpl. by rewrite option_guard_True.
      + rewrite lookup_insert. simpl. by rewrite option_guard_False, IH, Hm.
    - case_decide.
      + by rewrite !lookup_insert_ne by done.
      + by rewrite !lookup_insert_ne.
  Qed.

  Lemma map_lookup_filter_Some m i x :
    filter P m !! i = Some x ↔ m !! i = Some x ∧ P (i, x).
  Proof.
    rewrite map_lookup_filter.
    destruct (m !! i); simpl; repeat case_guard; naive_solver.
  Qed.
  Lemma map_lookup_filter_Some_1_1 m i x :
    filter P m !! i = Some x → m !! i = Some x.
  Proof. apply map_lookup_filter_Some. Qed.
  Lemma map_lookup_filter_Some_1_2 m i x :
    filter P m !! i = Some x → P (i, x).
  Proof. apply map_lookup_filter_Some. Qed.
  Lemma map_lookup_filter_Some_2 m i x :
    m !! i = Some x →
    P (i, x) →
    filter P m !! i = Some x.
  Proof. intros. by apply map_lookup_filter_Some. Qed.

  Lemma map_lookup_filter_None m i :
    filter P m !! i = None ↔ m !! i = None ∨ ∀ x, m !! i = Some x → ¬ P (i, x).
  Proof.
    rewrite eq_None_not_Some. unfold is_Some.
    setoid_rewrite map_lookup_filter_Some. naive_solver.
  Qed.
  Lemma map_lookup_filter_None_1 m i :
    filter P m !! i = None →
    m !! i = None ∨ ∀ x, m !! i = Some x → ¬ P (i, x).
  Proof. apply map_lookup_filter_None. Qed.
  Lemma map_lookup_filter_None_2 m i :
    m !! i = None ∨ (∀ x : A, m !! i = Some x → ¬ P (i, x)) →
    filter P m !! i = None.
  Proof. apply map_lookup_filter_None. Qed.

  Lemma map_filter_empty_not_lookup m i x :
    filter P m = ∅ → P (i,x) → m !! i ≠ Some x.
  Proof.
    rewrite map_empty. setoid_rewrite map_lookup_filter_None. intros Hm ?.
    destruct (Hm i); naive_solver.
  Qed.
End map_lookup_filter.

Section map_filter_ext.
  Context {A} (P Q : K * A → Prop) `{!∀ x, Decision (P x), !∀ x, Decision (Q x)}.

  Lemma map_filter_strong_ext (m1 m2 : M A) :
    filter P m1 = filter Q m2 ↔
    (∀ i x, (P (i, x) ∧ m1 !! i = Some x) ↔ (Q (i, x) ∧ m2 !! i = Some x)).
  Proof.
    intros. rewrite map_eq_iff. setoid_rewrite option_eq.
    setoid_rewrite map_lookup_filter_Some. naive_solver.
  Qed.
  Lemma map_filter_strong_ext_1 (m1 m2 : M A) :
    (∀ i x, (P (i, x) ∧ m1 !! i = Some x) ↔ (Q (i, x) ∧ m2 !! i = Some x)) →
    filter P m1 = filter Q m2.
  Proof. by rewrite map_filter_strong_ext. Qed.
  Lemma map_filter_strong_ext_2 (m1 m2 : M A) i x :
    filter P m1 = filter Q m2 →
    (P (i, x) ∧ m1 !! i = Some x) ↔ (Q (i, x) ∧ m2 !! i = Some x).
  Proof. by rewrite map_filter_strong_ext. Qed.
  Lemma map_filter_ext (m : M A) :
    (∀ i x, m !! i = Some x → P (i, x) ↔ Q (i, x)) ↔
    filter P m = filter Q m.
  Proof. rewrite map_filter_strong_ext. naive_solver. Qed.

  Lemma map_filter_strong_subseteq_ext (m1 m2 : M A) :
    filter P m1 ⊆ filter Q m2 ↔
    (∀ i x, (P (i, x) ∧ m1 !! i = Some x) → (Q (i, x) ∧ m2 !! i = Some x)).
  Proof.
    rewrite map_subseteq_spec.
    setoid_rewrite map_lookup_filter_Some. naive_solver.
  Qed.
  Lemma map_filter_subseteq_ext (m : M A) :
    filter P m ⊆ filter Q m ↔
    (∀ i x, m !! i = Some x → P (i, x) → Q (i, x)).
  Proof. rewrite map_filter_strong_subseteq_ext. naive_solver. Qed.
End map_filter_ext.

Section map_filter.
  Context {A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.
  Implicit Types m : M A.

  Lemma map_filter_empty : filter P ∅ =@{M A} ∅.
  Proof. apply map_fold_empty. Qed.
  Lemma map_filter_empty_iff m :
    filter P m = ∅ ↔ map_Forall (λ i x, ¬P (i,x)) m.
  Proof.
    rewrite map_empty. setoid_rewrite map_lookup_filter_None. split.
    - intros Hm i x Hi. destruct (Hm i); naive_solver.
    - intros Hm i. destruct (m !! i) as [x|] eqn:?; [|by auto].
      right; intros ? [= <-]. by apply Hm.
  Qed.

  Lemma map_filter_delete m i : filter P (delete i m) = delete i (filter P m).
  Proof.
    apply map_eq. intros j. apply option_eq; intros y.
    destruct (decide (j = i)) as [->|?].
    - rewrite map_lookup_filter_Some, !lookup_delete. naive_solver.
    - rewrite lookup_delete_ne, !map_lookup_filter_Some, lookup_delete_ne by done.
      naive_solver.
  Qed.
  Lemma map_filter_delete_not m i:
    (∀ y, m !! i = Some y → ¬ P (i, y)) →
    filter P (delete i m) = filter P m.
  Proof.
    intros. apply map_filter_strong_ext. intros j y.
    rewrite lookup_delete_Some. naive_solver.
  Qed.

  Lemma map_filter_insert m i x :
    filter P (<[i:=x]> m)
    = if decide (P (i, x)) then <[i:=x]> (filter P m) else filter P (delete i m).
  Proof.
    apply map_eq. intros j. apply option_eq; intros y.
    rewrite map_lookup_filter_Some, lookup_insert_Some. case_decide.
    - rewrite lookup_insert_Some, map_lookup_filter_Some. naive_solver.
    - rewrite map_lookup_filter_Some, lookup_delete_Some. naive_solver.
  Qed.
  Lemma map_filter_insert_True m i x :
    P (i, x) → filter P (<[i:=x]> m) = <[i:=x]> (filter P m).
  Proof. intros. by rewrite map_filter_insert, decide_True. Qed.
  Lemma map_filter_insert_False m i x :
    ¬ P (i, x) → filter P (<[i:=x]> m) = filter P (delete i m).
  Proof. intros. by rewrite map_filter_insert, decide_False. Qed.

  Lemma map_filter_insert_not' m i x :
    ¬ P (i, x) → (∀ y, m !! i = Some y → ¬ P (i, y)) →
    filter P (<[i:=x]> m) = filter P m.
  Proof.
    intros. rewrite map_filter_insert, decide_False by done.
    by rewrite map_filter_delete_not.
  Qed.
  Lemma map_filter_insert_not m i x :
    (∀ y, ¬ P (i, y)) → filter P (<[i:=x]> m) = filter P m.
  Proof. intros. by apply map_filter_insert_not'. Qed.

  Lemma map_filter_singleton i x :
    filter P {[i := x]} =@{M A} if decide (P (i, x)) then {[i := x]} else ∅.
  Proof.
    by rewrite <-!insert_empty, map_filter_insert, delete_empty, map_filter_empty.
  Qed.
  Lemma map_filter_singleton_True i x :
    P (i, x) → filter P {[i := x]} =@{M A} {[i := x]}.
  Proof. intros. by rewrite map_filter_singleton, decide_True. Qed.
  Lemma map_filter_singleton_False i x :
    ¬ P (i, x) → filter P {[i := x]} =@{M A} ∅.
  Proof. intros. by rewrite map_filter_singleton, decide_False. Qed.

  Lemma map_filter_alt m : filter P m = list_to_map (filter P (map_to_list m)).
  Proof.
    apply list_to_map_flip. induction m as [|k x m ? IH] using map_ind.
    { by rewrite map_to_list_empty, map_filter_empty, map_to_list_empty. }
    rewrite map_to_list_insert, filter_cons by done. destruct (decide (P _)).
    - rewrite map_filter_insert_True by done.
      by rewrite map_to_list_insert, IH by (rewrite map_lookup_filter_None; auto).
    - by rewrite map_filter_insert_not' by naive_solver.
  Qed.

  Lemma map_filter_fmap {B} (f : B → A) (m : M B) :
    filter P (f <$> m) = f <$> filter (λ '(i, x), P (i, (f x))) m.
  Proof.
    apply map_eq. intros i. apply option_eq; intros x.
    repeat (rewrite lookup_fmap, fmap_Some || setoid_rewrite map_lookup_filter_Some).
    naive_solver.
  Qed.

  Lemma map_filter_filter Q `{!∀ x, Decision (Q x)} m :
    filter P (filter Q m) = filter (λ '(i, x), P (i, x) ∧ Q (i, x)) m.
  Proof.
    apply map_filter_strong_ext. intros ??.
    rewrite map_lookup_filter_Some. naive_solver.
  Qed.
  Lemma map_filter_filter_l Q `{!∀ x, Decision (Q x)} m :
    (∀ i x, m !! i = Some x → P (i, x) → Q (i, x)) →
    filter P (filter Q m) = filter P m.
  Proof. intros ?. rewrite map_filter_filter. apply map_filter_ext. naive_solver. Qed.
  Lemma map_filter_filter_r Q `{!∀ x, Decision (Q x)} m :
    (∀ i x, m !! i = Some x → Q (i, x) → P (i, x)) →
    filter P (filter Q m) = filter Q m.
  Proof. intros ?. rewrite map_filter_filter. apply map_filter_ext. naive_solver. Qed.

  Lemma map_filter_id m :
    (∀ i x, m !! i = Some x → P (i, x)) → filter P m = m.
  Proof.
    intros Hi. apply map_eq. intros i. rewrite map_lookup_filter.
    destruct (m !! i) eqn:Hlook; [|done].
    apply option_guard_True, Hi, Hlook.
  Qed.

  Lemma map_filter_subseteq m : filter P m ⊆ m.
  Proof. apply map_subseteq_spec, map_lookup_filter_Some_1_1. Qed.

  Lemma map_filter_subseteq_mono m1 m2 : m1 ⊆ m2 → filter P m1 ⊆ filter P m2.
  Proof.
    rewrite map_subseteq_spec. intros Hm1m2.
    apply map_filter_strong_subseteq_ext. naive_solver.
  Qed.

  Lemma map_size_filter m :
    size (filter P m) ≤ size m.
  Proof. apply map_subseteq_size. apply map_filter_subseteq. Qed.

End map_filter.

Lemma map_filter_comm {A}
    (P Q : K * A → Prop) `{!∀ x, Decision (P x), !∀ x, Decision (Q x)} (m : M A) :
  filter P (filter Q m) = filter Q (filter P m).
Proof. rewrite !map_filter_filter. apply map_filter_ext. naive_solver. Qed.

(** ** Properties of the [merge] operation *)
Section merge.
  Context {A} (f : option A → option A → option A).
  Implicit Types m : M A.

  (** These instances can in many cases not be applied automatically due to Coq
  unification bug #6294. Hence there are many explicit derived instances for
  specific operations such as union or difference in the rest of this file. *)
  Global Instance: LeftId (=) None f → LeftId (=@{M A}) ∅ (merge f).
  Proof.
    intros ? m. apply map_eq; intros i.
    rewrite !lookup_merge, lookup_empty. destruct (m !! i); by simpl.
  Qed.
  Global Instance: RightId (=) None f → RightId (=@{M A}) ∅ (merge f).
  Proof.
    intros ? m. apply map_eq; intros i.
    rewrite !lookup_merge, lookup_empty. destruct (m !! i); by simpl.
  Qed.
  Global Instance: LeftAbsorb (=) None f → LeftAbsorb (=@{M A}) ∅ (merge f).
  Proof.
    intros ? m. apply map_eq; intros i.
    rewrite !lookup_merge, lookup_empty. destruct (m !! i); by simpl.
  Qed.
  Global Instance: RightAbsorb (=) None f → RightAbsorb (=@{M A}) ∅ (merge f).
  Proof.
    intros ? m. apply map_eq; intros i.
    rewrite !lookup_merge, lookup_empty. destruct (m !! i); by simpl.
  Qed.
  Lemma merge_comm m1 m2 :
    (∀ i, f (m1 !! i) (m2 !! i) = f (m2 !! i) (m1 !! i)) →
    merge f m1 m2 = merge f m2 m1.
  Proof.
    intros Hm. apply map_eq; intros i. specialize (Hm i).
    rewrite !lookup_merge. by destruct (m1 !! i), (m2 !! i).
  Qed.
  Global Instance merge_comm' : Comm (=) f → Comm (=@{M A}) (merge f).
  Proof. intros ???. apply merge_comm. intros. by apply (comm f). Qed.
  Lemma merge_assoc m1 m2 m3 :
    (∀ i, diag_None f (m1 !! i) (diag_None f (m2 !! i) (m3 !! i)) =
          diag_None f (diag_None f (m1 !! i) (m2 !! i)) (m3 !! i)) →
    merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
  Proof.
    intros Hm. apply map_eq; intros i. specialize (Hm i).
    by rewrite !lookup_merge.
  Qed.
  Lemma merge_idemp m1 :
    (∀ i, f (m1 !! i) (m1 !! i) = m1 !! i) → merge f m1 m1 = m1.
  Proof.
    intros Hm. apply map_eq; intros i. specialize (Hm i).
    rewrite !lookup_merge. by destruct (m1 !! i).
  Qed.
  Global Instance merge_idemp' : IdemP (=) f → IdemP (=@{M A}) (merge f).
  Proof. intros ??. apply merge_idemp. intros. by apply (idemp f). Qed.
End merge.

Section more_merge.
  Context {A B C} (f : option A → option B → option C).

  Lemma merge_Some (m1 : M A) (m2 : M B) (m : M C) :
    f None None = None →
    (∀ i, m !! i = f (m1 !! i) (m2 !! i)) ↔ merge f m1 m2 = m.
  Proof.
   intros. rewrite map_eq_iff. apply forall_proper; intros i.
   rewrite lookup_merge. destruct (m1 !! i), (m2 !! i); naive_solver congruence.
  Qed.
  Lemma merge_empty : merge f ∅ ∅ =@{M C} ∅.
  Proof. apply map_eq. intros. by rewrite !lookup_merge, !lookup_empty. Qed.
  Lemma partial_alter_merge g g1 g2 (m1 : M A) (m2 : M B) i :
    g (diag_None f (m1 !! i) (m2 !! i)) = diag_None f (g1 (m1 !! i)) (g2 (m2 !! i)) →
    partial_alter g i (merge f m1 m2) =
      merge f (partial_alter g1 i m1) (partial_alter g2 i m2).
  Proof.
    intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
    - by rewrite lookup_merge, !lookup_partial_alter, !lookup_merge.
    - by rewrite lookup_merge, !lookup_partial_alter_ne, lookup_merge.
  Qed.
  Lemma partial_alter_merge_l g g1 (m1 : M A) (m2 : M B) i :
    g (diag_None f (m1 !! i) (m2 !! i)) = diag_None f (g1 (m1 !! i)) (m2 !! i) →
    partial_alter g i (merge f m1 m2) = merge f (partial_alter g1 i m1) m2.
  Proof.
    intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
    - by rewrite lookup_merge, !lookup_partial_alter, !lookup_merge.
    - by rewrite lookup_merge, !lookup_partial_alter_ne, lookup_merge.
  Qed.
  Lemma partial_alter_merge_r g g2 (m1 : M A) (m2 : M B) i :
    g (diag_None f (m1 !! i) (m2 !! i)) = diag_None f (m1 !! i) (g2 (m2 !! i)) →
    partial_alter g i (merge f m1 m2) = merge f m1 (partial_alter g2 i m2).
  Proof.
    intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
    - by rewrite lookup_merge, !lookup_partial_alter, !lookup_merge.
    - by rewrite lookup_merge, !lookup_partial_alter_ne, lookup_merge.
  Qed.
  Lemma insert_merge (m1 : M A) (m2 : M B) i x y z :
    f (Some y) (Some z) = Some x →
    <[i:=x]>(merge f m1 m2) = merge f (<[i:=y]>m1) (<[i:=z]>m2).
  Proof. intros; by apply partial_alter_merge. Qed.
  Lemma delete_merge (m1 : M A) (m2 : M B) i :
    delete i (merge f m1 m2) = merge f (delete i m1) (delete i m2).
  Proof. intros; by apply partial_alter_merge. Qed.
  Lemma merge_singleton i x y z :
    f (Some y) (Some z) = Some x →
    merge f {[i := y]} {[i := z]} =@{M C} {[i := x]}.
  Proof.
    intros. by erewrite <-!insert_empty, <-insert_merge, merge_empty by eauto.
  Qed.
  Lemma insert_merge_l (m1 : M A) (m2 : M B) i x y :
    f (Some y) (m2 !! i) = Some x →
    <[i:=x]>(merge f m1 m2) = merge f (<[i:=y]>m1) m2.
  Proof. by intros; apply partial_alter_merge_l. Qed.
  Lemma insert_merge_r (m1 : M A) (m2 : M B) i x z :
    f (m1 !! i) (Some z) = Some x →
    <[i:=x]>(merge f m1 m2) = merge f m1 (<[i:=z]>m2).
  Proof. intros; apply partial_alter_merge_r. by destruct (m1 !! i). Qed.

  Lemma fmap_merge {D} (g : C → D) (m1 : M A) (m2 : M B) :
    g <$> merge f m1 m2 = merge (λ mx1 mx2, g <$> f mx1 mx2) m1 m2.
  Proof.
    apply map_eq; intros i. rewrite lookup_fmap, !lookup_merge.
    by destruct (m1 !! i), (m2 !! i).
  Qed.
  Lemma omap_merge {D} (g : C → option D) (m1 : M A) (m2 : M B) :
    omap g (merge f m1 m2) = merge (λ mx1 mx2, f mx1 mx2 ≫= g) m1 m2.
  Proof.
    apply map_eq; intros i. rewrite lookup_omap, !lookup_merge.
    by destruct (m1 !! i), (m2 !! i).
  Qed.
End more_merge.

Lemma merge_empty_l {A B C} (f : option A → option B → option C) (m2 : M B) :
  merge f ∅ m2 = omap (f None ∘ Some) m2.
Proof.
  apply map_eq; intros i. rewrite lookup_merge, lookup_omap, lookup_empty.
  by destruct (m2 !! i).
Qed.
Lemma merge_empty_r {A B C} (f : option A → option B → option C) (m1 : M A) :
  merge f m1 ∅ = omap (flip f None ∘ Some) m1.
Proof.
  apply map_eq; intros i. rewrite lookup_merge, lookup_omap, lookup_empty.
  by destruct (m1 !! i).
Qed.
Lemma merge_diag {A C} (f : option A → option A → option C) (m : M A) :
  merge f m m = omap (λ x, f (Some x) (Some x)) m.
Proof.
  apply map_eq. intros i.
  rewrite lookup_merge, lookup_omap. by destruct (m !! i).
Qed.

(** Properties of the [map_zip_with] and [map_zip] functions *)
Lemma map_lookup_zip_with {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i :
  map_zip_with f m1 m2 !! i = (x ← m1 !! i; y ← m2 !! i; Some (f x y)).
Proof.
  unfold map_zip_with. rewrite lookup_merge.
  by destruct (m1 !! i), (m2 !! i).
Qed.
Lemma map_lookup_zip_with_Some {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i z :
  map_zip_with f m1 m2 !! i = Some z ↔
    ∃ x y, z = f x y ∧ m1 !! i = Some x ∧ m2 !! i = Some y.
Proof. rewrite map_lookup_zip_with. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.
Lemma map_lookup_zip_with_None {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i :
  map_zip_with f m1 m2 !! i = None ↔ m1 !! i = None ∨ m2 !! i = None.
Proof. rewrite map_lookup_zip_with. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.

Lemma map_lookup_zip_Some {A B} (m1 : M A) (m2 : M B) i p :
  map_zip m1 m2 !! i = Some p ↔ m1 !! i = Some p.1 ∧ m2 !! i = Some p.2.
Proof. rewrite map_lookup_zip_with_Some. destruct p. naive_solver. Qed.

Lemma map_zip_with_empty {A B C} (f : A → B → C) :
  map_zip_with f ∅ ∅ =@{M C} ∅.
Proof. unfold map_zip_with. by rewrite merge_empty by done. Qed.
Lemma map_zip_with_empty_l {A B C} (f : A → B → C) m2 :
  map_zip_with f ∅ m2 =@{M C} ∅.
Proof.
  unfold map_zip_with. apply map_eq; intros i.
  rewrite lookup_merge, !lookup_empty. destruct (m2 !! i); done.
Qed.
Lemma map_zip_with_empty_r {A B C} (f : A → B → C) m1 :
  map_zip_with f m1 ∅ =@{M C} ∅.
Proof.
  unfold map_zip_with. apply map_eq; intros i.
  rewrite lookup_merge, !lookup_empty. destruct (m1 !! i); done.
Qed.

Lemma map_insert_zip_with {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i y z :
  <[i:=f y z]>(map_zip_with f m1 m2) = map_zip_with f (<[i:=y]>m1) (<[i:=z]>m2).
Proof. unfold map_zip_with. by erewrite insert_merge by done. Qed.
Lemma map_delete_zip_with {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i :
  delete i (map_zip_with f m1 m2) = map_zip_with f (delete i m1) (delete i m2).
Proof. unfold map_zip_with. by rewrite delete_merge. Qed.
Lemma map_zip_with_singleton {A B C} (f : A → B → C) i x y :
  map_zip_with f {[ i := x ]} {[ i := y ]} =@{M C} {[ i := f x y ]}.
Proof. unfold map_zip_with. by erewrite merge_singleton. Qed.

Lemma map_zip_with_fmap {A' A B' B C} (f : A → B → C)
    (g1 : A' → A) (g2 : B' → B) (m1 : M A') (m2 : M B') :
  map_zip_with f (g1 <$> m1) (g2 <$> m2) = map_zip_with (λ x y, f (g1 x) (g2 y)) m1 m2.
Proof.
  apply map_eq; intro i. rewrite !map_lookup_zip_with, !lookup_fmap.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_zip_with_fmap_1 {A' A B C} (f : A → B → C)
    (g : A' → A) (m1 : M A') (m2 : M B) :
  map_zip_with f (g <$> m1) m2 = map_zip_with (λ x y, f (g x) y) m1 m2.
Proof.
  rewrite <- (map_fmap_id m2) at 1. by rewrite map_zip_with_fmap.
Qed.

Lemma map_zip_with_fmap_2 {A B' B C} (f : A → B → C)
    (g : B' → B) (m1 : M A) (m2 : M B') :
  map_zip_with f m1 (g <$> m2) = map_zip_with (λ x y, f x (g y)) m1 m2.
Proof.
  rewrite <-(map_fmap_id m1) at 1. by rewrite map_zip_with_fmap.
Qed.

Lemma map_fmap_zip_with {A B C D} (f : A → B → C) (g : C → D)
    (m1 : M A) (m2 : M B) :
  g <$> map_zip_with f m1 m2 = map_zip_with (λ x y, g (f x y)) m1 m2.
Proof.
  apply map_eq; intro i. rewrite lookup_fmap, !map_lookup_zip_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_zip_with_flip {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) :
  map_zip_with (flip f) m2 m1 = map_zip_with f m1 m2.
Proof.
  apply map_eq; intro i. rewrite !map_lookup_zip_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_zip_with_map_zip {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) :
  map_zip_with f m1 m2 = uncurry f <$> map_zip m1 m2.
Proof.
  apply map_eq; intro i. rewrite lookup_fmap, !map_lookup_zip_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_fmap_zip {A' A B' B} (g1 : A' → A)
    (g2 : B' → B) (m1 : M A') (m2 : M B') :
  map_zip (fmap g1 m1) (fmap g2 m2) = prod_map g1 g2 <$> map_zip m1 m2.
Proof.
  rewrite map_zip_with_fmap, map_zip_with_map_zip.
  generalize (map_zip m1 m2); intro m. apply map_eq; intro i.
  by rewrite !lookup_fmap; destruct (m !! i) as [[x1 x2]|].
Qed.

Lemma map_fmap_zip_with_l
    {A B C} (f : A → B → C) (g : C → A) (m1 : M A) (m2 : M B) :
  (∀ x y, g (f x y) = x) →
  (∀ k, is_Some (m1 !! k) → is_Some (m2 !! k)) →
  g <$> map_zip_with f m1 m2 = m1.
Proof.
  intros ? Hm. apply map_eq; intros k. rewrite lookup_fmap, map_lookup_zip_with.
  destruct (m1 !! _) as [x|] eqn:?; simpl; [|done].
  destruct (Hm k) as [y ->]; [by eauto|]. by f_equal/=.
Qed.
Lemma map_fmap_zip_with_r
    {A B C} (f : A → B → C) (g : C → B) (m1 : M A) (m2 : M B) :
  (∀ x y, g (f x y) = y) →
  (∀ k, is_Some (m2 !! k) → is_Some (m1 !! k)) →
  g <$> map_zip_with f m1 m2 = m2.
Proof.
  intros ? Hm. apply map_eq; intros k. rewrite lookup_fmap, map_lookup_zip_with.
  destruct (m2 !! _) as [x|] eqn:?; simpl; [|by destruct (m1 !! _)].
  destruct (Hm k) as [y ->]; [by eauto|]. by f_equal/=.
Qed.

Lemma map_zip_with_diag {A C} (f : A → A → C) (m : M A) :
  map_zip_with f m m = (λ x, f x x) <$> m.
Proof. unfold map_zip_with. by rewrite merge_diag, map_fmap_alt. Qed.

Lemma map_zip_diag {A} (m : M A) :
  map_zip m m = (λ x, (x, x)) <$> m.
Proof. apply map_zip_with_diag. Qed.

Lemma fst_map_zip {A B} (m1 : M A) (m2 : M B) :
  (∀ k : K, is_Some (m1 !! k) → is_Some (m2 !! k)) →
  fst <$> map_zip m1 m2 = m1.
Proof. intros ?. by apply map_fmap_zip_with_l. Qed.

Lemma snd_map_zip {A B} (m1 : M A) (m2 : M B) :
  (∀ k : K, is_Some (m2 !! k) → is_Some (m1 !! k)) →
  snd <$> map_zip m1 m2 = m2.
Proof. intros ?. by apply map_fmap_zip_with_r. Qed.

Lemma map_zip_fst_snd {A B} (m : M (A * B)) :
  map_zip (fst <$> m) (snd <$> m) = m.
Proof.
  apply map_eq; intros k.
  rewrite map_lookup_zip_with, !lookup_fmap. by destruct (m !! k) as [[]|].
Qed.

(** ** Properties on the [map_relation] relation *)
Section Forall2.
  Context {A B} (R : A → B → Prop) (P : A → Prop) (Q : B → Prop).
  Context `{∀ x y, Decision (R x y), ∀ x, Decision (P x), ∀ y, Decision (Q y)}.

  Let f (mx : option A) (my : option B) : option bool :=
    match mx, my with
    | Some x, Some y => Some (bool_decide (R x y))
    | Some x, None => Some (bool_decide (P x))
    | None, Some y => Some (bool_decide (Q y))
    | None, None => None
    end.
  Lemma map_relation_alt (m1 : M A) (m2 : M B) :
    map_relation R P Q m1 m2 ↔ map_Forall (λ _, Is_true) (merge f m1 m2).
  Proof.
    split.
    - intros Hm i P'; rewrite lookup_merge; intros.
      specialize (Hm i). destruct (m1 !! i), (m2 !! i);
        simplify_eq/=; auto using bool_decide_pack.
    - intros Hm i. specialize (Hm i). rewrite lookup_merge in Hm.
      destruct (m1 !! i), (m2 !! i); simplify_eq/=; auto;
        by eapply bool_decide_unpack, Hm.
  Qed.
  Global Instance map_relation_dec : RelDecision (map_relation (M:=M) R P Q).
  Proof.
    refine (λ m1 m2, cast_if (decide (map_Forall (λ _, Is_true) (merge f m1 m2))));
      abstract by rewrite map_relation_alt.
  Defined.
  (** Due to the finiteness of finite maps, we can extract a witness if the
  relation does not hold. *)
  Lemma map_not_Forall2 (m1 : M A) (m2 : M B) :
    ¬map_relation R P Q m1 m2 ↔ ∃ i,
      (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ ¬R x y)
      ∨ (∃ x, m1 !! i = Some x ∧ m2 !! i = None ∧ ¬P x)
      ∨ (∃ y, m1 !! i = None ∧ m2 !! i = Some y ∧ ¬Q y).
  Proof.
    split.
    - rewrite map_relation_alt, (map_not_Forall _). intros (i&?&Hm&?); exists i.
      rewrite lookup_merge in Hm.
      destruct (m1 !! i), (m2 !! i); naive_solver auto 2 using bool_decide_pack.
    - unfold map_relation, option_relation.
      by intros [i[(x&y&?&?&?)|[(x&?&?&?)|(y&?&?&?)]]] Hm;
        specialize (Hm i); simplify_option_eq.
  Qed.
End Forall2.

(** ** Properties of the [map_agree] operation *)
Lemma map_agree_spec {A} (m1 m2 : M A) :
  map_agree m1 m2 ↔ ∀ i x y, m1 !! i = Some x → m2 !! i = Some y → x = y.
Proof.
  apply forall_proper; intros i; destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_agree_alt {A} (m1 m2 : M A) :
  map_agree m1 m2 ↔ ∀ i, m1 !! i = None ∨ m2 !! i = None ∨ m1 !! i = m2 !! i.
Proof.
  apply forall_proper; intros i; destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_not_agree {A} (m1 m2 : M A) `{!EqDecision A}:
  ¬map_agree m1 m2 ↔ ∃ i x1 x2, m1 !! i = Some x1 ∧ m2 !! i = Some x2 ∧ x1 ≠ x2.
Proof.
  unfold map_agree. rewrite map_not_Forall2 by solve_decision. naive_solver.
Qed.
Global Instance map_agree_refl {A} : Reflexive (map_agree : relation (M A)).
Proof. intros ?. rewrite !map_agree_spec. naive_solver. Qed.
Global Instance map_agree_sym {A} : Symmetric (map_agree : relation (M A)).
Proof.
  intros m1 m2. rewrite !map_agree_spec.
  intros Hm i x y Hm1 Hm2. symmetry. naive_solver.
Qed.
Lemma map_agree_empty_l {A} (m : M A) : map_agree ∅ m.
Proof. rewrite !map_agree_spec. intros i x y. by rewrite lookup_empty. Qed.
Lemma map_agree_empty_r {A} (m : M A) : map_agree m ∅.
Proof. rewrite !map_agree_spec. intros i x y. by rewrite lookup_empty. Qed.
Lemma map_agree_weaken {A} (m1 m1' m2 m2' : M A) :
  map_agree m1' m2' → m1 ⊆ m1' → m2 ⊆ m2' → map_agree m1 m2.
Proof. rewrite !map_subseteq_spec, !map_agree_spec. eauto. Qed.
Lemma map_agree_weaken_l {A} (m1 m1' m2  : M A) :
  map_agree m1' m2 → m1 ⊆ m1' → map_agree m1 m2.
Proof. eauto using map_agree_weaken. Qed.
Lemma map_agree_weaken_r {A} (m1 m2 m2' : M A) :
  map_agree m1 m2' → m2 ⊆ m2' → map_agree m1 m2.
Proof. eauto using map_agree_weaken. Qed.
Lemma map_agree_Some_l {A} (m1 m2 : M A) i x:
  map_agree m1 m2 → m1 !! i = Some x → m2 !! i = Some x ∨ m2 !! i = None.
Proof. rewrite map_agree_spec. destruct (m2 !! i) eqn: ?; naive_solver. Qed.
Lemma map_agree_Some_r {A} (m1 m2 : M A) i x:
  map_agree m1 m2 → m2 !! i = Some x → m1 !! i = Some x ∨ m1 !! i = None.
Proof. rewrite (symmetry_iff map_agree). apply map_agree_Some_l. Qed.
Lemma map_agree_singleton_l {A} (m: M A) i x :
  map_agree {[i:=x]} m ↔ m !! i = Some x ∨ m !! i = None.
Proof.
  rewrite map_agree_spec. setoid_rewrite lookup_singleton_Some.
  destruct (m !! i) eqn:?; naive_solver.
Qed.
Lemma map_agree_singleton_r {A} (m : M A) i x :
  map_agree m {[i := x]} ↔ m !! i = Some x ∨ m !! i = None.
Proof. by rewrite (symmetry_iff map_agree), map_agree_singleton_l. Qed.
Lemma map_agree_delete_l {A} (m1 m2 : M A) i :
  map_agree m1 m2 → map_agree (delete i m1) m2.
Proof.
  rewrite !map_agree_alt. intros Hagree j. rewrite lookup_delete_None.
  destruct (Hagree j) as [|[|<-]]; auto.
  destruct (decide (i = j)); [naive_solver|].
  rewrite lookup_delete_ne; naive_solver.
Qed.
Lemma map_agree_delete_r {A} (m1 m2 : M A) i :
  map_agree m1 m2 → map_agree m1 (delete i m2).
Proof. symmetry. by apply map_agree_delete_l. Qed.

Lemma map_agree_filter {A} (P : K * A → Prop)
    `{!∀ x, Decision (P x)} (m1 m2 : M A) :
  map_agree m1 m2 → map_agree (filter P m1) (filter P m2).
Proof.
  rewrite !map_agree_spec. intros ? i x y.
  rewrite !map_lookup_filter_Some. naive_solver.
Qed.

Lemma map_agree_fmap_1 {A B} (f : A → B) (m1 m2 : M A) `{!Inj (=) (=) f}:
  map_agree (f <$> m1) (f <$> m2) → map_agree m1 m2.
Proof.
  rewrite !map_agree_spec. setoid_rewrite lookup_fmap_Some. naive_solver.
Qed.
Lemma map_agree_fmap_2 {A B} (f : A → B) (m1 m2 : M A):
  map_agree m1 m2 → map_agree (f <$> m1) (f <$> m2).
Proof.
  rewrite !map_agree_spec. setoid_rewrite lookup_fmap_Some. naive_solver.
Qed.
Lemma map_agree_fmap {A B} (f : A → B) (m1 m2 : M A) `{!Inj (=) (=) f}:
  map_agree (f <$> m1) (f <$> m2) ↔ map_agree m1 m2.
Proof. naive_solver eauto using map_agree_fmap_1, map_agree_fmap_2. Qed.

Lemma map_agree_omap {A B} (f : A → option B) (m1 m2 : M A) :
  map_agree m1 m2 → map_agree (omap f m1) (omap f m2).
Proof. rewrite !map_agree_spec. setoid_rewrite lookup_omap_Some. naive_solver. Qed.

(** ** Properties on the disjoint maps *)
Lemma map_disjoint_spec {A} (m1 m2 : M A) :
  m1 ##ₘ m2 ↔ ∀ i x y, m1 !! i = Some x → m2 !! i = Some y → False.
Proof.
  apply forall_proper; intros i; destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_disjoint_alt {A} (m1 m2 : M A) :
  m1 ##ₘ m2 ↔ ∀ i, m1 !! i = None ∨ m2 !! i = None.
Proof.
  apply forall_proper; intros i; destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_not_disjoint {A} (m1 m2 : M A) :
  ¬m1 ##ₘ m2 ↔ ∃ i x1 x2, m1 !! i = Some x1 ∧ m2 !! i = Some x2.
Proof.
  unfold disjoint, map_disjoint. rewrite map_not_Forall2 by solve_decision.
  naive_solver.
Qed.
Global Instance map_disjoint_sym {A} : Symmetric (map_disjoint : relation (M A)).
Proof. intros m1 m2. rewrite !map_disjoint_spec. naive_solver. Qed.
Lemma map_disjoint_empty_l {A} (m : M A) : ∅ ##ₘ m.
Proof. rewrite !map_disjoint_spec. intros i x y. by rewrite lookup_empty. Qed.
Lemma map_disjoint_empty_r {A} (m : M A) : m ##ₘ ∅.
Proof. rewrite !map_disjoint_spec. intros i x y. by rewrite lookup_empty. Qed.
Lemma map_disjoint_weaken {A} (m1 m1' m2 m2' : M A) :
  m1' ##ₘ m2' → m1 ⊆ m1' → m2 ⊆ m2' → m1 ##ₘ m2.
Proof. rewrite !map_subseteq_spec, !map_disjoint_spec. eauto. Qed.
Lemma map_disjoint_weaken_l {A} (m1 m1' m2  : M A) :
  m1' ##ₘ m2 → m1 ⊆ m1' → m1 ##ₘ m2.
Proof. eauto using map_disjoint_weaken. Qed.
Lemma map_disjoint_weaken_r {A} (m1 m2 m2' : M A) :
  m1 ##ₘ m2' → m2 ⊆ m2' → m1 ##ₘ m2.
Proof. eauto using map_disjoint_weaken. Qed.
Lemma map_disjoint_Some_l {A} (m1 m2 : M A) i x:
  m1 ##ₘ m2 → m1 !! i = Some x → m2 !! i = None.
Proof. rewrite map_disjoint_spec, eq_None_not_Some. intros ?? [??]; eauto. Qed.
Lemma map_disjoint_Some_r {A} (m1 m2 : M A) i x:
  m1 ##ₘ m2 → m2 !! i = Some x → m1 !! i = None.
Proof. rewrite (symmetry_iff map_disjoint). apply map_disjoint_Some_l. Qed.
Lemma map_disjoint_singleton_l {A} (m: M A) i x : {[i:=x]} ##ₘ m ↔ m !! i = None.
Proof.
  rewrite !map_disjoint_spec. setoid_rewrite lookup_singleton_Some.
  destruct (m !! i) eqn:?; naive_solver.
Qed.
Lemma map_disjoint_singleton_r {A} (m : M A) i x :
  m ##ₘ {[i := x]} ↔ m !! i = None.
Proof. by rewrite (symmetry_iff map_disjoint), map_disjoint_singleton_l. Qed.
Lemma map_disjoint_singleton_l_2 {A} (m : M A) i x :
  m !! i = None → {[i := x]} ##ₘ m.
Proof. by rewrite map_disjoint_singleton_l. Qed.
Lemma map_disjoint_singleton_r_2 {A} (m : M A) i x :
  m !! i = None → m ##ₘ {[i := x]}.
Proof. by rewrite map_disjoint_singleton_r. Qed.
Lemma map_disjoint_delete_l {A} (m1 m2 : M A) i : m1 ##ₘ m2 → delete i m1 ##ₘ m2.
Proof.
  rewrite !map_disjoint_alt. intros Hdisjoint j. destruct (Hdisjoint j); auto.
  rewrite lookup_delete_None. tauto.
Qed.
Lemma map_disjoint_delete_r {A} (m1 m2 : M A) i : m1 ##ₘ m2 → m1 ##ₘ delete i m2.
Proof. symmetry. by apply map_disjoint_delete_l. Qed.

Lemma map_disjoint_filter {A} (P : K * A → Prop)
    `{!∀ x, Decision (P x)} (m1 m2 : M A) :
  m1 ##ₘ m2 → filter P m1 ##ₘ filter P m2.
Proof.
  rewrite !map_disjoint_spec. intros ? i x y.
  rewrite !map_lookup_filter_Some. naive_solver.
Qed.
Lemma map_disjoint_filter_complement {A} (P : K * A → Prop)
    `{!∀ x, Decision (P x)} (m : M A) :
  filter P m ##ₘ filter (λ v, ¬ P v) m.
Proof.
  apply map_disjoint_spec. intros i x y.
  rewrite !map_lookup_filter_Some. naive_solver.
Qed.

Lemma map_disjoint_fmap {A B} (f1 f2 : A → B) (m1 m2 : M A) :
  f1 <$> m1 ##ₘ f2 <$> m2 ↔ m1 ##ₘ m2.
Proof.
  rewrite !map_disjoint_spec. setoid_rewrite lookup_fmap_Some. naive_solver.
Qed.
Lemma map_disjoint_omap {A B} (f1 f2 : A → option B) (m1 m2 : M A) :
  m1 ##ₘ m2 → omap f1 m1 ##ₘ omap f2 m2.
Proof.
  rewrite !map_disjoint_spec. setoid_rewrite lookup_omap_Some. naive_solver.
Qed.

Lemma map_disjoint_agree {A} (m1 m2 : M A) :
  m1 ##ₘ m2 → map_agree m1 m2.
Proof. rewrite !map_disjoint_spec, !map_agree_spec. naive_solver. Qed.

(** ** Properties of the [union_with] operation *)
Section union_with.
  Context {A} (f : A → A → option A).
  Implicit Types m : M A.

  Lemma lookup_union_with m1 m2 i :
    union_with f m1 m2 !! i = union_with f (m1 !! i) (m2 !! i).
  Proof.
    unfold union_with, map_union_with. rewrite lookup_merge.
    by destruct (m1 !! i), (m2 !! i).
  Qed.
  Lemma lookup_union_with_Some m1 m2 i z :
    union_with f m1 m2 !! i = Some z ↔
      (m1 !! i = Some z ∧ m2 !! i = None) ∨
      (m1 !! i = None ∧ m2 !! i = Some z) ∨
      (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
  Proof.
    rewrite lookup_union_with.
    destruct (m1 !! i), (m2 !! i); compute; naive_solver.
  Qed.
  Global Instance: LeftId (=@{M A}) ∅ (union_with f).
  Proof. unfold union_with, map_union_with. apply _. Qed.
  Global Instance: RightId (=@{M A}) ∅ (union_with f).
  Proof. unfold union_with, map_union_with. apply _. Qed.
  Lemma union_with_comm m1 m2 :
    (∀ i x y, m1 !! i = Some x → m2 !! i = Some y → f x y = f y x) →
    union_with f m1 m2 = union_with f m2 m1.
  Proof.
    intros. apply merge_comm. intros i.
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
  Qed.
  Global Instance: Comm (=) f → Comm (=@{M A}) (union_with f).
  Proof. intros ???. apply union_with_comm. eauto. Qed.
  Lemma union_with_idemp m :
    (∀ i x, m !! i = Some x → f x x = Some x) → union_with f m m = m.
  Proof.
    intros. apply merge_idemp. intros i.
    destruct (m !! i) eqn:?; simpl; eauto.
  Qed.
  Lemma alter_union_with (g : A → A) m1 m2 i :
    (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) (g y)) →
    alter g i (union_with f m1 m2) =
      union_with f (alter g i m1) (alter g i m2).
  Proof.
    intros. apply partial_alter_merge.
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
  Qed.
  Lemma alter_union_with_l (g : A → A) m1 m2 i :
    (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) y) →
    (∀ y, m1 !! i = None → m2 !! i = Some y → g y = y) →
    alter g i (union_with f m1 m2) = union_with f (alter g i m1) m2.
  Proof.
    intros. apply partial_alter_merge_l.
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; f_equal/=; auto.
  Qed.
  Lemma alter_union_with_r (g : A → A) m1 m2 i :
    (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f x (g y)) →
    (∀ x, m1 !! i = Some x → m2 !! i = None → g x = x) →
    alter g i (union_with f m1 m2) = union_with f m1 (alter g i m2).
  Proof.
    intros. apply partial_alter_merge_r.
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; f_equal/=; auto.
  Qed.
  Lemma delete_union_with m1 m2 i :
    delete i (union_with f m1 m2) = union_with f (delete i m1) (delete i m2).
  Proof. by apply partial_alter_merge. Qed.
  Lemma foldr_delete_union_with (m1 m2 : M A) is :
    foldr delete (union_with f m1 m2) is =
      union_with f (foldr delete m1 is) (foldr delete m2 is).
  Proof.
    induction is as [|?? IHis]; simpl; [done|].
    by rewrite IHis, delete_union_with.
  Qed.
  Lemma insert_union_with m1 m2 i x y z :
    f x y = Some z →
    <[i:=z]>(union_with f m1 m2) = union_with f (<[i:=x]>m1) (<[i:=y]>m2).
  Proof. by intros; apply (partial_alter_merge _). Qed.
  Lemma insert_union_with_l m1 m2 i x :
    m2 !! i = None → <[i:=x]>(union_with f m1 m2) = union_with f (<[i:=x]>m1) m2.
  Proof.
    intros Hm2. unfold union_with, map_union_with.
    by erewrite insert_merge_l by (by rewrite Hm2).
  Qed.
  Lemma insert_union_with_r m1 m2 i x :
    m1 !! i = None → <[i:=x]>(union_with f m1 m2) = union_with f m1 (<[i:=x]>m2).
  Proof.
    intros Hm1. unfold union_with, map_union_with.
    by erewrite insert_merge_r by (by rewrite Hm1).
  Qed.
End union_with.

(** ** Properties of the [union] operation *)
Global Instance map_empty_union {A} : LeftId (=@{M A}) ∅ (∪) := _.
Global Instance map_union_empty {A} : RightId (=@{M A}) ∅ (∪) := _.
Global Instance map_union_assoc {A} : Assoc (=@{M A}) (∪).
Proof.
  intros m1 m2 m3. unfold union, map_union, union_with, map_union_with.
  apply merge_assoc. intros i.
  by destruct (m1 !! i), (m2 !! i), (m3 !! i).
Qed.
Global Instance map_union_idemp {A} : IdemP (=@{M A}) (∪).
Proof. intros ?. by apply union_with_idemp. Qed.
Lemma lookup_union {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = (m1 !! i) ∪ (m2 !! i).
Proof. apply lookup_union_with. Qed.
Lemma lookup_union_r {A} (m1 m2 : M A) i :
  m1 !! i = None → (m1 ∪ m2) !! i = m2 !! i.
Proof. intros Hi. by rewrite lookup_union, Hi, (left_id_L _ _).  Qed.
Lemma lookup_union_l {A} (m1 m2 : M A) i :
  m2 !! i = None → (m1 ∪ m2) !! i = m1 !! i.
Proof. intros Hi. rewrite lookup_union, Hi. by destruct (m1 !! i). Qed.
Lemma lookup_union_l' {A} (m1 m2 : M A) i :
  is_Some (m1 !! i) → (m1 ∪ m2) !! i = m1 !! i.
Proof. intros [x Hi]. rewrite lookup_union, Hi. by destruct (m2 !! i). Qed.
Lemma lookup_union_Some_raw {A} (m1 m2 : M A) i x :
  (m1 ∪ m2) !! i = Some x ↔
    m1 !! i = Some x ∨ (m1 !! i = None ∧ m2 !! i = Some x).
Proof. rewrite lookup_union. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.
Lemma lookup_union_None {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
Proof. rewrite lookup_union.  destruct (m1 !! i), (m2 !! i); naive_solver. Qed.
Lemma lookup_union_None_1 {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = None → m1 !! i = None ∧ m2 !! i = None.
Proof. apply lookup_union_None. Qed.
Lemma lookup_union_None_2 {A} (m1 m2 : M A) i :
  m1 !! i = None → m2 !! i = None → (m1 ∪ m2) !! i = None.
Proof. intros. by apply lookup_union_None. Qed.
Lemma lookup_union_Some {A} (m1 m2 : M A) i x :
  m1 ##ₘ m2 → (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m2 !! i = Some x.
Proof.
  intros Hdisjoint. rewrite lookup_union_Some_raw.
  intuition eauto using map_disjoint_Some_r.
Qed.
Lemma lookup_union_Some_l {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → (m1 ∪ m2) !! i = Some x.
Proof. intro. rewrite lookup_union_Some_raw; intuition. Qed.
Lemma lookup_union_Some_r {A} (m1 m2 : M A) i x :
  m1 ##ₘ m2 → m2 !! i = Some x → (m1 ∪ m2) !! i = Some x.
Proof. intro. rewrite lookup_union_Some; intuition. Qed.
Lemma lookup_union_Some_inv_l {A} (m1 m2 : M A) i x :
  (m1 ∪ m2) !! i = Some x → m2 !! i = None → m1 !! i = Some x.
Proof. rewrite lookup_union_Some_raw. naive_solver. Qed.
Lemma lookup_union_Some_inv_r {A} (m1 m2 : M A) i x :
  (m1 ∪ m2) !! i = Some x → m1 !! i = None → m2 !! i = Some x.
Proof. rewrite lookup_union_Some_raw. naive_solver. Qed.
Lemma lookup_union_is_Some {A} (m1 m2 : M A) i :
  is_Some ((m1 ∪ m2) !! i) ↔ is_Some (m1 !! i) ∨ is_Some (m2 !! i).
Proof.
  rewrite <-!not_eq_None_Some, !lookup_union_None.
  destruct (m1 !! i); naive_solver.
Qed.

Lemma map_union_comm {A} (m1 m2 : M A) : m1 ##ₘ m2 → m1 ∪ m2 = m2 ∪ m1.
Proof.
  intros Hdisjoint. apply (merge_comm (union_with (λ x _, Some x))).
  intros i. specialize (Hdisjoint i).
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.

Lemma map_positive_l {A} (m1 m2 : M A) : m1 ∪ m2 = ∅ → m1 = ∅.
Proof.
  intros Hm. apply map_empty. intros i. apply (f_equal (.!! i)) in Hm.
  rewrite lookup_empty, lookup_union_None in Hm; tauto.
Qed.
Lemma map_positive_l_alt {A} (m1 m2 : M A) : m1 ≠ ∅ → m1 ∪ m2 ≠ ∅.
Proof. eauto using map_positive_l. Qed.

Lemma map_subseteq_union {A} (m1 m2 : M A) : m1 ⊆ m2 → m1 ∪ m2 = m2.
Proof.
  rewrite map_subseteq_spec.
  intros Hm1m2. apply map_eq. intros i. apply option_eq. intros x.
  rewrite lookup_union_Some_raw. split; [by intuition |].
  intros Hm2. specialize (Hm1m2 i). destruct (m1 !! i) as [y|]; [| by auto].
  rewrite (Hm1m2 y eq_refl) in Hm2. intuition congruence.
Qed.
Lemma map_union_subseteq_l {A} (m1 m2 : M A) : m1 ⊆ m1 ∪ m2.
Proof.
  rewrite map_subseteq_spec. intros ? i x. rewrite lookup_union_Some_raw. tauto.
Qed.
Lemma map_union_subseteq_r {A} (m1 m2 : M A) : m1 ##ₘ m2 → m2 ⊆ m1 ∪ m2.
Proof.
  intros. rewrite map_union_comm by done. by apply map_union_subseteq_l.
Qed.
Lemma map_union_subseteq_l' {A} (m1 m2 m3 : M A) : m1 ⊆ m2 → m1 ⊆ m2 ∪ m3.
Proof. intros. trans m2; auto using map_union_subseteq_l. Qed.
Lemma map_union_subseteq_r' {A} (m1 m2 m3 : M A) :
  m2 ##ₘ m3 → m1 ⊆ m3 → m1 ⊆ m2 ∪ m3.
Proof. intros. trans m3; auto using map_union_subseteq_r. Qed.

Lemma map_union_least {A} (m1 m2 m3 : M A) :
  m1 ⊆ m3 → m2 ⊆ m3 → m1 ∪ m2 ⊆ m3.
Proof.
  intros ??. apply map_subseteq_spec.
  intros ?? [?|[_ ?]]%lookup_union_Some_raw; by eapply lookup_weaken.
Qed.

Lemma map_union_mono_l {A} (m1 m2 m3 : M A) : m1 ⊆ m2 → m3 ∪ m1 ⊆ m3 ∪ m2.
Proof.
  rewrite !map_subseteq_spec. intros ???.
  rewrite !lookup_union_Some_raw. naive_solver.
Qed.
Lemma map_union_mono_r {A} (m1 m2 m3 : M A) :
  m2 ##ₘ m3 → m1 ⊆ m2 → m1 ∪ m3 ⊆ m2 ∪ m3.
Proof.
  intros. rewrite !(map_union_comm _ m3)
    by eauto using map_disjoint_weaken_l.
  by apply map_union_mono_l.
Qed.
Lemma map_union_reflecting_l {A} (m1 m2 m3 : M A) :
  m3 ##ₘ m1 → m3 ##ₘ m2 → m3 ∪ m1 ⊆ m3 ∪ m2 → m1 ⊆ m2.
Proof.
  rewrite !map_subseteq_spec. intros Hm31 Hm32 Hm i x ?. specialize (Hm i x).
  rewrite !lookup_union_Some in Hm by done. destruct Hm; auto.
  by rewrite map_disjoint_spec in Hm31; destruct (Hm31 i x x).
Qed.
Lemma map_union_reflecting_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 ⊆ m2 ∪ m3 → m1 ⊆ m2.
Proof.
  intros ??. rewrite !(map_union_comm _ m3) by done.
  by apply map_union_reflecting_l.
Qed.
Lemma map_union_cancel_l {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m3 ∪ m1 = m3 ∪ m2 → m1 = m2.
Proof.
  intros. apply (anti_symm (⊆)); apply map_union_reflecting_l with m3;
    by try apply reflexive_eq.
Qed.
Lemma map_union_cancel_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 = m2 ∪ m3 → m1 = m2.
Proof.
  intros. apply (anti_symm (⊆)); apply map_union_reflecting_r with m3;
    by try apply reflexive_eq.
Qed.
Lemma map_disjoint_union_l {A} (m1 m2 m3 : M A) :
  m1 ∪ m2 ##ₘ m3 ↔ m1 ##ₘ m3 ∧ m2 ##ₘ m3.
Proof.
  rewrite !map_disjoint_alt. setoid_rewrite lookup_union_None. naive_solver.
Qed.
Lemma map_disjoint_union_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m2 ∪ m3 ↔ m1 ##ₘ m2 ∧ m1 ##ₘ m3.
Proof.
  rewrite !map_disjoint_alt. setoid_rewrite lookup_union_None. naive_solver.
Qed.
Lemma map_disjoint_union_l_2 {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m2 ##ₘ m3.
Proof. by rewrite map_disjoint_union_l. Qed.
Lemma map_disjoint_union_r_2 {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m2 → m1 ##ₘ m3 → m1 ##ₘ m2 ∪ m3.
Proof. by rewrite map_disjoint_union_r. Qed.
Lemma insert_union_singleton_l {A} (m : M A) i x : <[i:=x]>m = {[i := x]} ∪ m.
Proof.
  apply map_eq. intros j. apply option_eq. intros y.
  rewrite lookup_union_Some_raw.
  destruct (decide (i = j)); subst.
  - rewrite !lookup_singleton, lookup_insert. intuition congruence.
  - rewrite !lookup_singleton_ne, lookup_insert_ne; intuition congruence.
Qed.
Lemma insert_union_singleton_r {A} (m : M A) i x :
  m !! i = None → <[i:=x]>m = m ∪ {[i := x]}.
Proof.
  intro. rewrite insert_union_singleton_l, map_union_comm; [done |].
  by apply map_disjoint_singleton_l.
Qed.
Lemma union_singleton_r {A} (m : M A) i x y :
  m !! i = Some x → m ∪ {[i := y]} = m.
Proof.
  intro Hlkup. apply map_eq. intros j. rewrite lookup_union.
  destruct (decide (i = j)); subst.
  - by rewrite !lookup_singleton, Hlkup.
  - rewrite lookup_singleton_ne by done.
    by destruct (m !! j).
Qed.
Lemma map_disjoint_insert_l {A} (m1 m2 : M A) i x :
  <[i:=x]>m1 ##ₘ m2 ↔ m2 !! i = None ∧ m1 ##ₘ m2.
Proof.
  rewrite insert_union_singleton_l.
  by rewrite map_disjoint_union_l, map_disjoint_singleton_l.
Qed.
Lemma map_disjoint_insert_r {A} (m1 m2 : M A) i x :
  m1 ##ₘ <[i:=x]>m2 ↔ m1 !! i = None ∧ m1 ##ₘ m2.
Proof.
  rewrite insert_union_singleton_l.
  by rewrite map_disjoint_union_r, map_disjoint_singleton_r.
Qed.
Lemma map_disjoint_insert_l_2 {A} (m1 m2 : M A) i x :
  m2 !! i = None → m1 ##ₘ m2 → <[i:=x]>m1 ##ₘ m2.
Proof. by rewrite map_disjoint_insert_l. Qed.
Lemma map_disjoint_insert_r_2 {A} (m1 m2 : M A) i x :
  m1 !! i = None → m1 ##ₘ m2 → m1 ##ₘ <[i:=x]>m2.
Proof. by rewrite map_disjoint_insert_r. Qed.
Lemma insert_union_l {A} (m1 m2 : M A) i x :
  <[i:=x]>(m1 ∪ m2) = <[i:=x]>m1 ∪ m2.
Proof. by rewrite !insert_union_singleton_l, (assoc_L (∪)). Qed.
Lemma insert_union_r {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]>(m1 ∪ m2) = m1 ∪ <[i:=x]>m2.
Proof.
  intro. rewrite !insert_union_singleton_l, !(assoc_L (∪)).
  rewrite (map_union_comm m1); [done |].
  by apply map_disjoint_singleton_r.
Qed.
Lemma foldr_insert_union {A} (m : M A) l :
  foldr (λ p, <[p.1:=p.2]>) m l = list_to_map l ∪ m.
Proof.
  induction l as [|i l IH]; simpl; [by rewrite (left_id_L _ _)|].
  by rewrite IH, insert_union_l.
Qed.
Lemma delete_union {A} (m1 m2 : M A) i :
  delete i (m1 ∪ m2) = delete i m1 ∪ delete i m2.
Proof. apply delete_union_with. Qed.
Lemma union_delete_insert {A} (m1 m2 : M A) i x :
  m1 !! i = Some x →
  delete i m1 ∪ <[i:=x]> m2 = m1 ∪ m2.
Proof.
  intros. rewrite <-insert_union_r by apply lookup_delete.
  by rewrite insert_union_l, insert_delete by done.
Qed.
Lemma union_insert_delete {A} (m1 m2 : M A) i x :
  m1 !! i = None → m2 !! i = Some x →
  <[i:=x]> m1 ∪ delete i m2 = m1 ∪ m2.
Proof.
  intros. rewrite <-insert_union_l by apply lookup_delete.
  by rewrite insert_union_r, insert_delete by done.
Qed.
Lemma map_Forall_union_1_1 {A} (m1 m2 : M A) P :
  map_Forall P (m1 ∪ m2) → map_Forall P m1.
Proof. intros HP i x ?. apply HP, lookup_union_Some_raw; auto. Qed.
Lemma map_Forall_union_1_2 {A} (m1 m2 : M A) P :
  m1 ##ₘ m2 → map_Forall P (m1 ∪ m2) → map_Forall P m2.
Proof. intros ? HP i x ?. apply HP, lookup_union_Some; auto. Qed.
Lemma map_Forall_union_2 {A} (m1 m2 : M A) P :
  map_Forall P m1 → map_Forall P m2 → map_Forall P (m1 ∪ m2).
Proof. intros ???? [|[]]%lookup_union_Some_raw; eauto. Qed.
Lemma map_Forall_union {A} (m1 m2 : M A) P :
  m1 ##ₘ m2 →
  map_Forall P (m1 ∪ m2) ↔ map_Forall P m1 ∧ map_Forall P m2.
Proof.
  naive_solver eauto using map_Forall_union_1_1,
    map_Forall_union_1_2, map_Forall_union_2.
Qed.
Lemma map_filter_union {A} (P : K * A → Prop) `{!∀ x, Decision (P x)} (m1 m2 : M A) :
  m1 ##ₘ m2 →
  filter P (m1 ∪ m2) = filter P m1 ∪ filter P m2.
Proof.
  intros. apply map_eq; intros i. apply option_eq; intros x.
  rewrite lookup_union_Some, !map_lookup_filter_Some,
    lookup_union_Some by auto using map_disjoint_filter.
  naive_solver.
Qed.
Lemma map_filter_union_complement {A} (P : K * A → Prop)
    `{!∀ x, Decision (P x)} (m : M A) :
  filter P m ∪ filter (λ v, ¬ P v) m = m.
Proof.
  apply map_eq; intros i. apply option_eq; intros x.
  rewrite lookup_union_Some, !map_lookup_filter_Some
    by auto using map_disjoint_filter_complement.
  destruct (decide (P (i,x))); naive_solver.
Qed.
Lemma map_filter_or {A} (P Q : K * A → Prop)
    `{!∀ x, Decision (P x), !∀ x, Decision (Q x)} (m : M A) :
  filter (λ x, P x ∨ Q x) m = filter P m ∪ filter Q m.
Proof.
  apply map_eq. intros k. rewrite lookup_union. rewrite !map_lookup_filter.
  destruct (m !! k); simpl; repeat case_guard; naive_solver.
Qed.
Lemma map_fmap_union {A B} (f : A → B) (m1 m2 : M A) :
  f <$> (m1 ∪ m2) = (f <$> m1) ∪ (f <$> m2).
Proof.
  apply map_eq; intros i. apply option_eq; intros x.
  rewrite lookup_fmap, !lookup_union, !lookup_fmap.
  destruct (m1 !! i), (m2 !! i); auto.
Qed.
Lemma map_omap_union {A B} (f : A → option B) (m1 m2 : M A) :
  m1 ##ₘ m2 →
  omap f (m1 ∪ m2) = omap f m1 ∪ omap f m2.
Proof.
  intros Hdisj. apply map_eq; intros i. specialize (Hdisj i).
  apply option_eq; intros x.
  rewrite lookup_omap, !lookup_union, !lookup_omap.
  destruct (m1 !! i), (m2 !! i); simpl; repeat (destruct (f _)); naive_solver.
Qed.

Lemma map_size_disj_union {A} (m1 m2 : M A) :
  m1 ##ₘ m2 → size (m1 ∪ m2) = size m1 + size m2.
Proof.
  intros Hdisj. induction m1 as [|k x m1 Hm1 IH] using map_ind.
  { rewrite (left_id _ _), map_size_empty. done. }
  rewrite <-insert_union_l.
  rewrite map_size_insert.
  rewrite lookup_union_r by done.
  apply map_disjoint_insert_l in Hdisj as [-> Hdisj].
  rewrite map_size_insert, Hm1.
  rewrite IH by done. done.
Qed.

Lemma map_cross_split {A} (ma mb mc md : M A) :
  ma ##ₘ mb → mc ##ₘ md →
  ma ∪ mb = mc ∪ md →
  ∃ mac mad mbc mbd,
    mac ##ₘ mad ∧ mbc ##ₘ mbd ∧
    mac ##ₘ mbc ∧ mad ##ₘ mbd ∧
    mac ∪ mad = ma ∧ mbc ∪ mbd = mb ∧ mac ∪ mbc = mc ∧ mad ∪ mbd = md.
Proof.
  intros Hab_disj Hcd_disj Hab.
  exists (filter (λ kx, is_Some (mc !! kx.1)) ma),
    (filter (λ kx, ¬is_Some (mc !! kx.1)) ma),
    (filter (λ kx, is_Some (mc !! kx.1)) mb),
    (filter (λ kx, ¬is_Some (mc !! kx.1)) mb).
  split_and!; [auto using map_disjoint_filter_complement, map_disjoint_filter,
    map_filter_union_complement..| |].
  - rewrite <-map_filter_union, Hab by done.
    apply map_eq; intros k. apply option_eq; intros x.
    rewrite map_lookup_filter_Some, lookup_union_Some, <-not_eq_None_Some by done.
    rewrite map_disjoint_alt in Hcd_disj; naive_solver.
  - rewrite <-map_filter_union, Hab by done.
    apply map_eq; intros k. apply option_eq; intros x.
    rewrite map_lookup_filter_Some, lookup_union_Some, <-not_eq_None_Some by done.
    rewrite map_disjoint_alt in Hcd_disj; naive_solver.
Qed.

(** ** Properties of the [union_list] operation *)
Lemma map_disjoint_union_list_l {A} (ms : list (M A)) (m : M A) :
  ⋃ ms ##ₘ m ↔ Forall (.##ₘ m) ms.
Proof.
  split.
  - induction ms; simpl; rewrite ?map_disjoint_union_l; intuition.
  - induction 1; simpl; [apply map_disjoint_empty_l |].
    by rewrite map_disjoint_union_l.
Qed.
Lemma map_disjoint_union_list_r {A} (ms : list (M A)) (m : M A) :
  m ##ₘ ⋃ ms ↔ Forall (.##ₘ m) ms.
Proof. by rewrite (symmetry_iff map_disjoint), map_disjoint_union_list_l. Qed.
Lemma map_disjoint_union_list_l_2 {A} (ms : list (M A)) (m : M A) :
  Forall (.##ₘ m) ms → ⋃ ms ##ₘ m.
Proof. by rewrite map_disjoint_union_list_l. Qed.
Lemma map_disjoint_union_list_r_2 {A} (ms : list (M A)) (m : M A) :
  Forall (.##ₘ m) ms → m ##ₘ ⋃ ms.
Proof. by rewrite map_disjoint_union_list_r. Qed.

(** ** Properties of the folding the [delete] function *)
Lemma lookup_foldr_delete {A} (m : M A) is j :
  j ∈ is → foldr delete m is !! j = None.
Proof.
  induction 1 as [|i j is]; simpl; [by rewrite lookup_delete|].
  by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_delete, ?lookup_delete_ne by done.
Qed.
Lemma lookup_foldr_delete_not_elem_of {A} (m : M A) is j :
  j ∉ is → foldr delete m is !! j = m !! j.
Proof.
  induction is; simpl; [done |]. rewrite elem_of_cons; intros.
  rewrite lookup_delete_ne; intuition.
Qed.
Lemma lookup_foldr_delete_Some {A} (m : M A) is j y :
  foldr delete m is !! j = Some y ↔ j ∉ is ∧ m !! j = Some y.
Proof. induction is; simpl; rewrite ?lookup_delete_Some; set_solver. Qed.
Lemma foldr_delete_notin {A} (m : M A) is :
  Forall (λ i, m !! i = None) is → foldr delete m is = m.
Proof. induction 1; simpl; [done |]. rewrite delete_notin; congruence. Qed.
Lemma foldr_delete_commute {A} (m : M A) is j :
  delete j (foldr delete m is) = foldr delete (delete j m) is.
Proof. induction is as [|?? IH]; [done| ]. simpl. by rewrite delete_commute, IH. Qed.
Lemma foldr_delete_insert {A} (m : M A) is j x :
  j ∈ is → foldr delete (<[j:=x]>m) is = foldr delete m is.
Proof.
  induction 1 as [i is|j i is ? IH]; simpl; [|by rewrite IH].
  by rewrite !foldr_delete_commute, delete_insert_delete.
Qed.
Lemma foldr_delete_insert_ne {A} (m : M A) is j x :
  j ∉ is → foldr delete (<[j:=x]>m) is = <[j:=x]>(foldr delete m is).
Proof.
  induction is as [|?? IHis]; simpl; [done |]. rewrite elem_of_cons. intros.
  rewrite IHis, delete_insert_ne; intuition.
Qed.
Lemma map_disjoint_foldr_delete_l {A} (m1 m2 : M A) is :
  m1 ##ₘ m2 → foldr delete m1 is ##ₘ m2.
Proof. induction is; simpl; auto using map_disjoint_delete_l. Qed.
Lemma map_disjoint_foldr_delete_r {A} (m1 m2 : M A) is :
  m1 ##ₘ m2 → m1 ##ₘ foldr delete m2 is.
Proof. induction is; simpl; auto using map_disjoint_delete_r. Qed.
Lemma map_agree_foldr_delete_l {A} (m1 m2 : M A) is :
  map_agree m1 m2 → map_agree (foldr delete m1 is) m2.
Proof. induction is; simpl; auto using map_agree_delete_l. Qed.
Lemma map_agree_foldr_delete_r {A} (m1 m2 : M A) is :
  map_agree m1 m2 → map_agree m1 (foldr delete m2 is).
Proof. induction is; simpl; auto using map_agree_delete_r. Qed.
Lemma foldr_delete_union {A} (m1 m2 : M A) is :
  foldr delete (m1 ∪ m2) is = foldr delete m1 is ∪ foldr delete m2 is.
Proof. apply foldr_delete_union_with. Qed.

(** ** Properties on conversion to lists that depend on [∪] and [##ₘ] *)
Lemma list_to_map_app {A} (l1 l2 : list (K * A)):
  list_to_map (l1 ++ l2) =@{M A} list_to_map l1 ∪ list_to_map l2.
Proof.
  induction l1 as [|[??] ? IH]; simpl.
  { by rewrite (left_id _ _). }
  by rewrite IH, insert_union_l.
Qed.
Lemma map_disjoint_list_to_map_l {A} (m : M A) ixs :
  list_to_map ixs ##ₘ m ↔ Forall (λ ix, m !! ix.1 = None) ixs.
Proof.
  split.
  - induction ixs; simpl; rewrite ?map_disjoint_insert_l in *; intuition.
  - induction 1; simpl; [apply map_disjoint_empty_l|].
    rewrite map_disjoint_insert_l. auto.
Qed.
Lemma map_disjoint_list_to_map_r {A} (m : M A) ixs :
  m ##ₘ list_to_map ixs ↔ Forall (λ ix, m !! ix.1 = None) ixs.
Proof. by rewrite (symmetry_iff map_disjoint), map_disjoint_list_to_map_l. Qed.
Lemma map_disjoint_list_to_map_zip_l {A} (m : M A) is xs :
  length is = length xs →
  list_to_map (zip is xs) ##ₘ m ↔ Forall (λ i, m !! i = None) is.
Proof.
  intro. rewrite map_disjoint_list_to_map_l.
  rewrite <-(fst_zip is xs) at 2 by lia. by rewrite Forall_fmap.
Qed.
Lemma map_disjoint_list_to_map_zip_r {A} (m : M A) is xs :
  length is = length xs →
  m ##ₘ list_to_map (zip is xs) ↔ Forall (λ i, m !! i = None) is.
Proof.
  intro. by rewrite (symmetry_iff map_disjoint), map_disjoint_list_to_map_zip_l.
Qed.
Lemma map_disjoint_list_to_map_zip_l_2 {A} (m : M A) is xs :
  length is = length xs → Forall (λ i, m !! i = None) is →
  list_to_map (zip is xs) ##ₘ m.
Proof. intro. by rewrite map_disjoint_list_to_map_zip_l. Qed.
Lemma map_disjoint_list_to_map_zip_r_2 {A} (m : M A) is xs :
  length is = length xs → Forall (λ i, m !! i = None) is →
  m ##ₘ list_to_map (zip is xs).
Proof. intro. by rewrite map_disjoint_list_to_map_zip_r. Qed.

(** ** Properties of the [intersection_with] operation *)
Section intersection_with.
  Context {A} (f : A → A → option A).
  Implicit Type (m: M A).
  Global Instance : LeftAbsorb (=@{M A}) ∅ (intersection_with f).
  Proof. unfold intersection_with, map_intersection_with. apply _. Qed.
  Global Instance: RightAbsorb (=@{M A}) ∅ (intersection_with f).
  Proof. unfold intersection_with, map_intersection_with. apply _. Qed.
  Lemma lookup_intersection_with m1 m2 i :
    intersection_with f m1 m2 !! i = intersection_with f (m1 !! i) (m2 !! i).
  Proof.
    unfold intersection_with, map_intersection_with. rewrite lookup_merge.
    by destruct (m1 !! i), (m2 !! i).
  Qed.
  Lemma lookup_intersection_with_Some m1 m2 i z :
    intersection_with f m1 m2 !! i = Some z ↔
      (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
  Proof.
    rewrite lookup_intersection_with.
    destruct (m1 !! i), (m2 !! i); compute; naive_solver.
  Qed.
  Lemma intersection_with_comm m1 m2 :
    (∀ i x y, m1 !! i = Some x → m2 !! i = Some y → f x y = f y x) →
    intersection_with f m1 m2 = intersection_with f m2 m1.
  Proof.
    intros. apply (merge_comm _). intros i.
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
  Qed.
  Global Instance: Comm (=) f → Comm (=@{M A}) (intersection_with f).
  Proof. intros ???. apply intersection_with_comm. eauto. Qed.
  Lemma intersection_with_idemp m :
    (∀ i x, m !! i = Some x → f x x = Some x) → intersection_with f m m = m.
  Proof.
    intros. apply (merge_idemp _). intros i.
    destruct (m !! i) eqn:?; simpl; eauto.
  Qed.
  Lemma alter_intersection_with (g : A → A) m1 m2 i :
    (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) (g y)) →
    alter g i (intersection_with f m1 m2) =
      intersection_with f (alter g i m1) (alter g i m2).
  Proof.
    intros. apply (partial_alter_merge _).
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
  Qed.
  Lemma delete_intersection_with m1 m2 i :
    delete i (intersection_with f m1 m2) =
      intersection_with f (delete i m1) (delete i m2).
  Proof. by apply (partial_alter_merge _). Qed.
  Lemma foldr_delete_intersection_with (m1 m2 : M A) is :
    foldr delete (intersection_with f m1 m2) is =
      intersection_with f (foldr delete m1 is) (foldr delete m2 is).
  Proof.
    induction is as [|?? IHis]; simpl; [done|].
    by rewrite IHis, delete_intersection_with.
  Qed.
  Lemma insert_intersection_with m1 m2 i x y z :
    f x y = Some z →
    <[i:=z]>(intersection_with f m1 m2) =
      intersection_with f (<[i:=x]>m1) (<[i:=y]>m2).
  Proof. by intros; apply (partial_alter_merge _). Qed.
End intersection_with.

(** ** Properties of the [intersection] operation *)
Global Instance map_empty_interaction {A} : LeftAbsorb (=@{M A}) ∅ (∩) := _.
Global Instance map_interaction_empty {A} : RightAbsorb (=@{M A}) ∅ (∩) := _.
Global Instance map_interaction_assoc {A} : Assoc (=@{M A}) (∩).
Proof.
  intros m1 m2 m3.
  unfold intersection, map_intersection, intersection_with, map_intersection_with.
  apply (merge_assoc _). intros i.
  by destruct (m1 !! i), (m2 !! i), (m3 !! i).
Qed.
Global Instance map_intersection_idemp {A} : IdemP (=@{M A}) (∩).
Proof. intros ?. by apply intersection_with_idemp. Qed.

Lemma lookup_intersection {A} (m1 m2 : M A) i :
  (m1 ∩ m2) !! i = m1 !! i ∩ m2 !! i.
Proof.
  apply lookup_intersection_with.
Qed.
Lemma lookup_intersection_Some {A} (m1 m2 : M A) i x :
  (m1 ∩ m2) !! i = Some x ↔ m1 !! i = Some x ∧ is_Some (m2 !! i).
Proof.
  unfold intersection, map_intersection. rewrite lookup_intersection_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma lookup_intersection_None {A} (m1 m2 : M A) i :
  (m1 ∩ m2) !! i = None ↔ m1 !! i = None ∨ m2 !! i = None.
Proof.
  unfold intersection, map_intersection. rewrite lookup_intersection_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma map_intersection_filter {A} (m1 m2 : M A) :
  m1 ∩ m2 = filter (λ kx, is_Some (m1 !! kx.1) ∧ is_Some (m2 !! kx.1)) (m1 ∪ m2).
Proof.
  apply map_eq; intros i. apply option_eq; intros x.
  rewrite lookup_intersection_Some, map_lookup_filter_Some, lookup_union; simpl.
  unfold is_Some. destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_filter_and {A} (P Q : K * A → Prop)
    `{!∀ x, Decision (P x), !∀ x, Decision (Q x)} (m : M A) :
  filter (λ x, P x ∧ Q x) m = filter P m ∩ filter Q m.
Proof.
  apply map_eq. intros k. rewrite lookup_intersection. rewrite !map_lookup_filter.
  destruct (m !! k); simpl; repeat case_guard; naive_solver.
Qed.
Lemma map_fmap_intersection {A B} (f : A → B) (m1 m2 : M A) :
  f <$> (m1 ∩ m2) = (f <$> m1) ∩ (f <$> m2).
Proof.
  apply map_eq. intros i.
  rewrite !lookup_intersection, !lookup_fmap, !lookup_intersection.
  destruct (m1 !! i), (m2 !! i); done.
Qed.

(** ** Properties of the [difference_with] operation *)
Lemma lookup_difference_with {A} (f : A → A → option A) (m1 m2 : M A) i :
  difference_with f m1 m2 !! i = difference_with f (m1 !! i) (m2 !! i).
Proof.
  unfold difference_with, map_difference_with. rewrite lookup_merge.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma lookup_difference_with_Some {A} (f : A → A → option A) (m1 m2 : M A) i z :
  difference_with f m1 m2 !! i = Some z ↔
    (m1 !! i = Some z ∧ m2 !! i = None) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
Proof.
  rewrite lookup_difference_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.

(** ** Properties of the [difference] operation *)
Lemma lookup_difference {A} (m1 m2 : M A) i :
  (m1 ∖ m2) !! i = match m2 !! i with None => m1 !! i | _ => None end.
Proof.
  unfold difference, map_difference; rewrite lookup_difference_with.
  destruct (m1 !! i), (m2 !! i); done.
Qed.
Lemma lookup_difference_Some {A} (m1 m2 : M A) i x :
  (m1 ∖ m2) !! i = Some x ↔ m1 !! i = Some x ∧ m2 !! i = None.
Proof. rewrite lookup_difference. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.
Lemma lookup_difference_is_Some {A} (m1 m2 : M A) i :
  is_Some ((m1 ∖ m2) !! i) ↔ is_Some (m1 !! i) ∧ m2 !! i = None.
Proof. unfold is_Some. setoid_rewrite lookup_difference_Some. naive_solver. Qed.
Lemma lookup_difference_None {A} (m1 m2 : M A) i :
  (m1 ∖ m2) !! i = None ↔ m1 !! i = None ∨ is_Some (m2 !! i).
Proof.
  rewrite lookup_difference.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma map_disjoint_difference_l {A} (m1 m2 : M A) : m1 ⊆ m2 → m2 ∖ m1 ##ₘ m1.
Proof.
  intros Hm i; specialize (Hm i).
  unfold difference, map_difference; rewrite lookup_difference_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.
Lemma map_disjoint_difference_r {A} (m1 m2 : M A) : m1 ⊆ m2 → m1 ##ₘ m2 ∖ m1.
Proof. intros. symmetry. by apply map_disjoint_difference_l. Qed.
Lemma map_subseteq_difference_l {A} (m1 m2 m : M A) : m1 ⊆ m → m1 ∖ m2 ⊆ m.
Proof.
  rewrite !map_subseteq_spec. setoid_rewrite lookup_difference_Some. naive_solver.
Qed.
Lemma map_difference_union {A} (m1 m2 : M A) :
  m1 ⊆ m2 → m1 ∪ m2 ∖ m1 = m2.
Proof.
  rewrite map_subseteq_spec. intro Hm1m2. apply map_eq. intros i.
  apply option_eq. intros v. specialize (Hm1m2 i).
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite lookup_union_Some_raw, lookup_merge.
  destruct (m1 !! i) as [x'|], (m2 !! i);
    try specialize (Hm1m2 x'); compute; intuition congruence.
Qed.
Lemma map_difference_diag {A} (m : M A) : m ∖ m = ∅.
Proof.
  apply map_empty; intros i. rewrite lookup_difference_None.
  destruct (m !! i); eauto.
Qed.
Global Instance map_difference_right_id {A} : RightId (=@{M A}) ∅ (∖) := _.
Lemma map_difference_empty {A} (m : M A) : m ∖ ∅ = m.
Proof. by rewrite (right_id _ _). Qed.
Lemma map_fmap_difference {A B} (f : A → B) (m1 m2 : M A) :
  f <$> (m1 ∖ m2) = (f <$> m1) ∖ (f <$> m2).
Proof.
  apply map_eq. intros i.
  rewrite !lookup_difference, !lookup_fmap, !lookup_difference.
  destruct (m1 !! i), (m2 !! i); done.
Qed.

Lemma insert_difference {A} (m1 m2 : M A) i x :
  <[i:=x]> (m1 ∖ m2) = <[i:=x]> m1 ∖ delete i m2.
Proof.
  intros. apply map_eq. intros j. apply option_eq. intros y.
  rewrite lookup_insert_Some, !lookup_difference_Some,
    lookup_insert_Some, lookup_delete_None.
  naive_solver.
Qed.
Lemma insert_difference' {A} (m1 m2 : M A) i x :
  m2 !! i = None → <[i:=x]> (m1 ∖ m2) = <[i:=x]> m1 ∖ m2.
Proof. intros. by rewrite insert_difference, delete_notin. Qed.

Lemma difference_insert {A} (m1 m2 : M A) i x1 x2 x3 :
  <[i:=x1]> m1 ∖ <[i:=x2]> m2 = m1 ∖ <[i:=x3]> m2.
Proof.
  apply map_eq. intros i'. apply option_eq. intros x'.
  rewrite !lookup_difference_Some, !lookup_insert_Some, !lookup_insert_None.
  naive_solver.
Qed.
Lemma difference_insert_subseteq {A} (m1 m2 : M A) i x1 x2 :
  <[i:=x1]> m1 ∖ <[i:=x2]> m2 ⊆ m1 ∖ m2.
Proof.
  apply map_subseteq_spec. intros i' x'.
  rewrite !lookup_difference_Some, lookup_insert_Some, lookup_insert_None.
  naive_solver.
Qed.

Lemma delete_difference {A} (m1 m2 : M A) i x :
  delete i (m1 ∖ m2) = m1 ∖ <[i:=x]> m2.
Proof.
  apply map_eq. intros j. apply option_eq. intros y.
  rewrite lookup_delete_Some, !lookup_difference_Some, lookup_insert_None.
  naive_solver.
Qed.
Lemma difference_delete {A} (m1 m2 : M A) i x :
  m1 !! i = Some x →
  m1 ∖ delete i m2 = <[i:=x]> (m1 ∖ m2).
Proof.
  intros. apply map_eq. intros j. apply option_eq. intros y.
  rewrite lookup_insert_Some, !lookup_difference_Some, lookup_delete_None.
  destruct (decide (i = j)); naive_solver.
Qed.

Lemma map_difference_filter {A} (m1 m2 : M A) :
  m1 ∖ m2 = filter (λ kx, m2 !! kx.1 = None) m1.
Proof.
  apply map_eq; intros i. apply option_eq; intros x.
  by rewrite lookup_difference_Some, map_lookup_filter_Some.
Qed.

(** ** Misc properties about the order *)
Lemma map_subseteq_inv {A} (m1 m2 : M A) : m1 ⊆ m2 → m1 ⊂ m2 ∨ m1 = m2.
Proof.
  intros. destruct (decide (m2 ∖ m1 = ∅)) as [Hm21|(i&x&Hi)%map_choose].
  - right. by rewrite <-(map_difference_union m1 m2), Hm21, (right_id_L _ _).
  - left. apply lookup_difference_Some in Hi as [??].
    apply map_subset_alt; eauto.
Qed.

(** ** Setoids *)
Section setoid.
  Context `{Equiv A}.

  Lemma map_equiv_iff (m1 m2 : M A) : m1 ≡ m2 ↔ ∀ i, m1 !! i ≡ m2 !! i.
  Proof. done. Qed.

  Lemma map_equiv_lookup_l (m1 m2 : M A) i x :
    m1 ≡ m2 → m1 !! i = Some x → ∃ y, m2 !! i = Some y ∧ x ≡ y.
  Proof. intros Hm Hi. destruct (Hm i); naive_solver. Qed.
  Lemma map_equiv_lookup_r (m1 m2 : M A) i y :
    m1 ≡ m2 → m2 !! i = Some y → ∃ x, m1 !! i = Some x ∧ x ≡ y.
  Proof. intros Hm Hi. destruct (Hm i); naive_solver. Qed.

  Global Instance map_equivalence : Equivalence (≡@{A}) → Equivalence (≡@{M A}).
  Proof.
    split.
    - by intros m i.
    - by intros m1 m2 ? i.
    - by intros m1 m2 m3 ?? i; trans (m2 !! i).
  Qed.
  Global Instance map_leibniz `{!LeibnizEquiv A} : LeibnizEquiv (M A).
  Proof. intros m1 m2 Hm; apply map_eq; intros i. apply leibniz_equiv, Hm. Qed.

  Global Instance lookup_proper (i : K) : Proper ((≡@{M A}) ==> (≡)) (lookup i).
  Proof. by intros m1 m2 Hm. Qed.
  Global Instance lookup_total_proper (i : K) `{!Inhabited A} :
    Proper (≡@{A}) inhabitant →
    Proper ((≡@{M A}) ==> (≡)) (.!!! i).
  Proof.
    intros ? m1 m2 Hm. unfold lookup_total, map_lookup_total.
    apply from_option_proper; auto. by intros ??.
  Qed.
  Global Instance partial_alter_proper :
    Proper (((≡) ==> (≡)) ==> (=) ==> (≡) ==> (≡@{M A})) partial_alter.
  Proof.
    by intros f1 f2 Hf i ? <- m1 m2 Hm j; destruct (decide (i = j)) as [->|];
      rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne by done;
      try apply Hf; apply lookup_proper.
  Qed.
  Global Instance insert_proper (i : K) :
    Proper ((≡) ==> (≡) ==> (≡@{M A})) (insert i).
  Proof. by intros ???; apply partial_alter_proper; [constructor|]. Qed.
  Global Instance singletonM_proper k : Proper ((≡) ==> (≡@{M A})) (singletonM k).
  Proof.
    intros ???; apply insert_proper; [done|].
    intros ?. rewrite lookup_empty; constructor.
  Qed.
  Global Instance delete_proper (i : K) : Proper ((≡) ==> (≡@{M A})) (delete i).
  Proof. by apply partial_alter_proper; [constructor|]. Qed.
  Global Instance alter_proper :
    Proper (((≡) ==> (≡)) ==> (=) ==> (≡) ==> (≡@{M A})) alter.
  Proof.
    intros ?? Hf; apply partial_alter_proper.
    by destruct 1; constructor; apply Hf.
  Qed.
  Global Instance merge_proper `{Equiv B, Equiv C} :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡@{M A}) ==> (≡@{M B}) ==> (≡@{M C})) merge.
  Proof.
    intros ?? Hf ?? Hm1 ?? Hm2 i. rewrite !lookup_merge.
    destruct (Hm1 i), (Hm2 i); try apply Hf; by constructor.
  Qed.

  Global Instance union_with_proper :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡) ==> (≡) ==>(≡@{M A})) union_with.
  Proof.
    intros ?? Hf. apply merge_proper.
    by do 2 destruct 1; first [apply Hf | constructor].
  Qed.
  Global Instance intersection_with_proper :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡) ==> (≡) ==>(≡@{M A})) intersection_with.
  Proof.
    intros ?? Hf. apply merge_proper.
    by do 2 destruct 1; first [apply Hf | constructor].
  Qed.
  Global Instance difference_with_proper :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡) ==> (≡) ==>(≡@{M A})) difference_with.
  Proof.
    intros ?? Hf. apply merge_proper.
    by do 2 destruct 1; first [apply Hf | constructor].
  Qed.
  Global Instance union_proper : Proper ((≡) ==> (≡) ==>(≡@{M A})) union.
  Proof. apply union_with_proper; solve_proper. Qed.
  Global Instance intersection_proper : Proper ((≡) ==> (≡) ==>(≡@{M A})) intersection.
  Proof. apply intersection_with_proper; solve_proper. Qed.
  Global Instance difference_proper : Proper ((≡) ==> (≡) ==>(≡@{M A})) difference.
  Proof. apply difference_with_proper. constructor. Qed.

  Global Instance map_zip_with_proper `{Equiv B, Equiv C} :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡@{M A}) ==> (≡@{M B}) ==> (≡@{M C}))
      map_zip_with.
  Proof.
    intros f1 f2 Hf. apply merge_proper.
    destruct 1; destruct 1; repeat f_equiv; constructor || by apply Hf.
  Qed.

  Global Instance map_disjoint_proper :
    Proper ((≡@{M A}) ==> (≡@{M A}) ==> iff) map_disjoint.
  Proof.
    intros m1 m1' Hm1 m2 m2' Hm2; split;
      intros Hm i; specialize (Hm i); by destruct (Hm1 i), (Hm2 i).
  Qed.
  Global Instance map_fmap_proper `{Equiv B} :
    Proper (((≡) ==> (≡)) ==> (≡@{M A}) ==> (≡@{M B})) fmap.
  Proof.
    intros f f' Hf m m' ? k; rewrite !lookup_fmap. by apply option_fmap_proper.
  Qed.
  Global Instance map_omap_proper `{Equiv B} :
    Proper (((≡) ==> (≡)) ==> (≡@{M A}) ==> (≡@{M B})) omap.
  Proof.
    intros f f' ? m m' ? k; rewrite !lookup_omap. by apply option_bind_proper.
  Qed.

  Global Instance map_filter_proper (P : K * A → Prop) `{!∀ kx, Decision (P kx)} :
    (∀ k, Proper ((≡) ==> iff) (curry P k)) →
    Proper ((≡@{M A}) ==> (≡)) (filter P).
  Proof.
    intros ? m1 m2 Hm i. rewrite !map_lookup_filter.
    destruct (Hm i); simpl; repeat case_guard; try constructor; naive_solver.
  Qed.

  Global Instance map_singleton_equiv_inj :
    Inj2 (=) (≡) (≡) (singletonM (M:=M A)).
  Proof.
    intros i1 x1 i2 x2 Heq. specialize (Heq i1).
    rewrite lookup_singleton in Heq. destruct (decide (i1 = i2)) as [->|].
    - rewrite lookup_singleton in Heq. apply (inj _) in Heq. naive_solver.
    - rewrite lookup_singleton_ne in Heq by done. inv Heq.
  Qed.

  Global Instance map_fmap_equiv_inj `{Equiv B} (f : A → B) :
    Inj (≡) (≡) f → Inj (≡@{M A}) (≡@{M B}) (fmap f).
  Proof.
    intros ? m1 m2 Hm i. apply (inj (fmap (M:=option) f)).
    rewrite <-!lookup_fmap. by apply Hm.
  Qed.

  Lemma map_fmap_equiv_ext `{Equiv B} (f1 f2 : A → B) (m : M A) :
    (∀ i x, m !! i = Some x → f1 x ≡ f2 x) → f1 <$> m ≡ f2 <$> m.
  Proof.
    intros Hi i; rewrite !lookup_fmap.
    destruct (m !! i) eqn:?; constructor; eauto.
  Qed.
End setoid.

(** The lemmas below make it possible to turn an [≡] into an [=]. *)
Section setoid_inversion.
  Context `{Equiv A, !Equivalence (≡@{A})}.
  Implicit Types m : M A.

  Lemma map_empty_equiv_eq m : m ≡ ∅ ↔ m = ∅.
  Proof.
    split; [intros Hm; apply map_eq; intros i|intros ->].
    - generalize (Hm i). by rewrite lookup_empty, None_equiv_eq.
    - intros ?. rewrite lookup_empty; constructor.
  Qed.

  Lemma partial_alter_equiv_eq (f : option A → option A) (m1 m2 : M A) i :
    Proper ((≡) ==> (≡)) f →
    (∀ x1 mx2, Some x1 ≡ f mx2 → ∃ mx2', Some x1 = f mx2' ∧ mx2' ≡ mx2) →
    m1 ≡ partial_alter f i m2 ↔ ∃ m2', m1 = partial_alter f i m2' ∧ m2' ≡ m2.
  Proof.
    intros ? Hf. split; [|by intros (?&->&<-)]. intros Hm.
    assert (∃ mx2', m1 !! i = f mx2' ∧ mx2' ≡ m2 !! i) as (mx2'&?&?).
    { destruct (m1 !! i) as [x1|] eqn:Hix1.
      - apply (Hf x1 (m2 !! i)). by rewrite <-Hix1, Hm, lookup_partial_alter.
      - exists (m2 !! i). split; [|done]. apply symmetry, None_equiv_eq.
        by rewrite <-Hix1, Hm, lookup_partial_alter. }
    exists (partial_alter (λ _, mx2') i m1). split.
    - apply map_eq; intros j. destruct (decide (i = j)) as [->|?].
      + by rewrite !lookup_partial_alter.
      + by rewrite !lookup_partial_alter_ne.
    - intros j. destruct (decide (i = j)) as [->|?].
      + by rewrite lookup_partial_alter.
      + by rewrite Hm, !lookup_partial_alter_ne.
  Qed.
  Lemma alter_equiv_eq (f : A → A) (m1 m2 : M A) i :
    Proper ((≡) ==> (≡)) f →
    (∀ x1 x2, x1 ≡ f x2 → ∃ x2', x1 = f x2' ∧ x2' ≡ x2) →
    m1 ≡ alter f i m2 ↔ ∃ m2', m1 = alter f i m2' ∧ m2' ≡ m2.
  Proof.
    intros ? Hf. apply (partial_alter_equiv_eq _ _ _ _ _). intros mx1 [x2|]; simpl.
    - intros (x2'&->&?)%(inj _)%Hf. exists (Some x2'). by repeat constructor.
    - intros ->%None_equiv_eq. by exists None.
  Qed.

  Lemma delete_equiv_eq m1 m2 i :
    m1 ≡ delete i m2 ↔ ∃ m2', m1 = delete i m2' ∧ m2' ≡ m2.
  Proof. apply (partial_alter_equiv_eq _ _ _ _ _). intros ?? [=]%None_equiv_eq. Qed.
  Lemma insert_equiv_eq m1 m2 i x :
    m1 ≡ <[i:=x]> m2 ↔ ∃ x' m2', m1 = <[i:=x']> m2' ∧ x' ≡ x ∧ m2' ≡ m2.
  Proof.
    split; [|by intros (?&?&->&<-&<-)]. intros Hm.
    assert (is_Some (m1 !! i)) as [x' Hix'].
    { rewrite Hm, lookup_insert. eauto. }
    destruct (m2 !! i) as [y|] eqn:?.
    - exists x', (<[i:=y]> m1). split_and!.
      + by rewrite insert_insert, insert_id by done.
      + apply (inj Some). by rewrite <-Hix', Hm, lookup_insert.
      + by rewrite Hm, insert_insert, insert_id by done.
    - exists x', (delete i m1). split_and!.
      + by rewrite insert_delete by done.
      + apply (inj Some). by rewrite <-Hix', Hm, lookup_insert.
      + by rewrite Hm, delete_insert by done.
  Qed.
  Lemma map_singleton_equiv_eq m i x :
    m ≡ {[i:=x]} ↔ ∃ x', m = {[i:=x']} ∧ x' ≡ x.
  Proof.
    rewrite <-!insert_empty, insert_equiv_eq.
    setoid_rewrite map_empty_equiv_eq. naive_solver.
  Qed.

  Lemma map_filter_equiv_eq (P : K * A → Prop) `{!∀ kx, Decision (P kx)} (m1 m2 : M A):
    (∀ k, Proper ((≡) ==> iff) (curry P k)) →
    m1 ≡ filter P m2 ↔ ∃ m2', m1 = filter P m2' ∧ m2' ≡ m2.
  Proof.
    intros HP. split; [|by intros (?&->&->)].
    revert m1. induction m2 as [|i x m2 ? IH] using map_ind; intros m1 Hm.
    { rewrite map_filter_empty in Hm. exists ∅.
      by rewrite map_filter_empty, <-map_empty_equiv_eq. }
    rewrite map_filter_insert in Hm. case_decide.
    - apply insert_equiv_eq in Hm as (x'&m2'&->&?&(m2''&->&?)%IH).
      exists (<[i:=x']> m2''). split; [|by f_equiv].
      by rewrite map_filter_insert_True by (by eapply HP).
    - rewrite delete_notin in Hm by done.
      apply IH in Hm as (m2'&->&Hm2). exists (<[i:=x]> m2'). split; [|by f_equiv].
      assert (m2' !! i = None).
      { by rewrite <-None_equiv_eq, Hm2, None_equiv_eq. }
      by rewrite map_filter_insert_not' by naive_solver.
  Qed.
End setoid_inversion.

Lemma map_omap_equiv_eq `{Equiv A, !Equivalence (≡@{A}),
      Equiv B, !Equivalence (≡@{B})}
    (f : A → option B) (m1 : M B) (m2 : M A) :
  Proper ((≡) ==> (≡)) f →
  (∀ y x, Some y ≡ f x → ∃ x', Some y = f x' ∧ x' ≡ x) →
  m1 ≡ omap f m2 ↔ ∃ m2', m1 = omap f m2' ∧ m2' ≡ m2.
Proof.
  intros ? Hf. split; [|by intros (?&->&->)].
  revert m1. induction m2 as [|i x m2 ? IH] using map_ind; intros m1 Hm.
  { rewrite omap_empty, map_empty_equiv_eq in Hm. subst m1.
    exists ∅. by rewrite omap_empty. }
  rewrite omap_insert in Hm. destruct (f x) as [y|] eqn:Hfx.
  - apply insert_equiv_eq in Hm as (y'&m1'&->&Hy&(m2'&->&?)%IH).
    destruct (Hf y' x) as (x'&Hfx'&?).
    { by rewrite Hfx, Hy. }
    exists (<[i:=x']> m2'). split; [|by f_equiv].
    by rewrite omap_insert, <-Hfx'.
  - apply delete_equiv_eq in Hm as (m1'&->&(m2'&->&?)%IH).
    exists (<[i:=x]> m2'). split; [|by f_equiv]. by rewrite omap_insert, Hfx.
Qed.
Lemma map_fmap_equiv_eq `{Equiv A, !Equivalence (≡@{A}),
      Equiv B, !Equivalence (≡@{B})} (f : A → B) (m1 : M B) (m2 : M A) :
  Proper ((≡) ==> (≡)) f →
  (∀ y x, y ≡ f x → ∃ x', y = f x' ∧ x' ≡ x) →
  m1 ≡ f <$> m2 ↔ ∃ m2', m1 = f <$> m2' ∧ m2' ≡ m2.
Proof.
  intros ? Hf. rewrite map_fmap_alt; setoid_rewrite map_fmap_alt.
  apply map_omap_equiv_eq; [solve_proper|].
  intros ?? (?&->&?)%(inj _)%Hf; eauto.
Qed.

Lemma merge_equiv_eq `{Equiv A, !Equivalence (≡@{A}),
    Equiv B, !Equivalence (≡@{B}), Equiv C, !Equivalence (≡@{C})}
    (f : option A → option B → option C) (m1 : M C) (m2a : M A) (m2b : M B) :
  Proper ((≡) ==> (≡) ==> (≡)) f →
  (∀ y mx1 mx2,
    Some y ≡ f mx1 mx2 →
    ∃ mx1' mx2', Some y = f mx1' mx2' ∧ mx1' ≡ mx1 ∧ mx2' ≡ mx2) →
  m1 ≡ merge f m2a m2b ↔
    ∃ m2a' m2b', m1 = merge f m2a' m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b.
Proof.
  intros ? Hf. split; [|by intros (?&?&->&->&->)].
  revert m1. induction m2a as [|i x m2a ? IH] using map_ind; intros m1.
  { assert (∀ y x,
      Some y ≡ f None (Some x) → ∃ x', Some y = f None (Some x') ∧ x' ≡ x).
    { intros ?? (?&?&?&->%None_equiv_eq&(?&->&?)%Some_equiv_eq)%Hf; eauto. }
    rewrite merge_empty_l, map_omap_equiv_eq by (done || solve_proper).
    intros (m2'&->&?). exists ∅, m2'. by rewrite merge_empty_l. }
  unfold insert at 1, map_insert at 1.
  rewrite <-(partial_alter_merge_l _ (λ _, f (Some x) (m2b !! i))) by done.
  destruct (f (Some x) (m2b !! i)) as [y|] eqn:Hfi.
  - intros (y'&m'&->&Hy&(m2a'&m2b'&->&Hm2a&Hm2b)%IH)%insert_equiv_eq.
    destruct (Hf y' (Some x) (m2b !! i)) as (mx1&mx2&?&(x'&->&?)%Some_equiv_eq&?).
    { by rewrite Hy, Hfi. }
    exists (<[i:=x']> m2a'), (partial_alter (λ _, mx2) i m2b').
    split_and!; [by apply partial_alter_merge|by f_equiv|].
    intros j. destruct (decide (i = j)) as [->|?].
    + by rewrite lookup_partial_alter.
    + by rewrite Hm2b, lookup_partial_alter_ne.
  - intros (m'&->&(m2a'&m2b'&->&Hm2a&Hm2b)%IH)%delete_equiv_eq.
    exists (<[i:=x]> m2a'), m2b'. split_and!; [|by f_equiv|done].
    apply partial_alter_merge_l, symmetry, None_equiv_eq; simpl.
    by rewrite Hm2b, Hfi.
Qed.

Lemma map_union_with_equiv_eq `{Equiv A, !Equivalence (≡@{A})}
    (f : A → A → option A) (m1 m2a m2b : M A) :
  Proper ((≡) ==> (≡) ==> (≡)) f →
  (∀ y x1 x2,
    Some y ≡ f x1 x2 → ∃ x1' x2', Some y = f x1' x2' ∧ x1' ≡ x1 ∧ x2' ≡ x2) →
  m1 ≡ union_with f m2a m2b ↔
    ∃ m2a' m2b', m1 = union_with f m2a' m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b.
Proof.
  intros ? Hf. apply (merge_equiv_eq _ _ _ _ _).
  intros ? [x1|] [x2|]; simpl;
    first [intros (?&?&?&?&?)%Hf|intros (?&?&?)%Some_equiv_eq|intros ?%None_equiv_eq];
    by repeat econstructor.
Qed.
Lemma map_intersection_with_equiv_eq `{Equiv A, !Equivalence (≡@{A})}
    (f : A → A → option A) (m1 m2a m2b : M A) :
  Proper ((≡) ==> (≡) ==> (≡)) f →
  (∀ y x1 x2,
    Some y ≡ f x1 x2 → ∃ x1' x2', Some y = f x1' x2' ∧ x1' ≡ x1 ∧ x2' ≡ x2) →
  m1 ≡ intersection_with f m2a m2b ↔
    ∃ m2a' m2b', m1 = intersection_with f m2a' m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b.
Proof.
  intros ? Hf. apply (merge_equiv_eq _ _ _ _ _).
  intros ? [x1|] [x2|]; simpl;
    first [intros (?&?&?&?&?)%Hf|intros (?&?&?)%Some_equiv_eq|intros ?%None_equiv_eq];
    by repeat econstructor.
Qed.
Lemma map_difference_with_equiv_eq `{Equiv A, !Equivalence (≡@{A})}
    (f : A → A → option A) (m1 m2a m2b : M A) :
  Proper ((≡) ==> (≡) ==> (≡)) f →
  (∀ y x1 x2,
    Some y ≡ f x1 x2 → ∃ x1' x2', Some y = f x1' x2' ∧ x1' ≡ x1 ∧ x2' ≡ x2) →
  m1 ≡ difference_with f m2a m2b ↔
    ∃ m2a' m2b', m1 = difference_with f m2a' m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b.
Proof.
  intros ? Hf. apply (merge_equiv_eq _ _ _ _ _).
  intros ? [x1|] [x2|]; simpl;
    first [intros (?&?&?&?&?)%Hf|intros (?&?&?)%Some_equiv_eq|intros ?%None_equiv_eq];
    by repeat econstructor.
Qed.

Lemma map_union_equiv_eq `{Equiv A, !Equivalence (≡@{A})} (m1 m2a m2b : M A) :
  m1 ≡ m2a ∪ m2b ↔ ∃ m2a' m2b', m1 = m2a' ∪ m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b.
Proof.
  apply map_union_with_equiv_eq; [solve_proper|]. intros ??? ?%(inj _); eauto.
Qed.
Lemma map_intersection_equiv_eq `{Equiv A, !Equivalence (≡@{A})} (m1 m2a m2b : M A) :
  m1 ≡ m2a ∩ m2b ↔ ∃ m2a' m2b', m1 = m2a' ∩ m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b.
Proof.
  apply map_intersection_with_equiv_eq; [solve_proper|]. intros ??? ?%(inj _); eauto.
Qed.
Lemma map_difference_equiv_eq `{Equiv A, !Equivalence (≡@{A})} (m1 m2a m2b : M A) :
  m1 ≡ m2a ∖ m2b ↔ ∃ m2a' m2b', m1 = m2a' ∖ m2b' ∧ m2a' ≡ m2a ∧ m2b' ≡ m2b.
Proof.
  apply map_difference_with_equiv_eq; [constructor|]. intros ??? [=]%None_equiv_eq.
Qed.
End theorems.

(** ** The [map_seq] operation *)
Section map_seq.
  Context `{FinMap nat M} {A : Type}.
  Implicit Types x : A.
  Implicit Types xs : list A.

  Global Instance map_seq_proper `{Equiv A} start :
    Proper ((≡@{list A}) ==> (≡@{M A})) (map_seq start).
  Proof.
    intros l1 l2 Hl. revert start.
    induction Hl as [|x1 x2 l1 l2 ?? IH]; intros start; simpl.
    - intros ?. rewrite lookup_empty; constructor.
    - repeat (done || f_equiv).
  Qed.

  Lemma lookup_map_seq start xs i :
    map_seq (M:=M A) start xs !! i = (guard (start ≤ i);; xs !! (i - start)).
  Proof.
    revert start. induction xs as [|x' xs IH]; intros start; simpl.
    { rewrite lookup_empty; simplify_option_eq; by rewrite ?lookup_nil. }
    destruct (decide (start = i)) as [->|?].
    - by rewrite lookup_insert, option_guard_True, Nat.sub_diag by lia.
    - rewrite lookup_insert_ne, IH by done.
      simplify_option_eq; try done || lia.
      by replace (i - start) with (S (i - S start)) by lia.
  Qed.
  Lemma lookup_map_seq_0 xs i : map_seq (M:=M A) 0 xs !! i = xs !! i.
  Proof. by rewrite lookup_map_seq, option_guard_True, Nat.sub_0_r by lia. Qed.

  Lemma lookup_map_seq_Some_inv start xs i x :
    xs !! i = Some x ↔ map_seq (M:=M A) start xs !! (start + i) = Some x.
  Proof.
    rewrite lookup_map_seq, option_guard_True by lia.
    by rewrite Nat.add_sub_swap, Nat.sub_diag.
  Qed.
  Lemma lookup_map_seq_Some start xs i x :
    map_seq (M:=M A) start xs !! i = Some x ↔ start ≤ i ∧ xs !! (i - start) = Some x.
  Proof. rewrite lookup_map_seq. case_guard; naive_solver. Qed.
  Lemma lookup_map_seq_None start xs i :
    map_seq (M:=M A) start xs !! i = None ↔ i < start ∨ start + length xs ≤ i.
  Proof.
    rewrite lookup_map_seq.
    case_guard; simplify_option_eq; rewrite ?lookup_ge_None; naive_solver lia.
  Qed.
  Lemma lookup_map_seq_is_Some start xs i x :
    is_Some (map_seq (M:=M A) start xs !! i) ↔ start ≤ i < start + length xs.
  Proof. rewrite <-not_eq_None_Some, lookup_map_seq_None. lia. Qed.

  Lemma map_seq_singleton start x :
    map_seq (M:=M A) start [x] = {[ start := x ]}.
  Proof. done. Qed.

  (** [map_seq_disjoint] uses [length xs = 0] instead of [xs = []] as
  [lia] can handle the former but not the latter. *)
  Lemma map_seq_disjoint start1 start2 xs1 xs2 :
    map_seq (M:=M A) start1 xs1 ##ₘ map_seq start2 xs2 ↔
      start1 + length xs1 ≤ start2 ∨ start2 + length xs2 ≤ start1
      ∨ length xs1 = 0 ∨ length xs2 = 0.
  Proof.
    rewrite map_disjoint_alt. setoid_rewrite lookup_map_seq_None.
    split; intros Hi; [|lia]. pose proof (Hi start1). pose proof (Hi start2). lia.
  Qed.
  Lemma map_seq_app_disjoint start xs1 xs2 :
    map_seq (M:=M A) start xs1 ##ₘ map_seq (start + length xs1) xs2.
  Proof. apply map_seq_disjoint. lia. Qed.
  Lemma map_seq_app start xs1 xs2 :
    map_seq start (xs1 ++ xs2)
    =@{M A} map_seq start xs1 ∪ map_seq (start + length xs1) xs2.
  Proof.
    revert start. induction xs1 as [|x1 xs1 IH]; intros start; simpl.
    - by rewrite (left_id_L _ _), Nat.add_0_r.
    - by rewrite IH, Nat.add_succ_r, !insert_union_singleton_l, (assoc_L _).
  Qed.

  Lemma map_seq_cons_disjoint start xs :
    map_seq (M:=M A) (S start) xs !! start = None.
  Proof. rewrite lookup_map_seq_None. lia. Qed.
  Lemma map_seq_cons start xs x :
    map_seq start (x :: xs) =@{M A} <[start:=x]> (map_seq (S start) xs).
  Proof. done. Qed.

  Lemma map_seq_snoc_disjoint start xs :
    map_seq (M:=M A) start xs !! (start+length xs) = None.
  Proof. rewrite lookup_map_seq_None. lia. Qed.
  Lemma map_seq_snoc start xs x :
    map_seq start (xs ++ [x]) =@{M A} <[start+length xs:=x]> (map_seq start xs).
  Proof.
    rewrite map_seq_app, map_seq_singleton.
    by rewrite insert_union_singleton_r by (by rewrite map_seq_snoc_disjoint).
  Qed.

  Lemma fmap_map_seq {B} (f : A → B) start xs :
    f <$> map_seq start xs =@{M B} map_seq start (f <$> xs).
  Proof.
    revert start. induction xs as [|x xs IH]; intros start; csimpl.
    { by rewrite fmap_empty. }
    by rewrite fmap_insert, IH.
  Qed.

  Lemma insert_map_seq start xs i x:
    start ≤ i < start + length xs →
    <[i:=x]> (map_seq start xs) =@{M A} map_seq start (<[i - start:=x]> xs).
  Proof.
    intros. apply map_eq. intros j. destruct (decide (i = j)) as [->|?].
    - rewrite lookup_insert, lookup_map_seq, option_guard_True by lia.
      by rewrite list_lookup_insert by lia.
    - rewrite lookup_insert_ne, !lookup_map_seq by done.
      case_guard; [|done]. by rewrite list_lookup_insert_ne by lia.
  Qed.
  Lemma map_seq_insert start xs i x:
    i < length xs →
    map_seq start (<[i:=x]> xs) =@{M A} <[start + i:=x]> (map_seq start xs).
  Proof. intros. rewrite insert_map_seq by lia. auto with f_equal lia. Qed.

  Lemma insert_map_seq_0 xs i x:
    i < length xs →
    <[i:=x]> (map_seq 0 xs) =@{M A} map_seq 0 (<[i:=x]> xs).
  Proof. intros. rewrite insert_map_seq by lia. auto with f_equal lia. Qed.
End map_seq.

(** ** The [map_seqZ] operation *)
Section map_seqZ.
  Context `{FinMap Z M} {A : Type}.
  Implicit Types x : A.
  Implicit Types xs : list A.
  Local Open Scope Z_scope.

  Global Instance map_seqZ_proper `{Equiv A} start :
    Proper ((≡@{list A}) ==> (≡@{M A})) (map_seqZ start).
  Proof.
    intros l1 l2 Hl. revert start.
    induction Hl as [|x1 x2 l1 l2 ?? IH]; intros start; simpl.
    - intros ?. rewrite lookup_empty; constructor.
    - repeat (done || f_equiv).
  Qed.

  Lemma lookup_map_seqZ start xs i :
    map_seqZ (M:=M A) start xs !! i = (guard (start ≤ i);; xs !! Z.to_nat (i - start)).
  Proof.
    revert start. induction xs as [|x' xs IH]; intros start; simpl.
    { rewrite lookup_empty; simplify_option_eq; by rewrite ?lookup_nil. }
    destruct (decide (start = i)) as [->|?].
    - by rewrite lookup_insert, option_guard_True, Z.sub_diag by lia.
    - rewrite lookup_insert_ne, IH by done.
      simplify_option_eq; try done || lia.
      replace (i - start) with (Z.succ (i - Z.succ start)) by lia.
      by rewrite Z2Nat.inj_succ; [|lia].
  Qed.
  Lemma lookup_map_seqZ_0 xs i :
    0 ≤ i →
    map_seqZ (M:=M A) 0 xs !! i = xs !! Z.to_nat i.
  Proof. intros ?. by rewrite lookup_map_seqZ, option_guard_True, Z.sub_0_r. Qed.

  Lemma lookup_map_seqZ_Some_inv start xs i x :
    xs !! i = Some x ↔ map_seqZ (M:=M A) start xs !! (start + Z.of_nat i) = Some x.
  Proof.
    rewrite ->lookup_map_seqZ, option_guard_True by lia.
    assert (Z.to_nat (start + Z.of_nat i - start) = i) as -> by lia.
    done.
  Qed.
  Lemma lookup_map_seqZ_Some start xs i x :
    map_seqZ (M:=M A) start xs !! i = Some x ↔
      start ≤ i ∧ xs !! Z.to_nat (i - start) = Some x.
  Proof. rewrite lookup_map_seqZ. case_guard; naive_solver. Qed.
  Lemma lookup_map_seqZ_None start xs i :
    map_seqZ (M:=M A) start xs !! i = None ↔
      i < start ∨ start + Z.of_nat (length xs) ≤ i.
  Proof.
    rewrite lookup_map_seqZ.
    case_guard; simplify_option_eq; rewrite ?lookup_ge_None; naive_solver lia.
  Qed.
  Lemma lookup_map_seqZ_is_Some start xs i :
    is_Some (map_seqZ (M:=M A) start xs !! i) ↔
      start ≤ i < start + Z.of_nat (length xs).
  Proof. rewrite <-not_eq_None_Some, lookup_map_seqZ_None. lia. Qed.

  Lemma map_seqZ_singleton start x :
    map_seqZ (M:=M A) start [x] = {[ start := x ]}.
  Proof. done. Qed.

  (** [map_seqZ_disjoint] uses [length xs = 0] instead of [xs = []] as
  [lia] can handle the former but not the latter. *)
  Lemma map_seqZ_disjoint start1 start2 xs1 xs2 :
    map_seqZ (M:=M A) start1 xs1 ##ₘ map_seqZ (M:=M A) start2 xs2 ↔
     start1 + Z.of_nat (length xs1) ≤ start2 ∨ start2 + Z.of_nat (length xs2) ≤ start1
     ∨ length xs1 = 0%nat ∨ length xs2 = 0%nat.
  Proof.
    rewrite map_disjoint_alt. setoid_rewrite lookup_map_seqZ_None.
    split; intros Hi; [|lia]. pose proof (Hi start1). pose proof (Hi start2). lia.
  Qed.
  Lemma map_seqZ_app_disjoint start xs1 xs2 :
    map_seqZ (M:=M A) start xs1 ##ₘ map_seqZ (start + Z.of_nat (length xs1)) xs2.
  Proof. apply map_seqZ_disjoint. lia. Qed.
  Lemma map_seqZ_app start xs1 xs2 :
    map_seqZ start (xs1 ++ xs2)
    =@{M A} map_seqZ start xs1 ∪ map_seqZ (start + Z.of_nat (length xs1)) xs2.
  Proof.
    revert start. induction xs1 as [|x1 xs1 IH]; intros start; simpl.
    - by rewrite ->(left_id_L _ _), Z.add_0_r.
    - by rewrite IH, Nat2Z.inj_succ, Z.add_succ_r, Z.add_succ_l,
        !insert_union_singleton_l, (assoc_L _).
  Qed.

  Lemma map_seqZ_cons_disjoint start xs :
    map_seqZ (M:=M A) (Z.succ start) xs !! start = None.
  Proof. rewrite lookup_map_seqZ_None. lia. Qed.
  Lemma map_seqZ_cons start xs x :
    map_seqZ start (x :: xs) =@{M A} <[start:=x]> (map_seqZ (Z.succ start) xs).
  Proof. done. Qed.

  Lemma map_seqZ_snoc_disjoint start xs :
    map_seqZ (M:=M A) start xs !! (start + Z.of_nat (length xs)) = None.
  Proof. rewrite lookup_map_seqZ_None. lia. Qed.
  Lemma map_seqZ_snoc start xs x :
    map_seqZ start (xs ++ [x])
    =@{M A} <[(start + Z.of_nat (length xs)):=x]> (map_seqZ start xs).
  Proof.
    rewrite map_seqZ_app, map_seqZ_singleton.
    by rewrite insert_union_singleton_r by (by rewrite map_seqZ_snoc_disjoint).
  Qed.

  Lemma fmap_map_seqZ {B} (f : A → B) start xs :
    f <$> map_seqZ start xs =@{M B} map_seqZ start (f <$> xs).
  Proof.
    revert start. induction xs as [|x xs IH]; intros start; csimpl.
    { by rewrite fmap_empty. }
    by rewrite fmap_insert, IH.
  Qed.

  Lemma insert_map_seqZ start xs i x:
    start ≤ i < start + Z.of_nat (length xs) →
    <[i:=x]> (map_seqZ start xs)
    =@{M A} map_seqZ start (<[Z.to_nat (i - start):=x]> xs).
  Proof.
    intros. apply map_eq. intros j. destruct (decide (i = j)) as [->|?].
    - rewrite lookup_insert, lookup_map_seqZ, option_guard_True by lia.
      by rewrite list_lookup_insert by lia.
    - rewrite lookup_insert_ne, !lookup_map_seqZ by done.
      case_guard; [|done]. by rewrite list_lookup_insert_ne by lia.
  Qed.
  Lemma map_seqZ_insert start xs i x:
    (i < length xs)%nat →
    map_seqZ start (<[i:=x]> xs) =@{M A}
    <[start + Z.of_nat i:=x]> (map_seqZ start xs).
  Proof. intros. rewrite insert_map_seqZ by lia. auto with lia f_equal. Qed.

  Lemma insert_map_seqZ_0 xs i x:
    0 ≤ i < Z.of_nat (length xs) →
    <[i:=x]> (map_seqZ 0 xs) =@{M A} map_seqZ 0 (<[Z.to_nat i:=x]> xs).
  Proof. intros. rewrite insert_map_seqZ by lia. auto with lia f_equal. Qed.
  Lemma map_seqZ_insert_0 xs i x:
    (i < length xs)%nat →
    map_seqZ 0 (<[i:=x]> xs) =@{M A} <[Z.of_nat i:=x]> (map_seqZ 0 xs).
  Proof. intros. by rewrite map_seqZ_insert. Qed.
End map_seqZ.

Section kmap.
  Context `{FinMap K1 M1} `{FinMap K2 M2}.
  Context (f : K1 → K2) `{!Inj (=) (=) f}.
  Local Notation kmap := (kmap (M1:=M1) (M2:=M2)).

  Lemma lookup_kmap_Some {A} (m : M1 A) (j : K2) x :
    kmap f m !! j = Some x ↔ ∃ i, j = f i ∧ m !! i = Some x.
  Proof.
    assert (∀ x',
      (j, x) ∈ prod_map f id <$> map_to_list m →
      (j, x') ∈ prod_map f id <$> map_to_list m → x = x').
    { intros x'. rewrite !elem_of_list_fmap.
      intros [[j' y1] [??]] [[? y2] [??]]; simplify_eq/=.
      by apply (map_to_list_unique m j'). }
    unfold kmap. rewrite <-elem_of_list_to_map', elem_of_list_fmap by done.
    setoid_rewrite elem_of_map_to_list'. split.
    - intros [[??] [??]]; naive_solver.
    - intros [? [??]]. eexists (_, _); naive_solver.
  Qed.
  Lemma lookup_kmap_is_Some {A} (m : M1 A) (j : K2) :
    is_Some (kmap f m !! j) ↔ ∃ i, j = f i ∧ is_Some (m !! i).
  Proof. unfold is_Some. setoid_rewrite lookup_kmap_Some. naive_solver. Qed.
  Lemma lookup_kmap_None {A} (m : M1 A) (j : K2) :
    kmap f m !! j = None ↔ ∀ i, j = f i → m !! i = None.
  Proof.
    setoid_rewrite eq_None_not_Some.
    rewrite lookup_kmap_is_Some. naive_solver.
  Qed.
  (** Note that to state a lemma [map_kmap f m !! j = ...] we need to have a
  partial inverse [f_inv] of [f] (which one cannot define constructively). Then
  we could write [map_kmap f m !! j = (i ← f_inv j; m !! i)] *)
  Lemma lookup_kmap {A} (m : M1 A) (i : K1) :
    kmap f m !! (f i) = m !! i.
  Proof. apply option_eq. setoid_rewrite lookup_kmap_Some. naive_solver. Qed.
  Lemma lookup_total_kmap `{Inhabited A} (m : M1 A) (i : K1) :
    kmap f m !!! (f i) = m !!! i.
  Proof. by rewrite !lookup_total_alt, lookup_kmap. Qed.

  Global Instance kmap_inj {A} : Inj (=@{M1 A}) (=) (kmap f).
  Proof.
    intros m1 m2 Hm. apply map_eq. intros i. by rewrite <-!lookup_kmap, Hm.
  Qed.

  Lemma kmap_empty {A} : kmap f ∅ =@{M2 A} ∅.
  Proof. unfold kmap. by rewrite map_to_list_empty. Qed.
  Lemma kmap_empty_iff {A} (m : M1 A) : kmap f m = ∅ ↔ m = ∅.
  Proof. rewrite !map_empty. setoid_rewrite lookup_kmap_None. naive_solver. Qed.

  Lemma kmap_singleton {A} i (x : A) : kmap f {[ i := x ]} = {[ f i := x ]}.
  Proof. unfold kmap. by rewrite map_to_list_singleton. Qed.

  Lemma kmap_partial_alter {A} (g : option A → option A) (m : M1 A) i :
    kmap f (partial_alter g i m) = partial_alter g (f i) (kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    destruct (decide (j = f i)) as [->|?].
    { by rewrite lookup_partial_alter, !lookup_kmap, lookup_partial_alter. }
    rewrite lookup_partial_alter_ne, !lookup_kmap_Some by done. split.
    - intros [i' [? Hm]]; simplify_eq/=.
      rewrite lookup_partial_alter_ne in Hm by naive_solver. naive_solver.
    - intros [i' [? Hm]]; simplify_eq/=. exists i'.
      rewrite lookup_partial_alter_ne by naive_solver. naive_solver.
  Qed.
  Lemma kmap_insert {A} (m : M1 A) i x :
    kmap f (<[i:=x]> m) = <[f i:=x]> (kmap f m).
  Proof. apply kmap_partial_alter. Qed.
  Lemma kmap_delete {A} (m : M1 A) i :
    kmap f (delete i m) = delete (f i) (kmap f m).
  Proof. apply kmap_partial_alter. Qed.
  Lemma kmap_alter {A} (g : A → A) (m : M1 A) i :
    kmap f (alter g i m) = alter g (f i) (kmap f m).
  Proof. apply kmap_partial_alter. Qed.

  Lemma kmap_merge {A B C} (g : option A → option B → option C)
      (m1 : M1 A) (m2 : M1 B) :
    kmap f (merge g m1 m2) = merge g (kmap f m1) (kmap f m2).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    rewrite lookup_merge, lookup_kmap_Some.
    setoid_rewrite lookup_merge. split.
    { intros [i [-> ?]]. by rewrite !lookup_kmap. }
    intros Hg. destruct (kmap f m1 !! j) as [x1|] eqn:Hm1.
    { apply lookup_kmap_Some in Hm1 as (i&->&Hm1i).
      exists i. split; [done|]. by rewrite Hm1i, <-lookup_kmap. }
    destruct (kmap f m2 !! j) as [x2|] eqn:Hm2; [|naive_solver].
    apply lookup_kmap_Some in Hm2 as (i&->&Hm2i).
    exists i. split; [done|]. by rewrite Hm2i, <-lookup_kmap, Hm1.
  Qed.
  Lemma kmap_union_with {A} (g : A → A → option A) (m1 m2 : M1 A) :
    kmap f (union_with g m1 m2)
    = union_with g (kmap f m1) (kmap f m2).
  Proof. apply kmap_merge. Qed.
  Lemma kmap_intersection_with {A} (g : A → A → option A) (m1 m2 : M1 A) :
    kmap f (intersection_with g m1 m2)
    = intersection_with g (kmap f m1) (kmap f m2).
  Proof. apply kmap_merge. Qed.
  Lemma kmap_difference_with {A} (g : A → A → option A) (m1 m2 : M1 A) :
    kmap f (difference_with g m1 m2)
    = difference_with g (kmap f m1) (kmap f m2).
  Proof. apply kmap_merge. Qed.

  Lemma kmap_union {A} (m1 m2 : M1 A) :
    kmap f (m1 ∪ m2) = kmap f m1 ∪ kmap f m2.
  Proof. apply kmap_union_with. Qed.
  Lemma kmap_intersection {A} (m1 m2 : M1 A) :
    kmap f (m1 ∩ m2) = kmap f m1 ∩ kmap f m2.
  Proof. apply kmap_intersection_with. Qed.
  Lemma kmap_difference {A} (m1 m2 : M1 A) :
    kmap f (m1 ∖ m2) = kmap f m1 ∖ kmap f m2.
  Proof. apply kmap_difference_with. Qed.

  Lemma kmap_zip_with {A B C} (g : A → B → C) (m1 : M1 A) (m2 : M1 B) :
    kmap f (map_zip_with g m1 m2) = map_zip_with g (kmap f m1) (kmap f m2).
  Proof. by apply kmap_merge. Qed.

  Lemma kmap_imap {A B} (g : K2 → A → option B) (m : M1 A) :
    kmap f (map_imap (g ∘ f) m) = map_imap g (kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    rewrite map_lookup_imap, bind_Some. setoid_rewrite lookup_kmap_Some.
    setoid_rewrite map_lookup_imap. setoid_rewrite bind_Some. naive_solver.
  Qed.
  Lemma kmap_omap {A B} (g : A → option B) (m : M1 A) :
    kmap f (omap g m) = omap g (kmap f m).
  Proof.
    apply map_eq; intros j. apply option_eq; intros y.
    rewrite lookup_omap, bind_Some. setoid_rewrite lookup_kmap_Some.
    setoid_rewrite lookup_omap. setoid_rewrite bind_Some. naive_solver.
  Qed.
  Lemma kmap_fmap {A B} (g : A → B) (m : M1 A) :
    kmap f (g <$> m) = g <$> (kmap f m).
  Proof. by rewrite !map_fmap_alt, kmap_omap. Qed.

  Lemma map_disjoint_kmap {A} (m1 m2 : M1 A) :
    kmap f m1 ##ₘ kmap f m2 ↔ m1 ##ₘ m2.
  Proof.
    rewrite !map_disjoint_spec. setoid_rewrite lookup_kmap_Some. naive_solver.
  Qed.
  Lemma map_agree_kmap {A} (m1 m2 : M1 A) :
    map_agree (kmap f m1) (kmap f m2) ↔ map_agree m1 m2.
  Proof.
    rewrite !map_agree_spec. setoid_rewrite lookup_kmap_Some. naive_solver.
  Qed.
  Lemma kmap_subseteq {A} (m1 m2 : M1 A) :
    kmap f m1 ⊆ kmap f m2 ↔ m1 ⊆ m2.
  Proof.
    rewrite !map_subseteq_spec. setoid_rewrite lookup_kmap_Some. naive_solver.
  Qed.
  Lemma kmap_subset {A} (m1 m2 : M1 A) :
    kmap f m1 ⊂ kmap f m2 ↔ m1 ⊂ m2.
  Proof. unfold strict. by rewrite !kmap_subseteq. Qed.
End kmap.

Section preimg.
  (** We restrict the theory to finite sets with Leibniz equality, which is
  sufficient for [gset], but not for [boolset] or [propset]. The result of the
  pre-image is a map of sets. To support general sets, we would need setoid
  equality on sets, and thus setoid equality on maps. *)
  Context `{FinMap K MK, FinMap A MA, FinSet K SK, !LeibnizEquiv SK}.
  Local Notation map_preimg :=
    (map_preimg (K:=K) (A:=A) (MKA:=MK A) (MASK:=MA SK) (SK:=SK)).
  Implicit Types m : MK A.

  Lemma map_preimg_empty : map_preimg ∅ = ∅.
  Proof. apply map_fold_empty. Qed.
  Lemma map_preimg_insert m i x :
    m !! i = None →
    map_preimg (<[i:=x]> m) =
      partial_alter (λ mX, Some ({[ i ]} ∪ default ∅ mX)) x (map_preimg m).
  Proof.
    intros Hi. refine (map_fold_insert_L _ _ i x m _ Hi).
    intros j1 j2 x1 x2 m' ? _ _. destruct (decide (x1 = x2)) as [->|?].
    - rewrite <-!partial_alter_compose.
      apply partial_alter_ext; intros ? _; f_equal/=. set_solver.
    - by apply partial_alter_commute.
  Qed.

  (** The [map_preimg] function never returns an empty set (we represent that
  case via [None]). *)
  Lemma lookup_preimg_Some_non_empty m x :
    map_preimg m !! x ≠ Some ∅.
  Proof.
    induction m as [|i x' m ? IH] using map_ind.
    { by rewrite map_preimg_empty, lookup_empty. }
    rewrite map_preimg_insert by done. destruct (decide (x = x')) as [->|].
    - rewrite lookup_partial_alter. intros [=]. set_solver.
    - rewrite lookup_partial_alter_ne by done. set_solver.
  Qed.

  Lemma lookup_preimg_None_1 m x i :
    map_preimg m !! x = None → m !! i ≠ Some x.
  Proof.
    induction m as [|i' x' m ? IH] using map_ind; [by rewrite lookup_empty|].
    rewrite map_preimg_insert by done. destruct (decide (x = x')) as [->|].
    - by rewrite lookup_partial_alter.
    - rewrite lookup_partial_alter_ne, lookup_insert_Some by done. naive_solver.
  Qed.

  Lemma lookup_preimg_Some_1 m X x i :
    map_preimg m !! x = Some X →
    i ∈ X ↔ m !! i = Some x.
  Proof.
    revert X. induction m as [|i' x' m ? IH] using map_ind; intros X.
    { by rewrite map_preimg_empty, lookup_empty. }
    rewrite map_preimg_insert by done. destruct (decide (x = x')) as [->|].
    - rewrite lookup_partial_alter. intros [= <-].
      rewrite elem_of_union, elem_of_singleton, lookup_insert_Some.
      destruct (map_preimg m !! x') as [X'|] eqn:Hx'; simpl.
      + rewrite IH by done. naive_solver.
      + apply (lookup_preimg_None_1 _ _ i) in Hx'. set_solver.
    - rewrite lookup_partial_alter_ne, lookup_insert_Some by done. naive_solver.
  Qed.

  Lemma lookup_preimg_None m x :
    map_preimg m !! x = None ↔ ∀ i, m !! i ≠ Some x.
  Proof.
    split; [by eauto using lookup_preimg_None_1|].
    intros Hm. apply eq_None_not_Some; intros [X ?].
    destruct (set_choose_L X) as [i ?].
    { intros ->. by eapply lookup_preimg_Some_non_empty. }
    by eapply (Hm i), lookup_preimg_Some_1.
  Qed.

  Lemma lookup_preimg_Some m x X :
    map_preimg m !! x = Some X ↔ X ≠ ∅ ∧ ∀ i, i ∈ X ↔ m !! i = Some x.
  Proof.
    split.
    - intros HxX. split; [intros ->; by eapply lookup_preimg_Some_non_empty|].
      intros j. by apply lookup_preimg_Some_1.
    - intros [HXne HX]. destruct (map_preimg m !! x) as [X'|] eqn:HX'.
      + f_equal; apply set_eq; intros i. rewrite HX.
        by apply lookup_preimg_Some_1.
      + apply set_choose_L in HXne as [j ?].
        apply (lookup_preimg_None_1 _ _ j) in HX'. naive_solver.
  Qed.

  Lemma lookup_total_preimg m x i :
    i ∈ map_preimg m !!! x ↔ m !! i = Some x.
  Proof.
    rewrite lookup_total_alt. destruct (map_preimg m !! x) as [X|] eqn:HX.
    - by apply lookup_preimg_Some.
    - rewrite lookup_preimg_None in HX. set_solver.
  Qed.
End preimg.


(** ** The [map_img] (image/codomain) operation *)
Section img.
  Context `{FinMap K M, SemiSet A SA}.
  Implicit Types m : M A.
  Implicit Types x y : A.
  Implicit Types X : SA.

  (* avoid writing ≡@{D} everywhere... *)
  Notation map_img := (map_img (M:=M A) (SA:=SA)).

  Lemma elem_of_map_img m x : x ∈ map_img m ↔ ∃ i, m !! i = Some x.
  Proof. unfold map_img. rewrite elem_of_map_to_set. naive_solver. Qed.
  Lemma elem_of_map_img_1 m x : x ∈ map_img m → ∃ i, m !! i = Some x.
  Proof. apply elem_of_map_img. Qed.
  Lemma elem_of_map_img_2 m i x : m !! i = Some x → x ∈ map_img m.
  Proof. rewrite elem_of_map_img. eauto. Qed.

  Lemma not_elem_of_map_img m x : x ∉ map_img m ↔ ∀ i, m !! i ≠ Some x.
  Proof. rewrite elem_of_map_img. naive_solver. Qed.
  Lemma not_elem_of_map_img_1 m i x : x ∉ map_img m → m !! i ≠ Some x.
  Proof. rewrite not_elem_of_map_img. eauto. Qed.
  Lemma not_elem_of_map_img_2 m x : (∀ i, m !! i ≠ Some x) → x ∉ map_img m.
  Proof. apply not_elem_of_map_img. Qed.

  Lemma map_subseteq_img m1 m2 : m1 ⊆ m2 → map_img m1 ⊆ map_img m2.
  Proof.
    rewrite map_subseteq_spec. intros ? x.
    rewrite !elem_of_map_img. naive_solver.
  Qed.

  Lemma map_img_filter (P : K * A → Prop) `{!∀ ix, Decision (P ix)} m X :
    (∀ x, x ∈ X ↔ ∃ i, m !! i = Some x ∧ P (i, x)) →
    map_img (filter P m) ≡ X.
  Proof.
    intros HX x. rewrite elem_of_map_img, HX.
    unfold is_Some. by setoid_rewrite map_lookup_filter_Some.
  Qed.
  Lemma map_img_filter_subseteq (P : K * A → Prop) `{!∀ ix, Decision (P ix)} m :
    map_img (filter P m) ⊆ map_img m.
  Proof. apply map_subseteq_img, map_filter_subseteq. Qed.

  Lemma map_img_empty : map_img ∅ ≡ ∅.
  Proof.
    rewrite set_equiv. intros x. rewrite elem_of_map_img, elem_of_empty.
    setoid_rewrite lookup_empty. naive_solver.
  Qed.
  Lemma map_img_empty_iff m : map_img m ≡ ∅ ↔ m = ∅.
  Proof.
    split; [|intros ->; by rewrite map_img_empty].
    intros Hm. apply map_empty; intros i.
    apply eq_None_ne_Some; intros x ?%elem_of_map_img_2. set_solver.
  Qed.
  Lemma map_img_empty_inv m : map_img m ≡ ∅ → m = ∅.
  Proof. apply map_img_empty_iff. Qed.

  Lemma map_img_delete_subseteq i m : map_img (delete i m) ⊆ map_img m.
  Proof. apply map_subseteq_img, delete_subseteq. Qed.

  Lemma map_img_insert m i x :
    map_img (<[i:=x]> m) ≡ {[ x ]} ∪ map_img (delete i m).
  Proof.
    intros y. rewrite elem_of_union, !elem_of_map_img, elem_of_singleton.
    setoid_rewrite lookup_delete_Some. setoid_rewrite lookup_insert_Some.
    naive_solver.
  Qed.
  Lemma map_img_insert_notin m i x :
    m !! i = None → map_img (<[i:=x]> m) ≡ {[ x ]} ∪ map_img m.
  Proof. intros. by rewrite map_img_insert, delete_notin. Qed.

  Lemma map_img_insert_subseteq m i x :
    map_img (<[i:=x]> m) ⊆ {[ x ]} ∪ map_img m.
  Proof.
    rewrite map_img_insert. apply union_mono_l, map_img_delete_subseteq.
  Qed.
  Lemma elem_of_map_img_insert m i x : x ∈ map_img (<[i:=x]> m).
  Proof. apply elem_of_map_img. exists i. apply lookup_insert. Qed.
  Lemma elem_of_map_img_insert_ne m i x y :
    x ≠ y → x ∈ map_img (<[i:=y]> m) → x ∈ map_img m.
  Proof. intros ? ?%map_img_insert_subseteq. set_solver. Qed.

  Lemma map_img_singleton i x : map_img {[ i := x ]} ≡ {[ x ]}.
  Proof.
    apply set_equiv. intros y.
    rewrite elem_of_map_img. setoid_rewrite lookup_singleton_Some. set_solver.
  Qed.

  Lemma elem_of_map_img_union m1 m2 x :
    x ∈ map_img (m1 ∪ m2) →
    x ∈ map_img m1 ∨ x ∈ map_img m2.
  Proof.
    rewrite !elem_of_map_img. setoid_rewrite lookup_union_Some_raw. naive_solver.
  Qed.
  Lemma elem_of_map_img_union_l m1 m2 x :
    x ∈ map_img m1 → x ∈ map_img (m1 ∪ m2).
  Proof.
    rewrite !elem_of_map_img. setoid_rewrite lookup_union_Some_raw. naive_solver.
  Qed.
  Lemma elem_of_map_img_union_r m1 m2 x :
    m1 ##ₘ m2 → x ∈ map_img m2 → x ∈ map_img (m1 ∪ m2).
  Proof.
    intros. rewrite map_union_comm by done. by apply elem_of_map_img_union_l.
  Qed.
  Lemma elem_of_map_img_union_disjoint m1 m2 x :
    m1 ##ₘ m2 → x ∈ map_img (m1 ∪ m2) ↔ x ∈ map_img m1 ∨ x ∈ map_img m2.
  Proof.
    naive_solver eauto using elem_of_map_img_union,
      elem_of_map_img_union_l, elem_of_map_img_union_r.
  Qed.

  Lemma map_img_union_subseteq m1 m2 :
    map_img (m1 ∪ m2) ⊆ map_img m1 ∪ map_img m2.
  Proof. intros v Hv. apply elem_of_union, elem_of_map_img_union. exact Hv. Qed.
  Lemma map_img_union_subseteq_l m1 m2 : map_img m1 ⊆ map_img (m1 ∪ m2).
  Proof. intros v Hv. by apply elem_of_map_img_union_l. Qed.
  Lemma map_img_union_subseteq_r m1 m2 :
    m1 ##ₘ m2 → map_img m2 ⊆ map_img (m1 ∪ m2).
  Proof. intros Hdisj v Hv. by apply elem_of_map_img_union_r. Qed.
  Lemma map_img_union_disjoint m1 m2 :
    m1 ##ₘ m2 → map_img (m1 ∪ m2) ≡ map_img m1 ∪ map_img m2.
  Proof.
    intros Hdisj. apply set_equiv. intros x.
    rewrite elem_of_union. by apply elem_of_map_img_union_disjoint.
  Qed.

  Lemma map_img_finite m : set_finite (map_img m).
  Proof.
    induction m as [|i x m ? IH] using map_ind.
    - rewrite map_img_empty. apply empty_finite.
    - eapply set_finite_subseteq; [by apply map_img_insert_subseteq|].
      apply union_finite; [apply singleton_finite | apply IH].
  Qed.

  (** Alternative definition of [img] in terms of [map_to_list]. *)
  Lemma map_img_alt m : map_img m ≡ list_to_set (map_to_list m).*2.
  Proof.
    induction m as [|i x m ? IH] using map_ind.
    { by rewrite map_img_empty, map_to_list_empty. }
    by rewrite map_img_insert_notin, map_to_list_insert by done.
  Qed.

  Lemma map_img_singleton_inv m i x :
    map_img m ≡ {[ x ]} → m !! i = None ∨ m !! i = Some x.
  Proof.
    intros Hm. destruct (m !! i) eqn:Hmk; [|by auto].
    apply elem_of_map_img_2 in Hmk. set_solver.
  Qed.

  Lemma map_img_union_inv `{!RelDecision (∈@{SA})} X Y m :
    X ## Y →
    map_img m ≡ X ∪ Y →
    ∃ m1 m2, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ map_img m1 ≡ X ∧ map_img m2 ≡ Y.
  Proof.
    intros Hsep Himg.
    exists (filter (λ '(_,x), x ∈ X) m), (filter (λ '(_,x), x ∉ X) m).
    assert (filter (λ '(_,x), x ∈ X) m ##ₘ filter (λ '(_,x), x ∉ X) m).
    { apply map_disjoint_filter_complement. }
    split_and!.
    - symmetry. apply map_filter_union_complement.
    - done.
    - apply map_img_filter; intros x. split; [|naive_solver].
      intros. destruct (elem_of_map_img_1 m x); set_solver.
    - apply map_img_filter; intros x; split.
      + intros. destruct (elem_of_map_img_1 m x); set_solver.
      + intros (i & ?%elem_of_map_img_2 & ?). set_solver.
  Qed.

  Section leibniz.
    Context `{!LeibnizEquiv SA}.

    Lemma map_img_empty_L : map_img ∅ = ∅.
    Proof. unfold_leibniz. exact map_img_empty. Qed.

    Lemma map_img_empty_iff_L m : map_img m = ∅ ↔ m = ∅.
    Proof. unfold_leibniz. apply map_img_empty_iff. Qed.
    Lemma map_img_empty_inv_L m : map_img m = ∅ → m = ∅.
    Proof. apply map_img_empty_iff_L. Qed.

    Lemma map_img_singleton_L i x : map_img {[ i := x ]} = {[ x ]}.
    Proof. unfold_leibniz. apply map_img_singleton. Qed.

    Lemma map_img_insert_notin_L m i x :
      m !! i = None → map_img (<[i:=x]> m) = {[ x ]} ∪ map_img m.
    Proof. unfold_leibniz. apply map_img_insert_notin. Qed.

    Lemma map_img_union_disjoint_L m1 m2 :
      m1 ##ₘ m2 → map_img (m1 ∪ m2) = map_img m1 ∪ map_img m2.
    Proof. unfold_leibniz. apply map_img_union_disjoint. Qed.

    Lemma map_img_alt_L m : map_img m = list_to_set (map_to_list m).*2.
    Proof. unfold_leibniz. apply map_img_alt. Qed.

    Lemma map_img_singleton_inv_L m i x :
      map_img m = {[ x ]} → m !! i = None ∨ m !! i = Some x.
    Proof. unfold_leibniz. apply map_img_singleton_inv. Qed.

    Lemma map_img_union_inv_L `{!RelDecision (∈@{SA})} X Y m :
      X ## Y →
      map_img m = X ∪ Y →
      ∃ m1 m2, m = m1 ∪ m2 ∧ m1 ##ₘ m2 ∧ map_img m1 = X ∧ map_img m2 = Y.
    Proof. unfold_leibniz. apply map_img_union_inv. Qed.
  End leibniz.

  (** Set solver instances *)
  Global Instance set_unfold_map_img_empty x :
    SetUnfoldElemOf x (map_img (∅:M A)) False.
  Proof. constructor. by rewrite map_img_empty, elem_of_empty. Qed.
  Global Instance set_unfold_map_img_singleton x i y :
    SetUnfoldElemOf x (map_img ({[i:=y]}:M A)) (x = y).
  Proof. constructor. by rewrite map_img_singleton, elem_of_singleton. Qed.
End img.

Lemma map_img_fmap `{FinMap K M, FinSet A SA, SemiSet B SB} (f : A → B) (m : M A) :
  map_img (f <$> m) ≡@{SB} set_map (C:=SA) f (map_img m).
Proof.
  apply set_equiv. intros y. rewrite elem_of_map_img, elem_of_map.
  setoid_rewrite lookup_fmap. setoid_rewrite fmap_Some.
  setoid_rewrite elem_of_map_img. naive_solver.
Qed.
Lemma map_img_fmap_L `{FinMap K M, FinSet A SA, SemiSet B SB, !LeibnizEquiv SB}
    (f : A → B) (m : M A) :
  map_img (f <$> m) =@{SB} set_map (C:=SA) f (map_img m).
Proof. unfold_leibniz. apply map_img_fmap. Qed.

Lemma map_img_kmap `{FinMap K M, FinMap K2 M2, SemiSet A SA}
    (f : K → K2) `{!Inj (=) (=) f} m :
  map_img (kmap (M2:=M2) f m) ≡@{SA} map_img m.
Proof.
  apply set_equiv. intros x. rewrite !elem_of_map_img.
  setoid_rewrite (lookup_kmap_Some f). naive_solver.
Qed.
Lemma map_img_kmap_L `{FinMap K M, FinMap K2 M2, SemiSet A SA, !LeibnizEquiv SA}
    (f : K → K2) `{!Inj (=) (=) f} m :
  map_img (kmap (M2:=M2) f m) =@{SA} map_img m.
Proof. unfold_leibniz. by apply map_img_kmap. Qed.

(** ** The [map_compose] operation *)
Section map_compose.
  Context `{FinMap A MA, FinMap B MB} {C : Type}.
  Implicit Types (m : MB C) (n : MA B) (a : A) (b : B) (c : C).

  Lemma map_lookup_compose m n a : (m ∘ₘ n) !! a = n !! a ≫= (m !!.).
  Proof. apply lookup_omap. Qed.

  Lemma map_lookup_compose_Some m n a c :
    (m ∘ₘ n) !! a = Some c ↔ ∃ b, n !! a = Some b ∧ m !! b = Some c.
  Proof. rewrite map_lookup_compose. destruct (n !! a) eqn:?; naive_solver. Qed.
  Lemma map_lookup_compose_Some_1 m n a c :
    (m ∘ₘ n) !! a = Some c → ∃ b, n !! a = Some b ∧ m !! b = Some c.
  Proof. by rewrite map_lookup_compose_Some. Qed.
  Lemma map_lookup_compose_Some_2 m n a b c :
    n !! a = Some b → m !! b = Some c → (m ∘ₘ n) !! a = Some c.
  Proof. intros. apply map_lookup_compose_Some. by exists b. Qed.

  Lemma map_lookup_compose_None m n a :
    (m ∘ₘ n) !! a = None ↔
    n !! a = None ∨ ∃ b, n !! a = Some b ∧ m !! b = None.
  Proof. rewrite map_lookup_compose. destruct (n !! a) eqn:?; naive_solver. Qed.
  Lemma map_lookup_compose_None_1 m n a :
    (m ∘ₘ n) !! a = None → n !! a = None ∨ ∃ b, n !! a = Some b ∧ m !! b = None.
  Proof. apply map_lookup_compose_None. Qed.
  Lemma map_lookup_compose_None_2_1 m n a : n !! a = None → (m ∘ₘ n) !! a = None.
  Proof. intros. apply map_lookup_compose_None. by left. Qed.
  Lemma map_lookup_compose_None_2_2 m n a b :
    n !! a = Some b → m !! b = None → (m ∘ₘ n) !! a = None.
  Proof. intros. apply map_lookup_compose_None. naive_solver. Qed.

  Lemma map_compose_img_subseteq `{SemiSet C D} m n :
    map_img (m ∘ₘ n) ⊆@{D} map_img m.
  Proof.
    intros c. rewrite !elem_of_map_img.
    setoid_rewrite map_lookup_compose_Some. naive_solver.
  Qed.

  Lemma map_compose_empty_r m : m ∘ₘ ∅ =@{MA C} ∅.
  Proof. apply omap_empty. Qed.
  Lemma map_compose_empty_l n : (∅ : MB C) ∘ₘ n =@{MA C} ∅.
  Proof.
    apply map_eq. intros k. rewrite map_lookup_compose, lookup_empty.
    destruct (n !! k); simpl; [|done]. apply lookup_empty.
  Qed.
  Lemma map_compose_empty_iff m n :
    m ∘ₘ n = ∅ ↔ ∀ a b, n !! a = Some b → m !! b = None.
  Proof.
    rewrite map_empty. setoid_rewrite map_lookup_compose_None.
    apply forall_proper; intros a. destruct (n !! a); naive_solver.
  Qed.

  Lemma map_disjoint_compose_l m1 m2 n : m1 ##ₘ m2 → m1 ∘ₘ n ##ₘ m2 ∘ₘ n.
  Proof.
    rewrite !map_disjoint_spec; intros Hdisj a c1 c2.
    rewrite !map_lookup_compose. destruct (n !! a); naive_solver.
  Qed.
  Lemma map_disjoint_compose_r m n1 n2 : n1 ##ₘ n2 → m ∘ₘ n1 ##ₘ m ∘ₘ n2.
  Proof. apply map_disjoint_omap. Qed.

  Lemma map_compose_union_l m1 m2 n : (m1 ∪ m2) ∘ₘ n = (m1 ∘ₘ n) ∪ (m2 ∘ₘ n).
  Proof.
    apply map_eq; intros a. rewrite lookup_union, !map_lookup_compose.
    destruct (n !! a) as [b|] eqn:?; simpl; [|done]. by rewrite lookup_union.
  Qed.
  Lemma map_compose_union_r m n1 n2 :
    n1 ##ₘ n2 → m ∘ₘ (n1 ∪ n2) = (m ∘ₘ n1) ∪ (m ∘ₘ n2).
  Proof. intros Hs. by apply map_omap_union. Qed.

  Lemma map_compose_mono_l m n1 n2 : n1 ⊆ n2 → m ∘ₘ n1 ⊆ m ∘ₘ n2.
  Proof. by apply map_omap_mono. Qed.
  Lemma map_compose_mono_r m1 m2 n : m1 ⊆ m2 → m1 ∘ₘ n ⊆ m2 ∘ₘ n.
  Proof.
    rewrite !map_subseteq_spec; intros ? a c.
    rewrite !map_lookup_compose_Some. naive_solver.
  Qed.
  Lemma map_compose_mono m1 m2 n1 n2 :
    m1 ⊆ m2 → n1 ⊆ n2 → m1 ∘ₘ n1 ⊆ m2 ∘ₘ n2.
  Proof.
    intros. transitivity (m1 ∘ₘ n2);
      [by apply map_compose_mono_l|by apply map_compose_mono_r].
  Qed.

  Lemma map_compose_as_omap m n : m ∘ₘ n = omap (m !!.) n.
  Proof. done. Qed.

  (** Alternative definition of [m ∘ₘ n] by recursion on [n] *)
  Lemma map_compose_as_fold m n :
    m ∘ₘ n = map_fold (λ a b,
               match m !! b with
               | Some c => <[a:=c]>
               | None => id
               end) ∅ n.
  Proof.
    apply (map_fold_ind (λ mn n, omap (m !!.) n = mn)).
    { apply map_compose_empty_r. }
    intros k b n' mn Hn' IH. rewrite omap_insert, <-IH.
    destruct (m !! b); [done|].
    by apply delete_notin, map_lookup_compose_None_2_1.
  Qed.

  Lemma map_compose_min_l `{SemiSet B D, !RelDecision (∈@{D})} m n :
    m ∘ₘ n = filter (λ '(b,_), b ∈ map_img (SA:=D) n) m ∘ₘ n.
  Proof.
    apply map_eq; intros a. rewrite !map_lookup_compose.
    destruct (n !! a) as [b|] eqn:?; simpl; [|done].
    rewrite map_lookup_filter. destruct (m !! b) eqn:?; simpl; [|done].
    by rewrite option_guard_True by (by eapply elem_of_map_img_2).
  Qed.
  Lemma map_compose_min_r m n :
    m ∘ₘ n = m ∘ₘ filter (λ '(_,b), is_Some (m !! b)) n.
  Proof.
    apply map_eq; intros a. rewrite !map_lookup_compose, map_lookup_filter.
    destruct (n !! a) as [b|] eqn:?; simpl; [|done]. by destruct (m !! b) eqn:?.
  Qed.

  Lemma map_compose_insert_Some m n a b c :
    m !! b = Some c →
    m ∘ₘ <[a:=b]> n =@{MA C} <[a:=c]> (m ∘ₘ n).
  Proof. intros. by apply omap_insert_Some. Qed.
  Lemma map_compose_insert_None m n a b :
    m !! b = None →
    m ∘ₘ <[a:=b]> n =@{MA C} delete a (m ∘ₘ n).
  Proof. intros. by apply omap_insert_None. Qed.

  Lemma map_compose_delete m n a :
    m ∘ₘ delete a n =@{MA C} delete a (m ∘ₘ n).
  Proof. intros. by apply omap_delete. Qed.

  Lemma map_compose_singleton_Some m a b c :
    m !! b = Some c →
    m ∘ₘ {[a := b]} =@{MA C} {[a := c]}.
  Proof. intros. by apply omap_singleton_Some. Qed.
  Lemma map_compose_singleton_None m a b :
    m !! b = None →
    m ∘ₘ {[a := b]} =@{MA C} ∅.
  Proof. intros. by apply omap_singleton_None. Qed.

  Lemma map_compose_singletons a b c :
    ({[b := c]} : MB C) ∘ₘ {[a := b]} =@{MA C} {[a := c]}.
  Proof. by apply map_compose_singleton_Some, lookup_insert. Qed.
End map_compose.

Lemma map_compose_assoc `{FinMap A MA, FinMap B MB, FinMap C MC} {D}
    (m : MC D) (n : MB C) (o : MA B) :
  m ∘ₘ (n ∘ₘ o) = (m ∘ₘ n) ∘ₘ o.
Proof.
  apply map_eq; intros a. rewrite !map_lookup_compose.
  destruct (o !! a); simpl; [|done]. by rewrite map_lookup_compose.
Qed.

Lemma map_fmap_map_compose `{FinMap A MA, FinMap B MB} {C1 C2} (f : C1 → C2)
    (m : MB C1) (n : MA B) :
  f <$> (m ∘ₘ n) = (f <$> m) ∘ₘ n.
Proof.
  apply map_eq; intros a. rewrite lookup_fmap, !map_lookup_compose.
  destruct (n !! a); simpl; [|done]. by rewrite lookup_fmap.
Qed.

Lemma map_omap_map_compose `{FinMap A MA, FinMap B MB} {C1 C2} (f : C1 → option C2)
    (m : MB C1) (n : MA B) :
  omap f (m ∘ₘ n) = omap f m ∘ₘ n.
Proof.
  apply map_eq; intros a. rewrite lookup_omap, !map_lookup_compose.
  destruct (n !! a); simpl; [|done]. by rewrite lookup_omap.
Qed.

(** * Tactics *)
(** The tactic [decompose_map_disjoint] simplifies occurrences of [disjoint]
in the hypotheses that involve the empty map [∅], the union [(∪)] or insert
[<[_:=_]>] operation, the singleton [{[_:= _]}] map, and disjointness of lists of
maps. This tactic does not yield any information loss as all simplifications
performed are reversible. *)
Ltac decompose_map_disjoint := repeat
  match goal with
  | H : _ ∪ _ ##ₘ _ |- _ => apply map_disjoint_union_l in H; destruct H
  | H : _ ##ₘ _ ∪ _ |- _ => apply map_disjoint_union_r in H; destruct H
  | H : {[ _ := _ ]} ##ₘ _ |- _ => apply map_disjoint_singleton_l in H
  | H : _ ##ₘ {[ _ := _ ]} |- _ =>  apply map_disjoint_singleton_r in H
  | H : <[_:=_]>_ ##ₘ _ |- _ => apply map_disjoint_insert_l in H; destruct H
  | H : _ ##ₘ <[_:=_]>_ |- _ => apply map_disjoint_insert_r in H; destruct H
  | H : ⋃ _ ##ₘ _ |- _ => apply map_disjoint_union_list_l in H
  | H : _ ##ₘ ⋃ _ |- _ => apply map_disjoint_union_list_r in H
  | H : ∅ ##ₘ _ |- _ => clear H
  | H : _ ##ₘ ∅ |- _ => clear H
  | H : Forall (.##ₘ _) _ |- _ => rewrite Forall_vlookup in H
  | H : Forall (.##ₘ _) [] |- _ => clear H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_app in H; destruct H
  end.

(** To prove a disjointness property, we first decompose all hypotheses, and
then use an auto database to prove the required property. *)
Create HintDb map_disjoint discriminated.
Ltac solve_map_disjoint :=
  solve [decompose_map_disjoint; auto with map_disjoint].

(** We declare these hints using [Hint Extern] instead of [Hint Resolve] as
[eauto] works badly with hints parametrized by type class constraints. *)
Global Hint Extern 1 (_ ##ₘ _) => done : map_disjoint.
Global Hint Extern 2 (∅ ##ₘ _) => apply map_disjoint_empty_l : map_disjoint.
Global Hint Extern 2 (_ ##ₘ ∅) => apply map_disjoint_empty_r : map_disjoint.
Global Hint Extern 2 ({[ _ := _ ]} ##ₘ _) =>
  apply map_disjoint_singleton_l_2 : map_disjoint.
Global Hint Extern 2 (_ ##ₘ {[ _ := _ ]}) =>
  apply map_disjoint_singleton_r_2 : map_disjoint.
Global Hint Extern 2 (_ ∪ _ ##ₘ _) => apply map_disjoint_union_l_2 : map_disjoint.
Global Hint Extern 2 (_ ##ₘ _ ∪ _) => apply map_disjoint_union_r_2 : map_disjoint.
Global Hint Extern 2 ({[_:= _]} ##ₘ _) => apply map_disjoint_singleton_l : map_disjoint.
Global Hint Extern 2 (_ ##ₘ {[_:= _]}) => apply map_disjoint_singleton_r : map_disjoint.
Global Hint Extern 2 (<[_:=_]>_ ##ₘ _) => apply map_disjoint_insert_l_2 : map_disjoint.
Global Hint Extern 2 (_ ##ₘ <[_:=_]>_) => apply map_disjoint_insert_r_2 : map_disjoint.
Global Hint Extern 2 (delete _ _ ##ₘ _) => apply map_disjoint_delete_l : map_disjoint.
Global Hint Extern 2 (_ ##ₘ delete _ _) => apply map_disjoint_delete_r : map_disjoint.
Global Hint Extern 2 (list_to_map _ ##ₘ _) =>
  apply map_disjoint_list_to_map_zip_l_2 : mem_disjoint.
Global Hint Extern 2 (_ ##ₘ list_to_map _) =>
  apply map_disjoint_list_to_map_zip_r_2 : mem_disjoint.
Global Hint Extern 2 (⋃ _ ##ₘ _) => apply map_disjoint_union_list_l_2 : mem_disjoint.
Global Hint Extern 2 (_ ##ₘ ⋃ _) => apply map_disjoint_union_list_r_2 : mem_disjoint.
Global Hint Extern 2 (foldr delete _ _ ##ₘ _) =>
  apply map_disjoint_foldr_delete_l : map_disjoint.
Global Hint Extern 2 (_ ##ₘ foldr delete _ _) =>
  apply map_disjoint_foldr_delete_r : map_disjoint.
Global Hint Extern 3 (_ ∘ₘ _ ##ₘ _ ∘ₘ _) =>
  apply map_disjoint_compose_l : map_disjoint.
Global Hint Extern 3 (_ ∘ₘ _ ##ₘ _ ∘ₘ _) =>
  apply map_disjoint_compose_r : map_disjoint.

(** The tactic [simpl_map by tac] simplifies occurrences of finite map look
ups. It uses [tac] to discharge generated inequalities. Look ups in unions do
not have nice equational properties, hence it invokes [tac] to prove that such
look ups yield [Some]. *)
Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert in H || rewrite lookup_insert_ne in H by tac
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter in H || rewrite lookup_alter_ne in H by tac
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete in H || rewrite lookup_delete_ne in H by tac
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton in H || rewrite lookup_singleton_ne in H by tac
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := mk_evar A in
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x) as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert || rewrite lookup_insert_ne by tac
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter || rewrite lookup_alter_ne by tac
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete || rewrite lookup_delete_ne by tac
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton || rewrite lookup_singleton_ne by tac
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := mk_evar A in
    let E := fresh in
    assert (m !! i = Some x) as E by tac;
    rewrite E; clear E
  end.

Create HintDb simpl_map discriminated.
Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.

Global Hint Extern 80 ((_ ∪ _) !! _ = Some _) => apply lookup_union_Some_l : simpl_map.
Global Hint Extern 81 ((_ ∪ _) !! _ = Some _) => apply lookup_union_Some_r : simpl_map.
Global Hint Extern 80 ({[ _:=_ ]} !! _ = Some _) => apply lookup_singleton : simpl_map.
Global Hint Extern 80 (<[_:=_]> _ !! _ = Some _) => apply lookup_insert : simpl_map.

(** Now we take everything together and also discharge conflicting look ups,
simplify overlapping look ups, and perform cancellations of equalities
involving unions. *)
Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    opose proof* (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [|by tac|by tac]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [|by tac|by tac]
  | H : {[?i := ?x]} = ∅ |- _ => by destruct (map_non_empty_singleton i x)
  | H : ∅ = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
  | H : ?m !! ?i = Some _, H2 : ?m !! ?j = None |- _ =>
     unless (i ≠ j) by done;
     assert (i ≠ j) by (by intros ?; simplify_eq)
  end.
Tactic Notation "simplify_map_eq" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || simplify_map_eq by tac).
Tactic Notation "simplify_map_eq" :=
  simplify_map_eq by eauto with simpl_map map_disjoint.
Tactic Notation "simplify_map_eq" "/=" :=
  simplify_map_eq/= by eauto with simpl_map map_disjoint.
