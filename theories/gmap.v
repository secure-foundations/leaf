(** This file implements finite maps and finite sets with keys of any countable
type. The implementation is based on [Pmap]s, radix-2 search trees.

Computations on [gmap] or [gset], even concrete ones, are prevented from
reducing with [simpl] or [cbv] (by marking [gmap_empty] as [Opaque]), because
[simpl] reduces too eagerly.
To compute concrete results, you need to both:
- project in the end to some concrete data structure that, unlike
  [gmap]/[gset], does not contain proofs, say via [map_to_list] or [!!]; and
- use [vm_compute] to run the computation, because it ignores opacity.
*)
From stdpp Require Export countable infinite fin_maps fin_map_dom.
From stdpp Require Import pmap mapset propset.
From stdpp Require Import options.

(* FIXME: This file needs a 'Proof Using' hint, but they need to be set
locally (or things moved out of sections) as no default works well enough. *)
Unset Default Proof Using.

(** * The data structure *)
(** We pack a [Pmap] together with a proof that ensures that all keys correspond
to codes of actual elements of the countable type. *)
Definition gmap_wf K `{Countable K} {A} (m : Pmap A) : Prop :=
  bool_decide (map_Forall (λ p _, encode (A:=K) <$> decode p = Some p) m).
Record gmap K `{Countable K} A := GMap {
  gmap_car : Pmap A;
  gmap_prf : gmap_wf K gmap_car
}.
Global Arguments GMap {_ _ _ _} _ _ : assert.
Global Arguments gmap_car {_ _ _ _} _ : assert.
Lemma gmap_eq `{Countable K} {A} (m1 m2 : gmap K A) :
  m1 = m2 ↔ gmap_car m1 = gmap_car m2.
Proof.
  split; [by intros ->|intros]. destruct m1, m2; simplify_eq/=.
  f_equal; apply proof_irrel.
Qed.
Global Instance gmap_eq_eq `{Countable K, EqDecision A} : EqDecision (gmap K A).
Proof.
 refine (λ m1 m2, cast_if (decide (gmap_car m1 = gmap_car m2)));
  abstract (by rewrite gmap_eq).
Defined.

(** * Operations on the data structure *)
Global Instance gmap_lookup `{Countable K} {A} : Lookup K A (gmap K A) :=
  λ i '(GMap m _), m !! encode i.
Global Instance gmap_empty `{Countable K} {A} : Empty (gmap K A) := GMap ∅ I.
(** Block reduction, even on concrete [gmap]s.
Marking [gmap_empty] as [simpl never] would not be enough, because of
https://github.com/coq/coq/issues/2972 and
https://github.com/coq/coq/issues/2986.
And marking [gmap] consumers as [simpl never] does not work either, see:
https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/171#note_53216
*)
Global Opaque gmap_empty.
Lemma gmap_partial_alter_wf `{Countable K} {A} (f : option A → option A) m i :
  gmap_wf K m → gmap_wf K (partial_alter f (encode (A:=K) i) m).
Proof.
  unfold gmap_wf; rewrite !bool_decide_spec.
  intros Hm p x. destruct (decide (encode i = p)) as [<-|?].
  - rewrite decode_encode; eauto.
  - rewrite lookup_partial_alter_ne by done. by apply Hm.
Qed.

Global Instance gmap_partial_alter `{Countable K} {A} :
    PartialAlter K A (gmap K A) := λ f i '(GMap m Hm),
  GMap (partial_alter f (encode i) m) (gmap_partial_alter_wf f m i Hm).

Lemma gmap_fmap_wf `{Countable K} {A B} (f : A → B) m :
  gmap_wf K m → gmap_wf K (f <$> m).
Proof.
  unfold gmap_wf; rewrite !bool_decide_spec.
  intros ? p x. rewrite lookup_fmap, fmap_Some; intros (?&?&?); eauto.
Qed.
Global Instance gmap_fmap `{Countable K} : FMap (gmap K) := λ A B f '(GMap m Hm),
  GMap (f <$> m) (gmap_fmap_wf f m Hm).
Lemma gmap_omap_wf `{Countable K} {A B} (f : A → option B) m :
  gmap_wf K m → gmap_wf K (omap f m).
Proof.
  unfold gmap_wf; rewrite !bool_decide_spec.
  intros ? p x; rewrite lookup_omap, bind_Some; intros (?&?&?); eauto.
Qed.
Global Instance gmap_omap `{Countable K} : OMap (gmap K) := λ A B f '(GMap m Hm),
  GMap (omap f m) (gmap_omap_wf f m Hm).
Lemma gmap_merge_wf `{Countable K} {A B C}
    (f : option A → option B → option C) m1 m2 :
  gmap_wf K m1 → gmap_wf K m2 → gmap_wf K (merge f m1 m2).
Proof.
  unfold gmap_wf; rewrite !bool_decide_spec.
  intros Hm1 Hm2 p z. rewrite lookup_merge; intros.
  destruct (m1 !! _) eqn:?, (m2 !! _) eqn:?; naive_solver.
Qed.
Global Instance gmap_merge `{Countable K} : Merge (gmap K) :=
  λ A B C f '(GMap m1 Hm1) '(GMap m2 Hm2),
    GMap (merge f m1 m2) (gmap_merge_wf f m1 m2 Hm1 Hm2).
Global Instance gmap_to_list `{Countable K} {A} : FinMapToList K A (gmap K A) :=
  λ '(GMap m _),
    omap (λ '(i, x), (., x) <$> decode i) (map_to_list m).

(** * Instantiation of the finite map interface *)
Global Instance gmap_finmap `{Countable K} : FinMap K (gmap K).
Proof.
  split.
  - unfold lookup; intros A [m1 Hm1] [m2 Hm2] Hm.
    apply gmap_eq, map_eq; intros i; simpl in *.
    apply bool_decide_unpack in Hm1; apply bool_decide_unpack in Hm2.
    apply option_eq; intros x; split; intros Hi.
    + pose proof (Hm1 i x Hi); simpl in *.
      by destruct (decode i); simplify_eq/=; rewrite <-Hm.
    + pose proof (Hm2 i x Hi); simpl in *.
      by destruct (decode i); simplify_eq/=; rewrite Hm.
  - done.
  - intros A f [m Hm] i; apply (lookup_partial_alter f m).
  - intros A f [m Hm] i j Hs; apply (lookup_partial_alter_ne f m).
    by contradict Hs; apply (inj encode).
  - intros A B f [m Hm] i; apply (lookup_fmap f m).
  - intros A [m Hm]; unfold map_to_list; simpl.
    apply bool_decide_unpack, map_Forall_to_list in Hm; revert Hm.
    induction (NoDup_map_to_list m) as [|[p x] l Hpx];
      inversion 1 as [|??? Hm']; simplify_eq/=; [by constructor|].
    destruct (decode p) as [i|] eqn:?; simplify_eq/=; constructor; eauto.
    rewrite elem_of_list_omap; intros ([p' x']&?&?); simplify_eq/=.
    feed pose proof (proj1 (Forall_forall _ _) Hm' (p',x')); simpl in *; auto.
    by destruct (decode p') as [i'|]; simplify_eq/=.
  - intros A [m Hm] i x; unfold map_to_list, lookup; simpl.
    apply bool_decide_unpack in Hm; rewrite elem_of_list_omap; split.
    + intros ([p' x']&Hp'&?); apply elem_of_map_to_list in Hp'.
      feed pose proof (Hm p' x'); simpl in *; auto.
      by destruct (decode p') as [i'|] eqn:?; simplify_eq/=.
    + intros; exists (encode i,x); simpl.
      by rewrite elem_of_map_to_list, decode_encode.
  - intros A B f [m Hm] i; apply (lookup_omap f m).
  - intros A B C f [m1 Hm1] [m2 Hm2] i; unfold merge, lookup; simpl.
    by rewrite lookup_merge by done; destruct (m1 !! _), (m2 !! _).
Qed.

Global Program Instance gmap_countable
    `{Countable K, Countable A} : Countable (gmap K A) := {
  encode m := encode (map_to_list m : list (K * A));
  decode p := list_to_map <$> decode p
}.
Next Obligation.
  intros K ?? A ?? m; simpl. rewrite decode_encode; simpl.
  by rewrite list_to_map_to_list.
Qed.

(** * Curry and uncurry *)
Definition gmap_curry `{Countable K1, Countable K2} {A} :
    gmap K1 (gmap K2 A) → gmap (K1 * K2) A :=
  map_fold (λ i1 m' macc,
    map_fold (λ i2 x, <[(i1,i2):=x]>) macc m') ∅.
Definition gmap_uncurry `{Countable K1, Countable K2} {A} :
    gmap (K1 * K2) A → gmap K1 (gmap K2 A) :=
  map_fold (λ '(i1, i2) x,
    partial_alter (Some ∘ <[i2:=x]> ∘ default ∅) i1) ∅.

Section curry_uncurry.
  Context `{Countable K1, Countable K2} {A : Type}.

  (* FIXME: the type annotations `option (gmap K2 A)` are silly. Maybe these are
  a consequence of Coq bug #5735 *)
  Lemma lookup_gmap_curry (m : gmap K1 (gmap K2 A)) i j :
    gmap_curry m !! (i,j) = (m !! i : option (gmap K2 A)) ≫= (.!! j).
  Proof.
    apply (map_fold_ind (λ mr m, mr !! (i,j) = m !! i ≫= (.!! j))).
    { by rewrite !lookup_empty. }
    clear m; intros i' m2 m m12 Hi' IH.
    apply (map_fold_ind (λ m2r m2, m2r !! (i,j) = <[i':=m2]> m !! i ≫= (.!! j))).
    { rewrite IH. destruct (decide (i' = i)) as [->|].
      - rewrite lookup_insert, Hi'; simpl; by rewrite lookup_empty.
      - by rewrite lookup_insert_ne by done. }
    intros j' y m2' m12' Hj' IH'. destruct (decide (i = i')) as [->|].
    - rewrite lookup_insert; simpl. destruct (decide (j = j')) as [->|].
      + by rewrite !lookup_insert.
      + by rewrite !lookup_insert_ne, IH', lookup_insert by congruence.
    - by rewrite !lookup_insert_ne, IH', lookup_insert_ne by congruence.
  Qed.

  Lemma lookup_gmap_uncurry (m : gmap (K1 * K2) A) i j :
    (gmap_uncurry m !! i : option (gmap K2 A)) ≫= (.!! j) = m !! (i, j).
  Proof.
    apply (map_fold_ind (λ mr m, mr !! i ≫= (.!! j) = m !! (i, j))).
    { by rewrite !lookup_empty. }
    clear m; intros [i' j'] x m12 mr Hij' IH.
    destruct (decide (i = i')) as [->|].
    - rewrite lookup_partial_alter. destruct (decide (j = j')) as [->|].
      + destruct (mr !! i'); simpl; by rewrite !lookup_insert.
      + destruct (mr !! i'); simpl; by rewrite !lookup_insert_ne by congruence.
    - by rewrite lookup_partial_alter_ne, lookup_insert_ne by congruence.
  Qed.

  Lemma lookup_gmap_uncurry_None (m : gmap (K1 * K2) A) i :
    gmap_uncurry m !! i = None ↔ (∀ j, m !! (i, j) = None).
  Proof.
    apply (map_fold_ind (λ mr m, mr !! i = None ↔ (∀ j, m !! (i, j) = None)));
      [done|].
    clear m; intros [i' j'] x m12 mr Hij' IH.
    destruct (decide (i = i')) as [->|].
    - split; [by rewrite lookup_partial_alter|].
      intros Hi. specialize (Hi j'). by rewrite lookup_insert in Hi.
    - rewrite lookup_partial_alter_ne, IH; [|done]. apply forall_proper.
      intros j. rewrite lookup_insert_ne; [done|congruence].
  Qed.

  Lemma gmap_curry_uncurry (m : gmap (K1 * K2) A) :
    gmap_curry (gmap_uncurry m) = m.
  Proof.
   apply map_eq; intros [i j]. by rewrite lookup_gmap_curry, lookup_gmap_uncurry.
  Qed.

  Lemma gmap_uncurry_non_empty (m : gmap (K1 * K2) A) i x :
    gmap_uncurry m !! i = Some x → x ≠ ∅.
  Proof.
    intros Hm ->. eapply eq_None_not_Some; [|by eexists].
    eapply lookup_gmap_uncurry_None; intros j.
    by rewrite <-lookup_gmap_uncurry, Hm.
  Qed.

  Lemma gmap_uncurry_curry_non_empty (m : gmap K1 (gmap K2 A)) :
    (∀ i x, m !! i = Some x → x ≠ ∅) →
    gmap_uncurry (gmap_curry m) = m.
  Proof.
    intros Hne. apply map_eq; intros i. destruct (m !! i) as [m2|] eqn:Hm.
    - destruct (gmap_uncurry (gmap_curry m) !! i) as [m2'|] eqn:Hcurry.
      + f_equal. apply map_eq. intros j.
        trans ((gmap_uncurry (gmap_curry m) !! i : option (gmap _ _)) ≫= (.!! j)).
        { by rewrite Hcurry. }
        by rewrite lookup_gmap_uncurry, lookup_gmap_curry, Hm.
      + rewrite lookup_gmap_uncurry_None in Hcurry.
        exfalso; apply (Hne i m2), map_eq; [done|intros j].
        by rewrite lookup_empty, <-(Hcurry j), lookup_gmap_curry, Hm.
   - apply lookup_gmap_uncurry_None; intros j. by rewrite lookup_gmap_curry, Hm.
  Qed.
End curry_uncurry.

(** * Finite sets *)
Definition gset K `{Countable K} := mapset (gmap K).

Section gset.
  Context `{Countable K}.
  Global Instance gset_elem_of: ElemOf K (gset K) := _.
  Global Instance gset_empty : Empty (gset K) := _.
  Global Instance gset_singleton : Singleton K (gset K) := _.
  Global Instance gset_union: Union (gset K) := _.
  Global Instance gset_intersection: Intersection (gset K) := _.
  Global Instance gset_difference: Difference (gset K) := _.
  Global Instance gset_elements: Elements K (gset K) := _.
  Global Instance gset_leibniz : LeibnizEquiv (gset K) := _.
  Global Instance gset_semi_set : SemiSet K (gset K) | 1 := _.
  Global Instance gset_set : Set_ K (gset K) | 1 := _.
  Global Instance gset_fin_set : FinSet K (gset K) := _.
  Global Instance gset_eq_dec : EqDecision (gset K) := _.
  Global Instance gset_countable : Countable (gset K) := _.
  Global Instance gset_equiv_dec : RelDecision (≡@{gset K}) | 1 := _.
  Global Instance gset_elem_of_dec : RelDecision (∈@{gset K}) | 1 := _.
  Global Instance gset_disjoint_dec : RelDecision (##@{gset K}) := _.
  Global Instance gset_subseteq_dec : RelDecision (⊆@{gset K}) := _.
  Global Instance gset_dom {A} : Dom (gmap K A) (gset K) := mapset_dom.
  Global Instance gset_dom_spec : FinMapDom K (gmap K) (gset K) := mapset_dom_spec.

  (** If you are looking for a lemma showing that [gset] is extensional, see
  [sets.set_eq]. *)

  Definition gset_to_gmap {A} (x : A) (X : gset K) : gmap K A :=
    (λ _, x) <$> mapset_car X.

  Lemma lookup_gset_to_gmap {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = guard (i ∈ X); Some x.
  Proof.
    destruct X as [X].
    unfold gset_to_gmap, gset_elem_of, elem_of, mapset_elem_of; simpl.
    rewrite lookup_fmap.
    case_option_guard; destruct (X !! i) as [[]|]; naive_solver.
  Qed.
  Lemma lookup_gset_to_gmap_Some {A} (x : A) (X : gset K) i y :
    gset_to_gmap x X !! i = Some y ↔ i ∈ X ∧ x = y.
  Proof. rewrite lookup_gset_to_gmap. simplify_option_eq; naive_solver. Qed.
  Lemma lookup_gset_to_gmap_None {A} (x : A) (X : gset K) i :
    gset_to_gmap x X !! i = None ↔ i ∉ X.
  Proof. rewrite lookup_gset_to_gmap. simplify_option_eq; naive_solver. Qed.

  Lemma gset_to_gmap_empty {A} (x : A) : gset_to_gmap x ∅ = ∅.
  Proof. apply fmap_empty. Qed.
  Lemma gset_to_gmap_union_singleton {A} (x : A) i Y :
    gset_to_gmap x ({[ i ]} ∪ Y) = <[i:=x]>(gset_to_gmap x Y).
  Proof.
    apply map_eq; intros j; apply option_eq; intros y.
    rewrite lookup_insert_Some, !lookup_gset_to_gmap_Some, elem_of_union,
      elem_of_singleton; destruct (decide (i = j)); intuition.
  Qed.
  Lemma gset_to_gmap_difference_singleton {A} (x : A) i Y :
    gset_to_gmap x (Y ∖ {[i]}) = delete i (gset_to_gmap x Y).
  Proof.
    apply map_eq; intros j; apply option_eq; intros y.
    rewrite lookup_delete_Some, !lookup_gset_to_gmap_Some, elem_of_difference,
      elem_of_singleton; destruct (decide (i = j)); intuition.
  Qed.

  Lemma fmap_gset_to_gmap {A B} (f : A → B) (X : gset K) (x : A) :
    f <$> gset_to_gmap x X = gset_to_gmap (f x) X.
  Proof.
    apply map_eq; intros j. rewrite lookup_fmap, !lookup_gset_to_gmap.
    by simplify_option_eq.
  Qed.
  Lemma gset_to_gmap_dom {A B} (m : gmap K A) (y : B) :
    gset_to_gmap y (dom _ m) = const y <$> m.
  Proof.
    apply map_eq; intros j. rewrite lookup_fmap, lookup_gset_to_gmap.
    destruct (m !! j) as [x|] eqn:?.
    - by rewrite option_guard_True by (rewrite elem_of_dom; eauto).
    - by rewrite option_guard_False by (rewrite not_elem_of_dom; eauto).
  Qed.
  Lemma dom_gset_to_gmap {A} (X : gset K) (x : A) :
    dom _ (gset_to_gmap x X) = X.
  Proof.
    induction X as [| y X not_in IH] using set_ind_L.
    - rewrite gset_to_gmap_empty, dom_empty_L; done.
    - rewrite gset_to_gmap_union_singleton, dom_insert_L, IH; done.
  Qed.
End gset.

Typeclasses Opaque gset.
