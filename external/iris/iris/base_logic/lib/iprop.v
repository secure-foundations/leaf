From iris.algebra Require Import gmap.
From iris.algebra Require cofe_solver.
From iris.base_logic Require Export base_logic.
From iris.prelude Require Import options.

(** In this file we construct the type [iProp] of propositions of the Iris
logic. This is done by solving the following recursive domain equation:

  iProp ≈ uPred (∀ i : gid, gname -fin-> (Σ i) iProp)

where:

  Σ : gFunctors  := lists of locally constractive functors
  i : gid        := indexes addressing individual functors in [Σ]
  γ : gname      := ghost variable names

The Iris logic is parametrized by a list of locally contractive functors [Σ]
from the category of COFEs to the category of CMRAs. These functors are
instantiated with [iProp], the type of Iris propositions, which allows one to
construct impredicate CMRAs, such as invariants and stored propositions using
the agreement CMRA. *)


(** * Locally contractive functors *)
(** The type [gFunctor] bundles a functor from the category of COFEs to the
category of CMRAs with a proof that it is locally contractive. *)
Structure gFunctor := GFunctor {
  gFunctor_F :> rFunctor;
  gFunctor_map_contractive : rFunctorContractive gFunctor_F;
}.
Global Arguments GFunctor _ {_}.
Global Existing Instance gFunctor_map_contractive.
Add Printing Constructor gFunctor.

(** The type [gFunctors] describes the parameters [Σ] of the Iris logic: lists
of [gFunctor]s.

Note that [gFunctors] is isomorphic to [list gFunctor], but defined in an
alternative way to avoid universe inconsistencies with respect to the universe
monomorphic [list] type. *)
Definition gFunctors := { n : nat & fin n → gFunctor }.

Definition gid (Σ : gFunctors) := fin (projT1 Σ).
Definition gFunctors_lookup (Σ : gFunctors) : gid Σ → gFunctor := projT2 Σ.

Definition gname := positive.
Canonical Structure gnameO := leibnizO gname.

(** The resources functor [iResF Σ A := ∀ i : gid, gname -fin-> (Σ i) A]. *)
Definition iResF (Σ : gFunctors) : urFunctor :=
  discrete_funURF (λ i, gmapURF gname (gFunctors_lookup Σ i)).


(** We define functions for the empty list of functors, the singleton list of
functors, and the append operator on lists of functors. These are used to
compose [gFunctors] out of smaller pieces. *)
Module gFunctors.
  Definition nil : gFunctors := existT 0 (fin_0_inv _).

  Definition singleton (F : gFunctor) : gFunctors :=
    existT 1 (fin_S_inv (λ _, gFunctor) F (fin_0_inv _)).

  Definition app (Σ1 Σ2 : gFunctors) : gFunctors :=
    existT (projT1 Σ1 + projT1 Σ2) (fin_plus_inv _ (projT2 Σ1) (projT2 Σ2)).
End gFunctors.

Coercion gFunctors.singleton : gFunctor >-> gFunctors.
Notation "#[ ]" := gFunctors.nil (format "#[ ]").
Notation "#[ Σ1 ; .. ; Σn ]" :=
  (gFunctors.app Σ1 .. (gFunctors.app Σn gFunctors.nil) ..).


(** * Subfunctors *)
(** In order to make proofs in the Iris logic modular, they are not done with
respect to some concrete list of functors [Σ], but are instead parametrized by
an arbitrary list of functors [Σ] that contains at least certain functors. For
example, the lock library is parameterized by a functor [Σ] that should have
the functors corresponding to the heap and the exclusive monoid to manage to
lock invariant.

The contraints to can be expressed using the type class [subG Σ1 Σ2], which
expresses that the functors [Σ1] are contained in [Σ2]. *)
Class subG (Σ1 Σ2 : gFunctors) := in_subG i :
  { j | gFunctors_lookup Σ1 i = gFunctors_lookup Σ2 j }.

(** Avoid trigger happy type class search: this line ensures that type class
search is only triggered if the arguments of [subG] do not contain evars. Since
instance search for [subG] is restrained, instances should persistently have [subG] as
their first parameter to avoid loops. For example, the instances [subG_authΣ]
and [auth_discrete] otherwise create a cycle that pops up arbitrarily. *)
Global Hint Mode subG ! + : typeclass_instances.

Lemma subG_inv Σ1 Σ2 Σ : subG (gFunctors.app Σ1 Σ2) Σ → subG Σ1 Σ * subG Σ2 Σ.
Proof.
  move=> H; split.
  - move=> i; move: H=> /(_ (Fin.L _ i)) [j] /=. rewrite fin_plus_inv_L; eauto.
  - move=> i; move: H=> /(_ (Fin.R _ i)) [j] /=. rewrite fin_plus_inv_R; eauto.
Qed.

Global Instance subG_refl Σ : subG Σ Σ.
Proof. move=> i; by exists i. Qed.
Global Instance subG_app_l Σ Σ1 Σ2 : subG Σ Σ1 → subG Σ (gFunctors.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.L _ j). by rewrite /= fin_plus_inv_L.
Qed.
Global Instance subG_app_r Σ Σ1 Σ2 : subG Σ Σ2 → subG Σ (gFunctors.app Σ1 Σ2).
Proof.
  move=> H i; move: H=> /(_ i) [j ?].
  exists (Fin.R _ j). by rewrite /= fin_plus_inv_R.
Qed.


(** * Solution of the recursive domain equation *)
(** We first declare a module type and then an instance of it so as to seal all of
the construction, this way we are sure we do not use any properties of the
construction, and also avoid Coq from blindly unfolding it. *)
Module Type iProp_solution_sig.
  Parameter iPrePropO : gFunctors → ofe.
  Global Declare Instance iPreProp_cofe {Σ} : Cofe (iPrePropO Σ).

  Definition iResUR (Σ : gFunctors) : ucmra :=
    discrete_funUR (λ i,
      gmapUR gname (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ))).
  Notation iProp Σ := (uPred (iResUR Σ)).
  Notation iPropO Σ := (uPredO (iResUR Σ)).
  Notation iPropI Σ := (uPredI (iResUR Σ)).

  Parameter iProp_unfold: ∀ {Σ}, iPropO Σ -n> iPrePropO Σ.
  Parameter iProp_fold: ∀ {Σ}, iPrePropO Σ -n> iPropO Σ.
  Parameter iProp_fold_unfold: ∀ {Σ} (P : iProp Σ),
    iProp_fold (iProp_unfold P) ≡ P.
  Parameter iProp_unfold_fold: ∀ {Σ} (P : iPrePropO Σ),
    iProp_unfold (iProp_fold P) ≡ P.
End iProp_solution_sig.

Module Export iProp_solution : iProp_solution_sig.
  Import cofe_solver.
  Definition iProp_result (Σ : gFunctors) :
    solution (uPredOF (iResF Σ)) := solver.result _.
  Definition iPrePropO (Σ : gFunctors) : ofe := iProp_result Σ.
  Global Instance iPreProp_cofe {Σ} : Cofe (iPrePropO Σ) := _.

  Definition iResUR (Σ : gFunctors) : ucmra :=
    discrete_funUR (λ i,
      gmapUR gname (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ))).
  Notation iProp Σ := (uPred (iResUR Σ)).
  Notation iPropO Σ := (uPredO (iResUR Σ)).

  Definition iProp_unfold {Σ} : iPropO Σ -n> iPrePropO Σ :=
    ofe_iso_1 (iProp_result Σ).
  Definition iProp_fold {Σ} : iPrePropO Σ -n> iPropO Σ :=
    ofe_iso_2 (iProp_result Σ).
  Lemma iProp_fold_unfold {Σ} (P : iProp Σ) : iProp_fold (iProp_unfold P) ≡ P.
  Proof. apply ofe_iso_21. Qed.
  Lemma iProp_unfold_fold {Σ} (P : iPrePropO Σ) : iProp_unfold (iProp_fold P) ≡ P.
  Proof. apply ofe_iso_12. Qed.
End iProp_solution.


(** * Properties of the solution to the recursive domain equation *)
Lemma iProp_unfold_equivI {Σ} (P Q : iProp Σ) :
  iProp_unfold P ≡ iProp_unfold Q ⊢@{iPropI Σ} P ≡ Q.
Proof.
  rewrite -{2}(iProp_fold_unfold P) -{2}(iProp_fold_unfold Q). apply: f_equivI.
Qed.
