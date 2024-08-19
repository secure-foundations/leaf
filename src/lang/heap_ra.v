From iris.algebra Require Import gmap_view frac.
From iris.algebra Require Export dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Import ghost_map.

(*|
========
Heap RA
========

We define ghost state for reasoning about the simp_lang heap. This is a
simplification of gen_heap from Iris, which is what HeapLang uses. We don't
actually build an RA in this library but wrap gmap_view with lemmas about
ownership in order to give easy-to-read definitions and easy-to-use lemmas.

If you were instantiating Iris you would probably start with gen_heap, but you
might deviate from it or add to it for custom program logic features that are
directly tied to the state.
|*)


(** This file provides a generic mechanism for a language-level point-to
connective [l ↦{dq} v] reflecting the physical heap.  This library is designed to
be used as a singleton (i.e., with only a single instance existing in any
proof), with the [gen_heapG] typeclass providing the ghost names of that unique
instance.  That way, [mapsto] does not need an explicit [gname] parameter.
This mechanism is plugged into a language and related to the physical heap
by using [gen_heap_interp σ] in the state interpretation of the weakest
precondition. See primitive_laws.v for where that happens.
 *)

(** The CMRAs we need, and the global ghost names we are using. *)

Class gen_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heapGpreS_inG : ghost_mapG Σ L V;
}.
Local Existing Instance gen_heapGpreS_inG.

Class gen_heapGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapGS {
  gen_heap_inG : gen_heapGpreS L V Σ;
  gen_heap_name : gname;
}.
Global Arguments GenHeapGS L V Σ {_ _ _} _ : assert.
Global Arguments gen_heap_name {L V Σ _ _} _ : assert.
Local Existing Instance gen_heap_inG.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (gmap_viewR L (agreeR (leibnizO V)))
].

Global Instance subG_gen_heapGpreS {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapGpreS L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_heapGS L V Σ}.

(*|
These two definitions are the key idea behind the state interpretation.
`gen_heap_interp` is the authoritative element of this RA, which will be the
state interpretation of `σ`, while `mapsto_def` has fragments that live outside
the state interpretation and are owned by threads. `l ↦ v` will be notation for
`mapsto`, with a full 1 fraction.
|*)

(*
  What the paper calls \mathcal{H}(\sigma)

  Note about Leaf: This is forked from iris-simp-lang which uses more traditional Iris fractional
  permissions instead of Leaf's version of fractions. These definitions
  here still use Iris fractions, but we basically don't use any fractions other than 1
  for any of our examples.
*)

  Definition gen_heap_interp (σ : gmap L V) : iProp Σ :=
    ghost_map_auth (gen_heap_name hG) (1) σ.

  Definition mapsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    l ↪[gen_heap_name hG]{dq} v.
  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section gen_heap.
  Context {L V} `{Countable L, !gen_heapGS L V Σ}.
  Implicit Types (P Q : iProp Σ).
  Implicit Types (Φ : V → iProp Σ).
  Implicit Types (σ : gmap L V) (l : L) (v : V).

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l dq v : Timeless (l ↦{dq} v).
  Proof. rewrite mapsto_eq. apply _. Qed.

  Lemma mapsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite mapsto_eq. 
    apply ghost_map_elem_valid_2.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (mapsto_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp mapsto_eq /mapsto_def /=.
    iIntros "Hσ".
    iMod (ghost_map_insert l with "Hσ") as "[Hσ Hl]"; first done.
    iModIntro. iFrame.
  Qed.

  Lemma gen_heap_valid σ l dq v : gen_heap_interp σ -∗ l ↦{dq} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq.
    by iCombine "Hσ Hl" gives %?. 
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp /mapsto_eq.
    rewrite mapsto_eq.
    iCombine "Hσ Hl" gives %Hl.
    iMod (ghost_map_update with "Hσ Hl") as "[Hσ Hl]". 
    iModIntro. iFrame.
  Qed.
  
  Lemma gen_heap_free σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (delete l σ).
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq /mapsto_def.
    iCombine "Hσ Hl" gives %Hl.
    iMod (ghost_map_delete with "Hσ Hl") as "Hσ". 
    iModIntro. iFrame.
  Qed.
End gen_heap.

Lemma gen_heap_init `{Countable L, !gen_heapGpreS L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapGS L V Σ, gen_heap_interp σ.
Proof.
  induction σ as [| l v σ' Hl IH] using map_ind.
  - iMod (ghost_map_alloc_empty (K:=L) (V:=V)) as (γh) "Hh".
    iExists (GenHeapGS _ _ _ γh). iModIntro. iFrame.
  - iIntros. iMod IH as (H0) "T".
    iMod (gen_heap_alloc _ l v with "T") as "[S T]"; trivial.
    iModIntro. iExists H0. iFrame.
Qed.
