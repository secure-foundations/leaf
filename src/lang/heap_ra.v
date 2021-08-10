From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Require Import Burrow.ra.
Require Import Burrow.tpcms.
Require Import Burrow.rollup.

Require Import Tpcms.auth_frag.
Require Import Tpcms.gmap.
Require Import Tpcms.heap.

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

Class gen_heapGpreS (P V : Type) (𝜇: BurrowCtx) (Σ : gFunctors) `{!EqDecision P} `{!Countable P} `{!EqDecision V} := {
  gen_burrow_pre_inG :> @gen_burrowGpreS 𝜇 Σ;
  gen_heapGpreS_HasTPCM :> HasTPCM 𝜇 (AuthFrag (gmap P (option V)));
}.

Class gen_heapGS (P V : Type) (𝜇: BurrowCtx) (Σ : gFunctors) `{!EqDecision P} `{!Countable P} `{!EqDecision V} := GenHeapGS {
  (*gen_heap_inG :> gen_heapGpreS P V 𝜇 Σ;*)
  gen_burrow_inG :> @gen_burrowGS 𝜇 Σ;
  gen_heapGS_HasTPCM :> HasTPCM 𝜇 (AuthFrag (gmap P (option V)));
  gen_heap_name : BurrowLoc 𝜇;
}.
Global Arguments GenHeapGS P V 𝜇 Σ {_ _ _ _ _} _ : assert.
Global Arguments gen_heap_name {P V 𝜇 Σ _ _ _} _ : assert.

Definition gen_heapΣ (P V : Type) (𝜇: BurrowCtx) `{Countable P} `{EqDecision V}
    `{HasTPCM 𝜇 (AuthFrag (gmap P (option V)))}
    : gFunctors := #[
  @gen_burrowΣ 𝜇
].

Global Instance subG_gen_heapGpreS {𝜇 Σ P V} `{Countable P} `{EqDecision V}
    `{!HasTPCM 𝜇 (AuthFrag (gmap P (option V)))} :
  subG (gen_heapΣ P V 𝜇) Σ → gen_heapGpreS P V 𝜇 Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!EqDecision V, Countable P, hG : !gen_heapGS P V 𝜇 Σ}.

(*|
These two definitions are the key idea behind the state interpretation.
`gen_heap_interp` is the authoritative element of this RA, which will be the
state interpretation of `σ`, while `mapsto_def` has fragments that live outside
the state interpretation and are owned by threads. `l ↦ v` will be notation for
`mapsto`, with a full 1 fraction.
|*)

  Definition gen_heap_interp (σ : gmap P V) : iProp Σ :=
    L (gen_heap_name hG) (auth (map_somes σ)).
    
  Definition cmapsto_def (p : P) (v: V) : HeapT P V :=
    frag ({[ p := Some v ]} : gmap P (option V)).
    
  Definition cmapsto_aux : seal (@cmapsto_def). Proof. by eexists. Qed.
  Definition cmapsto := cmapsto_aux.(unseal).
  Definition cmapsto_eq : @cmapsto = @cmapsto_def := cmapsto_aux.(seal_eq).
  
End definitions.

Notation "p $↦ v" := (cmapsto p v)
  (at level 20, format "p  $↦  v").
  
Section definitions2.
  Context `{!EqDecision V, Countable P, hG : !gen_heapGS P V 𝜇 Σ}.
  
  Definition mapsto (p: P) (v: V) := L (gen_heap_name hG) (p $↦ v).
  Definition bmapsto (𝜅: Lifetime) (p: P) (v: V) := B 𝜅 (gen_heap_name hG) (p $↦ v).
End definitions2.

Notation "p ↦ v" := (mapsto p v)
  (at level 20, format "p  ↦  v") : bi_scope.
Notation "p &{ k }↦ v" := (bmapsto k p v)
  (at level 20, format "p  &{ k }↦  v") : bi_scope.

Section gen_heap.
  Context {P V} `{!EqDecision V} `{Countable P, !gen_heapGS P V 𝜇 Σ}.
  Implicit Types (P Q : iProp Σ).
  Implicit Types (Φ : V → iProp Σ).
  Implicit Types (σ : gmap P V) (l : P) (v : V).

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l v : Timeless (l ↦ v).
  Proof. unfold mapsto. rewrite cmapsto_eq. apply _. Qed.

  (*
  Lemma mapsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite mapsto_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%gmap_view_frag_op_valid_P.
    auto.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (mapsto_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.
  *)

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp /mapsto cmapsto_eq /cmapsto_def /=.
    iIntros "Hσ".
    rewrite <- L_op.
    iMod (FrameUpdate _ _
        (dot (auth (map_somes (<[l:=v]> σ))) (frag {[l := Some v]}))
    with "Hσ") as "Hσ".
    - rewrite map_somes_insert. apply heapt_alloc.
        rewrite lookup_fmap. unfold "<$>", option_fmap, option_map. rewrite Hσl. trivial.
    - iModIntro. iFrame.
  Qed.

  Lemma gen_heap_valid σ l v : gen_heap_interp σ -∗ l ↦ v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp /mapsto cmapsto_eq.
    iDestruct (LiveValid_2 with "Hσ Hl") as "%va".
    iPureIntro.
    unfold cmapsto_def in va.
    apply auth_frag_agree with (EqDecision0 := EqDecision0). trivial.
  Qed.
  
  Lemma gen_heap_valid_borrow σ 𝜅 l v : gen_heap_interp σ -∗ A 𝜅 -∗ l &{𝜅}↦ v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ A Hl".
    rewrite /gen_heap_interp /bmapsto cmapsto_eq.
    iDestruct (LiveAndBorrowValid with "A Hσ Hl") as "%va".
    iPureIntro.
    unfold cmapsto_def in va.
    apply auth_frag_agree with (EqDecision0 := EqDecision0). trivial.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl".
    iDestruct (gen_heap_valid with "Hσ Hl") as "%va".
    rewrite /gen_heap_interp /mapsto cmapsto_eq /cmapsto_def.
    iDestruct (L_join with "Hσ Hl") as "H".
    iMod (FrameUpdate _ _ (
      dot (auth (map_somes (<[l:=v2]> σ))) (frag {[l := Some v2]})  
    ) with "H") as "H".
    - apply auth_frag_update. trivial.
    - rewrite L_op. iModIntro. iFrame.
  Qed.
End gen_heap.

Lemma gen_heap_init `{EqDecision V, Countable P, !gen_heapGpreS P V 𝜇 Σ} σ :
  ⊢ |==> ∃ _ : gen_heapGS P V 𝜇 Σ, gen_heap_interp σ.
Proof.
  iIntros.
  iMod (gen_burrow_init) as (gb) "gbi".
  iMod (InitializeNormal (auth (map_somes σ))) as (𝛾) "H".
  - apply auth_map_somes.
  - iExists (GenHeapGS P V 𝜇 Σ 𝛾).
    unfold gen_heap_interp. unfold gen_heap_name. iModIntro. done.
Qed.
