From iris.program_logic Require Export adequacy.
From BurrowLang Require Import simp heap_ra.
From iris.prelude Require Import options.

Require Import Tpcms.auth_frag.
Require Import Tpcms.gmap.
Require Import Tpcms.heap.
Require Import Burrow.ra.
Require Import Burrow.tpcms.

(*|
===========
Adequacy
===========

This is a really important part of setting up the language. The infrastructure
we've set up will let us prove specifications in Iris for simp_lang, but what do
these theorems mean? This file proves **adequacy** of the weakest preconditions,
which lifts a weakest precondition from within separation logic to a safety
theorem about the semantics that's independent of Iris.

Most of this is proven already for the generic weakest precondition definition
we're using. Only one thing is missing: we need to initialize the state
interpretation for the initial state. This gets to execute a ghost update, which
we use to create the initial auth element for the heap_ra ghost state.

The Coq implementation mostly consists of an orthogonal problem related to these
Σ and related assumptions we make all over the place; if you want the details
you should read
https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md,
but here is a brief explanation. This argument is a list of RA functors and
determine which ghost state is available in an Iris proof (this is needed to
support impredicative ghost state, that is ghost state that refers to other
ghost state). The simpGS assumption over Σ not only assumes that some RAs are
available but also bundles a ghost name for the heap. Here, we allocate that
ghost name and associated state.
|*)

(** These assumptions are just functors in Σ, unlike simpGS which also has a
ghost name. *)
Class simpGpreS 𝜇 Σ `{!HasTPCM 𝜇 (AuthFrag (gmap loc (option val)))} := SimpPreG {
  simp_preG_iris :> invGpreS Σ;
  simp_preG_heap :> gen_heapGpreS loc val 𝜇 Σ;
}.

Definition simpΣ 𝜇 `{!HasTPCM 𝜇 (AuthFrag (gmap loc (option val)))} : gFunctors :=
  #[invΣ; gen_heapΣ loc val 𝜇].

Global Instance subG_heapGpreS {𝜇} `{!HasTPCM 𝜇 (AuthFrag (gmap loc (option val)))} {Σ}
    : subG (simpΣ 𝜇) Σ → simpGpreS 𝜇 Σ.
Proof. solve_inG. Qed.

Definition simp_adequacy Σ
            {𝜇} `{!HasTPCM 𝜇 (AuthFrag (gmap loc (option val)))}
            `{!simpGpreS 𝜇 Σ}
           (s: stuckness) (e: expr) (σ: state) (φ: val → Prop) :
  (∀ (simpGS0: simpGS 𝜇 Σ), ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ (v: val) _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iModIntro. iExists
    (λ σ κs, (gen_heap_interp σ.(heap))%I),
    (λ _, True%I).
  iFrame. iApply (Hwp (SimpGS _ _ _ _ _)).
Qed.

(*|
The thing to observe in the adequacy theorem's statement is that we assume
`simpGpreS Σ` (these are just ordinary functors, which we'll get by including
`simpΣ` in our definition of Σ) and then pass a `simpGS Σ` to a WP proof (this is
higher-order, so you have to carefully follow the positive and negative
occurrences). This is possible because `wp_adequacy` permits us to execute any
initial ghost updates to create the first state interpretation.
|*)
