From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From lang Require Import notation tactics class_instances.
From lang Require Import heap_ra.
From iris Require Import options.
Require Import guarding.guard.

(*|
This is one of the most interesting parts of the instantiation. Now that we have
a syntax and semantics, we want a program logic. There's exactly one more thing
Iris needs before we can define weakest preconditions: a **state
interpretation**. This is a function from state (recall, just a heap for
simp_lang) to iProp Σ. The way this plugs into Iris is by instantiating the
`irisGS simp_lang Σ` typeclass, which is an assumption for `wp`, the generic
definition of weakest preconditions (this is the definition you usually interact
with through either the `WP` notation or "Texan" Hoare-triple notation).

The state interpretation for simp_lang maps `gmap loc val` into an appropriate
RA. Most of the definition is related to `gen_heapG`, which is defined in
`heap_ra.v`. We can think of the state interpretation as being an invariant
maintained by the weakest precondition, except that it is a function of the
state and thus has meaning tied to the program execution. Therefore we pick an
RA which is like an auth of a gmap for the state interpretation and map `σ :
gmap loc val` to something like `own γ (●σ)`. Then we can use fragments to
define the core points-to connective for this language, something like `l ↦ v :=
own γ (◯{|l := v|})`.

When we prove the WP for an atomic language primitive, we'll prove it more
directly than usual. The proof obligation will be to transform the state
interpretation of `σ` to the state interpretation of some `σ'` that's a valid
transition of the primitive. It's here that we'll **update the ghost state** to
match transitions like allocation and use agreement between the auth and
fragments to prove the WP for loads, for example. These are the most interesting
proofs about the language because they don't just reason about pure reduction
steps but actually have to make use of the logic and the ghost state we set up
to reason about its state --- the purely functional part of the language clearly
doesn't need separation logic!

The code implements this with two differences. First, the RA we actually use in
`heap_ra.` is an Iris library `gmap_viewR loc val` which uses a generalization
of auth called views. The important point is that the auth component is the
state's heap and the fragments are sub-heaps; the view RA keeps track of the
fact that the composition of all the fragments is a sub-heap of the
authoritative element. It also adds something called discardable fractions, a
generalization of the fraction RA, in order to model fractional and persistent
permissions to heap locations, but we can mostly ignore this complication.

Second, there's a pesky ghost name `γ` in the informal definitions above. These
are hidden away in the `simpGS` typeclass as part of `gen_heapG` that all proofs
about this language will carry. It'll be fixed once before any execution by the
adequacy theorem, as you'll see in adequacy.v. After that we get it through a
typeclass to avoid mentioning it explicitly in any proofs.

If you were writing your own language, you would probably start with `gen_heapG`
from the Iris standard library to get all the nice features and lemmas for the
heap part of the state interpretation. Then you could add other algebras and
global ghost names to the equivalent of `simpGS`, as long as you also instantiate
them in `adequacy.v`.
|*)


Class simpGS Σ := SimpGS {
  simp_invG : invGS Σ;
  #[global] simp_gen_heapG :: gen_heapGS loc val Σ;
}.

(* Observe that this instance assumes [simpGS Σ], which already has a fixed ghost
name for the heap ghost state. We'll see in adequacy.v how to obtain a [simpGS Σ]
after allocating that ghost state. *)
Global Instance simpG_irisG `{!simpGS Σ} : irisGS simp_lang Σ := {
  iris_invGS := simp_invG;
  state_interp σ _ κs _ := (gen_heap_interp σ.(heap))%I;
  fork_post _ := True%I;
  (* These two fields are for a new feature that makes the number of laters per
  physical step flexible; picking 0 here means we get just one later per
  physical step, as older versions of Iris had. This is the same way heap_lang
  works. *)
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section lifting.
Context `{!simpGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 κ κs n nt) "Hσ !>"; iSplit; first by eauto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep); inv_head_step. iIntros. by iFrame.
Qed.

(** Heap *)

(* Heap-Ref *)

Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E
  {{{ l, RET LitV (LitInt l); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 κ κs n nt) "Hσ !>"; iSplit; first by auto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_alloc σ1.(heap) l v with "Hσ") as "[Hσ Hl]"; first done.
  iIntros. iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* Heap-Free *)

Lemma wp_free s E l v :
  {{{ l ↦ v }}} Free (Val $ LitV $ LitInt l) @ s; E
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 κ κs n nt) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_free _ _ _ v with "Hσ Hl") as "Hσ".
  iIntros. iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* Heap-Read *)

Lemma wp_load s E l dq v :
  {{{ l ↦{dq} v }}} Load (Val $ LitV $ LitInt l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 κ κs n nt) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iIntros. iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* Heap-Read-Shared *)

Lemma wp_load_b s E l v F g (su: F ⊆ E) :
  {{{ g ∗ (g &&{F}&&> (l ↦ v)) }}} Load (Val $ LitV $ LitInt l) @ s; E {{{ RET v; g }}}.
Proof.
  iIntros (Φ) "[g Hl] HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 κ κs n nt) "Hσ". (*"Hσ !>".*)
  
  iMod (guards_extract_persistent2
      (state_interp σ1 κ (κs ++ n) nt)
      g (l ↦ v) (⌜ (heap σ1) !! l = Some v ⌝) E F with "[Hσ g Hl]") as "[Hσ [g %j]]".
  { trivial. }
  { iFrame. iIntros "[Hσ Hl]".
    iDestruct (gen_heap_valid with "Hσ Hl") as %?.
    iPureIntro. trivial.
  }
  
  iModIntro.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iIntros. iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* Heap-Write *)

Lemma wp_store s E l v w :
  {{{ l ↦ v }}} Store (Val $ LitV $ LitInt l) (Val $ w) @ s; E {{{ RET #(); l ↦ w }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 κ κs n nt) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update _ _ _ w with "Hσ Hl") as "[Hσ Hl]".
  iIntros. iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* Heap-FetchAdd *)

Lemma wp_faa s E l (n1 n2: Z) :
  {{{ l ↦ #n1 }}}
    FAA (Val $ LitV $ LitInt l) (Val $ LitV $ LitInt $ n2) @ s; E
  {{{ RET #n1; l ↦ #(n1+n2) }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 κ κs n nt) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update _ _ _ #(n1 + n2) with "Hσ Hl") as "[Hσ Hl]".
  iIntros. iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas s E l (v_actual v_old v_new: base_lit) :
  {{{ l ↦ (LitV v_actual) }}}
    CAS (Val $ LitV $ LitInt l) (Val $ LitV $ v_old) (Val $ LitV $ v_new) @ s; E
  {{{ RET (LitV $ LitBool (bool_decide (v_actual = v_old))) ;
      l ↦ (LitV (if decide (v_actual = v_old) then v_new else v_actual)) }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; first done.
  iIntros (σ1 κ κs n nt) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update _ _ _ (LitV (if decide (v_actual = v_old) then v_new else v_actual)) with "Hσ Hl") as "[Hσ Hl]".
  iIntros. iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

(* Heap-CAS-True *)

Lemma wp_cas_eq s E l (v_actual v_new: base_lit) :
  {{{ l ↦ (LitV v_actual) }}}
    CAS (Val $ LitV $ LitInt l) (Val $ LitV $ v_actual) (Val $ LitV $ v_new) @ s; E
  {{{ RET (LitV $ LitBool true) ;
      l ↦ (LitV v_new) }}}.
Proof.
  have j := wp_cas s E l v_actual v_actual v_new.
  case_decide.
  - assert (bool_decide (v_actual = v_actual) = true) as X.
     ** unfold bool_decide. case_decide; trivial. contradiction.
     ** rewrite X in j. trivial.
  - contradiction.
Qed.

(* Heap-CAS-False *)

Lemma wp_cas_ne s E l (v_actual v_old v_new: base_lit)
  (ne: v_actual ≠ v_old) :
  {{{ l ↦ (LitV v_actual) }}}
    CAS (Val $ LitV $ LitInt l) (Val $ LitV $ v_old) (Val $ LitV $ v_new) @ s; E
  {{{ RET (LitV $ LitBool false) ;
      l ↦ (LitV v_actual) }}}.
Proof.
  have j := wp_cas s E l v_actual v_old v_new.
  case_decide.
  - contradiction.
  - assert (bool_decide (v_actual = v_old) = false) as X.
     ** unfold bool_decide. case_decide; trivial. contradiction.
     ** rewrite X in j. trivial.
Qed.

End lifting.
