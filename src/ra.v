From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates.
From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.gmap_utils.
Require Import Burrow.tactics.
Require Import Burrow.locations.
Require Import Burrow.rollup.
Require Import Burrow.tpcms.
Require Import Burrow.resource_proofs.
Require Import coq_tricks.Deex.

Global Instance state_pcore (𝜇 : BurrowCtx)
      : PCore (BurrowState 𝜇) := λ state , Some state_unit.

Definition burrow_ra_mixin (𝜇: BurrowCtx)
    : RAMixin (BurrowState 𝜇).
Proof. split.
  - typeclasses eauto.
  - unfold pcore. unfold state_pcore. intros. exists cx. split; trivial.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - unfold pcore. unfold state_pcore. intros.
      inversion H.
      setoid_rewrite state_comm.
      apply op_state_unit.
  - unfold pcore. unfold state_pcore. intros. rewrite H. unfold "≡", option_equiv.
      apply Some_Forall2. trivial.
  - intros. exists state_unit. split.
    + unfold pcore. unfold state_pcore. trivial.
    + unfold "≼". exists state_unit. unfold pcore, state_pcore in H0.
        assert (cx = state_unit) by crush. rewrite H1.
        setoid_rewrite op_state_unit. trivial.
  - intros. unfold "✓", state_valid in *.
      deex. exists (y ⋅ p). setoid_rewrite state_assoc. trivial.
Defined.

Global Instance State_equivalence
    (𝜇: BurrowCtx)
  : Equivalence (≡@{BurrowState 𝜇}).
Proof. split; typeclasses eauto. Defined.

Canonical Structure burrowO
    (𝜇: BurrowCtx)
  := discreteO (BurrowState 𝜇).

Canonical Structure burrowR
    (𝜇: BurrowCtx)
    := discreteR (BurrowState 𝜇) (burrow_ra_mixin 𝜇).
    
Context {𝜇: BurrowCtx}.
    
Class gen_burrowGpreS (Σ : gFunctors) := {
  gen_burrowGpreS_inG :> inG Σ (burrowR 𝜇);
}.

Class gen_burrowGS (Σ : gFunctors) := GenBurrowGS {
  gen_burrow_inG :> gen_burrowGpreS Σ;
  gen_burrow_name : gname;
}.
Global Arguments GenBurrowGS Σ {_} _ : assert.
Global Arguments gen_burrow_name {Σ} _ : assert.

Definition gen_burrowΣ : gFunctors := #[
  GFunctor (burrowR 𝜇)
].

Global Instance subG_gen_burrowGpreS {Σ} :
  subG (gen_burrowΣ) Σ → gen_burrowGpreS Σ.
Proof. solve_inG. Qed.

Context `{hG : !gen_burrowGS Σ}.

Definition L
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (m: M) : iProp Σ
    := own (gen_burrow_name hG) (live' 𝛾 m).
    
Definition R
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝜅: Lifetime) (𝛾: BurrowLoc 𝜇) (m: M) : iProp Σ
    := own (gen_burrow_name hG) (reserved' 𝜅 𝛾 m) ∧ ⌜ 𝜅 ≠ empty_lifetime ⌝.
    
Definition B
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝜅: Lifetime) (𝛾: BurrowLoc 𝜇) (m: M) : iProp Σ
    := ∃ rstate ,
        own (gen_burrow_name hG) rstate ∧
        ⌜ is_borrow' 𝜅 𝛾 m rstate /\ state_no_live rstate ⌝.

Definition A (𝜅: Lifetime) : iProp Σ
    := own (gen_burrow_name hG) (active 𝜅 : BurrowState 𝜇).

Global Instance burrow_cmra_discrete : CmraDiscrete (burrowR 𝜇).
Proof. apply discrete_cmra_discrete. Qed.

Global Instance burrow_cmra_total : CmraTotal (burrowR 𝜇).
Proof. unfold CmraTotal. intros. unfold pcore, cmra_pcore, burrowR, state_pcore.
  unfold is_Some. exists state_unit. trivial.
Qed.

Lemma BorrowExpire
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝜅: Lifetime) (𝛾: BurrowLoc 𝜇) (m: M)
  : A 𝜅 ∗ R 𝜅 𝛾 m ==∗ L 𝛾 m.
Proof. unfold A, R, L.
  iIntros "[H1 [H2 %H3]]". 
  iCombine "H1" "H2" as "H".
  iMod (own_update (gen_burrow_name hG) ((active 𝜅: BurrowState 𝜇) ⋅ reserved' 𝜅 𝛾 m) (live' 𝛾 m) with "H") as "$".
  - have h := cmra_discrete_update.
    rewrite cmra_discrete_update.
    intro. apply borrow_expire. trivial.
  - done.
Qed.
