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

Global Instance burrow_unit 𝜇 : Unit (BurrowState 𝜇) := state_unit.
Lemma burrow_ucmra_mixin 𝜇 : UcmraMixin (BurrowState 𝜇).
Proof. split. Admitted.
Canonical Structure burrowUR 𝜇 : ucmra := Ucmra (BurrowState 𝜇) (burrow_ucmra_mixin 𝜇).
    
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

Lemma L_op
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (m n: M)
  : L 𝛾 (dot m n) ⊣⊢ L 𝛾 m ∗ L 𝛾 n.
Proof.
  unfold L.
  setoid_rewrite <- live_dot_live'.
  apply own_op.
Qed.

Lemma L_unit
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    𝛾
  : ⊢ |==> L 𝛾 (unit: M).
Proof.
  unfold L. setoid_rewrite live_unit'. apply own_unit.
Qed.

Lemma LiveAndBorrowValid
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (𝜅: Lifetime) (m k : M)
  : A 𝜅 ∗ L 𝛾 m ∗ B 𝜅 𝛾 k ⊢ ⌜ m_valid (dot m k) ⌝.
Proof.
  unfold A, L, B.
  iIntros "[H1 [H2 H3]]".
  iDestruct "H3" as (rstate) "[H4 %H5]".
  iDestruct (own_valid_3 with "H1 H2 H4") as "%H". 
  iPureIntro.
  destruct_ands.
  apply (live_and_borrow_implies_valid' _ _ _ _ _ H0 H).
Qed.

Lemma BorrowBegin_1
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (m : M)
     : L 𝛾 m ==∗ (∃ 𝜅 , A 𝜅 ∗ R 𝜅 𝛾 m).
Proof.
  iIntros "L". unfold L, A, R.
  iMod (own_updateP (λ a': BurrowState 𝜇, ∃ 𝜅 , a' = active 𝜅 ⋅ reserved' 𝜅 𝛾 m /\ 𝜅 ≠ empty_lifetime) with "L") as "T".
   - rewrite cmra_discrete_updateP.
      intros.
      have j := borrow_begin' 𝛾 m z H. deex.
      exists (active 𝜅 ⋅ reserved' 𝜅 𝛾 m). destruct_ands.
      split; trivial. exists 𝜅. split; trivial.
   - iDestruct "T" as (a') "[%E T]".
      deex. destruct_ands. subst a'.
      iModIntro. iExists 𝜅. 
      rewrite own_op. iDestruct "T" as "[Q R]". iFrame.
      iPureIntro. trivial.
Qed.

Lemma DupeR
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (𝜅: Lifetime) (m : M)
     : R 𝜅 𝛾 m ⊣⊢ R 𝜅 𝛾 m ∗ R 𝜅 𝛾 m.
Proof.
  unfold R.
  have h := state_no_live_reserved' 𝜅 𝛾 m.
  have h' := h EqDecision0 TPCM0 HasTPCM0.
  have j := no_live_duplicable (reserved' 𝜅 𝛾 m) h'.
  iIntros. iSplit.
    - iIntros "[T %ne]".
      pattern (own (gen_burrow_name hG) (reserved' 𝜅 𝛾 m)) at 2.
      pattern (own (gen_burrow_name hG) (reserved' 𝜅 𝛾 m)) at 2.
      setoid_rewrite <- j.
      rewrite own_op.
      iDestruct "T" as "[Q R]".
      iFrame.
      iSplit; iPureIntro; trivial.
    - iIntros "[Q R]". iFrame.
Qed.

Lemma R_to_B
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (𝜅: Lifetime) (m : M)
     : R 𝜅 𝛾 m ⊢ B 𝜅 𝛾 m.
Proof.
  unfold R, B.
  iIntros "[T %ne]".
  iExists (reserved' 𝜅 𝛾 m).
  iFrame. iPureIntro. split.
  - apply is_borrow_reserved'.
  - apply state_no_live_reserved'.
Qed.
  
Lemma BorrowBegin
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (m : M)
     : L 𝛾 m ==∗ (∃ 𝜅 , A 𝜅 ∗ R 𝜅 𝛾 m ∗ B 𝜅 𝛾 m).
Proof.
  unfold L, A, R, B.
  iIntros "T".
  iMod (BorrowBegin_1 with "T") as (𝜅) "[X Y]".
  rewrite DupeR. 
  iDestruct "Y" as "[Y Z]".
  iDestruct (R_to_B with "Z") as "Z".
  iModIntro. iExists 𝜅. iFrame.
Qed.

Lemma BorrowExpire
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝜅: Lifetime) (𝛾: BurrowLoc 𝜇) (m: M)
  : A 𝜅 ∗ R 𝜅 𝛾 m ==∗ L 𝛾 m.
Proof. unfold A, R, L.
  iIntros "[H1 [H2 %H3]]". 
  iCombine "H1" "H2" as "H".
  iMod (own_update (gen_burrow_name hG) ((active 𝜅: BurrowState 𝜇) ⋅ reserved' 𝜅 𝛾 m) (live' 𝛾 m) with "H") as "$".
  - rewrite cmra_discrete_update.
    intro. apply borrow_expire'. trivial.
  - done.
Qed.

Lemma DupeB
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (𝜅: Lifetime) (m : M)
     : B 𝜅 𝛾 m ⊢ B 𝜅 𝛾 m ∗ B 𝜅 𝛾 m.
Proof.
  unfold B.
  (*have h := state_no_live_reserved' 𝜅 𝛾 m.
  have h' := h EqDecision0 TPCM0 HasTPCM0.
  have j := no_live_duplicable (reserved' 𝜅 𝛾 m) h'.*)
  iIntros "T".
    - iDestruct "T" as (rstate) "[T %h]". destruct_ands.
      rewrite <- no_live_duplicable; trivial.
      rewrite own_op.
      iDestruct "T" as "[S T]".
      iSplitL "S".
      + iExists rstate. iFrame. iPureIntro. split; trivial.
      + iExists rstate. iFrame. iPureIntro. split; trivial.
Qed.

Lemma BorrowLifetimeInclusion
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    𝜅 𝜅' 𝛾 (m: M) (state: BurrowState 𝜇)
    (li: lifetime_included 𝜅' 𝜅)
    : B 𝜅 𝛾 m ⊢ B 𝜅' 𝛾 m.
Proof. iIntros "T". unfold B.
  iDestruct "T" as (rstate) ["[T %h]"]. destruct_ands.
  iExists rstate. iFrame. iPureIntro. split; trivial.
  apply borrow_lifetime_inclusion' with (𝜅0:=𝜅); trivial.
Qed.

Lemma BorrowCombine
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    𝜅 𝛾 (a b c: M)
    (abcr: ∀ r , m_valid r -> tpcm_le a r -> tpcm_le b r -> tpcm_le c r)
    : B 𝜅 𝛾 a ∗ B 𝜅 𝛾 b ⊢ B 𝜅 𝛾 c.
Proof.
 unfold B.
 iIntros "[S T]".
  iDestruct "S" as (rstate1) ["[S %h]"]. destruct_ands.
  iDestruct "T" as (rstate2) ["[T %h]"]. destruct_ands.
  iCombine "S" "T" as "S".
  iExists (rstate1 ⋅ rstate2). iFrame. iPureIntro. split.
   - apply borrow_nonseparating_conjunction' with (a0:=a) (b0:=b); trivial.
   - apply no_live_op; trivial.
Qed.

Lemma BorrowBack
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {R} `{!EqDecision R} `{!TPCM R} `{!HasTPCM 𝜇 R}
    (ref: Refinement R M) `{hr: !HasRef 𝜇 ref}
    𝛼 𝛾 f m 𝜅
    (bbcond : ∀ p: R, rel_defined R M ref (dot f p) ->
        tpcm_le m (rel R M ref (dot f p)))
    : B 𝜅 (extend_loc 𝛼 ref 𝛾) f ⊢ B 𝜅 𝛾 m.
Proof. iIntros "T". unfold B.
  iDestruct "T" as (rstate) ["[T %h]"]. destruct_ands.
  iExists rstate. iFrame. iPureIntro. split; trivial.
  apply borrow_back' with (ref0 := ref) (hr0 := hr) (𝛼0 := 𝛼) (f0 := f); trivial.
Qed.

Lemma BorrowBackLeft
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {N} `{!EqDecision N} `{!TPCM N} `{!HasTPCM 𝜇 N}
  (𝛾1 𝛾2 : BurrowLoc 𝜇) (m1 : M) (m2 : N) 𝜅
  : B 𝜅 (cross_loc 𝛾1 𝛾2) (m1, m2) ⊢ B 𝜅 𝛾1 m1.
Proof. iIntros "T". unfold B.
  iDestruct "T" as (rstate) ["[T %h]"]. destruct_ands.
  iExists rstate. iFrame. iPureIntro. split; trivial.
  apply borrow_back_left' with (𝛾4:=𝛾2) (m4:=m2); trivial.
Qed.

Lemma BorrowBackRight
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {N} `{!EqDecision N} `{!TPCM N} `{!HasTPCM 𝜇 N}
  (𝛾1 𝛾2 : BurrowLoc 𝜇) (m1 : M) (m2 : N) 𝜅
  : B 𝜅 (cross_loc 𝛾1 𝛾2) (m1, m2) ⊢ B 𝜅 𝛾2 m2.
Proof. iIntros "T". unfold B.
  iDestruct "T" as (rstate) ["[T %h]"]. destruct_ands.
  iExists rstate. iFrame. iPureIntro. split; trivial.
  apply borrow_back_right' with (𝛾3:=𝛾1) (m3:=m1); trivial.
Qed.

Lemma FrameUpdateWithBorrow
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    𝜅 𝛾 (m z m' : M)
    (exchange_cond: mov (dot m z) (dot m' z))
    : A 𝜅 -∗ L 𝛾 m -∗ B 𝜅 𝛾 z ==∗ A 𝜅 ∗ L 𝛾 m' ∗ B 𝜅 𝛾 z.
Proof.
  iIntros "A L B".
  unfold A, L, B.
  iDestruct "B" as (rstate) "[B %h]". destruct_ands.
  iMod (own_update_3 _ _ _ _ (
    ((active 𝜅 : BurrowState 𝜇) ⋅ live' 𝛾 m' ⋅ rstate)
  ) with "A L B") as "X".
  - rewrite cmra_discrete_update.
    intros. apply borrow_exchange_normal' with (m0:=m) (z1:=z); trivial.
  - rewrite own_op. rewrite own_op. iDestruct "X" as "[[A L] B]".
    iModIntro. iFrame. iExists rstate. iFrame. iPureIntro. split; trivial.
Qed.

Lemma FrameUpdate
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    𝛾 (m m' : M)
    (exchange_cond: mov m m')
    : L 𝛾 m ==∗ L 𝛾 m'.
Proof.
  iIntros "L".
  iMod (L_unit 𝛾) as "U".
  iMod (BorrowBegin with "U") as (𝜅) "[A [R B]]".
  iMod (FrameUpdateWithBorrow 𝜅 𝛾 m unit m' with "A L B") as "[A [L B]]".
  - repeat (rewrite unit_dot). trivial.
  - iFrame. done.
Qed.
