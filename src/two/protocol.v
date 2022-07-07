From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

From iris.base_logic.lib Require Export invariants.

From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export fancy_updates_from_vs.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export wsat.

From iris.bi Require Import derived_laws.

Require Import Two.inved.
Require Import Two.guard.

(*
Context {Σ: gFunctors}.
Context `{!invGS Σ}.
*)

Record StorageMixin P B
    `{Equiv P, PCore P, Op P, Valid P, PInv P}
    {equ: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
:= {
    protocol_mixin: ProtocolMixin P;
    base_ra_mixin: RAMixin B; (* completely ignore core *)
    
    interp: P -> B;

    interp_proper: Proper ((≡) ==> (≡)) interp;
    interp_val: ∀ p: P , pinv p -> ✓ interp p;
}. 

Section PropMap.
  Context {Σ: gFunctors}.
  
  Context `{Equiv B, Op B, Valid B, Unit B}.
  
  Definition wf_prop_map (f: B -> iProp Σ) :=
      Proper ((≡) ==> (≡)) f
      /\ f ε ≡ (True)%I
      /\ (∀ a b , ✓(a ⋅ b) -> f (a ⋅ b) ≡ (f a ∗ f b) % I).
      
  
End PropMap.

Section StorageLogic.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{Equiv P, PCore P, Op P, PInv P, Valid P}.
  Context {equ: Equivalence (≡@{P})}.
  Context {equb: Equivalence (≡@{B})}.
  Context {storage_mixin: StorageMixin P B}.
  
  Definition storage_protocol_guards (p: P) (b: B) :=
      ∀ q , pinv (p ⋅ q) -> b ≼ interp P B storage_mixin (p ⋅ q).
  
  Context {Σ: gFunctors}.
  Context `{!inG Σ (authUR (inved_protocolUR (protocol_mixin P B storage_mixin)))}.
  Context `{!invGS Σ}.
  
  Definition maps (γ: gname) (f: B -> iProp Σ) : iProp Σ :=
      ⌜ wf_prop_map f /\ (∃ p: P , True) ⌝ ∗
      ownI γ (
        ∃ (state: P) ,
          own γ (● (Inved state))
          ∗ ⌜ pinv state ⌝
          ∗ (f (interp P B storage_mixin state))
      ). 
  
  Definition p_own (γ: gname) (p: P) : iProp Σ := own γ (◯ (Inved p)).
  
  Lemma ownIagree (γ : gname) (X Y : iProp Σ) : ownI γ X ∗ ownI γ Y ⊢ (▷ X ≡ ▷ Y).
  Admitted.
  
  Lemma and_later_r (X Y : iProp Σ)
      : X ∧ ▷ Y ⊢ ▷ (X ∧ Y). Admitted.
  
  (*Lemma logic_guard_conjunct_fact (γ: gname) (p state: P) (f: B -> iProp Σ)
  : own γ (◯ Inved p)
        ∧ ▷ (own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp P B storage_mixin state))
    ⊢ ⌜ p ≼ state ⌝.
  Proof.
    iIntros "x".
    iDestruct (and_later_r with "x") as "x".
    iMod "x" as "x".*)
  
  Lemma and_timeless (X Y : iProp Σ) (ti: Timeless Y)
      : ⊢ (X ∧ (▷ Y) -∗ ◇ (X ∧ Y)) % I.
  Proof.
    iIntros "r". unfold Timeless in ti.
    rewrite bi.except_0_and.
    iSplit. { iDestruct "r" as "[r _]". iModIntro. iFrame. }
    iDestruct "r" as "[_ r]".  iDestruct (ti with "r") as "r". iFrame.
  Qed.
  
  Lemma and_timeless2 (X Y : iProp Σ) (ti: Timeless Y)
      : ⊢ (X ∧ (▷ Y) ={∅}=∗ (X ∧ Y)) % I.
  Proof.
    iIntros "x".  iMod (and_timeless with "x") as "x". iModIntro. iFrame.
  Qed.
  
  Lemma apply_timeless (X Y Z W V : iProp Σ) (ti: Timeless Z) (ti2: Timeless W)
      : X ∧ (Y ∗ ▷ (Z ∗ W ∗ V)) -∗ ◇ (X ∧ (Y ∗ Z ∗ W ∗ ▷ (V))).
      Admitted.
      
  Lemma stuff1 (X Y Z W V : iProp Σ)
      : (X ∧ (Y ∗ Z ∗ W ∗ V)) ⊢ W. Admitted.
      
  Lemma stuff2 (γ: gname) (p state: P) (T W: iProp Σ)
      : own γ (◯ Inved p) ∧ (T ∗ own γ (● Inved state) ∗ W)
          ⊢ ⌜ p ≼ state ⌝. Admitted.
  
  Lemma logic_guard (p: P) (b: B) (γ: gname) (f: B -> iProp Σ)
    (g: storage_protocol_guards p b)
    : maps γ f ⊢ (p_own γ p &&{ {[ γ ]} }&&> ▷ f b).
  Proof.
    unfold guards, guards_with, maps.
    iIntros "[%wf #inv]".
    destruct wf as [wf exists_p].
    iIntros (T) "[po b]".
    rewrite storage_bulk_inv_singleton. unfold storage_inv.
    unfold p_own.
    iAssert ((own γ (◯ Inved p) ∧
        (∃ state : P, T ∗ ▷
               (own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp P B storage_mixin state))))%I)
        with "[po b]" as "x".
    { iSplit. { iFrame. } 
      iDestruct ("b" with "po") as "[ex t]".
      iDestruct "ex" as (P0) "[#own lat]".
      iDestruct (ownIagree γ P0 _ with "[inv own]") as "eq".
      { iSplitL. { iFrame "own". } iFrame "inv". }
      iRewrite "eq" in "lat".
      iDestruct (bi.later_exist with "lat") as (state) "lat".
      iExists state. iFrame.
    }
    rewrite bi.and_exist_l.
    iDestruct "x" as (state) "x".
    iMod (apply_timeless with "x") as "x".
    iDestruct (stuff1 with "x") as "%pinvs".
    iDestruct (stuff2 with "x") as "%incll".
    iDestruct "x" as "[_ [t [o [p latf]]]]".
    
    unfold storage_protocol_guards in g.
    unfold "≼" in incll. destruct incll as [z incll].
    assert (pinv (p ⋅ z)) as pinv_pz.
        { destruct storage_mixin. destruct protocol_mixin0. setoid_rewrite <- incll. trivial. }
    have gz := g z pinv_pz.
    unfold "≼" in gz. destruct gz as [y gz].
    assert (interp P B storage_mixin state ≡ b ⋅ y) as ieqop.
    { destruct storage_mixin. unfold interp. 
        setoid_rewrite incll. trivial. }
    
    unfold wf_prop_map in wf.
    destruct wf as [fprop [funit fop]].
    
    assert (✓ (b ⋅ y)) as is_val.
    { destruct storage_mixin. destruct base_ra_mixin0.
        setoid_rewrite <- ieqop. apply interp_val0. trivial. }
        
    setoid_rewrite ieqop.
    setoid_rewrite fop; trivial.
    
    rewrite bi.later_sep. 
    iDestruct "latf" as "[fb fy]".
    iModIntro.
    iFrame "fb".
    iIntros "fb".
    iFrame "t".
    iExists ((∃ state0 : P,
              own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp P B storage_mixin state0))%I).
    iFrame "inv".
    iNext. iExists state. iFrame.
    setoid_rewrite ieqop. setoid_rewrite fop; trivial. iFrame.
    
    Unshelve.
    apply inhabits.
    apply exists_inhabited.
    apply inhabitant.
      
      

Print own.
    
  
End Storage.
