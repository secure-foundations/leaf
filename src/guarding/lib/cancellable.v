Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

Class ecInv_logicG Σ := { ecInv_exclG : inG Σ (exclR unitO) }.
Local Existing Instance ecInv_exclG. 
  
Definition ecInv_logicΣ : gFunctors := #[ GFunctor (exclR unitO) ].

Global Instance subG_ecInv_logicΣ Σ : subG ecInv_logicΣ Σ → ecInv_logicG Σ.
Proof.
  solve_inG.
Qed.  

Section CancellableInvariants.

  Context {Σ: gFunctors}.
  Context `{!ecInv_logicG Σ}.
  Context `{!invGS_gen hlc Σ}.

  Definition Active (γ: gname) : iProp Σ := own γ (Excl ()).
  
  Definition external_inv (γ: gname) (N: namespace) (P: iProp Σ) : iProp Σ := 
      inv N (P ∨ Active γ).
  
  Local Lemma new_active : ⊢ |==> ∃ γ , Active γ.
  Proof.
    iIntros. iDestruct (own_alloc (Excl ())) as "H"; first done. unfold Active. iFrame "H".
  Qed.
  
  Local Lemma active_active_false (γc : gname) : Active γc ∗ Active γc ⊢ False.
  Proof. 
    iIntros "X". unfold Active. rewrite <- own_op.
    iDestruct (own_valid with "X") as "%J". contradiction.
  Qed.
  
  Lemma external_inv_alloc (N: namespace) (E : coPset) (P : iProp Σ) :
    ▷ P ={E}=∗ ∃ γ, external_inv γ N P ∗ Active γ.
  Proof.
    iIntros "latp".
    iMod new_active as (γ) "a".
    iMod (inv_alloc N E (P ∨ Active γ) with "[latp]") as "x".
    { iNext. iLeft. iFrame "latp". }
    iModIntro. iExists γ. iFrame "a". iFrame "x".
  Qed.
  
  Global Instance pers_external_inv γ N P : Persistent (external_inv γ N P).
  Proof.
    typeclasses eauto.
  Qed.
  
  Lemma external_inv_acc_strong γ N P G F E :
    (↑N ## F) →
    (↑N ∪ F ⊆ E) →
    external_inv γ N P ∗ (G &&{F}&&> Active γ) ∗ G ={E, E ∖ ↑N}=∗
      G ∗ (▷ P) ∗ (∀ E', (▷ (P ∨ Active γ)) ={E', ↑N ∪ E'}=∗ True).
  Proof.
    intros disj subs. iIntros "[#ei [#gu g]]".
    iDestruct (inv_acc_strong E N with "ei") as "T". { set_solver. }
    iMod "T" as "[[P|a] back]".
    - replace ((↑N ∪ F) ∖ ↑N) with F by set_solver.
      + iModIntro. iFrame "g". iFrame "P". iFrame "back".
    - iDestruct (guards_open G (Active γ) F F with "[g]") as "X". { set_solver. }
        { iFrame "g". iFrame "gu". }
      iApply (fupd_mask_mono F). { set_solver. }
      iMod "X" as "[a2 _]". iMod "a".
      iExFalso. iApply active_active_false. iFrame "a". iFrame "a2".
  Qed.
  
  Lemma external_inv_cancel γ N P E :
    (↑N ⊆ E) →
    external_inv γ N P ∗ Active γ ={E}=∗ ▷ P.
  Proof.
    intros subs. iIntros "[#ei a]".
    iDestruct (external_inv_acc_strong γ N P (Active γ) ∅ E with "[a]") as "J".
      { set_solver. } { set_solver. }
      { iFrame "a". iFrame "ei". iApply guards_refl. }
    iMod "J" as "[a [p back]]". iDestruct ("back" $! (E ∖ ↑N)) as "back".
    iDestruct ("back" with "[a]") as "back".
    { iModIntro. iRight. iFrame "a". }
    iMod "back".
    replace ((↑N) ∪ (E ∖ (↑N))) with E. { iModIntro. iFrame "p". }
    rewrite <- (guard.copset_diff_union); trivial.
  Qed.

End CancellableInvariants.
