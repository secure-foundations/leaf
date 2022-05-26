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

Context {Σ: gFunctors}.
Context `{!invGS Σ}.

Definition supports E x y : iProp Σ := □ (x ={E, ∅}=∗ y ∗ (y ={∅, E}=∗ x))%I.
Notation "P =&{ E }&=> Q" := (supports E P Q)
  (at level 99, E at level 50, Q at level 200).

Lemma supports_refl E P : ⊢ P =&{ E }&=> P.
Proof.
  unfold supports. iIntros. iModIntro. iIntros "x".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iIntros "[t z]". iMod ownE_empty as "l". iModIntro. iModIntro.
  iFrame. iIntros "a [b c]". iModIntro. iModIntro. iFrame.
Qed.

Lemma supports_add_set E1 E2 P Q :
  (disjoint E1 E2) ->
  supports E1 P Q ⊢ supports (E1 ∪ E2) P Q.
Proof.
  intro.
  unfold supports. iIntros "#x". iModIntro. iIntros "p".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iDestruct ("x" with "p") as "t".
  iIntros "[s e12]".
  iDestruct (ownE_op with "e12") as "[e1 e2]"; trivial.
  iDestruct ("t" with "[s e1]") as "z". { iFrame. }
  iMod "z" as "z". iModIntro.
  iMod "z" as "z". iModIntro.
  iDestruct "z" as "[a [b [c d]]]".
  iFrame. iIntros "e f".
  iDestruct ("d" with "e f") as "d".
  iMod "d" as "d". iModIntro.
  iMod "d" as "d". iModIntro.
  iDestruct "d" as "[q [r s]]". iFrame.
  rewrite ownE_op; trivial. iFrame.
Qed.

Lemma supports_trans E1 E2 P Q R : (disjoint E1 E2) ->
    (P =&{E1}&=> Q) ∗ (Q =&{E2}&=> R) ⊢ P =&{E1 ∪ E2}&=> R.
Proof.
  intro.
  iIntros "[#x #y]".
  iDestruct (supports_add_set _ E2 _ _ with "x") as "#z"; trivial.
  unfold supports. iModIntro.
  iIntros "p".
  iMod ("z" with "p") as "[l s]".
  iMod ("y" with "l") as "R".
  iMod ("s" with "l") as "p".
  
  iModIntro.
  
Qed.
