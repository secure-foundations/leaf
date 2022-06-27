From iris.algebra Require Export cmra.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.

From iris.algebra Require Import auth.
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


Section ConjunctOwnRule.

Context {Σ: gFunctors}.
Context `{i : !inG Σ A}.
Implicit Types a : A.

Lemma stuff (x y: A) (𝛾: gname)  :
    ((▷ (x ≡ y)) : iProp Σ) ⊢ □ (▷ (x ≡ y)).
Proof.
  iIntros "#x".
  iModIntro.
  iFrame "#".
Qed.

own ⊢ 
γ 
