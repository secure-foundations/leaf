(** This file contains the examples from the paper:

MoSeL: A General, Extensible Modal Framework for Interactive Proofs in
Separation Logic
Robbert Krebbers, Jacques-Henri Jourdan, Ralf Jung, Joseph Tassarotti,
Jan-Oliver Kaiser, Amin Timany, Arthur Charguéraud, Derek Dreyer
ICFP 2018 *)
From iris.bi Require Import monpred.
From iris.proofmode Require Import tactics monpred.

Unset Mangle Names.

Lemma example_1 {PROP : bi} {A : Type} (P : PROP) (Φ Ψ : A → PROP) :
  P ∗ (∃ a, Φ a ∨ Ψ a) -∗ ∃ a, (P ∗ Φ a) ∨ (P ∗ Ψ a).
Proof.
  iIntros "[HP H]". Show.
  iDestruct "H" as (x) "[H1|H2]".
  - Show. iExists x. iLeft. iSplitL "HP"; iAssumption.
  - Show. iExists x. iRight. iSplitL "HP"; iAssumption.
Qed.
Lemma example {PROP : bi} {A : Type} (P : PROP) (Φ Ψ : A → PROP) :
P ∗ (∃ a, Φ a ∨ Ψ a) -∗ ∃ a, (P ∗ Φ a) ∨ (P ∗ Ψ a).
Proof.
  iIntros "[HP H]". Show.
  iFrame "HP". Show.
  iAssumption.
Qed.

Lemma example_2 {PROP : bi} {A : Type} (P : PROP) (Φ Ψ : A → PROP) :
  <affine> P ∗ (∃ a, Φ a ∨ Ψ a) -∗ ∃ a, Φ a ∨ (P ∗ Ψ a).
Proof.
  iIntros "[HP H]". iDestruct "H" as (x) "[H1|H2]".
  - iExists x. iLeft. Show. iAssumption.
  - iExists x. iRight. Show. iSplitL "HP"; iAssumption.
Qed.

Lemma example_3 {PROP : bi} {A : Type} (P : PROP) (Φ Ψ : A → PROP) :
  □ P ∗ (∃ a, Φ a ∨ Ψ a) -∗ ∃ a, Φ a ∨ (P ∗ P ∗ Ψ a).
Proof.
  iIntros "[#HP H]". Show. iDestruct "H" as (x) "[H1|H2]".
  - iExists x. iLeft. iAssumption.
  - iExists x. iRight. Show. iSplitR; [|iSplitR]; iAssumption.
Qed.
Lemma example_4 {PROP : bi} {A : Type} (P Q : PROP) : □ P ∧ □ Q -∗ □ (P ∗ Q).
Proof. iIntros "[#HP #HQ]". Show. iModIntro. iSplitL; iAssumption. Qed.

Lemma example_monpred {I PROP} (Φ Ψ : monPred I PROP) : Φ ∗ (Φ -∗ Ψ) ⊢ Ψ.
Proof. iIntros "[H1 H2]". Show. iApply "H2". iAssumption. Qed.

Lemma example_monpred_model {I PROP} (Φ Ψ : monPred I PROP) : Φ ∗ (Φ -∗ Ψ) ⊢ Ψ.
Proof. iStartProof PROP. Show. iIntros (i) "[H1 H2]". iApply "H2". iAssumption. Qed.

Lemma example_monpred_2 {I PROP} (Φ : monPred I PROP) (P Q : PROP) :
  ⎡ P -∗ Q ⎤ -∗ ⎡ □ P ⎤ -∗ <affine> Φ -∗ ⎡ P ∗ Q ⎤.
Proof. iIntros "H1 #H2 H3". Show. iFrame "H2". Show. iApply "H1". iAssumption. Qed.
