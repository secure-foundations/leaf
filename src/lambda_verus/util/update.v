From iris.bi Require Import updates.
From iris.proofmode Require Import proofmode.
From lrust.util Require Import basic.

(* TODO : move all that to Iris *)

(** * Utility for Multi-Step-Taking Updates *)

Section lemmas.
Context `{!BiFUpd PROP}.
Implicit Type P Q R: PROP.

Global Instance step_fupdN_proper E n : Proper ((⊣⊢) ==> (⊣⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_ne E n m : Proper (dist m ==> dist m) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_mono E n : Proper ((⊢) ==> (⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_flip_mono E n :
  Proper (flip (⊢) ==> flip (⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. move=> ???. by apply step_fupdN_mono. Qed.

Lemma step_fupdN_full_intro E n P : P ={E}▷=∗^n P.
Proof. iIntros "?". by iApply step_fupdN_intro. Qed.

Lemma step_fupdN_nmono m n P E : m ≤ n → (|={E}▷=>^m P) -∗ (|={E}▷=>^n P).
Proof.
  move: n. elim m=>/= [|?]; [iIntros; by iApply step_fupdN_full_intro|].
  move=> IH ? /succ_le [?[->Le]]/=. iIntros "?". by iApply IH.
Qed.

Lemma step_fupdN_sep n P Q E :
  (|={E}▷=>^n P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^n (P ∗ Q)).
Proof.
  elim n=>/= [|?]; [iIntros; by iFrame|]. iIntros (IH) ">UpdP >UpdQ !>!>".
  by iMod (IH with "UpdP UpdQ").
Qed.

Global Instance step_fupdN_from_sep n P Q E :
  FromSep (|={E}▷=>^n (P ∗ Q)) (|={E}▷=>^n P) (|={E}▷=>^n Q).
Proof.
  rewrite /FromSep. iIntros "[P Q]". iApply (step_fupdN_sep with "P Q").
Qed.

Global Instance frame_step_fupdN p R E n P Q :
  Frame p R P Q → Frame p R (|={E}▷=>^n P) (|={E}▷=>^n Q).
Proof.
  rewrite /Frame=> <-. iIntros "[R Q]".
  iDestruct (step_fupdN_full_intro with "R") as "R". by iCombine "R Q" as "?".
Qed.

Lemma step_fupdN_sep_max m n P Q E :
  (|={E}▷=>^m P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^(m `max` n) (P ∗ Q)).
Proof.
  set l := m `max` n. rewrite !(step_fupdN_nmono _ l _); [|lia|lia].
  apply step_fupdN_sep.
Qed.

Global Instance step_fupdN_from_sep_max m n P Q E :
  FromSep (|={E}▷=>^(m `max` n) (P ∗ Q)) (|={E}▷=>^m P) (|={E}▷=>^n Q) | 10.
Proof.
  rewrite /FromSep. iIntros "[P Q]". iApply (step_fupdN_sep_max with "P Q").
Qed.

Lemma step_fupdN_with_emp n P E F :
  (|={E, F}=> |={F}▷=>^n |={F, E}=> P) -∗ (|={E, ∅}=> |={∅}▷=>^n |={∅, E}=> P).
Proof.
  iIntros ">Upd". iInduction n as [|] "IH"=>/=.
  - iApply fupd_mask_intro; [set_solver|]. by iIntros ">?".
  - iApply fupd_mask_intro; [set_solver|]. iIntros ">_". iMod "Upd".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Get !>". iMod "Get".
    iMod ("IH" with "Upd") as "$".
Qed.

Lemma step_fupdN_add E n m P :
  (|={E}▷=>^(n + m) P) ⊣⊢ (|={E}▷=>^n |={E}▷=>^m P).
Proof.
  induction n as [|n IH]; [done| rewrite /= IH //].
Qed.

Lemma step_fupdN_fupd_mask_mono E₁ E₂ n P :
  E₁ ⊆ E₂ → (|={E₁}▷=>^n |={E₁}=> P) -∗ (|={E₂}▷=>^n |={E₂}=> P).
Proof.
  move=> Hsub. induction n as [|n IH].
  - by iApply fupd_mask_mono.
  - iIntros "H /=". iApply fupd_mask_mono; [done|]. iApply IH.
    iMod "H". iModIntro. by iApply fupd_mask_mono; [done|].
Qed.

Lemma fupd_step_fupdN_fupd_mask_mono E₁ E₂ n P :
  E₁ ⊆ E₂ →
  (|={E₁}=> |={E₁}▷=>^n |={E₁}=> P) -∗ (|={E₂}=> |={E₂}▷=>^n |={E₂}=> P).
Proof.
  iIntros (Hsub) "Hstep". iApply fupd_mask_mono; [done|].
  by iApply step_fupdN_fupd_mask_mono; [done|].
Qed.
End lemmas.
