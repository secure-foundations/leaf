From iris.algebra Require Import gmap auth frac.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Export lifetime.
Set Default Proof Using "Type".

(** Atomic persistent bors  *)
(* TODO : update the TEX with the fact that we can choose the namespace. *)
Definition at_bor `{!invGS Σ, !lftGS Σ} κ N (P : iProp Σ) :=
  (∃ i, &{κ,i}P ∗
    (⌜N ## lftN⌝ ∗ inv N (idx_bor_own 1 i) ∨
     ⌜N = lftN⌝ ∗ inv N (∃ q, idx_bor_own q i)))%I.
Notation "&at{ κ , N }" := (at_bor κ N) (format "&at{ κ , N }") : bi_scope.

Section atomic_bors.
  Context `{!invGS Σ, !lftGS Σ} (P : iProp Σ) (N : namespace).

  Global Instance at_bor_ne κ n : Proper (dist n ==> dist n) (at_bor κ N).
  Proof. solve_proper. Qed.
  Global Instance at_bor_contractive κ : Contractive (at_bor κ N).
  Proof. solve_contractive. Qed.
  Global Instance at_bor_proper κ : Proper ((⊣⊢) ==> (⊣⊢)) (at_bor κ N).
  Proof. solve_proper. Qed.

  Lemma at_bor_iff κ P' : ▷ □ (P ↔ P') -∗ &at{κ, N} P -∗ &at{κ, N} P'.
  Proof.
    iIntros "HPP' H". iDestruct "H" as (i) "[HP ?]". iExists i. iFrame.
    iApply (idx_bor_iff with "HPP' HP").
  Qed.

  Global Instance at_bor_persistent κ N P : Persistent (&at{κ, N} P) := _.

  Lemma bor_share E κ :
    N ## lftN → &{κ}P ={E}=∗ &at{κ, N}P.
  Proof.
    iIntros (HN) "HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "(#?&Hown)".
    iExists i. iFrame "#".
    iLeft. iSplitR. done. by iMod (inv_alloc with "[Hown]") as "$"; auto.
  Qed.

  Lemma bor_share_lftN E κ :
    ↑lftN ⊆ E → &{κ}P ={E}=∗ &at{κ, lftN}P.
  Proof.
    iIntros (?) "HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "(#?&Hown)".
    iExists i. iFrame "#". subst.
    iRight. iSplitR. done. by iMod (inv_alloc with "[Hown]") as "$"; auto.
  Qed.

  Lemma at_bor_acc E κ :
    ↑lftN ⊆ E → ↑N ⊆ E →
    lft_ctx -∗ &at{κ,N}P ={E,E∖↑N∖↑lftN}=∗ ▷P ∗ (▷P ={E∖↑N∖↑lftN,E}=∗ True) ∨
               [†κ] ∗ |={E∖↑N∖↑lftN,E}=> True.
  Proof.
    iIntros (??) "#LFT #HP". iDestruct "HP" as (i) "#[Hidx [[% Hinv]|[% Hinv]]]".
    - iInv N as ">Hi" "Hclose". iMod (idx_bor_atomic_acc with "LFT Hidx Hi")
        as "[[HP Hclose']|[H† Hclose']]". solve_ndisj.
      + iLeft. iFrame. iIntros "!>HP". iMod ("Hclose'" with "HP"). by iApply "Hclose".
      + iRight. iFrame. iIntros "!>". iMod "Hclose'". by iApply "Hclose".
    - subst. rewrite difference_twice_L. iInv lftN as (q') ">[Hq'0 Hq'1]" "Hclose".
      iMod ("Hclose" with "[Hq'1]") as "_". by eauto.
      iMod (idx_bor_atomic_acc with "LFT Hidx Hq'0") as "[[HP Hclose]|[H† Hclose]]". done.
      + iLeft. iFrame. iIntros "!>HP". by iMod ("Hclose" with "HP").
      + iRight. iFrame. iIntros "!>". by iMod "Hclose".
  Qed.

  Lemma at_bor_acc_tok E q κ :
    ↑lftN ⊆ E → ↑N ⊆ E →
    lft_ctx -∗ &at{κ,N}P -∗ q.[κ] ={E,E∖↑N}=∗ ▷P ∗ (▷P ={E∖↑N,E}=∗ q.[κ]).
  Proof.
    iIntros (??) "#LFT #HP Hκ". iDestruct "HP" as (i) "#[Hidx [[% Hinv]|[% Hinv]]]".
    - iInv N as ">Hi" "Hclose".
      iMod (idx_bor_acc with "LFT Hidx Hi Hκ") as "[$ Hclose']". solve_ndisj.
      iIntros "!> H". iMod ("Hclose'" with "H") as "[? $]". by iApply "Hclose".
    - iMod (at_bor_acc with "LFT []") as "[[$ Hclose]|[H† _]]"; try done.
      + iExists i. auto.
      + subst. rewrite difference_twice_L. iIntros "!>HP". by iMod ("Hclose" with "HP").
      + iDestruct (lft_tok_dead with "Hκ H†") as "[]".
  Qed.

  Lemma at_bor_shorten κ κ': κ ⊑ κ' -∗ &at{κ',N}P -∗ &at{κ,N}P.
  Proof.
    iIntros "#H⊑ H". iDestruct "H" as (i) "[??]". iExists i. iFrame.
      by iApply (idx_bor_shorten with "H⊑").
  Qed.

  Lemma at_bor_fake E κ:
    ↑lftN ⊆ E → N ## lftN → lft_ctx -∗ [†κ] ={E}=∗ &at{κ,N}P.
  Proof.
    iIntros (??) "#LFT#H†". iApply (bor_share with "[>]"); try done.
    by iApply (bor_fake with "LFT H†").
  Qed.

  Lemma at_bor_fake_lftN E κ:
    ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &at{κ,lftN}P.
  Proof.
    iIntros (?) "#LFT#H†". iApply (bor_share_lftN with "[>]"); try done.
    by iApply (bor_fake with "LFT H†").
  Qed.
End atomic_bors.

Lemma at_bor_acc_lftN `{!invGS Σ, !lftGS Σ} (P : iProp Σ) E κ :
  ↑lftN ⊆ E →
  lft_ctx -∗ &at{κ,lftN}P ={E,E∖↑lftN}=∗ ▷P ∗ (▷P ={E∖↑lftN,E}=∗ True) ∨
             [†κ] ∗ |={E∖↑lftN,E}=> True.
Proof. intros. by rewrite (at_bor_acc _ lftN) // difference_twice_L. Qed.

Global Typeclasses Opaque at_bor.
