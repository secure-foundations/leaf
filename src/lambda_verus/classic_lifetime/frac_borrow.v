From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From iris.algebra Require Import frac.
From lrust.lifetime Require Export at_borrow.
Set Default Proof Using "Type".

Class frac_borG Σ := frac_borG_inG :> inG Σ fracR.

Local Definition frac_bor_inv `{!invGS Σ, !lftGS Σ, !frac_borG Σ} (φ : Qp → iProp Σ) γ κ' :=
  (∃ q, φ q ∗ own γ q ∗ (⌜q = 1%Qp⌝ ∨ ∃ q', ⌜(q + q' = 1)%Qp⌝ ∗ q'.[κ']))%I.

Definition frac_bor `{!invGS Σ, !lftGS Σ, !frac_borG Σ} κ (φ : Qp → iProp Σ) :=
  (∃ γ κ', κ ⊑ κ' ∗ &at{κ',lftN} (frac_bor_inv φ γ κ'))%I.
Notation "&frac{ κ }" := (frac_bor κ) (format "&frac{ κ }") : bi_scope.

Section frac_bor.
  Context `{!invGS Σ, !lftGS Σ, !frac_borG Σ} (φ : Qp → iProp Σ).
  Implicit Types E : coPset.

  Global Instance frac_bor_contractive κ n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (frac_bor κ).
  Proof. rewrite /frac_bor /frac_bor_inv. solve_contractive. Qed.
  Global Instance frac_bor_ne κ n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (frac_bor κ).
  Proof. rewrite /frac_bor /frac_bor_inv. solve_proper. Qed.
  Global Instance frac_bor_proper κ :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (frac_bor κ).
  Proof. rewrite /frac_bor /frac_bor_inv. solve_proper. Qed.

  Lemma frac_bor_iff κ φ' :
    ▷ □ (∀ q, φ q ↔ φ' q) -∗ &frac{κ} φ -∗ &frac{κ} φ'.
  Proof.
    iIntros "#Hφφ' H". iDestruct "H" as (γ κ') "[? Hφ]". iExists γ, κ'. iFrame.
    iApply (at_bor_iff with "[Hφφ'] Hφ"). iNext. iModIntro.
    iSplit; iIntros "H"; iDestruct "H" as (q) "[H ?]"; iExists q; iFrame; by iApply "Hφφ'".
  Qed.

  Global Instance frac_bor_persistent κ : Persistent (&frac{κ}φ) := _.

  Lemma bor_fracture E κ :
    ↑lftN ⊆ E → lft_ctx -∗ &{κ}(φ 1%Qp) ={E}=∗ &frac{κ}φ.
  Proof.
    iIntros (?) "#LFT Hφ". iMod (own_alloc 1%Qp) as (γ) "?". done.
    iMod (bor_acc_atomic_strong with "LFT Hφ") as "[H|[H† Hclose]]". done.
    - iDestruct "H" as (κ') "(#Hκκ' & Hφ & Hclose)".
      iMod ("Hclose" with "[] [-]") as "Hφ"; last first.
      { iExists γ, κ'. iFrame "#". iApply (bor_share_lftN with "Hφ"); auto. }
      { iExists 1%Qp. iFrame. eauto. }
      iIntros "!>Hφ H†!>". iNext. iDestruct "Hφ" as (q') "(Hφ & _ & [%|Hκ])". by subst.
      iDestruct "Hκ" as (q'') "[_ Hκ]".
      iDestruct (lft_tok_dead with "Hκ H†") as "[]".
    - iMod "Hclose" as "_"; last first.
      iExists γ, κ. iSplitR. by iApply lft_incl_refl.
      by iApply at_bor_fake_lftN.
  Qed.

  Lemma frac_bor_atomic_acc E κ :
    ↑lftN ⊆ E →
    lft_ctx -∗ &frac{κ}φ ={E,E∖↑lftN}=∗ (∃ q, ▷ φ q ∗ (▷ φ q ={E∖↑lftN,E}=∗ True))
                                      ∨ [†κ] ∗ |={E∖↑lftN,E}=> True.
  Proof.
    iIntros (?) "#LFT #Hφ". iDestruct "Hφ" as (γ κ') "[Hκκ' Hshr]".
    iMod (at_bor_acc_lftN with "LFT Hshr") as "[[Hφ Hclose]|[H† Hclose]]"; try done.
    - iLeft. iDestruct "Hφ" as (q) "(Hφ & Hγ & H)". iExists q. iFrame.
      iIntros "!>Hφ". iApply "Hclose". iExists q. iFrame.
    - iRight. iMod "Hclose" as "_". iMod (lft_incl_dead with "Hκκ' H†") as "$". done.
      iApply fupd_mask_subseteq. set_solver.
  Qed.

  Local Lemma frac_bor_trade1 γ κ' q :
    □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ∗ φ q2) -∗
    ▷ frac_bor_inv φ γ κ' ∗ ▷ own γ q ∗ ▷ φ q -∗
    ▷ (frac_bor_inv φ γ κ' ∗ q.[κ']).
  Proof.
    iIntros "#Hφ (H & Hown & Hφ1)". iNext.
    iDestruct "H" as (qφ) "(Hφqφ & Hown' & [%|Hq])".
    { subst. iCombine "Hown'" "Hown" as "Hown".
      by iDestruct (own_valid with "Hown") as %Hval%Qp_not_add_le_l. }
    rewrite /frac_bor_inv. iApply bi.sep_exist_r. iExists (q + qφ)%Qp.
    iDestruct "Hq" as (q' Hqφq') "Hq'κ". iCombine "Hown'" "Hown" as "Hown".
    iDestruct (own_valid with "Hown") as %Hval. rewrite comm_L. iFrame "Hown".
    iCombine "Hφ1 Hφqφ" as "Hφq". iDestruct ("Hφ" with "Hφq") as "$".
    assert (q ≤ q')%Qp as [[r ->]%Qp_lt_sum|<-]%Qp_le_lteq.
    { apply (Qp_add_le_mono_l _ _ qφ). by rewrite Hqφq'. }
    - iDestruct "Hq'κ" as "[$ Hr]".
      iRight. iExists _. iIntros "{$Hr} !%".
      by rewrite (comm_L Qp_add q) -assoc_L.
    - iFrame "Hq'κ". iLeft. iPureIntro. rewrite comm_L. done.
  Qed.

  Local Lemma frac_bor_trade2 γ κ' qκ' :
    □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ∗ φ q2) -∗
    ▷ frac_bor_inv φ γ κ' ∗ ▷ qκ'.[κ'] -∗
    ▷ (frac_bor_inv φ γ κ' ∗ ∃ q0 q1, ⌜qκ' = (q0 + q1)%Qp⌝ ∗ q1.[κ'] ∗ own γ q0 ∗ φ q0).
  Proof.
    iIntros "#Hφ [H Hκ']". iNext.
    iDestruct "H" as (qφ) "(Hφqφ & Hown & Hq)".
    destruct (Qp_lower_bound qκ' qφ) as (qq & qκ'0 & qφ0 & Hqκ' & Hqφ).
    iApply bi.sep_exist_l. iExists qq.
    iApply bi.sep_exist_l. iExists qκ'0.
    subst qκ' qφ. rewrite /frac_bor_inv.
    iApply bi.sep_exist_r. iExists qφ0.
    iDestruct ("Hφ" with "Hφqφ") as "[$ $] {Hφ}".
    iDestruct "Hown" as "[$ $]".
    iDestruct "Hκ'" as "[Hκ' $]".
    iSplit; last done.
    iDestruct "Hq" as "[%|Hq]".
      - iRight. iExists qq. iFrame. iPureIntro.
        by rewrite (comm _ qφ0).
      - iDestruct "Hq" as (q') "[% Hq'κ]". iRight. iExists (qq + q')%Qp.
        iSplitR; last first. { iApply fractional_split. iFrame. }
        iPureIntro. rewrite assoc (comm _ _ qq). done.
  Qed.

  Lemma frac_bor_acc' E q κ :
    ↑lftN ⊆ E →
    lft_ctx -∗ □ (∀ q1 q2, φ (q1+q2)%Qp ↔ φ q1 ∗ φ q2) -∗
    &frac{κ}φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ φ q' ∗ (▷ φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT #Hφ Hfrac Hκ". unfold frac_bor.
    iDestruct "Hfrac" as (γ κ') "#[#Hκκ' Hshr]".
    iMod (lft_incl_acc with "Hκκ' Hκ") as (qκ') "[[Hκ1 Hκ2] Hclose]". done.
    iMod (at_bor_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']"; try done.
    iDestruct (frac_bor_trade2 with "Hφ [$H $Hκ2]") as "[H Htrade]".
    iDestruct "Htrade" as (q0 q1) "(>Hq & >Hκ2 & >Hown & Hqφ)".
    iDestruct "Hq" as %Hq.
    iMod ("Hclose'" with "H") as "Hκ1".
    iExists q0. iFrame "Hqφ". iIntros "!>Hqφ".
    iMod (at_bor_acc_tok with "LFT Hshr Hκ1") as "[H Hclose']"; try done.
    iDestruct (frac_bor_trade1 with "Hφ [$H $Hown $Hqφ]") as "[H >Hκ3]".
    iMod ("Hclose'" with "H") as "Hκ1".
    iApply "Hclose". iApply fractional_half. iFrame "Hκ1". rewrite Hq.
    iApply fractional_split. iFrame.
  Qed.

  Lemma frac_bor_acc E q κ `{!Fractional φ} :
    ↑lftN ⊆ E →
    lft_ctx -∗ &frac{κ}φ -∗ q.[κ] ={E}=∗ ∃ q', ▷ φ q' ∗ (▷ φ q' ={E}=∗ q.[κ]).
  Proof.
    iIntros (?) "LFT". iApply (frac_bor_acc' with "LFT"). done.
    iIntros "!>*". rewrite fractional. iSplit; auto.
  Qed.

  Lemma frac_bor_shorten κ κ' : κ ⊑ κ' -∗ &frac{κ'}φ -∗ &frac{κ}φ.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (γ κ0) "[#H⊑ ?]". iExists γ, κ0. iFrame.
    iApply (lft_incl_trans with "Hκκ' []"). auto.
  Qed.

  Lemma frac_bor_fake E κ :
    ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &frac{κ}φ.
  Proof.
    iIntros (?) "#LFT#H†". iApply (bor_fracture with "LFT [>]"); first done.
    by iApply (bor_fake with "LFT").
  Qed.
End frac_bor.

Lemma frac_bor_lft_incl `{!invGS Σ, !lftGS Σ, !frac_borG Σ} κ κ' q:
  lft_ctx -∗ &frac{κ}(λ q', (q * q').[κ']) -∗ κ ⊑ κ'.
Proof.
  iIntros "#LFT#Hbor". iApply lft_incl_intro. iModIntro. iSplitR.
  - iIntros (q') "Hκ'".
    iMod (frac_bor_acc with "LFT Hbor Hκ'") as (q'') "[>? Hclose]". done.
    iExists _. iFrame. iIntros "!>Hκ'". iApply "Hclose". auto.
  - iIntros "H†'".
    iMod (frac_bor_atomic_acc with "LFT Hbor") as "[H|[$ $]]". done.
    iDestruct "H" as (q') "[>Hκ' _]".
    iDestruct (lft_tok_dead with "Hκ' H†'") as "[]".
Qed.

Global Typeclasses Opaque frac_bor.
