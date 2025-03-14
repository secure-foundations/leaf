From lrust.lifetime Require Export primitive.
From lrust.lifetime Require Export faking.
From iris.algebra Require Import csum auth frac gmap agree gset.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section borrow.
Context `{!invGS Σ, !lftGS Σ}.
Implicit Types κ : lft.

Lemma raw_bor_create E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ ▷ P ={E}=∗ raw_bor κ P ∗ ([†κ] ={E}=∗ ▷ P).
Proof.
  iIntros (HE) "#LFT HP". iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ with "HA HI Hinv") as (A' I') "(Hκ & HA & HI & Hinv)".
  iDestruct "Hκ" as %Hκ. iDestruct (@big_sepS_later with "Hinv") as "Hinv".
  iDestruct (big_sepS_elem_of_acc _ _ κ with "Hinv") as "[Hinv Hclose']".
  { by apply elem_of_dom. }
  rewrite {1}/lft_inv. iDestruct "Hinv" as "[[Hinv >%]|[Hinv >%]]".
  - rewrite {1}lft_inv_alive_unfold;
      iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    rewrite /lft_bor_alive; iDestruct "Halive" as (B) "(HboxB & >HownB & HB)".
    iMod (lft_inh_extend _ _ P with "Hinh")
      as "(Hinh & HIlookup & Hinh_close)"; first solve_ndisj.
    iMod (slice_insert_full _ _ true with "HP HboxB")
      as (γB) "(HBlookup & HsliceB & HboxB)"; first by solve_ndisj.
    rewrite lookup_fmap. iDestruct "HBlookup" as %HBlookup.
    rewrite -(fmap_insert bor_filled _ _ Bor_in).
    iMod (own_bor_update with "HownB") as "[HB● HB◯]".
    { eapply auth_update_alloc,
        (alloc_singleton_local_update _ γB (1%Qp, to_agree Bor_in)); last done.
      rewrite lookup_fmap. case:(B !! γB) HBlookup; done. }
    rewrite -fmap_insert.
    iSpecialize ("Hclose'" with "[Hvs Hinh HboxB HB● HB]").
    { iNext. rewrite /lft_inv. iLeft. iFrame "%".
      rewrite lft_inv_alive_unfold. iExists (P ∗ Pb)%I, (P ∗ Pi)%I.
      iFrame "Hinh". iSplitL "HboxB HB● HB"; last by iApply lft_vs_frame.
      rewrite /lft_bor_alive. iExists _. iFrame "HboxB HB●".
      iApply @big_sepM_insert; first by destruct (B !! γB).
      simpl. iFrame. }
    iMod ("Hclose" with "[HA HI Hclose']") as "_"; [by iNext; iExists _, _; iFrame|].
    iSplitL "HB◯ HsliceB".
    + rewrite /bor /raw_bor /idx_bor_own. iModIntro. iExists γB. iFrame.
      iExists P. rewrite -bi.iff_refl. auto.
    + clear -HE. iIntros "!> H†".
      iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
      iDestruct ("HIlookup" with "HI") as %Hκ.
      iDestruct (big_sepS_elem_of_acc _ _ κ with "Hinv") as "[Hinv Hclose']".
      { by apply elem_of_dom. }
      rewrite /lft_dead; iDestruct "H†" as (Λ) "[% #H†]".
      iDestruct (own_alft_auth_agree A Λ false with "HA H†") as %EQAΛ.
      rewrite {1}/lft_inv; iDestruct "Hinv" as "[[_ >%]|[Hinv >%]]".
      { unfold lft_alive_in in *. naive_solver. }
      rewrite /lft_inv_dead; iDestruct "Hinv" as (Pinh) "(Hdead & >Hcnt & Hinh)".
      iMod ("Hinh_close" $! Pinh with "Hinh") as (Pinh') "(? & $ & ?)".
      iApply "Hclose". iExists A, I. iFrame. iNext. iApply "Hclose'".
      rewrite /lft_inv. iRight. iFrame "%".
      rewrite /lft_inv_dead. iExists Pinh'. iFrame.
  - iFrame "HP". iApply fupd_frame_r. iSplitR ""; last by auto.
    rewrite /lft_inv_dead. iDestruct "Hinv" as (Pinh) "(Hdead & Hcnt & Hinh)" .
    iMod (raw_bor_fake with "Hdead") as "[Hdead Hbor]"; first solve_ndisj.
    unfold bor. iFrame. iApply "Hclose". iExists _, _. iFrame. rewrite big_sepS_later.
    iApply "Hclose'". iNext. rewrite /lft_inv. iRight.
    rewrite /lft_inv_dead. iFrame. eauto.
Qed.

Lemma bor_create E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ ▷ P ={E}=∗ &{κ}P ∗ ([†κ] ={E}=∗ ▷ P).
Proof.
  iIntros (?) "#LFT HP". iMod (raw_bor_create with "LFT HP") as "[HP $]"; [done|].
  rewrite /bor. iExists _. iFrame. iApply lft_incl_refl.
Qed.
End borrow.
