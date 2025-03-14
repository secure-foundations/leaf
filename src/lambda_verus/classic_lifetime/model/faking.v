From lrust.lifetime Require Export primitive.
From iris.algebra Require Import csum auth frac gmap agree gset numbers.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section faking.
Context `{!invGS Σ, !lftGS Σ}.
Implicit Types κ : lft.

Lemma ilft_create A I κ :
  own_alft_auth A -∗ own_ilft_auth I -∗ ▷ ([∗ set] κ ∈ dom _ I, lft_inv A κ)
      ==∗ ∃ A' I', ⌜is_Some (I' !! κ)⌝ ∗
    own_alft_auth A' ∗ own_ilft_auth I' ∗ ▷ ([∗ set] κ ∈ dom _ I', lft_inv A' κ).
Proof.
  iIntros "HA HI Hinv".
  destruct (decide (is_Some (I !! κ))) as [?|HIκ%eq_None_not_Some].
  { iModIntro. iExists A, I. by iFrame. }
  iMod (own_alloc (● 0 ⋅ ◯ 0)) as (γcnt) "[Hcnt Hcnt']"; first by apply auth_both_valid_discrete.
  iMod (own_alloc (● (∅ : gmap slice_name
    (frac * agree bor_stateO)) ⋅ ◯ ∅)) as (γbor) "[Hbor Hbor']".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc (● (ε : gset_disj slice_name)))
     as (γinh) "Hinh"; first by apply auth_auth_valid.
  set (γs := LftNames γbor γcnt γinh).
  iMod (own_update with "HI") as "[HI Hγs]".
  { apply auth_update_alloc,
      (alloc_singleton_local_update _ κ (to_agree γs)); last done.
    by rewrite lookup_fmap HIκ. }
  iDestruct "Hγs" as "#Hγs".
  iAssert (own_cnt κ (● 0)) with "[Hcnt]" as "Hcnt".
  { rewrite /own_cnt. iExists γs. by iFrame. }
  iAssert (own_cnt κ (◯ 0)) with "[Hcnt']" as "Hcnt'".
  { rewrite /own_cnt. iExists γs. by iFrame. }
  iAssert (∀ b, lft_inh κ b True)%I with "[Hinh]" as "Hinh".
  { iIntros (b). rewrite /lft_inh. iExists ∅. rewrite gset_to_gmap_empty.
    iSplitL; [|iApply box_alloc]. rewrite /own_inh. iExists γs. by iFrame. }
  iAssert (lft_inv_dead κ ∧ lft_inv_alive κ)%I
    with "[-HA HI Hinv]" as "Hdeadandalive".
  { iSplit.
    - rewrite /lft_inv_dead. iExists True%I. iFrame "Hcnt".
      iSplitL "Hbor"; last by iApply "Hinh".
      rewrite /lft_bor_dead. iExists ∅, True%I. rewrite !gset_to_gmap_empty.
      iSplitL "Hbor". iExists γs. by iFrame. iApply box_alloc.
    - rewrite lft_inv_alive_unfold. iExists True%I, True%I. iSplitL "Hbor".
      { rewrite /lft_bor_alive. iExists ∅.
        rewrite /to_borUR !fmap_empty big_sepM_empty.
        iSplitR; [iApply box_alloc|]. iSplit=>//.
        rewrite /own_bor. iExists γs. by iFrame. }
      iSplitR "Hinh"; last by iApply "Hinh".
      rewrite lft_vs_unfold. iExists 0. iFrame "Hcnt Hcnt'". auto. }
  destruct (lft_alive_or_dead_in A κ) as [(Λ&?&HAΛ)|Haliveordead].
  - iMod (own_update with "HA") as "[HA _]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ Λ (Cinr ())); last done.
      by rewrite lookup_fmap HAΛ. }
    iModIntro. iExists (<[Λ:=false]>A), (<[κ:=γs]> I).
    iSplit; first rewrite lookup_insert; eauto.
    rewrite /own_ilft_auth /own_alft_auth /to_ilftUR /to_alftUR !fmap_insert.
    iFrame "HA HI". rewrite dom_insert_L big_sepS_insert ?not_elem_of_dom //.
    iSplitR "Hinv".
    { rewrite /lft_inv. iNext. iRight. iSplit.
      { by iDestruct "Hdeadandalive" as "[? _]". }
      iPureIntro. exists Λ. rewrite lookup_insert; auto. }
    iNext. iApply (@big_sepS_impl with "[$Hinv]").
    rewrite /lft_inv. iIntros "!>"; iIntros (κ' ?%elem_of_dom)
      "[[HA HA']|[HA HA']]"; iDestruct "HA'" as %HA.
    + iLeft. iFrame "HA". iPureIntro. by apply lft_alive_in_insert.
    + iRight. iFrame "HA". iPureIntro. by apply lft_dead_in_insert.
  - iModIntro. iExists A, (<[κ:=γs]> I).
    iSplit; first rewrite lookup_insert; eauto.
    rewrite /own_ilft_auth /to_ilftUR fmap_insert. iFrame "HA HI".
    rewrite dom_insert_L.
    iApply @big_sepS_insert; first by apply not_elem_of_dom.
    iFrame "Hinv". iNext. rewrite /lft_inv. destruct Haliveordead.
    + iLeft. by iDestruct "Hdeadandalive" as "[_ $]".
    + iRight. by iDestruct "Hdeadandalive" as "[$ _]".
Qed.

Lemma raw_bor_fake E κ P :
  ↑borN ⊆ E → ▷ lft_bor_dead κ ={E}=∗ ▷ lft_bor_dead κ ∗ raw_bor κ P.
Proof.
  iIntros (?). rewrite /lft_bor_dead. iDestruct 1 as (B Pinh) "[>HB● Hbox]".
  iMod (slice_insert_empty _ _ true _ P with "Hbox") as (γ) "(% & #Hslice & Hbox)".
  iMod (own_bor_update with "HB●") as "[HB● H◯]".
  { eapply auth_update_alloc,
      (alloc_singleton_local_update _ _ (1%Qp, to_agree Bor_in)); last done.
    by do 2 eapply lookup_gset_to_gmap_None. }
  rewrite /bor /raw_bor /idx_bor_own /=. iModIntro. iSplitR "H◯".
  - iExists ({[γ]} ∪ B), (P ∗ Pinh)%I. rewrite !gset_to_gmap_union_singleton. by iFrame.
  - iExists γ. iFrame. iExists P. rewrite -bi.iff_refl. eauto.
Qed.

Lemma raw_bor_fake' E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ [†κ] ={E}=∗ raw_bor κ P.
Proof.
  iIntros (?) "#LFT H†". iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iMod (ilft_create _ _ κ with "HA HI Hinv") as (A' I') "(Hκ & HA & HI & Hinv)".
  iDestruct "Hκ" as %Hκ. rewrite /lft_dead. iDestruct "H†" as (Λ) "[% #H†]".
  iDestruct (own_alft_auth_agree A' Λ false with "HA H†") as %EQAΛ.
  iDestruct (@big_sepS_elem_of_acc with "Hinv")
    as "[Hinv Hclose']"; first by apply elem_of_dom.
  rewrite {1}/lft_inv; iDestruct "Hinv" as "[[_ >%]|[Hinv >%]]".
  { unfold lft_alive_in in *; naive_solver. }
  rewrite /lft_inv_dead; iDestruct "Hinv" as (Pinh) "(Hdead & Hcnt & Hinh)".
  iMod (raw_bor_fake _ _ P with "Hdead") as "[Hdead Hbor]"; first solve_ndisj.
  iFrame. iApply "Hclose". iExists A', I'. iFrame. iNext. iApply "Hclose'".
  rewrite /lft_inv /lft_inv_dead. iRight. iFrame. eauto.
Qed.

Lemma bor_fake E κ P :
  ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &{κ}P.
Proof.
  iIntros (?) "#LFT H†". iMod (raw_bor_fake' with "LFT H†"); first done.
  iModIntro. unfold bor. iExists κ. iFrame. iApply lft_incl_refl.
Qed.
End faking.
