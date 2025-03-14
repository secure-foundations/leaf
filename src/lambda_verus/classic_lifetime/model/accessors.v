From lrust.lifetime Require Export primitive.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import csum auth frac gmap agree gset.
From iris.base_logic.lib Require Import boxes.
Set Default Proof Using "Type".

Section accessors.
Context `{!invGS Σ, !lftGS Σ}.
Implicit Types κ : lft.

(* Helper internal lemmas *)
Lemma bor_open_internal E P i Pb q :
  ↑borN ⊆ E →
  slice borN (i.2) P -∗ ▷ lft_bor_alive (i.1) Pb -∗
  idx_bor_own 1%Qp i -∗ (q).[i.1] ={E}=∗
    ▷ lft_bor_alive (i.1) Pb ∗
    own_bor (i.1) (◯ {[i.2 := (1%Qp, to_agree (Bor_open q))]}) ∗ ▷ P.
Proof.
  iIntros (?) "Hslice Halive Hbor Htok". unfold lft_bor_alive, idx_bor_own.
  iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
  iDestruct (own_bor_valid_2 with "Hown Hbor")
    as %[EQB%to_borUR_included _]%auth_both_valid_discrete.
  iMod (slice_empty _ _ true with "Hslice Hbox") as "[$ Hbox]".
    solve_ndisj. by rewrite lookup_fmap EQB.
  rewrite -(fmap_insert bor_filled _ _ (Bor_open q)).
  iMod (own_bor_update_2 with "Hown Hbor") as "Hbor". apply auth_update.
  { eapply singleton_local_update. by rewrite lookup_fmap EQB.
    by apply (exclusive_local_update _ (1%Qp, to_agree (Bor_open q))). }
  rewrite own_bor_op -fmap_insert. iDestruct "Hbor" as "[Hown $]".
  iExists _. iFrame "∗".
  rewrite -insert_delete_insert big_sepM_insert ?lookup_delete // big_sepM_delete /=; last done.
  iDestruct "HB" as "[_ $]". auto.
Qed.

Lemma bor_close_internal E P i Pb q :
  ↑borN ⊆ E →
  slice borN (i.2) P -∗ ▷ lft_bor_alive (i.1) Pb -∗
  own_bor (i.1) (◯ {[i.2 := (1%Qp, to_agree (Bor_open q))]}) -∗ ▷ P ={E}=∗
    ▷ lft_bor_alive (i.1) Pb ∗ idx_bor_own 1%Qp i ∗ (q).[i.1].
Proof.
  iIntros (?) "Hslice Halive Hbor HP". unfold lft_bor_alive, idx_bor_own.
  iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
  iDestruct (own_bor_valid_2 with "Hown Hbor")
    as %[EQB%to_borUR_included _]%auth_both_valid_discrete.
  iMod (slice_fill _ _ true with "Hslice HP Hbox") as "Hbox".
    solve_ndisj. by rewrite lookup_fmap EQB.
  rewrite -(fmap_insert bor_filled _ _ Bor_in).
  iMod (own_bor_update_2 with "Hown Hbor") as "Hbor". apply auth_update.
  { eapply singleton_local_update. by rewrite lookup_fmap EQB.
    by apply (exclusive_local_update _ (1%Qp, to_agree Bor_in)). }
  rewrite own_bor_op -fmap_insert. iDestruct "Hbor" as "[Hown $]".
  rewrite big_sepM_delete //. simpl. iDestruct "HB" as "[>$ HB]".
  iExists _. iFrame "Hbox Hown".
  rewrite -insert_delete_insert big_sepM_insert ?lookup_delete //. simpl. by iFrame.
Qed.

Lemma add_vs Pb Pb' P Q Pi κ :
  ▷ (Pb ≡ (P ∗ Pb')) -∗ lft_vs κ Pb Pi -∗ (▷ Q -∗ [†κ] ={↑lft_userN}=∗ ▷ P) -∗
  lft_vs κ (Q ∗ Pb') Pi.
Proof.
  iIntros "#HEQ Hvs HvsQ". iApply (lft_vs_cons with "[-Hvs] Hvs").
  iIntros "[HQ HPb'] #H†".
  iApply fupd_mask_mono; last iMod ("HvsQ" with "HQ H†") as "HP". set_solver.
  iModIntro. iNext. iRewrite "HEQ". iFrame.
Qed.

(** Indexed borrow *)
Lemma idx_bor_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ,i}P -∗ idx_bor_own 1 i -∗ q.[κ] ={E}=∗
            ▷ P ∗ (▷ P ={E}=∗ idx_bor_own 1 i ∗ q.[κ]).
Proof.
  unfold idx_bor. iIntros (HE) "#LFT [#Hle #Hs] Hbor Htok".
  iDestruct "Hs" as (P') "[#HPP' Hs]".
  iMod (lft_incl_acc with "Hle Htok") as (q') "[Htok Hclose]". solve_ndisj.
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
  iDestruct (own_bor_auth with "HI [Hbor]") as %Hκ'. by unfold idx_bor_own.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in lft_inv_alive_unfold.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose'']".
  - iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    iMod (bor_open_internal with "Hs Halive Hbor Htok") as "(Halive & Hf & HP')".
    { solve_ndisj. }
    iDestruct ("HPP'" with "HP'") as "$".
    iMod ("Hclose'" with "[-Hf Hclose]") as "_".
    { iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''".
      iLeft. iFrame "%". iExists _, _. iFrame. }
    iIntros "!>HP'". iDestruct ("HPP'" with "HP'") as "HP". clear -HE.
    iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
    iDestruct (own_bor_auth with "HI Hf") as %Hκ'.
    rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
            /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in /lft_bor_dead.
    iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >Hdead_in]] Hclose'']".
    + rewrite lft_inv_alive_unfold.
      iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
      iMod (bor_close_internal with "Hs Halive Hf HP") as "(Halive & $ & Htok)".
        solve_ndisj.
      iMod ("Hclose'" with "[-Htok Hclose]") as "_"; last by iApply "Hclose".
      iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''".
      iLeft. iFrame "%". iExists _, _. iFrame.
    + iDestruct "Hinv" as (?) "[Hinv _]". iDestruct "Hinv" as (B ?) "[>Hinv _]".
      iDestruct (own_bor_valid_2 with "Hinv Hf")
        as %[(_ & <- & INCL%option_included)%singleton_included_l _]%auth_both_valid_discrete.
      by destruct INCL as [[=]|(? & ? & [=<-] &
        [[_<-]%lookup_gset_to_gmap_Some [[_ ?%(inj to_agree)]|[]%(exclusive_included _)]])].
  - iMod (lft_dead_in_tok with "HA") as "[_ H†]". done.
    iDestruct (lft_tok_dead with "Htok H†") as "[]".
Qed.

Lemma idx_bor_atomic_acc E q κ i P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ,i}P -∗ idx_bor_own q i ={E,E∖↑lftN}=∗
              (▷ P ∗ (▷ P ={E∖↑lftN,E}=∗ idx_bor_own q i)) ∨
              ([†κ] ∗ |={E∖↑lftN,E}=> idx_bor_own q i).
Proof.
  unfold idx_bor, idx_bor_own. iIntros (HE) "#LFT [#Hle #Hs] Hbor".
  iDestruct "Hs" as (P') "[#HPP' Hs]".
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
  iDestruct (own_bor_auth with "HI Hbor") as %Hκ'.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in lft_inv_alive_unfold.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose'']".
  - iLeft. iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    unfold lft_bor_alive.
    iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
    iDestruct (own_bor_valid_2 with "Hown Hbor")
      as %[EQB%to_borUR_included _]%auth_both_valid_discrete.
    iMod (slice_empty _ _ true with "Hs Hbox") as "[HP' Hbox]".
      solve_ndisj. by rewrite lookup_fmap EQB.
    iDestruct ("HPP'" with "HP'") as "$".
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hclose HP'".
    iDestruct ("HPP'" with "HP'") as "HP".
    iMod "Hclose" as "_". iMod (slice_fill _ _ true with "Hs HP Hbox") as "Hbox".
      solve_ndisj. by rewrite lookup_insert. iFrame.
    iApply "Hclose'". iExists _, _. iFrame. rewrite big_sepS_later.
    iApply "Hclose''". iLeft. iFrame "%". iExists _, _. iFrame.
    iExists _. iFrame.
    rewrite insert_insert -(fmap_insert _ _ _ Bor_in) insert_id //.
  - iRight. iMod (lft_dead_in_tok with "HA") as "[HA #H†]". done.
    iMod ("Hclose'" with "[-Hbor]") as "_".
    + iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''". eauto.
    + iMod (lft_incl_dead with "Hle H†"). done. iFrame.
      iApply fupd_mask_subseteq. solve_ndisj.
Qed.

(** Basic borrows  *)

Lemma bor_acc_strong E q κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P -∗ q.[κ] ={E}=∗ ∃ κ', κ ⊑ κ' ∗ ▷ P ∗
    ∀ Q, ▷(▷ Q -∗ [†κ'] ={↑lft_userN}=∗ ▷ P) -∗ ▷ Q ={E}=∗ &{κ'} Q ∗ q.[κ].
Proof.
  unfold bor, raw_bor. iIntros (HE) "#LFT Hbor Htok".
  iDestruct "Hbor" as (κ'') "(#Hle & Htmp)". iDestruct "Htmp" as (s'') "(Hbor & #Hs)".
  iDestruct "Hs" as (P') "[#HPP' Hs]".
  iMod (lft_incl_acc with "Hle Htok") as (q') "[Htok Hclose]". solve_ndisj.
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
  iDestruct (own_bor_auth with "HI [Hbor]") as %Hκ'. by unfold idx_bor_own.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in lft_inv_alive_unfold.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose'']".
  - iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    iMod (bor_open_internal _ _ (κ'', s'') with "Hs Halive Hbor Htok")
      as "(Halive & Hbor & HP')". solve_ndisj.
    iDestruct ("HPP'" with "HP'") as "$".
    iMod ("Hclose'" with "[-Hbor Hclose]") as "_".
    { iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''".
      iLeft. iFrame "%". iExists _, _. iFrame. }
    iExists κ''. iFrame "#". iIntros "!>* HvsQ HQ". clear -HE.
    iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
    iDestruct (own_bor_auth with "HI Hbor") as %Hκ'.
    rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
            /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in /lft_bor_dead.
    iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >Hdead_in]] Hclose'']".
    + rewrite lft_inv_alive_unfold /lft_bor_alive.
      iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
      iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
      iDestruct (own_bor_valid_2 with "Hown Hbor")
        as %[EQB%to_borUR_included _]%auth_both_valid_discrete.
      iMod (slice_delete_empty _ _ true with "Hs Hbox") as (Pb') "[EQ Hbox]".
        solve_ndisj. by rewrite lookup_fmap EQB.
      iDestruct (add_vs with "EQ Hvs [HvsQ]") as "Hvs".
      { iNext. iIntros "HQ H†". iApply "HPP'". iApply ("HvsQ" with "HQ H†"). }
      iMod (slice_insert_empty _ _ true _ Q with "Hbox") as (j) "(% & #Hs' & Hbox)".
      iMod (own_bor_update_2 with "Hown Hbor") as "Hown".
      { apply auth_update. etrans.
        - apply delete_singleton_local_update, _.
        - apply (alloc_singleton_local_update _ j
                   (1%Qp, to_agree (Bor_open q'))); last done.
          rewrite -fmap_delete lookup_fmap fmap_None
                  -fmap_None -lookup_fmap fmap_delete //. }
      rewrite own_bor_op. iDestruct "Hown" as "[Hown Hbor]".
      iMod (bor_close_internal _ _ (_, _) with "Hs' [Hbox Hown HB] Hbor HQ")
        as "(Halive & Hbor & Htok)". solve_ndisj.
      { rewrite -!fmap_delete -fmap_insert -(fmap_insert _ _ _ (Bor_open q'))
                /lft_bor_alive. iExists _. iFrame "Hbox Hown".
        rewrite big_sepM_insert. by rewrite big_sepM_delete.
        by rewrite -fmap_None -lookup_fmap fmap_delete. }
      iMod ("Hclose'" with "[-Hbor Htok Hclose]") as "_".
      { iExists _, _. iFrame. rewrite big_sepS_later /lft_bor_alive. iApply "Hclose''".
        iLeft. iFrame "%". iExists _, _. iFrame. }
      iMod ("Hclose" with "Htok") as "$". iExists κ''. iModIntro.
      iSplit; first by iApply lft_incl_refl. iExists j. iFrame.
      iExists Q. rewrite -bi.iff_refl. eauto.
    + iDestruct "Hinv" as (?) "[Hinv _]". iDestruct "Hinv" as (B ?) "[>Hinv _]".
      iDestruct (own_bor_valid_2 with "Hinv Hbor")
        as %[(_ & <- & INCL%option_included)%singleton_included_l _]%auth_both_valid_discrete.
      by destruct INCL as [[=]|(? & ? & [=<-] &
        [[_<-]%lookup_gset_to_gmap_Some [[_?%(inj to_agree)]|[]%(exclusive_included _)]])].
  - iMod (lft_dead_in_tok with "HA") as "[_ H†]". done.
    iDestruct (lft_tok_dead with "Htok H†") as "[]".
Qed.

Lemma bor_acc_atomic_strong E κ P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ} P ={E,E∖↑lftN}=∗
   (∃ κ', κ ⊑ κ' ∗ ▷ P ∗
      ∀ Q, ▷ (▷ Q -∗ [†κ'] ={↑lft_userN}=∗ ▷ P) -∗ ▷ Q ={E∖↑lftN,E}=∗ &{κ'} Q) ∨
    ([†κ] ∗ |={E∖↑lftN,E}=> True).
Proof.
  iIntros (HE) "#LFT Hbor". rewrite bor_unfold_idx /idx_bor /bor /raw_bor.
  iDestruct "Hbor" as (i) "((#Hle & #Hs) & Hbor)".
  iDestruct "Hs" as (P') "[#HPP' Hs]".
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose'".
  iDestruct (own_bor_auth with "HI [Hbor]") as %Hκ'. by unfold idx_bor_own.
  rewrite big_sepS_later big_sepS_elem_of_acc ?elem_of_dom //
          /lfts_inv /lft_inv /lft_inv_dead /lft_alive_in lft_inv_alive_unfold.
  iDestruct "Hinv" as "[[[Hinv >%]|[Hinv >%]] Hclose'']".
  - iLeft. iExists (i.1). iFrame "#".
    iDestruct "Hinv" as (Pb Pi) "(Halive & Hvs & Hinh)".
    unfold lft_bor_alive, idx_bor_own.
    iDestruct "Halive" as (B) "(Hbox & >Hown & HB)".
    iDestruct (own_bor_valid_2 with "Hown Hbor")
      as %[EQB%to_borUR_included _]%auth_both_valid_discrete.
    iMod (slice_delete_full _ _ true with "Hs Hbox") as (Pb') "(HP' & EQ & Hbox)".
      solve_ndisj. by rewrite lookup_fmap EQB. iDestruct ("HPP'" with "HP'") as "$".
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hclose * HvsQ HQ".
    iMod "Hclose" as "_". iDestruct (add_vs with "EQ Hvs [HvsQ]") as "Hvs".
    { iNext. iIntros "HQ H†". iApply "HPP'". iApply ("HvsQ" with "HQ H†"). }
    iMod (slice_insert_full _ _ true with "HQ Hbox") as (j) "(% & #Hs' & Hbox)".
      solve_ndisj.
    iMod (own_bor_update_2 with "Hown Hbor") as "Hown".
    { apply auth_update. etrans.
      - apply delete_singleton_local_update, _.
      - apply (alloc_singleton_local_update _ j (1%Qp, to_agree (Bor_in))); last done.
        rewrite -fmap_delete lookup_fmap fmap_None
                -fmap_None -lookup_fmap fmap_delete //. }
    rewrite own_bor_op. iDestruct "Hown" as "[H● H◯]".
    iMod ("Hclose'" with "[- H◯]"); last first.
    { iModIntro. iExists (i.1). iSplit; first by iApply lft_incl_refl.
      iExists j. iFrame. iExists Q. rewrite -bi.iff_refl. auto. }
    iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''".
    iLeft. iFrame "%". iExists _, _. iFrame. iNext.
    rewrite -!fmap_delete -fmap_insert -(fmap_insert _ _ _ Bor_in).
    iExists _. iFrame "Hbox H●".
    rewrite big_sepM_insert. by rewrite big_sepM_delete.
      by rewrite -fmap_None -lookup_fmap fmap_delete.
  - iRight. iMod (lft_dead_in_tok with "HA") as "[HA #H†]". done.
    iMod ("Hclose'" with "[-Hbor]") as "_".
    + iExists _, _. iFrame. rewrite big_sepS_later. iApply "Hclose''". eauto.
    + iMod (lft_incl_dead with "Hle H†") as "$". done.
      iApply fupd_mask_subseteq. solve_ndisj.
Qed.
End accessors.
