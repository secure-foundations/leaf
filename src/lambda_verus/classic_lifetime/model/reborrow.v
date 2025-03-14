From lrust.lifetime Require Import borrow accessors.
From iris.algebra Require Import csum auth frac gmap agree gset numbers.
From iris.base_logic.lib Require Import boxes.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section reborrow.
Context `{!invGS Σ, !lftGS Σ}.
Implicit Types κ : lft.

(* Notice that taking lft_inv for both κ and κ' already implies
   κ ≠ κ'.  Still, it is probably more instructing to require
   κ ⊂ κ' in this lemma (as opposed to just κ ⊆ κ'), and it
   should not increase the burden on the user. *)
Lemma raw_bor_unnest E A I Pb Pi P κ i κ' :
  ↑borN ⊆ E →
  let Iinv := (own_ilft_auth I ∗ ▷ lft_inv A κ)%I in
  κ ⊂ κ' →
  lft_alive_in A κ' →
  Iinv -∗ idx_bor_own 1 (κ, i) -∗ slice borN i P -∗ ▷ lft_bor_alive κ' Pb -∗
  ▷ lft_vs κ' (idx_bor_own 1 (κ, i) ∗ Pb) Pi ={E}=∗ ∃ Pb',
    Iinv ∗ raw_bor κ' P ∗ ▷ lft_bor_alive κ' Pb' ∗ ▷ lft_vs κ' Pb' Pi.
Proof.
  iIntros (? Iinv Hκκ' Haliveκ') "(HI & Hκ) Hi #Hislice Hκalive' Hvs".
  rewrite lft_vs_unfold. iDestruct "Hvs" as (n) "[>Hn● Hvs]".
  iMod (own_cnt_update with "Hn●") as "[Hn● H◯]".
  { apply auth_update_alloc, (nat_local_update _ 0 (S n) 1); lia. }
  rewrite {1}/raw_bor /idx_bor_own /=.
  iDestruct (own_bor_auth with "HI Hi") as %?.
  assert (κ ⊆ κ') by (by apply strict_include).
  iDestruct (lft_inv_alive_in with "Hκ") as "Hκ";
    first by eauto using lft_alive_in_subseteq.
  rewrite lft_inv_alive_unfold;
    iDestruct "Hκ" as (Pb' Pi') "(Hκalive&Hvs'&Hinh')".
  rewrite {2}/lft_bor_alive; iDestruct "Hκalive" as (B) "(Hbox & >HB● & HB)".
  iDestruct (own_bor_valid_2 with "HB● Hi")
    as %[HB%to_borUR_included _]%auth_both_valid_discrete.
  iMod (slice_empty _ _ true with "Hislice Hbox") as "[HP Hbox]"; first done.
  { by rewrite lookup_fmap HB. }
  iMod (own_bor_update_2 with "HB● Hi") as "[HB● Hi]".
  { eapply auth_update, singleton_local_update; last eapply
     (exclusive_local_update _ (1%Qp, to_agree (Bor_rebor κ'))); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HB. }
  iAssert (▷ lft_inv A κ)%I with "[H◯ HB● HB Hvs' Hinh' Hbox]" as "Hκ".
  { iNext. rewrite /lft_inv. iLeft.
    iSplit; last by eauto using lft_alive_in_subseteq.
    rewrite lft_inv_alive_unfold. iExists Pb', Pi'. iFrame "Hvs' Hinh'".
    rewrite /lft_bor_alive. iExists (<[i:=Bor_rebor κ']>B).
    rewrite /to_borUR !fmap_insert. iFrame "Hbox HB●".
    iDestruct (@big_sepM_delete with "HB") as "[_ HB]"; first done.
    rewrite (big_sepM_delete _ (<[_:=_]>_) i); last by rewrite lookup_insert.
    rewrite -insert_delete_insert delete_insert ?lookup_delete //=. iFrame; auto. }
  clear B HB Pb' Pi'.
  rewrite {1}/lft_bor_alive. iDestruct "Hκalive'" as (B) "(Hbox & >HB● & HB)".
  iMod (slice_insert_full _ _ true with "HP Hbox")
    as (j) "(HBj & #Hjslice & Hbox)"; first done.
  iDestruct "HBj" as %HBj; move: HBj; rewrite lookup_fmap fmap_None=> HBj.
  iMod (own_bor_update with "HB●") as "[HB● Hj]".
  { apply auth_update_alloc,
     (alloc_singleton_local_update _ j (1%Qp, to_agree Bor_in)); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HBj. }
  iModIntro. iExists (P ∗ Pb)%I. rewrite /Iinv. iFrame "HI Hκ". iSplitL "Hj".
  { iExists j. iFrame. iExists P. rewrite -bi.iff_refl. auto. }
  iSplitL "Hbox HB● HB".
  { rewrite /lft_bor_alive. iNext. iExists (<[j:=Bor_in]> B).
    rewrite /to_borUR !fmap_insert big_sepM_insert //. iFrame.
    by rewrite /bor_cnt. }
  clear dependent Iinv I.
  iNext. rewrite lft_vs_unfold. iExists (S n). iFrame "Hn●".
  iIntros (I) "Hinv [HP HPb] #Hκ†".
  rewrite {1}lft_vs_inv_unfold; iDestruct "Hinv" as "(HI & Hinv)".
  iDestruct (own_bor_auth with "HI Hi") as %?%(elem_of_dom (D:=gset lft)).
  iDestruct (@big_sepS_delete with "Hinv") as "[Hκalive Hinv]"; first done.
  rewrite lft_inv_alive_unfold.
  iDestruct ("Hκalive" with "[//]") as (Pb' Pi') "(Hκalive&Hvs'&Hinh)".
  rewrite /lft_bor_alive; iDestruct "Hκalive" as (B') "(Hbox & HB● & HB)".
  iDestruct (own_bor_valid_2 with "HB● Hi")
    as %[HB%to_borUR_included _]%auth_both_valid_discrete.
  iMod (own_bor_update_2 with "HB● Hi") as "[HB● Hi]".
  { eapply auth_update, singleton_local_update,
     (exclusive_local_update _ (1%Qp, to_agree Bor_in)); last done.
    rewrite /to_borUR lookup_fmap. by rewrite HB. }
  iMod (slice_fill _ _ false with "Hislice HP Hbox")
     as "Hbox".
  { set_solver-. }
  { by rewrite lookup_fmap HB. }
  iDestruct (@big_sepM_delete with "HB") as "[Hcnt HB]"; first done.
  rewrite /=. iDestruct "Hcnt" as "[% H1◯]".
  iMod ("Hvs" $! I with "[HI Hinv Hvs' Hinh HB● Hbox HB]
                         [$HPb $Hi] Hκ†") as "($ & $ & Hcnt')".
  { rewrite lft_vs_inv_unfold. iFrame "HI".
    iApply (big_sepS_delete _ (dom (gset lft) I) with "[- $Hinv]"); first done.
    iIntros (_). rewrite lft_inv_alive_unfold.
    iExists Pb', Pi'. iFrame "Hvs' Hinh". rewrite /lft_bor_alive.
    iExists (<[i:=Bor_in]>B'). rewrite /to_borUR !fmap_insert. iFrame.
    rewrite -insert_delete_insert big_sepM_insert ?lookup_delete //=. by iFrame. }
  iModIntro. rewrite -[S n]Nat.add_1_l -nat_op auth_frag_op own_cnt_op.
  by iFrame.
Qed.

Lemma raw_idx_bor_unnest E κ κ' i P :
  ↑lftN ⊆ E → κ ⊂ κ' →
  lft_ctx -∗ slice borN i P -∗ raw_bor κ' (idx_bor_own 1 (κ, i))
  ={E}=∗ raw_bor κ' P.
Proof.
  iIntros (? Hκκ') "#LFT #Hs Hraw".
  iInv mgmtN as (A I) "(>HA & >HI & Hinv)" "Hclose".
  iDestruct (raw_bor_inI with "HI Hraw") as %HI'.
  rewrite (big_sepS_delete _ _ κ') ?elem_of_dom // [_ A κ']/lft_inv.
  iDestruct "Hinv" as "[[[Hinvκ >%]|[Hinvκ >%]] Hinv]"; last first.
  { rewrite /lft_inv_dead. iDestruct "Hinvκ" as (Pi) "[Hbordead H]".
    iMod (raw_bor_fake with "Hbordead") as "[Hbordead $]"; first solve_ndisj.
    iApply "Hclose". iExists _, _. iFrame.
    rewrite (big_opS_delete _ (dom _ _) κ') ?elem_of_dom // /lft_inv /lft_inv_dead.
    auto 10 with iFrame. }
  rewrite {1}/raw_bor. iDestruct "Hraw" as (i') "[Hbor H]".
  iDestruct "H" as (P') "[#HP' #Hs']".
  rewrite lft_inv_alive_unfold /lft_bor_alive [in _ _ (κ', i')]/idx_bor_own.
  iDestruct "Hinvκ" as (Pb Pi) "(Halive & Hvs & Hinh)".
  iDestruct "Halive" as (B) "(Hbox & >H● & HB)".
  iDestruct (own_bor_valid_2 with "H● Hbor")
    as %[EQB%to_borUR_included _]%auth_both_valid_discrete.
  iMod (slice_empty _ _ true with "Hs' Hbox") as "[Hidx Hbox]".
    solve_ndisj. by rewrite lookup_fmap EQB.
  iAssert (▷ idx_bor_own 1 (κ, i))%I with "[Hidx]" as ">Hidx"; [by iApply "HP'"|].
  iDestruct (own_bor_auth with "HI [Hidx]") as %HI; [by rewrite /idx_bor_own|].
  iDestruct (big_sepS_elem_of_acc _ _ κ with "Hinv") as "[Hinvκ Hclose']";
    first by rewrite elem_of_difference elem_of_dom not_elem_of_singleton;
    eauto using strict_ne.
  iMod (slice_delete_empty with "Hs' Hbox") as (Pb') "[#HeqPb' Hbox]";
    [solve_ndisj|by apply lookup_insert|].
  iMod (own_bor_update_2 with "H● Hbor") as "H●".
  { apply auth_update_dealloc, delete_singleton_local_update. apply _. }
  iMod (raw_bor_unnest with "[$HI $Hinvκ] Hidx Hs [Hbox H● HB] [Hvs]")
    as (Pb'') "HH"; [solve_ndisj|done|done| | |].
  { rewrite /lft_bor_alive (big_sepM_delete _ B i') //. iDestruct "HB" as "[_ HB]".
    iExists (delete i' B). rewrite -fmap_delete. iFrame.
    rewrite fmap_delete -insert_delete_insert delete_insert ?lookup_delete //=. }
  { iNext. iApply (lft_vs_cons with "[] Hvs"). iIntros "[??] _ !>". iNext.
    iRewrite "HeqPb'". iFrame. by iApply "HP'". }
  iDestruct "HH" as "([HI Hinvκ] & $ & Halive & Hvs)".
  iApply "Hclose". iExists _, _. iFrame.
  rewrite (big_opS_delete _ (dom _ _) κ') ?elem_of_dom //.
  iDestruct ("Hclose'" with "Hinvκ") as "$".
  rewrite /lft_inv lft_inv_alive_unfold. auto 10 with iFrame.
Qed.

Lemma raw_bor_shorten E κ κ' P :
  ↑lftN ⊆ E → κ ⊆ κ' →
  lft_ctx -∗ raw_bor κ P ={E}=∗ raw_bor κ' P.
Proof.
  iIntros (? Hκκ') "#LFT Hbor".
  destruct (decide (κ = κ')) as [<-|Hκneq]; [by iFrame|].
  assert (κ ⊂ κ') by (by apply strict_spec_alt).
  rewrite [_ κ P]/raw_bor. iDestruct "Hbor" as (s) "[Hbor Hs]".
  iDestruct "Hs" as (P') "[#HP'P #Hs]".
  iMod (raw_bor_create _ κ' with "LFT Hbor") as "[Hbor _]"; [done|].
  iApply (raw_bor_iff with "HP'P"). by iApply raw_idx_bor_unnest.
Qed.

Lemma idx_bor_unnest E κ κ' i P :
  ↑lftN ⊆ E →
  lft_ctx -∗ &{κ,i} P -∗ &{κ'}(idx_bor_own 1 i) ={E}=∗ &{κ ⊓ κ'} P.
Proof.
  iIntros (?) "#LFT #HP Hbor".
  rewrite [(&{κ'}_)%I]/bor. iDestruct "Hbor" as (κ'0) "[#Hκ'κ'0 Hbor]".
  destruct (decide (κ'0 = static)) as [->|Hκ'0].
  { iMod (bor_acc_strong with "LFT [Hbor] []") as (?) "(_ & Hbor & _)";
      [done| |iApply (lft_tok_static 1)|].
    - rewrite /bor. iExists static. iFrame. iApply lft_incl_refl.
    - iDestruct "Hbor" as ">Hbor".
      iApply bor_shorten; [|by rewrite bor_unfold_idx; auto].
      iApply lft_intersect_incl_l. }
  rewrite /idx_bor /bor. destruct i as [κ0 i].
  iDestruct "HP" as "[Hκκ0 HP]". iDestruct "HP" as (P') "[HPP' HP']".
  iMod (raw_bor_shorten _ _ (κ0 ⊓ κ'0) with "LFT Hbor") as "Hbor";
    [done|by apply gmultiset_disj_union_subseteq_r|].
  iMod (raw_idx_bor_unnest with "LFT HP' Hbor") as "Hbor";
    [done|by apply gmultiset_disj_union_subset_l|].
  iExists _. iDestruct (raw_bor_iff with "HPP' Hbor") as "$".
    by iApply lft_intersect_mono.
Qed.
End reborrow.
