From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lang.lib Require Import memcpy arc.
From lrust.lifetime Require Import at_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option.
Set Default Proof Using "Type".

Definition arcN := lrustN .@ "arc".
Definition arc_invN := arcN .@ "inv".
Definition arc_shrN := arcN .@ "shr".
Definition arc_endN := arcN .@ "end".

Section arc.
  Context `{!typeG Σ, !arcG Σ}.

  (* Preliminary definitions. *)
  Let P1 ν q := (q.[ν])%I.
  Global Instance P1_fractional ν : Fractional (P1 ν).
  Proof. unfold P1. apply _. Qed.
  Let P2 l n := († l…(2 + n) ∗ (l +ₗ 2) ↦∗: λ vl, ⌜length vl = n⌝)%I.
  Definition arc_persist tid ν (γ : gname) (l : loc) (ty : type) : iProp Σ :=
    (is_arc (P1 ν) (P2 l ty.(ty_size)) arc_invN γ l ∗
     (* We use this disjunction, and not simply [ty_shr] here, *)
     (*    because [weak_new] cannot prove ty_shr, even for a dead *)
     (*    lifetime. *)
     (ty.(ty_shr) (ν ⊓ ty_lft ty) tid (l +ₗ 2) ∨ [†ν]) ∗
     □ (1.[ν] ={↑lftN ∪ ↑lft_userN ∪ ↑arc_endN}[↑lft_userN]▷=∗
          [†ν] ∗ ▷ (l +ₗ 2) ↦∗: ty.(ty_own) tid ∗ † l…(2 + ty.(ty_size))))%I.

  Lemma arc_persist_type_incl tid ν γ l ty1 ty2:
    type_incl ty1 ty2 -∗ arc_persist tid ν γ l ty1 -∗ arc_persist tid ν γ l ty2.
  Proof.
    iIntros "#(Heqsz & Hl & Hinclo & Hincls) #(?& Hs & Hvs)".
    iDestruct "Heqsz" as %->. iFrame "#". iSplit.
    - iDestruct "Hs" as "[?|?]"; last auto. iLeft. iApply "Hincls".
      iApply (ty_shr_mono with "[] [//]").
      iApply lft_intersect_mono; [iApply lft_incl_refl|done].
    - iIntros "!> Hν". iMod ("Hvs" with "Hν") as "H". iModIntro. iNext.
      iMod "H" as "($ & H & $)". iDestruct "H" as (vl) "[??]". iExists _.
      iFrame. by iApply "Hinclo".
  Qed.

  Lemma arc_persist_send tid tid' ν γ l ty `{!Send ty,!Sync ty} :
    arc_persist tid ν γ l ty -∗ arc_persist tid' ν γ l ty.
  Proof.
    iIntros "#($ & ? & Hvs)". rewrite sync_change_tid. iFrame "#".
    iIntros "!> Hν". iMod ("Hvs" with "Hν") as "H". iModIntro. iNext.
    iMod "H" as "($ & H & $)". iDestruct "H" as (vl) "?". iExists _.
    by rewrite send_change_tid.
  Qed.

  (* Model of arc *)
  (* The ty_own part of the arc type cointains either the
     shared protocol or the full ownership of the
     content. The reason is that get_mut does not have the
     masks to rebuild the invariants. *)
  Definition full_arc_own l ty tid : iProp Σ:=
    (l ↦ #1 ∗ (l +ₗ 1) ↦ #1 ∗ † l…(2 + ty.(ty_size)) ∗
       ▷ (l +ₗ 2) ↦∗: ty.(ty_own) tid)%I.
  Definition shared_arc_own l ty tid : iProp Σ:=
    (∃ γ ν q, arc_persist tid ν γ l ty ∗ arc_tok γ q ∗ q.[ν])%I.
  Lemma arc_own_share E l ty tid q :
    ↑lftN ⊆ E →
    lft_ctx -∗ (q).[ty_lft ty] -∗ full_arc_own l ty tid
    ={E}=∗ (q).[ty_lft ty] ∗ shared_arc_own l ty tid.
  Proof.
    iIntros (?) "#LFT Htok (Hl1 & Hl2 & H† & Hown)".
    iMod (lft_create with "LFT") as (ν) "[Hν #Hν†]"=>//.
    (* TODO: We should consider changing the statement of
       bor_create to dis-entangle the two masks such that this is no
      longer necessary. *)
    iApply fupd_trans. iApply (fupd_mask_mono (↑lftN))=>//.
    iMod (bor_create _ ν with "LFT Hown") as "[HP HPend]"=>//. iModIntro.
    iDestruct (lft_intersect_acc with "Hν Htok") as (q') "[Htok Hclose]".
    iMod (ty_share with "LFT [] [HP] Htok") as "[#? Htok]"; first solve_ndisj.
    { iApply lft_intersect_incl_r. }
    { iApply (bor_shorten with "[] HP"). iApply lft_intersect_incl_l. }
    iDestruct ("Hclose" with "Htok") as "[Hν $]".
    iMod (create_arc (P1 ν) (P2 l ty.(ty_size)) arc_invN with "Hl1 Hl2 Hν")
      as (γ q'') "(#? & ? & ?)".
    iExists _, _, _. iFrame "∗#". iCombine "H†" "HPend" as "H".
    iMod (inv_alloc arc_endN _ ([†ν] ∨ _)%I with "[H]") as "#INV";
      first by iRight; iApply "H". iIntros "!> !> Hν".
    iMod (inv_acc with "INV") as "[[H†|[$ Hvs]] Hclose]";
      [set_solver|iDestruct (lft_tok_dead with "Hν H†") as ">[]"|].
    rewrite difference_union_distr_l_L difference_diag_L right_id_L
            difference_disjoint_L; last first.
    { apply disjoint_union_l. split; solve_ndisj. }
    iMod ("Hν†" with "Hν") as "H". iModIntro. iNext. iApply fupd_trans.
    iMod "H" as "#Hν".
    iMod fupd_intro_mask' as "Hclose2"; last iMod ("Hvs" with "Hν") as "$".
    { set_solver-. }
    iIntros "{$Hν} !>".
    iMod "Hclose2" as "_". iApply "Hclose". auto.
  Qed.

  Program Definition arc (ty : type) :=
    {| ty_size := 1; ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => full_arc_own l ty tid ∨ shared_arc_own l ty tid
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l' : loc), &frac{κ} (λ q, l ↦{q} #l') ∗
           □ ∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ]
             ={F}[F∖↑shrN]▷=∗ q.[κ] ∗ ∃ γ ν q', κ ⊑ ν ∗
                arc_persist tid ν γ l' ty ∗
                &at{κ, arc_shrN}(arc_tok γ q')
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT #Hincl Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    (* Ideally, we'd change ty_shr to say "l ↦{q} #l" in the fractured borrow,
       but that would be additional work here... *)
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iFrame "Htok". iExists _. iFrame "#". rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    set (C := (∃ _ _ _, _ ∗ _ ∗ &at{_,_} _)%I).
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ C)%I
          with "[Hpbown]") as "#Hinv"; first by iLeft.
    iIntros "!> !>" (F q' ?) "Htok".
    iMod (inv_acc with "Hinv") as "[INV Hclose1]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ} _)%I with "[Hbtok]" as "Hb".
      { rewrite bor_unfold_idx. iExists _. by iFrame. }
      iClear "H↦ Hinv Hpb". iDestruct "Htok" as "[Htok1 Htok2]".
      iMod (bor_acc_cons with "LFT Hb Htok1") as "[HP Hclose2]"; first solve_ndisj.
      iModIntro. iNext.
      iAssert (shared_arc_own l' ty tid ∗ (q' / 2).[κ])%I with "[>HP Htok2]" as "[HX $]".
      { iDestruct "HP" as "[?|$]"; last done.
        iMod (lft_incl_acc with "Hincl Htok2") as (q'') "[Htok Hclose]"; first solve_ndisj.
        iMod (arc_own_share with "LFT Htok [$]") as "[Htok $]"; first solve_ndisj.
        by iApply "Hclose". }
      iDestruct "HX" as (γ ν q'') "[#Hpersist H]".
      iMod ("Hclose2" with "[] H") as "[HX $]"; first by unfold shared_arc_own; auto 10.
      iAssert C with "[>HX]" as "#$".
      { iExists _, _, _. iFrame "Hpersist".
        iMod (bor_sep with "LFT HX") as "[Hrc Hlft]"; first solve_ndisj.
        iDestruct (frac_bor_lft_incl with "LFT [> Hlft]") as "$".
        { iApply (bor_fracture with "LFT"); first solve_ndisj. by rewrite Qp_mul_1_r. }
        iApply (bor_share with "Hrc"); solve_ndisj. }
      iApply ("Hclose1" with "[]"). by auto.
    - iMod ("Hclose1" with "[]") as "_"; first by auto.
      iApply step_fupd_intro; first solve_ndisj. by iFrame.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H". iDestruct "H" as (l') "[#Hl #Hshr]".
    iExists _. iSplit; first by iApply frac_bor_shorten.
    iModIntro. iIntros (F q) "% Htok".
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hshr" with "[] Htok") as "Hshr2"; first done.
    iModIntro. iNext. iMod "Hshr2" as "[Htok HX]".
    iMod ("Hclose" with "Htok") as "$". iDestruct "HX" as (? ν ?) "(? & ? & ?)".
    iExists _, _, _. iModIntro. iFrame. iSplit.
    - by iApply lft_incl_trans.
    - by iApply at_bor_shorten.
  Qed.

  Global Instance arc_type_contractive : TypeContractive arc.
  Proof.
    split.
    - apply (type_lft_morphism_add _ static [] [])=>?.
      + rewrite left_id. iApply lft_equiv_refl.
      + by rewrite /elctx_interp /= left_id right_id.
    - done.
    - intros n ty1 ty2 Hsz Hl HE Ho Hs tid vl. destruct vl as [|[[|l|]|] [|]]=>//=.
      rewrite /full_arc_own /shared_arc_own /arc_persist Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ α, ty1.(ty_shr) (α ⊓ ty_lft ty1) tid (l +ₗ 2) ≡{n}≡
                   ty2.(ty_shr) (α ⊓ ty_lft ty2) tid (l +ₗ 2)) as Hs'.
      { intros. rewrite Hs. apply equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      repeat (apply Ho || apply dist_S, Ho || apply Hs' || f_contractive || f_equiv).
    - intros n ty1 ty2 Hsz Hl HE Ho Hs κ tid l. rewrite /= /arc_persist Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ l α, dist_later n (ty1.(ty_shr) (α ⊓ ty_lft ty1) tid (l +ₗ 2))
                              (ty2.(ty_shr) (α ⊓ ty_lft ty2) tid (l +ₗ 2))) as Hs'.
      { intros. rewrite Hs. apply dist_dist_later, equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      repeat (apply dist_S, Ho || apply Hs' || f_contractive || f_equiv).
  Qed.

  Global Instance arc_ne : NonExpansive arc.
  Proof.
    unfold arc, full_arc_own, shared_arc_own, arc_persist.
    intros n x y Hxy. constructor; [done|by apply Hxy..| |].
    - intros. rewrite ![X in X {| ty_own := _ |}]/ty_own.
      solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
    - solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
  Qed.

  Lemma arc_subtype ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (arc ty1) (arc ty2).
  Proof.
    iIntros "#Hincl". iPoseProof "Hincl" as "(#Hsz & Hl & #Hoincl & #Hsincl)".
    iSplit; [done|]. iSplit; [done|]. iSplit; iModIntro.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      iDestruct "Hvl" as "[(Hl1 & Hl2 & H† & Hc) | Hvl]".
      { iLeft. iFrame. iDestruct "Hsz" as %->.
        iFrame. iApply (heap_mapsto_pred_wand with "Hc"). iApply "Hoincl". }
      iDestruct "Hvl" as (γ ν q) "(#Hpersist & Htk & Hν)".
      iRight. iExists _, _, _. iFrame "#∗". by iApply arc_persist_type_incl.
    - iIntros "* #Hshr". iDestruct "Hshr" as (l') "[Hfrac Hshr]". iExists l'.
      iIntros "{$Hfrac} !> * % Htok". iMod ("Hshr" with "[% //] Htok") as "{Hshr} H".
      iModIntro. iNext. iMod "H" as "[$ H]".
      iDestruct "H" as (γ ν q') "(Hlft & Hpersist & Hna)".
      iExists _, _, _. iFrame. by iApply arc_persist_type_incl.
  Qed.

  Global Instance arc_mono E L :
    Proper (subtype E L ==> subtype E L) arc.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!> #HE". iApply arc_subtype. by iApply "Hsub".
  Qed.
  Global Instance arc_proper E L :
    Proper (eqtype E L ==> eqtype E L) arc.
  Proof. intros ??[]. by split; apply arc_mono. Qed.

  Global Instance arc_send ty :
    Send ty → Sync ty → Send (arc ty).
  Proof.
    intros Hse Hsy tid tid' vl. destruct vl as [|[[|l|]|] []]=>//=.
    unfold full_arc_own, shared_arc_own.
    repeat (apply send_change_tid || apply bi.exist_mono ||
            (apply arc_persist_send; apply _) || f_equiv || intros ?).
  Qed.

  Global Instance arc_sync ty :
    Send ty → Sync ty → Sync (arc ty).
  Proof.
    intros Hse Hsy ν tid tid' l.
    repeat (apply send_change_tid || apply bi.exist_mono ||
            (apply arc_persist_send; apply _) || f_equiv || intros ?).
  Qed.

  (* Model of weak *)
  Program Definition weak (ty : type) :=
    {| ty_size := 1; ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => ∃ γ ν, arc_persist tid ν γ l ty ∗ weak_tok γ
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l' : loc), &frac{κ} (λ q, l ↦{q} #l') ∗
           □ ∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ]
             ={F}[F∖↑shrN]▷=∗ q.[κ] ∗ ∃ γ ν,
                arc_persist tid ν γ l' ty ∗ &at{κ, arc_shrN}(weak_tok γ)
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hincl Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    (* Ideally, we'd change ty_shr to say "l ↦{q} #l" in the fractured borrow,
       but that would be additional work here... *)
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iFrame "Htok". iExists _. iFrame "#". rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    set (C := (∃ _ _, _ ∗ &at{_,_} _)%I).
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ C)%I
          with "[Hpbown]") as "#Hinv"; first by iLeft.
    iIntros "!> !> * % Htok".
    iMod (inv_acc with "Hinv") as "[INV Hclose1]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ} _)%I with "[Hbtok]" as "Hb".
      { rewrite bor_unfold_idx. iExists _. by iFrame. }
      iClear "H↦ Hinv Hpb".
      iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose2]"; first solve_ndisj.
      iDestruct "HP" as (γ ν) "[#Hpersist H]".
      iMod ("Hclose2" with "[] H") as "[HX $]"; first by auto 10.
      iModIntro. iNext. iAssert C with "[>HX]" as "#$".
      { iExists _, _. iFrame "Hpersist". iApply bor_share; solve_ndisj. }
      iApply ("Hclose1" with "[]"). by auto.
    - iMod ("Hclose1" with "[]") as "_"; first by auto.
      iApply step_fupd_intro; first solve_ndisj. by iFrame.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H". iDestruct "H" as (l') "[#Hl #Hshr]".
    iExists _. iSplit; first by iApply frac_bor_shorten.
    iModIntro. iIntros (F q) "% Htok".
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hshr" with "[] Htok") as "Hshr2"; first done.
    iModIntro. iNext. iMod "Hshr2" as "[Htok HX]".
    iMod ("Hclose" with "Htok") as "$". iDestruct "HX" as (? ν) "[??]".
    iExists _, _. iModIntro. iFrame. by iApply at_bor_shorten.
  Qed.

  Global Instance weak_type_contractive : TypeContractive weak.
  Proof.
    split.
    - apply (type_lft_morphism_add _ static [] [])=>?.
      + rewrite left_id. iApply lft_equiv_refl.
      + by rewrite /elctx_interp /= left_id right_id.
    - done.
    - intros n ty1 ty2 Hsz Hl HE Ho Hs tid vl. destruct vl as [|[[|l|]|] [|]]=>//=.
      rewrite /arc_persist Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ α, ty1.(ty_shr) (α ⊓ ty_lft ty1) tid (l +ₗ 2) ≡{n}≡
                   ty2.(ty_shr) (α ⊓ ty_lft ty2) tid (l +ₗ 2)) as Hs'.
      { intros. rewrite Hs. apply equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      repeat (apply Ho || apply dist_S, Ho || apply Hs' || f_contractive || f_equiv).
    - intros n ty1 ty2 Hsz Hl HE Ho Hs κ tid l. rewrite /= /arc_persist Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ l α, dist_later n (ty1.(ty_shr) (α ⊓ ty_lft ty1) tid (l +ₗ 2))
                              (ty2.(ty_shr) (α ⊓ ty_lft ty2) tid (l +ₗ 2))) as Hs'.
      { intros. rewrite Hs. apply dist_dist_later, equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      repeat (apply dist_S, Ho || apply Hs' || f_contractive || f_equiv).
  Qed.

  Global Instance weak_ne : NonExpansive weak.
  Proof.
    unfold weak, arc_persist. intros n x y Hxy. constructor; [done|by apply Hxy..| |].
    - intros. rewrite ![X in X {| ty_own := _ |}]/ty_own.
      solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
    - solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
  Qed.

  Lemma weak_subtype ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (weak ty1) (weak ty2).
  Proof.
    iIntros "#Hincl". iPoseProof "Hincl" as "(#Hsz & #Hoincl & #Hsincl)".
    iSplit; [done|]. iSplit; [done|]. iSplit; iModIntro.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      iDestruct "Hvl" as (γ ν) "(#Hpersist & Htk)".
      iExists _, _. iFrame "#∗". by iApply arc_persist_type_incl.
    - iIntros "* #Hshr". iDestruct "Hshr" as (l') "[Hfrac Hshr]". iExists l'.
      iIntros "{$Hfrac} !> * % Htok". iMod ("Hshr" with "[% //] Htok") as "{Hshr} H".
      iModIntro. iNext. iMod "H" as "[$ H]". iDestruct "H" as (γ ν) "[Hpersist Hna]".
      iExists _, _. iFrame. by iApply arc_persist_type_incl.
  Qed.

  Global Instance weak_mono E L :
    Proper (subtype E L ==> subtype E L) weak.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!> #HE". iApply weak_subtype. by iApply "Hsub".
  Qed.
  Global Instance weak_proper E L :
    Proper (eqtype E L ==> eqtype E L) weak.
  Proof. intros ??[]. by split; apply weak_mono. Qed.

  Global Instance weak_send ty :
    Send ty → Sync ty → Send (weak ty).
  Proof.
    intros Hse Hsy tid tid' vl. destruct vl as [|[[|l|]|] []]=>//=.
    repeat (apply send_change_tid || apply bi.exist_mono ||
            (apply arc_persist_send; apply _) || f_equiv || intros ?).
  Qed.

  Global Instance weak_sync ty :
    Send ty → Sync ty → Sync (weak ty).
  Proof.
    intros Hse Hsy ν tid tid' l.
    repeat (apply send_change_tid || apply bi.exist_mono ||
            (apply arc_persist_send; apply _) || f_equiv || intros ?).
  Qed.

  (* Code : constructors *)
  Definition arc_new ty : val :=
    fn: ["x"] :=
      let: "arcbox" := new [ #(2 + ty.(ty_size))%nat ] in
      let: "arc" := new [ #1 ] in
      "arcbox" +ₗ #0 <- #1;;
      "arcbox" +ₗ #1 <- #1;;
      "arcbox" +ₗ #2 <-{ty.(ty_size)} !"x";;
      "arc" <- "arcbox";;
      delete [ #ty.(ty_size); "x"];; return: ["arc"].

  Lemma arc_new_type ty :
    typed_val (arc_new ty) (fn(∅; ty) → arc ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new (2 + ty.(ty_size))); [solve_typing..|]; iIntros (rcbox); simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (rc); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrc [Hrcbox [Hx _]]]".
    rewrite !tctx_hasty_val.
    iDestruct (ownptr_own with "Hx") as (lx vlx) "(% & Hx↦ & Hx & Hx†)". subst x.
    iDestruct (ownptr_uninit_own with "Hrcbox")
      as (lrcbox vlrcbox) "(% & Hrcbox↦ & Hrcbox†)". subst rcbox. inv_vec vlrcbox=>???.
    iDestruct (heap_mapsto_vec_cons with "Hrcbox↦") as "[Hrcbox↦0 Hrcbox↦1]".
    iDestruct (heap_mapsto_vec_cons with "Hrcbox↦1") as "[Hrcbox↦1 Hrcbox↦2]".
    rewrite shift_loc_assoc.
    iDestruct (ownptr_uninit_own with "Hrc") as (lrc vlrc) "(% & Hrc↦ & Hrc†)". subst rc.
    inv_vec vlrc=>?. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. rewrite shift_loc_0. wp_write. wp_op. wp_write.
    wp_op. iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hrcbox↦2 $Hx↦]"); [by auto using vec_to_list_length..|].
    iIntros "[Hrcbox↦2 Hx↦]". wp_seq. wp_write.
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (ty_size ty)); #lrc ◁ box (arc ty)]
        with "[] LFT HE Hna HL Hk [>-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=. iFrame.
      iSplitL "Hx↦"; first by iExists _; rewrite ->uninit_own; auto.
      iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. iLeft.
      rewrite freeable_sz_full_S. iFrame. iExists _. by iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition weak_new ty : val :=
    fn: [] :=
      let: "arcbox" := new [ #(2 + ty.(ty_size))%nat ] in
      let: "w" := new [ #1 ] in
      "arcbox" +ₗ #0 <- #0;;
      "arcbox" +ₗ #1 <- #1;;
      "w" <- "arcbox";;
      return: ["w"].

  Lemma weak_new_type ty :
    typed_val (weak_new ty) (fn(∅) → weak ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg. simpl_subst.
    iApply (type_new (2 + ty.(ty_size))); [solve_typing..|]; iIntros (rcbox); simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (rc); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrc [Hrcbox _]]". rewrite !tctx_hasty_val.
    iDestruct (ownptr_uninit_own with "Hrcbox")
      as (lrcbox vlrcbox) "(% & Hrcbox↦ & Hrcbox†)". subst rcbox. inv_vec vlrcbox=>??? /=.
    iDestruct (heap_mapsto_vec_cons with "Hrcbox↦") as "[Hrcbox↦0 Hrcbox↦1]".
    iDestruct (heap_mapsto_vec_cons with "Hrcbox↦1") as "[Hrcbox↦1 Hrcbox↦2]".
    rewrite shift_loc_assoc.
    iDestruct (ownptr_uninit_own with "Hrc") as (lrc vlrc) "(% & Hrc↦ & Hrc†)". subst rc.
    inv_vec vlrc=>?. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lft_create with "LFT") as (ν) "[Hν Hν†]"; first done.
    wp_bind (_ +ₗ _)%E. iSpecialize ("Hν†" with "Hν").
    iApply wp_mask_mono; last iApply (wp_step_fupd with "Hν†"); [set_solver-..|].
    wp_op. iIntros "#H† !>". rewrite shift_loc_0. wp_write. wp_op. wp_write. wp_write.
    iApply (type_type _ _ _ [ #lrc ◁ box (weak ty)]
            with "[] LFT HE Hna HL Hk [>-]"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val' //=. iFrame.
      iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
      iMod (create_weak (P1 ν) (P2 lrcbox ty.(ty_size))
            with "Hrcbox↦0 Hrcbox↦1 [-]") as (γ) "[Ha Htok]".
      { rewrite freeable_sz_full_S. iFrame. iExists _. iFrame.
        by rewrite vec_to_list_length. }
      iExists γ, ν. iFrame. iSplitL; first by auto. iIntros "!>!>!> Hν".
      iDestruct (lft_tok_dead with "Hν H†") as "[]". }
    iApply type_jump; solve_typing.
  Qed.

  (* Code : deref *)
  Definition arc_deref : val :=
    fn: ["arc"] :=
      let: "x" := new [ #1 ] in
      let: "arc'" := !"arc" in
      "x" <- (!"arc'" +ₗ #2);;
      delete [ #1; "arc" ];; return: ["x"].

  Lemma arc_deref_type ty :
    typed_val arc_deref (fn(∀ α, ∅; &shr{α}(arc ty)) → &shr{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (x); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [#Hrc' [Hx _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock.
    iDestruct (ownptr_uninit_own with "Hx") as (lrc2 vlrc2) "(% & Hx & Hx†)".
    subst x. inv_vec vlrc2=>?. rewrite heap_mapsto_vec_singleton.
    destruct rc' as [[|rc'|]|]; try done. simpl of_val.
    iDestruct "Hrc'" as (l') "[Hrc' #Hdelay]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hdelay" with "[] Hα1"); last iApply (wp_step_fupd with "Hdelay"); [done..|].
    iMod (frac_bor_acc with "LFT Hrc' Hα2") as (q') "[Hrc'↦ Hclose2]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose2" with "[$Hrc'↦]") as "Hα2". iIntros "!> [Hα1 #Hproto] !>".
    iDestruct "Hproto" as (γ ν q'') "#(Hαν & Hpersist & _)".
    iDestruct "Hpersist" as "(_ & [Hshr|Hν†] & _)"; last first.
    { iMod (lft_incl_dead with "Hαν Hν†") as "Hα†". done.
      iDestruct (lft_tok_dead with "Hα1 Hα†") as "[]". }
    wp_op. wp_write. iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ rcx ◁ box (&shr{α}(arc ty)); #lrc2 ◁ box (&shr{α}ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame "Hrcx". iFrame "Hx†". iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "Hx". iApply (ty_shr_mono with "[] Hshr").
      iApply lft_incl_glb; [done|]. iApply elctx_interp_ty_outlives_E.
      rewrite !elctx_interp_app /=. iDestruct "HE" as "(_ & [[_ $] _] & _)". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Code : getters *)
  Definition arc_strong_count : val :=
    fn: ["arc"] :=
      let: "r" := new [ #1 ] in
      let: "arc'" := !"arc" in
      let: "arc''" := !"arc'" in
      "r" <- strong_count ["arc''"];;
      delete [ #1; "arc" ];; return: ["r"].

  Lemma arc_strong_count_type ty :
    typed_val arc_strong_count (fn(∀ α, ∅; &shr{α}(arc ty)) → int).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|]. wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". clear q'. iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q') "#(Hαν & Hpersist & Hrctokb)". iModIntro. wp_let.
    wp_apply (strong_count_spec (P1 ν) (P2 l' ty.(ty_size)) _ _ _ (q.[α])%I
       with "[] [] [$Hα1 $Hα2]"); first by iDestruct "Hpersist" as "[$ _]".
    { iIntros "!> Hα".
      iMod (at_bor_acc_tok with "LFT Hrctokb Hα") as "[>Htok Hclose1]"; [solve_ndisj..|].
      iExists _. iFrame. iMod fupd_intro_mask' as "Hclose2"; last iModIntro. set_solver.
      iIntros "Htok". iMod "Hclose2" as "_". by iApply "Hclose1". }
    iIntros (c) "[Hα _]". iMod ("Hclose1" with "Hα HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(arc ty)); #c ◁ int; r ◁ box (uninit 1)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition arc_weak_count : val :=
    fn: ["arc"] :=
      let: "r" := new [ #1 ] in
      let: "arc'" := !"arc" in
      let: "arc''" := !"arc'" in
      "r" <- weak_count ["arc''"];;
      delete [ #1; "arc" ];; return: ["r"].

  Lemma arc_weak_count_type ty :
    typed_val arc_weak_count (fn(∀ α, ∅; &shr{α}(arc ty)) → int).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|]. wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". clear q'. iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q') "#(Hαν & Hpersist & Hrctokb)". iModIntro. wp_let.
    wp_apply (weak_count_spec (P1 ν) (P2 l' ty.(ty_size)) _ _ _ (q.[α])%I
       with "[] [] [$Hα1 $Hα2]"); first by iDestruct "Hpersist" as "[$ _]".
    { iIntros "!> Hα".
      iMod (at_bor_acc_tok with "LFT Hrctokb Hα") as "[>Htok Hclose1]"; [solve_ndisj..|].
      iExists _. iFrame. iMod fupd_intro_mask' as "Hclose2"; last iModIntro. set_solver.
      iIntros "Htok". iMod "Hclose2" as "_". by iApply "Hclose1". }
    iIntros (c) "[Hα _]". iMod ("Hclose1" with "Hα HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(arc ty)); #c ◁ int; r ◁ box (uninit 1)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Code : clone, [up/down]grade. *)
  Definition arc_clone : val :=
    fn: ["arc"] :=
      let: "r" := new [ #1 ] in
      let: "arc'" := !"arc" in
      let: "arc''" := !"arc'" in
      clone_arc ["arc''"];;
      "r" <- "arc''";;
      delete [ #1; "arc" ];; return: ["r"].

  Lemma arc_clone_type ty :
    typed_val arc_clone (fn(∀ α, ∅; &shr{α}(arc ty)) → arc ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|]. wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". clear q'. iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q') "#(Hαν & Hpersist & Hrctokb)". iModIntro. wp_let.
    wp_apply (clone_arc_spec (P1 ν) (P2 l' ty.(ty_size)) _ _ _ (q.[α])%I
       with "[] [] [$Hα1 $Hα2]"); first by iDestruct "Hpersist" as "[$ _]".
    { iIntros "!> Hα".
      iMod (at_bor_acc_tok with "LFT Hrctokb Hα") as "[>Htok Hclose1]"; [solve_ndisj..|].
      iExists _. iFrame. iMod fupd_intro_mask' as "Hclose2"; last iModIntro. set_solver.
      iIntros "Htok". iMod "Hclose2" as "_". by iApply "Hclose1". }
    iIntros (q'') "[Hα Hown]". wp_seq. iMod ("Hclose1" with "Hα HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(arc ty)); #l' ◁ arc ty; r ◁ box (uninit 1)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. simpl. unfold shared_arc_own. auto 10 with iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition weak_clone : val :=
    fn: ["w"] :=
      let: "r" := new [ #1 ] in
      let: "w'" := !"w" in
      let: "w''" := !"w'" in
      clone_weak ["w''"];;
      "r" <- "w''";;
      delete [ #1; "w" ];; return: ["r"].

  Lemma weak_clone_type ty :
    typed_val weak_clone (fn(∀ α, ∅; &shr{α}(weak ty)) → weak ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|]. wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". clear q'. iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν) "#[Hpersist Hrctokb]". iModIntro. wp_let.
    wp_apply (clone_weak_spec (P1 ν) (P2 l' ty.(ty_size)) _ _ _ (q.[α])%I
       with "[] [] [$Hα1 $Hα2]"); first by iDestruct "Hpersist" as "[$ _]".
    { iIntros "!> Hα".
      iMod (at_bor_acc_tok with "LFT Hrctokb Hα") as "[>$ Hclose1]"; [solve_ndisj..|].
      iMod fupd_intro_mask' as "Hclose2"; last iModIntro. set_solver.
      iIntros "Htok". iMod "Hclose2" as "_". by iApply "Hclose1". }
    iIntros "[Hα Hown]". wp_seq. iMod ("Hclose1" with "Hα HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(weak ty)); #l' ◁ weak ty; r ◁ box (uninit 1) ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. simpl. eauto 10 with iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition downgrade : val :=
    fn: ["arc"] :=
      let: "r" := new [ #1 ] in
      let: "arc'" := !"arc" in
      let: "arc''" := !"arc'" in
      downgrade ["arc''"];;
      "r" <- "arc''";;
      delete [ #1; "arc" ];; return: ["r"].

  Lemma downgrade_type ty :
    typed_val downgrade (fn(∀ α, ∅; &shr{α}(arc ty)) → weak ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|]. wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". clear q'. iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q') "#(Hαν & Hpersist & Hrctokb)". iModIntro. wp_let.
    wp_apply (downgrade_spec (P1 ν) (P2 l' ty.(ty_size)) _ _ _ (q.[α])%I
              with "[] [] [$Hα1 $Hα2]"); first by iDestruct "Hpersist" as "[$ _]".
    { iIntros "!> Hα".
      iMod (at_bor_acc_tok with "LFT Hrctokb Hα") as "[>Htok Hclose1]"; [solve_ndisj..|].
      iExists _. iFrame. iMod fupd_intro_mask' as "Hclose2"; last iModIntro. set_solver.
      iIntros "Htok". iMod "Hclose2" as "_". by iApply "Hclose1". }
    iIntros "[Hα Hown]". wp_seq. iMod ("Hclose1" with "Hα HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(arc ty)); #l' ◁ weak ty; r ◁ box (uninit 1) ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. simpl. eauto 10 with iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition upgrade : val :=
    fn: ["w"] :=
      let: "r" := new [ #2 ] in
      let: "w'" := !"w" in
      let: "w''" := !"w'" in
      if: upgrade ["w''"] then
        "r" <-{Σ some} "w''";;
        delete [ #1; "w" ];; return: ["r"]
      else
        "r" <-{Σ none} ();;
        delete [ #1; "w" ];; return: ["r"].

  Lemma upgrade_type ty :
    typed_val upgrade (fn(∀ α, ∅; &shr{α}(weak ty)) → option (arc ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 2); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|]. wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". clear q'. iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν) "#[Hpersist Hrctokb]". iModIntro. wp_let.
    wp_apply (upgrade_spec (P1 ν) (P2 l' ty.(ty_size)) _ _ _ (q.[α])%I
              with "[] [] [$Hα1 $Hα2]"); first by iDestruct "Hpersist" as "[$ _]".
    { iIntros "!> Hα".
      iMod (at_bor_acc_tok with "LFT Hrctokb Hα") as "[>$ Hclose1]"; [solve_ndisj..|].
      iMod fupd_intro_mask' as "Hclose2"; last iModIntro. set_solver.
      iIntros "Htok". iMod "Hclose2" as "_". by iApply "Hclose1". }
    iIntros ([] q') "[Hα Hown]"; wp_if; iMod ("Hclose1" with "Hα HL") as "HL".
    - (* Finish up the proof (sucess). *)
      iApply (type_type _ _ _ [ x ◁ box (&shr{α}(weak ty)); #l' ◁ arc ty;
                                r ◁ box (uninit 2) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
        unlock. iFrame. simpl. unfold shared_arc_own. eauto 10 with iFrame. }
      iApply (type_sum_assign (option (arc ty))); [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    - (* Finish up the proof (fail). *)
      iApply (type_type _ _ _ [ x ◁ box (&shr{α}(weak ty)); r ◁ box (uninit 2) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
        unlock. iFrame. }
      iApply (type_sum_unit (option (arc ty))); [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  (* Code : drop *)
  Definition arc_drop ty : val :=
    fn: ["arc"] :=
      let: "r" := new [ #(option ty).(ty_size) ] in
      let: "arc'" := !"arc" in
      "r" <-{Σ none} ();;
      (if: drop_arc ["arc'"] then
         "r" <-{ty.(ty_size),Σ some} !("arc'" +ₗ #2);;
         if: drop_weak ["arc'"] then
           delete [ #(2 + ty.(ty_size)); "arc'" ]
         else #☠
       else #☠);;
      delete [ #1; "arc"];; return: ["r"].

  Lemma arc_drop_type ty :
    typed_val (arc_drop ty) (fn(∅; arc ty) → option ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (_ ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new (option ty).(ty_size)); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iApply (type_sum_unit (option ty)); [solve_typing..|].
    iIntros (tid) "#LFT #HE Hna HL Hk [Hr [Hrcx [Hrc' _]]]".
    rewrite !tctx_hasty_val. destruct rc' as [[|rc'|]|]=>//=.
    iAssert (shared_arc_own rc' ty tid ∗ llctx_interp [ϝ ⊑ₗ []] 1)%I
      with "[>Hrc' HL]" as "[Hrc' HL]".
    { iDestruct "Hrc'" as "[?|$]"; last done.
      iMod (lctx_lft_alive_tok ty_lft ty with "HE HL")
        as (?) "(Htok & HL & Hclose)"; [done| |].
      { change (ty_outlives_E (arc ty)) with (ty_outlives_E ty).
        eapply (lctx_lft_alive_incl _ _ ϝ); first solve_typing.
        iIntros (?) "_ !>". rewrite !elctx_interp_app /=.
        iIntros "(_ & _ & [? _] & _ & _)". by iApply elctx_interp_ty_outlives_E. }
      iMod (arc_own_share with "LFT Htok [$]") as "[Htok $]"; first solve_ndisj.
      by iApply ("Hclose" with "Htok"). }
    iDestruct "Hrc'" as (γ ν q) "(#Hpersist & Htok & Hν)".
    wp_bind (drop_arc _). iApply (drop_arc_spec with "[] [$Htok Hν]");
      [by iDestruct "Hpersist" as "[$?]"|done|].
    iNext. iIntros (b) "Hdrop". wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ _, ty_own (box (option ty)) tid [r])%I with "[Hdrop Hr]").
    { destruct b; wp_if=>//. destruct r as [[]|]; try done.
      (* FIXME: 'simpl' reveals a match here.  Didn't we forbid that for ty_own? *)
      rewrite {3}[option]lock. simpl. rewrite -{2 3}lock. (* FIXME: Tried using contextual pattern, did not work. *)
      iDestruct "Hr" as "[Hr ?]". iDestruct "Hr" as ([|d vl]) "[H↦ Hown]";
        first by iDestruct "Hown" as (???) "[>% ?]".
      rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[H↦0 H↦1]".
      iDestruct "Hpersist" as "(? & ? & H†)". wp_bind (_ <- _)%E.
      iDestruct "Hdrop" as "[Hν Hdrop]". iSpecialize ("H†" with "Hν").
      iApply wp_mask_mono; last iApply (wp_step_fupd with "H†"); first done.
      { set_solver-. (* FIXME [solve_ndisj] fails *) }
      iDestruct "Hown" as (???) "(_ & Hlen & _)". wp_write. iIntros "(#Hν & Hown & H†)!>".
      wp_seq. wp_op. wp_op. iDestruct "Hown" as (?) "[H↦ Hown]".
      iDestruct (ty_size_eq with "Hown") as %?. rewrite Max.max_0_r.
      iDestruct "Hlen" as %[= ?]. wp_apply (wp_memcpy with "[$H↦1 $H↦]"); [congruence..|].
      iIntros "[? Hrc']". wp_seq. iMod ("Hdrop" with "[Hrc' H†]") as "Htok".
      { unfold P2. auto with iFrame. }
      wp_apply (drop_weak_spec with "[//] Htok"). unlock. iIntros ([]); last first.
      { iIntros "_". wp_if. unlock. iFrame. iExists (_::_). rewrite heap_mapsto_vec_cons.
        iFrame. iExists 1%nat, _, []. rewrite /= !right_id_L Max.max_0_r.
        auto 10 with iFrame. }
      iIntros "([H† H1] & H2 & H3)". iDestruct "H1" as (vl1) "[H1 Heq]".
      iDestruct "Heq" as %<-. wp_if.
      wp_apply (wp_delete _ _ _ (_::_::vl1) with "[H1 H2 H3 H†]").
      { simpl. lia. }
      { rewrite 2!heap_mapsto_vec_cons shift_loc_assoc. auto with iFrame. }
      iFrame. iIntros "_". iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame.
      iExists 1%nat, _, []. rewrite !right_id_L. iFrame. iSplit; [by auto|simpl].
      auto with lia. }
    iIntros (?) "Hr". wp_seq.
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); r ◁ box (option ty) ]
            with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val. unlock. iFrame.
      by rewrite tctx_hasty_val. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition weak_drop ty : val :=
    fn: ["arc"] :=
      let: "r" := new [ #0] in
      let: "arc'" := !"arc" in
      (if: drop_weak ["arc'"] then delete [ #(2 + ty.(ty_size)); "arc'" ]
       else #☠);;
      delete [ #1; "arc"];; return: ["r"].

  Lemma weak_drop_type ty :
    typed_val (weak_drop ty) (fn(∅; weak ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (_ ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new 0); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[r]]lock. destruct rc' as [[|rc'|]|]=>//=.
    iDestruct "Hrc'" as (γ ν) "[#Hpersist Htok]". wp_bind (drop_weak _).
    iApply (drop_weak_spec with "[] [Htok]"); [by iDestruct "Hpersist" as "[$?]"|by auto|].
    iIntros "!> * Hdrop". wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ _, True)%I with "[Hdrop]").
    { destruct b; wp_if=>//. iDestruct "Hdrop" as "((? & H↦) & ? & ?)".
      iDestruct "H↦" as (vl) "[? Heq]". iDestruct "Heq" as %<-.
      wp_apply (wp_delete _ _ _ (_::_::vl) with "[-]"); [simpl;lia| |done].
      rewrite !heap_mapsto_vec_cons shift_loc_assoc. iFrame. }
    iIntros (?) "_". wp_seq.
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); r ◁ box (uninit 0) ]
            with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val. unlock. iFrame.
      by rewrite tctx_hasty_val. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Code : other primitives *)
  Definition arc_try_unwrap ty : val :=
    fn: ["arc"] :=
      let: "r" := new [ #(Σ[ ty; arc ty ]).(ty_size) ] in
      let: "arc'" := !"arc" in
      if: try_unwrap ["arc'"] then
        (* Return content *)
        "r" <-{ty.(ty_size),Σ 0} !("arc'" +ₗ #2);;
        (* Decrement the "strong weak reference" *)
        (if: drop_weak ["arc'"] then delete [ #(2 + ty.(ty_size)); "arc'" ]
         else #☠);;
        delete [ #1; "arc"];; return: ["r"]
      else
        "r" <-{Σ 1} "arc'";;
        delete [ #1; "arc"];; return: ["r"].

  Lemma arc_try_unwrap_type ty :
    typed_val (arc_try_unwrap ty) (fn(∅; arc ty) → Σ[ ty; arc ty ]).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (_ ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new (Σ[ ty; arc ty ]).(ty_size));
      [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[r]]lock. destruct rc' as [[|rc'|]|]=>//=.
    iAssert (shared_arc_own rc' ty tid ∗ llctx_interp [ϝ ⊑ₗ []] 1)%I
      with "[>Hrc' HL]" as "[Hrc' HL]".
    { iDestruct "Hrc'" as "[?|$]"; last done.
      iMod (lctx_lft_alive_tok ty_lft ty with "HE HL")
        as (?) "(Htok & HL & Hclose)"; [done| |].
      { change (ty_outlives_E (arc ty)) with (ty_outlives_E ty).
        eapply (lctx_lft_alive_incl _ _ ϝ); first solve_typing.
        iIntros (?) "_ !>". rewrite !elctx_interp_app /=.
        iIntros "(_ & _ & [?_] & _ & _)". by iApply elctx_interp_ty_outlives_E. }
      iMod (arc_own_share with "LFT Htok [$]") as "[Htok $]"; first solve_ndisj.
      by iApply ("Hclose" with "Htok"). }
    iDestruct "Hrc'" as (γ ν q) "(#Hpersist & Htok & Hν)".
    wp_apply (try_unwrap_spec with "[] [Hν Htok]");
      [by iDestruct "Hpersist" as "[$?]"|iFrame|].
    iIntros ([]) "H"; wp_if.
    - iDestruct "H" as "[Hν Hend]". rewrite -(lock [r]). destruct r as [[|r|]|]=>//=.
      iDestruct "Hr" as "[Hr >Hfree]". iDestruct "Hr" as (vl0) "[>Hr Hown]".
      iDestruct "Hown" as ">Hlen".
      destruct vl0 as [|? vl0]=>//; iDestruct "Hlen" as %[=Hlen0].
      rewrite heap_mapsto_vec_cons. iDestruct "Hr" as "[Hr0 Hr1]".
      iDestruct "Hpersist" as "(Ha & _ & H†)". wp_bind (_ <- _)%E.
      iSpecialize ("H†" with "Hν").
      iApply wp_mask_mono; last iApply (wp_step_fupd with "H†"); first done.
      { (* FIXME [solve_ndisj] fails *) set_solver-. }
      wp_write. iIntros "(#Hν & Hown & H†) !>". wp_seq. wp_op. wp_op.
      rewrite -(firstn_skipn ty.(ty_size) vl0) heap_mapsto_vec_app.
      iDestruct "Hr1" as "[Hr1 Hr2]". iDestruct "Hown" as (vl) "[Hrc' Hown]".
      iDestruct (ty_size_eq with "Hown") as %Hlen.
      wp_apply (wp_memcpy with "[$Hr1 $Hrc']"); rewrite /= ?firstn_length_le; try lia.
      iIntros "[Hr1 Hrc']". wp_seq. wp_bind (drop_weak _).
      iMod ("Hend" with "[$H† Hrc']") as "Htok"; first by eauto.
      iApply (drop_weak_spec with "Ha Htok").
      iIntros "!> * Hdrop". wp_bind (if: _ then _ else _)%E.
      iApply (wp_wand _ _ _ (λ _, True)%I with "[Hdrop]").
      { destruct b; wp_if=>//. iDestruct "Hdrop" as "((? & H↦) & ? & ?)".
        iDestruct "H↦" as (vl') "[? Heq]". iDestruct "Heq" as %<-.
        wp_apply (wp_delete _ _ _ (_::_::vl') with "[-]"); [simpl; lia| |done].
        rewrite !heap_mapsto_vec_cons shift_loc_assoc. iFrame. }
      iIntros (?) "_". wp_seq.
      iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); #r ◁ box (Σ[ ty; arc ty ]) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val. unlock.
        iFrame. iCombine "Hr1" "Hr2" as "Hr1". iCombine "Hr0" "Hr1" as "Hr".
        rewrite -[in _ +ₗ ty.(ty_size)]Hlen -heap_mapsto_vec_app
                -heap_mapsto_vec_cons tctx_hasty_val' //. iFrame. iExists _. iFrame.
        iExists O, _, _. iSplit; first by auto. iFrame. iIntros "!> !% /=".
        rewrite app_length drop_length. lia. }
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    - iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); #rc' ◁ arc ty;
                                r ◁ box (uninit (Σ[ ty; arc ty ]).(ty_size)) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
        unlock. iFrame. iRight. iExists _, _, _. auto with iFrame. }
      iApply (type_sum_assign Σ[ ty; arc ty ]); [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition arc_get_mut : val :=
    fn: ["arc"] :=
      let: "r" := new [ #2 ] in
      let: "arc'" := !"arc" in
      let: "arc''" := !"arc'" in
      if: is_unique ["arc''"] then
        Skip;;
        (* Return content *)
        "r" <-{Σ some} "arc''" +ₗ #2;;
        delete [ #1; "arc"];; return: ["r"]
      else
        "r" <-{Σ none} ();;
        delete [ #1; "arc"];; return: ["r"].

  Lemma arc_get_mut_type ty :
    typed_val arc_get_mut (fn(∀ α, ∅; &uniq{α}(arc ty)) → option (&uniq{α}ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (α ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new 2); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[r]]lock.
    iDestruct "Hrc'" as "[#? Hrc']". destruct rc' as [[|rc'|]|]=>//=.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & HL & Hclose1)";
      [solve_typing..|].
    iMod (bor_exists with "LFT Hrc'") as (rcvl) "Hrc'"=>//.
    iMod (bor_sep with "LFT Hrc'") as "[Hrc'↦ Hrc]"=>//.
    destruct rcvl as [|[[|rc|]|][|]]; try by
      iMod (bor_persistent with "LFT Hrc Hα") as "[>[] ?]".
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_acc with "LFT Hrc'↦ Hα") as "[Hrc'↦ Hclose2]"=>//. wp_read.
    iMod ("Hclose2" with "Hrc'↦") as "[_ [Hα1 Hα2]]".
    iMod (bor_acc_cons with "LFT Hrc Hα1") as "[Hrc Hclose2]"=>//. wp_let.
    iAssert (shared_arc_own rc ty tid ∗ (q / 2).[α])%I with "[>Hrc Hα2]" as "[Hrc Hα2]".
    { iDestruct "Hrc" as "[Hrc|$]"=>//.
      iMod (lft_incl_acc with "[//] Hα2") as (q') "[Htok Hclose]"; [solve_ndisj|].
      iMod (arc_own_share with "LFT Htok Hrc") as "[Htok $]"; [solve_ndisj|].
      by iApply "Hclose". }
    iDestruct "Hrc" as (γ ν q') "[#(Hi & Hs & #Hc) Htoks]".
    wp_apply (is_unique_spec with "Hi Htoks"). iIntros ([]) "H"; wp_if.
    - iDestruct "H" as "(Hrc & Hrc1 & Hν)". iSpecialize ("Hc" with "Hν"). wp_bind Skip.
      iApply wp_mask_mono; last iApply (wp_step_fupd with "Hc"); first done.
      { (* FIXME [solve_ndisj] fails *) set_solver-. }
      wp_seq. iIntros "(#Hν & Hown & H†) !>". wp_seq.
      iMod ("Hclose2" with "[Hrc Hrc1 H†] Hown") as "[Hb Hα1]".
      { iIntros "!> Hown !>". iLeft. iFrame. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); #rc +ₗ #2 ◁ &uniq{α}ty;
                                r ◁ box (uninit 2) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                tctx_hasty_val' //. unlock. by iFrame. }
      iApply (type_sum_assign (option (&uniq{α}ty))); [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    - iMod ("Hclose2" with "[] [H]") as "[_ Hα1]";
        [by iIntros "!> H"; iRight; iApply "H"|iExists _, _, _; iFrame "∗#"|].
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); r ◁ box (uninit 2) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. unlock. iFrame. }
      iApply (type_sum_unit (option (&uniq{α}ty))); [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition arc_make_mut (ty : type) (clone : val) : val :=
    fn: ["arc"] :=
      let: "r" := new [ #1 ] in
      let: "arc'" := !"arc" in
      let: "arc''" := !"arc'" in
      (case: try_unwrap_full ["arc''"] of
       [ "r" <- "arc''" +ₗ #2;;
         delete [ #1; "arc"];; return: ["r"];

         let: "rcbox" := new [ #(2 + ty.(ty_size))%nat ] in
         "rcbox" +ₗ #0 <- #1;;
         "rcbox" +ₗ #1 <- #1;;
         "rcbox" +ₗ #2 <-{ty.(ty_size)} !"arc''" +ₗ #2;;
         "arc'" <- "rcbox";;
         "r" <- "rcbox" +ₗ #2;;
         delete [ #1; "arc"];; return: ["r"];

         letalloc: "x" <- "arc''" +ₗ #2 in
         letcall: "c" := clone ["x"]%E in (* FIXME : why do I need %E here ? *)
         let: "rcbox" := new [ #(2 + ty.(ty_size))%nat ] in
         "rcbox" +ₗ #0 <- #1;;
         "rcbox" +ₗ #1 <- #1;;
         "rcbox" +ₗ #2 <-{ty.(ty_size)} !"c";;
         delete [ #ty.(ty_size); "c"];;
         "arc'" <- "rcbox";;
         letalloc: "rcold" <- "arc''" in
         (* FIXME : here, we are dropping the old arc pointer. In the
            case another strong reference has been dropped while
            cloning, it is possible that we are actually dropping the
            last reference here. This means that we may have to drop an
            instance of [ty] here. Instead, we simply forget it. *)
         let: "drop" := arc_drop ty in
         letcall: "content" := "drop" ["rcold"]%E in
         delete [ #(option ty).(ty_size); "content"];;
         "r" <- "rcbox" +ₗ #2;;
         delete [ #1; "arc"];; return: ["r"]
       ]).

  Lemma arc_make_mut_type ty clone :
    typed_val clone (fn(∀ α, ∅; &shr{α}ty) → ty) →
    typed_val (arc_make_mut ty clone) (fn(∀ α, ∅; &uniq{α}(arc ty)) → &uniq{α} ty).
  Proof.
    intros Hclone E L. iApply type_fn; [solve_typing..|]. rewrite [(2 + ty_size ty)%nat]lock.
    iIntros "/= !>". iIntros (α ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[r]]lock.
    iDestruct "Hrc'" as "[#? Hrc']". destruct rc' as [[|rc'|]|]=>//=.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hrc' Hα1") as "[Hrc' Hclose2]"=>//.
    iDestruct "Hrc'" as (rcvl) "[Hrc'↦ Hrc]".
    destruct rcvl as [|[[|rc|]|][|]]; try by iDestruct "Hrc" as ">[]".
    rewrite heap_mapsto_vec_singleton. wp_read.
    iAssert (shared_arc_own rc ty tid ∗ (q / 2).[α])%I with "[>Hrc Hα2]" as "[Hrc Hα2]".
    { iDestruct "Hrc" as "[Hrc|$]"=>//.
      iMod (lft_incl_acc with "[//] Hα2") as (q') "[Htok Hclose]"; [solve_ndisj|].
      iMod (arc_own_share with "LFT Htok Hrc") as "[Htok $]"; [solve_ndisj|].
      by iApply "Hclose". }
    iDestruct "Hrc" as (γ ν q') "[#(Hi & Hs & #Hc) Htoks]". wp_let.
    wp_apply (try_unwrap_full_spec with "Hi Htoks"). iIntros (x).
    pose proof (fin_to_nat_lt x). destruct (fin_to_nat x) as [|[|[]]]; last lia.
    - iIntros "(Hrc0 & Hrc1 & HP1)". wp_case. wp_bind (_ +ₗ _)%E.
      iSpecialize ("Hc" with "HP1").
      iApply wp_mask_mono; last iApply (wp_step_fupd with "Hc"); first done.
      { (* FIXME [solve_ndisj] fails *) set_solver-. }
      wp_op. iIntros "(#Hν & Hrc2 & H†)". iModIntro.
      iMod ("Hclose2" with "[Hrc'↦ Hrc0 Hrc1 H†] Hrc2") as "[Hb Hα1]".
      { iIntros "!> Hrc2". iExists [_]. rewrite heap_mapsto_vec_singleton.
        iFrame. iLeft. by iFrame. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); #(rc +ₗ 2) ◁ &uniq{α}ty;
                                r ◁ box (uninit 1) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                tctx_hasty_val' //. unlock. by iFrame. }
      iApply type_assign; [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    - iIntros "[Hν Hweak]". wp_case. iSpecialize ("Hc" with "Hν"). wp_bind (new _).
      iApply wp_mask_mono; last iApply (wp_step_fupd with "Hc"); first done.
      { (* FIXME [solve_ndisj] fails *) set_solver-. }
      wp_apply wp_new=>//. lia. iIntros (l) "(H† & Hlvl) (#Hν & Hown & H†') !>".
      rewrite -!lock Nat2Z.id.
      wp_let. wp_op. rewrite !heap_mapsto_vec_cons shift_loc_assoc shift_loc_0.
      iDestruct "Hlvl" as "(Hrc0 & Hrc1 & Hrc2)". wp_write. wp_op. wp_write.
      wp_op. wp_op. iDestruct "Hown" as (vl) "[H↦ Hown]".
      iDestruct (ty_size_eq with "Hown") as %Hsz.
      wp_apply (wp_memcpy with "[$Hrc2 $H↦]").
      { by rewrite repeat_length. } { by rewrite Hsz. }
      iIntros "[H↦ H↦']". wp_seq. wp_write.
      iMod ("Hclose2" $! ((l +ₗ 2) ↦∗: ty_own ty tid)%I
        with "[Hrc'↦ Hrc0 Hrc1 H†] [H↦ Hown]") as "[Hb Hα1]"; [|by auto with iFrame|].
      { iIntros "!> H↦". iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
        iLeft. iFrame. iDestruct "H†" as "[?|%]"=>//. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      iApply (type_type _ _ _ [ rcx ◁ box (uninit 1); (#l +ₗ #2) ◁ &uniq{α}ty;
                                r ◁ box (uninit 1) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                tctx_hasty_val' //. unlock. by iFrame. }
      iApply type_assign; [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    - iIntros "[Htok Hν]". wp_case. wp_apply wp_new=>//.
      iIntros (l) "/= (H† & Hl)". wp_let. wp_op.
      rewrite heap_mapsto_vec_singleton. wp_write. wp_let.
      wp_bind (of_val clone).
      iApply (wp_wand with "[Hna]").
      { iApply (Hclone _ [] with "LFT HE Hna"); rewrite /llctx_interp /tctx_interp //. }
      clear Hclone clone. iIntros (clone) "(Hna & _ & [Hclone _])". rewrite tctx_hasty_val.
      iDestruct "Hs" as "[Hs|Hν']"; last by iDestruct (lft_tok_dead with "Hν Hν'") as "[]".
      iDestruct (lft_intersect_acc with "Hν Hα2") as (q'') "[Hαν Hclose3]".
      rewrite -[ν ⊓ α](right_id_L).
      iApply (type_call_iris _ [ν ⊓ α] (ν ⊓ α) [_] with
              "LFT HE Hna Hαν Hclone [Hl H†]"); [solve_typing| |].
      { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full.
        iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
        iApply ty_shr_mono; last done. iApply lft_intersect_mono; [|done].
        iApply lft_incl_refl. }
      iIntros ([[|cl|]|]) "Hna Hαν Hcl //". wp_rec.
      iDestruct "Hcl" as "[Hcl Hcl†]". iDestruct "Hcl" as (vl) "[Hcl↦ Hown]".
      iDestruct (ty_size_eq with "Hown") as %Hsz.
      iDestruct ("Hclose3" with "Hαν") as "[Hν Hα2]".
      wp_apply wp_new=>//. lia. iIntros (l') "(Hl'† & Hl')". wp_let. wp_op.
      rewrite shift_loc_0. rewrite -!lock Nat2Z.id.
      rewrite !heap_mapsto_vec_cons shift_loc_assoc.
      iDestruct "Hl'" as "(Hl' & Hl'1 & Hl'2)". wp_write. wp_op. wp_write. wp_op.
      wp_apply (wp_memcpy with "[$Hl'2 $Hcl↦]").
      { by rewrite repeat_length. } { by rewrite Hsz. }
      iIntros "[Hl'2 Hcl↦]". wp_seq. rewrite freeable_sz_full.
      wp_apply (wp_delete with "[$Hcl↦ Hcl†]");
        [lia|by replace (length vl) with (ty.(ty_size))|].
      iIntros "_". wp_seq. wp_write.
      iMod ("Hclose2" $! ((l' +ₗ 2) ↦∗: ty_own ty tid)%I with
          "[Hrc'↦ Hl' Hl'1  Hl'†] [Hl'2 Hown]") as "[Hl' Hα1]".
      { iIntros "!> H". iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
        iLeft. iFrame. iDestruct "Hl'†" as "[?|%]"=>//. }
      { iExists _.  iFrame. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      iApply (type_type _ _ _ [ #rc ◁ arc ty; #l' +ₗ #2 ◁ &uniq{α}ty;
                                r ◁ box (uninit 1); rcx ◁ box (uninit 1) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 3!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                !tctx_hasty_val' //. unlock. iFrame "∗#". iRight.
        iExists _, _, _. iFrame "∗#". }
      iApply type_letalloc_1; [solve_typing..|]. iIntros (rcold). simpl_subst.
      iApply type_let. apply arc_drop_type. solve_typing. iIntros (drop). simpl_subst.
      iApply (type_letcall ()); [solve_typing..|]. iIntros (content). simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_assign; [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.
End arc.
