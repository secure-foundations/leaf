From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree excl numbers.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option.
Set Default Proof Using "Type".

Definition rc_stR :=
  prodUR (optionUR (csumR (prodR fracR positiveR) (exclR unitO))) natUR.
Class rcG Σ :=
  RcG :> inG Σ (authR rc_stR).
Definition rcΣ : gFunctors := #[GFunctor (authR rc_stR)].
Global Instance subG_rcΣ {Σ} : subG rcΣ Σ → rcG Σ.
Proof. solve_inG. Qed.

Definition rc_tok q : authR rc_stR :=
  ◯ (Some $ Cinl (q, 1%positive), 0%nat).
Definition rc_dropping_tok : authR rc_stR :=
  ◯ (Some $ Cinr $ Excl (), 0%nat).
Definition weak_tok : authR rc_stR := ◯ (None, 1%nat).

Definition rcN := lrustN .@ "rc".
Definition rc_invN := rcN .@ "inv".
Definition rc_shrN := rcN .@ "shr".

Section rc.
  Context `{!typeG Σ, !rcG Σ}.

  (* The RC can be in four different states :
       - The living state, meaning that some strong reference exists. The
         authoritative state is something like (Some (Cinl (q, strong)), weak),
         where q is the total fraction owned by strong references, strong is
         the number of strong references and weak is the number of weak
         references.
       - The "dropping" state, meaning that the last strong reference has been
         dropped, and that the content in being dropped. The authoritative
         state is something like (Some (Cinr (Excl ())), weak), where weak is
         the number of weak references. The client owning the Excl also owns
         the content of the box.
         In our case, this state is not really necesary, because we do not
         properly support dropping the content, but just copy it out of the RC
         box. However, including it is more realistic, and this state is
         still necessary for Arc anyway.
       - The weak state, meaning that there only exists weak references. The
         authoritative state is something like (None, weak), where weak is the
         number of weak references.
       - The dead state, meaning that no reference exist anymore. The
         authoritative state is something like (None, 0).

   Note that when we are in the living or dropping states, the weak reference
   count stored in the heap is actually one plus the actual number of weak
   references. This hack (which also exists in Rust's implementation) makes the
   implementation of weak_drop easier, because it does not have to check the
   strong count. *)

  Definition rc_inv tid ν (γ : gname) (l : loc) (ty : type) : iProp Σ :=
    (∃ st : rc_stR, own γ (● st) ∗
      match st with
      | (Some (Cinl (q, strong)), weak) => ∃ q',
        l ↦ #(Zpos strong) ∗ (l +ₗ 1) ↦ #(S weak) ∗ † l…(2 + ty.(ty_size)) ∗
          ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν] ∗
          (* We keep this view shift decomposed because we store the persistent
             part in ty_own, to make it available with one step less. *)
          ([†ν] ={↑lftN}=∗ ▷ (l +ₗ 2) ↦∗: ty.(ty_own) tid)
      | (Some (Cinr _), weak) =>
        l ↦ #0 ∗ (l +ₗ 1) ↦ #(S weak)
      | (None, (S _) as weak) =>
        l ↦ #0 ∗ (l +ₗ 1) ↦ #weak ∗ † l…(2 + ty.(ty_size)) ∗
          (l +ₗ 2) ↦∗: λ vl, ⌜length vl = ty.(ty_size)⌝
      | _ => True
      end)%I.

  Definition rc_persist tid ν (γ : gname) (l : loc) (ty : type) : iProp Σ :=
    tc_opaque (∃ ty', ▷ type_incl ty' ty ∗
              na_inv tid rc_invN (rc_inv tid ν γ l ty') ∗
              (* We use this disjunction, and not simply [ty_shr] here,
                 because [weak_new] cannot prove ty_shr, even for a dead
                 lifetime. *)
              (ty.(ty_shr) (ν ⊓ ty_lft ty) tid (l +ₗ 2) ∨ [†ν]) ∗
              □ (1.[ν] ={↑lftN ∪ ↑lft_userN}[↑lft_userN]▷=∗ [†ν]))%I.

  Global Instance rc_persist_persistent tid ν γ l ty : Persistent (rc_persist tid ν γ l ty).
  Proof. unfold rc_persist, tc_opaque. apply _. Qed.

  Lemma rc_persist_type_incl tid ν γ l ty1 ty2:
    type_incl ty1 ty2 -∗ rc_persist tid ν γ l ty1 -∗ rc_persist tid ν γ l ty2.
  Proof.
    iIntros "#Hincl H". iDestruct "H" as (ty) "#(?&?& Hs &?)". iExists ty.
    iFrame "#". iSplit.
    - iNext. by iApply type_incl_trans.
    - iDestruct "Hs" as "[?|?]"; last auto.
      iLeft. iDestruct "Hincl" as "(_&Hlft&_&Hincls)". iApply "Hincls".
      iApply (ty_shr_mono with "[] [//]"). iApply lft_intersect_mono; [|done].
      iApply lft_incl_refl.
  Qed.

  Program Definition rc (ty : type) :=
    {| ty_size := 1;
       ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           (* The ty_own part of the rc type cointains either the
              shared protocol or the full ownership of the
              content. The reason is that get_mut does not have the
              masks to rebuild the invariants. *)
           (l ↦ #1 ∗ (l +ₗ 1) ↦ #1 ∗ † l…(2 + ty.(ty_size)) ∗
            ▷ (l +ₗ 2) ↦∗: ty.(ty_own) tid) ∨
           (∃ γ ν q, rc_persist tid ν γ l ty ∗ own γ (rc_tok q) ∗ q.[ν])
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l' : loc), &frac{κ} (λ q, l ↦{q} #l') ∗
           □ ∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ]
             ={F}[F∖↑shrN]▷=∗ q.[κ] ∗ ∃ γ ν q', κ ⊑ ν ∗
                rc_persist tid ν γ l' ty ∗
                &na{κ, tid, rc_shrN}(own γ (rc_tok q'))
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT #Hout Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iFrame "Htok". iExists _. iFrame "#". rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    set (C := (∃ _ _ _, _ ∗ _ ∗ &na{_,_,_} _)%I).
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ C)%I
          with "[Hpbown]") as "#Hinv"; first by iLeft.
    iIntros "!> !>" (F q') "% [Htok1 Htok2]".
    iMod (inv_acc with "Hinv") as "[INV Hclose1]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ} _)%I with "[Hbtok]" as "Hb".
      { rewrite bor_unfold_idx. iExists _. by iFrame. }
      iClear "H↦ Hinv Hpb".
      iMod (bor_acc_cons with "LFT Hb Htok1") as "[HP Hclose2]"; first solve_ndisj.
      set (X := (∃ _ _ _, _)%I). iModIntro. iNext.
      iAssert (X ∗ (q'/2).[κ])%I with "[>HP Htok2]" as "[HX $]".
      { iDestruct "HP" as "[(Hl'1 & Hl'2 & H† & Hown)|$]"; last done.
        iMod (lft_create with "LFT") as (ν) "[[Hν1 Hν2] #Hν†]"; first solve_ndisj.
        (* TODO: We should consider changing the statement of
           bor_create to dis-entangle the two masks such that this is no
          longer necessary. *)
        iApply (fupd_mask_mono (↑lftN)); first solve_ndisj.
        iMod (bor_create with "LFT Hown") as "[HP HPend]"; first solve_ndisj.
        iMod (own_alloc (● (Some $ Cinl ((1/2)%Qp, 1%positive), 0%nat) ⋅
                         ◯ (Some $ Cinl ((1/2)%Qp, 1%positive), 0%nat))) as (γ) "[Ha Hf]".
        { by apply auth_both_valid_discrete. }
        iMod (na_inv_alloc tid _ _ (rc_inv tid ν γ l' ty)
              with "[Ha Hν2 Hl'1 Hl'2 H† HPend]") as "#?".
        { rewrite /rc_inv. iExists (Some $ Cinl (_, _), _). iFrame. iExists _.
          iFrame "#∗". rewrite Qp_div_2; auto. }
        iMod (lft_incl_acc with "Hout Htok2") as (q'') "[Htok Hclose]"; [done|].
        iDestruct (lft_intersect_acc with "Hν1 Htok") as (q''') "[Htok Hclose']".
        iMod (ty_share with "LFT [] [HP] Htok") as "[? Htok]"; first solve_ndisj.
        { iApply lft_intersect_incl_r. }
        { iApply (bor_shorten with "[] HP" ). iApply lft_intersect_incl_l. }
        iDestruct ("Hclose'" with "Htok") as "[? Htok]".
        iMod ("Hclose" with "Htok") as "$".
        iExists _, _, _. iFrame. iExists ty. iFrame "#". iSplitR; last by auto.
          by iApply type_incl_refl. }
      iDestruct "HX" as (γ ν q'') "(#Hpersist & Hrctok)".
      iMod ("Hclose2" with "[] Hrctok") as "[HX $]".
      { unfold X. iIntros "!> [??] !>". iNext. iRight. do 3 iExists _.
        iFrame "#∗". }
      iAssert C with "[>HX]" as "#$".
      { iExists _, _, _. iFrame "Hpersist".
        iMod (bor_sep with "LFT HX") as "[Hrc Hlft]"; first solve_ndisj.
        iDestruct (frac_bor_lft_incl with "LFT [> Hlft]") as "$".
        { iApply (bor_fracture with "LFT"); first solve_ndisj. by rewrite Qp_mul_1_r. }
        iApply (bor_na with "Hrc"); solve_ndisj. }
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
    - by iApply na_bor_shorten.
  Qed.

  Global Instance rc_type_contractive : TypeContractive rc.
    split.
    - apply (type_lft_morphism_add _ static [] []).
      + intros. rewrite left_id. iApply lft_equiv_refl.
      + intros. by rewrite /= /elctx_interp /= left_id right_id.
    - done.
    - intros n ty1 ty2 Hsz Hl HE Ho Hs tid vl. destruct vl as [|[[|l|]|] [|]]=>//=.
      rewrite /rc_persist /type_incl Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ α l, ty1.(ty_shr) (α ⊓ ty_lft ty1) tid l ≡{n}≡
                     ty2.(ty_shr) (α ⊓ ty_lft ty2) tid l) as Hs'.
      { intros. rewrite Hs. apply equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      simpl. repeat (apply Ho || apply dist_S, Hs || apply Hs' ||
                     apply equiv_dist, lft_incl_equiv_proper_l, Hl ||
                     f_contractive || f_equiv).
    - intros n ty1 ty2 Hsz Hl HE Ho Hs κ tid l. rewrite /= /rc /rc_persist /type_incl Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ l α, dist_later n (ty1.(ty_shr) (α ⊓ ty_lft ty1) tid l)
                                  (ty2.(ty_shr) (α ⊓ ty_lft ty2) tid l)) as Hs'.
      { intros. rewrite Hs. apply dist_dist_later, equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      simpl. repeat (apply Ho || apply dist_S, Hs || apply Hs' ||
                     apply equiv_dist, lft_incl_equiv_proper_l, Hl ||
                     f_contractive || f_equiv).
  Qed.

  Global Instance rc_ne : NonExpansive rc.
    unfold rc, rc_persist, type_incl.
    intros n x y Hxy. constructor; [done|by apply Hxy..| |].
    - intros. rewrite ![X in X {| ty_own := _ |}]/ty_own /=.
      solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
    - solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
  Qed.

  Lemma rc_subtype ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (rc ty1) (rc ty2).
  Proof.
    iIntros "#Hincl". iPoseProof "Hincl" as "(#Hsz & #Hl & #Hoincl & #Hsincl)".
    iSplit; [done|]. iSplit; [done|]. iSplit; iModIntro.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      iDestruct "Hvl" as "[(Hl1 & Hl2 & H† & Hc) | Hvl]".
      { iLeft. iFrame. iDestruct "Hsz" as %->.
        iFrame. iApply (heap_mapsto_pred_wand with "Hc"). iApply "Hoincl". }
      iDestruct "Hvl" as (γ ν q) "(#Hpersist & Htk & Hν)".
      iRight. iExists _, _, _. iFrame "#∗". by iApply rc_persist_type_incl.
    - iIntros "* #Hshr". iDestruct "Hshr" as (l') "[Hfrac Hshr]". iExists l'.
      iIntros "{$Hfrac} !> * % Htok". iMod ("Hshr" with "[% //] Htok") as "{Hshr} H".
      iModIntro. iNext. iMod "H" as "[$ H]".
      iDestruct "H" as (γ ν q') "(Hlft & Hpersist & Hna)".
      iExists _, _, _. iFrame. by iApply rc_persist_type_incl.
  Qed.

  Global Instance rc_mono E L :
    Proper (subtype E L ==> subtype E L) rc.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!> #HE". iApply rc_subtype. by iApply "Hsub".
  Qed.
  Global Instance rc_proper E L :
    Proper (eqtype E L ==> eqtype E L) rc.
  Proof. intros ??[]. by split; apply rc_mono. Qed.
End rc.

Section code.
  Context `{!typeG Σ, !rcG Σ}.

  Lemma rc_check_unique ty F tid (l : loc) :
    ↑rc_invN ⊆ F →
    {{{ na_own tid F ∗ ty_own (rc ty) tid [ #l ] }}}
    !#l
    {{{ strong, RET #(Zpos strong); l ↦ #(Zpos strong) ∗
        (((⌜strong = 1%positive⌝ ∗
           (∃ weak : Z, (l +ₗ 1) ↦ #weak ∗
             ((⌜weak = 1⌝ ∗
               |={⊤}[↑lft_userN]▷=> † l…(2 + ty.(ty_size)) ∗
                          ▷ (l +ₗ 2) ↦∗: ty.(ty_own) tid ∗ na_own tid F) ∨
             (⌜weak > 1⌝ ∗
              ((l ↦ #1 -∗ (l +ₗ 1) ↦ #weak
                ={⊤}=∗ na_own tid F ∗ ty_own (rc ty) tid [ #l ]) ∧
               (l ↦ #0 -∗ (l +ₗ 1) ↦ #(weak - 1)
                ={⊤}[↑lft_userN]▷=∗ ▷ (l +ₗ 2) ↦∗: ty.(ty_own) tid ∗
                ((l +ₗ 2) ↦∗: (λ vl, ⌜length vl = ty.(ty_size)⌝)
                 ={⊤}=∗ na_own tid F)))))) ∧
           (l ↦ #0 ={⊤}[↑lft_userN]▷=∗
             ▷ (l +ₗ 2) ↦∗: ty.(ty_own) tid ∗ † l…(2 + ty.(ty_size)) ∗ na_own tid F ∗
             (na_own tid F ={⊤}=∗ ∃ weak : Z,
                (l +ₗ 1) ↦ #weak ∗
                ((⌜weak = 1⌝ ∗ l ↦ #0 ∗ na_own tid F) ∨
                 (⌜weak > 1⌝ ∗
                   († l…(2 + ty.(ty_size)) -∗ (l +ₗ 1) ↦ #(weak-1) -∗
                    (l +ₗ 2) ↦∗: (λ vl, ⌜length vl = ty.(ty_size)⌝)
                    ={⊤}=∗ na_own tid F))))))
         ) ∨
         (⌜(1 < strong)%positive⌝ ∗
           ((l ↦ #(Zpos strong) ={⊤}=∗ na_own tid F ∗ ty_own (rc ty) tid [ #l ]) ∧
            (l ↦ #(Zpos strong - 1) ={⊤}=∗ na_own tid F))))
     }}}.
  Proof.
    iIntros (? Φ) "[Hna [(Hl1 & Hl2 & H† & Hown)|Hown]] HΦ".
    - wp_read. iApply "HΦ". iFrame "Hl1". iLeft. iSplit. done. iSplit.
      + iExists _. iFrame "Hl2". iLeft. iFrame. iSplit; first done.
        iApply step_fupd_intro; auto.
      + iIntros "Hl1". iFrame. iApply step_fupd_intro; first done.
        auto 10 with iFrame.
    - iDestruct "Hown" as (γ ν q) "(#Hpersist & Htok & Hν1)".
      iPoseProof "Hpersist" as (ty') "(Hincl & Hinv & _ & #Hνend)".
      iMod (na_inv_acc with "Hinv Hna") as "(Hproto & Hna & Hclose)"; [solve_ndisj..|].
      iDestruct "Hproto" as ([st weak]) "[>Hst Hproto]".
      iDestruct (own_valid_2 with "Hst Htok") as %[[[[=]|(?&st'&[=<-]&EQst'&Hincl)]
        %option_included _]%prod_included [Hval _]]%auth_both_valid_discrete.
      simpl in EQst'. subst st. destruct Hincl as [Hincl|Hincl].
      + destruct st' as [[]| |]; try by inversion Hincl. apply (inj Cinl) in Hincl.
        apply (inj2 pair) in Hincl. destruct Hincl as [<-%leibniz_equiv <-%leibniz_equiv].
        iDestruct "Hproto" as (q') "(Hl1 & Hl2 & Hl† & >Hqq' & Hν & Hν†)".
        iDestruct "Hqq'" as %Hqq'. iPoseProof "Hincl" as "(>Hincls & _ & Hinclo & _)".
        iDestruct "Hincls" as %Hincls.
        wp_read. iApply "HΦ". iFrame "Hl1". iLeft. iSplit; first done. iSplit.
        * iExists _. iFrame "Hl2". destruct weak.
          -- iLeft. iSplit; first done. rewrite Hincls. iFrame "Hl†".
             iMod (own_update_2 with "Hst Htok") as "Hst".
             { apply auth_update_dealloc. rewrite -{1}(right_id (None, 0%nat) _ (_, _)).
               apply cancel_local_update_unit, _. }
             rewrite -[in (1).[ν]%I]Hqq' -[(|={↑lft_userN,⊤}=>_)%I]fupd_trans.
             iApply step_fupd_mask_mono;
               last iMod ("Hνend" with "[$Hν $Hν1]") as "H†"; try done.
             iModIntro. iNext. iMod "H†".
             iMod fupd_intro_mask' as "Hclose2"; last iMod ("Hν†" with "H†") as "Hty".
             { set_solver-. }
             iMod "Hclose2" as "_". iModIntro.
             iMod ("Hclose" with "[Hst $Hna]") as "$"; first by iExists _; iFrame.
             iModIntro. iNext. iDestruct "Hty" as (vl) "[??]". iExists _. iFrame.
             by iApply "Hinclo".
          -- iRight. iSplit; first by auto with lia. iSplit.
             ++ iIntros "Hl1 Hl2".
                iMod ("Hclose" with "[-Htok Hν1]") as "$"; last by auto 10 with iFrame.
                iFrame. iExists _. auto with iFrame.
             ++ iIntros "Hl1 Hl2".
                rewrite -[in (1).[ν]%I]Hqq' -[(|={↑lft_userN,⊤}=>_)%I]fupd_trans.
                iApply step_fupd_mask_mono;
                  last iMod ("Hνend" with "[$Hν $Hν1]") as "H†"; try done.
                iModIntro. iNext. iMod "H†".
                iMod fupd_intro_mask' as "Hclose2"; last iMod ("Hν†" with "H†") as "Hty".
                { set_solver-. }
                iMod "Hclose2" as "_". iModIntro.
                iMod (own_update_2 with "Hst Htok") as "Hst".
                { apply auth_update_dealloc, prod_local_update_1,
                        (cancel_local_update_unit (Some _) None). }
                iSplitL "Hty".
                { iDestruct "Hty" as (vy) "[H Hty]". iExists vy. iFrame.
                  by iApply "Hinclo". }
                iIntros "!> H". iApply ("Hclose" with "[>-]"). iFrame. iExists _.
                iFrame. rewrite Hincls /= !Nat2Z.inj_succ -!Z.add_1_l Z.add_simpl_l.
                by iFrame.
        * iIntros "Hl1".
          iMod (own_update_2 with "Hst Htok") as "[Hst Htok]".
          { apply auth_update. etrans.
            - rewrite [(Some _, weak)]pair_split. apply cancel_local_update_unit, _.
            - apply (op_local_update _ _ (Some (Cinr (Excl tt)), 0%nat)). auto. }
          rewrite -[(|={↑lft_userN,⊤}=>_)%I]fupd_trans -[in (1).[ν]%I]Hqq'.
          iApply step_fupd_mask_mono;
            last iMod ("Hνend" with "[$Hν $Hν1]") as "H†"; try done.
          iModIntro. iNext. iMod "H†".
          iMod fupd_intro_mask' as "Hclose2"; last iMod ("Hν†" with "H†") as "Hty".
          { set_solver-. }
          iMod "Hclose2" as "_". iModIntro.
          iMod ("Hclose" with "[Hst $Hna Hl1 Hl2]") as "$";
            first by iExists _; iFrame; iFrame.
          rewrite Hincls. iFrame. iSplitL "Hty".
          { iDestruct "Hty" as (vl) "[??]". iExists _. iFrame. by iApply "Hinclo". }
          iIntros "!> Hna". iClear "Hνend". clear q' Hqq' weak Hval.
          iMod (na_inv_acc with "Hinv Hna") as "(Hproto & Hna & Hclose)"; [solve_ndisj..|].
          iDestruct "Hproto" as ([st weak]) "[>Hst Hproto]".
          iDestruct (own_valid_2 with "Hst Htok") as %[[[[=]|(?&st'&[=<-]&EQst'&Hincl)]
            %option_included _]%prod_included [Hval _]]%auth_both_valid_discrete.
          simpl in EQst'. subst st. destruct Hincl as [Hincl|Hincl]; first last.
          { apply csum_included in Hincl. destruct Hincl as
             [->|[(?&?&[=]&?)|(?&?&[=<-]&->&?%exclusive_included)]]; try done. apply _. }
          setoid_subst. iDestruct "Hproto" as ">(Hl1 & Hl2)". iExists _. iFrame.
          rewrite right_id. destruct weak as [|weak].
          -- iLeft. iFrame. iSplitR; first done.
             iApply ("Hclose" with "[>- $Hna]"). iExists (None, 0%nat).
             iMod (own_update_2 with "Hst Htok") as "$"; last done.
             apply auth_update_dealloc. rewrite -{1}(right_id (None, 0%nat) _ (_, _)).
             apply cancel_local_update_unit, _.
          -- iRight. iSplitR; first by auto with lia. iIntros "!> Hl† Hl2 Hvl".
             iApply ("Hclose" with "[>- $Hna]"). iExists (None, S weak).
             rewrite Hincls. iFrame. iSplitR "Hl2"; last first.
             { by rewrite !Nat2Z.inj_succ -!Z.add_1_l Z.add_simpl_l. }
             iMod (own_update_2 with "Hst Htok") as "$"; last done.
             apply auth_update_dealloc, prod_local_update', reflexivity.
             rewrite -{1}(right_id None _ (Some _)). apply: cancel_local_update_unit.
      + apply csum_included in Hincl.
        destruct Hincl as [->|[(?&(?,?)&[=<-]&->&(q',strong)&[]%(inj2 pair))|
                               (?&?&[=]&?)]]; first done. setoid_subst.
        iDestruct "Hproto" as (q'') "(Hl1 & Hl2 & Hl† & >Hqq' & Hν & Hν†)".
        iDestruct "Hqq'" as %Hqq'. wp_read. iApply "HΦ". iFrame "Hl1". iRight.
        iSplit; first by rewrite !pos_op_plus; auto with lia. iSplit; iIntros "H↦".
        * iMod ("Hclose" with "[- Htok Hν1]") as "$"; last by auto 10 with iFrame.
          iFrame. iExists _. iFrame. auto with iFrame.
        * iMod (own_update_2 with "Hst Htok") as "Hst".
          { apply auth_update_dealloc.
            rewrite pair_op Cinl_op Some_op -{1}(left_id 0%nat _ weak) pair_op.
            apply (cancel_local_update_unit _ (_, _)). }
          iApply "Hclose". iFrame. iExists _. iFrame. iExists (q+q'')%Qp. iFrame.
          iSplitL; first last.
          { rewrite [(_+_)%Qp]assoc [(q'+_)%Qp]comm. auto. }
          rewrite pos_op_plus Z.sub_1_r -Pos2Z.inj_pred; last lia.
          by rewrite Pos.add_1_l Pos.pred_succ.
  Qed.

  Definition rc_strong_count : val :=
    fn: ["rc"] :=
      let: "r" := new [ #1 ] in
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "strong" := !("rc''" +ₗ #0) in
      "r" <- "strong";;
      delete [ #1; "rc" ];; return: ["r"].

  Lemma rc_strong_count_type ty :
    typed_val rc_strong_count (fn(∀ α, ∅; &shr{α}(rc ty)) → int).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q'') "#(Hαν & Hpersist & Hrctokb)".
    iModIntro. wp_let. wp_op. rewrite shift_loc_0.
    (* Finally, finally... opening the thread-local Rc protocol. *)
    iPoseProof "Hpersist" as (ty') "(_ & Hinv & _ & _)".
    iMod (na_inv_acc with "Hinv Hna") as "(Hrcproto & Hna & Hclose2)"; [solve_ndisj..|].
    iMod (na_bor_acc with "LFT Hrctokb Hα1 Hna") as "(>Hrctok & Hna & Hclose3)"; [solve_ndisj..|].
    iDestruct "Hrcproto" as ([st weak]) "[>Hrc● Hrcst]".
    iDestruct (own_valid_2 with "Hrc● Hrctok") as %[[[[=]|(?&[[q0 s0]| |]&[=<-]&?&Hincl)]
               %option_included _]%prod_included [Hval _]]%auth_both_valid_discrete;
    setoid_subst; try done; last first.
    { exfalso. destruct Hincl as [Hincl|Hincl]. by inversion Hincl.
      apply csum_included in Hincl. naive_solver. }
    iDestruct "Hrcst" as (qb) "(Hl'1 & Hl'2 & Hl'† & >% & Hνtok & Hν†)".
    wp_read. wp_let.
    (* And closing it again. *)
    iMod ("Hclose3" with "[$Hrctok] Hna") as "[Hα1 Hna]".
    iMod ("Hclose2" with "[Hrc● Hl'1 Hl'2 Hl'† Hνtok Hν† $Hna]") as "Hna".
    { iExists _. iFrame "Hrc●". iExists _. auto with iFrame. }
    iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(rc ty)); r ◁ box (uninit 1);
                              #(Z.pos s0) ◁ int ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { unlock.
      rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_weak_count : val :=
    fn: ["rc"] :=
      let: "r" := new [ #1 ] in
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "weak" := !("rc''" +ₗ #1) in
      let: "one" := #1 in
      let: "weak" := "weak" - "one" in
      "r" <- "weak";;
      delete [ #1; "rc" ];; return: ["r"].

  Lemma rc_weak_count_type ty :
    typed_val rc_weak_count (fn(∀ α, ∅; &shr{α}(rc ty)) → int).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock [[r]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q'') "#(Hαν & Hpersist & Hrctokb)".
    iModIntro. wp_let. wp_op.
    (* Finally, finally... opening the thread-local Rc protocol. *)
    iPoseProof "Hpersist" as (ty') "(_ & Hinv & _ & _)".
    iMod (na_inv_acc with "Hinv Hna") as "(Hrcproto & Hna & Hclose2)"; [solve_ndisj..|].
    iMod (na_bor_acc with "LFT Hrctokb Hα1 Hna") as "(>Hrctok & Hna & Hclose3)"; [solve_ndisj..|].
    iDestruct "Hrcproto" as ([st weak]) "[>Hrc● Hrcst]".
    iDestruct (own_valid_2 with "Hrc● Hrctok") as %[[[[=]|(?&[[q0 weak0]| |]&[=<-]&?&Hincl)]
               %option_included _]%prod_included [Hval _]]%auth_both_valid_discrete;
    setoid_subst; try done; last first.
    { exfalso. destruct Hincl as [Hincl|Hincl]. by inversion Hincl.
      apply csum_included in Hincl. naive_solver. }
    iDestruct "Hrcst" as (qb) "(Hl'1 & Hl'2 & Hl'† & >% & Hνtok & Hν†)".
    wp_read. wp_let.
    (* And closing it again. *)
    iMod ("Hclose3" with "[$Hrctok] Hna") as "[Hα1 Hna]".
    iMod ("Hclose2" with "[Hrc● Hl'1 Hl'2 Hl'† Hνtok Hν† $Hna]") as "Hna".
    { iExists _. iFrame "Hrc●". iExists _. auto with iFrame. }
    iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(rc ty)); r ◁ box (uninit 1);
                              #(S weak) ◁ int ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { unlock.
      rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      iFrame. }
    iApply type_int. iIntros (?). simpl_subst.
    iApply type_minus; [solve_typing..|]. iIntros (?). simpl_subst.
    iApply type_assign; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_new ty : val :=
    fn: ["x"] :=
      let: "rcbox" := new [ #(2 + ty.(ty_size))%nat ] in
      let: "rc" := new [ #1 ] in
      "rcbox" +ₗ #0 <- #1;;
      "rcbox" +ₗ #1 <- #1;;
      "rcbox" +ₗ #2 <-{ty.(ty_size)} !"x";;
      "rc" <- "rcbox";;
      delete [ #ty.(ty_size); "x"];; return: ["rc"].

  Lemma rc_new_type ty :
    typed_val (rc_new ty) (fn(∅; ty) → rc ty).
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
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (ty_size ty)); #lrc ◁ box (rc ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=. iFrame.
      iSplitL "Hx↦".
      { iExists _. rewrite uninit_own. auto. }
      iNext. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. iLeft.
      rewrite freeable_sz_full_S. iFrame. iExists _. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_clone : val :=
    fn: ["rc"] :=
      let: "r" := new [ #1 ] in
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "strong" := !("rc''" +ₗ #0) in
      "rc''" +ₗ #0 <- "strong" + #1;;
      "r" <- "rc''";;
      delete [ #1; "rc" ];; return: ["r"].

  Lemma rc_clone_type ty :
    typed_val rc_clone (fn(∀ α, ∅; &shr{α}(rc ty)) → rc ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    iDestruct (ownptr_uninit_own with "Hr") as (lr vlr) "(% & Hr & Hr†)".
    subst r. inv_vec vlr=>r. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q'') "#(Hαν & Hpersist & Hrctokb)".
    iModIntro. wp_let. wp_op. rewrite shift_loc_0.
    (* Finally, finally... opening the thread-local Rc protocol. *)
    iPoseProof "Hpersist" as (ty') "(_ & Hinv & _ & _)".
    iMod (na_inv_acc with "Hinv Hna") as "(Hrcproto & Hna & Hclose2)"; [solve_ndisj..|].
    iMod (na_bor_acc with "LFT Hrctokb Hα1 Hna") as "(>Hrctok & Hna & Hclose3)"; [solve_ndisj..|].
    iDestruct "Hrcproto" as ([st weak]) "[>Hrc● Hrcst]".
    iDestruct (own_valid_2 with "Hrc● Hrctok") as %[[[[=]|(?&[[q0 s0]| |]&[=<-]&?&Hincl)]
               %option_included _]%prod_included [Hval _]]%auth_both_valid_discrete;
    setoid_subst; try done; last first.
    { exfalso. destruct Hincl as [Hincl|Hincl]. by inversion Hincl.
      apply csum_included in Hincl. naive_solver. }
    iDestruct "Hrcst" as (qb) "(Hl'1 & Hl'2 & Hl'† & >% & Hνtok & Hν†)".
    wp_read. wp_let. wp_op. rewrite shift_loc_0. wp_op. wp_write. wp_write.
    (* And closing it again. *)
    iMod (own_update with "Hrc●") as "[Hrc● Hrctok2]".
    { apply auth_update_alloc, prod_local_update_1,
      (op_local_update_discrete _ _ (Some (Cinl ((qb/2)%Qp, 1%positive))))=>-[/= Hqa _].
      split; simpl; last done. apply frac_valid'. rewrite /= -H comm_L.
      by apply Qp_add_le_mono_l, Qp_div_le. }
    rewrite right_id -Some_op -Cinl_op -pair_op. iDestruct "Hνtok" as "[Hνtok1 Hνtok2]".
    iMod ("Hclose3" with "[$Hrctok] Hna") as "[Hα1 Hna]".
    iMod ("Hclose2" with "[Hrc● Hl'1 Hl'2 Hl'† Hνtok2 Hν† $Hna]") as "Hna".
    { iExists _. iFrame "Hrc●". iExists _. rewrite Z.add_comm. iFrame.
      rewrite [_ ⋅ _]comm frac_op' -[(_ + _)%Qp]assoc Qp_div_2. auto. }
    iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(rc ty)); #lr ◁ box (rc ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame "Hx". iFrame "Hr†". iExists [# #l'].
      rewrite heap_mapsto_vec_singleton /=. simpl. eauto 10 with iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_deref : val :=
    fn: ["rc"] :=
      let: "x" := new [ #1 ] in
      let: "rc'" := !"rc" in
      "x" <- (!"rc'" +ₗ #2);;
      delete [ #1; "rc" ];; return: ["x"].

  Lemma rc_deref_type ty :
    typed_val rc_deref (fn(∀ α, ∅; &shr{α}(rc ty)) → &shr{α}ty).
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
    iDestruct "Hpersist" as (ty') "(_ & _ & [Hshr|Hν†] & _)"; last first.
    { iMod (lft_incl_dead with "Hαν Hν†") as "Hα†". done.
      iDestruct (lft_tok_dead with "Hα1 Hα†") as "[]". }
    wp_op. wp_write. iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ rcx ◁ box (&shr{α}(rc ty)); #lrc2 ◁ box (&shr{α}ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame "Hrcx". iFrame "Hx†". iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "Hx". iApply (ty_shr_mono with "[] Hshr").
      iApply lft_incl_glb; [done|]. iApply elctx_interp_ty_outlives_E.
      rewrite !elctx_interp_app /=. iDestruct "HE" as "(_ & [[_ $] _] & _)". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rc_try_unwrap ty : val :=
    fn: ["rc"] :=
      let: "r" := new [ #(Σ[ ty; rc ty ]).(ty_size) ] in
    withcont: "k":
      let: "rc'" := !"rc" in
      let: "strong" := !("rc'" +ₗ #0) in
      if: "strong" = #1 then
        (* Decrement strong *)
        "rc'" +ₗ #0 <- #0;;
        Skip;;
        (* Return content *)
        "r" <-{ty.(ty_size),Σ 0} !("rc'" +ₗ #2);;
        (* Decrement weak (removing the one weak ref collectively held by all
           strong refs), and deallocate if weak count reached 0. *)
        let: "weak" := !("rc'" +ₗ #1) in
        if: "weak" = #1 then
          delete [ #(2 + ty.(ty_size)); "rc'" ];;
          "k" []
        else
          "rc'" +ₗ #1 <- "weak" - #1;;
          "k" []
      else
        "r" <-{Σ 1} "rc'";;
        "k" []
    cont: "k" [] :=
      delete [ #1; "rc"];; return: ["r"].

  Lemma rc_try_unwrap_type ty :
    typed_val (rc_try_unwrap ty) (fn(∅; rc ty) → Σ[ ty; rc ty ]).
  Proof.
    (* TODO: There is a *lot* of duplication between this proof and the one for drop. *)
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (_ ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new (Σ[ ty; rc ty ]).(ty_size)); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ _, [rcx ◁ box (uninit 1); r ◁ box (Σ[ ty; rc ty ])])) ;
      [solve_typing..| |]; last first.
    { simpl. iModIntro. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[r]]lock.
    destruct rc' as [[|rc'|]|]; try done.
    rewrite [[ #rc' ]]lock. wp_op. rewrite shift_loc_0 -(lock [ #rc' ]).
    wp_apply (rc_check_unique with "[$Hna $Hrc']"); first solve_ndisj.
    iIntros (strong) "[Hrc Hc]". wp_let.
    iDestruct "Hc" as "[[% [_ Hproto]]|[% [Hproto _]]]".
    - subst strong. wp_op. wp_if. wp_op.
      rewrite shift_loc_0. wp_write. wp_bind (#☠;;#☠)%E.
      iApply (wp_step_fupd with "[Hproto Hrc]");
        [|by iApply ("Hproto" with "Hrc")|];
        [done..|wp_seq; iIntros "(Hty&H†&Hna&Hproto) !>"].
      rewrite <-freeable_sz_full_S, <-(freeable_sz_split _ 2 ty.(ty_size)).
      iDestruct "H†" as "[H†1 H†2]". wp_seq. wp_bind (_<-_;;_)%E.
      iApply (wp_wand with "[Hna HL Hty Hr H†2]").
      { iApply (type_sum_memcpy_instr 0 [_; (rc ty)] with "LFT HE Hna HL"); first done.
        { by eapply (write_own _ (uninit _)). } { apply read_own_move. }
        iSplitL "Hr"; first by unlock; rewrite tctx_hasty_val. iSplitL; last done.
        rewrite tctx_hasty_val'; last done. iFrame. }
      iIntros (?) "(Hna & HL & [Hr [Hrc _]])". wp_seq.
      iMod ("Hproto" with "Hna") as (weak) "[H↦weak Hproto]". wp_op. wp_read. wp_let.
      iDestruct "Hproto" as "[(% & H↦strong & Hna)|[% Hproto]]".
      + subst. wp_op. wp_if.
        iApply (type_type _ _ _
             [ r ◁ own_ptr (ty_size Σ[ ty; rc ty ]) (Σ[ ty; rc ty]);
               rcx ◁ box (uninit 1);
               #rc' +ₗ #2 ◁ own_ptr (2 + ty.(ty_size)) (uninit (ty.(ty_size)));
               #rc' +ₗ #0 ◁ own_ptr (2 + ty.(ty_size)) (uninit 2)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
        { unlock. rewrite 3!tctx_interp_cons tctx_interp_singleton. iFrame "Hr Hrc".
          rewrite 1!tctx_hasty_val tctx_hasty_val' //. iFrame "Hrcx".
          rewrite shift_loc_0 /=. iFrame. iExists [_; _].
          rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
          auto with iFrame. }
        iApply (type_delete (Π[uninit 2;uninit ty.(ty_size)])); [solve_typing..|].
        iApply type_jump; solve_typing.
      + rewrite (tctx_hasty_val' _ (#rc' +ₗ #2)); last done.
        iDestruct "Hrc" as "[Hrc H†2]". wp_op; case_bool_decide; first lia. wp_if. wp_op. wp_op. wp_write.
        iMod ("Hproto" with "[H†1 H†2] H↦weak Hrc") as "Hna".
        { rewrite -freeable_sz_full_S -(freeable_sz_split _ 2 ty.(ty_size)). iFrame. }
        iApply (type_type _ _ _
             [ r ◁ own_ptr (ty_size Σ[ ty; rc ty ]) (Σ[ ty; rc ty]);
               rcx ◁ box (uninit 1) ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
        { unlock. rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
        iApply type_jump; solve_typing.
    - wp_op; case_bool_decide as Hc; first lia. wp_if. iMod ("Hproto" with "Hrc") as "[Hna Hrc]".
      iApply (type_type _ _ _ [ r ◁ own_ptr (ty_size Σ[ ty; rc ty ]) (uninit _);
                                rcx ◁ box (uninit 1); #rc' ◁ rc ty ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton.
        rewrite !tctx_hasty_val tctx_hasty_val' //. unlock. iFrame. }
      iApply (type_sum_assign Σ[ ty; rc ty ]); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition rc_drop ty : val :=
    fn: ["rc"] :=
      let: "r" := new [ #(option ty).(ty_size) ] in
    withcont: "k":
      let: "rc'" := !"rc" in
      let: "strong" := !("rc'" +ₗ #0) in
      "rc'" +ₗ #0 <- "strong" - #1;;
      if: "strong" = #1 then
        (* Return content. *)
        "r" <-{ty.(ty_size),Σ some} !("rc'" +ₗ #2);;
        (* Decrement weak (removing the one weak ref collectively held by all
           strong refs), and deallocate if weak count reached 0. *)
        let: "weak" := !("rc'" +ₗ #1) in
        if: "weak" = #1 then
          delete [ #(2 + ty.(ty_size)); "rc'" ];;
          "k" []
        else
          "rc'" +ₗ #1 <- "weak" - #1;;
          "k" []
      else
        "r" <-{Σ none} ();;
        "k" []
    cont: "k" [] :=
      delete [ #1; "rc"];; return: ["r"].

  Lemma rc_drop_type ty :
    typed_val (rc_drop ty) (fn(∅; rc ty) → option ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (_ ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new (option ty).(ty_size)); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ _, [rcx ◁ box (uninit 1); r ◁ box (option ty)]));
      [solve_typing..| |]; last first.
    { simpl. iModIntro. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[r]]lock.
    destruct rc' as [[|rc'|]|]; try done. rewrite [[ #rc' ]]lock.
    wp_op. rewrite shift_loc_0. rewrite -(lock [ #rc' ]).
    wp_apply (rc_check_unique with "[$Hna $Hrc']"); first solve_ndisj.
    iIntros (strong) "[Hrc Hc]". wp_let. wp_op. rewrite shift_loc_0.
    rewrite {3}[Z.pos strong]lock. wp_op. unlock. wp_write.
    iDestruct "Hc" as "[[% [_ Hproto]]|[% [_ Hproto]]]".
    - subst strong. wp_bind (#1 = #1)%E.
      iApply (wp_step_fupd with "[Hproto Hrc]");
        [|by iApply ("Hproto" with "Hrc")|];
        [done..|wp_op; iIntros "(Hty&H†&Hna&Hproto) !>"; wp_if].
      rewrite <-freeable_sz_full_S, <-(freeable_sz_split _ 2 ty.(ty_size)).
      iDestruct "H†" as "[H†1 H†2]". wp_bind (_<-_;;_)%E.
      iApply (wp_wand with "[Hna HL Hty Hr H†2]").
      { iApply (type_sum_memcpy_instr 1 [unit; _] with "LFT HE Hna HL"); first done.
        { by eapply (write_own _ (uninit _)). } { apply read_own_move. }
        iSplitL "Hr"; first by unlock; rewrite tctx_hasty_val. iSplitL; last done.
        rewrite tctx_hasty_val'; last done. iFrame. }
      iIntros (?) "(Hna & HL & [Hr [Hrc _]])". wp_seq.
      iMod ("Hproto" with "Hna") as (weak) "[H↦weak Hproto]". wp_op. wp_read. wp_let.
      iDestruct "Hproto" as "[(% & H↦strong & Hna)|[% Hproto]]".
      + subst. wp_op. wp_if.
        iApply (type_type _ _ _
             [ r ◁ own_ptr (ty_size (option ty)) (option ty);
               rcx ◁ box (uninit 1);
               #rc' +ₗ #2 ◁ own_ptr (2 + ty.(ty_size)) (uninit (ty.(ty_size)));
               #rc' +ₗ #0 ◁ own_ptr (2 + ty.(ty_size)) (uninit 2)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
        { unlock. rewrite 3!tctx_interp_cons tctx_interp_singleton. iFrame "Hr Hrc".
          rewrite 1!tctx_hasty_val tctx_hasty_val' //. iFrame "Hrcx".
          rewrite shift_loc_0 /=. iFrame. iExists [_; _].
          rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
          auto with iFrame. }
        iApply (type_delete (Π[uninit 2;uninit ty.(ty_size)])); [solve_typing..|].
        iApply type_jump; solve_typing.
      + rewrite (tctx_hasty_val' _ (#rc' +ₗ #2)); last done.
        iDestruct "Hrc" as "[Hrc H†2]". wp_op. case_bool_decide; first lia. wp_if. wp_op. wp_op. wp_write.
        iMod ("Hproto" with "[H†1 H†2] H↦weak Hrc") as "Hna".
        { rewrite -freeable_sz_full_S -(freeable_sz_split _ 2 ty.(ty_size)). iFrame. }
        iApply (type_type _ _ _
             [ r ◁ own_ptr (ty_size (option ty)) (option ty); rcx ◁ box (uninit 1) ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
        { unlock. rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
        iApply type_jump; solve_typing.
    - wp_op; case_bool_decide as Hc; first lia. wp_if. iMod ("Hproto" with "Hrc") as "Hna".
      iApply (type_type _ _ _ [ r ◁ own_ptr (ty_size (option ty)) (uninit _);
                                rcx ◁ box (uninit 1) ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton.
        rewrite !tctx_hasty_val. iFrame. }
      iApply (type_sum_unit (option ty)); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition rc_get_mut : val :=
    fn: ["rc"] :=
      let: "r" := new [ #2 ] in
    withcont: "k":
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "strong" := !("rc''" +ₗ #0) in
      if: "strong" = #1 then
        let: "weak" := !("rc''" +ₗ #1) in
        if: "weak" = #1 then
          "r" <-{Σ some} ("rc''" +ₗ #2);;
          "k" []
        else
          "r" <-{Σ none} ();;
          "k" []
      else
        "r" <-{Σ none} ();;
        "k" []
    cont: "k" [] :=
      delete [ #1; "rc"];; return: ["r"].

  Lemma rc_get_mut_type ty :
    typed_val rc_get_mut (fn(∀ α, ∅; &uniq{α}(rc ty)) → option (&uniq{α}ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new 2); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ _, [rcx ◁ box (uninit 1); r ◁ box (option $ &uniq{α}ty)]));
      [solve_typing..| |]; last first.
    { simpl. iModIntro. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val  [[rcx]]lock [[r]]lock.
    iDestruct "Hrc'" as "[#? Hrc']". destruct rc' as [[|rc'|]|]; try done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & HL & Hclose1)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hrc' Hα") as "[Hrc' Hclose2]"; first solve_ndisj.
    iDestruct (heap_mapsto_ty_own with "Hrc'") as (vl) "[>Hrc' Hrcown]".
    inv_vec vl=>l. rewrite heap_mapsto_vec_singleton.
    wp_read. destruct l as [[|l|]|]; try done.
    wp_let. wp_op. rewrite shift_loc_0.
    wp_apply (rc_check_unique with "[$Hna Hrcown]"); first done.
    { (* Boy this is silly... *) iDestruct "Hrcown" as "[(?&?&?&?)|?]"; last by iRight.
      iLeft. by iFrame. }
    iIntros (c) "(Hl1 & Hc)". wp_let. wp_op; case_bool_decide as Hc.
    - wp_if. iDestruct "Hc" as "[[% [Hc _]]|[% _]]"; last lia. subst.
      iDestruct "Hc" as (weak) "[Hl2 Hweak]". wp_op. wp_read. wp_let.
      iDestruct "Hweak" as "[[% Hrc]|[% [Hrc _]]]".
      + subst. wp_bind (#1 = #1)%E. iApply (wp_step_fupd with "Hrc"); [done..|].
        wp_op. iIntros "(Hl† & Hty & Hna)!>". wp_if.
        iMod ("Hclose2" with "[Hrc' Hl1 Hl2 Hl†] [Hty]") as "[Hty Hα]"; [|iNext; iExact "Hty"|].
        { iIntros "!> Hty". iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "Hrc'".
          iLeft. by iFrame. }
        iMod ("Hclose1" with "Hα HL") as "HL".
        iApply (type_type _ _ _ [ r ◁ box (uninit 2); #l +ₗ #2 ◁ &uniq{α}ty;
                                  rcx ◁ box (uninit 1)]
                with "[] LFT HE Hna HL Hk [-]"); last first.
        { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
          unlock. iFrame "∗#". }
        iApply (type_sum_assign (option (&uniq{_}_))); [solve_typing..|].
        iApply type_jump; solve_typing.
      + wp_op; case_bool_decide; first lia. wp_if. iMod ("Hrc" with "Hl1 Hl2") as "[Hna Hrc]".
        iMod ("Hclose2" with "[] [Hrc' Hrc]") as "[Hrc' Hα]".
        { iIntros "!> HX". iModIntro. iExact "HX". }
        { iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. auto. }
        iMod ("Hclose1" with "Hα HL") as "HL".
        iApply (type_type _ _ _ [ r ◁ box (uninit 2); rcx ◁ box (uninit 1)]
                with "[] LFT HE Hna HL Hk [-]"); last first.
        { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
          unlock. iFrame. }
        iApply (type_sum_unit (option (&uniq{_}_))); [solve_typing..|].
        iApply type_jump; solve_typing.
    - wp_if. iDestruct "Hc" as "[[% _]|[% [Hproto _]]]"; first lia.
      iMod ("Hproto" with "Hl1") as "[Hna Hrc]".
      iMod ("Hclose2" with "[] [Hrc' Hrc]") as "[Hrc' Hα]".
      { iIntros "!> HX". iModIntro. iExact "HX". }
      { iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. auto. }
      iMod ("Hclose1" with "Hα HL") as "HL".
      iApply (type_type _ _ _ [ r ◁ box (uninit 2); rcx ◁ box (uninit 1)]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
        unlock. iFrame. }
      iApply (type_sum_unit (option (&uniq{_}_))); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  (* TODO : it is not nice that we have to inline the definition of
     rc_new and of rc_deref. *)
  Definition rc_make_mut (ty : type) (clone : val) : val :=
    fn: ["rc"] :=
      let: "r" := new [ #1 ] in
    withcont: "k":
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "strong" := !("rc''" +ₗ #0) in
      if: "strong" = #1 then
        let: "weak" := !("rc''" +ₗ #1) in
        if: "weak" = #1 then
          (* This is the last strong ref, and there is no weak ref.
             We just return a deep ptr into the Rc. *)
          "r" <- "rc''" +ₗ #2;;
          "k" []
        else
          (* This is the last strong ref, but there are weak refs.
             We make ourselves a new Rc, move the content, and mark the old one killed
             (strong count becomes 0, strong idx removed from weak cnt).
             We store the new Rc in our argument (which is a &uniq rc),
             and return a deep ptr into it. *)
          "rc''" +ₗ #0 <- #0;;
          "rc''" +ₗ #1 <- "weak" - #1;;
          (* Inlined rc_new("rc''" +ₗ #2) begins. *)
          let: "rcbox" := new [ #(2 + ty.(ty_size))%nat ] in
          "rcbox" +ₗ #0 <- #1;;
          "rcbox" +ₗ #1 <- #1;;
          "rcbox" +ₗ #2 <-{ty.(ty_size)} !"rc''" +ₗ #2;;
          "rc'" <- "rcbox";;
          (* Inlined rc_new ends. *)
          "r" <- "rcbox" +ₗ #2;;
          "k" []
      else
        (* There are other strong refs, we have to make a copy and clone the content. *)
        let: "x" := new [ #1 ] in
        "x" <- "rc''" +ₗ #2;;
        let: "clone" := clone in
        letcall: "c" := "clone" ["x"]%E in (* FIXME : why do I need %E here ? *)
        (* Inlined rc_new("c") begins. *)
        let: "rcbox" := new [ #(2 + ty.(ty_size))%nat ] in
        "rcbox" +ₗ #0 <- #1;;
        "rcbox" +ₗ #1 <- #1;;
        "rcbox" +ₗ #2 <-{ty.(ty_size)} !"c";;
        delete [ #ty.(ty_size); "c"];;
        "rc'" <- "rcbox";;
        (* Inlined rc_new ends. *)
        letalloc: "rcold" <- "rc''" in
        (* FIXME : here, we are dropping the old rc pointer. In the
           case another strong reference has been dropped while
           cloning, it is possible that we are actually dropping the
           last reference here. This means that we may have to drop an
           instance of [ty] here. Instead, we simply forget it. *)
        let: "drop" := rc_drop ty in
        letcall: "content" := "drop" ["rcold"]%E in
        delete [ #(option ty).(ty_size); "content"];;
        "r" <- "rcbox" +ₗ #2;;
        "k" []
    cont: "k" [] :=
      delete [ #1; "rc"];; return: ["r"].

  Lemma rc_make_mut_type ty clone :
    (* ty : Clone, as witnessed by the impl clone *)
    typed_val clone (fn(∀ α, ∅; &shr{α}ty) → ty) →
    typed_val (rc_make_mut ty clone) (fn(∀ α, ∅; &uniq{α}(rc ty)) → &uniq{α}ty).
  Proof.
    intros Hclone E L. iApply type_fn; [solve_typing..|].
    rewrite [(2 + ty_size ty)%nat]lock.
    iIntros "/= !>".  iIntros (α ϝ ret arg). inv_vec arg=>rcx. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ _, [rcx ◁ box (uninit 1); r ◁ box (&uniq{α}ty)]));
      [solve_typing..| |]; last first.
    { simpl. iModIntro. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hrcx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[rcx]]lock [[r]]lock.
    iDestruct "Hrc'" as "[#? Hrc']". destruct rc' as [[|rc'|]|]; try done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)";
      [solve_typing..|].
    iMod (bor_acc_cons with "LFT Hrc' Hα1") as "[Hrc' Hclose2]"; first solve_ndisj.
    iDestruct (heap_mapsto_ty_own with "Hrc'") as (vl) "[>Hrc' Hrcown]".
    inv_vec vl=>l. rewrite heap_mapsto_vec_singleton.
    wp_read. destruct l as [[|l|]|]; try done. wp_let. wp_op. rewrite shift_loc_0.
    wp_apply (rc_check_unique with "[$Hna Hrcown]"); first done.
    { (* Boy this is silly... *) iDestruct "Hrcown" as "[(?&?&?&?)|?]"; last by iRight.
      iLeft. by iFrame. }
    iIntros (c) "(Hl1 & Hc)". wp_let. wp_op; case_bool_decide as Hc; wp_if.
    - iDestruct "Hc" as "[[% [Hc _]]|[% _]]"; last lia. subst.
      iDestruct "Hc" as (weak) "[Hl2 Hweak]". wp_op. wp_read. wp_let.
      iDestruct "Hweak" as "[[% Hrc]|[% [_ Hrc]]]".
      + subst. wp_bind (#1 = #1)%E. iApply (wp_step_fupd with "Hrc"); [done..|].
        wp_op. iIntros "(Hl† & Hty & Hna)!>". wp_if.
        iMod ("Hclose2" with "[Hrc' Hl1 Hl2 Hl†] [Hty]") as "[Hty Hα1]"; [|iNext; iExact "Hty"|].
        { iIntros "!> Hty". iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "Hrc'".
          iLeft. by iFrame. }
        iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
        iApply (type_type _ _ _ [ r ◁ box (uninit 1); #l +ₗ #2 ◁ &uniq{α}ty;
                                  rcx ◁ box (uninit 1)]
                with "[] LFT HE Hna HL Hk [-]"); last first.
        { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                  tctx_hasty_val' //. unlock. iFrame "∗#". }
        iApply type_assign; [solve_typing..|].
        iApply type_jump; solve_typing.
      + wp_op; case_bool_decide; first lia. wp_if. wp_op. rewrite shift_loc_0. wp_write. wp_op.
        wp_op. wp_write. wp_bind (new _). iSpecialize ("Hrc" with "Hl1 Hl2").
        iApply (wp_step_fupd with "Hrc"); [done..|]. iApply wp_new; first lia. done.
        rewrite -!lock Nat2Z.id.
        iNext. iIntros (lr) "/= ([H†|%] & H↦lr) [Hty Hproto] !>"; last lia.
        rewrite 2!heap_mapsto_vec_cons. iDestruct "H↦lr" as "(Hlr1 & Hlr2 & Hlr3)".
        wp_let. wp_op. rewrite shift_loc_0. wp_write. wp_op. wp_write. wp_op. wp_op.
        iDestruct "Hty" as (vlr) "[H↦vlr Hty]". rewrite shift_loc_assoc.
        iDestruct (ty_size_eq with "Hty") as %Hsz.
        wp_apply (wp_memcpy with "[$Hlr3 $H↦vlr]").
        { by rewrite repeat_length. } { by rewrite Hsz. }
        iIntros "[Hlr3 Hvlr]". wp_seq. wp_write. wp_op.
        iMod ("Hproto" with "[Hvlr]") as "Hna"; first by eauto.
        iMod ("Hclose2" $! ((lr +ₗ 2) ↦∗: ty_own ty tid)%I
              with "[Hrc' Hlr1 Hlr2 H†] [Hlr3 Hty]") as "[Hb Hα1]".
        { iIntros "!> H !>". iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
          iLeft. iFrame. }
        { iExists _. iFrame. }
        iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
        iApply (type_type _ _ _ [ r ◁ box (uninit 1); #(lr +ₗ 2) ◁ &uniq{α}ty;
                                  rcx ◁ box (uninit 1)]
                with "[] LFT HE Hna HL Hk [-]"); last first.
        { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                  tctx_hasty_val' //. unlock. iFrame "∗#". }
        iApply type_assign; [solve_typing..|].
        iApply type_jump; solve_typing.
    - wp_apply wp_new; [lia|done|].
      iIntros (lr) "/= ([H†|%] & H↦lr)"; last lia.
      iDestruct "Hc" as "[[% ?]|[% [Hproto _]]]"; first lia.
      iMod ("Hproto" with "Hl1") as "[Hna Hty]". wp_let. wp_op.
      rewrite heap_mapsto_vec_singleton. wp_write.
      iAssert (∃ γ ν q', rc_persist tid ν γ l ty ∗ own γ (rc_tok q') ∗ q'.[ν] ∗
                         (q / 2).[α])%I
        with "[>Hty Hα2]" as (γ ν q') "(Hty & Htok & Hν & Hα2)".
      { iDestruct "Hty" as "[(Hl1 & Hl2 & Hl† & Hl3)|Hty]"; last by iFrame.
        iMod (own_alloc (● (Some $ Cinl ((1/2)%Qp, 1%positive), 0%nat) ⋅
                         rc_tok (1/2)%Qp)) as (γ) "[Ha Hf]";
          first by apply auth_both_valid_discrete.
        iMod (lft_create with "LFT") as (ν) "[[Hν1 Hν2] #Hν†]"=>//.
        iApply (fupd_mask_mono (↑lftN))=>//. iExists γ, ν, (1/2)%Qp. iFrame "Hν2 Hf".
        iMod (bor_create _ ν with "LFT Hl3") as "[Hb Hh]"=>//.
        iMod (lft_incl_acc with "[//] Hα2") as (q') "[Htok Hclose]"; [done|].
        iDestruct (lft_intersect_acc with "Hν1 Htok") as (q'') "[Htok Hclose']".
        iMod (ty_share with "LFT [] [Hb] Htok") as "[Hty Htok]"=>//.
        { iApply lft_intersect_incl_r. }
        { iApply (bor_shorten with "[] Hb"). iApply lft_intersect_incl_l. }
        iDestruct ("Hclose'" with "Htok") as "[? Htok]".
        iMod ("Hclose" with "Htok") as "$".
        iExists ty. iSplitR; [iApply type_incl_refl|].
        iSplitR "Hty"; last by auto. iApply na_inv_alloc. iExists _. do 2 iFrame.
        iExists _. iFrame. by rewrite Qp_div_2. }
      iDestruct "Hty" as (ty') "#(Hty'ty & Hinv & Hs & Hν†)".
      iDestruct "Hs" as "[Hs|Hν']"; last by iDestruct (lft_tok_dead with "Hν Hν'") as "[]".
      wp_bind (of_val clone). iApply (wp_wand with "[Hna]").
      { iApply (Hclone _ [] with "LFT HE Hna").
          by rewrite /llctx_interp. by rewrite /tctx_interp. }
      clear clone Hclone. iIntros (clone) "(Hna & _ & Hclone)".
      wp_let. wp_let. rewrite tctx_interp_singleton tctx_hasty_val.
      iDestruct (lft_intersect_acc with "Hν Hα2") as (q'') "[Hαν Hclose3]".
      rewrite -[ν ⊓ α](right_id_L).
      iApply (type_call_iris _ [ν ⊓ α] (ν ⊓ α) [_]
              with "LFT HE Hna Hαν Hclone [H† H↦lr]"); [solve_typing| |].
      { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full_S.
        iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
        iApply ty_shr_mono; [|done]. iApply lft_intersect_mono; [|done].
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
          "[Hrc' Hl' Hl'1  Hl'†] [Hl'2 Hown]") as "[Hl' Hα1]".
      { iIntros "!> H". iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
        iLeft. iFrame. iDestruct "Hl'†" as "[?|%]"=>//. }
      { iExists _.  iFrame. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      iApply (type_type _ _ _ [ #l ◁ rc ty; #l' +ₗ #2 ◁ &uniq{α}ty;
                                r ◁ box (uninit 1); rcx ◁ box (uninit 1) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 3!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                !tctx_hasty_val' //. unlock. iFrame "∗#". iRight. iExists γ, ν, _.
        unfold rc_persist, tc_opaque. iFrame "∗#". eauto. }
      iApply type_letalloc_1; [solve_typing..|]. iIntros (rcold). simpl_subst.
      iApply type_let. apply rc_drop_type. solve_typing. iIntros (drop). simpl_subst.
      iApply (type_letcall ()); [solve_typing..|]. iIntros (content). simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_assign; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.
End code.
