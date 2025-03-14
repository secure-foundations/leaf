From lrust.typing Require Export uniq_bor shr_bor own uniq_util.
From lrust.typing Require Import lft_contexts type_context programs.
Set Default Proof Using "Type".

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{!typeG Σ}.

  Lemma tctx_borrow {𝔄} E L p n (ty: type 𝔄) κ:
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_incl E L +[p ◁ own_ptr n ty] +[p ◁ &uniq{κ} ty; p ◁{κ} own_ptr n ty]
      (λ post '-[a], ∀a': 𝔄, post -[(a, a'); a']).
  Proof.
    intros Out. split; [intros ??? [?[]]; by apply forall_proper|].
    iIntros (??[vπ[]]?) "#LFT #PROPH #UNIQ #E L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iDestruct "p" as ([[]|][|]?) "[#⧖ own]"=>//.
    iDestruct "own" as "[(%& >↦ & ty) †]". iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#?".
    iMod (uniq_intro vπ with "PROPH UNIQ") as (ξi) "[Vo Pc]"; [done|].
    set ξ := PrVar _ ξi.
    iMod (bor_create ⊤ κ (∃vπ' d, ⧖(S d) ∗ .PC[ξ] vπ' d ∗
      _ ↦∗: ty.(ty_own) vπ' d _)%I with "LFT [↦ ty Pc]") as "[Bor Toty]"; [done| |].
    { iExists _, _. iFrame "Pc ⧖". iExists _. iFrame. }
    iExists -[pair ∘ vπ ⊛ (.$ ξ); (.$ ξ)]. rewrite/= right_id. iFrame "L". iModIntro.
    iSplitR "Obs"; [|by iApply proph_obs_impl; [|done]=>/=]. iSplitL "Vo Bor".
    - iExists _, _. do 2 (iSplit; [done|]). iFrame "#". iExists _, _. by iFrame.
    - iExists _. iSplit; [done|]. iIntros "†κ".
      iMod ("Toty" with "†κ") as (??) "(>⧖' & Pc & ↦ty)". iExists _, _.
      iFrame "⧖' ↦ty †". iIntros "!>!>".
      iDestruct (proph_ctrl_eqz with "PROPH Pc") as "$".
  Qed.

  Lemma tctx_extract_hasty_borrow {𝔄 𝔅 ℭl} E L p n
      (ty : type 𝔄) (ty' : type 𝔅) κ (T : tctx ℭl) f:
    subtype E L ty' ty f →
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_extract_elt E L (p ◁ &uniq{κ}ty) (p ◁ own_ptr n ty' +:: T)
      (p ◁{κ} own_ptr n ty +:: T)
      (λ post '(b -:: bs), ∀b': 𝔄, post ((f b, b') -:: b' -:: bs)).
  Proof.
    intros. eapply tctx_incl_impl.
    - eapply tctx_incl_trans; [by eapply subtype_tctx_incl, own_subtype|].
      eapply (tctx_incl_frame_r +[_] +[_; _]). by eapply tctx_borrow.
    - done.
    - intros ??? [??]. by apply forall_proper.
  Qed.

  Lemma type_share_instr {𝔄} p κ (ty : type 𝔄) E L :
    lctx_lft_alive E L κ →
    typed_instr E L +[p ◁ &uniq{κ}ty] Share (const +[p ◁ &shr{κ} ty])
      (λ post '-[(a, a')], a' = a -> post -[a]).
  Proof.
    iIntros (Hκ ?? [vπ []]) "#LFT #TIME #PROPH #UNIQ #HE $ HL [Huniq _] Hproph".
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; [done..|].
    iDestruct "Huniq" as ([[]|] [|d]) "(% & _ & [#? H]) /="; try done;
      iDestruct "H" as (? ?) "([% %Eq] & Hvo & Huniq)"; try lia.
    iMod (bor_exists_tok with "LFT Huniq Htok1") as (vπ') "[Huniq Htok1]"; [done|].
    iMod (bor_exists_tok with "LFT Huniq Htok1") as (d'') "[Huniq Htok1]"; [done|].
    iMod (bor_acc with "LFT Huniq Htok1") as "[(>#Hd'' & Hpc & Hown) Hclose']"; [done|].
    iDestruct "Hown" as (?) "[H↦ Hown]".
    iDestruct (ty.(ty_own_proph) with "LFT [$] Hown [$Htok2]") as "H"; [solve_ndisj|].
    wp_bind Skip.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME Hd'' [H]"); [done..| |].
    { iApply step_fupdN_with_emp.
      by iApply (fupd_step_fupdN_fupd_mask_mono with "H"). }
    wp_seq. iDestruct 1 as (ξl q') "/= (%Hdep & Hdt & Hclose'')".
    iDestruct (uniq_agree with "Hvo Hpc") as "%Hag"; inversion Hag; subst; clear Hag.
    iMod (uniq_resolve with "PROPH Hvo Hpc Hdt") as "(Hobs & Hpc & Hdt)"; [done|done| ].
    iMod ("Hclose''" with "Hdt") as "[Hown Htok]".
    iMod ("Hclose'" with "[H↦ Hown Hpc]") as "[Huniq Htok2]".
    { iFrame "#∗". iExists _. iFrame. }
    do 2 (iMod (bor_sep with "LFT Huniq") as "[_ Huniq]"; [done|]).
    iDestruct (ty.(ty_share) with "LFT [$] Huniq Htok") as "Hshr"; [done|].
    iModIntro. wp_seq.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME Hd'' [Hshr]");
      [done..| |].
    { iApply step_fupdN_with_emp.
      iApply (fupd_step_fupdN_fupd_mask_mono with "Hshr"); done. }
    wp_seq. iIntros "[Hshr Htok1]". iMod ("Hclose" with "[$Htok1 $Htok2]") as "$".
    iExists -[_]. rewrite /= right_id. iSplitR "Hproph Hobs".
    - iExists _, _. by iFrame "# % Hshr".
    - iCombine "Hobs Hproph" as "Hobs". iApply proph_obs_impl; [|done]=>/= π.
      move: (equal_f Eq π)=>/=. case (vπ π)=>/= ??<-[<-Imp]. by apply Imp.
  Qed.

  Lemma type_share {𝔄 𝔅l ℭl 𝔇} p κ (ty: type 𝔄) (T: tctx 𝔅l) (T' : tctx ℭl)
    trx tr e E L (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ &uniq{κ} ty] T T' trx →
    lctx_lft_alive E L κ →
    typed_body E L C (p ◁ &shr{κ} ty +:: T') e tr -∗
    typed_body E L C T (Share;; e) (trx ∘
      (λ post '((a, a') -:: bl), a' = a → tr post (a -:: bl)))%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_seq; [by eapply type_share_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.

  Lemma tctx_reborrow_uniq {𝔄} E L p (ty: type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L +[p ◁ &uniq{κ} ty] +[p ◁ &uniq{κ'} ty; p ◁{κ'} &uniq{κ} ty]
      (λ post '-[(a, a')], ∀a'': 𝔄, post -[(a, a''); (a'', a')]).
  Proof.
    intros κκ'. split; [intros ??? [[??][]]; by apply forall_proper|].
    iIntros (??[vπ[]]?) "#LFT #PROPH #UNIQ E L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iDestruct (κκ' with "L E") as "#κ⊑κ'". iFrame "L".
    iDestruct "p" as ([[]|]??) "[⧖ [#In uniq]]"=>//.
    iDestruct "uniq" as (? ξi [Le Eq]) "[ξVo ξBor]". set ξ := PrVar _ ξi.
    move: Le=> /succ_le[?[->?]].
    iMod (rebor with "LFT κ⊑κ' ξBor") as "[ξBor ToξBor]"; [done|].
    iMod (uniq_intro (fst ∘ vπ) with "PROPH UNIQ") as (ζi) "(ζVo & ζPc)"; [done|].
    set ζ := PrVar _ ζi.
    iMod (bor_create _ κ' (∃vπ' d', .VO[ξ] vπ' d' ∗ ⧖(S d') ∗ .PC[ζ] vπ' d')%I
      with "LFT [⧖ ξVo ζPc]") as "[ζBor ToζBig]"; [done| |].
    { iExists _, _. iFrame "ξVo ζPc". iApply persistent_time_receipt_mono; [|done]. lia. }
    iMod (bor_combine with "LFT ξBor ζBor") as "Bor"; [done|].
    iExists -[λ π, ((vπ π).1, π ζ); λ π, (π ζ, (vπ π).2)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs") => /= π. case (vπ π)=>/= ?? All. apply All. }
    iMod (bor_acc_atomic_cons with "LFT Bor") as
      "[[[ξBig ζBig] ToBor]|[#†κ' TolftN]]"; [done| |]; last first.
    { iMod "TolftN" as "_". iMod ("ToξBor" with "†κ'").
      iMod ("ToζBig" with "†κ'") as (??) "(>ξVo & >#⧖ & ζPc)".
      iMod (uniq_strip_later with "ζVo ζPc") as (<-<-) "[ζVo ζPc]". iSplitL "ζVo".
      - iExists _, _. iFrame "⧖". iSplitR; [done|].
        iSplitR; [by iApply lft_incl_trans|]. iExists _, ζi. iFrame "ζVo".
        iSplitR; [done|]. by iApply bor_fake.
      - iModIntro. iSplitL; [|done]. iExists _. iSplit; [done|]. iIntros "_!>".
        iExists _, _. iFrame "⧖". iSplitL "ζPc"; last first.
        { iFrame "In". iExists _, _. by iFrame. }
        iNext. iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
        iApply (proph_eqz_prod with "[Eqz]"); [done|iApply proph_eqz_refl]. }
    iDestruct "ξBig" as (??) "(>#⧖ & ξPc & ↦ty)".
    iDestruct "ζBig" as (??) "(>ξVo & _ & ζPc)".
    iMod (uniq_strip_later with "ξVo ξPc") as (<-<-) "[ξVo ξPc]".
    iMod (uniq_strip_later with "ζVo ζPc") as (<-<-) "[ζVo ζPc]".
    iMod ("ToBor" $! (∃ vπ' d', ⧖(S d') ∗ .PC[ζ] vπ' d' ∗
      l ↦∗: ty.(ty_own) vπ' d' tid)%I with "[ξVo ξPc] [ζPc ↦ty]") as "ζBor".
    { iIntros "!> (%&% & #? & ζPc & ↦ty)".
      iMod (uniq_update with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
      iSplitL "↦ty ξPc"; iExists _, _; by iFrame. }
    { iNext. iExists _, _. by iFrame. }
    iModIntro. iSplitL "ζVo ζBor"; [|iSplitL; [|done]].
    { iExists _, _. iSplit; [done|]. iFrame "⧖".
      iSplitR; [by iApply lft_incl_trans|]. iExists _, _. by iFrame. }
    iExists _. iSplit; [done|]. iIntros "#†κ'". iMod ("ToξBor" with "†κ'") as "ξBor".
    iMod ("ToζBig" with "†κ'") as (vπ' ?) "(>ξVo & >⧖' & ζPc)". iModIntro.
    iExists _, _. iFrame "⧖' In". iSplitL "ζPc".
    - iNext. iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
      iApply (proph_eqz_prod _ (pair ∘ vπ' ⊛ (snd ∘ vπ)) with "[Eqz]");
      [done|iApply proph_eqz_refl].
    - iExists _, _.
      rewrite /uniq_body (proof_irrel (prval_to_inh _) (prval_to_inh (fst ∘ vπ))).
      by iFrame.
  Qed.

  Lemma tctx_extract_hasty_reborrow {𝔄 𝔅l} (ty ty': type 𝔄) κ κ' (T: tctx 𝔅l) E L p :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    tctx_extract_elt E L (p ◁ &uniq{κ'} ty) (p ◁ &uniq{κ} ty' +:: T)
      (p ◁{κ'} &uniq{κ} ty' +:: T) (λ post '((a, a') -:: bl),
        ∀a'': 𝔄, post ((a, a'') -:: (a'', a') -:: bl)).
  Proof.
    move=> ??. eapply tctx_incl_impl.
    - apply (tctx_incl_frame_r +[_] +[_;_]).
      eapply tctx_incl_trans; [by apply tctx_reborrow_uniq|].
      by apply subtype_tctx_incl, uniq_subtype, eqtype_symm.
    - by move=>/= ?[[??]?].
    - intros ??? [[??]?]. by apply forall_proper.
  Qed.

  Lemma type_deref_uniq_own_instr {𝔄} κ p n (ty: type 𝔄) E L :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &uniq{κ} (own_ptr n ty)]
        (!p) (&uniq{κ} ty) (λ post '-[a], post a).
  Proof.
    iIntros (Alvκ ?? [vπ []]) "#LFT #TIME #PROPH #UNIQ #E $ L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iMod (Alvκ with "E L") as (q) "[κ ToL]"; [done|]. wp_apply (wp_hasty with "p").
    iIntros ([[]|] ??) "#⧖ [#? uniq]"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[ξVo Bor]". set ξ := PrVar _ ξi.
    iMod (bor_acc_cons with "LFT Bor κ") as "[Body ToBor]"; [done|].
    iDestruct "Body" as (? d'') "(_ & ξPc & ↦own)". rewrite split_mt_ptr.
    case d'' as [|]; [iDestruct "↦own" as ">[]"|].
    iDestruct "↦own" as (?) "(>↦ & ↦ty & †)". iApply wp_fupd.
    iApply wp_cumulative_time_receipt; [done..|]. wp_read. iIntros "⧗1".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<-->].
    iMod (uniq_intro (fst ∘ vπ) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    rewrite proph_tok_singleton. set ζ := PrVar _ ζi.
    iMod (uniq_preresolve with "PROPH ξVo ξPc ζ") as "(EqObs & ζ & ToξPc)";
      [done|apply (proph_dep_one ζ)|].
    iCombine "EqObs Obs" as "Obs". iDestruct ("ToζPc" with "ζ") as "ζPc".
    iMod ("ToBor" with "[↦ ⧗1 † ToξPc] [↦ty ζPc]") as "[Bor κ]"; last first.
    - iExists -[λ π, ((vπ π).1, π ζ)]. iMod ("ToL" with "κ") as "$".
      rewrite right_id tctx_hasty_val'; [|done]. iModIntro. iSplitR "Obs".
      + iExists _. iFrame "⧖". iFrame "#". iExists d'', _. iFrame "ζVo Bor".
        iPureIntro. split; by [lia|].
      + iApply proph_obs_impl; [|done]=> π[<-?]. eapply eq_ind; [done|].
        move: (equal_f Eq π)=>/=. by case (vπ π)=>/= ??->.
    - iExists _, _. iNext. iFrame "↦ty ζPc".
      iApply persistent_time_receipt_mono; [|done]. lia.
    - iIntros "!> (%&%& >⧖' & ζPc &?)".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗1 ⧖'") as "⧖'";
        [solve_ndisj|].
      iIntros "!>!>". iDestruct ("ToξPc" with "[ζPc]") as "ξPc".
      { iApply (proph_ctrl_eqz with "PROPH ζPc"). }
      iExists _, _. iFrame "⧖' ξPc". rewrite split_mt_ptr. iExists _. iFrame.
  Qed.

  Lemma type_deref_uniq_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_uniq_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.

  Lemma type_deref_shr_own_instr {𝔅} {E L} κ p n (ty : type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L
      +[p ◁ &shr{κ} (own_ptr n ty)] (!p) (&shr{κ} ty) (λ post '-[a], post a).
  Proof.
    iIntros (Hκ tid ? [vπ []]) "#LFT #TIME #PROPH #UNIQ HE $ HL [Hp _] /= Hproph".
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; [done|].
    wp_apply (wp_hasty with "Hp"). iIntros ([[]|] [|[|depth]]) "_ #Hd Hown /="; try done.
    iDestruct "Hown" as (l') "#[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iApply wp_fupd. wp_read. iMod ("Hclose'" with "[H↦]") as "Htok1"; first by auto.
    iExists -[_]. iMod ("Hclose" with "[$Htok1 $Htok2]") as "[$$]".
    rewrite right_id tctx_hasty_val' //. iFrame.
    iExists (S _). simpl. iFrame "Hown".
    iApply (persistent_time_receipt_mono with "Hd"); lia.
  Qed.

  Lemma type_deref_shr_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_shr_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.

  Lemma type_deref_uniq_uniq_instr {𝔄 E L} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &uniq{κ} (&uniq{κ'}ty)] (!p) (&uniq{κ} ty)
      (λ post '-[((v, w), (v', w'))], w' = w → post (v, v')).
  Proof.
    iIntros (Hκ tid ? [vπ []]) "/= #LFT #TIME #PROPH #UNIQ #HE $ HL [Hp _] Hproph".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp").
    iIntros ([[]|] [|depth1]) "% #Hdepth1 [#Hκκ' H] //=";
      iDestruct "H" as (d' ξi) "([% %vπEqξ] & ξVo & Huniq)"; first lia.
    move: vπEqξ. set ξ := PrVar _ ξi=> vπEqξ.
    iAssert (κ ⊑ foldr meet static (ty_lfts ty))%I as "Hκ".
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iMod (bor_acc_cons with "LFT Huniq Htok") as "[big Hclose']"; [done|].
    iMod (bi.later_exist_except_0 with "big") as (? depth2) "(>#Hdepth2' & ξPc & ↦uniq)".
    rewrite split_mt_uniq_bor.
    iDestruct "↦uniq" as "(#Hκ' & %&%& %ωi &>[% %ωEq]& >Hl & ωVo & Hbor)".
    case depth2 as [|depth2]; [lia|]. set ω := PrVar _ ωi.
    iMod (uniq_strip_later with "ξVo ξPc") as (<-->) "[ξVo ξPc]".
    iMod (uniq_update ξ with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [done|].
    iMod ("Hclose'" $! (∃l': loc, l ↦ #l' ∗
      (∃ vπ' d', .VO[ω] vπ' d' ∗ .PC[ξ] (λ π, (vπ' π, π ω)) (S d') ∗ ⧖ (S (S d'))) ∗
      &{κ'}(∃ vπ' d', ⧖(S d') ∗ .PC[ω] vπ' d' ∗ l' ↦∗: ty.(ty_own) vπ' d' tid))%I
      with "[] [Hbor Hl ωVo ξPc]") as "[Hbor Htok]".
    { iIntros "!> H !>!>". iDestruct "H" as (l') "(H↦ & (%&%& ωVo & ξPc & ⧖) & H)".
      iExists _, (S d'). iFrame "⧖ ξPc". rewrite split_mt_uniq_bor. iFrame "Hκ'".
      iExists _, d', ωi. iFrame "H↦". rewrite /uniq_body.
      rewrite (proof_irrel (prval_to_inh _) (prval_to_inh (fst ∘ (fst ∘ vπ)))).
      by iFrame. }
    { iNext. iExists _. iFrame "Hl Hbor". iExists _, _. iFrame.
      iApply (persistent_time_receipt_mono); [|done]. lia. }
    iClear "Hdepth1 Hdepth2'". clear dependent p depth1 Hκ.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor"; [done|].
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]"; [done|].
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']"; [done|].
    iMod (bor_sep with "LFT Hbor") as "[BorVoPc Hbor]"; [done|].
    iMod (bor_unnest with "LFT Hbor") as "Hbor"; [done|].
    iApply wp_fupd. iApply wp_cumulative_time_receipt=>//. wp_read. iIntros "Ht".
    iMod "Hbor". iMod ("Hclose'" with "[H↦]") as "[_ Htok]"; first by auto.
    iMod (bor_combine with "LFT BorVoPc [Hbor]") as "Hbor"; [done| |].
    { iApply (bor_shorten with "[] Hbor").
      iApply lft_incl_glb; [|iApply lft_incl_refl].
      iApply lft_incl_trans; [iApply "Hκκ'" |]. iApply lft_intersect_incl_l. }
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[[VoPc Hown] Hclose']"; [done|].
    iDestruct "VoPc" as (vπ' ?) "(Hvo & Hpc & ?)".
    iMod (bi.later_exist_except_0 with "Hown") as (wπ depth3') "(>#? & Hpcω & Hown)".
    iMod (uniq_strip_later with "ξVo Hpc") as (?->) "[ξVo ξPc]".
    have ->: vπ' = fst ∘ (fst ∘ vπ).
    (* TODO: remove usage of fun_ext here.  *)
    { fun_ext => x /=. move: (equal_f H x) => /= y. by inversion y.  }
    iMod (uniq_strip_later with "Hvo Hpcω") as (<-->) "[ωVo ωPc]".
    iMod (uniq_intro (fst ∘ (fst ∘ vπ)) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    set ζ := PrVar _ ζi.
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    iDestruct (uniq_proph_tok with "ωVo ωPc") as "(ωVo & ω & ToωPc)".
    iMod (uniq_preresolve ξ [ζ; ω] (λ π, (π ζ, π ω)) with "PROPH ξVo ξPc [$ζ $ω]")
      as "(Hobs & (ζ & ω &_) & Heqz)"; [done| |done|].
    { apply (proph_dep_prod [_] [_]); apply proph_dep_one. }
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    iDestruct ("ToωPc" with "ω") as "ωPc".
    iMod ("Hclose'" $! (∃vπ' d', ⧖ (S d') ∗ .PC[ζ] vπ' d' ∗
      l' ↦∗: ty.(ty_own) vπ' d' tid)%I with "[Heqz ωVo ωPc Ht] [Hown ζPc]") as "[? Htok]".
    { iIntros "!> H".
      iMod (bi.later_exist_except_0 with "H") as (? ?) "(>#Hd' & Hpc & Hinner)".
      iMod (uniq_update with "UNIQ ωVo ωPc") as "[ωVo ωPc]"; [solve_ndisj|].
      iSplitR "Hinner ωPc".
      - iExists _, d'.
        iMod (cumulative_persistent_time_receipt with "TIME Ht Hd'") as "$";
          [solve_ndisj|].
        iFrame. iApply "Heqz". iDestruct (proph_ctrl_eqz with "PROPH Hpc") as "Eqz".
        iApply (proph_eqz_constr2 with "Eqz []"). iApply proph_eqz_refl.
      - iExists _, _. by iFrame. }
    { iExists _, _. by iFrame. }
    iExists -[λ π, ((vπ π).1.1 , π ζ)]. rewrite right_id.
    iMod ("Hclose" with "Htok") as "$". iSplitR "Hproph Hobs".
    - iExists _, _. iFrame "#". iSplitR; [done|]. iExists _, ζi. by iFrame.
    - iCombine "Hproph Hobs" as "?". iApply proph_obs_impl; [|done]=>/= π.
      move: (equal_f vπEqξ π) (equal_f ωEq π)=>/=. case (vπ π)=> [[??][??]]/=.
      case (π ξ)=> ??[=<-<-<-][Imp[=<-?]]. by apply Imp.
  Qed.

  Lemma type_deref_uniq_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e) (trx ∘
      (λ post '(((v, w), (v', w')) -:: cl), w' = w → tr post ((v, v') -:: cl)))%type.
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    by iApply type_let; [by eapply type_deref_uniq_uniq_instr|solve_typing| |done].
  Qed.

  Lemma type_deref_shr_uniq_instr {𝔄} {E L} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &shr{κ} (&uniq{κ'} ty)] (!p) (&shr{κ} ty)
      (λ post '-[(a, _)], post a).
  Proof.
    iIntros (Hκ tid ? [vπ []]) "#LFT #TIME #PROPH #UNIQ HE $ HL [Hp _] Hproph".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; [done|].
    wp_apply (wp_hasty with "Hp"). iIntros ([[]|] [|[|depth]]) "% #Hdepth Hshr //".
    iDestruct "Hshr" as (l' ξ) "(% & H↦ & Hdep & Hshr)".
    iMod (frac_bor_acc with "LFT H↦ Htok") as (q'') "[>H↦ Hclose']"; [done|].
    iApply wp_fupd. wp_read.
    iMod ("Hclose'" with "[H↦]") as "Htok"; [done|].
    iMod ("Hclose" with "Htok") as "$". iModIntro.
    rewrite [vπ]surjective_pairing_fun=>/=. iExists -[_]. iFrame "Hproph".
    rewrite right_id tctx_hasty_val' //. iExists (S depth). iFrame "Hshr".
    iApply (persistent_time_receipt_mono with "Hdepth"). lia.
  Qed.

  Lemma type_deref_shr_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e)
      (trx ∘ (λ post '((a, _) -:: bl), tr post (a -:: bl))).
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    iApply type_let; [by eapply type_deref_shr_uniq_instr|apply tctx_incl_refl| |done].
    by move=>/= ?[[??]?].
  Qed.
End borrow.

Global Hint Resolve tctx_extract_hasty_borrow tctx_extract_hasty_reborrow
  | 10 : lrust_typing.
