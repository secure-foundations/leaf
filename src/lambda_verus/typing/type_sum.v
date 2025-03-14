From iris.proofmode Require Import proofmode.
From lrust.lang Require Import memcpy.
From lrust.typing Require Import int uninit uniq_bor shr_bor own sum.
From lrust.typing Require Import lft_contexts type_context programs product.
From lrust.typing Require Import base_type.

Set Default Proof Using "Type".
Open Scope nat.

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Notation sum_pad_size tyl ty := (max_ty_size tyl - ty.(ty_size))%nat.

Section type_sum.
  Context `{!typeG Σ}.

  (** * Owning Pointers *)

  Lemma tctx_unwrap_own_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) n p (T: tctx 𝔅l) E L :
    let tyi := tyl +!! i in
    tctx_incl E L (p ◁ own_ptr n (Σ! tyl) +:: T)
      (p +ₗ #0 ◁ own_ptr n int +:: p +ₗ #1 ◁ own_ptr n tyi +::
        p +ₗ #(S tyi.(ty_size)) ◁ own_ptr n (↯ (sum_pad_size tyl tyi)) +:: T)
      (λ post '(s -:: bl), ∃a: 𝔄l !!ₗ i,
        s = pinj i a ∧ post (Z.of_nat i -:: a -:: () -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by do 3 f_equiv. }
    iIntros (??[??]?) "_ PROPH _ _ $ /=[p T] #Obs".
    iDestruct "p" as ([[]|][|]Ev) "[#⧖ own]"=>//. rewrite/= split_mt_sum.
    iDestruct "own" as "[big †]".
    iMod (bi.later_exist_except_0 with "big") as (?) "big".
    iMod (bi.later_exist_except_0 with "big") as (?) "(>->&(↦i &%& ↦p &><-)&%& ↦ & ty)".
    rewrite -(Nat.add_1_l (_+_)) -!freeable_sz_split.
    iDestruct "†" as "(†i & † & †p)". iDestruct (ty_size_eq with "ty") as "#>%Sz".
    iMod (proph_obs_sat with "PROPH Obs") as %[?[?[Eq _]]]; [done|].
    apply pinj_inj in Eq. move: Eq=> [? _]. subst. iModIntro.
    iExists (const _-::_-::const ()-::_). iFrame "T". iSplit; last first.
    { iApply proph_obs_impl; [|done]=>/= ?[?[Eq ?]]. apply pinj_Inj in Eq. by subst. }
    iSplitL "↦i †i"; [|iSplitR "↦p †p"]; iExists _, _=>/=; rewrite Ev;
    do 2 (iSplit; [done|]).
    - rewrite shift_loc_0. iFrame "†i". iNext. iExists [_].
      rewrite heap_mapsto_vec_singleton. iFrame "↦i". by iExists _.
    - iFrame "†". iNext. iExists _. iFrame.
    - iSplitL "↦p". { iNext. iExists _. iFrame "↦p". iPureIntro. lia. }
      rewrite shift_loc_assoc_nat. iApply freeable_sz_eq; [|done]. lia.
  Qed.

  Lemma type_case_own_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) n p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ own_ptr n (Σ! tyl)] T T' trx →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L C (p ◁ own_ptr n (Σ! tyl) +:: T') e tr) -∗
    typed_body E L C T (case: !p of el)
      (trx ∘ (λ post '(s -:: cl), let 'xinj i _ := to_xsum s in
        (trl -!! i) post (s -:: cl)))%type.
  Proof.
    move=> ->. iIntros (?) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (?[??]?) "LFT TIME PROPH UNIQ E Na L C /=[p T] #?".
    wp_apply (wp_hasty with "p"). iIntros ([[]|][|]?) "#⧖ own"=>//.
    iDestruct "own" as "[(%& >↦ & big) †]".
    iMod (bi.later_exist_except_0 with "big") as (?) "big".
    iMod (bi.later_exist_except_0 with "big") as (aπ ??) "[>(->&->&%) ty]".
    rewrite heap_mapsto_vec_cons. iDestruct "↦" as "[↦i ↦]". wp_read. wp_case.
    { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    rewrite big_sepHL_2_lookup. iApply ("el" $! _ ((λ π, _) -:: _) with
      "LFT TIME PROPH UNIQ E Na L C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _, _. iSplit; [done|]. iFrame "⧖ †". iNext.
    iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame "↦ ↦i".
    iExists _, _, _, _. by iFrame "ty".
  Qed.

  Lemma type_case_own {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) n p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ own_ptr n (Σ! tyl)] T T' trx →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L C (p ◁ own_ptr n (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L C
          (p +ₗ #0 ◁ own_ptr n int +:: p +ₗ #1 ◁ own_ptr n ty +::
            p +ₗ #(S ty.(ty_size)) ◁ own_ptr n (↯ (sum_pad_size tyl ty)) +:: T') e itr
      end) -∗
    typed_body E L C T (case: !p of el) (trx ∘ (λ post '(s -:: cl),
      let 'xinj i a := to_xsum s in match trl -!! i with
        | inl otr => otr post (s -:: cl)
        | inr itr => itr post (Z.of_nat i -:: a -:: () -:: cl)
        end)).
  Proof.
    iIntros (??) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_own_outer _ (pbyidx (λ i post '(s -:: cl),
        match trl -!! i with inl otr => otr post (s -:: cl) | inr itr => _ end
        : Prop))); [apply tctx_incl_refl|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "?". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?; [by via_tr_impl; [done|]=> ?[??]?|]. via_tr_impl.
      { iApply typed_body_tctx_incl; [apply tctx_unwrap_own_xsum|done]. }
      move=>/= ?[??]. exact id. }
    move=> ?[s ?]/=. case (to_xsum s) as [i ?] eqn: Eq. rewrite pbyidx_plookup.
    move: (trl -!! i). case; [done|]=>/= ??. eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_own_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) n p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ own_ptr n (Σ! tyl)] T T' trx →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L C (p +ₗ #0 ◁ own_ptr n int +:: p +ₗ #1 ◁ own_ptr n ty +::
        p +ₗ #(S ty.(ty_size)) ◁ own_ptr n (↯ (sum_pad_size tyl ty)) +:: T') e tr) -∗
    typed_body E L C T (case: !p of el) (trx ∘ (λ post '(s -:: cl),
      let 'xinj i a := to_xsum s in
      (trl -!! i) post (Z.of_nat i -:: a -:: () -:: cl))).
  Proof.
    iIntros (??) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_own _ (pbyidx (λ i, inr (trl -!! i)))); [solve_typing|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[s ?]/=. case (to_xsum s)=>/= ??. by rewrite pbyidx_plookup.
  Qed.

  (** * Shared References *)

  Lemma tctx_unwrap_shr_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) κ p (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ &shr{κ} (Σ! tyl) +:: T) (p +ₗ #1 ◁ &shr{κ} (tyl +!! i) +:: T)
      (λ post '(s -:: bl), ∃a: 𝔄l !!ₗ i, s = pinj i a ∧ post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by do 3 f_equiv. }
    iIntros (??[??]?) "_ PROPH _ _ $ /=[p T] #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as %[?[?[Eq _]]]; [done|]. iModIntro.
    iDestruct "p" as ([[]|][|]Ev) "[#⧖ sum]"=>//.
    iDestruct "sum" as (??->) "[_ ty]". apply pinj_inj in Eq. move: Eq=> [??].
    subst. iExists (_-::_). iFrame "T". iSplit.
    { iExists _, _. iSplit; [by rewrite/= Ev|]. iFrame "⧖ ty". }
    iApply proph_obs_impl; [|done]=>/= ?[?[Eq ?]]. apply pinj_Inj in Eq. by subst.
  Qed.

  Lemma type_case_shr_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L C (p ◁ &shr{κ} (Σ! tyl) +:: T') e tr) -∗
    typed_body E L C T (case: !p of el)
      (trx ∘ (λ post '(s -:: cl), let 'xinj i _ := to_xsum s in
        (trl -!! i) post (s -:: cl)))%type.
  Proof.
    move=> ->. iIntros (? Alv) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (?[??]?) "#LFT TIME PROPH UNIQ #E Na L C /=[p T] #?".
    wp_apply (wp_hasty with "p"). iIntros ([[]|][|]?) "#⧖ sum"=>//.
    iDestruct "sum" as (??->) "[#Bor ty]".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (frac_bor_acc with "LFT Bor κ") as (?) "[[>↦i ↦p] Toκ]"; [done|].
    wp_read. iMod ("Toκ" with "[$↦i $↦p]") as "κ". iMod ("ToL" with "κ") as "L".
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    rewrite big_sepHL_2_lookup. iApply ("el" $! _ ((λ π, _) -:: _) with
      "LFT TIME PROPH UNIQ E Na L C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _, _. iSplit; [done|]. iFrame "⧖". iExists _, _.
    by iFrame "Bor ty".
  Qed.

  Lemma type_case_shr {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L C (p ◁ &shr{κ} (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L C (p +ₗ #1 ◁ &shr{κ} ty +:: T') e itr
      end) -∗
    typed_body E L C T (case: !p of el) (trx ∘ (λ post '(s -:: cl),
      let 'xinj i a := to_xsum s in match trl -!! i with
        | inl otr => otr post (s -:: cl)
        | inr itr => itr post (a -:: cl)
        end)).
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_shr_outer _ (pbyidx (λ i post '(s -:: cl),
        match trl -!! i with inl otr => otr post (s -:: cl) | inr itr => _ end
        : Prop))); [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "?". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?; [by via_tr_impl; [done|]=> ?[??]?|]. via_tr_impl.
      { iApply typed_body_tctx_incl; [apply tctx_unwrap_shr_xsum|done]. }
      move=>/= ?[??]. exact id. }
    move=> ?[s ?]/=. case (to_xsum s) as [i ?] eqn: Eq. rewrite pbyidx_plookup.
    move: (trl -!! i). case; [done|]=>/= ??. eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_shr_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L C (p +ₗ #1 ◁ &shr{κ} ty +:: T') e tr) -∗
    typed_body E L C T (case: !p of el) (trx ∘ (λ post '(s -:: cl),
      let 'xinj i a := to_xsum s in (trl -!! i) post (a -:: cl))).
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_shr _ (pbyidx (λ i, inr (trl -!! i))));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[s ?]/=. case (to_xsum s)=>/= ??. by rewrite pbyidx_plookup.
  Qed.

  (** * Unique References *)

  Lemma tctx_unwrap_uniq_xsum {𝔄l 𝔅l} i (tyl: typel 𝔄l) κ p (T: tctx 𝔅l) E L :
    lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} (Σ! tyl) +:: T) (p +ₗ #1 ◁ &uniq{κ} (tyl +!! i) +:: T)
      (λ post '((s, s') -:: bl), ∃a: 𝔄l !!ₗ i, s = pinj i a ∧
        ∀a': 𝔄l !!ₗ i, s' = pinj i a' → post ((a, a') -:: bl)).
  Proof.
    move=> Alv. split.
    { move=>/= ???[[??]?]. do 3 f_equiv. by do 2 (apply forall_proper=> ?). }
    iIntros (??[vπ ?]?) "LFT #PROPH UNIQ E L /=[p T] #Obs".
    iDestruct "p" as ([[]|]? Ev) "(_&#?& uniq)"=>//.
    iDestruct "uniq" as (? ξi [? Eq2]) "[Vo Bor]". set ξ := PrVar _ ξi.
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ") as "[big ToBor]" ; [done|].
    iMod (bi.later_exist_except_0 with "big") as (??) "(>#⧖ & Pc & big)".
    rewrite split_mt_sum. iMod (bi.later_exist_except_0 with "big") as (i') "big".
    iMod (bi.later_exist_except_0 with "big") as (aπ) "(>->& ↦ip &%& >↦ & ty)".
    iMod (uniq_strip_later with "Vo Pc") as (Eq1 <-) "[Vo Pc]".
    have ->: vπ = λ π, (pinj i' (aπ π), π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    iMod (proph_obs_sat with "PROPH Obs") as %[?[?[Eq _]]]; [done|].
    apply pinj_inj in Eq. move: Eq=> [? _]. subst.
    iMod (uniq_intro aπ with "PROPH UNIQ") as (ζi) "[Vo' Pc']"; [done|].
    set ζ := PrVar _ ζi. iDestruct (uniq_proph_tok with "Vo' Pc'") as "(Vo' & ζ & Pc')".
    iMod (uniq_preresolve ξ [ζ] (λ π, pinj i (π ζ)) with "PROPH Vo Pc [$ζ]")
      as "(Obs' &[ζ _]& ToPc)"; [done|by apply proph_dep_constr, proph_dep_one|done|].
    iCombine "Obs' Obs" as "#?". iClear "Obs". iSpecialize ("Pc'" with "ζ").
    iMod ("ToBor" with "[↦ip ToPc] [↦ ty Pc']") as "[Bor κ]"; last first.
    - iMod ("ToL" with "κ") as "$". iModIntro.
      iExists ((λ π, (aπ π, π ζ)) -::_). iFrame "T". iSplitL.
      { iExists _, _. iSplit; [by rewrite/= Ev|]. iFrame "⧖". iSplit.
        { iApply lft_incl_trans; [done|]. iApply ty_lfts_lookup_incl. }
        iExists _, _. by iFrame. }
      iApply proph_obs_impl; [|done]=>/= ?[?[?[Eq All]]]. apply pinj_Inj in Eq.
      subst. by apply All.
    - iNext. iExists _, _. iFrame "⧖ Pc'". iExists _. iFrame.
    - iIntros "!> big !>!>". iDestruct "big" as (??) "(⧖' & Pc' &%& ↦ & ty)".
      iExists _, _. iFrame "⧖'". iSplitL "Pc' ToPc".
      { iApply "ToPc". iApply proph_eqz_constr. by iApply proph_ctrl_eqz. }
      rewrite split_mt_sum. iExists _, _. iSplit; [done|]. iFrame "↦ip".
      iExists _. iFrame.
  Qed.

  Lemma type_case_uniq_outer {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L C (p ◁ &uniq{κ} (Σ! tyl) +:: T') e tr) -∗
    typed_body E L C T (case: !p of el)
      (trx ∘ (λ post '((s, s') -:: cl), let 'xinj i _ := to_xsum s in
        (trl -!! i) post ((s, s') -:: cl)))%type.
  Proof.
    move=> ->. iIntros (? Alv) "el". iApply typed_body_tctx_incl; [done|].
    iIntros (?[vπ ?]?) "#LFT TIME PROPH UNIQ #E Na L C /=[p T] #?".
    wp_apply (wp_hasty with "p"). iIntros ([[]|]??) "_ [#In uniq]"=>//.
    iDestruct "uniq" as (? ξi [??]) "[Vo Bor]". set ξ := PrVar _ ξi.
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as "[big ToBor]"; [done|].
    iMod (bi.later_exist_except_0 with "big") as (??) "(#⧖ & Pc & big)".
    rewrite split_mt_sum. iMod (bi.later_exist_except_0 with "big") as (i) "big".
    iMod (bi.later_exist_except_0 with "big") as (aπ) "(>->& [>↦i ↦p] & ↦ty)".
    wp_read. iDestruct (uniq_agree with "Vo Pc") as %[Eq <-].
    iMod ("ToBor" with "[Pc ↦i ↦p ↦ty]") as "[Bor κ]".
    { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_sum. iExists _, _. by iFrame. }
    iMod ("ToL" with "κ") as "L". wp_case.
    { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    rewrite big_sepHL_2_lookup. iApply ("el" $! _ (vπ -:: _) with
      "LFT TIME PROPH UNIQ E Na L C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq π)=>/=.
      case (vπ π)=>/= ??->. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _, _. iSplit; [done|]. iFrame "⧖ In". iExists _, _. by iFrame.
  Qed.

  Lemma type_case_uniq {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl, match tr with
      | inl otr => typed_body E L C (p ◁ &uniq{κ} (Σ! tyl) +:: T') e otr
      | inr itr => typed_body E L C (p +ₗ #1 ◁ &uniq{κ} ty +:: T') e itr
      end) -∗
    typed_body E L C T (case: !p of el) (trx ∘ (λ post '((s, s') -:: cl),
      let 'xinj i a := to_xsum s in match trl -!! i with
        | inl otr => otr post ((s, s') -:: cl)
        | inr itr => ∀a': 𝔄l !!ₗ i, s' = pinj i a' → itr post ((a, a') -:: cl)
        end))%type.
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_uniq_outer _ (pbyidx (λ i post '((s, s') -:: cl),
        match trl -!! i with inl otr => otr post ((s, s') -:: cl) | inr itr => _ end
        : Prop))); [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (i) "?". rewrite pbyidx_plookup.
      case (trl -!! i)=> ?; [by via_tr_impl; [done|]=> ?[[??]?]?|]. via_tr_impl.
      { iApply typed_body_tctx_incl; [by apply tctx_unwrap_uniq_xsum|done]. }
      move=>/= ?[[??]?]. exact id. }
    move=> ?[[s ?]?]/=. case (to_xsum s) as [i ?] eqn: Eq. rewrite pbyidx_plookup.
    move: (trl -!! i). case; [done|]=>/= ??. eexists _. split; [|done].
    move: Eq=> /(f_equal of_xsum)=>/= <-. by rewrite semi_iso'.
  Qed.

  Lemma type_case_uniq_inner {𝔄l 𝔅l ℭl 𝔇} (tyl: typel 𝔄l) trl (T: tctx 𝔅l)
      (T': tctx ℭl) κ p el el' trx E L (C: cctx 𝔇) :
    IntoPlistc el el' →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (Σ! tyl)] T T' trx → lctx_lft_alive E L κ →
    ([∗ hlist] ty;- e; tr ∈ tyl;- el'; trl,
      typed_body E L C (p +ₗ #1 ◁ &uniq{κ} ty +:: T') e tr) -∗
    typed_body E L C T (case: !p of el) (trx ∘ (λ post '((s, s') -:: cl),
      let 'xinj i a := to_xsum s in
      ∀a': 𝔄l !!ₗ i, s' = pinj i a' → (trl -!! i) post ((a, a') -:: cl)))%type.
  Proof.
    iIntros (???) "el". iApply typed_body_tctx_incl; [done|]. via_tr_impl.
    { iApply (type_case_uniq _ (pbyidx (λ i, inr (trl -!! i))));
        [apply tctx_incl_refl|done|].
      rewrite !big_sepHL_2_big_sepN. iApply (big_sepN_impl with "el").
      iIntros "!>" (?) "?". by rewrite pbyidx_plookup. }
    move=> ?[[s ?]?]/=. case (to_xsum s)=>/= ??. by rewrite pbyidx_plookup.
  Qed.

  (** * Write *)

  Lemma type_sum_assign_instr {𝔄 𝔄' 𝔅 𝔅l} (tyl: typel 𝔅l) (i: fin _)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')  p q gt st Φ E L :
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    typed_instr E L +[p ◁ ty; q ◁ tyl +!! i] (p <-{Σ i} q) (λ _, +[p ◁ ty'])
      (λ post '-[a; b], Φ (gt a) (post -[st a (pinj i b)])).
  Proof.
    iIntros ([Sztyb Wrt] Rslv ??(?&?&[]))
      "#LFT #TIME PROPH UNIQ #E $ [L L₊] /=(p & q &_) Obs".
    iDestruct (closed_hasty with "p") as %?. iDestruct (closed_hasty with "q") as %?.
    wp_apply (wp_hasty with "p"). iIntros (???) "⧖ ty".
    iMod (Wrt with "LFT UNIQ E L ty") as (?->) "[(%vl & ↦ & tyb) Toty']".
    iDestruct (ty_size_eq with "tyb") as "#>%Lenvl".
    move: Lenvl. rewrite Sztyb. move: vl=> [|]; [done|]=>/= ? vl [= Lenvl].
    rewrite heap_mapsto_vec_cons. iDestruct "↦" as "[>↦i ↦]". wp_write.
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?->).
    iMod (Rslv with "LFT PROPH E L₊ tyb") as "Upd"; [done|]. wp_bind (_+ₗ_)%E.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
      [done..| |]. { iApply step_fupdN_with_emp. by rewrite difference_empty_L. }
    wp_op. iIntros "[Obs' $] !>". iCombine "Obs Obs'" as "Obs".
    wp_apply (wp_hasty with "q"). iIntros (???) "⧖' tyi".
    iDestruct (ty_size_eq with "tyi") as %Sztyi.
    move: (max_hlist_with_ge (λ _, ty_size) tyl i). rewrite -Sztyi -Lenvl /=.
    case vl=>/=; [lia|]=> ?? _. rewrite heap_mapsto_vec_cons.
    iDestruct "↦" as "[↦ ↦p]". iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [done|]. wp_write.
    iIntros "#⧖'". iMod ("Toty'" with "[↦i ↦ ↦p tyi] ⧖'") as "[$ ty']".
    { iNext. iExists (_::_::_). rewrite !heap_mapsto_vec_cons.
      iFrame "↦i ↦ ↦p". iExists _, _, [_], _. by iFrame. }
    iModIntro. iExists -[_]. rewrite right_id.
    iSplit. { iExists _, _. by iFrame "⧖' ty'". }
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp.
  Qed.

  Lemma type_sum_assign {𝔄 𝔄' 𝔅 𝔅l ℭl 𝔇l 𝔈} (tyl: typel 𝔅l) (i: fin _)
      (k: Z) (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
      (T: tctx ℭl) (T': tctx 𝔇l) p q gt st Φ tr trx E L (C: cctx 𝔈) e :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ ty; q ◁ tyl +!! i] T T' trx →
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    typed_body E L C (p ◁ ty' +:: T') e tr -∗
    typed_body E L C T (p <-{Σ k} q;; e) (trx ∘ (λ post '(a -:: b' -:: dl),
      Φ (gt a) (tr post (st a (pinj i b') -:: dl)))).
  Proof.
    iIntros (?->???) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_assign_instr|apply tctx_incl_refl| |done].
    by move=> ?[?[??]]/=.
  Qed.

  Lemma type_sum_unit_instr {𝔄 𝔄' 𝔅 𝔅l} (tyl: typel 𝔅l) (i: fin _)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') f p gt st Φ E L :
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    subtype E L () (tyl +!! i) f →
    typed_instr E L +[p ◁ ty] (p <-{Σ i} ()) (λ _, +[p ◁ ty'])
      (λ post '-[a], Φ (gt a) (post -[st a (pinj i (f ()))])).
  Proof.
    iIntros ([Sztyb Wrt] Rslv Sub ??[?[]]) "#LFT #TIME PROPH UNIQ #E $ [L L₊] [p _] Obs".
    iDestruct (Sub with "L") as "#In". iDestruct ("In" with "E") as "(%&_& #InOwn &_)".
    wp_apply (wp_hasty with "p"). iIntros (???) "⧖ ty".
    iMod (Wrt with "LFT UNIQ E L ty") as (?->) "[(%vl & ↦ & tyb) Toty']".
    iDestruct (ty_size_eq with "tyb") as "#>%Lenvl".
    move: Lenvl. rewrite Sztyb. move: vl=> [|]; [done|]=>/= ? vl [= Lenvl].
    rewrite heap_mapsto_vec_cons. iDestruct "↦" as "[>↦i ↦]". wp_bind (_<-_)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. wp_write.
    iIntros "#⧖". iMod (Rslv with "LFT PROPH E L₊ tyb") as "Upd"; [done|].
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
      [done..| |].
    { iApply step_fupdN_with_emp. rewrite difference_empty_L /=.
      by iIntros "!>!>!>!>!>!>!>". }
    do 2 wp_seq. iIntros "[Obs' $]". iCombine "Obs Obs'" as "Obs".
    iDestruct ("InOwn" $! (const ()) _ _ [] with "[]") as "tyi".
    { by iExists (const -[]). }
    iMod ("Toty'" with "[↦i ↦ tyi] ⧖") as "[$ ty']".
    { iNext. iExists (_::_). rewrite !heap_mapsto_vec_cons. iFrame "↦i ↦".
      iExists i, _, [], _. iFrame "tyi". by rewrite/= Lenvl. }
    iModIntro. iExists -[_]. rewrite right_id.
    iSplit. { iExists _, _. by iFrame "⧖ ty'". }
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp.
  Qed.

  Lemma type_sum_unit {𝔄 𝔄' 𝔅 𝔅l ℭl 𝔇l 𝔈} (tyl: typel 𝔅l) (i: fin _) (k: Z)
      (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') (T: tctx ℭl) (T': tctx 𝔇l)
      f trx tr p gt st e Φ E L (C: cctx 𝔈) :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    typed_write E L ty tyb ty' (Σ! tyl) gt st → resolve' E L tyb Φ →
    subtype E L () (tyl +!! i) f →
    typed_body E L C (p ◁ ty' +:: T') e tr -∗
    typed_body E L C T (p <-{Σ k} ();; e) (trx ∘
      (λ post '(a -:: dl), Φ (gt a) (tr post (st a (pinj i (f ())) -:: dl)))).
  Proof.
    iIntros (?->????) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_unit_instr|by apply tctx_incl_refl| |done].
    by move=> ?[??]/=.
  Qed.

  Lemma type_sum_memcpy_instr {𝔄 𝔄' 𝔅 𝔅' ℭ ℭl} (tyl: typel ℭl) (i: fin _)
      (tyw: type 𝔄) (tyw': type 𝔄') (tyr: type 𝔅) (tyr': type 𝔅')
      (tyb: type ℭ) p q gtw stw gtr str Φ E L :
    typed_write E L tyw tyb tyw' (Σ! tyl) gtw stw → resolve' E L tyb Φ →
    typed_read E L tyr (tyl +!! i) tyr' gtr str →
    typed_instr E L +[p ◁ tyw; q ◁ tyr]
      (p <-{(tyl +!! i).(ty_size),Σ i} !q) (λ _, +[p ◁ tyw'; q ◁ tyr'])
      (λ post '-[a; b], Φ (gtw a) (post -[stw a (pinj i (gtr b)); str b])).
  Proof.
    set tyi := tyl +!! i. iIntros ([Sztyb Wrt] Rslv Rd ??(?&?&[]))
      "#LFT #TIME PROPH UNIQ #E Na [L L₊] /=(p & q &_) Obs".
    iDestruct (closed_hasty with "p") as %?. iDestruct (closed_hasty with "q") as %?.
    wp_apply (wp_hasty with "p"). iIntros (???) "#⧖ tyw".
    iMod (Wrt with "LFT UNIQ E L tyw") as (?->) "[(%vl & ↦ & tyb) Totyw']".
    iDestruct (ty_size_eq with "tyb") as "#>%Lenvl".
    move: Lenvl. rewrite Sztyb. move: vl=> [|]; [done|]=>/= ? vl [= Lenvl].
    rewrite heap_mapsto_vec_cons. iDestruct "↦" as "[>↦i ↦]". wp_write.
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?->).
    iMod (Rslv with "LFT PROPH E L₊ tyb") as "Upd"; [done|]. wp_bind (_+ₗ_)%E.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
      [done..| |]. { iApply step_fupdN_with_emp. by rewrite difference_empty_L. }
    wp_op. iIntros "[Obs' L₊] !>". iCombine "Obs Obs'" as "Obs".
    wp_apply (wp_hasty with "q"). iIntros (???) "#⧖' tyr".
    iMod (Rd with "LFT E Na L₊ tyr") as (? vl' ?->) "(↦' & tyi & Totyr')".
    iDestruct (ty_size_eq with "tyi") as "#>%Lenvl'".
    move: (max_hlist_with_ge (λ _, ty_size) tyl i).
    set tyisz := tyi.(ty_size). set maxsz := max_hlist_with _ _=> ?.
    have LenvlAdd: length vl = tyisz + (maxsz - tyisz) by lia.
    move: LenvlAdd=> /app_length_ex[wl[wl'[->[Lenwl ?]]]].
    rewrite heap_mapsto_vec_app Lenwl. iDestruct "↦" as "[↦ ↦p]". iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [done|].
    iApply (wp_memcpy with "[$↦ $↦']"); [lia..|]. iIntros "!> [↦ ↦'] #⧖'S".
    iMod ("Totyr'" with "↦'") as "($&$& tyr')".
    iMod ("Totyw'" with "[↦i ↦ ↦p tyi] ⧖'S") as "($& tyw')".
    { iNext. iExists (_::_++_). rewrite heap_mapsto_vec_cons heap_mapsto_vec_app.
      rewrite /tyisz -Lenvl'. iFrame "↦i ↦ ↦p". iExists _, _, _, _. iFrame "tyi".
      iPureIntro. do 2 (split; [done|]). rewrite/= app_length. lia. }
    iModIntro. iExists -[λ π, _;λ π, _]. rewrite right_id. iSplit; last first.
    { iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp. }
    iSplitL "tyw'"; iExists _, _; (iSplit; [done|]); by iFrame.
  Qed.

  Lemma type_sum_memcpy {𝔄 𝔄' 𝔅 𝔅' ℭ ℭl 𝔇l 𝔈l 𝔉} (tyl: typel ℭl) (i: fin _)
      (tyw: type 𝔄) (tyr: type 𝔅) (tyw': type 𝔄') (tyr': type 𝔅') (tyb: type ℭ) (k n: Z)
      (T: tctx 𝔇l) (T': tctx 𝔈l) p q gtw stw gtr str trx tr e Φ E L (C: cctx 𝔉) :
    Closed [] e → k = i → tctx_extract_ctx E L +[p ◁ tyw; q ◁ tyr] T T' trx →
    typed_write E L tyw tyb tyw' (Σ! tyl) gtw stw → resolve' E L tyb Φ →
    n = (tyl +!! i).(ty_size) → typed_read E L tyr (tyl +!! i) tyr' gtr str →
    typed_body E L C (p ◁ tyw' +:: q ◁ tyr' +:: T') e tr -∗
    typed_body E L C T (p <-{n,Σ k} !q;; e)
      (trx ∘ (λ post '(a -:: b -:: el),
        Φ (gtw a) (tr post (stw a (pinj i (gtr b)) -:: str b -:: el)))).
  Proof.
    iIntros (?->???->?) "e". iApply typed_body_tctx_incl; [done|].
    iApply type_seq; [by eapply type_sum_memcpy_instr|by apply tctx_incl_refl| |done].
    by move=> ?[?[??]]/=.
  Qed.

  Lemma ty_outlives_E_elctx_sat_sum {𝔄l} E L (tyl: typel 𝔄l) κ :
    elctx_sat E L (tyl_outlives_E tyl κ) →
    elctx_sat E L (ty_outlives_E (Σ! tyl) κ).
  Proof.
    move=> Sat. eapply eq_ind; [done|]. clear Sat.
    rewrite /tyl_outlives_E /ty_outlives_E /=.
    induction tyl as [|???? IH]=>//=. by rewrite IH fmap_app.
  Qed.
End type_sum.

Global Hint Resolve ty_outlives_E_elctx_sat_sum : lrust_typing.
