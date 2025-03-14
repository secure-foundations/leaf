From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs array_util
  array int own shr_bor uniq_bor product product_split.
Set Default Proof Using "Type".

Implicit Type 𝔄: syn_type.

Section array_idx.
  Context `{!typeG Σ}.

  (** * Owning Pointers *)

  Fixpoint hasty_own_idxs {𝔄} (p: path) (k: nat) (ty: type 𝔄) (n: nat)
      (i: nat) : tctx (replicate n 𝔄) :=
    match n with
    | O => +[]
    | S m =>
      p +ₗ #(i * ty.(ty_size))%nat ◁ own_ptr k ty +::
      hasty_own_idxs p k ty m (S i)
    end.

  Lemma hasty_own_idxs_equiv {𝔄} p k (ty: type 𝔄) n i :
    tctx_equiv (hasty_own_idxs (p +ₗ #ty.(ty_size)) k ty n i)
      (hasty_own_idxs p k ty n (S i)).
  Proof.
    apply get_tctx_equiv=> ? vπl. move: p i. induction n; [done|]=> p ?.
    case vπl=>/= ??. f_equiv; [|done].
    rewrite tctx_elt_interp_hasty_path; [done|]=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Lemma tctx_split_own_array {𝔄} k (ty: type 𝔄) n p E L :
    tctx_incl E L +[p ◁ own_ptr k [ty;^ n]] (hasty_own_idxs p k ty n 0)
      (λ post '-[al], post (vec_to_plist al)).
  Proof.
    move: p. elim n.
    { move=> ?. eapply tctx_incl_ext; [by apply tctx_incl_resolve_head|]=>/= ?[v[]].
      by inv_vec v. }
    move=>/= ? IH ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans;
        [by eapply subtype_tctx_incl; eapply own_subtype, proj1, array_succ_prod|].
      eapply tctx_incl_trans; [by eapply tctx_split_own_prod|]. apply tctx_incl_tail.
      eapply tctx_incl_trans; [by apply IH|]. eapply proj1, hasty_own_idxs_equiv. }
    move=>/= ?[v[]]. by inv_vec v.
  Qed.

  Lemma tctx_extract_split_own_array {𝔄 𝔄' 𝔅l ℭl} (t: tctx_elt 𝔄) k
      (ty: type 𝔄') n (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_own_idxs p k ty n 0) T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr k [ty;^ n] +:: T) (T' h++ T) (λ post
      '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) (vec_to_plist al)).
  Proof.
    move=> Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; by [apply tctx_split_own_array|]. }
    destruct Extr as [Htr _]=>/= ?[??]. apply Htr.  by case.
  Qed.

  Lemma tctx_merge_own_array {𝔄} k (ty: type 𝔄) n p E L :
    tctx_incl E L (hasty_own_idxs p k ty (S n) 0) +[p ◁ own_ptr k [ty;^ S n]]
      (λ post al, post -[plist_to_vec al]).
  Proof.
    move: p. elim: n.
    { move=> ?. eapply tctx_incl_ext.
      { eapply tctx_incl_trans; [by apply tctx_of_shift_loc_0|].
        eapply subtype_tctx_incl, own_subtype, proj2, array_one. }
      by move=> ?[?[]]. }
    move=>/= ? IH ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans;
        [|by eapply subtype_tctx_incl, own_subtype, proj2, array_succ_prod].
      eapply tctx_incl_trans; [|by eapply tctx_merge_own_prod].
      apply tctx_incl_tail. eapply tctx_incl_trans; [|by apply IH].
      apply (tctx_incl_app +[_] +[_]); [|by eapply proj2, hasty_own_idxs_equiv].
      rewrite Nat2Z.inj_add. eapply proj2, tctx_shift_loc_assoc. }
    by move=>/= ?[?[??]].
  Qed.

  Lemma tctx_extract_merge_own_array {𝔄 𝔅l ℭl} k (ty: type 𝔄) n
    (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_ctx E L (hasty_own_idxs p k ty (S n) 0) T T' tr →
    tctx_extract_elt E L (p ◁ own_ptr k [ty;^ S n]) T T' (λ post, tr
      (λ acl, let '(al, cl) := psep acl in post (plist_to_vec al -:: cl))).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [done|].
      apply (tctx_incl_frame_r _ +[_]), tctx_merge_own_array. }
    done.
  Qed.

  (** * Shared References *)

  Lemma tctx_idx_shr_array {𝔄 𝔅l} (ty: type 𝔄) n κ p (i: fin n) (T: tctx 𝔅l) E L :
    tctx_incl E L (p ◁ &shr{κ} [ty;^ n] +:: T)
      (p +ₗ #(i * ty.(ty_size))%nat ◁ &shr{κ} ty +:: T)
      (λ post '(al -:: bl), post (al !!! i -:: bl)).
  Proof.
    split; [by intros ??? [??]|].
    iIntros (??[??]?) "_ _ _ _ $ [p T] Obs !>". iExists (_-::_).
    iFrame "Obs T". iDestruct "p" as ([[]|][|]Ev) "[⧖ ?]"=>//=. iExists _, _.
    iSplit; [by rewrite/= Ev|]. iFrame "⧖". by rewrite big_sepL_vlookup vfunsep_lookup.
  Qed.

  Lemma tctx_extract_idx_shr_array {𝔄 𝔅l} (ty: type 𝔄)
      n κ p (i: fin n) (T: tctx 𝔅l) E L :
    tctx_extract_elt E L (p +ₗ #(i * ty.(ty_size))%nat ◁ &shr{κ} ty)
      (p ◁ &shr{κ} [ty;^ n] +:: T) (p ◁ &shr{κ} [ty;^ n] +:: T)
      (λ post '(al -:: bl), post (al !!! i -:: al -:: bl)).
  Proof.
    eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [apply copy_tctx_incl, _|apply tctx_idx_shr_array]. }
    done.
  Qed.

  (* The precondition requires that the index is within bounds *)
  Lemma type_idx_shr_array_instr {𝔄} (ty: type 𝔄) n κ p q E L :
    typed_instr_ty E L +[p ◁ &shr{κ} [ty;^ n]; q ◁ int]
      (p +ₗ q * #ty.(ty_size)) (&shr{κ} ty)
      (λ post '-[al; z], ∃i: fin n, z = i ∧ post (al !!! i)).
  Proof.
    iIntros (??(vπ &?&[])) "_ _ PROPH _ _ $$ (p & q &_) #Obs".
    wp_apply (wp_hasty with "p"). iIntros ([[]|][|]) "_ ⧖ ? //".
    wp_apply (wp_hasty with "q"). iIntros "%% _ _" ((?&->&[=->]))=>/=.
    iMod (proph_obs_sat with "PROPH Obs") as %(?& i &->&_); [done|].
    do 2 wp_op. iExists -[(.!!! i) ∘ vπ]. iSplit; last first.
    { iApply proph_obs_impl; [|done]=>/= ?[?[Eq +]].
      do 2 apply (inj _) in Eq. by rewrite Eq. }
    iSplit; [|done]. iExists _, _. do 2 (iSplit; [done|]).
    by rewrite/= -Nat2Z.inj_mul big_sepL_vlookup vfunsep_lookup.
  Qed.

  Lemma type_idx_shr_array {𝔄 𝔄l 𝔅l ℭ} (ty: type 𝔄) n κ p q
        (T: tctx 𝔄l) (T': tctx 𝔅l) trx tr x e E L (C: cctx ℭ) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} [ty;^ n]; q ◁ int] T T' trx →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p +ₗ q * #ty.(ty_size) in e) (trx ∘
      (λ post '(al -:: z -:: bl), ∃i: fin n, z = i ∧ tr post (al !!! i -:: bl)))%type.
  Proof.
    iIntros (? Extr) "?".
    iApply type_let; [by apply type_idx_shr_array_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?. apply Htrx. by case=> [?[??]].
  Qed.

  (** * Unique References *)

  Fixpoint hasty_uniq_idxs {𝔄} (p: path) (κ: lft) (ty: type 𝔄) (n: nat)
      (i: nat) : tctx (replicate n (𝔄 * 𝔄)%ST) :=
    match n with
    | O => +[]
    | S m =>
      p +ₗ #(i * ty.(ty_size))%nat ◁ &uniq{κ} ty +::
      hasty_uniq_idxs p κ ty m (S i)
    end.

  Lemma tctx_split_uniq_array {𝔄} (ty: type 𝔄) n κ p E L :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} [ty;^ n]] (hasty_uniq_idxs p κ ty n 0)
      (λ post '-[(al, al')], post (vec_to_plist (vzip al al'))).
  Proof.
    move=> ?. move: p. elim: n.
    { move=> ?. eapply tctx_incl_ext;
       [by apply tctx_incl_resolve_head|]=>/= ?[[v v'][]]. inv_vec v. by inv_vec v'. }
    move=>/= n IH p. eapply tctx_incl_ext.
    { eapply tctx_incl_trans.
      { eapply tctx_uniq_eqtype; by [apply array_succ_prod|apply _|]. }
      eapply tctx_incl_trans.
      { by eapply (tctx_incl_frame_r +[_]), tctx_split_uniq_prod. }
      apply tctx_incl_tail. eapply tctx_incl_trans; [apply IH|].
      eapply proj1, get_tctx_equiv=> ? vπl.
      move: p 0%nat. clear. induction n; [done|]=> p ?. case vπl=>/= ??.
      f_equiv; [|done]. rewrite tctx_elt_interp_hasty_path; [done|]=>/=.
      case (eval_path p)=>//. (do 2 case=>//)=> ?.
      by rewrite shift_loc_assoc -Nat2Z.inj_add. }
    move=> ?[[v v'][]]. inv_vec v. by inv_vec v'.
  Qed.

  Lemma tctx_extract_split_uniq_array {𝔄 𝔅 ℭl 𝔇l} (t: tctx_elt 𝔄) κ
      (ty: type 𝔅) n (T: tctx ℭl) (T': tctx 𝔇l) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t (hasty_uniq_idxs p κ ty n 0) T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} [ty;^ n] +:: T) (T' h++ T)
      (λ post '((bl, bl') -:: cl),
        tr (λ '(a -:: dl), post (a -:: dl -++ cl)) (vec_to_plist (vzip bl bl'))).
  Proof.
    move=> ? Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; by [apply tctx_split_uniq_array|]. }
    destruct Extr as [Htr _]=>/= ?[[??]?]. apply Htr. by case.
  Qed.

  Lemma type_idx_uniq_array_instr {𝔄} (ty: type 𝔄) n κ p q E L :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &uniq{κ} [ty;^ n]; q ◁ int]
      (p +ₗ q * #ty.(ty_size)) (&uniq{κ} ty)
      (λ post '-[(al, al'); z], ∃i: fin n, z = i ∧
        ∀a': 𝔄, al' = vinsert i a' al → post (al !!! i, a')).
  Proof.
    iIntros (Alv ??(vπ &?&[])) "#LFT TIME #PROPH UNIQ E $ L (p & q &_) #Obs".
    wp_apply (wp_hasty with "p"). iIntros ([[]|]?) "_ _ [#In uniq] //".
    wp_apply (wp_hasty with "q"). iIntros "%% _ _" ((?&->&[=->]))=>/=.
    iDestruct "uniq" as (? ξi [? Eq2]) "[Vo Bor]". set ξ := PrVar _ ξi.
    iMod (Alv with "E L") as (?) "[(κ & κ₊ & κ₊₊) ToL]"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ") as "[big ToBor]"; [done|]. wp_op.
    iDestruct "big" as (??) "(#⧖ & Pc & ↦tys)". rewrite split_mt_array.
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    set aπl := vfunsep (fst ∘ vπ).
    have ->: vπ = pair ∘ vapply aπl ⊛ (.$ ξ).
    { by rewrite [vπ]surjective_pairing_fun /aπl vapply_funsep Eq2. }
    iMod (proph_obs_sat with "PROPH Obs") as %[?[i[->_]]]; [done|].
    rewrite -Nat2Z.inj_mul.
    iDestruct (big_sepL_vtakemiddrop i with "↦tys") as "(↦tys & ↦ty & ↦tys')".
    iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys κ₊") as "Upd"; [done|].
    setoid_rewrite shift_loc_ty_assoc.
    iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys' κ₊₊") as "Upd'"; [done|].
    iCombine "Upd Upd'" as "Upd". rewrite fupd_sep.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
      [done|done| |].
    { iApply step_fupdN_with_emp. rewrite difference_empty_L.
      iApply step_fupdN_nmono; [|done]. lia. }
    wp_op. iIntros "[(%&%&%& ξl & To↦tys) (%&%&%& ξl' & To↦tys')]".
    iMod (uniq_intro (aπl !!! i) with "PROPH UNIQ") as (ζi) "[Vo' Pc']"; [done|].
    set ζ := PrVar _ ζi.
    iDestruct (uniq_proph_tok with "Vo' Pc'") as "(Vo' & ζ & Pc')".
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζ ξl'") as (?) "[ζξl Toζξl]".
    iDestruct (proph_tok_combine with "ξl ζξl") as (?) "[ξζξl Toξζξl]".
    iMod (uniq_preresolve ξ _ (vapply (vinsert i (.$ ζ) aπl))
      with "PROPH Vo Pc ξζξl") as "(Obs' & ξζξl & ToPc)"; [done| |].
    { apply proph_dep_vinsert=>//. apply proph_dep_one. }
    iCombine "Obs Obs'" as "#?". iClear "Obs".
    iDestruct ("Toξζξl" with "ξζξl") as "[ξl ζξl]".
    iDestruct ("Toζξl" with "ζξl") as "[ζ ξl']". iSpecialize ("Pc'" with "ζ").
    iMod ("To↦tys" with "ξl") as "(↦tys & α₊)".
    iMod ("To↦tys'" with "ξl'") as "(↦tys' & α₊₊)".
    iMod ("ToBor" with "[↦tys ↦tys' ToPc] [↦ty Pc']") as "[Bor α]"; last first.
    - iMod ("ToL" with "[$α $α₊ $α₊₊]") as "$". iModIntro.
      iExists -[λ π, ((aπl !!! i) π, π ζ)]. iSplitL.
      + iSplitL; [|done]. rewrite tctx_hasty_val. iExists _. iFrame "⧖ In".
        iExists _, _. by iFrame.
      + iApply proph_obs_impl; [|done]=>/= ?[[?[/Nat2Z.inj/fin_to_nat_inj<-Imp]]Eqξ].
        rewrite -vapply_lookup. apply Imp. by rewrite Eqξ vapply_insert.
    - iNext. iExists _, _. by iFrame.
    - iIntros "!> big !>!>". iDestruct "big" as (??) "(⧖' & Pc' & ↦ty)".
      iCombine "⧖ ⧖'" as "⧖!"=>/=. iExists _, _. iFrame "⧖!".
      iDestruct ("ToPc" with "[Pc']") as "$".
      { iDestruct (proph_ctrl_eqz with "PROPH Pc'") as "Eqz".
        by iApply proph_eqz_vinsert. }
      iClear "#". rewrite split_mt_array semi_iso' vinsert_backmid -big_sepL_vbackmid.
      iSplitL "↦tys". { iStopProof. do 6 f_equiv. iApply ty_own_depth_mono. lia. }
      iSplitL "↦ty". { iStopProof. do 3 f_equiv. iApply ty_own_depth_mono. lia. }
      iStopProof. do 6 f_equiv; [|iApply ty_own_depth_mono; lia].
      f_equiv. rewrite shift_loc_assoc_nat. f_equal. lia.
  Qed.

  (* The precondition requires that the index is within bounds *)
  Lemma type_idx_uniq_array {𝔄 𝔄l 𝔅l ℭ} (ty: type 𝔄) n κ p q
        (T: tctx 𝔄l) (T': tctx 𝔅l) trx tr x e E L (C: cctx ℭ) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} [ty;^ n]; q ◁ int] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p +ₗ q * #ty.(ty_size) in e) (trx ∘
      (λ post '((al, al') -:: z -:: bl), ∃i: fin n, z = i ∧
        ∀a': 𝔄, al' = vinsert i a' al → tr post ((al !!! i, a') -:: bl)))%type.
  Proof.
    iIntros (? Ex ?) "?".
    iApply type_let; [by apply type_idx_uniq_array_instr|solve_typing| |done].
    move: Ex=> [Htrx _]?. apply Htrx. by case=> [?[??]].
  Qed.
End array_idx.

Global Hint Resolve tctx_extract_split_own_array
  tctx_extract_idx_shr_array tctx_extract_split_uniq_array | 5 : lrust_typing.
Global Hint Resolve tctx_extract_merge_own_array | 40 : lrust_typing_merge.
