From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.smallvec Require Import smallvec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section smallvec_index.
  Context `{!typeG Σ}.

  Definition smallvec_index {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"; "i"] :=
      let: "r" := new [ #1] in
      if: !(!"v") then
        "r" <- !"v" +ₗ #4 +ₗ !"i" * #ty.(ty_size);;
        delete [ #1; "v"];; delete [ #1; "i"];;
        return: ["r"]
      else
        "r" <- !(!"v" +ₗ #1) +ₗ !"i" * #ty.(ty_size);;
        delete [ #1; "v"];; delete [ #1; "i"];;
        return: ["r"].

  (* Rust's SmallVec::index *)
  (* The precondition requires that the index is within bounds of the list *)
  Lemma smallvec_index_shr_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_index ty) (fn<α>(∅; &shr{α} (smallvec n ty), int) → &shr{α} ty)
      (λ post '-[al; z], ∃(i: nat) (a: 𝔄), z = i ∧ al !! i = Some a ∧ post a).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[i[]]]. simpl_subst.
    iIntros (?(?&?&[])?) "LFT TIME PROPH _ E Na L C (v & i & _) #Obs".
    rewrite !tctx_hasty_val.
    iDestruct "v" as ([|d]) "[⧖ v]"=>//. case v as [[|v|]|]=>//=.
    iDestruct "i" as ([|]) "[_ i]"=>//. case i as [[|i|]|]=>//=.
    wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]". wp_let.
    iDestruct "v" as "[(%vl & ↦v & svec) †v]". move: d=> [|d]//=.
    case vl as [|[[]|][]]=>//. iDestruct "svec" as (?????->) "[Bor tys]".
    iDestruct "i" as "[(%& ↦i & (%&->&->)) †i]"=>/=.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Bor α") as (?) "[>↦ Toα]"; [done|].
    rewrite !heap_mapsto_vec_singleton !heap_mapsto_vec_cons !heap_mapsto_vec_nil.
    iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)". do 2 wp_read. case b; wp_case.
    - wp_read. wp_op. wp_read. do 2 wp_op. wp_write.
      iMod ("Toα" with "[$↦₀ $↦₁ $↦₂ $↦₃]") as "α". iMod ("ToL" with "α L") as "L".
      do 2 rewrite -heap_mapsto_vec_singleton freeable_sz_full.
      wp_apply (wp_delete with "[$↦v $†v]"); [done|]. iIntros "_". wp_seq.
      wp_apply (wp_delete with "[$↦i $†i]"); [done|]. iIntros "_". do 3 wp_seq.
      iMod (proph_obs_sat with "PROPH Obs") as %(?& inat &?&->& Lkup &_); [done|].
      move: Lkup. rewrite -vec_to_list_apply -vlookup_lookup'. move=> [In _].
      set ifin := nat_to_fin In. have Eqi: inat = ifin by rewrite fin_to_nat_to_fin.
      rewrite cctx_interp_singleton.
      iApply ("C" $! [# #_] -[aπl !!! ifin] with "Na L [-] []").
      + iSplit; [|done]. rewrite tctx_hasty_val. iExists (S (S d)).
        iSplit. { iApply persistent_time_receipt_mono; [|done]. lia. }
        rewrite/= freeable_sz_full. iFrame "†r". iNext. rewrite split_mt_ptr'.
        iExists _. iFrame "↦r". rewrite/= -Nat2Z.inj_mul Eqi.
        iApply (big_sepL_vlookup with "tys").
      + iApply proph_obs_impl; [|done]=>/= ?[?[?[/Nat2Z.inj <-[++]]]].
        by rewrite Eqi -vlookup_lookup -vapply_lookup=> <-.
    - wp_read. wp_op. do 2 wp_read. do 2 wp_op. wp_write.
      iMod ("Toα" with "[$↦₀ $↦₁ $↦₂ $↦₃]") as "α". iMod ("ToL" with "α L") as "L".
      do 2 rewrite -heap_mapsto_vec_singleton freeable_sz_full.
      wp_apply (wp_delete with "[$↦v $†v]"); [done|]. iIntros "_". wp_seq.
      wp_apply (wp_delete with "[$↦i $†i]"); [done|]. iIntros "_". do 3 wp_seq.
      iMod (proph_obs_sat with "PROPH Obs") as %(?& inat &?&->& Lkup &_); [done|].
      move: Lkup. rewrite -vec_to_list_apply -vlookup_lookup'. move=> [In _].
      set ifin := nat_to_fin In. have Eqi: inat = ifin by rewrite fin_to_nat_to_fin.
      rewrite cctx_interp_singleton.
      iApply ("C" $! [# #_] -[aπl !!! ifin] with "Na L [-] []").
      + iSplit; [|done]. rewrite tctx_hasty_val. iExists (S (S d)).
        iSplit. { iApply persistent_time_receipt_mono; [|done]. lia. }
        rewrite/= freeable_sz_full. iFrame "†r". iNext. rewrite split_mt_ptr'.
        iExists _. iFrame "↦r". rewrite/= -Nat2Z.inj_mul Eqi.
        iApply (big_sepL_vlookup with "tys").
      + iApply proph_obs_impl; [|done]=>/= ?[?[?[/Nat2Z.inj <-[++]]]].
        by rewrite Eqi -vlookup_lookup -vapply_lookup=> <-.
  Qed.

  (* Rust's SmallVec::index_mut *)
  (* The precondition requires that the index is within bounds of the list *)
  Lemma smallvec_index_uniq_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_index ty) (fn<α>(∅; &uniq{α} (smallvec n ty), int) → &uniq{α} ty)
      (λ post '-[(al, al'); z], ∃(i: nat) (a: 𝔄), z = i ∧
        al !! i = Some a ∧ ∀a': 𝔄, al' = <[i := a']> al → post (a, a')).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[i[]]]. simpl_subst.
    iIntros (?(vπ &?&[])?) "#LFT #TIME #PROPH UNIQ E Na L C (v & i & _) #Obs".
    rewrite !tctx_hasty_val.
    iDestruct "v" as ([|d]) "[#⧖ v]"=>//. case v as [[|v|]|]=>//=.
    iDestruct "i" as ([|]) "[_ i]"=>//. case i as [[|i|]|]=>//=.
    wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]".
    iDestruct "v" as "[(%vl & ↦v & #In & uniq) †v]". case vl as [|[[]|][]]=>//=.
    iDestruct "i" as "[(%& ↦i & (%&->&->)) †i]". rewrite !heap_mapsto_vec_singleton.
    iDestruct "uniq" as (d' ξi [Le Eq2]) "[Vo Bor]". set ξ := PrVar _ ξi.
    iMod (lctx_lft_alive_tok α with "E L") as
      (?) "((α & α₊ & α₊₊) & L & ToL)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Bor α") as "[(%&%&_& Pc & ↦svec) ToBor]"; [done|].
    wp_let. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_smallvec. iDestruct "↦svec" as (b ??? aπl Eq1) "[↦ big]".
    rewrite !heap_mapsto_vec_cons !shift_loc_assoc.
    iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)".
    have ->: vπ = λ π, (lapply aπl π: list _, π ξ).
    { rewrite [vπ]surjective_pairing_fun. by rewrite Eq1 Eq2. }
    do 2 wp_read. case b; wp_case.
    - iDestruct "big" as "[↦tys ↦tl]". wp_read. wp_op. wp_read. do 2 wp_op. wp_write.
      do 2 rewrite -{1}heap_mapsto_vec_singleton. rewrite !freeable_sz_full.
      wp_apply (wp_delete with "[$↦v $†v]"); [done|]. iIntros "_". wp_seq.
      wp_apply (wp_delete with "[$↦i $†i]"); [done|]. iIntros "_". wp_seq.
      iMod (proph_obs_sat with "PROPH Obs") as %(?& Obs); [done|].
      move: Obs=> [inat[?[->[+ _]]]]. rewrite -vec_to_list_apply -vlookup_lookup'.
      move=> [In _]. rewrite -Nat2Z.inj_mul. set ifin := nat_to_fin In.
      have Eqi: inat = ifin by rewrite fin_to_nat_to_fin.
      set Inh: Inhabited 𝔄 := populate ((aπl !!! ifin) inhabitant).
      iDestruct (big_sepL_vtakemiddrop ifin with "↦tys") as "(↦tys & ↦ty & ↦tys')".
      iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys α₊") as "Upd"; [done|].
      setoid_rewrite shift_loc_ty_assoc.
      iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys' α₊₊") as "Upd'"; [done|].
      iCombine "Upd Upd'" as "Upd". rewrite fupd_sep. wp_bind Skip.
      iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
        [done|done| |].
      { iApply step_fupdN_with_emp. rewrite difference_empty_L.
        iApply step_fupdN_nmono; [|iApply "Upd"]. lia. }
      wp_seq. iIntros "[(%ξl &%&%& ξl & To↦tys) (%ξl' &%&%& ξl' & To↦tys')] !>". wp_seq.
      iMod (uniq_intro (aπl !!! ifin) with "PROPH UNIQ") as (ζi) "[Vo' Pc']"; [done|].
      set ζ := PrVar _ ζi. iDestruct (uniq_proph_tok with "Vo' Pc'") as "(Vo' & ζ & Pc')".
      rewrite proph_tok_singleton.
      iDestruct (proph_tok_combine with "ζ ξl'") as (?) "[ζξl Toζξl]".
      iDestruct (proph_tok_combine with "ξl ζξl") as (?) "[ξζξl Toξζξl]".
      iMod (uniq_preresolve ξ _ (lapply (vinsert ifin (.$ ζ) aπl))
        with "PROPH Vo Pc ξζξl") as "(Obs' & ξζξl & ToPc)"; [done| |].
      { rewrite -vec_to_list_apply.
        apply proph_dep_constr, proph_dep_vinsert=>//. apply proph_dep_one. }
      iCombine "Obs Obs'" as "#?". iClear "Obs".
      iDestruct ("Toξζξl" with "ξζξl") as "[ξl ζξl]".
      iDestruct ("Toζξl" with "ζξl") as "[ζ ξl']". iSpecialize ("Pc'" with "ζ").
      iMod ("To↦tys" with "ξl") as "(↦tys & α₊)".
      iMod ("To↦tys'" with "ξl'") as "(↦tys' & α₊₊)".
      iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦₃ ↦tl ↦tys ↦tys' ToPc] [Pc' ↦ty]")
        as "[Bor α]"; last first.
      + rewrite cctx_interp_singleton.
        iMod ("ToL" with "[$α $α₊ $α₊₊] L") as "L".
        iApply ("C" $! [# #_] -[λ π, ((aπl !!! ifin) π, π ζ)] with "Na L [-] []").
        * iSplitL; [|done]. rewrite tctx_hasty_val. iExists (S _).
          rewrite/= -freeable_sz_full split_mt_uniq_bor. iFrame "⧖ †r In". iNext.
          iExists _, d', _. iFrame "↦r Vo' Bor". iPureIntro. split; [lia|done].
        * iApply proph_obs_impl; [|done]=>/= ?[[?[?[/Nat2Z.inj <-[++]]]]Eqξ].
          rewrite Eqi -vlookup_lookup=> <- Imp. rewrite -vapply_lookup. apply Imp.
          by rewrite Eqξ -vec_to_list_apply vapply_insert -vec_to_list_insert.
      + iNext. iExists _, _. rewrite -Eqi. iFrame "Pc' ↦ty".
        iApply persistent_time_receipt_mono; [|done]. lia.
      + iIntros "!> (%&%& >⧖' & Pc' & ↦ty)". iCombine "⧖ ⧖'" as "⧖!". iIntros "/=!>!>".
        iExists _, _. iFrame "⧖!". iDestruct ("ToPc" with "[Pc']") as "$".
        { iDestruct (proph_ctrl_eqz with "PROPH Pc'") as "Eqz".
          rewrite -vec_to_list_apply. iApply proph_eqz_constr.
          by iApply proph_eqz_vinsert. }
        rewrite split_mt_smallvec. iExists true, _, _, _, _=>/=.
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
        iFrame "↦₀ ↦₁ ↦₂ ↦₃ ↦tl". iSplit; [by rewrite vec_to_list_apply|].
        iClear "#". rewrite vinsert_backmid -big_sepL_vbackmid Eqi. iSplitL "↦tys".
        { iStopProof. do 6 f_equiv. iApply ty_own_depth_mono. lia. }
        setoid_rewrite shift_loc_assoc. iSplitL "↦ty".
        { iStopProof. do 3 f_equiv. iApply ty_own_depth_mono. lia. }
        iStopProof. do 6 f_equiv; [|iApply ty_own_depth_mono; lia]. do 2 f_equiv. lia.
    - iDestruct "big" as "(↦tl & ↦tys & ex†)". wp_read. wp_op. do 2 wp_read.
      do 2 wp_op. wp_write. do 2 rewrite -{1}heap_mapsto_vec_singleton.
      rewrite !freeable_sz_full. wp_apply (wp_delete with "[$↦v $†v]"); [done|].
      iIntros "_". wp_seq. wp_apply (wp_delete with "[$↦i $†i]"); [done|]. iIntros "_".
      wp_seq. iMod (proph_obs_sat with "PROPH Obs") as %(?& Obs); [done|].
      move: Obs=> [inat[?[->[+ _]]]]. rewrite -vec_to_list_apply -vlookup_lookup'.
      move=> [In _]. rewrite -Nat2Z.inj_mul. set ifin := nat_to_fin In.
      have Eqi: inat = ifin by rewrite fin_to_nat_to_fin.
      set Inh: Inhabited 𝔄 := populate ((aπl !!! ifin) inhabitant).
      iDestruct (big_sepL_vtakemiddrop ifin with "↦tys") as "(↦tys & ↦ty & ↦tys')".
      iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys α₊") as "Upd"; [done|].
      setoid_rewrite shift_loc_ty_assoc.
      iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys' α₊₊") as "Upd'"; [done|].
      iCombine "Upd Upd'" as "Upd". rewrite fupd_sep. wp_bind Skip.
      iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
        [done|done| |].
      { iApply step_fupdN_with_emp. rewrite difference_empty_L.
        iApply step_fupdN_nmono; [|iApply "Upd"]. lia. }
      wp_seq. iIntros "[(%ξl &%&%& ξl & To↦tys) (%ξl' &%&%& ξl' & To↦tys')] !>". wp_seq.
      iMod (uniq_intro (aπl !!! ifin) with "PROPH UNIQ") as (ζi) "[Vo' Pc']"; [done|].
      set ζ := PrVar _ ζi. iDestruct (uniq_proph_tok with "Vo' Pc'") as "(Vo' & ζ & Pc')".
      rewrite proph_tok_singleton.
      iDestruct (proph_tok_combine with "ζ ξl'") as (?) "[ζξl Toζξl]".
      iDestruct (proph_tok_combine with "ξl ζξl") as (?) "[ξζξl Toξζξl]".
      iMod (uniq_preresolve ξ _ (lapply (vinsert ifin (.$ ζ) aπl))
        with "PROPH Vo Pc ξζξl") as "(Obs' & ξζξl & ToPc)"; [done| |].
      { rewrite -vec_to_list_apply.
        apply proph_dep_constr, proph_dep_vinsert=>//. apply proph_dep_one. }
      iCombine "Obs Obs'" as "#?". iClear "Obs".
      iDestruct ("Toξζξl" with "ξζξl") as "[ξl ζξl]".
      iDestruct ("Toζξl" with "ζξl") as "[ζ ξl']". iSpecialize ("Pc'" with "ζ").
      iMod ("To↦tys" with "ξl") as "(↦tys & α₊)".
      iMod ("To↦tys'" with "ξl'") as "(↦tys' & α₊₊)".
      iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦₃ ↦tl ex† ↦tys ↦tys' ToPc] [Pc' ↦ty]")
        as "[Bor α]"; last first.
      + rewrite cctx_interp_singleton.
        iMod ("ToL" with "[$α $α₊ $α₊₊] L") as "L".
        iApply ("C" $! [# #_] -[λ π, ((aπl !!! ifin) π, π ζ)] with "Na L [-] []").
        * iSplitL; [|done]. rewrite tctx_hasty_val. iExists _.
          rewrite -freeable_sz_full. iFrame "⧖ †r". iNext. iExists [_].
          rewrite heap_mapsto_vec_singleton. iFrame "↦r In". iExists d', _.
          iFrame "Vo' Bor". iPureIntro. split; [lia|done].
        * iApply proph_obs_impl; [|done]=>/= ?[[?[?[/Nat2Z.inj <-[++]]]]Eqξ].
          rewrite Eqi -vlookup_lookup=> <- Imp. rewrite -vapply_lookup. apply Imp.
          by rewrite Eqξ -vec_to_list_apply vapply_insert -vec_to_list_insert.
      + iNext. iExists _, _. rewrite -Eqi. iFrame "Pc' ↦ty".
        iApply persistent_time_receipt_mono; [|done]. lia.
      + iIntros "!> (%&%& >⧖' & Pc' & ↦ty)". iCombine "⧖ ⧖'" as "⧖!". iIntros "/=!>!>".
        iExists _, _. iFrame "⧖!". iDestruct ("ToPc" with "[Pc']") as "$".
        { iDestruct (proph_ctrl_eqz with "PROPH Pc'") as "Eqz".
          rewrite -vec_to_list_apply. iApply proph_eqz_constr.
          by iApply proph_eqz_vinsert. }
        rewrite split_mt_smallvec. iExists false, _, _, _, _=>/=.
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
        iFrame "↦₀ ↦₁ ↦₂ ↦₃ ↦tl ex†". iSplit; [by rewrite vec_to_list_apply|].
        iClear "#". rewrite vinsert_backmid -big_sepL_vbackmid Eqi. iSplitL "↦tys".
        { iStopProof. do 6 f_equiv. iApply ty_own_depth_mono. lia. }
        setoid_rewrite shift_loc_assoc. iSplitL "↦ty".
        { iStopProof. do 3 f_equiv. iApply ty_own_depth_mono. lia. }
        iStopProof. do 6 f_equiv; [|iApply ty_own_depth_mono; lia]. do 2 f_equiv. lia.
  Qed.
End smallvec_index.
