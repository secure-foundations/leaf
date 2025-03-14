From lrust.typing Require Export type.
From lrust.typing Require Import typing uniq_array_util lib.option.
From lrust.typing.lib.slice Require Import slice.
Set Default Proof Using "Type".

Implicit Type 𝔄: syn_type.

Section iter.
  Context `{!typeG Σ}.

  (** For simplicity, we model the shared and unique iterators
    the same as the shared and unique slices *)

  (* Rust's Iter<'a, T> *)
  Definition iter_shr {𝔄} (κ: lft) (ty: type 𝔄) : type (listₛ 𝔄) :=
    shr_slice κ ty.

  (* Rust's IterMut<'a, T> *)
  Definition iter_uniq {𝔄} (κ: lft) (ty: type 𝔄) : type (listₛ (𝔄 * 𝔄)) :=
    uniq_slice κ ty.

  Definition iter_next {𝔄} (ty: type 𝔄) : val :=
    fn: ["b"] :=
      let: "it" := !"b" in delete [ #1; "b"];;
      let: "len" := !("it" +ₗ #1) in
      if: "len" ≤ #0 then
        let: "r" := new [ #2] in "r" <-{Σ 0} ();; return: ["r"]
      else
        let: "l" := !"it" in
        "it" <- "l" +ₗ #ty.(ty_size);; "it" +ₗ #1 <- "len" - #1;;
        let: "r" := new [ #2] in "r" <-{Σ 1} "l";; return: ["r"].

  (* Rust's Iter::next *)
  Lemma iter_shr_next_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_shr α ty)) → option_ty (&shr{α} ty))
      (λ post '-[(al, al')], al' = tail al → post (hd_error al)).
  Proof.
    eapply type_fn; [apply _|]. move=>/= [α β]??[b[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[b _] #Obs".
    rewrite tctx_hasty_val. iDestruct "b" as ([|]) "[#⧖' box]"=>//.
    case b as [[|b|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In' & %it &%& %ξi &>[% %Eq2]& >↦b & Vo & Bor) †b]".
    set ξ := PrVar _ ξi. wp_read.
    iMod (lctx_lft_alive_tok β with "E L") as (?) "(β & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor β") as "[big ToBor]"; [done|]. wp_let.
    iDestruct "big" as (? d') "(#⧖ & Pc & ↦it)". rewrite split_mt_shr_slice.
    case d' as [|]=>//=. iDestruct "↦it" as (? len aπl->) "(↦ & ↦' & tys)".
    rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦b $†b]"); [done|]. iIntros "_". wp_seq.
    iDestruct (uniq_agree with "Vo Pc") as %[Eq1 ->]. wp_op. wp_read. wp_let.
    wp_op. wp_case. case len as [|]=>/=.
    { iMod ("ToBor" with "[Pc ↦ ↦' tys]") as "[Bor β]".
      { iNext. iExists _, _. rewrite split_mt_shr_slice. iFrame "⧖ Pc".
        iExists _, _, _. by iFrame. }
      iMod ("ToL" with "β L") as "L".
      iApply (type_type +[#it ◁ &uniq{β} (iter_shr α ty)] -[vπ]
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst.
        iApply (type_sum_unit +[(); &shr{_} _]%T 0%fin);
          [done|solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= !(tctx_hasty_val #_). iSplitL; [|done]. iExists _.
        iFrame "⧖' In'". iExists _, _. iFrame. iPureIntro. split; [lia|done].
      - iApply proph_obs_eq; [|done]=> π. move: (equal_f Eq1 π)=>/=.
        case (vπ π)=>/= ??->. by inv_vec aπl. }
    inv_vec aπl. move=> aπ aπl' Eq1 /=.
    wp_read. wp_let. wp_op. wp_write. do 2 wp_op. wp_write.
    have ->: S len - 1 = len by lia.
    have ->: vπ = λ π, (aπ π :: lapply aπl' π, π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    iDestruct "tys" as "[ty tys]". rewrite shift_loc_0.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[Pc ↦ ↦' tys]") as "[Bor β]".
    { iNext. iExists _, _. rewrite split_mt_shr_slice. iFrame "⧖ Pc".
      iExists _, _, _. iFrame "↦ ↦'". iSplit; [done|].
      setoid_rewrite <-shift_loc_assoc_nat. by iFrame. }
    iMod ("ToL" with "β L") as "L".
    iApply (type_type +[#it ◁ &uniq{β} (iter_shr α ty); #l ◁ &shr{α} ty]
      -[λ π, (lapply aπl' π, π ξ); aπ]
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_new; [done|]. intro_subst.
      iApply (type_sum_assign +[(); &shr{_} _]%T 1%fin);
        [done|solve_extract|solve_typing..|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_). iSplitL "Vo Bor"; [|iSplitL; [|done]].
      + iExists _. iFrame "⧖ In'". iExists _, _. rewrite /uniq_body.
        rewrite (proof_irrel (@prval_to_inh (listₛ _) (lapply aπl'))
          (@prval_to_inh (listₛ _) (fst ∘ vπ))).
        by iFrame.
      + iExists _. iFrame "⧖". iApply ty_shr_depth_mono; [|done]. lia.
    - done.
  Qed.

  (* Rust's IterMut::next *)
  Lemma iter_uniq_next_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_uniq α ty)) → option_ty (&uniq{α} ty))
      (λ post '-[(aal, aal')], aal' = tail aal → post (hd_error aal)).
  Proof.
    eapply type_fn; [apply _|]. move=>/= [α β]??[b[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[b _] #Obs".
    rewrite tctx_hasty_val. iDestruct "b" as ([|]) "[#⧖' box]"=>//.
    case b as [[|b|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In' & %it &%& %ξi &>[% %Eq2]& >↦b & Vo & Bor) †b]".
    set ξ := PrVar _ ξi. wp_read.
    iMod (lctx_lft_alive_tok β with "E L") as (?) "(β & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor β") as "[big ToBor]"; [done|]. wp_let.
    iDestruct "big" as (??) "(#⧖ & Pc & ↦it)". rewrite split_mt_uniq_slice.
    iDestruct "↦it" as "(#In & %l & %len &%& big)".
    rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦b $†b]"); [done|]. iIntros "_". wp_seq.
    iDestruct "big" as (aπζil [->?]) "(↦ & ↦' & uniqs)".
    set aaπl := vmap _ _. iDestruct (uniq_agree with "Vo Pc") as %[Eq1 <-].
    wp_op. wp_read. wp_let. wp_op. wp_case. case len as [|].
    { iMod ("ToBor" with "[Pc ↦ ↦' uniqs]") as "[Bor β]".
      { iNext. iExists _, _. rewrite split_mt_uniq_slice. iFrame "⧖ Pc In".
        iExists _, _, _, _. by iFrame. }
      iMod ("ToL" with "β L") as "L".
      iApply (type_type +[#it ◁ &uniq{β} (iter_uniq α ty)] -[vπ]
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst.
        iApply (type_sum_unit +[(); &uniq{_} _]%T 0%fin);
          [done|solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= !(tctx_hasty_val #_). iSplitL; [|done]. iExists _.
        iFrame "⧖' In'". iExists _, _. iFrame. iPureIntro. split; [lia|done].
      - iApply proph_obs_eq; [|done]=> π. move: (equal_f Eq1 π)=>/=.
        case (vπ π)=>/= ??->. move: (aaπl)=> aaπl'. by inv_vec aaπl'. }
    inv_vec aπζil. move=> [aπ ζi] aπζil' aaπl Eq1 /=.
    wp_read. wp_let. wp_op. wp_write. do 2 wp_op. wp_write.
    have ->: S len - 1 = len by lia.
    have ->: vπ = λ π, (lapply aaπl π, π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    iDestruct "uniqs" as "[uniq uniqs]". rewrite shift_loc_0.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[Pc ↦ ↦' uniqs]") as "[Bor β]".
    { iNext. iExists _, _. rewrite split_mt_uniq_slice. iFrame "⧖ Pc In".
      iExists _, _, _, aπζil'. setoid_rewrite <-shift_loc_assoc_nat. by iFrame. }
    iMod ("ToL" with "β L") as "L".
    set aaπl' := vmap _ aπζil'. rewrite /uniq_body. set ζ := PrVar _ ζi.
    iApply (type_type +[#it ◁ &uniq{β} (iter_uniq α ty); #l ◁ &uniq{α} ty]
      -[λ π, (lapply aaπl' π, π ξ); λ π, (aπ π, π ζ)]
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_new; [done|]. intro_subst.
      iApply (type_sum_assign +[(); &uniq{_} _]%T 1%fin);
        [done|solve_extract|solve_typing..|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_). iSplitL "Vo Bor"; [|iSplitL; [|done]].
      + iExists _. iFrame "⧖ In'". iExists _, _. rewrite /uniq_body.
        rewrite (proof_irrel (@prval_to_inh (listₛ (_*_)) (lapply aaπl'))
          (@prval_to_inh (listₛ (_*_)) (fst ∘ vπ))).
        by iFrame.
      + iExists _. iFrame "⧖ In". iExists _, _. iFrame. iPureIntro. split; [lia|done].
    - done.
  Qed.

  Definition iter_next_back {𝔄} (ty: type 𝔄) : val :=
    fn: ["b"] :=
      let: "it" := !"b" in delete [ #1; "b"];;
      let: "len" := !("it" +ₗ #1) in
      if: "len" ≤ #0 then
        let: "r" := new [ #2] in "r" <-{Σ 0} ();; return: ["r"]
      else
        let: "len'" := "len" - #1 in "it" +ₗ #1 <- "len'";;
        let: "l'" := !"it" +ₗ "len'" * #ty.(ty_size) in
        let: "r" := new [ #2] in "r" <-{Σ 1} "l'";; return: ["r"].

  (* Rust's Iter::next_back *)
  Lemma iter_shr_next_back_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next_back ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_shr α ty)) → option_ty (&shr{α} ty))
      (λ post '-[(al, al')], al' = removelast al → post (last_error al)).
  Proof.
    eapply type_fn; [apply _|]. move=>/= [α β]??[b[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[b _] #Obs".
    rewrite tctx_hasty_val. iDestruct "b" as ([|]) "[#⧖' box]"=>//.
    case b as [[|b|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In' & %it &%& %ξi &>[% %Eq2]& >↦b & Vo & Bor) †b]".
    set ξ := PrVar _ ξi. wp_read.
    iMod (lctx_lft_alive_tok β with "E L") as (?) "(β & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor β") as "[big ToBor]"; [done|]. wp_let.
    iDestruct "big" as (? d') "(#⧖ & Pc & ↦it)". rewrite split_mt_shr_slice.
    case d' as [|]=>//=. iDestruct "↦it" as (? len aπl->) "(↦ & ↦' & tys)".
    rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦b $†b]"); [done|]. iIntros "_". wp_seq.
    iDestruct (uniq_agree with "Vo Pc") as %[Eq1 ->]. wp_op. wp_read. wp_let.
    wp_op. wp_case. case len as [|]=>/=.
    { iMod ("ToBor" with "[Pc ↦ ↦' tys]") as "[Bor β]".
      { iNext. iExists _, _. rewrite split_mt_shr_slice. iFrame "⧖ Pc".
        iExists _, _, _. by iFrame. }
      iMod ("ToL" with "β L") as "L".
      iApply (type_type +[#it ◁ &uniq{β} (iter_shr α ty)] -[vπ]
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst.
        iApply (type_sum_unit +[(); &shr{_} _]%T 0%fin);
          [done|solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= !(tctx_hasty_val #_). iSplitL; [|done]. iExists _.
        iFrame "⧖' In'". iExists _, _. iFrame. iPureIntro. split; [lia|done].
      - iApply proph_obs_eq; [|done]=> π. move: (equal_f Eq1 π)=>/=.
        case (vπ π)=>/= ??->. by inv_vec aπl. }
    iDestruct (big_sepL_vinitlast with "tys") as "[tys ty]".
    set aπl' := vinit _. set aπ := vlast _.
    wp_op. wp_let. wp_op. wp_write. wp_read. do 2 wp_op. wp_let.
    have ->: S len - 1 = len by lia. rewrite -Nat2Z.inj_mul.
    have ->: vπ = λ π, (lapply aπl π, π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[Pc ↦ ↦' tys]") as "[Bor β]".
    { iNext. iExists _, _. rewrite split_mt_shr_slice. iFrame "⧖ Pc".
      iExists _, _, _. by iFrame. }
    iMod ("ToL" with "β L") as "L".
    iApply (type_type +[#it ◁ &uniq{β} (iter_shr α ty); #(l +ₗ[ty] len) ◁ &shr{α} ty]
      -[λ π, (lapply aπl' π, π ξ); aπ]
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_new; [done|]. intro_subst.
      iApply (type_sum_assign +[(); &shr{_} _]%T 1%fin);
        [done|solve_extract|solve_typing..|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_). iSplitL "Vo Bor"; [|iSplitL; [|done]].
      + iExists _. iFrame "⧖ In'". iExists _, _. rewrite /uniq_body.
        rewrite (proof_irrel (@prval_to_inh (listₛ _) (lapply aπl'))
          (@prval_to_inh (listₛ _) (fst ∘ vπ))).
        by iFrame.
      + iExists _. iFrame "⧖". iApply ty_shr_depth_mono; [|done]. lia.
    - iApply proph_obs_impl; [|done]=>/= π. clear.
      have ->: last_error (lapply aπl π) = Some (aπ π).
      { inv_vec aπl=>/= + aπl'. by elim aπl'; [done|]=>/= *. }
      have ->: removelast (lapply aπl π) = lapply aπl' π.
      { inv_vec aπl=>/= + aπl'. elim aπl'; [done|]=>/= *. by f_equal. }
      done.
  Qed.

  (* Rust's IterMut::next_back *)
  Lemma iter_uniq_next_back_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next_back ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_uniq α ty)) → option_ty (&uniq{α} ty))
      (λ post '-[(aal, aal')], aal' = removelast aal → post (last_error aal)).
  Proof.
    eapply type_fn; [apply _|]. move=>/= [α β]??[b[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[b _] #Obs".
    rewrite tctx_hasty_val. iDestruct "b" as ([|]) "[#⧖' box]"=>//.
    case b as [[|b|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In' & %it &%& %ξi &>[% %Eq2]& >↦b & Vo & Bor) †b]".
    set ξ := PrVar _ ξi. wp_read.
    iMod (lctx_lft_alive_tok β with "E L") as (?) "(β & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor β") as "[big ToBor]"; [done|]. wp_let.
    iDestruct "big" as (??) "(#⧖ & Pc & ↦it)". rewrite split_mt_uniq_slice.
    iDestruct "↦it" as "(#In & %l & %len &%& big)".
    rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦b $†b]"); [done|]. iIntros "_". wp_seq.
    iDestruct "big" as (aπζil [->?]) "(↦ & ↦' & uniqs)".
    set aaπl := vmap _ _. iDestruct (uniq_agree with "Vo Pc") as %[Eq1 <-].
    wp_op. wp_read. wp_let. wp_op. wp_case. case len as [|]=>/=.
    { iMod ("ToBor" with "[Pc ↦ ↦' uniqs]") as "[Bor β]".
      { iNext. iExists _, _. rewrite split_mt_uniq_slice. iFrame "⧖ Pc In".
        iExists _, _, _, _. by iFrame. }
      iMod ("ToL" with "β L") as "L".
      iApply (type_type +[#it ◁ &uniq{β} (iter_uniq α ty)] -[vπ]
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst.
        iApply (type_sum_unit +[(); &uniq{_} _]%T 0%fin);
          [done|solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= !(tctx_hasty_val #_). iSplitL; [|done]. iExists _.
        iFrame "⧖' In'". iExists _, _. iFrame. iPureIntro. split; [lia|done].
      - iApply proph_obs_impl; [|done]=> π. move: (equal_f Eq1 π)=>/=.
        case (vπ π)=>/= ??->. move: (aaπl)=> aaπl'. inv_vec aaπl'=>/= [Imp ?].
        by apply Imp. }
    iDestruct (big_sepL_vinitlast with "uniqs") as "[uniqs uniq]".
    set aπζil' := vinit _. set aπζi := vlast _.
    wp_op. wp_let. wp_op. wp_write. wp_read. do 2 wp_op. wp_let.
    have ->: S len - 1 = len by lia. rewrite -Nat2Z.inj_mul.
    have ->: vπ = λ π, (lapply aaπl π, π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[Pc ↦ ↦' uniqs]") as "[Bor β]".
    { iNext. iExists _, _. rewrite split_mt_uniq_slice. iFrame "⧖ Pc In".
      iExists _, _, _, aπζil'. by iFrame. }
    iMod ("ToL" with "β L") as "L".
    set aaπl' := vmap _ aπζil'. rewrite /uniq_body. set ζ := PrVar _ aπζi.2.
    iApply (type_type +[#it ◁ &uniq{β} (iter_uniq α ty); #(l +ₗ[ty] len) ◁ &uniq{α} ty]
      -[λ π, (lapply aaπl' π, π ξ); λ π, (aπζi.1 π, π ζ)]
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_new; [done|]. intro_subst.
      iApply (type_sum_assign +[(); &uniq{_} _]%T 1%fin);
        [done|solve_extract|solve_typing..|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_). iSplitL "Vo Bor"; [|iSplitL; [|done]].
      + iExists _. iFrame "⧖ In'". iExists _, _. rewrite /uniq_body.
        rewrite (proof_irrel (@prval_to_inh (listₛ (_*_)) (lapply aaπl'))
          (@prval_to_inh (listₛ (_*_)) (fst ∘ vπ))).
        by iFrame.
      + iExists _. iFrame "⧖ In". iExists _, _. iFrame. iPureIntro. split; [lia|done].
    - iApply proph_obs_impl; [|done]=>/= π. clear.
      have ->: last_error (lapply aaπl π) = Some (aπζi.1 π, π ζ).
      { inv_vec aπζil=>/= + aπζil'. by elim aπζil'; [done|]=>/= *. }
      have ->: removelast (lapply aaπl π) = lapply aaπl' π.
      { inv_vec aπζil=>/= + aπζil'. elim aπζil'; [done|]=>/= *. by f_equal. }
      done.
  Qed.
End iter.
