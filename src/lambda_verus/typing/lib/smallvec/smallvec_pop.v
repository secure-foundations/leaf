From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib Require Import option vec_util smallvec.smallvec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section smallvec_pop.
  Context `{!typeG Σ}.

  Definition smallvec_pop {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      let: "len" := !("v'" +ₗ #2) in
      let: "r" := new [ #(option_ty ty).(ty_size)] in
      if: "len" ≤ #0 then
        "r" <- #0;; return: ["r"]
      else
        let: "len'" := "len" - #1 in
        "v'" +ₗ #2 <- "len'";; "r" <- #1;;
        if: !"v'" then (* array mode *)
          "r" +ₗ #1 <-{ty.(ty_size)} !("v'" +ₗ #4 +ₗ "len'" * #ty.(ty_size));;
          return: ["r"]
        else (* vector mode *)
          "v'" +ₗ #3 <- !("v'" +ₗ #3) + #1;;
          "r" +ₗ #1 <-{ty.(ty_size)} !(!("v'" +ₗ #1) +ₗ "len'" * #ty.(ty_size));;
          return: ["r"].

  (* Rust's SmallVec::pop *)
  Lemma smallvec_pop_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_pop ty) (fn<α>(∅; &uniq{α} (smallvec n ty)) → option_ty ty)
      (λ post '-[(al, al')], al' = removelast al → post (last_error al)).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[]]. simpl_subst.
    iIntros (?[pπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[v _] #Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦ & [#LftIn uniq]) †]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    wp_apply (wp_delete with "[$↦ $†]"); [done|]. iIntros "_".
    iDestruct "uniq" as (d ξi [? Eq2]) "[Vo Bor]". move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& #⧖ & Pc & big) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-]. rewrite split_mt_smallvec.
    iDestruct "big" as (?? len ex aπl Eq1) "(↦ & big)".
    rewrite !heap_mapsto_vec_cons !shift_loc_assoc.
    iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)". wp_op. wp_read. wp_let.
    wp_apply wp_new; [lia|done|]. iIntros (r) "[†r ↦r]".
    rewrite Nat2Z.id/= heap_mapsto_vec_cons. iDestruct "↦r" as "[↦r ↦r']".
    wp_let. wp_op. wp_if. case len as [|len]=>/=.
    { wp_write. iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦₃ big Pc]") as "[Bor β]".
      { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_smallvec.
        iExists _, _, _, _, _.
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
        by iFrame "↦₀ ↦₁ ↦₂ ↦₃ big". }
      iMod ("ToL" with "β L") as "L".
      iApply (type_type +[#v' ◁ &uniq{α} (smallvec n ty); #r ◁ box (option_ty ty)]
        -[pπ; const None] with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= !(tctx_hasty_val #_). iSplitR "↦r ↦r' †r".
        { iExists _. iFrame "⧖ LftIn". iExists _, _. iFrame. iPureIntro.
          split; [lia|done]. }
        iSplitL; [|done]. iExists _. rewrite -freeable_sz_full. iFrame "⧖ †r".
        iNext. rewrite /option_ty. setoid_rewrite mod_ty_own; [|apply _].
        rewrite split_mt_sum. iExists 0%fin, (const ()). iSplit; [done|]. iFrame "↦r".
        iSplitL. { iExists _. iFrame. iPureIntro. by rewrite/= repeat_length. }
        iFrame. iExists []. rewrite heap_mapsto_vec_nil=>/=.
        iSplit; [done|]. by iExists (const -[]).
      - iApply proph_obs_impl; [|done]=> π. move: (equal_f Eq1 π)=>/=. clear.
        inv_vec aπl. by case (pπ π)=>/= ??->. }
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    wp_op. wp_let. have ->: (S len - 1)%Z = len by lia. wp_op. do 2 wp_write.
    wp_read. wp_if. set pπ' := λ π, (lapply (vinit aπl) π, π ξ). case b=>/=.
    - iDestruct "big" as "[↦tys (%&% & ↦tl)]".
      iDestruct (big_sepL_vinitlast with "↦tys") as "[↦tys (%& ↦last & ty)]"=>/=.
      iDestruct (ty_size_eq with "ty") as %Lvl. do 4 wp_op. rewrite -Nat2Z.inj_mul.
      wp_apply (wp_memcpy with "[$↦r' $↦last]"); [rewrite repeat_length; lia|lia|].
      iIntros "[↦r' ↦last]". wp_seq.
      iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦₃ ↦tys ↦last ↦tl ⧖ Pc]") as "[Bor α]".
      { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_smallvec.
        iExists _, _, _, _, _.
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
        iFrame "↦₀ ↦₁ ↦₂ ↦₃ ↦tys". iSplit; [done|]. iExists (_++_).
        rewrite heap_mapsto_vec_app shift_loc_assoc -Z.add_assoc -Nat2Z.inj_add
          -Lvl Nat.add_comm.
        iFrame "↦last ↦tl". iPureIntro. rewrite app_length. lia. }
      iMod ("ToL" with "α L") as "L".
      iApply (type_type +[#v' ◁ &uniq{α} (smallvec n ty); #r ◁ box (option_ty ty)]
        -[pπ'; Some ∘ _] with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      + iApply type_jump; [solve_typing|solve_extract|solve_typing].
      + rewrite/= !(tctx_hasty_val #_) right_id. iSplitL "Vo Bor".
        * iExists _. iFrame "⧖ LftIn". iExists _, _. rewrite /uniq_body.
          rewrite (proof_irrel (@prval_to_inh (listₛ 𝔄) (fst ∘ pπ'))
            (@prval_to_inh (listₛ 𝔄) (fst ∘ pπ))). by iFrame.
        * iExists _. rewrite -freeable_sz_full. iFrame "⧖ †r". iNext.
          rewrite /option_ty. setoid_rewrite mod_ty_own; [|apply _].
          rewrite split_mt_sum. iExists 1%fin, _. iSplit; [done|]. iFrame "↦r". iSplitR.
          { iExists []. rewrite heap_mapsto_vec_nil left_id. iPureIntro=>/=.
            move: ty.(ty_size)=> ?. lia. }
          iExists _. iFrame "↦r'". iApply ty_own_depth_mono; [|done]. lia.
      + iApply proph_obs_impl; [|done]=>/= π.
        move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. clear. case (pπ π)=>/= ??->->.
        have ->: last_error (lapply aπl π) = Some (vlast aπl π).
        { inv_vec aπl=> + aπl'. by elim aπl'=>/= *. }
        have ->: removelast (lapply aπl π) = lapply (vinit aπl) π.
        { inv_vec aπl=> + aπl'. elim aπl'; [done|]=>/= *. by f_equal. } done.
    - iDestruct "big" as "(↦tl & ↦tys & (%&% & ↦ex) & †)".
      iDestruct (big_sepL_vinitlast with "↦tys") as "[↦tys (%& ↦last & ty)]"=>/=.
      iDestruct (ty_size_eq with "ty") as %Lvl. do 2 wp_op. wp_read. wp_op.
      wp_write. have ->: (ex + 1)%Z = S ex by lia. do 2 wp_op. wp_read.
      do 2 wp_op. rewrite -Nat2Z.inj_mul.
      wp_apply (wp_memcpy with "[$↦r' $↦last]"); [rewrite repeat_length; lia|lia|].
      iIntros "[↦r' ↦last]". wp_seq.
      iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦₃ ↦tys ↦tl ↦last ↦ex † ⧖ Pc]") as "[Bor α]".
      { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_smallvec.
        iExists _, _, _, _, _.
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
        iFrame "↦₀ ↦₁ ↦₂ ↦₃ ↦tl ↦tys". have ->: len + S ex = S (len + ex) by lia.
        iFrame "†". iSplit; [done|]. iExists (_++_). rewrite heap_mapsto_vec_app.
        iFrame "↦last". rewrite shift_loc_assoc_nat app_length Nat.add_comm Lvl.
        iFrame. iPureIntro=>/=. lia. }
      iMod ("ToL" with "α L") as "L".
      iApply (type_type +[#v' ◁ &uniq{α} (smallvec n ty); #r ◁ box (option_ty ty)]
        -[pπ'; Some ∘ _] with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      + iApply type_jump; [solve_typing|solve_extract|solve_typing].
      + rewrite/= !(tctx_hasty_val #_) right_id. iSplitL "Vo Bor".
        * iExists _. iFrame "⧖ LftIn". iExists _, _. rewrite /uniq_body.
          rewrite (proof_irrel (@prval_to_inh (listₛ 𝔄) (fst ∘ pπ'))
            (@prval_to_inh (listₛ 𝔄) (fst ∘ pπ))). by iFrame.
        * iExists _. rewrite -freeable_sz_full. iFrame "⧖ †r". iNext.
          rewrite /option_ty. setoid_rewrite mod_ty_own; [|apply _].
          rewrite split_mt_sum. iExists 1%fin, _. iSplit; [done|]. iFrame "↦r". iSplitR.
          { iExists []. rewrite heap_mapsto_vec_nil left_id. iPureIntro=>/=.
            move: ty.(ty_size)=> ?. lia. }
          iExists _. iFrame "↦r'". iApply ty_own_depth_mono; [|done]. lia.
      + iApply proph_obs_impl; [|done]=>/= π.
        move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. clear. case (pπ π)=>/= ??->->.
        have ->: last_error (lapply aπl π) = Some (vlast aπl π).
        { inv_vec aπl=> + aπl'. by elim aπl'=>/= *. }
        have ->: removelast (lapply aπl π) = lapply (vinit aπl) π.
        { inv_vec aπl=> + aπl'. elim aπl'; [done|]=>/= *. by f_equal. } done.
  Qed.
End smallvec_pop.
