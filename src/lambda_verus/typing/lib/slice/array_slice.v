From lrust.typing Require Export type.
From lrust.typing Require Import uniq_array_util typing.
From lrust.typing.lib Require Import slice.slice.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section array_slice.
  Context `{!typeG Σ}.

  Definition array_as_slice (n: nat) : val :=
    fn: ["ba"] :=
      let: "a" := !"ba" in delete [ #1; "ba"];;
      let: "r" := new [ #2] in
      "r" <- "a";; "r" +ₗ #1 <- #n;;
      return: ["r"].

  (* Rust's [T; n]::as_slice *)
  Lemma array_as_shr_slice_type {𝔄} n (ty: type 𝔄) :
    typed_val (array_as_slice n) (fn<α>(∅; &shr{α} [ty;^ n]) → shr_slice α ty)
      (λ post '-[al], post al).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[ba[]]. simpl_subst.
    iIntros (?(vπ &[])?) "#LFT #TIME #PROPH UNIQ E Na L C /=[ba _] #Obs".
    rewrite tctx_hasty_val. iDestruct "ba" as ([|d]) "[#⧖ box]"=>//.
    case ba as [[|ba|]|]=>//=. rewrite split_mt_ptr.
    case d as [|]; [by iDestruct "box" as "[>[] _]"|]=>/=.
    iDestruct "box" as "[(%& ↦ & tys) †]". wp_read. wp_let.
    rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦ $†]"); [done|]. iIntros "_". wp_seq.
    wp_apply wp_new; [done..|]. iIntros (?) "[† ↦]". wp_let.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "↦" as "[↦ ↦']". wp_write. wp_op. wp_write. do 2 wp_seq.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[_] with "Na L [-] Obs"). iSplit; [|done].
    rewrite tctx_hasty_val. iExists (S _). rewrite/= split_mt_shr_slice.
    rewrite freeable_sz_full. iFrame "⧖ †". iNext. iExists _, _, _. iFrame.
    iPureIntro. by rewrite -vec_to_list_apply vapply_funsep.
  Qed.

  (* Rust's [T; n]::as_mut_slice *)
  Lemma array_as_uniq_slice_type {𝔄} n (ty: type 𝔄) :
    typed_val (array_as_slice n) (fn<α>(∅; &uniq{α} [ty;^ n]) → uniq_slice α ty)
      (λ post '-[(al, al')], length al' = length al → post (zip al al')).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[ba[]]. simpl_subst.
    iIntros (?(vπ &[])?) "#LFT #TIME #PROPH UNIQ E Na L C /=[ba _] Obs".
    rewrite tctx_hasty_val. iDestruct "ba" as ([|]) "[#⧖ box]"=>//.
    case ba as [[|ba|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In &%&%& %ξi &>[% %Eq2]& ↦ba & Vo & Bor) †ba]".
    wp_read. wp_let. rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦ba $†ba]"); [done|]. iIntros "_".
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Bor α") as "[big ToBor]"; [done|]. wp_seq.
    iDestruct "big" as (vπ' ?) "(_ & Pc & ↦tys)". rewrite split_mt_array.
    wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]". wp_let.
    set ξ := PrVar _ ξi.
    have ->: vπ' = vapply (vfunsep vπ') by rewrite semi_iso'.
    move: (vfunsep vπ')=> aπl. rewrite semi_iso'.
    iDestruct (uniq_agree with "Vo Pc") as %[Eq1 <-].
    have ->: vπ = λ π, (vapply aπl π, π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    rewrite !heap_mapsto_vec_cons. iDestruct "↦r" as "(↦r & ↦r' &_)".
    wp_write. wp_op. wp_write. do 2 wp_seq.
    iMod (uniq_intro_vec aπl with "PROPH UNIQ") as (ζil) "VoPcs"; [done|].
    iDestruct (uniq_proph_tok_vec with "VoPcs") as "[ζl VoPcs]".
    set aπζil := vzip _ _. set ζl := map _ aπζil.
    set aπl' := vmap (λ aπζi (π: proph_asn),
      π (PrVar (𝔄 ↾ prval_to_inh aπζi.1) aπζi.2): 𝔄) aπζil.
    set aaπl := vmap (λ aπζi π,
      (aπζi.1 π, π (PrVar (𝔄 ↾ prval_to_inh aπζi.1) aπζi.2): 𝔄)) aπζil.
    iMod (uniq_preresolve ξ ζl (vapply aπl') with "PROPH Vo Pc ζl")
      as "(Obs' & ζl & ToPc)"; [done|by apply proph_dep_prvars|].
    iCombine "Obs' Obs" as "#?". iSpecialize ("VoPcs" with "ζl").
    iDestruct (big_sepL_sep with "VoPcs") as "[Vos Pcs]".
    iMod ("ToBor" $! (big_sepL _ _) with "[ToPc] [↦tys Pcs]") as "[Bor α]"; last first.
    - iMod ("ToL" with "α L") as "L". rewrite cctx_interp_singleton.
      iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
      iApply ("C" $! [# #_] -[lapply aaπl] with "Na L [-]").
      + rewrite/= right_id (tctx_hasty_val #_) -freeable_sz_full. iExists _.
        iFrame "⧖ †r". iNext. rewrite split_mt_uniq_slice. iFrame "In".
        iExists _, _, _, _. rewrite big_sepL_sep. by iFrame.
      + iApply proph_obs_impl; [|done]=>/= π [-> Imp].
        have ->: lapply aaπl π = zip (vapply aπl π) (vapply aπl' π).
        { clear. induction aπl; inv_vec ζil=>//= *. by f_equal. }
        apply Imp. clear. induction aπl; inv_vec ζil=>//= *. by f_equal.
    - iNext. iApply (merge_big_sepL_proph_ctrl_mt_ty_own with "[] Pcs ↦tys").
      iApply persistent_time_receipt_mono; [|done]. lia.
    - iIntros "!> big".
      iDestruct (split_big_sepL_proph_ctrl_mt_ty_own with "PROPH ⧖ big") as "big".
      iMod (bi.later_exist_except_0 with "big") as (wπl ?) "(>⧖' & Eqzs & ↦tys)".
      iIntros "!>!>". iExists (vapply wπl), _. iFrame "⧖'". iSplitL "Eqzs ToPc".
      { iApply "ToPc". iApply (proph_eqz_prvars with "Eqzs"). }
      rewrite split_mt_array semi_iso'. iFrame.
  Qed.
End array_slice.
