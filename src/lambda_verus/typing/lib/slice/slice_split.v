From lrust.typing Require Export type.
From lrust.typing Require Import uniq_array_util typing.
From lrust.typing.lib Require Import slice.slice.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Open Scope nat.

Section slice_split.
  Context `{!typeG Σ}.

  Definition slice_split_at {𝔄} (ty: type 𝔄) : val :=
    fn: ["s"; "bi"] :=
      let: "l" := !"s" in let: "len" := !("s" +ₗ #1) in delete [ #2; "s"];;
      let: "i" := !"bi" in delete [ #1; "bi"];;
      let: "r" := new [ #4] in
      "r" <- "l";; "r" +ₗ #1 <- "i";;
      "r" +ₗ #2 <- "l" +ₗ "i" * #ty.(ty_size);; "r" +ₗ #3 <- "len" - "i";;
      return: ["r"].

  (* Rust's split_at *)
  Lemma slice_split_at_shr_type {𝔄} (ty: type 𝔄) :
    typed_val (slice_split_at ty)
      (fn<α>(∅; shr_slice α ty, int) → shr_slice α ty * shr_slice α ty)
      (λ post '-[al; z], ∃i: nat, z = i ∧ i < length al ∧ post (take i al, drop i al)).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[s[bi[]]]. simpl_subst.
    iIntros (?(vπ &?&[])?) "_ _ PROPH _ _ Na L C /=(s & bi & _) #Obs".
    rewrite !tctx_hasty_val. iDestruct "s" as ([|d]) "[#⧖ box]"=>//.
    case s as [[|s|]|]=>//=. iDestruct "bi" as ([|]) "[_ boxi]"=>//.
    case bi as [[|bi|]|]=>//=. rewrite split_mt_shr_slice.
    case d as [|]; [iDestruct "box" as "[>[] _]"|]. iDestruct "box" as "[(%&%& big) †s]".
    iMod (bi.later_exist_except_0 with "big") as (aπl) "(>->& >↦s & ↦s' & tys)".
    wp_read. wp_let. wp_op. wp_read. wp_let. rewrite !freeable_sz_full.
    wp_apply (wp_delete [_;_] with "[↦s ↦s' $†s]"); [done|..].
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
    iIntros "_". wp_seq. iDestruct "boxi" as "[(%& ↦bi &%&->&->) †bi]".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    rewrite -heap_mapsto_vec_singleton. wp_apply (wp_delete with "[$↦bi $†bi]"); [done|].
    iIntros "_". wp_seq. wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]". wp_let.
    rewrite !heap_mapsto_vec_cons !shift_loc_assoc.
    iDestruct "↦r" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)".
    wp_write. wp_op. wp_write. do 3 wp_op. wp_write. do 2 wp_op. wp_write. do 2 wp_seq.
    iMod (proph_obs_sat with "PROPH Obs") as %(?& inat &->& Lt &_); [done|].
    rewrite -vec_to_list_apply vec_to_list_length in Lt. set ifin := nat_to_fin Lt.
    have Eqi: inat = ifin by rewrite fin_to_nat_to_fin. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[λ π, (_, _)] with "Na L [-] []").
    - iSplitL; [|done]. rewrite tctx_hasty_val. iExists _. iFrame "⧖".
      rewrite -freeable_sz_full. iFrame "†r". iNext. iExists [_;_;_;_].
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
      rewrite -Nat2Z.inj_mul. rewrite -Nat2Z.inj_sub; [|lia]. iFrame "↦₀ ↦₁ ↦₂ ↦₃".
      iExists [_;_], [_;_]. iSplit; [done|]. rewrite (big_sepL_vtakedrop ifin).
      iDestruct "tys" as "[tys tys']". rewrite Eqi.
      iSplitL "tys"; iExists _,_,_; [by iFrame "tys"|]. iSplit; [done|].
      setoid_rewrite shift_loc_assoc_nat. setoid_rewrite <-Nat.mul_add_distr_r. iFrame.
    - iApply proph_obs_impl; [|done]=>/= π [?[/Nat2Z.inj<-[_ +]]].
      rewrite Eqi. clear. move: ifin=> ifin ?. eapply eq_ind; [done|]. clear.
      induction aπl; inv_fin ifin; [done|]=>/= ifin. by move: (IHaπl ifin)=> [=->->].
  Qed.

  (* Rust's split_at_mut *)
  Lemma slice_split_at_uniq_type {𝔄} (ty: type 𝔄) :
    typed_val (slice_split_at ty)
      (fn<α>(∅; uniq_slice α ty, int) → uniq_slice α ty * uniq_slice α ty)
      (λ post '-[aal; z],
        ∃i: nat, z = i ∧ i < length aal ∧ post (take i aal, drop i aal)).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[s[bi[]]]. simpl_subst.
    iIntros (?(vπ &?&[])?) "_ _ PROPH _ _ Na L C /=(s & bi & _) #Obs".
    rewrite !tctx_hasty_val.
    iDestruct "s" as ([|]) "[#⧖ box]"=>//. case s as [[|s|]|]=>//=.
    iDestruct "bi" as ([|]) "[_ boxi]"=>//=. case bi as [[|bi|]|]=>//.
    rewrite split_mt_uniq_slice. iDestruct "box" as "[(#In &%&%&%& big) †s]".
    iMod (bi.later_exist_except_0 with "big") as (aπξil) "(>[->%] & >↦s & ↦s' & uniqs)".
    wp_read. wp_let. wp_op. wp_read. wp_let. rewrite !freeable_sz_full.
    wp_apply (wp_delete [_;_] with "[↦s ↦s' $†s]"); [done|..].
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
    iIntros "_". wp_seq. iDestruct "boxi" as "[(%& ↦bi &%&->&->) †bi]".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    rewrite -heap_mapsto_vec_singleton. wp_apply (wp_delete with "[$↦bi $†bi]"); [done|].
    iIntros "_". wp_seq. wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]". wp_let.
    rewrite !heap_mapsto_vec_cons !shift_loc_assoc.
    iDestruct "↦r" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)".
    wp_write. wp_op. wp_write. do 3 wp_op. wp_write. do 2 wp_op. wp_write. do 2 wp_seq.
    iMod (proph_obs_sat with "PROPH Obs") as %(?& inat &->& Lt &_); [done|].
    rewrite -vec_to_list_apply vec_to_list_length in Lt. set ifin := nat_to_fin Lt.
    have Eqi: inat = ifin by rewrite fin_to_nat_to_fin. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[λ π, (_, _)] with "Na L [-] []").
    - iSplitL; [|done]. rewrite tctx_hasty_val. iExists _. iFrame "⧖".
      rewrite -freeable_sz_full. iFrame "†r". iNext. iExists [_;_;_;_].
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
      rewrite -Nat2Z.inj_mul. rewrite -Nat2Z.inj_sub; [|lia]. iFrame "↦₀ ↦₁ ↦₂ ↦₃".
      iExists [_;_], [_;_]. iSplit; [done|]. rewrite (big_sepL_vtakedrop ifin).
      iDestruct "uniqs" as "[uniqs uniqs']". rewrite Eqi.
      iSplitL "uniqs"; iFrame "In"; iExists _,_,_,_; [by iFrame "uniqs"|].
      iSplit; [done|]. setoid_rewrite shift_loc_assoc_nat.
      setoid_rewrite <-Nat.mul_add_distr_r. iFrame.
    - iApply proph_obs_impl; [|done]=>/= π [?[/Nat2Z.inj<-[_ +]]].
      rewrite Eqi. clear. move: ifin=> ifin ?. eapply eq_ind; [done|]. clear.
      induction aπξil; inv_fin ifin; [done|]=>/= ifin.
      by move: (IHaπξil ifin)=> [=->->].
  Qed.
End slice_split.
