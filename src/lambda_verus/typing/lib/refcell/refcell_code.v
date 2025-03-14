From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing option.
From lrust.typing.lib.refcell Require Import refcell ref refmut.
Set Default Proof Using "Type".

Section refcell_functions.
  Context `{!typeG Σ, !refcellG Σ}.

  (* Constructing a refcell. *)
  Definition refcell_new ty : val :=
    fn: ["x"] :=
      let: "r" := new [ #(S ty.(ty_size))] in
      "r" +ₗ #0 <- #0;;
      "r" +ₗ #1 <-{ty.(ty_size)} !"x";;
      delete [ #ty.(ty_size) ; "x"];; return: ["r"].

  Lemma refcell_new_type ty :
    typed_val (refcell_new ty) (fn(∅; ty) → refcell ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new (S ty.(ty_size))); [solve_typing..|].
    iIntros (r tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]".
    iDestruct (ownptr_own with "Hx") as (lx vlx) "(% & Hx↦ & Hx & Hx†)". subst x.
    iDestruct (ownptr_uninit_own with "Hr") as (lr vlr) "(% & Hr↦ & Hr†)". subst r.
    inv_vec vlr=>??. iDestruct (heap_mapsto_vec_cons with "Hr↦") as "[Hr↦0 Hr↦1]". wp_op.
    rewrite shift_loc_0. wp_write. wp_op. iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hr↦1 $Hx↦]"); [by auto using vec_to_list_length..|].
    iIntros "[Hr↦1 Hx↦]". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (ty_size ty)); #lr ◁ box (refcell ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=.
      iFrame. iSplitL "Hx↦".
      - iExists _. rewrite uninit_own. auto.
      - simpl. iFrame. iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame=>//=. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* The other direction: getting ownership out of a refcell. *)
  Definition refcell_into_inner ty : val :=
    fn: ["x"] :=
      let: "r" := new [ #ty.(ty_size)] in
      "r" <-{ty.(ty_size)} !("x" +ₗ #1);;
          (* TODO: Can we make it so that the parenthesis above are mandatory?
             Leaving them away is inconsistent with `let ... := !"x" +ₗ #1`. *)
       delete [ #(S ty.(ty_size)) ; "x"];; return: ["r"].

  Lemma refcell_into_inner_type ty :
    typed_val (refcell_into_inner ty) (fn(∅; refcell ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new ty.(ty_size)); [solve_typing..|].
    iIntros (r tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]".
    iDestruct (ownptr_own with "Hx") as (lx vlx) "(% & >Hx↦ & Hx & Hx†)". subst x.
    inv_vec vlx=>-[[|?|?]|????] vl; simpl; try iDestruct "Hx" as ">[]".
    iDestruct (heap_mapsto_vec_cons with "Hx↦") as "[Hx↦0 Hx↦1]".
    iDestruct (ownptr_uninit_own with "Hr") as (lr vlr) "(% & Hr↦ & Hr†)". subst r.
    wp_op. wp_apply (wp_memcpy with "[$Hr↦ $Hx↦1]"); [by auto using vec_to_list_length..|].
    iIntros "[Hr↦ Hx↦1]". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (S (ty_size ty))); #lr ◁ box ty]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //. iFrame.
      iSplitR "Hr↦ Hx".
      - iExists (_::_). rewrite heap_mapsto_vec_cons uninit_own. iFrame.
        rewrite /= vec_to_list_length. auto.
      - iExists vl. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition refcell_get_mut : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      "x" <- "x'" +ₗ #1;;       (* Get the second field *)
      return: ["x"].

  Lemma refcell_get_mut_type ty :
    typed_val refcell_get_mut
              (fn(∀ α, ∅; &uniq{α} (refcell ty)) → &uniq{α} ty)%T.
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL HC HT".
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx [#? Hx']]".
    destruct x' as [[|lx'|]|];  try iDestruct "Hx'" as "[]".
    iAssert (&{α} (∃ (z : Z), lx' ↦ #z) ∗
        (&uniq{α} ty).(ty_own) tid [ #(lx' +ₗ 1)])%I with "[> Hx']" as "[_ Hx']".
    { simpl. iFrame "#". iApply bor_sep; [done..|]. iApply (bor_proper with "Hx'"). iSplit.
      - iIntros "[H1 H2]". iDestruct "H1" as (z) "?". iDestruct "H2" as (vl) "[??]".
        iExists (_::_). rewrite heap_mapsto_vec_cons /=. iFrame=>//=.
      - iIntros "H".
        iDestruct "H" as ([|[[| |z]|]vl]) "[H↦ H]";
          simpl; try iDestruct "H" as "[]".
        rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[H↦1 H↦2]".
        iSplitL "H↦1"; eauto. iExists _. iFrame. }
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as (vl) "[Hx↦ Hx]". rewrite uninit_own. wp_op.
    iApply (type_type _ _ _
            [ #lx ◁ box (uninit 1); #(lx' +ₗ 1) ◁ &uniq{α}ty]
            with "[] LFT HE Hna HL HC [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //. iFrame.
      iNext. iExists _. rewrite uninit_own. iFrame. }
    iApply type_assign; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Shared borrowing. *)
  Definition refcell_try_borrow : val :=
    fn: ["x"] :=
      let: "r" := new [ #3 ] in
    withcont: "k":
      let: "x'" := !"x" in
      let: "n" := !"x'" in
      if: "n" ≤ #-1 then
        "r" <-{Σ none} ();;
        "k" []
      else
        "x'" <- "n" + #1;;
        let: "ref" := new [ #2 ] in
        "ref" <- "x'" +ₗ #1;;
        "ref" +ₗ #1 <- "x'";;
        "r" <-{2,Σ some} !"ref";;
        delete [ #2; "ref"];;
        "k" []
    cont: "k" [] :=
      delete [ #1; "x"];; return: ["r"].

  Lemma refcell_try_borrow_type ty :
    typed_val refcell_try_borrow
      (fn(∀ α, ∅; &shr{α}(refcell ty)) → option (ref α ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []] (λ _, [x ◁ box (&shr{α}(refcell ty));
                                         r ◁ box (option (ref α ty))]));
      [iIntros (k)|iIntros "/= !>"; iIntros (k arg); inv_vec arg]; simpl_subst; last first.
    { iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iApply type_deref; [solve_typing..|].
    iIntros (x' tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)". destruct x' as [[|lx|]|]=>//=.
    iDestruct "Hx'" as (β γ) "#(Hαβ & Hβty & Hinv)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[[Hβtok1 Hβtok2] Hclose']". done.
    iMod (na_bor_acc with "LFT Hinv Hβtok1 Hna") as "(INV & Hna & Hclose'')"; try done.
    iDestruct "INV" as (st) "(Hlx & Hownst & Hst)". wp_read. wp_let. wp_op; case_bool_decide; wp_if.
    - iMod ("Hclose''" with "[Hlx Hownst Hst] Hna") as "[Hβtok1 Hna]";
        first by iExists st; iFrame.
      iMod ("Hclose'" with "[$Hβtok1 $Hβtok2]") as "Hα".
      iMod ("Hclose" with "Hα HL") as "HL".
      iApply (type_type _ _ _
              [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3) ]
              with "[] LFT HE Hna HL Hk"); first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      iApply (type_sum_unit (option $ ref α ty)); [solve_typing..|]; first last.
      simpl. iApply type_jump; solve_typing.
    - wp_op. wp_write. wp_apply wp_new; [done..|].
      iIntros (lref) "(H† & Hlref)". wp_let.
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iDestruct "Hlref" as "[Hlref0 Hlref1]". wp_op. wp_write. wp_op. wp_write.
      iAssert (∃ qν ν, (qβ / 2).[β] ∗ (qν).[ν] ∗
                       ty_shr ty (β ⊓ ν) tid (lx +ₗ 1) ∗
                       own γ (◯ reading_stR qν ν) ∗ refcell_inv tid lx γ β ty)%I
        with "[> Hlx Hownst Hst Hβtok2]" as (q' ν) "(Hβtok2 & Hν & Hshr & Hreading & INV)".
      { destruct st as [[[[ν []] s] n]|].
        - simpl in *; lia.
        - iDestruct "Hst" as "(H† & Hst & #Hshr)".
          iDestruct "Hst" as (q' Hqq') "[Hν1 Hν2]".
          iExists _, _. iFrame "Hν1". iMod (own_update with "Hownst") as "[Hownst ?]".
          { apply auth_update_alloc,
              (op_local_update_discrete _ _ (reading_stR (q'/2)%Qp ν)) => ?.
            split; [split|].
            - by rewrite /= agree_idemp.
            - apply frac_valid'. rewrite /= -Hqq' comm_L.
              by apply Qp_add_le_mono_l, Qp_div_le.
            - done. }
          iFrame "∗#". iExists (Some (ν, false, _, _)). iFrame "∗#".
          rewrite [_ ⋅ _]comm -Some_op -!pair_op agree_idemp. iFrame.
          iExists _. iFrame. rewrite -(assoc Qp_add) Qp_div_2 //.
        - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]". done.
          iMod (own_update with "Hownst") as "[Hownst Hreading]"; first by apply
            auth_update_alloc, (op_local_update_discrete _ _ (reading_stR (1/2)%Qp ν)).
          rewrite (right_id None). iExists _, _. iFrame "Htok1 Hreading".
          iDestruct (lft_intersect_acc with "Hβtok2 Htok2") as (q) "[Htok Hclose]".
          iApply (fupd_mask_mono (↑lftN)); first done.
          iMod (rebor _ _ (β ⊓ ν) with "LFT [] Hst") as "[Hst Hh]". done.
          { iApply lft_intersect_incl_l. }
          iMod (ty_share with "LFT [] Hst Htok") as "[#Hshr Htok]". done.
          { iApply lft_incl_trans; [|done]. iApply lft_intersect_incl_l. }
          iFrame "Hshr".
          iDestruct ("Hclose" with "Htok") as "[$ Htok2]". iExists _. iFrame "∗#".
          iSplitR "Htok2".
          + iIntros "!> Hν". iMod ("Hhν" with "Hν") as "Hν". iModIntro.
            iNext. iMod "Hν".
            iMod fupd_intro_mask' as "Hclose"; last iMod ("Hh" with "[Hν]") as "$".
            { set_solver-. }
            * rewrite -lft_dead_or. auto.
            * done.
          + iExists _. iFrame. by rewrite Qp_div_2. }
      iMod ("Hclose''" with "[$INV] Hna") as "[Hβtok1 Hna]".
      iMod ("Hclose'" with "[$Hβtok1 $Hβtok2]") as "Hα".
      iMod ("Hclose" with "Hα HL") as "HL".
      iApply (type_type  _ _ _
        [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3); #lref ◁ box (ref α ty)]
              with "[] LFT HE Hna HL Hk"); first last.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame.
        rewrite tctx_hasty_val' //. rewrite /= freeable_sz_full. iFrame.
        iExists [_; _]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
        iFrame. simpl. iExists _, _, _, _, _. iFrame "∗#". iApply ty_shr_mono; try by auto.
        iApply lft_intersect_mono. done. iApply lft_incl_refl. }
      iApply (type_sum_memcpy (option $ ref α ty)); [solve_typing..|].
      simpl. iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  (* Unique borrowing. *)
  Definition refcell_try_borrow_mut : val :=
    fn: ["x"] :=
      let: "r" := new [ #3 ] in
    withcont: "k":
      let: "x'" := !"x" in
      let: "n" := !"x'" in
      if: "n" = #0 then
        "x'" <- #(-1);;
        let: "ref" := new [ #2 ] in
        "ref" <- "x'" +ₗ #1;;
        "ref" +ₗ #1 <- "x'";;
        "r" <-{2,Σ some} !"ref";;
        delete [ #2; "ref"];;
        "k" []
      else
        "r" <-{Σ none} ();;
        "k" []
    cont: "k" [] :=
      delete [ #1; "x"];; return: ["r"].

  Lemma refcell_try_borrow_mut_type ty :
    typed_val refcell_try_borrow_mut
              (fn(∀ α, ∅; &shr{α}(refcell ty)) → option (refmut α ty))%T.
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []] (λ _, [x ◁ box (&shr{α}(refcell ty));
                                            r ◁ box (option (refmut α ty))]));
      [iIntros (k)|iIntros "/= !>"; iIntros (k arg); inv_vec arg];
      simpl_subst; last first.
    { iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iApply type_deref; [solve_typing..|].
    iIntros (x' tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)". destruct x' as [[|lx|]|]=>//=.
    iDestruct "Hx'" as (β γ) "#(Hαβ & Hβty & Hinv)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβtok Hclose']". done.
    iMod (na_bor_acc with "LFT Hinv Hβtok Hna") as "(INV & Hna & Hclose'')"; try done.
    iDestruct "INV" as (st) "(Hlx & Hownst & Hb)". wp_read. wp_let. wp_op; case_bool_decide; wp_if.
    - wp_write. wp_apply wp_new; [done..|].
      iIntros (lref) "(H† & Hlref)". wp_let.
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iDestruct "Hlref" as "[Hlref0 Hlref1]". wp_op. wp_write. wp_op. wp_write.
      destruct st as [[[[ν []] s] n]|]; try done.
      iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]". done.
      iMod (own_update with "Hownst") as "[Hownst ?]".
      { by eapply auth_update_alloc,
          (op_local_update_discrete _ _ (refcell_st_to_R $ Some (ν, true, (1/2)%Qp, xH))). }
      rewrite (right_id None). iApply fupd_wp. iApply (fupd_mask_mono (↑lftN)); first done.
      iMod (rebor _ _ (β ⊓ ν) with "LFT [] Hb") as "[Hb Hbh]". done.
      { iApply lft_intersect_incl_l. }
      iModIntro. iMod ("Hclose''" with "[Hlx Hownst Hbh Htok1] Hna") as "[Hβtok Hna]".
      { iExists _. iFrame. iNext. iSplitL "Hbh".
        - iIntros "Hν". iMod ("Hhν" with "Hν") as "Hν". iModIntro. iNext. iMod "Hν".
          iMod fupd_intro_mask' as "Hclose"; last iMod ("Hbh" with "[Hν]") as "$".
          { set_solver-. }
          * rewrite -lft_dead_or. auto.
          * done.
        - iSplitL; [|done]. iExists _. iFrame. by rewrite Qp_div_2. }
      iMod ("Hclose'" with "Hβtok") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
      iApply (type_type _ _ _
        [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3); #lref ◁ box (refmut α ty)]
              with "[] LFT HE Hna HL Hk"); first last.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame.
        rewrite tctx_hasty_val' //. rewrite /= freeable_sz_full. iFrame.
        iExists [_; _]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
        iFrame. simpl.
        iExists _, _, _, _, _. iFrame "#∗". iSplitL.
        - iApply (bor_shorten with "[] [$Hb]").
          iApply lft_intersect_mono; first done. iApply lft_incl_refl.
        - iApply lft_incl_trans; [|done]. iApply lft_incl_trans; [|done].
          iApply lft_intersect_incl_l. }
      iApply (type_sum_memcpy (option $ refmut α ty)); [solve_typing..|].
      simpl. iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
    - iMod ("Hclose''" with "[Hlx Hownst Hb] Hna") as "[Hβtok Hna]";
        first by iExists st; iFrame.
      iMod ("Hclose'" with "Hβtok") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
      iApply (type_type _ _ _
              [ x ◁ box (&shr{α}(refcell ty)); r ◁ box (uninit 3) ]
              with "[] LFT HE Hna HL Hk"); first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      iApply (type_sum_unit (option $ refmut α ty)); [solve_typing..|].
      simpl. iApply type_jump; solve_typing.
  Qed.
End refcell_functions.
