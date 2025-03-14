From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing option.
From lrust.typing.lib.rwlock Require Import rwlock rwlockreadguard rwlockwriteguard.
Set Default Proof Using "Type".

Section rwlock_functions.
  Context `{!typeG Σ, !rwlockG Σ}.

  (* Constructing a rwlock. *)
  Definition rwlock_new ty : val :=
    fn: ["x"] :=
      let: "r" := new [ #(S ty.(ty_size))] in
      "r" +ₗ #0 <- #0;;
      "r" +ₗ #1 <-{ty.(ty_size)} !"x";;
       delete [ #ty.(ty_size) ; "x"];; return: ["r"].

  Lemma rwlock_new_type ty :
    typed_val (rwlock_new ty) (fn(∅; ty) → rwlock ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ret ϝ arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new (S ty.(ty_size))); [solve_typing..|].
    iIntros (r tid) "#LFT HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]". destruct x as [[|lx|]|]; try done.
    iDestruct "Hx" as "[Hx Hx†]". iDestruct "Hx" as (vl) "[Hx↦ Hx]".
    destruct r as [[|lr|]|]; try done. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (vl') "Hr". rewrite uninit_own.
    iDestruct "Hr" as "[Hr↦ >SZ]". destruct vl' as [|]; iDestruct "SZ" as %[=].
    rewrite heap_mapsto_vec_cons. iDestruct "Hr↦" as "[Hr↦0 Hr↦1]". wp_op.
    rewrite shift_loc_0. wp_write. wp_op. iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hr↦1 $Hx↦]"); [done||lia..|].
    iIntros "[Hr↦1 Hx↦]". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (ty_size ty)); #lr ◁ box (rwlock ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //=. iFrame.
      iSplitL "Hx↦".
      - iExists _. rewrite uninit_own. auto.
      - iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame. simpl. iFrame. auto. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* The other direction: getting ownership out of a rwlock.
     Note: as we ignore poisonning, this cannot fail. *)
  Definition rwlock_into_inner ty : val :=
    fn: ["x"] :=
      let: "r" := new [ #ty.(ty_size)] in
      "r" <-{ty.(ty_size)} !("x" +ₗ #1);;
       delete [ #(S ty.(ty_size)) ; "x"];; return: ["r"].

  Lemma rwlock_into_inner_type ty :
    typed_val (rwlock_into_inner ty) (fn(∅; rwlock ty) → ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ret ϝ arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new ty.(ty_size)); [solve_typing..|].
    iIntros (r tid) "#LFT HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hr Hx]". destruct x as [[|lx|]|]; try done.
    iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[]|]vl]) "[Hx↦ Hx]"; try iDestruct "Hx" as ">[]".
    destruct r as [[|lr|]|]; try done. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (vl') "Hr". rewrite uninit_own heap_mapsto_vec_cons.
    iDestruct "Hr" as "[Hr↦ >%]". iDestruct "Hx↦" as "[Hx↦0 Hx↦1]". wp_op.
    iDestruct "Hx" as "[% Hx]". iDestruct (ty.(ty_size_eq) with "Hx") as %Hsz.
    wp_apply (wp_memcpy with "[$Hr↦ $Hx↦1]"); [done||lia..|].
    iIntros "[Hr↦ Hx↦1]". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit (S (ty_size ty))); #lr ◁ box ty]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //. iFrame.
      iSplitR "Hr↦ Hx".
      - iExists (_::_). rewrite heap_mapsto_vec_cons uninit_own -Hsz. iFrame. auto.
      - iExists vl. iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition rwlock_get_mut : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      "x" <- "x'" +ₗ #1;;
      return: ["x"].

  Lemma rwlock_get_mut_type ty :
    typed_val rwlock_get_mut (fn(∀ α, ∅; &uniq{α} (rwlock ty)) → &uniq{α} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iIntros (tid) "#LFT HE Hna HL HC HT".
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx [#? Hx']]".
    destruct x' as [[|lx'|]|]; try iDestruct "Hx'" as "[]".
    iAssert (&{α} (∃ (z : Z), lx' ↦ #z ∗ ⌜-1 ≤ z⌝) ∗
        (&uniq{α} ty).(ty_own) tid [ #(lx' +ₗ 1)])%I with "[> Hx']" as "[_ Hx']".
    { iFrame "#". iApply bor_sep; [done..|]. iApply (bor_proper with "Hx'"). iSplit.
      - iIntros "[H1 H2]". iDestruct "H1" as (z) "[??]". iDestruct "H2" as (vl) "[??]".
        iExists (_::_). rewrite heap_mapsto_vec_cons. iFrame. iFrame.
      - iIntros "H". iDestruct "H" as ([|[[| |z]|]vl]) "[H↦ H]"; try done.
        rewrite heap_mapsto_vec_cons.
        iDestruct "H" as "[H1 H2]". iDestruct "H↦" as "[H↦1 H↦2]".
        iSplitL "H1 H↦1"; eauto. iExists _. iFrame. }
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

  (* Acquiring a read lock. *)
  Definition rwlock_try_read : val :=
    fn: ["x"] :=
      let: "r" := new [ #2 ] in
      let: "x'" := !"x" in
    withcont: "k":
    withcont: "loop":
      "loop" []
    cont: "loop" [] :=
      let: "n" := !ˢᶜ"x'" in
        if: "n" ≤ #-1 then
          "r" <-{Σ none} ();;
          "k" []
        else
          if: CAS "x'" "n" ("n" + #1) then
            "r" <-{Σ some} "x'";;
            "k" []
          else "loop" []
    cont: "k" [] :=
      delete [ #1; "x"];; return: ["r"].

  Lemma rwlock_try_read_type ty :
    typed_val rwlock_try_read
        (fn(∀ α, ∅; &shr{α}(rwlock ty)) → option (rwlockreadguard α ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []] (λ _, [x ◁ box (&shr{α}(rwlock ty));
                                            r ◁ box (option (rwlockreadguard α ty))]));
      [iIntros (k)|iIntros "/= !>"; iIntros (k arg); inv_vec arg];
      simpl_subst; last first.
    { iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iApply (type_cont [] [ϝ ⊑ₗ []] (λ _, [x ◁ _; x' ◁ _; r ◁ _]));
      [iIntros (loop)|iIntros "/= !>"; iIntros (loop arg); inv_vec arg];
      simpl_subst.
    { iApply type_jump; solve_typing. }
    iIntros (tid) "#LFT #HE Hna HL Hk HT".
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)". destruct x' as [[|lx|]|]; try done.
    iDestruct "Hx'" as (β γ) "#(Hαβ & Hβty & Hinv)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)";
      [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[[Hβtok1 Hβtok2] Hclose']". done.
    wp_bind (!ˢᶜ(LitV lx))%E.
    iMod (at_bor_acc_tok with "LFT Hinv Hβtok1") as "[INV Hclose'']"; try done.
    iDestruct "INV" as (st) "(Hlx & INV)". wp_read.
    iMod ("Hclose''" with "[Hlx INV]") as "Hβtok1"; first by iExists _; iFrame.
    iModIntro. wp_let. wp_op; case_bool_decide as Hm1; wp_if.
    - iMod ("Hclose'" with "[$]") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
      iApply (type_type _ _ _
              [ x ◁ box (&shr{α}(rwlock ty)); r ◁ box (uninit 2) ]
              with "[] LFT HE Hna HL Hk"); first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      iApply (type_sum_unit (option $ rwlockreadguard α ty));
        [solve_typing..|]; first last.
      simpl. iApply type_jump; solve_typing.
    - wp_op. wp_bind (CAS _ _ _).
      iMod (at_bor_acc_tok with "LFT Hinv Hβtok1") as "[INV Hclose'']"; try done.
      iDestruct "INV" as (st') "(Hlx & Hownst & Hst)". revert Hm1.
      destruct (decide (Z_of_rwlock_st st = Z_of_rwlock_st st')) as [->|?]=>?.
      + iApply (wp_cas_int_suc with "Hlx"). iNext. iIntros "Hlx".
        iAssert (∃ qν ν, (qβ / 2).[β] ∗ (qν).[ν] ∗
                         ty_shr ty (β ⊓ ν) tid (lx +ₗ 1) ∗
                         own γ (◯ reading_st qν ν) ∗ rwlock_inv tid tid lx γ β ty ∗
                         ((1).[ν] ={↑lftN ∪ ↑lft_userN}[↑lft_userN]▷=∗ [†ν]))%I
          with "[> Hlx Hownst Hst Hβtok2]"
          as (q' ν) "(Hβtok2 & Hν & Hshr & Hreading & INV & H†)".
        { destruct st' as [[|[[agν q] n]|]|]; try done.
          - iDestruct "Hst" as (ν q') "(Hag & #H† & Hh & #Hshr & #Hqq' & [Hν1 Hν2])".
            iExists _, _. iFrame "Hν1". iDestruct "Hag" as %Hag. iDestruct "Hqq'" as %Hqq'.
            iMod (own_update with "Hownst") as "[Hownst ?]".
            { apply auth_update_alloc,
              (op_local_update_discrete _ _ (reading_st (q'/2)%Qp ν))=>-[Hagv _].
              split; [split|].
              - by rewrite /= Hag agree_idemp.
              - apply frac_valid'. rewrite /= -Hqq' comm_L.
                by apply Qp_add_le_mono_l, Qp_div_le.
              - done. }
            iFrame "∗#". iExists _. rewrite Z.add_comm /=. iFrame. iExists _, _.
            iFrame "∗#". iSplitR; first by rewrite /= Hag agree_idemp.
            rewrite (comm Qp_add) (assoc Qp_add) Qp_div_2 (comm Qp_add). auto.
          - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]". solve_ndisj.
            iMod (own_update with "Hownst") as "[Hownst Hreading]"; first by apply
              auth_update_alloc, (op_local_update_discrete _ _ (reading_st (1/2)%Qp ν)).
            rewrite right_id. iExists _, _. iFrame "Htok1 Hreading".
            iDestruct (lft_intersect_acc with "Hβtok2 Htok2") as (q) "[Htok Hclose]".
            iApply (fupd_mask_mono (↑lftN)). solve_ndisj.
            iMod (rebor _ _ (β ⊓ ν) with "LFT [] Hst") as "[Hst Hh]". solve_ndisj.
            { iApply lft_intersect_incl_l. }
            iMod (ty_share with "LFT [] Hst Htok") as "[#Hshr Htok]". solve_ndisj.
            { iApply lft_incl_trans; [|done]. iApply lft_intersect_incl_l. }
            iFrame "#". iDestruct ("Hclose" with "Htok") as "[$ Htok2]".
            iExists _. iFrame. iExists _, _. iSplitR; first done. iFrame "#∗".
            rewrite Qp_div_2. iSplitL; last done.
            iIntros "!> Hν". iApply "Hh". rewrite -lft_dead_or. auto. }
        iMod ("Hclose''" with "[$INV]") as "Hβtok1". iModIntro. wp_case.
        iMod ("Hclose'" with "[$]") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
        iApply (type_type  _ _ _
                   [ x ◁ box (&shr{α}(rwlock ty)); r ◁ box (uninit 2);
                     #lx ◁ rwlockreadguard α ty]
              with "[] LFT HE Hna HL Hk"); first last.
        { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                  tctx_hasty_val' //. iFrame.
          iExists _, _, _, _, _. iFrame "∗#". iApply ty_shr_mono; last done.
          iApply lft_intersect_mono; first done. iApply lft_incl_refl. }
        iApply (type_sum_assign (option $ rwlockreadguard α ty)); [solve_typing..|].
        simpl. iApply type_jump; solve_typing.
      + iApply (wp_cas_int_fail with "Hlx"); try done. iNext. iIntros "Hlx".
        iMod ("Hclose''" with "[Hlx Hownst Hst]") as "Hβtok1"; first by iExists _; iFrame.
        iModIntro. wp_case. iMod ("Hclose'" with "[$]") as "Hα".
        iMod ("Hclose" with "Hα HL") as "HL".
        iSpecialize ("Hk" with "[]"); first solve_typing.
        iApply ("Hk" $! [#] with "Hna HL").
        rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame.
        iExists _. iSplit. done. simpl. eauto.
  Qed.

  (* Acquiring a write lock. *)
  Definition rwlock_try_write : val :=
    fn: ["x"] :=
    withcont: "k":
      let: "r" := new [ #2 ] in
      let: "x'" := !"x" in
      if: CAS "x'" #0 #(-1) then
        "r" <-{Σ some} "x'";;
        "k" ["r"]
      else
        "r" <-{Σ none} ();;
        "k" ["r"]
    cont: "k" ["r"] :=
      delete [ #1; "x"];; return: ["r"].

  Lemma rwlock_try_write_type ty :
    typed_val rwlock_try_write
        (fn(∀ α, ∅; &shr{α}(rwlock ty)) → option (rwlockwriteguard α ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_cont [_] [ϝ ⊑ₗ []] (λ r, [x ◁ box (&shr{α}(rwlock ty));
                                        (r!!!0%fin:val) ◁ box (option (rwlockwriteguard α ty))]));
      [iIntros (k)|iIntros "/= !>"; iIntros (k arg); inv_vec arg=>r];
      simpl_subst; last first.
    { iApply type_delete; [solve_typing..|]. iApply type_jump; solve_typing. }
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_deref; [solve_typing..|].
    iIntros (x' tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & Hx' & Hr)". destruct x' as [[|lx|]|]; try done.
    iDestruct "Hx'" as (β γ) "#(Hαβ & Hβty & Hinv)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβtok Hclose']". done.
    wp_bind (CAS _ _ _).
    iMod (at_bor_acc_tok with "LFT Hinv Hβtok") as "[INV Hclose'']"; try done.
    iDestruct "INV" as (st) "(Hlx & >Hownst & Hst)". destruct st.
    - iApply (wp_cas_int_fail with "Hlx"). by destruct c as [|[[]]|].
      iNext. iIntros "Hlx".
      iMod ("Hclose''" with "[Hlx Hownst Hst]") as "Hβtok"; first by iExists _; iFrame.
      iMod ("Hclose'" with "Hβtok") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
      iModIntro. wp_case.
      iApply (type_type _ _ _
              [ x ◁ box (&shr{α}(rwlock ty)); r ◁ box (uninit 2) ]
              with "[] LFT HE Hna HL Hk"); first last.
      { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val. iFrame. }
      iApply (type_sum_unit (option $ rwlockwriteguard α ty));
        [solve_typing..|]; first last.
      rewrite /option /=. iApply type_jump; solve_typing.
    - iApply (wp_cas_int_suc with "Hlx"). iIntros "!> Hlx".
      iMod (own_update with "Hownst") as "[Hownst ?]".
      { by eapply auth_update_alloc, (op_local_update_discrete _ _ writing_st). }
      iMod ("Hclose''" with "[Hlx Hownst]") as "Hβtok". { iExists _. iFrame. }
      iModIntro. wp_case. iMod ("Hclose'" with "Hβtok") as "Hα".
      iMod ("Hclose" with "Hα HL") as "HL".
      iApply (type_type  _ _ _
                   [ x ◁ box (&shr{α}(rwlock ty)); r ◁ box (uninit 2);
                     #lx ◁ rwlockwriteguard α ty]
              with "[] LFT HE Hna HL Hk"); first last.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton !tctx_hasty_val
                tctx_hasty_val' //. iFrame.  iExists _, _, _. iFrame "∗#". }
      iApply (type_sum_assign (option $ rwlockwriteguard α ty)); [solve_typing..|].
      simpl. iApply type_jump; solve_typing.
  Qed.
End rwlock_functions.
