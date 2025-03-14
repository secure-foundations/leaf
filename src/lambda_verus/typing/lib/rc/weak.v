From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree numbers.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option.
From lrust.typing.lib Require Export rc.
Set Default Proof Using "Type".

Section weak.
  Context `{!typeG Σ, !rcG Σ}.

  Program Definition weak (ty : type) :=
    {| ty_size := 1; ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] => ∃ γ ν, rc_persist tid ν γ l ty ∗ own γ weak_tok
         | _ => False end;
       ty_shr κ tid l :=
         ∃ (l' : loc), &frac{κ} (λ q, l ↦{q} #l') ∗
           □ ∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ]
             ={F}[F∖↑shrN]▷=∗ q.[κ] ∗ ∃ γ ν, rc_persist tid ν γ l' ty ∗
                &na{κ, tid, rc_shrN}(own γ weak_tok)
    |}%I.
  Next Obligation. by iIntros (ty tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT #? Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    (* Ideally, we'd change ty_shr to say "l ↦{q} #l" in the fractured borrow,
       but that would be additional work here... *)
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]|][|]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    setoid_rewrite heap_mapsto_vec_singleton.
    iFrame "Htok". iExists _. iFrame "#". rewrite bor_unfold_idx.
    iDestruct "Hb" as (i) "(#Hpb&Hpbown)".
    set (C := (∃ _ _, _ ∗ &na{_,_,_} _)%I).
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ C)%I with "[Hpbown]") as "#Hinv";
      first by iLeft.
    iIntros "!> !> * % Htok".
    iMod (inv_acc with "Hinv") as "[INV Hclose1]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iAssert (&{κ} _)%I with "[Hbtok]" as "Hb".
      { rewrite bor_unfold_idx. iExists _. by iFrame. }
      iClear "H↦ Hinv Hpb".
      iMod (bor_acc_cons with "LFT Hb Htok") as "[HP Hclose2]"; first solve_ndisj.
      iDestruct "HP" as (γ ν) "(#Hpersist & Hweak)".
      iModIntro. iNext. iMod ("Hclose2" with "[] Hweak") as "[Hb $]"; first by auto 10.
      iAssert C with "[>Hb]" as "#HC".
      { iExists _, _. iFrame "Hpersist". iApply (bor_na with "Hb"). solve_ndisj. }
      iMod ("Hclose1" with "[]") as "_"; by auto.
    - iMod ("Hclose1" with "[]") as "_"; first by auto.
      iApply step_fupd_intro; first solve_ndisj. auto.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' tid l) "#Hincl H". iDestruct "H" as (l') "[#Hl #Hshr]".
    iExists _. iSplit; first by iApply frac_bor_shorten.
    iModIntro. iIntros (F q) "% Htok".
    iMod (lft_incl_acc with "Hincl Htok") as (q'') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hshr" with "[] Htok") as "Hshr2"; first done.
    iModIntro. iNext. iMod "Hshr2" as "[Htok HX]".
    iMod ("Hclose" with "Htok") as "$". iDestruct "HX" as (? ν) "(? & ?)".
    iExists _, _. iFrame. by iApply na_bor_shorten.
  Qed.

  Global Instance weak_type_contractive : TypeContractive weak.
    split.
    - apply (type_lft_morphism_add _ static [] [])=>?.
      + rewrite left_id. iApply lft_equiv_refl.
      + by rewrite /elctx_interp /= left_id right_id.
    - done.
    - intros n ty1 ty2 Hsz Hl HE Ho Hs tid vl. destruct vl as [|[[|l|]|] [|]]=>//=.
      rewrite /rc_persist /type_incl Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ α l, ty1.(ty_shr) (α ⊓ ty_lft ty1) tid l ≡{n}≡
                     ty2.(ty_shr) (α ⊓ ty_lft ty2) tid l) as Hs'.
      { intros. rewrite Hs. apply equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      simpl. repeat (apply Ho || apply dist_S, Hs || apply Hs' ||
                     apply equiv_dist, lft_incl_equiv_proper_l, Hl ||
                     f_contractive || f_equiv).
    - intros n ty1 ty2 Hsz Hl HE Ho Hs κ tid l. rewrite /= /weak /rc_persist /type_incl Hsz.
      assert (∀ α, ⊢ α ⊓ ty_lft ty1 ≡ₗ α ⊓ ty_lft ty2) as Hl'.
      { intros α. iApply lft_intersect_equiv_proper; [|done]. iApply lft_equiv_refl. }
      assert (∀ l α, dist_later n (ty1.(ty_shr) (α ⊓ ty_lft ty1) tid (l +ₗ 2))
                              (ty2.(ty_shr) (α ⊓ ty_lft ty2) tid (l +ₗ 2))) as Hs'.
      { intros. rewrite Hs. apply dist_dist_later, equiv_dist.
        by iSplit; iApply ty_shr_mono; iDestruct Hl' as "[??]". }
      simpl. repeat (apply Ho || apply dist_S, Hs || apply Hs' ||
                     apply equiv_dist, lft_incl_equiv_proper_l, Hl ||
                     f_contractive || f_equiv).
  Qed.

  Global Instance weak_ne : NonExpansive weak.
    unfold weak, rc_persist, type_incl.
    intros n x y Hxy. constructor; [done|by apply Hxy..| |].
    - intros. rewrite ![X in X {| ty_own := _ |}]/ty_own /=.
      solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
    - solve_proper_core ltac:(fun _ => eapply ty_size_ne || eapply ty_lfts_ne || f_equiv).
  Qed.

  Lemma weak_subtype ty1 ty2 :
    type_incl ty1 ty2 -∗ type_incl (weak ty1) (weak ty2).
  Proof.
    iIntros "#Hincl". iPoseProof "Hincl" as "(Hsz & #Hl & #Hoincl & #Hsincl)".
    iSplit; [done|]. iSplit; [done|]. iSplit; iModIntro.
    - iIntros "* Hvl". destruct vl as [|[[|vl|]|] [|]]; try done.
      iDestruct "Hvl" as (γ ν) "(#Hpersist & Htok)".
      iExists _, _. iFrame "Htok". by iApply rc_persist_type_incl.
    - iIntros "* #Hshr". iDestruct "Hshr" as (l') "[Hfrac Hshr]". iExists l'.
      iIntros "{$Hfrac} !> * % Htok". iMod ("Hshr" with "[% //] Htok") as "{Hshr} H".
      iModIntro. iNext. iMod "H" as "[$ H]". iDestruct "H" as (γ ν) "(Hpersist & Hshr)".
      iExists _, _. iFrame "Hshr". by iApply rc_persist_type_incl.
  Qed.

  Global Instance weak_mono E L :
    Proper (subtype E L ==> subtype E L) weak.
  Proof.
    iIntros (ty1 ty2 Hsub ?) "HL". iDestruct (Hsub with "HL") as "#Hsub".
    iIntros "!> #HE". iApply weak_subtype. iApply "Hsub"; done.
  Qed.
  Global Instance weak_proper E L :
    Proper (eqtype E L ==> eqtype E L) weak.
  Proof. intros ??[]. by split; apply weak_mono. Qed.
End weak.

Section code.
  Context `{!typeG Σ, !rcG Σ}.

  Definition rc_upgrade : val :=
    fn: ["w"] :=
      let: "r" := new [ #2 ] in
    withcont: "k":
      let: "w'" := !"w" in
      let: "w''" := !"w'" in
      let: "strong" := !("w''" +ₗ #0) in
      if: "strong" = #0 then
        "r" <-{Σ none} ();;
        "k" []
      else
        "w''" +ₗ #0 <- "strong" + #1;;
        "r" <-{Σ some} "w''";;
        "k" []
    cont: "k" [] :=
      delete [ #1; "w" ];; return: ["r"].

  Lemma rc_upgrade_type ty :
    typed_val rc_upgrade (fn(∀ α, ∅; &shr{α}(weak ty)) → option (rc ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>w. simpl_subst.
    iApply (type_new 2); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []]
                      (λ _, [w ◁ box (&shr{α}(weak ty)); r ◁ box (option (rc ty))])) ;
      [solve_typing..| |]; last first.
    { simpl. iModIntro. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (w'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hw [Hw' [Hr _]]]".
    rewrite !tctx_hasty_val [[w]]lock.
    destruct w' as [[|lw|]|]; try done. iDestruct "Hw'" as (l') "[#Hlw #Hshr]".
    iDestruct (ownptr_uninit_own with "Hr") as (lr vlr) "(% & Hr & Hr†)".
    subst r. inv_vec vlr=>r0 r1. rewrite !heap_mapsto_vec_cons.
    iDestruct "Hr" as "(Hr1 & Hr2 & _)".
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlw Hα2") as (q') "[Hlw↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlw↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν) "#(Hpersist & Hwtokb)".
    iModIntro. wp_let. wp_op. rewrite shift_loc_0.
    (* Finally, finally... opening the thread-local Rc protocol. *)
    iPoseProof "Hpersist" as (ty') "(_ & Hinv & _ & _)".
    iMod (na_inv_acc with "Hinv Hna") as "(Hrcproto & Hna & Hclose2)"; [solve_ndisj..|].
    iMod (na_bor_acc with "LFT Hwtokb Hα1 Hna") as "(>Hwtok & Hna & Hclose3)"; [solve_ndisj..|].
    iDestruct "Hrcproto" as ([st weakc]) "[>Hrc● Hrcst]".
    iDestruct (own_valid_2 with "Hrc● Hwtok") as
      %[[_ Hweak%nat_included]%prod_included [Hval _]]%auth_both_valid_discrete.
    destruct st as [[[q'' strong]| |]|]; try done.
    - (* Success case. *)
      iDestruct "Hrcst" as (qb) "(Hl'1 & Hl'2 & Hl'† & >Hq''q0 & [Hν1 Hν2] & Hν†)".
      iDestruct "Hq''q0" as %Hq''q0.
      wp_read. wp_let. wp_op. wp_if. wp_op. rewrite shift_loc_0. wp_op. wp_write.
      (* Closing the invariant. *)
      iMod (own_update with "Hrc●") as "[Hrc● Hrctok2]".
      { apply auth_update_alloc, prod_local_update_1,
        (op_local_update_discrete _ _ (Some (Cinl ((qb/2)%Qp, 1%positive))))=>-[/= Hqa _].
        split; simpl; last done. apply frac_valid'.
        rewrite /= -Hq''q0 comm_L. by apply Qp_add_le_mono_l, Qp_div_le. }
      rewrite right_id -Some_op -Cinl_op -pair_op.
      iMod ("Hclose3" with "[$Hwtok] Hna") as "[Hα1 Hna]".
      iMod ("Hclose2" with "[Hrc● Hl'1 Hl'2 Hl'† Hν2 Hν† $Hna]") as "Hna".
      { iExists _. iFrame "Hrc●". iExists _. rewrite Z.add_comm. iFrame.
        rewrite [_ ⋅ _]comm frac_op' -[(_ + _)%Qp]assoc Qp_div_2. auto. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      (* Finish up the proof. *)
      iApply (type_type _ _ _ [ w ◁ box (&shr{α}(weak ty)); #lr ◁ box (uninit 2);
                                #l' ◁ rc ty ]
          with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite 2!tctx_interp_cons tctx_interp_singleton tctx_hasty_val !tctx_hasty_val' //.
        unlock. iFrame "Hr† Hw". iSplitL "Hr1 Hr2".
        - iExists [_;_].
          rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. auto with iFrame.
        - iRight. auto with iFrame. }
      iApply (type_sum_assign (option (rc ty))); [solve_typing..|].
      iApply type_jump; solve_typing.
    - (* Failure : dropping *)
      (* TODO : The two failure cases are almost identical. *)
      iDestruct "Hrcst" as "[Hl'1 Hl'2]". wp_read. wp_let. wp_op. wp_if.
      (* Closing the invariant. *)
      iMod ("Hclose3" with "[$Hwtok] Hna") as "[Hα1 Hna]".
      iMod ("Hclose2" with "[Hrc● Hl'1 Hl'2 $Hna]") as "Hna".
      { iExists _. auto with iFrame. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      (* Finish up the proof. *)
      iApply (type_type _ _ _ [ w ◁ box (&shr{α}(weak ty)); #lr ◁ box (uninit 2) ]
          with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
        unlock. iFrame. iExists [_;_].
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. auto with iFrame. }
      iApply (type_sum_unit (option (rc ty))); [solve_typing..|].
      iApply type_jump; solve_typing.
    - (* Failure : general case *)
      destruct weakc as [|weakc]; first by simpl in *; lia.
      iDestruct "Hrcst" as "[Hl'1 Hrcst]". wp_read. wp_let. wp_op. wp_if.
      (* Closing the invariant. *)
      iMod ("Hclose3" with "[$Hwtok] Hna") as "[Hα1 Hna]".
      iMod ("Hclose2" with "[Hrc● Hl'1 Hrcst $Hna]") as "Hna".
      { iExists _. auto with iFrame. }
      iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
      (* Finish up the proof. *)
      iApply (type_type _ _ _ [ w ◁ box (&shr{α}(weak ty)); #lr ◁ box (uninit 2) ]
          with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
        unlock. iFrame. iExists [_;_].
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. auto with iFrame. }
      iApply (type_sum_unit (option (rc ty))); [solve_typing..|].
      iApply type_jump; solve_typing.
  Qed.

  Definition rc_downgrade : val :=
    fn: ["rc"] :=
      let: "r" := new [ #1 ] in
      let: "rc'" := !"rc" in
      let: "rc''" := !"rc'" in
      let: "weak" := !("rc''" +ₗ #1) in
      "rc''" +ₗ #1 <- "weak" + #1;;
      "r" <- "rc''";;
      delete [ #1; "rc" ];; return: ["r"].

  Lemma rc_downgrade_type ty :
    typed_val rc_downgrade (fn(∀ α, ∅; &shr{α}(rc ty)) → weak ty).
  Proof.
    (* TODO : this is almost identical to rc_clone *)
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    iDestruct (ownptr_uninit_own with "Hr") as (lr vlr) "(% & Hr & Hr†)".
    subst r. inv_vec vlr=>r. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν q'') "#(Hαν & Hpersist & Hrctokb)".
    iModIntro. wp_let. wp_op.
    (* Finally, finally... opening the thread-local Rc protocol. *)
    iPoseProof "Hpersist" as (ty') "(_ & Hinv & _ & _)".
    iMod (na_inv_acc with "Hinv Hna") as "(Hrcproto & Hna & Hclose2)"; [solve_ndisj..|].
    iMod (na_bor_acc with "LFT Hrctokb Hα1 Hna") as "(>Hrctok & Hna & Hclose3)"; [solve_ndisj..|].
    iDestruct "Hrcproto" as ([st weakc]) "[>Hrc● Hrcst]".
    iDestruct (own_valid_2 with "Hrc● Hrctok") as %[[[[=]|(?&[[q0 weak0]| |]&[=<-]&?&Hincl)]
               %option_included _]%prod_included [Hval _]]%auth_both_valid_discrete;
    setoid_subst; try done; last first.
    { exfalso. destruct Hincl as [Hincl|Hincl]. by inversion Hincl.
      apply csum_included in Hincl. naive_solver. }
    iDestruct "Hrcst" as (qb) "(Hl'1 & Hl'2 & Hrcst)".
    wp_read. wp_let. wp_op. wp_op. wp_write. wp_write.
    (* And closing it again. *)
    iMod (own_update with "Hrc●") as "[Hrc● Hrctok2]".
    { by apply auth_update_alloc, prod_local_update_2, (op_local_update_discrete _ _ 1%nat). }
    iMod ("Hclose3" with "[$Hrctok] Hna") as "[Hα1 Hna]".
    iMod ("Hclose2" with "[Hrc● Hl'1 Hl'2 Hrcst $Hna]") as "Hna".
    { iExists _. iFrame "Hrc●". iExists _.
      rewrite !Nat2Z.inj_succ Z.add_1_r. iFrame. }
    iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(rc ty)); #lr ◁ box (weak ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame "Hx". iFrame "Hr†". iExists [# #l'].
      rewrite heap_mapsto_vec_singleton /=. eauto 10 with iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Exact same code as downgrade *)
  Definition weak_clone : val :=
    fn: ["w"] :=
      let: "r" := new [ #1 ] in
      let: "w'" := !"w" in
      let: "w''" := !"w'" in
      let: "weak" := !("w''" +ₗ #1) in
      "w''" +ₗ #1 <- "weak" + #1;;
      "r" <- "w''";;
      delete [ #1; "w" ];; return: ["r"].

  Lemma weak_clone_type ty :
    typed_val weak_clone (fn(∀ α, ∅; &shr{α}(weak ty)) → weak ty).
  Proof.
    (* TODO : this is almost identical to rc_clone *)
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (rc'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hx [Hrc' [Hr _]]]".
    rewrite !tctx_hasty_val [[x]]lock.
    destruct rc' as [[|lrc|]|]; try done. iDestruct "Hrc'" as (l') "[#Hlrc #Hshr]".
    iDestruct (ownptr_uninit_own with "Hr") as (lr vlr) "(% & Hr & Hr†)".
    subst r. inv_vec vlr=>r. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "([Hα1 Hα2] & HL & Hclose1)"; [solve_typing..|].
    wp_bind (!_)%E.
    iSpecialize ("Hshr" with "[] Hα1"); last iApply (wp_step_fupd with "Hshr"); [done..|].
    iMod (frac_bor_acc with "LFT Hlrc Hα2") as (q') "[Hlrc↦ Hclose]"; first solve_ndisj.
    iApply wp_fupd. wp_read.
    iMod ("Hclose" with "[$Hlrc↦]") as "Hα2". iIntros "!> [Hα1 Hproto]".
    iDestruct "Hproto" as (γ ν) "#[Hpersist Hwtokb]".
    iModIntro. wp_let. wp_op.
    (* Finally, finally... opening the thread-local Rc protocol. *)
    iPoseProof "Hpersist" as (ty') "(_ & Hinv & _ & _)".
    iAssert (∃ wv : Z, (l' +ₗ 1) ↦ #wv ∗ ((l' +ₗ 1) ↦ #(wv + 1) ={⊤}=∗
               na_own tid ⊤ ∗ (q / 2).[α] ∗ own γ weak_tok))%I
      with "[> Hna Hα1]" as (wv) "[Hwv Hclose2]".
    { iMod (na_inv_acc with "Hinv Hna") as "(Hrcproto & Hna & Hclose2)"; [solve_ndisj..|].
      iMod (na_bor_acc with "LFT Hwtokb Hα1 Hna") as "(>Hwtok & Hna & Hclose3)"; [solve_ndisj..|].
      iDestruct "Hrcproto" as ([st weakc]) "[>Hrc● Hrcst]".
      iDestruct (own_valid_2 with "Hrc● Hwtok") as
        %[[_ Hweak%nat_included]%prod_included [Hval _]]%auth_both_valid_discrete.
      iMod (own_update with "Hrc●") as "[Hrc● $]".
      { by apply auth_update_alloc, prod_local_update_2,
           (op_local_update_discrete _ _ 1%nat). }
      destruct st as [[[q'' strong]| |]|]; try done.
      - iExists _. iDestruct "Hrcst" as (q0) "(Hl'1 & >$ & Hrcst)".
        iIntros "!> Hl'2". iMod ("Hclose3" with "[$Hwtok] Hna") as "[$ Hna]".
        iApply ("Hclose2" with "[- $Hna]"). iExists _. iFrame "Hrc●".
        iExists _. rewrite /Z.add /= Pos.add_1_r. iFrame.
      - iExists _. iDestruct "Hrcst" as "[Hl'1 >$]". iIntros "!> Hl'2".
        iMod ("Hclose3" with "[$Hwtok] Hna") as "[$ Hna]".
        iApply ("Hclose2" with "[- $Hna]"). iExists _. iFrame "Hrc●".
        rewrite /Z.add /= Pos.add_1_r. iFrame.
      - destruct weakc as [|weakc]; first by simpl in Hweak; lia.
        iExists _. iDestruct "Hrcst" as "(Hl'1 & >$ & Hrcst)". iIntros "!> Hl'2".
        iMod ("Hclose3" with "[$Hwtok] Hna") as "[$ Hna]".
        iApply ("Hclose2" with "[- $Hna]"). iExists _. iFrame "Hrc●".
        rewrite /Z.add /= Pos.add_1_r. iFrame. }
    wp_read. wp_let. wp_op. wp_op. wp_write.
    iMod ("Hclose2" with "Hwv") as "(Hna & Hα1 & Hwtok)".
    iMod ("Hclose1" with "[$Hα1 $Hα2] HL") as "HL". wp_write.
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(weak ty)); #lr ◁ box (weak ty)]
        with "[] LFT HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iExists [# #l']. rewrite heap_mapsto_vec_singleton /=.
      auto 10 with iFrame. }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  Definition weak_drop ty : val :=
    fn: ["w"] :=
    withcont: "k":
      let: "w'" := !"w" in
      let: "weak" := !("w'" +ₗ #1) in
      if: "weak" = #1 then
        delete [ #(2 + ty.(ty_size)); "w'" ];;
        "k" []
      else
        "w'" +ₗ #1 <- "weak" - #1;;
        "k" []
    cont: "k" [] :=
      let: "r" := new [ #0] in
      delete [ #1; "w"];; return: ["r"].

  Lemma weak_drop_type ty :
    typed_val (weak_drop ty) (fn(∅; weak ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
    iIntros (_ ϝ ret arg). inv_vec arg=>w. simpl_subst.
    iApply (type_cont [] [ϝ ⊑ₗ []] (λ _, [w ◁ box (uninit 1)]));
      [solve_typing..| |]; last first.
    { simpl. iModIntro. iIntros (k arg). inv_vec arg. simpl_subst.
      iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing. }
    iIntros (k). simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (w'); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hw [Hw' _]]".
    rewrite !tctx_hasty_val [[w]]lock. destruct w' as [[|lw|]|]; try done. wp_op.
    iDestruct "Hw'" as (γ ν) "[#Hpersist Hwtok]".
    iAssert (∃ wv : Z, (lw +ₗ 1) ↦ #wv ∗
        ((⌜wv = 1⌝ ∗ na_own tid ⊤ ∗
          ∃ s, lw ↦ s ∗ ((lw +ₗ 2) ↦∗: λ vl, ⌜length vl = ty.(ty_size)⌝) ∗
               † lw … (2 + ty_size ty)) ∨
         (⌜wv > 1⌝ ∗ ((lw +ₗ 1) ↦ #(wv - 1) ={⊤}=∗ na_own tid ⊤))))%I
      with "[>Hna Hwtok]" as (wv) "[Hlw [(% & Hna & H)|[% Hclose]]]".
    { iPoseProof "Hpersist" as (ty') "([>Hszeq _] & Hinv & _ & _)".
      iDestruct "Hszeq" as %Hszeq.
      iMod (na_inv_acc with "Hinv Hna") as "(Hrcproto & Hna & Hclose)"; [solve_ndisj..|].
      iDestruct "Hrcproto" as ([st weakc]) "[>Hrc● Hrcst]".
      iDestruct (own_valid_2 with "Hrc● Hwtok") as
          %[[_ Hweak%nat_included]%prod_included [Hval _]]%auth_both_valid_discrete.
      destruct weakc; first by simpl in *; lia.
      iMod (own_update_2 with "Hrc● Hwtok") as "Hrc●".
      { apply auth_update_dealloc, prod_local_update_2,
              (cancel_local_update_unit 1%nat), _. }
      destruct st as [[[q'' strong]| |]|]; try done.
      - iExists _. iDestruct "Hrcst" as (q0) "(Hlw & >$ & Hrcst)". iRight.
        iSplitR; first by auto with lia. iIntros "!>?". iApply "Hclose". iFrame.
        iExists _. iFrame. iExists _. iFrame.
        by rewrite !Nat2Z.inj_succ -!Z.add_1_l Z.add_simpl_l.
      - iExists _. iDestruct "Hrcst" as "[Hlw >$]". iRight.
        iSplitR; first by auto with lia. iIntros "!>?". iApply "Hclose". iFrame.
        iExists _. iFrame. simpl.
        by rewrite !Nat2Z.inj_succ -!Z.add_1_l Z.add_simpl_l.
      - iExists _. iDestruct "Hrcst" as "(>Hlw & >$ & >H† & >H)". destruct weakc.
        + iLeft. iSplitR; first done. iMod ("Hclose" with "[$Hna Hrc●]") as "$".
          { iExists _. iFrame. }
          rewrite Hszeq. auto with iFrame.
        + iRight. iSplitR; first by auto with lia. iIntros "!>?". iApply "Hclose".
          iFrame. iExists _. iFrame.
          by rewrite !Nat2Z.inj_succ -!Z.add_1_l Z.add_simpl_l. }
    - subst. wp_read. wp_let. wp_op. wp_if.
      iApply (type_type _ _ _ [ w ◁ box (uninit 1); #lw ◁ box (uninit (2 + ty.(ty_size))) ]
              with "[] LFT HE Hna HL Hk [-]"); last first.
      { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
        unlock. iFrame. iDestruct "H" as (?) "(? & H↦ & ?)". iDestruct "H↦" as (?) "[? %]".
        rewrite /= freeable_sz_full_S. iFrame. iExists (_::_::_).
        rewrite 2!heap_mapsto_vec_cons shift_loc_assoc. iFrame.
        iIntros "!> !%". simpl. congruence. }
      iApply type_delete; [try solve_typing..|].
      iApply type_jump; solve_typing.
    - wp_read. wp_let. wp_op; case_bool_decide; first lia. wp_if. wp_op. wp_op. wp_write.
      iMod ("Hclose" with "Hlw") as "Hna".
      iApply (type_type _ _ _ [ w ◁ box (uninit 1) ]
        with "[] LFT HE Hna HL Hk [-]"); last first.
      { unlock. by rewrite tctx_interp_singleton tctx_hasty_val. }
      iApply type_jump; solve_typing.
  Qed.

  Definition weak_new ty : val :=
    fn: [] :=
      let: "rcbox" := new [ #(2 + ty.(ty_size))%nat ] in
      let: "w" := new [ #1 ] in
      "rcbox" +ₗ #0 <- #0;;
      "rcbox" +ₗ #1 <- #1;;
      "w" <- "rcbox";;
      return: ["w"].

  Lemma weak_new_type ty :
    typed_val (weak_new ty) (fn(∅) → weak ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (_ ϝ ret arg). inv_vec arg. simpl_subst.
    iApply (type_new (2 + ty.(ty_size))); [solve_typing..|]; iIntros (rcbox); simpl_subst.
    iApply (type_new 1); [solve_typing..|]; iIntros (w); simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk [Hw [Hrcbox _]]". rewrite !tctx_hasty_val.
    iDestruct (ownptr_uninit_own with "Hrcbox") as (lrcbox vlrcbox)
       "(% & Hrcbox↦ & Hrcbox†)". subst rcbox. inv_vec vlrcbox=>??? /=.
    iDestruct (heap_mapsto_vec_cons with "Hrcbox↦") as "[Hrcbox↦0 Hrcbox↦1]".
    iDestruct (heap_mapsto_vec_cons with "Hrcbox↦1") as "[Hrcbox↦1 Hrcbox↦2]".
    iDestruct (ownptr_uninit_own with "Hw") as (lw vlw) "(% & Hw↦ & Hw†)". subst w.
    inv_vec vlw=>?. rewrite heap_mapsto_vec_singleton.
    (* All right, we are done preparing our context. Let's get going. *)
    wp_op. rewrite shift_loc_0. wp_write. wp_op. wp_write.
    iMod (lft_create with "LFT") as (ν) "[Hν #Hν†]"; first done.
    iPoseProof ("Hν†" with "Hν") as "H†". wp_bind (_ <- _)%E.
    iApply wp_mask_mono; last iApply (wp_step_fupd with "H†"); [set_solver-..|].
    wp_write. iIntros "#Hν !>". wp_seq.
    iApply (type_type _ _ _ [ #lw ◁ box (weak ty)]
        with "[] LFT HE Hna HL Hk [> -]"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val' //=. iFrame.
      iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame.
      iMod (own_alloc (● _ ⋅ ◯ _)) as (γ) "[??]"; last (iExists _, _; iFrame).
      { apply auth_both_valid_discrete. by split. }
      iExists ty. iFrame "Hν†". iSplitR; first by iApply type_incl_refl.
      iSplitL; last by iRight. iMod (na_inv_alloc with "[-]") as "$"; last done.
      iExists _. iFrame. rewrite freeable_sz_full_S shift_loc_assoc. iFrame.
      iExists _. iFrame. rewrite vec_to_list_length. auto. }
    iApply type_jump; solve_typing.
  Qed.
End code.
