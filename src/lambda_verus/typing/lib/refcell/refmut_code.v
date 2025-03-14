From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree numbers.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.refcell Require Import refcell refmut.
Set Default Proof Using "Type".

Section refmut_functions.
  Context `{!typeG Σ, !refcellG Σ}.

  (* Turning a refmut into a shared borrow. *)
  Definition refmut_deref : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma refmut_deref_type ty :
    typed_val refmut_deref (fn(∀ '(α, β), ∅; &shr{α}(refmut β ty)) → &shr{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]=>//=.
    iDestruct "Hx'" as (lv lrc) "#(Hfrac & #Hshr)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose')";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose'')";
      [solve_typing..|].
    iDestruct (lft_intersect_acc with "Hβ Hα2") as (qβα) "[Hα2β Hcloseβα2]".
    wp_bind (!#lx')%E. iApply (wp_step_fupd with "[Hα2β]");
         [|by iApply ("Hshr" with "[] Hα2β")|]; first done.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. iIntros "[#Hshr' Hα2β] !>". wp_let.
    iDestruct ("Hcloseβα2" with "Hα2β") as "[Hβ Hα2]".
    iMod ("Hcloseα1" with "[$H↦1 $H↦2]") as "Hα1".
    iMod ("Hclose''" with "Hβ HL") as "HL". iMod ("Hclose'" with "[$] HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(refmut β ty)); #lv ◁ &shr{α}ty]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr'").
      by iApply lft_incl_glb; last iApply lft_incl_refl. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Turning a refmut into a unique borrow. *)
  Definition refmut_derefmut : val := refmut_deref.

  Lemma refmut_derefmut_type ty :
    typed_val refmut_derefmut
              (fn(∀ '(α, β), ∅; &uniq{α}(refmut β ty)) → &uniq{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "(Hx & #Hαty & Hx')". destruct x' as [[|lx'|]|]; try done.
    iMod (bor_exists with "LFT Hx'") as (vl) "H". done.
    iMod (bor_sep with "LFT H") as "[H↦ H]". done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose')";
      [solve_typing..|].
    destruct vl as [|[[|lv|]|][|[[|lrc|]|][]]]; simpl;
      try by iMod (bor_persistent with "LFT H Hα") as "[>[] _]".
    iMod (bor_exists with "LFT H") as (ν) "H". done.
    iMod (bor_exists with "LFT H") as (q) "H". done.
    iMod (bor_exists with "LFT H") as (γ) "H". done.
    iMod (bor_exists with "LFT H") as (δ) "H". done.
    iMod (bor_exists with "LFT H") as (ty') "H". done.
    iMod (bor_sep with "LFT H") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hβδ H]". done.
    iMod (bor_sep with "LFT H") as "[Hβty H]". done.
    iMod (bor_persistent with "LFT Hβδ Hα") as "[#Hβδ Hα]". done.
    iMod (bor_persistent with "LFT Hβty Hα") as "[#Hβty Hα]". done.
    iMod (bor_sep with "LFT H") as "[_ H]". done.
    iMod (bor_sep with "LFT H") as "[H _]". done.
    iMod (bor_fracture (λ q', (q * q').[ν])%I with "LFT [H]") as "H". done.
    { by rewrite Qp_mul_1_r. }
    iDestruct (frac_bor_lft_incl _ _ q with "LFT H") as "#Hαν". iClear "H".
    rewrite heap_mapsto_vec_cons. iMod (bor_sep with "LFT H↦") as "[H↦ _]". done.
    iMod (bor_acc with "LFT H↦ Hα") as "[H↦ Hcloseα]". done.
    wp_bind (!#lx')%E. iMod (bor_unnest with "LFT Hb") as "Hb"; first done.
    wp_read. wp_let. iMod "Hb".
    iMod ("Hcloseα" with "[$H↦]") as "[_ Hα]". iMod ("Hclose'" with "Hα HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _ [ x ◁ box (uninit 1); #lv ◁ &uniq{α}ty]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame "Hx". iSplitR.
      - iApply lft_incl_trans; [|done]. by iApply lft_incl_glb.
      - iApply (bor_shorten with "[] Hb").
        by iApply lft_incl_glb; [iApply lft_incl_glb|iApply lft_incl_refl]. }
    iApply (type_letalloc_1 (&uniq{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Dropping a refmut and set the count to 0 in the corresponding refcell. *)
  Definition refmut_drop : val :=
    fn: ["x"] :=
      let: "rc" := !("x" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" + #1;;
      Endlft;;
      delete [ #2; "x"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma refmut_drop_type ty :
    typed_val refmut_drop (fn(∀ α, ∅; refmut α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk Hx". rewrite tctx_interp_singleton tctx_hasty_val.
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Hx"; simpl;
      try iDestruct "Hx" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hx" as "[[Hx↦1 Hx↦2] Hx]". wp_op. wp_read. wp_let.
    iDestruct "Hx" as (ν q γ β ty') "(Hb & #Hαβ & #Hβty & #Hinv & Hν & H◯)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)";
      [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hcloseβ)"; [done..|].
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)". wp_read. wp_let. wp_op. wp_write.
    iAssert (|={↑lftN ∪ ↑lft_userN}[↑lft_userN]▷=> refcell_inv tid lrc γ β ty')%I
      with "[H↦lrc H● H◯ Hν INV]" as "INV".
    { iDestruct (own_valid_2 with "H● H◯") as
        %[[[=]|(? & [[? q'] ?] & [= <-] & Hst & INCL)]%option_included _]
         %auth_both_valid_discrete.
      destruct st as [[[[??]?]?]|]; [|done]. move: Hst=>-[= ???]. subst.
      destruct INCL as [[[[ν' ?]%to_agree_inj ?] ?]|
            [[[??]%to_agree_included [q'' Hq'']]%prod_included [n' Hn']]%prod_included].
      - simpl in *. setoid_subst. iExists None. iFrame.
        iMod (own_update_2 with "H● H◯") as "$".
        { apply auth_update_dealloc. rewrite -(right_id None op (Some _)).
          apply cancel_local_update_unit, _. }
        iDestruct "INV" as "(H† & Hq & _)".
        iApply "H†".
        iDestruct "Hq" as (q) "(<- & ?)". iFrame.
      - simpl in *. setoid_subst. iExists (Some (_, _, _, _)).
        iMod (own_update_2 with "H● H◯") as "$".
        { apply auth_update_dealloc. rewrite -(agree_idemp (to_agree _)) !pair_op Some_op.
          apply (cancel_local_update_unit (writing_stR q _)), _. }
        iDestruct "INV" as "(H† & Hq & _)".
        rewrite /= (_:Z.neg (1%positive ⋅ n') + 1 = Z.neg n');
          last (rewrite pos_op_plus; lia). iFrame.
        iApply step_fupd_intro; [set_solver-|]. iSplitL; [|done].
        iDestruct "Hq" as (q' ?) "?". iExists (q+q')%Qp. iFrame.
        rewrite assoc (comm _ q'' q) //. }
    wp_bind Endlft. iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); first done.
    iApply (wp_step_fupd with "INV"); [set_solver-|]. wp_seq. iIntros "{Hb} Hb !>".
    iMod ("Hcloseβ" with "Hb Hna") as "[Hβ Hna]".
    iMod ("Hcloseα" with "Hβ") as "Hα". iMod ("Hclose" with "Hα HL") as "HL". wp_seq.
    iApply (type_type _ _ _ [ #lx ◁ box (uninit 2)]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame. iExists [ #lv;#lrc].
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton uninit_own. iFrame. auto. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  (* Apply a function within the refmut, typically for accessing a component. *)
  Definition refmut_map (call_once : val) : val :=
    fn: ["ref"; "f"] :=
      let: "call_once" := call_once in
      let: "x'" := !"ref" in
      letalloc: "x" <- "x'" in
      letcall: "r" := "call_once" ["f"; "x"]%E in
      let: "r'" := !"r" in delete [ #1; "r"];;
      "ref" <- "r'";;
      return: ["ref"].

  Lemma refmut_map_type ty1 ty2 call_once fty :
    (* fty : for<'a>, FnOnce(&'a ty1) -> &'a ty2, as witnessed by the impl call_once *)
    typed_val call_once (fn(∀ α, ∅; fty, &uniq{α}ty1) → &uniq{α}ty2) →
    typed_val (refmut_map call_once) (fn(∀ α, ∅; refmut α ty1, fty) → refmut α ty2).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret arg).
       inv_vec arg=>ref env. simpl_subst.
    iApply type_let; [apply Hf | solve_typing |]. iIntros (f'). simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk (#Hf' & Href & Henv & _)".
    rewrite (tctx_hasty_val _ ref). destruct ref as [[|lref|]|]; try done.
    iDestruct "Href" as "[Href Href†]".
    iDestruct "Href" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Href"; simpl;
      try iDestruct "Href" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Href" as "[[Href↦1 Href↦2] Href]".
    iDestruct "Href" as (ν q γ β ty') "(Hbor & #Hαβ & #Hβty & #Hinv & >Hν & Hγ)".
    wp_read. wp_let. wp_apply wp_new; first done. done.
    iIntros (lx) "(H† & Hlx)". rewrite heap_mapsto_vec_singleton.
    wp_let. wp_write. wp_let. rewrite tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (?) "(Hα & HL & Hclose1)";[solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (?) "(Hϝ & HL & Hclose2)";[solve_typing..|].
    iDestruct (lft_intersect_acc with "Hα Hν") as (?) "[Hαν Hclose3]".
    iDestruct (lft_intersect_acc with "Hαν Hϝ") as (?) "[Hανϝ Hclose4]".
    rewrite -[ϝ in (α ⊓ ν) ⊓ ϝ](right_id_L).
    iApply (type_call_iris _ [α ⊓ ν; ϝ] (α ⊓ ν) [_; _]
            with "LFT HE Hna [Hανϝ] Hf' [$Henv Hlx H† Hbor]"); [solve_typing|done| |].
    { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full.
      iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. by iFrame. }
    iIntros ([[|r|]|]) "Hna Hανϝ Hr //".
    iDestruct ("Hclose4" with "Hανϝ") as "[Hαν Hϝ]".
    iDestruct ("Hclose3" with "Hαν") as "[Hα Hν]".
    iMod ("Hclose2" with "Hϝ HL") as "HL". iMod ("Hclose1" with "Hα HL") as "HL".
    wp_rec. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as ([|[[]|][]]) "(Hr & #Hl & Hr')"=>//.
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    wp_apply (wp_delete _ _ _ [_] with "[Hr Hr†]")=>//.
    { rewrite heap_mapsto_vec_singleton freeable_sz_full. iFrame. } iIntros "_".
    wp_seq. wp_write.
    iApply (type_type _ [_] _ [ #lref ◁ box (refmut α ty2) ]
       with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. simpl. iFrame.
      iExists [_;_]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iFrame. simpl. auto 20 with iFrame. }
    iApply type_jump; solve_typing.
  Qed.

  (* Apply a function within the refmut, and create two refmuts,
     typically for splitting the reference. *)
  Definition refmut_map_split (call_once : val) : val :=
    fn: ["refmut"; "f"] :=
      let: "call_once" := call_once in
      let: "x'" := !"refmut" in

      letalloc: "x" <- "x'" in
      letcall: "r" := "call_once" ["f"; "x"]%E in
      let: "a" := !"r" in
      let: "b" := !("r" +ₗ #1) in
      delete [ #2; "r"];;

      let: "rc" := !("refmut" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" - #1;;

      delete [ #2; "refmut"];;

      let: "refmuts" := new [ #4 ] in
      "refmuts" <- "a";;
      "refmuts" +ₗ #1 <- "rc";;
      "refmuts" +ₗ #2 <- "b";;
      "refmuts" +ₗ #3 <- "rc";;

      return: ["refmuts"].

  Lemma refmut_map_split_type ty ty1 ty2 call_once fty :
    (* fty : for<'a>, FnOnce(&mut'a ty) -> (&mut'a ty1, &mut'a ty2),
       as witnessed by the impl call_once *)
    typed_val call_once
              (fn(∀ α, ∅; fty, &uniq{α}ty) → Π[&uniq{α}ty1; &uniq{α}ty2]) →
    typed_val (refmut_map_split call_once)
              (fn(∀ α, ∅; refmut α ty, fty) → Π[refmut α ty1; refmut α ty2]).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret arg).
       inv_vec arg=>refmut env. simpl_subst.
    iApply type_let; [apply Hf | solve_typing |]. iIntros (f'). simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk (#Hf' & Hrefmut & Henv & _)".
    rewrite (tctx_hasty_val _ refmut). destruct refmut as [[|lrefmut|]|]; try done.
    iDestruct "Hrefmut" as "[Hrefmut Hrefmut†]".
    iDestruct "Hrefmut" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Hrefmut"; simpl;
      try iDestruct "Hrefmut" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hrefmut" as "[[Hrefmut↦1 Hrefmut↦2] Hrefmut]".
    iDestruct "Hrefmut" as (ν qν γ β ty') "(Hbor & #Hαβ & #Hl & #Hinv & >Hν & Hγ)".
    wp_read. wp_let. wp_apply wp_new; [done..|].
    iIntros (lx) "(H† & Hlx)". rewrite heap_mapsto_vec_singleton.
    wp_let. wp_write. wp_let. rewrite tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (?) "(Hα & HL & Hclose1)";[solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (?) "(Hϝ & HL & Hclose2)";[solve_typing..|].
    iDestruct (lft_intersect_acc with "Hα Hν") as (?) "[Hαν Hclose3]".
    iDestruct (lft_intersect_acc with "Hαν Hϝ") as (?) "[Hανϝ Hclose4]".
    rewrite -[ϝ in (α ⊓ ν) ⊓ ϝ](right_id_L).
    iApply (type_call_iris _ [α ⊓ ν; ϝ] (α ⊓ ν) [_; _]
       with "LFT HE Hna [Hανϝ] Hf' [$Henv Hlx H† Hbor]"); [solve_typing|done| |].
    { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full.
      iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame. auto. }
    iIntros ([[|r|]|]) "Hna Hανϝ Hr //".
    iDestruct ("Hclose4" with "Hανϝ") as "[Hαν Hϝ]".
    iDestruct ("Hclose3" with "Hαν") as "[Hα Hν]".
    iMod ("Hclose2" with "Hϝ HL") as "HL".
    wp_rec. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (?) "[Hr H]". iDestruct "H" as (vl1 vl1' ->) "[[#? Hr1'] H]".
    iDestruct "H" as (vl2 vl2' ->) "[[#? Hr2'] ->]".
    destruct vl1 as [|[[|lr1|]|] []], vl2 as [|[[|lr2|]|] []]=>//=.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hr" as "[Hr1 Hr2]". wp_read. wp_let. wp_op. wp_read. wp_let.
    wp_apply (wp_delete _ _ _ [_; _] with "[Hr1 Hr2 Hr†]")=>//.
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton /= freeable_sz_full.
      iFrame. }
    iIntros "_".
    iMod (lft_incl_acc  with "Hαβ Hα") as (?) "[Hβ Hβclose]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hclosena)"; [done..|].
    wp_seq. wp_op. wp_read.
    iDestruct "INV" as (st) "(Hlrc & H● & Hst)".
    iDestruct (own_valid_2 with "H● Hγ") as %[Hst _]%auth_both_valid_discrete.
    destruct st as [[[[??]?]?]|]; last by destruct Hst as [[?|] Hst]; inversion Hst.
    move:Hst=>/Some_pair_included [/Some_pair_included_total_1
              [/to_agree_included /(leibniz_equiv _ _) [= <- <-] _] _].
    iDestruct "Hst" as "(H† & Hq & _)". iDestruct "Hq" as (q1 Hqq1) "[Hν1 Hν2]".
    iMod (own_update with "H●") as "[H● ?]".
    { apply auth_update_alloc,
         (op_local_update_discrete _ _ (writing_stR (q1/2)%Qp ν))=>-[Hagv _].
      split; [split|done].
      - by rewrite /= agree_idemp.
      - apply frac_valid'. rewrite /= -Hqq1 comm_L.
        by apply Qp_add_le_mono_l, Qp_div_le. }
    wp_let. wp_read. wp_let. wp_op. wp_write.
    wp_apply (wp_delete _ _ _ [_; _] with "[Hrefmut↦1 Hrefmut↦2 Hrefmut†]")=>//.
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton /= freeable_sz_full.
      iFrame. }
    iIntros "_". wp_seq. wp_apply wp_new; [done..|]. iIntros (lrefmuts) "[Hrefmuts† Hrefmuts]".
    rewrite 3!heap_mapsto_vec_cons heap_mapsto_vec_singleton. wp_let.
    iDestruct "Hrefmuts" as "(Hrefmuts1 & Hrefmuts2 & Hrefmuts3 & Hrefmuts4)".
    rewrite !shift_loc_assoc. wp_write. do 3 (wp_op; wp_write).
    iMod ("Hclosena" with "[Hlrc H● Hν1 H†] Hna") as "[Hβ Hna]".
    { iExists (Some (_, true, _, _)).
      rewrite -Some_op -!pair_op agree_idemp /= (comm _ xH _).
      iFrame. iSplitL; [|done]. iExists _. iFrame.
      rewrite (comm Qp_add) (assoc Qp_add) Qp_div_2 (comm Qp_add). auto. }
    iMod ("Hβclose" with "Hβ") as "Hα". iMod ("Hclose1" with "Hα HL") as "HL".
    iApply (type_type _ [_] _ [ #lrefmuts ◁ box (Π[refmut α ty1; refmut α ty2]) ]
       with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //= -freeable_sz_full.
      simpl. iFrame. iExists [_;_;_;_].
      rewrite 3!heap_mapsto_vec_cons heap_mapsto_vec_singleton !shift_loc_assoc.
      iFrame. iExists [_;_], [_;_]. iSplit=>//=.
      iSplitL "Hν Hγ Hr1'"; [by auto 10 with iFrame|]. iExists [_;_], [].
      iSplitR=>//=. rewrite right_id. auto 20 with iFrame. }
    iApply type_jump; solve_typing.
  Qed.
End refmut_functions.
