From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree numbers.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import lifetime na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.refcell Require Import refcell ref.
Set Default Proof Using "Type".

Section ref_functions.
  Context `{!typeG Σ, !refcellG Σ}.

  Lemma refcell_inv_reading_inv tid l γ α ty q ν :
    refcell_inv tid l γ α ty -∗
    own γ (◯ reading_stR q ν) -∗
    ∃ (q' : Qp) n, l ↦ #(Zpos n) ∗ ⌜(q ≤ q')%Qp⌝ ∗
            own γ (● (refcell_st_to_R $ Some (ν, false, q', n)) ⋅ ◯ reading_stR q ν) ∗
            ((1).[ν] ={↑lftN ∪ ↑lft_userN}[↑lft_userN]▷=∗ &{α}((l +ₗ 1) ↦∗: ty_own ty tid)) ∗
            (∃ q'', ⌜(q' + q'' = 1)%Qp⌝ ∗ q''.[ν]) ∗
            ty.(ty_shr) (α ⊓ ν) tid (l +ₗ 1).
  Proof.
    iIntros "INV H◯".
    iDestruct "INV" as (st) "(H↦lrc & H● & INV)".
    iAssert (∃ q' n, st ≡ Some (ν, false, q', n) ∗ ⌜q ≤ q'⌝%Qp)%I with
       "[#]" as (q' n) "[%%]".
    { destruct st as [[[[??]?]?]|];
      iDestruct (own_valid_2 with "H● H◯")
        as %[[[=]|(?&[[? q'] n]&[=<-]&[=]&[[[Eq_ag ?%leibniz_equiv]_]|Hle])]
               %option_included Hv]%auth_both_valid_discrete; simpl in *; subst.
      - apply (inj to_agree), (inj2 pair) in Eq_ag.
        destruct Eq_ag. setoid_subst. eauto.
      - revert Hle=> /prod_included [/= /prod_included
                  [/= /to_agree_included [/= ??] /frac_included_weak ?] _].
        setoid_subst. eauto. }
    setoid_subst. iExists q', n. rewrite own_op. by iFrame.
  Qed.

  (* Cloning a ref. We need to increment the counter. *)
  Definition ref_clone : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      let: "rc" := !("x'" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" + #1;;
      letalloc: "r" <-{2} !"x'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma ref_clone_type ty :
    typed_val ref_clone (fn(∀ '(α, β), ∅; &shr{α}(ref β ty)) → ref β ty).

  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]=>//=.
    iDestruct "Hx'" as (ν q γ δ ty' lv lrc) "#(Hαν & Hfrac & Hshr & Hβδ & Hinv & H◯inv)".
    wp_op.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hβδ Hβ") as (qδ) "[Hδ Hcloseβ]". done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose')";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    iMod (na_bor_acc with "LFT Hinv Hδ Hna") as "(INV & Hna & Hcloseδ)"; [done..|].
    iMod (na_bor_acc with "LFT H◯inv Hα2 Hna") as "(H◯ & Hna & Hcloseα2)"; [solve_ndisj..|].
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. wp_let.
    iDestruct (refcell_inv_reading_inv with "INV H◯")
      as (q' n) "(H↦lrc & _ & [H● H◯] & H† & Hq' & Hshr')".
    wp_read. wp_let. wp_op. wp_write. iDestruct "Hq'" as (q'') "(Hq'q'' & Hν1 & Hν2)".
    iDestruct "Hq'q''" as %Hq'q''. iMod (own_update with "H●") as "[H● ?]".
    { apply auth_update_alloc,
         (op_local_update_discrete _ _ (reading_stR (q''/2)%Qp ν))=>-[Hagv _].
      split; [split|done].
      - by rewrite /= agree_idemp.
      - apply frac_valid'. rewrite /= -Hq'q'' comm_L.
        by apply Qp_add_le_mono_l, Qp_div_le. }
    wp_apply wp_new; [done..|]. iIntros (lr) "(?&Hlr)".
    iAssert (lx' ↦∗{qlx'} [ #lv; #lrc])%I  with "[H↦1 H↦2]" as "H↦".
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
    wp_let. wp_apply (wp_memcpy with "[$Hlr $H↦]"); [done..|].
    iIntros "[Hlr H↦]". wp_seq. iMod ("Hcloseα2" with "[$H◯] Hna") as "[Hα1 Hna]".
    iMod ("Hcloseδ" with "[H↦lrc H● Hν1 Hshr' H†] Hna") as "[Hδ Hna]".
    { iExists (Some (_, false, _, _)). rewrite Z.add_comm -Some_op -!pair_op agree_idemp.
      iFrame. iExists _. iFrame.
      rewrite (comm Qp_add) (assoc Qp_add) Qp_div_2 (comm Qp_add). auto. }
    iMod ("Hcloseβ" with "Hδ") as "Hβ". iMod ("Hcloseα1" with "[$H↦]") as "Hα2".
    iMod ("Hclose'" with "[$Hα1 $Hα2] HL") as "HL". iMod ("Hclose" with "Hβ HL") as "HL".
    iApply (type_type _ _ _
           [ x ◁ box (&shr{α}(ref β ty)); #lr ◁ box(ref β ty)]
        with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      rewrite /= freeable_sz_full. iFrame. iExists _. iFrame. simpl.
      iExists _, _, _, _, _. iFrame "∗#". }
    iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Turning a ref into a shared borrow. *)
  Definition ref_deref : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma ref_deref_type ty :
    typed_val ref_deref
      (fn(∀ '(α, β), ∅; &shr{α}(ref β ty)) → &shr{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]=>//=.
    iDestruct "Hx'" as (ν q γ δ ty' lv lrc) "#(Hαν & Hfrac & Hshr & Hx')".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα") as (qlx') "[H↦ Hcloseα]". done.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. wp_let.
    iMod ("Hcloseα" with "[$H↦1 $H↦2]") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _
        [ x ◁ box (&shr{α}(ref β ty)); #lv ◁ &shr{α}ty]
        with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr"). by iApply lft_incl_glb. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Dropping a ref and decrement the count in the corresponding refcell. *)
  Definition ref_drop : val :=
    fn: ["x"] :=
      let: "rc" := !("x" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" - #1;;
      Endlft;;
      delete [ #2; "x"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma ref_drop_type ty :
    typed_val ref_drop (fn(∀ α, ∅; ref α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk Hx". rewrite tctx_interp_singleton tctx_hasty_val.
    destruct x as [[|lx|]|]; try done. iDestruct "Hx" as "[Hx Hx†]".
    iDestruct "Hx" as ([|[[|lv|]|][|[[|lrc|]|][]]]) "Hx"; simpl;
      try iDestruct "Hx" as "[_ >[]]".
    rewrite {1}heap_mapsto_vec_cons heap_mapsto_vec_singleton.
    iDestruct "Hx" as "[[Hx↦1 Hx↦2] Hx]". wp_op. wp_read. wp_let.
    iDestruct "Hx" as (ν q γ β ty') "(_ & #Hαβ & #Hinv & Hν & H◯)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    iMod (na_bor_acc with "LFT Hinv Hβ Hna") as "(INV & Hna & Hcloseβ)"; [done..|].
    iDestruct (refcell_inv_reading_inv with "INV [$H◯]")
      as (q' n) "(H↦lrc & >% & H●◯ & H† & Hq' & Hshr)".
    iDestruct "Hq'" as (q'') ">[% Hν']".
    wp_read. wp_let. wp_op. wp_write.
    iAssert (|={↑lftN ∪ ↑lft_userN}[↑lft_userN]▷=> refcell_inv tid lrc γ β ty')%I
      with "[H↦lrc H●◯ Hν Hν' Hshr H†]" as "INV".
    { iDestruct (own_valid with "H●◯") as
          %[[[[_ ?]?]|[[_ [q0 Hq0]]%prod_included [n' Hn']]%prod_included]
              %Some_included _]%auth_both_valid_discrete.
      - simpl in *. setoid_subst.
        iExists None. iFrame. iMod (own_update with "H●◯") as "$".
        { apply auth_update_dealloc. rewrite -(right_id None op (Some _)).
          apply cancel_local_update_unit, _. }
        iApply "H†". replace 1%Qp with (q'+q'')%Qp by naive_solver. iFrame.
      - simpl in *. setoid_subst. iExists (Some (ν, false, q0, n')). iFrame.
        iAssert (lrc ↦ #(Z.pos n'))%I with "[H↦lrc]" as "$".
        { rewrite pos_op_plus Z.sub_1_r -Pos2Z.inj_pred; last lia.
          by rewrite Pos.add_1_l Pos.pred_succ. }
        iMod (own_update with "H●◯") as "$".
        { apply auth_update_dealloc.
          rewrite -(agree_idemp (to_agree _)) !pair_op Some_op.
          apply (cancel_local_update_unit (reading_stR q ν)), _. }
        iApply step_fupd_intro; first set_solver-. iExists (q+q'')%Qp. iFrame.
        by rewrite assoc (comm _ q0 q). }
    wp_bind Endlft. iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); first done.
    iApply (wp_step_fupd with "INV"); [set_solver-..|]. wp_seq.
    iIntros "INV !>". wp_seq. iMod ("Hcloseβ" with "[$INV] Hna") as "[Hβ Hna]".
    iMod ("Hcloseα" with "Hβ") as "Hα". iMod ("Hclose" with "Hα HL") as "HL".
    iApply (type_type _ _ _ [ #lx ◁ box (uninit 2)] with "[] LFT HE Hna HL Hk");
      first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame. iExists [ #lv;#lrc].
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton uninit_own. iFrame. auto. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_jump; solve_typing.
  Qed.

  (* Apply a function within the ref, typically for accessing a component. *)
  Definition ref_map (call_once : val) : val :=
    fn: ["ref"; "f"] :=
      let: "call_once" := call_once in
      let: "x'" := !"ref" in
      letalloc: "x" <- "x'" in
      letcall: "r" := "call_once" ["f"; "x"]%E in
      let: "r'" := !"r" in delete [ #1; "r"];;
      "ref" <- "r'";;
      return: ["ref"].

  Lemma ref_map_type ty1 ty2 call_once fty :
    (* fty : for<'a>, FnOnce(&'a ty1) -> &'a ty2, as witnessed by the impl call_once *)
    typed_val call_once (fn(∀ α, ∅; fty, &shr{α}ty1) → &shr{α}ty2) →
    typed_val (ref_map call_once) (fn(∀ α, ∅; ref α ty1, fty) → ref α ty2).
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
    iDestruct "Href" as (ν qν γ β ty') "(#Hshr & #Hαβ & #Hinv & >Hν & Hγ)".
    wp_read. wp_let. wp_apply wp_new; try done.
    iIntros (lx) "(H† & Hlx)". rewrite heap_mapsto_vec_singleton.
    wp_let. wp_write. wp_let. rewrite tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (?) "(Hα & HL & Hclose1)";[solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (?) "(Hϝ & HL & Hclose2)";[solve_typing..|].
    iDestruct (lft_intersect_acc with "Hα Hν") as (?) "[Hαν Hclose3]".
    iDestruct (lft_intersect_acc with "Hαν Hϝ") as (?) "[Hανϝ Hclose4]".
    rewrite -[ϝ in (α ⊓ ν) ⊓ ϝ](right_id_L).
    iApply (type_call_iris _ [α ⊓ ν; ϝ] (α ⊓ ν) [_; _]
       with "LFT HE Hna [Hανϝ] Hf' [$Henv Hlx H†]"); [solve_typing|done| |].
    { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full.
      iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. by iFrame. }
    iIntros ([[|r|]|]) "Hna Hανϝ Hr //".
    iDestruct ("Hclose4" with "Hανϝ") as "[Hαν Hϝ]".
    iDestruct ("Hclose3" with "Hαν") as "[Hα Hν]".
    iMod ("Hclose2" with "Hϝ HL") as "HL". iMod ("Hclose1" with "Hα HL") as "HL".
    wp_rec. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as ([|r'[]]) "[Hr #Hr']";
      try by iDestruct (ty_size_eq with "Hr'") as "%".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let.
    wp_apply (wp_delete _ _ _ [_] with "[Hr Hr†]")=>//.
    { rewrite heap_mapsto_vec_singleton freeable_sz_full. iFrame. } iIntros "_".
    wp_seq. wp_write.
    iApply (type_type _ [_] _ [ #lref ◁ box (ref α ty2) ]
       with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //. simpl. iFrame.
      iExists [_;_]. rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton.
      iFrame. destruct r' as [[]|]=>//=. auto 10 with iFrame. }
    iApply type_jump; solve_typing.
  Qed.

  (* Apply a function within the ref, and create two ref,
     typically for splitting the reference. *)
  Definition ref_map_split (call_once : val) : val :=
    fn: ["ref"; "f"] :=
      let: "call_once" := call_once in
      let: "x'" := !"ref" in

      letalloc: "x" <- "x'" in
      letcall: "r" := "call_once" ["f"; "x"]%E in
      let: "a" := !"r" in
      let: "b" := !("r" +ₗ #1) in
      delete [ #2; "r"];;

      let: "rc" := !("ref" +ₗ #1) in
      let: "n" := !"rc" in
      "rc" <- "n" + #1;;

      delete [ #2; "ref"];;

      let: "refs" := new [ #4 ] in
      "refs" <- "a";;
      "refs" +ₗ #1 <- "rc";;
      "refs" +ₗ #2 <- "b";;
      "refs" +ₗ #3 <- "rc";;

      return: ["refs"].

  Lemma ref_map_split_type ty ty1 ty2 call_once fty :
    (* fty : for<'a>, FnOnce(&'a ty) -> (&'a ty1, &'a ty2),
       as witnessed by the impl call_once *)
    typed_val call_once
              (fn(∀ α, ∅; fty, &shr{α}ty) → Π[&shr{α}ty1; &shr{α}ty2]) →
    typed_val (ref_map_split call_once)
              (fn(∀ α, ∅; ref α ty, fty) → Π[ref α ty1; ref α ty2]).
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
    iDestruct "Href" as (ν qν γ β ty') "(#Hshr & #Hαβ & #Hinv & >Hν & Hγ)".
    wp_read. wp_let. wp_apply wp_new; [done..|].
    iIntros (lx) "(H† & Hlx)". rewrite heap_mapsto_vec_singleton.
    wp_let. wp_write. wp_let. rewrite tctx_hasty_val.
    iMod (lctx_lft_alive_tok α with "HE HL") as (?) "(Hα & HL & Hclose1)";[solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (?) "(Hϝ & HL & Hclose2)";[solve_typing..|].
    iDestruct (lft_intersect_acc with "Hα Hν") as (?) "[Hαν Hclose3]".
    iDestruct (lft_intersect_acc with "Hαν Hϝ") as (?) "[Hανϝ Hclose4]".
    rewrite -[ϝ in (α ⊓ ν) ⊓ ϝ](right_id_L).
    iApply (type_call_iris _ [α ⊓ ν; ϝ] (α ⊓ ν) [_; _]
       with "LFT HE Hna [Hανϝ] Hf' [$Henv Hlx H†]"); [solve_typing|done| |].
    { rewrite big_sepL_singleton tctx_hasty_val' //. rewrite /= freeable_sz_full.
      iFrame. iExists [_]. rewrite heap_mapsto_vec_singleton. by iFrame. }
    iIntros ([[|r|]|]) "Hna Hανϝ Hr //".
    iDestruct ("Hclose4" with "Hανϝ") as "[Hαν Hϝ]".
    iDestruct ("Hclose3" with "Hαν") as "[Hα Hν]".
    iMod ("Hclose2" with "Hϝ HL") as "HL".
    wp_rec. iDestruct "Hr" as "[Hr Hr†]".
    iDestruct "Hr" as (?) "[Hr H]". iDestruct "H" as (vl1 vl1' ->) "[#Hr1' H]".
    iDestruct "H" as (vl2 vl2' ->) "[#Hr2' ->]".
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
    iDestruct (refcell_inv_reading_inv with "INV Hγ")
      as (q1 n) "(H↦lrc & _ & [H● H◯] & H† & Hq1 & Hshr')".
    iDestruct "Hq1" as (q2) "(Hq1q2 & Hν1 & Hν2)".
    iDestruct "Hq1q2" as %Hq1q2. iMod (own_update with "H●") as "[H● ?]".
    { apply auth_update_alloc,
         (op_local_update_discrete _ _ (reading_stR (q2/2)%Qp ν))=>-[Hagv _].
      split; [split|done].
      - by rewrite /= agree_idemp.
      - apply frac_valid'. rewrite /= -Hq1q2 comm_L.
        by apply Qp_add_le_mono_l, Qp_div_le. }
    wp_let. wp_read. wp_let. wp_op. wp_write.
    wp_apply (wp_delete _ _ _ [_; _] with "[Href↦1 Href↦2 Href†]")=>//.
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton /= freeable_sz_full.
      iFrame. }
    iIntros "_". wp_seq. wp_apply wp_new; [done..|]. iIntros (lrefs) "[Hrefs† Hrefs]".
    rewrite 3!heap_mapsto_vec_cons heap_mapsto_vec_singleton. wp_let.
    iDestruct "Hrefs" as "(Hrefs1 & Hrefs2 & Hrefs3 & Hrefs4)".
    rewrite !shift_loc_assoc. wp_write. do 3 (wp_op; wp_write).
    iMod ("Hclosena" with "[H↦lrc H● Hν1 Hshr' H†] Hna") as "[Hβ Hna]".
    { iExists (Some (_, false, _, _)). rewrite Z.add_comm -Some_op -!pair_op agree_idemp.
      iFrame. iExists _. iFrame.
      rewrite (comm Qp_add) (assoc Qp_add) Qp_div_2 (comm Qp_add). auto. }
    iMod ("Hβclose" with "Hβ") as "Hα". iMod ("Hclose1" with "Hα HL") as "HL".
    iApply (type_type _ [_] _ [ #lrefs ◁ box (Π[ref α ty1; ref α ty2]) ]
       with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val' //= -freeable_sz_full.
      simpl. iFrame. iExists [_;_;_;_].
      rewrite 3!heap_mapsto_vec_cons heap_mapsto_vec_singleton !shift_loc_assoc.
      iFrame. iExists [_;_], [_;_]. iSplit=>//=.
      iSplitL "Hν H◯"; [by auto 10 with iFrame|]. iExists [_;_], [].
      iSplitR=>//=. rewrite right_id. auto 20 with iFrame. }
    iApply type_jump; solve_typing.
  Qed.
End ref_functions.
