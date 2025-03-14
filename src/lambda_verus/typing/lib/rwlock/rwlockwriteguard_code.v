From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.rwlock Require Import rwlock rwlockwriteguard.
Set Default Proof Using "Type".

Section rwlockwriteguard_functions.
  Context `{!typeG Σ, !rwlockG Σ}.

  (* Turning a rwlockwriteguard into a shared borrow. *)
  Definition rwlockwriteguard_deref : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" +ₗ #1 in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma rwlockwriteguard_deref_type ty :
    typed_val rwlockwriteguard_deref
      (fn(∀ '(α, β), ∅; &shr{α}(rwlockwriteguard β ty)) → &shr{α} ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']". destruct x' as [[|lx'|]|]; try done.
    iDestruct "Hx'" as (l') "#[Hfrac Hshr]".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "([Hα1 Hα2] & HL & Hclose)";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Hfrac Hα1") as (qlx') "[H↦ Hcloseα1]". done.
    rewrite heap_mapsto_vec_singleton.
    iMod (lctx_lft_alive_tok β with "HE HL") as (qβ) "(Hβ & HL & Hclose')";
      [solve_typing..|].
    iDestruct (lft_intersect_acc with "Hβ Hα2") as (qβα) "[Hα2β Hcloseβα2]".
    wp_bind (!(LitV lx'))%E. iApply (wp_step_fupd with "[Hα2β]");
         [|by iApply ("Hshr" with "[] Hα2β")|]; first done.
    iMod "H↦" as "[H↦1 H↦2]". wp_read. iIntros "[#Hshr' Hα2β]!>". wp_op. wp_let.
    iDestruct ("Hcloseβα2" with "Hα2β") as "[Hβ Hα2]".
    iMod ("Hcloseα1" with "[$H↦1 $H↦2]") as "Hα1". iMod ("Hclose'" with "Hβ HL") as "HL".
    iMod ("Hclose" with "[$] HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _ [ x ◁ box (&shr{α}(rwlockwriteguard β ty));
                              #(l' +ₗ 1) ◁ &shr{α}ty]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iApply (ty_shr_mono with "[] Hshr'"). iApply lft_incl_glb; first done.
        by iApply lft_incl_refl. }
    iApply (type_letalloc_1 (&shr{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Turning a rwlockwriteguard into a unique borrow. *)
  Definition rwlockwriteguard_derefmut : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      let: "r'" := !"x'" +ₗ #1 in
      letalloc: "r" <- "r'" in
      delete [ #1; "x"];; return: ["r"].

  Lemma rwlockwriteguard_derefmut_type ty :
    typed_val rwlockwriteguard_derefmut
      (fn(∀ '(α, β), ∅; &uniq{α}(rwlockwriteguard β ty)) → &uniq{α}ty).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x').
    iIntros (tid) "#LFT #HE Hna HL Hk HT". simpl_subst.
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx [#? Hx']]". destruct x' as [[|lx'|]|]; try done.
    iMod (bor_exists with "LFT Hx'") as (vl) "H". done.
    iMod (bor_sep with "LFT H") as "[H↦ H]". done.
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)"; [solve_typing..|].
    destruct vl as [|[[|l|]|][]];
      try by iMod (bor_persistent with "LFT H Hα") as "[>[] _]".
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_exists with "LFT H") as (γ) "H". done.
    iMod (bor_exists with "LFT H") as (δ) "H". done.
    iMod (bor_exists with "LFT H") as (tid_shr) "H". done.
    iMod (bor_sep with "LFT H") as "[Hb H]". done.
    iMod (bor_sep with "LFT H") as "[Hβδ H]". done.
    iMod (bor_sep with "LFT H") as "[Hβty _]". done.
    iMod (bor_persistent with "LFT Hβδ Hα") as "[#Hβδ Hα]". done.
    iMod (bor_persistent with "LFT Hβty Hα") as "[#Hβty Hα]". done.
    iMod (bor_acc with "LFT H↦ Hα") as "[H↦ Hcloseα]". done.
    wp_bind (!(LitV lx'))%E. iMod (bor_unnest with "LFT Hb") as "Hb"; first done.
    wp_read. wp_op. wp_let. iMod "Hb".
    iMod ("Hcloseα" with "[$H↦]") as "[_ Hα]". iMod ("Hclose" with "Hα HL") as "HL".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iApply (type_type _ _ _ [ x ◁ box (uninit 1); #(l +ₗ 1) ◁ &uniq{α}ty]
            with "[] LFT HE Hna HL Hk"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
      iFrame. iSplitR.
      - repeat iApply lft_incl_trans=>//.
      - iApply (bor_shorten with "[] Hb"). iApply lft_incl_glb.
          by iApply lft_incl_trans. by iApply lft_incl_refl. }
    iApply (type_letalloc_1 (&uniq{α}ty)); [solve_typing..|].
    iIntros (r). simpl_subst. iApply type_delete; [solve_typing..|].
    iApply type_jump; solve_typing.
  Qed.

  (* Drop a rwlockwriteguard and release the lock. *)
  Definition rwlockwriteguard_drop : val :=
    fn: ["x"] :=
      let: "x'" := !"x" in
      "x'" <-ˢᶜ #0;;
      delete [ #1; "x"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma rwlockwriteguard_drop_type ty :
    typed_val rwlockwriteguard_drop
              (fn(∀ α, ∅; rwlockwriteguard α ty) → unit).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iApply type_deref; [solve_typing..|]. iIntros (x'). simpl_subst.
    iIntros (tid) "#LFT #HE Hna HL Hk HT".
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val.
    iDestruct "HT" as "[Hx Hx']".
    destruct x' as [[|lx'|]|]; try done. simpl.
    iDestruct "Hx'" as (γ β tid_own) "(Hx' & #Hαβ & #Hβty & #Hinv & H◯)".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose)";
      [solve_typing..|].
    iMod (lft_incl_acc with "Hαβ Hα") as (qβ) "[Hβ Hcloseα]". done.
    wp_bind (#lx' <-ˢᶜ #0)%E.
    iMod (at_bor_acc_tok with "LFT Hinv Hβ") as "[INV Hcloseβ]"; [done..|].
    iDestruct "INV" as (st) "(H↦ & H● & INV)". wp_write.
    iMod ("Hcloseβ" with "[> H↦ H● H◯ INV Hx']") as "Hβ".
    { iDestruct (own_valid_2 with "H● H◯") as %[[[=]| (? & st0 & [=<-] & -> &
         [Heq|Hle])]%option_included Hv]%auth_both_valid_discrete;
      last by destruct (exclusive_included _ _ Hle).
      destruct st0 as [[[]|]| |]; try by inversion Heq.
      iExists None. iFrame. iMod (own_update_2 with "H● H◯") as "$"; last done.
      apply auth_update_dealloc. rewrite -(right_id None op (Some _)).
      apply cancel_local_update_unit, _. }
    iModIntro. wp_seq. iMod ("Hcloseα" with "Hβ") as "Hα".
    iMod ("Hclose" with "Hα HL") as "HL".
    iApply (type_type _ _ _ [ x ◁ box (uninit 1)]
            with "[] LFT HE Hna HL Hk"); first last.
    { rewrite tctx_interp_singleton tctx_hasty_val //. }
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply type_jump; solve_typing.
  Qed.
End rwlockwriteguard_functions.
