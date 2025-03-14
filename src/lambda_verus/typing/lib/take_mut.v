From iris.proofmode Require Import proofmode.
From lrust.lang.lib Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section code.
  Context `{!typeG Σ}.

  Definition take ty (call_once : val) : val :=
    fn: ["x"; "f"] :=
      let: "x'" := !"x" in
      let: "call_once" := call_once in
      letalloc: "t" <-{ty.(ty_size)} !"x'" in
      letcall: "r" := "call_once" ["f"; "t"]%E in
      "x'" <-{ty.(ty_size)} !"r";;
      delete [ #1; "x"];;  delete [ #ty.(ty_size); "r"];;
      let: "r" := new [ #0] in return: ["r"].

  Lemma take_type ty fty call_once :
    (* fty : FnOnce(ty) -> ty, as witnessed by the impl call_once *)
    typed_val call_once (fn(∅; fty, ty) → ty) →
    typed_val (take ty call_once) (fn(∀ α, ∅; &uniq{α} ty, fty) → unit).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret arg).
      inv_vec arg=>x env. simpl_subst.
    iApply type_deref; [solve_typing..|]; iIntros (x'); simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]; iIntros (f'); simpl_subst.
    iApply (type_new ty.(ty_size)); [solve_typing..|]; iIntros (t); simpl_subst.
    (* Switch to Iris. *)
    iIntros (tid) "#LFT #TIME #HE Hna HL Hk (Ht & Hf' & Hx & Hx' & Henv & _)".
    rewrite !tctx_hasty_val [[x]]lock [[env]]lock [fn _]lock.
    iDestruct "Hx'" as (depthx) "[Hdepthx Hx']". iDestruct "Hx'" as "[#Houtx Hx']".
    iDestruct "Ht" as (deptht) "[Hdeptht Ht]".
    iDestruct (ownptr_uninit_own with "Ht") as (tl tvl) "(% & % & >Htl & Htl†)". subst t. simpl.
    destruct x' as [[|lx'|]|], depthx as [|depthx]=>//=.
    iDestruct "Hx'" as (depthx' γ ?) "[H◯ Hx']".
    iMod (lctx_lft_alive_tok α with "HE HL") as (qα) "(Hα & HL & Hclose1)"; [solve_typing..|].
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (qϝ) "(Hϝ & HL & Hclose2)"; [solve_typing..|].
    iMod (bor_acc with "LFT Hx' Hα") as "[Hx' Hclose3]"; first done.
    iDestruct "Hx'" as (depthx'') "(H● & Hdepthx'' & Hx')".
    iDestruct (heap_mapsto_ty_own with "Hx'") as (x'vl) "[>Hx'↦ Hx'vl]".
    wp_apply (wp_memcpy with "[$Htl $Hx'↦]"); [by auto using vec_to_list_length..|].
    iIntros "[Htl Hx'↦]". wp_seq.
    (* Call the function. *)
    wp_let. unlock.
    iDestruct "Hf'" as (?) "[_ Hf']".
    iApply (type_call_iris _ [ϝ] () [_; _]
      with "LFT TIME HE Hna [Hϝ] Hf' [Henv Htl Htl† Hx'vl Hdepthx'']"); [solve_typing| | |].
    { by rewrite /= (right_id static). }
    { rewrite /= !tctx_hasty_val tctx_hasty_val' //. iFrame. iSplitL; [|done].
      iExists _. iFrame. iExists _. iFrame. }
    (* Prove the continuation of the function call. *)
    iIntros (r depth') "Hna Hϝ Hdepth' Hr". simpl.
    iDestruct (ownptr_own with "Hr") as (lr rvl) "(% & % & Hlr & Hrvl & Hlr†)". subst r.
    wp_rec.
    rewrite (right_id static). destruct depth'; [lia|].
    wp_apply (wp_memcpy with "[$Hx'↦ $Hlr]"); [by auto using vec_to_list_length..|].
    iIntros "[Hlx' Hlr]". wp_seq.
    iMod (own_update_2 with "H● H◯") as "[H● H◯]"; [by apply excl_auth_update|].
    iMod ("Hclose3" with "[Hlx' Hrvl Hdepth' H●]") as "[Hlx' Hα]".
    { iExists _. iFrame. iExists _. iFrame. }
    iMod ("Hclose2" with "Hϝ HL") as "HL".
    iMod ("Hclose1" with "Hα HL") as "HL".
    (* Finish up the proof. *)
    iApply (type_type _ _ _ [ x ◁ _; #lr ◁ box (uninit ty.(ty_size)) ]
        with "[] LFT TIME HE Hna HL Hk [-]"); last first.
    { rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val tctx_hasty_val' //.
      unlock. iFrame. iExists (S depthx). iFrame. iExists _.
      rewrite uninit_own. iFrame. auto using vec_to_list_length. }
    iApply type_delete; [solve_typing..|].
    iApply type_delete; [solve_typing..|].
    iApply type_new; [solve_typing..|]; iIntros (r); simpl_subst.
    iApply type_jump; solve_typing.
  Qed.
End code.
