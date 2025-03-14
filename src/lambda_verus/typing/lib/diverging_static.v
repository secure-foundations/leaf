From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section diverging_static.
  Context `{!typeG Σ}.

  (* Show that we can convert any live borrow to 'static with an infinite
     loop. *)
  Definition diverging_static_loop (call_once : val) : val :=
    fn: ["x"; "f"] :=
      let: "call_once" := call_once in
      letcall: "ret" := "call_once" ["f"; "x"]%E in
    withcont: "loop":
      "loop" []
    cont: "loop" [] :=
      "loop" [].

  Lemma diverging_static_loop_type T F call_once :
    (* F : FnOnce(&'static T), as witnessed by the impl call_once *)
    typed_val call_once (fn(∅; F, &shr{static} T) → unit) →
    typed_val (diverging_static_loop call_once)
              (fn(∀ α, λ ϝ, ty_outlives_E T static; &shr{α} T, F) → ∅).
  Proof.
    intros Hf E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros (α ϝ ret arg). inv_vec arg=>x f. simpl_subst.
    iApply type_let; [apply Hf|solve_typing|]. iIntros (call); simpl_subst.
    (* Drop to Iris *)
    iIntros (tid) "#LFT #TIME #HE Hna HL Hk (Hcall & Hx & Hf & _)".
    (* We need a ϝ token to show that we can call F despite it being non-'static. *)
    iMod (lctx_lft_alive_tok ϝ with "HE HL") as (qϝ) "(Hϝ & HL & _)";
      [solve_typing..|].
    iMod (lctx_lft_alive_tok α with "HE HL") as (q) "(Hα & _ & _)";
      [solve_typing..|].
    iMod (lft_eternalize with "Hα") as "#Hα".
    iAssert (type_incl (box (&shr{α} T)) (box (&shr{static} T))) as "#[_ [_ [Hincl _]]]".
    { iApply box_type_incl. iApply shr_type_incl; first done.
      iApply type_incl_refl. }
    wp_let. rewrite (tctx_hasty_val _ call). iDestruct "Hcall" as (?) "[_ Hcall]".
    iApply (type_call_iris _ [ϝ] () [_; _] with "LFT TIME HE Hna [Hϝ] Hcall [Hx Hf]").
    - solve_typing.
    - by rewrite /= (right_id static).
    - simpl. iFrame. iSplit; last done. rewrite !tctx_hasty_val.
      iDestruct "Hx" as (?) "[??]". iExists _. iFrame. iApply "Hincl". done.
    - iClear "Hα Hincl". iIntros (r depth') "Htl Hϝ1 Hdepth Hret". wp_rec.
      (* Go back to the type system. *)
      iApply (type_type _ [] _ [] with "[] LFT TIME HE Htl [] Hk [-]"); last first.
      { rewrite /tctx_interp /=. done. }
      { rewrite /llctx_interp /=. done. }
      iApply (type_cont [] [] (λ _, [])).
      + iIntros (?). simpl_subst. iApply type_jump; solve_typing.
      + iIntros "!>" (? args). inv_vec args. simpl_subst. iApply type_jump; solve_typing.
  Qed.
End diverging_static.
