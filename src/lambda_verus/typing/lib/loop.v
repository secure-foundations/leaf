From lrust.typing Require Import typing.

Notation inf_loop :=
  (letcont: (BNamed "inf_loop") [] :=
    jump: (Var "inf_loop") [] in jump: (Var "inf_loop") [])%E.

Section loop.
  Context `{!typeG Σ}.

  Lemma type_inf_loop {𝔄l 𝔅} E L (C: cctx 𝔅) (T: tctx 𝔄l) :
    ⊢ typed_body E L C T inf_loop (λ _ _, True)%type.
  Proof.
    iApply (type_cont [] (λ _, +[]) (λ _ _, True) L).
    { intro_subst. via_tr_impl.
      { iApply (type_jump (λ _, +[]));
          [solve_typing|apply tctx_incl_refl|apply resolve_tctx_just]. }
      done. }
    iIntros "!>" (? v). inv_vec v. simpl_subst. via_tr_impl.
    { iApply (type_jump (λ _, +[]));
      [solve_typing|apply tctx_incl_refl|apply resolve_tctx_just]. }
    done.
  Qed.
End loop.
