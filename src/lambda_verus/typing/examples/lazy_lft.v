From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section lazy_lft.
  Context `{!typeG Σ}.

  Definition lazy_lft: val :=
    fn: [] :=
      Newlft;;
      let: "t" := new [ #2] in let: "f" := new [ #1] in let: "g" := new [ #1] in
      let: "42" := #42 in "f" <- "42";;
      Share;; "t" +ₗ #0 <- "f";; "t" +ₗ #1 <- "f";;
      let: "t0'" := !("t" +ₗ #0) in "t0'";;
      let: "23" := #23 in "g" <- "23";;
      Share;; "t" +ₗ #1 <- "g";;
      delete [ #2; "t"];; Endlft;;
      let: "r" := new [ #0] in
      delete [ #1; "f"];; delete [ #1; "g"];; return: ["r"].

  Lemma lazy_lft_type : typed_val lazy_lft (fn(∅) → ()) (λ post _, post ()).
  Proof.
    eapply type_fn; [apply _|]=> _??[]. simpl_subst. via_tr_impl.
    { iApply (type_newlft []). iIntros (α).
      iApply (type_new_subtype (↯ 1 * ↯ 1)); [done|solve_typing|]. intro_subst.
      iApply type_new; [done|]. intro_subst_as f. iApply type_new; [done|].
      intro_subst_as g. iApply type_int. intro_subst.
      iApply type_assign; [solve_extract|solve_typing|solve_typing|]. via_tr_impl.
      { iApply (type_share f α); [solve_extract|solve_typing|].
        do 2 (iApply type_assign; [solve_extract|solve_typing|solve_typing|]).
        iApply type_deref; [solve_extract|solve_typing|done|]. intro_subst.
        iApply type_letpath; [solve_extract|]. intro_subst. iApply type_int.
        intro_subst. iApply type_assign; [solve_extract|solve_typing|solve_typing|].
        via_tr_impl.
        { iApply (type_share g α); [solve_extract|solve_typing|].
          iApply type_assign; [solve_extract|solve_typing|solve_typing|].
          iApply (type_delete (&shr{α} int * &shr{α} int)); [solve_extract|done|done|].
          via_tr_impl.
          { iApply type_endlft; [solve_resolve_unblock|solve_typing|].
            iApply (type_new_subtype ()); [done|solve_typing|].
            intro_subst. do 2 (iApply type_delete; [solve_extract|done|done|]).
            iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
          move=> ??/=. exact id. }
        move=> ??/=. exact id. }
      move=> ??/=. exact id. }
    by move=> ?[]? _ _ _ _/=.
  Qed.
End lazy_lft.
