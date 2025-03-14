From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section init_prod.
  Context `{!typeG Σ}.

  Definition init_prod: val :=
    fn: ["x"; "y"] :=
      let: "x'" := !"x" in let: "y'" := !"y" in
      let: "r" := new [ #2] in
      "r" +ₗ #0 <- "x'";; "r" +ₗ #1 <- "y'";;
      delete [ #1; "x"];; delete [ #1; "y"];; return: ["r"].

  Lemma init_prod_type:
    typed_val init_prod (fn(∅; int, int) → int * int)
      (λ post '-[z; z'], post (z, z')).
  Proof.
    eapply type_fn; [apply _|]=> _ ??[?[?[]]]. simpl_subst. via_tr_impl.
    { do 2 (iApply type_deref; [solve_extract|solve_typing|done|]; intro_subst).
      iApply (type_new_subtype (↯ 1 * ↯ 1)); [done|solve_typing|].
      intro_subst. have ->: Z.to_nat 2 = 2%nat by done.
      iApply type_assign; [solve_extract|solve_typing|solve_typing|].
      iApply type_assign; [solve_extract|solve_typing|solve_typing|].
      do 2 (iApply type_delete; [solve_extract|done|done|]).
      iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=> ?[?[?[]]]/=.
  Qed.
End init_prod.
