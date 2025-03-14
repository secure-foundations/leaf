From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section rebor.
  Context `{!typeG Σ}.

  Definition rebor : val :=
    fn: ["t1"; "t2"] :=
      Newlft;;
      letalloc: "x" <- "t1" in
      let: "x'" := !"x" in let: "y" := "x'" +ₗ #0 in
      "x" <- "t2";;
      let: "y'" := !"y" in
      letalloc: "r" <- "y'" in
      delete [ #1; "x"];; Endlft;;
      delete [ #2; "t1"];; delete [ #2; "t2"];; return: ["r"].

  Lemma rebor_type :
    typed_val rebor (fn(∅; int * int, int * int) → int)
      (λ post '-[(z, _); _], post z).
  Proof.
    eapply type_fn; [apply _|]=> _??[?[?[]]]. simpl_subst. via_tr_impl.
    { iApply (type_newlft []). iIntros (α).
      iApply (type_letalloc_1 (&uniq{α} (int * int))); [solve_extract|done|].
      intro_subst. iApply type_deref; [solve_extract|solve_typing|done|].
      intro_subst. iApply (type_letpath (&uniq{α} int)); [solve_extract|].
      intro_subst. iApply (type_assign _ _ _ (&uniq{α} (int * int)));
        [solve_extract|solve_typing|solve_typing|].
      iApply type_deref; [solve_extract|solve_typing|done|]. intro_subst.
      iApply type_letalloc_1; [solve_extract|done|]. intro_subst.
      iApply type_delete; [solve_extract|done|done|]. via_tr_impl.
      { iApply type_endlft; [solve_resolve_unblock|solve_typing|].
        do 2 (iApply type_delete; [solve_extract|done|done|]).
        iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
      move=>/= ??. exact id. }
    by move=>/= ?[[??][?[]]]?[??]_ _ _.
  Qed.
End rebor.
