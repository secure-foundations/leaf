From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Open Scope Z_scope.

Section inc_max.
  Context `{!typeG Σ}.

  Definition take_max: val :=
    fn: ["oua"; "oub"] :=
      let: "ua" := !"oua" in let: "ub" := !"oub" in
      let: "a" := !"ua" in let: "b" := !"ub" in let: "ord" := "b" ≤ "a" in
      if: "ord" then
        "oua" <- "ua";; delete [ #1; "oub"];; return: ["oua"]
      else
        "oub" <- "ub";; delete [ #1; "oua"];; return: ["oub"].

  Lemma take_max_type :
    typed_val take_max (fn<α>(∅; &uniq{α} int, &uniq{α} int) → &uniq{α} int)
      (λ (post: pred' (_*_)) '-[(a, a'); (b, b')], if bool_decide (b ≤ a)
        then b' = b → post (a, a') else a' = a → post (b, b')).
  Proof.
    eapply type_fn; [apply _|]=>/= ???[?[?[]]]. simpl_subst. via_tr_impl.
    { do 2 (iApply type_deref; [solve_extract|solve_typing|done|]; intro_subst).
      do 2 (iApply type_deref; [solve_extract|solve_typing|done|]; intro_subst).
      iApply type_le; [solve_extract|]. intro_subst. via_tr_impl.
      { iApply type_if; [solve_extract| |];
        ( iApply type_assign; [solve_extract|solve_typing|solve_typing|];
          iApply type_delete; [solve_extract|done|done|];
          iApply type_jump; [solve_typing|solve_extract|solve_typing] ). }
      move=> ??/=. exact id. }
    by move=> ?[[??][[??][]]]/=.
  Qed.

  Definition inc_max: val :=
    fn: ["oa"; "ob"] := Newlft;;
      letalloc: "oua" <- "oa" in letalloc: "oub" <- "ob" in
      let: "take_max" := take_max in
      letcall: "ouc" := "take_max" ["oua"; "oub"] in
      let: "uc" := !"ouc" in let: "c" := !"uc" in let: "1" := #1 in
      let: "c'" := "c" + "1" in "uc" <- "c'";; Endlft;;
      let: "a" := !"oa" in let: "b" := !"ob" in
      let: "d" := "a" - "b" in letalloc: "od" <- "d" in
      delete [ #1; "oa"];; delete [ #1; "ob"];; return: ["od"].

  Lemma inc_max_type :
    typed_val inc_max (fn(∅; int, int) → int)
      (λ (post: pred' _) _, ∀n, n ≠ 0 → post n).
  Proof.
    eapply type_fn; [apply _|]=>/= _ ??[?[?[]]]. simpl_fp_E. simpl_subst.
    via_tr_impl.
    { iApply (type_newlft []). iIntros (α).
      do 2 (iApply (type_letalloc_1 (&uniq{α} _)); [solve_extract|done|]; intro_subst).
      iApply type_val; [apply take_max_type|]. intro_subst.
      iApply type_letcall; [solve_typing|solve_extract|solve_typing|].
      intro_subst. via_tr_impl.
      { do 2 (iApply type_deref; [solve_extract|solve_typing|done|]; intro_subst).
        iApply type_int. intro_subst. iApply type_plus; [solve_extract|]. intro_subst.
        iApply type_assign; [solve_extract|solve_typing|solve_typing|]. via_tr_impl.
        { iApply type_endlft; [solve_resolve_unblock|solve_typing|].
          do 2 (iApply type_deref; [solve_extract|solve_typing|done|]; intro_subst).
          iApply type_minus; [solve_extract|]. intro_subst.
          iApply type_letalloc_1; [solve_extract|done|]. intro_subst.
          do 2 (iApply type_delete; [solve_extract|done|done|]).
          iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
        move=> ??/=. exact id. }
      move=> ??/=. exact id. }
    move=> ?[a[b[]]] Imp ??/=.
    case Le: (bool_decide (b ≤ a))=> ->->; apply Imp; move: Le;
    [rewrite bool_decide_eq_true|rewrite bool_decide_eq_false]; lia.
  Qed.
End inc_max.
