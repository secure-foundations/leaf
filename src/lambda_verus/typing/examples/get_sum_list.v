From lrust.typing Require Import typing lib.list.
Set Default Proof Using "Type".

Open Scope Z_scope.
Implicit Type 𝔄: syn_type.

Section get_sum_list.
  Context `{!typeG Σ}.

  Definition get_sum_list: val :=
    fnrec: "get_sum_list" ["box"] :=
      let: "sla" := !"box" in
      case: !"sla" of
      [ let: "0" := #0 in "box" <- "0";; return: ["box"]
      ; let: "sca" := "sla" +ₗ #1 in
        let: "a" := !("sca" +ₗ #0) in
        let: "sla'" := !("sca" +ₗ #1) in
        "box" <- "sla'";; letcall: "box'" := "get_sum_list" ["box"] in
        let: "b" := !"box'" in let: "a+b" := "a" + "b" in
        "box'" <- "a+b";; return: ["box'"]].

  Definition sum_listZ (la: list Z) : Z := foldr Z.add 0 la.

  Lemma get_sum_list_type :
    typed_val get_sum_list (fn<α>(∅; &shr{α} (list_ty int)) → int)
      (λ post '-[la], post (sum_listZ la)).
  Proof.
    eapply type_fnrec; [apply _|]=>/= α ???[?[]]. simpl_subst. simpl_fp_E. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
      iApply (type_case_shr_inner +[_;_] -[_;_]); [solve_extract|solve_typing|].
      rewrite/= right_id. iSplitL.
      - iApply type_int. intro_subst.
        iApply type_assign; [solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - iApply type_letpath; [solve_extract|]. intro_subst.
        iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
        iApply type_deref_shr_own; [solve_extract|solve_typing|]. intro_subst.
        iApply type_assign; [solve_extract|solve_typing..|]. via_tr_impl.
        { iApply (type_letcall α); [solve_typing|solve_extract|solve_typing|].
          intro_subst. iApply type_deref; [solve_extract|solve_typing..|].
          intro_subst. iApply type_plus; [solve_extract|]. intro_subst.
          iApply type_assign; [solve_extract|solve_typing..|].
          iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
        move=>/= ??. exact id. }
    move=>/= ?[?[[|??][]]][??]//=. by subst.
  Qed.
End get_sum_list.
