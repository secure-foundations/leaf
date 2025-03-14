From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Open Scope Z_scope.

Section odd_sum.
  Context `{!typeG Σ}.

  Definition odd_sum: val :=
    fnrec: "odd_sum" ["ba"] :=
      let: "a" := !"ba" in let: "0" := #0 in let: "a≤0" := "a" ≤ "0" in
      if: "a≤0" then
        "ba" <- "0";; return: ["ba"]
      else
        let: "1" := #1 in let: "a-1" := "a" - "1" in "ba" <- "a-1";;
        letcall: "br" := "odd_sum" ["ba"] in
        let: "r" := !"br" in let: "2a-1" := "a-1" + "a" in
        let: "r'" := "r" + "2a-1" in "br" <- "r'";;
        return: ["br"].

  Lemma odd_sum_type :
    typed_val odd_sum (fn(∅; int) → int)
      (λ post '-[z], let z' := 0 `max` z in post (z' * z')).
  Proof.
    eapply type_fnrec; [apply _|]=>/= _ ???[?[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
      iApply type_int. intro_subst. iApply type_le; [solve_extract|].
      intro_subst. iApply type_if; [solve_extract| |].
      - iApply type_assign; [solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - iApply type_int. intro_subst. iApply type_minus; [solve_extract|].
        intro_subst. iApply type_assign; [solve_extract|solve_typing..|].
        via_tr_impl.
        { iApply (type_letcall ()); [solve_typing|solve_extract|solve_typing|].
          intro_subst. iApply type_deref; [solve_extract|solve_typing..|].
          intro_subst. iApply type_plus; [solve_extract|]. intro_subst.
          iApply type_plus; [solve_extract|]. intro_subst.
          iApply type_assign; [solve_extract|solve_typing..|].
          iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
        move=>/= ??. exact id. }
    move=>/= ?[?[z[]]][-> Post]. case Le: (bool_decide (z ≤ 0)); move: Post;
    move: Le; [rewrite bool_decide_eq_true|rewrite bool_decide_eq_false]=> ??;
    (eapply eq_ind; [done|]); [lia|]. have ->: 0 `max` (z - 1) = z - 1; lia.
  Qed.
End odd_sum.
