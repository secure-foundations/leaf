From lrust.typing Require Import typing lib.cell.
Set Default Proof Using "Type".

Open Scope Z_scope.

Section inc_cell.
  Context `{!typeG Σ}.

  Definition inc_cell: val :=
    fn: ["bc"; "bi"] :=
      let: "c" := !"bc" in let: "i" := !"bi" in delete [ #1; "bi"];;
      let: "cell_get" := cell_get int in
      letcall: "ba" := "cell_get" ["bc"] in
      let: "a" := !"ba" in
      let: "a+i" := "a" + "i" in "ba" <- "a+i";;
      letalloc: "bc" <- "c" in
      let: "cell_set" := cell_set int in
      letcall: "bu" := "cell_set" ["bc"; "ba"] in
      return: ["bu"].

  Lemma inc_cell_type :
    typed_val inc_cell (fn<α>(∅; &shr{α} (cell int), int) → ())
      (λ post '-[Φ; i], (∀z, Φ z → Φ (z + i)) ∧ post ()).
  Proof.
    eapply type_fn; [apply _|]=>/= ???[?[?[]]]. simpl_subst. via_tr_impl.
    { do 2 (iApply type_deref; [solve_extract|solve_typing|done|]; intro_subst).
      iApply type_delete; [solve_extract|done..|].
      iApply type_val; [apply cell_get_type, _|]. intro_subst.
      iApply type_letcall; [solve_typing|solve_extract|solve_typing|]. intro_subst.
      iApply type_deref; [solve_extract|solve_typing|done|]. intro_subst.
      iApply type_plus; [solve_extract|]. intro_subst.
      iApply type_assign; [solve_extract|solve_typing..|].
      iApply type_letalloc_1; [solve_extract|solve_typing|]. intro_subst. via_tr_impl.
      { iApply type_val; [apply cell_set_type|]. intro_subst.
        iApply type_letcall; [solve_typing|solve_extract|solve_typing|]. intro_subst.
        iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
      move=>/= ??. exact id. }
    move=> ?[?[?[]]]/= [Imp ?]??. split; by [apply Imp|].
  Qed.

  Definition inc_cell_repeat: val :=
    fnrec: "inc_cell_repeat" ["bc"; "bi"] :=
      let: "b" := NdBool in
      if: "b" then
        let: "bu" := new [ #0] in
        return: ["bu"]
      else
        let: "c" := !"bc" in let: "i" := !"bi" in
        let: "inc_cell" := inc_cell in
        letcall: "bu" := "inc_cell" ["bc"; "bi"] in delete [ #0; "bu"];;
        letalloc: "bc" <- "c" in letalloc: "bi" <- "i" in
        letcall: "bu" := "inc_cell_repeat" ["bc"; "bi"] in
        return: ["bu"].

  Lemma inc_cell_repeat_type :
    typed_val inc_cell_repeat (fn<α>(∅; &shr{α} (cell int), int) → ())
      (λ post '-[Φ; i], (∀z, Φ z → Φ (z + i)) ∧ post ()).
  Proof.
    eapply type_fnrec; [apply _|]=>/= ????[?[?[]]]. simpl_subst. via_tr_impl.
    { iApply type_nd_bool. intro_subst. iApply type_if; [solve_extract|..].
      { iApply (type_new_subtype ()%T); [solve_typing..|]. intro_subst.
        iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
      do 2 (iApply type_deref; [solve_extract|solve_typing|done|]; intro_subst).
      iApply type_val; [apply inc_cell_type|]. intro_subst.
      iApply type_letcall; [solve_typing|solve_extract|solve_typing|]. intro_subst.
      iApply type_delete; [solve_extract|done..|].
      do 2 (iApply type_letalloc_1; [solve_extract|solve_typing|]; intro_subst).
      via_tr_impl.
      { iApply type_letcall; [solve_typing|solve_extract|solve_typing|]. intro_subst.
        iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
      move=>/= ??. exact id. }
    move=> ?[?[?[?[]]]]/=[->[Imp ?]]. by case.
  Qed.

  Definition inc_cell_use: val :=
    fn: ["bi"] :=
      let: "a" := #0 in letalloc: "ba" <- "a" in Skip;;
      let: "cell_new" := cell_new in
      letcall: "bc" := "cell_new" ["ba"] in
      Newlft;;
      let: "sc" := "bc" in Share;;
      letalloc: "bsc" <- "sc" in
      let: "inc_cell_repeat" := inc_cell_repeat in
      letcall: "bu" := "inc_cell_repeat" ["bsc"; "bi"] in
      delete [ #0; "bu"];;
      Endlft;;
      let: "cell_into_inner" := cell_into_inner in
      letcall: "ba" := "cell_into_inner" ["bc"] in
      return: ["ba"].

  Lemma inc_cell_use_type :
    typed_val inc_cell_use (fn(∅; int) → int)
      (λ post '-[i], ∀z, (∃k, z = k * i) → post z).
  Proof.
    eapply type_fn; [apply _|]=>/= ???[bi[]]. simpl_subst. via_tr_impl.
    { iApply type_int. intro_subst.
      iApply type_letalloc_1; [solve_extract|solve_typing|]. intro_subst.
      iApply (type_dep +[bi ◁ box int]); [solve_extract|solve_typing|].
      iIntros (i'). via_tr_impl.
      { iApply type_val; [eapply (cell_new_type int (λ z, ∃k, z = k * phd i'))|].
        intro_subst. iApply (type_letcall ()); [solve_typing|solve_extract|solve_typing|].
        intro_subst. iApply type_newlft. iIntros (α).
        iApply (type_letpath (&uniq{α} _)); [solve_extract|]. intro_subst.
        iApply type_share; [solve_extract|solve_typing|].
        iApply type_letalloc_1; [solve_extract|solve_typing|]. intro_subst.
        iApply type_val; [apply inc_cell_repeat_type|]. intro_subst.
        iApply type_letcall; [solve_typing|solve_extract|solve_typing|]. intro_subst.
        iApply type_delete; [solve_extract|done..|]. via_tr_impl.
        { iApply type_endlft; [solve_resolve_unblock|solve_typing|].
          iApply type_val; [eapply cell_into_inner_type|]. intro_subst.
          iApply (type_letcall ()); [solve_typing|solve_extract|solve_typing|].
          intro_subst. iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
        move=>/= ??. exact id. }
      move=>/= ??. exact id. }
    move=> ?[?[]]/= Imp. split. { exists 0. lia. }
    move=> ?->. split; [|done]=> ?[k ->]. exists (k + 1). lia.
  Qed.
End inc_cell.
