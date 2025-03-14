From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
From lrust.typing.lib.vec Require Import vec vec_slice.
From lrust.typing.lib.slice Require Import slice iter.
Set Default Proof Using "Type".

Section code.
  Context `{!typeG Σ}.

  Definition inc_vec : val :=
    fn: ["v"] :=
      let: "iter_mut" := vec_as_slice in
      letcall: "it" := "iter_mut" ["v"] in
      withcont: "k":
        withcont: "loop":
          jump: "loop" []
        cont: "loop" [] :=
          let: "next" := iter_next int in
          Newlft;;
          letalloc: "bit" <- "it" in
          letcall: "e" := "next" ["bit"] in
          Endlft;;
          case: !"e" of
          [ jump: "k" []
          ; let: "i" := !("e" +ₗ #1) in
            let: "i1" := ! "i" in
            let: "5" := #5 in
            let: "i2" := "i1" + "5" in
            "i" <- "i2" ;;
            jump: "loop" []
          ]
      cont: "k" [] :=
        delete [ #2; "it" ] ;;
        let: "r" := new [ #0] in
        return: [ "r" ].

  Lemma inc_vec_type :
    typed_val inc_vec (fn<α>(∅; &uniq{α} (vec_ty int)) → ())
      (λ post '-[(v, v')], v' = map (λ e, e + 5) v → post ()).
  Proof.
    eapply type_fn; [apply _|]=>/= α ϝ ret [v[]]. simpl_subst. via_tr_impl.
    { iApply type_val; [apply (vec_as_uniq_slice_type int)|]. intro_subst.
      iApply type_letcall; [solve_typing|solve_extract|solve_typing|..].
      iIntros (iter). simpl_subst.
      iApply (type_cont [] (λ _, +[iter ◁ _]) (λ (post : ()%ST → _) _, post ())).
      intro_subst.
      iApply (type_cont [] (λ _, +[iter ◁ box (uniq_slice _ int)])
        (λ (post : ()%ST → Prop) '-[v],
          foldr (λ '(a, a') (b : Prop), a' = a + 5 → b) (post ()) v)).
      - intro_subst.
        iApply (type_jump (λ _, +[iter ◁ box (uniq_slice _ int)]));
          [solve_typing|solve_extract|solve_typing|..].
      - iModIntro. iIntros (? ?). inv_vec vl. simpl_subst. via_tr_impl.
        { iApply type_val; [apply iter_uniq_next_type|]. intro_subst.
          iApply type_newlft. iIntros (γ).
          iApply (type_letalloc_1 (&uniq{γ} _)); [solve_extract| solve_typing |..].
          intro_subst.
          iApply (type_letcall (_, γ)); [solve_typing|solve_extract|solve_typing|..].
          intro_subst.
          (* why do we need to rewrite static? *)
          iApply type_endlft; [solve_resolve_unblock| solve_typing | .. ].
          iApply (type_case_own_inner +[_; _] -[_; _]); [solve_extract|..].
          rewrite/= right_id. iSplitL.
          + iApply (type_jump (λ _, +[_])); [solve_typing| solve_extract| solve_typing].
          + iApply type_deref; [solve_extract|solve_typing|solve_typing|..]. intro_subst.
            iApply type_deref; [solve_extract|solve_typing|solve_typing|..]. intro_subst.
            iApply type_int. intro_subst.
            iApply type_plus; [solve_extract|..]. intro_subst.
            iApply type_assign; [solve_typing|solve_typing|solve_typing|..].
            iApply (type_jump (λ _, +[iter ◁ box (uniq_slice _ int)]));
              [solve_typing|solve_extract|solve_typing|..]. }
        move=>/= ? [[|[??]?] []] //= ?? -> //=.
    - iModIntro. iIntros (? vl) "/=". inv_vec vl. simpl_subst. via_tr_impl.
      { iApply type_delete; [solve_extract|solve_typing|solve_typing|].
        iApply type_new; [solve_typing|]. intro_subst.
        iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
      move => /= ?[? []] //. }
    move => /= ? [[al +] []]. induction al.
    - move => ?. by rewrite length_zero_iff_nil.
    - case; naive_solver.
  Qed.
End code.
