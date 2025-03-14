From lrust.typing Require Import typing lib.list.
Set Default Proof Using "Type".

Open Scope Z_scope.
Implicit Type 𝔄: syn_type.

Section split_uniq_list.
  Context `{!typeG Σ}.

  Definition split_uniq_list {𝔄} (ty: type 𝔄) : val :=
    fnrec: "split_uniq_list" ["bula"] :=
      let: "ula" := !"bula" in delete [ #1; "bula"];;
      let: "r" := new [ #3] in
      case: !"ula" of
      [ "r" <-{Σ 0} ();; return: ["r"]
      ; let: "uca" := "ula" +ₗ #1 in
        let: "c" := new [ #2] in
        "c" +ₗ #0 <- "uca" +ₗ #0;;
        let: "ula'" := !("uca" +ₗ #ty.(ty_size)) in
        letalloc: "bula'" <- "ula'" in
        letcall: "blua'" := "split_uniq_list" ["bula'"] in
        "c" +ₗ #1 <- "blua'";;
        "r" <-{2,Σ 1} !"c";; return: ["r"]].

  Lemma split_uniq_list_type {𝔄} (ty: type 𝔄) :
    typed_val (split_uniq_list ty)
      (fn<α>(∅; &uniq{α} (list_ty ty)) → list_ty (&uniq{α} ty))
      (λ post '-[(la, la')], length la' = length la → post (zip la la')).
  Proof.
    eapply type_fnrec; [apply _|]=>/= α ϝ ??[?[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
      iApply type_delete; [solve_extract|done..|].
      iApply type_new; [done|]. intro_subst.
      iApply (type_case_uniq_inner +[_;_] -[_;_]); [solve_extract|solve_typing|].
      iSplitL; [|iSplitL; [|done]].
      - iApply (type_sum_unit +[(); list_cons_ty (&uniq{_} _)]%T 0%fin);
          [done|solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - iApply type_letpath; [solve_extract|]. intro_subst.
        iApply (type_new_subtype (↯ 1 * ↯ 1)); [solve_typing..|]. intro_subst.
        iApply type_assign; [solve_extract|solve_typing..|].
        iApply type_deref_uniq_own; [solve_extract|solve_typing|]. intro_subst.
        iApply type_letalloc_1; [solve_extract|done|]. intro_subst. via_tr_impl.
        { iApply (type_letcall α); [solve_typing|solve_extract|solve_typing|].
          intro_subst. iApply type_assign; [solve_extract|solve_typing..|]. via_tr_impl.
          { (* FIXME: [solve_extract] doesn't work here. *)
            iApply (type_sum_memcpy +[()%T; list_cons_ty (&uniq{α} ty)] 1%fin
              _ (own_ptr 2 (list_cons_ty (&uniq{α} ty))));
              [done|eapply tctx_extract_ctx_elt; solve_typing|solve_typing..|].
            iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
          move=>/= ??. exact id. }
        move=>/= ??. exact id. }
    move=>/= ?[?[[[|??]al'][]]]/=.
    - move=> [_ +][]. case al'=>// Post _ _. by apply Post.
    - move=> [->+]. case al'=>//= ?? Post [??][=<-<-]?. apply Post. by f_equal.
    (* FIXME: The last QED check takes ~80 seconds. *)
  Qed.
End split_uniq_list.
