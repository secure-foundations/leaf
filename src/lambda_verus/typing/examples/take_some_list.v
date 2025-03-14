From lrust.typing Require Import typing lib.list lib.loop lib.gfp.
Set Default Proof Using "Type".

Open Scope Z_scope.
Implicit Type 𝔄: syn_type.

Section take_some_list.
  Context `{!typeG Σ}.

  Definition take_some_list {𝔄} (ty: type 𝔄) : val :=
    fnrec: "take_some_list" ["box"] :=
      let: "ula" := !"box" in
      case: !"ula" of
      [ inf_loop
      ; let: "uca" := "ula" +ₗ #1 in
        let: "b" := NdBool in
        if: "b" then
          "box" <- "uca" +ₗ #0;; return: ["box"]
        else
          let: "ula'" := !("uca" +ₗ #ty.(ty_size)) in
          "box" <- "ula'";; letcall: "box'" := "take_some_list" ["box"] in
          return: ["box'"]].

  Definition take_some_list_tr {𝔄}
      : predl_trans'_map [listₛ 𝔄 * listₛ 𝔄]%ST (𝔄 * 𝔄)%ST :=
    λ tr post '-[(al, al')], match al, al' with
      | [], _ | _::_, [] => True
      | a :: al2, a' :: al2' =>
          (al2' = al2 → post (a, a')) ∧ (tr (λ b, a' = a → post b) -[(al2, al2')])
      end.

  Global Instance take_some_list_tr_mono {𝔄} : MonoTrans'Map (@take_some_list_tr 𝔄).
  Proof.
    move=> ?? Imp ?[[[|??][|??]][]]//=. move=> [? Post]. split; [done|].
    by apply Imp, Post.
  Qed.

  Lemma take_some_list_type {𝔄} (ty: type 𝔄) :
    typed_val (take_some_list ty) (fn<α>(∅; &uniq{α} (list_ty ty)) → &uniq{α} ty)
      (trans'_gfp take_some_list_tr).
  Proof.
    eapply type_fnrec; [apply _|]=>/= α ???[?[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
      iApply (type_case_uniq_inner +[_;_] -[_;_]); [solve_extract|solve_typing|].
      rewrite/= right_id. iSplitL; [iApply type_inf_loop|].
      iApply type_letpath; [solve_extract|]. intro_subst.
      iApply type_nd_bool. intro_subst. via_tr_impl.
      { iApply type_if; [solve_extract|..].
        - iApply type_assign; [solve_extract|solve_typing..|]=>/=.
          iApply type_jump; [solve_typing|solve_extract|solve_typing].
        - iApply type_deref_uniq_own; [solve_extract|solve_typing|]. intro_subst.
          iApply type_assign; [solve_extract|solve_typing..|]=>/=. via_tr_impl.
          { iApply (type_letcall α); [solve_typing|solve_extract|solve_typing|].
            intro_subst. iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
          move=>/= ??. exact id. }
      move=>/= ??. exact id. }
    move=>/= ?[?[[[|??][|??]][]]]//=. move=> [-> gfp].
    apply trans'_gfp_unfold in gfp; [|apply _]. move: gfp=> [??].
    by move=> [??][=<-<-][|].
  Qed.
End take_some_list.
