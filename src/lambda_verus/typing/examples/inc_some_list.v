From lrust.typing Require Import typing lib.list lib.gfp
  examples.get_sum_list examples.take_some_list.
Set Default Proof Using "Type".

Open Scope Z_scope.
Implicit Type 𝔄: syn_type.

Section inc_some_list.
  Context `{!typeG Σ}.

  Definition inc_some_list: val :=
    fn: ["bla"] :=
      let: "get_sum_list" := get_sum_list in
      let: "take_some_list" := take_some_list int in
      Newlft;;
      let: "sla" := "bla" in Share;; letalloc: "bsla" <- "sla" in
      letcall: "bsum" := "get_sum_list" ["bsla"] in
      let: "sum" := !"bsum" in delete [ #1; "bsum"];;
      Endlft;; Newlft;;
      letalloc: "bula" <- "bla" in
      letcall: "bua" := "take_some_list" ["bula"] in
      let: "ua" := !"bua" in delete [ #1; "bua"];;
      let: "a" := !"ua" in let: "1" := #1 in let: "a+1" := "a" + "1" in
      "ua" <- "a+1";;
      Endlft;; Newlft;;
      let: "sla'" := "bla" in Share;; letalloc: "bsla'" <- "sla'" in
      letcall: "box" := "get_sum_list" ["bsla'"] in let: "sum'" := !"box" in
      Endlft;;
      let: "r" := "sum'" - "sum" in letalloc: "box" <- "r" in return: ["box"].

  Definition inc_some_list_inv: predl_trans' [listₛ Zₛ * listₛ Zₛ]%ST (Zₛ * Zₛ) :=
    λ post '-[(al, al')], ∀a, post (a, a + (sum_listZ al' - sum_listZ al)).

  Global Instance inc_some_list_inv_mono : MonoTrans' inc_some_list_inv.
  Proof. move=>/= ?? Imp [[??][]]??. by apply Imp. Qed.

  Lemma inc_some_list_inv_fp post al :
    inc_some_list_inv post al → (@take_some_list_tr Zₛ) inc_some_list_inv post al.
  Proof.
    move: al=> [[[|a ?][|??]][]]//=. move=> Post. split.
    - move=> ?. subst. eapply eq_ind; [apply (Post a)|]. f_equal. lia.
    - move=> a' ?. subst. eapply eq_ind; [apply (Post a')|]. f_equal. lia.
  Qed.

  Lemma inc_some_list_type {𝔄} :
    typed_val inc_some_list (fn(∅; list_ty int) → int) (λ post '-[_], post 1).
   Proof.
    eapply type_fn; [apply _|]=>/= _ ??[?[]]. simpl_subst. via_tr_impl.
    { iApply type_val; [apply get_sum_list_type|]. intro_subst.
      iApply type_val; [apply take_some_list_type|]. intro_subst.
      iApply type_newlft. iIntros (α).
      iApply (type_letpath (&uniq{α} _)%T); [solve_typing|]. intro_subst.
      iApply type_share; [solve_extract|solve_typing|].
      iApply type_letalloc_1; [solve_extract|done|]. intro_subst. via_tr_impl.
      { iApply (type_letcall α); [solve_typing|solve_extract|solve_typing..|].
        intro_subst. iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
        iApply type_delete; [solve_extract|done..|]. via_tr_impl.
        { iApply type_endlft; [solve_resolve_unblock|solve_typing|].
          iApply type_newlft. iIntros (β).
          iApply (type_letalloc_1 (&uniq{β} _)%T); [solve_extract|done|].
          intro_subst. via_tr_impl.
          { iApply (type_letcall β); [solve_typing|solve_extract|solve_typing..|].
            intro_subst. iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
            iApply type_delete; [solve_extract|done..|].
            iApply type_deref; [solve_extract|solve_typing..|]. intro_subst.
            iApply type_int. intro_subst. iApply type_plus; [solve_extract|]. intro_subst.
            iApply type_assign; [solve_extract|solve_typing..|]. via_tr_impl.
            { iApply type_endlft; [solve_resolve_unblock|solve_typing|].
              iApply type_newlft. iIntros (γ).
              iApply (type_letpath (&uniq{γ} _)%T); [solve_typing|]. intro_subst.
              iApply type_share; [solve_extract|solve_typing|].
              iApply type_letalloc_1; [solve_extract|done|]. intro_subst. via_tr_impl.
              { iApply (type_letcall γ); [solve_typing|solve_extract|solve_typing..|].
                intro_subst. iApply type_deref; [solve_extract|solve_typing..|].
                intro_subst. via_tr_impl.
                { iApply type_endlft; [solve_resolve_unblock|solve_typing|].
                  iApply type_minus; [solve_extract|]. intro_subst.
                  iApply type_letalloc_1; [solve_extract|done|]. intro_subst.
                  iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
                move=>/= ??. exact id. }
              move=>/= ??. exact id. }
            move=>/= ??. exact id. }
          move=>/= ??. exact id. }
        move=>/= ??. exact id. }
      move=>/= ??. exact id. }
    move=>/= ?[?[]]??<-?. exists inc_some_list_inv. split; [apply _|].
    split; [apply inc_some_list_inv_fp|]. move=>/= ????.
    eapply eq_ind; [done|]. lia.
  Qed.
End inc_some_list.
