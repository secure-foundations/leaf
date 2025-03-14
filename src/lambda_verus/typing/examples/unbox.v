From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section unbox.
  Context `{!typeG Σ}.

  Definition unbox: val :=
    fn: ["b"] :=
      let: "b'" := !"b" in let: "bx" := !"b'" in
      letalloc: "r" <- "bx" +ₗ #0 in
      delete [ #1; "b"];; return: ["r"].

  Lemma unbox_type :
    typed_val unbox (fn<α>(∅; &uniq{α} (box (int * int))) → &uniq{α} int)
      (λ post '-[((z, w), (z', w'))], w' = w → post (z, z')).
  Proof.
    eapply type_fn; [apply _|]=>/= ???[?[]]. simpl_fp_E. simpl_subst.
    via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing|done|]. intro_subst.
      iApply type_deref_uniq_own; [solve_extract|solve_typing|]. intro_subst.
      iApply type_letalloc_1; [solve_extract|done|]. intro_subst.
      iApply type_delete; [solve_extract|done|done|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=> ?[[[??][??]][]]/=.
  Qed.
End unbox.
