From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".


Section code.
  Context `{!typeG Σ}.

  Definition projection_toggle {𝔄} (ty : type 𝔄) : val :=
    fn: ["p"; "b"] :=
    let: "ba" := !"b" in
    let: "p'" := !"p" in
    if: "ba" then
      "p" <- "p'" +ₗ #0 ;;
      return: ["p"]
    else
      "p" <- "p'" +ₗ #ty.(ty_size);;
      return: ["p"]
  .

  Lemma projection_toggle_type {𝔄} (ty : type 𝔄) :
    typed_val (projection_toggle ty) (fn<α>(∅; &uniq{α} (ty * ty), bool_ty) → &uniq{α} ty)
      (λ post '-[(p, p'); b], if b then p'.2 = p.2 → post (p.1, p'.1) else p'.1 = p.1 → post (p.2, p'.2)).
  Proof.
    eapply type_fn; [apply _|] => /= x ϝ k [? [? []]]. simpl_subst. via_tr_impl.

    iApply type_deref; [solve_extract | solve_typing | done | ]; intro_subst.
    iApply type_deref; [solve_extract | solve_typing | done | ]; intro_subst.
    iApply type_if; [solve_extract| ..].
    - via_tr_impl.
      iApply type_assign; [solve_extract| solve_typing| solve_typing| ].
      iApply type_jump; [solve_typing| solve_extract| simpl; solve_typing].
      move =>/= ??. exact id.
    - via_tr_impl.
      iApply type_assign; [solve_extract| solve_typing| solve_typing| ].
      iApply type_jump; [solve_typing| solve_extract| simpl; solve_typing].
      move =>/= ??. exact id.
    - move => ? [[[? ?] [? ?]] [[|] []]] //=.
  Qed.
End code.
