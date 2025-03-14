From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

(* Minimal support for panic and assert.
   Lambdarust does not support unwinding the stack.
   Instead, we get stuck in the current thread.

   This properly models "panic=abort", but fails to take into account the
   trouble caused by unwinding. This is why we do not get into trouble with
   [take_mut]. *)

Notation "assert: e" := (if: e then #☠ else stuck_term)%E (at level 9) : expr_scope.

Section panic.
  Context `{!typeG Σ}.

  Definition panic: val := fn: [] := stuck_term.

  (* Rust's panic! *)
  Lemma panic_type: typed_val panic (fn(∅) → ∅) (λ _ _, False).
  Proof.
    eapply type_fn; [apply _|]=>/= *.
    iIntros (???) "_ _ PROPH _ _ _ _ _ _ Obs".
    iMod (proph_obs_false with "PROPH Obs") as "[]"; [done|move=> ?[]].
  Qed.

  Lemma type_assert_instr E L p :
    typed_instr E L +[p ◁ bool_ty] (assert: p) (const +[])
      (λ post '-[b], if b then post -[] else False).
  Proof.
    iIntros (??[?[]]) "_ _ PROPH _ _ $$ [T _] Obs".
    wp_bind p. iApply (wp_hasty with "T"). iIntros (???) "⧖ T".
    iDestruct "T" as ([|]->) "%Eq"; move: Eq=> [=->]; wp_case.
    - iExists -[]. iFrame.
    - iMod (proph_obs_false with "PROPH Obs") as "[]"; [done|move=> ?[]].
  Qed.

  Lemma type_assert {𝔄l 𝔅l ℭ} E L (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) p e trx tr :
    Closed [] e → tctx_extract_ctx E L +[p ◁ bool_ty] T T' trx →
    typed_body E L C T' e tr -∗
    typed_body E L C T (assert: p ;; e)
      (trx ∘ (λ post '(b -:: al), if b then tr post al else False))%type.
  Proof.
    iIntros (? Extr) "?".
    iApply type_seq; [by apply type_assert_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.

  Definition assert : val :=
    fn: ["bb"] :=
      let: "b" := !"bb" in delete [ #1; "bb"];;
      assert: "b";;
      let: "r" := new [ #0] in return: ["r"].

  (* Rust's assert! *)
  Lemma assert_type:
    typed_val assert (fn(∅; bool_ty) → ())
      (λ post '-[b], if b then post () else False).
  Proof.
    eapply type_fn; [apply _|]=> ???[?[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing|done|]. intro_subst.
      iApply type_delete; [solve_extract|done..|].
      iApply type_assert; [solve_extract|]. iApply type_new; [done|].
      intro_subst. iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=> ?[?[]].
  Qed.
End panic.
