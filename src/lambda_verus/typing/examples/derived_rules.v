From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Notation "drop: x" := Skip%E (only parsing, at level 102, x at level 1)
  : expr_scope.

Notation "let: x := &uniq{ κ } p 'in' e" := (let: x := p in e)%E
  (only parsing, at level 102, x at level 1, e at level 150) : expr_scope.

Section rules.
  Context `{!typeG Σ}.

  Lemma ty_box_write {𝔄 𝔅} E L p (ty: type 𝔄) p' (ty': type 𝔅):
    ty.(ty_size) = ty'.(ty_size) →
    typed_instr E L +[p ◁ box ty; p' ◁ ty'] (p <- p') (λ _, +[p ◁ box ty'])
      (λ post '-[_; b], post -[b]).
  Proof.
    move=> Eq. rewrite /box Eq.
    eapply (type_assign_instr _ _ _ _ _ _ (λ _ post, post));
      [solve_typing|eapply resolve'_just, resolve_just].
  Qed.

  Lemma ty_uniq_ref_write {𝔄} E L κ (ty: type 𝔄) p p' :
    lctx_lft_alive E L κ →
    typed_instr E L +[p ◁ &uniq{κ} ty; p' ◁ ty] (p <- p')
      (λ _, +[p ◁ &uniq{κ} ty]) (λ post '-[aa; b], post -[(b, aa.2)] ).
  Proof.
    move=> ?. eapply (type_assign_instr (&uniq{κ} ty) ty (&uniq{κ} ty) ty
      fst (λ v w, (w, v.2)) (λ _ post, post)); [solve_typing|].
    eapply resolve'_just, resolve_just.
  Qed.

  Lemma ty_uniq_ref_read {𝔄} E L κ (ty: type 𝔄) p :
    lctx_lft_alive E L κ → Copy ty → ty.(ty_size) = 1%nat →
    typed_instr E L +[p ◁ &uniq{κ} ty] (!p)
      (λ x, +[x ◁ ty; p ◁ &uniq{κ} ty]) (λ post '-[aa], post -[aa.1; aa] ).
  Proof. move=> ???. eapply type_deref_instr; solve_typing. Qed.

  Lemma ty_uniq_ref_bye {𝔄} E L (ty: type 𝔄) κ p :
    lctx_lft_alive E L κ →
    typed_instr E L +[p ◁ &uniq{κ} ty] (drop: p) (λ _, +[])
      (λ post '-[aa], aa.2 = aa.1 → post -[]).
  Proof.
    move=> ?. eapply type_resolve_instr. eapply resolve_impl; [solve_typing|].
    by case.
  Qed.

  Lemma ty_uniq_bor {𝔄 𝔄l ℭ} E L (C: cctx ℭ) (T: tctx 𝔄l) (ty: type 𝔄) p x e κ tr:
    Closed (x :b: []) e → elctx_sat E L (ty_outlives_E ty κ) →
    (∀v: val, typed_body E L C
      (v ◁ &uniq{κ} ty +:: p ◁{κ} box ty +:: T) (subst' x v e) tr) -∗
    typed_body E L C (p ◁ box ty +:: T) (let: x := &uniq{κ} p in e)
      (λ post '(a -:: t), (∀ a', tr post ((a, a') -:: a' -:: t)))%type.
  Proof.
    iIntros (??) "?". via_tr_impl.
    { iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_]). by eapply tctx_borrow. }
      iApply type_letpath; [solve_typing|done]. }
    by move=> ?[??].
  Qed.
End rules.