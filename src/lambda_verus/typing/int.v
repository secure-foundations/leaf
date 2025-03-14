From lrust.typing Require Export type.
From lrust.typing Require Import bool programs.
Set Default Proof Using "Type".
Open Scope Z_scope.

Section int.
  Context `{!typeG Σ}.

  Program Definition int: type Zₛ :=
    {| pt_size := 1;  pt_own (z: Zₛ) _ vl := ⌜vl = [ #z]⌝; |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance int_send: Send int.
  Proof. done. Qed.

  Lemma int_resolve E L : resolve E L int (const True).
  Proof. apply resolve_just. Qed.

  Lemma bool_ty_to_int E L : subtype E L bool_ty int Z_of_bool.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. by iIntros.
  Qed.

  Lemma type_int_instr (z: Z) : typed_val #z int z.
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_value. iExists -[const z]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "⧖". by iExists z.
  Qed.

  Lemma type_int {𝔄l 𝔅} (z: Z) (T: tctx 𝔄l) x e tr E L (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ int +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := #z in e) (λ post al, tr post (z -:: al)).
  Proof. iIntros. iApply type_let; [apply type_int_instr|solve_typing|done..]. Qed.

  Lemma type_plus_instr E L p1 p2 :
    typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 + p2) int
      (λ post '-[z; z'], post (z + z')).
  Proof.
    iIntros (??(?&?&[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "% %d _ ⧖" ((z &->&[=->])).
    wp_apply (wp_hasty with "p2"). iIntros "%% _ _" ((z' &->&[=->])).
    wp_op. iExists -[const (z + z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". by iExists (z + z').
  Qed.

  Lemma type_plus {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p1 + p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z + z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_plus_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_minus_instr E L p1 p2 :
    typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 - p2) int
      (λ post '-[z; z'], post (z - z')).
  Proof.
    iIntros (??(?&?&[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "% %d _ ⧖" ((z &->&[=->])).
    wp_apply (wp_hasty with "p2"). iIntros "%% _ _" ((z' &->&[=->])).
    wp_op. iExists -[const (z - z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". by iExists (z - z').
  Qed.

  Lemma type_minus {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p1 - p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z - z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_minus_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_mult_instr E L p1 p2 :
    typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 * p2) int
      (λ post '-[z; z'], post (z * z')).
  Proof.
    iIntros (??(?&?&[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "% %d _ ⧖" ((z &->&[=->])).
    wp_apply (wp_hasty with "p2"). iIntros "%% _ _" ((z' &->&[=->])).
    wp_op. iExists -[const (z * z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "⧖". by iExists (z * z').
  Qed.

  Lemma type_mult {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p1 * p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z * z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_mult_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_le_instr E L p1 p2 :
    typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 ≤ p2) bool_ty
      (λ post '-[z; z'], post (bool_decide (z ≤ z'))).
  Proof.
    iIntros (??(?&?&[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros "% %d _ ⧖" ((z &->&[=->])).
    wp_apply (wp_hasty with "p2"). iIntros "%% _ _" ((z' &->&[=->])).
    wp_op. iExists -[const (bool_decide (z ≤ z'))]. iFrame "Obs".
    rewrite right_id tctx_hasty_val'; [|done]. iExists d.
    iFrame "⧖". by iExists (bool_decide (z ≤ z')).
  Qed.

  Lemma type_le {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L C (v ◁ bool_ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p1 ≤ p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (bool_decide (z ≤ z') -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_le_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_nd_int_instr E L :
    typed_instr_ty E L +[] NdInt int (λ post '-[], ∀z, post z).
  Proof.
    iIntros (???) "_ _ _ _ _ $$ _ #?". iMod persistent_time_receipt_0 as "⧖".
    wp_nd_int z. iExists -[const _]. rewrite right_id tctx_hasty_val'; [|done].
    iSplit. { iExists _. iFrame "⧖". by iExists _. }
    by iApply proph_obs_impl; [|done]=>/= ??.
  Qed.

  Lemma type_nd_int {𝔄l 𝔅} x e tr E L (C: cctx 𝔅) (T: tctx 𝔄l) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ int +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := NdInt in e)
      (λ post bl, ∀z, tr post (z -:: bl))%type.
  Proof.
    iIntros. by iApply type_let; [apply type_nd_int_instr|solve_typing| |done].
  Qed.
End int.

Global Hint Resolve int_resolve : lrust_typing.
