From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Set Default Proof Using "Type".

Section bool.
  Context `{!typeG Σ}.

  Program Definition bool_ty: type boolₛ :=
    {| pt_size := 1;  pt_own (b: boolₛ) _ vl := ⌜vl = [ #b]⌝; |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance bool_send: Send bool_ty.
  Proof. done. Qed.

  Lemma bool_resolve E L : resolve E L bool_ty (const True).
  Proof. apply resolve_just. Qed.

  Lemma type_bool_instr (b: bool) : typed_val #b bool_ty b.
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_value. iExists -[const b]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "⧖". by iExists b.
  Qed.

  Lemma type_bool {𝔄l 𝔅} (b: bool) (T: tctx 𝔄l) x e tr E L (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := #b in e) (λ post al, tr post (b -:: al)).
  Proof.
    iIntros. iApply type_let; [apply type_bool_instr|solve_typing|done..].
  Qed.

  Lemma type_nd_bool_instr E L :
    typed_instr_ty E L +[] NdBool bool_ty (λ post '-[], ∀b, post b).
  Proof.
    iIntros (???) "_ _ _ _ _ $$ _ #?". iMod persistent_time_receipt_0 as "⧖".
    wp_nd_int z. wp_op. iExists -[const _]. rewrite right_id tctx_hasty_val'; [|done].
    iSplit. { iExists _. iFrame "⧖". by iExists _. }
    by iApply proph_obs_impl; [|done]=>/= ??.
  Qed.

  Lemma type_nd_bool {𝔄l 𝔅} (T: tctx 𝔄l) x e tr E L (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := NdBool in e)
      (λ post al, ∀b, tr post (b -:: al))%type.
  Proof.
    iIntros. by iApply type_let; [apply type_nd_bool_instr|solve_typing| |done].
  Qed.

  Lemma type_if {𝔄l 𝔅l ℭ} p (T: tctx 𝔄l) (T': tctx 𝔅l) e1 e2 tr1 tr2 trx E L (C: cctx ℭ) :
    tctx_extract_ctx E L +[p ◁ bool_ty] T T' trx →
    typed_body E L C T' e1 tr1 -∗ typed_body E L C T' e2 tr2 -∗
    typed_body E L C T (if: p then e1 else e2)
      (trx ∘ (λ post '(b -:: vl), if b then tr1 post vl else tr2 post vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]=>/=.
    iIntros (?[??]?) "/= #LFT #TIME #PROPH #UNIQ #E Na L C [p T] Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (?? _) "_".
    iDestruct 1 as ([|]->) "%Eq"; move: Eq=> [=->]; wp_case.
    - by iApply ("e1" with "LFT TIME PROPH UNIQ E Na L C T").
    - by iApply ("e2" with "LFT TIME PROPH UNIQ E Na L C T").
  Qed.
End bool.

Global Hint Resolve bool_resolve : lrust_typing.
