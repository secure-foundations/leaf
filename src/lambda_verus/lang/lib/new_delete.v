From lrust.lang Require Export notation.
From lrust.lang Require Import heap proofmode memcpy.
Set Default Proof Using "Type".

Definition new : val :=
  λ: ["n"],
    if: "n" ≤ #0 then #((42%positive, 1337):loc)
    else Alloc "n".

Definition delete : val :=
  λ: ["n"; "loc"],
    if: "n" ≤ #0 then #☠
    else Free "n" "loc".

Section specs.
  Context `{!lrustGS Σ}.

  Lemma wp_new E n:
    0 ≤ n →
    {{{ True }}} new [ #n ] @ E
    {{{ l, RET LitV $ LitLoc l;
        (†l…(Z.to_nat n) ∨ ⌜n = 0⌝) ∗ l ↦∗ repeat (LitV LitPoison) (Z.to_nat n) }}}.
  Proof.
    iIntros (? Φ) "_ HΦ". wp_lam. wp_op; case_bool_decide.
    - wp_if. assert (n = 0) as -> by lia. iApply "HΦ".
      rewrite heap_mapsto_vec_nil. auto.
    - wp_if. wp_alloc l as "H↦" "H†". lia. iApply "HΦ". subst sz. iFrame.
  Qed.

  Lemma wp_delete vl (n: Z) l E :
    n = length vl →
    {{{ l ↦∗ vl ∗ (†l…(length vl) ∨ ⌜n = 0⌝) }}}
      delete [ #n; #l] @ E
    {{{ RET #☠; True }}}.
  Proof.
    iIntros (? Φ) "(H↦ & [H†|%]) HΦ";
      wp_lam; wp_op; case_bool_decide; try lia;
      wp_if; try wp_free; by iApply "HΦ".
  Qed.
End specs.

Notation "letalloc: x <- e1 'in' e2" :=
  ((Lam [BNamed x%string%E] (Seq (Var x <- e1) e2))
    [App (of_val new) [ #(LitInt 1)]])%E
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.

Notation "letalloc: x <-{ n } ! e1 'in' e2" :=
  ((Lam [BNamed x%string%E%E]
    (Seq (Var x <-{n%Z%E} !e1) e2))
    [App (of_val new) [ Lit (LitInt n)]])%E
  (at level 102, x at level 1, e1, e2 at level 150,
    format "letalloc:  x  <-{ n }  ! e1  'in'  e2") : expr_scope.
