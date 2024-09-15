From iris.prelude Require Import options.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.

Require Import guarding.guard.
Require Import guarding.tactics.

(* Derivation for Heap-Read-Shared law for HeapLang. *)

Section HeapLangWpLoadShared.

  Context `{!heapGS Σ}.

  Lemma wp_load_shared s E F l dq v G : (F ⊆ E) →
    {{{ G ∗ (G &&{F}&&> l ↦{dq} v) }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; G }}}.
  Proof.
    intros Hfe.
    iIntros (Φ) "[G #g] HΦ".
    leaf_open "g" with "G" as "[Hpt Hback]". { set_solver. }
    wp_load.
    iMod ("Hback" with "Hpt") as "G".
    iModIntro. iApply "HΦ". iFrame "G".
  Qed.

End HeapLangWpLoadShared.
