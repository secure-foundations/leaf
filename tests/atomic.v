From iris.proofmode Require Import tactics.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation atomic_heap.
Set Default Proof Using "Type".

Unset Mangle Names.

Section tests.
  Context `{!heapGS Σ} {aheap: atomic_heap Σ}.
  Import atomic_heap.notation.

  (* FIXME: removing the `val` type annotation breaks printing. *)
  Lemma test_awp_apply_without (Q : iProp Σ) (l : loc) v :
    Q -∗ l ↦ v -∗ WP !#l {{ _, Q }}.
  Proof.
    iIntros "HQ Hl". awp_apply load_spec without "HQ". Show.
    iAaccIntro with "Hl"; eauto with iFrame.
  Qed.
End tests.

(* Test if we get reasonable error messages with non-laterable assertions in the context. *)
Section error.
  Context `{!heapGS Σ} {aheap: atomic_heap Σ}.
  Import atomic_heap.notation.

  Check "non_laterable".
  Lemma non_laterable (P : iProp Σ) (l : loc) :
    P -∗ WP !#l {{ _, True }}.
  Proof.
    iIntros "HP". wp_apply load_spec. iAuIntro. Show.
  Restart.
    iIntros "HP". awp_apply load_spec. Show.
  Abort.
End error.


(* Test if AWP and the AU obtained from AWP print. *)
Check "printing".
Section printing.
  Context `{!heapGS Σ}.

  Definition code : expr := #().

  Lemma print_both_quant (P : val → iProp Σ) :
    ⊢ <<< ∀ x, P x >>> code @ ⊤ <<< ∃ y, P y, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_first_quant l :
    ⊢ <<< ∀ x, l ↦ x >>> code @ ⊤ <<< l ↦ x, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_second_quant l :
    ⊢ <<< l ↦ #() >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_no_quant l :
    ⊢ <<< l ↦ #() >>> code @ ⊤ <<< l ↦ #(), RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Check "Now come the long pre/post tests".

  Lemma print_both_quant_long l :
    ⊢ <<< ∀ x, l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_both_quant_longpre l :
    ⊢ <<< ∀ x, l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_both_quant_longpost l :
    ⊢ <<< ∀ xx, l ↦ xx ∗ l ↦ xx ∗ l ↦ xx >>> code @ ⊤ <<< ∃ yyyy, l ↦ yyyy ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "?". Show.
  Abort.

  Lemma print_first_quant_long l :
    ⊢ <<< ∀ x, l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< l ↦ x, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_second_quant_long l x :
    ⊢ <<< l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< ∃ y, l ↦ y, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_no_quant_long l x :
    ⊢ <<< l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x >>> code @ ⊤ <<< l ↦ #(), RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_no_quant_longpre l xx yyyy :
    ⊢ <<< l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx >>> code @ ⊤ <<< l ↦ yyyy, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_no_quant_longpost l xx yyyy :
    ⊢ <<< l ↦ xx ∗ l ↦ xx ∗ l ↦ xx >>> code @ ⊤ <<< l ↦ yyyy ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx, RET #() >>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Check "Prettification".

  Lemma iMod_prettify (P : val → iProp Σ) :
    ⊢ <<< ∀ x, P x >>> !#0 @ ⊤ <<< ∃ y, P y, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". iMod "AU". Show.
  Abort.

End printing.
