From iris.bi Require Import atomic.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation atomic_heap.
From iris.prelude Require Import options.

Unset Mangle Names.

Section general_bi_tests.
  Context `{BiFUpd PROP} {TA TB : tele} (Eo Ei : coPset).

  (** We can quantify over telescopes *inside* Iris and use them with atomic
  updates. *)
  Definition AU_tele_quantify_iris : Prop :=
    ⊢ ∀ (TA TB : tele) (α : TA → PROP) (β Φ : TA → TB → PROP),
        atomic_update Eo Ei α β Φ.

  (** iAuIntro works. *)
  Lemma au_intro_1 (P : PROP) (α : TA → PROP) (β Φ : TA → TB → PROP) :
    P -∗ atomic_update Eo Ei α β Φ.
  Proof. iIntros "HP". iAuIntro. Abort.
End general_bi_tests.

Section tests.
  Context `{!atomic_heap, !heapGS Σ, !atomic_heapGS Σ}.
  Import atomic_heap.notation.

  Check "test_awp_apply".
  Lemma test_awp_apply (Q : iProp Σ) (l : loc) v :
    Q -∗ l ↦ v -∗ WP !#l {{ _, Q }}.
  Proof.
    iIntros "HQ Hl". awp_apply load_spec. Show.
    iAaccIntro with "Hl"; eauto with iFrame.
  Qed.

  Check "test_awp_apply_without".
  Lemma test_awp_apply_without (Q : iProp Σ) (l : loc) v :
    Q -∗ l ↦ v -∗ WP !#l {{ _, Q }}.
  Proof.
    iIntros "HQ Hl". awp_apply load_spec without "HQ". Show.
    iAaccIntro with "Hl"; eauto with iFrame.
  Qed.
End tests.

(* Test if AWP and the AU obtained from AWP print (and also tests that all the AWP variants parse and type-check). *)
Check "printing".
Section printing.
  Context `{!heapGS Σ}.

  Definition code : expr := #().

  (* Without private postcondition or RET binders *)
  Lemma print_both_quant (P : val → iProp Σ) :
    ⊢ <<{ ∀∀ x, P x }>> code @ ∅ <<{ ∃∃ y, P y | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". rewrite difference_empty_L. Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_first_quant l :
    ⊢ <<{ ∀∀ x, l ↦ x }>> code @ ∅ <<{ l ↦ x | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_second_quant l :
    ⊢ <<{ l ↦ #() }>> code @ ∅ <<{ ∃∃ y, l ↦ y | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Lemma print_no_quant l :
    ⊢ <<{ l ↦ #() }>> code @ ∅ <<{ l ↦ #() | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
    iPoseProof (aupd_aacc with "AU") as "?". Show.
  Abort.

  Check "Now come the long pre/post tests".

  Lemma print_both_quant_long l :
    ⊢ <<{ ∀∀ x, l ↦ x ∗ l ↦ x }>> code @ ∅ <<{ ∃ y, l ↦ y | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_both_quant_longpre l :
    ⊢ <<{ ∀∀ x, l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x }>> code @ ∅ <<{ ∃∃ y, l ↦ y | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_both_quant_longpost l :
    ⊢ <<{ ∀∀ xx, l ↦ xx ∗ l ↦ xx ∗ l ↦ xx }>> code @ ∅ <<{ ∃∃ yyyy, l ↦ yyyy ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "?". Show.
  Abort.

  Lemma print_first_quant_long l :
    ⊢ <<{ ∀∀ x, l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x }>> code @ ∅ <<{ l ↦ x | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_second_quant_long l x :
    ⊢ <<{ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x }>> code @ ∅ <<{ ∃∃ y, l ↦ y | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_no_quant_long l x :
    ⊢ <<{ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x ∗ l ↦ x }>> code @ ∅ <<{ l ↦ #() | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_no_quant_longpre l xx yyyy :
    ⊢ <<{ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx }>> code @ ∅ <<{ l ↦ yyyy | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  Lemma print_no_quant_longpost l xx yyyy :
    ⊢ <<{ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx }>> code @ ∅ <<{ l ↦ yyyy ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx ∗ l ↦ xx | RET #() }>>.
  Proof.
    Show. iIntros (Φ) "AU". Show.
  Abort.

  (* With private postcondition.
  (Makes no big difference for the AU so we only print the initial triple here.) *)
  Lemma print_all (P : val → iProp Σ) :
    ⊢ <<{ ∀∀ x, P x }>> code @ ∅ <<{ ∃∃ y, P y | z, RET z; P z }>>.
  Proof. Show. Abort.

  Lemma print_no_ret (P : val → iProp Σ) :
    ⊢ <<{ ∀∀ x, P x }>> code @ ∅ <<{ ∃∃ y, P y | RET y; P y }>>.
  Proof. Show. Abort.

  Lemma print_no_ex_ret (P : val → iProp Σ) :
    ⊢ <<{ ∀∀ x, P x }>> code @ ∅ <<{ P x | RET x; P x }>>.
  Proof. Show. Abort.

  Lemma print_no_all_ret (P : val → iProp Σ) :
    ⊢ <<{ P #() }>> code @ ∅ <<{ ∃∃ y, P y | RET y; P y }>>.
  Proof. Show. Abort.

  Lemma print_no_all_ex_ret (P : iProp Σ) :
    ⊢ <<{ P }>> code @ ∅ <<{ P | RET #42; P }>>.
  Proof. Show. Abort.

  (* misc *)
  Check "Prettification".

  Lemma iMod_prettify (P : val → iProp Σ) :
    ⊢ <<{ ∀∀ x, P x }>> !#0 @ ∅ <<{ ∃∃ y, P y | RET #() }>>.
  Proof.
    iIntros (Φ) "AU". iMod "AU". Show.
  Abort.


End printing.
