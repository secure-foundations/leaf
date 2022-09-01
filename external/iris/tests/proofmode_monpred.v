From iris.proofmode Require Import tactics monpred.
From iris.base_logic.lib Require Import invariants.

Unset Mangle Names.

Section tests.
  Context {I : biIndex} {PROP : bi}.
  Local Notation monPred := (monPred I PROP).
  Local Notation monPredI := (monPredI I PROP).
  Implicit Types P Q R : monPred.
  Implicit Types 𝓟 𝓠 𝓡 : PROP.
  Implicit Types i j : I.

  Lemma test0 P : P -∗ P.
  Proof. iIntros "$". Qed.

  Lemma test_iStartProof_1 P : P -∗ P.
  Proof. iStartProof. iStartProof. iIntros "$". Qed.
  Lemma test_iStartProof_2 P : P -∗ P.
  Proof. iStartProof monPred. iStartProof monPredI. iIntros "$". Qed.
  Lemma test_iStartProof_3 P : P -∗ P.
  Proof. iStartProof monPredI. iStartProof monPredI. iIntros "$". Qed.
  Lemma test_iStartProof_4 P : P -∗ P.
  Proof. iStartProof monPredI. iStartProof monPred. iIntros "$". Qed.
  Lemma test_iStartProof_5 P : P -∗ P.
  Proof. iStartProof PROP. iIntros (i) "$". Qed.
  Lemma test_iStartProof_6 P : P ⊣⊢ P.
  Proof. iStartProof PROP. iIntros (i). iSplit; iIntros "$". Qed.
  Lemma test_iStartProof_7 `{!BiInternalEq PROP} P : ⊢@{monPredI} P ≡ P.
  Proof. iStartProof PROP. done. Qed.

  Lemma test_intowand_1 P Q : (P -∗ Q) -∗ P -∗ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". Show.
    iIntros (j ->) "HP". Show. by iApply "HW".
  Qed.
  Lemma test_intowand_2 P Q : (P -∗ Q) -∗ P -∗ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP".
    iSpecialize ("HW" with "[HP //]"). done.
  Qed.
  Lemma test_intowand_3 P Q : (P -∗ Q) -∗ P -∗ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP".
    iSpecialize ("HW" with "HP"). done.
  Qed.
  Lemma test_intowand_4 P Q : (P -∗ Q) -∗ ▷ P -∗ ▷ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP". by iApply "HW".
  Qed.
  Lemma test_intowand_5 P Q : (P -∗ Q) -∗ ▷ P -∗ ▷ Q.
  Proof.
    iStartProof PROP. iIntros (i) "HW". iIntros (j ->) "HP".
    iSpecialize ("HW" with "HP"). done.
  Qed.

  Lemma test_apply_in_elim (P : monPredI) (i : I) : monPred_in i -∗ ⎡ P i ⎤ → P.
  Proof. iIntros. by iApply monPred_in_elim. Qed.

  Lemma test_iStartProof_forall_1 (Φ : nat → monPredI) : ∀ n, Φ n -∗ Φ n.
  Proof.
    iStartProof PROP. iIntros (n i) "$".
  Qed.
  Lemma test_iStartProof_forall_2 (Φ : nat → monPredI) : ∀ n, Φ n -∗ Φ n.
  Proof.
    iStartProof. iIntros (n) "$".
  Qed.

  Lemma test_embed_wand (P Q : PROP) : (⎡P⎤ -∗ ⎡Q⎤) -∗ ⎡P -∗ Q⎤ : monPred.
  Proof.
    iIntros "H HP". by iApply "H".
  Qed.

  Lemma test_objectively P Q : <obj> emp -∗ <obj> P -∗ <obj> Q -∗ <obj> (P ∗ Q).
  Proof. iIntros "#? HP HQ". iModIntro. by iSplitL "HP". Qed.

  Lemma test_objectively_absorbing P Q R `{!Absorbing P} :
    <obj> emp -∗ <obj> P -∗ <obj> Q -∗ R -∗ <obj> (P ∗ Q).
  Proof. iIntros "#? HP HQ HR". iModIntro. by iSplitL "HP". Qed.

  Lemma test_objectively_affine P Q R `{!Affine R} :
    <obj> emp -∗ <obj> P -∗ <obj> Q -∗ R -∗ <obj> (P ∗ Q).
  Proof. iIntros "#? HP HQ HR". iModIntro. by iSplitL "HP". Qed.

  Lemma test_iModIntro_embed P `{!Affine Q} 𝓟 𝓠 :
    □ P -∗ Q -∗ ⎡𝓟⎤ -∗ ⎡𝓠⎤ -∗ ⎡ 𝓟 ∗ 𝓠 ⎤.
  Proof. iIntros "#H1 _ H2 H3". iModIntro. iFrame. Qed.

  Lemma test_iModIntro_embed_objective P `{!Objective Q} 𝓟 𝓠 :
    □ P -∗ Q -∗ ⎡𝓟⎤ -∗ ⎡𝓠⎤ -∗ ⎡ ∀ i, 𝓟 ∗ 𝓠 ∗ Q i ⎤.
  Proof. iIntros "#H1 H2 H3 H4". iModIntro. Show. iFrame. Qed.

  Lemma test_iModIntro_embed_nested P 𝓟 𝓠 :
    □ P -∗ ⎡◇ 𝓟⎤ -∗ ⎡◇ 𝓠⎤ -∗ ⎡ ◇ (𝓟 ∗ 𝓠) ⎤.
  Proof. iIntros "#H1 H2 H3". iModIntro ⎡ _ ⎤%I. by iSplitL "H2". Qed.

  Lemma test_into_wand_embed 𝓟 𝓠 :
    (𝓟 -∗ ◇ 𝓠) →
    ⎡𝓟⎤ ⊢@{monPredI} ◇ ⎡𝓠⎤.
  Proof.
    iIntros (HPQ) "HP".
    iMod (HPQ with "[-]") as "$"; last by auto.
    iAssumption.
  Qed.

  Lemma test_monPred_at_and_pure P i j :
    (monPred_in j ∧ P) i ⊢ ⌜ j ⊑ i ⌝ ∧ P i.
  Proof.
    iDestruct 1 as "[% $]". done.
  Qed.
  Lemma test_monPred_at_sep_pure P i j :
    (monPred_in j ∗ <absorb> P) i ⊢ ⌜ j ⊑ i ⌝ ∧ <absorb> P i.
  Proof.
    iDestruct 1 as "[% ?]". auto.
  Qed.

  Context (FU : BiFUpd PROP).

  Lemma test_apply_fupd_intro_mask_subseteq E1 E2 P :
    E2 ⊆ E1 → P -∗ |={E1,E2}=> |={E2,E1}=> P.
  Proof. iIntros. by iApply @fupd_mask_intro_subseteq. Qed.
  Lemma test_apply_fupd_mask_subseteq E1 E2 P :
    E2 ⊆ E1 → P -∗ |={E1,E2}=> |={E2,E1}=> P.
  Proof. iIntros. iFrame. by iApply @fupd_mask_subseteq. Qed.

  Lemma test_iFrame_embed_persistent (P : PROP) (Q: monPred) :
    Q ∗ □ ⎡P⎤ ⊢ Q ∗ ⎡P ∗ P⎤.
  Proof.
    iIntros "[$ #HP]". iFrame "HP".
  Qed.

  Lemma test_iNext_Bi P :
    ▷ P ⊢@{monPredI} ▷ P.
  Proof. iIntros "H". by iNext. Qed.

  (** Test monPred_at framing *)
  Lemma test_iFrame_monPred_at_wand (P Q : monPred) i :
    P i -∗ (Q -∗ P) i.
  Proof. iIntros "$". Show. Abort.

  Program Definition monPred_id (R : monPred) : monPred :=
    MonPred (λ V, R V) _.
  Next Obligation. intros ? ???. eauto. Qed.

  Lemma test_iFrame_monPred_id (Q R : monPred) i :
    Q i ∗ R i -∗ (Q ∗ monPred_id R) i.
  Proof.
    iIntros "(HQ & HR)". iFrame "HR". iAssumption.
  Qed.

  Lemma test_iFrame_rel P i j ij :
    IsBiIndexRel i ij → IsBiIndexRel j ij →
    P i -∗ P j -∗ P ij ∗ P ij.
  Proof. iIntros (??) "HPi HPj". iFrame. Qed.

  Lemma test_iFrame_later_rel `{!BiAffine PROP} P i j :
    IsBiIndexRel i j →
    ▷ (P i) -∗ (▷ P) j.
  Proof. iIntros (?) "?". iFrame. Qed.

  Lemma test_iFrame_laterN n P i :
    ▷^n (P i) -∗ (▷^n P) i.
  Proof. iIntros "?". iFrame. Qed.

  Lemma test_iFrame_quantifiers P i :
    P i -∗ (∀ _:(), ∃ _:(), P) i.
  Proof. iIntros "?". iFrame. Show. iIntros ([]). iExists (). iEmpIntro. Qed.

  Lemma test_iFrame_embed (P : PROP) i :
    P -∗ (embed (B:=monPredI) P) i.
  Proof. iIntros "$". Qed.

  (* Make sure search doesn't diverge on an evar *)
  Lemma test_iFrame_monPred_at_evar (P : monPred) i j :
    P i -∗ ∃ Q, (Q j).
  Proof. iIntros "HP". iExists _. Fail iFrame "HP". Abort.

End tests.

Section tests_iprop.
  Context {I : biIndex} `{!invGS Σ}.

  Local Notation monPred := (monPred I (iPropI Σ)).
  Implicit Types P Q R : monPred.
  Implicit Types 𝓟 𝓠 𝓡 : iProp Σ.

  Lemma test_iInv_0 N 𝓟 :
    embed (B:=monPred) (inv N (<pers> 𝓟)) ={⊤}=∗ ⎡▷ 𝓟⎤.
  Proof.
    iIntros "#H".
    iInv N as "#H2". Show.
    iModIntro. iSplit=>//. iModIntro. iModIntro; auto.
  Qed.

  Lemma test_iInv_0_with_close N 𝓟 :
    embed (B:=monPred) (inv N (<pers> 𝓟)) ={⊤}=∗ ⎡▷ 𝓟⎤.
  Proof.
    iIntros "#H".
    iInv N as "#H2" "Hclose". Show.
    iMod ("Hclose" with "H2").
    iModIntro. iModIntro. by iNext.
  Qed.

  Lemma test_iPoseProof `{inG Σ A} P γ (x y : A) :
    x ~~> y → P ∗ ⎡own γ x⎤ ==∗ ⎡own γ y⎤.
  Proof.
    iIntros (?) "[_ Hγ]".
    iPoseProof (own_update with "Hγ") as "H"; first done.
    by iMod "H".
  Qed.
End tests_iprop.
