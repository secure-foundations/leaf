From stdpp Require Import nat_cancel.
From iris.bi Require Import bi.
From iris.proofmode Require Import modality_instances classes.
From iris.proofmode Require Import ltac_tactics class_instances.
From iris.prelude Require Import options.
Import bi.

Section class_instances_updates.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

Global Instance from_assumption_bupd `{!BiBUpd PROP} p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (|==> Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_intro. Qed.
Global Instance from_assumption_fupd
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} E p P Q :
  FromAssumption p P (|==> Q) → KnownRFromAssumption p P (|={E}=> Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply bupd_fupd. Qed.

Global Instance from_pure_bupd `{!BiBUpd PROP} a P φ :
  FromPure a P φ → FromPure a (|==> P) φ.
Proof. rewrite /FromPure=> <-. apply bupd_intro. Qed.
Global Instance from_pure_fupd `{!BiFUpd PROP} a E P φ :
  FromPure a P φ → FromPure a (|={E}=> P) φ.
Proof. rewrite /FromPure=> <-. apply fupd_intro. Qed.

Global Instance into_wand_bupd `{!BiBUpd PROP} p q R P Q :
  IntoWand false false R P Q → IntoWand p q (|==> R) (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite bupd_sep wand_elim_r.
Qed.
Global Instance into_wand_fupd `{!BiFUpd PROP} E p q R P Q :
  IntoWand false false R P Q →
  IntoWand p q (|={E}=> R) (|={E}=> P) (|={E}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite !intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_sep wand_elim_r.
Qed.

Global Instance into_wand_bupd_persistent `{!BiBUpd PROP} p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|==> R) P (|==> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite bupd_frame_l wand_elim_r.
Qed.
Global Instance into_wand_fupd_persistent `{!BiFUpd PROP} E1 E2 p q R P Q :
  IntoWand false q R P Q → IntoWand p q (|={E1,E2}=> R) P (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand /= => HR. rewrite intuitionistically_if_elim HR.
  apply wand_intro_l. by rewrite fupd_frame_l wand_elim_r.
Qed.

Global Instance into_wand_bupd_args `{!BiBUpd PROP} p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|==> P) (|==> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim bupd_wand_r.
Qed.
Global Instance into_wand_fupd_args `{!BiFUpd PROP} E1 E2 p q R P Q :
  IntoWand p false R P Q → IntoWand' p q R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => ->.
  apply wand_intro_l. by rewrite intuitionistically_if_elim fupd_wand_r.
Qed.

Global Instance from_sep_bupd `{!BiBUpd PROP} P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromSep=><-. apply bupd_sep. Qed.
Global Instance from_sep_fupd `{!BiFUpd PROP} E P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
Proof. rewrite /FromSep =><-. apply fupd_sep. Qed.

Global Instance from_or_bupd `{!BiBUpd PROP} P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /FromOr=><-. apply bupd_or. Qed.
Global Instance from_or_fupd `{!BiFUpd PROP} E1 E2 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof. rewrite /FromOr=><-. apply fupd_or. Qed.

Global Instance into_and_bupd `{!BiBUpd PROP} P Q1 Q2 :
  IntoAnd false P Q1 Q2 → IntoAnd false (|==> P) (|==> Q1) (|==> Q2).
Proof. rewrite /IntoAnd/==>->. apply bupd_and. Qed.
Global Instance into_and_fupd `{!BiFUpd PROP} E1 E2 P Q1 Q2 :
  IntoAnd false P Q1 Q2 → IntoAnd false (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
Proof. rewrite /IntoAnd/==>->. apply fupd_and. Qed.

Global Instance from_exist_bupd `{!BiBUpd PROP} {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|==> P) (λ a, |==> Φ a)%I.
Proof. rewrite /FromExist=><-. apply bupd_exist. Qed.
Global Instance from_exist_fupd `{!BiFUpd PROP} {A} E1 E2 P (Φ : A → PROP) :
  FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof. rewrite /FromExist=><-. apply fupd_exist. Qed.

Global Instance into_forall_bupd `{!BiBUpd PROP} {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (|==> P) (λ a, |==> Φ a)%I.
Proof. rewrite /IntoForall=>->. apply bupd_forall. Qed.
Global Instance into_forall_fupd `{!BiFUpd PROP} {A} E1 E2 P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
Proof. rewrite /IntoForall=>->. apply fupd_forall. Qed.

Global Instance from_forall_fupd
    `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP} E1 E2 {A} P (Φ : A → PROP) name :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ name → (∀ x, Plain (Φ x)) →
  FromForall (|={E1,E2}=> P) (λ a, |={E1,E2}=> (Φ a))%I name.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite fupd_plain_forall; set_solver.
Qed.
Global Instance from_forall_step_fupd
    `{!BiFUpd PROP, !BiPlainly PROP, !BiFUpdPlainly PROP} E1 E2 {A} P (Φ : A → PROP) name :
  (* Some cases in which [E2 ⊆ E1] holds *)
  TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅)) →
  FromForall P Φ name → (∀ x, Plain (Φ x)) →
  FromForall (|={E1}[E2]▷=> P) (λ a, |={E1}[E2]▷=> (Φ a))%I name.
Proof.
  rewrite /FromForall=> -[->|[->|->]] <- ?; rewrite step_fupd_plain_forall; set_solver.
Qed.

Global Instance is_except_0_bupd `{!BiBUpd PROP} P : IsExcept0 P → IsExcept0 (|==> P).
Proof.
  rewrite /IsExcept0=> HP.
  by rewrite -{2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P).
Qed.
Global Instance is_except_0_fupd `{!BiFUpd PROP} E1 E2 P :
  IsExcept0 (|={E1,E2}=> P).
Proof. by rewrite /IsExcept0 except_0_fupd. Qed.

Global Instance from_modal_bupd `{!BiBUpd PROP} P :
  FromModal True modality_id (|==> P) (|==> P) P.
Proof. by rewrite /FromModal /= -bupd_intro. Qed.
Global Instance from_modal_fupd E P `{!BiFUpd PROP} :
  FromModal True modality_id (|={E}=> P) (|={E}=> P) P.
Proof. by rewrite /FromModal /= -fupd_intro. Qed.
Global Instance from_modal_fupd_wrong_mask E1 E2 P `{!BiFUpd PROP} :
  FromModal
        (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [iApply fupd_mask_intro] to introduce mask-changing update modalities")
    modality_id (|={E1,E2}=> P) (|={E1,E2}=> P) P | 100.
Proof. by intros []. Qed.

Global Instance elim_modal_bupd `{!BiBUpd PROP} p P Q :
  ElimModal True p false (|==> P) P (|==> Q) (|==> Q).
Proof.
  by rewrite /ElimModal
    intuitionistically_if_elim bupd_frame_r wand_elim_r bupd_trans.
Qed.

Global Instance elim_modal_bupd_plain_goal
    `{!BiBUpd PROP, !BiPlainly PROP, !BiBUpdPlainly PROP} p P Q :
  Plain Q → ElimModal True p false (|==> P) P Q Q.
Proof.
  intros. by rewrite /ElimModal intuitionistically_if_elim
    bupd_frame_r wand_elim_r bupd_plain.
Qed.
Global Instance elim_modal_bupd_plain
    `{!BiBUpd PROP, !BiPlainly PROP, !BiBUpdPlainly PROP} p P Q :
  Plain P → ElimModal True p p (|==> P) P Q Q.
Proof. intros. by rewrite /ElimModal bupd_plain wand_elim_r. Qed.
Global Instance elim_modal_bupd_fupd
    `{!BiBUpd PROP, !BiFUpd PROP, !BiBUpdFUpd PROP} p E1 E2 P Q :
  ElimModal True p false (|==> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q) | 10.
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_trans.
Qed.
Global Instance elim_modal_fupd_fupd `{!BiFUpd PROP} p E1 E2 E3 P Q :
  ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
Proof.
  by rewrite /ElimModal intuitionistically_if_elim
    fupd_frame_r wand_elim_r fupd_trans.
Qed.
Global Instance elim_modal_fupd_fupd_wrong_mask `{!BiFUpd PROP} p E0 E1 E2 E3 P Q :
  ElimModal
    (pm_error "Goal and eliminated modality must have the same mask.
Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
    p false
    (|={E1,E2}=> P) False (|={E0,E3}=> Q) False | 100.
Proof. intros []. Qed.

Global Instance add_modal_bupd `{!BiBUpd PROP} P Q : AddModal (|==> P) P (|==> Q).
Proof. by rewrite /AddModal bupd_frame_r wand_elim_r bupd_trans. Qed.

Global Instance add_modal_fupd `{!BiFUpd PROP} E1 E2 P Q :
  AddModal (|={E1}=> P) P (|={E1,E2}=> Q).
Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_trans. Qed.

Global Instance elim_acc_fupd `{!BiFUpd PROP} {X} E1 E2 E α β mγ Q :
  ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α β mγ
          (|={E1,E}=> Q)
          (λ x, |={E2}=> β x ∗ (mγ x -∗? |={E1,E}=> Q))%I.
Proof.
  iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
  iMod ("Hinner" with "Hα") as "[Hβ Hfin]".
  iMod ("Hclose" with "Hβ") as "Hγ". by iApply "Hfin".
Qed.
End class_instances_updates.
