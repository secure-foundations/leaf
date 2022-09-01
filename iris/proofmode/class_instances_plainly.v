From iris.bi Require Import bi.
From iris.proofmode Require Import modality_instances classes.
From iris.prelude Require Import options.
Import bi.

Section class_instances_plainly.
Context `{!BiPlainly PROP}.
Implicit Types P Q R : PROP.

Global Instance from_assumption_plainly_l_true P Q :
  FromAssumption true P Q → KnownLFromAssumption true (■ P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  rewrite intuitionistically_plainly_elim //.
Qed.
Global Instance from_assumption_plainly_l_false `{BiAffine PROP} P Q :
  FromAssumption true P Q → KnownLFromAssumption false (■ P) Q.
Proof.
  rewrite /KnownLFromAssumption /FromAssumption /= =><-.
  rewrite plainly_elim_persistently intuitionistically_into_persistently //.
Qed.

Global Instance from_pure_plainly P φ :
  FromPure false P φ → FromPure false (■ P) φ.
Proof. rewrite /FromPure=> <-. by rewrite plainly_pure. Qed.

Global Instance into_pure_plainly P φ :
  IntoPure P φ → IntoPure (■ P) φ.
Proof. rewrite /IntoPure=> ->. apply: plainly_elim. Qed.

Global Instance into_wand_plainly_true q R P Q :
  IntoWand true q R P Q → IntoWand true q (■ R) P Q.
Proof. rewrite /IntoWand /= intuitionistically_plainly_elim //. Qed.
Global Instance into_wand_plainly_false q R P Q :
  Absorbing R → IntoWand false q R P Q → IntoWand false q (■ R) P Q.
Proof. intros ?. by rewrite /IntoWand plainly_elim. Qed.

Global Instance from_and_plainly P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite plainly_and. Qed.

Global Instance from_sep_plainly P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromSep=> <-. by rewrite plainly_sep_2. Qed.

Global Instance into_and_plainly p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (■ P) (■ Q1) (■ Q2).
Proof.
  rewrite /IntoAnd /=. destruct p; simpl.
  - rewrite -plainly_and -[(□ ■ P)%I]intuitionistically_idemp intuitionistically_plainly =>->.
    rewrite [(□ (_ ∧ _))%I]intuitionistically_elim //.
  - intros ->. by rewrite plainly_and.
Qed.

Global Instance into_sep_plainly `{!BiPositive PROP} P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (■ P) (■ Q1) (■ Q2).
Proof. rewrite /IntoSep /= => ->. by rewrite plainly_sep. Qed.
Global Instance into_sep_plainly_affine P Q1 Q2 :
  IntoSep P Q1 Q2 →
  TCOr (Affine Q1) (Absorbing Q2) → TCOr (Absorbing Q1) (Affine Q2) →
  IntoSep (■ P) (■ Q1) (■ Q2).
Proof.
  rewrite /IntoSep /= => -> ??. by rewrite sep_and plainly_and plainly_and_sep_l_1.
Qed.

Global Instance from_or_plainly P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (■ P) (■ Q1) (■ Q2).
Proof. rewrite /FromOr=> <-. by rewrite -plainly_or_2. Qed.

Global Instance into_or_plainly `{!BiPlainlyExist PROP} P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (■ P) (■ Q1) (■ Q2).
Proof. rewrite /IntoOr=>->. by rewrite plainly_or. Qed.

Global Instance from_exist_plainly {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite -plainly_exist_2. Qed.

Global Instance into_exist_plainly `{!BiPlainlyExist PROP} {A} P (Φ : A → PROP) name :
  IntoExist P Φ name → IntoExist (■ P) (λ a, ■ (Φ a))%I name.
Proof. rewrite /IntoExist=> HP. by rewrite HP plainly_exist. Qed.

Global Instance into_forall_plainly {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (■ P) (λ a, ■ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP plainly_forall. Qed.

Global Instance from_forall_plainly {A} P (Φ : A → PROP) name :
  FromForall P Φ name → FromForall (■ P) (λ a, ■ (Φ a))%I name.
Proof. rewrite /FromForall=> <-. by rewrite plainly_forall. Qed.

Global Instance from_modal_plainly P :
  FromModal True modality_plainly (■ P) (■ P) P | 2.
Proof. by rewrite /FromModal. Qed.

Global Instance into_except_0_plainly `{!BiPlainlyExist PROP} P Q :
  IntoExcept0 P Q → IntoExcept0 (■ P) (■ Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_plainly. Qed.

Global Instance into_later_plainly n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (■ P) (■ Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_plainly. Qed.
End class_instances_plainly.
