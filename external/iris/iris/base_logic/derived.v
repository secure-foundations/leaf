From iris.algebra Require Import frac.
From iris.bi Require Export bi.
From iris.base_logic Require Export bi.
From iris.prelude Require Import options.
Import bi.bi base_logic.bi.uPred.

(** Derived laws for Iris-specific primitive connectives (own, valid).
    This file does NOT unseal! *)

Module uPred.
Section derived.
Context {M : ucmra}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P Q).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

(** Propers *)
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@uPred_ownM M) := ne_proper _.
Global Instance cmra_valid_proper {A : cmra} :
  Proper ((≡) ==> (⊣⊢)) (@uPred_cmra_valid M A) := ne_proper _.

(** Own and valid derived *)
Lemma persistently_cmra_valid_1 {A : cmra} (a : A) : ✓ a ⊢@{uPredI M} <pers> (✓ a).
Proof. by rewrite {1}plainly_cmra_valid_1 plainly_elim_persistently. Qed.
Lemma intuitionistically_ownM (a : M) : CoreId a → □ uPred_ownM a ⊣⊢ uPred_ownM a.
Proof.
  rewrite /bi_intuitionistically affine_affinely=>?; apply (anti_symm _);
    [by rewrite persistently_elim|].
  by rewrite {1}persistently_ownM_core core_id_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → uPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid cmra_valid_elim. Qed.
Global Instance ownM_mono : Proper (flip (≼) ==> (⊢)) (@uPred_ownM M).
Proof. intros a b [b' ->]. by rewrite ownM_op sep_elim_l. Qed.
Lemma ownM_unit' : uPred_ownM ε ⊣⊢ True.
Proof. apply (anti_symm _); first by apply pure_intro. apply ownM_unit. Qed.
Lemma plainly_cmra_valid {A : cmra} (a : A) : ■ ✓ a ⊣⊢ ✓ a.
Proof. apply (anti_symm _), plainly_cmra_valid_1. apply plainly_elim, _. Qed.
Lemma intuitionistically_cmra_valid {A : cmra} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof.
  rewrite /bi_intuitionistically affine_affinely. intros; apply (anti_symm _);
    first by rewrite persistently_elim.
  apply:persistently_cmra_valid_1.
Qed.
Lemma bupd_ownM_update x y : x ~~> y → uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =.)); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.

(** Timeless instances *)
Global Instance valid_timeless {A : cmra} `{!CmraDiscrete A} (a : A) :
  Timeless (✓ a : uPred M)%I.
Proof. rewrite /Timeless !discrete_valid. apply (timeless _). Qed.
Global Instance ownM_timeless (a : M) : Discrete a → Timeless (uPred_ownM a).
Proof.
  intros ?. rewrite /Timeless later_ownM. apply exist_elim=> b.
  rewrite (timeless (a≡b)) (except_0_intro (uPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym.
  apply (internal_eq_rewrite' b a (uPred_ownM) _);
    auto using and_elim_l, and_elim_r.
Qed.

(** Plainness *)
Global Instance cmra_valid_plain {A : cmra} (a : A) :
  Plain (✓ a : uPred M)%I.
Proof. rewrite /Persistent. apply plainly_cmra_valid_1. Qed.

(** Persistence *)
Global Instance cmra_valid_persistent {A : cmra} (a : A) :
  Persistent (✓ a : uPred M)%I.
Proof. rewrite /Persistent. apply persistently_cmra_valid_1. Qed.
Global Instance ownM_persistent a : CoreId a → Persistent (@uPred_ownM M a).
Proof.
  intros. rewrite /Persistent -{2}(core_id_core a). apply persistently_ownM_core.
Qed.

(** For big ops *)
Global Instance uPred_ownM_sep_homomorphism :
  MonoidHomomorphism op uPred_sep (≡) (@uPred_ownM M).
Proof. split; [split|]; try apply _; [apply ownM_op | apply ownM_unit']. Qed.

(** Consistency/soundness statement *)
Lemma bupd_plain_soundness P `{!Plain P} : (⊢ |==> P) → ⊢ P.
Proof.
  eapply bi_emp_valid_mono. etrans; last exact: bupd_plainly. apply bupd_mono'.
  apply: plain.
Qed.

Corollary soundness φ n : (⊢@{uPredI M} ▷^n ⌜ φ ⌝) → φ.
Proof.
  induction n as [|n IH]=> /=.
  - apply pure_soundness.
  - intros H. by apply IH, later_soundness.
Qed.

Corollary consistency_modal n : ¬ ⊢@{uPredI M} ▷^n False.
Proof. exact (soundness False n). Qed.

Corollary consistency : ¬ ⊢@{uPredI M} False.
Proof. exact (consistency_modal 0). Qed.
End derived.

End uPred.
