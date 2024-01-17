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
  Proof. intros. rewrite ownM_valid cmra_valid_elim. by apply pure_elim'. Qed.
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
  Lemma discrete_valid {A : cmra} `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
  Proof.
    apply (anti_symm _).
    - rewrite cmra_valid_elim. by apply pure_mono, cmra_discrete_valid.
    - apply pure_elim'=> ?. by apply cmra_valid_intro.
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

  (** Derive [NonExpansive]/[Contractive] from an internal statement *)
  Lemma ne_internal_eq {A B : ofe} (f : A → B) :
    NonExpansive f ↔ ∀ x1 x2, x1 ≡ x2 ⊢ f x1 ≡ f x2.
  Proof.
    split; [apply f_equivI|].
    intros Hf n x1 x2. by eapply internal_eq_entails.
  Qed.

  Lemma ne_2_internal_eq {A B C : ofe} (f : A → B → C) :
    NonExpansive2 f ↔ ∀ x1 x2 y1 y2, x1 ≡ x2 ∧ y1 ≡ y2 ⊢ f x1 y1 ≡ f x2 y2.
  Proof.
    split.
    - intros Hf x1 x2 y1 y2.
      change ((x1,y1).1 ≡ (x2,y2).1 ∧ (x1,y1).2 ≡ (x2,y2).2
        ⊢ uncurry f (x1,y1) ≡ uncurry f (x2,y2)).
      rewrite -prod_equivI. apply ne_internal_eq. solve_proper.
    - intros Hf n x1 x2 Hx y1 y2 Hy.
      change (uncurry f (x1,y1) ≡{n}≡ uncurry f (x2,y2)).
      apply ne_internal_eq; [|done].
      intros [??] [??]. rewrite prod_equivI. apply Hf.
  Qed.

  Lemma contractive_internal_eq {A B : ofe} (f : A → B) :
    Contractive f ↔ ∀ x1 x2, ▷ (x1 ≡ x2) ⊢ f x1 ≡ f x2.
  Proof.
    split; [apply f_equivI_contractive|].
    intros Hf n x1 x2 Hx. specialize (Hf x1 x2).
    rewrite -later_equivI internal_eq_entails in Hf. apply Hf. by f_contractive.
  Qed.

  (** Soundness statement for our modalities: facts derived under modalities in
  the empty context also without the modalities.
  For basic updates, soundness only holds for plain propositions. *)
  Lemma bupd_soundness P `{!Plain P} : (⊢ |==> P) → ⊢ P.
  Proof. rewrite bupd_elim. done. Qed.

  Lemma laterN_soundness P n : (⊢ ▷^n P) → ⊢ P.
  Proof. induction n; eauto using later_soundness. Qed.

  (** As pure demonstration, we also show that this holds for an arbitrary nesting
  of modalities. We have to do a bit of work to be able to state this theorem
  though. *)
  Inductive modality := MBUpd | MLater | MPersistently | MPlainly.
  Definition denote_modality (m : modality) : uPred M → uPred M :=
    match m with
    | MBUpd => bupd
    | MLater => bi_later
    | MPersistently => bi_persistently
    | MPlainly => plainly
    end.
  Definition denote_modalities (ms : list modality) : uPred M → uPred M :=
    λ P, foldr denote_modality P ms.

  (** Now we can state and prove 'soundness under arbitrary modalities' for plain
  propositions. This is probably not a lemma you want to actually use. *)
  Corollary modal_soundness P `{!Plain P} (ms : list modality) :
    (⊢ denote_modalities ms P) → ⊢ P.
  Proof.
    intros H. apply (laterN_soundness _ (length ms)).
    move: H. apply bi_emp_valid_mono.
    induction ms as [|m ms IH]; first done; simpl.
    destruct m; simpl; rewrite IH.
    - rewrite -later_intro. apply bupd_elim. apply _.
    - done.
    - rewrite -later_intro persistently_elim. done.
    - rewrite -later_intro plainly_elim. done.
  Qed.

  (** Consistency: one cannot deive [False] in the logic, not even under
  modalities. Again this is just for demonstration and probably not practically
  useful. *)
  Corollary consistency : ¬ ⊢@{uPredI M} False.
  Proof. intros H. by eapply pure_soundness. Qed.
End derived.
End uPred.
