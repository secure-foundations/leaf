From iris.bi Require Export bi.
From iris.si_logic Require Export siprop.
From iris.prelude Require Import options.
Import siProp_primitive.

(** BI instances for [siProp], and re-stating the remaining primitive laws in
terms of the BI interface.  This file does *not* unseal. *)

(** We pick [*] and [-*] to coincide with [∧] and [→], respectively. This seems
to be the most reasonable choice to fit a "pure" higher-order logic into the
proofmode's BI framework. *)
Definition siProp_emp : siProp := siProp_pure True.
Definition siProp_sep : siProp → siProp → siProp := siProp_and.
Definition siProp_wand : siProp → siProp → siProp := siProp_impl.
Definition siProp_persistently (P : siProp) : siProp := P.
Definition siProp_plainly (P : siProp) : siProp := P.

Local Existing Instance entails_po.

Lemma siProp_bi_mixin :
  BiMixin
    siProp_entails siProp_emp siProp_pure siProp_and siProp_or siProp_impl
    (@siProp_forall) (@siProp_exist) siProp_sep siProp_wand
    siProp_persistently.
Proof.
  split.
  - exact: entails_po.
  - exact: equiv_entails.
  - exact: pure_ne.
  - exact: and_ne.
  - exact: or_ne.
  - exact: impl_ne.
  - exact: forall_ne.
  - exact: exist_ne.
  - exact: and_ne.
  - exact: impl_ne.
  - solve_proper.
  - exact: pure_intro.
  - exact: pure_elim'.
  - exact: and_elim_l.
  - exact: and_elim_r.
  - exact: and_intro.
  - exact: or_intro_l.
  - exact: or_intro_r.
  - exact: or_elim.
  - exact: impl_intro_r.
  - exact: impl_elim_l'.
  - exact: @forall_intro.
  - exact: @forall_elim.
  - exact: @exist_intro.
  - exact: @exist_elim.
  - (* (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q' *)
    intros P P' Q Q' H1 H2. apply and_intro.
    + by etrans; first apply and_elim_l.
    + by etrans; first apply and_elim_r.
  - (* P ⊢ emp ∗ P *)
    intros P. apply and_intro; last done. by apply pure_intro.
  - (* emp ∗ P ⊢ P *)
    intros P. apply and_elim_r.
  - (* P ∗ Q ⊢ Q ∗ P *)
    intros P Q. apply and_intro; [ apply and_elim_r | apply and_elim_l ].
  - (* (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) *)
    intros P Q R. repeat apply and_intro.
    + etrans; first apply and_elim_l. by apply and_elim_l.
    + etrans; first apply and_elim_l. by apply and_elim_r.
    + apply and_elim_r.
  - (* (P ∗ Q ⊢ R) → P ⊢ Q -∗ R *)
    apply impl_intro_r.
  - (* (P ⊢ Q -∗ R) → P ∗ Q ⊢ R *)
    apply impl_elim_l'.
  - (* (P ⊢ Q) → <pers> P ⊢ <pers> Q *)
    done.
  - (* <pers> P ⊢ <pers> <pers> P *)
    done.
  - (* emp ⊢ <pers> emp *)
    done.
  - (* (∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a) *)
    done.
  - (* <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a) *)
    done.
  - (* <pers> P ∗ Q ⊢ <pers> P *)
    apply and_elim_l.
  - (* <pers> P ∧ Q ⊢ P ∗ Q *)
    done.
Qed.

Lemma siProp_bi_later_mixin :
  BiLaterMixin
    siProp_entails siProp_pure siProp_or siProp_impl
    (@siProp_forall) (@siProp_exist) siProp_sep siProp_persistently siProp_later.
Proof.
  split.
  - apply contractive_ne, later_contractive.
  - exact: later_mono.
  - exact: later_intro.
  - exact: @later_forall_2.
  - exact: @later_exist_false.
  - (* ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q *)
    intros P Q.
    apply and_intro; apply later_mono.
    + apply and_elim_l.
    + apply and_elim_r.
  - (* ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q) *)
    intros P Q.
    trans (siProp_forall (λ b : bool, siProp_later (if b then P else Q))).
    { apply forall_intro=> -[].
      - apply and_elim_l.
      - apply and_elim_r. }
    etrans; [apply later_forall_2|apply later_mono].
    apply and_intro.
    + refine (forall_elim true).
    + refine (forall_elim false).
  - (* ▷ <pers> P ⊢ <pers> ▷ P *)
    done.
  - (* <pers> ▷ P ⊢ ▷ <pers> P *)
    done.
  - exact: later_false_em.
Qed.

Canonical Structure siPropI : bi :=
  {| bi_ofe_mixin := ofe_mixin_of siProp;
     bi_bi_mixin := siProp_bi_mixin; bi_bi_later_mixin := siProp_bi_later_mixin |}.

Global Instance siProp_pure_forall : BiPureForall siPropI.
Proof. exact: @pure_forall_2. Qed.

Global Instance siProp_later_contractive : BiLaterContractive siPropI.
Proof. apply later_contractive. Qed.

Lemma siProp_internal_eq_mixin : BiInternalEqMixin siPropI (@siProp_internal_eq).
Proof.
  split.
  - exact: internal_eq_ne.
  - exact: @internal_eq_refl.
  - exact: @internal_eq_rewrite.
  - exact: @fun_ext.
  - exact: @sig_eq.
  - exact: @discrete_eq_1.
  - exact: @later_eq_1.
  - exact: @later_eq_2.
Qed.
Global Instance siProp_internal_eq : BiInternalEq siPropI :=
  {| bi_internal_eq_mixin := siProp_internal_eq_mixin |}.

Lemma siProp_plainly_mixin : BiPlainlyMixin siPropI siProp_plainly.
Proof.
  split; try done.
  - solve_proper.
  - (* P ⊢ ■ emp *)
    intros P. by apply pure_intro.
  - (* ■ P ∗ Q ⊢ ■ P *)
    intros P Q. apply and_elim_l.
Qed.
Global Instance siProp_plainlyC : BiPlainly siPropI :=
  {| bi_plainly_mixin := siProp_plainly_mixin |}.

Global Instance siProp_prop_ext : BiPropExt siPropI.
Proof. exact: prop_ext_2. Qed.

(** extra BI instances *)

Global Instance siProp_affine : BiAffine siPropI | 0.
Proof. intros P. exact: pure_intro. Qed.
(* Also add this to the global hint database, otherwise [eauto] won't work for
many lemmas that have [BiAffine] as a premise. *)
Global Hint Immediate siProp_affine : core.

Global Instance siProp_plain (P : siProp) : Plain P | 0.
Proof. done. Qed.
Global Instance siProp_persistent (P : siProp) : Persistent P.
Proof. done. Qed.

Global Instance siProp_plainly_exist_1 : BiPlainlyExist siPropI.
Proof. done. Qed.

(** Re-state/export soundness lemmas *)

Module siProp.
Section restate.
Lemma pure_soundness φ : (⊢@{siPropI} ⌜ φ ⌝) → φ.
Proof. apply pure_soundness. Qed.

Lemma internal_eq_soundness {A : ofe} (x y : A) : (⊢@{siPropI} x ≡ y) → x ≡ y.
Proof. apply internal_eq_soundness. Qed.

Lemma later_soundness (P : siProp) : (⊢ ▷ P) → ⊢ P.
Proof. apply later_soundness. Qed.
End restate.
End siProp.
