From iris.proofmode Require Import tactics.
From iris.base_logic Require Export base_logic.
From iris.prelude Require Import options.

(* The sections add extra BI assumptions, which is only picked up with [Type*]. *)
Set Default Proof Using "Type*".

(** This file contains an alternative version of basic updates, that is
expression in terms of just the plain modality [■]. *)
Definition bupd_alt `{BiPlainly PROP} (P : PROP) : PROP :=
  ∀ R, (P -∗ ■ R) -∗ ■ R.

(** This definition is stated for any BI with a plain modality. The above
definition is akin to the continuation monad, where one should think of [■ R]
being the final result that one wants to get out of the basic update in the end
of the day (via [bupd_alt (■ P) ⊢ ■ P]).

We show that:

1. [bupd_alt] enjoys the usual rules of the basic update modality.
2. [bupd_alt] entails any other modality that enjoys the laws of a basic update
   modality (see [bupd_bupd_alt]).
3. The ordinary basic update modality [|==>] on [uPred] entails [bupd_alt]
   (see [bupd_alt_bupd]). This result is proven in the model of [uPred].

The first two points are shown for any BI with a plain modality. *)

Local Coercion uPred_holds : uPred >-> Funclass.

Section bupd_alt.
  Context `{BiPlainly PROP}.
  Implicit Types P Q R : PROP.
  Notation bupd_alt := (@bupd_alt PROP _).

  Global Instance bupd_alt_ne : NonExpansive bupd_alt.
  Proof. solve_proper. Qed.
  Global Instance bupd_alt_proper : Proper ((≡) ==> (≡)) bupd_alt.
  Proof. solve_proper. Qed.
  Global Instance bupd_alt_mono' : Proper ((⊢) ==> (⊢)) bupd_alt.
  Proof. solve_proper. Qed.
  Global Instance bupd_alt_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) bupd_alt.
  Proof. solve_proper. Qed.

  (** The laws of the basic update modality hold *)
  Lemma bupd_alt_intro P : P ⊢ bupd_alt P.
  Proof. iIntros "HP" (R) "H". by iApply "H". Qed.
  Lemma bupd_alt_mono P Q : (P ⊢ Q) → bupd_alt P ⊢ bupd_alt Q.
  Proof. by intros ->. Qed.
  Lemma bupd_alt_trans P : bupd_alt (bupd_alt P) ⊢ bupd_alt P.
  Proof. iIntros "HP" (R) "H". iApply "HP". iIntros "HP". by iApply "HP". Qed.
  Lemma bupd_alt_frame_r P Q : bupd_alt P ∗ Q ⊢ bupd_alt (P ∗ Q).
  Proof.
    iIntros "[HP HQ]" (R) "H". iApply "HP". iIntros "HP". iApply ("H" with "[$]").
  Qed.
  Lemma bupd_alt_plainly P : bupd_alt (■ P) ⊢ ■ P.
  Proof. iIntros "H". iApply ("H" $! P with "[]"); auto. Qed.

  (** Any modality conforming with [BiBUpdPlainly] entails the alternative
  definition *)
  Lemma bupd_bupd_alt `{!BiBUpd PROP, BiBUpdPlainly PROP} P : (|==> P) ⊢ bupd_alt P.
  Proof. iIntros "HP" (R) "H". by iMod ("H" with "HP") as "?". Qed.

  (** We get the usual rule for frame preserving updates if we have an [own]
  connective satisfying the following rule w.r.t. interaction with plainly. *)
  Context {M : ucmra} (own : M → PROP).
  Context (own_updateP_plainly : ∀ x Φ R,
    x ~~>: Φ →
    own x ∗ (∀ y, ⌜Φ y⌝ -∗ own y -∗ ■ R) ⊢ ■ R).

  Lemma own_updateP x (Φ : M → Prop) :
    x ~~>: Φ → own x ⊢ bupd_alt (∃ y, ⌜Φ y⌝ ∧ own y).
  Proof.
    iIntros (Hup) "Hx"; iIntros (R) "H".
    iApply (own_updateP_plainly with "[$Hx H]"); first done.
    iIntros (y ?) "Hy". iApply "H"; auto.
  Qed.
End bupd_alt.

(** The alternative definition entails the ordinary basic update *)
Lemma bupd_alt_bupd {M} (P : uPred M) : bupd_alt P ⊢ |==> P.
Proof.
  rewrite /bupd_alt. uPred.unseal; split=> n x Hx H k y ? Hxy.
  unshelve refine (H {| uPred_holds k _ :=
    ∃ x' : M, ✓{k} (x' ⋅ y) ∧ P k x' |} k y _ _ _).
  - intros n1 n2 x1 x2 (z&?&?) _ ?.
    eauto using cmra_validN_le, uPred_mono.
  - done.
  - done.
  - intros k' z ?? HP. exists z. by rewrite (comm op).
Qed.

Lemma bupd_alt_bupd_iff {M} (P : uPred M) : bupd_alt P ⊣⊢ |==> P.
Proof.
  apply (anti_symm _).
  - apply bupd_alt_bupd.
  - apply bupd_bupd_alt.
Qed.

(** The law about the interaction between [uPred_ownM] and plainly holds. *)
Lemma ownM_updateP {M : ucmra} x (Φ : M → Prop) (R : uPred M) :
  x ~~>: Φ →
  uPred_ownM x ∗ (∀ y, ⌜Φ y⌝ -∗ uPred_ownM y -∗ ■ R) ⊢ ■ R.
Proof.
  uPred.unseal=> Hup; split; intros n z Hv (?&z2&?&[z1 ?]&HR); ofe_subst.
  destruct (Hup n (Some (z1 ⋅ z2))) as (y&?&?); simpl in *.
  { by rewrite assoc. }
  refine (HR y n z1 _ _ _ n y _ _ _); auto.
  - rewrite comm. by eapply cmra_validN_op_r.
  - by rewrite (comm _ _ y) (comm _ z2).
  - apply (reflexivity (R:=includedN _)).
Qed.
