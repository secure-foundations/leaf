From iris.bi Require Export bi plainly.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
Import bi.

(** The "core" of an assertion is its maximal persistent part,
    i.e. the conjunction of all persistent assertions that are weaker
    than P (as in, implied by P). *)
Definition coreP `{!BiPlainly PROP} (P : PROP) : PROP :=
  (* TODO: Looks like we want notation for affinely-plainly; that lets us avoid
  using conjunction/implication here. *)
  ∀ Q : PROP, <affine> ■ (Q -∗ <pers> Q) -∗ <affine> ■ (P -∗ Q) -∗ Q.
Global Instance: Params (@coreP) 1 := {}.
Typeclasses Opaque coreP.

Section core.
  Context `{!BiPlainly PROP}.
  Implicit Types P Q : PROP.

  Lemma coreP_intro P : P -∗ coreP P.
  Proof.
    rewrite /coreP. iIntros "HP" (Q) "_ HPQ".
    (* FIXME: Cannot apply HPQ directly. This works if we move it to the
    persistent context, but why should we? *)
    iDestruct (affinely_plainly_elim with "HPQ") as "HPQ".
    by iApply "HPQ".
  Qed.

  Global Instance coreP_persistent P : Persistent (coreP P).
  Proof.
    rewrite /coreP /Persistent. iIntros "HC" (Q).
    iApply persistently_wand_affinely_plainly. iIntros "#HQ".
    iApply persistently_wand_affinely_plainly. iIntros "#HPQ".
    iApply "HQ". iApply "HC"; auto.
  Qed.
  Global Instance coreP_affine P : Affine P → Affine (coreP P).
  Proof. intros ?. rewrite /coreP /Affine. iIntros "HC". iApply "HC"; eauto. Qed.

  Global Instance coreP_ne : NonExpansive (coreP (PROP:=PROP)).
  Proof. solve_proper. Qed.
  Global Instance coreP_proper : Proper ((⊣⊢) ==> (⊣⊢)) (coreP (PROP:=PROP)).
  Proof. solve_proper. Qed.

  Global Instance coreP_mono : Proper ((⊢) ==> (⊢)) (coreP (PROP:=PROP)).
  Proof. solve_proper. Qed.
  Global Instance coreP_flip_mono :
    Proper (flip (⊢) ==> flip (⊢)) (coreP (PROP:=PROP)).
  Proof. solve_proper. Qed.

  Lemma coreP_wand P Q : <affine> ■ (P -∗ Q) -∗ coreP P -∗ coreP Q.
  Proof.
    rewrite /coreP. iIntros "#HPQ HP" (R) "#HR #HQR". iApply ("HP" with "HR").
    iIntros "!> !> HP". iApply "HQR". by iApply "HPQ".
  Qed.

  Lemma coreP_elim P : Persistent P → coreP P -∗ P.
  Proof. rewrite /coreP. iIntros (?) "HCP". iApply "HCP"; auto. Qed.

  (** The [<affine>] modality is needed for general BIs:
  - The right-to-left direction corresponds to elimination of [<pers>], which
    cannot be done without [<affine>].
  - The left-to-right direction corresponds the introduction of [<pers>]. The
    [<affine>] modality makes it stronger since it appears in the LHS of the
    [⊢] in the premise. As a user, you have to prove [<affine> coreP P ⊢ Q],
    which is weaker than [coreP P ⊢ Q]. *)
  Lemma coreP_entails P Q : (<affine> coreP P ⊢ Q) ↔ (P ⊢ <pers> Q).
  Proof.
    split.
    - iIntros (HP) "HP". iDestruct (coreP_intro with "HP") as "#HcP {HP}".
      iIntros "!>". by iApply HP.
    - iIntros (->) "HcQ". by iDestruct (coreP_elim with "HcQ") as "#HQ".
  Qed.
  (** A more convenient variant of the above lemma for affine [P]. *)
  Lemma coreP_entails' P Q `{!Affine P} : (coreP P ⊢ Q) ↔ (P ⊢ □ Q).
  Proof.
    rewrite -(affine_affinely (coreP P)) coreP_entails. split.
    - rewrite -{2}(affine_affinely P). by intros ->.
    - intros ->. apply affinely_elim.
  Qed.
End core.
