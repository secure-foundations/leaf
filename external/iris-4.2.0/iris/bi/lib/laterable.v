From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

(** The class of laterable assertions *)
Class Laterable {PROP : bi} (P : PROP) := laterable :
  P ⊢ ∃ Q, ▷ Q ∗ □ (▷ Q -∗ ◇ P).
Global Arguments Laterable {_} _%I : simpl never.
Global Arguments laterable {_} _%I {_}.
Global Hint Mode Laterable + ! : typeclass_instances.

(** Proofmode class for turning [P] into a laterable [Q].
    Will be the identity if [P] already is laterable, and add
    [▷] otherwise. *)
Class IntoLaterable {PROP : bi} (P Q : PROP) : Prop := {
  (** This is non-standard; usually we would just demand
      [P ⊢ make_laterable Q]. However, we need these stronger properties for
      the [make_laterable_id] hack in [atomic.v]. *)
  into_laterable : P ⊢ Q;
  into_laterable_result_laterable : Laterable Q;
}.
Global Arguments IntoLaterable {_} P%I Q%I.
Global Arguments into_laterable {_} P%I Q%I {_}.
Global Arguments into_laterable_result_laterable {_} P%I Q%I {_}.
Global Hint Mode IntoLaterable + ! - : typeclass_instances.

Section instances.
  Context {PROP : bi}.
  Implicit Types P : PROP.
  Implicit Types Ps : list PROP.

  Global Instance laterable_proper : Proper ((⊣⊢) ==> (↔)) (@Laterable PROP).
  Proof. solve_proper. Qed.

  Global Instance later_laterable P : Laterable (▷ P).
  Proof.
    rewrite /Laterable. iIntros "HP". iExists P. iFrame.
    iIntros "!> HP !>". done.
  Qed.

  Global Instance timeless_laterable P :
    Timeless P → Laterable P.
  Proof.
    rewrite /Laterable. iIntros (?) "HP". iExists P%I. iFrame.
    iSplitR; first by iNext. iIntros "!> >HP !>". done.
  Qed.

  (** This lemma is not very useful: It needs a strange assumption about
      emp, and most of the time intuitionistic propositions can be just kept
      around anyway and don't need to be "latered".  The lemma exists
      because the fact that it needs the side-condition is interesting;
      it is not an instance because it won't usually get used. *)
  Lemma intuitionistic_laterable P :
    Timeless (PROP:=PROP) emp → Affine P → Persistent P → Laterable P.
  Proof.
    rewrite /Laterable. iIntros (???) "#HP".
    iExists emp%I. iSplitL; first by iNext.
    iIntros "!> >_". done.
  Qed.

  (** This instance, together with the one below, can lead to massive
      backtracking, but only when searching for [Laterable]. In the future, it
      should be rewritten using [Hint Immediate] or [Hint Cut], where the latter
      is preferred once we figure out how to use it. *)
  Global Instance persistent_laterable `{!BiAffine PROP} P :
    Persistent P → Laterable P.
  Proof.
    intros ?. apply intuitionistic_laterable; apply _.
  Qed.

  Global Instance sep_laterable P Q :
    Laterable P → Laterable Q → Laterable (P ∗ Q).
  Proof.
    rewrite /Laterable. iIntros (LP LQ) "[HP HQ]".
    iDestruct (LP with "HP") as (P') "[HP' #HP]".
    iDestruct (LQ with "HQ") as (Q') "[HQ' #HQ]".
    iExists (P' ∗ Q')%I. iSplitL; first by iFrame.
    iIntros "!> [HP' HQ']". iSplitL "HP'".
    - iApply "HP". done.
    - iApply "HQ". done.
  Qed.

  Global Instance exist_laterable {A} (Φ : A → PROP) :
    (∀ x, Laterable (Φ x)) → Laterable (∃ x, Φ x).
  Proof.
    rewrite /Laterable. iIntros (LΦ). iDestruct 1 as (x) "H".
    iDestruct (LΦ with "H") as (Q) "[HQ #HΦ]".
    iExists Q. iIntros "{$HQ} !> HQ". iExists x. by iApply "HΦ".
  Qed.

  Lemma big_sep_sepL_laterable Q Ps :
    Laterable Q →
    TCForall Laterable Ps →
    Laterable (Q ∗ [∗] Ps).
  Proof.
    intros HQ HPs. revert Q HQ. induction HPs as [|P Ps ?? IH]; intros Q HQ.
    { simpl. rewrite right_id. done. }
    simpl. rewrite assoc. apply IH; by apply _.
  Qed.

  Global Instance big_sepL_laterable Ps :
    Laterable (PROP:=PROP) emp →
    TCForall Laterable Ps →
    Laterable ([∗] Ps).
  Proof.
    intros. assert (Laterable (emp ∗ [∗] Ps)) as Hlater.
    { apply big_sep_sepL_laterable; done. }
    rewrite ->left_id in Hlater; last by apply _. done.
  Qed.

  (** A wrapper to obtain a weaker, laterable form of any assertion.
     Alternatively: the modality corresponding to [Laterable].
     The ◇ is required to make [make_laterable_intro'] hold.
   TODO: Define [Laterable] in terms of this (see [laterable_alt] below). *)
  Definition make_laterable (Q : PROP) : PROP :=
    ∃ P, ▷ P ∗ □ (▷ P -∗ ◇ Q).

  Global Instance make_laterable_ne : NonExpansive make_laterable.
  Proof. solve_proper. Qed.
  Global Instance make_laterable_proper : Proper ((≡) ==> (≡)) make_laterable := ne_proper _.
  Global Instance make_laterable_mono' : Proper ((⊢) ==> (⊢)) make_laterable.
  Proof. solve_proper. Qed.
  Global Instance make_laterable_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) make_laterable.
  Proof. solve_proper. Qed.

  Lemma make_laterable_mono Q1 Q2 :
    (Q1 ⊢ Q2) → (make_laterable Q1 ⊢ make_laterable Q2).
  Proof. by intros ->. Qed.

  Lemma make_laterable_except_0 Q :
    make_laterable (◇ Q) ⊢ make_laterable Q.
  Proof.
    iIntros "(%P & HP & #HPQ)". iExists P. iFrame.
    iIntros "!# HP". iMod ("HPQ" with "HP"). done.
  Qed.

  Lemma make_laterable_sep Q1 Q2 :
    make_laterable Q1 ∗ make_laterable Q2 ⊢ make_laterable (Q1 ∗ Q2).
  Proof.
    iIntros "[HQ1 HQ2]".
    iDestruct "HQ1" as (P1) "[HP1 #HQ1]".
    iDestruct "HQ2" as (P2) "[HP2 #HQ2]".
    iExists (P1 ∗ P2)%I. iFrame. iIntros "!# [HP1 HP2]".
    iDestruct ("HQ1" with "HP1") as ">$".
    iDestruct ("HQ2" with "HP2") as ">$".
    done.
  Qed.

  (** A stronger version of [make_laterable_mono] that lets us keep laterable
  resources. We cannot keep arbitrary resources since that would let us "frame
  in" non-laterable things. *)
  Lemma make_laterable_wand Q1 Q2 :
    make_laterable (Q1 -∗ Q2) ⊢ (make_laterable Q1 -∗ make_laterable Q2).
  Proof.
    iIntros "HQ HQ1".
    iDestruct (make_laterable_sep with "[$HQ $HQ1 //]") as "HQ".
    iApply make_laterable_mono; last done.
    by rewrite bi.wand_elim_l.
  Qed.

  (** A variant of the above for keeping arbitrary intuitionistic resources.
      Sadly, this is not implied by the above for non-affine BIs. *)
  Lemma make_laterable_intuitionistic_wand Q1 Q2 :
    □ (Q1 -∗ Q2) ⊢ (make_laterable Q1 -∗ make_laterable Q2).
  Proof.
    iIntros "#HQ HQ1". iDestruct "HQ1" as (P) "[HP #HQ1]".
    iExists P. iFrame. iIntros "!> HP".
    iDestruct ("HQ1" with "HP") as "{HQ1} >HQ1".
    iModIntro. iApply "HQ". done.
  Qed.

  Global Instance make_laterable_laterable Q :
    Laterable (make_laterable Q).
  Proof.
    rewrite /Laterable. iIntros "HQ". iDestruct "HQ" as (P) "[HP #HQ]".
    iExists P. iFrame. iIntros "!> HP !>". iExists P. by iFrame.
  Qed.

  Lemma make_laterable_elim Q :
    make_laterable Q ⊢ ◇ Q.
  Proof.
    iIntros "HQ". iDestruct "HQ" as (P) "[HP #HQ]". by iApply "HQ".
  Qed.

  (** Written internally (as an entailment of wands) to reflect
      that persistent assertions can be kept unchanged. *)
  Lemma make_laterable_intro P Q :
    Laterable P →
    □ (P -∗ Q) -∗ P -∗ make_laterable Q.
  Proof.
    iIntros (?) "#HQ HP".
    iDestruct (laterable with "HP") as (P') "[HP' #HPi]". iExists P'.
    iFrame. iIntros "!> HP'".
    iDestruct ("HPi" with "HP'") as ">HP". iModIntro.
    iApply "HQ". done.
  Qed.
  Lemma make_laterable_intro' Q :
    Laterable Q →
    Q ⊢ make_laterable Q.
  Proof.
    intros ?. iApply make_laterable_intro. iIntros "!# $".
  Qed.

  Lemma make_laterable_idemp Q :
    make_laterable (make_laterable Q) ⊣⊢ make_laterable Q.
  Proof.
    apply (anti_symm (⊢)).
    - trans (make_laterable (◇ Q)).
      + apply make_laterable_mono, make_laterable_elim.
      + apply make_laterable_except_0.
    - apply make_laterable_intro', _.
  Qed.

  Lemma laterable_alt Q :
    Laterable Q ↔ (Q ⊢ make_laterable Q).
  Proof.
    split.
    - intros ?. apply make_laterable_intro'. done.
    - intros ?. done.
  Qed.

  (** * Proofmode integration

      We integrate [make_laterable] with [iModIntro]. All non-laterable
      hypotheses have a ▷ added in front of them to ensure a laterable context.
  *)
  Global Instance into_laterable_laterable P :
    Laterable P →
    IntoLaterable P P.
  Proof. intros ?. constructor; done. Qed.

  Global Instance into_laterable_fallback P :
    IntoLaterable P (▷ P) | 100.
  Proof. constructor; last by apply _. apply bi.later_intro. Qed.

  Lemma modality_make_laterable_mixin `{!Timeless (PROP:=PROP) emp} :
    modality_mixin make_laterable MIEnvId (MIEnvTransform IntoLaterable).
  Proof.
    split; simpl; eauto using make_laterable_intro', make_laterable_mono,
      make_laterable_sep, intuitionistic_laterable with typeclass_instances; [].
    intros P Q ?. rewrite (into_laterable P).
    apply make_laterable_intro'. eapply (into_laterable_result_laterable P), _.
  Qed.

  Definition modality_make_laterable `{!Timeless (PROP:=PROP) emp} :=
    Modality _ modality_make_laterable_mixin.

  Global Instance from_modal_make_laterable `{!Timeless (PROP:=PROP) emp} P :
    FromModal True modality_make_laterable (make_laterable P) (make_laterable P) P.
  Proof. by rewrite /FromModal. Qed.

End instances.

Global Typeclasses Opaque make_laterable.
