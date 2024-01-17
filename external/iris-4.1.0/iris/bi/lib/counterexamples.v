From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

(* The sections add extra BI assumptions, which is only picked up with "Type"*. *)
Set Default Proof Using "Type*".

(** This proves that in an affine BI (i.e., a BI that enjoys [P ∗ Q ⊢ P]), the
classical excluded middle ([P ∨ ¬P]) axiom makes the separation conjunction
trivial, i.e., it gives [P -∗ P ∗ P] and [P ∧ Q -∗ P ∗ Q].

Our proof essentially follows the structure of the proof of Theorem 3 in
https://scholar.princeton.edu/sites/default/files/qinxiang/files/putting_order_to_the_separation_logic_jungle_revised_version.pdf *)
Module affine_em. Section affine_em.
  Context {PROP : bi} `{!BiAffine PROP}.
  Context (em : ∀ P : PROP, ⊢ P ∨ ¬P).
  Implicit Types P Q : PROP.

  Lemma sep_dup P : P -∗ P ∗ P.
  Proof.
    iIntros "HP". iDestruct (em P) as "[HP'|HnotP]".
    - iFrame "HP HP'".
    - iExFalso. by iApply "HnotP".
  Qed.

  Lemma and_sep P Q : P ∧ Q -∗ P ∗ Q.
  Proof.
    iIntros "HPQ". iDestruct (sep_dup with "HPQ") as "[HPQ HPQ']".
    iSplitL "HPQ".
    - by iDestruct "HPQ" as "[HP _]".
    - by iDestruct "HPQ'" as "[_ HQ]".
  Qed.
End affine_em. End affine_em.

(** This proves that the combination of Löb induction [(▷ P → P) ⊢ P] and the
classical excluded-middle [P ∨ ¬P] axiom makes the later operator trivial, i.e.,
it gives [▷ P] for any [P], or equivalently [▷ P ≡ True]. *)
Module löb_em. Section löb_em.
  Context {PROP : bi} `{!BiLöb PROP}.
  Context (em : ∀ P : PROP, ⊢ P ∨ ¬P).
  Implicit Types P : PROP.

  Lemma later_anything P : ⊢@{PROP} ▷ P.
  Proof.
    iDestruct (em (▷ False)) as "#[HP|HnotP]".
    - iNext. done.
    - iExFalso. iLöb as "IH". iSpecialize ("HnotP" with "IH"). done.
  Qed.
End löb_em. End löb_em.

(** This proves that we need the ▷ in a "Saved Proposition" construction with
name-dependent allocation. *)
Module savedprop. Section savedprop.
  Context {PROP : bi} `{!BiAffine PROP}.
  Implicit Types P : PROP.

  Context (bupd : PROP → PROP).
  Notation "|==> Q" := (bupd Q) : bi_scope.

  Hypothesis bupd_intro : ∀ P, P ⊢ |==> P.
  Hypothesis bupd_mono : ∀ P Q, (P ⊢ Q) → (|==> P) ⊢ |==> Q.
  Hypothesis bupd_trans : ∀ P, (|==> |==> P) ⊢ |==> P.
  Hypothesis bupd_frame_r : ∀ P R, (|==> P) ∗ R ⊢ |==> (P ∗ R).

  Context (ident : Type) (saved : ident → PROP → PROP).
  Hypothesis sprop_persistent : ∀ i P, Persistent (saved i P).
  Hypothesis sprop_alloc_dep :
    ∀ (P : ident → PROP), ⊢ (|==> ∃ i, saved i (P i)).
  Hypothesis sprop_agree : ∀ i P Q, saved i P ∧ saved i Q ⊢ □ (P ↔ Q).

  (** We assume that we cannot update to false. *)
  Hypothesis consistency : ¬(⊢ |==> False).

  Global Instance bupd_mono' : Proper ((⊢) ==> (⊢)) bupd.
  Proof. intros P Q ?. by apply bupd_mono. Qed.
  Global Instance elim_modal_bupd p P Q : ElimModal True p false (|==> P) P (|==> Q) (|==> Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      bupd_frame_r bi.wand_elim_r bupd_trans.
  Qed.

  (** A bad recursive reference: "Assertion with name [i] does not hold" *)
  Definition A (i : ident) : PROP := ∃ P, □ ¬ P ∗ saved i P.

  Lemma A_alloc : ⊢ |==> ∃ i, saved i (A i).
  Proof. by apply sprop_alloc_dep. Qed.

  Lemma saved_NA i : saved i (A i) ⊢ ¬ A i.
  Proof.
    iIntros "#Hs #HA". iPoseProof "HA" as "HA'".
    iDestruct "HA'" as (P) "[HNP HsP]". iApply "HNP".
    iDestruct (sprop_agree i P (A i) with "[]") as "#[_ HP]".
    { eauto. }
    iApply "HP". done.
  Qed.

  Lemma saved_A i : saved i (A i) ⊢ A i.
  Proof.
    iIntros "#Hs". iExists (A i). iFrame "Hs".
    iIntros "!>". by iApply saved_NA.
  Qed.

  Lemma contradiction : False.
  Proof using All.
    apply consistency.
    iMod A_alloc as (i) "#H".
    iPoseProof (saved_NA with "H") as "HN".
    iApply bupd_intro. iApply "HN". iApply saved_A. done.
  Qed.
End savedprop. End savedprop.


(** This proves that we need the ▷ when opening invariants. We have two
paradoxes in this section, but they share the general axiomatization of
invariants. *)
Module inv. Section inv.
  Context {PROP : bi} `{!BiAffine PROP}.
  Implicit Types P : PROP.

  (** Assumptions *)
  (** We have the update modality (two classes: empty/full mask) *)
  Inductive mask := M0 | M1.
  Context (fupd : mask → PROP → PROP).
  Hypothesis fupd_intro : ∀ E P, P ⊢ fupd E P.
  Hypothesis fupd_mono : ∀ E P Q, (P ⊢ Q) → fupd E P ⊢ fupd E Q.
  Hypothesis fupd_fupd : ∀ E P, fupd E (fupd E P) ⊢ fupd E P.
  Hypothesis fupd_frame_l : ∀ E P Q, P ∗ fupd E Q ⊢ fupd E (P ∗ Q).
  Hypothesis fupd_mask_mono : ∀ P, fupd M0 P ⊢ fupd M1 P.

  (** We have invariants *)
  Context (name : Type) (inv : name → PROP → PROP).
  Global Arguments inv _ _%I.
  Hypothesis inv_persistent : ∀ i P, Persistent (inv i P).
  Hypothesis inv_alloc : ∀ P, P ⊢ fupd M1 (∃ i, inv i P).
  Hypothesis inv_fupd :
    ∀ i P Q R, (P ∗ Q ⊢ fupd M0 (P ∗ R)) → (inv i P ∗ Q ⊢ fupd M1 R).

  (** We assume that we cannot update to false. *)
  Hypothesis consistency : ¬ (⊢ fupd M1 False).

  (** This completes the general assumptions shared by both paradoxes. We set up
      some general lemmas and proof mode compatibility before proceeding with
      the paradoxes. *)
  Lemma inv_fupd' i P R : inv i P ∗ (P -∗ fupd M0 (P ∗ fupd M1 R)) ⊢ fupd M1 R.
  Proof.
    iIntros "(#HiP & HP)". iApply fupd_fupd. iApply inv_fupd; last first.
    { iSplit; first done. iExact "HP". }
    iIntros "(HP & HPw)". by iApply "HPw".
  Qed.

  Global Instance fupd_mono' E : Proper ((⊢) ==> (⊢)) (fupd E).
  Proof. intros P Q ?. by apply fupd_mono. Qed.
  Global Instance fupd_proper E : Proper ((⊣⊢) ==> (⊣⊢)) (fupd E).
  Proof.
    intros P Q; rewrite !bi.equiv_entails=> -[??]; split; by apply fupd_mono.
  Qed.

  Lemma fupd_frame_r E P Q : fupd E P ∗ Q ⊢ fupd E (P ∗ Q).
  Proof. by rewrite comm fupd_frame_l comm. Qed.

  Global Instance elim_fupd_fupd p E P Q :
    ElimModal True p false (fupd E P) P (fupd E Q) (fupd E Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_fupd.
  Qed.

  Global Instance elim_fupd0_fupd1 p P Q :
    ElimModal True p false (fupd M0 P) P (fupd M1 Q) (fupd M1 Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_mask_mono fupd_fupd.
  Qed.

  Global Instance exists_split_fupd0 {A} E P (Φ : A → PROP) :
    FromExist P Φ → FromExist (fupd E P) (λ a, fupd E (Φ a)).
  Proof.
    rewrite /FromExist=>HP. apply bi.exist_elim=> a.
    apply fupd_mono. by rewrite -HP -(bi.exist_intro a).
  Qed.

  (** The original paradox, as found in the "Iris from the Ground Up" paper. *)
  Section inv1.
    (** On top of invariants themselves, we need a particular kind of ghost state:
     we have tokens for a little "two-state STS": [start] -> [finish].
     [start] also asserts the exact state; it is only ever owned by the
     invariant. [finished] is duplicable. *)
    (** Posssible implementations of these axioms:
     - Using the STS monoid of a two-state STS, where [start] is the
       authoritative saying the state is exactly [start], and [finish]
       is the "we are at least in state [finish]" typically owned by threads.
     - Ex () +_## ()
     *)
    Context (gname : Type).
    Context (start finished : gname → PROP).

    Hypothesis sts_alloc : ⊢ fupd M0 (∃ γ, start γ).
    Hypotheses start_finish : ∀ γ, start γ ⊢ fupd M0 (finished γ).

    Hypothesis finished_not_start : ∀ γ, start γ ∗ finished γ ⊢ False.

    Hypothesis finished_dup : ∀ γ, finished γ ⊢ finished γ ∗ finished γ.

    (** Now to the actual counterexample. We start with a weird form of saved propositions. *)
    Definition saved (γ : gname) (P : PROP) : PROP :=
      ∃ i, inv i (start γ ∨ (finished γ ∗ □ P)).
    Global Instance saved_persistent γ P : Persistent (saved γ P) := _.

    Lemma saved_alloc (P : gname → PROP) : ⊢ fupd M1 (∃ γ, saved γ (P γ)).
    Proof.
      iIntros "". iMod (sts_alloc) as (γ) "Hs".
      iMod (inv_alloc (start γ ∨ (finished γ ∗ □ (P γ))) with "[Hs]") as (i) "#Hi".
      { auto. }
      iApply fupd_intro. by iExists γ, i.
    Qed.

    Lemma saved_cast γ P Q : saved γ P ∗ saved γ Q ∗ □ P ⊢ fupd M1 (□ Q).
    Proof.
      iIntros "(#HsP & #HsQ & #HP)". iDestruct "HsP" as (i) "HiP".
      iApply (inv_fupd' i). iSplit; first done.
      iIntros "HaP". iAssert (fupd M0 (finished γ)) with "[HaP]" as "> Hf".
      { iDestruct "HaP" as "[Hs | [Hf _]]".
        - by iApply start_finish.
        - by iApply fupd_intro. }
      iDestruct (finished_dup with "Hf") as "[Hf Hf']".
      iApply fupd_intro. iSplitL "Hf'"; first by eauto.
      (* Step 2: Open the Q-invariant. *)
      iClear (i) "HiP ". iDestruct "HsQ" as (i) "HiQ".
      iApply (inv_fupd' i). iSplit; first done.
      iIntros "[HaQ | [_ #HQ]]".
      { iExFalso. iApply finished_not_start. by iFrame. }
      iApply fupd_intro. iSplitL "Hf".
      { iRight. by iFrame. }
      by iApply fupd_intro.
    Qed.

    (** And now we tie a bad knot. *)
    Notation not_fupd P := (□ (P -∗ fupd M1 False))%I.
    Definition A i : PROP := ∃ P, not_fupd P ∗ saved i P.
    Global Instance A_persistent i : Persistent (A i) := _.

    Lemma A_alloc : ⊢ fupd M1 (∃ i, saved i (A i)).
    Proof. by apply saved_alloc. Qed.

    Lemma saved_NA i : saved i (A i) ⊢ not_fupd (A i).
    Proof.
      iIntros "#Hi !> #HA". iPoseProof "HA" as "HA'".
      iDestruct "HA'" as (P) "#[HNP Hi']".
      iMod (saved_cast i (A i) P with "[]") as "HP".
      { eauto. }
      by iApply "HNP".
    Qed.

    Lemma saved_A i : saved i (A i) ⊢ A i.
    Proof.
      iIntros "#Hi". iExists (A i). iFrame "#".
      by iApply saved_NA.
    Qed.

    Lemma contradiction : False.
    Proof using All.
      apply consistency. iIntros "".
      iMod A_alloc as (i) "#H".
      iPoseProof (saved_NA with "H") as "HN".
      iApply "HN". iApply saved_A. done.
    Qed.

  End inv1.

  (** This is another proof showing that we need the ▷ when opening invariants.
  Unlike the two paradoxes above, this proof does not rely on impredicative
  quantification -- at least, not directly. Instead it exploits the impredicative
  quantification that is implicit in [fupd]. Unlike the previous paradox,
  the [finish] token needs to be persistent for this paradox to work.

  This paradox is due to Yusuke Matsushita. *)
  Section inv2.
    (** On top of invariants themselves, we need a particular kind of ghost state:
     we have tokens for a little "two-state STS": [start] -> [finish].
     [start] also asserts the exact state; it is only ever owned by the
     invariant. [finished] is persistent. *)
    (** Posssible implementations of these axioms:
     - Using the STS monoid of a two-state STS, where [start] is the
       authoritative saying the state is exactly [start], and [finish]
       is the "we are at least in state [finish]" typically owned by threads.
     - Ex () +_## ()
     *)
    Context (gname : Type).
    Context (start finished : gname → PROP).

    Hypothesis sts_alloc : ⊢ fupd M0 (∃ γ, start γ).
    Hypotheses start_finish : ∀ γ, start γ ⊢ fupd M0 (finished γ).

    Hypothesis finished_not_start : ∀ γ, start γ ∗ finished γ ⊢ False.

    Hypothesis finished_persistent : ∀ γ, Persistent (finished γ).

    (** Now to the actual counterexample. *)
    (** A version of ⊥ behind a persistent update. *)
    Definition B : PROP := □ fupd M1 False.
    (** A delayed-initialization invariant storing [B]. *)
    Definition P (γ : gname) : PROP := start γ ∨ B.
    Definition I (i : name) (γ : gname) : PROP := inv i (P γ).

    (** If we can ever finish initializing the invariant, we have a
     contradiction. *)
    Lemma finished_contradiction γ i :
      finished γ ∗ I i γ -∗ B.
    Proof.
      iIntros "[#Hfin #HI] !>".
      iApply (inv_fupd' i). iSplit; first done.
      iIntros "[Hstart|#Hfalse]".
      { iDestruct (finished_not_start with "[$Hfin $Hstart]") as %[]. }
      iApply fupd_intro. iSplitR; last done.
      by iRight.
    Qed.

    (** If we can even just create the invariant, we can finish initializing it
     using the above lemma, and then get the contradiction. *)
    Lemma invariant_contradiction γ i :
      I i γ -∗ B.
    Proof.
      iIntros "#HI !>".
      iApply (inv_fupd' i). iSplit; first done.
      iIntros "HP".
      iAssert (fupd M0 B) with "[HP]" as ">#Hfalse".
      { iDestruct "HP" as "[Hstart|#Hfalse]"; last by iApply fupd_intro.
        iMod (start_finish with "Hstart"). iApply fupd_intro.
        (** There's a magic moment here where we have the invariant open,
          but inside [finished_contradiction] we will be proving
          a [fupd M1] and so we can open the invariant *again*.
          Really we are just building up a thunk that can be used
          later when the invariant is closed again. But to build up that
          thunk we can use resources that we just got out of the invariant,
          before closing it again. *)
        iApply finished_contradiction. eauto. }
      iApply fupd_intro. iSplitR; last done.
      by iRight.
    Qed.

    (** Of course, creating the invariant is trivial. *)
    Lemma contradiction' : False.
    Proof using All.
      apply consistency.
      iMod sts_alloc as (γ) "Hstart".
      iMod (inv_alloc (P γ) with "[Hstart]") as (i) "HI".
      { by iLeft. }
      iDestruct (invariant_contradiction with "HI") as "#>[]".
    Qed.

  End inv2.
End inv. End inv.

(** This proves that if we have linear impredicative invariants, we can still
drop arbitrary resources (i.e., we can "defeat" linearity).
We assume [cinv_alloc] without any bells or whistles.
Moreover, we also have an accessor that gives back the invariant token
immediately, not just after the invariant got closed again.

The assumptions here match the proof rules in Iron, save for the side-condition
that the invariant must be "uniform".  In particular, [cinv_alloc] delays
handing out the [cinv_own] token until after the invariant has been created so
that this can match Iron by picking [cinv_own γ := fcinv_own γ 1 ∗
fcinv_cancel_own γ 1]. This means [cinv_own] is not "uniform" in Iron terms,
which is why Iron does not suffer from this contradiction.

This also loosely matches VST's locks with stored resource invariants.
There, the stronger variant of the "unlock" rule (see Aquinas Hobor's PhD thesis
"Oracle Semantics", §4.7, p. 88) also permits putting the token of a lock
entirely into that lock.
*)
Module linear. Section linear.
  Context {PROP: bi}.
  Implicit Types P : PROP.

  (** Assumptions. *)
  (** We have the mask-changing update modality (two classes: empty/full mask) *)
  Inductive mask := M0 | M1.
  Context (fupd : mask → mask → PROP → PROP).
  Hypothesis fupd_intro : ∀ E P, P ⊢ fupd E E P.
  Hypothesis fupd_mono : ∀ E1 E2 P Q, (P ⊢ Q) → fupd E1 E2 P ⊢ fupd E1 E2 Q.
  Hypothesis fupd_fupd : ∀ E1 E2 E3 P, fupd E1 E2 (fupd E2 E3 P) ⊢ fupd E1 E3 P.
  Hypothesis fupd_frame_l : ∀ E1 E2 P Q, P ∗ fupd E1 E2 Q ⊢ fupd E1 E2 (P ∗ Q).

  (** We have cancelable invariants. (Really they would have fractions at
  [cinv_own] but we do not need that. They would also have a name matching
  the [mask] type, but we do not need that either.) *)
  Context (gname : Type) (cinv : gname → PROP → PROP) (cinv_own : gname → PROP).
  Hypothesis cinv_alloc : ∀ E P,
    ▷ P -∗ fupd E E (∃ γ, cinv γ P ∗ cinv_own γ).
  Hypothesis cinv_acc : ∀ P γ,
    cinv γ P -∗ cinv_own γ -∗ fupd M1 M0 (▷ P ∗ cinv_own γ ∗ (▷ P -∗ fupd M0 M1 emp)).

  (** Some general lemmas and proof mode compatibility. *)
  Global Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (fupd E1 E2).
  Proof. intros P Q ?. by apply fupd_mono. Qed.
  Global Instance fupd_proper E1 E2 : Proper ((⊣⊢) ==> (⊣⊢)) (fupd E1 E2).
  Proof.
    intros P Q; rewrite !bi.equiv_entails=> -[??]; split; by apply fupd_mono.
  Qed.

  Lemma fupd_frame_r E1 E2 P Q : fupd E1 E2 P ∗ Q ⊢ fupd E1 E2 (P ∗ Q).
  Proof. by rewrite comm fupd_frame_l comm. Qed.

  Global Instance elim_fupd_fupd p E1 E2 E3 P Q :
    ElimModal True p false (fupd E1 E2 P) P (fupd E1 E3 Q) (fupd E2 E3 Q).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_fupd.
  Qed.

  (** Counterexample: now we can make any resource disappear. *)
  Lemma leak P : P -∗ fupd M1 M1 emp.
  Proof.
    iIntros "HP".
    iMod (cinv_alloc _ True with "[//]") as (γ) "[Hinv Htok]".
    iMod (cinv_acc with "Hinv Htok") as "(Htrue & Htok & Hclose)".
    iApply "Hclose". done.
  Qed.
End linear. End linear.
