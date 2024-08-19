(** This file implements later credits, in particular the later-elimination update.
That update is used internally to define the Iris [fupd]; it should not
usually be directly used unless you are defining your own [fupd]. *)
From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.algebra Require Export auth numbers.
From iris.base_logic.lib Require Import iprop own.
Import uPred.


(** The ghost state for later credits *)
Class lcGpreS (Σ : gFunctors) := LcGpreS {
  lcGpreS_inG : inG Σ (authR natUR)
}.

Class lcGS (Σ : gFunctors) := LcGS {
  lcGS_inG : inG Σ (authR natUR);
  lcGS_name : gname;
}.
Global Hint Mode lcGS - : typeclass_instances.
Local Existing Instances lcGS_inG lcGpreS_inG.

Definition lcΣ := #[GFunctor (authR (natUR))].
Global Instance subG_lcΣ {Σ} : subG lcΣ Σ → lcGpreS Σ.
Proof. solve_inG. Qed.


(** The user-facing credit resource, denoting ownership of [n] credits. *)
Local Definition lc_def `{!lcGS Σ} (n : nat) : iProp Σ := own lcGS_name (◯ n).
Local Definition lc_aux : seal (@lc_def). Proof. by eexists. Qed.
Definition lc := lc_aux.(unseal).
Local Definition lc_unseal :
  @lc = @lc_def := lc_aux.(seal_eq).
Global Arguments lc {Σ _} n.

Notation "'£'  n" := (lc n) (at level 1).

(** The internal authoritative part of the credit ghost state,
  tracking how many credits are available in total.
  Users should not directly interface with this. *)
Local Definition lc_supply_def `{!lcGS Σ} (n : nat) : iProp Σ := own lcGS_name (● n).
Local Definition lc_supply_aux : seal (@lc_supply_def). Proof. by eexists. Qed.
Local Definition lc_supply := lc_supply_aux.(unseal).
Local Definition lc_supply_unseal :
  @lc_supply = @lc_supply_def := lc_supply_aux.(seal_eq).
Global Arguments lc_supply {Σ _} n.


Section later_credit_theory.
  Context `{!lcGS Σ}.
  Implicit Types (P Q : iProp Σ).

  (** Later credit rules *)
  Lemma lc_split n m :
    £ (n + m) ⊣⊢ £ n ∗ £ m.
  Proof.
    rewrite lc_unseal /lc_def.
    rewrite -own_op auth_frag_op //=.
  Qed.

  Lemma lc_zero : ⊢ |==> £ 0.
  Proof.
    rewrite lc_unseal /lc_def. iApply own_unit.
  Qed.

  Lemma lc_supply_bound n m :
    lc_supply m -∗ £ n -∗ ⌜n ≤ m⌝.
  Proof.
    rewrite lc_unseal /lc_def.
    rewrite lc_supply_unseal /lc_supply_def.
    iIntros "H1 H2".
    iCombine "H1 H2" gives %Hop.
    iPureIntro. eapply auth_both_valid_discrete in Hop as [Hlt _].
    by eapply nat_included.
  Qed.

  Lemma lc_decrease_supply n m :
    lc_supply (n + m) -∗ £ n -∗ |==> lc_supply m.
  Proof.
    rewrite lc_unseal /lc_def.
    rewrite lc_supply_unseal /lc_supply_def.
    iIntros "H1 H2".
    iMod (own_update_2 with "H1 H2") as "Hown".
    { eapply auth_update. eapply (nat_local_update _ _ m 0). lia. }
    by iDestruct "Hown" as "[Hm _]".
  Qed.

  Lemma lc_succ n :
    £ (S n) ⊣⊢ £ 1 ∗ £ n.
  Proof. rewrite -lc_split //=. Qed.

  Lemma lc_weaken {n} m :
    m ≤ n → £ n -∗ £ m.
  Proof.
    intros [k ->]%Nat.le_sum. rewrite lc_split. iIntros "[$ _]".
  Qed.

  Global Instance lc_timeless n : Timeless (£ n).
  Proof.
    rewrite lc_unseal /lc_def. apply _.
  Qed.

  Global Instance lc_0_persistent : Persistent (£ 0).
  Proof.
    rewrite lc_unseal /lc_def. apply _.
  Qed.

  (** Make sure that the rule for [+] is used before [S], otherwise Coq's
  unification applies the [S] hint too eagerly. See Iris issue #470. *)
  Global Instance from_sep_lc_add n m :
    FromSep (£ (n + m)) (£ n) (£ m) | 0.
  Proof.
    by rewrite /FromSep lc_split.
  Qed.
  Global Instance from_sep_lc_S n :
    FromSep (£ (S n)) (£ 1) (£ n) | 1.
  Proof.
    by rewrite /FromSep (lc_succ n).
  Qed.
  (** When combining later credits with [iCombine], the priorities are
  reversed when compared to [FromSep] and [IntoSep]. This causes
  [£ n] and [£ 1] to be combined as [£ (S n)], not as [£ (n + 1)]. *)
  Global Instance combine_sep_lc_add n m :
    CombineSepAs (£ n) (£ m) (£ (n + m)) | 1.
  Proof.
    by rewrite /CombineSepAs lc_split.
  Qed.
  Global Instance combine_sep_lc_S_l n :
    CombineSepAs (£ n) (£ 1) (£ (S n)) | 0.
  Proof.
    by rewrite /CombineSepAs comm (lc_succ n).
  Qed.

  Global Instance into_sep_lc_add n m :
    IntoSep (£ (n + m)) (£ n) (£ m) | 0.
  Proof.
    by rewrite /IntoSep lc_split.
  Qed.
  Global Instance into_sep_lc_S n :
    IntoSep (£ (S n)) (£ 1) (£ n) | 1.
  Proof.
    by rewrite /IntoSep (lc_succ n).
  Qed.
End later_credit_theory.

(** Let users import the above without also getting the below laws.
  This should only be imported by the internal development of fancy updates. *)
Module le_upd.
  (** Definition of the later-elimination update *)
  Definition le_upd_pre `{!lcGS Σ}
      (le_upd : iProp Σ -d> iPropO Σ) : iProp Σ -d> iPropO Σ := λ P,
    (∀ n, lc_supply n ==∗
          (lc_supply n ∗ P) ∨ (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ le_upd P))%I.

  Local Instance le_upd_pre_contractive `{!lcGS Σ} : Contractive le_upd_pre.
  Proof. solve_contractive. Qed.
  Local Definition le_upd_def `{!lcGS Σ} :
    iProp Σ -d> iPropO Σ := fixpoint le_upd_pre.
  Local Definition le_upd_aux : seal (@le_upd_def). Proof. by eexists. Qed.
  Definition le_upd := le_upd_aux.(unseal).
  Local Definition le_upd_unseal : @le_upd = @le_upd_def := le_upd_aux.(seal_eq).
  Global Arguments le_upd {_ _} _.
  Notation "'|==£>' P" := (le_upd P%I) (at level 99, P at level 200, format "|==£>  P") : bi_scope.

  Local Lemma le_upd_unfold `{!lcGS Σ} P:
    (|==£> P) ⊣⊢
    ∀ n, lc_supply n ==∗
         (lc_supply n ∗ P) ∨ (∃ m, ⌜m < n⌝ ∗ lc_supply m ∗ ▷ le_upd P).
  Proof.
    by rewrite le_upd_unseal
      /le_upd_def {1}(fixpoint_unfold le_upd_pre P) {1}/le_upd_pre.
  Qed.

  Section le_upd.
    Context `{!lcGS Σ}.
    Implicit Types (P Q : iProp Σ).

    (** Rules for the later elimination update *)
    Global Instance le_upd_ne : NonExpansive le_upd.
    Proof.
      intros n; induction (lt_wf n) as [n _ IH].
      intros P1 P2 HP. rewrite (le_upd_unfold P1) (le_upd_unfold P2).
      do 9 (done || f_equiv). f_contractive. eapply IH, dist_le; [lia|done|lia].
    Qed.

    Lemma bupd_le_upd P : (|==> P) ⊢ (|==£> P).
    Proof.
      rewrite le_upd_unfold; iIntros "Hupd" (x) "Hpr".
      iMod "Hupd" as "P". iModIntro. iLeft. by iFrame.
    Qed.

    Lemma le_upd_intro P : P ⊢ |==£> P.
    Proof.
      iIntros "H"; by iApply bupd_le_upd.
    Qed.

    Lemma le_upd_bind P Q :
      (P -∗ |==£> Q) -∗ (|==£> P) -∗ (|==£> Q).
    Proof.
      iLöb as "IH". iIntros "PQ".
      iEval (rewrite (le_upd_unfold P) (le_upd_unfold Q)).
      iIntros "Hupd" (x) "Hpr". iMod ("Hupd" with "Hpr") as "[Hupd|Hupd]".
      - iDestruct "Hupd" as "[Hpr Hupd]".
        iSpecialize ("PQ" with "Hupd").
        iEval (rewrite le_upd_unfold) in "PQ".
        iMod ("PQ" with "Hpr") as "[Hupd|Hupd]".
        + iModIntro. by iLeft.
        + iModIntro. iRight. iDestruct "Hupd" as  (x'' Hstep'') "[Hpr Hupd]".
          iExists _; iFrame. by iPureIntro.
      - iModIntro. iRight. iDestruct "Hupd" as (x') "(Hstep & Hpr & Hupd)".
        iExists _; iFrame. iNext. by iApply ("IH" with "PQ Hupd").
    Qed.

    Lemma le_upd_later_elim P :
      £ 1 -∗ (▷ |==£> P) -∗ |==£> P.
    Proof.
      iIntros "Hc Hl".
      iEval (rewrite le_upd_unfold). iIntros (n) "Hs".
      iDestruct (lc_supply_bound with "Hs Hc") as "%".
      destruct n as [ | n]; first by lia.
      replace (S n) with (1 + n) by lia.
      iMod (lc_decrease_supply with "Hs Hc") as "Hs". eauto 10 with iFrame lia.
    Qed.

    (** Derived lemmas *)
    Lemma le_upd_mono P Q : (P ⊢ Q) → (|==£> P) ⊢ (|==£> Q).
    Proof.
      intros Hent. iApply le_upd_bind.
      iIntros "P"; iApply le_upd_intro; by iApply Hent.
    Qed.

    Global Instance le_upd_mono' : Proper ((⊢) ==> (⊢)) le_upd.
    Proof. intros P Q PQ; by apply le_upd_mono. Qed.
    Global Instance le_upd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) le_upd.
    Proof. intros P Q PQ; by apply le_upd_mono. Qed.
    Global Instance le_upd_equiv_proper : Proper ((≡) ==> (≡)) le_upd.
    Proof. apply ne_proper. apply _. Qed.

    Lemma le_upd_trans P :  (|==£> |==£> P) ⊢ |==£> P.
    Proof.
      iIntros "HP". iApply le_upd_bind; eauto.
    Qed.
    Lemma le_upd_frame_r P R : (|==£> P) ∗ R ⊢ |==£> P ∗ R.
    Proof.
      iIntros "[Hupd R]". iApply (le_upd_bind with "[R]"); last done.
      iIntros "P". iApply le_upd_intro. by iFrame.
    Qed.
    Lemma le_upd_frame_l P R : R ∗ (|==£> P) ⊢ |==£> R ∗ P.
    Proof. rewrite comm le_upd_frame_r comm //. Qed.

    Lemma le_upd_later P :
      £ 1 -∗ ▷ P -∗ |==£> P.
    Proof.
      iIntros "H1 H2". iApply (le_upd_later_elim with "H1").
      iNext. by iApply le_upd_intro.
    Qed.

    Lemma except_0_le_upd P : ◇ (le_upd P) ⊢ le_upd (◇ P).
    Proof.
      rewrite /bi_except_0. apply or_elim; eauto using le_upd_mono, or_intro_r.
      by rewrite -le_upd_intro -or_intro_l.
    Qed.

    (** A safety check that later-elimination updates can replace basic updates *)
    (** We do not use this to build an instance, because it would conflict
       with the basic updates. *)
    Local Lemma bi_bupd_mixin_le_upd : BiBUpdMixin (iPropI Σ) le_upd.
    Proof.
      split; rewrite /bupd.
      - apply _.
      - apply le_upd_intro.
      - apply le_upd_mono.
      - apply le_upd_trans.
      - apply le_upd_frame_r.
    Qed.

    (** unfolding the later elimination update *)
    Lemma le_upd_elim n P :
      lc_supply n -∗
      (|==£> P) -∗
      Nat.iter n (λ P, |==> ▷ P) (|==> ◇ (∃ m, ⌜m ≤ n⌝ ∗ lc_supply m ∗ P)).
    Proof.
      induction (Nat.lt_wf_0 n) as [n _ IH].
      iIntros "Ha". rewrite (le_upd_unfold P) //=.
      iIntros "Hupd". iSpecialize ("Hupd" with "Ha").
      destruct n as [|n]; simpl.
      - iMod "Hupd" as "[[H● ?]| Hf]".
        { do 2 iModIntro. iExists 0. iFrame. done. }
        iDestruct "Hf" as (x' Hlt) "_". lia.
      - iMod "Hupd" as "[[Hc P]|Hupd]".
        + iModIntro. iNext. iApply iter_modal_intro; last first.
          { do 2 iModIntro. iExists (S n); iFrame; done. }
          iIntros (Q) "Q"; iModIntro; by iNext.
        + iModIntro. iDestruct "Hupd" as (m Hstep) "[Hown Hupd]". iNext.
          iPoseProof (IH with "Hown Hupd") as "Hit"; first done.
          clear IH.
          assert (m ≤ n) as [k ->]%Nat.le_sum by lia.
          rewrite Nat.add_comm Nat.iter_add.
          iApply iter_modal_intro.
          { by iIntros (Q) "$". }
          iApply (iter_modal_mono with "[] Hit").
          { iIntros (R S) "Hent H". by iApply "Hent". }
          iIntros "H". iMod "H". iModIntro. iMod "H" as (m' Hle) "H".
          iModIntro. iExists m'. iFrame. iPureIntro. lia.
    Qed.

    Lemma le_upd_elim_complete n P :
      lc_supply n -∗
      (|==£> P) -∗
      Nat.iter (S n) (λ Q, |==> ▷ Q) P.
    Proof.
      iIntros "Hlc Hupd". iPoseProof (le_upd_elim with "Hlc Hupd") as "Hit".
      rewrite Nat.iter_succ_r. iApply (iter_modal_mono with "[] Hit").
      { clear. iIntros (P Q) "Hent HP". by iApply "Hent". }
      iIntros "Hupd". iMod "Hupd". iModIntro. iMod "Hupd".
      iNext. iDestruct "Hupd" as "[%m (_ & _ & $)]".
    Qed.

    (** Proof mode class instances internally needed for people defining their
    [fupd] with [le_upd]. *)
    Global Instance elim_bupd_le_upd p P Q :
      ElimModal True p false (bupd P) P (le_upd Q) (le_upd Q)%I.
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim //=.
      rewrite bupd_le_upd. iIntros "_ [HP HPQ]".
      iApply (le_upd_bind with "HPQ HP").
    Qed.

    Global Instance from_assumption_le_upd p P Q :
      FromAssumption p P Q → KnownRFromAssumption p P (le_upd Q).
    Proof.
      rewrite /KnownRFromAssumption /FromAssumption=>->. apply le_upd_intro.
    Qed.

    Global Instance from_pure_le_upd a P φ :
      FromPure a P φ → FromPure a (le_upd P) φ.
    Proof. rewrite /FromPure=> <-. apply le_upd_intro. Qed.

    Global Instance is_except_0_le_upd P : IsExcept0 P → IsExcept0 (le_upd P).
    Proof.
      rewrite /IsExcept0=> HP.
      by rewrite -{2}HP -(except_0_idemp P) -except_0_le_upd -(except_0_intro P).
    Qed.

    Global Instance from_modal_le_upd P :
      FromModal True modality_id (le_upd P) (le_upd P) P.
    Proof. by rewrite /FromModal /= -le_upd_intro. Qed.

    Global Instance elim_modal_le_upd p P Q :
      ElimModal True p false (le_upd P) P (le_upd Q) (le_upd Q).
    Proof.
      by rewrite /ElimModal
        intuitionistically_if_elim le_upd_frame_r wand_elim_r le_upd_trans.
    Qed.

    Global Instance frame_le_upd p R P Q :
      Frame p R P Q → Frame p R (le_upd P) (le_upd Q).
    Proof. rewrite /Frame=><-. by rewrite le_upd_frame_l. Qed.
  End le_upd.

  (** You probably do NOT want to use this lemma; use [lc_soundness] if you want
  to actually use [le_upd]! *)
  Local Lemma lc_alloc `{!lcGpreS Σ} n :
    ⊢ |==> ∃ _ : lcGS Σ, lc_supply n ∗ £ n.
  Proof.
    rewrite lc_unseal /lc_def lc_supply_unseal /lc_supply_def.
    iMod (own_alloc (● n ⋅ ◯ n)) as (γLC) "[H● H◯]";
      first (apply auth_both_valid; split; done).
    pose (C := LcGS _ _ γLC).
    iModIntro. iExists C. iFrame.
  Qed.

  Lemma lc_soundness `{!lcGpreS Σ} m (P : iProp Σ) `{!Plain P} :
    (∀ {Hc: lcGS Σ}, £ m -∗ |==£> P) → ⊢ P.
  Proof.
    intros H. apply (laterN_soundness _ (S m)).
    eapply bupd_soundness; first apply _.
    iStartProof.
    iMod (lc_alloc m) as (C) "[H● H◯]".
    iPoseProof (H C) as "Hc". iSpecialize ("Hc" with "H◯").
    iPoseProof (le_upd_elim_complete m with "H● Hc") as "H".
    simpl. iMod "H". iModIntro. iNext.
    clear H. iInduction m as [|m] "IH"; simpl; [done|].
    iMod "H". iNext. by iApply "IH".
  Qed.
End le_upd.

(** This should only be imported by the internal development of fancy updates. *)
Module le_upd_if.
  Export le_upd.

  Section le_upd_if.
    Context `{!lcGS Σ}.

    Definition le_upd_if (b : bool) : iProp Σ → iProp Σ :=
      if b then le_upd else bupd.

    Global Instance le_upd_if_mono' b : Proper ((⊢) ==> (⊢)) (le_upd_if b).
    Proof. destruct b; apply _. Qed.
    Global Instance le_upd_if_flip_mono' b :
      Proper (flip (⊢) ==> flip (⊢)) (le_upd_if b).
    Proof. destruct b; apply _. Qed.
    Global Instance le_upd_if_proper b : Proper ((≡) ==> (≡)) (le_upd_if b).
    Proof. destruct b; apply _. Qed.
    Global Instance le_upd_if_ne b : NonExpansive (le_upd_if b).
    Proof. destruct b; apply _. Qed.

    Lemma le_upd_if_intro b P : P ⊢ le_upd_if b P.
    Proof.
      destruct b; [apply le_upd_intro | apply bupd_intro].
    Qed.

    Lemma le_upd_if_bind b P Q :
      (P -∗ le_upd_if b Q) -∗ (le_upd_if b P) -∗ (le_upd_if b Q).
    Proof.
      destruct b; first apply le_upd_bind. simpl.
      iIntros "HPQ >HP". by iApply "HPQ".
    Qed.

    Lemma le_upd_if_mono b P Q : (P ⊢ Q) → (le_upd_if b P) ⊢ (le_upd_if b Q).
    Proof.
      destruct b; [apply le_upd_mono | apply bupd_mono].
    Qed.
    Lemma le_upd_if_trans b P : (le_upd_if b (le_upd_if b P)) ⊢ le_upd_if b P.
    Proof.
      destruct b; [apply le_upd_trans | apply bupd_trans].
    Qed.
    Lemma le_upd_if_frame_r b P R : (le_upd_if b P) ∗ R ⊢ le_upd_if b (P ∗ R).
    Proof.
      destruct b; [apply le_upd_frame_r | apply bupd_frame_r].
    Qed.

    Lemma bupd_le_upd_if b P : (|==> P) ⊢ (le_upd_if b P).
    Proof.
      destruct b; [apply bupd_le_upd | done].
    Qed.

    Lemma le_upd_if_frame_l b R Q : (R ∗ le_upd_if b Q) ⊢ le_upd_if b (R ∗ Q).
    Proof.
      rewrite comm le_upd_if_frame_r comm //.
    Qed.

    Lemma except_0_le_upd_if b P : ◇ (le_upd_if b P) ⊢ le_upd_if b (◇ P).
    Proof.
      rewrite /bi_except_0. apply or_elim; eauto using le_upd_if_mono, or_intro_r.
      by rewrite -le_upd_if_intro -or_intro_l.
    Qed.

    (** Proof mode class instances that we need for the internal development,
    i.e. for the definition of fancy updates. *)
    Global Instance elim_bupd_le_upd_if b p P Q :
      ElimModal True p false (bupd P) P (le_upd_if b Q) (le_upd_if b Q)%I.
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim //=.
      rewrite bupd_le_upd_if. iIntros "_ [HP HPQ]".
      iApply (le_upd_if_bind with "HPQ HP").
    Qed.

    Global Instance from_assumption_le_upd_if b p P Q :
      FromAssumption p P Q → KnownRFromAssumption p P (le_upd_if b Q).
    Proof.
      rewrite /KnownRFromAssumption /FromAssumption=>->. apply le_upd_if_intro.
    Qed.

    Global Instance from_pure_le_upd_if b a P φ :
      FromPure a P φ → FromPure a (le_upd_if b P) φ.
    Proof. rewrite /FromPure=> <-. apply le_upd_if_intro. Qed.

    Global Instance is_except_0_le_upd_if b P : IsExcept0 P → IsExcept0 (le_upd_if b P).
    Proof.
      rewrite /IsExcept0=> HP.
      by rewrite -{2}HP -(except_0_idemp P) -except_0_le_upd_if -(except_0_intro P).
    Qed.

    Global Instance from_modal_le_upd_if b P :
      FromModal True modality_id (le_upd_if b P) (le_upd_if b P) P.
    Proof. by rewrite /FromModal /= -le_upd_if_intro. Qed.

    Global Instance elim_modal_le_upd_if b p P Q :
      ElimModal True p false (le_upd_if b P) P (le_upd_if b Q) (le_upd_if b Q).
    Proof.
      by rewrite /ElimModal
        intuitionistically_if_elim le_upd_if_frame_r wand_elim_r le_upd_if_trans.
    Qed.

    Global Instance frame_le_upd_if b p R P Q :
      Frame p R P Q → Frame p R (le_upd_if b P) (le_upd_if b Q).
    Proof. rewrite /Frame=><-. by rewrite le_upd_if_frame_l. Qed.
  End le_upd_if.
End le_upd_if.
