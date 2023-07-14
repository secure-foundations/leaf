From iris.bi Require Import fixpoint big_op.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

(** The definition of total weakest preconditions is very similar to the
definition of normal (i.e. partial) weakest precondition, with the exception
that there is no later modality. Hence, instead of taking a Banach's fixpoint,
we take a least fixpoint. *)
Definition twp_pre `{!irisGS Λ Σ} (s : stuckness)
      (wp : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
    coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κs nt,
     state_interp σ1 ns κs nt ={E,∅}=∗
       ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
       ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
         ⌜κ = []⌝ ∗
         state_interp σ2 (S ns) κs (length efs + nt) ∗
         wp E e2 Φ ∗
         [∗ list] ef ∈ efs, wp ⊤ ef fork_post
  end%I.

(** This is some uninteresting bookkeeping to prove that [twp_pre_mono] is
monotone. The actual least fixpoint [twp_def] can be found below. *)
Lemma twp_pre_mono `{!irisGS Λ Σ} s
    (wp1 wp2 : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
  ⊢ (□ ∀ E e Φ, wp1 E e Φ -∗ wp2 E e Φ) →
    ∀ E e Φ, twp_pre s wp1 E e Φ -∗ twp_pre s wp2 E e Φ.
Proof.
  iIntros "#H"; iIntros (E e1 Φ) "Hwp". rewrite /twp_pre.
  destruct (to_val e1) as [v|]; first done.
  iIntros (σ1 ns κs nt) "Hσ". iMod ("Hwp" with "Hσ") as "($ & Hwp)"; iModIntro.
  iIntros (κ e2 σ2 efs) "Hstep".
  iMod ("Hwp" with "Hstep") as (?) "(Hσ & Hwp & Hfork)".
  iModIntro. iFrame "Hσ". iSplit; first done. iSplitL "Hwp".
  - by iApply "H".
  - iApply (@big_sepL_impl with "Hfork"); iIntros "!>" (k e _) "Hwp".
    by iApply "H".
Qed.

(* Uncurry [twp_pre] and equip its type with an OFE structure *)
Definition twp_pre' `{!irisGS Λ Σ} (s : stuckness) :
  (prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iPropO Σ) → iPropO Σ) →
  prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iPropO Σ) → iPropO Σ :=
    curry3 ∘ twp_pre s ∘ uncurry3.

Local Instance twp_pre_mono' `{!irisGS Λ Σ} s : BiMonoPred (twp_pre' s).
Proof.
  constructor.
  - iIntros (wp1 wp2) "#H"; iIntros ([[E e1] Φ]); iRevert (E e1 Φ).
    iApply twp_pre_mono. iIntros "!>" (E e Φ). iApply ("H" $! (E,e,Φ)).
  - intros wp Hwp n [[E1 e1] Φ1] [[E2 e2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=.
    rewrite /uncurry3 /twp_pre. do 26 (f_equiv || done). by apply pair_ne.
Qed.

Definition twp_def `{!irisGS Λ Σ} : Twp (iProp Σ) (expr Λ) (val Λ) stuckness
  := λ s E e Φ, bi_least_fixpoint (twp_pre' s) (E,e,Φ).
Definition twp_aux : seal (@twp_def). Proof. by eexists. Qed.
Definition twp' := twp_aux.(unseal).
Global Arguments twp' {Λ Σ _}.
Global Existing Instance twp'.
Lemma twp_eq `{!irisGS Λ Σ} : twp = @twp_def Λ Σ _.
Proof. rewrite -twp_aux.(seal_eq) //. Qed.

Section twp.
Context `{!irisGS Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma twp_unfold s E e Φ : WP e @ s; E [{ Φ }] ⊣⊢ twp_pre s (twp s) E e Φ.
Proof. by rewrite twp_eq /twp_def least_fixpoint_unfold. Qed.
Lemma twp_ind s Ψ :
  (∀ n E e, Proper (pointwise_relation _ (dist n) ==> dist n) (Ψ E e)) →
  □ (∀ e E Φ, twp_pre s (λ E e Φ, Ψ E e Φ ∧ WP e @ s; E [{ Φ }]) E e Φ -∗ Ψ E e Φ) -∗
  ∀ e E Φ, WP e @ s; E [{ Φ }] -∗ Ψ E e Φ.
Proof.
  iIntros (HΨ). iIntros "#IH" (e E Φ) "H". rewrite twp_eq.
  set (Ψ' := curry3 Ψ :
    prodO (prodO (leibnizO coPset) (exprO Λ)) (val Λ -d> iPropO Σ) → iPropO Σ).
  assert (NonExpansive Ψ').
  { intros n [[E1 e1] Φ1] [[E2 e2] Φ2]
      [[?%leibniz_equiv ?%leibniz_equiv] ?]; simplify_eq/=. by apply HΨ. }
  iApply (least_fixpoint_strong_ind _ Ψ' with "[] H").
  iIntros "!>" ([[??] ?]) "H". by iApply "IH".
Qed.

Global Instance twp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (twp (PROP:=iProp Σ) s E e).
Proof.
  intros Φ1 Φ2 HΦ. rewrite !twp_eq. by apply (least_fixpoint_ne _), pair_ne, HΦ.
Qed.
Global Instance twp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (twp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply twp_ne=>v; apply equiv_dist.
Qed.

Lemma twp_value_fupd' s E Φ v : WP of_val v @ s; E [{ Φ }] ⊣⊢ |={E}=> Φ v.
Proof. rewrite twp_unfold /twp_pre to_of_val. auto. Qed.

Lemma twp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 [{ Φ }] -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 [{ Ψ }].
Proof.
  iIntros (? HE) "H HΦ". iRevert (E2 Ψ HE) "HΦ"; iRevert (e E1 Φ) "H".
  iApply twp_ind; first solve_proper.
  iIntros "!>" (e E1 Φ) "IH"; iIntros (E2 Ψ HE) "HΦ".
  rewrite !twp_unfold /twp_pre. destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 ns κs nt) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("IH" with "[$]") as "[% IH]".
  iModIntro; iSplit; [by destruct s1, s2|]. iIntros (κ e2 σ2 efs Hstep).
  iMod ("IH" with "[//]") as (?) "(Hσ & IH & IHefs)"; auto.
  iMod "Hclose" as "_"; iModIntro.
  iFrame "Hσ". iSplit; first done. iSplitR "IHefs".
  - iDestruct "IH" as "[IH _]". iApply ("IH" with "[//] HΦ").
  - iApply (big_sepL_impl with "IHefs"); iIntros "!>" (k ef _) "[IH _]".
    iApply "IH"; auto.
Qed.

Lemma fupd_twp s E e Φ : (|={E}=> WP e @ s; E [{ Φ }]) -∗ WP e @ s; E [{ Φ }].
Proof.
  rewrite twp_unfold /twp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 ns κs nt) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma twp_fupd s E e Φ : WP e @ s; E [{ v, |={E}=> Φ v }] -∗ WP e @ s; E [{ Φ }].
Proof. iIntros "H". iApply (twp_strong_mono with "H"); auto. Qed.

Lemma twp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 [{ v, |={E2,E1}=> Φ v }]) -∗ WP e @ s; E1 [{ Φ }].
Proof.
  iIntros "H". rewrite !twp_unfold /twp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 ns κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (κ e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as (?) "(Hσ & H & Hefs)". destruct s.
  - rewrite !twp_unfold /twp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ?).
      by edestruct (atomic _ _ _ _ _ Hstep).
  - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
    rewrite twp_value_fupd'. iMod "H" as ">H".
    iModIntro. iSplit; first done. iFrame "Hσ Hefs". by iApply twp_value_fupd'.
Qed.

Lemma twp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E [{ v, WP K (of_val v) @ s; E [{ Φ }] }] -∗ WP K e @ s; E [{ Φ }].
Proof.
  revert Φ. cut (∀ Φ', WP e @ s; E [{ Φ' }] -∗ ∀ Φ,
    (∀ v, Φ' v -∗ WP K (of_val v) @ s; E [{ Φ }]) -∗ WP K e @ s; E [{ Φ }]).
  { iIntros (help Φ) "H". iApply (help with "H"); auto. }
  iIntros (Φ') "H". iRevert (e E Φ') "H". iApply twp_ind; first solve_proper.
  iIntros "!>" (e E1 Φ') "IH". iIntros (Φ) "HΦ".
  rewrite /twp_pre. destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply fupd_twp. by iApply "HΦ". }
  rewrite twp_unfold /twp_pre fill_not_val //.
  iIntros (σ1 ns κs nt) "Hσ". iMod ("IH" with "[$]") as "[% IH]".
  iModIntro; iSplit.
  { iPureIntro. unfold reducible_no_obs in *.
    destruct s; naive_solver eauto using fill_step. }
  iIntros (κ e2 σ2 efs Hstep).
  destruct (fill_step_inv e σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("IH" $! κ e2' σ2 efs with "[//]") as (?) "(Hσ & IH & IHefs)".
  iModIntro. iFrame "Hσ". iSplit; first done. iSplitR "IHefs".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite and_elim_r.
Qed.

Lemma twp_bind_inv K `{!LanguageCtx K} s E e Φ :
  WP K e @ s; E [{ Φ }] -∗ WP e @ s; E [{ v, WP K (of_val v) @ s; E [{ Φ }] }].
Proof.
  iIntros "H". remember (K e) as e' eqn:He'.
  iRevert (e He'). iRevert (e' E Φ) "H". iApply twp_ind; first solve_proper.
  iIntros "!>" (e' E1 Φ) "IH". iIntros (e ->).
  rewrite !twp_unfold {2}/twp_pre. destruct (to_val e) as [v|] eqn:He.
  { iModIntro. apply of_to_val in He as <-. rewrite !twp_unfold.
    iApply (twp_pre_mono with "[] IH"). by iIntros "!>" (E e Φ') "[_ ?]". }
  rewrite /twp_pre fill_not_val //.
  iIntros (σ1 ns κs nt) "Hσ". iMod ("IH" with "[$]") as "[% IH]".
  iModIntro; iSplit.
  { destruct s; eauto using reducible_no_obs_fill_inv. }
  iIntros (κ e2 σ2 efs Hstep).
  iMod ("IH" $! κ (K e2) σ2 efs with "[]") as (?) "(Hσ & IH & IHefs)"; eauto using fill_step.
  iModIntro. iFrame "Hσ". iSplit; first done. iSplitR "IHefs".
  - iDestruct "IH" as "[IH _]". by iApply "IH".
  - by setoid_rewrite and_elim_r.
Qed.

Lemma twp_wp s E e Φ : WP e @ s; E [{ Φ }] -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ).
  rewrite wp_unfold twp_unfold /wp_pre /twp_pre. destruct (to_val e) as [v|]=>//=.
  iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "Hσ") as "[% H]".
  iIntros "!>". iSplitR.
  { destruct s; eauto using reducible_no_obs_reducible. }
  iIntros (e2 σ2 efs) "Hstep". iMod ("H" with "Hstep") as (->) "(Hσ & H & Hfork)".
  iApply fupd_mask_intro; [set_solver+|]. iIntros "Hclose".
  iIntros "!>!>". iApply step_fupdN_intro=>//. iModIntro. iMod "Hclose" as "_".
  iModIntro. iFrame "Hσ". iSplitL "H".
  { by iApply "IH". }
  iApply (@big_sepL_impl with "Hfork").
  iIntros "!>" (k ef _) "H". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma twp_mono s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) → WP e @ s; E [{ Φ }] -∗ WP e @ s; E [{ Ψ }].
Proof.
  iIntros (HΦ) "H"; iApply (twp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma twp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E [{ Φ }] ⊢ WP e @ s2; E [{ Φ }].
Proof. iIntros (?) "H". iApply (twp_strong_mono with "H"); auto. Qed.
Lemma twp_stuck_weaken s E e Φ :
  WP e @ s; E [{ Φ }] ⊢ WP e @ E ?[{ Φ }].
Proof. apply twp_stuck_mono. by destruct s. Qed.
Lemma twp_mask_mono s E1 E2 e Φ :
  E1 ⊆ E2 → WP e @ s; E1 [{ Φ }] -∗ WP e @ s; E2 [{ Φ }].
Proof. iIntros (?) "H"; iApply (twp_strong_mono with "H"); auto. Qed.
Global Instance twp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (twp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply twp_mono. Qed.

Lemma twp_value_fupd s E Φ e v : IntoVal e v → WP e @ s; E [{ Φ }] ⊣⊢ |={E}=> Φ v.
Proof. intros <-. by apply twp_value_fupd'. Qed.
Lemma twp_value' s E Φ v : Φ v ⊢ WP (of_val v) @ s; E [{ Φ }].
Proof. rewrite twp_value_fupd'. auto. Qed.
Lemma twp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E [{ Φ }].
Proof. intros <-. apply twp_value'. Qed.

Lemma twp_frame_l s E e Φ R : R ∗ WP e @ s; E [{ Φ }] -∗ WP e @ s; E [{ v, R ∗ Φ v }].
Proof. iIntros "[? H]". iApply (twp_strong_mono with "H"); auto with iFrame. Qed.
Lemma twp_frame_r s E e Φ R : WP e @ s; E [{ Φ }] ∗ R -∗ WP e @ s; E [{ v, Φ v ∗ R }].
Proof. iIntros "[H ?]". iApply (twp_strong_mono with "H"); auto with iFrame. Qed.

Lemma twp_wand s E e Φ Ψ :
  WP e @ s; E [{ Φ }] -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E [{ Ψ }].
Proof.
  iIntros "H HΦ". iApply (twp_strong_mono with "H"); auto.
  iIntros (?) "?". by iApply "HΦ".
Qed.
Lemma twp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E [{ Φ }] -∗ WP e @ s; E [{ Ψ }].
Proof. iIntros "[H Hwp]". iApply (twp_wand with "Hwp H"). Qed.
Lemma twp_wand_r s E e Φ Ψ :
  WP e @ s; E [{ Φ }] ∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E [{ Ψ }].
Proof. iIntros "[Hwp H]". iApply (twp_wand with "Hwp H"). Qed.
Lemma twp_frame_wand s E e Φ R :
  R -∗ WP e @ s; E [{ v, R -∗ Φ v }] -∗ WP e @ s; E [{ Φ }].
Proof.
  iIntros "HR HWP". iApply (twp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

Lemma twp_wp_step s E e P Φ :
  TCEq (to_val e) None →
  ▷ P -∗
  WP e @ s; E [{ v, P ={E}=∗ Φ v }] -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP Hwp".
  iApply (wp_step_fupd _ _ E _ P with "[HP]"); [auto..|]. by iApply twp_wp.
Qed.
End twp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_twp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E [{ Φ }]) (WP e @ s; E [{ Ψ }]).
  Proof. rewrite /Frame=> HR. rewrite twp_frame_l. apply twp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E [{ Φ }]).
  Proof. by rewrite /IsExcept0 -{2}fupd_twp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_twp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E [{ Φ }]) (WP e @ s; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_twp.
  Qed.

  Global Instance elim_modal_fupd_twp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E [{ Φ }]) (WP e @ s; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_twp.
  Qed.

  Global Instance elim_modal_fupd_twp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (WP e @ s; E1 [{ Φ }]) (WP e @ s; E2 [{ v, |={E2,E1}=> Φ v }])%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r twp_atomic.
  Qed.

  Global Instance add_modal_fupd_twp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E [{ Φ }]).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_twp. Qed.
End proofmode_classes.
