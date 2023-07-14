(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export ectx_language total_weakestpre total_lifting.
From iris.prelude Require Import options.

Section wp.
Context {Λ : ectxLanguage} `{!irisGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve head_prim_reducible_no_obs head_reducible_prim_step
  head_reducible_no_obs_reducible : core.

Lemma twp_lift_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E,∅}=∗
    ⌜head_reducible_no_obs e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ⌜κ = []⌝ ∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E [{ Φ }] ∗
      [∗ list] i ↦ ef ∈ efs, WP ef @ s; ⊤ [{ fork_post }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H".
  iApply (twp_lift_step _ E)=>//. iIntros (σ1 ns κs nt) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; [destruct s; auto|]. iIntros (κ e2 σ2 efs Hstep).
  iApply "H". by eauto.
Qed.

Lemma twp_lift_pure_head_step_no_fork {s E Φ} e1 :
  (∀ σ1, head_reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E}=> ∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ → WP e2 @ s; E [{ Φ }] )
  ⊢ WP e1 @ s; E [{ Φ }].
Proof using Hinh.
  iIntros (??) ">H". iApply twp_lift_pure_step_no_fork; eauto.
  iIntros "!>" (?????). iApply "H"; eauto.
Qed.

Lemma twp_lift_atomic_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E}=∗
    ⌜head_reducible_no_obs e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜κ = []⌝ ∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ fork_post }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_atomic_step; eauto.
  iIntros (σ1 ns κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iIntros (κ e2 σ2 efs Hstep). iApply "H"; eauto.
Qed.

Lemma twp_lift_atomic_head_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E}=∗
    ⌜head_reducible_no_obs e1 σ1⌝ ∗
    ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜κ = []⌝ ∗ ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs nt
                            ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H". iApply twp_lift_atomic_head_step; eauto.
  iIntros (σ1 ns κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iIntros (κ v2 σ2 efs Hstep).
  iMod ("H" with "[# //]") as "(-> & -> & ? & $) /=". by iFrame.
Qed.

Lemma twp_lift_pure_det_head_step_no_fork {s E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2' σ2 efs',
    head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  WP e2 @ s; E [{ Φ }] ⊢ WP e1 @ s; E [{ Φ }].
Proof using Hinh.
  intros. rewrite -(twp_lift_pure_det_step_no_fork e1 e2); eauto.
Qed.
End wp.
