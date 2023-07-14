From iris.bi Require Export big_op.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export total_weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS Λ Σ}.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma twp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
    ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
      ⌜κ = []⌝ ∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E [{ Φ }] ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ fork_post }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof. by rewrite twp_unfold /twp_pre=> ->. Qed.

(** Derived lifting lemmas. *)
Lemma twp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s E Φ e1 :
  (∀ σ1, reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E}=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → WP e2 @ s; E [{ Φ }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (Hsafe Hstep) ">H". iApply twp_lift_step.
  { eapply reducible_not_val, reducible_no_obs_reducible, (Hsafe inhabitant). }
  iIntros (σ1 ns κs n) "Hσ".
  iApply fupd_mask_intro; first by set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; auto. }
  iIntros (κ e2 σ2 efs ?). destruct (Hstep σ1 κ e2 σ2 efs) as (->&<-&->); auto.
  iMod (state_interp_mono with "Hσ"). iMod "Hclose" as "_".
  iDestruct ("H" with "[//]") as "H". simpl. by iFrame.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma twp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κs nt, state_interp σ1 ns κs nt ={E}=∗
    ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
    ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={E}=∗
      ⌜κ = []⌝ ∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ [{ fork_post }])
  ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (?) "H".
  iApply (twp_lift_step _ E _ e1)=>//; iIntros (σ1 ns κs nt) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (κ e2 σ2 efs) "%". iMod "Hclose" as "_".
  iMod ("H" $! κ e2 σ2 efs with "[#]") as "($ & $ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply twp_value; last done. by apply of_to_val.
Qed.

Lemma twp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E Φ} e1 e2 :
  (∀ σ1, reducible_no_obs e1 σ1) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}=> WP e2 @ s; E [{ Φ }]) ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (? Hpuredet) ">H". iApply (twp_lift_pure_step_no_fork s E); try done.
  { naive_solver. }
  iIntros "!>" (κ' e' efs' σ (_&_&->&->)%Hpuredet); auto.
Qed.

Lemma twp_pure_step `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  WP e2 @ s; E [{ Φ }] ⊢ WP e1 @ s; E [{ Φ }].
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply twp_lift_pure_det_step_no_fork; [done|naive_solver|].
  iModIntro. by iApply "IH".
Qed.
End lifting.
