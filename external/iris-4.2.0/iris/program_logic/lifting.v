(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

Section lifting.
Context `{!irisGS_gen hlc Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Local Hint Resolve reducible_no_obs_reducible : core.

Lemma wp_lift_step_fupdN s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
      £ (S $ num_laters_per_step ns)
      ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. by rewrite wp_unfold /wp_pre=>->. Qed.

Lemma wp_lift_step_fupd s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={∅}=∗ ▷ |={∅,E}=>
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "Hwp". rewrite -wp_lift_step_fupdN; [|done].
  iIntros (?????) "Hσ". iMod ("Hwp" with "Hσ") as "($ & Hwp)".
  iIntros "!>" (??? ?) "Hcred".
  iPoseProof (lc_weaken 1 with "Hcred") as "Hcred"; first lia.
  simpl. rewrite -step_fupdN_intro; [|done]. rewrite -bi.laterN_intro.
  iMod ("Hwp" with "[//] Hcred") as "Hwp".
  iApply step_fupd_intro; done.
Qed.

Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ ns κs nt, state_interp σ ns κs nt ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 ns κ κs nt) "Hσ".
  iMod ("H" with "Hσ") as %[? Hirr]. iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr κ e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={∅,E}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % Hcred !> !>". by iApply "H".
Qed.

Lemma wp_lift_pure_step_no_fork `{!Inhabited (state Λ)} s E E' Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={E}[E']▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ -∗ £ 1 -∗ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (σ1 ns κ κs nt) "Hσ". iMod "H".
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?) "Hcred".
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod (state_interp_mono with "Hσ") as "$".
  iMod "Hclose" as "_". iMod "H". iModIntro.
  by iDestruct ("H" with "[//] Hcred") as "$".
Qed.

Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ ns κs nt) "_". iApply fupd_mask_intro; auto with set_solver.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ e1)=>//; iIntros (σ1 ns κ κs nt) "Hσ1".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iApply fupd_mask_intro; first set_solver.
  iIntros "Hclose" (e2 σ2 efs ?) "Hcred". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#] Hcred") as "H"; [done|].
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
  iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗ £ 1 ={E}=∗
      state_interp σ2 (S ns) κs (length efs + nt) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?????) "?". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "Hcred !> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E E' Φ} e1 e2 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> £ 1 -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork s E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n £ n -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl.
  { iMod lc_zero as "Hz". by iApply "Hwp". }
  iApply wp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - iApply (step_fupd_wand with "Hwp").
    iIntros "Hwp Hone". iApply "IH".
    iApply (step_fupdN_wand with "Hwp").
    iIntros "Hwp Hc". iApply ("Hwp" with "[Hone Hc]").
    rewrite (lc_succ n). iFrame.
Qed.

Lemma wp_pure_step_later `{!Inhabited (state Λ)} s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n (£ n -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  enough (∀ P, ▷^n P ⊢ |={E}▷=>^n P) as Hwp by apply Hwp. intros ?.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
