From iris.algebra Require Import lib.excl_auth.
From iris.proofmode Require Import tactics classes.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import lifting adequacy.
From iris.program_logic Require ectx_language.
From iris.prelude Require Import options.

(**
This module provides an interface to handling ownership of the global state that
works more like Iris 2.0 did.  The state interpretation (in WP) is fixed to be
authoritative ownership of the entire state (using the [excl] RA).  Users can
then put the corresponding fragment into an invariant on their own to establish
a more interesting notion of ownership, such as the standard heap with disjoint
union.
*)

Class ownPGS (Λ : language) (Σ : gFunctors) := OwnPGS {
  ownP_invG : invGS Σ;
  ownP_inG :> inG Σ (excl_authR (stateO Λ));
  ownP_name : gname;
}.

Global Instance ownPG_irisGS `{!ownPGS Λ Σ} : irisGS Λ Σ := {
  iris_invG := ownP_invG;
  state_interp σ _ κs _ := own ownP_name (●E σ)%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.
Global Opaque iris_invG.

Definition ownPΣ (Λ : language) : gFunctors :=
  #[invΣ;
    GFunctor (excl_authR (stateO Λ))].

Class ownPGpreS (Λ : language) (Σ : gFunctors) : Set := {
  ownPPre_invG :> invGpreS Σ;
  ownPPre_state_inG :> inG Σ (excl_authR (stateO Λ))
}.

Global Instance subG_ownPΣ {Λ Σ} : subG (ownPΣ Λ) Σ → ownPGpreS Λ Σ.
Proof. solve_inG. Qed.

(** Ownership *)
Definition ownP `{!ownPGS Λ Σ} (σ : state Λ) : iProp Σ :=
  own ownP_name (◯E σ).
Typeclasses Opaque ownP.
Global Instance: Params (@ownP) 3 := {}.

(* Adequacy *)
Theorem ownP_adequacy Σ `{!ownPGpreS Λ Σ} s e σ φ :
  (∀ `{!ownPGS Λ Σ}, ownP σ ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply (wp_adequacy Σ _).
  iIntros (? κs).
  iMod (own_alloc (●E σ ⋅ ◯E σ)) as (γσ) "[Hσ Hσf]";
    first by apply excl_auth_valid.
  iModIntro. iExists (λ σ κs, own γσ (●E σ))%I, (λ _, True%I).
  iFrame "Hσ".
  iApply (Hwp (OwnPGS _ _ _ _ γσ)). rewrite /ownP. iFrame.
Qed.

Theorem ownP_invariance Σ `{!ownPGpreS Λ Σ} s e σ1 t2 σ2 φ :
  (∀ `{!ownPGS Λ Σ},
      ownP σ1 ={⊤}=∗ WP e @ s; ⊤ {{ _, True }} ∗
      |={⊤,∅}=> ∃ σ', ownP σ' ∧ ⌜φ σ'⌝) →
  rtc erased_step ([e], σ1) (t2, σ2) →
  φ σ2.
Proof.
  intros Hwp Hsteps. eapply (wp_invariance Σ Λ s e σ1 t2 σ2 _)=> //.
  iIntros (? κs).
  iMod (own_alloc (●E σ1 ⋅ ◯E σ1)) as (γσ) "[Hσ Hσf]";
    first by apply auth_both_valid_discrete.
  iExists (λ σ κs' _, own γσ (●E σ))%I, (λ _, True%I).
  iFrame "Hσ".
  iMod (Hwp (OwnPGS _ _ _ _ γσ) with "[Hσf]") as "[$ H]";
    first by rewrite /ownP; iFrame.
  iIntros "!> Hσ". iExists ∅. iMod "H" as (σ2') "[Hσf %]". rewrite /ownP.
  iDestruct (own_valid_2 with "Hσ Hσf")
    as %[Hp%Excl_included _]%auth_both_valid_discrete; simplify_eq; auto.
Qed.


(** Lifting *)
Section lifting.
  Context `{!ownPGS Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types e : expr Λ.
  Implicit Types Φ : val Λ → iProp Σ.

  Lemma ownP_eq σ1 ns σ2 κs nt :
    state_interp σ1 ns κs nt -∗ ownP σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    iIntros "Hσ● Hσ◯". rewrite /ownP.
    by iDestruct (own_valid_2 with "Hσ● Hσ◯")
      as %[->%Excl_included _]%auth_both_valid_discrete.
  Qed.
  Lemma ownP_state_twice σ1 σ2 : ownP σ1 ∗ ownP σ2 ⊢ False.
  Proof.
    rewrite /ownP -own_op own_valid. by iIntros (?%excl_auth_frag_valid_op_1_l).
  Qed.
  Global Instance ownP_timeless σ : Timeless (@ownP Λ Σ _ σ).
  Proof. rewrite /ownP; apply _. Qed.

  Lemma ownP_lift_step s E Φ e1 :
    (|={E,∅}=> ∃ σ1, ⌜if s is NotStuck then reducible e1 σ1 else to_val e1 = None⌝ ∗
      ▷ ownP σ1 ∗
      ▷ ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
      ownP σ2
            ={∅,E}=∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros "H". destruct (to_val e1) as [v|] eqn:EQe1.
    - apply of_to_val in EQe1 as <-. iApply fupd_wp.
      iMod "H" as (σ1) "[Hred _]"; iDestruct "Hred" as %Hred.
      destruct s; last done. apply reducible_not_val in Hred.
      move: Hred; by rewrite to_of_val.
    - iApply wp_lift_step; [done|]; iIntros (σ1 ns κ κs nt) "Hσκs".
      iMod "H" as (σ1' ?) "[>Hσf H]".
      iDestruct (ownP_eq with "Hσκs Hσf") as %<-.
      iModIntro; iSplit; [by destruct s|]; iNext; iIntros (e2 σ2 efs Hstep).
      iDestruct "Hσκs" as "Hσ". rewrite /ownP.
      iMod (own_update_2 with "Hσ Hσf") as "[Hσ Hσf]".
      { apply excl_auth_update. }
      iFrame "Hσ". iApply ("H" with "[]"); eauto with iFrame.
  Qed.

  Lemma ownP_lift_stuck E Φ e :
    (|={E,∅}=> ∃ σ, ⌜stuck e σ⌝ ∗ ▷ (ownP σ))
    ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros "H". destruct (to_val e) as [v|] eqn:EQe.
    - apply of_to_val in EQe as <-. iApply fupd_wp.
      iMod "H" as (σ1) "[H _]". iDestruct "H" as %[Hnv _]. exfalso.
      by rewrite to_of_val in Hnv.
    - iApply wp_lift_stuck; [done|]. iIntros (σ1 ns κs nt) "Hσ".
      iMod "H" as (σ1') "(% & >Hσf)".
      by iDestruct (ownP_eq with "Hσ Hσf") as %->.
  Qed.

  Lemma ownP_lift_pure_step `{!Inhabited (state Λ)} s E Φ e1 :
    (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ σ1 κ e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1) →
    (▷ ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ →
      WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep) "H"; iApply wp_lift_step.
    { specialize (Hsafe inhabitant). destruct s; last done.
      by eapply reducible_not_val. }
    iIntros (σ1 ns κ κs nt) "Hσ". iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose". iSplit; [by destruct s|]; iNext; iIntros (e2 σ2 efs ?).
    destruct (Hstep σ1 κ e2 σ2 efs); auto; subst.
    by iMod "Hclose"; iModIntro; iFrame; iApply "H".
  Qed.

  (** Derived lifting lemmas. *)
  Lemma ownP_lift_atomic_step {s E Φ} e1 σ1 :
    (if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (▷ (ownP σ1) ∗
       ▷ ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ -∗
         ownP σ2 -∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "[Hσ H]"; iApply ownP_lift_step.
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose". iExists σ1; iFrame; iSplit; first by destruct s.
    iNext; iIntros (κ e2 σ2 efs ?) "Hσ".
    iDestruct ("H" $! κ e2 σ2 efs with "[] [Hσ]") as "[HΦ $]"; [by eauto..|].
    destruct (to_val e2) eqn:?; last by iExFalso.
    iMod "Hclose"; iApply wp_value; last done. by apply of_to_val.
  Qed.

  Lemma ownP_lift_atomic_det_step {s E Φ e1} σ1 v2 σ2 efs :
    (if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ κ' e2' σ2' efs', prim_step e1 σ1 κ' e2' σ2' efs' →
                     σ2' = σ2 ∧ to_val e2' = Some v2 ∧ efs' = efs) →
    ▷ (ownP σ1) ∗ ▷ (ownP σ2 -∗
      Φ v2 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (? Hdet) "[Hσ1 Hσ2]"; iApply ownP_lift_atomic_step; try done.
    iFrame; iNext; iIntros (κ' e2' σ2' efs' ?) "Hσ2'".
    edestruct (Hdet κ') as (<-&Hval&<-); first done. rewrite Hval.
    iApply ("Hσ2" with "Hσ2'").
  Qed.

  Lemma ownP_lift_atomic_det_step_no_fork {s E e1} σ1 v2 σ2 :
    (if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ κ' e2' σ2' efs', prim_step e1 σ1 κ' e2' σ2' efs' →
      σ2' = σ2 ∧ to_val e2' = Some v2 ∧ efs' = []) →
    {{{ ▷ (ownP σ1) }}} e1 @ s; E {{{ RET v2; ownP σ2 }}}.
  Proof.
    intros. rewrite -(ownP_lift_atomic_det_step σ1 v2 σ2 []); [|done..].
    rewrite big_sepL_nil right_id. apply bi.wand_intro_r. iIntros "[Hs Hs']".
    iSplitL "Hs"; first by iFrame. iModIntro. iIntros "Hσ2". iApply "Hs'". iFrame.
  Qed.

  Lemma ownP_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {s E Φ} e1 e2 :
    (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
    (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
    ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros. rewrite -(wp_lift_pure_det_step_no_fork e1 e2) //; eauto.
  Qed.
End lifting.

Section ectx_lifting.
  Import ectx_language.
  Context {Λ : ectxLanguage} `{!ownPGS Λ Σ} {Hinh : Inhabited (state Λ)}.
  Implicit Types s : stuckness.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types e : expr Λ.
  Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.
  Local Definition reducible_not_val_inhabitant e := reducible_not_val e inhabitant.
  Local Hint Resolve reducible_not_val_inhabitant : core.
  Local Hint Resolve head_stuck_stuck : core.

  Lemma ownP_lift_head_step s E Φ e1 :
    (|={E,∅}=> ∃ σ1, ⌜head_reducible e1 σ1⌝ ∗ ▷ (ownP σ1) ∗
            ▷ ∀ κ e2 σ2 efs, ⌜head_step e1 σ1 κ e2 σ2 efs⌝ -∗
            ownP σ2
            ={∅,E}=∗ WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros "H". iApply ownP_lift_step.
    iMod "H" as (σ1 ?) "[>Hσ1 Hwp]". iModIntro. iExists σ1. iSplit.
    { destruct s; try by eauto using reducible_not_val. }
    iFrame. iNext. iIntros (κ e2 σ2 efs ?) "Hσ2".
    iApply ("Hwp" with "[] Hσ2"); eauto.
  Qed.

  Lemma ownP_lift_head_stuck E Φ e :
    sub_redexes_are_values e →
    (|={E,∅}=> ∃ σ, ⌜head_stuck e σ⌝ ∗ ▷ (ownP σ))
    ⊢ WP e @ E ?{{ Φ }}.
  Proof.
    iIntros (?) "H". iApply ownP_lift_stuck. iMod "H" as (σ) "[% >Hσ]".
    iExists σ. iModIntro. by auto with iFrame.
  Qed.

  Lemma ownP_lift_pure_head_step s E Φ e1 :
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 κ e2 σ2 efs, head_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1) →
    (▷ ∀ κ e2 efs σ, ⌜head_step e1 σ κ e2 σ efs⌝ →
      WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (??) "H".  iApply ownP_lift_pure_step; eauto.
    { by destruct s; auto. }
    iNext. iIntros (?????). iApply "H"; eauto.
  Qed.

  Lemma ownP_lift_atomic_head_step {s E Φ} e1 σ1 :
    head_reducible e1 σ1 →
    ▷ (ownP σ1) ∗ ▷ (∀ κ e2 σ2 efs,
    ⌜head_step e1 σ1 κ e2 σ2 efs⌝ -∗ ownP σ2 -∗
      from_option Φ False (to_val e2) ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "[Hst H]". iApply ownP_lift_atomic_step; eauto.
    { by destruct s; eauto using reducible_not_val. }
    iSplitL "Hst"; first done.
    iNext. iIntros (???? ?) "Hσ". iApply ("H" with "[] Hσ"); eauto.
  Qed.

  Lemma ownP_lift_atomic_det_head_step {s E Φ e1} σ1 v2 σ2 efs :
    head_reducible e1 σ1 →
    (∀ κ' e2' σ2' efs', head_step e1 σ1 κ' e2' σ2' efs' →
      σ2' = σ2 ∧ to_val e2' = Some v2 ∧ efs' = efs) →
    ▷ (ownP σ1) ∗ ▷ (ownP σ2 -∗
                      Φ v2 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hr Hs.
    destruct s; apply ownP_lift_atomic_det_step; eauto using reducible_not_val;
    intros; eapply Hs; eauto 10.
  Qed.

  Lemma ownP_lift_atomic_det_head_step_no_fork {s E e1} σ1 κ v2 σ2 :
    head_reducible e1 σ1 →
    (∀ κ' e2' σ2' efs', head_step e1 σ1 κ' e2' σ2' efs' →
      κ' = κ ∧ σ2' = σ2 ∧ to_val e2' = Some v2 ∧ efs' = []) →
    {{{ ▷ (ownP σ1) }}} e1 @ s; E {{{ RET v2; ownP σ2 }}}.
  Proof.
    intros ???; apply ownP_lift_atomic_det_step_no_fork; last naive_solver.
    by destruct s; eauto using reducible_not_val.
  Qed.

  Lemma ownP_lift_pure_det_head_step_no_fork {s E Φ} e1 e2 :
    (∀ σ1, head_reducible e1 σ1) →
    (∀ σ1 κ e2' σ2 efs', head_step e1 σ1 κ e2' σ2 efs' → κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
    ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof using Hinh.
    iIntros (??) "H"; iApply wp_lift_pure_det_step_no_fork; try by eauto.
    by destruct s; eauto using reducible_not_val.
  Qed.
End ectx_lifting.
