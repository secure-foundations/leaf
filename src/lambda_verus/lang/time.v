From iris.algebra Require Import lib.mono_nat numbers.
From iris.base_logic Require Import lib.own.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import proofmode.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".
Import uPred.

Class timeGS Σ := TimeG {
  time_mono_nat_inG :> inG Σ mono_natR;
  time_nat_inG :> inG Σ (authR natUR);
  time_global_name : gname;
  time_persistent_name : gname;
  time_cumulative_name : gname;
}.

Class timePreG Σ := TimePreG {
  time_preG_mono_nat_inG :> inG Σ mono_natR;
  time_preG_nat_inG :> inG Σ (authR natUR);
}.

Definition timeΣ : gFunctors :=
  #[GFunctor (constRF mono_natR); GFunctor (constRF (authR natUR))].
Global Instance subG_timePreG Σ : subG timeΣ Σ → timePreG Σ.
Proof. solve_inG. Qed.

Definition timeN : namespace := nroot .@ "lft_usr" .@ "time".

Section definitions.
  Context `{!timeGS Σ}.

  (** persistent time receipt *)
  Definition persistent_time_receipt (n : nat) :=
    own time_persistent_name (mono_nat_lb n).
  (** cumulative time receipt *)
  Definition cumulative_time_receipt (n : nat) :=
    own time_cumulative_name (◯ n).
  (** invariant *)
  Definition time_ctx `{!invGS Σ} :=
    inv timeN (∃ n m,
       own time_global_name (mono_nat_lb (n + m)) ∗
       own time_cumulative_name (● n) ∗
       own time_persistent_name (●MN m)).
  (** authority *)
  Definition time_interp (n: nat) : iProp Σ :=
    own time_global_name (●MN n).
End definitions.

Global Typeclasses Opaque persistent_time_receipt cumulative_time_receipt.
Global Instance: Params (@persistent_time_receipt) 2 := {}.
Global Instance: Params (@cumulative_time_receipt) 2 := {}.

Notation "⧖ n" := (persistent_time_receipt n)
  (at level 1, format "⧖ n") : bi_scope.
Notation "⧗ n" := (cumulative_time_receipt n)
  (at level 1, format "⧗ n") : bi_scope.

Section time.
  Context `{!timeGS Σ}.
  Implicit Types P Q : iProp Σ.

  Global Instance persistent_time_receipt_timeless n : Timeless (⧖n).
  Proof. unfold persistent_time_receipt. apply _. Qed.
  Global Instance persistent_time_receipt_persistent n : Persistent (⧖n).
  Proof. unfold persistent_time_receipt. apply _. Qed.
  Global Instance cumulative_time_receipt_timeless n : Timeless (⧗n).
  Proof. unfold cumulative_time_receipt. apply _. Qed.

  Lemma time_interp_step n :
    time_interp n ==∗ time_interp (S n).
  Proof. eapply own_update, mono_nat_update. lia. Qed.

  Lemma persistent_time_receipt_mono n m :
    (n ≤ m)%nat → ⧖m -∗ ⧖n.
  Proof.
    intros ?. unfold persistent_time_receipt. by apply own_mono, mono_nat_lb_mono.
  Qed.
  Lemma cumulative_time_receipt_mono n m :
    (n ≤ m)%nat → ⧗m -∗ ⧗n.
  Proof.
    intros ?. unfold cumulative_time_receipt.
    by apply own_mono, auth_frag_mono, nat_included.
  Qed.

  Lemma persistent_time_receipt_sep n m : ⧖(n `max` m) ⊣⊢ ⧖n ∗ ⧖m.
  Proof. by rewrite /persistent_time_receipt mono_nat_lb_op own_op. Qed.
  Lemma cumulative_time_receipt_sep n m : ⧗(n + m) ⊣⊢ ⧗n ∗ ⧗m.
  Proof. by rewrite /cumulative_time_receipt -nat_op auth_frag_op own_op. Qed.

  Global Instance persistent_time_receipt_from_sep n m : FromSep ⧖(n `max` m) ⧖n ⧖m.
  Proof. rewrite /FromSep. by rewrite persistent_time_receipt_sep. Qed.
  Global Instance persistent_time_receipt_into_sep n m : IntoSep ⧖(n `max` m) ⧖n ⧖m.
  Proof. rewrite /IntoSep. by rewrite persistent_time_receipt_sep. Qed.
  Global Instance cumulative_time_receipt_from_sep n m : FromSep ⧗(n + m) ⧗n ⧗m.
  Proof. rewrite /FromSep. by rewrite cumulative_time_receipt_sep. Qed.
  Global Instance cumulative_time_receipt_into_sep n m : IntoSep ⧗(n + m) ⧗n ⧗m.
  Proof. rewrite /IntoSep. by rewrite cumulative_time_receipt_sep. Qed.

  Lemma persistent_time_receipt_0 : ⊢ |==> ⧖0.
  Proof. rewrite /persistent_time_receipt. apply own_unit. Qed.
  Lemma cumulative_time_receipt_0 : ⊢ |==> ⧗0.
  Proof. rewrite /cumulative_time_receipt. apply own_unit. Qed.

  Lemma cumulative_persistent_time_receipt `{!invGS Σ} E n m :
    ↑timeN ⊆ E → time_ctx -∗ ⧗n -∗ ⧖m ={E}=∗ ⧖(n + m).
  Proof.
    iIntros (?) "#TIME Hn #Hm".
    unfold persistent_time_receipt, cumulative_time_receipt.
    iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm')".
    iDestruct (own_valid_2 with "Hn' Hn")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hm' Hm") as %?%mono_nat_both_valid.
    iMod (own_update_2 with "Hn' Hn") as "Hnn'".
    { apply (auth_update_dealloc _ _ (n'-n)%nat), nat_local_update.
      rewrite -plus_n_O. lia. }
    iMod (own_update with "Hm'") as "Hm'n".
    { apply (mono_nat_update (m'+n)%nat); lia. }
    iDestruct (own_mono _ _ (mono_nat_lb _) with "Hm'n") as "#$".
    { rewrite <-mono_nat_included. apply mono_nat_lb_mono. lia. }
    iModIntro; iSplitL; [|done]. iExists _, _. iFrame.
    rewrite (_:(n'+m')%nat = ((n'-n) + (m'+n))%nat); [done|lia].
  Qed.

  Lemma step_cumulative_time_receipt `{!invGS Σ} E n :
    ↑timeN ⊆ E →
    time_ctx -∗ time_interp n ={E, E∖↑timeN}=∗ time_interp n ∗
    (time_interp (S n) ={E∖↑timeN, E}=∗ time_interp (S n) ∗ ⧗1).
  Proof.
    iIntros (?) "#TIME Hn". iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm')" "Hclose".
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iModIntro. iFrame. iIntros "HSn". unfold cumulative_time_receipt.
    iMod (own_update with "Hn'") as "[HSn' $]".
    { apply auth_update_alloc, nat_local_update. by rewrite -plus_n_O. }
    iDestruct (own_mono _ _ (mono_nat_lb _) with "HSn") as "#H'Sn".
    { apply mono_nat_included. }
    iFrame. iApply "Hclose". iExists _, _. iFrame.
    iApply (own_mono with "H'Sn"). apply mono_nat_lb_mono. lia.
  Qed.

  Lemma time_receipt_le `{!invGS Σ} E n m m' :
    ↑timeN ⊆ E →
    time_ctx -∗ time_interp n -∗ ⧖m -∗ ⧗m' ={E}=∗
    ⌜m+m' ≤ n⌝%nat ∗ time_interp n ∗ ⧗m'.
  Proof.
    iIntros (?) "#TIME Hn Hm Hm'". iInv "TIME" as (m'0 m0) ">(Hglob & Hm'0 & Hm0)".
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm0 Hm") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm'0 Hm'")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iModIntro. iFrame. iSplitL; auto with iFrame lia.
  Qed.
End time.

Lemma time_init `{!invGS Σ, !timePreG Σ} E : ↑timeN ⊆ E →
  ⊢ |={E}=> ∃ _ : timeGS Σ, time_ctx ∗ time_interp 0.
Proof.
  intros ?.
  iMod (own_alloc (●MN 0 ⋅ mono_nat_lb 0)) as (time_global_name) "[??]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (●MN 0)) as (time_persistent_name) "?";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc (● 0%nat)) as (time_cumulative_name) "?"; [by apply auth_auth_valid|].
  iExists (TimeG _ _ _ time_global_name time_persistent_name time_cumulative_name).
  iFrame. iApply inv_alloc. iExists 0%nat, 0%nat. iFrame.
Qed.
