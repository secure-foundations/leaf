(** Ghost state for a monotonically increasing non-negative integer.
This is basically a [Z]-typed wrapper over [mono_nat], which can be useful when
one wants to use [Z] consistently for everything.
Provides an authoritative proposition [mono_Z_auth_own γ q n] for the
underlying number [n] and a persistent proposition [mono_nat_lb_own γ m]
witnessing that the authoritative nat is at least [m].

The key rules are [mono_Z_lb_own_valid], which asserts that an auth at [n] and
a lower-bound at [m] imply that [m ≤ n], and [mono_Z_update], which allows to
increase the auth element. At any time the auth nat can be "snapshotted" with
[mono_Z_get_lb] to produce a persistent lower-bound proposition.

Note: This construction requires the integers to be non-negative, i.e., to have
the lower bound 0, which gives [mono_Z_lb_own_0 : |==> mono_Z_lb_own γ 0]. This
rule would be false if we were to generalize to negative integers. See
https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/889 for a discussion about
the generalization to negative integers. *)
From iris.proofmode Require Import proofmode.
From iris.algebra.lib Require Import mono_nat.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import mono_nat.
From iris.prelude Require Import options.

Local Open Scope Z_scope.

Class mono_ZG Σ :=
  MonoZG { mono_ZG_natG : mono_natG Σ; }.
Local Existing Instance mono_ZG_natG.
Definition mono_ZΣ := mono_natΣ.

Local Definition mono_Z_auth_own_def `{!mono_ZG Σ}
    (γ : gname) (q : Qp) (n : Z) : iProp Σ :=
  ⌜0 ≤ n⌝ ∗ mono_nat_auth_own γ q (Z.to_nat n).
Local Definition mono_Z_auth_own_aux : seal (@mono_Z_auth_own_def).
Proof. by eexists. Qed.
Definition mono_Z_auth_own := mono_Z_auth_own_aux.(unseal).
Local Definition mono_Z_auth_own_unseal :
  @mono_Z_auth_own = @mono_Z_auth_own_def := mono_Z_auth_own_aux.(seal_eq).
Global Arguments mono_Z_auth_own {Σ _} γ q n.

Local Definition mono_Z_lb_own_def `{!mono_ZG Σ} (γ : gname) (n : Z) : iProp Σ :=
  ⌜0 ≤ n⌝ ∗ mono_nat_lb_own γ (Z.to_nat n).
Local Definition mono_Z_lb_own_aux : seal (@mono_Z_lb_own_def). Proof. by eexists. Qed.
Definition mono_Z_lb_own := mono_Z_lb_own_aux.(unseal).
Local Definition mono_Z_lb_own_unseal :
  @mono_Z_lb_own = @mono_Z_lb_own_def := mono_Z_lb_own_aux.(seal_eq).
Global Arguments mono_Z_lb_own {Σ _} γ n.

Local Ltac unseal := rewrite
  ?mono_Z_auth_own_unseal /mono_Z_auth_own_def
  ?mono_Z_lb_own_unseal /mono_Z_lb_own_def.

Section mono_Z.
  Context `{!mono_ZG Σ}.
  Implicit Types (n m : Z).

  Global Instance mono_Z_auth_own_timeless γ q n : Timeless (mono_Z_auth_own γ q n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_Z_lb_own_timeless γ n : Timeless (mono_Z_lb_own γ n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_Z_lb_own_persistent γ n : Persistent (mono_Z_lb_own γ n).
  Proof. unseal. apply _. Qed.

  Global Instance mono_Z_auth_own_fractional γ n :
    Fractional (λ q, mono_Z_auth_own γ q n).
  Proof.
    unseal. intros p q. iSplit.
    - iIntros "[% [$ $]]". eauto.
    - iIntros "[[% H1] [% H2]]". iCombine "H1 H2" as "$". eauto.
  Qed.
  Global Instance mono_Z_auth_own_as_fractional γ q n :
    AsFractional (mono_Z_auth_own γ q n) (λ q, mono_Z_auth_own γ q n) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma mono_Z_auth_own_agree γ q1 q2 n1 n2 :
    mono_Z_auth_own γ q1 n1 -∗
    mono_Z_auth_own γ q2 n2 -∗
    ⌜(q1 + q2 ≤ 1)%Qp ∧ n1 = n2⌝.
  Proof.
    unseal. iIntros "[% H1] [% H2]".
    iDestruct (mono_nat_auth_own_agree with "H1 H2") as %?.
    iPureIntro. naive_solver lia.
  Qed.
  Lemma mono_Z_auth_own_exclusive γ n1 n2 :
    mono_Z_auth_own γ 1 n1 -∗ mono_Z_auth_own γ 1 n2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (mono_Z_auth_own_agree with "H1 H2") as %[[] _].
  Qed.

  Lemma mono_Z_lb_own_valid γ q n m :
    mono_Z_auth_own γ q n -∗ mono_Z_lb_own γ m -∗ ⌜(q ≤ 1)%Qp ∧ m ≤ n⌝.
  Proof.
    unseal. iIntros "[% Hauth] [% Hlb]".
    iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %Hvalid.
    iPureIntro. naive_solver lia.
  Qed.

  (** The conclusion of this lemma is persistent; the proofmode will preserve
  the [mono_Z_auth_own] in the premise as long as the conclusion is introduced
  to the persistent context, for example with [iDestruct (mono_Z_lb_own_get
  with "Hauth") as "#Hfrag"]. *)
  Lemma mono_Z_lb_own_get γ q n :
    mono_Z_auth_own γ q n -∗ mono_Z_lb_own γ n.
  Proof. unseal. iIntros "[% ?]". iSplit; first done. by iApply mono_nat_lb_own_get. Qed.

  Lemma mono_Z_lb_own_le {γ n} n' :
    n' ≤ n →
    0 ≤ n' →
    mono_Z_lb_own γ n -∗ mono_Z_lb_own γ n'.
  Proof.
    unseal. iIntros "% % [% ?]". iSplit; first done.
    iApply mono_nat_lb_own_le; last done. lia.
  Qed.

  Lemma mono_Z_lb_own_0 γ :
    ⊢ |==> mono_Z_lb_own γ 0.
  Proof. unseal. iMod mono_nat_lb_own_0 as "$". eauto. Qed.

  Lemma mono_Z_own_alloc n :
    0 ≤ n →
    ⊢ |==> ∃ γ, mono_Z_auth_own γ 1 n ∗ mono_Z_lb_own γ n.
  Proof.
    unseal. intros. iMod mono_nat_own_alloc as (γ) "[??]".
    iModIntro. iExists _. iFrame. eauto.
  Qed.

  Lemma mono_Z_own_update {γ n} n' :
    n ≤ n' →
    mono_Z_auth_own γ 1 n ==∗ mono_Z_auth_own γ 1 n' ∗ mono_Z_lb_own γ n'.
  Proof.
    iIntros (?) "Hauth".
    iAssert (mono_Z_auth_own γ 1 n') with "[> Hauth]" as "Hauth".
    { unseal. iDestruct "Hauth" as "[% Hauth]".
      iMod (mono_nat_own_update with "Hauth") as "[$ _]"; auto with lia. }
    iModIntro. iSplit; [done|]. by iApply mono_Z_lb_own_get.
  Qed.
End mono_Z.
