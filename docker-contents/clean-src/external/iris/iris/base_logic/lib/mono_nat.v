(** Ghost state for a monotonically increasing nat, wrapping the [mono_natR]
RA. Provides an authoritative proposition [mono_nat_auth_own γ q n] for the
underlying number [n] and a persistent proposition [mono_nat_lb_own γ m]
witnessing that the authoritative nat is at least m.

The key rules are [mono_nat_lb_own_valid], which asserts that an auth at [n] and
a lower-bound at [m] imply that [m ≤ n], and [mono_nat_update], which allows to
increase the auth element. At any time the auth nat can be "snapshotted" with
[mono_nat_get_lb] to produce a persistent lower-bound proposition. *)
From iris.proofmode Require Import tactics.
From iris.algebra.lib Require Import mono_nat.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Class mono_natG Σ :=
  MonoNatG { mono_natG_inG :> inG Σ mono_natR; }.
Definition mono_natΣ : gFunctors := #[ GFunctor mono_natR ].
Global Instance subG_mono_natΣ Σ : subG mono_natΣ Σ → mono_natG Σ.
Proof. solve_inG. Qed.

Definition mono_nat_auth_own_def `{!mono_natG Σ}
    (γ : gname) (q : Qp) (n : nat) : iProp Σ :=
  own γ (mono_nat_auth q n).
Definition mono_nat_auth_own_aux : seal (@mono_nat_auth_own_def). Proof. by eexists. Qed.
Definition mono_nat_auth_own := mono_nat_auth_own_aux.(unseal).
Definition mono_nat_auth_own_eq :
  @mono_nat_auth_own = @mono_nat_auth_own_def := mono_nat_auth_own_aux.(seal_eq).
Global Arguments mono_nat_auth_own {Σ _} γ q n.

Definition mono_nat_lb_own_def `{!mono_natG Σ} (γ : gname) (n : nat): iProp Σ :=
  own γ (mono_nat_lb n).
Definition mono_nat_lb_own_aux : seal (@mono_nat_lb_own_def). Proof. by eexists. Qed.
Definition mono_nat_lb_own := mono_nat_lb_own_aux.(unseal).
Definition mono_nat_lb_own_eq :
  @mono_nat_lb_own = @mono_nat_lb_own_def := mono_nat_lb_own_aux.(seal_eq).
Global Arguments mono_nat_lb_own {Σ _} γ n.

Local Ltac unseal := rewrite
  ?mono_nat_auth_own_eq /mono_nat_auth_own_def
  ?mono_nat_lb_own_eq /mono_nat_lb_own_def.

Section mono_nat.
  Context `{!mono_natG Σ}.
  Implicit Types (n m : nat).

  Global Instance mono_nat_auth_own_timeless γ q n : Timeless (mono_nat_auth_own γ q n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_lb_own_timeless γ n : Timeless (mono_nat_lb_own γ n).
  Proof. unseal. apply _. Qed.
  Global Instance mono_nat_lb_own_persistent γ n : Persistent (mono_nat_lb_own γ n).
  Proof. unseal. apply _. Qed.

  Global Instance mono_nat_auth_own_fractional γ n :
    Fractional (λ q, mono_nat_auth_own γ q n).
  Proof. unseal. intros p q. rewrite -own_op mono_nat_auth_frac_op //. Qed.
  Global Instance mono_nat_auth_own_as_fractional γ q n :
    AsFractional (mono_nat_auth_own γ q n) (λ q, mono_nat_auth_own γ q n) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma mono_nat_auth_own_agree γ q1 q2 n1 n2 :
    mono_nat_auth_own γ q1 n1 -∗
    mono_nat_auth_own γ q2 n2 -∗
    ⌜(q1 + q2 ≤ 1)%Qp ∧ n1 = n2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%mono_nat_auth_frac_op_valid; done.
  Qed.
  Lemma mono_nat_auth_own_exclusive γ n1 n2 :
    mono_nat_auth_own γ 1 n1 -∗ mono_nat_auth_own γ 1 n2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (mono_nat_auth_own_agree with "H1 H2") as %[[] _].
  Qed.

  Lemma mono_nat_lb_own_valid γ q n m :
    mono_nat_auth_own γ q n -∗ mono_nat_lb_own γ m -∗ ⌜(q ≤ 1)%Qp ∧ m ≤ n⌝.
  Proof.
    unseal. iIntros "Hauth Hlb".
    iDestruct (own_valid_2 with "Hauth Hlb") as %Hvalid%mono_nat_both_frac_valid.
    auto.
  Qed.

  (** The conclusion of this lemma is persistent; the proofmode will preserve
  the [mono_nat_auth_own] in the premise as long as the conclusion is introduced
  to the persistent context, for example with [iDestruct (mono_nat_lb_own_get
  with "Hauth") as "#Hfrag"]. *)
  Lemma mono_nat_lb_own_get γ q n :
    mono_nat_auth_own γ q n -∗ mono_nat_lb_own γ n.
  Proof. unseal. apply own_mono, mono_nat_included. Qed.

  Lemma mono_nat_lb_own_le {γ n} n' :
    n' ≤ n →
    mono_nat_lb_own γ n -∗ mono_nat_lb_own γ n'.
  Proof. unseal. intros. by apply own_mono, mono_nat_lb_mono. Qed.

  Lemma mono_nat_own_alloc n :
    ⊢ |==> ∃ γ, mono_nat_auth_own γ 1 n ∗ mono_nat_lb_own γ n.
  Proof.
    unseal. iMod (own_alloc (mono_nat_auth 1 n ⋅ mono_nat_lb n)) as (γ) "[??]".
    { apply mono_nat_both_valid; auto. }
    auto with iFrame.
  Qed.

  Lemma mono_nat_own_update {γ n} n' :
    n ≤ n' →
    mono_nat_auth_own γ 1 n ==∗ mono_nat_auth_own γ 1 n' ∗ mono_nat_lb_own γ n'.
  Proof.
    iIntros (?) "Hauth".
    iAssert (mono_nat_auth_own γ 1 n') with "[> Hauth]" as "Hauth".
    { unseal. iApply (own_update with "Hauth"). by apply mono_nat_update. }
    iModIntro. iSplit; [done|]. by iApply mono_nat_lb_own_get.
  Qed.
End mono_nat.
