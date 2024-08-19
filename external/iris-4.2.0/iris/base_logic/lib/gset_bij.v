(** Propositions for reasoning about monotone partial bijections.

This library provides two propositions [gset_bij_own_auth γ L] and
[gset_bij_own_elem γ a b], where [L] is a bijection between types [A] and [B]
represented by a set of associations [gset (A * B)]. The idea is that
[gset_bij_own_auth γ L] is an authoritative bijection [L], while
[gset_bij_own_elem γ a b] is a persistent resource saying [L] associates [a]
and [b].

The main use case is in a logical relation-based proof where [L] maintains the
association between locations [A] in one execution and [B] in another (perhaps
of different types, if the logical relation relates two different semantics).

The association [L] is always bijective, so that if [a] is mapped to [b], there
should be no other mappings for either [a] or [b]; the [gset_bij_own_extend]
update theorem enforces that new mappings respect this property, and
[gset_bij_own_elem_agree] allows the user to exploit bijectivity. The bijection
grows monotonically, so that the set of associations only grows; this is
captured by the persistence of [gset_bij_own_elem].

This library is a logical, ownership-based wrapper around [gset_bij]. *)

From iris.algebra.lib Require Import gset_bij.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

(* The uCMRA we need. *)
Class gset_bijG Σ A B `{Countable A, Countable B} :=
  GsetBijG { gset_bijG_inG : inG Σ (gset_bijR A B); }.
Local Existing Instance gset_bijG_inG.
Global Hint Mode gset_bijG - ! ! - - - - : typeclass_instances.

Definition gset_bijΣ A B `{Countable A, Countable B}: gFunctors :=
  #[ GFunctor (gset_bijR A B) ].
Global Instance subG_gset_bijΣ `{Countable A, Countable B} Σ :
  subG (gset_bijΣ A B) Σ → gset_bijG Σ A B.
Proof. solve_inG. Qed.

Definition gset_bij_own_auth_def `{gset_bijG Σ A B} (γ : gname)
    (dq : dfrac) (L : gset (A * B)) : iProp Σ :=
  own γ (gset_bij_auth dq L).
Definition gset_bij_own_auth_aux : seal (@gset_bij_own_auth_def). Proof. by eexists. Qed.
Definition gset_bij_own_auth := unseal gset_bij_own_auth_aux.
Definition gset_bij_own_auth_eq :
  @gset_bij_own_auth = @gset_bij_own_auth_def := seal_eq gset_bij_own_auth_aux.
Global Arguments gset_bij_own_auth {_ _ _ _ _ _ _ _}.

Definition gset_bij_own_elem_def `{gset_bijG Σ A B} (γ : gname)
  (a : A) (b : B) : iProp Σ := own γ (gset_bij_elem a b).
Definition gset_bij_own_elem_aux : seal (@gset_bij_own_elem_def). Proof. by eexists. Qed.
Definition gset_bij_own_elem := unseal gset_bij_own_elem_aux.
Definition gset_bij_own_elem_eq :
  @gset_bij_own_elem = @gset_bij_own_elem_def := seal_eq gset_bij_own_elem_aux.
Global Arguments gset_bij_own_elem {_ _ _ _ _ _ _ _}.

Section gset_bij.
  Context `{gset_bijG Σ A B}.
  Implicit Types (L : gset (A * B)) (a : A) (b : B).

  Global Instance gset_bij_own_auth_timeless γ q L :
    Timeless (gset_bij_own_auth γ q L).
  Proof. rewrite gset_bij_own_auth_eq. apply _. Qed.
  Global Instance gset_bij_own_elem_timeless γ a b :
    Timeless (gset_bij_own_elem γ a b).
  Proof. rewrite gset_bij_own_elem_eq. apply _. Qed.
  Global Instance gset_bij_own_elem_persistent γ a b :
    Persistent (gset_bij_own_elem γ a b).
  Proof. rewrite gset_bij_own_elem_eq. apply _. Qed.

  Global Instance gset_bij_own_auth_fractional γ L :
    Fractional (λ q, gset_bij_own_auth γ (DfracOwn q) L).
  Proof.
    intros p q. rewrite gset_bij_own_auth_eq -own_op gset_bij_auth_dfrac_op //.
  Qed.
  Global Instance gset_bij_own_auth_as_fractional γ q L :
    AsFractional (gset_bij_own_auth γ (DfracOwn q) L) (λ q, gset_bij_own_auth γ (DfracOwn q) L) q.
  Proof. split; [auto|apply _]. Qed.

  Lemma gset_bij_own_auth_agree γ dq1 dq2 L1 L2 :
    gset_bij_own_auth γ dq1 L1 -∗ gset_bij_own_auth γ dq2 L2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ L1 = L2 ∧ gset_bijective L1⌝.
  Proof.
    rewrite gset_bij_own_auth_eq. iIntros "H1 H2".
    by iCombine "H1 H2" gives %?%gset_bij_auth_dfrac_op_valid.
  Qed.
  Lemma gset_bij_own_auth_exclusive γ L1 L2 :
    gset_bij_own_auth γ (DfracOwn 1) L1 -∗ gset_bij_own_auth γ (DfracOwn 1) L2 -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (gset_bij_own_auth_agree with "H1 H2") as %[[] _].
  Qed.

  Lemma gset_bij_own_valid γ q L :
    gset_bij_own_auth γ q L -∗ ⌜✓ q ∧ gset_bijective L⌝.
  Proof.
    rewrite gset_bij_own_auth_eq. iIntros "Hauth".
    by iDestruct (own_valid with "Hauth") as %?%gset_bij_auth_dfrac_valid.
  Qed.

  Lemma gset_bij_own_elem_agree γ a a' b b' :
    gset_bij_own_elem γ a b -∗ gset_bij_own_elem γ a' b' -∗
    ⌜a = a' ↔ b = b'⌝.
  Proof.
    rewrite gset_bij_own_elem_eq. iIntros "Hel1 Hel2".
    by iCombine "Hel1 Hel2" gives %?%gset_bij_elem_agree.
  Qed.

  Lemma gset_bij_own_elem_get {γ q L} a b :
    (a, b) ∈ L →
    gset_bij_own_auth γ q L -∗ gset_bij_own_elem γ a b.
  Proof.
    intros. rewrite gset_bij_own_auth_eq gset_bij_own_elem_eq.
    iApply own_mono. by apply bij_view_included.
  Qed.

  Lemma gset_bij_elem_of {γ q L} a b :
    gset_bij_own_auth γ q L -∗ gset_bij_own_elem γ a b -∗ ⌜(a, b) ∈ L⌝.
  Proof.
    iIntros "Hauth Helem". rewrite gset_bij_own_auth_eq gset_bij_own_elem_eq.
    iCombine "Hauth Helem" gives "%Ha".
    iPureIntro. revert Ha. rewrite bij_both_dfrac_valid. intros (_ & _ & ?); done.
  Qed.

  Lemma gset_bij_own_elem_get_big γ q L :
    gset_bij_own_auth γ q L -∗ [∗ set] ab ∈ L, gset_bij_own_elem γ ab.1 ab.2.
  Proof.
    iIntros "Hauth". iApply big_sepS_forall. iIntros ([a b] ?) "/=".
    by iApply gset_bij_own_elem_get.
  Qed.

  Lemma gset_bij_own_alloc L :
    gset_bijective L →
    ⊢ |==> ∃ γ, gset_bij_own_auth γ (DfracOwn 1) L ∗ [∗ set] ab ∈ L, gset_bij_own_elem γ ab.1 ab.2.
  Proof.
    intro. iAssert (∃ γ, gset_bij_own_auth γ (DfracOwn 1) L)%I with "[>]" as (γ) "Hauth".
    { rewrite gset_bij_own_auth_eq. iApply own_alloc. by apply gset_bij_auth_valid. }
    iExists γ. iModIntro. iSplit; [done|].
    by iApply gset_bij_own_elem_get_big.
  Qed.
  Lemma gset_bij_own_alloc_empty :
    ⊢ |==> ∃ γ, gset_bij_own_auth γ (DfracOwn 1) (∅ : gset (A * B)).
  Proof. iMod (gset_bij_own_alloc ∅) as (γ) "[Hauth _]"; by auto. Qed.

  Lemma gset_bij_own_extend {γ L} a b :
    (∀ b', (a, b') ∉ L) → (∀ a', (a', b) ∉ L) →
    gset_bij_own_auth γ (DfracOwn 1) L ==∗
    gset_bij_own_auth γ (DfracOwn 1) ({[(a, b)]} ∪ L) ∗ gset_bij_own_elem γ a b.
  Proof.
    iIntros (??) "Hauth".
    iAssert (gset_bij_own_auth γ (DfracOwn 1) ({[(a, b)]} ∪ L)) with "[> Hauth]" as "Hauth".
    { rewrite gset_bij_own_auth_eq. iApply (own_update with "Hauth").
      by apply gset_bij_auth_extend. }
    iModIntro. iSplit; [done|].
    iApply (gset_bij_own_elem_get with "Hauth"). set_solver.
  Qed.

  Lemma gset_bij_own_extend_internal {γ L} a b :
    (∀ b', gset_bij_own_elem γ a b' -∗ False) -∗
    (∀ a', gset_bij_own_elem γ a' b -∗ False) -∗
    gset_bij_own_auth γ (DfracOwn 1) L ==∗
    gset_bij_own_auth γ (DfracOwn 1) ({[(a, b)]} ∪ L) ∗ gset_bij_own_elem γ a b.
  Proof.
    iIntros "Ha Hb HL".
    iAssert ⌜∀ b', (a, b') ∉ L⌝%I as %?.
    { iIntros (b' ?). iApply ("Ha" $! b'). by iApply gset_bij_own_elem_get. }
    iAssert ⌜∀ a', (a', b) ∉ L⌝%I as %?.
    { iIntros (a' ?). iApply ("Hb" $! a'). by iApply gset_bij_own_elem_get. }
    by iApply (gset_bij_own_extend with "HL").
  Qed.
End gset_bij.
