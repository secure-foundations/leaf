From iris.algebra Require Import lib.frac_auth numbers auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition newcounter : val := λ: <>, ref #0.
Definition incr : val := rec: "incr" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "incr" "l".
Definition read : val := λ: "l", !"l".

(** Monotone counter *)
Class mcounterG Σ := MCounterG { mcounter_inG : inG Σ (authR max_natUR) }.
Local Existing Instance mcounter_inG.

Definition mcounterΣ : gFunctors := #[GFunctor (authR max_natUR)].

Global Instance subG_mcounterΣ {Σ} : subG mcounterΣ Σ → mcounterG Σ.
Proof. solve_inG. Qed.

Section mono_proof.
  Context `{!heapGS Σ, !mcounterG Σ} (N : namespace).

  Definition mcounter_inv (γ : gname) (l : loc) : iProp Σ :=
    ∃ n, own γ (● (MaxNat n)) ∗ l ↦ #n.

  Definition mcounter (l : loc) (n : nat) : iProp Σ :=
    ∃ γ, inv N (mcounter_inv γ l) ∧ own γ (◯ (MaxNat n)).

  (** The main proofs. *)
  Global Instance mcounter_persistent l n : Persistent (mcounter l n).
  Proof. apply _. Qed.

  Lemma newcounter_mono_spec :
    {{{ True }}} newcounter #() {{{ l, RET #l; mcounter l 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /newcounter /=. wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (● (MaxNat O) ⋅ ◯ (MaxNat O))) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid_discrete.
    iMod (inv_alloc N _ (mcounter_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0. by iFrame. }
    iModIntro. iApply "HΦ". rewrite /mcounter; eauto 10.
  Qed.

  Lemma incr_mono_spec l n :
    {{{ mcounter l n }}} incr #l {{{ RET #(); mcounter l (S n) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". iLöb as "IH". wp_rec.
    iDestruct "Hl" as (γ) "[#? Hγf]".
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]".
    wp_load. iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (c') ">[Hγ Hl]".
    destruct (decide (c' = c)) as [->|].
    - iCombine "Hγ Hγf"
        gives %[?%max_nat_included _]%auth_both_valid_discrete.
      iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
      { apply auth_update, (max_nat_local_update _ _ (MaxNat (S c))). simpl. auto. }
      wp_cmpxchg_suc. iModIntro. iSplitL "Hl Hγ".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      wp_pures. iApply "HΦ". iModIntro. iExists γ; repeat iSplit; eauto.
      iApply (own_mono with "Hγf").
      (* FIXME: FIXME(Coq #6294): needs new unification *)
      apply: auth_frag_mono. by apply max_nat_included, le_n_S.
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]). iModIntro.
      iSplitL "Hl Hγ"; [iNext; iExists c'; by iFrame|].
      wp_pures. iApply ("IH" with "[Hγf] [HΦ]"); last by auto.
      rewrite {3}/mcounter; eauto 10.
  Qed.

  Lemma read_mono_spec l j :
    {{{ mcounter l j }}} read #l {{{ i, RET #i; ⌜j ≤ i⌝ ∧ mcounter l i }}}.
  Proof.
    iIntros (ϕ) "Hc HΦ". iDestruct "Hc" as (γ) "[#Hinv Hγf]".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hl]".
    wp_load.
    iCombine "Hγ Hγf"
      gives %[?%max_nat_included _]%auth_both_valid_discrete.
    iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
    { apply auth_update, (max_nat_local_update _ _ (MaxNat c)); auto. }
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[-]"). rewrite /mcounter; eauto 10.
  Qed.
End mono_proof.

(** Counter with contributions *)
Class ccounterG Σ :=
  CCounterG { ccounter_inG : inG Σ (frac_authR natR) }.
Local Existing Instance ccounter_inG.

Definition ccounterΣ : gFunctors :=
  #[GFunctor (frac_authR natR)].

Global Instance subG_ccounterΣ {Σ} : subG ccounterΣ Σ → ccounterG Σ.
Proof. solve_inG. Qed.

Section contrib_spec.
  Context `{!heapGS Σ, !ccounterG Σ} (N : namespace).

  Definition ccounter_inv (γ : gname) (l : loc) : iProp Σ :=
    ∃ n, own γ (●F n) ∗ l ↦ #n.

  Definition ccounter_ctx (γ : gname) (l : loc) : iProp Σ :=
    inv N (ccounter_inv γ l).

  Definition ccounter (γ : gname) (q : frac) (n : nat) : iProp Σ :=
    own γ (◯F{q} n).

  (** The main proofs. *)
  Lemma ccounter_op γ q1 q2 n1 n2 :
    ccounter γ (q1 + q2) (n1 + n2) ⊣⊢ ccounter γ q1 n1 ∗ ccounter γ q2 n2.
  Proof. by rewrite /ccounter frac_auth_frag_op -own_op. Qed.

  Lemma newcounter_contrib_spec (R : iProp Σ) :
    {{{ True }}} newcounter #()
    {{{ γ l, RET #l; ccounter_ctx γ l ∗ ccounter γ 1 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /newcounter /=. wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (●F O ⋅ ◯F 0)) as (γ) "[Hγ Hγ']";
      first by apply auth_both_valid_discrete.
    iMod (inv_alloc N _ (ccounter_inv γ l) with "[Hl Hγ]").
    { iNext. iExists 0. by iFrame. }
    iModIntro. iApply "HΦ". rewrite /ccounter_ctx /ccounter; eauto 10.
  Qed.

  Lemma incr_contrib_spec γ l q n :
    {{{ ccounter_ctx γ l ∗ ccounter γ q n }}} incr #l
    {{{ RET #(); ccounter γ q (S n) }}}.
  Proof.
    iIntros (Φ) "[#? Hγf] HΦ". iLöb as "IH". wp_rec.
    wp_bind (! _)%E. iInv N as (c) ">[Hγ Hl]".
    wp_load. iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (c') ">[Hγ Hl]".
    destruct (decide (c' = c)) as [->|].
    - iMod (own_update_2 with "Hγ Hγf") as "[Hγ Hγf]".
      { apply frac_auth_update, (nat_local_update _ _ (S c) (S n)); lia. }
      wp_cmpxchg_suc. iModIntro. iSplitL "Hl Hγ".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      wp_pures. by iApply "HΦ".
    - wp_cmpxchg_fail; first (by intros [= ?%Nat2Z.inj]).
      iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c'; by iFrame|].
      wp_pures. by iApply ("IH" with "[Hγf] [HΦ]"); auto.
  Qed.

  Lemma read_contrib_spec γ l q n :
    {{{ ccounter_ctx γ l ∗ ccounter γ q n }}} read #l
    {{{ c, RET #c; ⌜n ≤ c⌝ ∧ ccounter γ q n }}}.
  Proof.
    iIntros (Φ) "[#? Hγf] HΦ".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hl]". wp_load.
    iCombine "Hγ Hγf" gives % ?%frac_auth_included_total%nat_included.
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    iApply ("HΦ" with "[-]"); rewrite /ccounter; eauto 10.
  Qed.

  Lemma read_contrib_spec_1 γ l n :
    {{{ ccounter_ctx γ l ∗ ccounter γ 1 n }}} read #l
    {{{ RET #n; ccounter γ 1 n }}}.
  Proof.
    iIntros (Φ) "[#? Hγf] HΦ".
    rewrite /read /=. wp_lam. iInv N as (c) ">[Hγ Hl]". wp_load.
    iCombine "Hγ Hγf" gives % <-%frac_auth_agree_L.
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    by iApply "HΦ".
  Qed.
End contrib_spec.
