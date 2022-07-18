From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export base_logic.
From stdpp Require Import gmap.

From iris.algebra Require Export gmap.

Require Import TwoExamples.hash_table_raw.
Require Import iris.base_logic.lib.own.

Global Instance ht_unit : Unit HT := ht_unit.
Global Instance ht_equiv : Equiv HT := λ a b , a = b.
Global Instance ht_pcore : PCore HT := λ a , Some ε.
Global Instance ht_op : Op HT := λ a b , ht_dot a b.
Global Instance ht_valid : Valid HT := λ a , V a.

Definition ht_ra_mixin : RAMixin HT.
Proof. split.
  - typeclasses eauto.
  - unfold pcore, ht_pcore. intros x y cx H0 H. exists ε. split; trivial. inversion H. trivial.
  - typeclasses eauto.
  - unfold Assoc. intros. apply ht_dot_assoc.
  - unfold Comm. intros. apply ht_dot_comm.
  - unfold pcore, ht_pcore. intros x cx H. inversion H.
      unfold "≡", ht_equiv. unfold "⋅", ε, ht_op.
      rewrite ht_dot_comm. apply ht_unit_dot.
  - unfold pcore, ht_pcore. intros m cx H. rewrite H. trivial.
  - unfold pcore, ht_pcore. intros x y cx incl H.
      inversion H. subst cx. exists ε. split; trivial.
      unfold "≼". exists ε. unfold "⋅", ht_op. rewrite ht_unit_dot. trivial.
  - intros x y. apply ht_valid_monotonic.
Qed.

Canonical Structure htO
  := discreteO HT.
  
Canonical Structure htR
    :=
   discreteR HT ht_ra_mixin.
   
Global Instance ht_cmra_discrete : CmraDiscrete htR.
Proof. apply discrete_cmra_discrete. Qed.
   
Definition ht_ucmra_mixin : UcmraMixin HT.
Proof. split.
  - apply ht_unit_valid.
  - unfold LeftId. intro x. unfold ε, "⋅", ht_op. rewrite ht_dot_comm. apply ht_unit_dot.
  - trivial.
Qed.

Canonical Structure htUR := Ucmra HT ht_ucmra_mixin.

Class ht_logicG Σ :=
    {
      ht_logic_inG :> inG Σ htUR
    }.

Section HashTableLogic.

Context {Σ: gFunctors}.
Context {htl: ht_logicG Σ}.

Lemma ht_Init (n: nat) :
  ⊢ |==> (∃ γ , own γ (mseq n) ∗ own γ (sseq ht_fixed_size))%I.
Proof.
  iIntros.
  iMod (own_alloc ((mseq n) ⋅ (sseq ht_fixed_size))) as (γ) "x".
  { apply valid_mseq_sseq. }
  iModIntro. iExists γ. iDestruct (own_op with "x") as "[x y]". iFrame.
Qed.

Lemma ht_QueryFound1 γ j k v0 v :
  own γ (s j (Some (k, v0))) ∗ own γ (m k v) ⊢ ⌜ v = Some v0 ⌝.
Proof.
  rewrite <- own_op.
  iIntros "o".
  iDestruct (own_valid with "o") as "%val". iPureIntro.
  eapply ht_valid_QueryFound.
  apply val.
Qed.

Lemma ht_QueryFound 𝜅 𝛾 j k v0 v :
  A 𝜅 -∗ B 𝜅 𝛾 (s j (Some (k, v0))) -∗ L 𝛾 (m k v) -∗ ⌜ v = Some v0 ⌝.
Proof.
  iIntros "a b l".
  iDestruct (LiveAndBorrowValid with "a l b") as "%t".
  iPureIntro.
  eapply ht_valid_QueryFound.
    unfold m_valid, dot, ht_tpcm in t.
    rewrite ht_dot_comm in t.
    apply t.
Qed.

(*
Definition Range 𝛾 k i j : iProp Σ :=
  ∃ a , ⌜ full a k i j ⌝ ∗ L 𝛾 a.
  *)
  
Definition BorrowedRange 𝜅 𝛾 k i j : iProp Σ :=
  ∃ a , ⌜ full a k i j ⌝ ∗ B 𝜅 𝛾 a.

Lemma ht_QueryReachedEnd 𝜅 𝛾 k v :
  A 𝜅 -∗ BorrowedRange 𝜅 𝛾 k (hash k) ht_fixed_size -∗ L 𝛾 (m k v) -∗ ⌜ v = None ⌝.
Proof.
  iIntros "a range l".
  iDestruct "range" as (a) "[%f range]".
  iDestruct (LiveAndBorrowValid with "a l range") as "%t".
  iPureIntro.
  eapply ht_valid_QueryReachedEnd.
    - apply f.
    - rewrite ht_dot_comm. trivial.
Qed.

Lemma ht_QueryNotFound 𝜅 𝛾 k v j :
  A 𝜅 -∗ BorrowedRange 𝜅 𝛾 k (hash k) j -∗ B 𝜅 𝛾 (s j None) -∗ L 𝛾 (m k v) -∗ ⌜ v = None ⌝.
Proof.
  iIntros "a range c l".
  iDestruct "range" as (a) "[%f range]".
  iDestruct (BorrowCombine 𝜅 𝛾 (a) (s j None) ((ht_dot a (s j None))) with "[range c]") as "t".
  - intro. intros. apply full_add with (k := k) (i := hash k); trivial.
  - iFrame.
  - iDestruct (LiveAndBorrowValid with "a l t") as "%t".
    iPureIntro. apply ht_valid_QueryNotFound with (a := a) (k := k) (j := j); trivial.
    rewrite tpcm_assoc in t.
    replace ((dot (m k v) a)) with (dot a (m k v)) in t; trivial.
    apply tpcm_comm.
Qed.

(*
Lemma ht_RangeAppend 𝛾 k i j k0 v0
  (ne: k0 ≠ k) : Range 𝛾 k i j -∗ L 𝛾 (s j (Some (k0, v0))) -∗ Range 𝛾 k i (j+1).
Proof.
  iIntros "r l". unfold Range. iDestruct "r" as (a) "[%r q]".
  iExists (ht_dot a (s j (Some (k0, v0)))).
  rewrite L_op. iFrame. iPureIntro. apply full_dot; trivial.
Qed.
*)

Lemma ht_BorrowedRangeEmpty 𝛾 k i
  : ⊢ |==> ∃ 𝜅 , BorrowedRange 𝜅 𝛾 k i i ∗ A 𝜅.
Proof.
  iIntros.
  iMod (L_unit HT 𝛾) as "u".
  iMod (BorrowBegin _ _ with "u") as (𝜅) "[a [r b]]".
  iModIntro. unfold BorrowedRange. iExists 𝜅. iFrame. iExists unit. iFrame. iPureIntro.
  apply full_trivial.
Qed.

Lemma ht_BorrowedRangeAppend 𝜅 𝛾 k i j k0 v0
  (ne: k0 ≠ k) : BorrowedRange 𝜅 𝛾 k i j -∗ B 𝜅 𝛾 (s j (Some (k0, v0)))
      -∗ BorrowedRange 𝜅 𝛾 k i (j+1).
Proof.
  iIntros "r l". unfold BorrowedRange. iDestruct "r" as (a) "[%r q]".
  iDestruct (BorrowCombine 𝜅 𝛾 (a) (s j (Some (k0, v0))) ((ht_dot a (s j (Some (k0, v0))))) with "[q l]") as "t".
  - intro. intros. apply full_add with (k := k) (i := i); trivial.
  - iFrame.
  - iExists (ht_dot a (s j (Some (k0, v0)))).
    iFrame. iPureIntro. apply full_dot; trivial.
Qed.

Lemma ht_BorrowedRangeShorten 𝜅 𝜅' 𝛾 k i j
  (li: lifetime_included 𝜅' 𝜅)
  : BorrowedRange 𝜅 𝛾 k i j -∗ BorrowedRange 𝜅' 𝛾 k i j.
Proof.
  iIntros "b".
  unfold BorrowedRange. iDestruct "b" as (a) "[%f b]".
  iDestruct (BorrowShorten _ 𝜅' _ _ with "b") as "b"; trivial.
  iExists a. iFrame. iPureIntro. trivial.
Qed.

Lemma ht_UpdateExisting 𝛾 k v v0 v1 j :
  L 𝛾 (s j (Some (k, v1))) -∗ L 𝛾 (m k v0) ==∗
  L 𝛾 (s j (Some (k, v))) ∗ L 𝛾 (m k (Some v)).
Proof.
  iIntros "s m".
  iDestruct (L_join with "s m") as "s".
  iMod (FrameUpdate _ _ (ht_dot (s j (Some (k, v))) (m k (Some v))) with "s") as "A".
  - apply ht_update_existing.
  - iModIntro. rewrite <- L_op. iFrame.
Qed.

Lemma ht_UpdateNew 𝛾 k v j v0 a
  (f: full a k (hash k) j) :
  L 𝛾 a -∗ L 𝛾 (s j None) -∗ L 𝛾 (m k v0) ==∗
  L 𝛾 a ∗ L 𝛾 (s j (Some (k, v))) ∗ L 𝛾 (m k (Some v)).
Proof.
  iIntros "r s m".
  iDestruct (L_join with "s m") as "s".
  iDestruct (L_join with "s r") as "s".
  iMod (FrameUpdate _ _ (ht_dot (ht_dot (s j (Some (k, v))) (m k (Some v))) a) with "s") as "A".
  - apply ht_update_new. trivial.
  - iModIntro.
  iDestruct (L_op with "A") as "[x y]".
  iDestruct (L_op with "x") as "[x z]".
  iFrame.
Qed.

End HashTableLogic.
