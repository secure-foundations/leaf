From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export base_logic.
From stdpp Require Import gmap.

From iris.algebra Require Export gmap.

Require Import TwoExamples.hash_table_raw.
Require Import iris.base_logic.lib.own.
Require Import Two.guard.

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
Context `{!invGS Σ}. 

Lemma ht_Init (n: nat) :
  ⊢ |==> (∃ γ , own γ (mseq n) ∗ own γ (sseq ht_fixed_size))%I.
Proof.
  iIntros.
  iMod (own_alloc ((mseq n) ⋅ (sseq ht_fixed_size))) as (γ) "x".
  { apply valid_mseq_sseq. }
  iModIntro. iExists γ. iDestruct (own_op with "x") as "[x y]". iFrame.
Qed.

Lemma ht_QueryFound γ j k v0 v :
  own γ (s j (Some (k, v0))) ∗ own γ (m k v) ⊢ ⌜ v = Some v0 ⌝.
Proof.
  rewrite <- own_op.
  iIntros "o".
  iDestruct (own_valid with "o") as "%val". iPureIntro.
  eapply ht_valid_QueryFound.
  apply val.
Qed.

Lemma ht_QueryFound_b γ j k v0 v g F E (su: F ⊆ E) :
  ⊢ 
    g ∗ (g &&{F}&&>
      (own γ (s j (Some (k, v0))) ∗ own γ (m k v))
    ) ={E}=∗ g ∗ ⌜ v = Some v0 ⌝.
Proof.
  iIntros "[g guards]".
  iMod (guards_persistent g _ (⌜v = Some v0⌝)%I E F with "[g guards]") as "[g res]".
  { trivial. }
  { iFrame "g". iFrame "guards". iApply ht_QueryFound. }
  iModIntro. iFrame.
Qed.
  
  (*
Definition Range γ k i j : iProp Σ :=
  ∃ a , ⌜ full a k i j ⌝ ∗ own γ a.
  *)
  
Lemma ht_QueryReachedEnd γ k v r :
    full r k (hash k) ht_fixed_size ->
    (own γ r -∗ own γ (m k v) -∗ ⌜ v = None ⌝).
Proof.
  intro f.
  iIntros "range l".
  iDestruct (own_op γ r (m k v) with "[range l]") as "l". { iFrame. }
  iDestruct (own_valid with "l") as "%t".
  iPureIntro.
  eapply ht_valid_QueryReachedEnd.
    - apply f.
    - trivial.
Qed.

Lemma ht_QueryReachedEnd_b γ r k v g F E (su: F ⊆ E) :
    full r k (hash k) ht_fixed_size ->
  ⊢
    g ∗ (g &&{F}&&>
      own γ r ∗ own γ (m k v)
    ) ={E}=∗ g ∗ ⌜ v = None ⌝.
Proof.
  intro f.
  iIntros "[g guards]".
  iMod (guards_persistent g _ (⌜v = None⌝)%I E F with "[g guards]") as "[g res]".
  { trivial. }
  { iFrame "g". iFrame "guards".
    iIntros "[a b]".
    iDestruct (ht_QueryReachedEnd with "a b") as "t"; trivial.
  }
  iModIntro. iFrame.
Qed.

Lemma ht_QueryNotFound γ r k v j :
  full r k (hash k) j ->
  own γ r ∗ own γ (s j None) ∗ own γ (m k v) -∗ ⌜ v = None ⌝.
Proof.
  intro f.
  iIntros "[range [c l]]".
  iDestruct (own_valid_3 with "range l c") as "%t".
  iPureIntro.
  apply ht_valid_QueryNotFound with (a := r) (k := k) (j := j); trivial.
Qed.

Lemma ht_QueryNotFound_b γ r k v j g F E (su: F ⊆ E) :
  full r k (hash k) j ->
  ⊢
    g ∗ (g &&{F}&&>
      own γ r ∗ own γ (s j None) ∗ own γ (m k v)
    ) ={E}=∗ g ∗ ⌜ v = None ⌝.
Proof.
  intro f.
  iIntros "[g guards]".
  iMod (guards_persistent g _ (⌜v = None⌝)%I E F with "[g guards]") as "[g res]".
  { trivial. }
  { iFrame "g". iFrame "guards". iApply ht_QueryNotFound. trivial. }
  iModIntro. iFrame.
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

Lemma ht_BorrowedRangeEmpty γ k i
  : ⊢ |==> ∃ r , ⌜ full r k i i ⌝ ∗ own γ r.
Proof.
  iIntros.
  iMod (own_unit htUR γ) as "u".
  iModIntro. iExists ε. iFrame.
  iPureIntro.
  apply full_trivial.
Qed.

Lemma ht_BorrowedRangeAppend γ r k i j k0 v0 g1 g2 F1 F2
    (ne: k0 ≠ k) (f: full r k i j) :
    (g1 &&{F1}&&> own γ r) ∗
    (g2 &&{F2}&&> own γ (s j (Some (k0, v0))))
    ⊢ ∃ r' , ⌜ full r' k i (j+1) ⌝ ∗
    (g1 ∗ g2 &&{F1 ∪ F2}&&> own γ r').
Proof.
  iIntros "[a b]".
  iExists (ht_dot r (s j (Some (k0, v0)))).
  iSplit.
  { iPureIntro. apply full_dot; trivial. }
  Print guards_and_sep_union.
  iApply (guards_and_sep_union g1 g2 (own γ r) (own γ (s j (Some (k0, v0))))).
  {
    
 
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
