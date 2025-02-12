From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export base_logic.
From stdpp Require Import gmap.

From iris.algebra Require Export gmap.

Require Import examples.hash_table_raw.
Require Import iris.base_logic.lib.own.
Require Import guarding.guard.
Require Import guarding.own_and.

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
      #[global] ht_logic_inG :: inG Σ htUR
    }.

Definition ht_logicΣ : gFunctors := #[ GFunctor htUR ].

Global Instance subG_ht_logicΣ {Σ} : subG ht_logicΣ Σ → ht_logicG Σ.
Proof. solve_inG. Qed.

Section HashTableLogic.

Context {Σ: gFunctors}.
Context {htl: ht_logicG Σ}.
Context `{!invGS_gen hlc Σ}.

Lemma ht_Init (n: nat) :
  ⊢ |==> (∃ γ , own γ (mseq n) ∗ own γ (sseq ht_fixed_size))%I.
Proof.
  iIntros.
  iMod (own_alloc ((mseq n) ⋅ (sseq ht_fixed_size))) as (γ) "x".
  { apply valid_mseq_sseq. }
  iModIntro. iExists γ. iDestruct (own_op with "x") as "[x y]". iFrame.
Qed.

(* QueryFound *)

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
  iMod (guards_extract_persistent g _ (⌜v = Some v0⌝)%I E F with "[g guards]") as "[g res]".
  { trivial. }
  { iFrame "g". iFrame "guards". iApply ht_QueryFound. }
  iModIntro. iFrame.
Qed.
  
  (*
Definition Range γ k i j : iProp Σ :=
  ∃ a , ⌜ full a k i j ⌝ ∗ own γ a.
  *)

(* QueryNotFound *)
  
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
  iMod (guards_extract_persistent g _ (⌜v = None⌝)%I E F with "[g guards]") as "[g res]".
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
  iMod (guards_extract_persistent g _ (⌜v = None⌝)%I E F with "[g guards]") as "[g res]".
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

Lemma le_iff_ht_le a b
  : (a ≼ b) <-> (ht_le a b).
Proof.
  unfold "≼". unfold ht_le.
  unfold "⋅", ht_op. intuition.
  - destruct H as [z H]. exists z. rewrite H. trivial.
  - destruct H as [z H]. exists z. rewrite H. trivial.
Qed.

(* The rules listed under 'Addendum' in the paper aren't named lemmas here,
   but they are internal proof goals in the below proofs, proved by `and_own2_ucmra`
   (which the paper calls PCM-And)
*)

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
  iApply (guards_and_own_sep_union g1 g2 (own γ r) (own γ (s j (Some (k0, v0))))).
  {
    apply (@and_own_discrete_ucmra_specific Σ). { apply ht_cmra_discrete. }
    intro w.
    repeat (rewrite le_iff_ht_le).
    apply (full_add r k i j (Some (k0, v0))); trivial.
  }
  iFrame.
Qed.

Lemma ht_BorrowedRangeAddM γ r k i j k1 v1 g1 g2 F1 F2
    (f: full r k i j) :
    (g1 &&{F1}&&> own γ r) -∗
    (g2 &&{F2}&&> own γ (m k1 v1))
    -∗
    (g1 ∗ g2 &&{F1 ∪ F2}&&> (own γ r ∗ own γ (m k1 v1))).
Proof.
  iIntros "a b".
  rewrite <- own_op.
  iApply (guards_and_own_sep_union g1 g2 (own γ r) (own γ (m k1 v1))).
  {
    apply (@and_own_discrete_ucmra_specific Σ). { apply ht_cmra_discrete. }
    intro w.
    repeat (rewrite le_iff_ht_le).
    apply (range_add_m r k i j k1 v1); trivial.
  }
  iFrame.
Qed.

Lemma ht_SAddM γ i slot k1 v1 g1 g2 F1 F2 :
    (g1 &&{F1}&&> own γ (s i slot)) -∗
    (g2 &&{F2}&&> own γ (m k1 v1))
    -∗
    (g1 ∗ g2 &&{F1 ∪ F2}&&> (own γ (s i slot) ∗ own γ (m k1 v1))).
Proof.
  iIntros "a b".
  rewrite <- own_op.
  iApply (guards_and_own_sep_union g1 g2 (own γ (s i slot)) (own γ (m k1 v1))).
  {
    apply (@and_own_discrete_ucmra_specific Σ). { apply ht_cmra_discrete. }
    intro w.
    repeat (rewrite le_iff_ht_le).
    apply (s_add_m i slot k1 v1); trivial.
  }
  iFrame.
Qed.

Lemma ht_RangeAddSAddM γ r k i j slot k1 v1 g1 g2 g3 F1 F2 F3
    (f: full r k i j) :
    (g1 &&{F1}&&> own γ r) -∗
    (g2 &&{F2}&&> own γ (s j slot)) -∗
    (g3 &&{F3}&&> own γ (m k1 v1))
    -∗
    (g1 ∗ g2 ∗ g3 &&{F1 ∪ F2 ∪ F3}&&> (own γ r ∗ own γ (s j slot) ∗ own γ (m k1 v1))).
Proof.
  iIntros "a b c".
  iDestruct (ht_SAddM with "b c") as "d".
  rewrite <- own_op.
  rewrite <- own_op.
  replace (F1 ∪ F2 ∪ F3) with (F1 ∪ (F2 ∪ F3)) by set_solver.
  iApply (guards_and_own_sep_union g1 (g2 ∗ g3)%I (own γ r) (own γ (s j slot ⋅ m k1 v1))).
  {
    apply (@and_own_discrete_ucmra_specific Σ). { apply ht_cmra_discrete. }
    intro w.
    repeat (rewrite le_iff_ht_le).
    apply (full_add_s_m r k i j slot k1 v1); trivial.
    (*replace (s j slot ⋅ m k1 v1) with (ht_dot (s j slot) (m k1 v1)) by trivial.
    replace (s j slot ⋅ m k1 v1) with (ht_dot (s j slot) (m k1 v1)) by trivial. *)
  } 
  iFrame.
Qed.

(* UpdateExisting *)

Lemma ht_UpdateExisting γ k v v0 v1 j :
  own γ (s j (Some (k, v1))) -∗ own γ (m k v0) ==∗
  own γ (s j (Some (k, v))) ∗ own γ (m k (Some v)).
Proof.
  rewrite <- own_op.
  apply own_update_2.
  rewrite cmra_discrete_total_update.
  unfold "⋅", cmra_op, htR, ht_op.
  intros.
  have X := ht_update_existing j k v v0 v1.
  unfold ht_mov in X.
  apply X. trivial.
Qed.

(* UpdateInsert *)

Lemma ht_UpdateNew γ k v j v0 r
  (f: full r k (hash k) j) :
  own γ (s j None) -∗ own γ (m k v0) -∗ own γ r ==∗
  own γ (s j (Some (k, v))) ∗ own γ (m k (Some v)) ∗ own γ r.
Proof.
  rewrite <- own_op.
  rewrite <- own_op.
  apply own_update_3.
  rewrite cmra_discrete_total_update.
  unfold "⋅", cmra_op, htR, ht_op.
  intros.
  have X := ht_update_new j k v v0 r.
  unfold ht_mov in X.
  rewrite ht_dot_assoc.
  apply X; trivial.
Qed.

End HashTableLogic.
