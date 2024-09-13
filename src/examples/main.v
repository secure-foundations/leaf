From iris.base_logic.lib Require Import invariants.
From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From iris Require Import options.

Require Import guarding.guard.
Require Import guarding.lib.rwlock.

From lang Require Import lang simp adequacy primitive_laws.
From lang Require Import heap_ra.

From examples Require Import forever.
From examples Require Import hash_table.
From guarding Require Import guard_later.
From examples Require Import seqs.
From examples Require Import hash_table_logic.
From examples Require Import hash_table_raw.
From examples Require Import misc_tactics.

Definition main: lang.val :=
  λ: "unit" ,
    let: "ht" := new_hash_table #() in
    let: "insert_success" := update "ht" #0 #17 in
    Fork ( update "ht" #1 #12 ) ;;
    query "ht" #0
.

Section main_proof.

Context {Σ: gFunctors}.
Context `{@rwlock_logicG (option (Key * Value)) _ Σ}.
Context `{!simpGS Σ}.
Context {htl: ht_logicG Σ}.
Context {fl: forever_logicG Σ}.

(* note that our spec does not guarantee that update will succeed,
   so our spec for 'main' has to be that it either returns the value that was inserted,
   or nothing *)
Lemma wp_main :
  {{{ True }}} main #() {{{ v , RET v ; ⌜ v = (#true, #17)%V \/ v = (#false, #())%V ⌝ }}}.
Proof using H fl htl simpGS0 Σ.
  iIntros (Phi) "_ Phi". unfold main.
  wp_pures.
  wp_apply (wp_new_hash_table 2). { done. } iIntros (γ γrws ht) "[is_ht L]".
  rewrite mseq_append.
  rewrite mseq_append.
  iDestruct (own_op with "L") as "[L L1]".
  iDestruct (own_op with "L") as "[_ L0]".
  wp_pures.
  iDestruct (guards_refl ∅ (is_ht γ γrws ht)) as "g".
  wp_apply (wp_ht_update γ γrws ht 0 17 None (is_ht γ γrws ht)%I ∅ with "[is_ht L0]").
  { set_solver. }
  { iFrame. iFrame "g". }
  iIntros (b) "[is_ht ur]".
  wp_pures.
  
  iMod (make_forever _ _ with "is_ht") as "#gf_lat".
  iMod (extract_later (True)%I (is_ht γ γrws ht) ⊤ (↑FOREVER_NAMESPACE) with "[gf_lat]")
      as "[_ #gf]".
   { apply is_ht_extractable. }
   { set_solver. }
   { iFrame "gf_lat". }
  
  wp_apply (wp_fork with "[L1]").
  {
    iNext.
    wp_apply (wp_ht_update γ γrws ht 1 12 None (True)%I (↑FOREVER_NAMESPACE) with "[L1]").
    { apply ndot_ne_disjoint. intro. discriminate. }
    { iFrame. iFrame "gf". }
    iIntros. done.
  }
  wp_pures.
  iDestruct "ur" as "[[b0 L]|[b1 L]]".
  {
    iDestruct (guards_refl ⊤ (own γ (m 0 None))) as "gm".
    wp_apply (wp_ht_query _ _ _ _ _ (True)%I (own γ (m 0 None)) (↑FOREVER_NAMESPACE) with "[L]").
    { apply ndot_ne_disjoint. intro. discriminate. }
    { iFrame "gf". iFrame. iFrame "gm". }
    iIntros. iApply "Phi". iPureIntro. intuition.
  }
  {
    iDestruct (guards_refl ⊤ (own γ (m 0 _))) as "gm".
    wp_apply (wp_ht_query _ _ _ _ _ (True)%I (own γ (m 0 _)) (↑FOREVER_NAMESPACE) with "[L]").
    { apply ndot_ne_disjoint. intro. discriminate. }
    { iFrame "gf". iFrame. iFrame "gm". }
    iIntros. iApply "Phi". iPureIntro. intuition.
  }
Qed.

Lemma wp_main' :
  ⊢ WP main #() {{ v0, ⌜v0 = (#true, #17)%V ∨ v0 = (#false, #())%V⌝ }}.
Proof using H fl htl simpGS0 Σ.
  wp_apply wp_main. { done. } iIntros. iPureIntro. trivial.
Qed.

End main_proof.

(*** applying adequacy ***)

Definition mainΣ: gFunctors :=
  #[
      simpΣ;
      (*GFunctor (authUR (inved_protocolUR (protocol_mixin (RwLock S) (BaseOpt S) (rwlock_storage_mixin S))));*)
      @rwlock_logicΣ (option (Key * Value)) _;
      GFunctor htUR;
      forever_logicΣ
  ]. 

Lemma main_returns_value σ σ' v : 
  rtc erased_step ([ (main #())%E ], σ) ([Val v], σ') →
  v = (#true, #17)%V \/ v = (#false, #())%V.
Proof.
  intros Hstep.
  cut (adequate NotStuck (main #()) σ (λ v _, 
      v = (#true, #17)%V \/ v = (#false, #())%V)).
  { intros H. eapply adequate_alt in H as [Hval _]; eauto. }
  apply (simp_adequacy mainΣ).
  intros.
  (*Set Printing Implicit.
  Unset Printing Notations.*)
  apply (@wp_main' mainΣ).
  { apply subG_rwlock_logicΣ. apply _. }
  { apply subG_ht_logicΣ. apply _. }
  { apply subG_forever_logicΣ. apply _. }
Qed. 

(* Check that there are not any unproved assumptions.
   Should say 'Closed under global context'. *)
Print Assumptions main_returns_value.
