From iris.base_logic.lib Require Import invariants.
From twolang Require Import lang simp adequacy primitive_laws.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From iris Require Import options.

From TwoExamples Require Import rwlock.
From Two Require Import rwlock.
From TwoExamples Require Import hash_table.
From Two Require Import guard_later.
Require Import Two.guard.
From TwoExamples Require Import seqs.
From TwoExamples Require Import hash_table_logic.
From TwoExamples Require Import hash_table_raw.
From twolang Require Import heap_ra.
From TwoExamples Require Import misc_tactics.

Require Import coq_tricks.Deex.
Require Import cpdt.CpdtTactics.

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

(* note that our spec does not guarantee that update will succeed,
   so our spec for 'main' has to be that it either returns the value that was inserted,
   or nothing *)
Lemma wp_main :
  {{{ True }}} main #() {{{ v , RET v ; ⌜ v = (#true, #17)%V \/ v = (#false, #())%V ⌝ }}}.
Proof using HasRef0 simpGS0 Σ 𝜇.
  iIntros (Phi) "_ Phi". unfold main.
  wp_pures.
  wp_apply (wp_new_hash_table 2). { done. } iIntros (𝛾 ht) "[#is_ht L]".
  rewrite mseq_append.
  rewrite mseq_append.
  iDestruct (L_op with "L") as "[L L1]".
  iDestruct (L_op with "L") as "[_ L0]".
  wp_pures.
  wp_apply (wp_ht_update 𝛾 ht 0 17 None with "[is_ht L0]").
    { iFrame. iFrame "#". }
  iIntros (b) "x".
  wp_pures.
  wp_apply (wp_fork with "[L1]").
  {
    iNext.
    wp_apply (wp_ht_update 𝛾 ht 1 12 None with "[is_ht L1]").
    { iFrame. iFrame "#". }
    iIntros. done.
  }
  wp_pures.
  iDestruct "x" as "[[b0 L]|[b1 L]]".
  {
    wp_apply (wp_ht_query with "[is_ht L]"). { iFrame. iFrame "#". }
    iIntros. iApply "Phi". iPureIntro. intuition.
  }
  {
    wp_apply (wp_ht_query with "[is_ht L]"). { iFrame. iFrame "#". }
    iIntros. iApply "Phi". iPureIntro. intuition.
  }
Qed.

Lemma wp_main' :
  ⊢ WP main #() {{ v0, ⌜v0 = (#true, #17)%V ∨ v0 = (#false, #())%V⌝ }}.
Proof using HasRef0 simpGS0 Σ 𝜇.
  wp_apply wp_main. { done. } iIntros. iPureIntro. trivial.
Qed.

End main_proof.

(*** applying adequacy ***)

Definition 𝜇1 := (
      NewTPCMCtx (
        NewTPCMCtx
          (SingleTPCMCtx HT)
          (RwLock (HT * (HeapT loc lang.val)))
      )
      (AuthFrag (gmap loc (option lang.val)))
    ).
Definition main𝜇 := 
  NewRefCtx
    𝜇1
    (RwLock (HT * (HeapT loc lang.val)))
    (HT * (HeapT loc lang.val))
    (rwlock_ref (HT * (HeapT loc lang.val))).

Instance 𝜇1_has_tpcm_ht : HasTPCM 𝜇1 HT. typeclasses eauto. Defined.
Instance 𝜇1_has_tpcm_rw : HasTPCM 𝜇1 (RwLock (HT * (HeapT loc lang.val))).
    typeclasses eauto. Defined.
Instance 𝜇1_has_tpcm_heap : HasTPCM 𝜇1 (HeapT loc lang.val).
    typeclasses eauto. Defined.

Instance main𝜇_has_tpcm_ht : HasTPCM main𝜇 HT. typeclasses eauto. Defined.
Instance main𝜇_has_tpcm_rw : HasTPCM main𝜇 (RwLock (HT * (HeapT loc lang.val))).
    typeclasses eauto. Defined.
Instance main𝜇_has_tpcm_heap : HasTPCM main𝜇 (HeapT loc lang.val).
    typeclasses eauto. Defined.

Instance main𝜇_has_ref : HasRef main𝜇
      (NewRef_KeepsTPCM 𝜇1 _ _ _ (rwlock_ref (HT * HeapT loc lang.val)))
      (NewRef_KeepsTPCM 𝜇1 _ _ _ (rwlock_ref (HT * HeapT loc lang.val)))
    (rwlock_ref (HT * HeapT loc lang.val)).
    typeclasses eauto. Defined.

(* type class inference has a standard embedding of M * N in the lifted 𝜇
   which is different from the lifted embedding of M * N in 𝜇. 
   Here we show those are equivalent ...
   TODO fix the type class inference so we get this for free *)
Global Instance product_fixer (𝜇: BurrowCtx)
      R `{!EqDecision R} `{TPCM R}
      M `{!EqDecision M} `{TPCM M}
      N `{!EqDecision N} `{TPCM N}
    `{!HasTPCM 𝜇 R} `{!HasTPCM 𝜇 M} `{!HasTPCM 𝜇 N}
    (rf: Refinement R (M * N))
    (hr: HasRef (NewRefCtx 𝜇 R (M * N) rf)
      (NewRef_KeepsTPCM 𝜇 _ _ _ rf)
      (NewRef_KeepsTPCM 𝜇 _ _ _ rf)
      rf)
  : HasRef (NewRefCtx 𝜇 R (M * N) rf)
      (NewRef_KeepsTPCM 𝜇 _ _ _ rf)
      (@product_hastpcm (NewRefCtx 𝜇 R (M * N) rf) M N _ _ _ _ _ _
        (NewRef_KeepsTPCM 𝜇 _ _ _ rf)
        (NewRef_KeepsTPCM 𝜇 _ _ _ rf)
      ) rf.
Proof.
  refine ({|
    hasref_ri := ((@hasref_ri (NewRefCtx 𝜇 R (M * N) rf) R (M * N) _ _ _ _ _ _ rf hr) : bc_small_RI (NewRefCtx 𝜇 R (M * N) rf));
  |}).
  - destruct hr. trivial.
Qed.

Instance main𝜇_has_ref' : HasRef main𝜇 _ (@product_hastpcm _ _ _ _ _ _ _ _ _ _ _)
    (rwlock_ref (HT * HeapT loc lang.val)).
Proof.
  apply product_fixer.
  - typeclasses eauto.
  - typeclasses eauto.
  - typeclasses eauto.
  - apply main𝜇_has_ref.
Qed.

Definition mainΣ: gFunctors :=
  #[simpΣ main𝜇]. 

Lemma main_returns_value σ σ' v : 
  rtc erased_step ([ (main #())%E ], σ) ([Val v], σ') →
  v = (#true, #17)%V \/ v = (#false, #())%V.
Proof.
  intros Hstep.
  cut (adequate NotStuck (main #()) σ (λ v _, 
      v = (#true, #17)%V \/ v = (#false, #())%V)).
  { intros H. eapply adequate_alt in H as [Hval _]; eauto. }
  apply (@simp_adequacy mainΣ main𝜇 main𝜇_has_tpcm_heap).
  { typeclasses eauto. }
  intros. apply wp_main'.
Qed.

(* Check that there are not any unproved assumptions.
   Should say 'Closed under global context'. *)
Print Assumptions main_returns_value.
