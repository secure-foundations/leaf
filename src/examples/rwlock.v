From iris.base_logic.lib Require Import invariants.
From BurrowLang Require Import lang simp adequacy primitive_laws.
From Tpcms Require Import rwlock.
Require Import Burrow.tpcms.
Require Import Burrow.ra.
Require Import Burrow.rollup.
Require Import cpdt.CpdtTactics.
Require Import Burrow.tactics.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From BurrowLang Require Import notation tactics class_instances.
From BurrowLang Require Import heap_ra.
From BurrowLang Require Import lang.
From iris Require Import options.

Definition loop_until e : lang.expr :=
    (rec: "loop" "c" :=
      if: e then #()
      else "loop" "c") #0.

Definition new_rwlock : lang.expr :=
  Pair (ref #0) (ref #0).

Definition acquire_exc : lang.val :=
  λ: "rw" ,
    loop_until (CAS (Fst "rw") #0 #1) ;;
    loop_until (op_eq (!(Snd "rw")) #0).

Definition release_exc : lang.val :=
  λ: "rw" ,
    Fst "rw" <- #0.
    
Definition acquire_shared : lang.val :=
  λ: "rw" ,
    loop_until (
      FAA (Snd "rw") #1 ;;
      if: op_eq (!(Fst "rw")) #0 then
        #1
      else (
        FAA (Snd "rw") (#(-1)) ;;
        #0
      )
    ).
    
Definition release_shared : lang.val :=
  λ: "rw" ,
    FAA (Snd "rw") (#(-1)).
    

Section RwlockProof.

Context {𝜇: BurrowCtx}.

Context {M} `{!EqDecision M} `{!TPCM M}.
Context `{m_hastpcm: !HasTPCM 𝜇 M}.
Context `{rw_hastpcm: !HasTPCM 𝜇 (RwLock M)}.
Context `{!HasRef 𝜇 rw_hastpcm m_hastpcm (rwlock_ref M)}.

Context `{!simpGS 𝜇 Σ}.

Definition NS := nroot .@ "rwlock".

Definition rwlock_inv 𝛼 𝛾 (contents_inv: M -> Prop) l1 l2 : iProp Σ :=
  (∃ exc rc x ,
    L (rwloc 𝛼 𝛾) (Central exc rc x)
    ∗ ⌜ contents_inv x ⌝
    ∗ (l1 ↦ (LitV (LitInt (match exc with false => 0 | true => 1 end))))
    ∗ (l2 ↦ (LitV (LitInt rc)))
  ).

  
Global Instance rwlock_inv_timeless 𝛼 𝛾 contents_inv l1 l2 : Timeless (rwlock_inv 𝛼 𝛾 contents_inv l1 l2).
Proof. apply _. Qed.

Definition is_rwlock rwlock 𝛼 𝛾 (contents_inv: M -> Prop) : iProp Σ :=
  match rwlock with
    | PairV (LitV (LitInt l1)) (LitV (LitInt l2)) =>
        inv NS (rwlock_inv 𝛼 𝛾 contents_inv l1 l2)
    | _ => False
  end.
  
Lemma rwlock_get_struct rw 𝛼 𝛾 ci
  : is_rwlock rw 𝛼 𝛾 ci -∗ ⌜
    match rw with
    | PairV (LitV (LitInt l1)) (LitV (LitInt l2)) => True
    | _ => False
    end
  ⌝ .
Proof.
  iIntros "ir". unfold is_rwlock. destruct rw; try iFrame.
  destruct rw1, rw2; try iFrame.
  - destruct l, l0; try iFrame. done.
  - destruct l; try iFrame.
  - destruct l; try iFrame.
Qed.
    
  
Global Instance is_rwlock_persistent rwlock 𝛼 𝛾 contents_inv : Persistent (is_rwlock rwlock 𝛼 𝛾 contents_inv).
Proof. unfold is_rwlock. destruct rwlock; try (apply _).
  destruct rwlock1; try (apply _).
  destruct l; try (apply _).
  destruct rwlock2; try (apply _).
  destruct l; try (apply _).
Qed.

Lemma wp_new_rwlock (𝛾: BurrowLoc 𝜇) (x: M) (contents_inv: M -> Prop)
    (sat_inv: contents_inv x) :
  {{{ L 𝛾 x }}} new_rwlock
  {{{ rwlock 𝛼 , RET rwlock ; is_rwlock rwlock 𝛼 𝛾 contents_inv }}}.
Proof.
  iIntros (Phi) "H Q".
  unfold new_rwlock.
  wp_alloc b_ref as "rb".
  wp_alloc a_ref as "ra".
  iMod (rw_new _ _ with "H") as (𝛼) "H".
  iAssert (rwlock_inv 𝛼 𝛾 contents_inv a_ref b_ref) with "[rb ra H]" as "ri".
  - unfold rwlock_inv. iExists false. iExists 0. iExists x. iFrame. iPureIntro. trivial.
  - iMod (inv_alloc NS _ _ with "ri") as "i".
    wp_pures.
    iApply "Q".
    iModIntro.
    iFrame.
Qed.

Lemma loop_w_invariant e (P Q R : iProp Σ)
  (hr: {{{ Q }}} e {{{ n, RET #n ; (⌜n=0⌝ -∗ Q) ∗ (⌜n=1⌝ -∗ R) ∗ (⌜n=0 \/ n=1⌝) }}})
  (eokay: (∀ X Y , subst "c" Y (subst "loop" X e) = e))
  (entry: P ⊢ Q)
  : {{{ P }}} loop_until e {{{ RET #(); R }}}.
Proof.
  iIntros (phi) "p x".
  iDestruct (entry with "p") as "q".
  unfold loop_until.
  wp_pures.
  iLöb as "IH".
  rewrite eokay.
  wp_apply (hr with "q").
  iIntros "%n [w [v u]]".
  have h : Decision (n=0) by solve_decision. destruct h.
  - subst n.
    wp_pures. rewrite eokay. 
    iApply ("IH" with "x").
    iApply "w".
    iPureIntro. trivial.
  - have h : Decision (n=1) by solve_decision. destruct h.
     + subst n. wp_pures. iModIntro. iApply "x". iApply "v". iPureIntro. trivial.
     + iDestruct "u" as "%u". lia.
Qed.

Lemma acq1 (rwlock: lang.val) 𝛼 𝛾 contents_inv :
      {{{ is_rwlock rwlock 𝛼 𝛾 contents_inv }}}
      loop_until (CAS (Fst rwlock) #0 #1)
      {{{ RET #(); L (rwloc 𝛼 𝛾) ExcPending }}}.
Proof.
  iIntros (phi) "#isr p".
  wp_apply (loop_w_invariant _ (is_rwlock rwlock 𝛼 𝛾 contents_inv)%I (is_rwlock rwlock 𝛼 𝛾 contents_inv)%I (L (rwloc 𝛼 𝛾) ExcPending ∗ is_rwlock rwlock 𝛼 𝛾 contents_inv)%I).
  - iIntros (phi2) "#t p".
      iDestruct (rwlock_get_struct with "t") as "%".
        destruct rwlock; try contradiction.
        destruct rwlock1; try contradiction.
        destruct l; try contradiction.
        destruct rwlock2; try contradiction.
        destruct l; try contradiction.
        * wp_pures. iInv "t" as (exc rc) ">I".
              iDestruct "I" as (x) "I".
              iDestruct "I" as "[L [c [a b]]]".
            unfold rwlock_inv.
            wp_apply (wp_cas with "a").
            destruct exc.
              -- case_decide.
                ++ exfalso. inversion H0.
                ++ iIntros "n1". iModIntro. iSplitR "p".
                  ** iModIntro. iExists true, rc, x. iFrame.
                  ** simpl. iApply ("p" $! 0). iSplit.
                    --- iIntros. iFrame "#".
                    --- iSplit.
                      +++ iIntros "%". inversion H1.
                      +++ iPureIntro. lia.
              -- case_decide.
                ++ iIntros "n1".
                  iMod (rw_exc_begin with "L") as "[L pend]". iModIntro. iSplitR "p pend".
                   ** iModIntro. iExists true, rc, x. iFrame.
                   ** simpl. iApply ("p" $! 1). iSplit.
                    --- iIntros "%". inversion H1.
                    --- iSplitL "pend".
                      +++ iIntros. iFrame "#". iFrame.
                      +++ iPureIntro. lia.
                ++ contradiction.
    - intros. trivial.
    - iIntros. iFrame "#".
    - iFrame "#".
    - iIntros "[x y]". iApply "p". iFrame.
Qed.

Lemma acq2 (rwlock: lang.val) (𝛼: nat) 𝛾 contents_inv :
      {{{ is_rwlock rwlock 𝛼 𝛾 contents_inv ∗ L (rwloc 𝛼 𝛾) ExcPending }}}
      loop_until (op_eq (!(Snd rwlock)) #0)
      {{{ x, RET #(); L (rwloc 𝛼 𝛾) ExcGuard ∗ L 𝛾 x ∗ ⌜ contents_inv x ⌝ }}}.
Proof.
  iIntros (phi) "[#isr ep] p".
  wp_apply (loop_w_invariant _
    (is_rwlock rwlock 𝛼 𝛾 contents_inv ∗ L (rwloc 𝛼 𝛾) ExcPending)%I
    (is_rwlock rwlock 𝛼 𝛾 contents_inv ∗ L (rwloc 𝛼 𝛾) ExcPending)%I
    (∃ x, L (rwloc 𝛼 𝛾) ExcGuard ∗ L 𝛾 x ∗ ⌜ contents_inv x ⌝)%I
    with "[ep]"
    ).
  - iIntros (phi2) "[#t ep] p".
      iDestruct (rwlock_get_struct with "t") as "%".
        destruct rwlock; try contradiction.
        destruct rwlock1; try contradiction.
        destruct l; try contradiction.
        destruct rwlock2; try contradiction.
        destruct l; try contradiction.
        * unfold op_eq. wp_pures.
          wp_bind (HeapOp LoadOp _ _ _).
          iInv "t" as (exc rc) ">I".
              iDestruct "I" as (x) "I".
              iDestruct "I" as "[L [%c [a b]]]".
            wp_load.
            have h : Decision (rc = 0) by solve_decision. destruct h.
            -- subst rc.
              iMod (rw_exc_acquire with "L ep") as "[L [eg x]]".
              iModIntro.
              iSplitL "L a b".
              ++ iModIntro. unfold rwlock_inv. iExists  exc, 0, x. iFrame. iPureIntro. trivial.
              ++ wp_pures. iModIntro. iApply "p". 
                iSplitR.
                ** iIntros "%". inversion H0.
                ** iSplitL.
                 --- iIntros. iExists x. iFrame. iPureIntro. trivial.
                 --- iPureIntro. lia.
            -- iModIntro.
              iSplitL "L a b".
              ++ iModIntro. unfold rwlock_inv. iExists  exc, rc, x. iFrame. iPureIntro. trivial.
              ++ wp_pures. assert (bool_decide (#rc = #0) = false).
                ** unfold bool_decide. case_decide; trivial. inversion H0. contradiction.
                ** rewrite H0.
                  iModIntro. iApply ("p" $! 0).
                  iSplitL.
                  --- iIntros. iFrame. iFrame "#".
                  --- iSplit.
                    +++ iIntros "%". lia.
                    +++ iPureIntro. lia.
    - intros. trivial.
    - iIntros. iFrame "#". iFrame.
    - iFrame "#". iFrame.
    - iIntros "T". iDestruct "T" as (x) "T".
      iApply ("p" $! x). iFrame.
Qed.

Lemma wp_acquire_exc (rwlock: lang.val) 𝛼 𝛾 contents_inv :
      {{{ is_rwlock rwlock 𝛼 𝛾 contents_inv }}}
      acquire_exc rwlock
      {{{ x, RET #(); L (rwloc 𝛼 𝛾) ExcGuard ∗ L 𝛾 x ∗ ⌜ contents_inv x ⌝ }}}.
Proof.
  unfold acquire_exc.
  iIntros (p) "#isr P".
  wp_pure _.
  have j := acq1 rwlock 𝛼 𝛾 contents_inv. unfold loop_until in j.
  wp_bind ((rec: "loop" "c" := if: CAS (Fst rwlock) #0 #1 then #() else "loop" "c")%E #0).
  full_generalize ((rec: "loop" "c" := if: CAS (Fst rwlock) #0 #1 then #() else "loop" "c")%E #0) as e.
  wp_apply (j with "isr").
  iIntros "m".
  have k := acq2 rwlock 𝛼 𝛾 contents_inv. unfold loop_until in k. unfold op_eq in k.
  wp_seq.
  full_generalize ((rec: "loop" "c" := if: BinOp EqOp ! (Snd rwlock) #0 then #() else "loop" "c")%E #0) as e2.
  wp_apply (k with "[m]").
  - iFrame. iFrame "#".
  - iFrame.
Qed.

Lemma wp_release_exc (rwlock: lang.val) 𝛼 𝛾 contents_inv x :
      {{{ is_rwlock rwlock 𝛼 𝛾 contents_inv ∗
           L (rwloc 𝛼 𝛾) ExcGuard ∗ L 𝛾 x ∗ ⌜ contents_inv x ⌝ }}}
      release_exc rwlock
      {{{ RET #(); True }}}.
Proof.
  unfold release_exc.
  iIntros (P) "[#eg [c [l %ci1]]] P".
  iDestruct (rwlock_get_struct with "eg") as "%".
    destruct rwlock; try contradiction.
    destruct rwlock1; try contradiction.
    destruct l; try contradiction.
    destruct rwlock2; try contradiction.
    destruct l; try contradiction.
  wp_pures.
  unfold is_rwlock.
  iInv "eg" as (exc rc) ">I".
  iDestruct "I" as (x0) "[ck [%ci [le lr]]]".
  wp_store.
  iMod (rw_exc_release with "ck c l") as "ck".
  iModIntro.
  iSplitL "lr le ck".
  - iModIntro. unfold rwlock_inv. iExists false, rc, x. iFrame. iPureIntro. trivial.
  - iApply "P". done.
Qed.
  
Lemma wp_release_shared (rwlock: lang.val) 𝛼 𝛾 contents_inv x :
      {{{ is_rwlock rwlock 𝛼 𝛾 contents_inv ∗
           L (rwloc 𝛼 𝛾) (ShGuard x) }}}
      release_shared rwlock
      {{{ dummy, RET dummy; True }}}.
Proof.
  unfold release_shared.
  iIntros (P) "[#eg l] P".
  iDestruct (rwlock_get_struct with "eg") as "%".
    destruct rwlock; try contradiction.
    destruct rwlock1; try contradiction.
    destruct l; try contradiction.
    destruct rwlock2; try contradiction.
    destruct l; try contradiction.
  wp_pures.
  unfold is_rwlock.
  iInv "eg" as (exc rc) ">I".
  iDestruct "I" as (x0) "[ck [%ci [le lr]]]".
  wp_apply (wp_faa with "lr").
  iMod (rw_shared_release with "ck l") as "ck".
  iIntros "lr".
  iModIntro.
  iSplitL "lr le ck".
  - iModIntro. unfold rwlock_inv. iExists exc, (rc-1), x0. iFrame. iPureIntro. trivial.
  - iApply "P". done.
Qed.

Lemma wp_acquire_shared (rwlock: lang.val) 𝛼 𝛾 contents_inv :
      {{{ is_rwlock rwlock 𝛼 𝛾 contents_inv }}}
      acquire_shared rwlock
      {{{ x, RET #(); L (rwloc 𝛼 𝛾) (ShGuard x) ∗ ⌜ contents_inv x ⌝ }}}.
Proof.
  iIntros (phi) "#eg x".
  unfold acquire_shared.
  wp_pure _.
  
  iDestruct (rwlock_get_struct with "eg") as "%".
    destruct rwlock; try contradiction.
    destruct rwlock1; try contradiction.
    destruct l; try contradiction.
    destruct rwlock2; try contradiction.
    destruct l; try contradiction.
    
  wp_pures.
  iLöb as "IH".
  wp_pures.
  
  wp_pures.
  
  wp_bind (FAA #n0 #1).
  unfold is_rwlock.  iInv "eg" as ">I". iDestruct "I" as (exc rc x) "[L [%ci [le lr]]]".
  wp_apply (wp_faa with "lr"). iIntros "lr". 
  iMod (rw_shared_begin with "L") as "[L pend]".
  iModIntro. iSplitL "L le lr".
  {
    iModIntro. unfold rwlock_inv. iExists exc, (rc + 1), x. iFrame. iPureIntro. trivial.
  }
  wp_pures.
  
  wp_bind (! #n)%E.
  clear exc. clear rc. clear ci. clear x.
  iInv "eg" as ">I". iDestruct "I" as (exc rc x) "[L [%ci [le lr]]]".
  wp_load.
  destruct exc.
  
  (* exc = 1 case *)
  - iModIntro. iSplitL "L le lr".
    {
      iModIntro. unfold rwlock_inv. iExists true, rc, x. iFrame. iPureIntro. trivial.
    }
    wp_pures.
    
    wp_bind (FAA #n0 #(-1)).
    clear rc. clear ci. clear x.
    iInv "eg" as ">I". iDestruct "I" as (exc rc x) "[L [%ci [le lr]]]".
    wp_apply (wp_faa with "lr"). iIntros "lr". 
    iMod (rw_shared_retry with "L pend") as "L".
    iModIntro. iSplitL "L le lr".
    {
      iModIntro. unfold rwlock_inv. iExists exc, (rc - 1), x. iFrame. iPureIntro. trivial.
    }
    wp_pures.
    iApply ("IH" with "x").
  
  (* exc = 0 case *)
  - iMod (rw_shared_acquire with "L pend") as "[L guard]".
    iModIntro.
    iSplitL "L le lr".
    {
      iModIntro. unfold rwlock_inv. iExists false, rc, x. iFrame. iPureIntro. trivial.
    }
    wp_pures.
    iApply ("x" $! x).
    iModIntro. iFrame. iPureIntro. trivial.
Qed.

End RwlockProof.
