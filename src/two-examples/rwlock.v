From iris.base_logic.lib Require Import invariants.
From twolang Require Import lang simp adequacy primitive_laws.
From Two Require Import rwlock.
Require Import cpdt.CpdtTactics.

Require Import Two.guard.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import reduction.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import class_instances.
From iris.program_logic Require Import ectx_lifting.
From twolang Require Import notation tactics class_instances.
From twolang Require Import heap_ra.
From twolang Require Import lang.
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

Context {S: Type}.
Context {eqdec: EqDecision S}.

Context {Σ: gFunctors}.
Context `{@rwlock_logicG S _ Σ}.
Context `{!simpGS Σ}.

(* DON'T add an extra invGS, it will conflict with the one in simpGS Context `{!invGS Σ}.*)

Definition NS := nroot .@ "rwlock".

Definition rw_atomic_inv (γ: gname) (loc_exc loc_rc: loc) : iProp Σ :=
  (∃ exc rc (x: S) ,
          central γ exc rc x
          ∗ (loc_exc ↦ (LitV (LitInt (match exc with false => 0 | true => 1 end))))
          ∗ (loc_rc ↦ (LitV (LitInt rc)))
  ). 
     

Definition IsRwLock γ rwlock (storage_fn: S -> iProp Σ) : iProp Σ :=
    match rwlock with
     | PairV (LitV (LitInt loc_exc)) (LitV (LitInt loc_rc)) =>
        rw_lock_inst γ storage_fn ∗ rw_atomic_inv γ loc_exc loc_rc
     | _ => False
    end.
  
Global Instance rw_atomic_inv_timeless γ l1 l2 : Timeless (rw_atomic_inv γ l1 l2).
Proof. apply _. Qed.

Lemma rwlock_get_struct γ rwlock storage_fn
  : IsRwLock γ rwlock storage_fn -∗ ⌜
      ∃ exc_loc rw_loc , rwlock = 
          PairV (LitV (LitInt exc_loc)) (LitV (LitInt rw_loc))
  ⌝ .
Proof.
  iIntros "ir". unfold IsRwLock. destruct rwlock.
   { iExFalso. iFrame. }
   { iExFalso. iFrame. }
  - destruct rwlock1.
    + destruct l.
      * destruct rwlock2.
        -- destruct l.
          ++ iPureIntro. exists n. exists n0. trivial.
          ++ iExFalso. iFrame.
        -- iExFalso. iFrame.
        -- iExFalso. iFrame.
       * iExFalso. iFrame.
    + iExFalso. iFrame.
    + iExFalso. iFrame.
Qed.

Lemma guarded_rwlock_get_struct g E F γ rwlock storage_fn
  (su: F ⊆ E)
  : (g ∗ (g &&{F}&&> IsRwLock γ rwlock storage_fn) ={E}=∗ g ∗ ⌜
      ∃ exc_loc rw_loc , rwlock = 
          PairV (LitV (LitInt exc_loc)) (LitV (LitInt rw_loc))
  ⌝) .
Proof.
  iIntros "[g guards]".
  Print guards_persistent.
  iApply (guards_persistent g (IsRwLock γ rwlock storage_fn) _ E F); trivial.
  iFrame.
  iApply rwlock_get_struct.
Qed.

Lemma wp_new_rwlock (x: S) (storage_fn: S -> iProp Σ) :
  {{{ storage_fn x }}} new_rwlock
  {{{ rwlock γ , RET rwlock ; IsRwLock γ rwlock storage_fn }}}.
Proof.
  iIntros (Phi) "H Q".
  unfold new_rwlock.
  wp_alloc b_ref as "rb".
  wp_alloc a_ref as "ra".
  iMod (rw_new _ _ _ with "H") as (γ) "[H c]".
  wp_pures.
  iDestruct ("Q" $! (#a_ref, #b_ref)%V γ) as "Q".
  iApply "Q".
  iModIntro. unfold IsRwLock. unfold rw_atomic_inv.
  iFrame. iExists false, 0, x. iFrame.
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

Lemma acq1 γ (rwlock: lang.val) (g: iProp Σ) storage_fn E
    (not_in_e: γ ∉ E) :
      {{{ g ∗ □ (g &&{E}&&> IsRwLock γ rwlock storage_fn) }}}
      loop_until (CAS (Fst rwlock) #0 #1)
      {{{ RET #(); exc_pending γ ∗
          g ∗ □ (g &&{E}&&> IsRwLock γ rwlock storage_fn)
      }}}.
Proof.
  iIntros (phi) "g x".
  wp_apply (loop_w_invariant _
    (g ∗ □ (g &&{E}&&> IsRwLock γ rwlock storage_fn))%I
    (g ∗ □ (g &&{E}&&> IsRwLock γ rwlock storage_fn))%I
    (exc_pending γ ∗ g ∗ □ (g &&{E}&&> IsRwLock γ rwlock storage_fn))
    with "g"
  ).
  - iIntros (phi2) "[g #guard] t".
      iMod (guarded_rwlock_get_struct g ⊤ E with "[g guard]") as "[g %rwlock_form]".
      { set_solver. } { iFrame "g". iFrame "guard". }
      destruct rwlock_form as [exc_loc [rw_loc rwlock_form]]. subst rwlock.
  
      wp_pures.
      
      iMod (guards_open g (IsRwLock γ (#exc_loc, #rw_loc) storage_fn) ⊤ E with "[g guard]")
        as "[irl irl_back]".
      { set_solver. } { iFrame "g". iFrame "guard". }
      
      unfold IsRwLock at 4.
      unfold IsRwLock at 4.
      unfold rw_lock_inst, rw_atomic_inv.
      iDestruct "irl" as "[#maps ex]".
      iDestruct "ex" as (exc rc x) "[c [mem_exc mem_rc]]".
      
      destruct exc.
       -- (* exc=true case, CAS fail *)
            wp_apply (wp_cas_ne with "mem_exc"). { crush. }
            iIntros "mem_exc".
            iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
            { iFrame "maps". iExists true, rc, x. iFrame. }
            iModIntro. iApply "t".
            iSplitL "g".
            { iIntros "%". iFrame "g". iFrame "guard". }
            iSplitL.
            { iIntros "%". exfalso. crush. }
            { iPureIntro. lia. }
       -- (* exc=false case, CAS success *)
            wp_apply (wp_cas_eq with "mem_exc").
            iMod (rw_exc_begin with "maps c") as "[c pend]". { set_solver. }
            
            iIntros "mem_exc".
            iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
            { iFrame "maps". iExists true, rc, x. iFrame. }
            iModIntro. iApply "t".
            iSplitL "".
            { iIntros "%". exfalso. crush. }
            iSplitL.
            { iIntros "%". iFrame "pend". iFrame "guard". iFrame "g". }
            { iPureIntro. lia. }
  - intros. trivial.
  - iIntros. iFrame.
  - iFrame.
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
