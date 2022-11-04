From iris.base_logic.lib Require Import invariants.
From lang Require Import lang simp adequacy primitive_laws.
From examples Require Import rwlock_logic.
Require Import cpdt.CpdtTactics.

Require Import guarding.guard.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import reduction.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import class_instances.
From iris.program_logic Require Import ectx_lifting.
From lang Require Import notation tactics class_instances.
From lang Require Import heap_ra.
From lang Require Import lang.
From iris Require Import options.

Require Import guarding.guard_later.
Require Import examples.misc_tactics.

Definition loop_until e : lang.expr :=
    (rec: "loop" "c" :=
      if: e then #()
      else "loop" "c") #0.

Definition new_rwlock : lang.expr :=
  Pair (ref #0) (ref #0).
  
Definition free_rwlock : lang.expr :=
  λ: "rw" ,
    Free (Fst "rw") ;;
    Free (Snd "rw").

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

(*Definition NS := nroot .@ "rwlock".*)

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

Global Instance is_rwlock_extractable γ rwlock storage_fn
    : LaterGuardExtractable (IsRwLock γ rwlock storage_fn).
Proof. 
  unfold IsRwLock.
  destruct rwlock; try typeclasses eauto.
  destruct rwlock1; try typeclasses eauto.
  destruct l; try typeclasses eauto.
  destruct rwlock2; try typeclasses eauto.
  destruct l; try typeclasses eauto.
Qed.

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

Lemma wp_free_rwlock γ (rwlock: lang.val) (storage_fn: S -> iProp Σ) :
  {{{ IsRwLock γ rwlock storage_fn }}} free_rwlock rwlock
  {{{ RET #() ; True }}}.
Proof.
  iIntros (Phi) "H Q".
  unfold free_rwlock.
  iDestruct (rwlock_get_struct _ _ _ with "H") as "%rwlock_form".
  destruct rwlock_form as [exc_loc [rw_loc rwlock_form]]. subst rwlock.
  unfold IsRwLock, rw_atomic_inv.
  iDestruct "H" as "[rli e]".
  iDestruct "e" as (exc rc x) "[c [mem_e mem_rc]]".
  
  wp_pures.
  wp_apply (wp_free with "mem_e").
  iIntros.
  
  wp_pures.
  wp_apply (wp_free with "mem_rc").
  iIntros.
  
  iApply "Q". done.
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
      {{{ g ∗ (g &&{E}&&> IsRwLock γ rwlock storage_fn) }}}
      loop_until (CAS (Fst rwlock) #0 #1)
      {{{ RET #(); exc_pending γ ∗
          g ∗ (g &&{E}&&> IsRwLock γ rwlock storage_fn)
      }}}.
Proof.
  iIntros (phi) "g x".
  wp_apply (loop_w_invariant _
    (g ∗ (g &&{E}&&> IsRwLock γ rwlock storage_fn))%I
    (g ∗ (g &&{E}&&> IsRwLock γ rwlock storage_fn))%I
    (exc_pending γ ∗ g ∗ (g &&{E}&&> IsRwLock γ rwlock storage_fn))
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
            iDestruct ("t" $! (0)) as "t".
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
            iDestruct ("t" $! 1) as "t".
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

Lemma acq2 γ (rwlock: lang.val) (g: iProp Σ) storage_fn E
    (not_in_e: γ ∉ E) :
      {{{ g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn))
          ∗ exc_pending γ
       }}}
      loop_until (op_eq (!(Snd rwlock)) #0)
      {{{ x, RET #(); 
          g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn))
          ∗ exc_guard γ ∗ storage_fn x
      }}}.
Proof.
  iIntros (phi) "g x".
  wp_apply (loop_w_invariant _
    (g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn)) ∗ exc_pending γ)%I
    (g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn)) ∗ exc_pending γ)%I
    (g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn)) ∗ exc_guard γ
        ∗ (∃ x , storage_fn x))
    with "g"
  ).
  - iIntros (phi2) "[g [#guard pend]] t".
      iMod (guarded_rwlock_get_struct g ⊤ E with "[g guard]") as "[g %rwlock_form]".
      { set_solver. } { iFrame "g". iFrame "guard". }
      destruct rwlock_form as [exc_loc [rw_loc rwlock_form]]. subst rwlock.
      
      unfold op_eq. wp_pures.
      wp_bind (HeapOp LoadOp _ _ _).
      
      iMod (guards_open g (IsRwLock γ (#exc_loc, #rw_loc) storage_fn) ⊤ E with "[g guard]")
        as "[irl irl_back]".
      { set_solver. } { iFrame "g". iFrame "guard". }
      
      unfold IsRwLock at 4.
      unfold IsRwLock at 4.
      unfold rw_lock_inst, rw_atomic_inv.
      iDestruct "irl" as "[#maps ex]".
      iDestruct "ex" as (exc rc x) "[c [mem_exc mem_rc]]".
      
      wp_load.
      
      have h : Decision (rc = 0) by solve_decision. destruct h.
      -- (* rc = 0 case, success *)
        subst rc. iMod (rw_exc_acquire with "maps [c pend]") as "[c [handle fx]]". { set_solver. }
        { iFrame "c". iFrame "pend". }
        
        iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
        { iFrame "maps". iExists exc, 0, x. iFrame. }
        iModIntro. wp_pures.
        iDestruct ("t" $! 1) as "t".
        iModIntro. iApply "t".
        iSplitL "".
        { iIntros "%". exfalso. crush. }
        iSplitL.
        { iIntros "%". iFrame "handle". iFrame "guard". iFrame "g". iExists x. iFrame "fx". }
        { iPureIntro. lia. }
     -- (* rc != 0 case, failure *)
        iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
        { iFrame "maps". iExists exc, rc, x. iFrame. }
        iDestruct ("t" $! (0)) as "t".
        iModIntro. wp_pures.
        assert (bool_decide (#rc = #0) = false) as Xb.
                { unfold bool_decide. case_decide; trivial. inversion H0. contradiction. }
        rewrite Xb.
        iModIntro. iApply "t".
        iSplitL "g pend".
        { iIntros "%". iFrame "g". iFrame "guard". iFrame "pend". }
        iSplitL.
        { iIntros "%". exfalso. crush. }
        { iPureIntro. lia. }
  - intros. trivial.
  - iIntros. iFrame.
  - iIntros "[g [guard [eg s]]]".
    iDestruct "s" as (x) "s".
    iDestruct ("x" $! (x)) as "x".
    iApply "x".
    iFrame.
Qed.

Lemma wp_acquire_exc γ (rwlock: lang.val) (g: iProp Σ) storage_fn E
    (not_in_e: γ ∉ E) :
      {{{ g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn)) }}}
      acquire_exc rwlock
      {{{ x, RET #();
          g ∗ exc_guard γ ∗ storage_fn x
      }}}.
Proof.
  unfold acquire_exc.
  iIntros (p) "[g #guard] P".
  wp_pure _.
  have j := acq1 γ rwlock g storage_fn E not_in_e. unfold loop_until in j.
  wp_bind ((rec: "loop" "c" := if: CAS (Fst rwlock) #0 #1 then #() else "loop" "c")%E #0).
  full_generalize ((rec: "loop" "c" := if: CAS (Fst rwlock) #0 #1 then #() else "loop" "c")%E #0) as e.
  wp_apply (j with "[guard g]"). { iFrame "g". iFrame "guard". }
  iIntros "[e [g g2]]".
  have k := acq2 γ rwlock g storage_fn E not_in_e. unfold loop_until in k. unfold op_eq in k.
  wp_seq.
  full_generalize ((rec: "loop" "c" := if: BinOp EqOp ! (Snd rwlock) #0 then #() else "loop" "c")%E #0) as e2.
  wp_apply (k with "[g g2 e]").
  - iFrame.
  - iIntros (x) "[g [g2 [e s]]]". iApply "P". iFrame.
Qed.

Lemma wp_release_exc (γ: gname) (rwlock: lang.val) (g: iProp Σ) storage_fn E x
    (not_in_e: γ ∉ E) :
      {{{ g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn)) ∗
          exc_guard γ ∗ storage_fn x }}}
      release_exc rwlock
      {{{ RET #(); g }}}.
Proof.
  unfold release_exc.
  iIntros (p) "[g [#guard [e fx]]] P".
  
  wp_pures.
  
  iDestruct "guard" as "#guard".
  iMod (guarded_rwlock_get_struct g ⊤ E with "[g guard]") as "[g %rwlock_form]".
  { set_solver. } { iFrame "g". iFrame "guard". }
  destruct rwlock_form as [exc_loc [rw_loc rwlock_form]]. subst rwlock.
  
  wp_pures.
  
  iMod (guards_open g (IsRwLock γ (#exc_loc, #rw_loc) storage_fn) ⊤ E with "[g guard]")
    as "[irl irl_back]".
  { set_solver. } { iFrame "g". iFrame "guard". }
  
  unfold IsRwLock at 2.
  unfold IsRwLock at 2.
  unfold rw_atomic_inv.
  iDestruct "irl" as "[#maps ex]".
  iDestruct "ex" as (exc rc x0) "[c [mem_exc mem_rc]]".
  
  wp_store.
  
  iMod (rw_exc_release with "maps [e c fx]") as "c".
  { set_solver. }
  { iFrame "c". iFrame "e". iFrame "fx". }
  
  iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
  { iFrame "maps". iExists false, rc, x. iFrame. }
  
  iModIntro.
  iApply "P".
  done.
Qed.

Lemma wp_release_shared (γ: gname) (rwlock: lang.val) (g: iProp Σ) storage_fn E x
    (not_in_e: γ ∉ E) :
      {{{ g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn)) ∗
          sh_guard γ x }}}
      release_shared rwlock
      {{{ dummy, RET dummy; g }}}.
Proof.
  unfold release_shared.
  iIntros (p) "[g [#guard e]] P".
  
  wp_pures.
  
  iDestruct "guard" as "#guard".
  iMod (guarded_rwlock_get_struct g ⊤ E with "[g guard]") as "[g %rwlock_form]".
  { set_solver. } { iFrame "g". iFrame "guard". }
  destruct rwlock_form as [exc_loc [rw_loc rwlock_form]]. subst rwlock.
  
  wp_pures.
  
  iMod (guards_open g (IsRwLock γ (#exc_loc, #rw_loc) storage_fn) ⊤ E with "[g guard]")
    as "[irl irl_back]".
  { set_solver. } { iFrame "g". iFrame "guard". }
  
  unfold IsRwLock at 2.
  unfold IsRwLock at 2.
  unfold rw_atomic_inv.
  iDestruct "irl" as "[#maps ex]".
  iDestruct "ex" as (exc rc x0) "[c [mem_exc mem_rc]]".
  
  wp_apply (wp_faa with "mem_rc").
  iIntros "mem_rc".
  
  iMod (rw_shared_release with "maps [e c]") as "c".
  { set_solver. }
  { iFrame "c". iFrame "e". }
  
  iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
  { iFrame "maps". iExists exc, (Z.add rc (Zneg xH)), x0. iFrame. }
  
  iModIntro.
  iApply "P".
  done.
Qed.

Lemma wp_acquire_shared (γ: gname) (rwlock: lang.val) (g: iProp Σ) storage_fn E
    (not_in_e: γ ∉ E) :
      {{{ g ∗ ((g &&{E}&&> IsRwLock γ rwlock storage_fn)) }}}
      acquire_shared rwlock
      {{{ x, RET #();
          g ∗ sh_guard γ x
          ∗ ( (sh_guard γ x &&{ {[γ]} }&&> ▷ storage_fn x))
      }}}.
Proof.
  iIntros (phi) "[g #guard] P".
  
  unfold acquire_shared.
  wp_pure _.
  
  iDestruct "guard" as "#guard".
  iMod (guarded_rwlock_get_struct g ⊤ E with "[g guard]") as "[g %rwlock_form]".
  { set_solver. } { iFrame "g". iFrame "guard". }
  destruct rwlock_form as [exc_loc [rw_loc rwlock_form]]. subst rwlock.
  
  wp_pures.
  iLöb as "IH".
  
  wp_bind (FAA #rw_loc #1).
  
  iMod (guards_open g (IsRwLock γ (#exc_loc, #rw_loc) storage_fn) ⊤ E with "[g guard]")
    as "[irl irl_back]".
  { set_solver. } { iFrame "g". iFrame "guard". }
  unfold IsRwLock at 2.
  unfold IsRwLock at 2.
  unfold rw_atomic_inv.
  iDestruct "irl" as "[#maps ex]".
  iDestruct "ex" as (exc rc x0) "[c [mem_exc mem_rc]]".
  
  wp_apply (wp_faa with "mem_rc"). iIntros "mem_rc". 
  iMod (rw_shared_begin with "maps c") as "[c pend]". { set_solver. }
  
  iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
  { iFrame "maps". iExists exc, (rc + 1)%Z, x0. iFrame. }
  iModIntro.
  
  wp_pures.
  
  wp_bind (! #exc_loc)%E.
  
  clear exc. clear rc. clear x0.
  
  iMod (guards_open g (IsRwLock γ (#exc_loc, #rw_loc) storage_fn) ⊤ E with "[g guard]")
    as "[irl irl_back]".
  { set_solver. } { iFrame "g". iFrame "guard". }
  unfold IsRwLock at 2.
  unfold IsRwLock at 2.
  unfold rw_atomic_inv.
  iDestruct "irl" as "[_ ex]".
  iDestruct "ex" as (exc rc x0) "[c [mem_exc mem_rc]]".
  
  wp_load.
  
  destruct exc.
  - (* exc = 1, fail *)

    iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
    { iFrame "maps". iExists true, rc, x0. iFrame. }
    iModIntro.
    wp_pures.
    
    wp_bind (FAA #rw_loc #(-1)).
    
    clear rc. clear x0.
    iMod (guards_open g (IsRwLock γ (#exc_loc, #rw_loc) storage_fn) ⊤ E with "[g guard]")
    as "[irl irl_back]".
    { set_solver. } { iFrame "g". iFrame "guard". }
    unfold IsRwLock at 2.
    unfold IsRwLock at 2.
    unfold rw_atomic_inv.
    iDestruct "irl" as "[_ ex]".
    iDestruct "ex" as (exc rc x0) "[c [mem_exc mem_rc]]".
    
    wp_apply (wp_faa with "mem_rc"). iIntros "mem_rc". 
    iMod (rw_shared_retry with "maps [c pend]") as "c". { set_solver. }
    { iFrame "c". iFrame "pend". }
    
    iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
    { iFrame "maps". iExists exc, (Z.add rc (Zneg xH)), x0. iFrame. }
    iModIntro.
    
    wp_pures.
    iApply ("IH" with "P").
    iFrame "g".
  - (* exc = 1, success *)
  
    iMod (rw_shared_acquire with "maps [c pend]") as "[c shg]". { set_solver. }
    { iFrame "c". iFrame "pend". }
    
    iDestruct (rw_borrow_back γ storage_fn x0 with "maps") as "sh_guard_is_g".
    
    iMod ("irl_back" with "[c mem_rc mem_exc]") as "g".
    { iFrame "maps". iExists false, rc, x0. iFrame. }
    iModIntro.
    
    wp_pures.
    
    iModIntro. iApply "P".
    iFrame "g". iFrame "shg". iFrame "sh_guard_is_g".
Qed.

End RwlockProof.
