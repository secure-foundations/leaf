From iris.base_logic.lib Require Import invariants.
From BurrowLang Require Import lang simp adequacy primitive_laws.
From Tpcms Require Import rwlock.
Require Import Burrow.tpcms.
Require Import Burrow.ra.
Require Import Burrow.rollup.

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

Definition acquire_exc : lang.expr :=
  λ: "rw" ,
    loop_until (CAS (Fst "rw") #0 #1) ;;
    loop_until (op_eq (!(Snd "rw")) #0).

Definition release_exc : lang.expr :=
  λ: "rw" ,
    Fst "rw" <- #0.
    
Definition acquire_shared : lang.expr :=
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
    
Definition release_shared : lang.expr :=
  λ: "rw" ,
    FAA (Snd "rw") (#(-1)).
    

Section RwlockProof.

Context {𝜇: BurrowCtx}.

Context {M} `{!EqDecision M} `{!TPCM M}.
Context `{!HasTPCM 𝜇 M}.
Context `{!HasTPCM 𝜇 (RwLock M)}.
Context `{!HasRef 𝜇 (rwlock_ref M)}.

Context `{!simpGS 𝜇 Σ}.

Definition NS := nroot .@ "rwlock".

Definition rwlock_inv 𝛼 𝛾 (contents_inv: M -> Prop) l1 l2 : iProp Σ :=
  (∃ exc rc x ,
    L (rwloc 𝛼 𝛾) (Central exc rc x)
    ∗ ⌜ contents_inv x ⌝
    ∗ (l1 ↦ (LitV (LitInt (match exc with false => 0 | true => 1 end))))
    ∗ (l2 ↦ (LitV (LitInt rc)))
  ).
  
Global Instance rwlock_inv_timeless 𝛼 𝛾 contents_inv l1 l2 : Timeless (rwlock_inv 𝛼 𝛾 contents_inv l1 l2). Admitted.

Definition is_rwlock rwlock 𝛼 𝛾 (contents_inv: M -> Prop) : iProp Σ :=
  match rwlock with
    | PairV (LitV (LitInt l1)) (LitV (LitInt l2)) =>
        inv NS (rwlock_inv 𝛼 𝛾 contents_inv l1 l2)
    | _ => False
  end.
  
Global Instance is_rwlock_persistent rwlock 𝛼 𝛾 contents_inv : Persistent (is_rwlock rwlock 𝛼 𝛾 contents_inv). Admitted.

Lemma hoare_new_rwlock (𝛾: BurrowLoc 𝜇) (x: M) (contents_inv: M -> Prop)
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

From BurrowLang Require Import class_instances.

(*
From iris.algebra Require Import excl.

Definition join : val :=
  rec: "join" "c" :=
    let: "r" := !"c" in
    if: Fst "r" then Snd "r"
    else "join" "c".
    
Definition NONE: expr := (#false, #()).
Definition NONEV: val := (#false, #()).

Definition SOME: expr := λ: "v", (#true, "v").
Definition SOMEV (v:val): val := (#true, v).

Class spawnG Σ := SpawnG { spawn_tokG :> inG Σ (exclR unitO) }.
Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_spawnΣ : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

Context `{!simpGS 𝜇 Σ, !spawnG Σ} (N : namespace).
    
Definition spawn_inv (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ lv, l ↦ lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ own γ (Excl ()))).
    
Definition join_handle (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ, own γ (Excl ()) ∗ inv N (spawn_inv γ l Ψ).
  *)

(*
Lemma join_spec (Ψ : val → iProp Σ) l :
  {{{ join_handle l Ψ }}} join #l {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "H HΦ". iDestruct "H" as (γ) "[Hγ #?]".
  iLöb as "IH". unfold join. wp_rec. wp_bind (! _)%E. iInv N as (v) "[Hl Hinv]".
  wp_load. iDestruct "Hinv" as "[%|Hinv]"; subst.
  - iModIntro. iSplitL "Hl"; [iNext; iExists _; iFrame; eauto|].
    wp_pures. 
    wp_apply ("IH" with "Hγ [HΦ]"). auto.
  - iDestruct "Hinv" as (v' ->) "[HΨ|Hγ']".
    + iModIntro. iSplitL "Hl Hγ"; [iNext; iExists _; iFrame; eauto|].
      wp_pures. by iApply "HΦ".
    + iDestruct (own_valid_2 with "Hγ Hγ'") as %[].
Qed.
End proof.
*)


Lemma acq1 (rwlock: lang.val) 𝛼 𝛾 contents_inv :
      {{{ is_rwlock rwlock 𝛼 𝛾 contents_inv }}}
      loop_until (CAS (Fst rwlock) #0 #1)
      {{{ RET #(); L (rwloc 𝛼 𝛾) ExcPending }}}.
Proof.
  iIntros (phi) "#isr p".
  wp_apply (loop_w_invariant _ (is_rwlock rwlock 𝛼 𝛾 contents_inv)%I (is_rwlock rwlock 𝛼 𝛾 contents_inv)%I (L (rwloc 𝛼 𝛾) ExcPending ∗ is_rwlock rwlock 𝛼 𝛾 contents_inv)%I).
  - iIntros (phi2) "#t p".
      unfold is_rwlock. destruct rwlock; try (destruct rwlock1, rwlock2).
        + iExFalso. iFrame "#".
        + iExFalso. iFrame "#".
        + destruct l, l0.
          * wp_pures. iInv "t" as (exc rc) ">I".
              iDestruct "I" as (x) "I".
              iDestruct "I" as "[L [c [a b]]]".
            unfold rwlock_inv.
            wp_apply (wp_cas with "a").
            destruct exc.
              -- case_decide.
                ++ exfalso. inversion H.
                ++ iIntros "n1". iModIntro. iSplitR "p".
                  ** iModIntro. iExists true, rc, x. iFrame.
                  ** simpl. iApply ("p" $! 0). iSplit.
                    --- iIntros. iFrame "#".
                    --- iSplit.
                      +++ iIntros "%". inversion H0.
                      +++ iPureIntro. lia.
              -- case_decide.
                ++ iIntros "n1".
                  iMod (rw_exc_begin with "L") as "[L pend]". iModIntro. iSplitR "p pend".
                   ** iModIntro. iExists true, rc, x. iFrame.
                   ** simpl. iApply ("p" $! 1). iSplit.
                    --- iIntros "%". inversion H0.
                    --- iSplitL "pend".
                      +++ iIntros. iFrame "#". iFrame.
                      +++ iPureIntro. lia.
                ++ contradiction.
          * iExFalso. iFrame "#".
          * iExFalso. iFrame "#".
          * iExFalso. iFrame "#".
        + iExFalso. destruct l.
          * iFrame "#".
          * iFrame "#".
        + iExFalso. destruct l.
          * iFrame "#".
          * iFrame "#".
        + iExFalso. iFrame "#".
        + iExFalso. iFrame "#".
        + iExFalso. iFrame "#".
        + iExFalso. iFrame "#".
        + iExFalso. iFrame "#".
        + iExFalso. iFrame "#".
    - intros. trivial.
    - iIntros. iFrame "#".
    - iFrame "#".
    - iIntros "[x y]". iApply "p". iFrame.
Qed.

End rwlockProof.
