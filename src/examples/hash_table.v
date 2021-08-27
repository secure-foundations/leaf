From iris.base_logic.lib Require Import invariants.
From BurrowLang Require Import lang simp adequacy primitive_laws.
Require Import Burrow.tpcms.
Require Import Burrow.ra.
Require Import Burrow.rollup.
Require Import Burrow.tactics.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From BurrowLang Require Import notation tactics class_instances.
From BurrowLang Require Import heap_ra.
From BurrowLang Require Import lang.
From iris Require Import options.

From Tpcms Require Import hash_table.
From Tpcms Require Import rwlock.
From Tpcms Require Import heap.
From Examples Require Import rwlock.
From Examples Require Import seqs.

Require Import Burrow.tactics.
Require Import coq_tricks.Deex.
Require Import cpdt.CpdtTactics.

Definition compute_hash: lang.val. Admitted.

Definition query_iter: lang.val :=
  (rec: "query_iter" "slots" "locks" "k" "i" :=
    if: (BinOp EqOp "i" #(ht_fixed_size)) then
      PairV #false #()
    else
      acquire_shared (seq_idx "i" "locks") ;;
      let: "ret" := (
        let: "slot" := ! (seq_idx "i" "slots") in
          if: (Fst "slot") then
            let: "k1" := Fst (Snd "slot") in
            let: "v1" := Snd (Snd "slot") in
            if: (BinOp EqOp "k" "k1") then
              Pair #true "v1"
            else
              "query_iter" "slots" "locks" "k" ("i" + #1)
          else
            PairV #false #()
      ) in
      release_shared (seq_idx "i" "locks") ;;
      "ret")%V
.

Definition query: lang.val :=
  λ: "ht" "k" ,
    query_iter (Fst "ht") (Snd "ht") "k" (compute_hash "k").

Section HashTableProof.

Context {𝜇: BurrowCtx}.

Context `{!simpGS 𝜇 Σ}.
(*Context `{!HasTPCM 𝜇 (HeapT loc lang.val)}. *)

Context `{!HasTPCM 𝜇 HT}.
Context `{!HasTPCM 𝜇 (RwLock (HT * (HeapT loc lang.val)))}.
Context `{!HasRef 𝜇 (rwlock_ref (HT * (HeapT loc lang.val)))}.

Fixpoint seq_iprop (fn: nat -> iProp Σ) (n: nat) :=
  match n with
  | 0 => (True)%I
  | (S i) => (fn i ∗ seq_iprop fn i)%I
  end.

Lemma get_seq_iprop (fn: nat -> iProp Σ) (n: nat) (i: nat)
  (i_lt_n : i < n)
  : seq_iprop fn n ⊢ fn i.
Proof.
  induction n.
  - lia.
  - have h : Decision (i = n) by solve_decision. destruct h.
    + subst i. cbn [seq_iprop]. iIntros "[x y]". iFrame.
    + assert (i < n) by lia. intuition.
      cbn [seq_iprop]. iIntros "[x y]". iDestruct (H0 with "y") as "y". iFrame.
Qed.

Instance seq_iprop_persistent fn n (pi: ∀ i , Persistent (fn i)) : Persistent (seq_iprop fn n).
Proof.
  induction n.
  - apply _.
  - apply _.
Qed.

Definition slot_as_val (slot: option (Key * Value)) :=
  match slot with
  | None => PairV #false #()
  | Some (k, v) => PairV #true (PairV #k #v)
  end.
  
Definition opt_as_val (val: option Value) :=
  match val with
  | None => PairV #false #()
  | Some v => PairV #true #v
  end.

Definition ht_inv_i (i: nat) (l: loc) : ((HT * (HeapT loc lang.val)) -> Prop) :=
  λ p , match p with
    | (ht, mem) => ∃ slot ,
      mem = (l $↦ (slot_as_val slot))
      /\ ht = (s i slot)
  end.
  
Definition heap_name := gen_heap_name simp_gen_heapG.

Definition is_ht_i 𝛾 (slots locks: lang.val) (i: nat) :=
  match (elem slots i) with
  | LitV (LitInt l) => (∃ 𝛼 , is_rwlock (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l))%I
  | _ => (False) % I
  end.

Definition is_ht_sl 𝛾 (slots locks: lang.val) :=
  seq_iprop (is_ht_i 𝛾 slots locks) ht_fixed_size.
  
Instance is_ht_sl_persistent 𝛾 slots locks : Persistent (is_ht_sl 𝛾 slots locks).
Proof.
  apply seq_iprop_persistent.
  intro. unfold is_ht_i.
  destruct (elem slots i); try typeclasses eauto.
  destruct l; typeclasses eauto.
Qed.

Definition is_ht 𝛾 (ht: lang.val) :=
  match ht with
  | PairV slots locks => (is_ht_sl 𝛾 slots locks
      ∗ ⌜has_length slots ht_fixed_size /\ has_length locks ht_fixed_size⌝
      )%I
  | _ => (False)%I
  end.
  
Instance is_ht_persistent 𝛾 ht : Persistent (is_ht 𝛾 ht).
Proof.
  unfold is_ht.
  destruct ht; try apply _.
Qed.

Lemma destruct_slots_i 𝛾 slots locks i
  : is_ht_i 𝛾 slots locks i -∗ ⌜ ∃ (l: Z) , elem slots i = #l ⌝.
Proof.
  iIntros "ih". unfold is_ht_i. destruct (elem slots i).
  - destruct l.
    + iPureIntro. exists n. trivial.
    + iExFalso. iFrame.
  - iExFalso. iFrame.
  - iExFalso. iFrame.
Qed.

Lemma destruct_ht 𝛾 ht
  : is_ht 𝛾 ht -∗ ⌜ ∃ slots locks , ht = PairV slots locks ⌝.
Proof.
  iIntros "ih". unfold is_ht. destruct ht.
  - iExFalso. iFrame.
  - iExFalso. iFrame.
  - iPureIntro. exists ht1, ht2. trivial.
Qed.

Lemma z_n_add1 (i: nat)
  : ((LitV (Z.add i (Zpos xH))) = (LitV (Init.Nat.add i (S O)))). 
Proof.  f_equal. f_equal. lia. Qed.
  
Lemma wp_ht_query_iter 𝜅 𝛾 (slots locks: lang.val) (k: Key) (v: option Value) (i: nat) :
      {{{
        ⌜ hash k ≤ i ≤ ht_fixed_size ⌝ ∗
        is_ht_sl 𝛾 slots locks ∗ L 𝛾 (m k v) ∗ A 𝜅 ∗ BorrowedRange 𝜅 𝛾 k (hash k) i
        ∗ ⌜has_length slots ht_fixed_size /\ has_length locks ht_fixed_size⌝ 
      }}}
      query_iter slots locks #k #i
      {{{ RET (opt_as_val v); L 𝛾 (m k v) ∗ A 𝜅 }}}.
Proof.
  unfold query_iter.
  iRevert (i).
  iRevert (𝜅).
  iLöb as "IH".
  iIntros (𝜅 i Phi) "[%i_bound [#ht [m [a [range %szs]]]]] Phi".
  wp_pures.
  
  unfold query_iter. wp_pures.
  have h : Decision (i = ht_fixed_size) by solve_decision. destruct h.
  
  (* case: i = fixed_size *)
  
  - subst i. 
    assert (bool_decide (#ht_fixed_size = #ht_fixed_size) = true) as bd.
    { unfold bool_decide. case_decide; crush. }
    rewrite bd.
    wp_pures.
    iDestruct (ht_QueryReachedEnd with "a range m") as "%x". subst v.
    unfold opt_as_val. iModIntro.
    iApply "Phi". iFrame.
  
  (* case: i < fixed_size *)
  
  - 
    assert (bool_decide (#i = #ht_fixed_size) = false) as bd.
    { unfold bool_decide. case_decide; trivial. inversion H. lia. }
    rewrite bd.
    wp_if.
    wp_pures.
    
    (* lookup lock in sequence *)
    
    wp_bind (seq_idx #i locks).
    wp_apply wp_seq_idx.
    { apply has_elem_of_has_length with (len := ht_fixed_size).
      - lia. - intuition. } { done. }
    iIntros "_".
    
    (* acquire lock *)
    
    iDestruct (get_seq_iprop _ _ i with "ht") as "hti".
    { lia. }
    iDestruct (destruct_slots_i with "hti") as "%ds". 
    deex. unfold is_ht_i. rewrite ds. iDestruct "hti" as (𝛼) "hti".
    wp_bind (acquire_shared (elem locks i)).
    wp_apply (wp_acquire_shared (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) with "hti").
    iIntros (x) "[guard %xinv]".
    
    wp_pures. 
    
    (* lookup slot ptr in sequence *)
    
    wp_bind (seq_idx #i slots).
    wp_apply wp_seq_idx.
    { apply has_elem_of_has_length with (len := ht_fixed_size).
      - lia. - intuition. } { done. }
    iIntros "_".
    
    (* borrow from the guard *)
    
    iMod (BorrowBegin _ _ with "guard") as (𝜅0) "[a0 [r guard]]".
    iDestruct (rw_borrow_back _ _ _ _ with "guard") as "cross".
    unfold ht_inv_i in xinv. destruct x. deex. destruct_ands. subst h. subst h0.
    iDestruct (BorrowBackBoth _ _ _ _ _ with "cross") as "[slot mem]".
    
    (* read the slot *)
    
    rewrite ds.
    wp_apply (wp_load_borrow _ _ _ _ _ with "[a0 mem]").
    { iFrame. }
    iIntros "[a0 mem]".
    wp_pures.
    
    destruct slot.
    
    + (* case: the slot has something in it *)
    
      unfold slot_as_val. destruct p. wp_pures.
      
      have h : Decision (k = k0) by solve_decision. destruct h.
      
      * (* case: the found key matches *)

        subst k0. 
        assert (bool_decide (#k = #k) = true) as bd0.
        { rewrite bool_decide_decide. destruct (decide (#k = #k)); trivial. contradiction. }
        rewrite bd0.
        wp_if.
        wp_pure _.
        wp_pure _.
        wp_pure _.
        
        (* get the answer using the borrowed props *)
        
        (*
        iDestruct (ActiveJoin with "[a a0]") as "a". { iFrame. }
        iDestruct (BorrowShorten _ (lifetime_intersect 𝜅0 𝜅) _ _ with "slot") as "slot".
        { apply LifetimeInclusion_Left. }
        iDestruct (ht_BorrowedRangeShorten _ (lifetime_intersect 𝜅0 𝜅) with "range") as "range".
        { apply LifetimeInclusion_Right. }
        *)
        
        iDestruct (ht_QueryFound _ _ _ _ _ _ with "a0 slot m") as "%veq".
        rewrite veq.
        
        (* release lock *)
        
        iMod (@BorrowExpire _ _ _
          (RwLock (HT * (HeapT loc lang.val))) _ _ _
          _ _ _
          with "[a0 r]") as "guard".
        { iFrame. }
        
        wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        
        wp_bind (release_shared (elem locks i)).
        wp_apply (wp_release_shared (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) _ with "[hti guard]").
        { iFrame. iFrame "#". }
        iIntros (dummy) "_".
        
        wp_pures.
        unfold opt_as_val.
        iApply "Phi". iModIntro. iFrame.
        
      *
        (* case: the found key does not match - we have to recurse *)
        
        wp_pures.
        
        assert (bool_decide (#k = #k0) = false) as bd0.
        { rewrite bool_decide_decide. destruct (decide (#k = #k0)); trivial. crush. }
        rewrite bd0.

        iDestruct (ActiveJoin with "[a a0]") as "a". { iFrame. }
        iDestruct (BorrowShorten _ (lifetime_intersect 𝜅0 𝜅) _ _ with "slot") as "slot".
        { apply LifetimeInclusion_Left. }
        iDestruct (ht_BorrowedRangeShorten _ (lifetime_intersect 𝜅0 𝜅) with "range") as "range".
        { apply LifetimeInclusion_Right. }
        iDestruct (ht_BorrowedRangeAppend _ _ _ _ _ _ _ with "range slot") as "range".
        { crush. }
        
        wp_pure _.
        wp_pure _.
        replace (#true) with (#1) by trivial.
        replace (#false) with (#0) by trivial.
        full_generalize ((rec: "query_iter" "slots" "locks" "k" "i" :=
                      if: BinOp EqOp "i" #ht_fixed_size then (#0, #())%V
                      else acquire_shared (seq_idx "i" "locks");; 
                           let: "ret" := let: "slot" := ! (seq_idx "i" "slots") in
                                         if: Fst "slot"
                                         then let: "k1" := Fst (Snd "slot") in
                                              let: "v1" := Snd (Snd "slot") in
                                              if: BinOp EqOp "k" "k1" then 
                                              (#1, "v1")
                                              else "query_iter" "slots" "locks" "k"
                                                     ("i" + #1) else 
                                         (#0, #())%V in
                           release_shared (seq_idx "i" "locks");; "ret")%V) as big_e.
                           
       wp_bind (big_e slots locks #k #(i + 1)).
       rewrite z_n_add1.
       wp_apply ("IH" $! (lifetime_intersect 𝜅0 𝜅) (i + 1) with "[m a range]").
       {
          iSplitR. { iPureIntro. lia. }
          iSplitR. { iFrame "#". }
          iSplitL "m". { iFrame. }
          iSplitL "a". { iFrame. }
          iSplitL "range". { iFrame. }
          iPureIntro. intuition.
       }
       
       iIntros "[m a]".
       
       (* release the lock *)
       
        iDestruct (ActiveSplit with "a") as "[a0 a]".
               
        iMod (@BorrowExpire _ _ _
          (RwLock (HT * (HeapT loc lang.val))) _ _ _
          _ _ _
          with "[a0 r]") as "guard".
        { iFrame. }
        
        wp_pure _.
        wp_pure _.
        
        wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        
        wp_bind (release_shared (elem locks i)).
        wp_apply (wp_release_shared (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) _ with "[hti guard]").
        { iFrame. iFrame "#". }
        iIntros (dummy) "_".
        
        wp_pures.
        
        iModIntro. iApply ("Phi" with "[m a]"). { iFrame. }
    +
        (* case: the slot has nothing in it *)
        
        wp_pure _.
        wp_pure _.
        wp_pure _.
        wp_pure _.
        
        iDestruct (ActiveJoin with "[a a0]") as "a". { iFrame. }
        iDestruct (BorrowShorten _ (lifetime_intersect 𝜅0 𝜅) _ _ with "slot") as "slot".
        { apply LifetimeInclusion_Left. }
        iDestruct (ht_BorrowedRangeShorten _ (lifetime_intersect 𝜅0 𝜅) with "range") as "range".
        { apply LifetimeInclusion_Right. }

        iDestruct (ht_QueryNotFound _ _ _ _ _ with "a range slot m") as "%veq".
        rewrite veq.
        
        (* release lock *)
        
        iDestruct (ActiveSplit with "a") as "[a0 a]".
        
        iMod (@BorrowExpire _ _ _
          (RwLock (HT * (HeapT loc lang.val))) _ _ _
          _ _ _
          with "[a0 r]") as "guard".
        { iFrame. }
        
        wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        
        wp_bind (release_shared (elem locks i)).
        wp_apply (wp_release_shared (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) _ with "[hti guard]").
        { iFrame. iFrame "#". }
        iIntros (dummy) "_".
        
        wp_pures.
        unfold opt_as_val.
        iApply "Phi". iModIntro. iFrame.
Qed.

Lemma wp_compute_hash (k: Key) :
      {{{ True }}}
      compute_hash #k
      {{{ RET #(hash k) ; True }}}. Admitted.

Lemma wp_ht_query 𝛾 (ht: lang.val) (k: Key) (v: option Value) :
      {{{ is_ht 𝛾 ht ∗ L 𝛾 (m k v) }}}
      query ht #k
      {{{ RET (opt_as_val v); L 𝛾 (m k v) }}}.
Proof.
  unfold query.
  iIntros (Phi) "[#ht l] Phi".
  
  iDestruct (destruct_ht with "ht") as "%ds". deex. subst ht.
  
  wp_pure _. wp_pure _. wp_pure _.
  
  wp_bind (compute_hash #k).
  wp_apply (wp_compute_hash k). { done. }
  iIntros "_".
  
  iMod (ht_BorrowedRangeEmpty 𝛾 k (hash k)) as (𝜅) "[range a]".
  
  wp_apply (wp_ht_query_iter with "[l range a]").
  {
    unfold is_ht.
    iDestruct "ht" as "[#iht %l]".
    iFrame. iFrame "#".
    iPureIntro. intuition.
    assert (hash k < ht_fixed_size) by (apply hash_in_bound). lia. 
  }
  
  iIntros "[l a]". iApply "Phi". iFrame.
Qed.

End HashTableProof.
