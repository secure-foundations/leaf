From iris.base_logic.lib Require Import invariants.
From BurrowLang Require Import lang simp adequacy primitive_laws.
Require Import Burrow.tpcms.
Require Import Burrow.ra.
Require Import Burrow.rollup.
Require Import Burrow.CpdtTactics.
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

Definition compute_hash: lang.expr. Admitted.

Definition query_iter: lang.expr :=
  rec: "query_iter" "slots" "locks" "k" "i" :=
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
      "ret"
.

Definition query: lang.expr :=
  λ: "query" "ht" "k" ,
    query_iter (Fst "ht") (Snd "ht") "k" (compute_hash "k").

Section HashTableProof.

Context {𝜇: BurrowCtx}.

Print Instances RelDecision.
Print Instances Countable.


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
  
Instance seq_is_ht_sl 𝛾 slots locks : Persistent (is_ht_sl 𝛾 slots locks).
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

Lemma s_i_acquire_shared a : subst "i" a acquire_shared = acquire_shared.
Proof. trivial. Qed.
Lemma s_k_acquire_shared a : subst "k" a acquire_shared = acquire_shared.
Proof. trivial. Qed.
Lemma s_locks_acquire_shared a : subst "locks" a acquire_shared = acquire_shared.
Proof. trivial. Qed.
Lemma s_slots_acquire_shared a : subst "slots" a acquire_shared = acquire_shared.
Proof. trivial. Qed.
Lemma s_query_iter_acquire_shared a : subst "query_iter" a acquire_shared = acquire_shared.
Proof. trivial. Qed.
Lemma s_i_release_shared a : subst "i" a release_shared = release_shared.
Proof. trivial. Qed.
Lemma s_k_release_shared a : subst "k" a release_shared = release_shared.
Proof. trivial. Qed.
Lemma s_locks_release_shared a : subst "locks" a release_shared = release_shared.
Proof. trivial. Qed.
Lemma s_slots_release_shared a : subst "slots" a release_shared = release_shared.
Proof. trivial. Qed.
Lemma s_ret_release_shared a : subst "ret" a release_shared = release_shared.
Proof. trivial. Qed.
Lemma s_query_iter_release_shared a : subst "query_iter" a release_shared = release_shared.
Proof. trivial. Qed.
Lemma s_i_seq_idx a : subst "i" a seq_idx = seq_idx.
Proof. trivial. Qed.
Lemma s_k_seq_idx a : subst "k" a seq_idx = seq_idx.
Proof. trivial. Qed.
Lemma s_locks_seq_idx a : subst "locks" a seq_idx = seq_idx.
Proof. trivial. Qed.
Lemma s_slots_seq_idx a : subst "slots" a seq_idx = seq_idx.
Proof. trivial. Qed.
Lemma s_query_iter_seq_idx a : subst "query_iter" a seq_idx = seq_idx.
Proof. trivial. Qed.
Lemma s_ret_seq_idx a : subst "ret" a seq_idx = seq_idx.
Proof. trivial. Qed.


Opaque acquire_shared.
Opaque release_shared.
Opaque seq_idx.
  
Lemma wp_ht_query 𝜅 𝛾 (slots locks: lang.val) (k: Key) (v: option Value) (i: nat)
  (i_bound: hash k ≤ i ≤ ht_fixed_size) :
      {{{ is_ht_sl 𝛾 slots locks ∗ L 𝛾 (m k v) ∗ A 𝜅 ∗ BorrowedRange 𝜅 𝛾 k (hash k) i
        ∗ ⌜has_length slots ht_fixed_size /\ has_length locks ht_fixed_size⌝ 
      }}}
      query_iter slots locks #k #i
      {{{ RET (opt_as_val v); L 𝛾 (m k v) }}}.
Proof.
  iIntros (Phi) "[#ht [m [a [range %szs]]]] Phi".
  wp_pures.
    rewrite s_query_iter_acquire_shared.
    rewrite s_slots_acquire_shared.
    rewrite s_locks_acquire_shared.
    rewrite s_k_acquire_shared.
    rewrite s_i_acquire_shared.
    rewrite s_query_iter_release_shared.
    rewrite s_slots_release_shared.
    rewrite s_locks_release_shared.
    rewrite s_k_release_shared.
    rewrite s_i_release_shared.
    rewrite s_query_iter_seq_idx.
    rewrite s_slots_seq_idx.
    rewrite s_locks_seq_idx.
    rewrite s_k_seq_idx.
    rewrite s_i_seq_idx.
  induction i as [i IHi] using (induction_ltof1 _ (λ j, ht_fixed_size - j)); unfold ltof in IHi.
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
    
    iDestruct (get_seq_iprop _ _ i _ with "ht") as "hti".
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
        rewrite s_ret_release_shared.
        rewrite s_ret_seq_idx.
        
        (* get the answer using the borrowed props *)
        
        (*
        iDestruct (ActiveJoin with "[a a0]") as "a". {iFrame.}
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
        
        wp_pure _.
        
      
        
        
        
        iIntros (x) "[guard %xinv]".

        
        
        
        
        
        
        

      
      
    
    unfold slot_as_val.
    wp_pures.
    
    

Lemma wp_ht_query 𝛾 (ht: lang.val) (k: Key) (v: option Value) :
      {{{ is_ht 𝛾 ht ∗ L 𝛾 (m k v) }}}
      query ht #k
      {{{ RET (opt_as_val v); L 𝛾 (m k v) }}}.
  

End HashTableProof.

