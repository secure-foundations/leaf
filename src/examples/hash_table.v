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

Definition init_slots: lang.val :=
  (rec: "init_slots" "n" :=
    if: (BinOp EqOp "n" #0) then
      #()
    else
      Pair (ref (#false, #())) ("init_slots" ("n" + #(-1)))
  ).
  
Definition init_locks: lang.val :=
  (rec: "init_locks" "n" :=
    if: (BinOp EqOp "n" #0) then
      #()
    else
      Pair new_rwlock ("init_locks" ("n" + #(-1)))
  ).

Definition new_hash_table: lang.val :=
  λ: "unit" ,
    let: "slots" := init_slots #(ht_fixed_size) in
    let: "locks" := init_locks #(ht_fixed_size) in
    ("slots", "locks").

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
    
Definition update_iter: lang.val :=
  (rec: "update_iter" "slots" "locks" "k" "v" "i" :=
    if: (BinOp EqOp "i" #(ht_fixed_size)) then
      #false
    else
      acquire_exc (seq_idx "i" "locks") ;;
      let: "ret" := (
        let: "slot" := ! (seq_idx "i" "slots") in
          if: (Fst "slot") then
            let: "k1" := Fst (Snd "slot") in
            let: "v1" := Snd (Snd "slot") in
            if: (BinOp EqOp "k" "k1") then
              (seq_idx "i" "slots") <- (#true, ("k", "v")) ;; #true
            else
              "update_iter" "slots" "locks" "k" "v" ("i" + #1)
          else
            (seq_idx "i" "slots") <- (#true, ("k", "v")) ;; #true
      ) in
      release_exc (seq_idx "i" "locks") ;;
      "ret")%V
.


Definition update: lang.val :=
  λ: "ht" "k" "v" ,
    update_iter (Fst "ht") (Snd "ht") "k" "v" (compute_hash "k").
    
Definition main: lang.val :=
  λ: "unit" ,
    let: "ht" := new_hash_table #() in
    let: "insert_success" := update "ht" #0 #17 in
    Fork ( update "ht" #1 #12 ) ;;
    query "ht" #0
.

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

Definition is_slot_i (slots: lang.val) (i: nat) :=
  match (elem slots i) with
  | LitV (LitInt l) => (l ↦ slot_as_val None)%I
  | _ => (False) % I
  end.
  
Lemma seq_iprop_is_slot_i_extend (n: nat) slots slot_ref :
  ⊢ seq_iprop (is_slot_i slots) n -∗
  @mapsto lang.val val_eq_dec' loc Z_eq_dec Z_countable 𝜇 Σ (@simp_gen_heapG 𝜇 Σ simpGS0)
              slot_ref (#0, #())%V -∗
  seq_iprop (is_slot_i (#slot_ref, slots)) (S n).
Proof.
  induction n.
    - iIntros "si sr".
      unfold seq_iprop. unfold is_slot_i. unfold elem. unfold slot_as_val. iFrame.
    - iIntros "si sr".
      cbn [seq_iprop].
      iDestruct "si" as "[isi si]".
      iDestruct (IHn with "si sr") as "x".
      cbn [seq_iprop]. iFrame.
Qed.

Lemma wp_init_slots (n: nat) :
      {{{ True }}}
      init_slots #n
      {{{ slots , RET slots;
          seq_iprop (is_slot_i slots) n ∗ ⌜ has_length slots n ⌝
      }}}.
Proof.
  induction n.
  - unfold init_slots. iIntros (Phi) "t Phi". wp_pures.
    iModIntro. iApply "Phi". unfold seq_iprop. iFrame.
  - unfold init_slots. iIntros (Phi) "t Phi".
    wp_pure _. wp_pure _. wp_pure _. wp_pure _.
    unfold init_slots in IHn.
    replace (LitV ((Z.add (S n) (Zneg xH)))) with (LitV n) by (f_equal; f_equal; lia).
    replace (#false) with (#0) in IHn by trivial.
    full_generalize (rec: "init_slots" "n" :=
        if: BinOp EqOp "n" #0 then #() else (ref (#0, #()), "init_slots" ("n" + #(-1))))%V as big_e.
    wp_bind (big_e #n).
    wp_apply IHn.
    { done. }
    iIntros (slots) "[si %hl]".
    
    wp_alloc slot_ref as "rslot".
    wp_pures.
    iModIntro. iApply "Phi".
    iDestruct (seq_iprop_is_slot_i_extend with "si rslot") as "x".
    iFrame.
    iPureIntro. unfold has_length. destruct n; trivial.
Qed.

Definition is_lock_i (locks: lang.val) (i: nat) :=
  match (elem locks i) with
  | PairV (LitV (LitInt l1)) (LitV (LitInt l2)) => (l1 ↦ #0 ∗ l2 ↦ #0)%I
  | _ => (False) % I
  end.
  
Lemma seq_iprop_is_lock_i_extend (n: nat) locks lock_ref1 lock_ref2 :
  ⊢ seq_iprop (is_lock_i locks) n -∗
  @mapsto lang.val val_eq_dec' loc Z_eq_dec Z_countable 𝜇 Σ (@simp_gen_heapG 𝜇 Σ simpGS0)
              lock_ref1 #0 -∗
  @mapsto lang.val val_eq_dec' loc Z_eq_dec Z_countable 𝜇 Σ (@simp_gen_heapG 𝜇 Σ simpGS0)
              lock_ref2 #0 -∗
  seq_iprop (is_lock_i ((#lock_ref1, #lock_ref2), locks)) (S n).
Proof.
  induction n.
    - iIntros "si sr1 sr2".
      unfold seq_iprop. unfold is_lock_i. unfold elem. iFrame.
    - iIntros "si sr1 sr2".
      cbn [seq_iprop].
      iDestruct "si" as "[isi si]".
      iDestruct (IHn with "si sr1 sr2") as "x".
      cbn [seq_iprop]. iFrame.
Qed.

Lemma wp_init_locks (n: nat) :
      {{{ True }}}
      init_locks #n
      {{{ locks , RET locks;
          seq_iprop (is_lock_i locks) n ∗ ⌜ has_length locks n ⌝
      }}}.
Proof.
  induction n.
  - unfold init_locks. iIntros (Phi) "t Phi". wp_pures.
    iModIntro. iApply "Phi". unfold seq_iprop. done.
  - unfold init_locks. iIntros (Phi) "t Phi".
    wp_pure _. wp_pure _. wp_pure _. wp_pure _.
    unfold init_locks in IHn.
    replace (LitV ((Z.add (S n) (Zneg xH)))) with (LitV n) by (f_equal; f_equal; lia).
    replace (#false) with (#0) in IHn by trivial.
    full_generalize ((rec: "init_locks" "n" :=
        if: BinOp EqOp "n" #0 then #() else (new_rwlock, "init_locks" ("n" + #(-1))))%V) as big_e.
    wp_bind (big_e #n).
    wp_apply IHn.
    { done. }
    iIntros (locks) "[si %hl]".
    
    wp_alloc r2 as "r2".
    wp_alloc r1 as "r1".
    wp_pures.
    iModIntro. iApply "Phi".
    iDestruct (seq_iprop_is_lock_i_extend with "si r1 r2") as "x".
    iFrame.
    iPureIntro. unfold has_length. destruct n; trivial.
Qed.

Lemma init_is_ht_sl 𝛾 slots locks :
  L 𝛾 (sseq ht_fixed_size) -∗
  seq_iprop (is_slot_i slots) ht_fixed_size -∗
  seq_iprop (is_lock_i locks) ht_fixed_size -∗
  |={⊤}=>
  is_ht_sl 𝛾 slots locks.
Proof.
  unfold is_ht_sl. full_generalize ht_fixed_size as n. induction n.
  - iIntros. trivial.
  - iIntros "L slots locks".
    rewrite sseq_append.
    cbn [seq_iprop].
    iDestruct "slots" as "[slot slots]".
    iDestruct "locks" as "[lock locks]".
    iDestruct (L_op with "L") as "[L me]".
    iSplitL "slot lock me".
    + unfold is_ht_i.
      unfold is_slot_i.
      unfold is_lock_i.
      destruct (elem slots n); try (iExFalso; iFrame; fail).
      destruct l; try (iExFalso; iFrame; fail).
      destruct (elem locks n); try (iExFalso; iFrame; fail).
      destruct v1; try (iExFalso; iFrame; fail).
      destruct l; try (iExFalso; iFrame; fail).
      destruct v2; try (iExFalso; iFrame; fail).
      destruct l; try (iExFalso; iFrame; fail).
      iMod (CrossJoin _ _ _ _ with "me slot") as "cross".
      iMod (rw_new _ _ with "cross") as (𝛼) "rw".
      iAssert (rwlock_inv 𝛼 (cross_loc 𝛾 (gen_heap_name simp_gen_heapG)) (ht_inv_i n n0) n1 n2) with "[lock rw]" as "ri".
      { unfold rwlock_inv. iExists false. iExists 0.
          iExists (s n None, n0 $↦ slot_as_val None). iFrame.
          iPureIntro. unfold ht_inv_i. exists None. intuition. }
      iMod (inv_alloc NS _ _ with "ri") as "i".
      iModIntro.
      iExists 𝛼.
      unfold is_rwlock. trivial.
    + iMod (IHn with "L slots locks") as "X". iModIntro. iFrame.
Qed.

Lemma wp_new_hash_table (maxkey: nat) :
      {{{ True }}}
      new_hash_table #()
      {{{ 𝛾 ht , RET ht; is_ht 𝛾 ht ∗ L 𝛾 (mseq maxkey) }}}.
Proof.
  iIntros (Phi) "t Phi".
  unfold new_hash_table.
  wp_pures.
  wp_apply wp_init_slots. { done. } iIntros (slots) "[slots %hl_slots]".
  wp_apply wp_init_locks. { done. } iIntros (locks) "[locks %hl_locks]".
  wp_pures.
  iMod (ht_Init maxkey) as (𝛾) "[mseq sseq]".
  iApply ("Phi" $! (𝛾)).
  unfold is_ht.
  iMod (init_is_ht_sl with "sseq slots locks") as "X".
  iModIntro.
  iFrame. iPureIntro. intuition.
Qed.

Lemma z_n_add1 (i: nat)
  : ((LitV (Z.add i (Zpos xH))) = (LitV (Init.Nat.add i (S O)))). 
Proof.  f_equal. f_equal. lia. Qed.

Lemma wp_ht_update_iter 𝛾 range (slots locks: lang.val) (k: Key) (v: Value) (v0: option Value) (i: nat) :
      {{{
        ⌜ hash k ≤ i ≤ ht_fixed_size ⌝ ∗
        is_ht_sl 𝛾 slots locks ∗ L 𝛾 (m k v0) ∗ L 𝛾 range ∗ ⌜ full range k (hash k) i ⌝
        ∗ ⌜has_length slots ht_fixed_size /\ has_length locks ht_fixed_size⌝ 
      }}}
      update_iter slots locks #k #v #i
      {{{ b , RET (#b);
          ((⌜ b = 0 ⌝ ∗ L 𝛾 (m k v0)) ∨ (⌜ b = 1 ⌝ ∗ L 𝛾 (m k (Some v)))) ∗ L 𝛾 range
      }}}.
Proof.
  unfold update_iter.
  iRevert (i).
  iRevert (range).
  iLöb as "IH".
  iIntros (range i Phi) "[%i_bound [#ht [m [a [%isf %szs]]]]] Phi".
  wp_pures.
  
  unfold update_iter. wp_pures.
  have h : Decision (i = ht_fixed_size) by solve_decision. destruct h.
  
  (* case: i = fixed_size *)
  
  - subst i. 
    assert (bool_decide (#ht_fixed_size = #ht_fixed_size) = true) as bd.
    { unfold bool_decide. case_decide; crush. }
    rewrite bd.
    wp_pures.
    iModIntro.
    iApply ("Phi" $! 0). iFrame.
    iLeft. iFrame. iPureIntro. trivial.
    
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
    wp_bind (acquire_exc (elem locks i)).
    wp_apply (wp_acquire_exc (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) with "hti").
    iIntros (x) "[guard [cross %hti]]".
    unfold ht_inv_i in hti. destruct x. deex. destruct_ands. subst h. subst h0.
    iMod (CrossSplit _ _ _ _ with "cross") as "[slot mem]".
    
    wp_pures. 
    
    (* lookup slot ptr in sequence *)
    
    wp_bind (seq_idx #i slots).
    wp_apply wp_seq_idx.
    { apply has_elem_of_has_length with (len := ht_fixed_size).
      - lia. - intuition. } { done. }
    iIntros "_".
    
    (* read the slot *)
    
    rewrite ds.
    wp_apply (wp_load _ _ _ _ _ with "mem").
    iIntros "mem".
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
        wp_pures.
        
        wp_bind (seq_idx #i slots).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        rewrite ds.
        wp_store.
        
        wp_pures.
        
        wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        
        iMod (ht_UpdateExisting _ _ v _ _ _ with "slot m") as "[slot m]".
        iMod (CrossJoin _ _ _ _ with "slot mem") as "cross".
        
        (* release the lock *)

        wp_bind (release_exc (elem locks i)).
        wp_apply (wp_release_exc (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) _ with "[hti guard cross]").
        { iFrame. iFrame "#". iPureIntro. unfold ht_inv_i. exists (Some (k, v)).
          split; trivial. }
          
        iIntros. 
        wp_pures.
        
        iApply ("Phi" $! 1). iModIntro. iFrame.
        iRight. iFrame. iPureIntro. trivial.
        
      *
        (* case: the found key does not match - we have to recurse *)
        
        wp_pures.
        
        assert (bool_decide (#k = #k0) = false) as bd0.
        { rewrite bool_decide_decide. destruct (decide (#k = #k0)); trivial. crush. }
        rewrite bd0.
        
        iDestruct (L_join with "a slot") as "a'".

        wp_pure _.
        wp_pure _.
        replace (#true) with (#1) by trivial.
        replace (#false) with (#0) by trivial.
        full_generalize ((rec: "update_iter" "slots" "locks" "k" "v" "i" :=
                      if: BinOp EqOp "i" #ht_fixed_size then #0
                      else acquire_exc (seq_idx "i" "locks");; 
                           let: "ret" := let: "slot" := ! (seq_idx "i" "slots") in
                                         if: Fst "slot"
                                         then let: "k1" := Fst (Snd "slot") in
                                              let: "v1" := Snd (Snd "slot") in
                                              if: BinOp EqOp "k" "k1"
                                              then seq_idx "i" "slots" <- (#1, ("k", "v"));; 
                                                   #1
                                              else "update_iter" "slots" "locks" "k" "v"
                                                     ("i" + #1)
                                         else seq_idx "i" "slots" <- (#1, ("k", "v"));; #1 in
                           release_exc (seq_idx "i" "locks");; "ret")%V) as big_e.
                           
       wp_bind (big_e slots locks #k #v #(i + 1)).
       rewrite z_n_add1.
       wp_apply ("IH" $! (dot range (s i (Some (k0, v1)))) (i + 1) with "[m a']").
       {
          iSplitR. { iPureIntro. lia. }
          iSplitR. { iFrame "#". }
          iSplitL "m". { iFrame. }
          iSplitL "a'". { iFrame. }
          iSplitL. { iPureIntro. apply full_dot; trivial. crush. }
          iPureIntro. intuition.
       }
       
       iIntros (b) "[m a]".
       wp_pures.
       
       (* release the lock *)
       
       iDestruct (L_op _ _ _ with "a") as "[a slot]".
       iMod (CrossJoin _ _ _ _ with "slot mem") as "cross".
       
       wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
       iIntros.

       wp_apply (wp_release_exc (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) _ with "[hti guard cross]").
        { iFrame. iFrame "#". iPureIntro. unfold ht_inv_i. exists (Some (k0, v1)).
          split; trivial. }
       iIntros.
       
       wp_pures.
       iModIntro.
       
       iApply ("Phi" $! b). iFrame.
    
    
    + 
       (* case: the slot has nothing in it *)
       
       wp_pures.
     
       wp_bind (seq_idx #i slots).
       wp_apply wp_seq_idx.
       { apply has_elem_of_has_length with (len := ht_fixed_size).
         - lia. - intuition. } { done. }
       iIntros "_".
       
       wp_pures.
       rewrite ds.
       wp_store.
       wp_pures.
       
       iMod (ht_UpdateNew _ _ v _ _ _ with "a slot m") as "[a [slot m]]".
       { trivial. }
       
       (* release the lock *)
       
       wp_bind (seq_idx #i locks).
       wp_apply wp_seq_idx.
       { apply has_elem_of_has_length with (len := ht_fixed_size).
         - lia. - intuition. } { done. }
       iIntros "_".
       iMod (CrossJoin _ _ _ _ with "slot mem") as "cross".

       wp_bind (release_exc (elem locks i)).
       wp_apply (wp_release_exc (elem locks i) 𝛼 (cross_loc 𝛾 heap_name) (ht_inv_i i l) _ with "[hti guard cross]").
       { iFrame. iFrame "#". iPureIntro. unfold ht_inv_i. exists (Some (k, v)).
          split; trivial. }
          
       iIntros. 
       wp_pures.
        
       iApply ("Phi" $! 1). iModIntro. iFrame.
       iRight. iFrame. iPureIntro. trivial.
Qed.

Lemma wp_compute_hash (k: Key) :
      {{{ True }}}
      compute_hash #k
      {{{ RET #(hash k) ; True }}}. Admitted.

Lemma wp_ht_update 𝛾 (ht: lang.val) (k: Key) (v: Value) (v0: option Value) :
      {{{ is_ht 𝛾 ht ∗ L 𝛾 (m k v0) }}}
      update ht #k #v
      {{{ b , RET (#b);
          ((⌜ b = 0 ⌝ ∗ L 𝛾 (m k v0)) ∨ (⌜ b = 1 ⌝ ∗ L 𝛾 (m k (Some v))))
      }}}.
Proof.
  unfold update.
  iIntros (Phi) "[#ht l] Phi".
  
  iDestruct (destruct_ht with "ht") as "%ds". deex. subst ht.
  
  wp_pures.
  
  wp_bind (compute_hash #k).
  wp_apply (wp_compute_hash k). { done. }
  iIntros "_".
  
  iMod (L_unit HT 𝛾) as "u".
  
  wp_pures.
  
  wp_apply (wp_ht_update_iter 𝛾 unit slots locks k v v0 with "[l u]").
  {
    unfold is_ht.
    iDestruct "ht" as "[#iht %l]".
    iFrame. iFrame "#".
    iPureIntro. intuition.
    - assert (hash k < ht_fixed_size) by (apply hash_in_bound). lia. 
    - apply full_trivial.
  }
  
  iIntros (b) "[l a]". iApply "Phi". iFrame.
Qed.
     
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

(* due to the simplifications, update isn't guaranteed to succeed,
   so our spec for 'main' has to be that it either returns the value that was inserted,
   or nothing *)
Lemma wp_main :
  {{{ True }}} main #() {{{ v , RET v ; ⌜ v = (#true, #17)%V \/ v = (#false, #())%V ⌝ }}}.
Proof using HasRef0 HasTPCM0 HasTPCM1 simpGS0 Σ 𝜇.
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

End HashTableProof.
