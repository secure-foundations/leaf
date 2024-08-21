From iris.base_logic.lib Require Import invariants.
From lang Require Import lang simp adequacy primitive_laws.

From examples Require Import rwlock.
From examples Require Import rwlock_logic.
From guarding Require Import guard_later.
Require Import guarding.guard.
From examples Require Import seqs.
From examples Require Import hash_table_logic.
From examples Require Import hash_table_raw.
From lang Require Import heap_ra.
From examples Require Import misc_tactics.
From examples Require Import rwlock_logic.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import reduction.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import class_instances.
From iris.program_logic Require Import ectx_lifting.
From lang Require Import notation.

Definition compute_hash: lang.val :=
  λ: "x" ,
    BinOp ModuloOp "x" (#ht_fixed_size).
    
(** Constructor **)

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
    
(** Destructor **)

Definition free_slots: lang.val :=
  (rec: "free_slots" "slots" "n" :=
    if: (BinOp EqOp "n" #0) then
      #()
    else
      Free (Fst "slots") ;;
      ("free_slots" (Snd "slots") ("n" + #(-1)))
  )%V.
  
Definition free_locks: lang.val :=
  (rec: "free_locks" "locks" "n" :=
    if: (BinOp EqOp "n" #0) then
      #()
    else
      acquire_exc (Fst "locks") ;;
      free_rwlock (Fst "locks") ;;
      ("free_locks" (Snd "locks") ("n" + #(-1)))
  )%V.
    
Definition free_hash_table: lang.val :=
  λ: "ht" ,
    free_locks (Snd "ht") #(ht_fixed_size) ;;
    free_slots (Fst "ht") #(ht_fixed_size).
    
(** Query **)

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
    
(** Update **)
    
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
    
Section HashTableProof.

Context {Σ: gFunctors}.
Context `{@rwlock_logicG (option (Key * Value)) _ Σ}.
Context `{!simpGS Σ}.
Context {htl: ht_logicG Σ}.

Fixpoint seq_iprop (fn: nat -> iProp Σ) (n: nat) :=
  match n with
  | O => (True)%I
  | (S i) => (fn i ∗ seq_iprop fn i)%I
  end.

Lemma get_seq_iprop_guard (fn: nat -> iProp Σ) (n: nat) (i: nat) F
  (i_lt_n : i < n)
  : ⊢ (seq_iprop fn n &&{F}&&> fn i)%I.
Proof.
  induction n.
  - lia.
  - have h : Decision (i = n) by solve_decision. destruct h.
    + subst i. cbn [seq_iprop].
      apply guards_weaken_l.
    + assert (i < n) as iln by lia. intuition.
      cbn [seq_iprop].
      iApply (guards_transitive F _ (seq_iprop fn n) _).
      iSplitL.
      { iApply guards_weaken_r. }
      iApply H0.
Qed.

Lemma get_seq_iprop (fn: nat -> iProp Σ) (n: nat) (i: nat)
  (i_lt_n : i < n)
  : seq_iprop fn n ⊢ fn i.
 Proof.
   induction n.
   - lia.
   - have h : Decision (i = n) by solve_decision. destruct h.
    + subst i. cbn [seq_iprop]. iIntros "[x y]". iFrame.
    + assert (i < n) as iln by lia. intuition.
      cbn [seq_iprop]. iIntros "[x y]". iDestruct (H0 with "y") as "y". iFrame.
Qed.

Instance seq_iprop_persistent fn n (pi: ∀ i , Persistent (fn i)) : Persistent (seq_iprop fn n).
Proof.
  induction n.
  - apply _.
  - apply _.
Qed.

Instance seq_iprop_extractable fn n (pi: ∀ i , LaterGuardExtractable (fn i)) : LaterGuardExtractable (seq_iprop fn n).
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

Definition storage_fn (γ: gname) (i: nat) (l: loc) (slot: option (Key * Value)) : iProp Σ :=
    l ↦ slot_as_val slot ∗ own γ (s i slot).
  
Definition is_ht_i (γ: gname) (γrws: nat -> gname) (slots locks: lang.val) (i: nat) :=
  match (elem slots i) with
  | LitV (LitInt slot_loc) =>
      IsRwLock (γrws i) (elem locks i) (storage_fn γ i slot_loc)
  | _ => (False)%I
  end
.
  
Definition is_ht_sl (γ: gname) (γrws: nat -> gname) (slots locks: lang.val) :=
  seq_iprop (is_ht_i γ γrws slots locks) ht_fixed_size.
  
Instance is_ht_i_extractable (γ: gname) (γrws: nat -> gname)
    (slots locks: lang.val) (i: nat) : LaterGuardExtractable (is_ht_i γ γrws slots locks i).
Proof.
  unfold is_ht_i.
  destruct (elem slots i); try typeclasses eauto.
  destruct l; try typeclasses eauto.
Qed.
  
Instance is_ht_sl_extractable (γ: gname) (γrws: nat -> gname)
    (slots locks: lang.val) : LaterGuardExtractable (is_ht_sl γ γrws slots locks).
Proof.
  apply seq_iprop_extractable.
  intro. apply is_ht_i_extractable.
Qed.

Definition HT_RW_NAMESPACE := nroot .@ "ht-rwlock".

Definition is_ht (γ: gname) (γrws: nat -> gname) (ht: lang.val) :=
  match ht with
  | PairV slots locks => (is_ht_sl γ γrws slots locks
      ∗ ⌜has_length slots ht_fixed_size /\ has_length locks ht_fixed_size
          /\ (∀ i , γrws i ∈ (↑ HT_RW_NAMESPACE : coPset)) ⌝
      )%I
  | _ => (False)%I
  end.
  
Instance is_ht_extractable γ γrws ht : LaterGuardExtractable (is_ht γ γrws ht).
Proof.
  unfold is_ht.
  destruct ht; try apply _.
Qed.

Lemma destruct_slots_i γ γrws slots locks i
  : is_ht_i γ γrws slots locks i -∗ ⌜ ∃ (l: Z) , elem slots i = #l ⌝.
Proof.
  iIntros "ih". unfold is_ht_i. destruct (elem slots i).
  - destruct l.
    + iPureIntro. exists n. trivial.
    + iExFalso. iFrame.
  - iExFalso. iFrame.
  - iExFalso. iFrame.
Qed.

Lemma guarded_destruct_slots_i g E F γ γrws slots locks i
  (su: F ⊆ E)
  : ⊢ g ∗ (g &&{F}&&> is_ht_i γ γrws slots locks i)
    ={E}=∗ g ∗ ⌜ ∃ (l: Z) , elem slots i = #l ⌝.
Proof.
  iIntros "[g guards]".
  iApply (guards_persistent g (is_ht_i γ γrws slots locks i) _ E F); trivial.
  iFrame.
  iApply destruct_slots_i.
Qed.

Lemma destruct_ht γ γrws ht
  : is_ht γ γrws ht -∗ ⌜ ∃ slots locks , ht = PairV slots locks
    /\ 
    has_length slots ht_fixed_size /\ has_length locks ht_fixed_size
          /\ (∀ i , γrws i ∈ (↑ HT_RW_NAMESPACE : coPset)) ⌝.
Proof.
  iIntros "ih". unfold is_ht. destruct ht.
  - iExFalso. iFrame.
  - iExFalso. iFrame.
  - iDestruct "ih" as "[a %b]".
  iPureIntro. exists ht1, ht2. intuition.
Qed.

Lemma guarded_destruct_ht g E F γ γrws ht
  (su: F ⊆ E)
  : ⊢ g ∗ (g &&{F}&&> is_ht γ γrws ht)
    ={E}=∗ g ∗ ⌜ ∃ slots locks , ht = PairV slots locks
    /\ has_length slots ht_fixed_size /\ has_length locks ht_fixed_size
          /\ (∀ i , γrws i ∈ (↑ HT_RW_NAMESPACE : coPset)) ⌝.
Proof.
  iIntros "[g guards]".
  iApply (guards_persistent g (is_ht γ γrws ht) _ E F); trivial.
  iFrame.
  iApply destruct_ht.
Qed.


Lemma guarded_inner_ht g F γ γrws slots locks
  : (g &&{F}&&> is_ht γ γrws (PairV slots locks))
    ⊢ (g &&{F}&&> is_ht_sl γ γrws slots locks).
Proof.
  unfold is_ht.
  apply guards_weaken_rhs_l.
Qed.

Lemma guard_is_ht_i g F γ γrws slots locks (i: nat)
  (lt: i < ht_fixed_size)
  :
  (g &&{ F }&&> is_ht_sl γ γrws slots locks)%I ⊢
    (g &&{ F }&&> is_ht_i γ γrws slots locks i)%I.
Proof.
  iIntros "guard". unfold is_ht_sl.
  iDestruct (get_seq_iprop_guard (is_ht_i γ γrws slots locks) ht_fixed_size i F)
      as "guard2"; trivial.
  iDestruct (guards_transitive with "[guard guard2]") as "j".
  { iSplitL "guard". - iFrame "guard". - iFrame "guard2". }
  iFrame "j".
Qed.

Definition is_slot_i (slots: lang.val) (i: nat) :=
  match (elem slots i) with
  | LitV (LitInt l) => (l ↦ slot_as_val None)%I
  | _ => (False) % I
  end.
  
Definition is_slot_i_at_exit (slots: lang.val) (i: nat) :=
  match (elem slots i) with
  | LitV (LitInt l) => (∃ s , l ↦ s)%I
  | _ => (False) % I
  end.

Lemma seq_iprop_is_slot_i_extend (n: nat) slots (slot_ref: Z) :
  ⊢ seq_iprop (is_slot_i slots) n -∗
      (slot_ref ↦ (#0, #())%V)%I
      -∗
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

Lemma seq_iprop_is_slot_i_pop (n: nat) slots (slot_ref: lang.val) :
  seq_iprop (is_slot_i_at_exit (slot_ref, slots)) (S n) ⊢
      (seq_iprop (is_slot_i_at_exit slots) n) ∗ (∃ (s: lang.val) (l: Z) , ⌜ slot_ref = #l ⌝ ∗ l ↦ s)%I.
Proof.
  induction n.
  - iIntros "s". unfold seq_iprop. unfold is_slot_i_at_exit. unfold elem.
    iDestruct "s" as "[s t]". iFrame.
    destruct slot_ref.
    + destruct l. ++ iDestruct "s" as (s) "x". iExists s. iExists n. iSplitR.
        { iPureIntro. trivial. } iFrame.
        ++ iExFalso. iFrame.
    + iExFalso. iFrame.
    + iExFalso. iFrame.
  - iIntros "s". cbn [seq_iprop].
    cbn [seq_iprop] in IHn.
    iDestruct "s" as "[a b]".
    iDestruct (IHn with "b") as "[b c]".
    iFrame.
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

Lemma has_length_of_has_elem l0 r n
  (hl : has_elem (#l0, r) n) : has_length r n. 
Proof.
  cbn [has_elem] in hl. destruct n. - trivial. - unfold has_length. trivial.
Qed.

Lemma wp_free_slots (n: nat) slots :
      {{{ seq_iprop (is_slot_i_at_exit slots) n ∗ ⌜ has_length slots n ⌝ }}}
      free_slots slots #n
      {{{ RET #(); True }}}.
Proof using H htl simpGS0 Σ.
  generalize slots. clear slots. induction n.
  - intro slots. unfold free_slots. iIntros (Phi) "t Phi". wp_pures.
    iModIntro. iApply "Phi". done.
  - intro slots. unfold free_slots. iIntros (Phi) "t Phi".
    wp_pure _. wp_pure _. wp_pure _. wp_pure _.
    wp_pure _.
    iDestruct "t" as "[t %hl]".
    unfold has_length in hl.
    assert (∃ l r , slots = PairV l r) as X.
    { 
      destruct slots.
      - unfold has_elem in hl. destruct n; contradiction.
      - unfold has_elem in hl. destruct n; contradiction.
      - exists slots1, slots2. trivial.
    }
    destruct X as [l [r X]]. subst slots.
    iDestruct (seq_iprop_is_slot_i_pop with "t") as "[x y]".
    iDestruct "y" as (s l0) "[%k z]".
    subst l.
    wp_pure _.
    wp_apply (wp_free _ with "z"). iIntros.
    wp_pure _. wp_pure _. wp_pure _. wp_pure _.
    unfold free_slots in IHn.
    replace (LitV ((Z.add (S n) (Zneg xH)))) with (LitV n) by (f_equal; f_equal; lia).
    replace (#false) with (#0) in IHn by trivial.
    full_generalize (rec: "free_slots" "slots" "n" :=
        if: BinOp EqOp "n" #0 then #()
        else Free (Fst "slots");; "free_slots" (Snd "slots") ("n" + #(-1)))%V as big_e.
    wp_apply (IHn with "[x]").
    { iSplitL. { iFrame. } iPureIntro. unfold has_length.
    apply (has_length_of_has_elem _ _ _ hl). }
    iFrame.
Qed.

Definition is_lock_i (locks: lang.val) (i: nat) :=
  match (elem locks i) with
  | PairV (LitV (LitInt l1)) (LitV (LitInt l2)) => (l1 ↦ #0 ∗ l2 ↦ #0)%I
  | _ => (False) % I
  end.
  
Lemma seq_iprop_is_lock_i_extend (n: nat) locks (lock_ref1 lock_ref2 : Z) :
  ⊢ seq_iprop (is_lock_i locks) n -∗
      (lock_ref1 ↦ (#0)%V) -∗
      (lock_ref2 ↦ (#0)%V) -∗
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

Definition is_lock_i_at_exit (slots: lang.val) (γ: gname) (γrws : nat -> gname) (locks: lang.val) (k: nat) (i: nat) : iProp Σ :=
  ⌜ k ≤ i ⌝ -∗ 
  ∃ l , ⌜ elem slots i = LitV (LitInt l) ⌝ ∗ (
      IsRwLock (γrws i) (elem locks (i-k)%nat) (storage_fn γ i l)
  ).
  
(*Definition is_lock_i_at_exit_except (slots: lang.val) (γ: gname) (γrws : nat -> gname) (locks: lang.val) (k: nat) (i: nat) : iProp Σ :=
  ⌜ k < i ⌝ -∗
  ∃ l , ⌜ elem slots i = LitV (LitInt l) ⌝ ∗ (
      IsRwLock (γrws i) (elem locks (i-k)%nat) (storage_fn γ i l)
  ).*)
  
  
Lemma seq_iprop_entails (fn1 fn2 : nat -> iProp Σ) (n: nat)
    (cond: ∀ (i: nat) , i < n -> fn1 i ⊢ fn2 i)
    : seq_iprop fn1 n ⊢ seq_iprop fn2 n.
Proof.
  induction n.
  - trivial.
  - cbn [seq_iprop]. iIntros "[f si]".
    iDestruct (cond with "f") as "f". { lia. }
    iDestruct (IHn with "si") as "si". { intros. apply cond. lia. }
    iFrame.
Qed.

Lemma seq_iprop_peel_mid (f g: nat -> iProp Σ) (n: nat) (j: nat)
    (j_lt_n: j < n)
    (fi: ∀ i , (0 ≤ i < n)%nat -> (i ≠ j) -> (f i ⊢ g i))
    (gi: True ⊢ g j)
    : seq_iprop f n ⊢ (seq_iprop g n) ∗ (f j).
Proof.
  induction n. { lia. }
  cbn [seq_iprop].
  have h : Decision (j = n) by solve_decision. destruct h.
  + subst j. iIntros "[f s]". iSplitL "s".
    { iSplitR. { iApply gi. done. }
        iApply (seq_iprop_entails with "s").
        intros. apply fi. { lia. } lia. }
    iFrame.
  + iIntros "[f s]". iDestruct (IHn with "s") as "[r m]". { lia. } { intuition. }
    iFrame. iApply fi. { lia. } { lia. } iFrame.
Qed.

Lemma wp_free_locks (slots: lang.val) (γ: gname) (γrws : nat -> gname) (locks: lang.val) (k: nat) (n: nat)
  (k_le_n: (k ≤ n)%nat) :
      {{{ seq_iprop (is_lock_i_at_exit slots γ γrws locks (n-k)%nat) n
        ∗ seq_iprop (is_slot_i_at_exit slots) (n-k)%nat
        ∗ ⌜ has_length locks k ⌝
      }}}
      free_locks locks #(k)
      {{{ RET #();
        seq_iprop (is_slot_i_at_exit slots) n
      }}}.
Proof.
  generalize locks. clear locks. induction k.
  - intro locks. iIntros (Phi) "[x [t r]] Phi". unfold free_locks. wp_pures. iModIntro.
    iApply "Phi". replace (n-0)%nat with n by lia. iFrame.
  - intro locks. iIntros (Phi) "[s [t %hl]] Phi".
    unfold free_locks.
    Opaque free_rwlock.
    wp_pure _. wp_pure _. wp_pure _. wp_pure _.
    wp_pure _.
    
    assert (∃ l r , locks = PairV l r) as X.
    { 
      unfold has_length in hl.
      destruct locks.
      - unfold has_elem in hl. destruct k; contradiction.
      - unfold has_elem in hl. destruct k; contradiction.
      - exists locks1, locks2. trivial.
    }
    destruct X as [l [r X]].
    
    iDestruct (seq_iprop_peel_mid 
        (is_lock_i_at_exit slots γ γrws locks (n - S k))
        (is_lock_i_at_exit slots γ γrws r (n - k)) n (n - S k)%nat with "s") as "[s p]".
    { lia. }
    { intros i W Y. iIntros "a".  unfold is_lock_i_at_exit. iIntros "%nki".
      iAssert (⌜(n - S k)%nat ≤ i⌝)%I as "J". { iPureIntro. lia. }
      iDestruct ("a" with "J") as (l0) "[%b a]". iExists l0. iSplitR.
      { iPureIntro. trivial. }
      subst locks.
      replace ((i - (n - S k)))%nat with (S (i - (n - k)))%nat by lia.
      cbn [elem]. iFrame.
    }
    { iIntros "t". unfold is_lock_i_at_exit. iIntros "%w". exfalso. lia. }
    
    subst locks.
    wp_pure _.
    unfold is_lock_i_at_exit at 2.
    iAssert (⌜(n - S k)%nat ≤ (n - S k)%nat⌝)%I as "X". { iPureIntro. lia. }
    iDestruct ("p" with "X") as (l0) "[%e p]".
    replace ((n - S k - (n - S k)))%nat with 0%nat by lia.
    cbn [elem].
    iDestruct (guards_refl ∅ (IsRwLock (γrws (n - S k)%nat) l (storage_fn γ (n - S k) l0))) as "g".
    wp_apply (wp_acquire_exc (γrws (n - S k)%nat) _ (IsRwLock (γrws (n - S k)%nat) l (storage_fn γ (n - S k) l0)) _ ∅ with "[p g]").
    { set_solver. }
    { iFrame. iFrame "g". }
    iIntros (x) "[r [gua sf]]".
    
    wp_pures.
    wp_apply (wp_free_rwlock with "r"). iIntros.
    wp_pure _.
    wp_pure _.
    wp_pure _.
    wp_pure _.
    unfold free_locks in IHk.
    replace (LitV ((Z.add (S k) (Zneg xH)))) with (LitV k) by (f_equal; f_equal; lia).
    full_generalize (rec: "free_locks" "locks" "n" :=
        if: BinOp EqOp "n" #0 then #()
        else acquire_exc (Fst "locks");; 
             free_rwlock (Fst "locks");; "free_locks" (Snd "locks") ("n" + #(-1)))%V as big_e.
    wp_apply (IHk with "[t s gua sf]").
    { lia. }
    { iFrame. iSplitL. { replace (n - k)%nat with (S ( n - S k))%nat by lia. 
        cbn [seq_iprop]. iFrame. unfold storage_fn. unfold is_slot_i_at_exit.
        rewrite e. iExists (slot_as_val x). iDestruct "sf" as "[sf1 sf2]".
        iFrame. }
    { iPureIntro. unfold has_length. unfold has_length in hl. destruct k; trivial. } }
    iFrame.
Qed.


Lemma init_is_ht_sl γ slots locks :
  own γ (sseq ht_fixed_size) -∗
  seq_iprop (is_slot_i slots) ht_fixed_size -∗
  seq_iprop (is_lock_i locks) ht_fixed_size
  ={⊤}=∗ ∃ γrws , ⌜ (∀ i , γrws i ∈ (↑ HT_RW_NAMESPACE : coPset)) ⌝
      ∗ is_ht_sl γ γrws slots locks.
Proof.
  unfold is_ht_sl. full_generalize ht_fixed_size as n. induction n.
  - iIntros. iExists (λ i , coPpick (↑HT_RW_NAMESPACE)). iModIntro.
    iSplitL "".
    { iPureIntro. intro. apply coPpick_elem_of. apply nclose_infinite. }
    trivial.
  - iIntros "L slots locks".
    rewrite sseq_append.
    cbn [seq_iprop].
    iDestruct "slots" as "[slot slots]".
    iDestruct "locks" as "[lock locks]".
    iDestruct (own_op with "L") as "[L me]".
    
    iMod (IHn with "L slots locks") as (γrws) "[%ns X]".
    
    unfold is_ht_i.
    unfold is_slot_i.
    unfold is_lock_i.
    destruct (elem slots n); try (iExFalso; iFrame; fail).
    destruct l; try (iExFalso; iFrame; fail).
    destruct (elem locks n); try (iExFalso; iFrame; fail).
    destruct v1; try (iExFalso; iFrame; fail).
    destruct l; try (iExFalso; iFrame; fail).
    destruct v2; try (iExFalso; iFrame; fail).
    destruct l; try (iExFalso; iFrame; fail).

    iMod (rw_new_ns None (storage_fn γ n n0) ⊤ HT_RW_NAMESPACE with "[slot me]") as (γi) "[%in_ns [maps rwcentral]]".
    { unfold storage_fn. iFrame. }
    
    iModIntro.
    iExists (λ i , if decide (i = n) then γi else γrws i).
    
    iSplitL "".
    {
      iPureIntro. intro.
      case_decide; trivial.
    }
    
    iSplitL "lock maps rwcentral".
    {
      case_decide; try contradiction.
      unfold IsRwLock, rw_lock_inst, rw_atomic_inv. iFrame "maps".
      iExists false, 0, None.
      iFrame.
    }
    iDestruct (seq_iprop_entails with "X") as "X".
    2: { iFrame "X". }
    intros i lt. iIntros "m".
    
    case_decide. { lia. }
    iFrame "m".
Qed.

Lemma wp_new_hash_table (maxkey: nat) :
      {{{ True }}}
      new_hash_table #()
      {{{ γ γrws ht , RET ht; is_ht γ γrws ht ∗ own γ (mseq maxkey) }}}.
Proof.
  iIntros (Phi) "t Phi".
  unfold new_hash_table.
  wp_pures.
  wp_apply wp_init_slots. { done. } iIntros (slots) "[slots %hl_slots]".
  wp_apply wp_init_locks. { done. } iIntros (locks) "[locks %hl_locks]".
  wp_pures.
  iMod (ht_Init maxkey) as (γ) "[mseq sseq]".
  unfold is_ht.
  iMod (init_is_ht_sl with "sseq slots locks") as (γrws) "[%inns X]".
  iApply ("Phi" $! (γ) (γrws)).
  iModIntro.
  iFrame. iPureIntro. intuition.
Qed.

Lemma wp_free_hash_table γ γrws ht :
        {{{ is_ht γ γrws ht }}}
        free_hash_table ht
        {{{ RET #(); True }}}.
Proof.
  unfold free_hash_table. iIntros (Phi) "ht Phi".
  wp_pures.
  iDestruct (destruct_ht with "ht") as "%j".
  destruct j as [slots [locks [eq [hl1 [hl2 hl3]]]]].
  subst ht.
  wp_pures.
  unfold is_ht.
  iDestruct "ht" as "[ht _]".
  unfold is_ht_sl.
  wp_apply (wp_free_locks slots γ γrws locks ht_fixed_size ht_fixed_size with "[ht]").
  { trivial. }
  { iSplitL "ht".
    { iApply (seq_iprop_entails with "ht"). iIntros (i w) "t".
      unfold is_ht_i.
      destruct (elem slots i) eqn:q.
      - destruct l.
        + unfold is_lock_i_at_exit. iIntros "_". iExists n. iSplitR.
          { iPureIntro. trivial. } 
          replace (i - (ht_fixed_size - ht_fixed_size))%nat with i%nat by lia.
          iFrame.
        + iExFalso. iFrame.
      - iExFalso. iFrame.
      - iExFalso. iFrame.
    }
    replace (ht_fixed_size - ht_fixed_size)%nat with 0%nat by lia.
    unfold seq_iprop. iSplitL. { done. } iPureIntro. trivial.
  }
  iIntros "j".
  wp_pures.
  wp_apply (wp_free_slots with "[j]").
  { iSplitL. { iFrame. } iPureIntro. trivial. }
  iIntros. iApply "Phi". done.
Qed.

Lemma z_n_add1 (i: nat)
  : ((LitV (Z.add i (Zpos xH))) = (LitV (Init.Nat.add i (S O)))). 
Proof.  f_equal. f_equal. lia. Qed.

Lemma wp_ht_update_iter γ γrws range (slots locks: lang.val) (k: Key) (v: Value) (v0: option Value) (i: nat) (g: iProp Σ) F
  (not_in: ∀ i , γrws i ∉ F)
:
      {{{
        ⌜ (hash k ≤ i ≤ ht_fixed_size)%nat ⌝ ∗
        g ∗ ((g &&{F}&&> is_ht_sl γ γrws slots locks)) ∗
        own γ (m k v0) ∗ own γ range ∗ ⌜ full range k (hash k) i ⌝
        ∗ ⌜has_length slots ht_fixed_size /\ has_length locks ht_fixed_size⌝ 
      }}}
      update_iter slots locks #k #v #i
      {{{ b , RET (#b);
          g ∗ ((⌜ b = 0 ⌝ ∗ own γ (m k v0)) ∨ (⌜ b = 1 ⌝ ∗ own γ (m k (Some v)))) ∗ own γ range
      }}}.
Proof.
  unfold update_iter.
  iRevert (i).
  iRevert (range).
  iLöb as "IH".
  iIntros (range i Phi) "[%i_bound [g [#ht [m [a [%isf %szs]]]]]] Phi".
  (*iMod (extract_later g (is_ht_sl γ γrws slots locks) _ F with "[g ht_later]") as "[g #ht]". { set_solver. }
    { iFrame "g". iFrame "ht_later". }*)
  wp_pures.
  
  unfold update_iter. wp_pures.
  have h : Decision (i = ht_fixed_size) by solve_decision. destruct h.
  
  (* case: i = fixed_size *)
  
  - subst i. 
    assert (bool_decide (#ht_fixed_size = #ht_fixed_size) = true) as bd.
    { unfold bool_decide. case_decide; trivial. contradiction. }
    rewrite bd.
    wp_pures.
    iModIntro.
    iApply ("Phi" $! 0). iFrame.
    iLeft. iFrame. iPureIntro. trivial.
    
  (* case: i < fixed_size *)
  
  - 
    iDestruct (guard_is_ht_i _ _ _ _ _ _ i with "ht") as "rw". { lia. }
  
    assert (bool_decide (#i = #ht_fixed_size) = false) as bd.
    { unfold bool_decide. case_decide; trivial. inversion H0. lia. }
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
    
    iMod (guarded_destruct_slots_i g ⊤ F with "[g rw]") as "[g %ds]".  { set_solver. }
    { iFrame "g". iFrame "rw". }
    destruct ds as [l ds].
    unfold is_ht_i. rewrite ds.
    wp_bind (acquire_exc (elem locks i)).
    wp_apply (wp_acquire_exc (γrws i) (elem locks i) g (storage_fn γ i l) F with "[g rw]").
    { apply not_in. } { iFrame "g". iFrame "rw". }
    iIntros (x) "[g [guard sf]]".
    iDestruct "sf" as "[mem os]".
    
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
    
    destruct x.
    
    + (* case: the slot has something in it *)
    
      unfold slot_as_val. destruct p as [k0 v1]. wp_pures.
      
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
        
        iMod (ht_UpdateExisting _ _ v _ _ _ with "os m") as "[os m]".
        
        (* release the lock *)

        wp_bind (release_exc (elem locks i)).
        wp_apply (wp_release_exc (γrws i) (elem locks i) g (storage_fn γ i l) F (Some (k, v)) with "[g rw mem os guard]"). { apply not_in. }
        { iFrame "g". iFrame "#". iFrame "guard".
            unfold storage_fn. iFrame. }
          
        iIntros. 
        wp_pures.
        
        iApply ("Phi" $! 1). iModIntro. iFrame.
        iRight. iFrame. iPureIntro. trivial.
        
      *
        (* case: the found key does not match - we have to recurse *)
        
        wp_pures.
        
        assert (bool_decide (#k = #k0) = false) as bd0.
        { rewrite bool_decide_decide. destruct (decide (#k = #k0)); trivial. inversion e. subst k. contradiction. }
        rewrite bd0.
        
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
       wp_apply ("IH" $! (range ⋅ (s i (Some (k0, v1)))) (i + 1)%nat with "[g m a os]").
       {
          iFrame. iFrame "#".
          rewrite own_op. iFrame.
          iPureIntro. split. { lia. }
          split.
          { apply full_dot; trivial. symmetry. trivial. }
          intuition.
       }
       
       iIntros (b) "[g [m a]]".
       wp_pures.
       
       (* release the lock *)
       
       iDestruct (own_op _ _ _ with "a") as "[a slot]".
       
       wp_bind (seq_idx #i locks).
       wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
       iIntros.

       wp_apply (wp_release_exc (γrws i) (elem locks i) g (storage_fn γ i l) F (Some (k0, v1)) with "[g rw mem slot guard]"). { apply not_in. }
        { iFrame. iFrame "#". }
        
       iIntros "g".
       
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
       
       iMod (ht_UpdateNew _ _ v _ _ _ with "os m a") as "[slot [m a]]".
       { trivial. }
       
       (* release the lock *)
       
       wp_bind (seq_idx #i locks).
       wp_apply wp_seq_idx.
       { apply has_elem_of_has_length with (len := ht_fixed_size).
         - lia. - intuition. } { done. }
       iIntros "_".

       wp_bind (release_exc (elem locks i)).
       wp_apply (wp_release_exc (γrws i) (elem locks i) g (storage_fn γ i l) F (Some (k, v)) with "[g rw mem slot guard]"). { apply not_in. }
        { iFrame "g". iFrame "#". iFrame "guard".
            unfold storage_fn. iFrame. }
          
       iIntros. 
       wp_pures.
        
       iApply ("Phi" $! 1). iModIntro. iFrame.
       iRight. iFrame. iPureIntro. trivial.
Qed.

Lemma wp_compute_hash (k: Key) :
      {{{ True }}}
      compute_hash #k
      {{{ RET #(hash k) ; True }}}.
Proof.
  iIntros (Phi) "_ Phi".
  unfold compute_hash.
  wp_pures.
  iModIntro.
  assert (#(hash k) = #(k `mod` ht_fixed_size)) as X.
  {
    f_equal. unfold hash. f_equal.
    have j := Z_mod_lt k ht_fixed_size.
    unfold ht_fixed_size in *.
    lia.
  }
  rewrite X.
  iApply "Phi".
  done.
Qed. 

Lemma wp_ht_update γ γrws (ht: lang.val) (k: Key) (v: Value) (v0: option Value) g F
  (F_disj: F ## ↑ HT_RW_NAMESPACE)
  :
      {{{ g ∗ ((g &&{F}&&> is_ht γ γrws ht)) ∗ own γ (m k v0) }}}
      update ht #k #v
      {{{ b , RET (#b); g ∗
          ((⌜ b = 0 ⌝ ∗ own γ (m k v0)) ∨ (⌜ b = 1 ⌝ ∗ own γ (m k (Some v))))
      }}}.
Proof.
  unfold update.
  iIntros (Phi) "[g [#guard o]] Phi".

  iMod (guarded_destruct_ht g ⊤ F γ γrws ht with "[guard g]") as "[g %ds]".
  { set_solver. }
  { iFrame "g". iFrame "guard". }
  destruct ds as [slots [locks [ds [l1 [l2 all_in_ns]]]]].
  subst ht.
  
  wp_pures.
  
  wp_bind (compute_hash #k).
  wp_apply (wp_compute_hash k). { done. }
  iIntros "_".
  
  iMod (own_unit htUR γ) as "u".
  
  wp_pures.
  
  iDestruct (guarded_inner_ht with "guard") as "guard2".
  
  wp_apply (wp_ht_update_iter γ γrws ε slots locks k v v0 _ g F with "[o g u]").
  { set_solver. }
  {
    iFrame. iFrame "#".
    iPureIntro. intuition.
    - assert (hash k < ht_fixed_size)%nat by (apply hash_in_bound). lia. 
    - apply full_trivial.
  }
  
  iIntros (b) "[l [a o]]". iApply "Phi". iFrame.
Qed.

Lemma wp_ht_query_iter γ γrws range (slots locks: lang.val) (k: Key) (v: option Value) (i: nat) (g gm gr: iProp Σ) F
  (F_disj: F ## ↑ HT_RW_NAMESPACE)
  (is_in: ∀ i , γrws i ∈ (↑HT_RW_NAMESPACE : coPset))
  :
      {{{
        ⌜ (hash k ≤ i ≤ ht_fixed_size)%nat ⌝
        ∗ g ∗ ((g &&{F}&&> is_ht_sl γ γrws slots locks))
        ∗ gr ∗ ((gr &&{↑HT_RW_NAMESPACE}&&> own γ range))
        ∗ gm ∗ ((gm &&{⊤}&&> own γ (m k v)))
        ∗ ⌜ full range k (hash k) i ⌝
        ∗ ⌜has_length slots ht_fixed_size /\ has_length locks ht_fixed_size⌝ 
      }}}
      query_iter slots locks #k #i
      {{{ RET (opt_as_val v); g ∗ gr ∗ gm }}}.
Proof.
  unfold query_iter.
  iRevert (i).
  iRevert (range).
  iRevert (gr).
  iLöb as "IH".
  iIntros (gr range i Phi) "[%i_bound [g [#ht [gr [#guardr [gm [#guardm [%isf %szs]]]]]]]] Phi".
  iDestruct (ht_BorrowedRangeAddM with "guardr guardm") as "guardrm". { apply isf. }
  replace (↑HT_RW_NAMESPACE ∪ ⊤) with (⊤: coPset) by set_solver.
  wp_pures.
  
  unfold query_iter. wp_pures.
  have h : Decision (i = ht_fixed_size) by solve_decision. destruct h.
  
  (* case: i = fixed_size *)
  
  - subst i. 
    assert (bool_decide (#ht_fixed_size = #ht_fixed_size) = true) as bd.
    { unfold bool_decide. case_decide; trivial. contradiction. }
    rewrite bd.
    wp_pures.
    iMod (ht_QueryReachedEnd_b γ range k v (gr ∗ gm) ⊤ ⊤ with "[gm gr guardrm]") as "[[gr gm] %is_none]". 
    { set_solver. } { trivial. } { iFrame "gm". iFrame "gr". iFrame "guardrm". }
    
    rewrite is_none.
    
    unfold opt_as_val. iModIntro.
    iApply "Phi". iFrame.
  
  (* case: i < fixed_size *)
  
  - 
    iDestruct (guard_is_ht_i _ _ _ _ _ _ i with "ht") as "rw". { lia. }
  
    assert (bool_decide (#i = #ht_fixed_size) = false) as bd.
    { unfold bool_decide. case_decide; trivial. inversion H0. lia. }
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
    
    iMod (guarded_destruct_slots_i g ⊤ F with "[g rw]") as "[g %ds]".  { set_solver. }
    { iFrame "g". iFrame "rw". }
    destruct ds as [l ds].
    unfold is_ht_i. rewrite ds.
    
    wp_bind (acquire_shared (elem locks i)).
    wp_apply (wp_acquire_shared (γrws i) (elem locks i) g (storage_fn γ i l) F with "[g rw]").
    { set_solver. } { iFrame "g". iFrame "rw". }
    
    iIntros (slot) "[g [sh_guard #guard_storage_lat]]".
    
    wp_pures. 
    
    (* lookup slot ptr in sequence *)
    
    wp_bind (seq_idx #i slots).
    wp_apply wp_seq_idx.
    { apply has_elem_of_has_length with (len := ht_fixed_size).
      - lia. - intuition. } { done. }
    iIntros "_".
    
    (* unpack all the stuff from the sh_guard *)
    
    iDestruct (guards_remove_later2 with "guard_storage_lat") as "guard_storage".
    unfold storage_fn at 3.
    iDestruct (guards_weaken_rhs_l with "guard_storage") as "guard_mem".
    iDestruct (guards_weaken_rhs_r with "guard_storage") as "guard_own_slot".
    
    (* read the slot *)
    
    rewrite ds.
    wp_apply (wp_load_b _ ⊤ l (slot_as_val slot) {[γrws i]} (sh_guard (γrws i) slot) with "[sh_guard guard_own_slot]").
    { set_solver. }
    { iFrame "sh_guard". iFrame "guard_mem". }
    
    iIntros "sh_guard".
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
        
        iDestruct (ht_SAddM with "guard_own_slot guardm") as "guard_s_m".
        replace ({[γrws i]} ∪ ⊤) with (⊤ : coPset) by set_solver.
        
        iMod (ht_QueryFound_b γ i k v0 v (sh_guard (γrws i) (Some (k, v0)) ∗ gm) ⊤ with "[sh_guard gm guard_s_m]") as "[[sh_guard gm] %veq]".
        { set_solver. }
        { iFrame "sh_guard". iFrame "gm". iFrame "guard_s_m". }
        rewrite veq.
        
        (* release lock *)
        
        wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        
        wp_bind (release_shared (elem locks i)).
        wp_apply (wp_release_shared (γrws i) (elem locks i) g (storage_fn γ i l) F (Some (k, v0)) with "[g rw sh_guard]").
        { set_solver. }
        { iFrame. iFrame "#". }
        iIntros (dummy) "g".
        
        wp_pures.
        unfold opt_as_val.
        iApply "Phi". iModIntro. iFrame.
        
      *
        (* case: the found key does not match - we have to recurse *)
        
        wp_pures.
        
        assert (bool_decide (#k = #k0) = false) as bd0.
        { rewrite bool_decide_decide. destruct (decide (#k = #k0)); trivial. inversion e. subst k. contradiction. }
        rewrite bd0.

        iDestruct (ht_BorrowedRangeAppend γ range k (hash k) i k0 v0
            gr (sh_guard (γrws i) (Some (k0, v0)))
            (↑HT_RW_NAMESPACE) ({[γrws i]})
            with "[guardr guard_own_slot]") as (r') "[%f' guardr2]".
        { symmetry. trivial. }
        { trivial. }
        { iFrame "guardr". iFrame "guard_own_slot". }
        replace (↑HT_RW_NAMESPACE ∪ {[γrws i]})
            with (↑HT_RW_NAMESPACE : coPset) by set_solver.
        
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
       wp_apply ("IH" $! (gr ∗ sh_guard (γrws i) (Some (k0, v0)))%I (r') (i + 1)%nat with "[gr sh_guard g gm]").
       {
          iFrame. iFrame "ht". iFrame "guardm". iFrame "guardr2".
          iPureIntro. split.
          { lia. }
          split.
          { trivial. }
          split.
          { intuition. }
          intuition.
       }
       iIntros "[g [[gr sh_guard] gm]]".
       
       (* release the lock *)
       
        wp_pure _.
        wp_pure _.
        
        wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        
        wp_bind (release_shared (elem locks i)).
        wp_apply (wp_release_shared (γrws i) (elem locks i) g (storage_fn γ i l) F (Some (k0, v0)) with "[rw g sh_guard]").
        { set_solver. }
        { iFrame. iFrame "#". }
        iIntros (dummy) "g".
        
        wp_pures.
        
        iModIntro. iApply ("Phi" with "[g gr gm]"). { iFrame. }
    +
        (* case: the slot has nothing in it *)
        
        wp_pure _.
        wp_pure _.
        wp_pure _.
        wp_pure _.
        
        (* get the answer using the borrowed props *)
        
        iDestruct (ht_RangeAddSAddM with "guardr guard_own_slot guardm") as "guard_s_m".
        { apply isf. }
        replace (↑HT_RW_NAMESPACE ∪ {[γrws i]} ∪ ⊤) with (⊤ : coPset) by set_solver.
        
        iMod (ht_QueryNotFound_b γ range k v i (gr ∗ sh_guard (γrws i) None ∗ gm)%I ⊤ with "[sh_guard gm guard_s_m gr]") as "[[gr [sh_guard gm]] %veq]".
        { set_solver. }
        { trivial. }
        { iFrame "sh_guard". iFrame "gm". iFrame "guard_s_m". iFrame "gr". }
        rewrite veq.
        
        (* release lock *)
        
        wp_bind (seq_idx #i locks).
        wp_apply wp_seq_idx.
        { apply has_elem_of_has_length with (len := ht_fixed_size).
          - lia. - intuition. } { done. }
        iIntros "_".
        
        wp_bind (release_shared (elem locks i)).
        wp_apply (wp_release_shared (γrws i) (elem locks i) g (storage_fn γ i l) F None with "[g rw sh_guard]").
        { set_solver. }
        { iFrame. iFrame "#". }
        iIntros (dummy) "g".
        
        wp_pures.
        unfold opt_as_val.
        iApply "Phi". iModIntro. iFrame.
Qed.

Lemma wp_ht_query γ γrws (ht: lang.val) (k: Key) (v: option Value) g gm F
  (F_disj: F ## ↑ HT_RW_NAMESPACE) :
      {{{
          g ∗ ((g &&{F}&&> is_ht γ γrws ht)) ∗
          gm ∗ ((gm &&{⊤}&&> own γ (m k v)))
      }}}
      query ht #k
      {{{ RET (opt_as_val v); g ∗ gm }}}.
Proof.
  unfold query.
  iIntros (Phi) "[g [#guard [gm #guardm]]] Phi".
  
  iMod (guarded_destruct_ht g ⊤ F γ γrws ht with "[guard g]") as "[g %ds]".
  { set_solver. }
  { iFrame "g". iFrame "guard". }
  destruct ds as [slots [locks [ds [l1 [l2 all_in_ns]]]]].
  subst ht.
  
  wp_pures.
  
  wp_bind (compute_hash #k).
  wp_apply (wp_compute_hash k). { done. }
  iIntros "_".
  
  iMod (ht_BorrowedRangeEmpty γ k (hash k)) as (range) "[%is_f o]".
  
  iDestruct (guarded_inner_ht with "guard") as "guard2".
  iDestruct (guards_refl (↑ HT_RW_NAMESPACE) (own γ range)) as "guard3".
  
  wp_apply (wp_ht_query_iter γ γrws range slots locks k v (hash k) g gm (own γ range) F with "[gm g o]").
  { trivial. }
  { set_solver. }
  { iFrame. iFrame "#". iPureIntro.
    intuition.
    assert (hash k < ht_fixed_size)%nat by (apply hash_in_bound). lia. 
  }
  
  iIntros "[l [a b]]". iApply "Phi". iFrame.
Qed.

End HashTableProof.
