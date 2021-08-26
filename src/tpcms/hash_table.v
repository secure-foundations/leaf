Require Import Burrow.rollup.
From stdpp Require Import gmap.

Require Import Burrow.CpdtTactics.
Require Import Tpcms.gmap.
Require Import Burrow.tactics.
Require Import coq_tricks.Deex.
From iris.prelude Require Import options.

Definition ht_fixed_size: nat. Admitted.

Class Hashable (Key: Type) := hash : (Key -> nat).

Context {Key} `{!EqDecision Key} `{!Countable Key} `{!Hashable Key}.
Context {Value} `{!EqDecision Value}.

Inductive HT :=
  HTR (ms: gmap Key (option (option Value))) (slots: gmap nat (option (option (Key * Value)))) : HT
.

Definition ht_dot (a b : HT) :=
  match a, b with
  | HTR x1 y1, HTR x2 y2 => HTR (gmap_dot x1 x2) (gmap_dot y1 y2)
  end.
  
Lemma ht_dot_comm (a b : HT) : ht_dot a b = ht_dot b a.
Proof.
  unfold ht_dot. destruct a, b.
  f_equal; apply gmap_dot_comm.
Qed.

Lemma ht_dot_assoc (a b c : HT) : ht_dot a (ht_dot b c) = ht_dot (ht_dot a b) c.
Proof.
  unfold ht_dot. destruct a, b, c.
  f_equal; apply gmap_dot_assoc.
Qed.

Definition P (a: HT) :=
  match a with
  | HTR ms slots =>
         gmap_valid slots
      /\ gmap_valid ms
      /\ (∀ i e , slots !! i = Some e -> i < ht_fixed_size)
      /\ (∀ (i1 i2: nat) (k: Key) (v1 v2: Value) ,
          slots !! i1 = Some (Some (Some (k, v1))) /\ slots !! i2 = Some (Some (Some (k, v2)))
            -> i1 = i2)
      /\ (∀ k v , ms !! k = Some (Some (Some v)) -> ∃ i , slots !! i = Some (Some (Some (k, v))))
      /\ (∀ (i: nat) (k: Key) (v: Value) , slots !! i = Some (Some (Some (k, v))) ->
        ms !! k = Some (Some (Some v)) /\ hash k ≤ i
        /\ (∀ j , hash k ≤ j -> j ≤ i -> ∃ k1 v1 , slots !! j = Some (Some (Some (k1, v1))))
        )
  end.

Definition V (a: HT) :=
  ∃ z , P (ht_dot a z).
  
Definition s (i: nat) (kv: option (Key * Value)) :=
  HTR ∅ {[ i := Some kv ]}.
  
Definition m (k: Key) (v: option Value) :=
  HTR {[ k := Some v ]} ∅.

Lemma ht_valid_QueryFound j k v v0
  : V (ht_dot (s j (Some (k, v0))) (m k v)) -> v = Some v0.
Proof.
  unfold V, s, m. intro. deex. destruct z. unfold ht_dot in *. unfold P in *.
  repeat (rewrite gmap_dot_empty in H).
  repeat (rewrite gmap_dot_empty_left in H).
  destruct_ands.
  have h := H4 j k v0. destruct_ands.
  assert (gmap_dot {[j := Some (Some (k, v0))]} slots !! j = Some (Some (Some (k, v0))))
    as t.
  {
    rewrite lookup_gmap_dot_left.
    - apply lookup_singleton.
    - trivial.
    - rewrite lookup_singleton. discriminate.
  }.
  have hr := h t. destruct_ands.
  rewrite lookup_gmap_dot_left in H5.
   - rewrite lookup_singleton in H5.
      inversion H5. trivial.
   - trivial.
   - rewrite lookup_singleton. discriminate.
Qed.

Definition full (a: HT) (k: Key) (i j : nat) :=
  match a with
  | HTR ms slots =>
    i ≤ j
      /\ (∀ l , i ≤ l -> l < j -> ∃ k1 v1 , slots !! l = Some (Some (Some (k1, v1))) /\ k1 ≠ k)
      /\ (∀ l e , slots !! l = Some e -> i ≤ l /\ l < j)
      /\ ms = ∅
  end.

Lemma ht_valid_QueryReachedEnd k a v
  (is_full: full a k (hash k) ht_fixed_size)
  : V (ht_dot a (m k v)) -> v = None.
Proof.
  unfold V, s, m. intro. deex. destruct z, a. unfold ht_dot in *. unfold P in *.
  unfold full in is_full. destruct_ands. subst ms0.
  repeat (rewrite gmap_dot_empty in H).
  repeat (rewrite gmap_dot_empty_left in H).
  repeat (rewrite gmap_dot_empty in H0).
  repeat (rewrite gmap_dot_empty_left in H0).
  repeat (rewrite gmap_dot_empty in H1).
  repeat (rewrite gmap_dot_empty_left in H1).
  repeat (rewrite gmap_dot_empty in H2).
  repeat (rewrite gmap_dot_empty_left in H2).
  repeat (rewrite gmap_dot_empty in H3).
  repeat (rewrite gmap_dot_empty_left in H3).
  repeat (rewrite gmap_dot_empty in H4).
  repeat (rewrite gmap_dot_empty_left in H4).
  destruct v; trivial. exfalso.
  have h := H3 k v.
  assert (gmap_dot {[k := Some (Some v)]} ms !! k = Some (Some (Some v))) as Q.
  {
    rewrite lookup_gmap_dot_left.
    - rewrite lookup_singleton. trivial.
    - trivial.
    - rewrite lookup_singleton. discriminate.
  }
  have hq := h Q. deex.
  
  have hx := H4 i k v hq. destruct_ands.
  have hy := H6 i H9.
  assert (i < ht_fixed_size) as ihfs.
  {
    apply H1 with (e := (Some (Some (k, v)))). trivial.
  }
  have hz := hy ihfs. deex.
  rewrite lookup_gmap_dot_left in hq.
  - destruct_ands. rewrite H11 in hq.  inversion hq. contradiction.
  - trivial.
  - destruct_ands. rewrite H11. discriminate.
Qed.
  
Lemma ht_valid_QueryNotFound k a v j
  (is_full: full a k (hash k) j)
  : V (ht_dot (ht_dot a (m k v)) (s j None)) -> v = None.
Proof.
  unfold V, s, m. intro. deex. destruct z, a. unfold ht_dot in *. unfold P in *.
  unfold full in is_full. destruct_ands. subst ms0.
  repeat (rewrite gmap_dot_empty in H).
  repeat (rewrite gmap_dot_empty_left in H).
  repeat (rewrite gmap_dot_empty in H0).
  repeat (rewrite gmap_dot_empty_left in H0).
  repeat (rewrite gmap_dot_empty in H1).
  repeat (rewrite gmap_dot_empty_left in H1).
  repeat (rewrite gmap_dot_empty in H2).
  repeat (rewrite gmap_dot_empty_left in H2).
  repeat (rewrite gmap_dot_empty in H3).
  repeat (rewrite gmap_dot_empty_left in H3).
  repeat (rewrite gmap_dot_empty in H4).
  repeat (rewrite gmap_dot_empty_left in H4).
  destruct v; trivial. exfalso.
  have h := H3 k v.
  assert (gmap_dot {[k := Some (Some v)]} ms !! k = Some (Some (Some v))) as Q.
  {
    rewrite lookup_gmap_dot_left.
    - rewrite lookup_singleton. trivial.
    - trivial.
    - rewrite lookup_singleton. discriminate.
  }
  have hq := h Q. deex.
  
  have hx := H4 i k v hq. destruct_ands.
  have hy := H6 i H9.
  assert (i < j) as ihfs.
  {
    have hij : Decision (i < j) by solve_decision. destruct hij; trivial.
    assert (j ≤ i) by lia.
    have mm := H10 j H5 H11. deex.
    rewrite lookup_gmap_dot_3mid in mm.
    - rewrite lookup_singleton in mm. inversion mm.
    - trivial.
    - rewrite lookup_singleton. discriminate.
  }
  have hz := hy ihfs. deex. destruct_ands.
  rewrite lookup_gmap_dot_3left in hq.
  - rewrite H11 in hq.  inversion hq. contradiction.
  - trivial.
  - rewrite H11. discriminate.
Qed.

Lemma preserves_lt_fixed_size j a b slots
  (ltfs : ∀ (i : nat) (e : option (option (Key * Value))),
         gmap_dot {[j := Some a]} slots !! i = Some e → i < ht_fixed_size)
  : ∀ (i : nat) (e : option (option (Key * Value))),
    gmap_dot {[j := Some b]} slots !! i = Some e → i < ht_fixed_size.
Proof.
  intros.
  (*have h : Decision (i = j) by solve_decision. destruct h.*)
  destruct (gmap_dot {[j := Some a]} slots !! i) eqn:gd.
  - exact (ltfs i o gd).
  - exfalso. unfold gmap_dot in H, gd.
      rewrite lookup_merge in H.
      rewrite lookup_merge in gd.
      unfold diag_None, gmerge in *.
      have h : Decision (j = i) by solve_decision. destruct h.
      + subst j.
        rewrite lookup_singleton in H.
        rewrite lookup_singleton in gd. destruct (slots !! i); discriminate.
      + rewrite lookup_singleton_ne in H; trivial.
        rewrite lookup_singleton_ne in gd; trivial.
        destruct (slots !! i); discriminate.
Qed.

Lemma gmap_key_vals_eq_of_gmap_dot
    {V} `{!EqDecision V} {K} `{!EqDecision K} `{!Countable K}
    (k: K) (m: gmap K (option V)) (e1 e2 : V)
  (gd : gmap_dot {[k := Some e1]} m !! k = Some (Some e2))
  : e1 = e2.
Proof.
  unfold gmap_dot in gd. rewrite lookup_merge in gd.
  unfold diag_None, gmerge in *. rewrite lookup_singleton in gd.
  destruct (m !! k).
  - discriminate.
  - inversion gd. intuition.
Qed.

Lemma key_vals_eq_of_gmap_dot (i: nat) (k k': Key) (v v': Value) slots
  (gd : gmap_dot {[i := Some (Some (k, v))]} slots !! i = Some (Some (Some (k', v'))))
  : k = k' /\ v = v'.
Proof.
  unfold gmap_dot in gd. rewrite lookup_merge in gd.
  unfold diag_None, gmerge in *. rewrite lookup_singleton in gd.
  destruct (slots !! i).
  - discriminate.
  - inversion gd. intuition.
Qed.

Lemma lookup_gmap_dot_singleton_ne {V} `{!EqDecision V} {K} `{!EqDecision K} `{!Countable K}
      (i1 i2: K) (e e': option V) (slots: gmap K (option V)) (ne: i1 ≠ i2) 
  : gmap_dot {[i1 := e]} slots !! i2 = gmap_dot {[i1 := e']} slots !! i2.
Proof.
  unfold gmap_dot. rewrite lookup_merge. rewrite lookup_merge. unfold diag_None, gmerge.
  rewrite lookup_singleton_ne; trivial.
  rewrite lookup_singleton_ne; trivial.
Qed.

(*
Lemma lookup_gmap_dot_singleton {V} `{!EqDecision V} {K} `{!EqDecision K} `{!Countable K}
      (i1 i2: K) (e e': option V) (slots: gmap K (option V))
  : gmap_dot {[i1 := e]} slots !! i1 = gmap_dot {[i1 := e']} slots !! i2.
  *)

Lemma gmap_dot_singleton_change {V} `{!EqDecision V} {K} `{!EqDecision K} `{!Countable K}
  (i1: K) (slots: gmap K (option V)) (a b: V) (c: option V)
 (gd: gmap_dot {[i1 := Some a]} slots !! i1 = Some (Some b))
    : gmap_dot {[i1 := c]} slots !! i1 = Some c.
Proof.
  unfold gmap_dot in *. rewrite lookup_merge. rewrite lookup_merge in gd.
    unfold diag_None, gmerge in *. rewrite lookup_singleton.
    rewrite lookup_singleton in gd. destruct (slots !! i1); trivial. inversion gd.
Qed.

Lemma preserves_unique_keys j k v v1 slots
  (uk : ∀ (i1 i2 : nat) (k0 : Key) (v2 v3 : Value),
         gmap_dot {[j := Some (Some (k, v1))]} slots !! i1 = Some (Some (Some (k0, v2)))
         ∧ gmap_dot {[j := Some (Some (k, v1))]} slots !! i2 = Some (Some (Some (k0, v3)))
         → i1 = i2)
  : ∀ (i1 i2 : nat) (k0 : Key) (v2 v3 : Value),
    gmap_dot {[j := Some (Some (k, v))]} slots !! i1 = Some (Some (Some (k0, v2)))
    ∧ gmap_dot {[j := Some (Some (k, v))]} slots !! i2 = Some (Some (Some (k0, v3)))
    → i1 = i2.
Proof.
  intros.
  destruct_ands.
  have ed : Decision (i1 = j) by solve_decision. destruct ed.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst. trivial.
      + subst j. have tk := uk i1 i2 k v1 v3.
        have t1 := key_vals_eq_of_gmap_dot _ _ _ _ _ _ H. destruct_ands. subst k0. subst v2.
        assert (i1 ≠ i2) as ne by crush.
        have t2 := lookup_gmap_dot_singleton_ne i1 i2
            (Some (Some (k, v))) (Some (Some (k, v1))) slots ne.
        rewrite t2 in H0. clear t2.
        apply tk. split; trivial.
        eapply gmap_dot_singleton_change. apply H.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst j. have tk := uk i1 i2 k v2 v1.
        have t1 := key_vals_eq_of_gmap_dot _ _ _ _ _ _ H0. destruct_ands. subst k0. subst v3.
        assert (i2 ≠ i1) as ne by crush.
        have t2 := lookup_gmap_dot_singleton_ne i2 i1
            (Some (Some (k, v))) (Some (Some (k, v1))) slots ne.
        rewrite t2 in H. clear t2.
        apply tk. split; trivial.
        eapply gmap_dot_singleton_change. apply H0.
      + have tk := uk i1 i2 k0 v2 v3.
        assert (j ≠ i1) as ne1 by crush.
        assert (j ≠ i2) as ne2 by crush.
        have t2 := lookup_gmap_dot_singleton_ne j i1
            (Some (Some (k, v))) (Some (Some (k, v1))) slots ne1.
        rewrite t2 in H. clear t2.
        have t2 := lookup_gmap_dot_singleton_ne j i2
            (Some (Some (k, v))) (Some (Some (k, v1))) slots ne2.
        rewrite t2 in H0. clear t2.
        intuition.
Qed.

Lemma pukn_helper2 j slots slots0 (i2: nat) (k k1: Key) (v1 v2: Value)
  (ac : gmap_dot {[j := Some None]} (gmap_dot slots slots0) !! i2 = Some (Some (Some (k, v2))))
  (zz : slots0 !! i2 = Some (Some (Some (k1, v1))))
  (ne : k1 ≠ k)
  : False.
Proof.
  unfold gmap_dot in ac.
  rewrite lookup_merge in ac. unfold diag_None, gmerge in ac.
  rewrite lookup_merge in ac. unfold diag_None, gmerge in ac.
  have h : Decision (j = i2) by solve_decision. destruct h.
  - subst i2.
    rewrite lookup_singleton in ac.
    destruct (slots !! j), (slots0 !! j); discriminate.
  - rewrite lookup_singleton_ne in ac; trivial.
    destruct (slots !! i2), (slots0 !! i2); try inversion ac; try discriminate.
    + subst o. inversion zz. crush.
Qed.

Lemma pukn_helper j k0 k v v1 slots v0 ms ms0 slots0 i2 v2
  (is_full : full (HTR ms0 slots0) k (hash k) j)
  (cntg : ∀ (i : nat) (k0 : Key) (v : Value),
        gmap_dot {[j := Some None]} (gmap_dot slots slots0) !! i =
        Some (Some (Some (k0, v)))
        → gmap_dot {[k := Some v0]} (gmap_dot ms ms0) !! k0 = Some (Some (Some v))
          ∧ hash k0 ≤ i
            ∧ (∀ j0 : nat,
                hash k0 ≤ j0
                → j0 ≤ i
                  → ∃ (k1 : Key) (v1 : Value),
                      gmap_dot {[j := Some None]} (gmap_dot slots slots0) !! j0 =
                      Some (Some (Some (k1, v1)))))
  (ab : gmap_dot {[j := Some (Some (k, v))]} (gmap_dot slots slots0) !! j =
      Some (Some (Some (k0, v1))))
  (ac : gmap_dot {[j := Some (Some (k, v))]} (gmap_dot slots slots0) !! i2 =
       Some (Some (Some (k0, v2))))
  : j = i2.
Proof.
  have t1 := key_vals_eq_of_gmap_dot j k k0 v v1 _ ab. destruct_ands. subst k0. subst v1.
  have h : Decision (j = i2) by solve_decision. destruct h; trivial. exfalso.
  rewrite (lookup_gmap_dot_singleton_ne _ _ _ (Some None)) in ac; trivial.
  have ctg := cntg i2 k v2 ac. destruct_ands.
  unfold full in is_full. destruct_ands.
  have ch := H1 j H2.
  have hle : Decision (j ≤ i2) by solve_decision. destruct hle.
  - have ch2 := ch l. deex.
    have gkv := gmap_key_vals_eq_of_gmap_dot _ _ _ _ ch2.
    assert (EqDecision (option (Key * Value))) by (typeclasses eauto).
    intuition. discriminate.
  - have yz := H3 i2.
    assert (hash k ≤ i2) as la1 by lia.
    assert (i2 < j) as la2 by lia.
    have zz := yz la1 la2. deex.
    destruct_ands.
    apply (pukn_helper2 j slots slots0 i2 k k1 v1 v2); trivial.
Qed. 

Lemma preserves_unique_keys_newslot j k v slots v0 ms ms0 slots0
  (is_full : full (HTR ms0 slots0) k (hash k) j)
  (uk : ∀ (i1 i2 : nat) (k : Key) (v1 v2 : Value),
         gmap_dot {[j := Some None]} (gmap_dot slots slots0) !! i1 =
         Some (Some (Some (k, v1)))
         ∧ gmap_dot {[j := Some None]} (gmap_dot slots slots0) !! i2 =
           Some (Some (Some (k, v2))) → i1 = i2)
  (cntg: ∀ (i : nat) (k0 : Key) (v : Value),
         gmap_dot {[j := Some None]} (gmap_dot slots slots0) !! i =
         Some (Some (Some (k0, v)))
         → gmap_dot {[k := Some v0]} (gmap_dot ms ms0) !! k0 = Some (Some (Some v))
           ∧ hash k0 ≤ i
             ∧ (∀ j0 : nat,
                  hash k0 ≤ j0
                  → j0 ≤ i
                    → ∃ (k1 : Key) (v1 : Value),
                        gmap_dot {[j := Some None]} (gmap_dot slots slots0) !! j0 =
                        Some (Some (Some (k1, v1)))))

  : ∀ (i1 i2 : nat) (k0 : Key) (v1 v2 : Value),
    gmap_dot {[j := Some (Some (k, v))]} (gmap_dot slots slots0) !! i1 =
    Some (Some (Some (k0, v1)))
    ∧ gmap_dot {[j := Some (Some (k, v))]} (gmap_dot slots slots0) !! i2 =
      Some (Some (Some (k0, v2))) → i1 = i2.
Proof.
  intros.
  destruct_ands.
  have ed : Decision (i1 = j) by solve_decision. destruct ed.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst. trivial.
      + subst i1.
        apply (pukn_helper j k0 k v v1 slots v0 ms ms0 slots0 i2 v2); trivial.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst i2. symmetry.
        apply (pukn_helper j k0 k v v2 slots v0 ms ms0 slots0 i1 v1); trivial.
      + have tk := uk i1 i2 k0 v1 v2.
        assert (j ≠ i1) as ne1 by crush.
        assert (j ≠ i2) as ne2 by crush.
        have t2 := lookup_gmap_dot_singleton_ne j i1
            (Some (Some (k, v))) (Some None) (gmap_dot slots slots0) ne1.
        rewrite t2 in H. clear t2.
        have t2 := lookup_gmap_dot_singleton_ne j i2
            (Some (Some (k, v))) (Some None) (gmap_dot slots slots0) ne2.
        rewrite t2 in H0. clear t2.
        intuition.
Qed.

Lemma preserves_map_to_slot (k: Key)
  (ms: gmap Key (option (option Value))) (slots: gmap nat (option (option (Key * Value))))
  (v0: option Value) (v: Value) (j: nat) (e: option (Key * Value))
  (gv: gmap_valid (gmap_dot {[j := Some e]} slots))
  (eokay: match e with Some (kprev, _) => k = kprev | None => True end)
  (mts : ∀ (k1 : Key) (v1 : Value),
         gmap_dot {[k := Some v0]} ms !! k1 = Some (Some (Some v1))
         → ∃ i : nat,
             gmap_dot {[j := Some e]} slots !! i = Some (Some (Some (k1, v1))))
  : ∀ (k2 : Key) (v2 : Value),
    gmap_dot {[k := Some (Some v)]} ms !! k2 = Some (Some (Some v2))
    → ∃ i : nat,
        gmap_dot {[j := Some (Some (k, v))]} slots !! i = Some (Some (Some (k2, v2))).
Proof.
  intros.
  have h : Decision (k = k2) by solve_decision. destruct h.
  - exists j. subst.
    assert (EqDecision (option Value)) by (typeclasses eauto).
    have t := gmap_key_vals_eq_of_gmap_dot _ _ _ _ H.
    have t' := t X.
    inversion t'. clear X. clear t. clear t'. clear H1.
    rewrite lookup_gmap_dot_left.
    + rewrite lookup_singleton. trivial.
    + eapply gmap_valid_update_singleton. apply gv.
    + rewrite lookup_singleton. discriminate.
  - have r := mts k2 v2.
      rewrite (lookup_gmap_dot_singleton_ne k k2 (Some (Some v)) (Some v0)) in H; trivial.
      intuition. deex. exists i.
      assert (i ≠ j).
      {
        intro. subst i.
        rewrite lookup_gmap_dot_left in H0.
        - rewrite lookup_singleton in H0. inversion H0. subst e. intuition.
        - trivial.
        - rewrite lookup_singleton. discriminate.
      }
      assert (j ≠ i) by crush.
      rewrite (lookup_gmap_dot_singleton_ne j i (Some (Some (k, v))) (Some e)); trivial.
Qed.

Lemma preserves_slot_to_map (k: Key) v j e slots v0 ms
  (eokay: match e with Some (kprev, _) => k = kprev | None => True end)
  (stm : ∀ (i : nat) (k1 : Key) (v1 : Value),
         gmap_dot {[j := Some e]} slots !! i =
         Some (Some (Some (k1, v1)))
         → gmap_dot {[k := Some v0]} ms !! k1 = Some (Some (Some v1))
           ∧ hash k1 ≤ i
             ∧ (∀ j0 : nat,
                  hash k1 ≤ j0
                  → j0 ≤ i
                    → ∃ (k3 : Key) (v3 : Value),
                        gmap_dot {[j := Some e]} slots !! j0 =
                        Some (Some (Some (k3, v3)))))
                        
  : ∀ (i : nat) (k2 : Key) (v2 : Value),
    gmap_dot {[j := Some (Some (k, v))]} slots !! i =
    Some (Some (Some (k2, v2)))
    → gmap_dot {[k := Some (Some v)]} ms !! k2 = Some (Some (Some v2))
      ∧ hash k2 ≤ i
        ∧ (∀ j0 : nat,
             hash k2 ≤ j0
             → j0 ≤ i
               → ∃ (k1 : Key) (v2 : Value),
                   gmap_dot {[j := Some (Some (k, v))]} slots !! j0 =
                   Some (Some (Some (k1, v2)))).
Proof.
  intros.
  have h : Decision (i = j) by solve_decision. destruct h.
  - subst j.
    destruct e.
    + destruct p. subst k0. have sx := stm i k v1.
      assert (gmap_dot {[i := Some (Some (k, v1))]} slots !! i = Some (Some (Some (k, v1)))).
      { eapply gmap_dot_singleton_change. apply H. }
      have qq := key_vals_eq_of_gmap_dot i k k2 v v2 slots H. destruct_ands.
      subst k2. subst v2.
      Admitted.
      (*
      intuition.
      * eapply gmap_dot_singleton_change. apply H2.
      * have ho := H4 j0. intuition.
        deex. exists k3, v3.
        rewrite 
    
    intuition.
    *)
    
  
  
  
  have h : Decision (k = k2) by solve_decision. destruct h.
  - subst k2.
    destruct e.
    + have sx := stm i k v2. intuition.
    
    have rrr := stm i k2 v2.


Lemma ht_helper_update_existing j k v v0 v1 z :
  P (ht_dot (ht_dot (s j (Some (k, v1))) (m k v0)) z) ->
  P (ht_dot (ht_dot (s j (Some (k, v))) (m k (Some v))) z).
Proof.
  intro. unfold P, ht_dot, s, m in *. destruct z.
  repeat (rewrite gmap_dot_empty).
  repeat (rewrite gmap_dot_empty_left).
  repeat (rewrite gmap_dot_empty in H).
  repeat (rewrite gmap_dot_empty_left in H).
  destruct_ands.
  split.
  { eapply gmap_valid_update_singleton. apply H. }
  split.
  { eapply gmap_valid_update_singleton. apply H0. }
  split.
  { eapply preserves_lt_fixed_size. apply H1. }
  split.
  { eapply preserves_unique_keys. apply H2. }
  split.
  { eapply preserves_map_to_slot.
    - apply H.
    - simpl. trivial.
    - apply H3.
  }
  Admitted.

Lemma ht_helper_update_new j k v v0 z a
  (is_full: full a k (hash k) j) :
  P (ht_dot (ht_dot (s j None) (m k v0)) (ht_dot z a)) ->
  P (ht_dot (ht_dot (s j (Some (k, v))) (m k (Some v))) (ht_dot z a)).
Proof.
  intro. unfold P, ht_dot, s, m in *. destruct z. destruct a.
  repeat (rewrite gmap_dot_empty).
  repeat (rewrite gmap_dot_empty_left).
  repeat (rewrite gmap_dot_empty in H).
  repeat (rewrite gmap_dot_empty_left in H).
  destruct_ands.
  split.
  { eapply gmap_valid_update_singleton. apply H. }
  split.
  { eapply gmap_valid_update_singleton. apply H0. }
  split.
  { eapply preserves_lt_fixed_size. apply H1. }
  split.
  {eapply preserves_unique_keys_newslot.
    - apply is_full.
    - apply H2.
    - apply H4.
  }
  split.
  { eapply preserves_map_to_slot.
    - apply H.
    - simpl. trivial.
    - apply H3.
  }

