From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export base_logic.
From stdpp Require Import gmap.

From iris.algebra Require Export gmap.

Require Import examples.gmap_option.
Require Import examples.misc_tactics.

Definition ht_fixed_size: nat := 4.

Definition Key := Z. 
Definition Value := Z.

(* we choose a concrete hash function for completeness, but the ht logic
doens't depend on this choice *)
Definition hash : Key -> nat := λ (k: Z) , Z.to_nat (Z.modulo k ht_fixed_size).

Lemma hash_in_bound (k: Key) : hash k < ht_fixed_size.
Proof. unfold hash.
  have h := Z_mod_lt k ht_fixed_size.
  unfold ht_fixed_size in *.
  lia.
Qed.

(* the rest of the hash_table doesn't depend on the specifics of hash *)
Opaque ht_fixed_size.
Opaque hash.

Inductive HT :=
  HTR (ms: gmap Key (option (option Value))) (slots: gmap nat (option (option (Key * Value)))) : HT
.

Definition ht_dot (a b : HT) :=
  match a, b with
  | HTR x1 y1, HTR x2 y2 => HTR (gmap_dot x1 x2) (gmap_dot y1 y2)
  end.

Definition ht_unit := HTR ∅ ∅.

Lemma ht_unit_dot (a: HT) : ht_dot a ht_unit = a.
Proof.
  unfold ht_dot, ht_unit.
  destruct a.
  rewrite gmap_dot_empty.
  rewrite gmap_dot_empty.
  trivial.
Qed.
  
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
  unfold V, s, m. intros [z H]. destruct z. unfold ht_dot in *. unfold P in *.
  repeat (rewrite gmap_dot_empty in H).
  repeat (rewrite gmap_dot_empty_left in H).
  destruct H as [H [H0 [H1 [H2 [H3 H4]]]]].
  have h := H4 j k v0.
  assert (gmap_dot {[j := Some (Some (k, v0))]} slots !! j = Some (Some (Some (k, v0))))
    as t.
  {
    rewrite lookup_gmap_dot_left.
    - apply lookup_singleton.
    - trivial.
    - rewrite lookup_singleton. discriminate.
  }
  have hr := h t. destruct hr as [H5 H6].
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
  unfold V, s, m. intros [z H]. destruct z, a. unfold ht_dot in *. unfold P in *.
  unfold full in is_full.
  destruct H as [H [H0 [H1 [H2 [H3 H4]]]]].
  destruct is_full as [H5 [H6 [H7 H8]]].
  subst ms0.
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
  have hq := h Q. destruct hq as [i hq].
  
  have hx := H4 i k v hq. destruct hx as [H8 [H9 H10]].
  have hy := H6 i H9.
  assert (i < ht_fixed_size) as ihfs.
  {
    apply H1 with (e := (Some (Some (k, v)))). trivial.
  }
  have hz := hy ihfs. destruct hz as [k1 [v1 hz]].
  rewrite lookup_gmap_dot_left in hq.
  - destruct hz as [H11 H12]. rewrite H11 in hq.  inversion hq. contradiction.
  - trivial.
  - destruct hz as [H11 H12]. rewrite H11. discriminate.
Qed.
  
Lemma ht_valid_QueryNotFound k a v j
  (is_full: full a k (hash k) j)
  : V (ht_dot (ht_dot a (m k v)) (s j None)) -> v = None.
Proof.
  unfold V, s, m. intros [z H]. destruct z, a. unfold ht_dot in *. unfold P in *.
  unfold full in is_full.
  destruct H as [H [H0 [H1 [H2 [H3 H4]]]]].
  destruct is_full as [H5 [H6 [H7 H8]]].
  subst ms0.
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
  have hq := h Q. destruct hq as [i hq].
  
  have hx := H4 i k v hq. destruct hx as [H8 [H9 H10]].
  have hy := H6 i H9.
  assert (i < j) as ihfs.
  {
    have hij : Decision (i < j) by solve_decision. destruct hij; trivial.
    assert (j ≤ i) by lia.
    have mm := H10 j H5 H11. destruct mm as [k1 [v1 mm]].
    rewrite lookup_gmap_dot_3mid in mm.
    - rewrite lookup_singleton in mm. inversion mm.
    - trivial.
    - rewrite lookup_singleton. discriminate.
  }
  have hz := hy ihfs. destruct hz as [k1 [v1 hz]]. destruct hz as [hz1 hz2].
  rewrite lookup_gmap_dot_3left in hq.
  - rewrite hz1 in hq.  inversion hq. contradiction.
  - trivial.
  - rewrite hz1. discriminate.
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
  destruct H as [H H0].
  have ed : Decision (i1 = j) by solve_decision. destruct ed.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst. trivial.
      + subst j. have tk := uk i1 i2 k v1 v3.
        have t1 := key_vals_eq_of_gmap_dot _ _ _ _ _ _ H. destruct t1 as [H1 H2]. subst k0. subst v2.
        assert (i1 ≠ i2) as ne by (symmetry; trivial).
        have t2 := lookup_gmap_dot_singleton_ne i1 i2
            (Some (Some (k, v))) (Some (Some (k, v1))) slots ne.
        rewrite t2 in H0. clear t2.
        apply tk. split; trivial.
        eapply gmap_dot_singleton_change. apply H.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst j. have tk := uk i1 i2 k v2 v1.
        have t1 := key_vals_eq_of_gmap_dot _ _ _ _ _ _ H0. destruct t1 as [H1 H2]. subst k0. subst v3.
        assert (i2 ≠ i1) as ne by (symmetry; trivial).
        have t2 := lookup_gmap_dot_singleton_ne i2 i1
            (Some (Some (k, v))) (Some (Some (k, v1))) slots ne.
        rewrite t2 in H. clear t2.
        apply tk. split; trivial.
        eapply gmap_dot_singleton_change. apply H0.
      + have tk := uk i1 i2 k0 v2 v3.
        assert (j ≠ i1) as ne1 by (symmetry; trivial).
        assert (j ≠ i2) as ne2 by (symmetry; trivial).
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
    + subst o. inversion zz. inversion zz. subst k. contradiction.
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
  have t1 := key_vals_eq_of_gmap_dot j k k0 v v1 _ ab. destruct t1 as [H1 H2]. subst k0. subst v1.
  have h : Decision (j = i2) by solve_decision. destruct h; trivial. exfalso.
  rewrite (lookup_gmap_dot_singleton_ne _ _ _ (Some None)) in ac; trivial.
  have ctg := cntg i2 k v2 ac. destruct ctg as [H [H0 H1]].
  unfold full in is_full. destruct is_full as [H2 [H3 [H4 H5]]].
  have ch := H1 j H2.
  have hle : Decision (j ≤ i2) by solve_decision. destruct hle.
  - have ch2 := ch l. destruct ch2 as [k1 [v1 ch2]].
    have gkv := gmap_key_vals_eq_of_gmap_dot _ _ _ _ ch2.
    assert (EqDecision (option (Key * Value))) by (typeclasses eauto).
    intuition. discriminate.
  - have yz := H3 i2.
    assert (hash k ≤ i2) as la1 by lia.
    assert (i2 < j) as la2 by lia.
    have zz := yz la1 la2. destruct zz as [k1 [v1 zz]].
    destruct zz as [zz1 zz2].
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
  destruct H as [H H0].
  have ed : Decision (i1 = j) by solve_decision. destruct ed.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst. trivial.
      + subst i1.
        apply (pukn_helper j k0 k v v1 slots v0 ms ms0 slots0 i2 v2); trivial.
    - have ed : Decision (i2 = j) by solve_decision. destruct ed.
      + subst i2. symmetry.
        apply (pukn_helper j k0 k v v2 slots v0 ms ms0 slots0 i1 v1); trivial.
      + have tk := uk i1 i2 k0 v1 v2.
        assert (j ≠ i1) as ne1 by (symmetry; trivial).
        assert (j ≠ i2) as ne2 by (symmetry; trivial).
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
      intuition. destruct H0 as [i H0]. exists i.
      assert (i ≠ j).
      {
        intro. subst i.
        rewrite lookup_gmap_dot_left in H0.
        - rewrite lookup_singleton in H0. inversion H0. subst e. intuition.
        - trivial.
        - rewrite lookup_singleton. discriminate.
      }
      assert (j ≠ i) by (symmetry; trivial).
      rewrite (lookup_gmap_dot_singleton_ne j i (Some (Some (k, v))) (Some e)); trivial.
Qed.

Lemma preserves_slot_to_map (k: Key) v j e slots v0 ms
  (eokay: match e with
    Some (kprev, _) => k = kprev |
    None =>
      gmap_valid (gmap_dot {[k := Some (Some v)]} ms)
      /\ hash k ≤ j
      /\ (
      ∀ j0 : nat,
        hash k ≤ j0
        → j0 ≤ j
          → ∃ (k1 : Key) (v2 : Value),
              gmap_dot {[j := Some (Some (k, v))]} slots !! j0 = Some (Some (Some (k1, v2)))
      )
  end)
  (gv: gmap_valid (gmap_dot {[j := Some e]} slots))
  (uk' : ∀ (i1 i2 : nat) (k0 : Key) (v1 v2 : Value),
         gmap_dot {[j := Some (Some (k, v))]} slots !! i1 =
         Some (Some (Some (k0, v1)))
         ∧ gmap_dot {[j := Some (Some (k, v))]} slots !! i2 =
           Some (Some (Some (k0, v2))) → i1 = i2)
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
  have h : Decision (j = i) by solve_decision. destruct h.
  - subst j.
    destruct e.
    + destruct p. subst k0. have sx := stm i k v1.
      assert (gmap_dot {[i := Some (Some (k, v1))]} slots !! i = Some (Some (Some (k, v1)))).
      { eapply gmap_dot_singleton_change. apply H. }
      have qq := key_vals_eq_of_gmap_dot i k k2 v v2 slots H. destruct qq as [qq1 qq2].
      subst k2. subst v2.
      intuition.
      * eapply gmap_dot_singleton_change. apply H2.
      * have ho := H4 j0. intuition.
        have h : Decision (i = j0) by solve_decision. destruct h.
        -- exists k, v. subst j0. trivial.
        -- destruct H7 as [k3 [v3 H7]]. exists k3, v3.
            rewrite (lookup_gmap_dot_singleton_ne i j0 _ (Some (Some (k, v1)))); trivial.
    + have kv := key_vals_eq_of_gmap_dot i k k2 v v2 slots H. destruct kv as [keq veq].
      subst k2. subst v2.
      assert (gmap_dot {[k := Some (Some v)]} ms !! k = Some (Some (Some v))).
      {
        rewrite lookup_gmap_dot_left.
        - rewrite lookup_singleton. trivial.
        - intuition.
        - rewrite lookup_singleton. discriminate.
      }
      split; trivial.
      split; intuition.
  - have sx := stm i k2 v2.
    assert (gmap_dot {[j := Some e]} slots !! i = Some (Some (Some (k2, v2)))) as gd.
    {
      rewrite (lookup_gmap_dot_singleton_ne _ _ _ (Some (Some (k, v)))); trivial.
    }
    assert (gmap_dot {[j := Some (Some (k, v))]} slots !! j = Some (Some (Some (k, v)))).
    {
      rewrite lookup_gmap_dot_left.
      - rewrite lookup_singleton. trivial.
      - eapply gmap_valid_update_singleton. apply gv.
      - rewrite lookup_singleton. discriminate.
    }
    assert (k ≠ k2).
    {
      intro. subst k2.
      apply n.
      eapply uk'.
      split.
      + apply H0.
      + apply H.
    }
    have sxr := sx gd. intuition.
    + rewrite (lookup_gmap_dot_singleton_ne _ _ _ (Some v0)); trivial.
    + have h : Decision (j = j0) by solve_decision. destruct h.
      * subst j0. exists k, v. trivial.
      * have gr := H8 j0 H7 H9. destruct gr as [k3 [v3 gr]]. exists k3, v3.
          rewrite (lookup_gmap_dot_singleton_ne _ _ _ (Some e)); trivial.
Qed.


Lemma full_with_dot ms0 slots0 k j slots j0 v v0 ms
  (is_full : full (HTR ms0 slots0) k (hash k) j)
  (is_val : gmap_valid (gmap_dot {[k := Some v0]} (gmap_dot ms ms0)))
  (is_val2 : gmap_valid (gmap_dot {[j := Some (Some (k, v))]} (gmap_dot slots slots0)))
  : hash k ≤ j0 -> j0 ≤ j ->
  ∃ (k1 : Key) (v2 : Value),
    gmap_dot {[j := Some (Some (k, v))]} (gmap_dot slots slots0) !! j0 =
    Some (Some (Some (k1, v2))).
Proof.
  have h : Decision (j = j0) by solve_decision. destruct h.
  - subst j0. intros.
      exists k, v.
      rewrite lookup_gmap_dot_left.
      + rewrite lookup_singleton. trivial.
      + trivial.
      + rewrite lookup_singleton. discriminate.
  - unfold full in is_full. destruct is_full as [H [H0 [H1 H2]]].
    intros.
    assert (j0 < j) as la by lia.
    have h := H0 j0. intuition.
    destruct H6 as [k1 [v1 H6]].
    exists k1, v1.
    rewrite gmap_dot_assoc.
      rewrite lookup_gmap_dot_right.
      + intuition.
      + rewrite <- gmap_dot_assoc. trivial.
      + destruct H6 as [H7 H8]. rewrite H7. discriminate.
Qed.

Lemma ht_helper_update_existing j k v v0 v1 z :
  P (ht_dot (ht_dot (s j (Some (k, v1))) (m k v0)) z) ->
  P (ht_dot (ht_dot (s j (Some (k, v))) (m k (Some v))) z).
Proof.
  intro. unfold P, ht_dot, s, m in *. destruct z.
  repeat (rewrite gmap_dot_empty).
  repeat (rewrite gmap_dot_empty_left).
  repeat (rewrite gmap_dot_empty in H).
  repeat (rewrite gmap_dot_empty_left in H).
  destruct H as [H [H0 [H1 [H2 [H3 H4]]]]].
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
  {
    eapply preserves_slot_to_map with (e := (Some (k, v1))).
    - trivial.
    - apply H.
    - eapply preserves_unique_keys. apply H2. 
    - apply H4.
  }
Qed.

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
  destruct H as [H [H0 [H1 [H2 [H3 H4]]]]].
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
  {
    eapply preserves_slot_to_map with (e := None).
    - repeat split.
      + eapply gmap_valid_update_singleton. apply H0.
      + unfold full in is_full. intuition.
      + intros. eapply full_with_dot with (v0 := v0).
        * apply is_full.
        * apply H0.
        * eapply gmap_valid_update_singleton. apply H.
        * trivial.
        * trivial.
    - trivial.
    - eapply preserves_unique_keys_newslot.
      + apply is_full.
      + apply H2.
      + apply H4.
    - apply H4.
  }
Qed.

Definition ht_mov (a b: HT) : Prop :=
  ∀ z , V (ht_dot a z) -> V (ht_dot b z).

Lemma ht_update_existing j k v v0 v1 :
  ht_mov
    (ht_dot (s j (Some (k, v1))) (m k v0))
    (ht_dot (s j (Some (k, v))) (m k (Some v))).
Proof.
  unfold ht_mov.
  unfold V. intros z [z0 H]. exists z0.
  rewrite <- ht_dot_assoc.
  rewrite <- ht_dot_assoc in H.
  eapply ht_helper_update_existing.
  apply H.
Qed.
  
Lemma ht_update_new j k v v0 a
  (is_full: full a k (hash k) j) :
  ht_mov
    (ht_dot (ht_dot (s j None) (m k v0)) (a))
    (ht_dot (ht_dot (s j (Some (k, v))) (m k (Some v))) (a)).
Proof.
  unfold ht_mov.
  unfold V. intros z [z0 H]. exists z0.
  rewrite <- ht_dot_assoc.
  rewrite <- ht_dot_assoc in H.
  full_generalize (ht_dot z z0) as y.
  rewrite <- ht_dot_assoc.
  rewrite <- ht_dot_assoc in H.
  assert (ht_dot a y = ht_dot y a) by (apply ht_dot_comm).
  rewrite H0 in H.
  rewrite H0.
  eapply ht_helper_update_new.
  - apply is_full.
  - apply H.
Qed.

Lemma full_trivial k i : full ht_unit k i i.
Proof.
  unfold full, ht_unit.
  repeat split.
  - lia.
  - intros. lia.
  - intros. rewrite lookup_empty in H. discriminate.
  - intros. rewrite lookup_empty in H. discriminate.
Qed.

Lemma full_dot a k i j k0 v0
  (fa: full a k i j)
  (ne: k0 ≠ k)
  : full (ht_dot a (s j (Some (k0, v0)))) k i (j+1).
Proof.
  unfold full, ht_dot, s in *. destruct a. destruct fa as [H [H0 [H1 H2]]]. repeat split.
  - lia.
  - intros. have x := H0 l H3.
    have h : Decision (l = j) by solve_decision. destruct h.
    + subst l. exists k0, v0. split; trivial.
      unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
        rewrite lookup_singleton. destruct (slots !! j) eqn:sj; trivial.
        have t := H1 j o sj. lia.
    + assert (l < j) as la by lia. intuition.
        destruct H5 as [k1 [v1 H5]]. exists k1, v1. split.
      * unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
        assert (j ≠ l) as la2 by lia.
        rewrite lookup_singleton_ne; trivial. destruct (slots !! l); intuition.
      * intuition.
  - have h : Decision (j = l) by solve_decision. destruct h.
    + lia.
    + unfold gmap_dot in H3.
      rewrite lookup_merge in H3. unfold diag_None, gmerge in H3.
      rewrite lookup_singleton_ne in H3; trivial.
      destruct (slots !! l) eqn:sl.
      * have t := H1 l o sl. lia.
      * discriminate.
  - have h : Decision (j = l) by solve_decision. destruct h.
    + lia.
    + unfold gmap_dot in H3.
      rewrite lookup_merge in H3. unfold diag_None, gmerge in H3.
      rewrite lookup_singleton_ne in H3; trivial.
      destruct (slots !! l) eqn:sl.
      * have t := H1 l o sl. lia.
      * discriminate.
  - rewrite gmap_dot_empty. trivial.
Qed.

Global Instance ht_eqdec : EqDecision HT.
Proof. solve_decision. Qed.

Lemma ht_valid_monotonic : forall x y , V (ht_dot x y) -> V x.
Proof.
  intros x y H. unfold V in *. destruct H as [z H]. exists (ht_dot y z).
  rewrite ht_dot_assoc. trivial.
Qed.

Lemma P_ht_unit : P ht_unit.
Proof.
  unfold P, ht_unit. repeat split; intros.
  - rewrite lookup_empty in H. discriminate.
  - rewrite lookup_empty in H. intuition. discriminate.
  - rewrite lookup_empty in H. discriminate.
  - rewrite lookup_empty in H. discriminate.
  - rewrite lookup_empty in H. discriminate.
  - rewrite lookup_empty in H. discriminate.
Qed.

Lemma ht_unit_valid : V ht_unit.
Proof.
  unfold V. exists ht_unit. rewrite ht_unit_dot.
  apply P_ht_unit.
Qed.

Lemma ht_mov_reflex : forall x , ht_mov x x.
Proof.
  intros. unfold ht_mov. trivial.
Qed.

Lemma ht_mov_trans : forall x y z , ht_mov x y -> ht_mov y z -> ht_mov x z. 
Proof.
  intros. unfold ht_mov in *. intro. have h := H z. have h0 := H0 z. intuition.
Qed.

Lemma ht_mov_monotonic : forall x y z ,
      ht_mov x y -> V (ht_dot x z) -> V (ht_dot y z) /\ ht_mov (ht_dot x z) (ht_dot y z).
Proof.
  intros. split.
    - unfold ht_mov in H. intuition.
    - unfold ht_mov in *. intros.
      have t := H (ht_dot z z0).
      rewrite ht_dot_assoc in t.
      rewrite ht_dot_assoc in t.
      intuition.
Qed.

(*
Global Instance ht_tpcm : TPCM HT := {
  m_valid := V ;
  dot := ht_dot ;
  mov := ht_mov ;
  unit := ht_unit ;
  
  valid_monotonic := ht_valid_monotonic ;
  unit_valid := ht_unit_valid ;
  unit_dot := ht_unit_dot ;
  tpcm_comm := ht_dot_comm ;
  tpcm_assoc := ht_dot_assoc ;
  reflex := ht_mov_reflex ;
  trans := ht_mov_trans ;
  mov_monotonic := ht_mov_monotonic ;
}.
*)

Definition ht_le a b :=
  ∃ c , ht_dot a c = b.

Lemma ht_tpcm_le a a' b b'
  : gmap_le a a' -> gmap_le b b' -> ht_le (HTR a b) (HTR a' b').
Proof.
  intros [c H] [c0 H0]. unfold gmap_le in *.
  exists (HTR c c0).
  unfold ht_dot. 
  rewrite H. rewrite H0. trivial.
Qed.

Lemma ht_tpcm_le_rev a a' b b'
  : ht_le (HTR a b) (HTR a' b') -> gmap_le a a' /\ gmap_le b b'.
Proof.
  intros H. unfold ht_le in H. destruct H as [c H]. destruct c.
  unfold ht_dot in H. inversion H. subst a'. subst b'.
  split.
  - unfold gmap_le. exists ms. trivial.
  - unfold gmap_le. exists slots. trivial.
Qed.

Lemma conjunct_and_lemma a1 b1 a2 b2
  (a_disj : ∀ k j1 j2 , a1 !! k = Some j1 -> a2 !! k = Some j2 -> False)
  (b_disj : ∀ k j1 j2 , b1 !! k = Some j1 -> b2 !! k = Some j2 -> False)
  : ∀ r , V r -> ht_le (HTR a1 b1) r -> ht_le (HTR a2 b2) r -> ht_le (ht_dot (HTR a1 b1) (HTR a2 b2)) r.
Proof.
  intros r Vr le1 le2. destruct r.
  unfold V in Vr. destruct Vr as [z Pdot].
  unfold P in Pdot.
  destruct z. unfold ht_dot in Pdot. destruct Pdot as [gv1 [gv2 _]].
  have val1 := gmap_valid_left _ _ gv1.
  have val2 := gmap_valid_left _ _ gv2.
  have le1' := ht_tpcm_le_rev _ _ _ _ le1. destruct le1' as [la lb].
  have le2' := ht_tpcm_le_rev _ _ _ _ le2. destruct le2' as [lc ld].
  apply ht_tpcm_le.
  - apply conjunct_and_gmap; trivial.
  - apply conjunct_and_gmap; trivial.
Qed.

Lemma s_add_m i slot k1 v1
  : ∀ r , V r -> ht_le (s i slot) r -> ht_le (m k1 v1) r -> ht_le (ht_dot (s i slot) (m k1 v1)) r.
Proof.
  unfold s. unfold m. apply conjunct_and_lemma.
  - intros k j1 j2 e1 e2. rewrite lookup_empty in e1. discriminate.
  - intros k j1 j2 e1 e2. rewrite lookup_empty in e2. discriminate.
Qed.
  
Lemma range_add_m a k i j k1 v1
  (fa: full a k i j)
  : ∀ r , V r -> ht_le a r -> ht_le (m k1 v1) r -> ht_le (ht_dot a (m k1 v1)) r.
Proof.
  destruct a. unfold m. apply conjunct_and_lemma.
  - intros k0 j1 j2 e1 e2. unfold full in fa. destruct fa as [ij [X1 [X2 mse]]].
    subst ms. rewrite lookup_empty in e1. discriminate.
  - intros k0 j1 j2 e1 e2. rewrite lookup_empty in e2. discriminate.
Qed.

Lemma full_add_s_m a k i j c k1 v1
  (fa: full a k i j)
  : ∀ r , V r -> ht_le a r -> ht_le (ht_dot (s j c) (m k1 v1)) r -> ht_le (ht_dot a (ht_dot (s j c) (m k1 v1))) r.
Proof.
  unfold m. unfold s. cbn [ht_dot]. destruct a.
  rewrite gmap_dot_empty_left. rewrite gmap_dot_empty.
  apply conjunct_and_lemma.
  - intros k0 j1 j2 e1 e2. unfold full in fa. destruct fa as [ij [X1 [X2 mse]]].
    subst ms. rewrite lookup_empty in e1. discriminate.
  - intros k0 j1 j2 e1 e2. unfold full in fa. destruct fa as [ij [X1 [X2 X3]]].
    have x2 := X2 k0 j1 e1.
    have h : Decision (j = k0) by solve_decision. destruct h.
    + subst k0. lia.
    + rewrite lookup_singleton_ne in e2; trivial. discriminate.
Qed.

Lemma full_add a k i j c
  (fa: full a k i j)
  : ∀ r , V r -> ht_le a r -> ht_le (s j c) r -> ht_le (ht_dot a (s j c)) r.
Proof.
  destruct a. unfold s. apply conjunct_and_lemma.
  - intros k0 j1 j2 e1 e2. unfold full in fa. destruct fa as [ij [X1 [X2 mse]]].
    subst ms. rewrite lookup_empty in e1. discriminate.
  - intros k0 j1 j2 e1 e2. unfold full in fa. destruct fa as [ij [X1 [X2 X3]]].
    have x2 := X2 k0 j1 e1.
    have h : Decision (j = k0) by solve_decision. destruct h.
    + subst k0. lia.
    + rewrite lookup_singleton_ne in e2; trivial. discriminate.
Qed.

Fixpoint gmap_seq {V} `{!EqDecision V} (n: nat) (v: V) : gmap nat V :=
  match n with
  | 0 => empty
  | S n => <[ n := v ]> (gmap_seq n v)
  end.
  
Fixpoint gmap_zseq {V} `{!EqDecision V} (n: nat) (v: V) : gmap Z V :=
  match n with
  | 0 => empty
  | S n => <[ (n : Z) := v ]> (gmap_zseq n v)
  end.

Definition mseq (n: nat) := HTR (gmap_zseq n (Some None)) empty.
Definition sseq (n: nat) := HTR empty (gmap_seq n (Some None)).

Lemma lookup_gmap_seq {V} `{!EqDecision V} (x: V) k (n: nat)
  (lt: k < n) : gmap_seq n x !! k = Some x.
Proof.
  induction n.
  - lia.
  - cbn [gmap_seq]. have h : Decision (n = k) by solve_decision. destruct h.
    + subst k. rewrite lookup_insert. trivial.
    + rewrite lookup_insert_ne; trivial. apply IHn. lia.
Qed.
  
Lemma lookup_gmap_seq_out {V} `{!EqDecision V} (x: V) k (n: nat)
  (lt: ¬ k < n) : gmap_seq n x !! k = None.
Proof.
  induction n.
  - unfold gmap_seq. rewrite lookup_empty. trivial.
  - assert (n ≠ k) by lia.
    cbn [gmap_seq]. rewrite lookup_insert_ne; trivial. apply IHn. lia.
Qed.
  
Lemma lookup_gmap_zseq {V} `{!EqDecision V} (x: V) (k: Z) (n: nat)
  (lt: Z.le 0 k /\ Z.lt k n) : gmap_zseq n x !! k = Some x.
Proof.
  induction n.
  - lia.
  - cbn [gmap_seq]. have h : Decision ((n:Z) = k) by solve_decision. destruct h.
    + subst k. rewrite lookup_insert. trivial.
    + rewrite lookup_insert_ne; trivial. apply IHn. lia.
Qed.
  
Lemma lookup_gmap_zseq_out {V} `{!EqDecision V} (x: V) k (n: nat)
  (lt: ¬ ( Z.le 0 k /\ Z.lt k n )) : gmap_zseq n x !! k = None.
Proof.
  induction n.
  - unfold gmap_seq. rewrite lookup_empty. trivial.
  - assert ((n: Z) ≠ k) by lia.
    cbn [gmap_seq]. rewrite lookup_insert_ne; trivial. apply IHn. lia.
Qed.

Lemma valid_mseq_sseq (n: nat) : V (ht_dot (mseq n) (sseq ht_fixed_size)).
Proof.
  unfold V. exists ht_unit. rewrite ht_unit_dot. unfold mseq, sseq, ht_dot.
      rewrite gmap_dot_empty. rewrite gmap_dot_empty_left. unfold P. split.
  { unfold gmap_valid. intro.
    have h : Decision (k < ht_fixed_size) by solve_decision. destruct h.
    + rewrite lookup_gmap_seq; trivial.
    + rewrite lookup_gmap_seq_out; trivial.
  }
  split.
  { unfold gmap_valid. intro.
    have h : Decision (Z.le 0 k /\ Z.lt k n) by solve_decision. destruct h.
    + rewrite lookup_gmap_zseq; trivial.
    + rewrite lookup_gmap_zseq_out; trivial.
  }
  split.
  { intros.
    have h : Decision (i < ht_fixed_size) by solve_decision. destruct h.
    + trivial.
    + rewrite lookup_gmap_seq_out in H; trivial. discriminate.
  } 
  split.
  { intros. destruct H as [H H0].
    have h : Decision (i1 < ht_fixed_size) by solve_decision. destruct h.
    + rewrite lookup_gmap_seq in H; trivial. discriminate.
    + rewrite lookup_gmap_seq_out in H; trivial. discriminate.
  } 
  split.
  {
    intros. exfalso.
    have h : Decision (Z.le 0 k /\ Z.lt k n) by solve_decision. destruct h.
    + rewrite lookup_gmap_zseq in H; trivial. discriminate.
    + rewrite lookup_gmap_zseq_out in H; trivial. discriminate.
  } 
  split.
  {
  - intros. exfalso.
    have h : Decision (i < ht_fixed_size) by solve_decision. destruct h.
    + rewrite lookup_gmap_seq in H; trivial. discriminate.
    + rewrite lookup_gmap_seq_out in H; trivial. discriminate.
  } 
  split.
  {
    exfalso.
    have h : Decision (i < ht_fixed_size) by solve_decision. destruct h.
    + rewrite lookup_gmap_seq in H; trivial. discriminate.
    + rewrite lookup_gmap_seq_out in H; trivial. discriminate.
  } 
  {
  - exfalso.
    have h : Decision (i < ht_fixed_size) by solve_decision. destruct h.
    + rewrite lookup_gmap_seq in H; trivial. discriminate.
    + rewrite lookup_gmap_seq_out in H; trivial. discriminate.
  }
Qed.

Lemma mseq_append (n: nat)
  : mseq (S n) = ht_dot (mseq n) (m (n: Z) None).
Proof.
  unfold mseq, m, ht_dot. rewrite gmap_dot_empty. f_equal.
  cbn [gmap_zseq]. apply map_eq. intro.
  have h : Decision ((n: Z) = i) by solve_decision. destruct h.
  - subst i. rewrite lookup_insert.
    unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
    rewrite lookup_gmap_zseq_out.
    { rewrite lookup_singleton. trivial. } lia.
  - have h : Decision (0 ≤ i < n)%Z by solve_decision. destruct h.
    + rewrite lookup_insert_ne; trivial.
      unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
      rewrite lookup_gmap_zseq; trivial.
      { rewrite lookup_singleton_ne; trivial. }
    + rewrite lookup_insert_ne; trivial.
      unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
      rewrite lookup_gmap_zseq_out; trivial.
      rewrite lookup_singleton_ne; trivial.
Qed.

Lemma sseq_append (n: nat)
  : sseq (S n) = ht_dot (sseq n) (s n None).
Proof.
  unfold sseq, s, ht_dot. rewrite gmap_dot_empty. f_equal.
  cbn [gmap_seq]. apply map_eq. intro.
  have h : Decision (n = i) by solve_decision. destruct h.
  - subst i. rewrite lookup_insert.
    unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
    rewrite lookup_gmap_seq_out.
    { rewrite lookup_singleton. trivial. } lia.
  - have h : Decision (i < n) by solve_decision. destruct h.
    + rewrite lookup_insert_ne; trivial.
      unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
      rewrite lookup_gmap_seq; trivial.
      { rewrite lookup_singleton_ne; trivial. }
    + rewrite lookup_insert_ne; trivial.
      unfold gmap_dot. rewrite lookup_merge. unfold diag_None, gmerge.
      rewrite lookup_gmap_seq_out; trivial.
      rewrite lookup_singleton_ne; trivial.
Qed.
