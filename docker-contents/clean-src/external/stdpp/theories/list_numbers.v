(** This file collects general purpose definitions and theorems on
lists of numbers that are not in the Coq standard library. *)
From stdpp Require Export list.
From stdpp Require Import options.

(** * Definitions *)
(** [seqZ m n] generates the sequence [m], [m + 1], ..., [m + n - 1]
over integers, provided [0 ≤ n]. If [n < 0], then the range is empty. **)
Definition seqZ (m len: Z) : list Z :=
  (λ i: nat, Z.add (Z.of_nat i) m) <$> (seq 0 (Z.to_nat len)).
Global Arguments seqZ : simpl never.

Definition sum_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x + go l
  end.
Notation sum_list := (sum_list_with id).

Definition max_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x `max` go l
  end.
Notation max_list := (max_list_with id).

(** ** Conversion of integers to and from little endian *)
(** [Z_to_little_endian m n z] converts [z] into a list of [m] [n]-bit
integers in the little endian format. A negative [z] is encoded using
two's-complement. If [z] uses more than [m * n] bits, these additional
bits are discarded (see [Z_to_little_endian_to_Z]). [m] and [n] should be
non-negative. *)
Definition Z_to_little_endian (m n : Z) : Z → list Z :=
  Z.iter m (λ rec z, Z.land z (Z.ones n) :: rec (z ≫ n)%Z) (λ _, []).
Global Arguments Z_to_little_endian : simpl never.

(** [little_endian_to_Z n bs] converts the list [bs] of [n]-bit integers
into a number by interpreting [bs] as the little endian encoding.
The integers [b] in [bs] should be in the range [0 ≤ b < 2 ^ n]. *)
Fixpoint little_endian_to_Z (n : Z) (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: bs => Z.lor b (little_endian_to_Z n bs ≪ n)
  end.


(** * Properties *)
(** ** Properties of the [seq] function *)
Section seq.
  Implicit Types m n i j : nat.

  Lemma fmap_add_seq j j' n : Nat.add j <$> seq j' n = seq (j + j') n.
  Proof.
    revert j'. induction n as [|n IH]; intros j'; csimpl; [reflexivity|].
    by rewrite IH, Nat.add_succ_r.
  Qed.
  Lemma fmap_S_seq j n : S <$> seq j n = seq (S j) n.
  Proof. apply (fmap_add_seq 1). Qed.
  Lemma imap_seq {A B} (l : list A) (g : nat → B) i :
    imap (λ j _, g (i + j)) l = g <$> seq i (length l).
  Proof.
    revert i. induction l as [|x l IH]; [done|].
    csimpl. intros n. rewrite <-IH, <-plus_n_O. f_equal.
    apply imap_ext; simpl; auto with lia.
  Qed.
  Lemma imap_seq_0 {A B} (l : list A) (g : nat → B) :
    imap (λ j _, g j) l = g <$> seq 0 (length l).
  Proof. rewrite (imap_ext _ (λ i o, g (0 + i))); [|done]. apply imap_seq. Qed.
  Lemma lookup_seq_lt j n i : i < n → seq j n !! i = Some (j + i).
  Proof.
    revert j i. induction n as [|n IH]; intros j [|i] ?; simpl; auto with lia.
    rewrite IH; auto with lia.
  Qed.
  Lemma lookup_total_seq_lt j n i : i < n → seq j n !!! i = j + i.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seq_lt. Qed.
  Lemma lookup_seq_ge j n i : n ≤ i → seq j n !! i = None.
  Proof. revert j i. induction n; intros j [|i] ?; simpl; auto with lia. Qed.
  Lemma lookup_total_seq_ge j n i : n ≤ i → seq j n !!! i = inhabitant.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seq_ge. Qed.
  Lemma lookup_seq j n i j' : seq j n !! i = Some j' ↔ j' = j + i ∧ i < n.
  Proof.
    destruct (le_lt_dec n i).
    - rewrite lookup_seq_ge by done. naive_solver lia.
    - rewrite lookup_seq_lt by done. naive_solver lia.
  Qed.
  Lemma NoDup_seq j n : NoDup (seq j n).
  Proof. apply NoDup_ListNoDup, seq_NoDup. Qed.
  (* FIXME: This lemma is in the stdlib since Coq 8.12 *)
  Lemma seq_S n j : seq j (S n) = seq j n ++ [j + n].
  Proof.
    revert j. induction n as [|n IH]; intros j; f_equal/=; [done |].
    by rewrite IH, Nat.add_succ_r.
  Qed.

  Lemma elem_of_seq j n k :
    k ∈ seq j n ↔ j ≤ k < j + n.
  Proof. rewrite elem_of_list_In, in_seq. done. Qed.

  Lemma Forall_seq (P : nat → Prop) i n :
    Forall P (seq i n) ↔ ∀ j, i ≤ j < i + n → P j.
  Proof. rewrite Forall_forall. setoid_rewrite elem_of_seq. auto with lia. Qed.
End seq.

(** ** Properties of the [seqZ] function *)
Section seqZ.
  Implicit Types (m n : Z) (i j : nat).
  Local Open Scope Z.

  Lemma seqZ_nil m n : n ≤ 0 → seqZ m n = [].
  Proof. by destruct n. Qed.
  Lemma seqZ_cons m n : 0 < n → seqZ m n = m :: seqZ (Z.succ m) (Z.pred n).
  Proof.
    intros H. unfold seqZ. replace n with (Z.succ (Z.pred n)) at 1 by lia.
    rewrite Z2Nat.inj_succ by lia. f_equal/=.
    rewrite <-fmap_S_seq, <-list_fmap_compose.
    apply map_ext; naive_solver lia.
  Qed.
  Lemma seqZ_length m n : length (seqZ m n) = Z.to_nat n.
  Proof. unfold seqZ; by rewrite fmap_length, seq_length. Qed.
  Lemma fmap_add_seqZ m m' n : Z.add m <$> seqZ m' n = seqZ (m + m') n.
  Proof.
    revert m'. induction n as [|n ? IH|] using (Z_succ_pred_induction 0); intros m'.
    - by rewrite seqZ_nil.
    - rewrite (seqZ_cons m') by lia. rewrite (seqZ_cons (m + m')) by lia.
      f_equal/=. rewrite Z.pred_succ, IH; simpl. f_equal; lia.
    - by rewrite !seqZ_nil by lia.
  Qed.
  Lemma lookup_seqZ_lt m n i : Z.of_nat i < n → seqZ m n !! i = Some (m + Z.of_nat i).
  Proof.
    revert m i. induction n as [|n ? IH|] using (Z_succ_pred_induction 0);
      intros m i Hi; [lia| |lia].
    rewrite seqZ_cons by lia. destruct i as [|i]; simpl.
    - f_equal; lia.
    - rewrite Z.pred_succ, IH by lia. f_equal; lia.
  Qed.
  Lemma lookup_total_seqZ_lt m n i : Z.of_nat i < n → seqZ m n !!! i = m + Z.of_nat i.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seqZ_lt. Qed.
  Lemma lookup_seqZ_ge m n i : n ≤ Z.of_nat i → seqZ m n !! i = None.
  Proof.
    revert m i.
    induction n as [|n ? IH|] using (Z_succ_pred_induction 0); intros m i Hi; try lia.
    - by rewrite seqZ_nil.
    - rewrite seqZ_cons by lia.
      destruct i as [|i]; simpl; [lia|]. by rewrite Z.pred_succ, IH by lia.
    - by rewrite seqZ_nil by lia.
  Qed.
  Lemma lookup_total_seqZ_ge m n i : n ≤ Z.of_nat i → seqZ m n !!! i = inhabitant.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seqZ_ge. Qed.
  Lemma lookup_seqZ m n i m' : seqZ m n !! i = Some m' ↔ m' = m + Z.of_nat i ∧ Z.of_nat i < n.
  Proof.
    destruct (Z_le_gt_dec n (Z.of_nat i)).
    - rewrite lookup_seqZ_ge by lia. naive_solver lia.
    - rewrite lookup_seqZ_lt by lia. naive_solver lia.
  Qed.
  Lemma NoDup_seqZ m n : NoDup (seqZ m n).
  Proof. apply NoDup_fmap_2, NoDup_seq. intros ???; lia. Qed.

  Lemma seqZ_app m n1 n2 :
    0 ≤ n1 →
    0 ≤ n2 →
    seqZ m (n1 + n2) = seqZ m n1 ++ seqZ (m + n1) n2.
  Proof.
    intros. unfold seqZ. rewrite Z2Nat.inj_add, seq_app, fmap_app by done.
    f_equal. rewrite Nat.add_comm, <-!fmap_add_seq, <-list_fmap_compose.
    apply list_fmap_ext; [|done]; intros j; simpl.
    rewrite Nat2Z.inj_add, Z2Nat.id by done. lia.
  Qed.

  Lemma seqZ_S m i : seqZ m (Z.of_nat (S i)) = seqZ m (Z.of_nat i) ++ [m + Z.of_nat i].
  Proof.
    unfold seqZ. rewrite !Nat2Z.id, seq_S, fmap_app.
    simpl. by rewrite Z.add_comm.
  Qed.

  Lemma elem_of_seqZ m n k :
    k ∈ seqZ m n ↔ m ≤ k < m + n.
  Proof.
    rewrite elem_of_list_lookup.
    setoid_rewrite lookup_seqZ. split; [naive_solver lia|].
    exists (Z.to_nat (k - m)). rewrite Z2Nat.id by lia. lia.
  Qed.

  Lemma Forall_seqZ (P : Z → Prop) m n :
    Forall P (seqZ m n) ↔ ∀ m', m ≤ m' < m + n → P m'.
  Proof. rewrite Forall_forall. setoid_rewrite elem_of_seqZ. auto with lia. Qed.
End seqZ.

(** ** Properties of the [sum_list] function *)
Section sum_list.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.
  Lemma sum_list_with_app (f : A → nat) l k :
    sum_list_with f (l ++ k) = sum_list_with f l + sum_list_with f k.
  Proof. induction l; simpl; lia. Qed.
  Lemma sum_list_with_reverse (f : A → nat) l :
    sum_list_with f (reverse l) = sum_list_with f l.
  Proof.
    induction l; simpl; rewrite ?reverse_cons, ?sum_list_with_app; simpl; lia.
  Qed.
  Lemma sum_list_with_in x (f : A → nat) ls : x ∈ ls → f x ≤ sum_list_with f ls.
  Proof. induction 1; simpl; lia. Qed.
  Lemma join_reshape szs l :
    sum_list szs = length l → mjoin (reshape szs l) = l.
  Proof.
    revert l. induction szs as [|sz szs IH]; simpl; intros l Hl; [by destruct l|].
    by rewrite IH, take_drop by (rewrite drop_length; lia).
  Qed.
  Lemma sum_list_replicate n m : sum_list (replicate m n) = m * n.
  Proof. induction m; simpl; auto. Qed.
End sum_list.

(** ** Properties of the [max_list] function *)
Section max_list.
  Context {A : Type}.

  Lemma max_list_elem_of_le n ns :
    n ∈ ns → n ≤ max_list ns.
  Proof. induction 1; simpl; lia. Qed.

  Lemma max_list_not_elem_of_gt n ns : max_list ns < n → n ∉ ns.
  Proof. intros ??%max_list_elem_of_le. lia. Qed.

  Lemma max_list_elem_of ns : ns ≠ [] → max_list ns ∈ ns.
  Proof.
    intros. induction ns as [|n ns IHns]; [done|]. simpl.
    destruct (Nat.max_spec n (max_list ns)) as [[? ->]|[? ->]].
    - destruct ns.
      + simpl in *. lia.
      + by apply elem_of_list_further, IHns.
    - apply elem_of_list_here.
  Qed.
End max_list.

(** ** Properties of the [Z_to_little_endian] and [little_endian_to_Z] functions *)
Section Z_little_endian.
  Local Open Scope Z_scope.
  Implicit Types m n z : Z.

  Lemma Z_to_little_endian_succ m n z :
    0 ≤ m →
    Z_to_little_endian (Z.succ m) n z
    = Z.land z (Z.ones n) :: Z_to_little_endian m n (z ≫ n).
  Proof.
    unfold Z_to_little_endian. intros.
    by rewrite !iter_nat_of_Z, Zabs2Nat.inj_succ by lia.
  Qed.

  Lemma Z_to_little_endian_to_Z m n bs:
    m = Z.of_nat (length bs) → 0 ≤ n →
    Forall (λ b, 0 ≤ b < 2 ^ n) bs →
    Z_to_little_endian m n (little_endian_to_Z n bs) = bs.
  Proof.
    intros -> ?. induction 1 as [|b bs ? ? IH]; [done|]; simpl.
    rewrite Nat2Z.inj_succ, Z_to_little_endian_succ by lia. f_equal.
    - apply Z.bits_inj_iff'. intros z' ?.
      rewrite !Z.land_spec, Z.lor_spec, Z_ones_spec by lia.
      case_bool_decide.
      + rewrite andb_true_r, Z.shiftl_spec_low, orb_false_r by lia. done.
      + rewrite andb_false_r.
        symmetry. eapply (Z_bounded_iff_bits_nonneg n); lia.
    - rewrite <-IH at 3. f_equal.
      apply Z.bits_inj_iff'. intros z' ?.
      rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
      assert (Z.testbit b (z' + n) = false) as ->.
      { apply (Z_bounded_iff_bits_nonneg n); lia. }
      rewrite orb_false_l. f_equal. lia.
  Qed.

  (* TODO: replace the calls to [nia] by [lia] after dropping support for Coq 8.10.2. *)
  Lemma little_endian_to_Z_to_little_endian m n z:
    0 ≤ n → 0 ≤ m →
    little_endian_to_Z n (Z_to_little_endian m n z) = z `mod` 2 ^ (m * n).
  Proof.
    intros ? Hm. rewrite <-Z.land_ones by nia.
    revert z.
    induction m as [|m ? IH|] using (Z_succ_pred_induction 0); intros z; [..|lia].
    { Z.bitwise. by rewrite andb_false_r. }
    rewrite Z_to_little_endian_succ by lia; simpl. rewrite IH by lia.
    apply Z.bits_inj_iff'. intros z' ?.
    rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec, !Z.land_spec by lia.
    rewrite (Z_ones_spec n z') by lia. case_bool_decide.
    - rewrite andb_true_r, (Z.testbit_neg_r _ (z' - n)), orb_false_r by lia. simpl.
      by rewrite Z_ones_spec, bool_decide_true, andb_true_r by nia.
    - rewrite andb_false_r, orb_false_l.
      rewrite Z.shiftr_spec by lia. f_equal; [f_equal; lia|].
      rewrite !Z_ones_spec by nia. apply bool_decide_iff. lia.
  Qed.

  Lemma Z_to_little_endian_length m n z :
    0 ≤ m →
    Z.of_nat (length (Z_to_little_endian m n z)) = m.
  Proof.
    intros. revert z. induction m as [|m ? IH|]
      using (Z_succ_pred_induction 0); intros z; [done| |lia].
    rewrite Z_to_little_endian_succ by lia. simpl. by rewrite Nat2Z.inj_succ, IH.
  Qed.

  Lemma Z_to_little_endian_bound m n z:
    0 ≤ n → 0 ≤ m →
    Forall (λ b, 0 ≤ b < 2 ^ n) (Z_to_little_endian m n z).
  Proof.
    intros. revert z.
    induction m as [|m ? IH|] using (Z_succ_pred_induction 0); intros z; [..|lia].
    { by constructor. }
    rewrite Z_to_little_endian_succ by lia.
    constructor; [|by apply IH]. rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia.
  Qed.

  Lemma little_endian_to_Z_bound n bs:
    0 ≤ n →
    Forall (λ b, 0 ≤ b < 2 ^ n) bs →
    0 ≤ little_endian_to_Z n bs < 2 ^ (Z.of_nat (length bs) * n).
  Proof.
    intros ?. induction 1 as [|b bs Hb ? IH]; [done|]; simpl.
    apply Z_bounded_iff_bits_nonneg'; [nia|..].
    { apply Z.lor_nonneg. split; [lia|]. apply Z.shiftl_nonneg. lia. }
    intros z' ?. rewrite Z.lor_spec.
    rewrite Z_bounded_iff_bits_nonneg' in Hb by lia.
    rewrite Hb, orb_false_l, Z.shiftl_spec by nia.
    apply (Z_bounded_iff_bits_nonneg' (Z.of_nat (length bs) * n)); nia.
  Qed.
End Z_little_endian.
