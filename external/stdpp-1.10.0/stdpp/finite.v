From stdpp Require Export countable vector.
From stdpp Require Import options.

Class Finite A `{EqDecision A} := {
  enum : list A;
  (* [NoDup] makes it easy to define the cardinality of the type. *)
  NoDup_enum : NoDup enum;
  elem_of_enum x : x ∈ enum
}.
Global Hint Mode Finite ! - : typeclass_instances.
Global Arguments enum : clear implicits.
Global Arguments enum _ {_ _} : assert.
Global Arguments NoDup_enum : clear implicits.
Global Arguments NoDup_enum _ {_ _} : assert.
Definition card A `{Finite A} := length (enum A).

Program Definition finite_countable `{Finite A} : Countable A := {|
  encode := λ x,
    Pos.of_nat $ S $ default 0 $ fst <$> list_find (x =.) (enum A);
  decode := λ p, enum A !! pred (Pos.to_nat p)
|}.
Next Obligation.
  intros ?? [xs Hxs HA] x; unfold encode, decode; simpl.
  destruct (list_find_elem_of (x =.) xs x) as [[i y] Hi]; auto.
  rewrite Nat2Pos.id by done; simpl; rewrite Hi; simpl.
  destruct (list_find_Some (x =.) xs i y); naive_solver.
Qed.
Global Hint Immediate finite_countable : typeclass_instances.

Definition find `{Finite A} (P : A → Prop) `{∀ x, Decision (P x)} : option A :=
  list_find P (enum A) ≫= decode_nat ∘ fst.

Lemma encode_lt_card `{finA: Finite A} (x : A) : encode_nat x < card A.
Proof.
  destruct finA as [xs Hxs HA]; unfold encode_nat, encode, card; simpl.
  rewrite Nat2Pos.id by done; simpl.
  destruct (list_find _ xs) as [[i y]|] eqn:HE; simpl.
  - apply list_find_Some in HE as (?&?&?); eauto using lookup_lt_Some.
  - destruct xs; simpl; [|lia].
    exfalso; eapply not_elem_of_nil, (HA x).
Qed.
Lemma encode_decode A `{finA: Finite A} i :
  i < card A → ∃ x : A, decode_nat i = Some x ∧ encode_nat x = i.
Proof.
  destruct finA as [xs Hxs HA].
  unfold encode_nat, decode_nat, encode, decode, card; simpl.
  intros Hi. apply lookup_lt_is_Some in Hi. destruct Hi as [x Hx].
  exists x. rewrite !Nat2Pos.id by done; simpl.
  destruct (list_find_elem_of (x =.) xs x) as [[j y] Hj]; auto.
  split; [done|]; rewrite Hj; simpl.
  apply list_find_Some in Hj as (?&->&?). eauto using NoDup_lookup.
Qed.
Lemma find_Some `{finA: Finite A} (P : A → Prop) `{∀ x, Decision (P x)} (x : A) :
  find P = Some x → P x.
Proof.
  destruct finA as [xs Hxs HA]; unfold find, decode_nat, decode; simpl.
  intros Hx. destruct (list_find _ _) as [[i y]|] eqn:Hi; simplify_eq/=.
  rewrite !Nat2Pos.id in Hx by done.
  destruct (list_find_Some P xs i y); naive_solver.
Qed.
Lemma find_is_Some `{finA: Finite A} (P : A → Prop) `{∀ x, Decision (P x)} (x : A) :
  P x → ∃ y, find P = Some y ∧ P y.
Proof.
  destruct finA as [xs Hxs HA]; unfold find, decode; simpl.
  intros Hx. destruct (list_find_elem_of P xs x) as [[i y] Hi]; auto.
  rewrite Hi; unfold decode_nat, decode; simpl. rewrite !Nat2Pos.id by done.
  simpl. apply list_find_Some in Hi; naive_solver.
Qed.

Definition encode_fin `{Finite A} (x : A) : fin (card A) :=
  Fin.of_nat_lt (encode_lt_card x).
Program Definition decode_fin `{Finite A} (i : fin (card A)) : A :=
  match Some_dec (decode_nat i) return _ with
  | inleft (x ↾ _) => x | inright _ => _
  end.
Next Obligation.
  intros A ?? i ?; exfalso.
  destruct (encode_decode A i); naive_solver auto using fin_to_nat_lt.
Qed.
Lemma decode_encode_fin `{Finite A} (x : A) : decode_fin (encode_fin x) = x.
Proof.
  unfold decode_fin, encode_fin. destruct (Some_dec _) as [[x' Hx]|Hx].
  { by rewrite fin_to_nat_to_fin, decode_encode_nat in Hx; simplify_eq. }
  exfalso; by rewrite ->fin_to_nat_to_fin, decode_encode_nat in Hx.
Qed.

Lemma fin_choice {n} {B : fin n → Type} (P : ∀ i, B i → Prop) :
  (∀ i, ∃ y, P i y) → ∃ f, ∀ i, P i (f i).
Proof.
  induction n as [|n IH]; intros Hex.
  { exists (fin_0_inv _); intros i; inv_fin i. }
  destruct (IH _ _ (λ i, Hex (FS i))) as [f Hf], (Hex 0%fin) as [y Hy].
  exists (fin_S_inv _ y f); intros i; by inv_fin i.
Qed.
Lemma finite_choice `{Finite A} {B : A → Type} (P : ∀ x, B x → Prop) :
  (∀ x, ∃ y, P x y) → ∃ f, ∀ x, P x (f x).
Proof.
  intros Hex. destruct (fin_choice _ (λ i, Hex (decode_fin i))) as [f ?].
  exists (λ x, eq_rect _ _ (f(encode_fin x)) _ (decode_encode_fin x)); intros x.
  destruct (decode_encode_fin x); simpl; auto.
Qed.

Lemma card_0_inv P `{finA: Finite A} : card A = 0 → A → P.
Proof.
  intros ? x. destruct finA as [[|??] ??]; simplify_eq.
  by destruct (not_elem_of_nil x).
Qed.
Lemma finite_inhabited A `{finA: Finite A} : 0 < card A → Inhabited A.
Proof.
  unfold card; intros. destruct finA as [[|x ?] ??]; simpl in *; [exfalso;lia|].
  constructor; exact x.
Qed.
Lemma finite_inj_submseteq `{finA: Finite A} `{finB: Finite B} (f: A → B)
  `{!Inj (=) (=) f} : f <$> enum A ⊆+ enum B.
Proof.
  intros. destruct finA, finB. apply NoDup_submseteq; auto using NoDup_fmap_2.
Qed.
Lemma finite_inj_Permutation `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} : card A = card B → f <$> enum A ≡ₚ enum B.
Proof.
  intros. apply submseteq_length_Permutation.
  - by apply finite_inj_submseteq.
  - rewrite fmap_length. by apply Nat.eq_le_incl.
Qed.
Lemma finite_inj_surj `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} : card A = card B → Surj (=) f.
Proof.
  intros HAB y. destruct (elem_of_list_fmap_2 f (enum A) y) as (x&?&?); eauto.
  rewrite finite_inj_Permutation; auto using elem_of_enum.
Qed.

Lemma finite_surj A `{Finite A} B `{Finite B} :
  0 < card A ≤ card B → ∃ g : B → A, Surj (=) g.
Proof.
  intros [??]. destruct (finite_inhabited A) as [x']; auto with lia.
  exists (λ y : B, default x' (decode_nat (encode_nat y))).
  intros x. destruct (encode_decode B (encode_nat x)) as (y&Hy1&Hy2).
  { pose proof (encode_lt_card x); lia. }
  exists y. by rewrite Hy2, decode_encode_nat.
Qed.
Lemma finite_inj A `{Finite A} B `{Finite B} :
  card A ≤ card B ↔ ∃ f : A → B, Inj (=) (=) f.
Proof.
  split.
  - intros. destruct (decide (card A = 0)) as [HA|?].
    { exists (card_0_inv B HA). intros y. apply (card_0_inv _ HA y). }
    destruct (finite_surj A B) as (g&?); auto with lia.
    destruct (surj_cancel g) as (f&?). exists f. apply cancel_inj.
  - intros [f ?]. unfold card. rewrite <-(fmap_length f).
    by apply submseteq_length, (finite_inj_submseteq f).
Qed.
Lemma finite_bijective A `{Finite A} B `{Finite B} :
  card A = card B ↔ ∃ f : A → B, Inj (=) (=) f ∧ Surj (=) f.
Proof.
  split.
  - intros; destruct (proj1 (finite_inj A B)) as [f ?]; auto with lia.
    exists f; split; [done|]. by apply finite_inj_surj.
  - intros (f&?&?). apply (anti_symm (≤)); apply finite_inj.
    + by exists f.
    + destruct (surj_cancel f) as (g&?). exists g. apply cancel_inj.
Qed.
Lemma inj_card `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} : card A ≤ card B.
Proof. apply finite_inj. eauto. Qed.
Lemma surj_card `{Finite A} `{Finite B} (f : A → B)
  `{!Surj (=) f} : card B ≤ card A.
Proof.
  destruct (surj_cancel f) as (g&?).
  apply inj_card with g, cancel_inj.
Qed.
Lemma bijective_card `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} `{!Surj (=) f} : card A = card B.
Proof. apply finite_bijective. eauto. Qed.

(** Decidability of quantification over finite types *)
Section forall_exists.
  Context `{Finite A} (P : A → Prop).

  Lemma Forall_finite : Forall P (enum A) ↔ (∀ x, P x).
  Proof. rewrite Forall_forall. intuition auto using elem_of_enum. Qed.
  Lemma Exists_finite : Exists P (enum A) ↔ (∃ x, P x).
  Proof. rewrite Exists_exists. naive_solver eauto using elem_of_enum. Qed.

  Context `{∀ x, Decision (P x)}.

  Global Instance forall_dec: Decision (∀ x, P x).
  Proof using Type*.
   refine (cast_if (decide (Forall P (enum A))));
    abstract by rewrite <-Forall_finite.
  Defined.
  Global Instance exists_dec: Decision (∃ x, P x).
  Proof using Type*.
   refine (cast_if (decide (Exists P (enum A))));
    abstract by rewrite <-Exists_finite.
  Defined.
End forall_exists.

(** Instances *)
Section enc_finite.
  Context `{EqDecision A}.
  Context (to_nat : A → nat) (of_nat : nat → A) (c : nat).
  Context (of_to_nat : ∀ x, of_nat (to_nat x) = x).
  Context (to_nat_c : ∀ x, to_nat x < c).
  Context (to_of_nat : ∀ i, i < c → to_nat (of_nat i) = i).

  Local Program Instance enc_finite : Finite A := {| enum := of_nat <$> seq 0 c |}.
  Next Obligation.
    apply NoDup_alt. intros i j x. rewrite !list_lookup_fmap. intros Hi Hj.
    destruct (seq _ _ !! i) as [i'|] eqn:Hi',
      (seq _ _ !! j) as [j'|] eqn:Hj'; simplify_eq/=.
    apply lookup_seq in Hi' as  [-> ?]. apply lookup_seq in Hj' as [-> ?].
    rewrite <-(to_of_nat i), <-(to_of_nat j) by done. by f_equal.
  Qed.
  Next Obligation.
    intros x. rewrite elem_of_list_fmap. exists (to_nat x).
    split; auto. by apply elem_of_list_lookup_2 with (to_nat x), lookup_seq.
  Qed.
  Lemma enc_finite_card : card A = c.
  Proof. unfold card. simpl. by rewrite fmap_length, seq_length. Qed.
End enc_finite.

(** If we have a surjection [f : A → B] and [A] is finite, then [B] is finite
too. The surjection [f] could map multiple [x : A] on the same [B], so we
need to remove duplicates in [enum]. If [f] is injective, we do not need to do that,
leading to a potentially faster implementation of [enum], see [bijective_finite]
below. *)
Section surjective_finite.
  Context `{Finite A, EqDecision B} (f : A → B).
  Context `{!Surj (=) f}.

  Program Definition surjective_finite: Finite B :=
    {| enum := remove_dups (f <$> enum A) |}.
  Next Obligation. apply NoDup_remove_dups. Qed.
  Next Obligation.
    intros y. rewrite elem_of_remove_dups, elem_of_list_fmap.
    destruct (surj f y). eauto using elem_of_enum.
  Qed.
End surjective_finite.

Section bijective_finite.
  Context `{Finite A, EqDecision B} (f : A → B).
  Context `{!Inj (=) (=) f, !Surj (=) f}.

  Program Definition bijective_finite : Finite B :=
    {| enum := f <$> enum A |}.
  Next Obligation. apply (NoDup_fmap f), NoDup_enum. Qed.
  Next Obligation.
    intros b. rewrite elem_of_list_fmap. destruct (surj f b).
    eauto using elem_of_enum.
  Qed.
End bijective_finite.

Global Program Instance option_finite `{Finite A} : Finite (option A) :=
  {| enum := None :: (Some <$> enum A) |}.
Next Obligation.
  constructor.
  - rewrite elem_of_list_fmap. by intros (?&?&?).
  - apply (NoDup_fmap_2 _); auto using NoDup_enum.
Qed.
Next Obligation.
  intros ??? [x|]; [right|left]; auto.
  apply elem_of_list_fmap. eauto using elem_of_enum.
Qed.
Lemma option_cardinality `{Finite A} : card (option A) = S (card A).
Proof. unfold card. simpl. by rewrite fmap_length. Qed.

Global Program Instance Empty_set_finite : Finite Empty_set := {| enum := [] |}.
Next Obligation. by apply NoDup_nil. Qed.
Next Obligation. intros []. Qed.
Lemma Empty_set_card : card Empty_set = 0.
Proof. done. Qed.

Global Program Instance unit_finite : Finite () := {| enum := [tt] |}.
Next Obligation. apply NoDup_singleton. Qed.
Next Obligation. intros []. by apply elem_of_list_singleton. Qed.
Lemma unit_card : card unit = 1.
Proof. done. Qed.

Global Program Instance bool_finite : Finite bool := {| enum := [true; false] |}.
Next Obligation.
  constructor; [ by rewrite elem_of_list_singleton | apply NoDup_singleton ].
Qed.
Next Obligation. intros [|]; [ left | right; left ]. Qed.
Lemma bool_card : card bool = 2.
Proof. done. Qed.

Global Program Instance sum_finite `{Finite A, Finite B} : Finite (A + B)%type :=
  {| enum := (inl <$> enum A) ++ (inr <$> enum B) |}.
Next Obligation.
  intros. apply NoDup_app; split_and?.
  - apply (NoDup_fmap_2 _). by apply NoDup_enum.
  - intro. rewrite !elem_of_list_fmap. intros (?&?&?) (?&?&?); congruence.
  - apply (NoDup_fmap_2 _). by apply NoDup_enum.
Qed.
Next Obligation.
  intros ?????? [x|y]; rewrite elem_of_app, !elem_of_list_fmap;
    [left|right]; (eexists; split; [done|apply elem_of_enum]).
Qed.
Lemma sum_card `{Finite A, Finite B} : card (A + B) = card A + card B.
Proof. unfold card. simpl. by rewrite app_length, !fmap_length. Qed.

Global Program Instance prod_finite `{Finite A, Finite B} : Finite (A * B)%type :=
  {| enum := a ← enum A; (a,.) <$> enum B |}.
Next Obligation.
  intros A ?????. apply NoDup_bind.
  - intros a1 a2 [a b] ?? (?&?&_)%elem_of_list_fmap (?&?&_)%elem_of_list_fmap.
    naive_solver.
  - intros a ?. rewrite (NoDup_fmap _). apply NoDup_enum.
  - apply NoDup_enum.
Qed.
Next Obligation.
  intros ?????? [a b]. apply elem_of_list_bind.
  exists a. eauto using elem_of_enum, elem_of_list_fmap_1.
Qed.
Lemma prod_card `{Finite A} `{Finite B} : card (A * B) = card A * card B.
Proof.
  unfold card; simpl. induction (enum A); simpl; auto.
  rewrite app_length, fmap_length. auto.
Qed.

Fixpoint vec_enum {A} (l : list A) (n : nat) : list (vec A n) :=
  match n with
  | 0 => [[#]]
  | S m => a ← l; vcons a <$> vec_enum l m
  end.

Global Program Instance vec_finite `{Finite A} n : Finite (vec A n) :=
  {| enum := vec_enum (enum A) n |}.
Next Obligation.
  intros A ?? n. induction n as [|n IH]; csimpl; [apply NoDup_singleton|].
  apply NoDup_bind.
  - intros x1 x2 y ?? (?&?&_)%elem_of_list_fmap (?&?&_)%elem_of_list_fmap.
    congruence.
  - intros x ?. rewrite NoDup_fmap by (intros ?; apply vcons_inj_2). done.
  - apply NoDup_enum.
Qed.
Next Obligation.
  intros A ?? n v. induction v as [|x n v IH]; csimpl; [apply elem_of_list_here|].
  apply elem_of_list_bind. eauto using elem_of_enum, elem_of_list_fmap_1.
Qed.
Lemma vec_card `{Finite A} n : card (vec A n) = card A ^ n.
Proof.
  unfold card; simpl. induction n as [|n IH]; simpl; [done|].
  rewrite <-IH. clear IH. generalize (vec_enum (enum A) n).
  induction (enum A) as [|x xs IH]; intros l; csimpl; auto.
  by rewrite app_length, fmap_length, IH.
Qed.

Global Instance list_finite `{Finite A} n : Finite { l : list A | length l = n }.
Proof.
  refine (bijective_finite (λ v : vec A n, vec_to_list v ↾ vec_to_list_length _)).
  - abstract (by intros v1 v2 [= ?%vec_to_list_inj2]).
  - abstract (intros [l <-]; exists (list_to_vec l);
      apply (sig_eq_pi _), vec_to_list_to_vec).
Defined.
Lemma list_card `{Finite A} n : card { l : list A | length l = n } = card A ^ n.
Proof. unfold card; simpl. rewrite fmap_length. apply vec_card. Qed.

Fixpoint fin_enum (n : nat) : list (fin n) :=
  match n with 0 => [] | S n => 0%fin :: (FS <$> fin_enum n) end.
Global Program Instance fin_finite n : Finite (fin n) := {| enum := fin_enum n |}.
Next Obligation.
  intros n. induction n; simpl; constructor.
  - rewrite elem_of_list_fmap. by intros (?&?&?).
  - by apply (NoDup_fmap _).
Qed.
Next Obligation.
  intros n i. induction i as [|n i IH]; simpl;
    rewrite elem_of_cons, ?elem_of_list_fmap; eauto.
Qed.
Lemma fin_card n : card (fin n) = n.
Proof. unfold card; simpl. induction n; simpl; rewrite ?fmap_length; auto. Qed.

(* shouldn’t be an instance (cycle with [sig_finite]): *)
Lemma finite_sig_dec `{!EqDecision A} (P : A → Prop) `{Finite (sig P)} x :
  Decision (P x).
Proof.
  assert {xs : list A | ∀ x, P x ↔ x ∈ xs} as [xs ?].
  { clear x. exists (proj1_sig <$> enum _). intros x. split; intros Hx.
    - apply elem_of_list_fmap_1_alt with (x ↾ Hx); [apply elem_of_enum|]; done.
    - apply elem_of_list_fmap in Hx as [[x' Hx'] [-> _]]; done. }
  destruct (decide (x ∈ xs)); [left | right]; naive_solver.
Qed. (* <- could be Defined but this lemma will probably not be used for computing *)

Section sig_finite.
  Context {A} (P : A → Prop) `{∀ x, Decision (P x)}.

  Fixpoint list_filter_sig (l : list A) : list (sig P) :=
    match l with
    | [] => []
    | x :: l => match decide (P x) with
              | left H => x ↾ H :: list_filter_sig l
              | _ => list_filter_sig l
              end
    end.
  Lemma list_filter_sig_filter (l : list A) :
    proj1_sig <$> list_filter_sig l = filter P l.
  Proof.
    induction l as [| a l IH]; [done |].
    simpl; rewrite filter_cons.
    destruct (decide _); csimpl; by rewrite IH.
  Qed.

  Context `{Finite A} `{∀ x, ProofIrrel (P x)}.

  Global Program Instance sig_finite : Finite (sig P) :=
    {| enum := list_filter_sig (enum A) |}.
  Next Obligation.
    eapply NoDup_fmap_1. rewrite list_filter_sig_filter.
    apply NoDup_filter, NoDup_enum.
  Qed.
  Next Obligation.
    intros p. apply (elem_of_list_fmap_2_inj proj1_sig).
    rewrite list_filter_sig_filter, elem_of_list_filter.
    split; [by destruct p | apply elem_of_enum].
  Qed.
  Lemma sig_card : card (sig P) = length (filter P (enum A)).
  Proof. by rewrite <-list_filter_sig_filter, fmap_length. Qed.
End sig_finite.

Lemma finite_pigeonhole `{Finite A} `{Finite B} (f : A → B) :
  card B < card A → ∃ x1 x2, x1 ≠ x2 ∧ f x1 = f x2.
Proof.
  intros. apply dec_stable; intros Heq.
  cut (Inj eq eq f); [intros ?%inj_card; lia|].
  intros x1 x2 ?. apply dec_stable. naive_solver.
Qed.

Lemma nat_pigeonhole (f : nat → nat) (n1 n2 : nat) :
  n2 < n1 →
  (∀ i, i < n1 → f i < n2) →
  ∃ i1 i2, i1 < i2 < n1 ∧ f i1 = f i2.
Proof.
  intros Hn Hf. pose (f' (i : fin n1) := nat_to_fin (Hf _ (fin_to_nat_lt i))).
  destruct (finite_pigeonhole f') as (i1&i2&Hi&Hf'); [by rewrite !fin_card|].
  apply (not_inj (f:=fin_to_nat)) in Hi. apply (f_equal fin_to_nat) in Hf'.
  unfold f' in Hf'. rewrite !fin_to_nat_to_fin in Hf'.
  pose proof (fin_to_nat_lt i1); pose proof (fin_to_nat_lt i2).
  destruct (decide (i1 < i2)); [exists i1, i2|exists i2, i1]; lia.
Qed.

Lemma list_pigeonhole {A} (l1 l2 : list A) :
  l1 ⊆ l2 →
  length l2 < length l1 →
  ∃ i1 i2 x, i1 < i2 ∧ l1 !! i1 = Some x ∧ l1 !! i2 = Some x.
Proof.
  intros Hl Hlen.
  assert (∀ i : fin (length l1), ∃ (j : fin (length l2)) x,
    l1 !! (fin_to_nat i) = Some x ∧
    l2 !! (fin_to_nat j) = Some x) as [f Hf]%fin_choice.
  { intros i. destruct (lookup_lt_is_Some_2 l1 i)
      as [x Hix]; [apply fin_to_nat_lt|].
    assert (x ∈ l2) as [j Hjx]%elem_of_list_lookup_1
      by (by eapply Hl, elem_of_list_lookup_2).
    exists (nat_to_fin (lookup_lt_Some _ _ _ Hjx)), x.
    by rewrite fin_to_nat_to_fin. }
  destruct (finite_pigeonhole f) as (i1&i2&Hi&Hf'); [by rewrite !fin_card|].
  destruct (Hf i1) as (x1&?&?), (Hf i2) as (x2&?&?).
  assert (x1 = x2) as -> by congruence.
  apply (not_inj (f:=fin_to_nat)) in Hi. apply (f_equal fin_to_nat) in Hf'.
  destruct (decide (i1 < i2)); [exists i1, i2|exists i2, i1]; eauto with lia.
Qed.
