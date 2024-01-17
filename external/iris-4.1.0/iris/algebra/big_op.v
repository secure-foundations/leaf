From stdpp Require Export functions gmap gmultiset.
From iris.algebra Require Export monoid.
From iris.prelude Require Import options.
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

(** We define the following big operators with binders build in:

- The operator [ [^o list] k ↦ x ∈ l, P ] folds over a list [l]. The binder [x]
  refers to each element at index [k].
- The operator [ [^o map] k ↦ x ∈ m, P ] folds over a map [m]. The binder [x]
  refers to each element at index [k].
- The operator [ [^o set] x ∈ X, P ] folds over a set [X]. The binder [x] refers
  to each element.

Since these big operators are like quantifiers, they have the same precedence as
[∀] and [∃]. *)

(** * Big ops over lists *)
Fixpoint big_opL {M : ofe} {o : M → M → M} `{!Monoid o} {A} (f : nat → A → M) (xs : list A) : M :=
  match xs with
  | [] => monoid_unit
  | x :: xs => o (f 0 x) (big_opL (λ n, f (S n)) xs)
  end.
Global Instance: Params (@big_opL) 4 := {}.
Global Arguments big_opL {M} o {_ A} _ !_ /.
Global Typeclasses Opaque big_opL.
Notation "'[^' o 'list]' k ↦ x ∈ l , P" := (big_opL o (λ k x, P) l)
  (at level 200, o at level 1, l at level 10, k, x at level 1, right associativity,
   format "[^ o  list]  k ↦ x  ∈  l ,  P") : stdpp_scope.
Notation "'[^' o 'list]' x ∈ l , P" := (big_opL o (λ _ x, P) l)
  (at level 200, o at level 1, l at level 10, x at level 1, right associativity,
   format "[^ o  list]  x  ∈  l ,  P") : stdpp_scope.

Local Definition big_opM_def {M : ofe} {o : M → M → M} `{!Monoid o} `{Countable K} {A} (f : K → A → M)
  (m : gmap K A) : M := big_opL o (λ _, uncurry f) (map_to_list m).
Local Definition big_opM_aux : seal (@big_opM_def). Proof. by eexists. Qed.
Definition big_opM := big_opM_aux.(unseal).
Global Arguments big_opM {M} o {_ K _ _ A} _ _.
Local Definition big_opM_unseal :
  @big_opM = @big_opM_def := big_opM_aux.(seal_eq).
Global Instance: Params (@big_opM) 7 := {}.
Notation "'[^' o 'map]' k ↦ x ∈ m , P" := (big_opM o (λ k x, P) m)
  (at level 200, o at level 1, m at level 10, k, x at level 1, right associativity,
   format "[^  o  map]  k ↦ x  ∈  m ,  P") : stdpp_scope.
Notation "'[^' o 'map]' x ∈ m , P" := (big_opM o (λ _ x, P) m)
  (at level 200, o at level 1, m at level 10, x at level 1, right associativity,
   format "[^ o  map]  x  ∈  m ,  P") : stdpp_scope.

Local Definition big_opS_def {M : ofe} {o : M → M → M} `{!Monoid o} `{Countable A} (f : A → M)
  (X : gset A) : M := big_opL o (λ _, f) (elements X).
Local Definition big_opS_aux : seal (@big_opS_def). Proof. by eexists. Qed.
Definition big_opS := big_opS_aux.(unseal).
Global Arguments big_opS {M} o {_ A _ _} _ _.
Local Definition big_opS_unseal :
  @big_opS = @big_opS_def := big_opS_aux.(seal_eq).
Global Instance: Params (@big_opS) 6 := {}.
Notation "'[^' o 'set]' x ∈ X , P" := (big_opS o (λ x, P) X)
  (at level 200, o at level 1, X at level 10, x at level 1, right associativity,
   format "[^ o  set]  x  ∈  X ,  P") : stdpp_scope.

Local Definition big_opMS_def {M : ofe} {o : M → M → M} `{!Monoid o} `{Countable A} (f : A → M)
  (X : gmultiset A) : M := big_opL o (λ _, f) (elements X).
Local Definition big_opMS_aux : seal (@big_opMS_def). Proof. by eexists. Qed.
Definition big_opMS := big_opMS_aux.(unseal).
Global Arguments big_opMS {M} o {_ A _ _} _ _.
Local Definition big_opMS_unseal :
  @big_opMS = @big_opMS_def := big_opMS_aux.(seal_eq).
Global Instance: Params (@big_opMS) 6 := {}.
Notation "'[^' o 'mset]' x ∈ X , P" := (big_opMS o (λ x, P) X)
  (at level 200, o at level 1, X at level 10, x at level 1, right associativity,
   format "[^ o  mset]  x  ∈  X ,  P") : stdpp_scope.

(** * Properties about big ops *)
Section big_op.
Context {M : ofe} {o : M → M → M} `{!Monoid o}.
Implicit Types xs : list M.
Infix "`o`" := o (at level 50, left associativity).

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : nat → A → M.

  Lemma big_opL_nil f : ([^o list] k↦y ∈ [], f k y) = monoid_unit.
  Proof. done. Qed.
  Lemma big_opL_cons f x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (S k) y.
  Proof. done. Qed.
  Lemma big_opL_singleton f x : ([^o list] k↦y ∈ [x], f k y) ≡ f 0 x.
  Proof. by rewrite /= right_id. Qed.
  Lemma big_opL_app f l1 l2 :
    ([^o list] k↦y ∈ l1 ++ l2, f k y)
    ≡ ([^o list] k↦y ∈ l1, f k y) `o` ([^o list] k↦y ∈ l2, f (length l1 + k) y).
  Proof.
    revert f. induction l1 as [|x l1 IH]=> f /=; first by rewrite left_id.
    by rewrite IH assoc.
  Qed.
  Lemma big_opL_snoc f l x :
    ([^o list] k↦y ∈ l ++ [x], f k y) ≡ ([^o list] k↦y ∈ l, f k y) `o` f (length l) x.
  Proof. rewrite big_opL_app big_opL_singleton Nat.add_0_r //. Qed.

  Lemma big_opL_unit l : ([^o list] k↦y ∈ l, monoid_unit) ≡ (monoid_unit : M).
  Proof. induction l; rewrite /= ?left_id //. Qed.

  Lemma big_opL_take_drop Φ l n :
    ([^o list] k ↦ x ∈ l, Φ k x) ≡
    ([^o list] k ↦ x ∈ take n l, Φ k x) `o` ([^o list] k ↦ x ∈ drop n l, Φ (n + k) x).
  Proof.
    rewrite -{1}(take_drop n l) big_opL_app take_length.
    destruct (decide (length l ≤ n)).
    - rewrite drop_ge //=.
    - rewrite Nat.min_l //=; lia.
  Qed.

  Lemma big_opL_gen_proper_2 {B} (R : relation M) f (g : nat → B → M)
        l1 (l2 : list B) :
    R monoid_unit monoid_unit →
    Proper (R ==> R ==> R) o →
    (∀ k,
      match l1 !! k, l2 !! k with
      | Some y1, Some y2 => R (f k y1) (g k y2)
      | None, None => True
      | _, _ => False
      end) →
    R ([^o list] k ↦ y ∈ l1, f k y) ([^o list] k ↦ y ∈ l2, g k y).
  Proof.
    intros ??. revert l2 f g. induction l1 as [|x1 l1 IH]=> -[|x2 l2] //= f g Hfg.
    - by specialize (Hfg 0).
    - by specialize (Hfg 0).
    - f_equiv; [apply (Hfg 0)|]. apply IH. intros k. apply (Hfg (S k)).
  Qed.
  Lemma big_opL_gen_proper R f g l :
    Reflexive R →
    Proper (R ==> R ==> R) o →
    (∀ k y, l !! k = Some y → R (f k y) (g k y)) →
    R ([^o list] k ↦ y ∈ l, f k y) ([^o list] k ↦ y ∈ l, g k y).
  Proof.
    intros. apply big_opL_gen_proper_2; [done..|].
    intros k. destruct (l !! k) eqn:?; auto.
  Qed.

  Lemma big_opL_ext f g l :
    (∀ k y, l !! k = Some y → f k y = g k y) →
    ([^o list] k ↦ y ∈ l, f k y) = [^o list] k ↦ y ∈ l, g k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.

  Lemma big_opL_permutation (f : A → M) l1 l2 :
    l1 ≡ₚ l2 → ([^o list] x ∈ l1, f x) ≡ ([^o list] x ∈ l2, f x).
  Proof.
    induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
    - by rewrite IH.
    - by rewrite !assoc (comm _ (f x)).
    - by etrans.
  Qed.
  Global Instance big_opL_permutation' (f : A → M) :
    Proper ((≡ₚ) ==> (≡)) (big_opL o (λ _, f)).
  Proof. intros xs1 xs2. apply big_opL_permutation. Qed.

  (** The lemmas [big_opL_ne] and [big_opL_proper] are more generic than the
  instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_opL_ne f g l n :
    (∀ k y, l !! k = Some y → f k y ≡{n}≡ g k y) →
    ([^o list] k ↦ y ∈ l, f k y) ≡{n}≡ ([^o list] k ↦ y ∈ l, g k y).
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_opL_proper f g l :
    (∀ k y, l !! k = Some y → f k y ≡ g k y) →
    ([^o list] k ↦ y ∈ l, f k y) ≡ ([^o list] k ↦ y ∈ l, g k y).
  Proof. apply big_opL_gen_proper; apply _. Qed.

  (** The version [big_opL_proper_2] with [≡] for the list arguments can only be
  used if there is a setoid on [A]. The version for [dist n] can be found in
  [algebra.list]. We do not define this lemma as a [Proper] instance, since
  [f_equiv] will then use sometimes use this one, and other times
  [big_opL_proper'], depending on whether a setoid on [A] exists. *)
  Lemma big_opL_proper_2 `{!Equiv A} f g l1 l2 :
    l1 ≡ l2 →
    (∀ k y1 y2,
      l1 !! k = Some y1 → l2 !! k = Some y2 → y1 ≡ y2 → f k y1 ≡ g k y2) →
    ([^o list] k ↦ y ∈ l1, f k y) ≡ ([^o list] k ↦ y ∈ l2, g k y).
  Proof.
    intros Hl Hf. apply big_opL_gen_proper_2; try (apply _ || done).
    (* FIXME (Coq #14441) unnecessary type annotation *)
    intros k. assert (l1 !! k ≡@{option A} l2 !! k) as Hlk by (by f_equiv).
    destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
  Qed.

  Global Instance big_opL_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (=) ==> dist n)
           (big_opL o (A:=A)).
  Proof. intros f f' Hf l ? <-. apply big_opL_ne; intros; apply Hf. Qed.
  Global Instance big_opL_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (=) ==> (≡))
           (big_opL o (A:=A)).
  Proof. intros f f' Hf l ? <-. apply big_opL_proper; intros; apply Hf. Qed.

  Lemma big_opL_consZ_l (f : Z → A → M) x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (1 + k)%Z y.
  Proof. rewrite big_opL_cons. auto using big_opL_ext with f_equal lia. Qed.
  Lemma big_opL_consZ_r (f : Z → A → M) x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (k + 1)%Z y.
  Proof. rewrite big_opL_cons. auto using big_opL_ext with f_equal lia. Qed.

  Lemma big_opL_fmap {B} (h : A → B) (f : nat → B → M) l :
    ([^o list] k↦y ∈ h <$> l, f k y) ≡ ([^o list] k↦y ∈ l, f k (h y)).
  Proof. revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite IH. Qed.

  Lemma big_opL_omap {B} (h : A → option B) (f : B → M) l :
    ([^o list] y ∈ omap h l, f y) ≡ ([^o list] y ∈ l, from_option f monoid_unit (h y)).
  Proof.
    revert f. induction l as [|x l IH]=> f //; csimpl.
    case_match; csimpl; by rewrite IH // left_id.
  Qed.

  Lemma big_opL_op f g l :
    ([^o list] k↦x ∈ l, f k x `o` g k x)
    ≡ ([^o list] k↦x ∈ l, f k x) `o` ([^o list] k↦x ∈ l, g k x).
  Proof.
    revert f g; induction l as [|x l IH]=> f g /=; first by rewrite left_id.
    by rewrite IH -!assoc (assoc _ (g _ _)) [(g _ _ `o` _)]comm -!assoc.
  Qed.

  (** Shows that some property [P] is closed under [big_opL]. Examples of [P]
  are [Persistent], [Affine], [Timeless]. *)
  Lemma big_opL_closed (P : M → Prop) f l :
    P monoid_unit →
    (∀ x y, P x → P y → P (x `o` y)) →
    (∀ k x, l !! k = Some x → P (f k x)) →
    P ([^o list] k↦x ∈ l, f k x).
  Proof.
    intros Hunit Hop. revert f. induction l as [|x l IH]=> f Hf /=; [done|].
    apply Hop; first by auto. apply IH=> k. apply (Hf (S k)).
  Qed.
End list.

Lemma big_opL_bind {A B} (h : A → list B) (f : B → M) l :
  ([^o list] y ∈ l ≫= h, f y) ≡ ([^o list] x ∈ l, [^o list] y ∈ h x, f y).
Proof.
  revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite big_opL_app IH.
Qed.

Lemma big_opL_sep_zip_with {A B C} (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : nat → A → M) (h2 : nat → B → M) l1 l2 :
  (∀ x y, g1 (f x y) = x) →
  (∀ x y, g2 (f x y) = y) →
  length l1 = length l2 →
  ([^o list] k↦xy ∈ zip_with f l1 l2, h1 k (g1 xy) `o` h2 k (g2 xy)) ≡
  ([^o list] k↦x ∈ l1, h1 k x) `o` ([^o list] k↦y ∈ l2, h2 k y).
Proof.
  intros Hlen Hg1 Hg2. rewrite big_opL_op.
  rewrite -(big_opL_fmap g1) -(big_opL_fmap g2).
  rewrite fmap_zip_with_r; [|auto with lia..].
  by rewrite fmap_zip_with_l; [|auto with lia..].
Qed.

Lemma big_opL_sep_zip {A B} (h1 : nat → A → M) (h2 : nat → B → M) l1 l2 :
  length l1 = length l2 →
  ([^o list] k↦xy ∈ zip l1 l2, h1 k xy.1 `o` h2 k xy.2) ≡
  ([^o list] k↦x ∈ l1, h1 k x) `o` ([^o list] k↦y ∈ l2, h2 k y).
Proof. by apply big_opL_sep_zip_with. Qed.

(** ** Big ops over finite maps *)

Lemma big_opM_empty `{Countable K} {B} (f : K → B → M) :
  ([^o map] k↦x ∈ ∅, f k x) = monoid_unit.
Proof. by rewrite big_opM_unseal /big_opM_def map_to_list_empty. Qed.

Lemma big_opM_insert `{Countable K} {B} (f : K → B → M) (m : gmap K B) i x :
  m !! i = None →
  ([^o map] k↦y ∈ <[i:=x]> m, f k y) ≡ f i x `o` [^o map] k↦y ∈ m, f k y.
Proof. intros ?. by rewrite big_opM_unseal /big_opM_def map_to_list_insert. Qed.

Lemma big_opM_delete `{Countable K} {B} (f : K → B → M) (m : gmap K B) i x :
  m !! i = Some x →
  ([^o map] k↦y ∈ m, f k y) ≡ f i x `o` [^o map] k↦y ∈ delete i m, f k y.
Proof.
  intros. rewrite -big_opM_insert ?lookup_delete //.
  by rewrite insert_delete.
Qed.

Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types f g : K → A → M.

  Lemma big_opM_gen_proper_2 {B} (R : relation M) f (g : K → B → M)
        m1 (m2 : gmap K B) :
    subrelation (≡) R → Equivalence R →
    Proper (R ==> R ==> R) o →
    (∀ k,
      match m1 !! k, m2 !! k with
      | Some y1, Some y2 => R (f k y1) (g k y2)
      | None, None => True
      | _, _ => False
      end) →
    R ([^o map] k ↦ x ∈ m1, f k x) ([^o map] k ↦ x ∈ m2, g k x).
  Proof.
    intros HR ??. revert m2 f g.
    induction m1 as [|k x1 m1 Hm1k IH] using map_ind=> m2 f g Hfg.
    { destruct m2 as [|k x2 m2 _ _] using map_ind.
      { rewrite !big_opM_empty. by apply HR. }
      generalize (Hfg k). by rewrite lookup_empty lookup_insert. }
    generalize (Hfg k). rewrite lookup_insert.
    destruct (m2 !! k) as [x2|] eqn:Hm2k; [intros Hk|done].
    etrans; [by apply HR, big_opM_insert|].
    etrans; [|by symmetry; apply HR, big_opM_delete].
    f_equiv; [done|]. apply IH=> k'. destruct (decide (k = k')) as [->|?].
    - by rewrite lookup_delete Hm1k.
    - generalize (Hfg k'). rewrite lookup_insert_ne // lookup_delete_ne //.
  Qed.

  Lemma big_opM_gen_proper R f g m :
    Reflexive R →
    Proper (R ==> R ==> R) o →
    (∀ k x, m !! k = Some x → R (f k x) (g k x)) →
    R ([^o map] k ↦ x ∈ m, f k x) ([^o map] k ↦ x ∈ m, g k x).
  Proof.
    intros ?? Hf. rewrite big_opM_unseal. apply (big_opL_gen_proper R); auto.
    intros k [i x] ?%elem_of_list_lookup_2. by apply Hf, elem_of_map_to_list.
  Qed.

  Lemma big_opM_ext f g m :
    (∀ k x, m !! k = Some x → f k x = g k x) →
    ([^o map] k ↦ x ∈ m, f k x) = ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_gen_proper; apply _. Qed.

  (** The lemmas [big_opM_ne] and [big_opM_proper] are more generic than the
  instances as they also give [m !! k = Some y] in the premise. *)
  Lemma big_opM_ne f g m n :
    (∀ k x, m !! k = Some x → f k x ≡{n}≡ g k x) →
    ([^o map] k ↦ x ∈ m, f k x) ≡{n}≡ ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_gen_proper; apply _. Qed.
  Lemma big_opM_proper f g m :
    (∀ k x, m !! k = Some x → f k x ≡ g k x) →
    ([^o map] k ↦ x ∈ m, f k x) ≡ ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_gen_proper; apply _. Qed.
  (** The version [big_opM_proper_2] with [≡] for the map arguments can only be
  used if there is a setoid on [A]. The version for [dist n] can be found in
  [algebra.gmap]. We do not define this lemma as a [Proper] instance, since
  [f_equiv] will then use sometimes use this one, and other times
  [big_opM_proper'], depending on whether a setoid on [A] exists. *)
  Lemma big_opM_proper_2 `{!Equiv A} f g m1 m2 :
    m1 ≡ m2 →
    (∀ k y1 y2,
      m1 !! k = Some y1 → m2 !! k = Some y2 → y1 ≡ y2 → f k y1 ≡ g k y2) →
    ([^o map] k ↦ y ∈ m1, f k y) ≡ ([^o map] k ↦ y ∈ m2, g k y).
  Proof.
    intros Hl Hf. apply big_opM_gen_proper_2; try (apply _ || done).
    (* FIXME (Coq #14441) unnecessary type annotation *)
    intros k. assert (m1 !! k ≡@{option A} m2 !! k) as Hlk by (by f_equiv).
    destruct (m1 !! k) eqn:?, (m2 !! k) eqn:?; inversion Hlk; naive_solver.
  Qed.

  Global Instance big_opM_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> (=) ==> dist n)
           (big_opM o (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opM_ne; intros; apply Hf. Qed.
  Global Instance big_opM_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> (=) ==> (≡))
           (big_opM o (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opM_proper; intros; apply Hf. Qed.

  (* FIXME: This lemma could be generalized from [≡] to [=], but that breaks
  [setoid_rewrite] in the proof of [big_sepS_sepS]. See Coq issue #14349. *)
  Lemma big_opM_map_to_list f m :
    ([^o map] k↦x ∈ m, f k x) ≡ [^o list] xk ∈ map_to_list m, f (xk.1) (xk.2).
  Proof. rewrite big_opM_unseal. apply big_opL_proper'; [|done]. by intros ? [??]. Qed.
  Lemma big_opM_list_to_map f l :
    NoDup l.*1 →
    ([^o map] k↦x ∈ list_to_map l, f k x) ≡ [^o list] xk ∈ l, f (xk.1) (xk.2).
  Proof.
    intros. rewrite big_opM_map_to_list.
    by apply big_opL_permutation, map_to_list_to_map.
  Qed.

  Lemma big_opM_singleton f i x : ([^o map] k↦y ∈ {[i:=x]}, f k y) ≡ f i x.
  Proof.
    rewrite -insert_empty big_opM_insert/=; last eauto using lookup_empty.
    by rewrite big_opM_empty right_id.
  Qed.

  Lemma big_opM_unit m : ([^o map] k↦y ∈ m, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    by induction m using map_ind; rewrite /= ?big_opM_insert ?left_id // big_opM_unseal.
  Qed.

  Lemma big_opM_fmap {B} (h : A → B) (f : K → B → M) m :
    ([^o map] k↦y ∈ h <$> m, f k y) ≡ ([^o map] k↦y ∈ m, f k (h y)).
  Proof.
    rewrite big_opM_unseal /big_opM_def map_to_list_fmap big_opL_fmap.
    by apply big_opL_proper=> ? [??].
  Qed.

  Lemma big_opM_omap {B} (h : A → option B) (f : K → B → M) m :
    ([^o map] k↦y ∈ omap h m, f k y)
    ≡ [^o map] k↦y ∈ m, from_option (f k) monoid_unit (h y).
  Proof.
    revert f. induction m as [|i x m Hmi IH] using map_ind=> f.
    { by rewrite omap_empty !big_opM_empty. }
    assert (omap h m !! i = None) by (by rewrite lookup_omap Hmi).
    destruct (h x) as [y|] eqn:Hhx.
    - by rewrite omap_insert Hhx //= !big_opM_insert // IH Hhx.
    - rewrite omap_insert_None // delete_notin // big_opM_insert //.
      by rewrite Hhx /= left_id.
  Qed.

  Lemma big_opM_insert_delete `{Countable K} {B} (f : K → B → M) (m : gmap K B) i x :
    ([^o map] k↦y ∈ <[i:=x]> m, f k y) ≡ f i x `o` [^o map] k↦y ∈ delete i m, f k y.
  Proof.
    rewrite -insert_delete_insert big_opM_insert; first done. by rewrite lookup_delete.
  Qed.

  Lemma big_opM_insert_override (f : K → A → M) m i x x' :
    m !! i = Some x → f i x ≡ f i x' →
    ([^o map] k↦y ∈ <[i:=x']> m, f k y) ≡ ([^o map] k↦y ∈ m, f k y).
  Proof.
    intros ? Hx. rewrite -insert_delete_insert big_opM_insert ?lookup_delete //.
    by rewrite -Hx -big_opM_delete.
  Qed.

  Lemma big_opM_fn_insert {B} (g : K → A → B → M) (f : K → B) m i (x : A) b :
    m !! i = None →
    ([^o map] k↦y ∈ <[i:=x]> m, g k y (<[i:=b]> f k))
    ≡ g i x b `o` [^o map] k↦y ∈ m, g k y (f k).
  Proof.
    intros. rewrite big_opM_insert // fn_lookup_insert.
    f_equiv; apply big_opM_proper; auto=> k y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opM_fn_insert' (f : K → M) m i x P :
    m !! i = None →
    ([^o map] k↦y ∈ <[i:=x]> m, <[i:=P]> f k) ≡ (P `o` [^o map] k↦y ∈ m, f k).
  Proof. apply (big_opM_fn_insert (λ _ _, id)). Qed.

  Lemma big_opM_filter' (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} f m :
    ([^o map] k ↦ x ∈ filter φ m, f k x)
    ≡ ([^o map] k ↦ x ∈ m, if decide (φ (k, x)) then f k x else monoid_unit).
  Proof.
    induction m as [|k v m ? IH] using map_ind.
    { by rewrite map_filter_empty !big_opM_empty. }
    destruct (decide (φ (k, v))).
    - rewrite map_filter_insert_True //.
      assert (filter φ m !! k = None) by (apply map_lookup_filter_None; eauto).
      by rewrite !big_opM_insert // decide_True // IH.
    - rewrite map_filter_insert_not' //; last by congruence.
      rewrite !big_opM_insert // decide_False // IH. by rewrite left_id.
  Qed.

  Lemma big_opM_union f m1 m2 :
    m1 ##ₘ m2 →
    ([^o map] k↦y ∈ m1 ∪ m2, f k y)
    ≡ ([^o map] k↦y ∈ m1, f k y) `o` ([^o map] k↦y ∈ m2, f k y).
  Proof.
    intros. induction m1 as [|i x m ? IH] using map_ind.
    { by rewrite big_opM_empty !left_id. }
    decompose_map_disjoint.
    rewrite -insert_union_l !big_opM_insert //;
      last by apply lookup_union_None.
    rewrite -assoc IH //.
  Qed.

  Lemma big_opM_op f g m :
    ([^o map] k↦x ∈ m, f k x `o` g k x)
    ≡ ([^o map] k↦x ∈ m, f k x) `o` ([^o map] k↦x ∈ m, g k x).
  Proof.
    rewrite big_opM_unseal /big_opM_def -big_opL_op. by apply big_opL_proper=> ? [??].
  Qed.

  (** Shows that some property [P] is closed under [big_opM]. Examples of [P]
  are [Persistent], [Affine], [Timeless]. *)
  Lemma big_opM_closed (P : M → Prop) f m :
    Proper ((≡) ==> iff) P →
    P monoid_unit →
    (∀ x y, P x → P y → P (x `o` y)) →
    (∀ k x, m !! k = Some x → P (f k x)) →
    P ([^o map] k↦x ∈ m, f k x).
  Proof.
    intros ?? Hop Hf. induction m as [|k x ?? IH] using map_ind.
    { by rewrite big_opM_empty. }
    rewrite big_opM_insert //. apply Hop.
    { apply Hf. by rewrite lookup_insert. }
    apply IH=> k' x' ?. apply Hf. rewrite lookup_insert_ne; naive_solver.
  Qed.
End gmap.

Lemma big_opM_sep_zip_with `{Countable K} {A B C}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (h1 : K → A → M) (h2 : K → B → M) m1 m2 :
  (∀ x y, g1 (f x y) = x) →
  (∀ x y, g2 (f x y) = y) →
  (∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
  ([^o map] k↦xy ∈ map_zip_with f m1 m2, h1 k (g1 xy) `o` h2 k (g2 xy)) ≡
  ([^o map] k↦x ∈ m1, h1 k x) `o` ([^o map] k↦y ∈ m2, h2 k y).
Proof.
  intros Hdom Hg1 Hg2. rewrite big_opM_op.
  rewrite -(big_opM_fmap g1) -(big_opM_fmap g2).
  rewrite map_fmap_zip_with_r; [|naive_solver..].
  by rewrite map_fmap_zip_with_l; [|naive_solver..].
Qed.

Lemma big_opM_sep_zip `{Countable K} {A B}
    (h1 : K → A → M) (h2 : K → B → M) m1 m2 :
  (∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
  ([^o map] k↦xy ∈ map_zip m1 m2, h1 k xy.1 `o` h2 k xy.2) ≡
  ([^o map] k↦x ∈ m1, h1 k x) `o` ([^o map] k↦y ∈ m2, h2 k y).
Proof. intros. by apply big_opM_sep_zip_with. Qed.


(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

  Lemma big_opS_gen_proper R f g X :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ x, x ∈ X → R (f x) (g x)) →
    R ([^o set] x ∈ X, f x) ([^o set] x ∈ X, g x).
  Proof.
    rewrite big_opS_unseal. intros ?? Hf. apply (big_opL_gen_proper R); auto.
    intros k x ?%elem_of_list_lookup_2. by apply Hf, elem_of_elements.
  Qed.

  Lemma big_opS_ext f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^o set] x ∈ X, f x) = ([^o set] x ∈ X, g x).
  Proof. apply big_opS_gen_proper; apply _. Qed.

  (** The lemmas [big_opS_ne] and [big_opS_proper] are more generic than the
  instances as they also give [x ∈ X] in the premise. *)
  Lemma big_opS_ne f g X n :
    (∀ x, x ∈ X → f x ≡{n}≡ g x) →
    ([^o set] x ∈ X, f x) ≡{n}≡ ([^o set] x ∈ X, g x).
  Proof. apply big_opS_gen_proper; apply _. Qed.
  Lemma big_opS_proper f g X :
    (∀ x, x ∈ X → f x ≡ g x) →
    ([^o set] x ∈ X, f x) ≡ ([^o set] x ∈ X, g x).
  Proof. apply big_opS_gen_proper; apply _. Qed.

  Global Instance big_opS_ne' n :
    Proper (pointwise_relation _ (dist n) ==> (=) ==> dist n) (big_opS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opS_ne; intros; apply Hf. Qed.
  Global Instance big_opS_proper' :
    Proper (pointwise_relation _ (≡) ==> (=) ==> (≡)) (big_opS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opS_proper; intros; apply Hf. Qed.

  (* FIXME: This lemma could be generalized from [≡] to [=], but that breaks
  [setoid_rewrite] in the proof of [big_sepS_sepS]. See Coq issue #14349. *)
  Lemma big_opS_elements f X :
    ([^o set] x ∈ X, f x) ≡ [^o list] x ∈ elements X, f x.
  Proof. by rewrite big_opS_unseal. Qed.

  Lemma big_opS_empty f : ([^o set] x ∈ ∅, f x) = monoid_unit.
  Proof. by rewrite big_opS_unseal /big_opS_def elements_empty. Qed.

  Lemma big_opS_insert f X x :
    x ∉ X → ([^o set] y ∈ {[ x ]} ∪ X, f y) ≡ (f x `o` [^o set] y ∈ X, f y).
  Proof. intros. by rewrite !big_opS_elements elements_union_singleton. Qed.
  Lemma big_opS_fn_insert {B} (f : A → B → M) h X x b :
    x ∉ X →
    ([^o set] y ∈ {[ x ]} ∪ X, f y (<[x:=b]> h y))
    ≡ f x b `o` [^o set] y ∈ X, f y (h y).
  Proof.
    intros. rewrite big_opS_insert // fn_lookup_insert.
    f_equiv; apply big_opS_proper; auto=> y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opS_fn_insert' f X x P :
    x ∉ X → ([^o set] y ∈ {[ x ]} ∪ X, <[x:=P]> f y) ≡ (P `o` [^o set] y ∈ X, f y).
  Proof. apply (big_opS_fn_insert (λ y, id)). Qed.

  Lemma big_opS_union f X Y :
    X ## Y →
    ([^o set] y ∈ X ∪ Y, f y) ≡ ([^o set] y ∈ X, f y) `o` ([^o set] y ∈ Y, f y).
  Proof.
    intros. induction X as [|x X ? IH] using set_ind_L.
    { by rewrite left_id_L big_opS_empty left_id. }
    rewrite -assoc_L !big_opS_insert; [|set_solver..].
    by rewrite -assoc IH; last set_solver.
  Qed.

  Lemma big_opS_delete f X x :
    x ∈ X → ([^o set] y ∈ X, f y) ≡ f x `o` [^o set] y ∈ X ∖ {[ x ]}, f y.
  Proof.
    intros. rewrite -big_opS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.

  Lemma big_opS_singleton f x : ([^o set] y ∈ {[ x ]}, f y) ≡ f x.
  Proof. intros. by rewrite big_opS_elements elements_singleton /= right_id. Qed.

  Lemma big_opS_unit X : ([^o set] y ∈ X, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    by induction X using set_ind_L; rewrite /= ?big_opS_insert ?left_id // big_opS_unseal.
  Qed.

  Lemma big_opS_filter' (φ : A → Prop) `{∀ x, Decision (φ x)} f X :
    ([^o set] y ∈ filter φ X, f y)
    ≡ ([^o set] y ∈ X, if decide (φ y) then f y else monoid_unit).
  Proof.
    induction X as [|x X ? IH] using set_ind_L.
    { by rewrite filter_empty_L !big_opS_empty. }
    destruct (decide (φ x)).
    - rewrite filter_union_L filter_singleton_L //.
      rewrite !big_opS_insert //; last set_solver.
      by rewrite decide_True // IH.
    - rewrite filter_union_L filter_singleton_not_L // left_id_L.
      by rewrite !big_opS_insert // decide_False // IH left_id.
  Qed.

  Lemma big_opS_op f g X :
    ([^o set] y ∈ X, f y `o` g y) ≡ ([^o set] y ∈ X, f y) `o` ([^o set] y ∈ X, g y).
  Proof. by rewrite !big_opS_elements -big_opL_op. Qed.

  Lemma big_opS_list_to_set f (l : list A) :
    NoDup l →
    ([^o set] x ∈ list_to_set l, f x) ≡ [^o list] x ∈ l, f x.
  Proof.
    induction 1 as [|x l ?? IHl].
    - rewrite big_opS_empty //.
    - rewrite /= big_opS_union; last set_solver.
      by rewrite big_opS_singleton IHl.
  Qed.

  (** Shows that some property [P] is closed under [big_opS]. Examples of [P]
  are [Persistent], [Affine], [Timeless]. *)
  Lemma big_opS_closed (P : M → Prop) f X :
    Proper ((≡) ==> iff) P →
    P monoid_unit →
    (∀ x y, P x → P y → P (x `o` y)) →
    (∀ x, x ∈ X → P (f x)) →
    P ([^o set] x ∈ X, f x).
  Proof.
    intros ?? Hop Hf. induction X as [|x X ? IH] using set_ind_L.
    { by rewrite big_opS_empty. }
    rewrite big_opS_insert //. apply Hop.
    { apply Hf. set_solver. }
    apply IH=> x' ?. apply Hf. set_solver.
  Qed.
End gset.

Lemma big_opS_set_map `{Countable A, Countable B} (h : A → B) (X : gset A) (f : B → M) :
  Inj (=) (=) h →
  ([^o set] x ∈ set_map h X, f x) ≡ ([^o set] x ∈ X, f (h x)).
Proof.
  intros Hinj.
  induction X as [|x X ? IH] using set_ind_L.
  { by rewrite set_map_empty !big_opS_empty. }
  rewrite set_map_union_L set_map_singleton_L.
  rewrite !big_opS_union; [|set_solver..].
  rewrite !big_opS_singleton IH //.
Qed.

Lemma big_opM_dom `{Countable K} {A} (f : K → M) (m : gmap K A) :
  ([^o map] k↦_ ∈ m, f k) ≡ ([^o set] k ∈ dom m, f k).
Proof.
  induction m as [|i x ?? IH] using map_ind.
  { by rewrite big_opM_unseal big_opS_unseal dom_empty_L. }
  by rewrite dom_insert_L big_opM_insert // IH big_opS_insert ?not_elem_of_dom.
Qed.
Lemma big_opM_gset_to_gmap `{Countable K} {A} (f : K → A → M) (X : gset K) c :
  ([^o map] k↦a ∈ gset_to_gmap c X, f k a) ≡ ([^o set] k ∈ X, f k c).
Proof.
  rewrite -{2}(dom_gset_to_gmap X c) -big_opM_dom.
  apply big_opM_proper. by intros k ? [_ ->]%lookup_gset_to_gmap_Some.
Qed.

(** ** Big ops over finite msets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types f : A → M.

  Lemma big_opMS_gen_proper R f g X :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ x, x ∈ X → R (f x) (g x)) →
    R ([^o mset] x ∈ X, f x) ([^o mset] x ∈ X, g x).
  Proof.
    rewrite big_opMS_unseal. intros ?? Hf. apply (big_opL_gen_proper R); auto.
    intros k x ?%elem_of_list_lookup_2. by apply Hf, gmultiset_elem_of_elements.
  Qed.

  Lemma big_opMS_ext f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^o mset] x ∈ X, f x) = ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_gen_proper; apply _. Qed.

  (** The lemmas [big_opMS_ne] and [big_opMS_proper] are more generic than the
  instances as they also give [x ∈ X] in the premise. *)
  Lemma big_opMS_ne f g X n :
    (∀ x, x ∈ X → f x ≡{n}≡ g x) →
    ([^o mset] x ∈ X, f x) ≡{n}≡ ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_gen_proper; apply _. Qed.
  Lemma big_opMS_proper f g X :
    (∀ x, x ∈ X → f x ≡ g x) →
    ([^o mset] x ∈ X, f x) ≡ ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_gen_proper; apply _. Qed.

  Global Instance big_opMS_ne' n :
    Proper (pointwise_relation _ (dist n) ==> (=) ==> dist n) (big_opMS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opMS_ne; intros; apply Hf. Qed.
  Global Instance big_opMS_proper' :
    Proper (pointwise_relation _ (≡) ==> (=) ==> (≡)) (big_opMS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opMS_proper; intros; apply Hf. Qed.

  (* FIXME: This lemma could be generalized from [≡] to [=], but that breaks
  [setoid_rewrite] in the proof of [big_sepS_sepS]. See Coq issue #14349. *)
  Lemma big_opMS_elements f X :
    ([^o mset] x ∈ X, f x) ≡ [^o list] x ∈ elements X, f x.
  Proof. by rewrite big_opMS_unseal. Qed.

  Lemma big_opMS_empty f : ([^o mset] x ∈ ∅, f x) = monoid_unit.
  Proof. by rewrite big_opMS_unseal /big_opMS_def gmultiset_elements_empty. Qed.

  Lemma big_opMS_disj_union f X Y :
    ([^o mset] y ∈ X ⊎ Y, f y) ≡ ([^o mset] y ∈ X, f y) `o` [^o mset] y ∈ Y, f y.
  Proof. by rewrite big_opMS_unseal /big_opMS_def gmultiset_elements_disj_union big_opL_app. Qed.

  Lemma big_opMS_singleton f x : ([^o mset] y ∈ {[+ x +]}, f y) ≡ f x.
  Proof.
    intros. by rewrite big_opMS_unseal /big_opMS_def gmultiset_elements_singleton /= right_id.
  Qed.

  Lemma big_opMS_insert f X x :
    ([^o mset] y ∈ {[+ x +]} ⊎ X, f y) ≡ (f x `o` [^o mset] y ∈ X, f y).
  Proof. intros. rewrite big_opMS_disj_union big_opMS_singleton //. Qed.

  Lemma big_opMS_delete f X x :
    x ∈ X → ([^o mset] y ∈ X, f y) ≡ f x `o` [^o mset] y ∈ X ∖ {[+ x +]}, f y.
  Proof.
    intros. rewrite -big_opMS_singleton -big_opMS_disj_union.
    by rewrite -gmultiset_disj_union_difference'.
  Qed.

  Lemma big_opMS_unit X : ([^o mset] y ∈ X, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    by induction X using gmultiset_ind;
      rewrite /= ?big_opMS_disj_union ?big_opMS_singleton ?left_id // big_opMS_unseal.
  Qed.

  Lemma big_opMS_op f g X :
    ([^o mset] y ∈ X, f y `o` g y) ≡ ([^o mset] y ∈ X, f y) `o` ([^o mset] y ∈ X, g y).
  Proof. by rewrite big_opMS_unseal /big_opMS_def -big_opL_op. Qed.

  (** Shows that some property [P] is closed under [big_opMS]. Examples of [P]
  are [Persistent], [Affine], [Timeless]. *)
  Lemma big_opMS_closed (P : M → Prop) f X :
    Proper ((≡) ==> iff) P →
    P monoid_unit →
    (∀ x y, P x → P y → P (x `o` y)) →
    (∀ x, x ∈ X → P (f x)) →
    P ([^o mset] x ∈ X, f x).
  Proof.
    intros ?? Hop Hf. induction X as [|x X IH] using gmultiset_ind.
    { by rewrite big_opMS_empty. }
    rewrite big_opMS_insert //. apply Hop.
    { apply Hf. set_solver. }
    apply IH=> x' ?. apply Hf. set_solver.
  Qed.
End gmultiset.

(** Commuting lemmas *)
Lemma big_opL_opL {A B} (f : nat → A → nat → B → M) (l1 : list A) (l2 : list B) :
  ([^o list] k1↦x1 ∈ l1, [^o list] k2↦x2 ∈ l2, f k1 x1 k2 x2) ≡
  ([^o list] k2↦x2 ∈ l2, [^o list] k1↦x1 ∈ l1, f k1 x1 k2 x2).
Proof.
  revert f l2. induction l1 as [|x1 l1 IH]; simpl; intros Φ l2.
  { by rewrite big_opL_unit. }
  by rewrite IH big_opL_op.
Qed.
Lemma big_opL_opM {A} `{Countable K} {B}
    (f : nat → A → K → B → M) (l1 : list A) (m2 : gmap K B) :
  ([^o list] k1↦x1 ∈ l1, [^o map] k2↦x2 ∈ m2, f k1 x1 k2 x2) ≡
  ([^o map] k2↦x2 ∈ m2, [^o list] k1↦x1 ∈ l1, f k1 x1 k2 x2).
Proof. repeat setoid_rewrite big_opM_map_to_list. by rewrite big_opL_opL. Qed.
Lemma big_opL_opS {A} `{Countable B}
    (f : nat → A → B → M) (l1 : list A) (X2 : gset B) :
  ([^o list] k1↦x1 ∈ l1, [^o set] x2 ∈ X2, f k1 x1 x2) ≡
  ([^o set] x2 ∈ X2, [^o list] k1↦x1 ∈ l1, f k1 x1 x2).
Proof. repeat setoid_rewrite big_opS_elements. by rewrite big_opL_opL. Qed.
Lemma big_opL_opMS {A} `{Countable B}
    (f : nat → A → B → M) (l1 : list A) (X2 : gmultiset B) :
  ([^o list] k1↦x1 ∈ l1, [^o mset] x2 ∈ X2, f k1 x1 x2) ≡
  ([^o mset] x2 ∈ X2, [^o list] k1↦x1 ∈ l1, f k1 x1 x2).
Proof. repeat setoid_rewrite big_opMS_elements. by rewrite big_opL_opL. Qed.

Lemma big_opM_opL {A} `{Countable K} {B}
    (f : K → A → nat → B → M) (m1 : gmap K A) (l2 : list B) :
  ([^o map] k1↦x1 ∈ m1, [^o list] k2↦x2 ∈ l2, f k1 x1 k2 x2) ≡
  ([^o list] k2↦x2 ∈ l2, [^o map] k1↦x1 ∈ m1, f k1 x1 k2 x2).
Proof. symmetry. apply big_opL_opM. Qed.
Lemma big_opM_opM `{Countable K1} {A} `{Countable K2} {B}
    (f : K1 → A → K2 → B → M) (m1 : gmap K1 A) (m2 : gmap K2 B) :
  ([^o map] k1↦x1 ∈ m1, [^o map] k2↦x2 ∈ m2, f k1 x1 k2 x2) ≡
  ([^o map] k2↦x2 ∈ m2, [^o map] k1↦x1 ∈ m1, f k1 x1 k2 x2).
Proof. repeat setoid_rewrite big_opM_map_to_list. by rewrite big_opL_opL. Qed.
Lemma big_opM_opS `{Countable K} {A} `{Countable B}
    (f : K → A → B → M) (m1 : gmap K A) (X2 : gset B) :
  ([^o map] k1↦x1 ∈ m1, [^o set] x2 ∈ X2, f k1 x1 x2) ≡
  ([^o set] x2 ∈ X2, [^o map] k1↦x1 ∈ m1, f k1 x1 x2).
Proof.
  repeat setoid_rewrite big_opM_map_to_list.
  repeat setoid_rewrite big_opS_elements. by rewrite big_opL_opL.
Qed.
Lemma big_opM_opMS `{Countable K} {A} `{Countable B} (f : K → A → B → M)
    (m1 : gmap K A) (X2 : gmultiset B) :
  ([^o map] k1↦x1 ∈ m1, [^o mset] x2 ∈ X2, f k1 x1 x2) ≡
  ([^o mset] x2 ∈ X2, [^o map] k1↦x1 ∈ m1, f k1 x1 x2).
Proof.
  repeat setoid_rewrite big_opM_map_to_list.
  repeat setoid_rewrite big_opMS_elements. by rewrite big_opL_opL.
Qed.

Lemma big_opS_opL `{Countable A} {B}
    (f : A → nat → B → M) (X1 : gset A) (l2 : list B) :
  ([^o set] x1 ∈ X1, [^o list] k2↦x2 ∈ l2, f x1 k2 x2) ≡
  ([^o list] k2↦x2 ∈ l2, [^o set] x1 ∈ X1, f x1 k2 x2).
Proof. symmetry. apply big_opL_opS. Qed.
Lemma big_opS_opM `{Countable A} `{Countable K} {B}
    (f : A → K → B → M) (X1 : gset A) (m2 : gmap K B) :
  ([^o set] x1 ∈ X1, [^o map] k2↦x2 ∈ m2, f x1 k2 x2) ≡
  ([^o map] k2↦x2 ∈ m2, [^o set] x1 ∈ X1, f x1 k2 x2).
Proof. symmetry. apply big_opM_opS. Qed.
Lemma big_opS_opS `{Countable A, Countable B}
    (X : gset A) (Y : gset B) (f : A → B → M) :
  ([^o set] x ∈ X, [^o set] y ∈ Y, f x y) ≡ ([^o set] y ∈ Y, [^o set] x ∈ X, f x y).
Proof. repeat setoid_rewrite big_opS_elements. by rewrite big_opL_opL. Qed.
Lemma big_opS_opMS `{Countable A, Countable B}
    (X : gset A) (Y : gmultiset B) (f : A → B → M) :
  ([^o set] x ∈ X, [^o mset] y ∈ Y, f x y) ≡ ([^o mset] y ∈ Y, [^o set] x ∈ X, f x y).
Proof.
  repeat setoid_rewrite big_opS_elements.
  repeat setoid_rewrite big_opMS_elements. by rewrite big_opL_opL.
Qed.

Lemma big_opMS_opL `{Countable A} {B}
    (f : A → nat → B → M) (X1 : gmultiset A) (l2 : list B) :
  ([^o mset] x1 ∈ X1, [^o list] k2↦x2 ∈ l2, f x1 k2 x2) ≡
  ([^o list] k2↦x2 ∈ l2, [^o mset] x1 ∈ X1, f x1 k2 x2).
Proof. symmetry. apply big_opL_opMS. Qed.
Lemma big_opMS_opM `{Countable A} `{Countable K} {B} (f : A → K → B → M)
    (X1 : gmultiset A) (m2 : gmap K B) :
  ([^o mset] x1 ∈ X1, [^o map] k2↦x2 ∈ m2, f x1 k2 x2) ≡
  ([^o map] k2↦x2 ∈ m2, [^o mset] x1 ∈ X1, f x1 k2 x2).
Proof. symmetry. apply big_opM_opMS. Qed.
Lemma big_opMS_opS `{Countable A, Countable B}
    (X : gmultiset A) (Y : gset B) (f : A → B → M) :
  ([^o mset] x ∈ X, [^o set] y ∈ Y, f x y) ≡ ([^o set] y ∈ Y, [^o mset] x ∈ X, f x y).
Proof. symmetry. apply big_opS_opMS. Qed.
Lemma big_opMS_opMS `{Countable A, Countable B}
    (X : gmultiset A) (Y : gmultiset B) (f : A → B → M) :
  ([^o mset] x ∈ X, [^o mset] y ∈ Y, f x y) ≡ ([^o mset] y ∈ Y, [^o mset] x ∈ X, f x y).
Proof. repeat setoid_rewrite big_opMS_elements. by rewrite big_opL_opL. Qed.

End big_op.

Section homomorphisms.
  Context {M1 M2 : ofe} {o1 : M1 → M1 → M1} {o2 : M2 → M2 → M2} `{!Monoid o1, !Monoid o2}.
  Infix "`o1`" := o1 (at level 50, left associativity).
  Infix "`o2`" := o2 (at level 50, left associativity).
  (** The ssreflect rewrite tactic only works for relations that have a
  [RewriteRelation] instance. For the purpose of this section, we want to
  rewrite with arbitrary relations, so we declare any relation to be a
  [RewriteRelation]. *)
  Local Instance: ∀ {A} (R : relation A), RewriteRelation R := {}.

  Lemma big_opL_commute {A} (h : M1 → M2) `{!MonoidHomomorphism o1 o2 R h}
      (f : nat → A → M1) l :
    R (h ([^o1 list] k↦x ∈ l, f k x)) ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof.
    revert f. induction l as [|x l IH]=> f /=.
    - apply monoid_homomorphism_unit.
    - by rewrite monoid_homomorphism IH.
  Qed.
  Lemma big_opL_commute1 {A} (h : M1 → M2) `{!WeakMonoidHomomorphism o1 o2 R h}
      (f : nat → A → M1) l :
    l ≠ [] → R (h ([^o1 list] k↦x ∈ l, f k x)) ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof.
    intros ?. revert f. induction l as [|x [|x' l'] IH]=> f //.
    - by rewrite !big_opL_singleton.
    - by rewrite !(big_opL_cons _ x) monoid_homomorphism IH.
  Qed.

  Lemma big_opM_commute `{Countable K} {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : K → A → M1) m :
    R (h ([^o1 map] k↦x ∈ m, f k x)) ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof.
    intros. induction m as [|i x m ? IH] using map_ind.
    - by rewrite !big_opM_empty monoid_homomorphism_unit.
    - by rewrite !big_opM_insert // monoid_homomorphism -IH.
  Qed.
  Lemma big_opM_commute1 `{Countable K} {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : K → A → M1) m :
    m ≠ ∅ → R (h ([^o1 map] k↦x ∈ m, f k x)) ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof.
    intros. induction m as [|i x m ? IH] using map_ind; [done|].
    destruct (decide (m = ∅)) as [->|].
    - by rewrite !big_opM_insert // !big_opM_empty !right_id.
    - by rewrite !big_opM_insert // monoid_homomorphism -IH //.
  Qed.

  Lemma big_opS_commute `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    R (h ([^o1 set] x ∈ X, f x)) ([^o2 set] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X ? IH] using set_ind_L.
    - by rewrite !big_opS_empty monoid_homomorphism_unit.
    - by rewrite !big_opS_insert // monoid_homomorphism -IH.
  Qed.
  Lemma big_opS_commute1 `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    X ≠ ∅ → R (h ([^o1 set] x ∈ X, f x)) ([^o2 set] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X ? IH] using set_ind_L; [done|].
    destruct (decide (X = ∅)) as [->|].
    - by rewrite !big_opS_insert // !big_opS_empty !right_id.
    - by rewrite !big_opS_insert // monoid_homomorphism -IH //.
  Qed.

  Lemma big_opMS_commute `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    R (h ([^o1 mset] x ∈ X, f x)) ([^o2 mset] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X IH] using gmultiset_ind.
    - by rewrite !big_opMS_empty monoid_homomorphism_unit.
    - by rewrite !big_opMS_disj_union !big_opMS_singleton monoid_homomorphism -IH.
  Qed.
  Lemma big_opMS_commute1 `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    X ≠ ∅ → R (h ([^o1 mset] x ∈ X, f x)) ([^o2 mset] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X IH] using gmultiset_ind; [done|].
    destruct (decide (X = ∅)) as [->|].
    - by rewrite !big_opMS_disj_union !big_opMS_singleton !big_opMS_empty !right_id.
    - by rewrite !big_opMS_disj_union !big_opMS_singleton monoid_homomorphism -IH //.
  Qed.

  Context `{!LeibnizEquiv M2}.

  Lemma big_opL_commute_L {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : nat → A → M1) l :
    h ([^o1 list] k↦x ∈ l, f k x) = ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opL_commute. Qed.
  Lemma big_opL_commute1_L {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : nat → A → M1) l :
    l ≠ [] → h ([^o1 list] k↦x ∈ l, f k x) = ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opL_commute1. Qed.

  Lemma big_opM_commute_L `{Countable K} {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : K → A → M1) m :
    h ([^o1 map] k↦x ∈ m, f k x) = ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opM_commute. Qed.
  Lemma big_opM_commute1_L `{Countable K} {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : K → A → M1) m :
    m ≠ ∅ → h ([^o1 map] k↦x ∈ m, f k x) = ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof using Type*. unfold_leibniz. by apply big_opM_commute1. Qed.

  Lemma big_opS_commute_L `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    h ([^o1 set] x ∈ X, f x) = ([^o2 set] x ∈ X, h (f x)).
  Proof using Type*. unfold_leibniz. by apply big_opS_commute. Qed.
  Lemma big_opS_commute1_L `{ Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    X ≠ ∅ → h ([^o1 set] x ∈ X, f x) = ([^o2 set] x ∈ X, h (f x)).
  Proof using Type*. intros. rewrite <-leibniz_equiv_iff. by apply big_opS_commute1. Qed.

  Lemma big_opMS_commute_L `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    h ([^o1 mset] x ∈ X, f x) = ([^o2 mset] x ∈ X, h (f x)).
  Proof using Type*. unfold_leibniz. by apply big_opMS_commute. Qed.
  Lemma big_opMS_commute1_L `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    X ≠ ∅ → h ([^o1 mset] x ∈ X, f x) = ([^o2 mset] x ∈ X, h (f x)).
  Proof using Type*. intros. rewrite <-leibniz_equiv_iff. by apply big_opMS_commute1. Qed.
End homomorphisms.
