From stdpp Require Import countable fin_sets functions.
From iris.algebra Require Export big_op.
From iris.algebra Require Import list gmap.
From iris.bi Require Import derived_laws_later.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.

(** Notations for unary variants *)
Notation "'[∗' 'list]' k ↦ x ∈ l , P" :=
  (big_opL bi_sep (λ k x, P%I) l) : bi_scope.
Notation "'[∗' 'list]' x ∈ l , P" :=
  (big_opL bi_sep (λ _ x, P%I) l) : bi_scope.
Notation "'[∗]' Ps" := (big_opL bi_sep (λ _ x, x) Ps%I) : bi_scope.

Notation "'[∧' 'list]' k ↦ x ∈ l , P" :=
  (big_opL bi_and (λ k x, P%I) l) : bi_scope.
Notation "'[∧' 'list]' x ∈ l , P" :=
  (big_opL bi_and (λ _ x, P%I) l) : bi_scope.
Notation "'[∧]' Ps" := (big_opL bi_and (λ _ x, x) Ps%I) : bi_scope.

Notation "'[∨' 'list]' k ↦ x ∈ l , P" :=
  (big_opL bi_or (λ k x, P%I) l) : bi_scope.
Notation "'[∨' 'list]' x ∈ l , P" :=
  (big_opL bi_or (λ _ x, P%I) l) : bi_scope.
Notation "'[∨]' Ps" := (big_opL bi_or (λ _ x, x) Ps%I) : bi_scope.

Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM bi_sep (λ k x, P%I) m) : bi_scope.
Notation "'[∗' 'map]' x ∈ m , P" := (big_opM bi_sep (λ _ x, P%I) m) : bi_scope.

Notation "'[∧' 'map]' k ↦ x ∈ m , P" := (big_opM bi_and (λ k x, P) m) : bi_scope.
Notation "'[∧' 'map]' x ∈ m , P" := (big_opM bi_and (λ _ x, P) m) : bi_scope.

Notation "'[∗' 'set]' x ∈ X , P" := (big_opS bi_sep (λ x, P%I) X) : bi_scope.

Notation "'[∗' 'mset]' x ∈ X , P" := (big_opMS bi_sep (λ x, P%I) X) : bi_scope.

(** Definitions and notations for binary variants *)
(** A version of the separating big operator that ranges over two lists. This
version also ensures that both lists have the same length. Although this version
can be defined in terms of the unary using a [zip] (see [big_sepL2_alt]), we do
not define it that way to get better computational behavior (for [simpl]). *)
Fixpoint big_sepL2 {PROP : bi} {A B}
    (Φ : nat → A → B → PROP) (l1 : list A) (l2 : list B) : PROP :=
  match l1, l2 with
  | [], [] => emp
  | x1 :: l1, x2 :: l2 => Φ 0 x1 x2 ∗ big_sepL2 (λ n, Φ (S n)) l1 l2
  | _, _ => False
  end%I.
Global Instance: Params (@big_sepL2) 3 := {}.
Global Arguments big_sepL2 {PROP A B} _ !_ !_ /.
Global Typeclasses Opaque big_sepL2.
Notation "'[∗' 'list]' k ↦ x1 ; x2 ∈ l1 ; l2 , P" :=
  (big_sepL2 (λ k x1 x2, P%I) l1 l2) : bi_scope.
Notation "'[∗' 'list]' x1 ; x2 ∈ l1 ; l2 , P" :=
  (big_sepL2 (λ _ x1 x2, P%I) l1 l2) : bi_scope.

Local Definition big_sepM2_def {PROP : bi} `{Countable K} {A B}
    (Φ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B) : PROP :=
  ⌜ dom m1 = dom m2 ⌝ ∧ [∗ map] k ↦ xy ∈ map_zip m1 m2, Φ k xy.1 xy.2.
Local Definition big_sepM2_aux : seal (@big_sepM2_def). Proof. by eexists. Qed.
Definition big_sepM2 := big_sepM2_aux.(unseal).
Global Arguments big_sepM2 {PROP K _ _ A B} _ _ _.
Local Definition big_sepM2_unseal : @big_sepM2 = _ := big_sepM2_aux.(seal_eq).
Global Instance: Params (@big_sepM2) 6 := {}.
Notation "'[∗' 'map]' k ↦ x1 ; x2 ∈ m1 ; m2 , P" :=
  (big_sepM2 (λ k x1 x2, P%I) m1 m2) : bi_scope.
Notation "'[∗' 'map]' x1 ; x2 ∈ m1 ; m2 , P" :=
  (big_sepM2 (λ _ x1 x2, P%I) m1 m2) : bi_scope.

(** * Properties *)
Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

(** ** Big ops over lists *)
Section sep_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_sepL_nil Φ : ([∗ list] k↦y ∈ nil, Φ k y) ⊣⊢ emp.
  Proof. done. Qed.
  Lemma big_sepL_nil' P `{!Affine P} Φ : P ⊢ [∗ list] k↦y ∈ nil, Φ k y.
  Proof. apply: affine. Qed.
  Lemma big_sepL_cons Φ x l :
    ([∗ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∗ [∗ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_sepL_singleton Φ x : ([∗ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_sepL_app Φ l1 l2 :
    ([∗ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∗ list] k↦y ∈ l1, Φ k y) ∗ ([∗ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.
  Lemma big_sepL_snoc Φ l x :
    ([∗ list] k↦y ∈ l ++ [x], Φ k y) ⊣⊢ ([∗ list] k↦y ∈ l, Φ k y) ∗ Φ (length l) x.
  Proof. by rewrite big_opL_snoc. Qed.

  Lemma big_sepL_take_drop Φ l n :
    ([∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢
    ([∗ list] k ↦ x ∈ take n l, Φ k x) ∗ ([∗ list] k ↦ x ∈ drop n l, Φ (n + k) x).
  Proof. by rewrite big_opL_take_drop. Qed.

  Lemma big_sepL_submseteq (Φ : A → PROP) `{!∀ x, Affine (Φ x)} l1 l2 :
    l1 ⊆+ l2 → ([∗ list] y ∈ l2, Φ y) ⊢ [∗ list] y ∈ l1, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. rewrite big_sepL_app.
    induction l as [|x l IH]; simpl; [by rewrite right_id|by rewrite sep_elim_r].
  Qed.

  (** The lemmas [big_sepL_mono], [big_sepL_ne] and [big_sepL_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_sepL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_sepL_ne Φ Ψ l n :
    (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y)%I ≡{n}≡ ([∗ list] k ↦ y ∈ l, Ψ k y)%I.
  Proof. apply big_opL_ne. Qed.
  Lemma big_sepL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∗ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opL] instances. *)
  Global Instance big_sepL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_sepL_mono; intros; apply Hf. Qed.
  Global Instance big_sepL_id_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_sep PROP) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Global Instance big_sepL_nil_persistent Φ :
    Persistent ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_sepL_persistent Φ l :
    (∀ k x, l !! k = Some x → Persistent (Φ k x)) →
    Persistent ([∗ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_sepL_persistent' Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ list] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_sepL_persistent, _. Qed.
  Global Instance big_sepL_persistent_id Ps :
    TCForall Persistent Ps → Persistent ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.

  Global Instance big_sepL_nil_affine Φ :
    Affine ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_sepL_affine Φ l :
    (∀ k x, l !! k = Some x → Affine (Φ k x)) →
    Affine ([∗ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_sepL_affine' Φ l :
    (∀ k x, Affine (Φ k x)) → Affine ([∗ list] k↦x ∈ l, Φ k x).
  Proof. intros. apply big_sepL_affine, _. Qed.
  Global Instance big_sepL_affine_id Ps : TCForall Affine Ps → Affine ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.

  Global Instance big_sepL_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_sepL_timeless `{!Timeless (emp%I : PROP)} Φ l :
    (∀ k x, l !! k = Some x → Timeless (Φ k x)) →
    Timeless ([∗ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_sepL_timeless' `{!Timeless (emp%I : PROP)} Φ l :
    (∀ k x, Timeless (Φ k x)) →
    Timeless ([∗ list] k↦x ∈ l, Φ k x).
  Proof. intros. apply big_sepL_timeless, _. Qed.
  Global Instance big_sepL_timeless_id `{!Timeless (emp%I : PROP)} Ps :
    TCForall Timeless Ps → Timeless ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.

  Lemma big_sepL_emp l : ([∗ list] k↦y ∈ l, emp) ⊣⊢@{PROP} emp.
  Proof. by rewrite big_opL_unit. Qed.

  Lemma big_sepL_insert_acc Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (∀ y, Φ i y -∗ ([∗ list] k↦y ∈ <[i:=y]>l, Φ k y)).
  Proof.
    intros Hli. assert (i ≤ length l) by eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(take_drop_middle l i x) // big_sepL_app /=.
    rewrite Nat.add_0_r take_length_le //.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. apply sep_mono_r, forall_intro=> y.
    rewrite insert_app_r_alt ?take_length_le //.
    rewrite Nat.sub_diag /=. apply wand_intro_l.
    rewrite assoc !(comm _ (Φ _ _)) -assoc big_sepL_app /=.
    by rewrite Nat.add_0_r take_length_le.
  Qed.

  Lemma big_sepL_lookup_acc Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ list] k↦y ∈ l, Φ k y)).
  Proof. intros. by rewrite {1}big_sepL_insert_acc // (forall_elim x) list_insert_id. Qed.

  Lemma big_sepL_lookup Φ l i x
    `{!TCOr (∀ j y, Affine (Φ j y)) (Absorbing (Φ i x))} :
    l !! i = Some x → ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof.
    intros Hi. destruct select (TCOr _ _).
    - rewrite -(take_drop_middle l i x) // big_sepL_app /= take_length.
      apply lookup_lt_Some in Hi. rewrite (_ : _ + 0 = i); last lia.
      rewrite sep_elim_r sep_elim_l //.
    - rewrite big_sepL_lookup_acc // sep_elim_l //.
  Qed.

  Lemma big_sepL_elem_of (Φ : A → PROP) l x
    `{!TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))} :
    x ∈ l → ([∗ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup.
    destruct select (TCOr _ _); by apply: big_sepL_lookup.
  Qed.

  Lemma big_sepL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∗ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∗ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_sepL_omap {B} (f : A → option B) (Φ : B → PROP) l :
    ([∗ list] y ∈ omap f l, Φ y) ⊣⊢ ([∗ list] y ∈ l, from_option Φ emp (f y)).
  Proof. by rewrite big_opL_omap. Qed.

  Lemma big_sepL_bind {B} (f : A → list B) (Φ : B → PROP) l :
    ([∗ list] y ∈ l ≫= f, Φ y) ⊣⊢ ([∗ list] x ∈ l, [∗ list] y ∈ f x, Φ y).
  Proof. by rewrite big_opL_bind. Qed.

  Lemma big_sepL_sep Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ list] k↦x ∈ l, Φ k x) ∗ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_op. Qed.

  Lemma big_sepL_sep_2 Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x) -∗
    ([∗ list] k↦x ∈ l, Ψ k x) -∗
    ([∗ list] k↦x ∈ l, Φ k x ∗ Ψ k x).
  Proof. apply entails_wand, wand_intro_r. rewrite big_sepL_sep //. Qed.

  Lemma big_sepL_and Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊢ ([∗ list] k↦x ∈ l, Φ k x) ∧ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. auto using and_intro, big_sepL_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepL_pure_1 (φ : nat → A → Prop) l :
    ([∗ list] k↦x ∈ l, ⌜φ k x⌝) ⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    induction l as [|x l IH] using rev_ind.
    { apply pure_intro=>??. rewrite lookup_nil. done. }
    rewrite big_sepL_snoc // IH sep_and -pure_and.
    f_equiv=>-[Hl Hx] k y /lookup_app_Some =>-[Hy|[Hlen Hy]].
    - by apply Hl.
    - apply list_lookup_singleton_Some in Hy as [Hk ->].
      replace k with (length l) by lia. done.
  Qed.
  Lemma big_sepL_affinely_pure_2 (φ : nat → A → Prop) l :
    <affine> ⌜∀ k x, l !! k = Some x → φ k x⌝ ⊢@{PROP} ([∗ list] k↦x ∈ l, <affine> ⌜φ k x⌝).
  Proof.
    induction l as [|x l IH] using rev_ind.
    { rewrite big_sepL_nil. apply affinely_elim_emp. }
    rewrite big_sepL_snoc // -IH.
    rewrite -persistent_and_sep_1 -affinely_and -pure_and.
    f_equiv. f_equiv=>- Hlx. split.
    - intros k y Hy. apply Hlx. rewrite lookup_app Hy //.
    - apply Hlx. rewrite lookup_app lookup_ge_None_2 //.
      rewrite Nat.sub_diag //.
  Qed.
  (** The general backwards direction requires [BiAffine] to cover the empty case. *)
  Lemma big_sepL_pure `{!BiAffine PROP} (φ : nat → A → Prop) l :
    ([∗ list] k↦x ∈ l, ⌜φ k x⌝) ⊣⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    apply (anti_symm (⊢)); first by apply big_sepL_pure_1.
    rewrite -(affine_affinely ⌜_⌝).
    rewrite big_sepL_affinely_pure_2. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepL_persistently `{!BiAffine PROP} Φ l :
    <pers> ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ [∗ list] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_intro Φ l :
    □ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x) ⊢ [∗ list] k↦x ∈ l, Φ k x.
  Proof.
    revert Φ. induction l as [|x l IH]=> Φ /=; [by apply (affine _)|].
    rewrite intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
      by rewrite intuitionistically_elim.
    - rewrite -IH. f_equiv.
      apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL_forall `{!BiAffine PROP} Φ l :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepL_lookup. }
    revert Φ HΦ. induction l as [|x l IH]=> Φ HΦ /=.
    { apply: affine. }
    rewrite -persistent_and_sep_1. apply and_intro.
    - rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl. done.
    - rewrite -IH. apply forall_intro => k. by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL_impl Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x) -∗
    □ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ list] k↦x ∈ l, Ψ k x.
  Proof.
    apply entails_wand, wand_intro_l. rewrite big_sepL_intro -big_sepL_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepL_wand Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x) -∗
    ([∗ list] k↦x ∈ l, Φ k x -∗ Ψ k x) -∗
    [∗ list] k↦x ∈ l, Ψ k x.
  Proof.
    apply entails_wand, wand_intro_r. rewrite -big_sepL_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepL_dup P `{!Affine P} l :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ list] k↦x ∈ l, P.
  Proof.
    apply entails_wand, wand_intro_l.
    induction l as [|x l IH]=> /=; first by apply: affine.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepL_delete Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊣⊢
    Φ i x ∗ [∗ list] k↦y ∈ l, if decide (k = i) then emp else Φ k y.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // !big_sepL_app /= Nat.add_0_r.
    rewrite take_length_le; last eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite decide_True // left_id.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. do 2 f_equiv.
    - apply big_sepL_proper=> k y Hk. apply lookup_lt_Some in Hk.
      rewrite take_length in Hk. by rewrite decide_False; last lia.
    - apply big_sepL_proper=> k y _. by rewrite decide_False; last lia.
  Qed.
  Lemma big_sepL_delete' `{!BiAffine PROP} Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊣⊢ Φ i x ∗ [∗ list] k↦y ∈ l, ⌜ k ≠ i ⌝ → Φ k y.
  Proof.
    intros. rewrite big_sepL_delete //. (do 2 f_equiv)=> k y.
    rewrite -decide_emp. by repeat case_decide.
  Qed.

  Lemma big_sepL_lookup_acc_impl {Φ l} i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) -∗
    (* We obtain [Φ] for [x] *)
    Φ i x ∗
    (* We reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ k y, ⌜ l !! k = Some y ⌝ → ⌜ k ≠ i ⌝ → Φ k y -∗ Ψ k y) -∗
      Ψ i x -∗
      [∗ list] k↦y ∈ l, Ψ k y.
  Proof.
    intros. apply entails_wand.
    rewrite big_sepL_delete //. apply sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepL_delete Ψ l i x) //. apply sep_mono_r.
    eapply wand_apply; [apply wand_entails, big_sepL_impl|apply sep_mono_r].
    apply intuitionistically_intro', forall_intro=> k; apply forall_intro=> y.
    apply impl_intro_l, pure_elim_l=> ?; apply wand_intro_r.
    rewrite (forall_elim ) (forall_elim y) pure_True // left_id.
    destruct (decide _) as [->|]; [by apply: affine|].
    by rewrite pure_True //left_id intuitionistically_elim wand_elim_l.
  Qed.

  Lemma big_sepL_replicate l P :
    [∗] replicate (length l) P ⊣⊢ [∗ list] y ∈ l, P.
  Proof. induction l as [|x l]=> //=; by f_equiv. Qed.

  Lemma big_sepL_later `{!BiAffine PROP} Φ l :
    ▷ ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_sepL_later_2 Φ l :
    ([∗ list] k↦x ∈ l, ▷ Φ k x) ⊢ ▷ [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.

  Lemma big_sepL_laterN `{!BiAffine PROP} Φ n l :
    ▷^n ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_sepL_laterN_2 Φ n l :
    ([∗ list] k↦x ∈ l, ▷^n Φ k x) ⊢ ▷^n [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
End sep_list.

(* Some lemmas depend on the generalized versions of the above ones. *)
Lemma big_sepL_sep_zip_with {A B C} (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (Φ1 : nat → A → PROP) (Φ2 : nat → B → PROP) l1 l2 :
  (∀ x y, g1 (f x y) = x) →
  (∀ x y, g2 (f x y) = y) →
  length l1 = length l2 →
  ([∗ list] k↦xy ∈ zip_with f l1 l2, Φ1 k (g1 xy) ∗ Φ2 k (g2 xy)) ⊣⊢
  ([∗ list] k↦x ∈ l1, Φ1 k x) ∗ ([∗ list] k↦y ∈ l2, Φ2 k y).
Proof. apply big_opL_sep_zip_with. Qed.

Lemma big_sepL_sep_zip {A B} (Φ1 : nat → A → PROP) (Φ2 : nat → B → PROP) l1 l2 :
  length l1 = length l2 →
  ([∗ list] k↦xy ∈ zip l1 l2, Φ1 k xy.1 ∗ Φ2 k xy.2) ⊣⊢
  ([∗ list] k↦x ∈ l1, Φ1 k x) ∗ ([∗ list] k↦y ∈ l2, Φ2 k y).
Proof. apply big_opL_sep_zip. Qed.

Lemma big_sepL_zip_with {A B C} (Φ : nat → A → PROP) f (l1 : list B) (l2 : list C) :
  ([∗ list] k↦x ∈ zip_with f l1 l2, Φ k x) ⊣⊢
  ([∗ list] k↦x ∈ l1, if l2 !! k is Some y then Φ k (f x y) else emp).
Proof.
  revert Φ l2; induction l1 as [|x l1 IH]=> Φ [|y l2] //=.
  - by rewrite big_sepL_emp left_id.
  - by rewrite IH.
Qed.

(** ** Big ops over two lists *)
Lemma big_sepL2_alt {A B} (Φ : nat → A → B → PROP) l1 l2 :
  ([∗ list] k↦y1;y2 ∈ l1; l2, Φ k y1 y2) ⊣⊢
  ⌜ length l1 = length l2 ⌝ ∧ [∗ list] k ↦ xy ∈ zip l1 l2, Φ k (xy.1) (xy.2).
Proof.
  apply (anti_symm _).
  - apply and_intro.
    + revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2] /=;
        auto using pure_intro, False_elim.
      rewrite IH sep_elim_r. apply pure_mono; auto.
    + revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2] /=;
        auto using pure_intro, False_elim.
      by rewrite IH.
  - apply pure_elim_l=> /Forall2_same_length Hl. revert Φ.
    induction Hl as [|x1 l1 x2 l2 _ _ IH]=> Φ //=. by rewrite -IH.
Qed.

Section sep_list2.
  Context {A B : Type}.
  Implicit Types Φ Ψ : nat → A → B → PROP.

  Lemma big_sepL2_nil Φ : ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2) ⊣⊢ emp.
  Proof. done. Qed.
  Lemma big_sepL2_nil' P `{!Affine P} Φ : P ⊢ [∗ list] k↦y1;y2 ∈ [];[], Φ k y1 y2.
  Proof. apply: affine. Qed.
  Lemma big_sepL2_nil_inv_l Φ l2 :
    ([∗ list] k↦y1;y2 ∈ []; l2, Φ k y1 y2) ⊢ ⌜l2 = []⌝.
  Proof. destruct l2; simpl; auto using False_elim, pure_intro. Qed.
  Lemma big_sepL2_nil_inv_r Φ l1 :
    ([∗ list] k↦y1;y2 ∈ l1; [], Φ k y1 y2) ⊢ ⌜l1 = []⌝.
  Proof. destruct l1; simpl; auto using False_elim, pure_intro. Qed.

  Lemma big_sepL2_cons Φ x1 x2 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ x1 :: l1; x2 :: l2, Φ k y1 y2)
    ⊣⊢ Φ 0 x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1;l2, Φ (S k) y1 y2.
  Proof. done. Qed.
  Lemma big_sepL2_cons_inv_l Φ x1 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ x1 :: l1; l2, Φ k y1 y2) ⊢
    ∃ x2 l2', ⌜ l2 = x2 :: l2' ⌝ ∧
              Φ 0 x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1;l2', Φ (S k) y1 y2.
  Proof.
    destruct l2 as [|x2 l2]; simpl; auto using False_elim.
    by rewrite -(exist_intro x2) -(exist_intro l2) pure_True // left_id.
  Qed.
  Lemma big_sepL2_cons_inv_r Φ x2 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1; x2 :: l2, Φ k y1 y2) ⊢
    ∃ x1 l1', ⌜ l1 = x1 :: l1' ⌝ ∧
              Φ 0 x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1';l2, Φ (S k) y1 y2.
  Proof.
    destruct l1 as [|x1 l1]; simpl; auto using False_elim.
    by rewrite -(exist_intro x1) -(exist_intro l1) pure_True // left_id.
  Qed.

  Lemma big_sepL2_singleton Φ x1 x2 :
    ([∗ list] k↦y1;y2 ∈ [x1];[x2], Φ k y1 y2) ⊣⊢ Φ 0 x1 x2.
  Proof. by rewrite /= right_id. Qed.

  Lemma big_sepL2_length Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1; l2, Φ k y1 y2) ⊢ ⌜ length l1 = length l2 ⌝.
  Proof. by rewrite big_sepL2_alt and_elim_l. Qed.

  Lemma big_sepL2_fst_snd Φ l :
    ([∗ list] k↦y1;y2 ∈ l.*1; l.*2, Φ k y1 y2) ⊣⊢
    [∗ list] k ↦ xy ∈ l, Φ k (xy.1) (xy.2).
  Proof.
    rewrite big_sepL2_alt !fmap_length.
    by rewrite pure_True // True_and zip_fst_snd.
  Qed.

  Lemma big_sepL2_app Φ l1 l2 l1' l2' :
    ([∗ list] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ⊢
    ([∗ list] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k) y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2).
  Proof.
    apply wand_intro_r. revert Φ l1'. induction l1 as [|x1 l1 IH]=> Φ -[|x1' l1'] /=.
    - by rewrite left_id.
    - rewrite left_absorb. apply False_elim.
    - rewrite left_absorb. apply False_elim.
    - by rewrite -assoc IH.
  Qed.
  Lemma big_sepL2_app_inv_l Φ l1' l1'' l2 :
    ([∗ list] k↦y1;y2 ∈ l1' ++ l1''; l2, Φ k y1 y2) ⊢
    ∃ l2' l2'', ⌜ l2 = l2' ++ l2'' ⌝ ∧
                ([∗ list] k↦y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
                ([∗ list] k↦y1;y2 ∈ l1'';l2'', Φ (length l1' + k) y1 y2).
  Proof.
    rewrite -(exist_intro (take (length l1') l2))
      -(exist_intro (drop (length l1') l2)) take_drop pure_True // left_id.
    revert Φ l2. induction l1' as [|x1 l1' IH]=> Φ -[|x2 l2] /=;
       [by rewrite left_id|by rewrite left_id|apply False_elim|].
    by rewrite IH -assoc.
  Qed.
  Lemma big_sepL2_app_inv_r Φ l1 l2' l2'' :
    ([∗ list] k↦y1;y2 ∈ l1; l2' ++ l2'', Φ k y1 y2) ⊢
    ∃ l1' l1'', ⌜ l1 = l1' ++ l1'' ⌝ ∧
                ([∗ list] k↦y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
                ([∗ list] k↦y1;y2 ∈ l1'';l2'', Φ (length l2' + k) y1 y2).
  Proof.
    rewrite -(exist_intro (take (length l2') l1))
      -(exist_intro (drop (length l2') l1)) take_drop pure_True // left_id.
    revert Φ l1. induction l2' as [|x2 l2' IH]=> Φ -[|x1 l1] /=;
       [by rewrite left_id|by rewrite left_id|apply False_elim|].
    by rewrite IH -assoc.
  Qed.
  Lemma big_sepL2_app_inv Φ l1 l2 l1' l2' :
    length l1 = length l1' ∨ length l2 = length l2' →
    ([∗ list] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2) ⊢
    ([∗ list] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ∗
    ([∗ list] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k)%nat y1 y2).
  Proof.
    revert Φ l1'. induction l1 as [|x1 l1 IH]=> Φ -[|x1' l1'] /= Hlen.
    - by rewrite left_id.
    - destruct Hlen as [[=]|Hlen]. rewrite big_sepL2_length Hlen /= app_length.
      apply pure_elim'; lia.
    - destruct Hlen as [[=]|Hlen]. rewrite big_sepL2_length -Hlen /= app_length.
      apply pure_elim'; lia.
    - by rewrite -assoc IH; last lia.
  Qed.
  Lemma big_sepL2_app_same_length Φ l1 l2 l1' l2' :
    length l1 = length l1' ∨ length l2 = length l2' →
    ([∗ list] k↦y1;y2 ∈ l1 ++ l2; l1' ++ l2', Φ k y1 y2) ⊣⊢
    ([∗ list] k↦y1;y2 ∈ l1; l1', Φ k y1 y2) ∗
    ([∗ list] k↦y1;y2 ∈ l2; l2', Φ (length l1 + k)%nat y1 y2).
  Proof.
    intros. apply (anti_symm _).
    - by apply big_sepL2_app_inv.
    - apply wand_elim_l', big_sepL2_app.
  Qed.

  Lemma big_sepL2_snoc Φ x1 x2 l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1 ++ [x1]; l2 ++ [x2], Φ k y1 y2) ⊣⊢
    ([∗ list] k↦y1;y2 ∈ l1; l2, Φ k y1 y2) ∗ Φ (length l1) x1 x2.
  Proof.
    rewrite big_sepL2_app_same_length; last by auto.
    by rewrite big_sepL2_singleton Nat.add_0_r.
  Qed.

  (** The lemmas [big_sepL2_mono], [big_sepL2_ne] and [big_sepL2_proper] are more
  generic than the instances as they also give [li !! k = Some yi] in the premise. *)
  Lemma big_sepL2_mono Φ Ψ l1 l2 :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊢ Ψ k y1 y2) →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ [∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros H. rewrite !big_sepL2_alt. f_equiv. apply big_sepL_mono=> k [y1 y2].
    rewrite lookup_zip_with=> ?; simplify_option_eq; auto.
  Qed.
  Lemma big_sepL2_ne Φ Ψ l1 l2 n :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ≡{n}≡ Ψ k y1 y2) →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)%I ≡{n}≡ ([∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2)%I.
  Proof.
    intros H. rewrite !big_sepL2_alt. f_equiv. apply big_sepL_ne=> k [y1 y2].
    rewrite lookup_zip_with=> ?; simplify_option_eq; auto.
  Qed.
  Lemma big_sepL2_proper Φ Ψ l1 l2 :
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 ⊣⊢ Ψ k y1 y2) →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ [∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros; apply (anti_symm _);
      apply big_sepL2_mono; auto using equiv_entails_1_1, equiv_entails_1_2.
  Qed.
  Lemma big_sepL2_proper_2 `{!Equiv A, !Equiv B} Φ Ψ l1 l2 l1' l2' :
    l1 ≡ l1' → l2 ≡ l2' →
    (∀ k y1 y1' y2 y2',
      l1 !! k = Some y1 → l1' !! k = Some y1' → y1 ≡ y1' →
      l2 !! k = Some y2 → l2' !! k = Some y2' → y2 ≡ y2' →
      Φ k y1 y2 ⊣⊢ Ψ k y1' y2') →
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢ [∗ list] k ↦ y1;y2 ∈ l1';l2', Ψ k y1 y2.
  Proof.
    intros Hl1 Hl2 Hf. rewrite !big_sepL2_alt. f_equiv.
    { do 2 f_equiv; by apply length_proper. }
    apply big_opL_proper_2; [by f_equiv|].
    intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%lookup_zip_with_Some
      (?&?&[=<- <-]&?&?)%lookup_zip_with_Some [??]; naive_solver.
  Qed.

  Global Instance big_sepL2_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n)))
      ==> (=) ==> (=) ==> (dist n))
           (big_sepL2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepL2_ne; intros; apply Hf. Qed.
  Global Instance big_sepL2_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
      ==> (=) ==> (=) ==> (⊢))
           (big_sepL2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepL2_mono; intros; apply Hf. Qed.
  Global Instance big_sepL2_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊣⊢)))
      ==> (=) ==> (=) ==> (⊣⊢))
           (big_sepL2 (PROP:=PROP) (A:=A) (B:=B)).
  Proof. intros f g Hf l1 ? <- l2 ? <-. apply big_sepL2_proper; intros; apply Hf. Qed.

  (** Shows that some property [P] is closed under [big_sepL2]. Examples of [P]
  are [Persistent], [Affine], [Timeless]. *)
  Lemma big_sepL2_closed (P : PROP → Prop) Φ l1 l2 :
    P emp%I → P False%I →
    (∀ Q1 Q2, P Q1 → P Q2 → P (Q1 ∗ Q2)%I) →
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → P (Φ k x1 x2)) →
    P ([∗ list] k↦x1;x2 ∈ l1; l2, Φ k x1 x2)%I.
  Proof.
    intros ?? Hsep. revert l2 Φ. induction l1 as [|x1 l1 IH]=> -[|x2 l2] Φ HΦ //=.
    apply Hsep; first by auto. apply IH=> k. apply (HΦ (S k)).
  Qed.

  Global Instance big_sepL2_nil_persistent Φ :
    Persistent ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Lemma big_sepL2_persistent Φ l1 l2 :
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → Persistent (Φ k x1 x2)) →
    Persistent ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. apply big_sepL2_closed; apply _. Qed.
  Global Instance big_sepL2_persistent' Φ l1 l2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    Persistent ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. intros; apply big_sepL2_persistent, _. Qed.

  Global Instance big_sepL2_nil_affine Φ :
    Affine ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Lemma big_sepL2_affine Φ l1 l2 :
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → Affine (Φ k x1 x2)) →
    Affine ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. apply big_sepL2_closed; apply _. Qed.
  Global Instance big_sepL2_affine' Φ l1 l2 :
    (∀ k x1 x2, Affine (Φ k x1 x2)) →
    Affine ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. intros; apply big_sepL2_affine, _. Qed.

  Global Instance big_sepL2_nil_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ list] k↦y1;y2 ∈ []; [], Φ k y1 y2).
  Proof. simpl; apply _. Qed.
  Lemma big_sepL2_timeless `{!Timeless (emp%I : PROP)} Φ l1 l2 :
    (∀ k x1 x2, l1 !! k = Some x1 → l2 !! k = Some x2 → Timeless (Φ k x1 x2)) →
    Timeless ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. apply big_sepL2_closed; apply _. Qed.
  Global Instance big_sepL2_timeless' `{!Timeless (emp%I : PROP)} Φ l1 l2 :
    (∀ k x1 x2, Timeless (Φ k x1 x2)) →
    Timeless ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. intros; apply big_sepL2_timeless, _. Qed.

  Lemma big_sepL2_insert_acc Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (∀ y1 y2, Φ i y1 y2 -∗ ([∗ list] k↦y1;y2 ∈ <[i:=y1]>l1;<[i:=y2]>l2, Φ k y1 y2)).
  Proof.
    intros Hl1 Hl2. rewrite big_sepL2_alt. apply pure_elim_l=> Hl.
    rewrite {1}big_sepL_insert_acc; last by rewrite lookup_zip_with; simplify_option_eq.
    apply sep_mono_r. apply forall_intro => y1. apply forall_intro => y2.
    rewrite big_sepL2_alt !insert_length pure_True // left_id -insert_zip_with.
    by rewrite (forall_elim (y1, y2)).
  Qed.

  Lemma big_sepL2_lookup_acc Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (Φ i x1 x2 -∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)).
  Proof.
    intros. rewrite {1}big_sepL2_insert_acc // (forall_elim x1) (forall_elim x2).
    by rewrite !list_insert_id.
  Qed.

  Lemma big_sepL2_lookup Φ l1 l2 i x1 x2
    `{!TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (Absorbing (Φ i x1 x2))} :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ Φ i x1 x2.
  Proof.
    intros Hx1 Hx2. destruct select (TCOr _ _).
    - rewrite -(take_drop_middle l1 i x1) // -(take_drop_middle l2 i x2) //.
      apply lookup_lt_Some in Hx1. apply lookup_lt_Some in Hx2.
      rewrite big_sepL2_app_same_length /= 2?take_length; last lia.
      rewrite (_ : _ + 0 = i); last lia.
      rewrite sep_elim_r sep_elim_l //.
    - rewrite big_sepL2_lookup_acc // sep_elim_l //.
  Qed.

  Lemma big_sepL2_fmap_l {A'} (f : A → A') (Φ : nat → A' → B → PROP) l1 l2 :
    ([∗ list] k↦y1;y2 ∈ f <$> l1; l2, Φ k y1 y2)
    ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k (f y1) y2).
  Proof.
    rewrite !big_sepL2_alt fmap_length zip_with_fmap_l zip_with_zip big_sepL_fmap.
    by f_equiv; f_equiv=> k [??].
  Qed.
  Lemma big_sepL2_fmap_r {B'} (g : B → B') (Φ : nat → A → B' → PROP) l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1; g <$> l2, Φ k y1 y2)
    ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 (g y2)).
  Proof.
    rewrite !big_sepL2_alt fmap_length zip_with_fmap_r zip_with_zip big_sepL_fmap.
    by f_equiv; f_equiv=> k [??].
  Qed.

  Lemma big_sepL2_reverse_2 (Φ : A → B → PROP) l1 l2 :
    ([∗ list] y1;y2 ∈ l1;l2, Φ y1 y2) ⊢ ([∗ list] y1;y2 ∈ reverse l1;reverse l2, Φ y1 y2).
  Proof.
    revert l2. induction l1 as [|x1 l1 IH]; intros [|x2 l2]; simpl; auto using False_elim.
    rewrite !reverse_cons (comm bi_sep) IH.
    by rewrite (big_sepL2_app _ _ [x1] _ [x2]) big_sepL2_singleton wand_elim_l.
  Qed.
  Lemma big_sepL2_reverse (Φ : A → B → PROP) l1 l2 :
    ([∗ list] y1;y2 ∈ reverse l1;reverse l2, Φ y1 y2) ⊣⊢ ([∗ list] y1;y2 ∈ l1;l2, Φ y1 y2).
  Proof. apply (anti_symm _); by rewrite big_sepL2_reverse_2 ?reverse_involutive. Qed.

  Lemma big_sepL2_replicate_l l x Φ n :
    length l = n →
    ([∗ list] k↦x1;x2 ∈ replicate n x; l, Φ k x1 x2) ⊣⊢ [∗ list] k↦x2 ∈ l, Φ k x x2.
  Proof. intros <-. revert Φ. induction l as [|y l IH]=> //= Φ. by rewrite IH. Qed.
  Lemma big_sepL2_replicate_r l x Φ n :
    length l = n →
    ([∗ list] k↦x1;x2 ∈ l;replicate n x, Φ k x1 x2) ⊣⊢ [∗ list] k↦x1 ∈ l, Φ k x1 x.
  Proof. intros <-. revert Φ. induction l as [|y l IH]=> //= Φ. by rewrite IH. Qed.

  Lemma big_sepL2_sep Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y1 y2)
    ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
  Proof.
    rewrite !big_sepL2_alt big_sepL_sep !persistent_and_affinely_sep_l.
    rewrite -assoc (assoc _ _ (<affine> _)%I). rewrite -(comm bi_sep (<affine> _)%I).
    rewrite -assoc (assoc _ _ (<affine> _)%I) -!persistent_and_affinely_sep_l.
    by rewrite affinely_and_r persistent_and_affinely_sep_l idemp.
  Qed.

  Lemma big_sepL2_sep_2 Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y1 y2).
  Proof. apply entails_wand, wand_intro_r. rewrite big_sepL2_sep //. Qed.

  Lemma big_sepL2_and Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∧ Ψ k y1 y2)
    ⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∧ ([∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
  Proof. auto using and_intro, big_sepL2_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepL2_pure_1 (φ : nat → A → B → Prop) l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, ⌜φ k y1 y2⌝) ⊢@{PROP}
      ⌜∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → φ k y1 y2⌝.
  Proof.
    rewrite big_sepL2_alt big_sepL_pure_1.
    rewrite -pure_and. f_equiv=>-[Hlen Hlookup] k y1 y2 Hy1 Hy2.
    eapply (Hlookup k (y1, y2)).
    rewrite lookup_zip_with Hy1 /= Hy2 /= //.
  Qed.
  Lemma big_sepL2_affinely_pure_2 (φ : nat → A → B → Prop) l1 l2 :
    length l1 = length l2 →
    <affine> ⌜∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → φ k y1 y2⌝ ⊢@{PROP}
    ([∗ list] k↦y1;y2 ∈ l1;l2, <affine> ⌜φ k y1 y2⌝).
  Proof.
    intros Hdom. rewrite big_sepL2_alt.
    rewrite -big_sepL_affinely_pure_2.
    rewrite affinely_and_r -pure_and. f_equiv. f_equiv=>-Hforall.
    split; first done.
    intros k [y1 y2] (? & ? & [= <- <-] & Hy1 & Hy2)%lookup_zip_with_Some.
    by eapply Hforall.
  Qed.
  (** The general backwards direction requires [BiAffine] to cover the empty case. *)
  Lemma big_sepL2_pure `{!BiAffine PROP} (φ : nat → A → B → Prop) l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, ⌜φ k y1 y2⌝) ⊣⊢@{PROP}
      ⌜length l1 = length l2 ∧
       ∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → φ k y1 y2⌝.
  Proof.
    apply (anti_symm (⊢)).
    { rewrite pure_and. apply and_intro.
      - apply big_sepL2_length.
      - apply big_sepL2_pure_1. }
    rewrite -(affine_affinely ⌜_⌝%I).
    rewrite pure_and -affinely_and_r.
    apply pure_elim_l=>Hdom.
    rewrite big_sepL2_affinely_pure_2 //. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepL2_persistently `{!BiAffine PROP} Φ l1 l2 :
    <pers> ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)
    ⊣⊢ [∗ list] k↦y1;y2 ∈ l1;l2, <pers> (Φ k y1 y2).
  Proof.
    by rewrite !big_sepL2_alt persistently_and persistently_pure big_sepL_persistently.
  Qed.

  Lemma big_sepL2_intro Φ l1 l2 :
    length l1 = length l2 →
    □ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2) ⊢
    [∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2.
  Proof.
    revert l2 Φ. induction l1 as [|x1 l1 IH]=> -[|x2 l2] Φ ?; simplify_eq/=.
    { by apply (affine _). }
    rewrite intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim 0) (forall_elim x1) (forall_elim x2).
      by rewrite !pure_True // !True_impl intuitionistically_elim.
    - rewrite -IH //. f_equiv.
      by apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL2_forall `{!BiAffine PROP} Φ l1 l2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2) ⊣⊢
      ⌜length l1 = length l2⌝
      ∧ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply and_intro; [apply big_sepL2_length|].
      apply forall_intro=> k. apply forall_intro=> x1. apply forall_intro=> x2.
      do 2 (apply impl_intro_l; apply pure_elim_l=> ?). by apply: big_sepL2_lookup. }
    apply pure_elim_l=> Hlen.
    revert l2 Φ HΦ Hlen. induction l1 as [|x1 l1 IH]=> -[|x2 l2] Φ HΦ Hlen; simplify_eq/=.
    { by apply (affine _). }
    rewrite -persistent_and_sep_1. apply and_intro.
    - rewrite (forall_elim 0) (forall_elim x1) (forall_elim x2).
      by rewrite !pure_True // !True_impl.
    - rewrite -IH //.
      by apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL2_impl Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    □ (∀ k x1 x2,
      ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2) -∗
    [∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    apply entails_wand. rewrite -(idemp bi_and (big_sepL2 _ _ _)) {1}big_sepL2_length.
    apply pure_elim_l=> ?. rewrite big_sepL2_intro //.
    apply bi.wand_intro_l. rewrite -big_sepL2_sep. by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepL2_wand Φ Ψ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 -∗ Ψ k y1 y2) -∗
    [∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    apply entails_wand, wand_intro_r. rewrite -big_sepL2_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepL2_delete Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
    Φ i x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1;l2, if decide (k = i) then emp else Φ k y1 y2.
  Proof.
    intros. rewrite -(take_drop_middle l1 i x1) // -(take_drop_middle l2 i x2) //.
    assert (i < length l1 ∧ i < length l2) as [??] by eauto using lookup_lt_Some.
    rewrite !big_sepL2_app_same_length /=; [|rewrite ?take_length; lia..].
    rewrite Nat.add_0_r take_length_le; [|lia].
    rewrite decide_True // left_id.
    rewrite assoc -!(comm _ (Φ _ _ _)) -assoc. do 2 f_equiv.
    - apply big_sepL2_proper=> k y1 y2 Hk. apply lookup_lt_Some in Hk.
      rewrite take_length in Hk. by rewrite decide_False; last lia.
    - apply big_sepL2_proper=> k y1 y2 _. by rewrite decide_False; last lia.
  Qed.
  Lemma big_sepL2_delete' `{!BiAffine PROP} Φ l1 l2 i x1 x2 :
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊣⊢
    Φ i x1 x2 ∗ [∗ list] k↦y1;y2 ∈ l1;l2, ⌜ k ≠ i ⌝ → Φ k y1 y2.
  Proof.
    intros. rewrite big_sepL2_delete //. (do 2 f_equiv)=> k y1 y2.
    rewrite -decide_emp. by repeat case_decide.
  Qed.

  Lemma big_sepL2_lookup_acc_impl {Φ l1 l2} i x1 x2 :
    l1 !! i = Some x1 →
    l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) -∗
    (* We obtain [Φ] for the [x1] and [x2] *)
    Φ i x1 x2 ∗
    (* We reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ k y1 y2,
        ⌜ l1 !! k = Some y1 ⌝ → ⌜ l2 !! k = Some y2 ⌝ → ⌜ k ≠ i ⌝ →
        Φ k y1 y2 -∗ Ψ k y1 y2) -∗
      Ψ i x1 x2 -∗
      [∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2.
  Proof.
    intros. rewrite big_sepL2_delete //. apply entails_wand, sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepL2_delete Ψ l1 l2 i) //. apply sep_mono_r.
    eapply wand_apply; [apply wand_entails, big_sepL2_impl|apply sep_mono_r].
    apply intuitionistically_intro', forall_intro=> k;
      apply forall_intro=> y1; apply forall_intro=> y2.
    do 2 (apply impl_intro_l, pure_elim_l=> ?); apply wand_intro_r.
    rewrite (forall_elim k) (forall_elim y1) (forall_elim y2).
    rewrite !(pure_True (_ = Some _)) // !left_id.
    destruct (decide _) as [->|]; [by apply: affine|].
    by rewrite pure_True //left_id intuitionistically_elim wand_elim_l.
  Qed.

  Lemma big_sepL2_later_1 `{!BiAffine PROP} Φ l1 l2 :
    (▷ [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢ ◇ [∗ list] k↦y1;y2 ∈ l1;l2, ▷ Φ k y1 y2.
  Proof.
    rewrite !big_sepL2_alt later_and big_sepL_later (timeless ⌜ _ ⌝).
    rewrite except_0_and. auto using and_mono, except_0_intro.
  Qed.

  Lemma big_sepL2_later_2 Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, ▷ Φ k y1 y2) ⊢ ▷ [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2.
  Proof.
    rewrite !big_sepL2_alt later_and big_sepL_later_2.
    auto using and_mono, later_intro.
  Qed.

  Lemma big_sepL2_laterN_2 Φ n l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l1;l2, ▷^n Φ k y1 y2) ⊢ ▷^n [∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2.
  Proof.
    rewrite !big_sepL2_alt laterN_and big_sepL_laterN_2.
    auto using and_mono, laterN_intro.
  Qed.

  Lemma big_sepL2_flip Φ l1 l2 :
    ([∗ list] k↦y1;y2 ∈ l2; l1, Φ k y2 y1) ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1; l2, Φ k y1 y2).
  Proof.
    revert Φ l2. induction l1 as [|x1 l1 IH]=> Φ -[|x2 l2]//=; simplify_eq.
    by rewrite IH.
  Qed.

  Lemma big_sepL2_sepL (Φ1 : nat → A → PROP) (Φ2 : nat → B → PROP) l1 l2 :
    length l1 = length l2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ1 k y1 ∗ Φ2 k y2) ⊣⊢
    ([∗ list] k↦y1 ∈ l1, Φ1 k y1) ∗ ([∗ list] k↦y2 ∈ l2, Φ2 k y2).
  Proof.
    intros. rewrite -big_sepL_sep_zip // big_sepL2_alt pure_True // left_id //.
  Qed.
  Lemma big_sepL2_sepL_2 (Φ1 : nat → A → PROP) (Φ2 : nat → B → PROP) l1 l2 :
    length l1 = length l2 →
    ([∗ list] k↦y1 ∈ l1, Φ1 k y1) -∗
    ([∗ list] k↦y2 ∈ l2, Φ2 k y2) -∗
    [∗ list] k↦y1;y2 ∈ l1;l2, Φ1 k y1 ∗ Φ2 k y2.
  Proof. intros. apply entails_wand, wand_intro_r. by rewrite big_sepL2_sepL. Qed.
End sep_list2.

Lemma big_sepL2_const_sepL_l {A B} (Φ : nat → A → PROP) (l1 : list A) (l2 : list B) :
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1)
  ⊣⊢ ⌜length l1 = length l2⌝ ∧ ([∗ list] k↦y1 ∈ l1, Φ k y1).
Proof.
  rewrite big_sepL2_alt.
  trans (⌜length l1 = length l2⌝ ∧ [∗ list] k↦y1 ∈ (zip l1 l2).*1, Φ k y1)%I.
  { rewrite big_sepL_fmap //. }
  apply (anti_symm (⊢)); apply pure_elim_l=> Hl; rewrite fst_zip;
    rewrite ?Hl //;
    (apply and_intro; [by apply pure_intro|done]).
Qed.
Lemma big_sepL2_const_sepL_r {A B}  (Φ : nat → B → PROP) (l1 : list A) (l2 : list B) :
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y2)
  ⊣⊢ ⌜length l1 = length l2⌝ ∧ ([∗ list] k↦y2 ∈ l2, Φ k y2).
Proof. by rewrite big_sepL2_flip big_sepL2_const_sepL_l (symmetry_iff (=)). Qed.

Lemma big_sepL2_sep_sepL_l {A B} (Φ : nat → A → PROP)
    (Ψ : nat → A → B → PROP) l1 l2 :
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 ∗ Ψ k y1 y2)
  ⊣⊢ ([∗ list] k↦y1 ∈ l1, Φ k y1) ∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Ψ k y1 y2).
Proof.
  rewrite big_sepL2_sep big_sepL2_const_sepL_l. apply (anti_symm _).
  { rewrite and_elim_r. done. }
  rewrite !big_sepL2_alt [(_ ∗ _)%I]comm -!persistent_and_sep_assoc.
  apply pure_elim_l=>Hl. apply and_intro.
  { apply pure_intro. done. }
  rewrite [(_ ∗ _)%I]comm. apply sep_mono; first done.
  apply and_intro; last done.
  apply pure_intro. done.
Qed.
Lemma big_sepL2_sep_sepL_r {A B} (Φ : nat → A → B → PROP)
    (Ψ : nat → B → PROP) l1 l2 :
  ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2 ∗ Ψ k y2)
  ⊣⊢ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ∗ ([∗ list] k↦y2 ∈ l2, Ψ k y2).
Proof.
  rewrite !(big_sepL2_flip _ _ l1). setoid_rewrite (comm bi_sep).
  by rewrite big_sepL2_sep_sepL_l.
Qed.

Lemma big_sepL_sepL2_diag {A} (Φ : nat → A → A → PROP) (l : list A) :
  ([∗ list] k↦y ∈ l, Φ k y y) ⊢
  ([∗ list] k↦y1;y2 ∈ l;l, Φ k y1 y2).
Proof.
  rewrite big_sepL2_alt. rewrite pure_True // left_id.
  rewrite zip_diag big_sepL_fmap /=. done.
Qed.

Lemma big_sepL2_ne_2 {A B : ofe}
    (Φ Ψ : nat → A → B → PROP) l1 l2 l1' l2' n :
  l1 ≡{n}≡ l1' → l2 ≡{n}≡ l2' →
  (∀ k y1 y1' y2 y2',
    l1 !! k = Some y1 → l1' !! k = Some y1' → y1 ≡{n}≡ y1' →
    l2 !! k = Some y2 → l2' !! k = Some y2' → y2 ≡{n}≡ y2' →
    Φ k y1 y2 ≡{n}≡ Ψ k y1' y2') →
  ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)%I ≡{n}≡ ([∗ list] k ↦ y1;y2 ∈ l1';l2', Ψ k y1 y2)%I.
Proof.
  intros Hl1 Hl2 Hf. rewrite !big_sepL2_alt. f_equiv.
  { do 2 f_equiv; by apply: length_ne. }
  apply big_opL_ne_2; [by f_equiv|].
  intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%lookup_zip_with_Some
    (?&?&[=<- <-]&?&?)%lookup_zip_with_Some [??]; naive_solver.
Qed.

Section and_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_andL_nil Φ : ([∧ list] k↦y ∈ nil, Φ k y) ⊣⊢ True.
  Proof. done. Qed.
  Lemma big_andL_nil' P Φ : P ⊢ [∧ list] k↦y ∈ nil, Φ k y.
  Proof. by apply pure_intro. Qed.
  Lemma big_andL_cons Φ x l :
    ([∧ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∧ [∧ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_andL_singleton Φ x : ([∧ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_andL_app Φ l1 l2 :
    ([∧ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∧ list] k↦y ∈ l1, Φ k y) ∧ ([∧ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.
  Lemma big_andL_snoc Φ l x :
    ([∧ list] k↦y ∈ l ++ [x], Φ k y) ⊣⊢ ([∧ list] k↦y ∈ l, Φ k y) ∧ Φ (length l) x.
  Proof. by rewrite big_opL_snoc. Qed.

  Lemma big_andL_submseteq (Φ : A → PROP) l1 l2 :
    l1 ⊆+ l2 → ([∧ list] y ∈ l2, Φ y) ⊢ [∧ list] y ∈ l1, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. by rewrite big_andL_app and_elim_l.
  Qed.

  (** The lemmas [big_andL_mono], [big_andL_ne] and [big_andL_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_andL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y) ⊢ [∧ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_andL_ne Φ Ψ l n :
    (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y)%I ≡{n}≡ ([∧ list] k ↦ y ∈ l, Ψ k y)%I.
  Proof. apply big_opL_ne. Qed.
  Lemma big_andL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∧ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∧ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opL] instances. *)
  Global Instance big_andL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_and PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_andL_mono; intros; apply Hf. Qed.
  Global Instance big_andL_id_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_and PROP) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Global Instance big_andL_nil_absorbing Φ :
    Absorbing ([∧ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_andL_absorbing Φ l :
    (∀ k x, l !! k = Some x → Absorbing (Φ k x)) →
    Absorbing ([∧ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_andL_absorbing' Φ l :
    (∀ k x, Absorbing (Φ k x)) → Absorbing ([∧ list] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_andL_absorbing, _. Qed.

  Global Instance big_andL_nil_persistent Φ :
    Persistent ([∧ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_andL_persistent Φ l :
    (∀ k x, l !! k = Some x → Persistent (Φ k x)) → Persistent ([∧ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_andL_persistent' Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∧ list] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_andL_persistent, _. Qed.

  Global Instance big_andL_nil_timeless Φ :
    Timeless ([∧ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Lemma big_andL_timeless Φ l :
    (∀ k x, l !! k = Some x → Timeless (Φ k x)) →
    Timeless ([∧ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_andL_timeless' Φ l :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∧ list] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_andL_timeless, _. Qed.

  Lemma big_andL_lookup Φ l i x :
    l !! i = Some x → ([∧ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof.
    intros. rewrite -(take_drop_middle l i x) // big_andL_app /=.
    rewrite Nat.add_0_r take_length_le;
      eauto using lookup_lt_Some, Nat.lt_le_incl, and_elim_l', and_elim_r'.
  Qed.

  Lemma big_andL_elem_of (Φ : A → PROP) l x :
    x ∈ l → ([∧ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup. by eapply (big_andL_lookup (λ _, Φ)).
  Qed.

  Lemma big_andL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∧ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∧ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_andL_bind {B} (f : A → list B) (Φ : B → PROP) l :
    ([∧ list] y ∈ l ≫= f, Φ y) ⊣⊢ ([∧ list] x ∈ l, [∧ list] y ∈ f x, Φ y).
  Proof. by rewrite big_opL_bind. Qed.

  Lemma big_andL_and Φ Ψ l :
    ([∧ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊣⊢ ([∧ list] k↦x ∈ l, Φ k x) ∧ ([∧ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_op. Qed.

  Lemma big_andL_persistently Φ l :
    <pers> ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ [∧ list] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_andL_forall Φ l :
    ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_andL_lookup. }
    revert Φ. induction l as [|x l IH]=> Φ; [by auto using big_andL_nil'|].
    rewrite big_andL_cons. apply and_intro.
    - by rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
    - rewrite -IH. apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.
  Lemma big_andL_intro Φ l :
    (∀ k x, ⌜l !! k = Some x⌝ → Φ k x) ⊢ [∧ list] k↦x ∈ l, Φ k x.
  Proof. rewrite big_andL_forall //. Qed.

  Lemma big_andL_impl Φ Ψ m :
    ([∧ list] k↦x ∈ m, Φ k x) ∧
    (∀ k x, ⌜m !! k = Some x⌝ → Φ k x → Ψ k x) ⊢
    [∧ list] k↦x ∈ m, Ψ k x.
  Proof.
    rewrite -big_andL_forall -big_andL_and.
    by setoid_rewrite bi.impl_elim_r.
  Qed.

  Lemma big_andL_pure_1 (φ : nat → A → Prop) l :
    ([∧ list] k↦x ∈ l, ⌜φ k x⌝) ⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    induction l as [|x l IH] using rev_ind.
    { apply pure_intro=>??. rewrite lookup_nil. done. }
    rewrite big_andL_snoc // IH -pure_and.
    f_equiv=>-[Hl Hx] k y /lookup_app_Some =>-[Hy|[Hlen Hy]].
    - by apply Hl.
    - apply list_lookup_singleton_Some in Hy as [Hk ->].
      replace k with (length l) by lia. done.
  Qed.
  Lemma big_andL_pure_2 (φ : nat → A → Prop) l :
    ⌜∀ k x, l !! k = Some x → φ k x⌝ ⊢@{PROP} ([∧ list] k↦x ∈ l, ⌜φ k x⌝).
  Proof.
    rewrite big_andL_forall pure_forall_1. f_equiv=>k.
    rewrite pure_forall_1. f_equiv=>x. apply pure_impl_1.
  Qed.
  Lemma big_andL_pure (φ : nat → A → Prop) l :
    ([∧ list] k↦x ∈ l, ⌜φ k x⌝) ⊣⊢@{PROP} ⌜∀ k x, l !! k = Some x → φ k x⌝.
  Proof.
    apply (anti_symm (⊢)); first by apply big_andL_pure_1.
    apply big_andL_pure_2.
  Qed.

  Lemma big_andL_later Φ l :
    ▷ ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∧ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_andL_laterN Φ n l :
    ▷^n ([∧ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∧ list] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opL_commute _). Qed.
End and_list.

Section or_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_orL_nil Φ : ([∨ list] k↦y ∈ nil, Φ k y) ⊣⊢ False.
  Proof. done. Qed.
  Lemma big_orL_cons Φ x l :
    ([∨ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∨ [∨ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_orL_singleton Φ x : ([∨ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_orL_app Φ l1 l2 :
    ([∨ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∨ list] k↦y ∈ l1, Φ k y) ∨ ([∨ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.
  Lemma big_orL_snoc Φ l x :
    ([∨ list] k↦y ∈ l ++ [x], Φ k y) ⊣⊢ ([∨ list] k↦y ∈ l, Φ k y) ∨ Φ (length l) x.
  Proof. by rewrite big_opL_snoc. Qed.

  Lemma big_orL_submseteq (Φ : A → PROP) l1 l2 :
    l1 ⊆+ l2 → ([∨ list] y ∈ l1, Φ y) ⊢ [∨ list] y ∈ l2, Φ y.
  Proof.
    intros [l ->]%submseteq_Permutation. by rewrite big_orL_app -or_intro_l.
  Qed.

  (** The lemmas [big_orL_mono], [big_orL_ne] and [big_orL_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_orL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∨ list] k ↦ y ∈ l, Φ k y) ⊢ [∨ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_gen_proper; apply _. Qed.
  Lemma big_orL_ne Φ Ψ l n :
    (∀ k y, l !! k = Some y → Φ k y ≡{n}≡ Ψ k y) →
    ([∨ list] k ↦ y ∈ l, Φ k y)%I ≡{n}≡ ([∨ list] k ↦ y ∈ l, Ψ k y)%I.
  Proof. apply big_opL_ne. Qed.
  Lemma big_orL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∨ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∨ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opL] instances. *)
  Global Instance big_orL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@bi_or PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_orL_mono; intros; apply Hf. Qed.
  Global Instance big_orL_id_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@bi_or PROP) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Global Instance big_orL_nil_persistent Φ :
    Persistent ([∨ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_orL_persistent Φ l :
    (∀ k x, l !! k = Some x → Persistent (Φ k x)) →
    Persistent ([∨ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_orL_persistent' Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∨ list] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_orL_persistent, _. Qed.

  Global Instance big_orL_nil_timeless Φ :
    Timeless ([∨ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_orL_timeless Φ l :
    (∀ k x, l !! k = Some x → Timeless (Φ k x)) →
    Timeless ([∨ list] k↦x ∈ l, Φ k x).
  Proof. apply big_opL_closed; apply _. Qed.
  Global Instance big_orL_timeless' Φ l :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∨ list] k↦x ∈ l, Φ k x).
  Proof. intros; apply big_orL_timeless, _. Qed.

  Lemma big_orL_intro Φ l i x :
    l !! i = Some x → Φ i x ⊢ ([∨ list] k↦y ∈ l, Φ k y).
  Proof.
    intros. rewrite -(take_drop_middle l i x) // big_orL_app /=.
    rewrite Nat.add_0_r take_length_le;
      eauto using lookup_lt_Some, Nat.lt_le_incl, or_intro_l', or_intro_r'.
  Qed.

  Lemma big_orL_elem_of (Φ : A → PROP) l x :
    x ∈ l → Φ x ⊢ ([∨ list] y ∈ l, Φ y).
  Proof.
    intros [i ?]%elem_of_list_lookup; by eapply (big_orL_intro (λ _, Φ)).
  Qed.

  Lemma big_orL_fmap {B} (f : A → B) (Φ : nat → B → PROP) l :
    ([∨ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∨ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_orL_bind {B} (f : A → list B) (Φ : B → PROP) l :
    ([∨ list] y ∈ l ≫= f, Φ y) ⊣⊢ ([∨ list] x ∈ l, [∨ list] y ∈ f x, Φ y).
  Proof. by rewrite big_opL_bind. Qed.

  Lemma big_orL_or Φ Ψ l :
    ([∨ list] k↦x ∈ l, Φ k x ∨ Ψ k x)
    ⊣⊢ ([∨ list] k↦x ∈ l, Φ k x) ∨ ([∨ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_op. Qed.

  Lemma big_orL_persistently Φ l :
    <pers> ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ [∨ list] k↦x ∈ l, <pers> (Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_orL_exist Φ l :
    ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ (∃ k x, ⌜l !! k = Some x⌝ ∧ Φ k x).
  Proof.
    apply (anti_symm _).
    { revert Φ. induction l as [|x l IH]=> Φ.
      { rewrite big_orL_nil. apply False_elim. }
      rewrite big_orL_cons. apply or_elim.
      - by rewrite -(exist_intro 0) -(exist_intro x) pure_True // left_id.
      - rewrite IH. apply exist_elim=> k. by rewrite -(exist_intro (S k)). }
    apply exist_elim=> k; apply exist_elim=> x. apply pure_elim_l=> ?.
    by apply: big_orL_intro.
  Qed.

  Lemma big_orL_pure (φ : nat → A → Prop) l :
    ([∨ list] k↦x ∈ l, ⌜φ k x⌝) ⊣⊢@{PROP} ⌜∃ k x, l !! k = Some x ∧ φ k x⌝.
  Proof.
    rewrite big_orL_exist.
    rewrite pure_exist. apply exist_proper=>k.
    rewrite pure_exist. apply exist_proper=>x.
    rewrite -pure_and. done.
  Qed.

  Lemma big_orL_sep_l P Φ l :
    P ∗ ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∨ list] k↦x ∈ l, P ∗ Φ k x).
  Proof.
    rewrite !big_orL_exist sep_exist_l.
    f_equiv=> k. rewrite sep_exist_l. f_equiv=> x.
    by rewrite !persistent_and_affinely_sep_l !assoc (comm _ P).
 Qed.
  Lemma big_orL_sep_r Q Φ l :
    ([∨ list] k↦x ∈ l, Φ k x) ∗ Q ⊣⊢ ([∨ list] k↦x ∈ l, Φ k x ∗ Q).
  Proof. setoid_rewrite (comm bi_sep). apply big_orL_sep_l. Qed.

  Lemma big_orL_later Φ l :
    l ≠ [] →
    ▷ ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∨ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_orL_laterN Φ n l :
    l ≠ [] →
    ▷^n ([∨ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∨ list] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opL_commute1 _). Qed.
End or_list.

(** ** Big ops over finite maps *)
Section sep_map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  (** The lemmas [big_sepM_mono], [big_sepM_ne] and [big_sepM_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_sepM_mono Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ [∗ map] k ↦ x ∈ m, Ψ k x.
  Proof. apply big_opM_gen_proper; apply _ || auto. Qed.
  Lemma big_sepM_ne Φ Ψ m n :
    (∀ k x, m !! k = Some x → Φ k x ≡{n}≡ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x)%I ≡{n}≡ ([∗ map] k ↦ x ∈ m, Ψ k x)%I.
  Proof. apply big_opM_ne. Qed.
  Lemma big_sepM_proper Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗ map] k ↦ x ∈ m, Ψ k x).
  Proof. apply big_opM_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opM] instances. *)
  Global Instance big_sepM_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opM (@bi_sep PROP) (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_sepM_mono; intros; apply Hf. Qed.

  Global Instance big_sepM_empty_persistent Φ :
    Persistent ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_empty. apply _. Qed.
  Lemma big_sepM_persistent Φ m :
    (∀ k x, m !! k = Some x → Persistent (Φ k x)) →
    Persistent ([∗ map] k↦x ∈ m, Φ k x).
  Proof. apply big_opM_closed; apply _. Qed.
  Global Instance big_sepM_persistent' Φ m :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros; apply big_sepM_persistent, _. Qed.

  Global Instance big_sepM_empty_affine Φ :
    Affine ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_empty. apply _. Qed.
  Lemma big_sepM_affine Φ m :
    (∀ k x, m !! k = Some x → Affine (Φ k x)) →
    Affine ([∗ map] k↦x ∈ m, Φ k x).
  Proof. apply big_opM_closed; apply _. Qed.
  Global Instance big_sepM_affine' Φ m :
    (∀ k x, Affine (Φ k x)) → Affine ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros; apply big_sepM_affine, _. Qed.

  Global Instance big_sepM_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_empty. apply _. Qed.
  Lemma big_sepM_timeless `{!Timeless (emp%I : PROP)} Φ m :
    (∀ k x, m !! k = Some x → Timeless (Φ k x)) →
    Timeless ([∗ map] k↦x ∈ m, Φ k x).
  Proof. apply big_opM_closed; apply _. Qed.
  Global Instance big_sepM_timeless' `{!Timeless (emp%I : PROP)} Φ m :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros; apply big_sepM_timeless, _. Qed.

  (* We place the [Affine] instance after [m1] and [m2], so that
     manually instantiating [m1] or [m2] in [iApply] does not also
     implicitly instantiate the [Affine] instance. If it gets
     instantiated too early, [Φ] is not known, and typeclass inference
     fails. *)
  Lemma big_sepM_subseteq Φ m1 m2 `{!∀ k x, Affine (Φ k x)} :
    m2 ⊆ m1 → ([∗ map] k ↦ x ∈ m1, Φ k x) ⊢ [∗ map] k ↦ x ∈ m2, Φ k x.
  Proof.
    intros ?. rewrite -(map_difference_union m2 m1) //.
    rewrite big_opM_union; last by apply map_disjoint_difference_r.
    assert (∀ kx, Affine (uncurry Φ kx)) by (intros []; apply _).
    by rewrite sep_elim_l.
  Qed.

  Lemma big_sepM_empty Φ : ([∗ map] k↦x ∈ ∅, Φ k x) ⊣⊢ emp.
  Proof. by rewrite big_opM_empty. Qed.
  Lemma big_sepM_empty' P `{!Affine P} Φ : P ⊢ [∗ map] k↦x ∈ ∅, Φ k x.
  Proof. rewrite big_sepM_empty. apply: affine. Qed.

  Lemma big_sepM_insert Φ m i x :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y.
  Proof. apply big_opM_insert. Qed.

  Lemma big_sepM_delete Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_delete. Qed.

  Lemma big_sepM_insert_delete Φ m i x :
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_insert_delete. Qed.

  Lemma big_sepM_insert_2 Φ m i x
    `{!TCOr (∀ y, Affine (Φ i y)) (Absorbing (Φ i x))} :
    Φ i x ⊢ ([∗ map] k↦y ∈ m, Φ k y) -∗ [∗ map] k↦y ∈ <[i:=x]> m, Φ k y.
  Proof.
    apply wand_intro_r. destruct (m !! i) as [y|] eqn:Hi; last first.
    { by rewrite -big_sepM_insert. }
    assert (TCOr (Affine (Φ i y)) (Absorbing (Φ i x))).
    { destruct select (TCOr _ _); apply _. }
    rewrite big_sepM_delete // assoc.
    rewrite (sep_elim_l (Φ i x)) -big_sepM_insert ?lookup_delete //.
    by rewrite insert_delete_insert.
  Qed.

  Lemma big_sepM_lookup_acc Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ map] k↦y ∈ m, Φ k y)).
  Proof.
    intros. rewrite big_sepM_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepM_lookup Φ m i x
    `{!TCOr (∀ j y, Affine (Φ j y)) (Absorbing (Φ i x))} :
    m !! i = Some x → ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
  Proof.
    intros Hi. destruct select (TCOr _ _).
    - rewrite big_sepM_delete // sep_elim_l //.
    - rewrite big_sepM_lookup_acc // sep_elim_l //.
  Qed.

  Lemma big_sepM_lookup_dom (Φ : K → PROP) m i
    `{!TCOr (∀ j, Affine (Φ j)) (Absorbing (Φ i))} :
    is_Some (m !! i) → ([∗ map] k↦_ ∈ m, Φ k) ⊢ Φ i.
  Proof. intros [x ?]. destruct select (TCOr _ _); by apply: big_sepM_lookup. Qed.

  Lemma big_sepM_singleton Φ i x : ([∗ map] k↦y ∈ {[i:=x]}, Φ k y) ⊣⊢ Φ i x.
  Proof. by rewrite big_opM_singleton. Qed.

  Lemma big_sepM_fmap {B} (f : A → B) (Φ : K → B → PROP) m :
    ([∗ map] k↦y ∈ f <$> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k (f y)).
  Proof. by rewrite big_opM_fmap. Qed.

  Lemma big_sepM_omap {B} (f : A → option B) (Φ : K → B → PROP) m :
    ([∗ map] k↦y ∈ omap f m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, from_option (Φ k) emp (f y)).
  Proof. by rewrite big_opM_omap. Qed.

  Lemma big_sepM_insert_override Φ m i x x' :
    m !! i = Some x → (Φ i x ⊣⊢ Φ i x') →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k y).
  Proof. apply big_opM_insert_override. Qed.

  Lemma big_sepM_insert_override_1 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊢
      (Φ i x' -∗ Φ i x) -∗ ([∗ map] k↦y ∈ m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite -insert_delete_insert big_sepM_insert ?lookup_delete //.
    by rewrite assoc wand_elim_l -big_sepM_delete.
  Qed.

  Lemma big_sepM_insert_override_2 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
      (Φ i x -∗ Φ i x') -∗ ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite {1}big_sepM_delete //; rewrite assoc wand_elim_l.
    rewrite -insert_delete_insert big_sepM_insert ?lookup_delete //.
  Qed.

  Lemma big_sepM_insert_acc Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
      Φ i x ∗ (∀ x', Φ i x' -∗ ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y)).
  Proof.
    intros ?. rewrite {1}big_sepM_delete //. apply sep_mono; [done|].
    apply forall_intro=> x'.
    rewrite -insert_delete_insert big_sepM_insert ?lookup_delete //.
    by apply wand_intro_l.
  Qed.

  Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → PROP) (f : K → B) m i x b :
    m !! i = None →
       ([∗ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
    ⊣⊢ (Ψ i x b ∗ [∗ map] k↦y ∈ m, Ψ k y (f k)).
  Proof. apply big_opM_fn_insert. Qed.

  Lemma big_sepM_fn_insert' (Φ : K → PROP) m i x P :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∗ [∗ map] k↦y ∈ m, Φ k).
  Proof. apply big_opM_fn_insert'. Qed.

  Lemma big_sepM_filter' (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} Φ m :
    ([∗ map] k ↦ x ∈ filter φ m, Φ k x) ⊣⊢
    ([∗ map] k ↦ x ∈ m, if decide (φ (k, x)) then Φ k x else emp).
  Proof. apply: big_opM_filter'. Qed.
  Lemma big_sepM_filter `{!BiAffine PROP}
      (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} Φ m :
    ([∗ map] k ↦ x ∈ filter φ m, Φ k x) ⊣⊢
    ([∗ map] k ↦ x ∈ m, ⌜φ (k, x)⌝ → Φ k x).
  Proof. setoid_rewrite <-decide_emp. apply big_sepM_filter'. Qed.

  Lemma big_sepM_union Φ m1 m2 :
    m1 ##ₘ m2 →
    ([∗ map] k↦y ∈ m1 ∪ m2, Φ k y)
    ⊣⊢ ([∗ map] k↦y ∈ m1, Φ k y) ∗ ([∗ map] k↦y ∈ m2, Φ k y).
  Proof. apply big_opM_union. Qed.

  Lemma big_sepM_sep Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ map] k↦x ∈ m, Φ k x) ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. apply big_opM_op. Qed.

  Lemma big_sepM_sep_2 Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ([∗ map] k↦x ∈ m, Ψ k x) -∗
    ([∗ map] k↦x ∈ m, Φ k x ∗ Ψ k x).
  Proof. apply entails_wand, wand_intro_r. rewrite big_sepM_sep //. Qed.

  Lemma big_sepM_and Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∧ Ψ k x)
    ⊢ ([∗ map] k↦x ∈ m, Φ k x) ∧ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. auto using and_intro, big_sepM_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepM_pure_1 (φ : K → A → Prop) m :
    ([∗ map] k↦x ∈ m, ⌜φ k x⌝) ⊢@{PROP} ⌜map_Forall φ m⌝.
  Proof.
    induction m as [|k x m ? IH] using map_ind.
    { apply pure_intro, map_Forall_empty. }
    rewrite big_sepM_insert // IH sep_and -pure_and.
    by rewrite -map_Forall_insert.
  Qed.
  Lemma big_sepM_affinely_pure_2 (φ : K → A → Prop) m :
    <affine> ⌜map_Forall φ m⌝ ⊢@{PROP} ([∗ map] k↦x ∈ m, <affine> ⌜φ k x⌝).
  Proof.
    induction m as [|k x m ? IH] using map_ind.
    { rewrite big_sepM_empty. apply affinely_elim_emp. }
    rewrite big_sepM_insert // -IH.
    by rewrite -persistent_and_sep_1 -affinely_and -pure_and map_Forall_insert.
  Qed.
  (** The general backwards direction requires [BiAffine] to cover the empty case. *)
  Lemma big_sepM_pure `{!BiAffine PROP} (φ : K → A → Prop) m :
    ([∗ map] k↦x ∈ m, ⌜φ k x⌝) ⊣⊢@{PROP} ⌜map_Forall φ m⌝.
  Proof.
    apply (anti_symm (⊢)); first by apply big_sepM_pure_1.
    rewrite -(affine_affinely ⌜_⌝).
    rewrite big_sepM_affinely_pure_2. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepM_persistently `{!BiAffine PROP} Φ m :
    (<pers> ([∗ map] k↦x ∈ m, Φ k x)) ⊣⊢ ([∗ map] k↦x ∈ m, <pers> (Φ k x)).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_intro Φ m :
    □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x) ⊢ [∗ map] k↦x ∈ m, Φ k x.
  Proof.
    revert Φ. induction m as [|i x m ? IH] using map_ind=> Φ.
    { by rewrite (affine (□ _)) big_sepM_empty. }
    rewrite big_sepM_insert // intuitionistically_sep_dup. f_equiv.
    - rewrite (forall_elim i) (forall_elim x) lookup_insert.
      by rewrite pure_True // True_impl intuitionistically_elim.
    - rewrite -IH. f_equiv. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_True // True_impl.
  Qed.

  Lemma big_sepM_forall `{!BiAffine PROP} Φ m :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepM_lookup. }
    revert Φ HΦ. induction m as [|i x m ? IH] using map_ind=> Φ HΦ.
    { rewrite big_sepM_empty. apply: affine. }
    rewrite big_sepM_insert // -persistent_and_sep_1. apply and_intro.
    - rewrite (forall_elim i) (forall_elim x) lookup_insert.
      by rewrite pure_True // True_impl.
    - rewrite -IH. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_True // True_impl.
  Qed.

  Lemma big_sepM_impl Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ map] k↦x ∈ m, Ψ k x.
  Proof.
    apply entails_wand, wand_intro_l. rewrite big_sepM_intro -big_sepM_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepM_wand Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    ([∗ map] k↦x ∈ m, Φ k x -∗ Ψ k x) -∗
    [∗ map] k↦x ∈ m, Ψ k x.
  Proof.
    apply entails_wand, wand_intro_r. rewrite -big_sepM_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepM_dup P `{!Affine P} m :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ map] k↦x ∈ m, P.
  Proof.
    apply entails_wand, wand_intro_l. induction m as [|i x m ? IH] using map_ind.
    { apply: big_sepM_empty'. }
    rewrite !big_sepM_insert //.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepM_lookup_acc_impl {Φ m} i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) -∗
    (* We obtain [Φ] for [x] *)
    Φ i x ∗
    (* We reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ k y, ⌜ m !! k = Some y ⌝ → ⌜ k ≠ i ⌝ → Φ k y -∗ Ψ k y) -∗
      Ψ i x -∗
      [∗ map] k↦y ∈ m, Ψ k y.
  Proof.
    intros. rewrite big_sepM_delete //. apply entails_wand, sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepM_delete Ψ m i x) //. apply sep_mono_r.
    eapply wand_apply; [apply wand_entails, big_sepM_impl|apply sep_mono_r].
    f_equiv; f_equiv=> k; f_equiv=> y.
    rewrite impl_curry -pure_and lookup_delete_Some.
    do 2 f_equiv. intros ?; naive_solver.
  Qed.

  Lemma big_sepM_later `{!BiAffine PROP} Φ m :
    ▷ ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷ Φ k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_sepM_later_2 Φ m :
    ([∗ map] k↦x ∈ m, ▷ Φ k x) ⊢ ▷ [∗ map] k↦x ∈ m, Φ k x.
  Proof. by rewrite big_opM_commute. Qed.

  Lemma big_sepM_laterN `{!BiAffine PROP} Φ n m :
    ▷^n ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷^n Φ k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_sepM_laterN_2 Φ n m :
    ([∗ map] k↦x ∈ m, ▷^n Φ k x) ⊢ ▷^n [∗ map] k↦x ∈ m, Φ k x.
  Proof. by rewrite big_opM_commute. Qed.

  Lemma big_sepM_map_to_list Φ m :
    ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ [∗ list] xk ∈ map_to_list m, Φ (xk.1) (xk.2).
  Proof. apply big_opM_map_to_list. Qed.
  Lemma big_sepM_list_to_map Φ l :
    NoDup l.*1 →
    ([∗ map] k↦x ∈ list_to_map l, Φ k x) ⊣⊢ [∗ list] xk ∈ l, Φ (xk.1) (xk.2).
  Proof. apply big_opM_list_to_map. Qed.

End sep_map.

(* Some lemmas depend on the generalized versions of the above ones. *)
Lemma big_sepM_sep_zip_with `{Countable K} {A B C}
    (f : A → B → C) (g1 : C → A) (g2 : C → B)
    (Φ1 : K → A → PROP) (Φ2 : K → B → PROP) m1 m2 :
  (∀ x y, g1 (f x y) = x) →
  (∀ x y, g2 (f x y) = y) →
  (∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
  ([∗ map] k↦xy ∈ map_zip_with f m1 m2, Φ1 k (g1 xy) ∗ Φ2 k (g2 xy)) ⊣⊢
  ([∗ map] k↦x ∈ m1, Φ1 k x) ∗ ([∗ map] k↦y ∈ m2, Φ2 k y).
Proof. apply big_opM_sep_zip_with. Qed.

Lemma big_sepM_sep_zip `{Countable K} {A B}
    (Φ1 : K → A → PROP) (Φ2 : K → B → PROP) m1 m2 :
  (∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
  ([∗ map] k↦xy ∈ map_zip m1 m2, Φ1 k xy.1 ∗ Φ2 k xy.2) ⊣⊢
  ([∗ map] k↦x ∈ m1, Φ1 k x) ∗ ([∗ map] k↦y ∈ m2, Φ2 k y).
Proof. apply big_opM_sep_zip. Qed.

Lemma big_sepM_impl_strong `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
  ([∗ map] k↦x ∈ m1, Φ k x) ⊢
  □ (∀ (k : K) (y : B),
    (if m1 !! k is Some x then Φ k x else emp) -∗
    ⌜m2 !! k = Some y⌝ →
    Ψ k y) -∗
  ([∗ map] k↦y ∈ m2, Ψ k y) ∗
  ([∗ map] k↦x ∈ filter (λ '(k, _), m2 !! k = None) m1, Φ k x).
Proof.
  apply wand_intro_r.
  revert m1. induction m2 as [|i y m ? IH] using map_ind=> m1.
  { rewrite big_sepM_empty left_id sep_elim_l.
    rewrite map_filter_id //. }
  rewrite big_sepM_insert; last done.
  rewrite intuitionistically_sep_dup.
  rewrite assoc. rewrite (comm _ _ (□ _))%I.
  rewrite {1}intuitionistically_elim {1}(forall_elim i) {1}(forall_elim y).
  rewrite lookup_insert pure_True // left_id.
  destruct (m1 !! i) as [x|] eqn:Hx.
  - rewrite big_sepM_delete; last done.
    rewrite assoc assoc wand_elim_l -2!assoc. apply sep_mono_r.
    assert (filter (λ '(k, _), <[i:=y]> m !! k = None) m1
          = filter (λ '(k, _), m !! k = None) (delete i m1)) as ->.
    { apply map_filter_strong_ext_1=> k z.
      rewrite lookup_insert_None lookup_delete_Some. naive_solver. }
    rewrite -IH. do 2 f_equiv. f_equiv=> k. f_equiv=> z.
    apply wand_intro_r. apply impl_intro_l, pure_elim_l=> ?.
    assert (i ≠ k) by congruence.
    rewrite lookup_insert_ne // pure_True // left_id.
    rewrite lookup_delete_ne // wand_elim_l //.
  - rewrite left_id -assoc. apply sep_mono_r.
    assert (filter (λ '(k, _), <[i:=y]> m !! k = None) m1
          = filter (λ '(k, _), m !! k = None) m1) as ->.
    { apply map_filter_strong_ext_1=> k z.
      rewrite lookup_insert_None. naive_solver. }
    rewrite -IH. do 2 f_equiv. f_equiv=> k. f_equiv=> z.
    apply wand_intro_r. apply impl_intro_l, pure_elim_l=> ?.
    rewrite lookup_insert_ne; last congruence.
    rewrite pure_True // left_id // wand_elim_l //.
Qed.

Lemma big_sepM_impl_dom_subseteq `{Countable K} {A B}
    (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
  dom m2 ⊆ dom m1 →
  ([∗ map] k↦x ∈ m1, Φ k x) -∗
  □ (∀ (k : K) (x : A) (y : B),
      ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
      Φ k x -∗ Ψ k y) -∗
  ([∗ map] k↦y ∈ m2, Ψ k y) ∗
  ([∗ map] k↦x ∈ filter (λ '(k, _), m2 !! k = None) m1, Φ k x).
Proof.
  intros. apply entails_wand. rewrite big_sepM_impl_strong.
  apply wand_mono; last done. f_equiv. f_equiv=> k. apply forall_intro=> y.
  apply wand_intro_r, impl_intro_l, pure_elim_l=> Hlm2.
  destruct (m1 !! k) as [x|] eqn:Hlm1.
  - rewrite (forall_elim x) (forall_elim y).
    do 2 rewrite pure_True // left_id //. apply wand_elim_l.
  - apply elem_of_dom_2 in Hlm2. apply not_elem_of_dom in Hlm1.
    set_solver.
Qed.

Section and_map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  (** The lemmas [big_andM_mono], [big_andM_ne] and [big_andM_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_andM_mono Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊢ Ψ k x) →
    ([∧ map] k ↦ x ∈ m, Φ k x) ⊢ [∧ map] k ↦ x ∈ m, Ψ k x.
  Proof. apply big_opM_gen_proper; apply _ || auto. Qed.
  Lemma big_andM_ne Φ Ψ m n :
    (∀ k x, m !! k = Some x → Φ k x ≡{n}≡ Ψ k x) →
    ([∧ map] k ↦ x ∈ m, Φ k x)%I ≡{n}≡ ([∧ map] k ↦ x ∈ m, Ψ k x)%I.
  Proof. apply big_opM_ne. Qed.
  Lemma big_andM_proper Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([∧ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∧ map] k ↦ x ∈ m, Ψ k x).
  Proof. apply big_opM_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opM] instances. *)
  Global Instance big_andM_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opM (@bi_and PROP) (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_andM_mono; intros; apply Hf. Qed.

  Global Instance big_andM_empty_persistent Φ :
    Persistent ([∧ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_empty. apply _. Qed.
  Lemma big_andM_persistent Φ m :
    (∀ k x, m !! k = Some x → Persistent (Φ k x)) →
    Persistent ([∧ map] k↦x ∈ m, Φ k x).
  Proof. apply big_opM_closed; apply _. Qed.
  Global Instance big_andM_persistent' Φ m :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∧ map] k↦x ∈ m, Φ k x).
  Proof. intros; apply big_andM_persistent, _. Qed.

  Global Instance big_andM_empty_timeless Φ :
    Timeless ([∧ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite big_opM_empty. apply _. Qed.
  Lemma big_andM_timeless Φ m :
    (∀ k x, m !! k = Some x → Timeless (Φ k x)) →
    Timeless ([∧ map] k↦x ∈ m, Φ k x).
  Proof. apply big_opM_closed; apply _. Qed.
  Global Instance big_andM_timeless' Φ m :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∧ map] k↦x ∈ m, Φ k x).
  Proof. intros; apply big_andM_timeless, _. Qed.

  Lemma big_andM_subseteq Φ m1 m2 :
    m2 ⊆ m1 → ([∧ map] k ↦ x ∈ m1, Φ k x) ⊢ [∧ map] k ↦ x ∈ m2, Φ k x.
  Proof.
    intros ?. rewrite -(map_difference_union m2 m1) //.
    rewrite big_opM_union; last by apply map_disjoint_difference_r.
    by rewrite and_elim_l.
  Qed.

  Lemma big_andM_empty Φ : ([∧ map] k↦x ∈ ∅, Φ k x) ⊣⊢ True.
  Proof. by rewrite big_opM_empty. Qed.
  Lemma big_andM_empty' P Φ : P ⊢ [∧ map] k↦x ∈ ∅, Φ k x.
  Proof. rewrite big_andM_empty. apply: True_intro. Qed.

  Lemma big_andM_insert Φ m i x :
    m !! i = None →
    ([∧ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∧ [∧ map] k↦y ∈ m, Φ k y.
  Proof. apply big_opM_insert. Qed.

  Lemma big_andM_delete Φ m i x :
    m !! i = Some x →
    ([∧ map] k↦y ∈ m, Φ k y) ⊣⊢ Φ i x ∧ [∧ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_delete. Qed.

  Lemma big_andM_insert_delete Φ m i x :
    ([∧ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∧ [∧ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_insert_delete. Qed.

  Lemma big_andM_insert_2 Φ m i x :
    Φ i x ∧ ([∧ map] k↦y ∈ m, Φ k y) ⊢ [∧ map] k↦y ∈ <[i:=x]> m, Φ k y.
  Proof.
    rewrite big_andM_insert_delete.
    destruct (m !! i) eqn:Hi; [ | by rewrite delete_notin ].
    rewrite big_andM_delete //. apply and_mono_r, and_elim_r.
  Qed.

  Lemma big_andM_lookup Φ m i x :
    m !! i = Some x → ([∧ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
  Proof.
    intros. rewrite -(insert_id m i x) // big_andM_insert_delete. apply and_elim_l.
  Qed.

  Lemma big_andM_lookup_dom (Φ : K → PROP) m i :
    is_Some (m !! i) → ([∧ map] k↦_ ∈ m, Φ k) ⊢ Φ i.
  Proof. intros [x ?]. by eapply (big_andM_lookup (λ i x, Φ i)). Qed.

  Lemma big_andM_singleton Φ i x : ([∧ map] k↦y ∈ {[i:=x]}, Φ k y) ⊣⊢ Φ i x.
  Proof. by rewrite big_opM_singleton. Qed.

  Lemma big_andM_fmap {B} (f : A → B) (Φ : K → B → PROP) m :
    ([∧ map] k↦y ∈ f <$> m, Φ k y) ⊣⊢ ([∧ map] k↦y ∈ m, Φ k (f y)).
  Proof. by rewrite big_opM_fmap. Qed.

  Lemma big_andM_omap {B} (f : A → option B) (Φ : K → B → PROP) m :
    ([∧ map] k↦y ∈ omap f m, Φ k y) ⊣⊢ ([∧ map] k↦y ∈ m, from_option (Φ k) True (f y)).
  Proof. by rewrite big_opM_omap. Qed.

  Lemma big_andM_fn_insert {B} (Ψ : K → A → B → PROP) (f : K → B) m i x b :
    m !! i = None →
       ([∧ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
    ⊣⊢ (Ψ i x b ∧ [∧ map] k↦y ∈ m, Ψ k y (f k)).
  Proof. apply big_opM_fn_insert. Qed.

  Lemma big_andM_fn_insert' (Φ : K → PROP) m i x P :
    m !! i = None →
    ([∧ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∧ [∧ map] k↦y ∈ m, Φ k).
  Proof. apply big_opM_fn_insert'. Qed.

  Lemma big_andM_filter' (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} Φ m :
    ([∧ map] k ↦ x ∈ filter φ m, Φ k x) ⊣⊢
    ([∧ map] k ↦ x ∈ m, if decide (φ (k, x)) then Φ k x else True).
  Proof. apply: big_opM_filter'. Qed.

  Lemma big_andM_filter (φ : K * A → Prop) `{∀ kx, Decision (φ kx)} Φ m :
    ([∧ map] k ↦ x ∈ filter φ m, Φ k x) ⊣⊢
    ([∧ map] k ↦ x ∈ m, ⌜φ (k, x)⌝ → Φ k x).
  Proof. setoid_rewrite <-decide_bi_True. apply big_andM_filter'. Qed.

  Lemma big_andM_union Φ m1 m2 :
    m1 ##ₘ m2 →
    ([∧ map] k↦y ∈ m1 ∪ m2, Φ k y)
    ⊣⊢ ([∧ map] k↦y ∈ m1, Φ k y) ∧ ([∧ map] k↦y ∈ m2, Φ k y).
  Proof. apply big_opM_union. Qed.

  Lemma big_andM_and Φ Ψ m :
    ([∧ map] k↦x ∈ m, Φ k x ∧ Ψ k x)
    ⊣⊢ ([∧ map] k↦x ∈ m, Φ k x) ∧ ([∧ map] k↦x ∈ m, Ψ k x).
  Proof. apply big_opM_op. Qed.

  Lemma big_andM_persistently Φ m :
    <pers> ([∧ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∧ map] k↦x ∈ m, <pers> (Φ k x)).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_andM_intro Φ m :
    (∀ k x, ⌜m !! k = Some x⌝ → Φ k x) ⊢ [∧ map] k↦x ∈ m, Φ k x.
  Proof.
    revert Φ. induction m as [|i x m ? IH] using map_ind=> Φ.
    { rewrite big_andM_empty. apply: True_intro. }
    rewrite big_andM_insert //. apply and_intro.
    - rewrite (forall_elim i) (forall_elim x) lookup_insert.
      by rewrite pure_True // True_impl.
    - rewrite -IH. apply forall_intro=> k. apply forall_intro=> x'.
      rewrite (forall_elim k) (forall_elim x').
      apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_True // True_impl.
  Qed.

  Lemma big_andM_forall Φ m :
    ([∧ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x).
  Proof.
    intros. apply (anti_symm _); [| by rewrite -big_andM_intro].
    apply forall_intro=> k; apply forall_intro=> x.
    apply impl_intro_l, pure_elim_l=> ?; by apply: big_andM_lookup.
  Qed.

  Lemma big_andM_impl Φ Ψ m :
    ([∧ map] k↦x ∈ m, Φ k x) ∧
    (∀ k x, ⌜m !! k = Some x⌝ → Φ k x → Ψ k x) ⊢
    [∧ map] k↦x ∈ m, Ψ k x.
  Proof.
    rewrite -big_andM_forall -big_andM_and.
    by setoid_rewrite bi.impl_elim_r.
  Qed.

  Lemma big_andM_pure_1 (φ : K → A → Prop) m :
    ([∧ map] k↦x ∈ m, ⌜φ k x⌝) ⊢@{PROP} ⌜map_Forall φ m⌝.
  Proof.
    induction m as [|k x m ? IH] using map_ind.
    { apply pure_intro, map_Forall_empty. }
    rewrite big_andM_insert // IH -pure_and.
    by rewrite -map_Forall_insert.
  Qed.

  Lemma big_andM_pure_2 (φ : K → A → Prop) m :
    ⌜map_Forall φ m⌝ ⊢@{PROP} ([∧ map] k↦x ∈ m, ⌜φ k x⌝).
  Proof.
    rewrite big_andM_forall pure_forall_1. f_equiv=>k.
    rewrite pure_forall_1. f_equiv=>x. apply pure_impl_1.
  Qed.

  Lemma big_andM_pure (φ : K → A → Prop) m :
    ([∧ map] k↦x ∈ m, ⌜φ k x⌝) ⊣⊢@{PROP} ⌜map_Forall φ m⌝.
  Proof.
    apply (anti_symm (⊢)); [ by apply big_andM_pure_1 | by apply big_andM_pure_2].
  Qed.

  Lemma big_andM_later Φ m :
    ▷ ([∧ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∧ map] k↦x ∈ m, ▷ Φ k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_andM_laterN Φ n m :
    ▷^n ([∧ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∧ map] k↦x ∈ m, ▷^n Φ k x).
  Proof. apply (big_opM_commute _). Qed.
End and_map.

(** ** Big ops over two maps *)
Lemma big_sepM2_alt `{Countable K} {A B} (Φ : K → A → B → PROP) m1 m2 :
  ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2) ⊣⊢
  ⌜ dom m1 = dom m2 ⌝ ∧ [∗ map] k ↦ xy ∈ map_zip m1 m2, Φ k xy.1 xy.2.
Proof. by rewrite big_sepM2_unseal. Qed.

Section map2.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : K → A → B → PROP.

  Lemma big_sepM2_alt_lookup (Φ : K → A → B → PROP) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2) ⊣⊢
    ⌜ ∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k) ⌝ ∧
    [∗ map] k ↦ xy ∈ map_zip m1 m2, Φ k xy.1 xy.2.
  Proof. rewrite big_sepM2_alt set_eq. by setoid_rewrite elem_of_dom. Qed.

  Lemma big_sepM2_lookup_iff Φ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2) ⊢
    ⌜ ∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k) ⌝.
  Proof. by rewrite big_sepM2_alt_lookup and_elim_l. Qed.

  Lemma big_sepM2_dom Φ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2) ⊢
    ⌜ dom m1 = dom m2 ⌝.
  Proof. by rewrite big_sepM2_alt and_elim_l. Qed.

  Lemma big_sepM2_flip Φ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m2; m1, Φ k y2 y1) ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1; m2, Φ k y1 y2).
  Proof.
    rewrite !big_sepM2_alt. apply and_proper; [apply pure_proper; naive_solver |].
    rewrite -map_zip_with_flip map_zip_with_map_zip big_sepM_fmap.
    apply big_sepM_proper. by intros k [b a].
  Qed.

  Lemma big_sepM2_empty Φ : ([∗ map] k↦y1;y2 ∈ ∅; ∅, Φ k y1 y2) ⊣⊢ emp.
  Proof.
    rewrite big_sepM2_alt map_zip_with_empty big_sepM_empty pure_True ?left_id //.
  Qed.
  Lemma big_sepM2_empty' P `{!Affine P} Φ : P ⊢ [∗ map] k↦y1;y2 ∈ ∅;∅, Φ k y1 y2.
  Proof. rewrite big_sepM2_empty. apply: affine. Qed.

  Lemma big_sepM2_empty_l m1 Φ : ([∗ map] k↦y1;y2 ∈ m1; ∅, Φ k y1 y2) ⊢ ⌜m1 = ∅⌝.
  Proof.
    rewrite big_sepM2_dom dom_empty_L.
    apply pure_mono, dom_empty_iff_L.
  Qed.
  Lemma big_sepM2_empty_r m2 Φ : ([∗ map] k↦y1;y2 ∈ ∅; m2, Φ k y1 y2) ⊢ ⌜m2 = ∅⌝.
  Proof.
    rewrite big_sepM2_dom dom_empty_L.
    apply pure_mono=>?. eapply dom_empty_iff_L. eauto.
  Qed.

  Lemma big_sepM2_insert Φ m1 m2 i x1 x2 :
    m1 !! i = None → m2 !! i = None →
    ([∗ map] k↦y1;y2 ∈ <[i:=x1]>m1; <[i:=x2]>m2, Φ k y1 y2)
    ⊣⊢ Φ i x1 x2 ∗ [∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2.
  Proof.
    intros Hm1 Hm2. rewrite !big_sepM2_alt -map_insert_zip_with.
    rewrite big_sepM_insert;
      last by rewrite map_lookup_zip_with Hm1.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite sep_assoc (sep_comm _ (Φ _ _ _)) -sep_assoc.
    repeat apply sep_proper=>//.
    apply affinely_proper, pure_proper. rewrite !dom_insert_L.
    apply not_elem_of_dom in Hm1. apply not_elem_of_dom in Hm2. set_solver.
  Qed.

  (** The lemmas [big_sepM2_mono], [big_sepM2_ne] and [big_sepM2_proper] are more
  generic than the instances as they also give [mi !! k = Some yi] in the premise. *)
  Lemma big_sepM2_mono Φ Ψ m1 m2 :
    (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → Φ k y1 y2 ⊢ Ψ k y1 y2) →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ [∗ map] k ↦ y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    intros Hm1m2. rewrite !big_sepM2_alt.
    apply and_mono_r, big_sepM_mono.
    intros k [x1 x2]. rewrite map_lookup_zip_with.
    specialize (Hm1m2 k x1 x2).
    destruct (m1 !! k) as [y1|]; last done.
    destruct (m2 !! k) as [y2|]; simpl; last done.
    intros ?; simplify_eq. by apply Hm1m2.
  Qed.
  Lemma big_sepM2_ne Φ Ψ m1 m2 n :
    (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → Φ k y1 y2 ≡{n}≡ Ψ k y1 y2) →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2)%I ≡{n}≡ ([∗ map] k ↦ y1;y2 ∈ m1;m2, Ψ k y1 y2)%I.
  Proof.
    intros Hm1m2. rewrite !big_sepM2_alt.
    f_equiv. apply big_sepM_ne=> k [x1 x2]. rewrite map_lookup_zip_with.
    specialize (Hm1m2 k x1 x2).
    destruct (m1 !! k) as [y1|]; last done.
    destruct (m2 !! k) as [y2|]; simpl; last done.
    intros ?; simplify_eq. by apply Hm1m2.
  Qed.
  Lemma big_sepM2_proper Φ Ψ m1 m2 :
    (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → Φ k y1 y2 ⊣⊢ Ψ k y1 y2) →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢ [∗ map] k ↦ y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    intros; apply (anti_symm _);
      apply big_sepM2_mono; auto using equiv_entails_1_1, equiv_entails_1_2.
  Qed.
  Lemma big_sepM2_proper_2 `{!Equiv A, !Equiv B} Φ Ψ m1 m2 m1' m2' :
    m1 ≡ m1' → m2 ≡ m2' →
    (∀ k y1 y1' y2 y2',
      m1 !! k = Some y1 → m1' !! k = Some y1' → y1 ≡ y1' →
      m2 !! k = Some y2 → m2' !! k = Some y2' → y2 ≡ y2' →
      Φ k y1 y2 ⊣⊢ Ψ k y1' y2') →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2) ⊣⊢ [∗ map] k ↦ y1;y2 ∈ m1';m2', Ψ k y1 y2.
  Proof.
    intros Hm1 Hm2 Hf. rewrite !big_sepM2_alt. f_equiv.
    { by rewrite Hm1 Hm2. }
    apply big_opM_proper_2; [by f_equiv|].
    intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some
      (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some [??]; naive_solver.
  Qed.

  Global Instance big_sepM2_ne' n :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (dist n)))
      ==> (=) ==> (=) ==> (dist n))
           (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B)).
  Proof. intros f g Hf m1 ? <- m2 ? <-. apply big_sepM2_ne; intros; apply Hf. Qed.
  Global Instance big_sepM2_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊢)))
      ==> (=) ==> (=) ==> (⊢)) (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B)).
  Proof. intros f g Hf m1 ? <- m2 ? <-. apply big_sepM2_mono; intros; apply Hf. Qed.
  Global Instance big_sepM2_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (⊣⊢)))
      ==> (=) ==> (=) ==> (⊣⊢)) (big_sepM2 (PROP:=PROP) (K:=K) (A:=A) (B:=B)).
  Proof. intros f g Hf m1 ? <- m2 ? <-. apply big_sepM2_proper; intros; apply Hf. Qed.

  (** Shows that some property [P] is closed under [big_sepM2]. Examples of [P]
  are [Persistent], [Affine], [Timeless]. *)
  Lemma big_sepM2_closed (P : PROP → Prop) Φ m1 m2 :
    Proper ((≡) ==> iff) P →
    P emp%I → P False%I →
    (∀ Q1 Q2, P Q1 → P Q2 → P (Q1 ∗ Q2)%I) →
    (∀ k x1 x2, m1 !! k = Some x1 → m2 !! k = Some x2 → P (Φ k x1 x2)) →
    P ([∗ map] k↦x1;x2 ∈ m1; m2, Φ k x1 x2)%I.
  Proof.
    intros ??? Hsep HΦ.
    rewrite big_sepM2_alt. destruct (decide (dom m1 = dom m2)).
    - rewrite pure_True // left_id. apply big_opM_closed; [done..|].
      intros k [x1 x2] Hk. rewrite map_lookup_zip_with in Hk.
      simplify_option_eq; auto.
    - by rewrite pure_False // left_absorb.
  Qed.

  Global Instance big_sepM2_empty_persistent Φ :
    Persistent ([∗ map] k↦y1;y2 ∈ ∅; ∅, Φ k y1 y2).
  Proof. rewrite big_sepM2_empty. apply _. Qed.
  Lemma big_sepM2_persistent Φ m1 m2 :
    (∀ k x1 x2, m1 !! k = Some x1 → m2 !! k = Some x2 → Persistent (Φ k x1 x2)) →
    Persistent ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
  Proof. apply big_sepM2_closed; apply _. Qed.
  Global Instance big_sepM2_persistent' Φ m1 m2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    Persistent ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
  Proof. intros; apply big_sepM2_persistent, _. Qed.

  Global Instance big_sepM2_empty_affine Φ :
    Affine ([∗ map] k↦y1;y2 ∈ ∅; ∅, Φ k y1 y2).
  Proof. rewrite big_sepM2_empty. apply _. Qed.
  Lemma big_sepM2_affine Φ m1 m2 :
    (∀ k x1 x2, m1 !! k = Some x1 → m2 !! k = Some x2 → Affine (Φ k x1 x2)) →
    Affine ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
  Proof. apply big_sepM2_closed; apply _. Qed.
  Global Instance big_sepM2_affine' Φ m1 m2 :
    (∀ k x1 x2, Affine (Φ k x1 x2)) →
    Affine ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2).
  Proof. intros; apply big_sepM2_affine, _. Qed.

  Global Instance big_sepM2_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ map] k↦x1;x2 ∈ ∅;∅, Φ k x1 x2).
  Proof. rewrite big_sepM2_alt map_zip_with_empty. apply _. Qed.
  Lemma big_sepM2_timeless `{!Timeless (emp%I : PROP)} Φ m1 m2 :
    (∀ k x1 x2, m1 !! k = Some x1 → m2 !! k = Some x2 → Timeless (Φ k x1 x2)) →
    Timeless ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2).
  Proof. apply big_sepM2_closed; apply _. Qed.
  Global Instance big_sepM2_timeless' `{!Timeless (emp%I : PROP)} Φ m1 m2 :
    (∀ k x1 x2, Timeless (Φ k x1 x2)) →
    Timeless ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2).
  Proof. intros; apply big_sepM2_timeless, _. Qed.

  Lemma big_sepM2_delete Φ m1 m2 i x1 x2 :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦x;y ∈ m1;m2, Φ k x y) ⊣⊢
      Φ i x1 x2 ∗ [∗ map] k↦x;y ∈ delete i m1;delete i m2, Φ k x y.
  Proof.
    rewrite !big_sepM2_alt=> Hx1 Hx2.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite sep_assoc (sep_comm  (Φ _ _ _)) -sep_assoc.
    apply sep_proper.
    - apply affinely_proper, pure_proper. rewrite !dom_delete_L.
      apply elem_of_dom_2 in Hx1; apply elem_of_dom_2 in Hx2. set_unfold.
      apply base.forall_proper=> k. destruct (decide (k = i)); naive_solver.
    - rewrite -map_delete_zip_with.
      apply (big_sepM_delete (λ i xx, Φ i xx.1 xx.2) (map_zip m1 m2) i (x1,x2)).
      by rewrite map_lookup_zip_with Hx1 Hx2.
  Qed.
  Lemma big_sepM2_delete_l Φ m1 m2 i x1 :
    m1 !! i = Some x1 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊣⊢ ∃ x2, ⌜m2 !! i = Some x2⌝ ∧
            (Φ i x1 x2 ∗ [∗ map] k↦y1;y2 ∈ delete i m1;delete i m2, Φ k y1 y2).
  Proof.
    intros Hm1. apply (anti_symm _).
    - rewrite big_sepM2_alt_lookup. apply pure_elim_l=> Hm.
      assert (is_Some (m2 !! i)) as [x2 Hm2].
      { apply Hm. by econstructor. }
      rewrite -(exist_intro x2).
      rewrite big_sepM2_alt_lookup (big_sepM_delete _ _ i (x1,x2)) /=;
        last by rewrite map_lookup_zip_with Hm1 Hm2.
      rewrite pure_True // left_id.
      f_equiv. apply and_intro.
      + apply pure_intro=> k. by rewrite !lookup_delete_is_Some Hm.
      + by rewrite -map_delete_zip_with.
    - apply exist_elim=> x2. apply pure_elim_l=> ?.
      by rewrite -big_sepM2_delete.
  Qed.
  Lemma big_sepM2_delete_r Φ m1 m2 i x2 :
    m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊣⊢ ∃ x1, ⌜m1 !! i = Some x1⌝ ∧
            (Φ i x1 x2 ∗ [∗ map] k↦y1;y2 ∈ delete i m1;delete i m2, Φ k y1 y2).
  Proof.
    intros Hm2. apply (anti_symm _).
    - rewrite big_sepM2_alt_lookup.
      apply pure_elim_l=> Hm.
      assert (is_Some (m1 !! i)) as [x1 Hm1].
      { apply Hm. by econstructor. }
      rewrite -(exist_intro x1).
      rewrite big_sepM2_alt_lookup (big_sepM_delete _ _ i (x1,x2)) /=;
        last by rewrite map_lookup_zip_with Hm1 Hm2.
      rewrite pure_True // left_id.
      f_equiv. apply and_intro.
      + apply pure_intro=> k. by rewrite !lookup_delete_is_Some Hm.
      + by rewrite -map_delete_zip_with.
    - apply exist_elim=> x1. apply pure_elim_l=> ?.
      by rewrite -big_sepM2_delete.
  Qed.

  Lemma big_sepM2_insert_delete Φ m1 m2 i x1 x2 :
    ([∗ map] k↦y1;y2 ∈ <[i:=x1]>m1; <[i:=x2]>m2, Φ k y1 y2)
    ⊣⊢ Φ i x1 x2 ∗ [∗ map] k↦y1;y2 ∈ delete i m1;delete i m2, Φ k y1 y2.
  Proof.
    rewrite -(insert_delete_insert m1) -(insert_delete_insert m2).
    apply big_sepM2_insert; by rewrite lookup_delete.
  Qed.

  Lemma big_sepM2_insert_acc Φ m1 m2 i x1 x2 :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (∀ x1' x2', Φ i x1' x2' -∗
        ([∗ map] k↦y1;y2 ∈ <[i:=x1']>m1;<[i:=x2']>m2, Φ k y1 y2)).
  Proof.
    intros ??. rewrite {1}big_sepM2_delete //. apply sep_mono; [done|].
    apply forall_intro=> x1'. apply forall_intro=> x2'.
    rewrite -(insert_delete_insert m1) -(insert_delete_insert m2)
      big_sepM2_insert ?lookup_delete //.
    by apply wand_intro_l.
  Qed.

  Lemma big_sepM2_insert_2 Φ m1 m2 i x1 x2
    `{!TCOr (∀ x y, Affine (Φ i x y)) (Absorbing (Φ i x1 x2))} :
    Φ i x1 x2 -∗
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    ([∗ map] k↦y1;y2 ∈ <[i:=x1]>m1; <[i:=x2]>m2, Φ k y1 y2).
  Proof.
    rewrite !big_sepM2_alt.
    assert (TCOr (∀ x, Affine (Φ i x.1 x.2)) (Absorbing (Φ i x1 x2))).
    { destruct select (TCOr _ _); apply _. }
    apply entails_wand, wand_intro_r.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite (sep_comm  (Φ _ _ _)) -sep_assoc. apply sep_mono.
    { apply affinely_mono, pure_mono. rewrite !dom_insert_L. set_solver. }
    rewrite (big_sepM_insert_2 (λ k xx, Φ k xx.1 xx.2) (map_zip m1 m2) i (x1, x2)).
    rewrite map_insert_zip_with. apply wand_elim_r.
  Qed.

  Lemma big_sepM2_lookup_acc Φ m1 m2 i x1 x2 :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ (Φ i x1 x2 -∗ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)).
  Proof.
    intros Hm1 Hm2. etrans; first apply big_sepM2_insert_acc=>//.
    apply sep_mono_r. rewrite (forall_elim x1) (forall_elim x2).
    rewrite !insert_id //.
 Qed.

  Lemma big_sepM2_lookup Φ m1 m2 i x1 x2
    `{!TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (Absorbing (Φ i x1 x2))} :
    m1 !! i = Some x1 → m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ Φ i x1 x2.
  Proof.
    intros Hx1 Hx2. destruct select (TCOr _ _).
    - rewrite big_sepM2_delete // sep_elim_l //.
    - rewrite big_sepM2_lookup_acc // sep_elim_l //.
  Qed.
  Lemma big_sepM2_lookup_l Φ m1 m2 i x1
    `{!TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (∀ x2, Absorbing (Φ i x1 x2))} :
    m1 !! i = Some x1 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊢ ∃ x2, ⌜m2 !! i = Some x2⌝ ∧ Φ i x1 x2.
  Proof.
    intros Hm1. rewrite big_sepM2_delete_l //.
    f_equiv=> x2. destruct select (TCOr _ _); by rewrite sep_elim_l.
  Qed.
  Lemma big_sepM2_lookup_r Φ m1 m2 i x2
    `{!TCOr (∀ j y1 y2, Affine (Φ j y1 y2)) (∀ x1, Absorbing (Φ i x1 x2))} :
    m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊢ ∃ x1, ⌜m1 !! i = Some x1⌝ ∧ Φ i x1 x2.
  Proof.
    intros Hm2. rewrite big_sepM2_delete_r //.
    f_equiv=> x1. destruct select (TCOr _ _); by rewrite sep_elim_l.
  Qed.

  Lemma big_sepM2_singleton Φ i x1 x2 :
    ([∗ map] k↦y1;y2 ∈ {[ i := x1 ]}; {[ i := x2 ]}, Φ k y1 y2) ⊣⊢ Φ i x1 x2.
  Proof.
    rewrite big_sepM2_alt.
    rewrite map_zip_with_singleton big_sepM_singleton.
    apply (anti_symm _).
    - apply and_elim_r.
    - rewrite <- (left_id True%I (∧)%I (Φ i x1 x2)).
      apply and_mono=> //. apply pure_mono=> _. set_solver.
  Qed.

  Lemma big_sepM2_fst_snd Φ m :
    ([∗ map] k↦y1;y2 ∈ fst <$> m; snd <$> m, Φ k y1 y2) ⊣⊢
    [∗ map] k ↦ xy ∈ m, Φ k (xy.1) (xy.2).
  Proof.
    rewrite big_sepM2_alt. rewrite !dom_fmap_L.
    by rewrite pure_True // True_and map_zip_fst_snd.
  Qed.

  Lemma big_sepM2_fmap {A' B'} (f : A → A') (g : B → B') (Φ : K → A' → B' → PROP) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ f <$> m1; g <$> m2, Φ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k (f y1) (g y2)).
  Proof.
    rewrite !big_sepM2_alt. by rewrite map_fmap_zip !dom_fmap_L big_sepM_fmap.
  Qed.

  Lemma big_sepM2_fmap_l {A'} (f : A → A') (Φ : K → A' → B → PROP) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ f <$> m1; m2, Φ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k (f y1) y2).
  Proof. rewrite -{1}(map_fmap_id m2). apply big_sepM2_fmap. Qed.

  Lemma big_sepM2_fmap_r {B'} (g : B → B') (Φ : K → A → B' → PROP) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1; g <$> m2, Φ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 (g y2)).
  Proof. rewrite -{1}(map_fmap_id m1). apply big_sepM2_fmap. Qed.

  Lemma big_sepM2_sep Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∗ Ψ k y1 y2)
    ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ∗ ([∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2).
  Proof.
    rewrite !big_sepM2_alt.
    rewrite -{1}(idemp bi_and ⌜ dom m1 = dom m2 ⌝%I).
    rewrite -assoc.
    rewrite !persistent_and_affinely_sep_l /=.
    rewrite -assoc. apply sep_proper=>//.
    rewrite assoc (comm _ _ (<affine> _)%I) -assoc.
    apply sep_proper=>//. apply big_sepM_sep.
  Qed.

  Lemma big_sepM2_sep_2 Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    ([∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2) -∗
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∗ Ψ k y1 y2).
  Proof. apply entails_wand, wand_intro_r. rewrite big_sepM2_sep //. Qed.

  Lemma big_sepM2_and Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 ∧ Ψ k y1 y2)
    ⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ∧ ([∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2).
  Proof. auto using and_intro, big_sepM2_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepM2_pure_1 (φ : K → A → B → Prop) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, ⌜φ k y1 y2⌝) ⊢@{PROP}
      ⌜∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → φ k y1 y2⌝.
  Proof.
    rewrite big_sepM2_alt.
    rewrite big_sepM_pure_1 -pure_and.
    f_equiv=>-[Hdom Hforall] k y1 y2 Hy1 Hy2.
    eapply (Hforall k (y1, y2)). clear Hforall.
    apply map_lookup_zip_with_Some. naive_solver.
  Qed.
  Lemma big_sepM2_affinely_pure_2 (φ : K → A → B → Prop) m1 m2 :
    (∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
    <affine> ⌜∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → φ k y1 y2⌝ ⊢@{PROP}
      ([∗ map] k↦y1;y2 ∈ m1;m2, <affine> ⌜φ k y1 y2⌝).
  Proof.
    intros Hdom.
    rewrite big_sepM2_alt_lookup.
    rewrite -big_sepM_affinely_pure_2.
    rewrite affinely_and_r -pure_and. f_equiv. f_equiv=>-Hforall.
    split; first done.
    intros k [y1 y2] (? & ? & [= <- <-] & Hy1 & Hy2)%map_lookup_zip_with_Some; simpl.
    by eapply Hforall.
  Qed.
  (** The general backwards direction requires [BiAffine] to cover the empty case. *)
  Lemma big_sepM2_pure `{!BiAffine PROP} (φ : K → A → B → Prop) m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, ⌜φ k y1 y2⌝) ⊣⊢@{PROP}
      ⌜(∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) ∧
       (∀ k y1 y2, m1 !! k = Some y1 → m2 !! k = Some y2 → φ k y1 y2)⌝.
  Proof.
    apply (anti_symm (⊢)).
    { rewrite pure_and. apply and_intro.
      - apply big_sepM2_lookup_iff.
      - apply big_sepM2_pure_1. }
    rewrite -(affine_affinely ⌜_⌝%I).
    rewrite pure_and -affinely_and_r.
    apply pure_elim_l=>Hdom.
    rewrite big_sepM2_affinely_pure_2 //. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepM2_persistently `{!BiAffine PROP} Φ m1 m2 :
    <pers> ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
    ⊣⊢ [∗ map] k↦y1;y2 ∈ m1;m2, <pers> (Φ k y1 y2).
  Proof.
    by rewrite !big_sepM2_alt persistently_and
      persistently_pure big_sepM_persistently.
  Qed.

  Lemma big_sepM2_intro Φ m1 m2 :
    (∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
    □ (∀ k x1 x2, ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ → Φ k x1 x2) ⊢
    [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2.
  Proof.
    intros. rewrite big_sepM2_alt_lookup.
    apply and_intro; [by apply pure_intro|].
    rewrite -big_sepM_intro. f_equiv; f_equiv=> k.
    apply forall_intro=> -[x1 x2]. rewrite (forall_elim x1) (forall_elim x2).
    apply impl_intro_l, pure_elim_l.
    intros (?&?&[= <- <-]&?&?)%map_lookup_zip_with_Some.
    by rewrite !pure_True // !True_impl.
  Qed.

  Lemma big_sepM2_forall `{!BiAffine PROP} Φ m1 m2 :
    (∀ k x1 x2, Persistent (Φ k x1 x2)) →
    ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2) ⊣⊢
      ⌜∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)⌝
      ∧ (∀ k x1 x2, ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ → Φ k x1 x2).
  Proof.
    intros. apply (anti_symm _).
    { apply and_intro; [apply big_sepM2_lookup_iff|].
      apply forall_intro=> k. apply forall_intro=> x1. apply forall_intro=> x2.
      do 2 (apply impl_intro_l; apply pure_elim_l=> ?). by apply: big_sepM2_lookup. }
    apply pure_elim_l=> Hdom. rewrite big_sepM2_alt_lookup.
    apply and_intro; [by apply pure_intro|].
    rewrite big_sepM_forall. f_equiv=> k.
    apply forall_intro=> -[x1 x2]. rewrite (forall_elim x1) (forall_elim x2).
    apply impl_intro_l, pure_elim_l.
    intros (?&?&[= <- <-]&?&?)%map_lookup_zip_with_Some.
    by rewrite !pure_True // !True_impl.
  Qed.

  Lemma big_sepM2_impl Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    □ (∀ k x1 x2,
      ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ → Φ k x1 x2 -∗ Ψ k x1 x2) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    apply entails_wand.
    rewrite -(idemp bi_and (big_sepM2 _ _ _)) {1}big_sepM2_lookup_iff.
    apply pure_elim_l=> ?. rewrite big_sepM2_intro //.
    apply bi.wand_intro_l. rewrite -big_sepM2_sep. by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepM2_wand Φ Ψ m1 m2 :
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2 -∗ Ψ k y1 y2) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    apply entails_wand, wand_intro_r. rewrite -big_sepM2_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepM2_lookup_acc_impl {Φ m1 m2} i x1 x2 :
    m1 !! i = Some x1 →
    m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    (* We obtain [Φ] for [x1] and [x2] *)
    Φ i x1 x2 ∗
    (* We reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ k y1 y2,
        ⌜ m1 !! k = Some y1 ⌝ → ⌜ m2 !! k = Some y2 ⌝ → ⌜ k ≠ i ⌝ →
        Φ k y1 y2 -∗ Ψ k y1 y2) -∗
      Ψ i x1 x2 -∗
      [∗ map] k↦y1;y2 ∈ m1;m2, Ψ k y1 y2.
  Proof.
    intros. rewrite big_sepM2_delete //. apply entails_wand, sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepM2_delete Ψ m1 m2 i) //. apply sep_mono_r.
    eapply wand_apply; [apply wand_entails, big_sepM2_impl|apply sep_mono_r].
    f_equiv; f_equiv=> k; f_equiv=> y1; f_equiv=> y2.
    rewrite !impl_curry -!pure_and !lookup_delete_Some.
    do 2 f_equiv. intros ?; naive_solver.
  Qed.

  Lemma big_sepM2_later_1 `{!BiAffine PROP} Φ m1 m2 :
    (▷ [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2)
    ⊢ ◇ ([∗ map] k↦x1;x2 ∈ m1;m2, ▷ Φ k x1 x2).
  Proof.
    rewrite !big_sepM2_alt later_and (timeless ⌜_⌝).
    rewrite big_sepM_later except_0_and.
    auto using and_mono_r, except_0_intro.
  Qed.
  Lemma big_sepM2_later_2 Φ m1 m2 :
    ([∗ map] k↦x1;x2 ∈ m1;m2, ▷ Φ k x1 x2)
    ⊢ ▷ [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2.
  Proof.
    rewrite !big_sepM2_alt later_and -(later_intro ⌜_⌝).
    apply and_mono_r. by rewrite big_opM_commute.
  Qed.

  Lemma big_sepM2_laterN_2 Φ n m1 m2 :
    ([∗ map] k↦x1;x2 ∈ m1;m2, ▷^n Φ k x1 x2)
    ⊢ ▷^n [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2.
  Proof.
    induction n as [|n IHn]; first done.
    rewrite later_laterN -IHn -big_sepM2_later_2.
    apply big_sepM2_mono. eauto.
  Qed.

  Lemma big_sepM2_sepM (Φ1 : K → A → PROP) (Φ2 : K → B → PROP) m1 m2 :
    (∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ1 k y1 ∗ Φ2 k y2) ⊣⊢
    ([∗ map] k↦y1 ∈ m1, Φ1 k y1) ∗ ([∗ map] k↦y2 ∈ m2, Φ2 k y2).
  Proof.
    intros.
    rewrite -big_sepM_sep_zip // big_sepM2_alt_lookup pure_True // left_id //.
  Qed.
  Lemma big_sepM2_sepM_2 (Φ1 : K → A → PROP) (Φ2 : K → B → PROP) m1 m2 :
    (∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) →
    ([∗ map] k↦y1 ∈ m1, Φ1 k y1) -∗
    ([∗ map] k↦y2 ∈ m2, Φ2 k y2) -∗
    [∗ map] k↦y1;y2 ∈ m1;m2, Φ1 k y1 ∗ Φ2 k y2.
  Proof. intros. apply entails_wand, wand_intro_r. by rewrite big_sepM2_sepM. Qed.

 Lemma big_sepM2_union_inv_l (Φ : K → A → B → PROP) m1 m2 m' :
    m1 ##ₘ m2 →
    ([∗ map] k↦x;y ∈ (m1 ∪ m2);m', Φ k x y)
    ⊢ ∃ m1' m2', ⌜m' = m1' ∪ m2'⌝ ∧ ⌜ m1' ##ₘ m2' ⌝ ∧
                 ([∗ map] k↦x;y ∈ m1;m1', Φ k x y) ∗
                 ([∗ map] k↦x;y ∈ m2;m2', Φ k x y).
  Proof.
    revert m'. induction m1 as [|i x m1 ? IH] using map_ind;
      intros m' ?; decompose_map_disjoint.
    { rewrite -(exist_intro ∅) -(exist_intro m') !left_id_L.
      rewrite !pure_True //; last by apply map_disjoint_empty_l.
      rewrite big_sepM2_empty !left_id //. }
    rewrite -insert_union_l big_sepM2_delete_l; last by apply lookup_insert.
    apply exist_elim=> y. apply pure_elim_l=> ?.
    rewrite delete_insert; last by apply lookup_union_None.
    rewrite IH //.
    rewrite sep_exist_l. eapply exist_elim=> m1'.
    rewrite sep_exist_l. eapply exist_elim=> m2'.
    rewrite comm. apply wand_elim_l', pure_elim_l=> Hm'. apply pure_elim_l=> ?.
    assert ((m1' ∪ m2') !! i = None) as [??]%lookup_union_None.
    { by rewrite -Hm' lookup_delete. }
    apply wand_intro_l.
    rewrite -(exist_intro (<[i:=y]> m1')) -(exist_intro m2'). apply and_intro.
    { apply pure_intro. by rewrite -insert_union_l -Hm' insert_delete. }
    apply and_intro.
    { apply pure_intro. by apply map_disjoint_insert_l. }
    by rewrite big_sepM2_insert // -assoc.
  Qed.
End map2.

Lemma big_sepM2_union_inv_r `{Countable K} {A B}
      (Φ : K → A → B → PROP) (m1 m2 : gmap K B) (m' : gmap K A) :
  m1 ##ₘ m2 →
  ([∗ map] k↦x;y ∈ m';(m1 ∪ m2), Φ k x y)
    ⊢ ∃ m1' m2', ⌜ m' = m1' ∪ m2' ⌝ ∧ ⌜ m1' ##ₘ m2' ⌝ ∧
               ([∗ map] k↦x;y ∈ m1';m1, Φ k x y) ∗
               ([∗ map] k↦x;y ∈ m2';m2, Φ k x y).
Proof.
  intros Hm. rewrite -(big_sepM2_flip Φ).
  rewrite (big_sepM2_union_inv_l (λ k (x : B) y, Φ k y x)) //.
  f_equiv=>n1. f_equiv=>n2. f_equiv.
  by rewrite -!(big_sepM2_flip Φ).
Qed.

Lemma big_sepM_sepM2_diag `{Countable K} {A} (Φ : K → A → A → PROP) (m : gmap K A) :
  ([∗ map] k↦y ∈ m, Φ k y y) ⊢
  ([∗ map] k↦y1;y2 ∈ m;m, Φ k y1 y2).
Proof.
  rewrite big_sepM2_alt. rewrite pure_True; last naive_solver. rewrite left_id.
  rewrite map_zip_diag big_sepM_fmap. done.
Qed.

Lemma big_sepM2_ne_2 `{Countable K} (A B : ofe)
    (Φ Ψ : K → A → B → PROP) m1 m2 m1' m2' n :
  m1 ≡{n}≡ m1' → m2 ≡{n}≡ m2' →
  (∀ k y1 y1' y2 y2',
    m1 !! k = Some y1 → m1' !! k = Some y1' → y1 ≡{n}≡ y1' →
    m2 !! k = Some y2 → m2' !! k = Some y2' → y2 ≡{n}≡ y2' →
    Φ k y1 y2 ≡{n}≡ Ψ k y1' y2') →
  ([∗ map] k ↦ y1;y2 ∈ m1;m2, Φ k y1 y2)%I ≡{n}≡ ([∗ map] k ↦ y1;y2 ∈ m1';m2', Ψ k y1 y2)%I.
Proof.
  intros Hm1 Hm2 Hf. rewrite !big_sepM2_alt. f_equiv.
  { by rewrite Hm1 Hm2. }
  apply big_opM_ne_2; [by f_equiv|].
  intros k [x1 y1] [x2 y2] (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some
    (?&?&[=<- <-]&?&?)%map_lookup_zip_with_Some [??]; naive_solver.
Qed.

(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types Φ : A → PROP.

  (** The lemmas [big_sepS_mono], [big_sepS_ne] and [big_sepS_proper] are more
  generic than the instances as they also give [x ∈ X] in the premise. *)
  Lemma big_sepS_mono Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ X, Ψ x.
  Proof. intros. apply big_opS_gen_proper; apply _ || auto. Qed.
  Lemma big_sepS_ne Φ Ψ X n :
    (∀ x, x ∈ X → Φ x ≡{n}≡ Ψ x) →
    ([∗ set] x ∈ X, Φ x)%I ≡{n}≡ ([∗ set] x ∈ X, Ψ x)%I.
  Proof. apply big_opS_ne. Qed.
  Lemma big_sepS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ set] x ∈ X, Ψ x).
  Proof. apply big_opS_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opS] instances. *)
  Global Instance big_sepS_mono' :
    Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opS (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. by apply big_sepS_mono. Qed.

  Global Instance big_sepS_empty_persistent Φ :
    Persistent ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite big_opS_empty. apply _. Qed.
  Lemma big_sepS_persistent Φ X :
    (∀ x, x ∈ X → Persistent (Φ x)) → Persistent ([∗ set] x ∈ X, Φ x).
  Proof. apply big_opS_closed; apply _. Qed.
  Global Instance big_sepS_persistent' Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ set] x ∈ X, Φ x).
  Proof. intros; apply big_sepS_persistent, _. Qed.

  Global Instance big_sepS_empty_affine Φ : Affine ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite big_opS_empty. apply _. Qed.
  Lemma big_sepS_affine Φ X :
    (∀ x, x ∈ X → Affine (Φ x)) → Affine ([∗ set] x ∈ X, Φ x).
  Proof. apply big_opS_closed; apply _. Qed.
  Global Instance big_sepS_affine' Φ X :
    (∀ x, Affine (Φ x)) → Affine ([∗ set] x ∈ X, Φ x).
  Proof. intros; apply big_sepS_affine, _. Qed.

  Global Instance big_sepS_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite big_opS_empty. apply _. Qed.
  Lemma big_sepS_timeless `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, x ∈ X → Timeless (Φ x)) → Timeless ([∗ set] x ∈ X, Φ x).
  Proof. apply big_opS_closed; apply _. Qed.
  Global Instance big_sepS_timeless' `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ set] x ∈ X, Φ x).
  Proof. intros; apply big_sepS_timeless, _. Qed.

  (* See comment above [big_sepM_subseteq] as for why the [Affine]
     instance is placed late. *)
  Lemma big_sepS_subseteq Φ X Y `{!∀ x, Affine (Φ x)} :
    Y ⊆ X → ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ Y, Φ x.
  Proof.
    intros ->%union_difference_L. rewrite big_opS_union; last set_solver.
    by rewrite sep_elim_l.
  Qed.

  Lemma big_sepS_elements Φ X :
    ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ list] x ∈ elements X, Φ x).
  Proof. by rewrite big_opS_elements. Qed.

  Lemma big_sepS_empty Φ : ([∗ set] x ∈ ∅, Φ x) ⊣⊢ emp.
  Proof. by rewrite big_opS_empty. Qed.
  Lemma big_sepS_empty' P `{!Affine P} Φ : P ⊢ [∗ set] x ∈ ∅, Φ x.
  Proof. rewrite big_sepS_empty. apply: affine. Qed.

  Lemma big_sepS_emp X : ([∗ set] x ∈ X, emp) ⊣⊢@{PROP} emp.
  Proof. by rewrite big_opS_unit. Qed.

  Lemma big_sepS_insert Φ X x :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, Φ y) ⊣⊢ (Φ x ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_insert. Qed.

  Lemma big_sepS_fn_insert {B} (Ψ : A → B → PROP) f X x b :
    x ∉ X →
       ([∗ set] y ∈ {[ x ]} ∪ X, Ψ y (<[x:=b]> f y))
    ⊣⊢ (Ψ x b ∗ [∗ set] y ∈ X, Ψ y (f y)).
  Proof. apply big_opS_fn_insert. Qed.

  Lemma big_sepS_fn_insert' Φ X x P :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, <[x:=P]> Φ y) ⊣⊢ (P ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_fn_insert'. Qed.

  Lemma big_sepS_union Φ X Y :
    X ## Y →
    ([∗ set] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ Y, Φ y).
  Proof. apply big_opS_union. Qed.

  Lemma big_sepS_delete Φ X x :
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ set] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply big_opS_delete. Qed.

  Lemma big_sepS_insert_2 {Φ X} x
    `{!TCOr (Affine (Φ x)) (Absorbing (Φ x))} :
    Φ x ⊢ ([∗ set] y ∈ X, Φ y) -∗ ([∗ set] y ∈ {[ x ]} ∪ X, Φ y).
  Proof.
    apply wand_intro_r. destruct (decide (x ∈ X)); last first.
    { rewrite -big_sepS_insert //. }
    rewrite big_sepS_delete // assoc.
    rewrite (sep_elim_l (Φ x)) -big_sepS_insert; last set_solver.
    rewrite -union_difference_singleton_L //.
    replace ({[x]} ∪ X) with X by set_solver.
    auto.
  Qed.
  Lemma big_sepS_insert_2' {Φ X} x
    `{!TCOr (Affine (Φ x)) (Absorbing (Φ x))} :
    Φ x -∗ ([∗ set] y ∈ X, Φ y) -∗ ([∗ set] y ∈ X ∪ {[ x ]}, Φ y).
  Proof. apply entails_wand. rewrite comm_L. by apply big_sepS_insert_2. Qed.

  Lemma big_sepS_union_2 {Φ} X Y
    `{!∀ x, TCOr (Affine (Φ x)) (Absorbing (Φ x))} :
    ([∗ set] y ∈ X, Φ y) -∗ ([∗ set] y ∈ Y, Φ y) -∗ ([∗ set] y ∈ X ∪ Y, Φ y).
  Proof.
    apply entails_wand, wand_intro_r. induction X as [|x X ? IH] using set_ind_L.
    { by rewrite left_id_L big_sepS_empty left_id. }
    rewrite big_sepS_insert // -assoc IH -assoc_L.
    destruct (decide (x ∈ Y)).
    { replace ({[x]} ∪ (X ∪ Y)) with (X ∪ Y) by set_solver.
      rewrite (big_sepS_delete _ _ x); last set_solver.
      by rewrite assoc sep_elim_r. }
    by rewrite big_sepS_insert; last set_solver.
  Qed.

  Lemma big_sepS_delete_2 {Φ X} x :
    Affine (Φ x) →
    Φ x ⊢ ([∗ set] y ∈ X ∖ {[ x ]}, Φ y) -∗ [∗ set] y ∈ X, Φ y.
  Proof.
    intros Haff. apply wand_intro_r. destruct (decide (x ∈ X)).
    { rewrite -big_sepS_delete //. }
    rewrite sep_elim_r.
    replace (X ∖ {[x]}) with X by set_solver.
    auto.
  Qed.

  Lemma big_sepS_elem_of Φ X x
    `{!TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))} :
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊢ Φ x.
  Proof.
    intros ?. rewrite big_sepS_delete //.
    destruct select (TCOr _ _); by rewrite sep_elim_l.
  Qed.

  Lemma big_sepS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ set] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ set] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepS_singleton Φ x : ([∗ set] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opS_singleton. Qed.

  Lemma big_sepS_filter' (φ : A → Prop) `{∀ x, Decision (φ x)} Φ X :
    ([∗ set] y ∈ filter φ X, Φ y)
    ⊣⊢ ([∗ set] y ∈ X, if decide (φ y) then Φ y else emp).
  Proof. apply: big_opS_filter'. Qed.
  Lemma big_sepS_filter `{!BiAffine PROP}
      (φ : A → Prop) `{∀ x, Decision (φ x)} Φ X :
    ([∗ set] y ∈ filter φ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ⌜φ y⌝ → Φ y).
  Proof. setoid_rewrite <-decide_emp. apply big_sepS_filter'. Qed.

  Lemma big_sepS_filter_acc' (φ : A → Prop) `{∀ y, Decision (φ y)} Φ X Y :
    (∀ y, y ∈ Y → φ y → y ∈ X) →
    ([∗ set] y ∈ X, Φ y) -∗
      ([∗ set] y ∈ Y, if decide (φ y) then Φ y else emp) ∗
      (([∗ set] y ∈ Y, if decide (φ y) then Φ y else emp) -∗ [∗ set] y ∈ X, Φ y).
  Proof.
    intros ?. destruct (proj1 (subseteq_disjoint_union_L (filter φ Y) X))
      as (Z&->&?); first set_solver.
    rewrite big_sepS_union // big_sepS_filter'.
    by apply entails_wand, sep_mono_r, wand_intro_l.
  Qed.
  Lemma big_sepS_filter_acc `{!BiAffine PROP}
      (φ : A → Prop) `{∀ y, Decision (φ y)} Φ X Y :
    (∀ y, y ∈ Y → φ y → y ∈ X) →
    ([∗ set] y ∈ X, Φ y) -∗
      ([∗ set] y ∈ Y, ⌜φ y⌝ → Φ y) ∗
      (([∗ set] y ∈ Y, ⌜φ y⌝ → Φ y) -∗ [∗ set] y ∈ X, Φ y).
  Proof. intros. setoid_rewrite <-decide_emp. by apply big_sepS_filter_acc'. Qed.

  Lemma big_sepS_list_to_set Φ (l : list A) :
    NoDup l →
    ([∗ set] x ∈ list_to_set l, Φ x) ⊣⊢ [∗ list] x ∈ l, Φ x.
  Proof. apply big_opS_list_to_set. Qed.

  Lemma big_sepS_sep Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ X, Ψ y).
  Proof. apply big_opS_op. Qed.

  Lemma big_sepS_sep_2 Φ Ψ X :
    ([∗ set] y ∈ X, Φ y) -∗
    ([∗ set] y ∈ X, Ψ y) -∗
    ([∗ set] y ∈ X, Φ y ∗ Ψ y).
  Proof. apply entails_wand, wand_intro_r. rewrite big_sepS_sep //. Qed.

  Lemma big_sepS_and Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ set] y ∈ X, Φ y) ∧ ([∗ set] y ∈ X, Ψ y).
  Proof. auto using and_intro, big_sepS_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepS_pure_1 (φ : A → Prop) X :
    ([∗ set] y ∈ X, ⌜φ y⌝) ⊢@{PROP} ⌜set_Forall φ X⌝.
  Proof.
    induction X as [|x X ? IH] using set_ind_L.
    { apply pure_intro, set_Forall_empty. }
    rewrite big_sepS_insert // IH sep_and -pure_and.
    f_equiv=>-[Hx HX]. apply set_Forall_union.
    - apply set_Forall_singleton. done.
    - done.
  Qed.
  Lemma big_sepS_affinely_pure_2 (φ : A → Prop) X :
    <affine> ⌜set_Forall φ X⌝ ⊢@{PROP} ([∗ set] y ∈ X, <affine> ⌜φ y⌝).
  Proof.
    induction X as [|x X ? IH] using set_ind_L.
    { rewrite big_sepS_empty. apply affinely_elim_emp. }
    rewrite big_sepS_insert // -IH.
    rewrite -persistent_and_sep_1 -affinely_and -pure_and.
    f_equiv. f_equiv=>HX. split.
    - apply HX. set_solver+.
    - apply set_Forall_union_inv_2 in HX. done.
  Qed.
  (** The general backwards direction requires [BiAffine] to cover the empty case. *)
  Lemma big_sepS_pure `{!BiAffine PROP} (φ : A → Prop) X :
    ([∗ set] y ∈ X, ⌜φ y⌝) ⊣⊢@{PROP} ⌜set_Forall φ X⌝.
  Proof.
    apply (anti_symm (⊢)); first by apply big_sepS_pure_1.
    rewrite -(affine_affinely ⌜_⌝%I).
    rewrite big_sepS_affinely_pure_2. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepS_persistently `{!BiAffine PROP} Φ X :
    <pers> ([∗ set] y ∈ X, Φ y) ⊣⊢ [∗ set] y ∈ X, <pers> (Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_intro Φ X :
    □ (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ [∗ set] x ∈ X, Φ x.
  Proof.
    revert Φ. induction X as [|x X ? IH] using set_ind_L=> Φ.
    { by rewrite (affine (□ _)) big_sepS_empty. }
    rewrite intuitionistically_sep_dup big_sepS_insert //. f_equiv.
    - rewrite (forall_elim x) pure_True ?True_impl; last set_solver.
      by rewrite intuitionistically_elim.
    - rewrite -IH. f_equiv. apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last set_solver.
  Qed.

  Lemma big_sepS_forall `{!BiAffine PROP} Φ X :
    (∀ x, Persistent (Φ x)) →
    ([∗ set] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepS_elem_of. }
    revert Φ HΦ. induction X as [|x X ? IH] using set_ind_L=> Φ HΦ.
    { rewrite big_sepS_empty. apply: affine. }
    rewrite big_sepS_insert // -persistent_and_sep_1. apply and_intro.
    - rewrite (forall_elim x) pure_True ?True_impl; last set_solver. done.
    - rewrite -IH. apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last set_solver.
  Qed.

  Lemma big_sepS_impl Φ Ψ X :
    ([∗ set] x ∈ X, Φ x) -∗
    □ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x) -∗
    [∗ set] x ∈ X, Ψ x.
  Proof.
    apply entails_wand, wand_intro_l. rewrite big_sepS_intro -big_sepS_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepS_wand Φ Ψ X :
    ([∗ set] x ∈ X, Φ x) -∗
    ([∗ set] x ∈ X, Φ x -∗ Ψ x) -∗
    [∗ set] x ∈ X, Ψ x.
  Proof.
    apply entails_wand, wand_intro_r. rewrite -big_sepS_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepS_elem_of_acc_impl {Φ X} x :
    x ∈ X →
    ([∗ set] y ∈ X, Φ y) -∗
    (* we get [Φ] for the element [x] *)
    Φ x ∗
    (* we reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ y, ⌜ y ∈ X ⌝ → ⌜ x ≠ y ⌝ → Φ y -∗ Ψ y) -∗
      Ψ x -∗
      [∗ set] y ∈ X, Ψ y.
  Proof.
    intros. rewrite big_sepS_delete //. apply entails_wand, sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepS_delete Ψ X x) //. apply sep_mono_r.
    eapply wand_apply; [apply wand_entails, big_sepS_impl|apply sep_mono_r].
    f_equiv; f_equiv=> y. rewrite impl_curry -pure_and.
    do 2 f_equiv. intros ?; set_solver.
  Qed.

  Lemma big_sepS_dup P `{!Affine P} X :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ set] x ∈ X, P.
  Proof.
    apply entails_wand, wand_intro_l. induction X as [|x X ? IH] using set_ind_L.
    { apply: big_sepS_empty'. }
    rewrite !big_sepS_insert //.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepS_later `{!BiAffine PROP} Φ X :
    ▷ ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷ Φ y).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_sepS_later_2 Φ X :
    ([∗ set] y ∈ X, ▷ Φ y) ⊢ ▷ ([∗ set] y ∈ X, Φ y).
  Proof. by rewrite big_opS_commute. Qed.

  Lemma big_sepS_laterN `{!BiAffine PROP} Φ n X :
    ▷^n ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_sepS_laterN_2 Φ n X :
    ([∗ set] y ∈ X, ▷^n Φ y) ⊢ ▷^n ([∗ set] y ∈ X, Φ y).
  Proof. by rewrite big_opS_commute. Qed.
End gset.

Lemma big_sepM_dom `{Countable K} {A} (Φ : K → PROP) (m : gmap K A) :
  ([∗ map] k↦_ ∈ m, Φ k) ⊣⊢ ([∗ set] k ∈ dom m, Φ k).
Proof. apply big_opM_dom. Qed.
Lemma big_sepM_gset_to_gmap `{Countable K} {A} (Φ : K → A → PROP) (X : gset K) c :
  ([∗ map] k↦a ∈ gset_to_gmap c X, Φ k a) ⊣⊢ ([∗ set] k ∈ X, Φ k c).
Proof. apply big_opM_gset_to_gmap. Qed.

(** ** Big ops over finite multisets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types Φ : A → PROP.

  (** The lemmas [big_sepMS_mono], [big_sepMS_ne] and [big_sepMS_proper] are more
  generic than the instances as they also give [l !! k = Some y] in the premise. *)
  Lemma big_sepMS_mono Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊢ [∗ mset] x ∈ X, Ψ x.
  Proof. intros. apply big_opMS_gen_proper; apply _ || auto. Qed.
  Lemma big_sepMS_ne Φ Ψ X n :
    (∀ x, x ∈ X → Φ x ≡{n}≡ Ψ x) →
    ([∗ mset] x ∈ X, Φ x)%I ≡{n}≡ ([∗ mset] x ∈ X, Ψ x)%I.
  Proof. apply big_opMS_ne. Qed.
  Lemma big_sepMS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊣⊢ ([∗ mset] x ∈ X, Ψ x).
  Proof. apply big_opMS_proper. Qed.

  (** No need to declare instances for non-expansiveness and properness, we
  get both from the generic [big_opMS] instances. *)
  Global Instance big_sepMS_mono' :
     Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opMS (@bi_sep PROP) (A:=A)).
  Proof. intros f g Hf m ? <-. by apply big_sepMS_mono. Qed.

  Global Instance big_sepMS_empty_persistent Φ :
    Persistent ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite big_opMS_empty. apply _. Qed.
  Lemma big_sepMS_persistent Φ X :
    (∀ x, x ∈ X → Persistent (Φ x)) → Persistent ([∗ mset] x ∈ X, Φ x).
  Proof. apply big_opMS_closed; apply _. Qed.
  Global Instance big_sepMS_persistent' Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ mset] x ∈ X, Φ x).
  Proof. intros; apply big_sepMS_persistent, _. Qed.

  Global Instance big_sepMS_empty_affine Φ : Affine ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite big_opMS_empty. apply _. Qed.
  Lemma big_sepMS_affine Φ X :
    (∀ x, x ∈ X → Affine (Φ x)) → Affine ([∗ mset] x ∈ X, Φ x).
  Proof. apply big_opMS_closed; apply _. Qed.
  Global Instance big_sepMS_affine' Φ X :
    (∀ x, Affine (Φ x)) → Affine ([∗ mset] x ∈ X, Φ x).
  Proof. intros; apply big_sepMS_affine, _. Qed.

  Global Instance big_sepMS_empty_timeless `{!Timeless (emp%I : PROP)} Φ :
    Timeless ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite big_opMS_empty. apply _. Qed.
  Lemma big_sepMS_timeless `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, x ∈ X → Timeless (Φ x)) → Timeless ([∗ mset] x ∈ X, Φ x).
  Proof. apply big_opMS_closed; apply _. Qed.
  Global Instance big_sepMS_timeless' `{!Timeless (emp%I : PROP)} Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ mset] x ∈ X, Φ x).
  Proof. intros; apply big_sepMS_timeless, _. Qed.

  (* See comment above [big_sepM_subseteq] as for why the [Affine]
     instance is placed late. *)
  Lemma big_sepMS_subseteq Φ X Y `{!∀ x, Affine (Φ x)} :
    Y ⊆ X → ([∗ mset] x ∈ X, Φ x) ⊢ [∗ mset] x ∈ Y, Φ x.
  Proof.
    intros ->%gmultiset_disj_union_difference.
    by rewrite big_opMS_disj_union sep_elim_l.
  Qed.

  Lemma big_sepMS_empty Φ : ([∗ mset] x ∈ ∅, Φ x) ⊣⊢ emp.
  Proof. by rewrite big_opMS_empty. Qed.
  Lemma big_sepMS_empty' P `{!Affine P} Φ : P ⊢ [∗ mset] x ∈ ∅, Φ x.
  Proof. rewrite big_sepMS_empty. apply: affine. Qed.

  Lemma big_sepMS_disj_union Φ X Y :
    ([∗ mset] y ∈ X ⊎ Y, Φ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ [∗ mset] y ∈ Y, Φ y.
  Proof. apply big_opMS_disj_union. Qed.

  Lemma big_sepMS_delete Φ X x :
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ mset] y ∈ X ∖ {[+ x +]}, Φ y.
  Proof. apply big_opMS_delete. Qed.

  Lemma big_sepMS_elem_of Φ X x
    `{!TCOr (∀ y, Affine (Φ y)) (Absorbing (Φ x))} :
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊢ Φ x.
  Proof.
    intros ?. rewrite big_sepMS_delete //.
    destruct select (TCOr _ _); by rewrite sep_elim_l.
  Qed.

  Lemma big_sepMS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ mset] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ mset] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepMS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepMS_singleton Φ x : ([∗ mset] y ∈ {[+ x +]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opMS_singleton. Qed.

  Lemma big_sepMS_insert Φ X x :
    ([∗ mset] y ∈ {[+ x +]} ⊎ X, Φ y) ⊣⊢ (Φ x ∗ [∗ mset] y ∈ X, Φ y).
  Proof. apply big_opMS_insert. Qed.

  Lemma big_sepMS_sep Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ ([∗ mset] y ∈ X, Ψ y).
  Proof. apply big_opMS_op. Qed.

  Lemma big_sepMS_sep_2 Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y) -∗
    ([∗ mset] y ∈ X, Ψ y) -∗
    ([∗ mset] y ∈ X, Φ y ∗ Ψ y).
  Proof. apply entails_wand, wand_intro_r. rewrite big_sepMS_sep //. Qed.

  Lemma big_sepMS_and Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ mset] y ∈ X, Φ y) ∧ ([∗ mset] y ∈ X, Ψ y).
  Proof. auto using and_intro, big_sepMS_mono, and_elim_l, and_elim_r. Qed.

  Lemma big_sepMS_later `{!BiAffine PROP} Φ X :
    ▷ ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷ Φ y).
  Proof. apply (big_opMS_commute _). Qed.
  Lemma big_sepMS_later_2 Φ X :
    ([∗ mset] y ∈ X, ▷ Φ y) ⊢ ▷ [∗ mset] y ∈ X, Φ y.
  Proof. by rewrite big_opMS_commute. Qed.

  Lemma big_sepMS_laterN `{!BiAffine PROP} Φ n X :
    ▷^n ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opMS_commute _). Qed.
  Lemma big_sepMS_laterN_2 Φ n X :
    ([∗ mset] y ∈ X, ▷^n Φ y) ⊢ ▷^n [∗ mset] y ∈ X, Φ y.
  Proof. by rewrite big_opMS_commute. Qed.

  Lemma big_sepMS_pure_1 (φ : A → Prop) X :
    ([∗ mset] y ∈ X, ⌜φ y⌝) ⊢@{PROP} ⌜∀ y : A, y ∈ X → φ y⌝.
  Proof.
    induction X as [|x X IH] using gmultiset_ind.
    { apply pure_intro=>??. exfalso. multiset_solver. }
    rewrite big_sepMS_insert // IH sep_and -pure_and.
    f_equiv=>-[Hx HX] y /gmultiset_elem_of_disj_union [|].
    - move=>/gmultiset_elem_of_singleton =>->. done.
    - eauto.
  Qed.
  Lemma big_sepMS_affinely_pure_2 (φ : A → Prop) X :
    <affine> ⌜∀ y : A, y ∈ X → φ y⌝ ⊢@{PROP} ([∗ mset] y ∈ X, <affine> ⌜φ y⌝).
  Proof.
    induction X as [|x X IH] using gmultiset_ind.
    { rewrite big_sepMS_empty. apply affinely_elim_emp. }
    rewrite big_sepMS_insert // -IH.
    rewrite -persistent_and_sep_1 -affinely_and -pure_and.
    f_equiv. f_equiv=>HX. split.
    - apply HX. set_solver+.
    - intros y Hy. apply HX. multiset_solver.
  Qed.
  (** The general backwards direction requires [BiAffine] to cover the empty case. *)
  Lemma big_sepMS_pure `{!BiAffine PROP} (φ : A → Prop) X :
    ([∗ mset] y ∈ X, ⌜φ y⌝) ⊣⊢@{PROP} ⌜∀ y : A, y ∈ X → φ y⌝.
  Proof.
    apply (anti_symm (⊢)); first by apply big_sepMS_pure_1.
    rewrite -(affine_affinely ⌜_⌝%I).
    rewrite big_sepMS_affinely_pure_2. by setoid_rewrite affinely_elim.
  Qed.

  Lemma big_sepMS_persistently `{!BiAffine PROP} Φ X :
    <pers> ([∗ mset] y ∈ X, Φ y) ⊣⊢ [∗ mset] y ∈ X, <pers> (Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Lemma big_sepMS_intro Φ X :
    □ (∀ x, ⌜x ∈ X⌝ → Φ x) ⊢ [∗ mset] x ∈ X, Φ x.
  Proof.
    revert Φ. induction X as [|x X IH] using gmultiset_ind=> Φ.
    { by rewrite (affine (□ _)) big_sepMS_empty. }
    rewrite intuitionistically_sep_dup big_sepMS_disj_union.
    rewrite big_sepMS_singleton. f_equiv.
    - rewrite (forall_elim x) pure_True ?True_impl; last multiset_solver.
      by rewrite intuitionistically_elim.
    - rewrite -IH. f_equiv. apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last multiset_solver.
  Qed.

  Lemma big_sepMS_forall `{!BiAffine PROP} Φ X :
    (∀ x, Persistent (Φ x)) →
    ([∗ mset] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply: big_sepMS_elem_of. }
    revert Φ HΦ. induction X as [|x X IH] using gmultiset_ind=> Φ HΦ.
    { rewrite big_sepMS_empty. apply: affine. }
    rewrite big_sepMS_disj_union.
    rewrite big_sepMS_singleton -persistent_and_sep_1. apply and_intro.
    - rewrite (forall_elim x) pure_True ?True_impl; last multiset_solver. done.
    - rewrite -IH. apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last multiset_solver.
  Qed.

  Lemma big_sepMS_impl Φ Ψ X :
    ([∗ mset] x ∈ X, Φ x) -∗
    □ (∀ x, ⌜x ∈ X⌝ → Φ x -∗ Ψ x) -∗
    [∗ mset] x ∈ X, Ψ x.
  Proof.
    apply entails_wand, wand_intro_l. rewrite big_sepMS_intro -big_sepMS_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepMS_wand Φ Ψ X :
    ([∗ mset] x ∈ X, Φ x) -∗
    ([∗ mset] x ∈ X, Φ x -∗ Ψ x) -∗
    [∗ mset] x ∈ X, Ψ x.
  Proof.
    apply entails_wand, wand_intro_r. rewrite -big_sepMS_sep.
    setoid_rewrite wand_elim_r. done.
  Qed.

  Lemma big_sepMS_dup P `{!Affine P} X :
    □ (P -∗ P ∗ P) -∗ P -∗ [∗ mset] x ∈ X, P.
  Proof.
    apply entails_wand, wand_intro_l. induction X as [|x X IH] using gmultiset_ind.
    { apply: big_sepMS_empty'. }
    rewrite !big_sepMS_disj_union big_sepMS_singleton.
    rewrite intuitionistically_sep_dup {1}intuitionistically_elim.
    rewrite assoc wand_elim_r -assoc. apply sep_mono; done.
  Qed.

  Lemma big_sepMS_elem_of_acc_impl {Φ X} x :
    x ∈ X →
    ([∗ mset] y ∈ X, Φ y) -∗
    (* we get [Φ] for [x] *)
    Φ x ∗
    (* we reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ y, ⌜ y ∈ X ∖ {[+ x +]} ⌝ → Φ y -∗ Ψ y) -∗
      Ψ x -∗
      [∗ mset] y ∈ X, Ψ y.
  Proof.
    intros. rewrite big_sepMS_delete //. apply entails_wand, sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, wand_intro_l.
    rewrite (big_sepMS_delete Ψ X x) //. apply sep_mono_r.
    apply wand_elim_l', wand_entails, big_sepMS_impl.
  Qed.
End gmultiset.

(** Commuting lemmas *)
Lemma big_sepL_sepL {A B} (Φ : nat → A → nat → B → PROP) (l1 : list A) (l2 : list B) :
  ([∗ list] k1↦x1 ∈ l1, [∗ list] k2↦x2 ∈ l2, Φ k1 x1 k2 x2) ⊣⊢
  ([∗ list] k2↦x2 ∈ l2, [∗ list] k1↦x1 ∈ l1, Φ k1 x1 k2 x2).
Proof. apply big_opL_opL. Qed.
Lemma big_sepL_sepM {A} `{Countable K} {B}
    (Φ : nat → A → K → B → PROP) (l1 : list A) (m2 : gmap K B) :
  ([∗ list] k1↦x1 ∈ l1, [∗ map] k2↦x2 ∈ m2, Φ k1 x1 k2 x2) ⊣⊢
  ([∗ map] k2↦x2 ∈ m2, [∗ list] k1↦x1 ∈ l1, Φ k1 x1 k2 x2).
Proof. apply big_opL_opM. Qed.
Lemma big_sepL_sepS {A} `{Countable B}
    (Φ : nat → A → B → PROP) (l1 : list A) (X2 : gset B) :
  ([∗ list] k1↦x1 ∈ l1, [∗ set] x2 ∈ X2, Φ k1 x1 x2) ⊣⊢
  ([∗ set] x2 ∈ X2, [∗ list] k1↦x1 ∈ l1, Φ k1 x1 x2).
Proof. apply big_opL_opS. Qed.
Lemma big_sepL_sepMS {A} `{Countable B}
    (Φ : nat → A → B → PROP) (l1 : list A) (X2 : gmultiset B) :
  ([∗ list] k1↦x1 ∈ l1, [∗ mset] x2 ∈ X2, Φ k1 x1 x2) ⊣⊢
  ([∗ mset] x2 ∈ X2, [∗ list] k1↦x1 ∈ l1, Φ k1 x1 x2).
Proof. apply big_opL_opMS. Qed.

Lemma big_sepM_sepL `{Countable K} {A} {B}
    (Φ : K → A → nat → B → PROP) (m1 : gmap K A) (l2 : list B) :
  ([∗ map] k1↦x1 ∈ m1, [∗ list] k2↦x2 ∈ l2, Φ k1 x1 k2 x2) ⊣⊢
  ([∗ list] k2↦x2 ∈ l2, [∗ map] k1↦x1 ∈ m1, Φ k1 x1 k2 x2).
Proof. apply big_opM_opL. Qed.
Lemma big_sepM_sepM `{Countable K1} {A} `{Countable K2} {B}
    (Φ : K1 → A → K2 → B → PROP) (m1 : gmap K1 A) (m2 : gmap K2 B) :
  ([∗ map] k1↦x1 ∈ m1, [∗ map] k2↦x2 ∈ m2, Φ k1 x1 k2 x2) ⊣⊢
  ([∗ map] k2↦x2 ∈ m2, [∗ map] k1↦x1 ∈ m1, Φ k1 x1 k2 x2).
Proof. apply big_opM_opM. Qed.
Lemma big_sepM_sepS `{Countable K} {A} `{Countable B}
    (Φ : K → A → B → PROP) (m1 : gmap K A) (X2 : gset B) :
  ([∗ map] k1↦x1 ∈ m1, [∗ set] x2 ∈ X2, Φ k1 x1 x2) ⊣⊢
  ([∗ set] x2 ∈ X2, [∗ map] k1↦x1 ∈ m1, Φ k1 x1 x2).
Proof. apply big_opM_opS. Qed.
Lemma big_sepM_sepMS `{Countable K} {A} `{Countable B} (Φ : K → A → B → PROP)
    (m1 : gmap K A) (X2 : gmultiset B) :
  ([∗ map] k1↦x1 ∈ m1, [∗ mset] x2 ∈ X2, Φ k1 x1 x2) ⊣⊢
  ([∗ mset] x2 ∈ X2, [∗ map] k1↦x1 ∈ m1, Φ k1 x1 x2).
Proof. apply big_opM_opMS. Qed.

Lemma big_sepS_sepL `{Countable A} {B}
    (f : A → nat → B → PROP) (X1 : gset A) (l2 : list B) :
  ([∗ set] x1 ∈ X1, [∗ list] k2↦x2 ∈ l2, f x1 k2 x2) ⊣⊢
  ([∗ list] k2↦x2 ∈ l2, [∗ set] x1 ∈ X1, f x1 k2 x2).
Proof. apply big_opS_opL. Qed.
Lemma big_sepS_sepM `{Countable A} `{Countable K} {B}
    (f : A → K → B → PROP) (X1 : gset A) (m2 : gmap K B) :
  ([∗ set] x1 ∈ X1, [∗ map] k2↦x2 ∈ m2, f x1 k2 x2) ⊣⊢
  ([∗ map] k2↦x2 ∈ m2, [∗ set] x1 ∈ X1, f x1 k2 x2).
Proof. apply big_opS_opM. Qed.
Lemma big_sepS_sepS `{Countable A, Countable B}
    (X : gset A) (Y : gset B) (Φ : A → B → PROP) :
  ([∗ set] x ∈ X, [∗ set] y ∈ Y, Φ x y) ⊣⊢ ([∗ set] y ∈ Y, [∗ set] x ∈ X, Φ x y).
Proof. apply big_opS_opS. Qed.
Lemma big_sepS_sepMS `{Countable A, Countable B}
    (X : gset A) (Y : gmultiset B) (Φ : A → B → PROP) :
  ([∗ set] x ∈ X, [∗ mset] y ∈ Y, Φ x y) ⊣⊢ ([∗ mset] y ∈ Y, [∗ set] x ∈ X, Φ x y).
Proof. apply big_opS_opMS. Qed.

Lemma big_sepMS_sepL `{Countable A} {B}
    (f : A → nat → B → PROP) (X1 : gmultiset A) (l2 : list B) :
  ([∗ mset] x1 ∈ X1, [∗ list] k2↦x2 ∈ l2, f x1 k2 x2) ⊣⊢
  ([∗ list] k2↦x2 ∈ l2, [∗ mset] x1 ∈ X1, f x1 k2 x2).
Proof. apply big_opMS_opL. Qed.
Lemma big_sepMS_sepM `{Countable A} `{Countable K} {B} (f : A → K → B → PROP)
    (X1 : gmultiset A) (m2 : gmap K B) :
  ([∗ mset] x1 ∈ X1, [∗ map] k2↦x2 ∈ m2, f x1 k2 x2) ⊣⊢
  ([∗ map] k2↦x2 ∈ m2, [∗ mset] x1 ∈ X1, f x1 k2 x2).
Proof. apply big_opMS_opM. Qed.
Lemma big_sepMS_sepS `{Countable A, Countable B}
    (X : gmultiset A) (Y : gset B) (f : A → B → PROP) :
  ([∗ mset] x ∈ X, [∗ set] y ∈ Y, f x y) ⊣⊢ ([∗ set] y ∈ Y, [∗ mset] x ∈ X, f x y).
Proof. apply big_opMS_opS. Qed.
Lemma big_sepMS_sepMS `{Countable A, Countable B}
    (X : gmultiset A) (Y : gmultiset B) (Φ : A → B → PROP) :
  ([∗ mset] x ∈ X, [∗ mset] y ∈ Y, Φ x y) ⊣⊢ ([∗ mset] y ∈ Y, [∗ mset] x ∈ X, Φ x y).
Proof. apply big_opMS_opMS. Qed.

End big_op.
