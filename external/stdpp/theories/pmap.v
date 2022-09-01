(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of positive binary naturals [positive]. The
implementation is based on Xavier Leroy's implementation of radix-2 search
trees (uncompressed Patricia trees) and guarantees logarithmic-time operations.
However, we extend Leroy's implementation by packing the trees into a Sigma
type such that canonicity of representation is ensured. This is necesarry for
Leibniz equality to become extensional. *)
From Coq Require Import PArith.
From stdpp Require Import mapset countable.
From stdpp Require Export fin_maps.
From stdpp Require Import options.

Local Open Scope positive_scope.
Local Hint Extern 0 (_ =@{positive} _) => congruence : core.
Local Hint Extern 0 (_ ≠@{positive} _) => congruence : core.

(** * The tree data structure *)
(** The internal data type [Pmap_raw] specifies radix-2 search trees. These
trees do not ensure canonical representations of maps. For example the empty map
can be represented as a binary tree of an arbitrary size that contains [None] at
all nodes.
See below for [Pmap] which ensures canonical representation. *)
Inductive Pmap_raw (A : Type) : Type :=
  | PLeaf: Pmap_raw A
  | PNode: option A → Pmap_raw A → Pmap_raw A → Pmap_raw A.
Global Arguments PLeaf {_} : assert.
Global Arguments PNode {_} _ _ _ : assert.

Global Instance Pmap_raw_eq_dec `{EqDecision A} : EqDecision (Pmap_raw A).
Proof. solve_decision. Defined.

Fixpoint Pmap_wf {A} (t : Pmap_raw A) : bool :=
  match t with
  | PLeaf => true
  | PNode None PLeaf PLeaf => false
  | PNode _ l r => Pmap_wf l && Pmap_wf r
  end.
Global Arguments Pmap_wf _ !_ / : simpl nomatch, assert.
Lemma Pmap_wf_l {A} o (l r : Pmap_raw A) : Pmap_wf (PNode o l r) → Pmap_wf l.
Proof. destruct o, l, r; simpl; rewrite ?andb_True; tauto. Qed.
Lemma Pmap_wf_r {A} o (l r : Pmap_raw A) : Pmap_wf (PNode o l r) → Pmap_wf r.
Proof. destruct o, l, r; simpl; rewrite ?andb_True; tauto. Qed.
Local Hint Immediate Pmap_wf_l Pmap_wf_r : core.
Definition PNode' {A} (o : option A) (l r : Pmap_raw A) :=
  match l, o, r with PLeaf, None, PLeaf => PLeaf | _, _, _ => PNode o l r end.
Global Arguments PNode' : simpl never.
Lemma PNode_wf {A} o (l r : Pmap_raw A) :
  Pmap_wf l → Pmap_wf r → Pmap_wf (PNode' o l r).
Proof. destruct o, l, r; simpl; auto. Qed.
Local Hint Resolve PNode_wf : core.

(** Operations *)
Global Instance Pempty_raw {A} : Empty (Pmap_raw A) := PLeaf.
Global Instance Plookup_raw {A} : Lookup positive A (Pmap_raw A) :=
  fix go (i : positive) (t : Pmap_raw A) {struct t} : option A :=
  let _ : Lookup _ _ _ := @go in
  match t with
  | PLeaf => None
  | PNode o l r => match i with 1 => o | i~0 => l !! i | i~1 => r !! i end
  end.
Local Arguments lookup _ _ _ _ _ !_ / : simpl nomatch, assert.
Fixpoint Psingleton_raw {A} (i : positive) (x : A) : Pmap_raw A :=
  match i with
  | 1 => PNode (Some x) PLeaf PLeaf
  | i~0 => PNode None (Psingleton_raw i x) PLeaf
  | i~1 => PNode None PLeaf (Psingleton_raw i x)
  end.
Fixpoint Ppartial_alter_raw {A} (f : option A → option A)
    (i : positive) (t : Pmap_raw A) {struct t} : Pmap_raw A :=
  match t with
  | PLeaf => match f None with None => PLeaf | Some x => Psingleton_raw i x end
  | PNode o l r =>
     match i with
     | 1 => PNode' (f o) l r
     | i~0 => PNode' o (Ppartial_alter_raw f i l) r
     | i~1 => PNode' o l (Ppartial_alter_raw f i r)
     end
  end.
Fixpoint Pfmap_raw {A B} (f : A → B) (t : Pmap_raw A) : Pmap_raw B :=
  match t with
  | PLeaf => PLeaf
  | PNode o l r => PNode (f <$> o) (Pfmap_raw f l) (Pfmap_raw f r)
  end.
Fixpoint Pto_list_raw {A} (j : positive) (t : Pmap_raw A)
    (acc : list (positive * A)) : list (positive * A) :=
  match t with
  | PLeaf => acc
  | PNode o l r => from_option (λ x, [(Preverse j, x)]) [] o ++
     Pto_list_raw (j~0) l (Pto_list_raw (j~1) r acc)
  end%list.
Fixpoint Pomap_raw {A B} (f : A → option B) (t : Pmap_raw A) : Pmap_raw B :=
  match t with
  | PLeaf => PLeaf
  | PNode o l r => PNode' (o ≫= f) (Pomap_raw f l) (Pomap_raw f r)
  end.
Fixpoint Pmerge_raw {A B C} (f : option A → option B → option C)
    (t1 : Pmap_raw A) (t2 : Pmap_raw B) : Pmap_raw C :=
  match t1, t2 with
  | PLeaf, t2 => Pomap_raw (f None ∘ Some) t2
  | t1, PLeaf => Pomap_raw (flip f None ∘ Some) t1
  | PNode o1 l1 r1, PNode o2 l2 r2 =>
      PNode' (diag_None f o1 o2) (Pmerge_raw f l1 l2) (Pmerge_raw f r1 r2)
  end.

(** Proofs *)
Lemma Pmap_wf_canon {A} (t : Pmap_raw A) :
  (∀ i, t !! i = None) → Pmap_wf t → t = PLeaf.
Proof.
  induction t as [|o l IHl r IHr]; intros Ht ?; auto.
  assert (o = None) as -> by (apply (Ht 1)).
  assert (l = PLeaf) as -> by (apply IHl; try apply (λ i, Ht (i~0)); eauto).
  by assert (r = PLeaf) as -> by (apply IHr; try apply (λ i, Ht (i~1)); eauto).
Qed.
Lemma Pmap_wf_eq {A} (t1 t2 : Pmap_raw A) :
  (∀ i, t1 !! i = t2 !! i) → Pmap_wf t1 → Pmap_wf t2 → t1 = t2.
Proof.
  revert t2.
  induction t1 as [|o1 l1 IHl r1 IHr]; intros [|o2 l2 r2] Ht ??; simpl; auto.
  - discriminate (Pmap_wf_canon (PNode o2 l2 r2)); eauto.
  - discriminate (Pmap_wf_canon (PNode o1 l1 r1)); eauto.
  - f_equal; [apply (Ht 1)| |].
    + apply IHl; try apply (λ x, Ht (x~0)); eauto.
    + apply IHr; try apply (λ x, Ht (x~1)); eauto.
Qed.
Lemma PNode_lookup {A} o (l r : Pmap_raw A) i :
  PNode' o l r !! i = PNode o l r !! i.
Proof. by destruct i, o, l, r. Qed.

Lemma Psingleton_wf {A} i (x : A) : Pmap_wf (Psingleton_raw i x).
Proof. induction i as [[]|[]|]; simpl; rewrite ?andb_true_r; auto. Qed.
Lemma Ppartial_alter_wf {A} f i (t : Pmap_raw A) :
  Pmap_wf t → Pmap_wf (Ppartial_alter_raw f i t).
Proof.
  revert i; induction t as [|o l IHl r IHr]; intros i ?; simpl.
  - destruct (f None); auto using Psingleton_wf.
  - destruct i; simpl; eauto.
Qed.
Lemma Pfmap_wf {A B} (f : A → B) t : Pmap_wf t → Pmap_wf (Pfmap_raw f t).
Proof.
  induction t as [|[x|] [] ? [] ?]; simpl in *; rewrite ?andb_True; intuition.
Qed.
Lemma Pomap_wf {A B} (f : A → option B) t : Pmap_wf t → Pmap_wf (Pomap_raw f t).
Proof. induction t; simpl; eauto. Qed.
Lemma Pmerge_wf {A B C} (f : option A → option B → option C) t1 t2 :
  Pmap_wf t1 → Pmap_wf t2 → Pmap_wf (Pmerge_raw f t1 t2).
Proof. revert t2. induction t1; intros []; simpl; eauto using Pomap_wf. Qed.

Lemma Plookup_empty {A} i : (∅ : Pmap_raw A) !! i = None.
Proof. by destruct i. Qed.
Lemma Plookup_singleton {A} i (x : A) : Psingleton_raw i x !! i = Some x.
Proof. by induction i. Qed.
Lemma Plookup_singleton_ne {A} i j (x : A) :
  i ≠ j → Psingleton_raw i x !! j = None.
Proof. revert j. induction i; intros [?|?|]; simpl; auto with congruence. Qed.
Lemma Plookup_alter {A} f i (t : Pmap_raw A) :
  Ppartial_alter_raw f i t !! i = f (t !! i).
Proof.
  revert i; induction t as [|o l IHl r IHr]; intros i; simpl.
  - by destruct (f None); rewrite ?Plookup_singleton.
  - destruct i; simpl; rewrite PNode_lookup; simpl; auto.
Qed.
Lemma Plookup_alter_ne {A} f i j (t : Pmap_raw A) :
  i ≠ j → Ppartial_alter_raw f i t !! j = t !! j.
Proof.
  revert i j; induction t as [|o l IHl r IHr]; simpl.
  - by intros; destruct (f None); rewrite ?Plookup_singleton_ne.
  - by intros [?|?|] [?|?|] ?; simpl; rewrite ?PNode_lookup; simpl; auto.
Qed.
Lemma Plookup_fmap {A B} (f : A → B) t i : (Pfmap_raw f t) !! i = f <$> t !! i.
Proof. revert i. by induction t; intros [?|?|]; simpl. Qed.
Lemma Pelem_of_to_list {A} (t : Pmap_raw A) j i acc x :
  (i,x) ∈ Pto_list_raw j t acc ↔
    (∃ i', i = i' ++ Preverse j ∧ t !! i' = Some x) ∨ (i,x) ∈ acc.
Proof.
  split.
  { revert j acc. induction t as [|[y|] l IHl r IHr]; intros j acc; simpl.
    - by right.
    - rewrite elem_of_cons. intros [?|?]; simplify_eq.
      { left; exists 1. by rewrite (left_id_L 1 (++))%positive. }
      destruct (IHl (j~0) (Pto_list_raw j~1 r acc)) as [(i'&->&?)|?]; auto.
      { left; exists (i' ~ 0). by rewrite Preverse_xO, (assoc_L _). }
      destruct (IHr (j~1) acc) as [(i'&->&?)|?]; auto.
      left; exists (i' ~ 1). by rewrite Preverse_xI, (assoc_L _).
    - intros.
      destruct (IHl (j~0) (Pto_list_raw j~1 r acc)) as [(i'&->&?)|?]; auto.
      { left; exists (i' ~ 0). by rewrite Preverse_xO, (assoc_L _). }
      destruct (IHr (j~1) acc) as [(i'&->&?)|?]; auto.
      left; exists (i' ~ 1). by rewrite Preverse_xI, (assoc_L _). }
  revert t j i acc. assert (∀ t j i acc,
    (i, x) ∈ acc → (i, x) ∈ Pto_list_raw j t acc) as help.
  { intros t; induction t as [|[y|] l IHl r IHr]; intros j i acc;
      simpl; rewrite ?elem_of_cons; auto. }
  intros t j ? acc [(i&->&Hi)|?]; [|by auto]. revert j i acc Hi.
  induction t as [|[y|] l IHl r IHr]; intros j i acc ?; simpl.
  - done.
  - rewrite elem_of_cons. destruct i as [i|i|]; simplify_eq/=.
    + right. apply help. specialize (IHr (j~1) i).
      rewrite Preverse_xI, (assoc_L _) in IHr. by apply IHr.
    + right. specialize (IHl (j~0) i).
      rewrite Preverse_xO, (assoc_L _) in IHl. by apply IHl.
    + left. by rewrite (left_id_L 1 (++))%positive.
  - destruct i as [i|i|]; simplify_eq/=.
    + apply help. specialize (IHr (j~1) i).
      rewrite Preverse_xI, (assoc_L _) in IHr. by apply IHr.
    + specialize (IHl (j~0) i).
      rewrite Preverse_xO, (assoc_L _) in IHl. by apply IHl.
Qed.
Lemma Pto_list_nodup {A} j (t : Pmap_raw A) acc :
  (∀ i x, (i ++ Preverse j, x) ∈ acc → t !! i = None) →
  NoDup acc → NoDup (Pto_list_raw j t acc).
Proof.
  revert j acc. induction t as [|[y|] l IHl r IHr]; simpl; intros j acc Hin ?.
  - done.
  - repeat constructor.
    { rewrite Pelem_of_to_list. intros [(i&Hi&?)|Hj].
      { apply (f_equal Plength) in Hi.
        rewrite Preverse_xO, !Papp_length in Hi; simpl in *; lia. }
      rewrite Pelem_of_to_list in Hj. destruct Hj as [(i&Hi&?)|Hj].
      { apply (f_equal Plength) in Hi.
        rewrite Preverse_xI, !Papp_length in Hi; simpl in *; lia. }
      specialize (Hin 1 y). rewrite (left_id_L 1 (++))%positive in Hin.
      discriminate (Hin Hj). }
    apply IHl.
    { intros i x. rewrite Pelem_of_to_list. intros [(?&Hi&?)|Hi].
      + rewrite Preverse_xO, Preverse_xI, !(assoc_L _) in Hi.
        by apply (inj (.++ _)) in Hi.
      + apply (Hin (i~0) x). by rewrite Preverse_xO, (assoc_L _) in Hi. }
    apply IHr; auto. intros i x Hi.
    apply (Hin (i~1) x). by rewrite Preverse_xI, (assoc_L _) in Hi.
  - apply IHl.
    { intros i x. rewrite Pelem_of_to_list. intros [(?&Hi&?)|Hi].
      + rewrite Preverse_xO, Preverse_xI, !(assoc_L _) in Hi.
        by apply (inj (.++ _)) in Hi.
      + apply (Hin (i~0) x). by rewrite Preverse_xO, (assoc_L _) in Hi. }
    apply IHr; auto. intros i x Hi.
    apply (Hin (i~1) x). by rewrite Preverse_xI, (assoc_L _) in Hi.
Qed.
Lemma Pomap_lookup {A B} (f : A → option B) t i :
  Pomap_raw f t !! i = t !! i ≫= f.
Proof.
  revert i. induction t as [|o l IHl r IHr]; intros [i|i|]; simpl;
    rewrite ?PNode_lookup; simpl; auto.
Qed.
Lemma Pmerge_lookup {A B C} (f : option A → option B → option C) t1 t2 i :
  Pmerge_raw f t1 t2 !! i = diag_None f (t1 !! i) (t2 !! i).
Proof.
  revert t2 i; induction t1 as [|o1 l1 IHl1 r1 IHr1]; intros t2 i; simpl.
  { rewrite Pomap_lookup. by destruct (t2 !! i). }
  unfold compose, flip.
  destruct t2 as [|o2 l2 r2]; rewrite PNode_lookup.
  - by destruct i; rewrite ?Pomap_lookup; simpl; rewrite ?Pomap_lookup;
      match goal with |- ?o ≫= _ = _ => destruct o end.
  - destruct i; rewrite ?Pomap_lookup; simpl; auto.
Qed.

(** Packed version and instance of the finite map type class *)
Inductive Pmap (A : Type) : Type :=
  PMap { pmap_car : Pmap_raw A; pmap_prf : Pmap_wf pmap_car }.
Global Arguments PMap {_} _ _ : assert.
Global Arguments pmap_car {_} _ : assert.
Global Arguments pmap_prf {_} _ : assert.
Lemma Pmap_eq {A} (m1 m2 : Pmap A) : m1 = m2 ↔ pmap_car m1 = pmap_car m2.
Proof.
  split; [by intros ->|intros]; destruct m1 as [t1 ?], m2 as [t2 ?].
  simplify_eq/=; f_equal; apply proof_irrel.
Qed.
Global Instance Pmap_eq_dec `{EqDecision A} : EqDecision (Pmap A) := λ m1 m2,
  match Pmap_raw_eq_dec (pmap_car m1) (pmap_car m2) with
  | left H => left (proj2 (Pmap_eq m1 m2) H)
  | right H => right (H ∘ proj1 (Pmap_eq m1 m2))
  end.
Global Instance Pempty {A} : Empty (Pmap A) := PMap ∅ I.
Global Instance Plookup {A} : Lookup positive A (Pmap A) := λ i m, pmap_car m !! i.
Global Instance Ppartial_alter {A} : PartialAlter positive A (Pmap A) := λ f i m,
  let (t,Ht) := m in PMap (partial_alter f i t) (Ppartial_alter_wf f i _ Ht).
Global Instance Pfmap : FMap Pmap := λ A B f m,
  let (t,Ht) := m in PMap (f <$> t) (Pfmap_wf f _ Ht).
Global Instance Pto_list {A} : FinMapToList positive A (Pmap A) := λ m,
  let (t,Ht) := m in Pto_list_raw 1 t [].
Global Instance Pomap : OMap Pmap := λ A B f m,
  let (t,Ht) := m in PMap (omap f t) (Pomap_wf f _ Ht).
Global Instance Pmerge : Merge Pmap := λ A B C f m1 m2,
  let (t1,Ht1) := m1 in let (t2,Ht2) := m2 in PMap _ (Pmerge_wf f _ _ Ht1 Ht2).

Global Instance Pmap_finmap : FinMap positive Pmap.
Proof.
  split.
  - by intros ? [t1 ?] [t2 ?] ?; apply Pmap_eq, Pmap_wf_eq.
  - by intros ? [].
  - intros ?? [??] ?. by apply Plookup_alter.
  - intros ?? [??] ??. by apply Plookup_alter_ne.
  - intros ??? [??]. by apply Plookup_fmap.
  - intros ? [??]. apply Pto_list_nodup; [|constructor].
    intros ??. by rewrite elem_of_nil.
  - intros ? [??] i x; unfold map_to_list, Pto_list.
    rewrite Pelem_of_to_list, elem_of_nil.
    split.
    + by intros [(?&->&?)|].
    + by left; exists i.
  - intros ?? ? [??] ?. by apply Pomap_lookup.
  - intros ??? ? [??] [??] ?. by apply Pmerge_lookup.
Qed.

Global Program Instance Pmap_countable `{Countable A} : Countable (Pmap A) := {
  encode m := encode (map_to_list m : list (positive * A));
  decode p := list_to_map <$> decode p
}.
Next Obligation.
  intros A ?? m; simpl. rewrite decode_encode; simpl. by rewrite list_to_map_to_list.
Qed.

(** * Finite sets *)
(** We construct sets of [positives]s satisfying extensional equality. *)
Notation Pset := (mapset Pmap).
Global Instance Pmap_dom {A} : Dom (Pmap A) Pset := mapset_dom.
Global Instance Pmap_dom_spec : FinMapDom positive Pmap Pset := mapset_dom_spec.
