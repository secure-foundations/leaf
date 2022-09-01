(** RA for monotone partial bijections.

This RA is a view where the authoritative element is a partial bijection between
types [A] and [B] and the fragments are subrels of the bijection. The data for
the bijection is represented as a set of pairs [A * B], and the view relation
enforces when an authoritative element is valid it is a bijection (that is, it
is deterministic as a function from [A → option B] and [B → option A]).

The fragments compose by set union, which means that fragments are their own
core, ownership of a fragment is persistent, and the authoritative element can
only grow (in that it can only map more pairs [(a,b)]). *)

(* [algebra.view] needs to be exported for the canonical instances *)
From iris.algebra Require Export view gset.
From iris.algebra Require Import updates.
From iris.prelude Require Import options.

Section gset_bijective.
  Context `{Countable A, Countable B}.
  Implicit Types (a : A) (b : B).

  (** [gset_bijective] states that for a graph [L] of [(a, b)] pairs, [L] maps
  from [A] to [B] and back deterministically. The key property characterizing
  [gset_bijective] is [gset_bijective_eq_iff]. *)
  Definition gset_bijective (L : gset (A * B)) :=
    ∀ a b, (a, b) ∈ L →
    (∀ b', (a, b') ∈ L → b' = b) ∧ (∀ a', (a', b) ∈ L → a' = a).

  (* Properties of [gset_bijective]. *)
  Lemma gset_bijective_empty : gset_bijective (∅ : gset (A * B)).
  Proof. by intros ?? []%not_elem_of_empty. Qed.

  (* a bijective graph [L] can be extended with a new mapping [(a,b)] as long as
  neither [a] nor [b] is currently mapped to anything. *)
  Lemma gset_bijective_extend L a b :
    gset_bijective L →
    (∀ b', (a, b') ∉ L) →
    (∀ a', (a', b) ∉ L) →
    gset_bijective ({[(a, b)]} ∪ L).
  Proof. rewrite /gset_bijective. set_solver. Qed.

  Lemma gset_bijective_eq_iff L (a1 a2 : A) (b1 b2 : B) :
    gset_bijective L →
    (a1, b1) ∈ L →
    (a2, b2) ∈ L →
    a1 = a2 ↔ b1 = b2.
  Proof. rewrite /gset_bijective. set_solver. Qed.

  Lemma gset_bijective_pair a1 b1 a2 b2 :
    gset_bijective {[(a1, b1); (a2, b2)]} →
    (a1 = a2 ↔ b1 = b2).
  Proof. rewrite /gset_bijective. set_solver. Qed.

  Lemma subseteq_gset_bijective L L' :
    gset_bijective L →
    L' ⊆ L →
    gset_bijective L'.
  Proof. rewrite /gset_bijective. set_solver. Qed.
End gset_bijective.

Section gset_bij_view_rel.
  Context `{Countable A, Countable B}.
  Implicit Types (bijL : gset (A * B)) (L : gsetUR (A * B)).

  Local Definition gset_bij_view_rel_raw (n : nat) bijL L: Prop :=
    L ⊆ bijL ∧ gset_bijective bijL.

  Local Lemma gset_bij_view_rel_raw_mono n1 n2 bijL1 bijL2 L1 L2 :
    gset_bij_view_rel_raw n1 bijL1 L1 →
    bijL1 ≡{n2}≡ bijL2 →
    L2 ≼{n2} L1 →
    n2 ≤ n1 →
    gset_bij_view_rel_raw n2 bijL2 L2.
  Proof.
    intros [??] <-%(discrete_iff _ _)%leibniz_equiv ?%gset_included _.
    split; [|done]. by trans L1.
  Qed.

  Local Lemma gset_bij_view_rel_raw_valid n bijL L :
    gset_bij_view_rel_raw n bijL L → ✓{n}L.
  Proof. by intros _. Qed.

  Local Lemma gset_bij_view_rel_raw_unit n :
    ∃ bijL, gset_bij_view_rel_raw n bijL ε.
  Proof. exists ∅. split; eauto using gset_bijective_empty. Qed.

  Canonical Structure gset_bij_view_rel : view_rel (gsetO (A * B)) (gsetUR (A * B)) :=
    ViewRel gset_bij_view_rel_raw gset_bij_view_rel_raw_mono
            gset_bij_view_rel_raw_valid gset_bij_view_rel_raw_unit.

  Global Instance gset_bij_view_rel_discrete : ViewRelDiscrete gset_bij_view_rel.
  Proof. intros n bijL L [??]. split; auto. Qed.

  Local Lemma gset_bij_view_rel_iff n bijL L :
    gset_bij_view_rel n bijL L ↔ L ⊆ bijL ∧ gset_bijective bijL.
  Proof. done. Qed.
End gset_bij_view_rel.

Definition gset_bij A B `{Countable A, Countable B} :=
  view (gset_bij_view_rel_raw (A:=A) (B:=B)).
Definition gset_bijO A B `{Countable A, Countable B} : ofe :=
  viewO (gset_bij_view_rel (A:=A) (B:=B)).
Definition gset_bijR A B `{Countable A, Countable B} : cmra :=
  viewR (gset_bij_view_rel (A:=A) (B:=B)).
Definition gset_bijUR A B `{Countable A, Countable B} : ucmra :=
  viewUR (gset_bij_view_rel (A:=A) (B:=B)).

Definition gset_bij_auth `{Countable A, Countable B}
  (dq : dfrac) (L : gset (A * B)) : gset_bij A B := ●V{dq} L ⋅ ◯V L.
Definition gset_bij_elem `{Countable A, Countable B}
  (a : A) (b : B) : gset_bij A B := ◯V {[ (a, b) ]}.

Section gset_bij.
  Context `{Countable A, Countable B}.
  Implicit Types (a:A) (b:B).
  Implicit Types (L : gset (A*B)).
  Implicit Types dq : dfrac.

  Global Instance gset_bij_elem_core_id a b : CoreId (gset_bij_elem a b).
  Proof. apply _. Qed.

  Lemma gset_bij_auth_dfrac_op dq1 dq2 L :
    gset_bij_auth dq1 L ⋅ gset_bij_auth dq2 L ≡ gset_bij_auth (dq1 ⋅ dq2) L.
  Proof.
    rewrite /gset_bij_auth view_auth_dfrac_op.
    rewrite (comm _ (●V{dq2} _)) -!assoc (assoc _ (◯V _)).
    by rewrite -core_id_dup (comm _ (◯V _)).
  Qed.

  Lemma gset_bij_auth_dfrac_valid dq L : ✓ gset_bij_auth dq L ↔ ✓ dq ∧ gset_bijective L.
  Proof.
    rewrite /gset_bij_auth view_both_dfrac_valid.
    setoid_rewrite gset_bij_view_rel_iff.
    naive_solver eauto using O.
  Qed.
  Lemma gset_bij_auth_valid L : ✓ gset_bij_auth (DfracOwn 1) L ↔ gset_bijective L.
  Proof. rewrite gset_bij_auth_dfrac_valid. naive_solver by done. Qed.

  Lemma gset_bij_auth_empty_dfrac_valid dq : ✓ gset_bij_auth (A:=A) (B:=B) dq ∅ ↔ ✓ dq.
  Proof.
    rewrite gset_bij_auth_dfrac_valid. naive_solver eauto using gset_bijective_empty.
  Qed.
  Lemma gset_bij_auth_empty_valid : ✓ gset_bij_auth (A:=A) (B:=B) (DfracOwn 1) ∅.
  Proof. by apply gset_bij_auth_empty_dfrac_valid. Qed.

  Lemma gset_bij_auth_dfrac_op_valid dq1 dq2 L1 L2 :
    ✓ (gset_bij_auth dq1 L1 ⋅ gset_bij_auth dq2 L2)
    ↔ ✓ (dq1 ⋅ dq2) ∧ L1 = L2 ∧ gset_bijective L1.
  Proof.
    rewrite /gset_bij_auth (comm _ (●V{dq2} _)) -!assoc (assoc _ (◯V _)).
    rewrite -view_frag_op (comm _ (◯V _)) assoc. split.
    - move=> /cmra_valid_op_l /view_auth_dfrac_op_valid.
      setoid_rewrite gset_bij_view_rel_iff. naive_solver eauto using 0.
    - intros (?&->&?). rewrite -core_id_dup -view_auth_dfrac_op.
      apply view_both_dfrac_valid. setoid_rewrite gset_bij_view_rel_iff. naive_solver.
  Qed.
  Lemma gset_bij_auth_op_valid L1 L2 :
    ✓ (gset_bij_auth (DfracOwn 1) L1 ⋅ gset_bij_auth (DfracOwn 1) L2) ↔ False.
  Proof. rewrite gset_bij_auth_dfrac_op_valid. naive_solver. Qed.

  Lemma bij_both_dfrac_valid dq L a b :
    ✓ (gset_bij_auth dq L ⋅ gset_bij_elem a b) ↔ ✓ dq ∧ gset_bijective L ∧ (a, b) ∈ L.
  Proof.
    rewrite /gset_bij_auth /gset_bij_elem -assoc -view_frag_op view_both_dfrac_valid.
    setoid_rewrite gset_bij_view_rel_iff.
    set_solver by eauto using O.
  Qed.
  Lemma bij_both_valid L a b :
    ✓ (gset_bij_auth (DfracOwn 1) L ⋅ gset_bij_elem a b) ↔ gset_bijective L ∧ (a, b) ∈ L.
  Proof. rewrite bij_both_dfrac_valid. naive_solver by done. Qed.

  Lemma gset_bij_elem_agree a1 b1 a2 b2 :
    ✓ (gset_bij_elem a1 b1 ⋅ gset_bij_elem a2 b2) → (a1 = a2 ↔ b1 = b2).
  Proof.
    rewrite /gset_bij_elem -view_frag_op gset_op view_frag_valid.
    setoid_rewrite gset_bij_view_rel_iff. intros. apply gset_bijective_pair.
    naive_solver eauto using subseteq_gset_bijective, O.
  Qed.

  Lemma bij_view_included dq L a b :
    (a,b) ∈ L → gset_bij_elem a b ≼ gset_bij_auth dq L.
  Proof.
    intros. etrans; [|apply cmra_included_r].
    apply view_frag_mono, gset_included. set_solver.
  Qed.

  Lemma gset_bij_auth_extend {L} a b :
    (∀ b', (a, b') ∉ L) → (∀ a', (a', b) ∉ L) →
    gset_bij_auth (DfracOwn 1) L ~~> gset_bij_auth (DfracOwn 1) ({[(a, b)]} ∪ L).
  Proof.
    intros. apply view_update=> n bijL.
    rewrite !gset_bij_view_rel_iff gset_op.
    set_solver by eauto using gset_bijective_extend.
  Qed.
End gset_bij.
