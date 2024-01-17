From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From iris.prelude Require Import options.

(** Given a preorder [R] on a type [A] we construct the "monotone" resource
algebra [mra R] and an injection [to_mra : A → mra R] such that:

   [R x y] iff [to_mra x ≼ to_mra y]

Here, [≼] is the extension order of the [mra R] resource algebra. This is
exactly what the lemma [to_mra_included] shows.

This resource algebra is useful for reasoning about monotonicity. See the
following paper for more details ([to_mra] is called "principal"):

  Reasoning About Monotonicity in Separation Logic
  Amin Timany and Lars Birkedal
  in Certified Programs and Proofs (CPP) 2021

Note that unlike most Iris algebra constructions [mra A] works on [A : Type],
not on [A : ofe]. See the comment at [mraO] below for more information. If [A]
has an [Equiv A] (i.e., is a setoid), there are some results at the bottom of
this file. *)
Record mra {A} (R : relation A) := { mra_car : list A }.
Definition to_mra {A} {R : relation A} (a : A) : mra R :=
  {| mra_car := [a] |}.
Global Arguments mra_car {_ _} _.

Section mra.
  Context {A} {R : relation A}.
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  (** Pronounced [a] is below [x]. *)
  Local Definition mra_below (a : A) (x : mra R) := ∃ b, b ∈ mra_car x ∧ R a b.

  Local Lemma mra_below_to_mra a b : mra_below a (to_mra b) ↔ R a b.
  Proof. set_solver. Qed.

  (* OFE *)
  Local Instance mra_equiv : Equiv (mra R) := λ x y,
    ∀ a, mra_below a x ↔ mra_below a y.

  Local Instance mra_equiv_equiv : Equivalence mra_equiv.
  Proof. unfold mra_equiv; split; intros ?; naive_solver. Qed.

  (** Generalizing [mra A] to [A : ofe] and [R : A -n> A -n> siProp] is not
  obvious. It is not clear what axioms to impose on [R] for the "extension
  axiom" to hold:

    cmra_extend :
      x ≡{n}≡ y1 ⋅ y2 →
      ∃ z1 z2, x ≡ z1 ⋅ z2 ∧ y1 ≡{n}≡ z1 ∧ y2 ≡{n}≡ z2

  To prove this, assume ([⋅] is defined as [++], see [mra_op]):

    x ≡{n}≡ y1 ++ y2

  When defining [dist] as the step-indexed version of [mra_equiv], this means:

    ∀ n' a, n' ≤ n →
            mra_below a x n' ↔ mra_below a y1 n' ∨ mra_below a y2 n'

  From this assumption it is not clear how to obtain witnesses [z1] and [z2]. *)
  Canonical Structure mraO := discreteO (mra R).

  (* CMRA *)
  Local Instance mra_valid : Valid (mra R) := λ x, True.
  Local Instance mra_validN : ValidN (mra R) := λ n x, True.
  Local Program Instance mra_op : Op (mra R) := λ x y,
    {| mra_car := mra_car x ++ mra_car y |}.
  Local Instance mra_pcore : PCore (mra R) := Some.

  Lemma mra_cmra_mixin : CmraMixin (mra R).
  Proof.
    apply discrete_cmra_mixin; first apply _.
    apply ra_total_mixin; try done.
    - (* [Proper] of [op] *) intros x y z Hyz a. specialize (Hyz a). set_solver.
    - (* [Proper] of [core] *) apply _.
    - (* [Assoc] *) intros x y z a. set_solver.
    - (* [Comm] *) intros x y a. set_solver.
    - (* [core x ⋅ x ≡ x] *) intros x a. set_solver.
  Qed.

  Canonical Structure mraR : cmra := Cmra (mra R) mra_cmra_mixin.

  Global Instance mra_cmra_total : CmraTotal mraR.
  Proof. rewrite /CmraTotal; eauto. Qed.
  Global Instance mra_core_id x : CoreId x.
  Proof. by constructor. Qed.

  Global Instance mra_cmra_discrete : CmraDiscrete mraR.
  Proof. split; last done. intros ? ?; done. Qed.

  Local Instance mra_unit : Unit (mra R) := {| mra_car := [] |}.
  Lemma auth_ucmra_mixin : UcmraMixin (mra R).
  Proof. split; done. Qed.

  Canonical Structure mraUR := Ucmra (mra R) auth_ucmra_mixin.

  (* Laws *)
  Lemma mra_idemp x : x ⋅ x ≡ x.
  Proof. intros a. set_solver. Qed.

  Lemma mra_included x y : x ≼ y ↔ y ≡ x ⋅ y.
  Proof.
    split; [|by intros ?; exists y].
    intros [z ->]; rewrite assoc mra_idemp; done.
  Qed.

  Lemma to_mra_R_op `{!Transitive R} a b :
    R a b →
    to_mra a ⋅ to_mra b ≡ to_mra b.
  Proof. intros Hab c. set_solver. Qed.

  Lemma to_mra_included `{!PreOrder R} a b :
    to_mra a ≼ to_mra b ↔ R a b.
  Proof.
    split.
    - move=> [z Hz]. specialize (Hz a). set_solver.
    - intros ?; exists (to_mra b). by rewrite to_mra_R_op.
  Qed.

  Lemma mra_local_update_grow `{!Transitive R} a x b:
    R a b →
    (to_mra a, x) ~l~> (to_mra b, to_mra b).
  Proof.
    intros Hana. apply local_update_unital_discrete=> z _ Habz.
    split; first done. intros c. specialize (Habz c). set_solver.
  Qed.

  Lemma mra_local_update_get_frag `{!PreOrder R} a b:
    R b a →
    (to_mra a, ε) ~l~> (to_mra a, to_mra b).
  Proof.
    intros Hana. apply local_update_unital_discrete=> z _.
    rewrite left_id. intros <-. split; first done.
    apply mra_included; by apply to_mra_included.
  Qed.
End mra.

Global Arguments mraO {_} _.
Global Arguments mraR {_} _.
Global Arguments mraUR {_} _.

(** If [R] is a partial order, relative to a reflexive relation [S] on the
carrier [A], then [to_mra] is proper and injective. The theory for
arbitrary relations [S] is overly general, so we do not declare the results
as instances. Below we provide instances for [S] being [=] and [≡]. *)
Section mra_over_rel.
  Context {A} {R : relation A} (S : relation A).
  Implicit Types a b : A.
  Implicit Types x y : mra R.

  Lemma to_mra_rel_proper :
    Reflexive S →
    Proper (S ==> S ==> iff) R →
    Proper (S ==> (≡@{mra R})) (to_mra).
  Proof. intros ? HR a1 a2 Ha b. rewrite !mra_below_to_mra. by apply HR. Qed.

  Lemma to_mra_rel_inj :
    Reflexive R →
    AntiSymm S R →
    Inj S (≡@{mra R}) (to_mra).
  Proof.
    intros ?? a b Hab. move: (Hab a) (Hab b). rewrite !mra_below_to_mra.
    intros. apply (anti_symm R); naive_solver.
  Qed.
End mra_over_rel.

Global Instance to_mra_inj {A} {R : relation A} :
  Reflexive R →
  AntiSymm (=) R →
  Inj (=) (≡@{mra R}) (to_mra) | 0. (* Lower cost than [to_mra_equiv_inj] *)
Proof. intros. by apply (to_mra_rel_inj (=)). Qed.

Global Instance to_mra_proper `{Equiv A} {R : relation A} :
  Reflexive (≡@{A}) →
  Proper ((≡) ==> (≡) ==> iff) R →
  Proper ((≡) ==> (≡@{mra R})) (to_mra).
Proof. intros. by apply (to_mra_rel_proper (≡)). Qed.

Global Instance to_mra_equiv_inj `{Equiv A} {R : relation A} :
  Reflexive R →
  AntiSymm (≡) R →
  Inj (≡) (≡@{mra R}) (to_mra) | 1.
Proof. intros. by apply (to_mra_rel_inj (≡)). Qed.
