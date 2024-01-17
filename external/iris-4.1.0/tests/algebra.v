From iris.algebra Require Import auth excl lib.gmap_view.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.

Section test_dist_equiv_mode.
  (* check that the mode for [Dist] does not trigger https://github.com/coq/coq/issues/14441.
  From https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/700#note_69303. *)
  Lemma list_dist_lookup {A : ofe} n (l1 l2 : list A) :
    l1 ≡{n}≡ l2 ↔ ∀ i, l1 !! i ≡{n}≡ l2 !! i.
  Abort.

  (* analogous test for [Equiv] and https://github.com/coq/coq/issues/14441.
  From https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/700#note_69303. *)
  Lemma list_equiv_lookup_ofe {A : ofe} (l1 l2 : list A) :
    l1 ≡ l2 ↔ ∀ i, l1 !! i ≡ l2 !! i.
  Abort.
End test_dist_equiv_mode.

(** Make sure that the same [Equivalence] instance is picked for Leibniz OFEs
with carriers that are definitionally equal. See also
https://gitlab.mpi-sws.org/iris/iris/issues/299 *)
Definition tag := nat.
Canonical Structure tagO := leibnizO tag.
Goal tagO = natO.
Proof. reflexivity. Qed.

Global Instance test_cofe {Σ} : Cofe (iPrePropO Σ) := _.

Section tests.
  Context `{!invGS_gen hlc Σ}.

  Program Definition test : (iPropO Σ -n> iPropO Σ) -n> (iPropO Σ -n> iPropO Σ) :=
    λne P v, (▷ (P v))%I.
  Solve Obligations with solve_proper.

End tests.

(** Check that [@Reflexive Prop ?r] picks the instance setoid_rewrite needs.
    Really, we want to set [Hint Mode Reflexive] in a way that this fails, but
    we cannot [1].  So at least we try to make sure the first solution found
    is the right one, to not pay performance in the success case [2].

    [1] https://github.com/coq/coq/issues/7916
    [2] https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp/merge_requests/38
*)
Lemma test_setoid_rewrite :
  ∃ R, @Reflexive Prop R ∧ R = iff.
Proof.
  eexists. split.
  - apply _.
  - reflexivity.
Qed.

(** Regression test for <https://gitlab.mpi-sws.org/iris/iris/issues/255>. *)
Definition testR := authR (prodUR
        (prodUR
          (optionUR (exclR unitO))
          (optionUR (exclR unitO)))
        (optionUR (agreeR (boolO)))).
Section test_prod.
  Context `{!inG Σ testR}.
  Lemma test_prod_persistent γ :
    Persistent (PROP:=iPropI Σ) (own γ (◯((None, None), Some (to_agree true)))).
  Proof. apply _. Qed.
End test_prod.

(** Make sure the [auth]/[gmap_view] notation does not mix up its arguments. *)
Definition auth_check {A : ucmra} :
  auth A = authO A := eq_refl.
Definition gmap_view_check {K : Type} `{Countable K} {V : ofe} :
  gmap_view K V = gmap_viewO K V := eq_refl.

Lemma uncurry_ne_test {A B C : ofe} (f : A → B → C) :
  NonExpansive2 f → NonExpansive (uncurry f).
Proof. apply _. Qed.
Lemma uncurry3_ne_test {A B C D : ofe} (f : A → B → C → D) :
  NonExpansive3 f → NonExpansive (uncurry3 f).
Proof. apply _. Qed.
Lemma uncurry4_ne_test {A B C D E : ofe} (f : A → B → C → D → E) :
  NonExpansive4 f → NonExpansive (uncurry4 f).
Proof. apply _. Qed.

Lemma curry_ne_test {A B C : ofe} (f : A * B → C) :
  NonExpansive f → NonExpansive2 (curry f).
Proof. apply _. Qed.
Lemma curry3_ne_test {A B C D : ofe} (f : A * B * C → D) :
  NonExpansive f → NonExpansive3 (curry3 f).
Proof. apply _. Qed.
Lemma curry4_ne_test {A B C D E : ofe} (f : A * B * C * D → E) :
  NonExpansive f → NonExpansive4 (curry4 f).
Proof. apply _. Qed.
