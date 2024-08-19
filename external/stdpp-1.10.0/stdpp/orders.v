(** Properties about arbitrary pre-, partial, and total orders. We do not use
the relation [⊆] because we often have multiple orders on the same structure *)
From stdpp Require Export tactics.
From stdpp Require Import options.

Section orders.
  Context {A} {R : relation A}.
  Implicit Types X Y : A.
  Infix "⊆" := R.
  Notation "X ⊈ Y" := (¬X ⊆ Y).
  Infix "⊂" := (strict R).

  Lemma reflexive_eq `{!Reflexive R} X Y : X = Y → X ⊆ Y.
  Proof. by intros <-. Qed.
  Lemma anti_symm_iff `{!PartialOrder R} X Y : X = Y ↔ R X Y ∧ R Y X.
  Proof. split; [by intros ->|]. by intros [??]; apply (anti_symm R). Qed.
  Lemma strict_spec X Y : X ⊂ Y ↔ X ⊆ Y ∧ Y ⊈ X.
  Proof. done. Qed.
  Lemma strict_include X Y : X ⊂ Y → X ⊆ Y.
  Proof. by intros [? _]. Qed.
  Lemma strict_ne X Y : X ⊂ Y → X ≠ Y.
  Proof. by intros [??] <-. Qed.
  Lemma strict_ne_sym X Y : X ⊂ Y → Y ≠ X.
  Proof. by intros [??] <-. Qed.
  Lemma strict_transitive_l `{!Transitive R} X Y Z : X ⊂ Y → Y ⊆ Z → X ⊂ Z.
  Proof.
    intros [? HXY] ?. split; [by trans Y|].
    contradict HXY. by trans Z.
  Qed.
  Lemma strict_transitive_r `{!Transitive R} X Y Z : X ⊆ Y → Y ⊂ Z → X ⊂ Z.
  Proof.
    intros ? [? HYZ]. split; [by trans Y|].
    contradict HYZ. by trans X.
  Qed.
  Global Instance: Irreflexive (strict R).
  Proof. firstorder. Qed.
  Global Instance: Transitive R → StrictOrder (strict R).
  Proof.
    split; try apply _.
    eauto using strict_transitive_r, strict_include.
  Qed.
  Global Instance preorder_subset_dec_slow `{!RelDecision R} :
    RelDecision (strict R) | 100.
  Proof. solve_decision. Defined.
  Lemma strict_spec_alt `{!AntiSymm (=) R} X Y : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y.
  Proof.
    split.
    - intros [? HYX]. split; [ done | by intros <- ].
    - intros [? HXY]. split; [ done | by contradict HXY; apply (anti_symm R) ].
  Qed.
  Lemma po_eq_dec `{!PartialOrder R, !RelDecision R} : EqDecision A.
  Proof.
    refine (λ X Y, cast_if_and (decide (X ⊆ Y)) (decide (Y ⊆ X)));
     abstract (rewrite anti_symm_iff; tauto).
  Defined.
  Lemma total_not `{!Total R} X Y : X ⊈ Y → Y ⊆ X.
  Proof. intros. destruct (total R X Y); tauto. Qed.
  Lemma total_not_strict `{!Total R} X Y : X ⊈ Y → Y ⊂ X.
  Proof. red; auto using total_not. Qed.
  Global Instance trichotomy_total
    `{!Trichotomy (strict R), !Reflexive R} : Total R.
  Proof.
    intros X Y.
    destruct (trichotomy (strict R) X Y) as [[??]|[<-|[??]]]; intuition.
  Qed.
End orders.

Section strict_orders.
  Context {A} {R : relation A}.
  Implicit Types X Y : A.
  Infix "⊂" := R.

  Lemma irreflexive_eq `{!Irreflexive R} X Y : X = Y → ¬X ⊂ Y.
  Proof. intros ->. apply (irreflexivity R). Qed.
  Lemma strict_anti_symm `{!StrictOrder R} X Y :
    X ⊂ Y → Y ⊂ X → False.
  Proof. intros. apply (irreflexivity R X). by trans Y. Qed.
  Global Instance trichotomyT_dec `{!TrichotomyT R, !StrictOrder R} :
      RelDecision R := λ X Y,
    match trichotomyT R X Y with
    | inleft (left H) => left H
    | inleft (right H) => right (irreflexive_eq _ _ H)
    | inright H => right (strict_anti_symm _ _ H)
    end.
  Global Instance trichotomyT_trichotomy `{!TrichotomyT R} : Trichotomy R.
  Proof. intros X Y. destruct (trichotomyT R X Y) as [[|]|]; tauto. Qed.
End strict_orders.

Ltac simplify_order := repeat
  match goal with
  | _ => progress simplify_eq/=
  | H : ?R ?x ?x |- _ => by destruct (irreflexivity _ _ H)
  | H1 : ?R ?x ?y |- _ =>
    match goal with
    | H2 : R y x |- _ =>
      assert (x = y) by (by apply (anti_symm R)); clear H1 H2
    | H2 : R y ?z |- _ =>
      unless (R x z) by done;
      assert (R x z) by (by trans y)
    end
  end.
