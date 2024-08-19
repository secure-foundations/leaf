From stdpp Require Export countable coPset.
From stdpp Require Import options.

Definition namespace := list positive.
Global Instance namespace_eq_dec : EqDecision namespace := _.
Global Instance namespace_countable : Countable namespace := _.
Global Typeclasses Opaque namespace.

Definition nroot : namespace := nil.

Local Definition ndot_def `{Countable A} (N : namespace) (x : A) : namespace :=
  encode x :: N.
Local Definition ndot_aux : seal (@ndot_def). by eexists. Qed.
Definition ndot {A A_dec A_count}:= unseal ndot_aux A A_dec A_count.
Local Definition ndot_unseal : @ndot = @ndot_def := seal_eq ndot_aux.

Local Definition nclose_def (N : namespace) : coPset :=
  coPset_suffixes (positives_flatten N).
Local Definition nclose_aux : seal (@nclose_def). by eexists. Qed.
Global Instance nclose : UpClose namespace coPset := unseal nclose_aux.
Local Definition nclose_unseal : @nclose = @nclose_def := seal_eq nclose_aux.

Notation "N .@ x" := (ndot N x)
  (at level 19, left associativity, format "N .@ x") : stdpp_scope.
Notation "(.@)" := ndot (only parsing) : stdpp_scope.

Global Instance ndisjoint : Disjoint namespace := λ N1 N2, nclose N1 ## nclose N2.

Section namespace.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types N : namespace.
  Implicit Types E : coPset.

  Global Instance ndot_inj : Inj2 (=) (=) (=) (@ndot A _ _).
  Proof. intros N1 x1 N2 x2; rewrite !ndot_unseal; naive_solver. Qed.

  Lemma nclose_nroot : ↑nroot = (⊤:coPset).
  Proof. rewrite nclose_unseal. by apply (sig_eq_pi _). Qed.

  Lemma nclose_subseteq N x : ↑N.@x ⊆ (↑N : coPset).
  Proof.
    intros p. unfold up_close. rewrite !nclose_unseal, !ndot_unseal.
    unfold nclose_def, ndot_def; rewrite !elem_coPset_suffixes.
    intros [q ->]. destruct (positives_flatten_suffix N (ndot_def N x)) as [q' ?].
    { by exists [encode x]. }
    by exists (q ++ q')%positive; rewrite <-(assoc_L _); f_equal.
  Qed.

  Lemma nclose_subseteq' E N x : ↑N ⊆ E → ↑N.@x ⊆ E.
  Proof. intros. etrans; eauto using nclose_subseteq. Qed.

  Lemma nclose_infinite N : ¬set_finite (↑ N : coPset).
  Proof. rewrite nclose_unseal. apply coPset_suffixes_infinite. Qed.

  Lemma ndot_ne_disjoint N x y : x ≠ y → N.@x ## N.@y.
  Proof.
    intros Hxy a. unfold up_close. rewrite !nclose_unseal, !ndot_unseal.
    unfold nclose_def, ndot_def; rewrite !elem_coPset_suffixes.
    intros [qx ->] [qy Hqy].
    revert Hqy. by intros [= ?%(inj encode)]%positives_flatten_suffix_eq.
  Qed.

  Lemma ndot_preserve_disjoint_l N E x : ↑N ## E → ↑N.@x ## E.
  Proof. intros. pose proof (nclose_subseteq N x). set_solver. Qed.

  Lemma ndot_preserve_disjoint_r N E x : E ## ↑N → E ## ↑N.@x.
  Proof. intros. by apply symmetry, ndot_preserve_disjoint_l. Qed.
End namespace.

(** The hope is that registering these will suffice to solve most goals
of the forms:
- [N1 ## N2]
- [↑N1 ⊆ E ∖ ↑N2 ∖ .. ∖ ↑Nn]
- [E1 ∖ ↑N1 ⊆ E2 ∖ ↑N2 ∖ .. ∖ ↑Nn] *)
Create HintDb ndisj discriminated.

(** Rules for goals of the form [_ ⊆ _] *)
(** If-and-only-if rules. Well, not quite, but for the fragment we are
considering they are. *)
Local Definition coPset_subseteq_difference_r := subseteq_difference_r (C:=coPset).
Global Hint Resolve coPset_subseteq_difference_r : ndisj.
Local Definition coPset_empty_subseteq := empty_subseteq (C:=coPset).
Global Hint Resolve coPset_empty_subseteq : ndisj.
Local Definition coPset_union_least := union_least (C:=coPset).
Global Hint Resolve coPset_union_least : ndisj.
(** For goals like [X ⊆ L ∪ R], backtrack for the two sides. *)
Local Definition coPset_union_subseteq_l' := union_subseteq_l' (C:=coPset).
Global Hint Resolve coPset_union_subseteq_l' | 50 : ndisj.
Local Definition coPset_union_subseteq_r' := union_subseteq_r' (C:=coPset).
Global Hint Resolve coPset_union_subseteq_r' | 50 : ndisj.
(** Fallback, loses lots of information but lets other rules make progress. *)
Local Definition coPset_subseteq_difference_l := subseteq_difference_l (C:=coPset).
Global Hint Resolve coPset_subseteq_difference_l | 100 : ndisj.
Global Hint Resolve nclose_subseteq' | 100 : ndisj.

(** Rules for goals of the form [_ ## _] *)
(** The base rule that we want to ultimately get down to. *)
Global Hint Extern 0 (_ ## _) => apply ndot_ne_disjoint; congruence : ndisj.
(** Trivial cases. *)
Local Definition coPset_disjoint_empty_l := disjoint_empty_l (C:=coPset).
Global Hint Resolve coPset_disjoint_empty_l : ndisj.
Local Definition coPset_disjoint_empty_r := disjoint_empty_r (C:=coPset).
Global Hint Resolve coPset_disjoint_empty_r : ndisj.
(** If-and-only-if rules for ∪ on the left/right. *)
Local Definition coPset_disjoint_union_l X1 X2 Y :=
  proj2 (disjoint_union_l (C:=coPset) X1 X2 Y).
Global Hint Resolve coPset_disjoint_union_l : ndisj.
Local Definition coPset_disjoint_union_r X Y1 Y2 :=
  proj2 (disjoint_union_r (C:=coPset) X Y1 Y2).
Global Hint Resolve coPset_disjoint_union_r : ndisj.
(** We prefer ∖ on the left of ## (for the [disjoint_difference] lemmas to
apply), so try moving it there. *)
Global Hint Extern 10 (_ ## (_ ∖ _)) =>
  lazymatch goal with
  | |- (_ ∖ _) ## _ => fail (* ∖ on both sides, leave it be *)
  | |- _ => symmetry
  end : ndisj.
(** Before we apply disjoint_difference, let's make sure we normalize the goal
to [_ ∖ (_ ∪ _)]. *)
Local Lemma coPset_difference_difference (X1 X2 X3 Y : coPset) :
  X1 ∖ (X2 ∪ X3) ## Y →
  X1 ∖ X2 ∖ X3 ## Y.
Proof. set_solver. Qed.
Global Hint Resolve coPset_difference_difference | 20 : ndisj.
(** Fallback, loses lots of information but lets other rules make progress.
Tests show trying [disjoint_difference_l1] first gives better performance. *)
Local Definition coPset_disjoint_difference_l1 := disjoint_difference_l1 (C:=coPset).
Global Hint Resolve coPset_disjoint_difference_l1 | 50 : ndisj.
Local Definition coPset_disjoint_difference_l2 := disjoint_difference_l2 (C:=coPset).
Global Hint Resolve coPset_disjoint_difference_l2 | 100 : ndisj.
Global Hint Resolve ndot_preserve_disjoint_l ndot_preserve_disjoint_r | 100 : ndisj.

Ltac solve_ndisj :=
  repeat match goal with
  | H : _ ∪ _ ⊆ _ |- _ => apply union_subseteq in H as [??]
  end;
  solve [eauto 12 with ndisj].
Global Hint Extern 1000 => solve_ndisj : solve_ndisj.
