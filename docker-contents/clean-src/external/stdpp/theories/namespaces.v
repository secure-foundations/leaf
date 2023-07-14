From stdpp Require Export countable coPset.
From stdpp Require Import options.

Definition namespace := list positive.
Global Instance namespace_eq_dec : EqDecision namespace := _.
Global Instance namespace_countable : Countable namespace := _.
Typeclasses Opaque namespace.

Definition nroot : namespace := nil.

Definition ndot_def `{Countable A} (N : namespace) (x : A) : namespace :=
  encode x :: N.
Definition ndot_aux : seal (@ndot_def). by eexists. Qed.
Definition ndot {A A_dec A_count}:= unseal ndot_aux A A_dec A_count.
Definition ndot_eq : @ndot = @ndot_def := seal_eq ndot_aux.

Definition nclose_def (N : namespace) : coPset :=
  coPset_suffixes (positives_flatten N).
Definition nclose_aux : seal (@nclose_def). by eexists. Qed.
Global Instance nclose : UpClose namespace coPset := unseal nclose_aux.
Definition nclose_eq : @nclose = @nclose_def := seal_eq nclose_aux.

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
  Proof. intros N1 x1 N2 x2; rewrite !ndot_eq; naive_solver. Qed.

  Lemma nclose_nroot : ↑nroot = (⊤:coPset).
  Proof. rewrite nclose_eq. by apply (sig_eq_pi _). Qed.

  Lemma nclose_subseteq N x : ↑N.@x ⊆ (↑N : coPset).
  Proof.
    intros p. unfold up_close. rewrite !nclose_eq, !ndot_eq.
    unfold nclose_def, ndot_def; rewrite !elem_coPset_suffixes.
    intros [q ->]. destruct (positives_flatten_suffix N (ndot_def N x)) as [q' ?].
    { by exists [encode x]. }
    by exists (q ++ q')%positive; rewrite <-(assoc_L _); f_equal.
  Qed.

  Lemma nclose_subseteq' E N x : ↑N ⊆ E → ↑N.@x ⊆ E.
  Proof. intros. etrans; eauto using nclose_subseteq. Qed.

  Lemma nclose_infinite N : ¬set_finite (↑ N : coPset).
  Proof. rewrite nclose_eq. apply coPset_suffixes_infinite. Qed.

  Lemma ndot_ne_disjoint N x y : x ≠ y → N.@x ## N.@y.
  Proof.
    intros Hxy a. unfold up_close. rewrite !nclose_eq, !ndot_eq.
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
(** Fallback, loses lots of information but lets other rules make progress. *)
Local Definition coPset_subseteq_difference_l := subseteq_difference_l (C:=coPset).
Global Hint Resolve coPset_subseteq_difference_l | 100 : ndisj.
Global Hint Resolve nclose_subseteq' | 100 : ndisj.

(** Rules for goals of the form [_ ## _] *)
(** The base rule that we want to ultimately get down to. *)
Global Hint Extern 0 (_ ## _) => apply ndot_ne_disjoint; congruence : ndisj.
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
