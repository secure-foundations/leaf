From iris.prelude Require Import options.
From iris.algebra Require Import cmra updates proofmode_classes auth functions gmap.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Import own iprop.
From iris.base_logic.lib Require Import fancy_updates fancy_updates_from_vs.
From iris.proofmode Require Import base ltac_tactics tactics coq_tactics reduction.
From iris.bi Require Import derived_laws_later derived_laws.
Require Import guarding.internal.factoring_upred.

(**
In general, it does _not_ hold that:
<<
    (P ⊢ Q) → (P &&{_}&&> Q)
>>
(See Appendix 1.4; https://arxiv.org/pdf/2309.04851 for a counter-example.)

However, this does hold if we can "factor" P as Q ∗ R.
<<
    (Q ∗ R) &&{_}&&> Q.
>>
For this reason, it is useful to identify propositions that Q that are _always_
factor-out-able in this sense. This is true for propositions like `own γ x`.
That is, we have:

    If [`P ⊢ own γ x`] then there exists [Q] such that [P ⊣⊢ own γ x ∗ Q]

(Specifically, we can take [Q] to be [own γ x -∗ P].)

This lets us prove:
<<
    (P ⊢ own γ x) → P &&{_}&&> own γ x
>>
Now, I don't know if this particular rule is very useful, but this factorizability property
_is_ crucial for stating and proving Leaf's (∧)-related rules.

Unfortunately, I don't have a clean description of the class of propositions Q that
meet this factorizability property, let alone one that also handles all the fiddly
details with [◇] and [▷] that we need. I do know that all propositions of the form
[uPred_ownM x] work for everything we need (thus any proposition of the form
[own γ x] and [∗]-conjunctions thereof). So that's what we classify here.

This definitely isn't the complete set -- we should probably extend it to include
persistent propositions at the very least.

In principle, it would be nice to have a clean definition like:
<<
    Definition can_always_factor_out Q := ∀ P , (P -∗ Q) ∗ P ⊢ Q ∗ (Q -∗ P).
>>
However, I haven't figured out how to make use of such a definition.
For example, I haven't been able to answer basic questions, like
whether this is true:
<<
    can_always_factor_out P →
    can_always_factor_out Q →
    can_always_factor_out (P ∗ Q)
>>   
*)

Section Factoring.

Context {Σ: gFunctors}.

(* A "point prop" is anything of the form `uPred_ownM x` *)
Definition point_prop (P: iProp Σ) := ∃ x , (P ≡ uPred_ownM x).

Global Instance point_prop_proper :
    Proper ((≡) ==> (↔)) point_prop.
Proof.
  solve_proper.
Qed.

Lemma point_prop_True : point_prop True.
Proof.
  unfold point_prop in *.
  exists (ε). 
  iIntros. iSplit. { iIntros "T". iDestruct (uPred.ownM_unit with "T") as "T". iFrame. }
  iIntros "T". done.
Qed.

(* PointProp-Sep *)

Lemma point_prop_sep (P Q: iProp Σ)
  (a: point_prop P) (b: point_prop Q)  : point_prop (P ∗ Q).
Proof.
  unfold point_prop in *. destruct a as [x a]. destruct b as [y b].
  exists (x ⋅ y). setoid_rewrite a. setoid_rewrite b.
  rewrite uPred.ownM_op. trivial.
Qed.

Lemma point_prop_big_sepS `{!EqDecision X, !Countable X} (S : gset X) (P : X → iProp Σ)
    (x_point : ∀ (x: X) , x ∈ S → point_prop (P x))
    : point_prop ([∗ set] x ∈ S , P x).
Proof.
  induction S as [|x T ? IH] using set_ind_L. 
  - rewrite big_sepS_empty. apply point_prop_True.
  - rewrite big_sepS_union.
    + apply point_prop_sep.
      * rewrite big_sepS_singleton. apply x_point. set_solver.
      * apply IH. intros y yT. apply x_point. set_solver.
    + set_solver.
Qed.

Context `{i : !inG Σ A}.

(* PointProp-Own *)

Lemma point_prop_own γ (x: A) : point_prop (own γ x).
Proof.
  rewrite own.own_eq. unfold own.own_def. unfold point_prop.
  exists (own.iRes_singleton γ x). trivial.
Qed.

Lemma own_separates_out γ (x: A) (P : iProp Σ)
  : (P -∗ own γ x) ∗ P ⊢ (
          own γ x ∗ (own γ x -∗ P)
      ).
Proof.
  rewrite own.own_eq. unfold own.own_def.
  apply uPred_ownM_separates_out.
Qed.

Lemma own_separates_out_except0 γ (x: A) (P : iProp Σ)
  : (P -∗ ◇ own γ x) ∗ P ⊢ (
          ◇ own γ x ∗ (own γ x -∗ P)
      ).
Proof.
  rewrite own.own_eq. unfold own.own_def.
  apply uPred_ownM_separates_out_except0.
Qed.


Lemma own_separates_out_point (P : iProp Σ) (Q: iProp Σ)
  (point: point_prop Q)
  : (P -∗ Q) ∗ P ⊢ (
          Q ∗ (Q -∗ P)
      ).
Proof.
  unfold point_prop in point. destruct point as [x point]. setoid_rewrite point.
  apply uPred_ownM_separates_out.
Qed.

Lemma own_separates_out_except0_point (P : iProp Σ) (Q: iProp Σ)
    (point: point_prop Q)
  : (P -∗ ◇ Q) ∗ P ⊢ (
          (◇ Q) ∗ (Q -∗ P)
      ).
Proof.
  unfold point_prop in point. destruct point as [x point]. setoid_rewrite point.
  apply uPred_ownM_separates_out_except0.
Qed.

Lemma own_separates_out_except0_point_later (P : iProp Σ) (Q: iProp Σ) (n: nat)
    (point: point_prop Q)
  : (P -∗ ▷^n ◇ Q) ∗ P ⊢ (
          ▷^n ((◇ Q) ∗ (Q -∗ P))
      ).
Proof.
  unfold point_prop in point. destruct point as [x point]. setoid_rewrite point.
  apply uPred_ownM_separates_out_except0_later.
Qed.

End Factoring.
