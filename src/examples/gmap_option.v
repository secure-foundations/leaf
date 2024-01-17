From stdpp Require Import gmap.

From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

Require Import cpdt.CpdtTactics.

Section GmapOptionDot.

Context {K} `{!EqDecision K} `{!Countable K}.
Context {V} `{!EqDecision V}.

Definition gmap_valid (p: gmap K (option V)) : Prop :=
  ∀ k , match p !! k with Some None => False | _ => True end.
  
Definition gmerge (a b : option (option V)) : option (option V) :=
  match a, b with
  | None, None => None
  | Some x, None => Some x
  | None, Some y => Some y
  | Some x, Some y => Some None
  end.
  
Definition gmap_dot (a b: gmap K (option V)) : gmap K (option V) :=
  merge gmerge a b.
  
Definition gmap_mov (a b: gmap K (option V)) : Prop :=
  ∀ z , gmap_valid (gmap_dot a z) -> gmap_valid (gmap_dot b z).
  
Lemma gmap_dot_comm x y
  : gmap_dot x y = gmap_dot y x.
Proof.
intros. unfold gmap_dot, gmerge. apply map_eq. intro. rewrite lookup_merge.
    rewrite lookup_merge. unfold diag_None. destruct (x !! i), (y !! i); trivial.
Qed.
  
Lemma gmap_dot_assoc x y z
  : gmap_dot x (gmap_dot y z) = gmap_dot (gmap_dot x y) z.
Proof. intros. unfold gmap_dot, gmerge. apply map_eq. intro. rewrite lookup_merge.
    rewrite lookup_merge.
    rewrite lookup_merge.
    unfold diag_None.
    rewrite lookup_merge.
    unfold diag_None.
    destruct (x !! i), (y !! i), (z !! i); trivial.
Qed.

Lemma gmap_dot_empty
  : ∀ x : gmap K (option V), gmap_dot x ∅ = x.
Proof.
intros. unfold gmap_dot. apply map_eq. intro. rewrite lookup_merge. rewrite lookup_empty.
    unfold diag_None, gmerge. destruct (x !! i); trivial.
Qed.

Lemma gmap_dot_empty_left
  : ∀ x : gmap K (option V), gmap_dot ∅ x = x.
Proof.
intros. unfold gmap_dot. apply map_eq. intro. rewrite lookup_merge. rewrite lookup_empty.
    unfold diag_None, gmerge. destruct (x !! i); trivial.
Qed.

Lemma lookup_gmap_dot_left a b k
  : gmap_valid (gmap_dot a b) -> (a !! k ≠ None) -> (gmap_dot a b) !! k = a !! k.
Proof.
  unfold gmap_valid, gmap_dot. intros.
  have j := H k. rewrite lookup_merge.
  rewrite lookup_merge in j. unfold diag_None, gmerge in *. destruct (a !! k), (b !! k);
  trivial; contradiction.
Qed.
  
Lemma lookup_gmap_dot_right a b k
  : gmap_valid (gmap_dot a b) -> (b !! k ≠ None) -> (gmap_dot a b) !! k = b !! k.
Proof.
  unfold gmap_valid, gmap_dot. intros. have j := H k. rewrite lookup_merge.
  rewrite lookup_merge in j. unfold diag_None, gmerge in *. destruct (a !! k), (b !! k);
  trivial; contradiction.
Qed.

Lemma lookup_gmap_dot_3mid a b c k
  : gmap_valid (gmap_dot (gmap_dot a b) c) -> (b !! k ≠ None) ->
      gmap_dot (gmap_dot a b) c !! k = b !! k.
Proof.
  intros.
  rewrite gmap_dot_comm in H.
  rewrite gmap_dot_assoc in H.
  rewrite gmap_dot_comm.
  rewrite gmap_dot_assoc.
  apply lookup_gmap_dot_right; trivial.
Qed.

Lemma lookup_gmap_dot_3left a b c k
  : gmap_valid (gmap_dot (gmap_dot a b) c) -> (a !! k ≠ None) ->
      gmap_dot (gmap_dot a b) c !! k = a !! k.
Proof.
  intros.
  rewrite <- gmap_dot_assoc in H.
  rewrite <- gmap_dot_assoc.
  apply lookup_gmap_dot_left; trivial.
Qed.

Lemma lookup_gmap_dot_3right a b c k
  : gmap_valid (gmap_dot (gmap_dot a b) c) -> (c !! k ≠ None) ->
      gmap_dot (gmap_dot a b) c !! k = c !! k.
Proof.
  apply lookup_gmap_dot_right.
Qed.

Lemma gmap_valid_left
  : ∀ x y : gmap K (option V), gmap_valid (gmap_dot x y) → gmap_valid x.
Proof.
  intros. unfold gmap_valid, gmap_dot in *.
    intro. have h := H k. clear H. rewrite lookup_merge in h. unfold diag_None in h.
        unfold gmerge in h.
        destruct (x !! k); trivial.
        destruct (y !! k); trivial. contradiction.
Qed.

Lemma gmap_valid_right
  : ∀ x y : gmap K (option V), gmap_valid (gmap_dot x y) → gmap_valid y.
Proof.
  intro. intro. rewrite gmap_dot_comm. apply gmap_valid_left.
Qed.

Lemma gmap_valid_update_singleton j x y (m: gmap K (option V)) :
  gmap_valid (gmap_dot {[j := Some x]} m) ->
  gmap_valid (gmap_dot {[j := Some y]} m).
Proof.
  intros. unfold gmap_valid, gmap_dot in *. intro.
  have r := H k. rewrite lookup_merge. rewrite lookup_merge in r.
  unfold gmerge, diag_None in *.
  have h : Decision (j = k) by solve_decision. destruct h.
  - subst k. rewrite lookup_singleton. rewrite lookup_singleton in r.
      destruct (m !! j); trivial.
  - rewrite lookup_singleton_ne; trivial.
    rewrite lookup_singleton_ne in r; trivial.
Qed.
 
 (*
#[refine]
Global Instance gmap_tpcm : TPCM (gmap K (option V)) := {
  m_valid p := gmap_valid p ;
  dot a b := gmap_dot a b ;
  mov a b := gmap_mov a b ;
  unit := empty ;
}.
 - apply gmap_valid_left.
 - unfold gmap_valid. intros. rewrite lookup_empty. trivial.
 - apply gmap_dot_empty.
 - intros. apply gmap_dot_comm.
 - intros. apply gmap_dot_assoc.
  - intros. unfold gmap_mov. intro. trivial.
  - intros. unfold gmap_mov in *. intros. apply H0. apply H. trivial.
  - intros. split.
    * unfold gmap_mov in H. apply H. apply H0.
    * unfold gmap_mov in H. unfold gmap_mov. intro.
        rewrite <- gmap_dot_assoc.
        rewrite <- gmap_dot_assoc.
        apply H.
Defined.
*)

Definition gmap_le (a b : gmap K (option V)) := ∃ c , gmap_dot a c = b.

Lemma le_of_subset (a b : gmap K (option V))
  (f: ∀ k v , a !! k = Some v -> b !! k = Some v) : gmap_le a b.
Proof.
  assert (∀ x : K * option V, Decision (match x with (k,v) => a !! k = None end)) as X
    by solve_decision.
  exists (map_filter (λ x , match x with (k,v) => a !! k = None end) X b).
  unfold gmap_dot. apply map_eq. intro.
  have ff := f i.
  rewrite lookup_merge. unfold diag_None, gmerge. 
  destruct (a !! i) eqn:ai.
  - rewrite map_lookup_filter.
    unfold "≫=", option_bind. destruct (b!!i) eqn:bi.
    + unfold mguard, option_guard. have fff := ff o. intuition. inversion H.
      destruct (X (i, o)).
      * rewrite ai in e. discriminate.
      * trivial.
    + have fff := ff o. intuition.
  - rewrite map_lookup_filter.
    unfold "≫=", option_bind. destruct (b!!i) eqn:bi; trivial.
    unfold mguard, option_guard. destruct (X (i, o)); trivial.
    contradiction.
Qed.

Lemma conjunct_and_gmap
    a1 a2 c
  (gv: gmap_valid c)
  (a_disj : ∀ (k : K) (j1 j2 : option V),
             a1 !! k = Some j1 → a2 !! k = Some j2 → False)
  (la1 : gmap_le a1 c)
  (la2 : gmap_le a2 c)
  : gmap_le (gmap_dot a1 a2) c.
Proof.
  apply le_of_subset. intros k v e1.
  unfold gmap_dot in e1. rewrite lookup_merge in e1. unfold diag_None in e1.
  destruct (a1 !! k) eqn:a1k; destruct (a2 !! k) eqn:a2k.
  - have l := a_disj _ _ _ a1k a2k. contradiction.
  - unfold gmerge in e1. inversion e1. subst o. unfold gmap_le in la1.
      destruct la1 as [d la]. subst c.
      unfold gmap_dot.
      unfold gmap_valid in gv. unfold gmap_dot in gv.
      rewrite lookup_merge. rewrite a1k. unfold diag_None.
      have gvk := gv k.
      rewrite lookup_merge in gvk. rewrite a1k in gvk. unfold diag_None in gvk.
      unfold gmerge. unfold gmerge in gvk. destruct (d !! k); trivial. contradiction.
  - unfold gmerge in e1. inversion e1. subst o. unfold gmap_le in la2.
      destruct la2 as [d la]. subst c.
      unfold gmap_dot.
      unfold gmap_valid in gv. unfold gmap_dot in gv.
      rewrite lookup_merge. rewrite a2k. unfold diag_None.
      have gvk := gv k.
      rewrite lookup_merge in gvk. rewrite a2k in gvk. unfold diag_None in gvk.
      unfold gmerge. unfold gmerge in gvk. destruct (d !! k); trivial. contradiction.
  - discriminate.
Qed.

End GmapOptionDot.
