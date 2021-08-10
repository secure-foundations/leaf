Require Import Burrow.rollup.
From stdpp Require Import gmap.

Require Import Burrow.CpdtTactics.


Section GmapTPCM.

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

#[refine]
Global Instance gmap_tpcm : TPCM (gmap K (option V)) := {
  m_valid p := gmap_valid p ;
  dot a b := gmap_dot a b ;
  mov a b := gmap_mov a b ;
  unit := empty ;
}.
 - intros. unfold gmap_valid, gmap_dot in *.
    intro. have h := H k. clear H. rewrite lookup_merge in h. unfold diag_None in h.
        unfold gmerge in h.
        destruct (x !! k); trivial.
        destruct (y !! k); trivial. contradiction.
 - unfold gmap_valid. intros. rewrite lookup_empty. trivial.
 - intros. unfold gmap_dot. apply map_eq. intro. rewrite lookup_merge. rewrite lookup_empty.
    unfold diag_None, gmerge. destruct (x !! i); trivial.
 - intros. unfold gmap_dot, gmerge. apply map_eq. intro. rewrite lookup_merge.
    rewrite lookup_merge. unfold diag_None. destruct (x !! i), (y !! i); trivial.
 - intros. apply gmap_dot_assoc.
  - intros. unfold gmap_mov. intro. trivial.
  - intros. unfold gmap_mov in *. intros. apply H0. apply H. trivial.
  - intros. split.
    * unfold gmap_mov in H. apply H. apply H0.
    * unfold gmap_mov in H. unfold gmap_mov. intro.
        rewrite <- gmap_dot_assoc.
        rewrite <- gmap_dot_assoc.
        apply H.
Qed.

End GmapTPCM.
