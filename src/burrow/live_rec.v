From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import cpdt.CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.trees.
Require Import Burrow.indexing.
Require Import Burrow.tactics.
Require Import Burrow.locations.
Require Import Burrow.resource_proofs.
Require Import Burrow.exchanges.
Require Import Burrow.assoc_comm.
Require Import coq_tricks.Deex.

Section LiveRec.

Context {M} `{!EqDecision M} `{!TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.

Fixpoint live_rec (loc: Loc RI) (m: M) :=
      match loc with
    | BaseLoc _ _ => live loc m
    | ExtLoc _ _ _ => live loc m
    | CrossLoc l r =>
          (live_rec l (rel M M (refinement_of (left_ri RI)) m)) ⋅
          (live_rec r (rel M M (refinement_of (right_ri RI)) m))
  end.

Lemma live_rec_eq (l r : Loc RI) (m1 m2 : M)
    : live_rec (CrossLoc l r) (pair_up RI m1 m2) = live_rec l m1 ⋅ live_rec r m2.
Proof.
  cbn [live_rec]. f_equal.
  - f_equal. apply refinement_of_left_pair_up.
  - f_equal. apply refinement_of_right_pair_up.
Qed.

Lemma update_a (a a' b c : State M RI)
  (u: ∀ p , ✓(a ⋅ p) → ✓(a' ⋅ p))
  : ✓(a ⋅ b ⋅ c) -> ✓(a' ⋅ b ⋅ c).
Proof.
   setoid_replace (a ⋅ b ⋅ c) with (a ⋅ (b ⋅ c)) by solve_assoc_comm.
   setoid_replace (a' ⋅ b ⋅ c) with (a' ⋅ (b ⋅ c)) by solve_assoc_comm.
   apply u.
Qed.
  
Lemma update_b (a b b' c : State M RI)
  (u: ∀ p , ✓(b ⋅ p) → ✓(b' ⋅ p))
  : ✓(a ⋅ b ⋅ c) -> ✓(a ⋅ b' ⋅ c).
Proof.
   setoid_replace (a ⋅ b ⋅ c) with (b ⋅ (a ⋅ c)) by solve_assoc_comm.
   setoid_replace (a ⋅ b' ⋅ c) with (b' ⋅ (a ⋅ c)) by solve_assoc_comm.
   apply u.
Qed.

Lemma pair_up_unit_unit
    : (pair_up RI (unit: M) unit) = unit.
Proof.
  assert (pair_up RI (unit: M) (unit: M) =
      pair_up RI (rel M M (refinement_of (left_ri RI)) unit)
                 (rel M M (refinement_of (right_ri RI)) unit)) as X.
  { rewrite rel_unit. rewrite rel_unit. trivial. }
  rewrite X.
  rewrite <- self_eq_pair.
  trivial.
Qed.

Lemma unit_unit_pair_is_unit (loc1 loc2: Loc RI)
  : live (CrossLoc loc1 loc2) (pair_up RI (unit: M) unit) ≡ (state_unit : State M RI).
Proof.
  rewrite pair_up_unit_unit. apply live_unit.
Qed.

Lemma op_state_unit_left x : state_unit ⋅ x ≡ x.
Proof. setoid_rewrite state_comm. apply op_state_unit. Qed.

Lemma live_split1 (loc1 loc2 : Loc RI) (m1 m2 : M) p
  (Q : ✓ (live (CrossLoc loc1 loc2) (pair_up RI m1 m2) ⋅ p))
  : ✓ (live loc1 m1 ⋅ live loc2 m2 ⋅ p).
Proof.
  assert (live loc1 m1 ≡ live loc1 m1 ⋅ live (CrossLoc loc1 loc2) (pair_up RI unit unit)) as X.
  { setoid_rewrite unit_unit_pair_is_unit. setoid_rewrite op_state_unit. trivial. }
  setoid_rewrite X.
  apply update_a with (a :=
    live loc1 unit ⋅ live (CrossLoc loc1 loc2) (pair_up RI m1 unit)
  ).
  { intro. apply swap_cross_left_valid. }
  setoid_rewrite live_unit.
  setoid_rewrite op_state_unit_left.
  setoid_replace (live (CrossLoc loc1 loc2) (pair_up RI m1 unit) ⋅ live loc2 m2) with
                 (live loc2 m2 ⋅ live (CrossLoc loc1 loc2) (pair_up RI m1 unit))
                 by (apply state_comm).
  apply swap_cross_right_valid. 
  setoid_rewrite live_unit.
  setoid_rewrite op_state_unit_left.
  trivial.
Qed.

Lemma live_join1 (loc1 loc2 : Loc RI) (m1 m2 : M) p
  (Q: ✓ (live loc1 m1 ⋅ live loc2 m2 ⋅ p))
  : ✓ (live (CrossLoc loc1 loc2) (pair_up RI m1 m2) ⋅ p).
Proof.
  setoid_replace (live (CrossLoc loc1 loc2) (pair_up RI m1 m2))
      with (live loc1 unit ⋅ live (CrossLoc loc1 loc2) (pair_up RI m1 m2))
      by (setoid_rewrite live_unit; setoid_rewrite op_state_unit_left; trivial).
  apply swap_cross_left_valid.
  setoid_replace (live (CrossLoc loc1 loc2) (pair_up RI unit m2))
      with (live loc2 unit ⋅ live (CrossLoc loc1 loc2) (pair_up RI unit m2))
      by (setoid_rewrite live_unit; setoid_rewrite op_state_unit_left; trivial).
  apply update_b with (b :=
    live loc2 m2 ⋅ live (CrossLoc loc1 loc2) (pair_up RI unit unit)
  ).
  { intro. apply swap_cross_right_valid. }
  setoid_rewrite unit_unit_pair_is_unit.
  setoid_rewrite op_state_unit.
  trivial.
Qed.

Lemma live_split (loc1 loc2 : Loc RI) (m : M) p
  (Q: ✓ (live (CrossLoc loc1 loc2) m ⋅ p))
  : ✓ (live loc1 (rel M M (refinement_of (left_ri RI)) m)
     ⋅ live loc2 (rel M M (refinement_of (right_ri RI)) m) ⋅ p).
Proof.
  rewrite (self_eq_pair m) in Q. apply live_split1. trivial.
Qed.

Lemma live_join (loc1 loc2 : Loc RI) (m : M) p
  (Q: ✓ (live loc1 (rel M M (refinement_of (left_ri RI)) m)
     ⋅ live loc2 (rel M M (refinement_of (right_ri RI)) m) ⋅ p))
  : ✓ (live (CrossLoc loc1 loc2) m ⋅ p).
Proof.
  rewrite (self_eq_pair m). apply live_join1. trivial.
Qed.

Lemma live_to_live_rec (loc: Loc RI) (m: M) p
   : ✓(live loc m ⋅ p) -> ✓(live_rec loc m ⋅ p).
Proof.
  generalize p. clear p. generalize m. clear m. induction loc.
  - trivial.
  - trivial.
  - cbn [live_rec]. intros.
      apply update_a with (a := live loc1 (rel M M (refinement_of (left_ri RI)) m)).
      { intro. apply IHloc1. }
      apply update_b with (b := live loc2 (rel M M (refinement_of (right_ri RI)) m)).
      { intro. apply IHloc2. }
      apply live_split. trivial.
Qed.

Lemma live_rec_to_live (loc: Loc RI) (m: M) p
   : ✓(live_rec loc m ⋅ p) -> ✓(live loc m ⋅ p).
Proof.
  generalize p. clear p. generalize m. clear m. induction loc.
  - trivial.
  - trivial.
  - cbn [live_rec]. intros.
      apply live_join.
      apply update_a with (a := live_rec loc1 (rel M M (refinement_of (left_ri RI)) m)).
      { intro. apply IHloc1. }
      apply update_b with (b := live_rec loc2 (rel M M (refinement_of (right_ri RI)) m)).
      { intro. apply IHloc2. }
      trivial.
Qed.

Lemma ref_left_dot (m1 m2: M)
  : rel M M (refinement_of (left_ri RI)) (dot m1 m2) =
  dot (rel M M (refinement_of (left_ri RI)) m1) (rel M M (refinement_of (left_ri RI)) m2).
Proof.
  rewrite (self_eq_pair m1).
  rewrite (self_eq_pair m2).
  rewrite dot_pair_up.
  rewrite <- (self_eq_pair m1).
  rewrite <- (self_eq_pair m2).
  rewrite refinement_of_left_pair_up.
  trivial.
Qed.

Lemma ref_right_dot (m1 m2: M)
  : rel M M (refinement_of (right_ri RI)) (dot m1 m2) =
  dot (rel M M (refinement_of (right_ri RI)) m1) (rel M M (refinement_of (right_ri RI)) m2).
Proof.
  rewrite (self_eq_pair m1).
  rewrite (self_eq_pair m2).
  rewrite dot_pair_up.
  rewrite <- (self_eq_pair m1).
  rewrite <- (self_eq_pair m2).
  rewrite refinement_of_right_pair_up.
  trivial.
Qed.

Lemma live_rec_dot_live_rec
    (gamma: Loc RI) (m1 m2: M)
    : live_rec gamma m1 ⋅ live_rec gamma m2 ≡ live_rec gamma (dot m1 m2).
Proof.
  generalize m1. clear m1. generalize m2. clear m2. induction gamma.
  - intros. unfold live_rec. apply live_dot_live.
  - intros. unfold live_rec. apply live_dot_live.
  - intros. cbn [live_rec].
      rewrite ref_left_dot.
      rewrite ref_right_dot.
      setoid_rewrite <- IHgamma1.
      setoid_rewrite <- IHgamma2.
      solve_assoc_comm.
Qed.

End LiveRec.
