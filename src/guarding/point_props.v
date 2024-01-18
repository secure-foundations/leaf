From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

From iris.base_logic.lib Require Export invariants.

From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export fancy_updates_from_vs.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export wsat.

From iris.bi Require Import derived_laws.

Section SeparableAnd.

Context {Σ: gFunctors}.

(* Split-Own *)

Lemma uPred_ownM_separates_out x (P : iProp Σ)
  : (P -∗ uPred_ownM x) ∗ P ⊢ (
          (uPred_ownM x)
          ∗ 
          ((uPred_ownM x) -∗ P)
      ).
Proof.
  uPred.unseal.
  split.
  intros n x0 val t.
  
  unfold uPred_holds, upred.uPred_sep_def in t.
  destruct t as [x1 [x2 [sum [t1 t2]]]].
  
  unfold uPred_holds, upred.uPred_wand_def in t1.
  
  assert (✓{n} (x1 ⋅ x2)) as val_12. { setoid_rewrite <- sum. trivial. }
  assert (n ≤ n) as nle by trivial.
  have t11 := t1 n x2 nle val_12 t2.
  
  unfold uPred_holds in t11. unfold upred.uPred_ownM_def in t11.
  unfold includedN in t11. destruct t11 as [z h].
  
  unfold uPred_holds. unfold upred.uPred_sep_def.
  exists x. exists z.
  
  assert (uPred_holds P n x0) as ux0. {
    eapply uPred_mono. { apply t2. }
    { setoid_rewrite sum. unfold includedN. exists x1.
        rewrite cmra_comm. trivial. }
    trivial.
  }
  
  split.
  { setoid_rewrite sum. trivial. }
  split.
  { unfold uPred_holds. unfold upred.uPred_ownM_def. trivial. }
  { unfold uPred_holds. unfold upred.uPred_wand_def. intros n' x' incl val2 uh.
      unfold uPred_holds in uh.
      unfold upred.uPred_ownM_def in uh.
      unfold includedN in uh. destruct uh as [w j].
      setoid_rewrite j.
      apply uPred_mono with (n1 := n) (x1 := x0); trivial.
      assert (z ⋅ (x ⋅ w) ≡ (z ⋅ x) ⋅ w) as associ. { apply cmra_assoc. }
      setoid_rewrite associ.
      assert ((z ⋅ x) ≡ (x ⋅ z)) as commu. { apply cmra_comm. }
      setoid_rewrite commu.
      unfold includedN. exists w.
      apply dist_le with (n := n); trivial.
      setoid_rewrite sum.
      setoid_rewrite h.
      trivial.
  } 
Qed.

(* Split-Own-Except0 *)

Lemma uPred_ownM_separates_out_except0 x (P : iProp Σ)
  : (P -∗ ◇ uPred_ownM x) ∗ P ⊢ (
          (◇ uPred_ownM x)
          ∗ 
          (uPred_ownM x -∗ P)
      ).
Proof.
  unfold "◇". uPred.unseal.
  split.
  intros n x0 val t.
  
  unfold uPred_holds, upred.uPred_sep_def in t.
  destruct t as [x1 [x2 [sum [t1 t2]]]].
  
  unfold uPred_holds, upred.uPred_wand_def in t1.
  
  assert (✓{n} (x1 ⋅ x2)) as val_12. { setoid_rewrite <- sum. trivial. }
  assert (n ≤ n) as nle by trivial.
  have t11 := t1 n x2 nle val_12 t2.
  
  unfold uPred_holds in t11. unfold upred.uPred_or_def in t11.
  destruct t11 as [tlatfalse|t11].
  {
    unfold uPred_holds in tlatfalse. unfold upred.uPred_later_def in tlatfalse.
    unfold uPred_holds in tlatfalse. unfold upred.uPred_pure_def in tlatfalse.
    destruct n; try contradiction.
    unfold uPred_holds, upred.uPred_sep_def. exists ε, x0.
    split.
    { rewrite ucmra_unit_left_id. trivial. }
    split.
    { unfold uPred_holds, upred.uPred_or_def. left. unfold uPred_holds, upred.uPred_later_def. trivial. }
    unfold uPred_holds, upred.uPred_wand_def.
    intros n' x' le0 valxx uh.
    assert (n' = 0) by lia. subst n'.
    setoid_rewrite sum.
    eapply uPred_mono. { apply t2. }
    { unfold includedN. exists (x1 ⋅ x').
      assert (x2 ⋅ (x1 ⋅ x') ≡ (x2 ⋅ x1 ⋅ x')) as J. { apply cmra_assoc. }
      setoid_rewrite J.
      assert (x1 ⋅ x2 ≡ x2 ⋅ x1) as K. { apply cmra_comm. }
      setoid_rewrite K.
      trivial.
    }
    lia.
  } 
  
  unfold uPred_holds in t11. unfold upred.uPred_ownM_def in t11.
  unfold includedN in t11. destruct t11 as [z h].
  
  unfold uPred_holds. unfold upred.uPred_sep_def.
  exists x. exists z.
  
  split.
  { setoid_rewrite sum. trivial. }
  split.
  { unfold uPred_holds, upred.uPred_or_def. right.
      unfold uPred_holds, upred.uPred_ownM_def. trivial. }
  { unfold uPred_holds, upred.uPred_wand_def.
    intros n' x' incl val2 uh.
      unfold uPred_holds in uh.
      unfold upred.uPred_ownM_def in uh.
      unfold includedN in uh. destruct uh as [w j].
      setoid_rewrite j.
      
       
      assert (uPred_holds P n x0) as ux0. {
        eapply uPred_mono. { apply t2. }
        { setoid_rewrite sum. unfold includedN. exists x1.
            rewrite cmra_comm. trivial. }
        trivial.
      }
      
      apply uPred_mono with (n1 := n) (x1 := x0); trivial.
      assert (z ⋅ (x ⋅ w) ≡ (z ⋅ x) ⋅ w) as associ. { apply cmra_assoc. }
      setoid_rewrite associ.
      assert ((z ⋅ x) ≡ (x ⋅ z)) as commu. { apply cmra_comm. }
      setoid_rewrite commu.
      unfold includedN. exists w.
      apply dist_le with (n := n); trivial.
      setoid_rewrite sum.
      setoid_rewrite h.
      trivial.
  } 
Qed.



(* For the "Point Proposition" formulation from the paper *)
Definition point_prop (P: iProp Σ) := ∃ x , (P ≡ uPred_ownM x).

(* PointProp-Sep *)

Lemma point_prop_sep (P Q: iProp Σ)
  (a: point_prop P) (b: point_prop Q)  : point_prop (P ∗ Q).
Proof.
  unfold point_prop in *. destruct a as [x a]. destruct b as [y b].
  exists (x ⋅ y). setoid_rewrite a. setoid_rewrite b.
  rewrite uPred.ownM_op. trivial.
Qed.

Context `{i : !inG Σ A}.

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

(* PointProp-Own *)

Lemma point_prop_own γ (x: A) : point_prop (own γ x).
Proof.
  rewrite own.own_eq. unfold own.own_def. unfold point_prop.
  exists (own.iRes_singleton γ x). trivial.
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
          ◇ Q ∗ (Q -∗ P)
      ).
Proof.
  unfold point_prop in point. destruct point as [x point]. setoid_rewrite point.
  apply uPred_ownM_separates_out_except0.
Qed.

End SeparableAnd.
