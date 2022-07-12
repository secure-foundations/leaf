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

Require Import Two.conjunct_own_rule.

Section AuthFragUtil.

Context {C : ucmra}.
Context {Σ: gFunctors}.
Context {m: inG Σ (authUR C)}.
Context `{Disc : CmraDiscrete C}.

Lemma auth_op_rhs_is_frag (p: C) z (val : ✓ (● p ⋅ z)) : ∃ q , z = ◯ q.
  destruct z. exists view_frag_proj. rename view_frag_proj into f.
  unfold "◯", "◯V". f_equal.
  destruct view_auth_proj; trivial.
  exfalso.
  unfold "●", "●V" in val.
  
  assert (
    @valid (@view C C (@auth_view_rel_raw C)) (view_valid_instance _)
        (@op _ (view_op_instance _)
          (View (Some (DfracOwn 1, to_agree p)) ε)
          (View (Some p0) f)
        )
  ) as val2.
    { trivial. }
  
  rewrite /op /view_op_instance /view_auth_proj /view_frag_proj in val2.
  rewrite /valid /view_valid_instance /view_auth_proj in val2.
  destruct p0.
  assert (Some (DfracOwn 1, to_agree p) ⋅ Some (d, a)
      = Some (DfracOwn 1 ⋅ d, to_agree p ⋅ a)) as Q.
    { trivial. }
  rewrite Q in val2.
  destruct val2 as [val_frac _].
  have k := dfrac_valid_own_l _ _ val_frac.
  assert (1 ≤ 1)%Qp as k1. { trivial. }
  generalize k1.
  rewrite Qp_le_ngt. intro h. apply h. trivial.
Qed.

Lemma view_op_rw (x w : option (dfrac * agree C)) (y z : C)
    : @op (@view C C (@auth_view_rel_raw C)) (view_op_instance _)
        (View x y) (View w z) = View (x ⋅ w) (y ⋅ z).
Proof. trivial. Qed.

Lemma rhs_has_auth (x y : C) (q1 q2: auth C)
    (v: ✓ (● x ⋅ q1))
    (eq: ● x ⋅ q1 ≡ ◯ y ⋅ q2)
    : ∃ r , q2 ≡ ● x ⋅ r.
Proof.
  have ao := auth_op_rhs_is_frag x q1 v.
  destruct ao as [q ao]. subst q1.
  destruct q2.
  exists (◯ view_frag_proj).
  unfold "●", "●V", "◯", "◯V".
  
  rewrite view_op_rw.
  f_equiv.
  - (*assert (Some (DfracOwn 1, to_agree x) ⋅ None = Some (DfracOwn 1, to_agree x)) as J by trivial.
    rewrite J.*)
    unfold "◯", "◯V", "●", "●V" in eq.
    rewrite view_op_rw in eq.
    rewrite view_op_rw in eq.
    
    inversion eq.
    unfold view.view_auth_proj in H.
    setoid_rewrite H.
    + destruct view_auth_proj; trivial.
  - rewrite left_id. trivial.
Qed.
  
Lemma auth_op_rhs2_is_frag (k p: C) z (val : ✓ (◯ k ⋅ ● p ⋅ z)) : ∃ q , z = ◯ q.
Proof.
  rewrite <- cmra_assoc in val.
  assert (✓ ((● p ⋅ z))) as val2.
    { eapply cmra_valid_op_r. apply val. }
  eapply auth_op_rhs_is_frag. apply val2.
Qed.

Lemma incl_lemma1 (p q r: C)
  (cond : p ⋅ q ≡ p)
  (incl : r ≼ p)
  : (q ⋅ r ≼ p).
Proof.
  unfold "≼" in *. destruct incl as [z incl].
  exists z.
  setoid_rewrite <- cmra_assoc.
  setoid_rewrite <- incl.
  setoid_rewrite <- cond at 1.
  apply cmra_comm.
Qed.

Lemma auth_conjure_frag γ (p q: C)
    (cond: p ⋅ q ≡ p)
    : own γ (● p) ==∗ own γ (● p) ∗ own γ (◯ q).
Proof using C Disc m Σ.
  rewrite <- own_op.
  apply own_update.
  rewrite cmra_discrete_update. intros z valpz.
  have isf := auth_op_rhs_is_frag _ _ valpz. destruct isf as [r isf].
  subst z.
  setoid_rewrite <- cmra_assoc.
  {
    setoid_rewrite <- auth_frag_op.
    generalize valpz. rewrite auth_both_valid_discrete. intros [incl valp].
    rewrite auth_both_valid_discrete. split; trivial.
    apply incl_lemma1; trivial.
  }
Qed.

Lemma val_faf (a s b : C)
  : ✓ (◯ a ⋅ ● s ⋅ ◯ b) -> (a ⋅ b ≼ s).
Proof using C Disc.
  assert ((◯ a ⋅ ● s) ≡ (● s ⋅ ◯ a)) as X.
  { apply cmra_comm. }
  setoid_rewrite X.
  intro Y.
  setoid_rewrite <- cmra_assoc in Y.
  generalize Y.
  setoid_rewrite <- auth_frag_op.
  rewrite auth_both_valid_discrete.
  intros Z. destruct Z. trivial.
Qed.

Lemma own_sep_auth_incll γ (p1 p2 state : C)
    (cond: ∀ z , p1 ⋅ z ≡ state -> ✓ (p2 ⋅ z))
    : own γ (◯ p1) ∗ own γ (● state) ==∗
        (∃ z , ⌜ p1 ⋅ z ≡ state ⌝ ∗ own γ (◯ p2) ∗ own γ (● (p2 ⋅ z)))%I.
Proof using C Disc m Σ.
  iIntros "t".
  rewrite <- own_op.
  iMod (own_updateP (λ y , ∃ z , p1 ⋅ z ≡ state /\ y = ◯ p2 ⋅ ● (p2 ⋅ z)) γ with "t") as "t".
  {
    rewrite cmra_discrete_updateP.
    intros z valpz.
    have z_is_f := auth_op_rhs2_is_frag _ _ _ valpz.
    destruct z_is_f as [q z_is_f]. subst z.
    have incll := val_faf _ _ _ valpz.
    unfold "≼" in incll. destruct incll as [z0 incll].
    symmetry in incll.
    setoid_rewrite <- cmra_assoc in incll.
    have cond0 := cond (q ⋅ z0) incll.
    exists (◯ p2 ⋅ ● (p2 ⋅ (q ⋅ z0))).
    split.
    {
      exists (q ⋅ z0). split; trivial.
    }
    assert (◯ p2 ⋅ ● (p2 ⋅ (q ⋅ z0)) ≡ ● (p2 ⋅ (q ⋅ z0)) ⋅ ◯ p2) as co.
      { apply cmra_comm. }
    setoid_rewrite co.
    setoid_rewrite <- cmra_assoc.
    setoid_rewrite <- auth_frag_op.
    setoid_rewrite cmra_assoc.
    rewrite auth_both_valid_discrete. split.
    { unfold "≼". exists z0. trivial. }
    { setoid_rewrite <- cmra_assoc. trivial. }
  }
  iDestruct "t" as (a') "[%q t]". iModIntro.
  destruct q as [z [q j]]. subst a'.
  iExists z.
  rewrite own_op. iFrame.
  iPureIntro. trivial.
Qed.

Lemma remove_question_mark (a : auth C) (b : option (auth C))
    : ∃ b' , a ⋅? b ≡ a ⋅ b'.
Proof.
  destruct b.
  - exists v. trivial.
  - exists ε. rewrite right_id. trivial.
Qed.

Lemma auth_frag_conjunct (x y : C) (γ : gname)
    : own γ (● x) ∧ own γ (◯ y) ⊢ ⌜ y ≼ x ⌝.
Proof using C Disc m Σ.
  iIntros "x".
  iDestruct (and_own with "x") as "%e".
  destruct e as [z [val [[t1 l1] [t2 l2]]]].
  setoid_rewrite l1 in l2.
  iPureIntro.
  
  have rqm1 := remove_question_mark (● x) t1.
  have rqm2 := remove_question_mark (◯ y) t2.
  destruct rqm1 as [q1 rqm1].
  destruct rqm2 as [q2 rqm2].
  
  setoid_rewrite rqm1 in l1.
  setoid_rewrite rqm1 in l2.
  setoid_rewrite rqm2 in l2.
  clear rqm1. clear rqm2. clear t1. clear t2.
  
  assert (✓ (● x ⋅ q1)) as D.
  { setoid_rewrite <- l1. trivial. }
  
  have jj := rhs_has_auth _ _ _ _ D l2. destruct jj as [r jj].
  setoid_rewrite jj in l2.
  setoid_rewrite l2 in l1.
  setoid_rewrite l1 in val.
  
  assert (◯ y ⋅ (● x ⋅ r) ≡ ◯ y ⋅ ● x ⋅ r) as asso.
  { apply cmra_assoc. }
  setoid_rewrite asso in val.
  
  assert (◯ y ⋅ ● x ≡ ● x ⋅ ◯ y) as com.
  { apply cmra_comm. }
  setoid_rewrite com in val.
  
  have ll := cmra_valid_op_l _ _ val.
  generalize ll.
  rewrite auth_both_valid_discrete. intuition.
Qed.

End AuthFragUtil.
