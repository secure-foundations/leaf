From iris.algebra Require Export cmra.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.

From iris.algebra Require Import auth.

From iris.proofmode Require Export tactics.

(*
  iProp version of a ≼ b.
  Like a ≼ b, this is not necessarily reflexive for non-unital camera.
*)
Definition uPred_cmra_incl {Σ: gFunctors} {M: cmra} (a b : M) : iProp Σ := ∃ c , b ≡ a ⋅ c.

Section ConjunctOwnRule2.

  Context {Σ: gFunctors}.
  Context `{i : !inG Σ A}.

  (* Our main goal is to prove:
      (own γ x ∧ own γ y) ⊢
          ∃ z , own γ z
          ∧ uPred_cmra_incl (Some x) (Some z)
          ∧ uPred_cmra_incl (Some y) (Some z)
    We start by proving the analogue in the global ucmra, using uPred_ownM.
  *)

  Local Lemma uPred_ownM_and (x y : iResUR Σ) :
    (uPred_ownM x ∧ uPred_ownM y) ⊢ ∃ z , uPred_ownM z ∧ uPred_cmra_incl x z ∧ uPred_cmra_incl y z.
  Proof.
    uPred.unseal. split. intros n w val_w lhs.
    unfold upred.uPred_and_def in lhs. unfold uPred_holds in lhs.
    unfold upred.uPred_ownM_def in lhs. destruct lhs as [x_incl_w y_incl_w].

    unfold upred.uPred_exist_def. unfold uPred_holds. exists w.
    unfold upred.uPred_and_def.
    split.
    { unfold uPred_holds. unfold upred.uPred_ownM_def. trivial. }
    unfold uPred_holds. unfold uPred_cmra_incl.
    uPred.unseal. unfold upred.uPred_internal_eq_def. unfold uPred_holds.
    split.
    { unfold includedN in x_incl_w. trivial. }
    { unfold includedN in x_incl_w. trivial. }
  Qed.

  (* Now, we need to relate `uPred_ownM (iRes_singleton γ _)` to `own γ _` so that we
    can bring this theorem from the global ucmra world to the A world.
    In particular, uPred_ownM_and gives us some `z` in the ucmra world, but to prove
    the theorem in the end, we need a `z` in the A world.
    We start by defining this `project` function to map from the ucmra world to the A world:
  *)

  Local Definition project (x : iResUR Σ) (γ : gname) : option A :=
    match (x (inG_id i) !! γ) with
    | Some t => Some (cmra_transport (eq_sym inG_prf) (own.inG_fold t))
    | None => None
    end.

  (* Now we prove some nice properties about `project` *)

  Lemma project_op (x y : iResUR Σ) γ n :
    (project (x ⋅ y) γ : option A) ≡{n}≡ (project x γ ⋅ project y γ).
  Proof.
    unfold project. rewrite lookup_op.
    destruct (x (inG_id i) !! γ) eqn:p1; destruct (y (inG_id i) !! γ) eqn:p2.
    - rewrite p1. rewrite p2.
        replace (Some o ⋅ Some o0) with (Some (o ⋅ o0)) by trivial.
        enough (cmra_transport (eq_sym inG_prf) (own.inG_fold (o ⋅ o0)) ≡{n}≡ 
                cmra_transport (eq_sym inG_prf) (own.inG_fold o)
                ⋅ cmra_transport (eq_sym inG_prf) (own.inG_fold o0)).
        { intros. setoid_rewrite H. trivial. }
        setoid_rewrite <- cmra_transport_op.
        f_equiv.
        unfold own.inG_fold. apply equiv_dist.
        apply cmra_morphism_op.
        typeclasses eauto.
    - rewrite p1. rewrite p2. trivial.
    - rewrite p1. rewrite p2. trivial.
    - rewrite p1. rewrite p2. trivial.
  Qed.

  Local Instance proper_project_equiv_n (n : nat) : Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) project.
  Proof.
    unfold Proper, "==>". intros x y H γ γ0 s0. unfold project. subst γ0.
    assert (x (inG_id i) !! γ ≡{n}≡ y (inG_id i) !! γ) as M.
    { enough (x (inG_id i) ≡{n}≡ y (inG_id i)). { trivial. } trivial. }
    destruct (x (inG_id i) !! γ);
    destruct (y (inG_id i) !! γ).
    - assert (o ≡{n}≡ o0) as Q.
      + unfold "≡" in M. unfold ofe_equiv, optionO, option_equiv in M.
            inversion M. trivial.
      + setoid_rewrite Q. trivial.
    - inversion M.
    - inversion M.
    - trivial.
  Qed.

  Local Lemma project_iRes_singleton (x : A) (γ : gname) :
    project (own.iRes_singleton γ x) γ ≡ Some x.
  Proof.
    unfold project, own.iRes_singleton. setoid_rewrite discrete_fun_lookup_singleton.
    rewrite lookup_singleton. f_equiv. setoid_rewrite own.inG_fold_unfold.
    rewrite cmra_transport_trans eq_trans_sym_inv_r /=. trivial.
  Qed.

  (* 
    To get from,
      ∃ z ,  uPred_ownM z   ∧ uPred_ucmra_incl x z    ∧ uPred_ucmra_incl y z
    to,
      ∃ z' , own γ z'       ∧ uPred_cmra_incl x z'    ∧ uPred_cmra_incl y z'
    We're going to set z' to be the projection of z. This requires us to establish
    3 entailments. The next lemma handles the first one, `uPred_ownM z ⊢ own γ z`:
  *)

  Local Lemma iRes_incl_from_proj γ z' z n :
    project z γ = Some z' →
        own.iRes_singleton γ z' ≼{n} z.
  Proof.
    intro p.
    unfold project in p.
    destruct (z (inG_id i) !! γ) eqn:e.
    - assert ((cmra_transport (eq_sym inG_prf) (own.inG_fold o)) ≡ z') as X.
      { unfold "≡", ofe_equiv, optionO, option_equiv in p. inversion p. trivial. }
      unfold includedN.
      unfold own.iRes_singleton.
      exists (discrete_fun_insert (inG_id i) (delete γ (z (inG_id i))) z).
      apply equiv_dist.
      intros x'.
      have h : Decision (inG_id i = x') by solve_decision. destruct h.
      + setoid_rewrite discrete_fun_lookup_op. subst x'.
        setoid_rewrite discrete_fun_lookup_singleton.
        setoid_rewrite discrete_fun_lookup_insert.
        intro γ0.
        have h1 : Decision (γ = γ0) by solve_decision. destruct h1.
        * subst γ0. rewrite lookup_op. rewrite lookup_delete.
          rewrite lookup_singleton. rewrite e.
          unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
          f_equiv.
          setoid_rewrite <- X.
          rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
          setoid_rewrite own.inG_unfold_fold. trivial.
        * rewrite lookup_op. rewrite lookup_delete_ne; trivial.
          rewrite lookup_singleton_ne; trivial.
          unfold "⋅", cmra_op, optionR, option_op_instance, union_with, option_union_with.
          destruct (z (inG_id i) !! γ0) eqn:s.
          ++ rewrite s. trivial.
          ++ rewrite s. trivial.
      + setoid_rewrite discrete_fun_lookup_op.
        setoid_rewrite discrete_fun_lookup_singleton_ne; trivial.
        setoid_rewrite discrete_fun_lookup_insert_ne; trivial.
        symmetry.
        apply ucmra_unit_left_id.
    - inversion p.
  Qed.

  Local Lemma uPred_ownM_implies_project_at_γ γ z' z :
    project z γ = Some z' → uPred_ownM z ⊢ uPred_ownM (own.iRes_singleton γ z').
  Proof.
    intros proj_eq. split. intros n t val_t.
    rewrite upred.uPred_ownM_unseal. unfold uPred_holds. unfold upred.uPred_ownM_def.
    intros w_le_t. have own_le_w := iRes_incl_from_proj γ z' z n proj_eq.
    eapply cmra_includedN_trans. { apply own_le_w. } trivial.
  Qed.

  (* This handles the other two entailments: *)

  Local Lemma uPred_ucmra_incl_implies_incl_at_γ γ x z' z :
      project z γ = Some z' →
        uPred_cmra_incl (own.iRes_singleton γ x) z ⊢ 
            @uPred_cmra_incl Σ (option A) (Some x) (Some z').
  Proof.
    intros proj_eqn. unfold uPred_cmra_incl. unfold uPred_cmra_incl.
    uPred.unseal. split. intros n x0 val_x0 uh.
    unfold upred.uPred_exist_def, uPred_holds in uh.
    unfold upred.uPred_internal_eq_def in uh.
    unfold uPred_holds, upred.uPred_exist_def.
    unfold upred.uPred_internal_eq_def, uPred_holds.
    destruct uh as [c uh]. exists (project c γ).
    assert (project z γ ≡{n}≡ project (own.iRes_singleton γ x) γ ⋅ project c γ) as X.
      { setoid_rewrite <- project_op. setoid_rewrite <- uh. trivial. }
    setoid_rewrite project_iRes_singleton in X.
    rewrite proj_eqn in X.
    unfold "⋅?". destruct (project c γ).
    - inversion X. trivial.
    - inversion X. trivial.
  Qed.

  (* We also need to show the projection is not None.
      TODO: some duplication with the above *)

  Local Lemma uPred_ucmra_incl_projection_is_not_none γ (x : A) (z : iResUR Σ)
    : project z γ = None →
        @uPred_cmra_incl Σ (iResUR Σ) (own.iRes_singleton γ x) z ⊢ False.
  Proof.
    intros proj_eqn. unfold uPred_cmra_incl. unfold uPred_cmra_incl.
    uPred.unseal. split. intros n x0 val_x0 uh.
    unfold upred.uPred_exist_def, uPred_holds in uh.
    unfold upred.uPred_internal_eq_def in uh.
    exfalso.
    destruct uh as [c uh].
    assert (project z γ ≡{n}≡ project (own.iRes_singleton γ x) γ ⋅ project c γ) as X.
      { setoid_rewrite <- project_op. setoid_rewrite <- uh. trivial. }
    setoid_rewrite project_iRes_singleton in X.
    rewrite proj_eqn in X.
    unfold "⋅?". destruct (project c γ).
    - inversion X.
    - inversion X.
  Qed.

  (* Finally we tie it all together. *)

  Lemma and_own (γ : gname) (x y : A) :
    (own γ x ∧ own γ y) ⊢ ∃ z , own γ z
        ∗ uPred_cmra_incl (Some x) (Some z)
        ∗ uPred_cmra_incl (Some y) (Some z).
  Proof.
    rewrite own.own_eq. unfold own.own_def.
    iIntros "and_own".
    iDestruct (uPred_ownM_and with "and_own") as (z) "[own_z [x_le_z y_le_z]]".
    destruct (project z γ) as [z'|] eqn:proj_eqn.
    { 
      iExists z'. iSplitL "own_z".
      { iApply (uPred_ownM_implies_project_at_γ γ z' z); trivial. }
      iSplitL "x_le_z".
      { iApply (uPred_ucmra_incl_implies_incl_at_γ γ x z' z); trivial. }
      { iApply (uPred_ucmra_incl_implies_incl_at_γ γ y z' z); trivial. }
    }
    { iExFalso. iApply (uPred_ucmra_incl_projection_is_not_none γ x z); trivial. }
  Qed.

  (* Now some corollaries *)

  Local Lemma uPred_cmra_incl_discrete_implies_pure {D : CmraDiscrete A} (x y : A) :
    @uPred_cmra_incl Σ (option A) (Some x) (Some y)  ⊢ ⌜ Some x ≼ Some y ⌝.
  Proof.
    unfold uPred_cmra_incl. iIntros "eq". iDestruct "eq" as (c) "eq".
    iDestruct (discrete_eq_1 with "eq") as "%eq".
    unfold "≼". iPureIntro. exists c. trivial.
  Qed.

  Lemma and_own_discrete {D : CmraDiscrete A} (γ : gname) (x y : A) :
    (own γ x ∧ own γ y) ⊢ ∃ z , own γ z ∗ ⌜ Some x ≼ Some z ∧ Some y ≼ Some z ⌝.
  Proof.
    iIntros "and_own". iDestruct (and_own with "and_own") as (z) "[own [a b]]".
    iExists z. iFrame "own".
    iDestruct (uPred_cmra_incl_discrete_implies_pure with "a") as "%a".
    iDestruct (uPred_cmra_incl_discrete_implies_pure with "b") as "%b".
    iPureIntro; split; trivial.
  Qed.

End ConjunctOwnRule2.

Section ConjunctOwnRule2Ucmra.

  Context {Σ : gFunctors}.
  Context {A : ucmra}.
  Context `{i : !inG Σ A}.

  Local Lemma uPred_cmra_incl_ucmra_discrete_implies_pure {D : CmraDiscrete A} (x y : A) :
    @uPred_cmra_incl Σ (option A) (Some x) (Some y)  ⊢ ⌜ x ≼ y ⌝.
  Proof.
    unfold uPred_cmra_incl. iIntros "eq". iDestruct "eq" as (c) "eq".
    iDestruct (discrete_eq_1 with "eq") as "%eq". unfold "≼". iPureIntro. destruct c.
    - exists c. setoid_rewrite <- Some_op in eq. inversion eq. trivial.
    - exists ε. rewrite right_id. inversion eq. trivial.
  Qed.

  Lemma and_own_discrete_ucmra {D : CmraDiscrete A} (γ : gname) (x y : A) :
    (own γ x ∧ own γ y) ⊢ ∃ z , own γ z ∗ ⌜ x ≼ z ∧ y ≼ z ⌝.
  Proof.
    iIntros "and_own". iDestruct (and_own with "and_own") as (z) "[own [a b]]".
    iExists z. iFrame "own".
    iDestruct (uPred_cmra_incl_ucmra_discrete_implies_pure with "a") as "%a".
    iDestruct (uPred_cmra_incl_ucmra_discrete_implies_pure with "b") as "%b".
    iPureIntro; split; trivial.
  Qed.

  Lemma and_own_discrete_ucmra_specific {D : CmraDiscrete A} (γ : gname) (x y z : A) :
    (∀ w , ✓ w → x ≼ w → y ≼ w → z ≼ w) →
    (own γ x ∧ own γ y) ⊢ own γ z.
  Proof.
    intros Hw. iIntros "and_own".
    iDestruct (and_own_discrete_ucmra with "and_own") as (w) "[own [%a %b]]".
    iDestruct (own_valid with "own") as "%v".
    assert (z ≼ w) as z_le_w. { apply Hw; trivial. }
    unfold "≼" in z_le_w. destruct z_le_w as [z1 eq]. setoid_rewrite eq.
    iDestruct "own" as "[own1 own2]". iFrame.
  Qed.

  Lemma and_own_discrete_ucmra_contradiction {D : CmraDiscrete A} (γ : gname) (x y : A) :
    (∀ w , ✓ w → x ≼ w → y ≼ w → False) →
    (own γ x ∧ own γ y) ⊢ False.
  Proof.
    intros Hw. iIntros "and_own".
    iDestruct (and_own_discrete_ucmra with "and_own") as (w) "[own [%a %b]]".
    iDestruct (own_valid with "own") as "%v". exfalso. apply (Hw w); trivial.
  Qed.

End ConjunctOwnRule2Ucmra.
