From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.gmap_utils.
Require Import Burrow.rollup.
Require Import Burrow.indexing.
Require Import Burrow.locations.
Require Import Burrow.tactics.

Require Import coq_tricks.Deex.

Section ExchangeProof.

Context {M} `{!EqDecision M} `{!TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.

Definition specific_exchange_cond (ref: Refinement M M) (p m f h s m' f' h' s' : M) :=
  ∃ j l l' ,
  rel_defined M M ref (dot f p) ->
  m_valid (dot m (rel M M ref (dot f p))) ->
      dot j s' = f' /\ m = dot l h /\ m' = dot l' h' /\
      rel_defined M M ref (dot (dot j s) p) /\
      mov (dot l (rel M M ref (dot f p))) (dot l' (rel M M ref (dot (dot j s) p))).


Definition specific_flow_cond p i (t t': Branch M) (active: Lifetime) (down up : PathLoc -> M) :=
  let q := (p, i) in
  let r := (p, S i) in
  let s := (p ++ [i], 0) in
  specific_exchange_cond (refinement_of_nat M RI i)
      (node_total_minus_live (refinement_of_nat M RI) (node_of_pl t q) active)
      (down q) (node_live (node_of_pl t q))
      (down r) (down s)
      (up q) (node_live (node_of_pl t' q))
      (up r) (up s).
    
Lemma dot_kjha k j a : (dot (dot a k) j) = (dot (dot j a) k).
Proof.  rewrite tpcm_comm. rewrite tpcm_assoc. trivial. Qed.

Lemma valid_reduce m k a :
  m_valid (dot (dot m k) a) -> m_valid (dot m a). 
Proof. intro. apply valid_monotonic with (y := k).
  rewrite dot_comm_right2. trivial. Qed.
  
Lemma dot_aklh a k l h
  : (dot (dot a k) (dot l h)) = dot (dot l a) (dot k h).
Proof.
  rewrite tpcm_assoc. rewrite tpcm_assoc. f_equal.
  apply dot_kjha. Qed.
  
Lemma dot_aklh2 a k l h
    : (dot (dot (dot l h) k) a) = (dot (dot l a) (dot k h)).
Proof.
  rewrite <- tpcm_assoc. rewrite <- tpcm_assoc. rewrite <- tpcm_assoc. f_equal.
  rewrite tpcm_assoc. rewrite tpcm_assoc. rewrite dot_kjha.
  rewrite dot_comm_right2. trivial. Qed.

Lemma dot_jszr (j s z r : M)
        : dot (dot j s) (dot z r) = dot (dot r s) (dot j z).
Proof.
  replace (dot j s) with (dot s j) by (apply tpcm_comm).
  replace (dot r s) with (dot s r) by (apply tpcm_comm).
  rewrite <- tpcm_assoc. rewrite <- tpcm_assoc. f_equal.
  replace (dot z r) with (dot r z) by (apply tpcm_comm).
  rewrite tpcm_assoc. rewrite tpcm_assoc. f_equal. apply tpcm_comm. Qed.
        
Lemma dot_jszr2 (j s z r : M)
        : (dot (dot (dot j s) z) r) = dot (dot r s) (dot j z).
Proof.
  rewrite <- tpcm_assoc.
  apply dot_jszr. Qed.
  
Lemma dot_qklh (q k l h : M)
  : dot (dot q k) (dot l h) = dot (dot k h) (dot q l).
Proof.
  replace (dot k h) with (dot h k) by (apply tpcm_comm).
  apply dot_jszr.
Qed.
  
Lemma all_the_movs (z m f h s r k m' f' h' s' r' k' : M) i
  (mo: mov (dot r s) (dot r' s'))
  (mo2: mov (dot k h) (dot k' h'))
  (inr: in_refinement_domain (refinement_of_nat M RI) i (dot f (dot z r)))
  (myflow : specific_exchange_cond (refinement_of_nat M RI i) (dot z r) m f h s m' f' h' s')
  (val : m_valid (dot (dot m k) (project (refinement_of_nat M RI) i (dot (dot f z) r))))
  : mov (dot (dot (project (refinement_of_nat M RI) i (dot (dot f z) r)) k) m)
        (dot (dot (project (refinement_of_nat M RI) i (dot (dot f' z) r')) k') m').
Proof.
  unfold specific_exchange_cond in myflow. deex.
  unfold in_refinement_domain in inr.
  unfold project in *.
  assert ((dot (dot f z) r) = (dot f (dot z r))) as A by (rewrite tpcm_assoc; trivial).
  rewrite A in val. rewrite A. clear A.
  (*destruct (rel M M (refinement_of_nat M RI i) (dot f (dot z r))) eqn:fzr.
  - rename m0 into a.*)
    have myf := myflow inr (valid_reduce m k _ val). clear myflow.
    destruct_ands.
    subst m.
    subst m'. subst f'.
    set a := (rel M M (refinement_of_nat M RI i) (dot f (dot z r))).
    set a' := (rel M M (refinement_of_nat M RI i) ((dot (dot j s) (dot z r)))).
      assert (m_valid (dot (dot a' k) (dot l' h)) /\
        (mov (dot (dot a k) (dot l h)) (dot (dot a' k) (dot l' h)))).
      * assert (dot (dot a k) (dot l h) = dot (dot l a) (dot k h)) as r1 by (apply dot_aklh).
        assert (dot (dot a' k) (dot l' h) = dot (dot l' a') (dot k h)) as r2 by (apply dot_aklh).
        rewrite r1.
        rewrite r2.
        subst a. subst a'.
        apply mov_monotonic; trivial.
        rewrite <- dot_aklh2. trivial.
      * destruct_ands.
        apply trans with (y := dot (dot a' k) (dot l' h)); trivial.
        
        subst a. subst a'.
        
        rewrite dot_jszr in H2.
        rewrite dot_jszr in H3.
        
        rewrite dot_jszr2.
        
        assert (m_valid (dot (dot r s) (dot j z))) as m_valid_srjz
         by ( apply (rel_valid_left M M (refinement_of_nat M RI i) (dot (dot r s) (dot j z))); trivial).
        assert (mov (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z))) as mov_rsjz
          by (apply mov_monotonic; trivial).
        
        have movr := mov_refines M M (refinement_of_nat M RI i)
            (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z)) mov_rsjz H2.
        deex. destruct_ands.
        
        assert (m_valid (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot r' s') (dot j z))) k) (dot l' h)) /\
          (mov (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) k) (dot l' h)) (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot r' s') (dot j z))) k) (dot l' h)))).
          -- replace
            ((dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) k) (dot l' h))) with
            ((dot ((rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r)))) (dot k (dot l' h)))) by (apply tpcm_assoc).
            replace
            ((dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) k) (dot l' h))) with
            ((dot ((rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r)))) (dot k (dot l' h)))) in H by (apply tpcm_assoc).
             replace
            ((dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot r' s') (dot j z))) k) (dot l' h))) with
            ((dot ((rel M M (refinement_of_nat M RI i) (dot (dot r' s') (dot j z)))) (dot k (dot l' h)))) by (apply tpcm_assoc).
            rewrite <- dot_jszr in H4.
             apply mov_monotonic; trivial.
          -- destruct_ands.
              apply trans with (y := (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot r' s') (dot j z))) k) (dot l' h))); trivial.
              rewrite dot_qklh.
              rewrite dot_qklh in H5.
              assert (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot r' s') (dot j z))) k') (dot l' h') = dot (dot k' h') (dot (rel M M (refinement_of_nat M RI i) (dot (dot r' s') (dot j z))) l'))
                  by (apply dot_qklh).
              rewrite H7.
              apply mov_monotonic; trivial.
Qed.
 
Lemma all_the_movs_ird (z m f h s r k m' f' h' s' r' k' : M) i
  (mo: mov (dot r s) (dot r' s'))
  (mo2: mov (dot k h) (dot k' h'))
  (inr: in_refinement_domain (refinement_of_nat M RI) i (dot f (dot z r)))
  (myflow : specific_exchange_cond (refinement_of_nat M RI i) (dot z r) m f h s m' f' h' s')
  (val : m_valid (dot (dot m k) (project (refinement_of_nat M RI) i (dot (dot f z) r))))
  : in_refinement_domain (refinement_of_nat M RI) i (dot (dot f' z) r').
Proof.
  unfold specific_exchange_cond in myflow. deex.
  unfold in_refinement_domain in inr.
  unfold project in *.
  assert ((dot (dot f z) r) = (dot f (dot z r))) as A by (rewrite tpcm_assoc; trivial).
  rewrite A in val. clear A.
    have myf := myflow inr (valid_reduce m k _ val). clear myflow.
    destruct_ands.
    subst m.
    subst m'.
    subst f'.
      assert (m_valid (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) k) (dot l' h)) /\
        (mov (dot (dot (rel M M (refinement_of_nat M RI i) (dot f (dot z r))) k) (dot l h)) (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) k) (dot l' h)))).
      * assert (dot (dot (rel M M (refinement_of_nat M RI i) (dot f (dot z r))) k) (dot l h) = dot (dot l (rel M M (refinement_of_nat M RI i) (dot f (dot z r)))) (dot k h)) as r1 by (apply dot_aklh).
        assert (dot (dot (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) k) (dot l' h) = dot (dot l' (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r)))) (dot k h)) as r2 by (apply dot_aklh).
        rewrite r1.
        rewrite r2.
        apply mov_monotonic; trivial.
        rewrite <- dot_aklh2. trivial.
      * destruct_ands.
        
        (*rewrite dot_jszr in jszr.
        rewrite dot_jszr2.*)
        
        rewrite dot_jszr in H2.
        rewrite dot_jszr in H3.
        
        rewrite dot_jszr2.
        
        assert (m_valid (dot (dot r s) (dot j z))) as m_valid_srjz
         by (apply (rel_valid_left M M (refinement_of_nat M RI i) (dot (dot r s) (dot j z)) ); trivial).
        assert (mov (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z))) as mov_rsjz
          by (apply mov_monotonic; trivial).
        
        have movr := mov_refines M M (refinement_of_nat M RI i)
            (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z))  mov_rsjz H2.
        deex. destruct_ands.
        
        unfold in_refinement_domain.
        trivial.
Qed.

Lemma m_valid_ca a b c
: m_valid (dot (dot a b) c) -> m_valid (dot c a).
Proof.
  intro. apply valid_monotonic with (y := b).
  rewrite dot_kjha in H. trivial.
Qed.

Lemma m_valid_bd (a b c d : M)
: m_valid (dot (dot a b) (dot c d)) -> m_valid (dot b d).
Proof.
  intro. apply valid_monotonic with (y := dot a c).
  rewrite dot_aklh. replace (dot d c) with (dot c d) by (apply tpcm_comm). trivial. Qed.

Lemma m_valid_db (a b c d : M)
: m_valid (dot (dot a b) (dot c d)) -> m_valid (dot d b).
Proof.
  intro. apply valid_monotonic with (y := dot a c).
  rewrite <- dot_aklh.
  replace (dot b a) with (dot a b) by (apply tpcm_comm).
  replace (dot d c) with (dot c d) by (apply tpcm_comm). trivial.
Qed.

Lemma rec_m_valid_branch
  (t t' : Branch M)
  (active : Lifetime)
  (branch : Branch M) p i
  (down up : PathLoc -> M)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (branch_is : branch ≡ branch_of_pl t (p, i))
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i))))
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch active i)
  : m_valid (dot
                  (branch_total (refinement_of_nat M RI) (branch_of_pl t (p, S i)) active
                     (S i)) (down (p, S i))).
Proof.
  setoid_rewrite branch_is in amval.
  setoid_rewrite branchcons_pl in amval.
  rewrite branch_total_unfold in amval.
  have fl := flow_update p i.
  unfold specific_flow_cond in fl.
  unfold specific_exchange_cond in fl. deex.
  
  setoid_rewrite branch_is in batird.
  setoid_rewrite branchcons_pl in batird.
  rewrite branch_all_total_in_refinement_domain_unfold in batird.
  destruct_ands. clear H0. rename H into natird.
  setoid_rewrite cellnode_pl in natird.
  rewrite node_all_total_in_refinement_domain_unfold in natird.
  destruct_ands. rename H into Y. clear H0.
  unfold in_refinement_domain in Y.
  assert ((node_total (refinement_of_nat M RI)
             (CellNode (cell_of_pl t (p, i)) (branch_of_pl t (p ++ [i], 0))) active)
             = node_total (refinement_of_nat M RI) (node_of_pl t (p, i)) active).
   - setoid_rewrite cellnode_pl. trivial.
   - rewrite H in Y.
     rewrite <- node_live_plus_node_total_minus_live in Y.
     
     rewrite <- node_live_plus_node_total_minus_live in amval.
     unfold project in amval.
     
     full_generalize (rel M M (refinement_of_nat M RI i)
          (dot (node_live (node_of_pl t (p, i)))
             (node_total_minus_live (refinement_of_nat M RI) (node_of_pl t (p, i)) active))) as x.
     + have fl' := fl Y (m_valid_ca _ _ _ amval).
       destruct_ands.
       rewrite H1 in amval.
       have am := m_valid_bd _ _ _ _ amval.
       trivial.
Qed.

Lemma rec_m_valid_node
  (t t' : Branch M)
  (active : Lifetime)
  (branch : Branch M) p i
  (down up : PathLoc -> M)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (branch_is : branch ≡ branch_of_pl t (p, i))
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i))))
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch active i)
      : m_valid
             (dot
                (branch_total (refinement_of_nat M RI) (branch_of_node (node_of_pl t (p, i)))
                   active 0) (down (p ++ [i], 0))).
Proof.
  (*setoid_rewrite branch_is in amval.
  setoid_rewrite branchcons_pl in amval.
  rewrite branch_total_unfold in amval.
  setoid_rewrite cellnode_pl in amval.
  rewrite node_total_unfold in amval.*)

  setoid_rewrite branch_is in amval.
  setoid_rewrite branchcons_pl in amval.
  rewrite branch_total_unfold in amval.
  have fl := flow_update p i.
  unfold specific_flow_cond in fl.
  unfold specific_exchange_cond in fl. deex.
  
  setoid_rewrite branch_is in batird.
  setoid_rewrite branchcons_pl in batird.
  rewrite branch_all_total_in_refinement_domain_unfold in batird.
  destruct_ands. clear H0. rename H into natird.
  setoid_rewrite cellnode_pl in natird.
  rewrite node_all_total_in_refinement_domain_unfold in natird.
  destruct_ands. rename H into Y. clear H0.
  unfold in_refinement_domain in Y.
  assert ((node_total (refinement_of_nat M RI)
             (CellNode (cell_of_pl t (p, i)) (branch_of_pl t (p ++ [i], 0))) active)
             = node_total (refinement_of_nat M RI) (node_of_pl t (p, i)) active).
   - setoid_rewrite cellnode_pl. trivial.
   - rewrite H in Y.
     rewrite <- node_live_plus_node_total_minus_live in Y.
     
     rewrite <- node_live_plus_node_total_minus_live in amval.
     unfold project in amval.
     
     full_generalize (rel M M (refinement_of_nat M RI i)
          (dot (node_live (node_of_pl t (p, i)))
             (node_total_minus_live (refinement_of_nat M RI) (node_of_pl t (p, i)) active))) as x.
     + have fl' := fl Y (m_valid_ca _ _ _ amval).
       destruct_ands.
       (*destruct (rel M M (refinement_of_nat M RI i)
           (dot (dot j (down (p ++ [i], 0)))
              (node_total_minus_live (refinement_of_nat M RI) (node_of_pl t (p, i)) active))) eqn:de.*)
       * have rvl := rel_valid_left M M (refinement_of_nat M RI i) ((dot (dot j (down (p ++ [i], 0))) (node_total_minus_live (refinement_of_nat M RI) (node_of_pl t (p, i)) active))) H3.
         setoid_rewrite cellnode_pl in rvl.
         unfold node_total_minus_live in rvl.
         have q := m_valid_db _ _ _ _ rvl .
         setoid_rewrite branch_of_node_node_of_pl.
         trivial.
Qed.

Lemma dot_cba a b c
  : (dot (dot a b) c) = (dot (dot c b) a).
Proof.
  rewrite dot_kjha. rewrite <- tpcm_assoc. rewrite <- tpcm_assoc. f_equal.
  apply tpcm_comm. Qed.
  
Lemma listset_max_fn (se : gset PathLoc) (fn: PathLoc -> nat)
  : ∃ lmax , ∀ pl , pl ∈ se -> fn pl ≤ lmax.
Proof. exists (set_fold (λ r k, k `max` fn r) 1 se).
  intros.
  replace (se) with ((se ∖ {[ pl ]}) ∪ {[ pl ]}).
  - rewrite set_fold_add_1_element.
    + lia.
    + set_solver.
    + intros. lia.
  - apply set_eq. intros. rewrite elem_of_union.
    rewrite elem_of_difference. rewrite elem_of_singleton. intuition.
    + subst. trivial.
    + have h : Decision (x = pl) by solve_decision. destruct h; intuition.
Qed.

Lemma listset_max_len (se : gset PathLoc)
  : ∃ lmax , ∀ p i , (p, i) ∈ se -> length p ≤ lmax.
Proof. have h := listset_max_fn se (λ pl , match pl with (p, i) => length p end).
  deex. exists lmax. intros. have q := h (p, i). apply q. trivial.
Qed.
  
Lemma listset_max_i (se : gset PathLoc)
  : ∃ imax , ∀ p i , (p, i) ∈ se -> i ≤ imax.
Proof. have h := listset_max_fn se (λ pl , match pl with (p, i) => i end).
  deex. exists lmax. intros. have q := h (p, i). apply q. trivial.
Qed.
    
Lemma batird_BranchNil active idx:
  branch_all_total_in_refinement_domain (refinement_of_nat M RI) BranchNil active idx.
Proof. unfold branch_all_total_in_refinement_domain. trivial. Qed.

Lemma branch_total_is_unit active i
 : branch_total (refinement_of_nat M RI) BranchNil active i = unit.
Proof. unfold branch_total. trivial. Qed.
  
Lemma resolve_trivial branch branch' active i
  (bt : branch_trivial branch)
  (bt' : branch_trivial branch')
  : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch' active i
  ∧ mov (dot (branch_total (refinement_of_nat M RI) branch active i) unit)
      (dot (branch_total (refinement_of_nat M RI) branch' active i) unit).
Proof.
  assert (branch ≡ BranchNil) as bn
   by (apply branch_equiv_of_trivial; trivial; unfold branch_trivial; trivial).
  assert (branch' ≡ BranchNil) as bn'
   by (apply branch_equiv_of_trivial; trivial; unfold branch_trivial; trivial).
  split.
  - setoid_rewrite bn'.
    apply batird_BranchNil.
  - setoid_rewrite bn.
    setoid_rewrite bn'.
    rewrite branch_total_is_unit.
    apply reflex.
Qed.

Lemma do_trivial_movs (m h s m' h' s': M) i
  (mov1 : mov h h')
  (mov2 : mov s s')
  (is_valid_m: m_valid m)
  (fl : specific_exchange_cond (refinement_of_nat M RI i) unit m unit h s m' unit h' s')
  : mov m m'.
Proof.
  have t : mov (dot (dot (project (refinement_of_nat M RI) i (dot (dot unit unit) unit)) unit) m) (dot (dot (project (refinement_of_nat M RI) i (dot (dot unit unit) unit)) unit) m').
  - apply all_the_movs with (h := h) (s := s) (h' := h') (s' := s').
    + rewrite unit_dot_left. rewrite unit_dot_left. trivial.
    + rewrite unit_dot_left. rewrite unit_dot_left. trivial.
    + rewrite unit_dot_left. rewrite unit_dot_left. 
        unfold in_refinement_domain. apply rel_defined_unit.
    + rewrite unit_dot_left. trivial.
    + repeat (rewrite unit_dot_left).
      repeat (rewrite unit_dot).
      unfold project. rewrite rel_unit.
      repeat (rewrite unit_dot).
      trivial.
  - unfold project in t.
    repeat (rewrite unit_dot_left in t).
    repeat (rewrite unit_dot in t).
    rewrite rel_unit in t.
    repeat (rewrite unit_dot_left in t).
    trivial.
Qed.

Lemma specexc_branch_tt_ind (t t': Branch M) (active: Lifetime) (se: gset PathLoc) : ∀ len_add i_add p i
  branch branch'
  (indl: ∀ p0 i0 , (p0, i0) ∈ se -> length p0 < len_add + length p)
  (indi: ∀ p0 i0 , (p0, i0) ∈ se -> i0 < i_add + i)
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (branch_is : branch ≡ branch_of_pl t (p, i))
  (branch'_is : branch' ≡ branch_of_pl t' (p, i))
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i))))
  (branch_is_trivial : branch_trivial branch)
  (branch'_is_trivial : branch_trivial branch')
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch active i)
  ,
            branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch' active i
      /\ mov
        (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i)))
        (dot (branch_total (refinement_of_nat M RI) branch' active i) (up (p, i))).
  induction len_add as [len_add IHnLen] using lt_wf_ind.
  induction i_add as [i_add IHnI] using lt_wf_ind.
Proof.
  intros.
  destruct len_add.
  - assert ((p, i) ∉ se).
    + intro. have indl_a := indl p i H. lia.
    + have d := flow_se p i H. destruct_ands. rewrite H0. rewrite H1.
        apply resolve_trivial; trivial.
  - destruct i_add.
    + assert ((p, i) ∉ se).
      * intro. have indi_a := indi p i H. lia.
      * have d := flow_se p i H. destruct_ands. rewrite H0. rewrite H1.
          apply resolve_trivial; trivial.
    +
      assert (len_add < S len_add) as len_add_lt_S by lia.
      assert (∀ (p0 : list nat) (i0 : nat),
           (p0, i0) ∈ se → length p0 < len_add + length (p ++ [i])) as afl
        by  (intros; have indla := indl p0 i0 H; rewrite app_length; simpl; lia).
      assert ((∀ (p0 : list nat) (i0 : nat), (p0, i0) ∈ se → i0 < S i_add + i + 0)) as ifl
        by (intros; have india := indi p0 i0 H; lia).
      assert (BranchNil ≡ branch_of_pl t (p ++ [i], 0)) as branch_nil_n_child
        by (apply branch_nil_of_n_child; setoid_rewrite branch_is in branch_is_trivial;
            trivial).
      assert (BranchNil ≡ branch_of_pl t' (p ++ [i], 0)) as branch_nil_n_child'
        by (apply branch_nil_of_n_child; setoid_rewrite branch'_is in branch'_is_trivial;
            trivial).
            
      assert (BranchNil ≡ branch_of_pl t (p, S i)) as branch_nil_b_child
        by (apply branch_nil_of_b_child; setoid_rewrite branch_is in branch_is_trivial;
            trivial).
      assert (BranchNil ≡ branch_of_pl t' (p, S i)) as branch_nil_b_child'
        by (apply branch_nil_of_b_child; setoid_rewrite branch'_is in branch'_is_trivial;
            trivial).
            
      have mval_b := rec_m_valid_branch t t' active branch p i down up flow_update branch_is
    amval batird.
      setoid_rewrite <- branch_nil_b_child in mval_b.

      have mval_n := rec_m_valid_node t t' active branch p i down up flow_update branch_is
    amval batird.
      setoid_rewrite branch_of_node_node_of_pl in mval_n.
      setoid_rewrite <- branch_nil_n_child in mval_n.
      
      assert (branch_trivial BranchNil) as bt_bn by (unfold branch_trivial; trivial).
    
      have Ih1 := IHnLen len_add len_add_lt_S (S i_add + i) (p ++ [i]) 0
          BranchNil BranchNil afl ifl down up flow_se flow_update branch_nil_n_child
          branch_nil_n_child' reserved_untouched mval_n bt_bn bt_bn
          (batird_BranchNil active 0).
          
      assert (i_add < S i_add) as i_add_lt_S by lia.
      
      assert (∀ (p0 : list nat) (i0 : nat), (p0, i0) ∈ se → length p0 < S len_add + length p)
          as merf by (intros; have q := indl p0 i0 H; lia).
          
      assert (∀ (p0 : list nat) (i0 : nat), (p0, i0) ∈ se → i0 < i_add + S i)
          as gerf by (intros; have q := indi p0 i0 H; lia).
      
      have Ih2 := IHnI i_add i_add_lt_S p (S i) BranchNil BranchNil merf gerf
          down up flow_se flow_update branch_nil_b_child
          branch_nil_b_child' reserved_untouched mval_b bt_bn bt_bn
          (batird_BranchNil active (S i)).
      
      clear IHnLen. clear IHnI.
      destruct_ands. rename H0 into mov1. rename H2 into mov2.
      
      assert (branch ≡ BranchNil) as b_bn by (apply branch_equiv_of_trivial; trivial).
      assert (branch' ≡ BranchNil) as b'_bn by (apply branch_equiv_of_trivial; trivial).
      
      split.
      * setoid_rewrite b'_bn. apply batird_BranchNil.
      * setoid_rewrite b'_bn. setoid_rewrite b_bn.
        rewrite branch_total_is_unit.
        rewrite branch_total_is_unit in mov1.
        rewrite branch_total_is_unit in mov2.
        setoid_rewrite b_bn in amval.
        rewrite branch_total_is_unit in amval.
        rewrite unit_dot_left.
        rewrite unit_dot_left.
        rewrite unit_dot_left in mov1.
        rewrite unit_dot_left in mov1.
        rewrite unit_dot_left in mov2.
        rewrite unit_dot_left in mov2.
        have fl := flow_update p i.
        unfold specific_flow_cond in fl.
        
        assert (node_of_pl t (p, i) ≡ triv_node) as is_triv_node
          by (apply node_triv_of_triv_branch; setoid_rewrite branch_is in branch_is_trivial;
              trivial).
              
        assert (node_of_pl t' (p, i) ≡ triv_node) as is_triv_node'
          by (apply node_triv_of_triv_branch; setoid_rewrite branch'_is in branch'_is_trivial;
              trivial).
              
        setoid_rewrite is_triv_node in fl.
        setoid_rewrite is_triv_node' in fl.
        rewrite node_total_minus_live_triv in fl.
        unfold node_live, triv_node, cell_live, triv_cell in fl.
        
        full_generalize (down (p, S i)) as h.
        full_generalize (up (p, S i)) as h'.
        full_generalize (down (p, i)) as m.
        full_generalize (up (p, i)) as m'.
        full_generalize ((down (p ++ [i], 0))) as s.
        full_generalize ((up(p ++ [i], 0))) as s'.
        apply do_trivial_movs with (h:=h) (s:=s) (h':=h') (s':=s') (i:=i); trivial.
        rewrite unit_dot_left in amval. trivial.
Qed.
        
Lemma specexc_branch_tt (t t': Branch M) (active: Lifetime) (se: gset PathLoc) p i
  branch branch'
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (branch_is : branch ≡ branch_of_pl t (p, i))
  (branch'_is : branch' ≡ branch_of_pl t' (p, i))
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i))))
  (branch_is_trivial : branch_trivial branch)
  (branch'_is_trivial : branch_trivial branch')
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch active i)
          : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch' active i
      /\ mov
        (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i)))
        (dot (branch_total (refinement_of_nat M RI) branch' active i) (up (p, i))).
Proof.
  have lmax_h := listset_max_len se.
  have imax_h := listset_max_i se. deex.
  assert ( ∀ (p0 : list nat) (i0 : nat), (p0, i0) ∈ se → length p0 < (lmax+1) + length p).
   - intros. have g := lmax_h p0 i0 H. lia.
   - assert (∀ (p0 : list nat) (i0 : nat), (p0, i0) ∈ se → i0 < imax + 1 + i).
    + intros. have g := imax_h p0 i0 H0. lia.
    + eapply (specexc_branch_tt_ind t t' active se (lmax+1) (imax+1) p i branch branch' H H0 down up flow_se flow_update branch_is
      branch'_is reserved_untouched amval branch_is_trivial branch'_is_trivial batird).
Qed.

Lemma specexc_branch_t (t t': Branch M) (active: Lifetime) (branch branch': Branch M) (se: gset PathLoc) p i
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (branch_is : branch ≡ branch_of_pl t (p, i))
  (branch'_is : branch' ≡ branch_of_pl t' (p, i))
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i))))
  (branch'_is_trivial : branch_trivial branch')
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch active i)
          : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch' active i
      /\ mov
        (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i)))
        (dot (branch_total (refinement_of_nat M RI) branch' active i) (up (p, i)))
with specexc_node_t (t t': Branch M) (active: Lifetime) (node node': Node M) (se: gset PathLoc) p i
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (node_is : node ≡ node_of_pl t (p, i))
  (node'_is : node' ≡ node_of_pl t' (p, i))
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) (branch_of_node node) active 0) (down (p++[i], 0))))
  (node'_is_trivial : node_trivial node')
  (batird : node_all_total_in_refinement_domain (refinement_of_nat M RI) node active i)
          : branch_all_total_in_refinement_domain (refinement_of_nat M RI) (branch_of_node node') active 0
      /\ mov
        (dot (branch_total (refinement_of_nat M RI) (branch_of_node node) active 0) (down (p++[i], 0)))
        (dot (branch_total (refinement_of_nat M RI) (branch_of_node node') active 0) (up (p++[i], 0))).
Proof.
 -
  have mval_b := rec_m_valid_branch t t' active branch p i down up flow_update branch_is
    amval batird.

  have mval_n := rec_m_valid_node t t' active branch p i down up flow_update branch_is
    amval batird.

   destruct branch.
   + have branch_destruct := branchcons_pl t p i.
     have triv_equiv : (branch_of_pl t' (p, S i) ≡ branch_of_pl t' (p, S i)) by trivial.
     have triv_equiv2 : (node_of_pl t' (p, i) ≡ node_of_pl t' (p, i)) by trivial.
     have b_equiv : branch ≡ branch_of_pl t (p, S i)
        by (apply branchcons_pl_inv_b with (n0 := n); symmetry; trivial).
     have n_equiv : n ≡ node_of_pl t (p, i)
        by (apply branchcons_pl_inv_n with (b := branch); symmetry; trivial).
        
     setoid_rewrite branch'_is in branch'_is_trivial.
     assert (branch_trivial (branch_of_pl t' (p, S i))) as rec_bt by
      (apply rec_branch_branch_triv; trivial).
     assert (node_trivial (node_of_pl t' (p, i))) as rec_nt by
      (apply rec_branch_node_triv; trivial).
        
     setoid_rewrite <- b_equiv in mval_b.
     have IHbranch := specexc_branch_t t t' active branch (branch_of_pl t' (p, S i)) se p (S i)
                          down up flow_se flow_update b_equiv triv_equiv reserved_untouched mval_b rec_bt.
     clear specexc_branch_t.
     setoid_rewrite <- n_equiv in mval_n.
     have IHnode := specexc_node_t t t' active n (node_of_pl t' (p, i)) se p i
                          down up flow_se flow_update n_equiv triv_equiv2 reserved_untouched mval_n rec_nt.
     clear specexc_node_t.
     
     setoid_rewrite branch_is in batird.
     setoid_rewrite branch_destruct in batird.
     rewrite branch_all_total_in_refinement_domain_unfold in batird.
     destruct_ands.
     rename H into natird.
     rename H0 into batird.
     setoid_rewrite <- n_equiv in natird.
     setoid_rewrite <- b_equiv in batird.
     
     have IHbranch' := IHbranch batird. clear IHbranch.
     have IHnode' := IHnode natird. clear IHnode.
        destruct_ands. rename H1 into Q1. rename H2 into Q2.
        rename H into Q3. rename H0 into Q4.
     
     setoid_rewrite branch_is. setoid_rewrite branch_destruct.
     rewrite branch_total_unfold.
     have myflow := flow_update p i.
     unfold specific_flow_cond in myflow.
     setoid_rewrite cellnode_pl.
     setoid_rewrite cellnode_pl in myflow.
     unfold node_total_minus_live in myflow.
        
     unfold node_live in myflow.
     setoid_rewrite branchcons_pl in Q1.
     (*setoid_rewrite branchcons_pl in Q2.*)
     setoid_rewrite b_equiv in Q2.
        
     setoid_rewrite n_equiv in natird.
     setoid_rewrite cellnode_pl in natird.
     rewrite node_all_total_in_refinement_domain_unfold in natird.
     rewrite node_total_unfold in natird.
     rewrite cell_total_split in natird.
     destruct_ands. rename H into ird.
        
     assert ((cell_total_minus_live (cell_of_pl t (p, i)) active)
            = (cell_total_minus_live (cell_of_pl t' (p, i)) active)) as ctml_pres
            by (apply reserved_untouched).
            
     setoid_rewrite branch_is in amval.
     setoid_rewrite branchcons_pl in amval.
     rewrite branch_total_unfold in amval.
     setoid_rewrite cellnode_pl in amval.
     rewrite node_total_unfold in amval.
     rewrite cell_total_split in amval.
     rewrite ctml_pres in amval.
        
     setoid_rewrite branch_of_node_node_of_pl in Q4.
     setoid_rewrite n_equiv in Q4.
     setoid_rewrite branch_of_node_node_of_pl in Q4.
        
     rewrite ctml_pres in myflow.
     rewrite ctml_pres in ird.
     rewrite <- tpcm_assoc in ird.
        
     (*rewrite (branch_total_unfold (refinement_of_nat M RI) (BranchCons n' branch')).*)
        
     split.
        
        * setoid_rewrite branch'_is.
          setoid_rewrite branchcons_pl.
          rewrite branch_all_total_in_refinement_domain_unfold.
          
          split.
        
          -- setoid_rewrite cellnode_pl.
             rewrite node_all_total_in_refinement_domain_unfold.
             rewrite node_total_unfold.
             split.
             
             
             
            (* ++ setoid_rewrite cellnode_pl in Q3.
              rewrite branch_all_total_in_refinement_domain_unfold in Q3.
              unfold branch_of_node in Q3.
              destruct (branch_of_pl t' (p ++ [i], 0)) eqn:ye.
              ** destruct Q3.
                 rewrite ye in H.*)
           
           ++ rewrite cell_total_split.
           
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t (p, S i)) active (S i))
          as k.
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p, S i)) active (S i))
          as k'.
        full_generalize (cell_live (cell_of_pl t (p, i))) as f.
        full_generalize (cell_live (cell_of_pl t' (p, i))) as f'.
        (*full_generalize (cell_total_minus_live (cell_of_pl t (p, i)) active) as z.*)
        full_generalize (cell_total_minus_live (cell_of_pl t' (p, i)) active) as z.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t (p ++ [i], 0)) active 0) as r.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p ++ [i], 0)) active 0) as r'.
        full_generalize (down (p, S i)) as h.
        full_generalize (up (p, S i)) as h'.
        full_generalize (down (p, i)) as m.
        full_generalize (up (p, i)) as m'.
        full_generalize ((down (p ++ [i], 0))) as s.
        full_generalize ((up(p ++ [i], 0))) as s'.
        
        apply all_the_movs_ird
          with (m:=m) (f:=f) (h:=h) (s:=s) (r:=r) (k:=k) (m':=m') (h':=h') (s':=s') (k':=k');
          trivial.
          ** rewrite dot_cba. trivial.
        
        ++ setoid_rewrite cellnode_pl in Q3. unfold branch_of_node in Q3. trivial.
      -- setoid_rewrite <- branchcons_pl in Q1. trivial.
        
        *
        (*
        (*setoid_rewrite n_equiv.*)
        rewrite branch_total_unfold.
        (*setoid_rewrite b_equiv.*)
        rewrite cell_total_split.
        (*rewrite cell_total_split.*)
        *)
        
        setoid_rewrite branch'_is.
        rewrite node_total_unfold.
        setoid_rewrite (branchcons_pl t' p i).
        rewrite (branch_total_unfold _ (BranchCons (node_of_pl t' (p, i)) (branch_of_pl t' (p, S i)))).
        setoid_rewrite (cellnode_pl t' p i).
        rewrite node_total_unfold.
        rewrite cell_total_split.
        rewrite cell_total_split.
        
        rewrite ctml_pres.
        
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t (p, S i)) active (S i))
          as k.
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p, S i)) active (S i))
          as k'.
        full_generalize (cell_live (cell_of_pl t (p, i))) as f.
        full_generalize (cell_live (cell_of_pl t' (p, i))) as f'.
        (*full_generalize (cell_total_minus_live (cell_of_pl t (p, i)) active) as z.*)
        full_generalize (cell_total_minus_live (cell_of_pl t' (p, i)) active) as z.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t (p ++ [i], 0)) active 0) as r.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p ++ [i], 0)) active 0) as r'.
        full_generalize (down (p, S i)) as h.
        full_generalize (up (p, S i)) as h'.
        full_generalize (down (p, i)) as m.
        full_generalize (up (p, i)) as m'.
        full_generalize ((down (p ++ [i], 0))) as s.
        full_generalize ((up(p ++ [i], 0))) as s'.
                
        apply all_the_movs with (h := h) (s := s) (h' := h') (s' := s'); trivial.
        rewrite dot_cba. trivial.
      + eapply specexc_branch_tt with (t := t) (t' := t') (se:=se); trivial.
 - clear specexc_node_t.
  assert (branch_trivial (branch_of_pl t' (p ++ [i], 0))) as rec_bt
   by (apply rec_node_branch_triv; setoid_rewrite <- node'_is; trivial).
  destruct node, node'. rename b into branch. rename b0 into branch'.
  assert (branch ≡ branch_of_pl t (p ++ [i], 0)) as branch1_equiv
      by (apply cellnode_pl_inv_b with (c1 := c); symmetry; trivial).
  assert (branch' ≡ branch_of_pl t' (p ++ [i], 0)) as branch2_equiv
      by (apply cellnode_pl_inv_b with (c1 := c0); symmetry; trivial).
  unfold branch_of_node in amval.
  rewrite node_all_total_in_refinement_domain_unfold in batird.
  destruct_ands. rename H into ird. rename H0 into batird.
  setoid_rewrite <- branch2_equiv in rec_bt.
  have Ihb := specexc_branch_t t t' active branch branch' se (p++[i]) 0 down up flow_se flow_update
      branch1_equiv branch2_equiv reserved_untouched amval rec_bt batird.
  destruct_ands.
  repeat split; trivial.
Qed.


Lemma specexc_branch (t t': Branch M) (active: Lifetime) (branch branch': Branch M) (se: gset PathLoc) p i
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (branch_is : branch ≡ branch_of_pl t (p, i))
  (branch'_is : branch' ≡ branch_of_pl t' (p, i))
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i))))
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch active i)
          : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch' active i
      /\ mov
        (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i)))
        (dot (branch_total (refinement_of_nat M RI) branch' active i) (up (p, i)))
with specexc_node (t t': Branch M) (active: Lifetime) (node node': Node M) (se: gset PathLoc) p i
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (node_is : node ≡ node_of_pl t (p, i))
  (node'_is : node' ≡ node_of_pl t' (p, i))
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) (branch_of_node node) active 0) (down (p++[i], 0))))
  (batird : node_all_total_in_refinement_domain (refinement_of_nat M RI) node active i)
          : branch_all_total_in_refinement_domain (refinement_of_nat M RI) (branch_of_node node') active 0
      /\ mov
        (dot (branch_total (refinement_of_nat M RI) (branch_of_node node) active 0) (down (p++[i], 0)))
        (dot (branch_total (refinement_of_nat M RI) (branch_of_node node') active 0) (up (p++[i], 0))).
Proof.
 - destruct branch'.
   + rename n into n'.
     have branch_destruct := branchcons_pl t p i.
     have triv_equiv : (branch_of_pl t (p, S i) ≡ branch_of_pl t (p, S i)) by trivial.
     have triv_equiv2 : (node_of_pl t (p, i) ≡ node_of_pl t (p, i)) by trivial.
     have b_equiv : branch' ≡ branch_of_pl t' (p, S i)
        by (apply branchcons_pl_inv_b with (n := n'); symmetry; trivial).
     have n_equiv : n' ≡ node_of_pl t' (p, i)
        by (apply branchcons_pl_inv_n with (b := branch'); symmetry; trivial).
        
     have mval_b := rec_m_valid_branch t t' active branch p i down up flow_update branch_is
        amval batird.
        
     have mval_n := rec_m_valid_node t t' active branch p i down up flow_update branch_is
        amval batird.
        
     have IHbranch := specexc_branch t t' active (branch_of_pl t (p, S i)) branch' se p (S i)
                          down up flow_se flow_update triv_equiv b_equiv reserved_untouched mval_b.
     clear specexc_branch.
     have IHnode := specexc_node t t' active (node_of_pl t (p, i)) n' se p i
                          down up flow_se flow_update triv_equiv2 n_equiv reserved_untouched mval_n.
     clear specexc_node.
     
     setoid_rewrite branch_is in batird.
     setoid_rewrite branch_destruct in batird.
     rewrite branch_all_total_in_refinement_domain_unfold in batird.
     destruct_ands.
     rename H into natird.
     rename H0 into batird.
     
     have IHbranch' := IHbranch batird. clear IHbranch.
     have IHnode' := IHnode natird. clear IHnode.
        destruct_ands. rename H1 into Q1. rename H2 into Q2.
        rename H into Q3. rename H0 into Q4.
       
       rewrite branch_all_total_in_refinement_domain_unfold.
       
       enough (
  (node_all_total_in_refinement_domain (refinement_of_nat M RI) n' active i)
  ∧ mov (dot (branch_total (refinement_of_nat M RI) branch active i) (down (p, i)))
      (dot (branch_total (refinement_of_nat M RI) (BranchCons n' branch') active i)
         (up (p, i))))
       by (destruct_ands; repeat split; trivial).
       
       setoid_rewrite branch_is. setoid_rewrite branch_destruct.
        rewrite branch_total_unfold.
        have myflow := flow_update p i.
        unfold specific_flow_cond in myflow.
        setoid_rewrite cellnode_pl.
        setoid_rewrite cellnode_pl in myflow.
        unfold node_total_minus_live in myflow.
        rewrite (branch_total_unfold (refinement_of_nat M RI) (BranchCons n' branch')).
        
        (*assert (node_all_total_in_refinement_domain (refinement_of_nat M RI) (node_of_pl t' (p, i)) active i <->
             node_all_total_in_refinement_domain (refinement_of_nat M RI) n' active i) by (split; setoid_rewrite n_equiv; trivial).
        rewrite <- H.*)
        
        unfold node_live in myflow.
        setoid_rewrite b_equiv in Q1.
        setoid_rewrite b_equiv in Q2.
        
        setoid_rewrite cellnode_pl in natird.
        rewrite node_all_total_in_refinement_domain_unfold in natird.
        rewrite node_total_unfold in natird.
        rewrite cell_total_split in natird.
        destruct_ands. rename H into ird.
        
        assert ((cell_total_minus_live (cell_of_pl t (p, i)) active)
            = (cell_total_minus_live (cell_of_pl t' (p, i)) active)) as ctml_pres
            by (apply reserved_untouched).
            
        setoid_rewrite branch_is in amval.
        setoid_rewrite branchcons_pl in amval.
        rewrite branch_total_unfold in amval.
        setoid_rewrite cellnode_pl in amval.
        rewrite node_total_unfold in amval.
        rewrite cell_total_split in amval.
        rewrite ctml_pres in amval.
        
        setoid_rewrite branch_of_node_node_of_pl in Q4.
        setoid_rewrite n_equiv in Q4.
        setoid_rewrite branch_of_node_node_of_pl in Q4.
        
        rewrite ctml_pres in myflow.
        rewrite ctml_pres in ird.
        rewrite <- tpcm_assoc in ird.
        
        split.
        
        * setoid_rewrite n_equiv.
          setoid_rewrite cellnode_pl.
          rewrite node_all_total_in_refinement_domain_unfold.
          rewrite node_total_unfold.
          split; trivial.
          -- rewrite cell_total_split.
           
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t (p, S i)) active (S i))
          as k.
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p, S i)) active (S i))
          as k'.
        full_generalize (cell_live (cell_of_pl t (p, i))) as f.
        full_generalize (cell_live (cell_of_pl t' (p, i))) as f'.
        (*full_generalize (cell_total_minus_live (cell_of_pl t (p, i)) active) as z.*)
        full_generalize (cell_total_minus_live (cell_of_pl t' (p, i)) active) as z.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t (p ++ [i], 0)) active 0) as r.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p ++ [i], 0)) active 0) as r'.
        full_generalize (down (p, S i)) as h.
        full_generalize (up (p, S i)) as h'.
        full_generalize (down (p, i)) as m.
        full_generalize (up (p, i)) as m'.
        full_generalize ((down (p ++ [i], 0))) as s.
        full_generalize ((up(p ++ [i], 0))) as s'.
        
        apply all_the_movs_ird
          with (m:=m) (f:=f) (h:=h) (s:=s) (r:=r) (k:=k) (m':=m') (h':=h') (s':=s') (k':=k');
          trivial.
          rewrite dot_cba. trivial.

          
          -- setoid_rewrite n_equiv in Q3.
             setoid_rewrite cellnode_pl in Q3. trivial.
        
        *
        setoid_rewrite n_equiv.
        rewrite node_total_unfold.
        setoid_rewrite (cellnode_pl t' p i).
        rewrite node_total_unfold.
        setoid_rewrite b_equiv.
        rewrite cell_total_split.
        rewrite cell_total_split.
        
        rewrite ctml_pres.
        
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t (p, S i)) active (S i))
          as k.
        full_generalize
          (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p, S i)) active (S i))
          as k'.
        full_generalize (cell_live (cell_of_pl t (p, i))) as f.
        full_generalize (cell_live (cell_of_pl t' (p, i))) as f'.
        (*full_generalize (cell_total_minus_live (cell_of_pl t (p, i)) active) as z.*)
        full_generalize (cell_total_minus_live (cell_of_pl t' (p, i)) active) as z.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t (p ++ [i], 0)) active 0) as r.
        full_generalize (branch_total (refinement_of_nat M RI) (branch_of_pl t' (p ++ [i], 0)) active 0) as r'.
        full_generalize (down (p, S i)) as h.
        full_generalize (up (p, S i)) as h'.
        full_generalize (down (p, i)) as m.
        full_generalize (up (p, i)) as m'.
        full_generalize ((down (p ++ [i], 0))) as s.
        full_generalize ((up(p ++ [i], 0))) as s'.
        unfold specific_exchange_cond in myflow.
        
        apply all_the_movs with (h := h) (s := s) (h' := h') (s' := s'); trivial.
        rewrite dot_cba. trivial.
      + eapply specexc_branch_t with (t := t) (t' := t') (se := se); trivial.
        unfold branch_trivial. trivial.
 - clear specexc_node.
  destruct node, node'. rename b into branch. rename b0 into branch'.
  assert (branch ≡ branch_of_pl t (p ++ [i], 0)) as branch1_equiv
      by (apply cellnode_pl_inv_b with (c1 := c); symmetry; trivial).
  assert (branch' ≡ branch_of_pl t' (p ++ [i], 0)) as branch2_equiv
      by (apply cellnode_pl_inv_b with (c1 := c0); symmetry; trivial).
  unfold branch_of_node in amval.
  rewrite node_all_total_in_refinement_domain_unfold in batird.
  destruct_ands. rename H into ird. rename H0 into batird.
  have Ihb := specexc_branch t t' active branch branch' se (p++[i]) 0 down up flow_se flow_update
      branch1_equiv branch2_equiv reserved_untouched amval batird.
  destruct_ands.
  repeat split; trivial.
Qed.

Lemma valid_of_mov (x y : M) : m_valid x -> mov x y -> m_valid y.
Proof.
  intros.
  have h := mov_monotonic x y unit.
  have j := h EqDecision0 TPCM0 EqDecision0 TPCM0.
  rewrite unit_dot in j.
  rewrite unit_dot in j.
  have l := j H0 H. destruct_ands. trivial.
Qed.
 
Lemma specific_flows_preserve_branch_all_total_in_refinement_domain
  (t t': Branch M) (active: Lifetime)
  (se: gset PathLoc)
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (down_0 : down ([], 0) = unit)
  (up_0 : up ([], 0) = unit)
  (reserved_untouched : ∀ pl, cell_reserved (cell_of_pl t pl) ≡ cell_reserved (cell_of_pl t' pl))
  (vts : valid_totals (refinement_of_nat M RI) t active)
       : valid_totals (refinement_of_nat M RI) t' active.
Proof.
  unfold valid_totals in *. destruct_ands.
  assert ((∀ pl : PathLoc,
         cell_total_minus_live (cell_of_pl t pl) active =
         cell_total_minus_live (cell_of_pl t' pl) active)) as ru2.
  - intros. have ru := reserved_untouched pl.
        unfold cell_reserved in ru.
        unfold cell_total_minus_live.
        destruct (cell_of_pl t pl).
        destruct (cell_of_pl t' pl).
        setoid_rewrite ru.
        trivial.
  - 
  assert (t ≡ branch_of_pl t ([], 0)) as tb0 by (rewrite <- branch_of_pl_zero; trivial).
  assert (t' ≡ branch_of_pl t' ([], 0)) as tb1 by (rewrite <- branch_of_pl_zero; trivial).
  have h := specexc_branch t t' active t t' se [] 0 down up flow_se flow_update
      tb0 tb1 ru2 _ _.
  rewrite down_0 in h.
  rewrite up_0 in h.
  rewrite unit_dot in h.
  rewrite unit_dot in h.
  have j := h H0 H.
  destruct_ands.
  split; trivial.
  apply valid_of_mov with (x := (branch_total (refinement_of_nat M RI) t active 0)); trivial.
Qed.

End ExchangeProof.
