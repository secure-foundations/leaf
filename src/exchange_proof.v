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

Require Import coq_tricks.Deex.

Context {M} `{!EqDecision M} `{!Countable M} `{!TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.

Definition specific_exchange_cond (ref: Refinement M M) (p m f h s m' f' h' s' : M) :=
  ∃ j l l' ,
  match rel M M ref (dot f p) with
  | None => True
  | Some i1 => m_valid (dot m i1) ->
      dot j s' = f' /\ m = dot l h /\ m' = dot l' h' /\
      match rel M M ref (dot (dot j s) p) with
      | None => False
      | Some i2 => mov (dot l i1) (dot l' i2)
      end
  end.


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

Lemma branchcons_pl t p i
  : branch_of_pl t (p, i) ≡ BranchCons (node_of_pl t (p, i)) (branch_of_pl t (p, S i)).
  Admitted.
  
Lemma cellnode_pl t p i
  : node_of_pl t (p, i) ≡ CellNode (cell_of_pl t (p, i)) (branch_of_pl t (p++[i], 0)).
  Admitted.
  
Lemma branchcons_pl_inv_b t p i b n
  : branch_of_pl t (p, i) ≡ BranchCons n b ->
      b ≡ branch_of_pl t (p, S i).
  Admitted.
  
Lemma branchcons_pl_inv_n t p i b n
  : branch_of_pl t (p, i) ≡ BranchCons n b ->
      n ≡ node_of_pl t (p, i).
  Admitted.
  
Lemma cellnode_pl_inv_b t p i c branch
  : node_of_pl t (p, i) ≡ CellNode c branch -> branch ≡ branch_of_pl t (p++[i], 0).
  Admitted.

Definition branch_of_node (node: Node M) := match node with CellNode _ b => b end.

Lemma branch_of_node_node_of_pl t p i
  : branch_of_node (node_of_pl t (p, i)) ≡ branch_of_pl t (p++[i], 0). Admitted.

Global Instance branch_of_node_proper :
  Proper ((≡) ==> (≡)) branch_of_node. Admitted.

Lemma cell_total_split (cell: Cell M) lt :
  cell_total cell lt = dot (cell_live cell) (cell_total_minus_live cell lt). Admitted.
  
Tactic Notation "full_generalize" constr(t) "as" simple_intropattern(name) :=
  let EQ := fresh in
  let name1 := fresh in
  assert (exists x , x = t) as EQ by (exists t; trivial); destruct EQ as [name1];
    try (rewrite <- EQ);
    (repeat match reverse goal with  
    | [H : context[t] |- _ ] => rewrite <- EQ in H
    end); clear EQ; try (clear name); rename name1 into name.
    
Lemma dot_kjha k j a : (dot (dot a k) j) = (dot (dot j a) k). Admitted.

Lemma valid_reduce m k a :
  m_valid (dot (dot m k) a) -> m_valid (dot m a). Admitted.
  
Lemma dot_aklh a k l h
  : (dot (dot a k) (dot l h)) = dot (dot l a) (dot k h). Admitted.
  
Lemma dot_aklh2 a k l h
    : (dot (dot (dot l h) k) a) = (dot (dot l a) (dot k h)). Admitted.

Lemma dot_jszr (j s z r : M)
        : dot (dot j s) (dot z r) = dot (dot r s) (dot j z). Admitted.
        
Lemma dot_jszr2 (j s z r : M)
        : (dot (dot (dot j s) z) r) = dot(dot r s) (dot j z). Admitted.
  
Lemma dot_comm_right2 (j a k : M) : dot (dot j a) k = dot (dot j k) a. Admitted.

Lemma dot_qklh (q k l h : M)
  : dot (dot q k) (dot l h) = dot (dot k h) (dot q l). Admitted.
    
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
  destruct (rel M M (refinement_of_nat M RI i) (dot f (dot z r))) eqn:fzr.
  - rename m0 into a.
    have myf := myflow (valid_reduce m k a val). clear myflow.
    destruct_ands.
    subst m.
    subst m'.
    destruct (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) eqn:jszr.
    + rename m into a'.
      assert (m_valid (dot (dot a' k) (dot l' h)) /\
        (mov (dot (dot a k) (dot l h)) (dot (dot a' k) (dot l' h)))).
      * assert (dot (dot a k) (dot l h) = dot (dot l a) (dot k h)) as r1 by (apply dot_aklh).
        assert (dot (dot a' k) (dot l' h) = dot (dot l' a') (dot k h)) as r2 by (apply dot_aklh).
        rewrite r1.
        rewrite r2.
        apply mov_monotonic; trivial.
        rewrite <- dot_aklh2. trivial.
      * destruct_ands.
        apply trans with (y := dot (dot a' k) (dot l' h)); trivial.
        
        subst f'.
        rewrite dot_jszr in jszr.
        rewrite dot_jszr2.
        
        assert (m_valid (dot (dot r s) (dot j z))) as m_valid_srjz
         by (apply (rel_valid_left M M (refinement_of_nat M RI i) (dot (dot r s) (dot j z)) a'); trivial).
        assert (mov (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z))) as mov_rsjz
          by (apply mov_monotonic; trivial).
        
        have movr := mov_refines M M (refinement_of_nat M RI i)
            (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z)) a' mov_rsjz jszr.
        deex. destruct_ands.
        rewrite H.
        
        assert (m_valid (dot (dot q' k) (dot l' h)) /\
          (mov (dot (dot a' k) (dot l' h)) (dot (dot q' k) (dot l' h)))).
          -- rewrite <- tpcm_assoc. rewrite <- tpcm_assoc. rewrite <- tpcm_assoc in H0.
             apply mov_monotonic; trivial.
          -- destruct_ands.
              apply trans with (y := (dot (dot q' k) (dot l' h))); trivial.
              rewrite dot_qklh.
              rewrite dot_qklh in H4.
              assert (dot (dot q' k') (dot l' h') = dot (dot k' h') (dot q' l'))
                  by (apply dot_qklh).
              rewrite H6.
              apply mov_monotonic; trivial.
    + contradiction.
  - contradiction.
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
  destruct (rel M M (refinement_of_nat M RI i) (dot f (dot z r))) eqn:fzr.
  - rename m0 into a.
    have myf := myflow (valid_reduce m k a val). clear myflow.
    destruct_ands.
    subst m.
    subst m'.
    destruct (rel M M (refinement_of_nat M RI i) (dot (dot j s) (dot z r))) eqn:jszr.
    + rename m into a'.
      assert (m_valid (dot (dot a' k) (dot l' h)) /\
        (mov (dot (dot a k) (dot l h)) (dot (dot a' k) (dot l' h)))).
      * assert (dot (dot a k) (dot l h) = dot (dot l a) (dot k h)) as r1 by (apply dot_aklh).
        assert (dot (dot a' k) (dot l' h) = dot (dot l' a') (dot k h)) as r2 by (apply dot_aklh).
        rewrite r1.
        rewrite r2.
        apply mov_monotonic; trivial.
        rewrite <- dot_aklh2. trivial.
      * destruct_ands.
        
        subst f'.
        rewrite dot_jszr in jszr.
        rewrite dot_jszr2.
        
        assert (m_valid (dot (dot r s) (dot j z))) as m_valid_srjz
         by (apply (rel_valid_left M M (refinement_of_nat M RI i) (dot (dot r s) (dot j z)) a'); trivial).
        assert (mov (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z))) as mov_rsjz
          by (apply mov_monotonic; trivial).
        
        have movr := mov_refines M M (refinement_of_nat M RI i)
            (dot (dot r s) (dot j z)) (dot (dot r' s') (dot j z)) a' mov_rsjz jszr.
        deex. destruct_ands.
        
        unfold in_refinement_domain.
        rewrite H. trivial.
   + contradiction.
 - contradiction.
Qed.

Lemma m_valid_ca a b c
: m_valid (dot (dot a b) c) -> m_valid (dot c a). Admitted.

Lemma m_valid_bd (a b c d : M)
: m_valid (dot (dot a b) (dot c d)) -> m_valid (dot b d). Admitted.

Lemma m_valid_db (a b c d : M)
: m_valid (dot (dot a b) (dot c d)) -> m_valid (dot d b). Admitted.

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
     destruct x.
     + have fl' := fl (m_valid_ca _ _ _ amval).
       destruct_ands.
       rewrite H1 in amval.
       have am := m_valid_bd _ _ _ _ amval.
       trivial.
     + contradiction.
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
     destruct x.
     + have fl' := fl (m_valid_ca _ _ _ amval).
       destruct_ands.
       destruct (rel M M (refinement_of_nat M RI i)
           (dot (dot j (down (p ++ [i], 0)))
              (node_total_minus_live (refinement_of_nat M RI) (node_of_pl t (p, i)) active))) eqn:de.
       * have rvl := rel_valid_left M M (refinement_of_nat M RI i) _ _ de.
         setoid_rewrite cellnode_pl in rvl.
         unfold node_total_minus_live in rvl.
         have q := m_valid_db _ _ _ _ rvl .
         setoid_rewrite branch_of_node_node_of_pl.
         trivial.
       * contradiction.
    + contradiction.
Qed.

(*Lemma transit_at_node
  (t t' : Branch M)
  (active : Lifetime)
  (branch branch' : Branch M) p i
  (c c' : Cell M)
  (down up : PathLoc -> M)
  (branch1_equiv : branch ≡ branch_of_pl t (p ++ [i], 0))
  (branch2_equiv : branch' ≡ branch_of_pl t' (p ++ [i], 0))
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) branch active 0) (down (p ++ [i], 0))))
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch active 0)
  (batird' : branch_all_total_in_refinement_domain (refinement_of_nat M RI) branch' active 0)
  (mo : mov (dot (branch_total (refinement_of_nat M RI) branch active 0) (down (p ++ [i], 0)))
         (dot (branch_total (refinement_of_nat M RI) branch' active 0) (up (p ++ [i], 0))))
  (ird : in_refinement_domain (refinement_of_nat M RI) i
          (dot (cell_total c active) (branch_total (refinement_of_nat M RI) branch active 0)))
  : in_refinement_domain (refinement_of_nat M RI) i
    (dot (cell_total c' active) (branch_total (refinement_of_nat M RI) branch' active 0)).
Proof.
  have fl := flow_update p i. clear flow_update.
  unfold specific_flow_cond, specific_exchange_cond in fl.
  
  setoid_rewrite branch1_equiv in batird. Admitted.*)

Lemma dot_cba a b c
  : (dot (dot a b) c) = (dot (dot c b) a). Admitted.

Lemma specexc_branch_t t t' active (branch branch': Branch M) p i
  (down up : PathLoc -> M)
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
with specexc_node_t t t' active (node node': Node M) p i
  (down up : PathLoc -> M)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (node_is : node ≡ node_of_pl t (p, i))
  (node'_is : node' ≡ node_of_pl t' (p, i))
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (amval : m_valid (dot (branch_total (refinement_of_nat M RI) (branch_of_node node) active 0) (down (p++[i], 0))))
  (node'_is_trivial : node_trivial node')
  (batird : node_all_total_in_refinement_domain (refinement_of_nat M RI) node active i)
          : node_all_total_in_refinement_domain (refinement_of_nat M RI) node' active i
      /\ mov
        (dot (branch_total (refinement_of_nat M RI) (branch_of_node node) active 0) (down (p++[i], 0)))
        (dot (branch_total (refinement_of_nat M RI) (branch_of_node node') active 0) (up (p++[i], 0))).
        Admitted.

Lemma specexc_branch t t' active (branch branch': Branch M) p i
  (down up : PathLoc -> M)
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
with specexc_node t t' active (node node': Node M) p i
  (down up : PathLoc -> M)
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
        
     have IHbranch := specexc_branch t t' active (branch_of_pl t (p, S i)) branch' p (S i)
                          down up flow_update triv_equiv b_equiv reserved_untouched mval_b.
     clear specexc_branch.
     have IHnode := specexc_node t t' active (node_of_pl t (p, i)) n' p i
                          down up flow_update triv_equiv2 n_equiv reserved_untouched mval_n.
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
      + eapply specexc_branch_t with (t := t) (t' := t'); trivial.
        unfold branch_trivial. trivial.
 - clear specexc_node.
  destruct node, node'. rename b into branch. rename b0 into branch'.
  assert (branch ≡ branch_of_pl t (p ++ [i], 0)) as branch1_equiv
      by (apply cellnode_pl_inv_b with (c := c); symmetry; trivial).
  assert (branch' ≡ branch_of_pl t' (p ++ [i], 0)) as branch2_equiv
      by (apply cellnode_pl_inv_b with (c := c0); symmetry; trivial).
  unfold branch_of_node in amval.
  rewrite node_all_total_in_refinement_domain_unfold in batird.
  destruct_ands. rename H into ird. rename H0 into batird.
  have Ihb := specexc_branch t t' active branch branch' (p++[i]) 0 down up flow_update
      branch1_equiv branch2_equiv reserved_untouched amval batird.
  destruct_ands.
  repeat split; trivial.
Qed.
 
Lemma specific_flows_preserve_branch_all_total_in_refinement_domain t t' active
  (down up : PathLoc -> M)
  (flow_update : ∀ p i , specific_flow_cond p i t t' active down up)
  (down_0 : down ([], 0) = unit)
  (up_0 : up ([], 0) = unit)
  (batird : branch_all_total_in_refinement_domain (refinement_of_nat M RI) t active 0)
          : branch_all_total_in_refinement_domain (refinement_of_nat M RI) t' active 0.
Proof.
