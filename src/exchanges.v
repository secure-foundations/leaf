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
Require Import Burrow.exchange_proof.
Require Import Burrow.resource_proofs.

Require Import coq_tricks.Deex.

Context {M} `{!EqDecision M} `{!TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.

Definition view_exchange_cond (ref: Refinement M M) (view: M -> Prop) (m f h s m' f' h' s' : M) :=
  ∀ p , view p -> specific_exchange_cond ref p m f h s m' f' h' s'.
   
Definition view_flow_cond p i (b t t': Branch M) (active: Lifetime) (down up : PathLoc -> M) :=
  let q := (p, i) in
  let r := (p, S i) in
  let s := (p ++ [i], 0) in
  view_exchange_cond (refinement_of_nat M RI i)
      (node_view (refinement_of_nat M RI) (node_of_pl b q) active)
      (down q) (node_live (node_of_pl t q))
      (down r) (down s)
      (up q) (node_live (node_of_pl t' q))
      (up r) (up s).
      
Lemma specific_exchange_cond_add_stuff (ref: Refinement M M) (p m f h s m' f' h' s' stuff : M) :
  specific_exchange_cond ref (dot p stuff) m f h s m' f' h' s'
      -> specific_exchange_cond ref p m (dot f stuff) h s m' (dot f' stuff) h' s'.
Proof. unfold specific_exchange_cond. intro. rewrite <- tpcm_assoc.
deex. exists (dot j stuff). exists l. exists l'.
rewrite <- tpcm_assoc. assert (dot p stuff = dot stuff p) by (apply tpcm_comm).
rewrite <- H0. trivial. destruct (rel M M ref (dot f (dot p stuff))); trivial.
intro. have ab := H H1. destruct_ands; repeat split; trivial.
- replace (dot stuff s') with (dot s' stuff).
  + rewrite tpcm_assoc. f_equal. trivial.
  + apply tpcm_comm.
- replace ((dot (dot (dot j stuff) s) p)) with ((dot (dot j s) (dot p stuff))); trivial.
  replace (dot p stuff) with (dot stuff p) by (apply tpcm_comm).
  rewrite tpcm_assoc. f_equal.
  rewrite <-tpcm_assoc.
  rewrite <-tpcm_assoc.
  f_equal. apply tpcm_comm.
Qed.

Lemma flows_preserve_branch_all_total_in_refinement_domain b t t' active
  (se: listset PathLoc)
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , view_flow_cond p i b t t' active down up)
  (down_0 : down ([], 0) = unit)
  (up_0 : up ([], 0) = unit)
  (reserved_untouched : ∀ pl, cell_total_minus_live (cell_of_pl t pl) active = cell_total_minus_live (cell_of_pl t' pl) active)
  (batird : valid_totals (refinement_of_nat M RI) (t⋅b) active)
          : valid_totals (refinement_of_nat M RI) (t'⋅b) active.
Proof.
  apply specific_flows_preserve_branch_all_total_in_refinement_domain with
      (t0 := t⋅b) (down0 := down) (up0 := up) (se0 := se); trivial.
  - intros.
    unfold specific_flow_cond. unfold view_flow_cond in flow_update.
    have flow_update' := flow_update p i. clear flow_update. rename flow_update' into flow_update.
    unfold view_exchange_cond in flow_update.

    assert (node_live (node_of_pl (t ⋅ b) (p, i)) =
        dot (node_live (node_of_pl t (p, i))) (node_live (node_of_pl b (p,i))))
    by (setoid_rewrite <- node_of_pl_op; apply node_live_op).
    rewrite H. clear H.

    assert (node_live (node_of_pl (t' ⋅ b) (p, i)) =
        dot (node_live (node_of_pl t' (p, i))) (node_live (node_of_pl b (p,i))))
    by (setoid_rewrite <- node_of_pl_op; apply node_live_op).
    rewrite H. clear H.

    (*rewrite tpcm_assoc. rewrite tpcm_assoc.*)

    apply specific_exchange_cond_add_stuff.

    apply flow_update. clear flow_update.
    apply node_view_le2.
    apply node_view_le with (b0 := node_of_pl t (p, i)).
    setoid_rewrite node_op_comm.
    setoid_rewrite node_of_pl_op.

    assert (view_sat (node_view (refinement_of_nat M RI) (node_of_pl (t ⋅ b) (p, i)) active)
      (node_total_minus_live (refinement_of_nat M RI) (node_of_pl (t ⋅ b) (p, i)) active)).
    + apply node_view_le_total_minus_live with (idx := plend (p,i)).
      * apply multiset_le_refl.
      * unfold valid_totals in batird. destruct_ands. rename H into batird.
        generalize batird. rewrite forall_equiv_branch_all_total_in_refinement_domain.
          intro. apply H.
    + unfold view_sat in H. trivial.
 - intro. setoid_rewrite <- cell_of_pl_op.
    rewrite cell_total_minus_live_op.
    rewrite cell_total_minus_live_op.
    rewrite reserved_untouched. trivial.
Qed.

 
Lemma view_exchange_cond_of_no_change ref view x y
  : view_exchange_cond ref view x y unit unit x y unit unit.
Proof. unfold view_exchange_cond. intro.
  deex. unfold specific_exchange_cond.
  exists y. exists x. exists x. rewrite unit_dot.
  full_generalize (rel M M ref (dot y p)) as t.
  destruct t; trivial.
  repeat split; trivial.
  - rewrite unit_dot. trivial.
  - rewrite unit_dot. trivial.
  - apply reflex.
Qed.

Lemma view_exchange_cond_of_no_change2 ref view x y z w
  : view_exchange_cond ref view x y x y z w z w.
Proof. unfold view_exchange_cond. intro.
  deex. unfold specific_exchange_cond. intro.
  exists unit. exists unit. exists unit.
  repeat (rewrite unit_dot_left). destruct (rel M M ref (dot y p)); trivial.
  intro. repeat split. apply reflex.
Qed.

Lemma specific_exchange_cond_of_whatever ref a x y m
    : specific_exchange_cond ref a x (dot m y) x m unit y unit unit.
Proof.
  unfold specific_exchange_cond. exists y. exists unit. exists unit.
  replace (dot y m) with (dot m y) by (apply tpcm_comm).
  repeat (rewrite unit_dot_left). destruct (rel M M ref (dot (dot m y) a)); trivial.
  intro. repeat split.
  - apply unit_dot.
  - apply reflex.
Qed.

Lemma specific_exchange_cond_of_whatever2 ref a x y
    : specific_exchange_cond ref a x y x unit unit y unit unit.
Proof.
  unfold specific_exchange_cond. exists y. exists unit. exists unit.
  rewrite unit_dot.
  destruct (rel M M ref (dot y a)); trivial.
  intro. repeat split; trivial.
  - rewrite unit_dot_left. trivial.
  - rewrite unit_dot. trivial.
  - apply reflex.
Qed.

 
Lemma view_exchange_cond_of_borrow_exchange_cond alpha ri gamma z m f m' f' p i borrow_branch
  (i_matches : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
  (active_lifetime : multiset nat)
  (exchange_cond : borrow_exchange_cond (refinement_of ri) z m f m' f')
  (isb : lmap_is_borrow active_lifetime (ExtLoc alpha ri gamma) z borrow_branch)
  : view_exchange_cond
    (refinement_of_nat M RI i)
    (node_view (refinement_of_nat M RI) (node_of_pl (as_tree borrow_branch) (p,i)) active_lifetime)
    m f unit unit m' f' unit unit.
Proof.
  have h := refinement_of_nat_eq_refinement_of_of_in_pls_of_loc p i alpha ri gamma.
  rewrite h; trivial. clear h.
  unfold view_exchange_cond. unfold specific_exchange_cond. unfold borrow_exchange_cond in *.
  unfold lmap_is_borrow in *.
  intro extra. intro.
  exists f'. exists m. exists m'.
  assert (tpcm_le z extra).
  - apply isb with (pl := (p,i)); trivial.
  - unfold tpcm_le in H0. deex. rewrite <- H0.
    rewrite tpcm_assoc. 
    rewrite tpcm_assoc. have ec := exchange_cond c.
    destruct (rel M M (refinement_of ri) (dot (dot f z) c)); trivial.
    intro Q.
    have ec2 := ec Q. repeat split.
    + apply unit_dot.
    + rewrite unit_dot. trivial.
    + rewrite unit_dot. trivial.
    + repeat (rewrite unit_dot). repeat (rewrite unit_dot_left). trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow(kappa, gamma, z) . live(gamma, m) . live(alpha ref gamma, y)
                         --> live(gamma, m') . live(alpha ref gamma, y') *)
  
Lemma cell_total_minus_live_cell_of_pl_build_empty (loc: Loc RI) (f:M) pl lt
  : cell_total_minus_live (cell_of_pl (build loc (CellCon f ∅)) pl) lt = unit.
  Admitted.
  
Lemma borrow_exchange b kappa gamma (m f z m' f': M) alpha (ri: RI)
  (isb: is_borrow kappa (ExtLoc alpha ri gamma) z b)
  (exchange_cond: borrow_exchange_cond (refinement_of ri) z m f m' f')
  (si: state_inv (active kappa ⋅ live (ExtLoc alpha ri gamma) f ⋅ b ⋅ live gamma m))
     : state_inv (active kappa ⋅ live (ExtLoc alpha ri gamma) f' ⋅ b ⋅ live gamma m').
Proof.
  unfold state_inv in *. destruct b. unfold live in *. unfold "⋅", state_op in *. split.
  - destruct si. trivial.
  - destruct si. clear H. rename H0 into sinv.
    repeat (rewrite multiset_add_empty).
    repeat (rewrite multiset_add_empty in sinv).
    setoid_rewrite as_tree_op.
    repeat (setoid_rewrite as_tree_op).
    repeat (setoid_rewrite as_tree_op in sinv).
    setoid_rewrite (as_tree_singleton (ExtLoc alpha ri gamma) (CellCon f' ∅)).
    setoid_rewrite (as_tree_singleton gamma (CellCon m' ∅)).
    setoid_rewrite as_tree_singleton in sinv.
    rename l0 into borrow_branch.
    setoid_rewrite assoc_comm.
    setoid_rewrite assoc_comm in sinv.
    
    assert (is_borrow (multiset_add kappa l) (ExtLoc alpha ri gamma) z
             (StateCon l borrow_branch)) by (apply is_borrow_weaken_lifetime; trivial).
    clear isb; rename H into isb.
    
    unfold is_borrow in isb.
    
    full_generalize (multiset_add kappa l) as active_lifetime.
    
    apply flows_preserve_branch_all_total_in_refinement_domain
      with (t := build (ExtLoc alpha ri gamma) (CellCon f ∅) ⋅ build gamma (CellCon m ∅))
      (se := updog_se gamma alpha ri)
      (down := updog m gamma alpha ri)
      (up   := updog m' gamma alpha ri)
      ; trivial.
    + intros. split; apply updog_se_okay; trivial.

    + intros. unfold view_flow_cond.
      have the_case : Decision ((p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma)) by solve_decision.
      destruct the_case.
    
    (* interesting case: ext location *)
    * rewrite (updog_eq_m p i); trivial. rewrite (updog_eq_m p i); trivial.
      rewrite (updog_eq_unit1 p i); trivial. rewrite (updog_eq_unit1 p i); trivial.
      rewrite (updog_eq_unit2 p i); trivial. rewrite (updog_eq_unit2 p i); trivial.
      rewrite <- node_of_pl_op. rewrite <- node_of_pl_op.
      repeat (rewrite unit_dot).
      repeat (rewrite unit_dot_left).
      rewrite node_live_op. rewrite node_live_op.
      rewrite node_node_cell_cell. rewrite node_node_cell_cell.
      rewrite node_node_cell_cell. rewrite node_node_cell_cell.
      assert ((p, i) ∉ pls_of_loc gamma) by (apply pl_not_in_of_pl_in_extloc with (alpha:=alpha) (ri:=ri); trivial ).
      rewrite build_spec; trivial.
      rewrite build_rest_triv; trivial.
      rewrite build_spec; trivial.
      rewrite build_rest_triv; trivial.
      unfold cell_live. unfold triv_cell.
      repeat (rewrite unit_dot).
      apply (view_exchange_cond_of_borrow_exchange_cond alpha ri gamma z); trivial.
      
    * have the_case2 : Decision ((p, i) ∈ pls_of_loc gamma) by solve_decision.
      destruct the_case2.
      
      (* semi-interesting case: base location *)
      --
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite <- (updog_other_eq_both p i); trivial.
        (*rewrite (updog_base_eq_unit1 p i); trivial. rewrite (updog_base_eq_unit1 p i); trivial.
        rewrite (updog_base_eq_unit2 p i); trivial. rewrite (updog_base_eq_unit2 p i); trivial.*)
        rewrite (updog_base_eq_m p i); trivial. rewrite (updog_base_eq_m p i); trivial.
        
        rewrite <- node_of_pl_op. rewrite <- node_of_pl_op.
        rewrite node_live_op. rewrite node_live_op.
        repeat (rewrite unit_dot).
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite build_rest_triv; trivial.
        rewrite build_spec; trivial.
        rewrite build_rest_triv; trivial.
        rewrite build_spec; trivial.
        unfold cell_live, triv_cell.
        repeat (rewrite unit_dot_left).
        (*rewrite tpcm_comm.*)
        assert (dot m m' = dot m' m) by apply tpcm_comm.
        (*rewrite H.*)
        apply view_exchange_cond_of_no_change2.

      (* uninteresting case *)
      --
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite updog_other_eq_unit; trivial.
        rewrite updog_other_eq_unit; trivial.

        rewrite <- node_of_pl_op. rewrite <- node_of_pl_op.
        rewrite node_live_op. rewrite node_live_op.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite build_rest_triv; trivial.
        rewrite build_rest_triv; trivial.
        rewrite build_rest_triv; trivial.
        rewrite build_rest_triv; trivial.
        unfold cell_live, triv_cell. repeat (rewrite unit_dot).
        apply view_exchange_cond_of_no_change2.
   + setoid_rewrite <- cell_of_pl_op.
     setoid_rewrite cell_total_minus_live_op.
     intro.
     repeat (rewrite cell_total_minus_live_cell_of_pl_build_empty). trivial.
Qed.


(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(I(f), gamma) -> live(f, alpha ref gamma) *)

Definition is_fresh_nat : Branch M -> nat -> Prop. Admitted.

Definition alloc_alpha : Branch M -> RI -> nat. Admitted.

Lemma is_fresh_alloc branch ri : is_fresh_nat branch
    (nat_of_extstep (alloc_alpha branch ri) ri). Admitted.

Lemma trivial_node_at_fresh (b: Branch M) p i
  (is_fresh: is_fresh_nat b i)
  : node_trivial (node_of_pl b (p, i)). Admitted.
    
Lemma i_value_of_pls_of_loc_ext p i gamma alpha (ri: RI)
  (in_pls: (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
  : i = nat_of_extstep alpha ri. Admitted.

Lemma node_total_minus_live_of_trivial ref node lt
  (istriv: node_trivial node)
  : node_total_minus_live ref node lt = unit. Admitted.

Lemma cell_triv_node_triv_op_right a b
  (nodetriv: node_trivial (a ⋅ b))
  : cell_trivial (match b with CellNode c _ => c end). Admitted.

Lemma ri_of_nat_nat_of_extstep alpha ri
  : ri_of_nat RI (nat_of_extstep alpha ri) = ri. Admitted.

Lemma initialize_ext gamma m f p ri
  (is_rel: rel M M (refinement_of ri) f = Some m)
  (si: state_inv (live gamma m ⋅ p))
  : ∃ alpha , state_inv (live (ExtLoc alpha ri gamma) f ⋅ p).
Proof.
  destruct p. unfold live in si. rename l0 into p.
  exists (alloc_alpha (build gamma (CellCon m ∅) ⋅ as_tree p) ri).
  unfold state_inv, live, "⋅", state_op in *. destruct_ands. split; trivial.
  
  rename H0 into batird.
  setoid_rewrite as_tree_op.
  setoid_rewrite as_tree_op in batird.
  
  setoid_rewrite as_tree_singleton.
  setoid_rewrite as_tree_singleton in batird.
  
  full_generalize (multiset_add empty_lifetime l) as lt.
  full_generalize (as_tree p) as q. clear p.
  
  eapply specific_flows_preserve_branch_all_total_in_refinement_domain
    with (t := (build gamma (CellCon m ∅) ⋅ q))
         (se := updog_se gamma (alloc_alpha (branch_op (build gamma (CellCon m ∅)) q) ri) ri)
         (down := updog m gamma (alloc_alpha (branch_op (build gamma (CellCon m ∅)) q) ri) ri)
         (up   := λ pl, unit); trivial.
         
  - intros. split; trivial. apply updog_se_okay; trivial.
  
  - assert (is_fresh_nat (branch_op (build gamma (CellCon m ∅)) q) (nat_of_extstep (alloc_alpha (branch_op (build gamma (CellCon m ∅)) q) ri) ri)) by (apply is_fresh_alloc; trivial).
    rename H0 into is_fresh.

    full_generalize (alloc_alpha (branch_op (build gamma (CellCon m ∅)) q) ri) as alpha.


    unfold specific_flow_cond.
    repeat (rewrite unit_dot_left).
    repeat (rewrite unit_dot).

    intros.
    have the_case : Decision ((p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma)) by solve_decision.
    destruct the_case.

    (* interesting case: ext location *)
  
  + rewrite (updog_eq_m p i); trivial. 
    rewrite (updog_eq_unit1 p i); trivial.
    rewrite (updog_eq_unit2 p i); trivial.
    rewrite <- node_of_pl_op. rewrite <- node_of_pl_op.
    repeat (rewrite unit_dot).
    repeat (rewrite unit_dot_left).
    rewrite node_live_op. rewrite node_live_op.
    rewrite node_node_cell_cell. rewrite node_node_cell_cell.
    rewrite node_node_cell_cell.
    
    assert ((p, i) ∉ pls_of_loc gamma) by (apply pl_not_in_of_pl_in_extloc with (alpha:=alpha) (ri:=ri); trivial ).
    rewrite build_rest_triv; trivial.
    
    rewrite build_spec; trivial.
    unfold cell_live, triv_cell.
    
    assert (node_trivial (node_of_pl ((build gamma (CellCon m ∅)) ⋅ q) (p, i))) as EqTrivNode by (
      apply trivial_node_at_fresh;
      rewrite <- (i_value_of_pls_of_loc_ext p i gamma) in is_fresh; trivial).
    
    rewrite <- node_of_pl_op in EqTrivNode.
    
    rewrite node_total_minus_live_of_trivial; trivial.
    
    have h := (cell_triv_node_triv_op_right _ _ EqTrivNode).
    unfold cell_of_pl. destruct (node_of_pl q (p, i)).
    unfold cell_trivial in h. destruct c. destruct_ands.
    subst m0.
    repeat (rewrite unit_dot).
    
    unfold specific_exchange_cond.
    exists f. exists m. exists unit.
    repeat (rewrite unit_dot).
    unfold refinement_of_nat.
    have j := i_value_of_pls_of_loc_ext p i gamma alpha ri e. rewrite j.
    rewrite ri_of_nat_nat_of_extstep.
    rewrite is_rel.
    rewrite rel_unit.
    repeat (rewrite unit_dot).
    repeat (rewrite unit_dot_left).
    intro. repeat split; trivial. apply reflex.
    
    + have the_case2 : Decision ((p, i) ∈ pls_of_loc gamma) by solve_decision.
      destruct the_case2.
      
      (* semi-interesting case: base location *)
      * 
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite (updog_base_eq_m p i); trivial.
        
        rewrite <- node_of_pl_op. rewrite <- node_of_pl_op.
        rewrite node_live_op. rewrite node_live_op.
        repeat (rewrite unit_dot).
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell.
        rewrite build_spec; trivial.
        rewrite build_rest_triv; trivial.
        unfold cell_live, triv_cell.
        repeat (rewrite unit_dot_left).
        apply specific_exchange_cond_of_whatever.

      (* uninteresting case *)
      * 
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite updog_other_eq_unit; trivial.

        rewrite <- node_of_pl_op. rewrite <- node_of_pl_op.
        rewrite node_live_op. rewrite node_live_op.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell.
        rewrite build_rest_triv; trivial.
        rewrite build_rest_triv; trivial.
        repeat (rewrite unit_dot_left).
        apply specific_exchange_cond_of_whatever2.
  - setoid_rewrite <- cell_of_pl_op.
    setoid_rewrite cell_total_minus_live_op.
    intro.
    repeat (rewrite cell_total_minus_live_cell_of_pl_build_empty). trivial.
Qed.

