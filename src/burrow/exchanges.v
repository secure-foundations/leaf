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
Require Import Burrow.assoc_comm.
Require Import Burrow.resource_proofs.
Require Import Burrow.fresh.
Require Import Burrow.updog.
Require Import Burrow.building.

Require Import coq_tricks.Deex.

Section Exchanges.

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
rewrite <- H0. trivial.
intros. have ab := H H1 H2.
assert (((dot (dot (dot j stuff) s) p)) = ((dot (dot j s) (dot p stuff)))) as asdf.
- replace (dot p stuff) with (dot stuff p) by (apply tpcm_comm).
  rewrite tpcm_assoc. f_equal.
  rewrite <-tpcm_assoc.
  rewrite <-tpcm_assoc.
  f_equal. apply tpcm_comm.
- destruct_ands; repeat split; trivial.
  + subst. rewrite <- tpcm_assoc. f_equal. apply tpcm_comm.
  + rewrite asdf. trivial.
  + rewrite asdf. trivial.
Qed.

Lemma cell_reserved_op a b
    : cell_reserved (a ⋅ b) ≡ cell_reserved a ∪ cell_reserved b.
Proof. unfold cell_reserved, "⋅", cell_op. destruct a, b. trivial.
Qed.

Lemma flows_preserve_branch_all_total_in_refinement_domain (b t t': Branch M) (active: Lifetime)
  (se: gset PathLoc)
  (down up : PathLoc -> M)
  (flow_se : ∀ p i , (p, i) ∉ se -> up (p, i) = unit /\ down (p, i) = unit)
  (flow_update : ∀ p i , view_flow_cond p i b t t' active down up)
  (down_0 : down ([], 0) = unit)
  (up_0 : up ([], 0) = unit)
  (reserved_untouched : ∀ pl, cell_reserved (cell_of_pl t pl)
                            ≡ cell_reserved (cell_of_pl t' pl))
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
    setoid_rewrite cell_reserved_op.
    setoid_rewrite reserved_untouched.
    trivial.
Qed.
 
Lemma view_exchange_cond_of_no_change ref view x y
  : view_exchange_cond ref view x y unit unit x y unit unit.
Proof. unfold view_exchange_cond. intro.
  deex. unfold specific_exchange_cond.
  exists y. exists x. exists x. rewrite unit_dot.
  full_generalize (rel M M ref (dot y p)) as t.
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
  repeat (rewrite unit_dot_left).
  intro. repeat split; trivial. apply reflex.
Qed.

Lemma specific_exchange_cond_of_whatever ref a x y m
    : specific_exchange_cond ref a x (dot m y) x m unit y unit unit.
Proof.
  unfold specific_exchange_cond. exists y. exists unit. exists unit.
  replace (dot y m) with (dot m y) by (apply tpcm_comm).
  repeat (rewrite unit_dot_left).
  intro. repeat split; trivial.
  - apply unit_dot.
  - apply reflex.
Qed.

Lemma specific_exchange_cond_of_whatever2 ref a x y z
    : specific_exchange_cond ref a x y x unit z y z unit.
Proof.
  unfold specific_exchange_cond. exists y. exists unit. exists unit.
  rewrite unit_dot.
  intro. repeat split; trivial.
  - rewrite unit_dot_left. trivial.
  - rewrite unit_dot_left. trivial.
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
  intro extra. intros.
  exists f'. exists m. exists m'.
  intros.
  (*destruct (rel M M (refinement_of ri) (dot f extra)) eqn:meqn; trivial.*)
  assert (tpcm_le z extra).
  - apply isb with (pl := (p,i)); trivial.
    apply m_valid_of_right_dot with (a := f).
    apply (rel_valid_left M M (refinement_of ri) (dot f extra)).
    trivial.
  - unfold tpcm_le in H2. deex.
    subst extra.
    have ec := exchange_cond c.
    rewrite tpcm_assoc in H0.
    have ec2 := ec H0.
    destruct_ands.
    repeat (rewrite unit_dot). repeat split; trivial.
    + rewrite tpcm_assoc. trivial.
    + rewrite tpcm_assoc. rewrite tpcm_assoc. trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow(kappa, alpha ref gamma, z) . live(gamma, m) . live(alpha ref gamma, y)
                         --> live(gamma, m') . live(alpha ref gamma, y') *)
  
Lemma cell_reserved_cell_of_pl_build_empty (loc: Loc RI) (f:M) pl
  : cell_reserved (cell_of_pl (build loc (CellCon f ∅)) pl) ≡ ∅.
Proof.
  have h : Decision (pl ∈ pls_of_loc loc) by solve_decision. destruct h.
  - setoid_rewrite build_spec; trivial.
  - setoid_rewrite build_rest_triv; trivial.
Qed.
  
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
      assert ((p, i) ∉ pls_of_loc gamma) by (apply pl_not_in_of_pl_in_extloc with (alpha0:=alpha) (ri0:=ri); trivial ).
      setoid_rewrite build_spec at 1; trivial.
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      setoid_rewrite build_rest_triv at 1; trivial.
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
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_spec at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_spec at 1; trivial.
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
        setoid_rewrite build_rest_triv; trivial.
        unfold cell_live, triv_cell. repeat (rewrite unit_dot).
        apply view_exchange_cond_of_no_change2.
   + setoid_rewrite <- cell_of_pl_op.
     setoid_rewrite cell_reserved_op.
     intro.
     repeat (rewrite cell_reserved_cell_of_pl_build_empty). trivial.
Qed.

Lemma bev_move (a b c d e f : State M RI)
  : a ⋅ b ⋅ c ⋅ d ⋅ e ⋅ f ≡ a ⋅ b ⋅ (c ⋅ (e ⋅ f)) ⋅ d.
Proof. solve_assoc_comm. Qed.

Lemma is_borrow_op kappa gamma z b b'
  : is_borrow kappa gamma z b -> is_borrow kappa gamma z (b ⋅ b').
Proof. intros. unfold is_borrow in *. destruct b, b'.
  unfold "⋅", state_op, lmap_is_borrow in *.
  intros. apply H with (pl := pl); trivial.
  setoid_rewrite as_tree_op in H2.
  setoid_rewrite <- node_of_pl_op in H2.
  eapply node_view_le. apply H2.
Qed.

Lemma borrow_exchange_valid b kappa gamma (m f z m' f': M) alpha (ri: RI) (p : State M RI)
  (isb: is_borrow kappa (ExtLoc alpha ri gamma) z b)
  (exchange_cond: borrow_exchange_cond (refinement_of ri) z m f m' f')
  (si: ✓ (active kappa ⋅ live (ExtLoc alpha ri gamma) f ⋅ b ⋅ live gamma m ⋅ p))
     : ✓ (active kappa ⋅ live (ExtLoc alpha ri gamma) f' ⋅ b ⋅ live gamma m' ⋅ p).
Proof.
  unfold "✓", state_valid in *. deex. exists p0.
  setoid_rewrite bev_move.
  setoid_rewrite bev_move in si.
  apply borrow_exchange with (m := m) (f := f) (z := z); trivial.
  apply is_borrow_op; trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow(kappa, gamma, z) . live(gamma, m)
                         --> live(gamma, m') *)
                          
Lemma view_exchange_cond_of_borrow_exchange_cond_normal gamma z m m' p i borrow_branch
  (i_matches : (p, i) ∈ pls_of_loc gamma)
  (active_lifetime : multiset nat)
  (exchange_cond : mov (dot m z) (dot m' z))
  (isb : lmap_is_borrow active_lifetime gamma z borrow_branch)
  : view_exchange_cond
    (refinement_of_nat M RI i)
    (node_view (refinement_of_nat M RI) (node_of_pl (as_tree borrow_branch) (p,i)) active_lifetime)
    unit m unit unit unit m' unit unit.
Proof.
  unfold view_exchange_cond. unfold specific_exchange_cond. unfold borrow_exchange_cond in *.
  unfold lmap_is_borrow in *.
  intro extra. intro.
  exists m'. exists unit. exists unit.
  intros.
  assert (tpcm_le z extra).
  - apply isb with (pl := (p,i)); trivial.
    apply m_valid_of_right_dot with (a := m).
    apply (rel_valid_left M M (refinement_of_nat M RI i) (dot m extra)).
    trivial.
  - unfold tpcm_le in H2. deex. subst extra.
    repeat (rewrite unit_dot).
    
    assert (mov (dot (dot m z) c) (dot (dot m' z) c)) as themov.
      + apply mov_monotonic; trivial.
        have j := rel_valid_left M M (refinement_of_nat M RI i) (dot m (dot z c)) H0.
        rewrite <- tpcm_assoc. trivial.
      + rewrite tpcm_assoc in H0.
        have mr := mov_refines M M (refinement_of_nat M RI i)
          (dot (dot m z) c) (dot (dot m' z) c) themov H0.
        destruct_ands.
        repeat split; trivial.
        * rewrite tpcm_assoc. trivial.
        * rewrite tpcm_assoc. rewrite tpcm_assoc.
            repeat (rewrite unit_dot_left).
            trivial.
Qed.
  
Lemma borrow_exchange_normal b kappa gamma (m z m' : M)
  (isb: is_borrow kappa gamma z b)
  (exchange_cond: mov (dot m z) (dot m' z))
  (si: state_inv (active kappa ⋅ live gamma m ⋅ b))
     : state_inv (active kappa ⋅ live gamma m' ⋅ b).
Proof.
  unfold state_inv in *. destruct b. unfold live in *. unfold "⋅", state_op in *. split.
  - destruct si. trivial.
  - destruct si. clear H. rename H0 into sinv.
    repeat (rewrite multiset_add_empty).
    repeat (rewrite multiset_add_empty in sinv).
    setoid_rewrite as_tree_op.
    setoid_rewrite empty_op_lmap.
    repeat (setoid_rewrite as_tree_op).
    setoid_rewrite as_tree_op in sinv.
    setoid_rewrite empty_op_lmap in sinv.
    setoid_rewrite (as_tree_singleton gamma (CellCon m' ∅)).
    setoid_rewrite as_tree_singleton in sinv.
    rename l0 into borrow_branch.
    
    assert (is_borrow (multiset_add kappa l) (gamma) z
             (StateCon l borrow_branch)) by (apply is_borrow_weaken_lifetime; trivial).
    clear isb; rename H into isb.
    
    unfold is_borrow in isb.
    
    full_generalize (multiset_add kappa l) as active_lifetime.
    
    apply flows_preserve_branch_all_total_in_refinement_domain
      with (t := build gamma (CellCon m ∅))
      (se := ∅)
      (down := λ pl, unit)
      (up   := λ pl, unit)
      ; trivial.
    + intros. split; trivial.

    + intros. unfold view_flow_cond.
      have the_case : Decision ((p, i) ∈ pls_of_loc gamma) by solve_decision.
      destruct the_case.
    
    (* interesting case: main location *)
    * 
      repeat (rewrite unit_dot).
      repeat (rewrite unit_dot_left).
      rewrite node_node_cell_cell. rewrite node_node_cell_cell.
      setoid_rewrite build_spec at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      unfold cell_live. unfold triv_cell.
      repeat (rewrite unit_dot).
      
      apply (view_exchange_cond_of_borrow_exchange_cond_normal gamma z); trivial.
      
    * 
      (* uninteresting case *)
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        unfold cell_live, triv_cell. repeat (rewrite unit_dot).
        apply view_exchange_cond_of_no_change2.
   + intro. 
     repeat (rewrite cell_reserved_cell_of_pl_build_empty). trivial.
Qed.

Lemma bev_move2 (a b c d e : State M RI)
  : a ⋅ b ⋅ c ⋅ d ⋅ e ≡ a ⋅ b ⋅ (c ⋅ (d ⋅ e)).
Proof. solve_assoc_comm. Qed.

Lemma borrow_exchange_normal_valid b kappa gamma (m z m' : M) (p: State M RI)
  (isb: is_borrow kappa gamma z b)
  (exchange_cond: mov (dot m z) (dot m' z))
  (si: state_valid (active kappa ⋅ live gamma m ⋅ b ⋅ p))
     : state_valid (active kappa ⋅ live gamma m' ⋅ b ⋅ p).
Proof.
  unfold "✓", state_valid in *. deex. exists p0.
  setoid_rewrite bev_move2.
  setoid_rewrite bev_move2 in si.
  apply borrow_exchange_normal with (m:=m) (z:=z); trivial.
  apply is_borrow_op; trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(I(f), gamma) -> live(f, alpha ref gamma) *)
    
Lemma node_total_minus_live_of_trivial ref node lt
  (istriv: node_trivial node)
  : node_total_minus_live ref node lt = unit.
Proof. unfold node_total_minus_live. destruct node. unfold node_trivial in istriv.
  destruct_ands. unfold cell_trivial in H. destruct c. destruct_ands.
  unfold cell_total_minus_live. rewrite H.
  unfold sum_reserved_over_lifetime. rewrite set_fold_empty.
  rewrite branch_total_of_trivial; trivial. rewrite unit_dot. trivial. Qed.

(*
Proof. unfold node_trivial in nodetriv. destruct a, b.
  unfold "⋅", node_op in nodetriv. destruct_ands.
  clear H0. unfold "⋅" in H. unfold cell_op in H. destruct c, c0.
  unfold cell_trivial in *. destruct_ands. split.
  - set_solver.
  -  *)

Lemma initialize_ext gamma m f p ri
  (is_rel_def: rel_defined M M (refinement_of ri) f)
  (is_rel: rel M M (refinement_of ri) f = m)
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
    
    assert ((p, i) ∉ pls_of_loc gamma) by (apply pl_not_in_of_pl_in_extloc with (alpha0:=alpha) (ri0:=ri); trivial ).
    setoid_rewrite build_rest_triv at 1; trivial.
    
    setoid_rewrite build_spec at 1; trivial.
    unfold cell_live, triv_cell.
    
    assert (is_fresh_nat (q) (nat_of_extstep alpha ri))
      as is_fresh_q by (eapply is_fresh_nat_of_op; apply is_fresh).
    
    assert (node_trivial (node_of_pl (q) (p, i))) as EqTrivNode_q by (
      apply trivial_node_at_fresh;
      rewrite <- (i_value_of_pls_of_loc_ext p i gamma) in is_fresh_q; trivial).
      
    assert (node_trivial (node_of_pl ((build gamma (CellCon m ∅)) ⋅ q) (p, i))) as EqTrivNode by (
      apply trivial_node_at_fresh;
      rewrite <- (i_value_of_pls_of_loc_ext p i gamma) in is_fresh; trivial).
    
    rewrite <- node_of_pl_op in EqTrivNode.
    rewrite node_total_minus_live_of_trivial; trivial.
    
    (*assert (cell_trivial (cell_of_pl q (p, i))) as EqTrivCell_q by
     (unfold cell_of_pl; destruct (node_of_pl q (p, i)); unfold node_trivial in EqTrivNode_q;
      destruct_ands; trivial).*)
    
    unfold cell_of_pl. destruct (node_of_pl q (p, i)).
    unfold node_trivial in EqTrivNode_q. destruct_ands.
    unfold cell_trivial in H1. destruct c. destruct_ands.
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
        setoid_rewrite build_spec at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
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
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        repeat (rewrite unit_dot_left).
        apply specific_exchange_cond_of_whatever2.
  - setoid_rewrite <- cell_of_pl_op.
    setoid_rewrite cell_reserved_op.
    intro.
    repeat (rewrite cell_reserved_cell_of_pl_build_empty). trivial.
Qed.

Lemma initialize_ext_valid gamma m f p ri
  (is_rel_def: rel_defined M M (refinement_of ri) f)
  (is_rel: rel M M (refinement_of ri) f = m)
  (si: ✓(live gamma m ⋅ p))
  : ∃ alpha , ✓(live (ExtLoc alpha ri gamma) f ⋅ p).
Proof.
  unfold "✓", state_valid in *.
  setoid_rewrite <- state_assoc. deex.
  setoid_rewrite <- state_assoc in si.
  have h := initialize_ext gamma m f (p⋅p0) ri is_rel_def is_rel si.
  deex. exists alpha. exists p0. trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* nothing -> live(m, alpha) *)

Lemma initialize_normal (m: M) p
  (is_val: m_valid m)
  (si: state_inv p)
  : ∃ alpha , state_inv (live (BaseLoc RI alpha) m ⋅ p).
Proof.
  destruct p. unfold live in si. rename l0 into p.
  exists (alloc_alpha (as_tree p) (triv_ri RI)).
  unfold state_inv, live, "⋅", state_op in *. destruct_ands.
  rewrite multiset_add_empty_left.
  split; trivial.
  
  rename H0 into batird.
  setoid_rewrite as_tree_op.
  
  setoid_rewrite as_tree_singleton.
  
  rename l into lt.
  full_generalize (as_tree p) as q. clear p.
  
  eapply specific_flows_preserve_branch_all_total_in_refinement_domain
    with (t := q)
         (se := ∅)
         (down := λ pl, unit)
         (up   := λ pl, unit); trivial.
         
  - intros. split; trivial.
  
  - assert (is_fresh_nat q
      (nat_of_basestep RI (alloc_alpha q (triv_ri RI))))
      as is_fresh
      by (apply is_fresh_alloc_base; trivial).
  
    full_generalize (alloc_alpha q (triv_ri RI)) as alpha.

    unfold specific_flow_cond.
    repeat (rewrite unit_dot_left).
    repeat (rewrite unit_dot).

    intros.
    have the_case : Decision ((p, i) ∈ pls_of_loc (BaseLoc RI alpha)) by solve_decision.
    destruct the_case.

    (* interesting case: ext location *)
  
  + 
    (*rewrite <- node_of_pl_op.
    repeat (rewrite unit_dot).
    repeat (rewrite unit_dot_left).
    rewrite node_live_op.
    rewrite node_node_cell_cell. rewrite node_node_cell_cell.
    
    rewrite build_spec; trivial.
    apply specific_exchange_cond_of_whatever.*)
    
    rewrite <- node_of_pl_op.
    repeat (rewrite unit_dot).
    repeat (rewrite unit_dot_left).
    rewrite node_live_op.
    rewrite node_node_cell_cell. rewrite node_node_cell_cell.
    
    setoid_rewrite build_spec at 1; trivial.
    unfold cell_live, triv_cell.
    
    assert (node_trivial (node_of_pl q (p, i))) as EqTrivNode
      by (apply trivial_node_at_fresh;
      rewrite <- (i_value_of_pls_of_base p i) in is_fresh; trivial).
    
    rewrite node_total_minus_live_of_trivial; trivial.
    
    unfold cell_of_pl. destruct (node_of_pl q (p, i)).
    unfold node_trivial in EqTrivNode. destruct c. destruct_ands.
    unfold cell_trivial in H0. destruct_ands. subst m0.
    rewrite unit_dot.
    
    unfold specific_exchange_cond.
    
    repeat (rewrite unit_dot).
    exists m. exists unit. exists unit.
    
    rewrite rel_unit.
    intros.
    repeat (rewrite unit_dot).
    repeat split; trivial.
    * rewrite (@i_value_of_pls_of_base RI EqDecision1 Countable0 p i alpha); trivial.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_basestep.
      apply rel_refinement_of_triv_ri_defined. trivial.
    * rewrite (@i_value_of_pls_of_base RI EqDecision1 Countable0 p i alpha); trivial.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_basestep.
      rewrite rel_refinement_of_triv_ri_eq_unit.
    
      repeat (rewrite unit_dot).
      apply reflex.
    
    (* uninteresting case *)
  + 
    rewrite <- node_of_pl_op.
    rewrite node_live_op.
    rewrite node_node_cell_cell. rewrite node_node_cell_cell.
    setoid_rewrite build_rest_triv at 1; trivial.
    unfold cell_live, triv_cell.
    repeat (rewrite unit_dot_left).
    apply specific_exchange_cond_of_whatever2.
    
  - setoid_rewrite <- cell_of_pl_op.
    setoid_rewrite cell_reserved_op.
    intro.
    repeat (rewrite cell_reserved_cell_of_pl_build_empty).
    set_solver.
Qed.

Lemma initialize_normal_valid (m: M) p
  (is_val: m_valid m)
  (si: ✓ p)
  : ∃ alpha , ✓ (live (BaseLoc RI alpha) m ⋅ p).
Proof.
  unfold "✓",state_valid in *.
  setoid_rewrite <- state_assoc. deex.
  have h := initialize_normal m (p ⋅ p0) is_val si. deex. exists alpha. exists p0.
  trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(m, gamma1) . live(m1 x m2, gamma1, gamma2) ->
   live(m1, gamma1) . live(m x m2, gamma1, gamma2)
*)
    
Lemma specific_exchange_cond_left_swap v m1 m2 m x
 : specific_exchange_cond (refinement_of (left_ri RI))
    v m (dot (pair_up RI m1 m2) x) unit unit
      m1 (dot (pair_up RI m m2) x) unit unit.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
  unfold specific_exchange_cond.
  exists (dot (pair_up RI m m2) x). exists m. exists m1. intros.
  repeat (rewrite unit_dot).
  repeat (rewrite <- tpcm_assoc).
  repeat (rewrite <- tpcm_assoc in H).
  repeat (rewrite <- tpcm_assoc in H0).
  full_generalize (dot x v) as y.
  have yp := y_is_pair_of_rel_defined_refinement_of_left _ _ H.
  have yp' := yp EqDecision1 Countable0.
  deex. subst y.
  rewrite dot_pair_up.
  rewrite dot_pair_up.
  rewrite dot_pair_up in H0.
  rewrite dot_pair_up in H.
  rewrite refinement_of_left_pair_up in H0.
  rewrite refinement_of_left_pair_up.
  rewrite refinement_of_left_pair_up.
  repeat split; trivial.
  - apply rel_defined_refinement_of_left_pair_up.
    + replace (dot m1 k1) with (dot k1 m1) in H0 by (apply tpcm_comm).
      rewrite tpcm_assoc in H0. apply valid_monotonic with (y := m1). trivial.
    + apply m_valid_right_of_rel_defined_refinement_of_left_pair_up with (a := dot m1 k1).
      trivial.
  - rewrite tpcm_assoc. rewrite tpcm_assoc.
      replace (dot m1 m) with (dot m m1) by (apply tpcm_comm). apply reflex.
Qed.

Lemma specific_exchange_cond_right_swap v m1 m2 m x
 : specific_exchange_cond (refinement_of (right_ri RI))
    v m (dot (pair_up RI m1 m2) x) unit unit
      m2 (dot (pair_up RI m1 m) x) unit unit.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
  unfold specific_exchange_cond.
  exists (dot (pair_up RI m1 m) x). exists m. exists m2. intros.
  repeat (rewrite unit_dot).
  repeat (rewrite <- tpcm_assoc).
  repeat (rewrite <- tpcm_assoc in H).
  repeat (rewrite <- tpcm_assoc in H0).
  full_generalize (dot x v) as y.
  have yp := y_is_pair_of_rel_defined_refinement_of_right _ _ H.
  have yp' := yp EqDecision1 Countable0.
  deex. subst y.
  rewrite dot_pair_up.
  rewrite dot_pair_up.
  rewrite dot_pair_up in H0.
  rewrite dot_pair_up in H.
  rewrite refinement_of_right_pair_up in H0.
  rewrite refinement_of_right_pair_up.
  rewrite refinement_of_right_pair_up.
  repeat split; trivial.
  - apply rel_defined_refinement_of_right_pair_up.
    + apply m_valid_left_of_rel_defined_refinement_of_right_pair_up with (b := dot m2 k2).
      trivial.
    + replace (dot m2 k2) with (dot k2 m2) in H0 by (apply tpcm_comm).
      rewrite tpcm_assoc in H0. apply valid_monotonic with (y := m2). trivial.
  - rewrite tpcm_assoc. rewrite tpcm_assoc.
      replace (dot m2 m) with (dot m m2) by (apply tpcm_comm). apply reflex.
Qed.

Lemma dot_mcmk (m c m1 k1 : M)
  : dot (dot m c) (dot m1 k1) = dot (dot m k1) (dot m1 c).
Proof.
  rewrite <- tpcm_assoc.
  rewrite <- tpcm_assoc. f_equal.
  replace (dot m1 k1) with (dot k1 m1) by (apply tpcm_comm).
  rewrite tpcm_assoc.
  replace (dot c k1) with (dot k1 c) by (apply tpcm_comm).
  rewrite <- tpcm_assoc.
  f_equal.
  apply tpcm_comm.
Qed.

Lemma specific_exchange_cond_left_swap2 m c d v x y m1 m2
  (mv: m_valid (dot (dot m c) (rel M M (refinement_of (left_ri RI))
                 (dot (dot (pair_up RI m1 m2) d) v))))
  : specific_exchange_cond (refinement_of (right_ri RI)) v 
    (x) (dot (pair_up RI m1 m2) d) (x) unit
    (y) (dot (pair_up RI m m2) d) (y) unit.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
  unfold specific_exchange_cond.
  exists (dot (pair_up RI m m2) d).
  exists unit. exists unit.
  intros.
  repeat (rewrite unit_dot_left).
  repeat (rewrite unit_dot).
  
  repeat (rewrite <- tpcm_assoc).
  assert ((dot (dot (pair_up RI m1 m2) d) v)
      = dot (pair_up RI m1 m2) (dot d v)) as r1 by (symmetry; apply tpcm_assoc).
  rewrite r1 in mv.
  rewrite r1 in H.
  rewrite r1 in H0.
  clear r1. full_generalize (dot d v) as z.
  
  have yp := y_is_pair_of_rel_defined_refinement_of_right _ _ H.
  have yp' := yp EqDecision1 Countable0.
  deex. subst z.
  repeat (rewrite dot_pair_up).
  repeat (rewrite dot_pair_up in H).
  repeat (rewrite dot_pair_up in H0).
  repeat (rewrite dot_pair_up in mv).
  
  rewrite refinement_of_left_pair_up in mv.
  repeat (rewrite refinement_of_right_pair_up).
  repeat (rewrite refinement_of_right_pair_up in H0).
  
  repeat split; trivial.
  - apply rel_defined_refinement_of_right_pair_up.
    + rewrite dot_mcmk in mv. apply valid_monotonic with (y0 := (dot m1 c)). trivial.
    + rewrite tpcm_comm in H0. apply valid_monotonic with (y0 := x). trivial.
  - apply reflex.
Qed.

Lemma specific_exchange_cond_right_swap2 m c d v x y m1 m2
  (mv: m_valid (dot (dot m c) (rel M M (refinement_of (right_ri RI))
                 (dot (dot (pair_up RI m1 m2) d) v))))
  : specific_exchange_cond (refinement_of (left_ri RI)) v 
    (x) (dot (pair_up RI m1 m2) d) (x) unit
    (y) (dot (pair_up RI m1 m) d) (y) unit.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
  unfold specific_exchange_cond.
  exists (dot (pair_up RI m1 m) d).
  exists unit. exists unit.
  intros.
  repeat (rewrite unit_dot_left).
  repeat (rewrite unit_dot).
  
  repeat (rewrite <- tpcm_assoc).
  assert ((dot (dot (pair_up RI m1 m2) d) v)
      = dot (pair_up RI m1 m2) (dot d v)) as r1 by (symmetry; apply tpcm_assoc).
  rewrite r1 in mv.
  rewrite r1 in H.
  rewrite r1 in H0.
  clear r1. full_generalize (dot d v) as z.
  
  have yp := y_is_pair_of_rel_defined_refinement_of_left _ _ H.
  have yp' := yp EqDecision1 Countable0.
  deex. subst z.
  repeat (rewrite dot_pair_up).
  repeat (rewrite dot_pair_up in H).
  repeat (rewrite dot_pair_up in H0).
  repeat (rewrite dot_pair_up in mv).
  
  rewrite refinement_of_right_pair_up in mv.
  repeat (rewrite refinement_of_left_pair_up).
  repeat (rewrite refinement_of_left_pair_up in H0).
  
  repeat split; trivial.
  - apply rel_defined_refinement_of_left_pair_up.
    + rewrite tpcm_comm in H0. apply valid_monotonic with (y0 := x). trivial.
    + rewrite dot_mcmk in mv. apply valid_monotonic with (y0 := (dot m2 c)). trivial.
  - apply reflex.
Qed.
  
(*Lemma cell_of_pl_as_tree_eq (l: lmap M RI) (pl1 pl2: PathLoc) (loc: Loc RI)
  (pl1_in: pl1 ∈ pls_of_loc loc)
  (pl2_in: pl2 ∈ pls_of_loc loc)
  : cell_of_pl (as_tree l) pl1 ≡ cell_of_pl (as_tree l) pl2. Admitted.*)

Lemma valid_child_and_parent (t: Branch M) p i j lt_active
  (vt: valid_totals (refinement_of_nat M RI) t lt_active)
  : m_valid (dot (cell_live (cell_of_pl t (p, i)))
      (rel M M (refinement_of_nat M RI j) (node_total (refinement_of_nat M RI) (node_of_pl t (p++[i], j)) lt_active))). Admitted.

Lemma specific_exchange_cond_of_no_change2 ref view x y z w
  : specific_exchange_cond ref view x y x y z w z w.
Proof. 
  unfold specific_exchange_cond.
  exists unit. exists unit. exists unit.
  repeat (rewrite unit_dot_left).
  intro. repeat split; trivial. apply reflex.
Qed.

Lemma node_of_pl_as_tree_eq (l: lmap M RI) (pl1 pl2: PathLoc) (loc: Loc RI)
  (pl1_in: pl1 ∈ pls_of_loc loc)
  (pl2_in: pl2 ∈ pls_of_loc loc)
  : node_of_pl (as_tree l) pl1 ≡ node_of_pl (as_tree l) pl2.
  (* call node_of_pl_build_eq *)
  Admitted.
  
  
Lemma swap_cross_left (gamma1 gamma2 : Loc RI) (m m1 m2 : M) p
  (si: state_inv (live gamma1 m ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m1 m2) ⋅ p))
     : state_inv (live gamma1 m1 ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m m2) ⋅ p).
Proof.
  unfold state_inv in *. destruct p. unfold live, "⋅", state_op in *. destruct_ands.
  split; trivial.
  full_generalize (multiset_add (multiset_add empty_lifetime empty_lifetime) l) as active_lt.
  rename H0 into vt.
  setoid_rewrite as_tree_op. 
  setoid_rewrite as_tree_op. 
  setoid_rewrite as_tree_singleton. 
  setoid_rewrite as_tree_op in vt. 
  setoid_rewrite as_tree_op in vt.
  setoid_rewrite as_tree_singleton in vt.
   
  eapply specific_flows_preserve_branch_all_total_in_refinement_domain
    with (t := build gamma1 (CellCon m ∅)
          ⋅ build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅) ⋅ (as_tree l0))
         (se := updo_se gamma1 (nat_of_leftstep RI gamma2))
         (down := updo m gamma1 (nat_of_leftstep RI gamma2))
         (up   := updo m1 gamma1 (nat_of_leftstep RI gamma2)); trivial.

  - intros. split.
    + apply updo_se_okay; trivial.
    + apply updo_se_okay; trivial.
  - intros.
    unfold specific_flow_cond.
    setoid_rewrite <- node_of_pl_op.
    setoid_rewrite <- node_of_pl_op.
    
    have the_case : Decision ((p, i) ∈ pls_of_loc_from_left gamma1 gamma2) by solve_decision.
    destruct the_case.
    
    + 
      assert ((p, i) ∉ pls_of_loc gamma1) by (apply pl_not_in_left_of_pl_in_left with (gamma4:=gamma2); trivial).
      assert ((p, i) ∈ pls_of_loc (CrossLoc gamma1 gamma2)) by (apply pl_in_crossloc_of_pl_in_left with (gamma4:=gamma2); trivial).
      repeat (rewrite node_live_op).
      repeat (rewrite node_node_cell_cell).
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      unfold cell_live, triv_cell.
      repeat (rewrite unit_dot_left).
      rewrite updo_eq_m_left; trivial.
      rewrite updo_eq_unit_left; trivial.
      rewrite updo_eq_unit2_left; trivial.
      rewrite updo_eq_m_left; trivial.
      rewrite updo_eq_unit_left; trivial.
      rewrite updo_eq_unit2_left; trivial.
      rewrite (i_value_of_pls_of_loc_from_left p i gamma1 gamma2); trivial.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_leftstep.
      apply specific_exchange_cond_left_swap.
      
    + 
    
    have the_case : Decision ((p, i) ∈ pls_of_loc_from_right gamma1 gamma2) by solve_decision.
    destruct the_case.

    *
    
      assert ((p, i) ∉ pls_of_loc gamma1) by (apply pl_not_in_left_of_pl_in_right with (gamma4:=gamma2); trivial).
      assert ((p, i) ∈ pls_of_loc (CrossLoc gamma1 gamma2)) as picl by (apply pl_in_crossloc_of_pl_in_right with (gamma3:=gamma1); trivial).
      
      have epl := exists_in_pls_of_loc_from_left gamma1 gamma2.
      deex. destruct pl. rename l1 into other_p. rename n0 into other_i.
      
      assert ((other_p, other_i) ∈ pls_of_loc (CrossLoc gamma1 gamma2)) as opicl by (apply pl_in_crossloc_of_pl_in_left with (gamma3:=gamma1); trivial).
      
      (*have ceq := cell_of_pl_as_tree_eq l0 (p, i) (other_p, other_i) (CrossLoc gamma1 gamma2) picl opicl.*)
      destruct (plsplit other_p) eqn:plsplit_other_p. rename l1 into other_p_p. rename n0 into other_p_i.
      
      have vcap := valid_child_and_parent
        (build gamma1 (CellCon m ∅) ⋅ build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅) ⋅ as_tree l0)
        other_p_p other_p_i other_i active_lt vt.
        
      have pio := plsplit_in_of_pls_of_loc_from_left gamma1 gamma2 other_p other_i epl.
      
      have qe := q_eq_pi_of_plsplit_cross gamma1 gamma2 other_p other_p_p other_p_i
          other_i opicl plsplit_other_p. rewrite <- qe in vcap; try (typeclasses eauto).
          
      assert (plsplit other_p ∉ pls_of_loc (CrossLoc gamma1 gamma2)) as npio
          by (apply pl_not_in_pls_of_loc_cross_from_in_left; trivial).
          
      assert ((other_p, other_i) ∉ pls_of_loc gamma1) as onp1
          by (apply pl_not_in_left_of_pl_in_left with (gamma4:=gamma2); trivial).
      
      rewrite <- plsplit_other_p in vcap.
      
      repeat (rewrite node_live_op).
      repeat (rewrite node_node_cell_cell).
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      (*replace (cell_live triv_cell) with (unit) by (unfold cell_live, triv_cell; trivial).*)
      unfold cell_live. unfold triv_cell.
      repeat (rewrite unit_dot_left).
      rewrite <- updo_other_eq_both_left; trivial.
      rewrite <- updo_other_eq_both_left; trivial.
      rewrite updo_eq_unit3_left; trivial.
      rewrite updo_eq_unit3_left; trivial.

      repeat (rewrite <- node_of_pl_op in vcap).
      repeat (rewrite <- cell_of_pl_op in vcap).
      setoid_rewrite build_spec at 1 in vcap; trivial.
      setoid_rewrite build_rest_triv at 1 in vcap; trivial.
      full_generalize (cell_of_pl (as_tree l0) (plsplit other_p)) as child_c.
      rewrite <- node_live_plus_node_total_minus_live in vcap.
      setoid_rewrite (node_of_pl_as_tree_eq _ (other_p, other_i) (p, i) (CrossLoc gamma1 gamma2)) in vcap; trivial.
      setoid_rewrite (node_of_pl_build_eq (other_p, other_i) (p, i) (CrossLoc gamma1 gamma2)) in vcap; trivial.
      full_generalize ((node_total_minus_live (refinement_of_nat M RI)
                       (node_of_pl (build gamma1 (CellCon m ∅)) (p, i)
                        ⋅ node_of_pl
                            (build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅))
                            (p, i) ⋅ node_of_pl (as_tree l0) (p, i)) active_lt)) as z.
      (*full_generalize ((node_total_minus_live (refinement_of_nat M RI)
                       (node_of_pl (build gamma1 (CellCon m ∅)) (other_p, other_i)
                        ⋅ node_of_pl
                            (build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅))
                            (other_p, other_i) ⋅ node_of_pl (as_tree l0) (other_p, other_i))
                       active_lt)) as z.*)
      repeat (rewrite node_live_op in vcap).
      repeat (rewrite node_node_cell_cell in vcap).
      setoid_rewrite build_rest_triv at 1 in vcap; trivial.
      setoid_rewrite build_spec at 1 in vcap; trivial.
      repeat (rewrite cell_live_op in vcap).
      unfold cell_live, triv_cell in vcap.
      rewrite unit_dot in vcap.
      rewrite unit_dot_left in vcap.
      
      rewrite (i_value_of_pls_of_loc_from_right p i gamma1 gamma2); trivial.
      rewrite (i_value_of_pls_of_loc_from_right p i gamma1 gamma2) in vcap; trivial.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_rightstep.
      
      rewrite (i_value_of_pls_of_loc_from_left other_p other_i gamma1 gamma2) in vcap; trivial.
      unfold refinement_of_nat in vcap.
      rewrite ri_of_nat_nat_of_leftstep in vcap.
      
      
      apply (specific_exchange_cond_left_swap2)
          with (c := match child_c with | CellCon m _ => m end).
      trivial.
      
    * have the_case : Decision ((p, i) ∈ pls_of_loc gamma1) by solve_decision.
      destruct the_case.
    
    --
        assert ((p, i) ∉ pls_of_loc (CrossLoc gamma1 gamma2))
            by (apply pl_not_in_pls_of_loc_cross_from_in_left; trivial).
        
        rewrite <- (updo_other_eq_both_left p i); trivial.
        rewrite <- (updo_other_eq_both_left p i); trivial.
        rewrite (updo_base_eq_m p i); trivial. rewrite (updo_base_eq_m p i); trivial.
        
        rewrite node_live_op. rewrite node_live_op.
        rewrite node_live_op. rewrite node_live_op.
        repeat (rewrite unit_dot).
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell.
        setoid_rewrite build_spec at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_spec at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        unfold cell_live, triv_cell.
        repeat (rewrite unit_dot).
        apply specific_exchange_cond_add_stuff.
        apply specific_exchange_cond_of_no_change2.

      (* uninteresting case *)
      --
        assert ((p, i) ∉ pls_of_loc (CrossLoc gamma1 gamma2))
            by (apply pl_not_in_pls_of_loc_cross_from_not_in_both; trivial).
      
        rewrite <- (updo_other_eq_both_left p i); trivial.
        rewrite <- (updo_other_eq_both_left p i); trivial.
        rewrite updo_other_eq_unit; trivial.
        rewrite updo_other_eq_unit; trivial.

        rewrite node_live_op. rewrite node_live_op.
        rewrite node_live_op. rewrite node_live_op.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell.
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        unfold cell_live, triv_cell.
        repeat (rewrite unit_dot).
        repeat (rewrite unit_dot_left).
        apply specific_exchange_cond_of_whatever2.
   - setoid_rewrite <- cell_of_pl_op.
     setoid_rewrite <- cell_of_pl_op.
     setoid_rewrite cell_reserved_op.
     setoid_rewrite cell_reserved_op.
     intro.
     setoid_rewrite cell_reserved_cell_of_pl_build_empty. trivial.
Qed.

Lemma swap_cross_right (gamma1 gamma2 : Loc RI) (m m1 m2 : M) p
  (si: state_inv (live gamma2 m ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m1 m2) ⋅ p))
     : state_inv (live gamma2 m2 ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m1 m) ⋅ p).
Proof.
  unfold state_inv in *. destruct p. unfold live, "⋅", state_op in *. destruct_ands.
  split; trivial.
  full_generalize (multiset_add (multiset_add empty_lifetime empty_lifetime) l) as active_lt.
  rename H0 into vt.
  setoid_rewrite as_tree_op. 
  setoid_rewrite as_tree_op. 
  setoid_rewrite as_tree_singleton. 
  setoid_rewrite as_tree_op in vt. 
  setoid_rewrite as_tree_op in vt.
  setoid_rewrite as_tree_singleton in vt.
   
  eapply specific_flows_preserve_branch_all_total_in_refinement_domain
    with (t := build gamma2 (CellCon m ∅)
          ⋅ build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅) ⋅ (as_tree l0))
         (se := updo_se gamma2 (nat_of_rightstep RI gamma1))
         (down := updo m gamma2 (nat_of_rightstep RI gamma1))
         (up   := updo m2 gamma2 (nat_of_rightstep RI gamma1)); trivial.

  - intros. split.
    + apply updo_se_okay; trivial.
    + apply updo_se_okay; trivial.
  - intros.
    unfold specific_flow_cond.
    setoid_rewrite <- node_of_pl_op.
    setoid_rewrite <- node_of_pl_op.
    
    have the_case : Decision ((p, i) ∈ pls_of_loc_from_right gamma1 gamma2) by solve_decision.
    destruct the_case.
    
    + 
      assert ((p, i) ∉ pls_of_loc gamma2) by (apply pl_not_in_right_of_pl_in_right with (gamma3:=gamma1); trivial).
      assert ((p, i) ∈ pls_of_loc (CrossLoc gamma1 gamma2)) by (apply pl_in_crossloc_of_pl_in_right with (gamma3:=gamma1); trivial).
      repeat (rewrite node_live_op).
      repeat (rewrite node_node_cell_cell).
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      unfold cell_live, triv_cell.
      repeat (rewrite unit_dot_left).
      rewrite updo_eq_m_right; trivial.
      rewrite updo_eq_unit_right; trivial.
      rewrite updo_eq_unit2_right; trivial.
      rewrite updo_eq_m_right; trivial.
      rewrite updo_eq_unit_right; trivial.
      rewrite updo_eq_unit2_right; trivial.
      rewrite (i_value_of_pls_of_loc_from_right p i gamma1 gamma2); trivial.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_rightstep.
      apply specific_exchange_cond_right_swap.
      
    + 
    
    have the_case : Decision ((p, i) ∈ pls_of_loc_from_left gamma1 gamma2) by solve_decision.
    destruct the_case.

    *
    
      assert ((p, i) ∉ pls_of_loc gamma2) by (apply pl_not_in_right_of_pl_in_left with (gamma3:=gamma1); trivial).
      assert ((p, i) ∈ pls_of_loc (CrossLoc gamma1 gamma2)) as picl by (apply pl_in_crossloc_of_pl_in_left with (gamma4:=gamma2); trivial).
      
      have epl := exists_in_pls_of_loc_from_right gamma1 gamma2.
      deex. destruct pl. rename l1 into other_p. rename n0 into other_i.
      
      assert ((other_p, other_i) ∈ pls_of_loc (CrossLoc gamma1 gamma2)) as opicl by (apply pl_in_crossloc_of_pl_in_right with (gamma4:=gamma2); trivial).
      
      (*have ceq := cell_of_pl_as_tree_eq l0 (p, i) (other_p, other_i) (CrossLoc gamma1 gamma2) picl opicl.*)
      destruct (plsplit other_p) eqn:plsplit_other_p. rename l1 into other_p_p. rename n0 into other_p_i.
      
      have vcap := valid_child_and_parent
        (build gamma2 (CellCon m ∅) ⋅ build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅) ⋅ as_tree l0)
        other_p_p other_p_i other_i active_lt vt.
        
      have pio := plsplit_in_of_pls_of_loc_from_right gamma1 gamma2 other_p other_i epl.
      
      have qe := q_eq_pi_of_plsplit_cross gamma1 gamma2 other_p other_p_p other_p_i
          other_i opicl plsplit_other_p. rewrite <- qe in vcap; try (typeclasses eauto).
          
      assert (plsplit other_p ∉ pls_of_loc (CrossLoc gamma1 gamma2)) as npio
          by (apply pl_not_in_pls_of_loc_cross_from_in_right; trivial).
          
      assert ((other_p, other_i) ∉ pls_of_loc gamma2) as onp1
          by (apply pl_not_in_right_of_pl_in_right with (gamma3:=gamma1); trivial).
      
      rewrite <- plsplit_other_p in vcap.
      
      repeat (rewrite node_live_op).
      repeat (rewrite node_node_cell_cell).
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      setoid_rewrite build_rest_triv at 1; trivial.
      setoid_rewrite build_spec at 1; trivial.
      (*replace (cell_live triv_cell) with (unit) by (unfold cell_live, triv_cell; trivial).*)
      unfold cell_live. unfold triv_cell.
      repeat (rewrite unit_dot_left).
      rewrite <- updo_other_eq_both_right; trivial.
      rewrite <- updo_other_eq_both_right; trivial.
      rewrite updo_eq_unit3_right; trivial.
      rewrite updo_eq_unit3_right; trivial.

      repeat (rewrite <- node_of_pl_op in vcap).
      repeat (rewrite <- cell_of_pl_op in vcap).
      setoid_rewrite build_spec at 1 in vcap; trivial.
      setoid_rewrite build_rest_triv at 1 in vcap; trivial.
      full_generalize (cell_of_pl (as_tree l0) (plsplit other_p)) as child_c.
      rewrite <- node_live_plus_node_total_minus_live in vcap.
      setoid_rewrite (node_of_pl_as_tree_eq _ (other_p, other_i) (p, i) (CrossLoc gamma1 gamma2)) in vcap; trivial.
      setoid_rewrite (node_of_pl_build_eq (other_p, other_i) (p, i) (CrossLoc gamma1 gamma2)) in vcap; trivial.
      full_generalize ((node_total_minus_live (refinement_of_nat M RI)
                       (node_of_pl (build gamma2 (CellCon m ∅)) (p, i)
                        ⋅ node_of_pl
                            (build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅))
                            (p, i) ⋅ node_of_pl (as_tree l0) (p, i)) active_lt)) as z.
      (*full_generalize ((node_total_minus_live (refinement_of_nat M RI)
                       (node_of_pl (build gamma1 (CellCon m ∅)) (other_p, other_i)
                        ⋅ node_of_pl
                            (build (CrossLoc gamma1 gamma2) (CellCon (pair_up RI m1 m2) ∅))
                            (other_p, other_i) ⋅ node_of_pl (as_tree l0) (other_p, other_i))
                       active_lt)) as z.*)
      repeat (rewrite node_live_op in vcap).
      repeat (rewrite node_node_cell_cell in vcap).
      setoid_rewrite build_rest_triv at 1 in vcap; trivial.
      setoid_rewrite build_spec at 1 in vcap; trivial.
      repeat (rewrite cell_live_op in vcap).
      unfold cell_live, triv_cell in vcap.
      rewrite unit_dot in vcap.
      rewrite unit_dot_left in vcap.
      
      rewrite (i_value_of_pls_of_loc_from_left p i gamma1 gamma2); trivial.
      rewrite (i_value_of_pls_of_loc_from_left p i gamma1 gamma2) in vcap; trivial.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_leftstep.
      
      rewrite (i_value_of_pls_of_loc_from_right other_p other_i gamma1 gamma2) in vcap; trivial.
      unfold refinement_of_nat in vcap.
      rewrite ri_of_nat_nat_of_rightstep in vcap.
      
      apply (specific_exchange_cond_right_swap2)
          with (c := match child_c with | CellCon m _ => m end).
      trivial.
      
    * have the_case : Decision ((p, i) ∈ pls_of_loc gamma2) by solve_decision.
      destruct the_case.
    
    --
        assert ((p, i) ∉ pls_of_loc (CrossLoc gamma1 gamma2))
            by (apply pl_not_in_pls_of_loc_cross_from_in_right; trivial).
        
        rewrite <- (updo_other_eq_both_right p i); trivial.
        rewrite <- (updo_other_eq_both_right p i); trivial.
        rewrite (updo_base_eq_m p i); trivial. rewrite (updo_base_eq_m p i); trivial.
        
        rewrite node_live_op. rewrite node_live_op.
        rewrite node_live_op. rewrite node_live_op.
        repeat (rewrite unit_dot).
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell.
        setoid_rewrite build_spec at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        setoid_rewrite build_spec at 1; trivial.
        setoid_rewrite build_rest_triv at 1; trivial.
        unfold cell_live, triv_cell.
        repeat (rewrite unit_dot).
        apply specific_exchange_cond_add_stuff.
        apply specific_exchange_cond_of_no_change2.

      (* uninteresting case *)
      --
        assert ((p, i) ∉ pls_of_loc (CrossLoc gamma1 gamma2))
            by (apply pl_not_in_pls_of_loc_cross_from_not_in_both; trivial).
      
        rewrite <- (updo_other_eq_both_right p i); trivial.
        rewrite <- (updo_other_eq_both_right p i); trivial.
        rewrite updo_other_eq_unit; trivial.
        rewrite updo_other_eq_unit; trivial.

        rewrite node_live_op. rewrite node_live_op.
        rewrite node_live_op. rewrite node_live_op.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell.
        setoid_rewrite build_rest_triv; trivial.
        unfold cell_live, triv_cell.
        repeat (rewrite unit_dot).
        repeat (rewrite unit_dot_left).
        apply specific_exchange_cond_of_whatever2.
   - setoid_rewrite <- cell_of_pl_op.
     setoid_rewrite <- cell_of_pl_op.
     setoid_rewrite cell_reserved_op.
     setoid_rewrite cell_reserved_op.
     intro.
     setoid_rewrite cell_reserved_cell_of_pl_build_empty. trivial.
Qed.

Lemma swap_cross_left_valid (gamma1 gamma2 : Loc RI) (m m1 m2 : M) p
  (si: ✓(live gamma1 m ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m1 m2) ⋅ p))
     : ✓(live gamma1 m1 ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m m2) ⋅ p).
Proof.
  unfold "✓", state_valid in *.
  setoid_rewrite <- state_assoc.
  setoid_rewrite <- state_assoc in si.
  deex.
  have h := swap_cross_left gamma1 gamma2 m m1 m2 (p ⋅ p0) si.
  exists p0. trivial.
Qed.

Lemma swap_cross_right_valid (gamma1 gamma2 : Loc RI) (m m1 m2 : M) p
  (si: ✓(live gamma2 m ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m1 m2) ⋅ p))
     : ✓(live gamma2 m2 ⋅ live (CrossLoc gamma1 gamma2) (pair_up RI m1 m) ⋅ p).
Proof.
  unfold "✓", state_valid in *.
  setoid_rewrite <- state_assoc.
  setoid_rewrite <- state_assoc in si.
  deex.
  have h := swap_cross_right gamma1 gamma2 m m1 m2 (p ⋅ p0) si.
  exists p0. trivial.
Qed.

End Exchanges.
