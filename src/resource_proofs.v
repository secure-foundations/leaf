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

Instance loc_eqdec RI `{!EqDecision RI} `{!Countable RI} : EqDecision (Loc RI). Admitted.
Instance loc_countable RI `{!EqDecision RI} `{!Countable RI} : Countable (Loc RI). Admitted.

Definition lmap M `{!EqDecision M} `{!Countable M} `{!TPCM M}
                RI `{!EqDecision RI, !Countable RI}
  := gmap (Loc RI) (Cell M).
Inductive State M `{!EqDecision M} `{!Countable M} `{!TPCM M}
                RI `{!EqDecision RI, !Countable RI} :=
  | StateCon : Lifetime -> lmap M RI -> State M RI
.
Arguments StateCon {M}%type_scope {EqDecision0 Countable0 TPCM0}
    {RI}%type_scope {EqDecision1 Countable1} _ _.
    
Context {M} `{!EqDecision M} `{!Countable M} `{!TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.
    
Definition lmap_lookup (m : gmap (Loc RI) (Cell M)) (l : Loc RI) :=
  match m !! l with None => triv_cell | Some c => c end.

Definition lmaps_equiv (m1 m2 : gmap (Loc RI) (Cell M)) :=
  ∀ l , lmap_lookup m1 l ≡ lmap_lookup m2 l.

Global Instance state_equiv
    : Equiv (State M RI) := λ x y ,
  match x, y with
  | StateCon lt1 m1, StateCon lt2 m2 =>
      (lt1 = lt2 /\ lmaps_equiv m1 m2)
  end.
  
Definition cell_op_opt (c1 c2 : option (Cell M)) := match c1, c2 with
  | None, None => None
  | Some c, None => Some c
  | None, Some c' => Some c'
  | Some c, Some c' => Some (c ⋅ c')
end.

Instance lmap_op : Op (lmap M RI) := λ x y ,
    merge cell_op_opt x y.

Instance state_op : Op (State M RI) := λ x y ,
      match x, y with
  | StateCon active1 lmap1, StateCon active2 lmap2 =>
      StateCon (multiset_add active1 active2) (lmap1 ⋅ lmap2)
  end.


Definition live (loc: Loc RI) (m: M) :=
      (*StateCon empty_lifetime (build loc (CellCon m empty)).*)
      StateCon empty_lifetime {[ loc := CellCon m empty ]}.
    
Definition reserved (lt: Lifetime) (loc: Loc RI) (m:M) :=
      StateCon empty_lifetime {[ loc := CellCon unit {[ (lt,m) ]} ]}.
    
Definition active (lt: Lifetime) : State M RI :=
      StateCon lt ∅.

Definition state_unit : State M RI := StateCon empty_lifetime ∅.

Definition as_tree (l : lmap M RI) : Branch M :=
  map_fold (λ k cell b , b ⋅ build k cell) BranchNil l.
  
Definition lmap_is_borrow (lt: Lifetime) (loc: Loc RI) (m: M) (l : lmap M RI) :=
  forall pl , pl ∈ pls_of_loc loc ->
    ∀ y , node_view (refinement_of_index M RI) (node_of_pl (as_tree l) pl) lt y -> tpcm_le m y.

Definition is_borrow (lt: Lifetime) (loc: Loc RI) (m: M) (state: State M RI) :=
    match state with
    | StateCon _ l => lmap_is_borrow lt loc m l
    end.
  
Definition state_inv (state: State M RI) : Prop :=
  match state with
  | StateCon active l =>
       multiset_no_dupes active /\
       branch_all_total_in_refinement_domain (refinement_of_index M RI) (as_tree l) active 0
  end.

Instance state_valid : Valid (State M RI) :=
  λ v , ∃ p , state_inv (v ⋅ p).
  
Lemma as_tree_dot (a b: lmap M RI) : (as_tree a) ⋅ (as_tree b) ≡ as_tree (a ⋅ b). Admitted.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, m) dot live(gamma, n) equiv live(gamma, m dot n) *)

(*Lemma live_dot_live
    {M} `{!EqDecision M, !Countable M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI}
    (gamma: Loc RI) (m1 m2: M)
    : live gamma m1 ⋅ live gamma m2 ≡ live gamma (dot m1 m2).
Proof.
  unfold "≡", state_equiv, live. unfold "⋅", state_op. split.
  - apply empty_add_empty_eq_empty.
  - apply equiv_extensionality_cells. intro.
      setoid_rewrite <- forall_cell_op.
      assert (Decision (pl ∈ pls_of_loc gamma)) by solve_decision.
      unfold Decision in H. destruct H.
      + repeat (rewrite build_spec); trivial. unfold "≡", "⋅", cell_equiv, cell_op.
          split; trivial. set_solver.
      + repeat (rewrite build_rest_triv); trivial.
          unfold triv_cell, "≡", cell_equiv, "⋅", cell_op. split.
          * apply unit_dot. * set_solver.
Qed.
*)

Lemma lmaps_equiv_of_eq (a1 a2 : lmap M RI) (e: a1 = a2) : (lmaps_equiv a1 a2).
Proof.  rewrite e. unfold lmaps_equiv. intro. apply cell_equiv_refl. Qed.

Lemma live_dot_live
    (gamma: Loc RI) (m1 m2: M)
    : live gamma m1 ⋅ live gamma m2 ≡ live gamma (dot m1 m2).
Proof.
  unfold "≡", state_equiv, live. unfold "⋅", state_op. split.
  - apply empty_add_empty_eq_empty.
  - unfold lmaps_equiv. intro. unfold lmap_lookup. unfold "⋅", lmap_op.
    rewrite lookup_merge. unfold diag_None.
    assert (Decision (gamma = l)) by solve_decision. destruct H.
    + rewrite e. repeat (rewrite lookup_singleton). unfold cell_op_opt.
      unfold "≡", cell_equiv, "⋅", cell_op. split; trivial. set_solver.
    + repeat (rewrite lookup_singleton_ne); trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, unit) = unit *)

Lemma live_unit (gamma : Loc RI) : live gamma unit ≡ state_unit.
Proof.
  unfold "≡", state_equiv, live, state_unit. split; trivial.
  unfold lmaps_equiv. intro. unfold "≡". 
  unfold lmap_lookup.
  assert (Decision (gamma = l)) by solve_decision. destruct H.
  - rewrite e. rewrite lookup_singleton. rewrite lookup_empty. unfold triv_cell.
    apply cell_equiv_refl.
  - rewrite lookup_singleton_ne; trivial. rewrite lookup_empty. unfold triv_cell.
    apply cell_equiv_refl.
Qed.
    
(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, m) . borrow(kappa, gamma, k) --> valid (a . b) *)

Instance state_equiv_symm : Symmetric state_equiv. Admitted.

Instance branch_all_total_in_refinement_domain_proper roi :
    Proper ((≡) ==> (=) ==> (=) ==> impl) (branch_all_total_in_refinement_domain roi).
    Admitted.

(*Instance branch_op_proper_left :
    Proper ((≡) ==> (=) ==> (≡)) branch_op. Admitted.
    
Instance branch_op_proper_right b :
    Proper ((≡) ==> (≡)) (branch_op b). Admitted.*)
    
Instance branch_op_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (branch_op). Admitted.
    
Instance node_op_proper_left :
    Proper ((≡) ==> (=) ==> (≡)) node_op. Admitted.
    
Instance node_op_proper_right n :
    Proper ((≡) ==> (≡)) (node_op n). Admitted.
    
Instance cell_op_proper_left :
    Proper ((≡) ==> (=) ==> (≡)) cell_op. Admitted.
    
Instance cell_op_proper_right n :
    Proper ((≡) ==> (≡)) (cell_op n). Admitted.


Instance node_view_proper roi :
    Proper ((≡) ==> (=) ==> (=) ==> impl) (node_view roi). Admitted.
    
Instance node_live_proper :
    Proper ((≡) ==> (=)) node_live. Admitted.
    
Instance cell_live_proper :
    Proper ((≡) ==> (=)) cell_live. Admitted.
    
Lemma as_tree_singleton (loc: Loc RI) (cell: Cell M)
  : as_tree {[loc := cell]} ≡ build loc cell. Admitted.

Lemma forall_equiv_branch_all_total_in_refinement_domain roi branch lt idx
  : branch_all_total_in_refinement_domain roi branch lt idx
    <-> forall pl, node_all_total_in_refinement_domain roi (node_of_pl branch pl) lt (plend pl). Admitted.

Definition any_pl_of_loc (loc: Loc RI) : PathLoc. Admitted.

Lemma any_pl_of_loc_is_of_loc (loc: Loc RI)
  : any_pl_of_loc loc ∈ pls_of_loc loc. Admitted.

Lemma multiset_add_chain_included (a b c d : Lifetime) :
  lifetime_included (multiset_add (multiset_add (multiset_add a b) c) d) a. Admitted.
  
Lemma in_refinement_domain_of_natird roi (node: Node M) (lifetime: Lifetime) (idx: nat)
  (natird : node_all_total_in_refinement_domain roi node lifetime idx)
      : in_refinement_domain roi idx (node_total roi node lifetime). Admitted.

Lemma exists_some_of_match {A} (t: option A) (is_some : match t with | Some _ => True | None => False end)
  : exists x , t = Some x. Admitted.

(*node_view roi (a ⋅ b) k -> node_view roi a k
            (node_of_pl (build gamma (CellCon m ∅) ⋅ as_tree l2 ⋅ as_tree l0)
               (any_pl_of_loc gamma)) kappa
            (node_total_minus_live (refinement_of_index M RI)
               (node_of_pl (build gamma (CellCon m ∅) ⋅ as_tree l2 ⋅ as_tree l0)
                  (any_pl_of_loc gamma))
               (multiset_add (multiset_add (multiset_add kappa empty_lifetime) l1) l))*)

Lemma node_view_le roi a b lt y : node_view roi (a ⋅ b) lt y -> node_view roi a lt y.
Admitted.

Lemma node_view_strip roi a b c loc kappa x :
  node_view roi (node_of_pl (a ⋅ b ⋅ c) loc) kappa x ->
  node_view roi (node_of_pl b loc) kappa x.
Proof.  
  intro.
  setoid_rewrite <- forall_node_op in H.
  assert (node_view roi (node_of_pl (a ⋅ b) loc) kappa x).
  - apply node_view_le with (b := node_of_pl c loc). trivial.
  - setoid_rewrite <- forall_node_op in H0.
    setoid_rewrite node_op_comm in H0.
    apply node_view_le with (b := node_of_pl a loc). trivial.
Qed.

Lemma node_node_cell_cell b pl : node_live (node_of_pl b pl) = cell_live (cell_of_pl b pl).
Admitted.

Lemma tpcm_le_m_node_live_with_m m gamma e b c
    : tpcm_le m
      (node_live (node_of_pl (build gamma (CellCon m e) ⋅ b ⋅ c) (any_pl_of_loc gamma))).
Proof.
  rewrite node_node_cell_cell.
  setoid_rewrite <- forall_cell_op.
  setoid_rewrite <- forall_cell_op.
  setoid_rewrite build_spec.
  - destruct (cell_of_pl b (any_pl_of_loc gamma)).
    destruct (cell_of_pl c (any_pl_of_loc gamma)).
    unfold cell_live. unfold "⋅", cell_op.
    unfold tpcm_le. exists (dot m0 m1). apply tpcm_assoc.
  - apply any_pl_of_loc_is_of_loc.
Qed.

Lemma live_and_borrow_implies_valid (gamma: Loc RI) (kappa: Lifetime) (m k: M) (b: State M RI)
    (isb: is_borrow kappa gamma k b)
    (isv: ✓(active kappa ⋅ live gamma m ⋅ b))
    : m_valid (dot m k).
Proof.
  unfold "✓", state_valid in isv. deex. destruct p.
  unfold state_inv in isv. unfold live in isv. destruct b. unfold "⋅" in isv.
  unfold state_op in isv. destruct isv. clear H. rename H0 into isv.
  unfold is_borrow, lmap_is_borrow in isb.
  setoid_rewrite <- as_tree_dot in isv.
  setoid_rewrite <- as_tree_dot in isv.
  setoid_rewrite <- as_tree_dot in isv.
  setoid_rewrite as_tree_singleton in isv.
  generalize isv. clear isv. rewrite forall_equiv_branch_all_total_in_refinement_domain. intro isv.
  
  rename isb into isb'. have isb := isb' (any_pl_of_loc gamma) (any_pl_of_loc_is_of_loc gamma). clear isb'.
  rename isv into isv'. have isv := isv' (any_pl_of_loc gamma). clear isv'.
  have nvlt := node_view_le_total_minus_live _ _ _ _ _ _ isv.
  have nvlt' := nvlt kappa (multiset_add_chain_included _ _ _ _). clear nvlt.
  unfold view_sat in nvlt'.
  
  have nvlt'' := node_view_strip _ _ _ _ _ _ _ nvlt'.
  have ineq := isb _ nvlt''.
  
  have ird := in_refinement_domain_of_natird _ _ _ _ isv.
  unfold in_refinement_domain in ird.
  rename ird into ird'. have ird := exists_some_of_match _ ird'. clear ird'. deex.
  have elem_is_val := rel_valid_left _ _ _ _ _ ird.
  clear ird.

  assert (tpcm_le m (node_live 
              (node_of_pl (build gamma (CellCon m ∅) ⋅ as_tree l2 ⋅ as_tree l0)
                 (any_pl_of_loc gamma)))) by apply tpcm_le_m_node_live_with_m.
  have summed_ineqs := le_add2 _ _ _ _ H ineq.
  rewrite node_live_plus_node_total_minus_live in summed_ineqs.
  unfold tpcm_le in summed_ineqs. deex.
  rewrite <- summed_ineqs in elem_is_val.
  have res := valid_monotonic _ _ elem_is_val.
  trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow(kappa, gamma, z) . live(gamma, m) . live(alpha ref gamma, y)
                         --> live(gamma, m') . live(alpha ref gamma, y') *)

Definition borrow_exchange_cond (ref: Refinement M M) (z m f m' f' : M) :=
  ∀ p , match rel M M ref (dot (dot f z) p) with
  | None => True
  | Some i1 => m_valid (dot m i1) ->
      match rel M M ref (dot (dot f' z) p) with
      | None => False
      | Some i2 => mov (dot m i1) (dot m' i2)
      end
  end.
  
Lemma multiset_add_empty (a : Lifetime) :
  multiset_add a empty_lifetime = a. Admitted.
  
Definition view_exchange_cond (ref: Refinement M M) (view: M -> Prop) (m f m' f' : M) :=
  ∀ p , view p -> match rel M M ref (dot f p) with
  | None => True
  | Some i1 => m_valid (dot m i1) ->
      match rel M M ref (dot f' p) with
      | None => False
      | Some i2 => mov (dot m i1) (dot m' i2)
      end
  end.
  
Definition flow_cond p i (b t t': Branch M) (active: Lifetime) (down up : PathLoc -> M) :=
  let q := (p, i) in
  let r := (p, S i) in
  let s := (p ++ [i], 0) in
  view_exchange_cond (refinement_of_index M RI i)
      (node_view (refinement_of_index M RI) (node_of_pl b q) active)
      (dot (down q) (up r))
      (dot (up s) (node_live (node_of_pl t q)))
      (dot (up q) (down r))
      (dot (down s) (node_live (node_of_pl t' q))).

Lemma flows_preserve_branch_all_total_in_refinement_domain b t t' active
  (down up : PathLoc -> M)
  (flow_update : ∀ p i , flow_cond p i b t t' active down up)
  (batird : branch_all_total_in_refinement_domain (refinement_of_index M RI) (t⋅b) active 0)
          : branch_all_total_in_refinement_domain (refinement_of_index M RI) (t'⋅b) active 0.
Admitted.

Lemma assoc_comm (a b c : Branch M) : (a ⋅ b) ⋅ c ≡ (a ⋅ c) ⋅ b.
Proof.
  have r : a ⋅ (b ⋅ c) ≡ (a ⋅ b) ⋅ c by apply branch_op_assoc.
  have q : a ⋅ (c ⋅ b) ≡ (a ⋅ c) ⋅ b by apply branch_op_assoc.
  have j : b ⋅ c ≡ c ⋅ b by apply branch_op_comm.
  setoid_rewrite <- r.
  setoid_rewrite <- q.
  setoid_rewrite j.
  trivial.
Qed.

Lemma is_borrow_weaken_lifetime k k1 gamma z b
  : is_borrow k gamma z b -> is_borrow (multiset_add k k1) gamma z b.
Admitted.

Definition plsplit (ln: list nat) : PathLoc. Admitted.

(*Instance thing_dec (p:PathLoc) (gamma: Loc RI) (i alpha:nat) (ri:RI) :
  Decision (p ∈ pls_of_loc gamma /\ i < nat_of_extstep alpha ri). solve_decision. Defined.*)

Definition updog (m: M) (gamma: Loc RI) (alpha: nat) (ri: RI) : (PathLoc -> M) :=
  λ (pl: PathLoc) , match pl with | (p, i) =>
        if decide (p ≠ [] /\ (plsplit p) ∈ pls_of_loc gamma /\ i < nat_of_extstep alpha ri) then
          m
        else
          unit
      end.

Lemma updog_eq_m p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, i)) = m. Admitted.
    
Lemma updog_eq_unit1 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, S i)) = unit. Admitted.
    
Lemma updog_eq_unit2 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p ++ [i], 0)) = unit. Admitted.

(*Lemma updog_base_eq_unit1 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p, i)) = unit. Admitted.
    
Lemma updog_base_eq_unit2 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p, S i)) = unit. Admitted.*)
    
Lemma updog_base_eq_m p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p ++ [i], 0)) = m. Admitted.
    
Lemma updog_other_eq_both p i alpha ri gamma m
  (is_not_in : (p, i) ∉ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, i)) = (updog m gamma alpha ri (p, S i)). Admitted.
    
Lemma updog_other_eq_unit p i alpha ri gamma m
  (is_not_in : (p, i) ∉ pls_of_loc gamma)
    : (updog m gamma alpha ri (p ++ [i], 0)) = unit. Admitted.
    
Lemma view_exchange_cond_of_no_change ref view x y
  : view_exchange_cond ref view x y x y.
Proof. unfold view_exchange_cond. intro.
  assert (exists t , t = rel M M ref (dot y p)) by (exists (rel M M ref (dot y p)); trivial).
  deex.
  rewrite <- H. destruct t; crush.
  apply reflex.  
Qed.

Lemma unit_dot_left a : dot unit a = a. Admitted.

Definition node_live_op (n1 n2: Node M) : node_live (n1 ⋅ n2) = dot (node_live n1) (node_live n2). Admitted.

Lemma pl_not_in_of_pl_in_extloc pl alpha (ri: RI) gamma
  : pl ∈ pls_of_loc (ExtLoc alpha ri gamma) -> pl ∉ pls_of_loc gamma. Admitted.
  
Lemma refinement_of_index_eq_refinement_of_of_in_pls_of_loc p i alpha ri gamma
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : refinement_of_index M RI i = refinement_of ri.
    Admitted.
  
Lemma view_exchange_cond_of_borrow_exchange_cond alpha ri gamma z m f m' f' p i borrow_branch
  (i_matches : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
  (active_lifetime : multiset nat)
  (exchange_cond : borrow_exchange_cond (refinement_of ri) z m f m' f')
  (isb : lmap_is_borrow active_lifetime (ExtLoc alpha ri gamma) z borrow_branch)
  : view_exchange_cond
    (refinement_of_index M RI i)
    (node_view (refinement_of_index M RI) (node_of_pl (as_tree borrow_branch) (p,i)) active_lifetime)
    m f m' f'.
Proof.
  have h := refinement_of_index_eq_refinement_of_of_in_pls_of_loc p i alpha ri gamma.
  rewrite h; trivial. clear h.
  unfold view_exchange_cond. unfold borrow_exchange_cond in *.
  unfold lmap_is_borrow in *.
  intro extra. intro.
  assert (tpcm_le z extra).
  - apply isb with (pl := (p,i)); trivial.
  - unfold tpcm_le in H0. deex. rewrite <- H0.
    rewrite tpcm_assoc. 
    rewrite tpcm_assoc. apply exchange_cond.
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
    repeat (setoid_rewrite <- as_tree_dot).
    repeat (setoid_rewrite <- as_tree_dot in sinv).
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
    
    assert (exists active_lifetime , active_lifetime = multiset_add kappa l) by (exists (multiset_add kappa l); trivial). deex. rewrite <- H in *. clear H. clear kappa. clear l.
    
    apply flows_preserve_branch_all_total_in_refinement_domain
      with (t := build (ExtLoc alpha ri gamma) (CellCon f ∅) ⋅ build gamma (CellCon m ∅))
      (down := updog m gamma alpha ri)
      (up   := updog m' gamma alpha ri); trivial.
    
    intros. unfold flow_cond.
    have the_case : Decision ((p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma)) by solve_decision.
    destruct the_case.
    
    (* interesting case: ext location *)
    + rewrite (updog_eq_m p i); trivial. rewrite (updog_eq_m p i); trivial.
      rewrite (updog_eq_unit1 p i); trivial. rewrite (updog_eq_unit1 p i); trivial.
      rewrite (updog_eq_unit2 p i); trivial. rewrite (updog_eq_unit2 p i); trivial.
      rewrite <- forall_node_op. rewrite <- forall_node_op.
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
      
    + have the_case2 : Decision ((p, i) ∈ pls_of_loc gamma) by solve_decision.
      destruct the_case2.
      
      (* semi-interesting case: base location *)
      * 
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite <- (updog_other_eq_both p i); trivial.
        (*rewrite (updog_base_eq_unit1 p i); trivial. rewrite (updog_base_eq_unit1 p i); trivial.
        rewrite (updog_base_eq_unit2 p i); trivial. rewrite (updog_base_eq_unit2 p i); trivial.*)
        rewrite (updog_base_eq_m p i); trivial. rewrite (updog_base_eq_m p i); trivial.
        
        rewrite <- forall_node_op. rewrite <- forall_node_op.
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
        rewrite tpcm_comm.
        assert (dot m m' = dot m' m) by apply tpcm_comm.
        rewrite H.
        apply view_exchange_cond_of_no_change.

      (* uninteresting case *)
      * 
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite <- (updog_other_eq_both p i); trivial.
        rewrite updog_other_eq_unit; trivial.
        rewrite updog_other_eq_unit; trivial.

        rewrite <- forall_node_op. rewrite <- forall_node_op.
        rewrite node_live_op. rewrite node_live_op.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite node_node_cell_cell. rewrite node_node_cell_cell.
        rewrite build_rest_triv; trivial.
        rewrite build_rest_triv; trivial.
        rewrite build_rest_triv; trivial.
        rewrite build_rest_triv; trivial.
        rewrite tpcm_comm.
        apply view_exchange_cond_of_no_change.
Qed.
