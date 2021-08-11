From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
From stdpp Require Import option.
Require Import Burrow.gmap_utils.
Require Import Burrow.rollup.
Require Import Burrow.indexing.
Require Import Burrow.locations.
Require Import Burrow.tactics.
Require Import Burrow.assoc_comm.
Require Import Coq.Arith.Wf_nat. 

Require Import coq_tricks.Deex.

Definition lmap M `{!EqDecision M} `{!TPCM M}
                RI `{!EqDecision RI, !Countable RI}
  := gmap (Loc RI) (Cell M).
Inductive State M `{!EqDecision M} `{!TPCM M}
                RI `{!EqDecision RI, !Countable RI, !RefinementIndex M RI} :=
  | StateCon : Lifetime -> lmap M RI -> State M RI
.
Arguments StateCon {M}%type_scope {EqDecision0 TPCM0}
    {RI}%type_scope {EqDecision1 Countable0 RefinementIndex0} _ _.

Section ResourceProofs.
    
Context {M} `{!EqDecision M} `{!TPCM M}.
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

Global Instance lmap_op : Op (lmap M RI) := λ x y ,
    merge cell_op_opt x y.

Global Instance state_op : Op (State M RI) := λ x y ,
      match x, y with
  | StateCon active1 lmap1, StateCon active2 lmap2 =>
      StateCon (multiset_add active1 active2) (lmap1 ⋅ lmap2)
  end.
  
Lemma lmap_op_comm (x y : gmap (Loc RI) (Cell M)) :
    lmaps_equiv (x ⋅ y) (y ⋅ x).
Proof.
  unfold "⋅", "≡", lmap_op. intro.
  unfold lmap_lookup.
  repeat (rewrite lookup_merge).
  unfold diag_None, cell_op_opt. destruct (x !! l), (y !! l); trivial.
  apply cell_op_comm.
Qed.
  
Lemma lmap_op_assoc (x y z : gmap (Loc RI) (Cell M)) :
    lmaps_equiv (x ⋅ (y ⋅ z)) ((x ⋅ y) ⋅ z).
Proof.
  unfold "⋅", "≡", lmap_op. intro.
  unfold lmap_lookup.
  repeat (rewrite lookup_merge).
  unfold diag_None, cell_op_opt. destruct (x !! l), (y !! l), (z !! l); trivial.
  apply cell_op_assoc.
Qed.
  (*- unfold "≡", option_equiv. apply Some_Forall2. apply cell_op_assoc.
  - unfold "≡", option_equiv. apply Some_Forall2. trivial.
  - unfold "≡", option_equiv. apply Some_Forall2. trivial.
  - unfold "≡", option_equiv. apply Some_Forall2. trivial.
  - unfold "≡", option_equiv. apply Some_Forall2. trivial.
  - unfold "≡", option_equiv. apply Some_Forall2. trivial.
  - unfold "≡", option_equiv. apply Some_Forall2. trivial.
  - unfold "≡", option_equiv. apply None_Forall2. Qed.*)

Lemma state_assoc (x y z : State M RI) : (x ⋅ (y ⋅ z)) ≡ ((x ⋅ y) ⋅ z).
Proof.
  unfold "⋅", "≡",state_equiv,state_op. destruct x, y, z. split.
  - apply multiset_add_assoc.
  - apply lmap_op_assoc.
Qed.

Lemma state_comm (x y : State M RI) : (x ⋅ y) ≡ (y ⋅ x).
Proof.
  unfold "⋅", "≡", state_equiv, state_op. destruct x, y. split.
  - apply multiset_add_comm.
  - apply lmap_op_comm.
Qed.

Global Instance state_op_assoc : Assoc state_equiv op := state_assoc.
Global Instance state_op_comm : Comm state_equiv op := state_comm.

Global Instance lmaps_equiv_refl : Reflexive lmaps_equiv. 
Proof. unfold Reflexive, lmaps_equiv. intros. trivial. Qed.

Global Instance lmaps_equiv_symm : Symmetric lmaps_equiv.
Proof. unfold Symmetric, lmaps_equiv. intros. symmetry. apply H. Qed.

Global Instance lmaps_equiv_trans : Transitive lmaps_equiv.
Proof. unfold Transitive, lmaps_equiv. intros. have a := H l. have b := H0 l.
    setoid_rewrite <- a in b. trivial. Qed.
    
Global Instance state_equiv_symm : Symmetric state_equiv.
Proof. unfold Symmetric. intros. unfold state_equiv in *. destruct x, y. destruct_ands.
  split. * symmetry. trivial. * symmetry. trivial. Qed.
  
Global Instance state_equiv_trans : Transitive state_equiv.
Proof. unfold Transitive, state_equiv. destruct x, y, z. intros. destruct_ands. subst.
  split; trivial. setoid_rewrite H2. setoid_rewrite <- H1. apply lmaps_equiv_refl. Qed.

Global Instance state_equiv_refl : Reflexive state_equiv.
Proof. unfold Reflexive, state_equiv. destruct x. split; trivial. apply lmaps_equiv_refl.
Qed.


Global Instance lmaps_op_proper
    : Proper (lmaps_equiv ==> lmaps_equiv ==> lmaps_equiv) lmap_op.
Proof.
  unfold Proper, lmaps_equiv, "==>", lmap_op. intros. unfold lmap_lookup in *.
      repeat (rewrite lookup_merge). unfold diag_None.
      have a := H l. have b := H0 l. clear H. clear H0.
      unfold cell_op_opt.
      destruct (x !! l), (x0 !! l), (y !! l), (y0 !! l); trivial.
      - setoid_rewrite a. setoid_rewrite b. trivial.
      - setoid_rewrite a. setoid_rewrite b. apply op_trivial_cell. unfold cell_trivial, triv_cell. split; trivial.
      - setoid_rewrite a. setoid_rewrite b. setoid_rewrite cell_op_comm. apply op_trivial_cell. unfold cell_trivial, triv_cell. split; trivial.
      - setoid_rewrite a. setoid_rewrite b. apply op_trivial_cell. unfold cell_trivial, triv_cell. split; trivial.
      - setoid_rewrite a. setoid_rewrite <- b. symmetry. apply op_trivial_cell. unfold cell_trivial, triv_cell. split; trivial.
      - setoid_rewrite a. setoid_rewrite <- b. trivial.
      - setoid_rewrite <- a. setoid_rewrite b. symmetry. setoid_rewrite cell_op_comm. apply op_trivial_cell. unfold cell_trivial, triv_cell. split; trivial.
      - setoid_rewrite <- a. setoid_rewrite b. trivial.
      - setoid_rewrite <- a. setoid_rewrite <- b. symmetry. apply op_trivial_cell. unfold cell_trivial, triv_cell. split; trivial.
Qed.

Global Instance state_op_proper : Proper ((≡) ==> (≡) ==> (≡)) state_op.
Proof. unfold Proper, equiv, "==>", state_equiv, state_op. intros. destruct x, y, x0, y0.
  destruct_ands. subst. split; trivial. setoid_rewrite H2. setoid_rewrite H1.
  apply lmaps_equiv_refl.
Qed.

Definition live (loc: Loc RI) (m: M) :=
      (*StateCon empty_lifetime (build loc (CellCon m empty)).*)
      StateCon empty_lifetime {[ loc := CellCon m empty ]}.
    
Definition reserved (lt: Lifetime) (loc: Loc RI) (m:M) :=
      StateCon empty_lifetime {[ loc := CellCon unit {[ (lt,m) ]} ]}.
    
Definition active (lt: Lifetime) : State M RI :=
      StateCon lt ∅.

Definition state_unit : State M RI := StateCon empty_lifetime ∅.

Lemma stuffx T (x: option T) :
  match x with
  | Some _ => match x with
              | Some c => Some c
              | None => None
              end
  | None => None
  end = x. Proof. destruct x; trivial. Qed.

Lemma lmap_op_empty_lookup (l: lmap M RI) i : (l ⋅ ∅) !! i = l !! i.
Proof.
  unfold "⋅", lmap_op. rewrite lookup_merge. unfold diag_None. rewrite lookup_empty.
  unfold cell_op_opt. apply stuffx. Qed.

Lemma lmaps_op_empty l : lmaps_equiv (l ⋅ ∅) l.
Proof.
  unfold lmaps_equiv. intro. unfold lmap_lookup.
  assert ((l ⋅ ∅) !! l0 = l !! l0).
  * apply lmap_op_empty_lookup.
  * rewrite H. trivial.
Qed.

Lemma op_state_unit x : x ⋅ state_unit ≡ x.
Proof. unfold state_unit, "⋅", state_op. destruct x. unfold "≡", state_equiv. split.
  - apply multiset_add_empty.
  - apply lmaps_op_empty.
Qed.

Definition as_tree (l : lmap M RI) : Branch M :=
  map_fold (λ k cell b , b ⋅ build k cell) BranchNil l.
  
Definition lmap_is_borrow (lt: Lifetime) (loc: Loc RI) (m: M) (l : lmap M RI) :=
  forall pl , pl ∈ pls_of_loc loc ->
    ∀ y , m_valid y -> node_view (refinement_of_nat M RI) (node_of_pl (as_tree l) pl) lt y -> tpcm_le m y.

Definition is_borrow (lt: Lifetime) (loc: Loc RI) (m: M) (state: State M RI) :=
    match state with
    | StateCon _ l => lmap_is_borrow lt loc m l
    end.

Definition branch_no_live (b: Branch M) := ∀ pl , cell_live (cell_of_pl b pl) = unit.
Definition lmap_no_live (l: lmap M RI) := branch_no_live (as_tree l).

Definition state_no_live (state: State M RI) :=
    match state with
    | StateCon a l => a = empty_multiset /\ lmap_no_live l
    end.
  
Definition state_inv (state: State M RI) : Prop :=
  match state with
  | StateCon active l =>
       multiset_no_dupes active /\
       valid_totals (refinement_of_nat M RI) (as_tree l) active
  end.
  
Global Instance build_proper (loc: Loc RI) : Proper ((≡) ==> (≡)) (build loc). Admitted.

Global Instance branch_equiv_preorder : PreOrder branch_equiv. Admitted.

Lemma branch_is_trivial_build_triv_cell (loc: Loc RI)
  : branch_trivial (build loc triv_cell). Admitted.
  
Lemma as_tree_equal_empty y
  (le : lmaps_equiv y ∅) : as_tree y ≡ as_tree ∅.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
  generalize le. clear le.
  apply map_ind with (P := λ (y: gmap (Loc RI) (Cell M)),
      lmaps_equiv y ∅ → as_tree y ≡ as_tree ∅).
  - intros. trivial.
  - intros.
    unfold as_tree.
    assert (
      map_fold (λ (k : Loc RI) (cell : Cell M) (b : Branch M), b ⋅ build k cell)
        BranchNil (<[i:=x]> m)
        ≡
      map_fold (λ (k : Loc RI) (cell : Cell M) (b : Branch M), b ⋅ build k cell)
        BranchNil m ⋅ build i x
      ).
    + apply (map_fold_insert (≡)
        (λ (k : Loc RI) (cell : Cell M) (b : Branch M), b ⋅ build k cell)).
      * intros. unfold Proper, "==>". intros. setoid_rewrite H2. trivial.
      * intros. solve_assoc_comm.
      * trivial.
    + setoid_rewrite H2. clear H2.
      unfold lmaps_equiv in H1. have h := H1 i.
        unfold lmap_lookup in h. rewrite lookup_empty in h. rewrite lookup_insert in h.
        setoid_rewrite h.
        have q := branch_is_trivial_build_triv_cell i.
        setoid_rewrite op_trivial_branch; trivial.
        apply H0.
        unfold lmaps_equiv. intro.
        have t := H1 l.
        have e : Decision (l = i) by solve_decision. destruct e.
        * subst l. unfold lmap_lookup. rewrite H. rewrite lookup_empty. trivial.
        * unfold lmap_lookup in *. rewrite lookup_insert_ne in t; trivial.
            crush.
Qed.

Lemma rewrite_map_fold_builder i x (m: gmap (Loc RI) (Cell M))
  (m_i_None: m !! i = None) :
      as_tree (<[i:=x]> m) ≡ as_tree m ⋅ build i x.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
unfold as_tree.
apply (map_fold_insert (≡)
        (λ (k : Loc RI) (cell : Cell M) (b : Branch M), b ⋅ build k cell)).
  - intros. unfold Proper, "==>". intros. setoid_rewrite H. trivial.
  - intros. solve_assoc_comm.
  - trivial.
Qed.

Lemma rewrite_map_as_insertion `{Countable K} {V} (y: gmap K V) i c
  (y_i : y !! i = Some c) : ∃ y', y = <[i:=c]> y' /\ y' !! i = None. Admitted.

Global Instance as_tree_proper : Proper ((lmaps_equiv) ==> (≡)) as_tree.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
unfold Proper, "==>". intro.
  apply map_ind with (P := λ x,
      ∀ y : gmap (Loc RI) (Cell M), lmaps_equiv x y → as_tree x ≡ as_tree y).
  - intros. symmetry. apply as_tree_equal_empty. apply lmaps_equiv_symm. trivial.
  - intros. destruct (y !! i) eqn:y_i.
    + have rmai := rewrite_map_as_insertion y i c y_i. deex. destruct_ands.
      subst y. rename y' into y.
      clear y_i.
      setoid_rewrite rewrite_map_fold_builder; trivial.
      unfold lmaps_equiv in H1. have h := H1 i. unfold lmap_lookup in h.
        rewrite lookup_insert in h. rewrite lookup_insert in h.
        setoid_rewrite h.
        setoid_rewrite (H0 y); trivial.
        unfold lmaps_equiv. intro. have j := H1 l.
        have e : Decision (l = i) by solve_decision. destruct e.
        * subst l. unfold lmap_lookup. rewrite H. rewrite H3. trivial.
        * unfold lmap_lookup in *.
          assert (i ≠ l) by crush.
          rewrite lookup_insert_ne in j; trivial.
          rewrite lookup_insert_ne in j; trivial.
    + setoid_rewrite rewrite_map_fold_builder; trivial.
      unfold lmaps_equiv in H1. have j := H1 i.
      unfold lmap_lookup in j. rewrite lookup_insert in j. rewrite y_i in j.
      setoid_rewrite j.
      have q := branch_is_trivial_build_triv_cell i.
      setoid_rewrite op_trivial_branch; trivial.
      apply H0.
      unfold lmaps_equiv. intro.
      have e : Decision (i = l) by solve_decision. destruct e.
      * subst l. unfold lmap_lookup. rewrite H. rewrite y_i. trivial.
      * have r := H1 l. unfold lmap_lookup in *.
        rewrite lookup_insert_ne in r; trivial.
Qed.

Global Instance state_inv_proper : Proper ((≡) ==> impl) state_inv.
Proof.
  unfold Proper, equiv, "==>", impl, state_inv, state_equiv. destruct x, y. intros.
  destruct_ands. subst. split; trivial.
  setoid_rewrite <- H2. trivial.
Qed.

Global Instance state_valid : Valid (State M RI) :=
  λ v , ∃ p , state_inv (v ⋅ p).
  
Global Instance state_valid_proper : Proper ((≡) ==> impl) state_valid.
Proof.
  unfold Proper, equiv, "==>", impl, state_valid. destruct x, y. intros.
  deex. exists p.
  destruct_ands. subst. 
  setoid_rewrite <- H. trivial.
Qed.

Lemma state_valid_state_unit : state_valid state_unit. Admitted.
  
Lemma as_tree_op (a b: lmap M RI)
    : as_tree (a ⋅ b) ≡ (as_tree a) ⋅ (as_tree b).
Proof. unfold as_tree.
    symmetry.
  apply map_fold_merge.
  - intros. setoid_rewrite branch_op_comm. apply op_trivial_branch.
      unfold branch_trivial. trivial.
  - intros. unfold cell_op_opt. trivial.
  - intros. unfold cell_op_opt. trivial.
  - intros. unfold cell_op_opt. exists (v ⋅ w). trivial.
  - intros. unfold Proper, "==>". intros. setoid_rewrite H. trivial.
  - intros. unfold Proper, "==>". intros. setoid_rewrite H0. setoid_rewrite H. trivial.
  - intros.
    setoid_rewrite <- branch_op_assoc.
    setoid_replace (build k2 v2 ⋅ build k1 v1) with (build k1 v1 ⋅ build k2 v2); trivial.
        apply branch_op_comm.
  - intros.
      setoid_rewrite <- branch_op_assoc.
      setoid_replace (build i x ⋅ (s ⋅ build i y)) with (s ⋅ build i z); trivial.
      setoid_rewrite branch_op_assoc.
      setoid_replace (build i x ⋅ s) with (s ⋅ build i x).
      + setoid_rewrite <- branch_op_assoc.
        setoid_replace ((build i x ⋅ build i y)) with (build i z); trivial.
        Admitted.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, m) dot live(gamma, n) equiv live(gamma, m dot n) *)

(*Lemma live_dot_live
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI}
    (gamma: Loc RI) (m1 m2: M)
    : live gamma m1 ⋅ live gamma m2 ≡ live gamma (dot m1 m2).
Proof.
  unfold "≡", state_equiv, live. unfold "⋅", state_op. split.
  - apply empty_add_empty_eq_empty.
  - apply equiv_extensionality_cells. intro.
      setoid_rewrite <- cell_of_pl_op.
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
      unfold "≡", cell_equiv, "⋅", cell_op. split; trivial.
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
(* active(k1) . active(k2) = active(k1 . k2) *)

Lemma active_additive (lt1 lt2: Lifetime)
  : active (multiset_add lt1 lt2) ≡ active lt1 ⋅ active lt2.
Proof.
  unfold active, "⋅", state_op. unfold "≡", state_equiv. split; trivial.
  unfold lmaps_equiv. intros. unfold "⋅", lmap_op, lmap_lookup.
  rewrite lookup_merge. unfold diag_None. rewrite lookup_empty. trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow(kappa, gamma, unit) is unit *)

Lemma is_borrow_unit (lt: Lifetime) (loc: Loc RI)
  : is_borrow lt loc unit state_unit.
Proof. unfold is_borrow. unfold state_unit. unfold lmap_is_borrow.
  intros. apply unit_le. Qed.
  
Lemma cell_live_cell_of_pl_as_tree_empty
  pl : cell_live (cell_of_pl (as_tree ∅) pl) = unit. Admitted.
  
Lemma state_no_live_unit
  : state_no_live state_unit.
Proof.
  unfold state_no_live, state_unit. split; trivial. unfold lmap_no_live.
  unfold branch_no_live. intros.
  unfold as_tree. rewrite map_fold_empty.
  apply cell_live_cell_of_pl_as_tree_empty.
Qed.

Lemma active_empty_unit
  : active empty_lifetime ≡ state_unit.
Proof.
  unfold active, state_unit. trivial. Qed.
  
(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow (a . b) -> borrow a *)

Lemma is_borrow_weaken kappa gamma (a b: M) state
  : is_borrow kappa gamma (dot a b) state -> is_borrow kappa gamma a state.
Proof.
  intros. unfold is_borrow in *. destruct state. unfold lmap_is_borrow in *.
  intros.
  have h := H pl H0 y H1 H2.
  unfold tpcm_le in *. deex. exists (dot b c). rewrite tpcm_assoc. trivial.
Qed.
    
(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, m) . borrow(kappa, gamma, k) --> valid (a . b) *)
    
Lemma as_tree_singleton (loc: Loc RI) (cell: Cell M)
  : as_tree {[loc := cell]} ≡ build loc cell.
Proof. unfold as_tree. unfold map_fold. unfold foldr, curry. unfold "∘".
  rewrite map_to_list_singleton. unfold Datatypes.uncurry.
  unfold "⋅". unfold branch_op. trivial. Qed.

Lemma forall_equiv_branch_all_total_in_refinement_domain roi branch lt idx
  : branch_all_total_in_refinement_domain roi branch lt idx
    <-> forall pl, node_all_total_in_refinement_domain roi (node_of_pl branch pl) lt (plend pl). Admitted.

Definition any_pl_of_loc (loc: Loc RI) : PathLoc. Admitted.

Lemma any_pl_of_loc_is_of_loc (loc: Loc RI)
  : any_pl_of_loc loc ∈ pls_of_loc loc. Admitted.

Lemma in_refinement_domain_of_natird roi (node: Node M) (lifetime: Lifetime) (idx: nat)
  (natird : node_all_total_in_refinement_domain roi node lifetime idx)
      : in_refinement_domain roi idx (node_total roi node lifetime).
Proof.
  unfold node_all_total_in_refinement_domain in natird.
    destruct node. destruct_ands; trivial. Qed.

Lemma exists_some_of_match {A} (t: option A) (is_some : match t with | Some _ => True | None => False end)
  : exists x , t = Some x. Proof. destruct t. - exists a; trivial. - contradiction. Qed.

(*node_view roi (a ⋅ b) k -> node_view roi a k
            (node_of_pl (build gamma (CellCon m ∅) ⋅ as_tree l2 ⋅ as_tree l0)
               (any_pl_of_loc gamma)) kappa
            (node_total_minus_live (refinement_of_nat M RI)
               (node_of_pl (build gamma (CellCon m ∅) ⋅ as_tree l2 ⋅ as_tree l0)
                  (any_pl_of_loc gamma))
               (multiset_add (multiset_add (multiset_add kappa empty_lifetime) l1) l))*)

Lemma node_view_le roi a b lt y : node_view roi (a ⋅ b) lt y -> node_view roi a lt y.
Admitted.

Lemma node_view_le2 roi a lt y z : node_view roi a lt y -> node_view roi a lt (dot y z).
Admitted.

Lemma node_view_strip roi a b c loc kappa x :
  node_view roi (node_of_pl (a ⋅ b ⋅ c) loc) kappa x ->
  node_view roi (node_of_pl b loc) kappa x.
Proof using Countable0 EqDecision0 EqDecision1 M RI RefinementIndex0 TPCM0.
  intro.
  setoid_rewrite <- node_of_pl_op in H.
  assert (node_view roi (node_of_pl (a ⋅ b) loc) kappa x).
  - apply node_view_le with (b := node_of_pl c loc). trivial.
  - setoid_rewrite <- node_of_pl_op in H0.
    setoid_rewrite node_op_comm in H0.
    apply node_view_le with (b := node_of_pl a loc). trivial.
Qed.

Lemma node_node_cell_cell b pl : node_live (node_of_pl b pl) = cell_live (cell_of_pl b pl).
Proof. unfold cell_of_pl. unfold node_live. unfold cell_live. destruct (node_of_pl b pl).
trivial. Qed.

Lemma tpcm_le_m_node_live_with_m m gamma e b c
    : tpcm_le m
      (node_live (node_of_pl (build gamma (CellCon m e) ⋅ b ⋅ c) (any_pl_of_loc gamma))).
Proof.
  rewrite node_node_cell_cell.
  setoid_rewrite <- cell_of_pl_op.
  setoid_rewrite <- cell_of_pl_op.
  setoid_rewrite build_spec.
  - destruct (cell_of_pl b (any_pl_of_loc gamma)).
    destruct (cell_of_pl c (any_pl_of_loc gamma)).
    unfold cell_live. unfold "⋅", cell_op.
    unfold tpcm_le. exists (dot m0 m1). apply tpcm_assoc.
  - apply any_pl_of_loc_is_of_loc.
Qed.

Lemma m_valid_of_right_dot a b
  : m_valid (dot a b) -> m_valid b. 
Proof.
  rewrite tpcm_comm. intro. apply valid_monotonic with (y := a). trivial. Qed.

Lemma live_and_borrow_implies_valid (gamma: Loc RI) (kappa: Lifetime) (m k: M) (b: State M RI)
    (isb: is_borrow kappa gamma k b)
    (isv: ✓(active kappa ⋅ live gamma m ⋅ b))
    : m_valid (dot m k).
Proof.
  unfold "✓", state_valid in isv. deex. destruct p.
  unfold state_inv in isv. unfold live in isv. destruct b. unfold "⋅" in isv.
  unfold state_op in isv. destruct isv. clear H. rename H0 into isv.
  unfold is_borrow, lmap_is_borrow in isb.
  unfold valid_totals in isv. destruct_ands. rename H into isv.
  setoid_rewrite as_tree_op in isv.
  setoid_rewrite as_tree_op in isv.
  setoid_rewrite as_tree_op in isv.
  setoid_rewrite as_tree_singleton in isv.
  generalize isv. clear isv. rewrite forall_equiv_branch_all_total_in_refinement_domain. intro isv.
  
  rename isb into isb'. have isb := isb' (any_pl_of_loc gamma) (any_pl_of_loc_is_of_loc gamma). clear isb'.
  rename isv into isv'. have isv := isv' (any_pl_of_loc gamma). clear isv'.
  have nvlt := node_view_le_total_minus_live _ _ _ _ _ _ isv.
  unfold lifetime_included in *.
  have nvlt' := nvlt kappa (multiset_add_chain_included _ _ _ _). clear nvlt.
  unfold view_sat in nvlt'.
  
  have nvlt'' := node_view_strip _ _ _ _ _ _ _ nvlt'.
  have ineq := isb _ _ nvlt''.
  
  have ird := in_refinement_domain_of_natird _ _ _ _ isv.
  unfold in_refinement_domain in ird.
  have elem_is_val := rel_valid_left _ _ _ _ ird.
  clear ird.
  
  assert (m_valid
           (node_total_minus_live (refinement_of_nat M RI)
              (node_of_pl (build gamma (CellCon m ∅) ⋅ as_tree l2 ⋅ as_tree l0)
                 (any_pl_of_loc gamma))
              (multiset_add (multiset_add (multiset_add kappa empty_lifetime) l1) l))) as mv2.
   - rewrite <- node_live_plus_node_total_minus_live in elem_is_val.
      have j := m_valid_of_right_dot _ _ elem_is_val. trivial.
   -

  assert (tpcm_le m (node_live 
              (node_of_pl (build gamma (CellCon m ∅) ⋅ as_tree l2 ⋅ as_tree l0)
                 (any_pl_of_loc gamma)))) by apply tpcm_le_m_node_live_with_m.
  have summed_ineqs := le_add2 _ _ _ _ H (ineq mv2).
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
(* live(gamma, m) --> valid m *)

Lemma live_implies_valid (gamma: Loc RI) (m: M)
    (isv: ✓(live gamma m))
    : m_valid m.
Proof.
  rewrite <- unit_dot.
  apply live_and_borrow_implies_valid with (gamma := gamma) (kappa := empty_lifetime) (b := state_unit).
  - apply is_borrow_unit.
  - setoid_rewrite op_state_unit.
    setoid_rewrite active_empty_unit.
    setoid_rewrite state_comm.
    setoid_rewrite op_state_unit.
    trivial.
Qed.

(**** exchange stuff ****)

Definition borrow_exchange_cond
    {R} `{!EqDecision R, !TPCM R}
    (ref: Refinement R M) (z:R) (m:M) (f:R) (m':M) (f':R) :=
  ∀ p ,
  rel_defined R M ref (dot (dot f z) p) ->
      rel_defined R M ref (dot (dot f' z) p)
      /\ mov
            (dot m (rel R M ref (dot (dot f z) p)))
            (dot m' (rel R M ref (dot (dot f' z) p))).

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

Definition plsplit (ln: list nat) : PathLoc. Admitted.

(*Global Instance thing_dec (p:PathLoc) (gamma: Loc RI) (i alpha:nat) (ri:RI) :
  Decision (p ∈ pls_of_loc gamma /\ i < nat_of_extstep alpha ri). solve_decision. Defined.*)

Definition updog (m: M) (gamma: Loc RI) (alpha: nat) (ri: RI) : (PathLoc -> M) :=
  λ (pl: PathLoc) , match pl with | (p, i) =>
        if decide (p ≠ [] /\ (plsplit p) ∈ pls_of_loc gamma /\ i < nat_of_extstep alpha ri) then
          m
        else
          unit
      end.
      
Definition updog_se (gamma: Loc RI) (alpha: nat) (ri: RI) : gset PathLoc. Admitted.

Lemma updog_se_okay (m: M) (gamma: Loc RI) (alpha: nat) (ri: RI)
  : ∀ (p : list nat) (i : nat),
    (p, i) ∉ updog_se gamma alpha ri
    → updog m gamma alpha ri (p, i) = unit.
    Admitted.

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
    
(*Lemma specific_exchange_cond_of_no_change ref p x y h s
  : specific_exchange_cond ref p x y h s x y h s. Admitted.*)
  
Lemma pl_not_in_of_pl_in_extloc pl alpha (ri: RI) gamma
  : pl ∈ pls_of_loc (ExtLoc alpha ri gamma) -> pl ∉ pls_of_loc gamma. Admitted.
  
Lemma refinement_of_nat_eq_refinement_of_of_in_pls_of_loc p i alpha ri gamma
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : refinement_of_nat M RI i = refinement_of ri.
    Admitted.
    
(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(m, gamma) -> exists kappa , active(kappa) . reserved(kappa, m, gamma) *)

Definition max_ltunit_in_branch (b: Branch M) : nat. Admitted.

(*Lemma branch_all_total_in_refinement_domain_of_preserved_cell_totals ref b1 b2 lt1 lt2 idx
  (pres: ∀ pl , cell_total (cell_of_pl b1 pl) lt1 = cell_total (cell_of_pl b2 pl) lt2)
  (batird : branch_all_total_in_refinement_domain ref b1 lt1 idx)
  : branch_all_total_in_refinement_domain ref b2 lt2 idx.
Admitted.*)

Lemma valid_totals_of_preserved_cell_totals ref b1 b2 lt1 lt2
  (pres: ∀ pl , cell_total (cell_of_pl b1 pl) lt1 = cell_total (cell_of_pl b2 pl) lt2)
  (batird : valid_totals ref b1 lt1)
    : valid_totals ref b2 lt2.
Admitted.

Lemma lt_singleton_not_eq_to_cell_lt ltunit b pl
  (isgreater: ltunit > max_ltunit_in_branch b)
  : match cell_of_pl b pl with CellCon _ rset =>
    ∀ r , r ∈ rset -> match r with (lt, _) => ¬(multiset_in lt ltunit) end
    end. Admitted.
  
Lemma sum_reserved_over_lifetime_union (a b: listset (Lifetime * M)) lt
  (disj: a ∩ b ≡ ∅)
  : sum_reserved_over_lifetime (a ∪ b) lt
      = dot (sum_reserved_over_lifetime a lt) (sum_reserved_over_lifetime b lt). Admitted.
    
Lemma sum_reserved_over_lifetime_singleton r lt
  : sum_reserved_over_lifetime {[ r ]} lt = reserved_get_or_unit r lt.
Proof. unfold sum_reserved_over_lifetime. rewrite set_fold_singleton.
  apply unit_dot_left. Qed.

Lemma sum_reserved_over_lifetime_eq_adding_singleton g active_lifetime (lt: Lifetime) alt
  (notin : ∀ r : multiset nat * M, r ∈ g → let (lt, _) := r in ¬ multiset_in lt alt)
  : (sum_reserved_over_lifetime g active_lifetime)
  = (sum_reserved_over_lifetime g (multiset_add (lt_singleton alt) active_lifetime)).
  Admitted.

Lemma borrow_begin (m: M) gamma p
  (si: state_inv (live gamma m ⋅ p))
     : exists kappa , state_inv (active kappa ⋅ reserved kappa gamma m ⋅ p)
        /\ kappa ≠ empty_lifetime.
Proof.
  destruct p. rename l into active_lifetime. rename l0 into p.
  
  assert ((max_ltunit_in_branch (as_tree p) `max` max_ltunit_in_lt active_lifetime) + 1 > 
    max_ltunit_in_branch (as_tree p)) as ineq1 by lia.
  assert ((max_ltunit_in_branch (as_tree p) `max` max_ltunit_in_lt active_lifetime) + 1 >
    max_ltunit_in_lt active_lifetime) as ineq2 by lia.
  full_generalize ((max_ltunit_in_branch (as_tree p) `max` max_ltunit_in_lt active_lifetime) + 1) as alt.
  exists (lt_singleton alt).
  
  unfold state_inv in *. unfold "⋅", state_op, active, reserved, live in *.
    destruct_ands. split.
  - split.
  
  + rewrite multiset_add_empty.
    rewrite multiset_add_empty_left in H.
    apply multiset_no_dupes_of_add_larger_elem; trivial.
  
  + setoid_rewrite as_tree_op.
    setoid_rewrite as_tree_op.
    rewrite multiset_add_empty.
    setoid_rewrite as_tree_singleton.
    rewrite multiset_add_empty_left in H0.
    setoid_rewrite as_tree_op in H0.
    setoid_rewrite as_tree_singleton in H0.
    eapply valid_totals_of_preserved_cell_totals
      with (b1 := build gamma (CellCon m ∅) ⋅ as_tree p)
           (lt1 := active_lifetime); trivial.
    intro.
    
    have h : Decision (pl ∈ pls_of_loc gamma) by solve_decision. destruct h.
    * setoid_rewrite <- cell_of_pl_op.
      setoid_rewrite build_spec; trivial.
      destruct (cell_of_pl (as_tree p) pl) eqn:cellpl.
      unfold cell_total, "⋅", cell_op.
      setoid_replace (∅ ∪ l) with (l) by set_solver.
      have h := lt_singleton_not_eq_to_cell_lt alt (as_tree p) pl ineq1.
      rewrite cellpl in h.
      assert ({[(lt_singleton alt, m)]} ∩ l ≡ ∅) as disjoint_empty.
      -- unfold "≡". intro. rewrite elem_of_empty. rewrite elem_of_intersection.
          rewrite elem_of_singleton. split. ** intro. destruct_ands. have h' := h x H2.
          rewrite H1 in h'. apply h'. apply multiset_in_lt_singleton. ** intro. contradiction.
      -- rewrite sum_reserved_over_lifetime_union; trivial.
        rewrite sum_reserved_over_lifetime_singleton.
        unfold reserved_get_or_unit.
        case_decide.
        ++ rewrite <- sum_reserved_over_lifetime_eq_adding_singleton; trivial.
           rewrite unit_dot_left.
           rewrite tpcm_assoc. trivial.
           assert (dot m m0 = dot m0 m) as co by (apply tpcm_comm). rewrite co. trivial.
        ++ exfalso. apply H1. apply multiset_le_add.
    * setoid_rewrite <- cell_of_pl_op.
      setoid_rewrite build_rest_triv; trivial.
      destruct (cell_of_pl (as_tree p) pl) eqn:cellpl.
      unfold cell_total, "⋅", cell_op, triv_cell.
      setoid_replace (∅ ∪ l) with (l) by set_solver.
      have h := lt_singleton_not_eq_to_cell_lt alt (as_tree p) pl ineq1.
      rewrite cellpl in h.
      rewrite <- sum_reserved_over_lifetime_eq_adding_singleton; trivial.
  - unfold lt_singleton, empty_lifetime, empty_multiset.
    intro. assert ({[alt := 0]} ≠ (∅ : gmap nat nat)).
    + intro. assert ((∅: gmap nat nat) !! alt = None) by (apply lookup_empty).
      rewrite <- H2 in H3.
      rewrite lookup_singleton in H3. discriminate.
    + crush.
Qed.

Lemma borrow_begin_valid (m: M) gamma p
  (si: ✓(live gamma m ⋅ p))
     : exists kappa , ✓(active kappa ⋅ reserved kappa gamma m ⋅ p)
        /\ kappa ≠ empty_lifetime.
Proof.
  unfold "✓", state_valid in si. deex. setoid_rewrite <- state_assoc in si.
  have bb := borrow_begin m gamma (p ⋅ p0) si. deex. exists kappa.
  unfold "✓", state_valid. destruct_ands. split; trivial. exists p0. setoid_rewrite <- state_assoc.
  trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* reserved(kappa, m, gamma) is a borrow *)

Definition cell_of_node (n: Node M) := match n with | CellNode c _ => c end.

Lemma cell_view_of_node_view roi node lt y :
  node_view roi node lt y -> cell_view (cell_of_node node) lt y. Admitted.

Lemma cell_of_node_node_of_pl b pl
  : cell_of_node (node_of_pl b pl) = cell_of_pl b pl.
Proof. unfold cell_of_pl. unfold cell_of_node. trivial. Qed.

Lemma is_borrow_reserved kappa gamma m
  : is_borrow kappa gamma m (reserved kappa gamma m).
Proof.
  unfold is_borrow, reserved, lmap_is_borrow. intros.
    setoid_rewrite as_tree_singleton in H1.
    have h := cell_view_of_node_view _ _ _ _ H1.
    unfold node_view in H1.
    rewrite cell_of_node_node_of_pl in h.
    rewrite build_spec in h; trivial.
    unfold cell_view in h.
    unfold conjoin_reserved_over_lifetime in h.
    rewrite set_fold_singleton in h.
    unfold conjoin_umbrella, umbrella_unit, umbrella, reserved_get_or_unit in h.
    deex. destruct_ands.
    case_decide.
    - unfold tpcm_le in *. deex. subst y0. exists (dot x c).
        subst y. rewrite tpcm_assoc. rewrite tpcm_assoc. f_equal. apply tpcm_comm.
    - assert (multiset_le kappa kappa) by (apply multiset_le_refl). contradiction.
Qed.

Lemma cell_live_cell_of_pl_unit (gamma: Loc RI) (res : listset (Lifetime * M)) pl
 : cell_live (cell_of_pl (build gamma (CellCon unit res)) pl) = unit.
Proof.
  have h : Decision (pl ∈ pls_of_loc gamma) by solve_decision.
  destruct h.
  - rewrite build_spec; trivial.
  - rewrite build_rest_triv; trivial.
Qed.

Lemma state_no_live_reserved kappa gamma m
  : state_no_live (reserved kappa gamma m).
Proof.
  unfold state_no_live. unfold reserved, lmap_no_live, branch_no_live.
  split; trivial.
  intro.
  setoid_rewrite as_tree_singleton.
  apply cell_live_cell_of_pl_unit.
Qed.

Lemma lmaps_equiv_of_tree_equiv a b
  : as_tree a ≡ as_tree b -> lmaps_equiv a b.
Admitted.

Lemma no_live_duplicable (s : State M RI)
  : state_no_live s -> s ⋅ s ≡ s.
Proof.
  destruct s. intro. unfold state_no_live in H. destruct_ands.
  unfold "⋅". unfold state_op. unfold "≡", state_equiv. split.
  - rewrite H. rewrite multiset_add_empty. trivial.
  - unfold lmap_no_live in H0. unfold branch_no_live in H0.
    apply lmaps_equiv_of_tree_equiv.
    setoid_rewrite as_tree_op.
    full_generalize (as_tree l0) as t.
    apply equiv_extensionality_cells.
    intro. setoid_rewrite <- cell_of_pl_op.
    unfold "⋅". have j := H0 pl.
    full_generalize (cell_of_pl t pl) as c.
    unfold cell_live in j. destruct c. unfold cell_op.
    rewrite j. rewrite unit_dot. unfold "≡", cell_equiv. split; trivial.
    set_solver.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow(kappa, m, gamma) -> borrow(kappa', m, gamma) *)

Lemma borrow_lifetime_inclusion kappa kappa' gamma m state
    (li: lifetime_included kappa' kappa)
    (ib: is_borrow kappa gamma m state)
       : is_borrow kappa' gamma m state.
Proof.
  unfold is_borrow in *. destruct state. unfold lmap_is_borrow in *. intros.
  have orig := ib pl H y. apply orig; trivial. clear orig.
  unfold lifetime_included in li.
  apply node_view_inclusion with (lt2 := kappa'); trivial.
Qed.
       
Lemma is_borrow_weaken_lifetime k k1 gamma z b
  : is_borrow k gamma z b -> is_borrow (multiset_add k k1) gamma z b.
Proof.
  intros. apply borrow_lifetime_inclusion with (kappa := k); trivial.
  unfold lifetime_included.
  apply multiset_le_add.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow(kappa, a, gamma) + borrow(kappa, b, gamma) -> borrow(kappa, c, gamma) *)

Lemma borrow_nonseparating_conjunction a b c kappa gamma state1 state2
  (abcr: ∀ r , m_valid r -> tpcm_le a r -> tpcm_le b r -> tpcm_le c r)
    (b1: is_borrow kappa gamma a state1)
    (b2: is_borrow kappa gamma b state2)
    : is_borrow kappa gamma c (state1 ⋅ state2).
Proof.
  unfold is_borrow in *. destruct state1, state2. unfold "⋅", state_op.
  unfold lmap_is_borrow in *.
  intros.
  setoid_rewrite as_tree_op in H1.
  setoid_rewrite <- node_of_pl_op in H1.
  apply abcr; trivial.
  - apply b1 with (pl := pl); trivial.
    apply node_view_le with (b := node_of_pl (as_tree l2) pl). trivial.
  - apply b2 with (pl := pl); trivial.
    apply node_view_le with (b := node_of_pl (as_tree l0) pl).
    setoid_rewrite node_op_comm. trivial.
Qed.

Lemma lmap_no_live_op l1 l2
  (nl1: lmap_no_live l1)
  (nl2: lmap_no_live l2)
  : (lmap_no_live (l1 ⋅ l2)).
Proof.
  unfold lmap_no_live in *.
  unfold branch_no_live in *.
  intro.
  setoid_rewrite as_tree_op.
  have t1 := nl1 pl.
  have t2 := nl2 pl.
  setoid_rewrite <- cell_of_pl_op.
  full_generalize (cell_of_pl (as_tree l1) pl) as c1.
  full_generalize (cell_of_pl (as_tree l2) pl) as c2.
  unfold "⋅", cell_op. unfold cell_live in *. destruct c1, c2.
  rewrite t1. rewrite t2.
  apply unit_dot.
Qed.

Lemma no_live_op state1 state2
  (nl1: state_no_live state1)
  (nl2: state_no_live state2)
  : (state_no_live (state1 ⋅ state2)).
Proof.
  unfold state_no_live in *. destruct state1, state2. unfold "⋅", state_op.
  destruct_ands. split.
  - rewrite H. rewrite H1.
      apply multiset_add_empty.
  - apply lmap_no_live_op; trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow back *)

Lemma pl_in_pls_of_loc_extloc p i alpha ri (gamma: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma)
  : (p++[i], nat_of_extstep alpha ri) ∈ pls_of_loc (ExtLoc alpha ri gamma).
Admitted.

Lemma pl_in_pls_of_loc_cross_left p i (gamma1 gamma2: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma1)
  : (p++[i], nat_of_leftstep RI gamma2) ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Admitted.

Lemma pl_in_pls_of_loc_cross_right p i (gamma1 gamma2: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma2)
  : (p++[i], nat_of_rightstep RI gamma1) ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Admitted.

Lemma branch_view_includes_child (t: Branch M) p h i active : ∀ j y,
  (j ≤ i) ->
  (branch_view (refinement_of_nat M RI) (branch_of_pl t (p++[h], j)) active j y) ->
  ∃ (q w: M) , dot (rel M M (refinement_of_nat M RI i) w) q = y
      /\ rel_defined M M (refinement_of_nat M RI i) w
      /\ (node_view (refinement_of_nat M RI) (node_of_pl t (p++[h], i)) active w).
Proof.
  induction j as [j IHj] using (induction_ltof1 _ (λ k , i - k)); unfold ltof in IHj.
  intros. rename H into j_le_i. rename H0 into bv.
  destruct j_le_i.
  - setoid_rewrite branchcons_pl in bv.
      rewrite branch_view_rewrite in bv.
      unfold project_fancy in bv.
      unfold rel_project_fancy in bv.
      unfold conjoin_umbrella in bv.
      deex. destruct_ands. deex. destruct_ands.
      unfold tpcm_le in H. deex.
      exists (dot c y0). exists b.
      repeat split; trivial.
      + subst y. subst x. rewrite tpcm_assoc. trivial.
  -
    assert (S m - (S j) < S m - j) as la by lia.
    assert (S j ≤ S m) as la2 by lia.
    
    setoid_rewrite branchcons_pl in bv. rewrite branch_view_rewrite in bv.
    unfold conjoin_umbrella in bv. deex. destruct_ands.
    rename H0 into bvsub.
    
    have IHji := IHj (S j) la y0 la2 bvsub.
    deex. destruct_ands.
    subst y. subst y0.
    exists (dot x q). exists w. repeat split; trivial.
    + rewrite tpcm_assoc. rewrite tpcm_assoc. f_equal. apply tpcm_comm.
Qed.

Lemma node_view_includes_child (t: Branch M) p h i y active
  (nv : node_view (refinement_of_nat M RI) (node_of_pl t (p, h)) active y)
  : ∃ (q w: M) , dot (rel M M (refinement_of_nat M RI i) w) q = y
      /\ rel_defined M M (refinement_of_nat M RI i) w
      /\ (node_view (refinement_of_nat M RI) (node_of_pl t (p++[h], i)) active w).
Proof.
  setoid_rewrite cellnode_pl in nv. rewrite node_view_rewrite in nv.
  assert (0 ≤ i) as la by lia.
  unfold conjoin_umbrella in nv.
  deex. destruct_ands.
  rename H0 into bvsub.
  have Ib := branch_view_includes_child t p h i active 0 y0 la bvsub.
  deex. destruct_ands.
  subst y0. subst y.
  exists (dot x q). exists w. repeat split; trivial.
  rewrite tpcm_assoc. rewrite tpcm_assoc. f_equal. apply tpcm_comm.
Qed.

Lemma ri_of_nat_nat_of_extstep alpha (ri: RI)
  : (ri_of_nat RI (nat_of_extstep alpha ri) = ri). Admitted.
  
Lemma ri_of_nat_nat_of_leftstep (gamma2 : Loc RI)
  : (ri_of_nat RI (nat_of_leftstep RI gamma2)) = left_ri RI. Admitted.
  
Lemma ri_of_nat_nat_of_rightstep (gamma1 : Loc RI)
  : (ri_of_nat RI (nat_of_rightstep RI gamma1)) = right_ri RI. Admitted.
  
Lemma tpcm_le_a_le_bc_of_a_le_b m r q
  : tpcm_le m r -> tpcm_le m (dot r q).
Proof.
  intros. unfold tpcm_le in *. deex. subst. exists (dot c q). apply tpcm_assoc.
Qed.

Lemma borrow_back alpha ri gamma f m kappa state
  (bbcond: ∀ p: M, rel_defined M M (refinement_of ri) (dot f p) ->
      tpcm_le m (rel M M (refinement_of ri) (dot f p)))
  (ib: is_borrow kappa (ExtLoc alpha ri gamma) f state)
  : is_borrow kappa gamma m state.
Proof.
  unfold is_borrow in *. destruct state.
  unfold lmap_is_borrow in *. intros.
  rename H0 into mval. rename H1 into nv.
  destruct pl.
  rename l1 into p. rename n into i.
  assert ((p ++ [i], nat_of_extstep alpha ri) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    as p_ext_in
    by (apply pl_in_pls_of_loc_extloc; trivial).
  
  have nvic := node_view_includes_child (as_tree l0) p i (nat_of_extstep alpha ri) y
      kappa nv.
  have nvic1 := nvic EqDecision1 Countable0. clear nvic.
  deex.
  destruct_ands. subst.
  
  assert (m_valid w) as wval.
    - eapply rel_valid_left with (M := M). apply H1.
    
    - have ibi := ib (p ++ [i], nat_of_extstep alpha ri) p_ext_in w wval H2.
      unfold tpcm_le in ibi. deex. subst.
      unfold refinement_of_nat in H1.
      rewrite ri_of_nat_nat_of_extstep in H1.
      have bbcond1 := bbcond c H1.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_extstep.
      apply tpcm_le_a_le_bc_of_a_le_b. trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow back (products) *)

Lemma borrow_back_left gamma1 gamma2 m1 m2 kappa state
  (ib: is_borrow kappa (CrossLoc gamma1 gamma2) (pair_up RI m1 m2) state)
  : is_borrow kappa gamma1 m1 state.
Proof.
    unfold is_borrow in *. destruct state.
  unfold lmap_is_borrow in *. intros.
  rename H0 into mval. rename H1 into nv.
  destruct pl.
  rename l1 into p. rename n into i.
  assert ((p ++ [i], nat_of_leftstep RI gamma2) ∈ pls_of_loc (CrossLoc gamma1 gamma2))
    as p_ext_in
    by (apply pl_in_pls_of_loc_cross_left; trivial).
  
  have nvic := node_view_includes_child (as_tree l0) p i (nat_of_leftstep RI gamma2) y
      kappa nv.
  deex.
  destruct_ands. subst.
  
  assert (m_valid w) as wval.
    - eapply rel_valid_left with (M := M). apply H1.
    
    - have ibi := ib (p ++ [i], nat_of_leftstep RI gamma2) p_ext_in w wval H2.
      unfold tpcm_le in ibi. deex. subst.
      unfold refinement_of_nat in H1.
      rewrite ri_of_nat_nat_of_leftstep in H1.
      have lo := leftproject_le_left _ _ _ H1.
      have lo2 := lo EqDecision1 Countable0.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_leftstep.
      apply tpcm_le_a_le_bc_of_a_le_b. trivial.
Qed.

Lemma borrow_back_right gamma1 gamma2 m1 m2 kappa state
  (ib: is_borrow kappa (CrossLoc gamma1 gamma2) (pair_up RI m1 m2) state)
  : is_borrow kappa gamma2 m2 state.
Proof.
    unfold is_borrow in *. destruct state.
  unfold lmap_is_borrow in *. intros.
  rename H0 into mval. rename H1 into nv.
  destruct pl.
  rename l1 into p. rename n into i.
  assert ((p ++ [i], nat_of_rightstep RI gamma1) ∈ pls_of_loc (CrossLoc gamma1 gamma2))
    as p_ext_in
    by (apply pl_in_pls_of_loc_cross_right; trivial).
  
  have nvic := node_view_includes_child (as_tree l0) p i (nat_of_rightstep RI gamma1) y
      kappa nv.
  deex.
  destruct_ands. subst.
  
  assert (m_valid w) as wval.
    - eapply rel_valid_left with (M := M). apply H1.
    
    - have ibi := ib (p ++ [i], nat_of_rightstep RI gamma1) p_ext_in w wval H2.
      unfold tpcm_le in ibi. deex. subst.
      unfold refinement_of_nat in H1.
      rewrite ri_of_nat_nat_of_rightstep in H1.
      have lo := rightproject_le_right _ _ _ H1.
      have lo2 := lo EqDecision1 Countable0.
      unfold refinement_of_nat.
      rewrite ri_of_nat_nat_of_rightstep.
      apply tpcm_le_a_le_bc_of_a_le_b. trivial.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* borrow expire *)


  (*si : state_inv (active kappa ⋅ q)
                q contains (reserved kappa m)
  ∃ p1 : State M RI, state_inv (live_stuff_from_q ⋅ q)
                live gamma m <= live_stuff_from_q*)
                
Definition reserved_get_or_unit_relive (reserved: Lifetime * M) (old: Lifetime) (new: Lifetime) : M :=
  match reserved with
  | (my_lt, m) => if decide (multiset_le my_lt old /\ ¬ multiset_le my_lt new) then m else unit
  end.

Definition sum_reserved_over_lifetime_relive (reserved: listset (Lifetime * M)) (old: Lifetime) (new: Lifetime) :=
  set_fold (λ reserved m , dot m (reserved_get_or_unit_relive reserved old new)) unit reserved.
  
Global Instance sum_reserved_over_lifetime_proper :
  Proper ((≡) ==> (=) ==> (=) ==> (=)) (sum_reserved_over_lifetime_relive). Admitted.
                
Definition relive_cell (cell: Cell M) (old: Lifetime) (new: Lifetime) : Cell M :=
  match cell with
  | CellCon m res =>
      CellCon (sum_reserved_over_lifetime_relive res old new) ∅
  end.
  
Definition relive_cell_exc (cell: Cell M) (old: Lifetime) (new: Lifetime) (exc: Lifetime * M)
      : Cell M :=
  match cell with
  | CellCon m res =>
      CellCon (sum_reserved_over_lifetime_relive (res ∖ {[ exc ]}) old new) ∅
  end.

Global Instance relive_cell_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) relive_cell. Admitted.
  
Definition lmap_relive (lm: lmap M RI) (old: Lifetime) (new: Lifetime) : lmap M RI. Admitted.

Definition lmap_relive_exc (lm: lmap M RI) (old: Lifetime) (new: Lifetime) (loc: Loc RI) (exc: Lifetime * M) : lmap M RI. Admitted.
                
Definition relive (state: State M RI) (unactive: Lifetime) : State M RI :=
  match state with
  | StateCon active l =>
      StateCon empty_multiset
        (lmap_relive l (multiset_add active unactive) active)
  end.
   
Definition relive_exc (state: State M RI) (unactive: Lifetime) (loc: Loc RI) (exc: Lifetime * M) : State M RI :=
  match state with
  | StateCon active l =>
      StateCon empty_multiset
        (lmap_relive_exc l (multiset_add active unactive) active loc exc)
  end.

  
Lemma cell_of_pl_as_tree_lmap_relive l old new pl
    : cell_of_pl (as_tree (lmap_relive l old new)) pl
    ≡ relive_cell (cell_of_pl (as_tree l) pl) old new.
    Admitted.
    
Lemma cell_of_pl_as_tree_lmap_relive_exc_self l old new pl loc exc
    : pl ∈ pls_of_loc loc ->
      cell_of_pl (as_tree (lmap_relive_exc l old new loc exc)) pl
        ≡ relive_cell_exc (cell_of_pl (as_tree l) pl) old new exc.
    Admitted.
     
Lemma cell_of_pl_as_tree_lmap_relive_exc_other l old new pl loc exc
    : pl ∉ pls_of_loc loc ->
      cell_of_pl (as_tree (lmap_relive_exc l old new loc exc)) pl
        ≡ relive_cell (cell_of_pl (as_tree l) pl) old new.
    Admitted.

Lemma multiset_no_dupes_of_multiset_no_dupes_add (a b: multiset nat)
  (mnd : multiset_no_dupes (multiset_add a b))
  : multiset_no_dupes b. Admitted.

Lemma backslash_union (a l1 : (listset (Lifetime * M)))
  : a ∪ l1 ≡ (l1 ∖ a) ∪ a.
Proof. unfold "≡", set_equiv_instance. intro.
    rewrite elem_of_union. rewrite elem_of_union.
    rewrite elem_of_difference.
    assert (Decision (x ∈ a)) by solve_decision. destruct H; intuition.
Qed.

Lemma live_in_relive m kappa gamma p
    (kappa_not_in_p : match p with StateCon p_active _ => ¬ multiset_le kappa p_active end)
  : exists r , live gamma m ⋅ r ≡ relive (reserved kappa gamma m ⋅ p) kappa.
Proof.
  exists (relive_exc p kappa gamma (kappa, m)).
  unfold live, relive, "≡", "⋅", state_op, reserved, state_equiv. destruct p.
    rename l into plifetime.
  split.
  - rewrite multiset_add_empty. trivial.
  - apply lmaps_equiv_of_tree_equiv.
    setoid_rewrite as_tree_op.
    setoid_rewrite as_tree_singleton.
    apply equiv_extensionality_cells.
    intros.
    setoid_rewrite <- cell_of_pl_op.
    setoid_rewrite cell_of_pl_as_tree_lmap_relive.
    rewrite multiset_add_empty_left.
    setoid_rewrite as_tree_op.
    setoid_rewrite as_tree_singleton.
    setoid_rewrite <- cell_of_pl_op.
    unfold relive_cell.
    assert (Decision (pl ∈ pls_of_loc gamma)) as plin by solve_decision.
    destruct plin.
    + setoid_rewrite build_spec; trivial.
      setoid_rewrite cell_of_pl_as_tree_lmap_relive_exc_self; trivial.
      unfold "⋅", "≡", cell_op, cell_equiv, relive_cell_exc.
      full_generalize (cell_of_pl (as_tree l0) pl) as pcell. destruct pcell.
      split.
       * assert (({[(kappa, m)]} ∪ l) ≡
            ( (l ∖ {[(kappa, m)]}) ∪ {[(kappa,m)]} )) as bdeq by (apply backslash_union).
         setoid_rewrite bdeq.
         unfold sum_reserved_over_lifetime_relive.
         rewrite set_fold_add_1_element; trivial.
         ** rewrite tpcm_comm. f_equal.
            unfold reserved_get_or_unit_relive. case_decide; trivial.
            assert (multiset_le kappa (multiset_add plifetime kappa)) by
                (apply multiset_le_add_right).
            intuition.
         ** set_solver.
         ** intros. apply dot_comm_right2.
       * set_solver.
   + setoid_rewrite build_rest_triv; trivial.
     setoid_rewrite cell_of_pl_as_tree_lmap_relive_exc_other; trivial.
      unfold "⋅", "≡", cell_op, cell_equiv, relive_cell.
      unfold triv_cell.
      full_generalize (cell_of_pl (as_tree l0) pl) as pcell. destruct pcell.
      split.
      * rewrite unit_dot_left.
        setoid_replace (∅ ∪ l) with (l) by set_solver. trivial.
      * set_solver.
Qed.
    
Lemma empty_op_lmap (l : lmap M RI) : as_tree (∅ ⋅ l) ≡ as_tree l. Admitted.

Lemma dot_xyz_impl (x y z c d : M)
  : x = dot y z -> dot (dot c d) x = dot (dot c y) (dot d z). Admitted.

Definition relive_preserves_inv kappa q
  (si : state_inv (active kappa ⋅ q))
      : state_inv (relive q kappa ⋅ q).
Proof.
  unfold state_inv, "⋅", state_op, relive, active in *. destruct q.
  destruct_ands. split.
  - rewrite multiset_add_empty_left.
    apply multiset_no_dupes_of_multiset_no_dupes_add with (a := kappa). trivial.
  - eapply valid_totals_of_preserved_cell_totals
      with (b1 := (as_tree (∅ ⋅ l0))) (lt1 := multiset_add kappa l); trivial.
    intros.
    setoid_rewrite empty_op_lmap.
    setoid_rewrite as_tree_op.
    setoid_rewrite <- cell_of_pl_op.
    setoid_rewrite cell_of_pl_as_tree_lmap_relive.
    full_generalize (cell_of_pl (as_tree l0) pl) as c.
    destruct c. unfold "⋅", cell_op, cell_total, relive_cell.
    replace
      (dot (sum_reserved_over_lifetime_relive l1 (multiset_add l kappa) l) m) with
      (dot m (sum_reserved_over_lifetime_relive l1 (multiset_add l kappa) l))
      by (apply tpcm_comm).
    rewrite <- tpcm_assoc. f_equal.
    setoid_replace (∅ ∪ l1) with l1 by set_solver.
    unfold sum_reserved_over_lifetime.
    unfold sum_reserved_over_lifetime_relive.
    apply set_relate3 with (R := λ a b c , a = dot b c).
    + rewrite unit_dot. trivial.
    + intros. subst b. apply dot_xyz_impl.
      unfold reserved_get_or_unit. unfold reserved_get_or_unit_relive. destruct a.
      rewrite multiset_add_empty_left.
      replace (multiset_add kappa l) with (multiset_add l kappa) by (apply multiset_add_comm).
      repeat case_decide; intuition.
      * rewrite unit_dot. trivial.
      * rewrite unit_dot_left. trivial.
      * exfalso. apply H1. apply multiset_le_transitive with (y := l); trivial.
          apply multiset_le_add.
      * rewrite unit_dot. trivial.
Qed.

Lemma abcde_state (a b c d e : State M RI)
  : a ⋅ b ⋅ (c ⋅ (d ⋅ e)) ≡ a ⋅ d ⋅ (b ⋅ c ⋅ e).
Proof. solve_assoc_comm. Qed.

Lemma not_le_of_nonempty (lt a b: multiset nat)
  (lt_nonempty : lt ≠ empty_multiset)
  (mnd : multiset_no_dupes (multiset_add lt (multiset_add a b)))
       : ¬ multiset_le lt b.
Admitted.
  
Lemma not_le_kappa_p kappa a b
    (kappa_nonempty : kappa ≠ empty_lifetime)
    (si: state_inv (active kappa ⋅ (a ⋅ b)))
  : (match b with | StateCon p_active _ => ¬ multiset_le kappa p_active end).
Proof.
  unfold state_inv, active in si.  destruct a, b. unfold "⋅", state_op in si.
  destruct_ands.
  apply not_le_of_nonempty with (a := l); trivial.
Qed.
  
Lemma borrow_expire (m: M) gamma kappa p
  (kappa_nonempty : kappa ≠ empty_lifetime)
  (si: state_valid (active kappa ⋅ reserved kappa gamma m ⋅ p))
     : state_valid (live gamma m ⋅ p).
Proof.
  unfold state_valid in *. deex.
  setoid_rewrite <- state_assoc in si.
  setoid_rewrite <- state_assoc in si.
  
  have ti := relive_preserves_inv _ _ si.
  
  have lir' := live_in_relive m kappa gamma (p ⋅ p0).
  have lir := lir' state_op
    (not_le_kappa_p kappa (reserved kappa gamma m) (p ⋅ p0) kappa_nonempty si).
  clear lir'.
  
  deex.
  exists (r ⋅ reserved kappa gamma m ⋅ p0).
  
  setoid_rewrite <- lir in ti.
  setoid_rewrite abcde_state in ti.
  trivial.
Qed.

End ResourceProofs.
