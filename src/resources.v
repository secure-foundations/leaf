Require Import rollup.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import CpdtTactics.
From stdpp Require Import gmap.

Context `{Countable RefinementIndex}.
Context `{EqDecision RefinementIndex}.

Inductive Loc :=
  | BaseLoc : nat -> Loc
  | ExtLoc : nat -> RefinementIndex -> Loc -> Loc
  | CrossLoc : Loc -> Loc -> Loc
.

Global Instance loc_eqdec : EqDecision Loc.
Proof. solve_decision. Defined.

Global Instance loc_countable : Countable Loc.
Proof.
  set (enc :=
    fix go l :=
      match l with
      | BaseLoc i => GenLeaf (inl i)
      | ExtLoc i ri linner => GenNode 0 [GenLeaf (inr (i, ri)); go linner]
      | CrossLoc l1 l2 => GenNode 1 [go l1; go l2]
      end
  ).
  set (dec :=
    fix go e :=
      match e with
      | GenLeaf (inl i) => BaseLoc i
      | GenNode 0 [GenLeaf (inr (i, ri)); einner] => ExtLoc i ri (go einner)
      | GenNode 1 [e1; e2] => CrossLoc (go e1) (go e2)
      | _ => BaseLoc 0 (* dummy *)
      end
  ).
  refine (inj_countable' enc dec _).
  refine (fix go (e : Loc) {struct e} := _).
  - destruct e as [| | ]; simpl; f_equal; trivial.
Qed.

Lemma pigeon (bound : nat) : ∀ (f : nat -> nat) 
  (inject: ∀ x y , x <= bound -> y <= bound -> f x = f y -> x = y)
  (into_hole : ∀ x , x <= bound -> f x < bound)
  , False.
Proof.
induction bound.
  - intros. have h := into_hole 0. lia.
  - intros.
    apply (IHbound (λ x , if decide (f x < f (S bound)) then f x else f x - 1)).
    * intro. intro.  case_decide; case_decide.
      + intros. apply inject; trivial. ** lia. ** lia.
      + intro. intro. intro.
          have j : f y = f (S bound) by lia.
          have l : y = S bound by apply inject; lia.
          lia.
      + intro. intro. intro.
          have j : f x = f (S bound) by lia.
          have l : x = S bound by apply inject; lia.
          lia.
      + intros.
          have t0 : f x <> f (S bound).
              ** intro.
                 have r : x = S bound by apply inject; lia. lia.
          ** have t1 : f y <> f (S bound).
              *** intro.
              have r : y = S bound by apply inject; lia. lia.
          *** have t2 : f x = f y by lia.
          apply inject; lia.
    * intros. case_decide.
      + have j : f (S bound) < S bound by apply into_hole.
        lia.
      + have j : f x < S bound.
        ** apply into_hole. lia.
        ** have t0 : f x <> f (S bound).
            *** intro.
            have r : x = S bound by apply inject; lia. lia.
            *** lia.
Qed.

Lemma value_above_bound_helper (f : nat -> nat) (bound : nat) (i: nat)
  (inject: ∀ x y , f x = f y -> x = y)
  : (∃ t , f t > bound) \/ (∀ j , j < i -> f j <= bound).
Proof.
induction i.
 - right. intros. lia.
 - destruct IHi.
  * left; trivial.
  * have q : (f i) <= bound \/ (f i) > bound. ** lia.
    ** destruct q.
    + right. intros. have r := H0 j.
      have u := decide (j = i). destruct u.
        *** solve_decision.
        *** rewrite <- e in H1. lia.
        *** lia.
    + left. exists i. trivial.
Qed.

Lemma value_above_bound (f : nat -> nat) (bound : nat)
  (inject: ∀ x y , f x = f y -> x = y)
  : (∃ t , f t > bound).
Proof.
  have h := value_above_bound_helper f bound (bound + 2) inject.
  destruct h.
  - trivial.
  - have k : False.
    ** apply (pigeon (bound + 1) f).
    + intros. apply inject. trivial.
    + intros. have r := H0 x. lia.
    ** contradiction.
Qed.

Context `{TPCM M}.

Definition idx_of_loc (loc: Loc) : nat := encode_nat loc.

Definition triv_cell : Cell := CellCon unit (λ x, false) empty.
Definition triv_node : Node := CellNode triv_cell BranchNil.

Fixpoint make_parent_from_branch (idx: nat) (branch: Branch) : Node :=
  match idx with
  | 0 => CellNode triv_cell branch
  | S i => make_parent_from_branch i (BranchCons triv_node branch)
  end
.

Definition make_parent_from_node (idx: nat) (node: Node) :=
  make_parent_from_branch idx (BranchCons node BranchNil).

Fixpoint build_tree_from_node (loc: Loc) (node: Node) :=
  match loc with
  | BaseLoc _ => make_parent_from_node (idx_of_loc loc) node
  | ExtLoc _ _ baseloc =>
      build_tree_from_node baseloc (make_parent_from_node (idx_of_loc loc) node)
  | CrossLoc l1 l2 =>
      node_op
        (build_tree_from_node l1 (make_parent_from_node (idx_of_loc loc) node))
        (build_tree_from_node l2 (make_parent_from_node (idx_of_loc loc) node))
  end.

Definition build_tree (loc: Loc) (cell: Cell) :=
  build_tree_from_node loc (CellNode cell BranchNil).

Definition live_tree (loc: Loc) (m: M) :=
  build_tree loc (CellCon m (λ x, false) empty).

Definition borrow_unit_func (bo: @BorrowObject M) : (BorrowObject -> bool) :=
  λ t , if decide (t = bo) then true else false.
  
Definition borrow_tree (lt: Lifetime) (loc: Loc) (m: M) :=
  build_tree loc (CellCon unit (borrow_unit_func (BorrowO lt m)) empty).
  
Definition reserved_tree (lt_unit: nat) (loc: Loc) (m: M) :=
  build_tree loc (CellCon unit (λ x, false) {[ lt_unit := Some m ]}).

Definition live (loc: Loc) (m:M) := StateCon empty (live_tree loc m).
Definition borrow (lt: Lifetime) (loc: Loc) (m:M) := StateCon empty (borrow_tree lt loc m).
Definition reserved (lt_unit: nat) (loc: Loc) (m:M) := StateCon empty (reserved_tree lt_unit loc m).
Definition active (lt: Lifetime) := StateCon lt triv_node.

Section Induct1.
  Variable R_cell : @Cell M -> Prop.
  Variable R_node : @Node M -> Prop.
  Variable R_branch : @Branch M -> Prop.
  Variable Rtriv : R_cell triv_cell.
  Variable induct_node : ∀ cell1 branch1 ,
        R_cell cell1 -> R_branch branch1 -> R_node (CellNode cell1 branch1).
  Variable Rbranch_triv : R_branch BranchNil.
  Variable Rinduct_branch : ∀ node1 branch1 ,
        R_node node1 -> R_branch branch1
          -> R_branch (BranchCons node1 branch1).
  Variable Rnode_add : ∀ n1 m1 ,
        R_node n1 -> R_node m1 ->
            R_node (node_op n1 m1).
  
  Lemma Induct1_make_parent_from_branch : ∀ idx b1 ,
        R_branch b1 ->
        R_node (make_parent_from_branch idx b1).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rtriv induct_node.
  induction idx. * crush. * crush. apply IHidx. apply Rinduct_branch.
      - unfold triv_node. apply induct_node. + apply Rtriv. + apply Rbranch_triv.
      - trivial. Qed.
      
  Lemma Induct1_make_parent_from_node : ∀ idx n1 ,
        R_node n1 ->
        R_node (make_parent_from_node idx n1).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rtriv induct_node.
  intros. unfold make_parent_from_node.
      apply Induct1_make_parent_from_branch.
      apply Rinduct_branch; trivial. Qed.
      
  Lemma Induct1_build_tree_from_node : ∀ loc n1 ,
      R_node n1 ->
      R_node (build_tree_from_node loc n1).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rnode_add Rtriv induct_node.
  induction loc.
    - intros. unfold build_tree_from_node. apply Induct1_make_parent_from_node.
      trivial.
    - intros. unfold build_tree_from_node. apply IHloc.
        apply Induct1_make_parent_from_node. trivial.
    - intros. unfold build_tree_from_node. apply Rnode_add.
      * apply IHloc1. apply Induct1_make_parent_from_node. trivial.
      * apply IHloc2. apply Induct1_make_parent_from_node. trivial.
  Qed.
            
  Lemma Induct1_build_tree :
     ∀ loc c1 (R_start : R_cell c1) ,
        R_node (build_tree loc c1).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rnode_add Rtriv induct_node.
    unfold build_tree. intros. apply Induct1_build_tree_from_node.
        apply induct_node; trivial.
  Qed.
End Induct1.

Section Induct1Disj.
  Variable R_cell : @Cell M -> nat -> Prop.
  Variable R_node : @Node M -> nat -> Prop.
  Variable R_branch : @Branch M -> nat -> Prop.
  Variable induct_node_cell : ∀ cell1 branch1 idx ,
        R_cell cell1 idx -> R_node (CellNode cell1 branch1) idx.
  Variable induct_node_branch : ∀ cell1 branch1 idx ,
        R_branch branch1 0 -> R_node (CellNode cell1 branch1) idx.
  Variable Rinduct_branch_node : ∀ node1 branch1 idx ,
        R_node node1 idx
          -> R_branch (BranchCons node1 branch1) idx.
  Variable Rinduct_branch_branch : ∀ node1 branch1 idx ,
        R_branch branch1 (S idx)
          -> R_branch (BranchCons node1 branch1) idx.
  Variable Rnode_add : ∀ n1 m1 idx ,
        R_node n1 idx -> R_node (node_op n1 m1) idx.
  
  Lemma Induct1Disj_make_parent_from_branch : ∀ idx idx0 b1 ,
        R_branch b1 idx ->
        R_node (make_parent_from_branch idx b1) idx0.
  Proof using R_branch R_node Rinduct_branch_branch induct_node_branch.
  induction idx.
    - intros. apply induct_node_branch; trivial.
    - intros. unfold make_parent_from_branch. apply IHidx. apply Rinduct_branch_branch. trivial.
  Qed.
      
  Lemma Induct1Disj_make_parent_from_node : ∀ idx idx0 n1 ,
        R_node n1 idx ->
        R_node (make_parent_from_node idx n1) idx0.
  Proof using R_branch R_node Rinduct_branch_branch Rinduct_branch_node induct_node_branch.
  intros. unfold make_parent_from_node.
      apply Induct1Disj_make_parent_from_branch.
      apply Rinduct_branch_node; trivial. Qed.
      
  Lemma Induct1Disj_build_tree_from_node : ∀ loc n1 idx0 ,
      R_node n1 (idx_of_loc loc) ->
      R_node (build_tree_from_node loc n1) idx0.
  Proof using R_branch R_node Rinduct_branch_branch Rinduct_branch_node Rnode_add
induct_node_branch.
  induction loc.
    - intros. unfold build_tree_from_node. apply Induct1Disj_make_parent_from_node.
      trivial.
    - intros. unfold build_tree_from_node. apply IHloc.
        apply Induct1Disj_make_parent_from_node. trivial.
    - intros. unfold build_tree_from_node. apply Rnode_add.
      * apply IHloc1. apply Induct1Disj_make_parent_from_node. trivial.
  Qed.

  Lemma Induct1Disj_build_tree :
     ∀ loc c1 idx (R_start : R_cell c1 (idx_of_loc loc)) ,
        R_node (build_tree loc c1) idx.
  Proof using R_branch R_cell R_node Rinduct_branch_branch Rinduct_branch_node Rnode_add induct_node_branch induct_node_cell.
    unfold build_tree. intros. apply Induct1Disj_build_tree_from_node.
        apply induct_node_cell; trivial.
  Qed.
End Induct1Disj.


(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, m) dot live(gamma, n) equiv live(gamma, m dot n) *)

Section Induct3.
  Variable R_cell : @Cell M -> @Cell M -> @Cell M -> Prop.
  Variable R_node : @Node M -> @Node M -> @Node M -> Prop.
  Variable R_branch : @Branch M -> @Branch M -> @Branch M -> Prop.
  Variable Rtriv : R_cell triv_cell triv_cell triv_cell.
  Variable induct_node : ∀ cell1 cell2 cell3 branch1 branch2 branch3 ,
        R_cell cell1 cell2 cell3 -> R_branch branch1 branch2 branch3 ->
            R_node (CellNode cell1 branch1) (CellNode cell2 branch2) (CellNode cell3 branch3).
  Variable Rbranch_triv : R_branch BranchNil BranchNil BranchNil.
  Variable Rinduct_branch : ∀ node1 node2 node3 branch1 branch2 branch3 ,
        R_node node1 node2 node3 -> R_branch branch1 branch2 branch3 
          -> R_branch (BranchCons node1 branch1)
            (BranchCons node2 branch2) (BranchCons node3 branch3).
  Variable Rnode_add : ∀ n1 n2 n3 m1 m2 m3 ,
        R_node n1 n2 n3 -> R_node m1 m2 m3 ->
            R_node (node_op n1 m1) (node_op n2 m2) (node_op n3 m3).
  
  Lemma Induct3_make_parent_from_branch : ∀ idx b1 b2 b3 ,
        R_branch b1 b2 b3 -> 
        R_node (make_parent_from_branch idx b1)
               (make_parent_from_branch idx b2)
               (make_parent_from_branch idx b3).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rtriv induct_node.
  induction idx. * crush. * crush. apply IHidx. apply Rinduct_branch.
      - unfold triv_node. apply induct_node. + apply Rtriv. + apply Rbranch_triv.
      - trivial. Qed.
      
  Lemma Induct3_make_parent_from_node : ∀ idx n1 n2 n3 ,
        R_node n1 n2 n3 -> 
        R_node (make_parent_from_node idx n1)
               (make_parent_from_node idx n2)
               (make_parent_from_node idx n3).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rtriv induct_node.
  intros. unfold make_parent_from_node.
      apply Induct3_make_parent_from_branch.
      apply Rinduct_branch; trivial. Qed.
      
  Lemma Induct3_build_tree_from_node : ∀ loc n1 n2 n3 ,
      R_node n1 n2 n3 ->
      R_node (build_tree_from_node loc n1)
             (build_tree_from_node loc n2)
             (build_tree_from_node loc n3).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rnode_add Rtriv induct_node.
  induction loc.
    - intros. unfold build_tree_from_node. apply Induct3_make_parent_from_node.
      trivial.
    - intros. unfold build_tree_from_node. apply IHloc.
        apply Induct3_make_parent_from_node. trivial.
    - intros. unfold build_tree_from_node. apply Rnode_add.
      * apply IHloc1. apply Induct3_make_parent_from_node. trivial.
      * apply IHloc2. apply Induct3_make_parent_from_node. trivial.
  Qed.
            
  Lemma Induct3_build_tree :
     ∀ loc c1 c2 c3 (R_start : R_cell c1 c2 c3) ,
        R_node (build_tree loc c1)
               (build_tree loc c2)
               (build_tree loc c3).
  Proof using R_branch R_cell R_node Rbranch_triv Rinduct_branch Rnode_add Rtriv induct_node.
    unfold build_tree. intros. apply Induct3_build_tree_from_node.
        apply induct_node; trivial.
  Qed.
End Induct3.

Print lookup_merge.
Lemma cell_triv_op_cell_triv : cell_equiv (cell_op triv_cell triv_cell) triv_cell.
Proof.
  - unfold triv_cell. unfold cell_equiv. crush. + apply unit_dot.
      + unfold equiv_func. unfold bool_or_func. crush.
      + rewrite equiv_rmerge_emptyset. trivial.
Qed.

Lemma node_op_equiv_left (nodeLeft1: Node) (nodeLeft2: Node) (nodeRight: Node)
    (node_eq: node_equiv nodeLeft1 nodeLeft2)
    : (node_equiv (node_op nodeLeft1 nodeRight) (node_op nodeLeft2 nodeRight)).
Proof.
  apply node_equiv_trans with (node2 := node_op nodeRight nodeLeft1).
  - apply node_op_comm.
  - apply node_equiv_trans with (node2 := node_op nodeRight nodeLeft2).
    + apply node_op_equiv. trivial.
    + apply node_op_comm.
Qed.

Lemma node_equiv_node_op_both (n1 n2 n3 n4 : Node)
      (eq1 : node_equiv n1 n3)
      (eq2 : node_equiv n2 n4)
    : node_equiv (node_op n1 n2) (node_op n3 n4).
Proof.
  apply node_equiv_trans with (node2 := node_op n3 n2).
      - apply node_op_equiv_left. trivial.
      - apply node_op_equiv. trivial.
Qed.

Print lookup_merge.
Lemma build_tree_cell_op (loc: Loc) (cell1 cell2 cell3: Cell)
    (equ : cell_equiv (cell_op cell1 cell2) cell3)
  : node_equiv
      (node_op (build_tree loc cell1) (build_tree loc cell2))
      (build_tree loc cell3).
Proof.
  apply Induct3_build_tree with
      (R_node := λ n1 n2 n3 , node_equiv (node_op n1 n2) n3)
      (R_branch := λ b1 b2 b3 , branch_equiv (branch_op b1 b2) b3)
      (R_cell := λ c1 c2 c3 , cell_equiv (cell_op c1 c2) c3).
  - apply cell_triv_op_cell_triv.
  - intros. unfold node_op. fold branch_op. unfold node_equiv. fold branch_equiv.
    split; trivial.
  - unfold branch_op. apply branch_equiv_refl.
  - intros. unfold branch_op. unfold branch_equiv. split; trivial.
  - intros.
      apply node_equiv_trans with (node2 :=
              (node_op (node_op n1 n2) (node_op m1 m2))).
      * apply node_equiv_trans with (node2 :=
              node_op n1 (node_op n2 (node_op m1 m2))).
      ** apply node_equiv_trans with (node2 :=
              node_op n1 (node_op m1 (node_op n2 m2))).
      *** apply node_equiv_symm. apply node_op_assoc.
      *** apply node_op_equiv.
            apply node_equiv_trans with (node2 := node_op (node_op m1 n2) m2).
            -- apply node_op_assoc.
            -- apply node_equiv_trans with (node2 := node_op (node_op n2 m1) m2).
            --- apply node_equiv_node_op_both.
            ---- apply node_op_comm.
            ---- apply node_equiv_refl.
            --- apply node_equiv_symm. apply node_op_assoc.
      ** apply node_op_assoc.
      * apply node_equiv_node_op_both; trivial.
  - trivial.
Qed.

Lemma live_dot_live (loc: Loc) (m n : M)
  : live loc (dot m n) ≡ live loc m ⋅ live loc n.
Proof.
  unfold live. unfold "≡". unfold state_equiv. unfold "⋅". unfold state_op.
  case_decide.
    * split.
      - apply set_eq. intro. rewrite elem_of_union. crush.
      - unfold live_tree. apply node_equiv_symm. apply build_tree_cell_op.
        unfold cell_equiv. unfold cell_op. repeat split.
        + rewrite equiv_rmerge_emptyset. trivial.
    * apply H1. apply set_eq. intro. unfold elem_of_intersection. crush.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, unit) = unit *)

Definition state_unit := StateCon empty triv_node.

Lemma cell_trivial_triv_cell : cell_trivial triv_cell.
Proof.
  unfold cell_trivial. unfold triv_cell. repeat split; trivial. Qed.
  
Lemma node_trivial_triv_node : node_trivial triv_node.
Proof.
  unfold node_trivial. unfold triv_node. repeat split; trivial. Qed.
  
Lemma node_trivial_node_op (n: Node) (m: Node)
    (nt1: node_trivial n) (nt2: node_trivial m) : node_trivial (node_op n m).
Proof. apply node_trivial_of_equiv with (node1 := triv_node).
  * apply node_equiv_trans with (node2 := node_op n triv_node).
  ** apply node_equiv_trans with (node2 := node_op triv_node triv_node).
    *** unfold triv_node. unfold node_equiv. unfold node_op. split.
      **** apply cell_equiv_symm. apply cell_triv_op_cell_triv.
      **** unfold branch_trivial. trivial.
    *** apply node_op_equiv_left. apply node_equiv_of_trivial.
      **** apply node_trivial_triv_node.
      **** trivial.
  ** apply node_op_equiv. apply node_equiv_of_trivial.
    **** apply node_trivial_triv_node.
    **** trivial.
  * apply node_trivial_triv_node.
Qed.

Lemma node_trivial_live_tree (loc: Loc)
  : node_trivial (live_tree loc unit).
Proof.
  apply Induct1_build_tree with
      (R_node := node_trivial)
      (R_branch := branch_trivial)
      (R_cell := cell_trivial).
  - apply cell_trivial_triv_cell.
  - intros. unfold node_trivial. split; trivial.
  - intros. unfold branch_trivial. trivial.
  - intros. unfold branch_trivial. split; trivial.
  - intros. unfold node_trivial. trivial. apply node_trivial_node_op; trivial.
  - intros. unfold cell_trivial. split; trivial. split; trivial.
Qed.

Lemma live_tree_unit (loc: Loc)
  : node_equiv (live_tree loc unit) triv_node.
Proof.
  apply node_equiv_of_trivial.
  - apply node_trivial_live_tree.
  - apply node_trivial_triv_node.
Qed.

Lemma live_unit (loc: Loc)
  : live loc unit ≡ state_unit.
Proof.
  unfold live. unfold state_unit. unfold equiv. unfold state_equiv. split; trivial.
  apply live_tree_unit.
Qed.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, m) is valid means m is valid *)

Variables refinement_of_index : RefinementIndex -> Refinement M M.
Global Instance state_valid : Valid State := alls_valid_instance refinement_of_index.

Lemma valid_of_live (loc: Loc) (m: M)
  : (✓ (live loc m)) -> m_valid m.
Proof.
  unfold "✓". unfold state_valid. unfold alls_valid_instance.
  intros. destruct H1.
  apply Induct1Disj_build_tree with
      (R_node := λ n i , node_all_total_in_refinement_domain n i -> m_valid m)
      (R_branch := λ b i , branch_all_total_in_refinement_domain b i -> m_valid m)
      (R_cell := λ c i , (match c with CellCon m0 _ _ => m_valid m0 end) -> m_valid m).
