Require Import rollup.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import CpdtTactics.
From stdpp Require Import gmap.

Context `{Countable RefinementIndex}.

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

(* live(gamma, m) dot live(gamma, n) equiv live(gamma, m dot n) *)

Lemma induct3
    (R_cell : Cell -> Cell -> Cell -> Prop)
    (R_node : Node -> Node -> Node -> Prop)
    (R_branch : Branch -> Branch -> Branch -> Prop)
    (Rtriv : R_cell triv_cell triv_cell triv_cell)
    (induct_node : ∀ cell1 cell2 cell3 branch1 branch2 branch3 ,
        R_cell cell1 cell2 cell3 -> R_branch branch1 branch2 branch3 ->
            R_node (CellNode cell1 branch1) (CellNode cell2 branch2) (CellNode cell3 branch3))

Lemma make_parent_from_branch_node_op (idx: nat) (branch1 branch2: Branch)
  : node_equiv
      (node_op (make_parent_from_branch idx branch1) (make_parent_from_branch idx branch2))
      (make_parent_from_branch idx (branch_op branch1 branch2)).
Proof.
  generalize branch2. clear branch2. induction branch1.
    + unfold node_op. unfold node_equiv. unfold make_parent_from_branch.
        fold node_op. fold node_equiv. fold make_parent_from_branch.
    + crush.

Lemma make_parent_from_node_node_op (idx: nat) (node1 node2: Node)
  : node_equiv
      (node_op (make_parent_from_node idx node1) (make_parent_from_node idx node2))
      (make_parent_from_node idx (node_op node1 node2)).

Lemma build_tree_from_node_node_op (loc: Loc) (node1 node2: Node)
  : node_equiv
      (node_op (build_tree_from_node loc node1) (build_tree_from_node loc node2))
      (build_tree_from_node loc (node_op node1 node2))

Lemma build_tree_cell_op (loc: Loc) (cell1 cell2: Cell)
  : node_equiv
      (node_op (build_tree loc cell1) (build_tree loc cell2))
      (build_tree loc (cell_op cell1 cell2)).
