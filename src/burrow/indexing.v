From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import cpdt.CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.gmap_utils.
Require Import Burrow.trees.
Require Import coq_tricks.Deex.

Definition PathLoc : Type := list nat * nat.
Definition plend (pl: PathLoc) := match pl with (_, l) => l end.

Section Indexing.

(*Context {M: Type}  `{!EqDecision M}.*)
(*Context `{!EqDecision RefinementIndex}.
Context {refinement_of_index : RefinementIndex -> Refinement M M}.*)

Context {M} `{!EqDecision M, !TPCM M}.

Global Instance CellNode_proper : Proper ((≡) ==> (≡) ==> (≡)) (CellNode).
Proof. unfold Proper, "==>". intros. unfold "≡", node_equiv. intuition. Qed.

Global Instance BranchCons_proper : Proper ((≡) ==> (≡) ==> (≡)) (BranchCons).
Proof. unfold Proper, "==>". intros. unfold "≡", branch_equiv. intuition. Qed.

Definition branch_of_branch (branch: Branch M) :=
  match branch with
  | BranchNil => BranchNil
  | BranchCons _ b => b
  end.
  
Definition node_of_branch (branch: Branch M) :=
  match branch with
  | BranchNil => triv_node
  | BranchCons n _ => n
  end.
  
Definition branch_of_node (node: Node M) :=
  match node with
  | CellNode _ b => b
  end.

Fixpoint walk (j: nat) (branch: Branch M) :=
  match j with
  | 0 => branch
  | S i => branch_of_branch (walk i branch)
  end.

Definition hop (j: nat) (branch: Branch M) := 
  branch_of_node (node_of_branch (walk j branch)).

Fixpoint hops (js: list nat) (branch: Branch M) :=
  match js with
  | [] => branch
  | (j :: ks) => (hops ks (hop j branch))
  end.
  
Definition branch_of_pl (branch: Branch M) (pl: PathLoc) : Branch M :=
  match pl with
  | (p, i) => walk i (hops p branch)
  end.
  
Definition node_of_pl (branch: Branch M) (pl: PathLoc) : Node M :=
  node_of_branch (branch_of_pl branch pl).
    
Definition cell_of_pl (branch: Branch M) (pl: PathLoc) : Cell M :=
  cell_of_node (node_of_pl branch pl).
    
Lemma node_trivial_triv_node : node_trivial triv_node.
Proof. unfold node_trivial, triv_node, cell_trivial, triv_cell. crush.
Qed.

Global Instance branch_of_branch_proper : Proper ((≡) ==> (≡)) branch_of_branch.
Proof. unfold Proper, "==>", branch_of_branch. intros. destruct x, y;
    unfold "≡", branch_equiv, branch_trivial in H; intuition.
Qed.

Global Instance node_of_branch_proper : Proper ((≡) ==> (≡)) node_of_branch.
Proof. unfold Proper, "==>", branch_of_branch. intros. destruct x, y;
    unfold "≡", branch_equiv, node_trivial, branch_trivial in H;
    unfold node_of_branch;
    intuition.
    - apply node_equiv_of_trivial; trivial. unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
    - apply node_equiv_of_trivial; trivial. unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
Qed.

Global Instance branch_of_node_proper : Proper ((≡) ==> (≡)) branch_of_node.
Proof. unfold Proper, "==>", branch_of_node. intros. destruct x, y.
unfold "≡", node_equiv in H. intuition.
Qed.

Global Instance cell_of_node_proper : Proper ((≡) ==> (≡)) cell_of_node.
Proof. unfold Proper, "==>". intros. destruct x, y. unfold cell_of_node.
  unfold "≡", node_equiv in H. intuition. Qed.

Global Instance walk_proper (j: nat) : Proper ((≡) ==> (≡)) (walk j).
Proof. unfold Proper, "==>". induction j.
 - intros. unfold walk. trivial.
 - intros. cbn [walk]. setoid_rewrite (IHj x y); trivial.
Qed.

Global Instance hop_proper (j: nat) : Proper ((≡) ==> (≡)) (hop j).
Proof. unfold Proper, "==>". intros. unfold hop. setoid_rewrite H. trivial.
Qed.

Global Instance hops_proper (js: list nat) : Proper ((≡) ==> (≡)) (hops js).
Proof. unfold Proper, "==>". induction js.
 - intros. trivial.
 - intros. cbn [hops]. setoid_rewrite (IHjs (hop a x) (hop a y)); trivial.
  setoid_rewrite H. trivial.
Qed.

Global Instance branch_of_pl_proper : Proper ((≡) ==> (=) ==> (≡)) branch_of_pl.
Proof. unfold Proper, "==>". intros. rewrite H0. unfold branch_of_pl. destruct y0.
    setoid_rewrite H. trivial. Qed.

Global Instance node_of_pl_proper : Proper ((≡) ==> (=) ==> (≡)) node_of_pl.
Proof. unfold Proper, "==>". intros. rewrite H0. unfold node_of_pl.
  setoid_rewrite H. trivial. Qed.
  
Global Instance cell_of_pl_proper : Proper ((≡) ==> (=) ==> (≡)) cell_of_pl.
Proof. unfold Proper, "==>". intros. rewrite H0. unfold cell_of_pl.
  setoid_rewrite H. trivial. Qed.

Lemma branch_of_branch_op (branch1 : Branch M) (branch2 : Branch M)
  : (branch_of_branch (branch1 ⋅ branch2)) ≡ branch_of_branch branch1 ⋅ branch_of_branch branch2.
Proof. destruct branch1, branch2; unfold "⋅", branch_of_branch, branch_op; trivial.
  destruct branch1; trivial.
Qed.

Lemma node_of_branch_op (branch1 : Branch M) (branch2 : Branch M)
  : (node_of_branch (branch1 ⋅ branch2)) ≡ node_of_branch branch1 ⋅ node_of_branch branch2.
Proof. destruct branch1, branch2; unfold "⋅", node_of_branch, branch_op; trivial.
  - setoid_rewrite op_trivial_node; trivial. unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
  - setoid_rewrite node_op_comm. setoid_rewrite op_trivial_node; trivial. unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
  - setoid_rewrite op_trivial_node; trivial. unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
Qed.

Lemma branch_of_node_op (node1 : Node M) (node2 : Node M)
  : (branch_of_node (node1 ⋅ node2)) ≡ branch_of_node node1 ⋅ branch_of_node node2.
Proof.
  destruct node1, node2. trivial.
Qed.

Lemma cell_of_node_op (node1 : Node M) (node2 : Node M)
  : (cell_of_node (node1 ⋅ node2)) ≡ cell_of_node node1 ⋅ cell_of_node node2.
Proof.
  destruct node1, node2. trivial.
Qed.

Lemma walk_op (j: nat) (branch1 : Branch M) (branch2 : Branch M)
  : (walk j (branch1 ⋅ branch2)) ≡ walk j branch1 ⋅ walk j branch2.
Proof.
  generalize branch1, branch2. clear branch1. clear branch2. induction j.
  - intros; trivial.
  - intros. cbn [walk]. setoid_rewrite IHj. apply branch_of_branch_op.
Qed.

Lemma hop_op (j: nat) (branch1 : Branch M) (branch2 : Branch M)
  : (hop j (branch1 ⋅ branch2)) ≡ hop j branch1 ⋅ hop j branch2.
Proof.
  unfold hop. setoid_rewrite walk_op. setoid_rewrite node_of_branch_op.
      apply branch_of_node_op.
Qed.

Lemma hops_op (js: list nat) (branch1 : Branch M) (branch2 : Branch M)
  : (hops js (branch1 ⋅ branch2)) ≡ hops js branch1 ⋅ hops js branch2.
Proof.
  generalize branch1, branch2. clear branch1. clear branch2. induction js.
  - intros. trivial.
  - intros. cbn [hops]. setoid_rewrite hop_op.
  setoid_rewrite IHjs. trivial.
Qed.

Lemma branch_of_pl_op (branch1 : Branch M) (branch2 : Branch M) pl
  : (branch_of_pl branch1 pl) ⋅ (branch_of_pl branch2 pl) ≡ branch_of_pl (branch1 ⋅ branch2) pl.
Proof. unfold branch_of_pl. destruct pl. setoid_rewrite hops_op.
  setoid_rewrite walk_op. trivial.
Qed.

Lemma node_of_pl_op (branch1 : Branch M) (branch2 : Branch M) pl
  : (node_of_pl branch1 pl) ⋅ (node_of_pl branch2 pl) ≡ node_of_pl (branch1 ⋅ branch2) pl.
Proof. unfold node_of_pl. setoid_rewrite <- branch_of_pl_op.
  setoid_rewrite node_of_branch_op. trivial. Qed.

Lemma cell_of_pl_op (branch1 : Branch M) (branch2 : Branch M) pl
  : (cell_of_pl branch1 pl) ⋅ (cell_of_pl branch2 pl) ≡ cell_of_pl (branch1 ⋅ branch2) pl.
Proof. unfold cell_of_pl. setoid_rewrite <- node_of_pl_op.
  setoid_rewrite cell_of_node_op. trivial. Qed.
  
Lemma BranchCons_node_of_branch_branch_of_branch b
 : b ≡ BranchCons (node_of_branch b) (branch_of_branch b).
Proof. destruct b.
 - unfold node_of_branch, branch_of_branch. trivial.
 - unfold node_of_branch, branch_of_branch, triv_node. unfold "≡", branch_equiv, branch_trivial. intuition. unfold cell_trivial, triv_cell. intuition.
Qed.

Lemma CellNode_cell_of_node_branch_of_node n
  : n = CellNode (cell_of_node n) (branch_of_node n). 
Proof. destruct n. trivial. Qed.

Lemma walk_add p q b
  : walk (p + q) b = walk q (walk p b).
Proof. generalize b. clear b. induction q.
  - trivial. intro. simpl. replace (p + 0) with p by lia. trivial.
  - intro. replace (p + S q) with (S (p + q)) by lia.
    cbn [walk]. rewrite IHq. trivial.
Qed.

Lemma hops_app p q b
  : hops (p ++ q) b = hops q (hops p b).
Proof. generalize b. clear b. induction p.
  - simpl. trivial.
  - simpl. intro. apply IHp.
Qed.
  
Lemma hops_app_last p i b
  : hops (p ++ [i]) b = hop i (hops p b).
Proof.
  rewrite hops_app. cbn [hops]. trivial. Qed.

Lemma branchcons_pl t p i
  : branch_of_pl t (p, i) ≡ BranchCons (node_of_pl t (p, i)) (branch_of_pl t (p, S i)).
Proof.
unfold branch_of_pl, node_of_pl, branch_of_pl. cbn [walk]. apply BranchCons_node_of_branch_branch_of_branch. Qed.
  
Lemma cellnode_pl t p i
  : node_of_pl t (p, i) = CellNode (cell_of_pl t (p, i)) (branch_of_pl t (p++[i], 0)).
Proof. unfold cell_of_pl, branch_of_pl, node_of_pl. cbn [walk].
  unfold branch_of_pl. rewrite hops_app_last. unfold hop.
  apply CellNode_cell_of_node_branch_of_node.
Qed.

Lemma b_equiv_branch_of_branch b0 b n
  (e : b0 ≡ BranchCons n b) : b ≡ branch_of_branch b0.
Proof.
  destruct b0.
  - unfold branch_of_branch. unfold "≡", branch_equiv in e. intuition.
  - unfold branch_of_branch. unfold "≡", branch_equiv, branch_trivial in e. intuition.
Qed.
  
Lemma n_equiv_node_of_branch b0 b n
  (e : b0 ≡ BranchCons n b) : n ≡ node_of_branch b0.
Proof.
  destruct b0.
  - unfold node_of_branch. unfold "≡", branch_equiv in e. intuition.
  - unfold branch_of_branch. unfold "≡", branch_equiv, branch_trivial in e.
      apply node_equiv_of_trivial; intuition.
      unfold node_of_branch, node_trivial, triv_node, cell_trivial, triv_cell. intuition.
Qed.
  
Lemma b_equiv_branch_of_node n b c
  (e : n ≡ CellNode c b) : b ≡ branch_of_node n.
Proof.
  destruct n. unfold branch_of_node. unfold "≡", node_equiv in e. intuition.
Qed.
  
Lemma branchcons_pl_inv_b t p i b n
  : branch_of_pl t (p, i) ≡ BranchCons n b ->
      b ≡ branch_of_pl t (p, S i).
Proof. unfold branch_of_pl in *. cbn [walk]. apply b_equiv_branch_of_branch. Qed.

Lemma branchcons_pl_inv_n t p i b n
  : branch_of_pl t (p, i) ≡ BranchCons n b ->
      n ≡ node_of_pl t (p, i).
Proof. unfold branch_of_pl, node_of_pl, branch_of_pl. apply n_equiv_node_of_branch. Qed.
  
Lemma cellnode_pl_inv_b t p i c branch
  : node_of_pl t (p, i) ≡ CellNode c branch -> branch ≡ branch_of_pl t (p++[i], 0).
Proof. unfold node_of_pl, branch_of_pl. setoid_rewrite hops_app_last. unfold hop.
  apply b_equiv_branch_of_node.
Qed.

Lemma branch_of_node_node_of_pl t p i
  : branch_of_node (node_of_pl t (p, i)) ≡ branch_of_pl t (p++[i], 0).
Proof. unfold node_of_pl, branch_of_pl. setoid_rewrite hops_app_last. unfold hop. trivial.
Qed.

Lemma branch_trivial_branch_of_branch b
  : branch_trivial b → branch_trivial (branch_of_branch b).
Proof.
  destruct b.
   - unfold branch_of_branch. intro. unfold branch_trivial in H. intuition.
   - unfold branch_of_branch. intro. unfold branch_trivial in H. intuition.
Qed.
  
Lemma node_trivial_node_of_branch b
  : branch_trivial b → node_trivial (node_of_branch b).
Proof.
  destruct b.
  - unfold node_of_branch. intro. unfold branch_trivial in H. intuition.
  - unfold node_of_branch. intro. unfold node_trivial, triv_node, cell_trivial, triv_cell.
      intuition.
Qed.
  
Lemma branch_trivial_branch_of_node n
  : node_trivial n → branch_trivial (branch_of_node n).
Proof. intro. destruct n. unfold branch_of_node. unfold node_trivial in H. intuition.
Qed.

Lemma rec_branch_branch_triv t p i
  : branch_trivial (branch_of_pl t (p, i)) ->
    branch_trivial (branch_of_pl t (p, S i)).
Proof. unfold branch_of_pl. cbn [walk]. apply branch_trivial_branch_of_branch. Qed.
    
Lemma rec_branch_node_triv t p i
  : branch_trivial (branch_of_pl t (p, i)) ->
    node_trivial (node_of_pl t (p, i)).
Proof. unfold node_of_pl, branch_of_pl. apply node_trivial_node_of_branch. Qed.
    
Lemma rec_node_branch_triv t p i
  : node_trivial (node_of_pl t (p, i)) ->
    branch_trivial (branch_of_pl t (p++[i], 0)).
Proof. unfold node_of_pl. unfold branch_of_pl. setoid_rewrite hops_app_last. unfold hop.
  apply branch_trivial_branch_of_node.
Qed.
    
Lemma branch_nil_of_n_child t p i :
    branch_trivial (branch_of_pl t (p, i)) -> BranchNil ≡ branch_of_pl t (p ++ [i], 0).
Proof.
  intros. unfold "≡", branch_equiv.  unfold branch_of_pl in *.
    setoid_rewrite hops_app_last. unfold hop.
    apply branch_trivial_branch_of_node.
    apply node_trivial_node_of_branch. trivial.
Qed.
    
Lemma branch_nil_of_b_child t p i :
    branch_trivial (branch_of_pl t (p, i)) -> BranchNil ≡ branch_of_pl t (p, S i).
Proof.
  intros. unfold "≡", branch_equiv. apply rec_branch_branch_triv. trivial.
Qed.
    
Lemma node_triv_of_triv_branch t p i
    : (branch_trivial (branch_of_pl t (p, i))) -> (node_of_pl t (p, i)) ≡ triv_node.
Proof.
  intro. apply node_equiv_of_trivial.
    - unfold node_of_pl. apply node_trivial_node_of_branch. trivial.
    - unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
Qed.

Lemma branch_of_pl_zero t : t = branch_of_pl t ([], 0).
Proof. trivial. Qed.

Lemma branch_of_branch_BranchNil
  : (branch_of_branch (BranchNil : Branch M)) = BranchNil.
Proof. trivial. Qed.

Lemma node_of_branch_BranchNil
  : (node_of_branch (BranchNil : Branch M)) = triv_node.
Proof. trivial. Qed.

Lemma branch_of_node_BranchNil
  : (branch_of_node triv_node) = BranchNil.
Proof. trivial. Qed.

Lemma walk_BranchNil j
  : (walk j (BranchNil : Branch M)) = BranchNil.
Proof. induction j; trivial. cbn [walk]. setoid_rewrite IHj. trivial.
Qed.

Lemma hop_BranchNil j
  : (hop j (BranchNil : Branch M)) = BranchNil.
Proof. unfold hop. setoid_rewrite walk_BranchNil. trivial.
Qed.

Lemma hops_BranchNil js
  : (hops js (BranchNil : Branch M)) = BranchNil.
Proof. induction js; trivial. cbn [hops]. rewrite hop_BranchNil. trivial.
Qed.

Lemma branch_of_pl_BranchNil (pl : PathLoc)
  : (branch_of_pl (BranchNil : Branch M) pl) = BranchNil.
Proof. unfold branch_of_pl. destruct pl. setoid_rewrite hops_BranchNil.
  setoid_rewrite walk_BranchNil. trivial. Qed.

Lemma node_of_pl_BranchNil (pl: PathLoc)
  : node_of_pl (BranchNil : Branch M) pl = triv_node.
Proof. unfold node_of_pl. setoid_rewrite branch_of_pl_BranchNil. trivial. Qed.

Lemma cell_of_pl_BranchNil (pl: PathLoc)
  : cell_of_pl (BranchNil : Branch M) pl = triv_cell.
Proof. unfold cell_of_pl. setoid_rewrite node_of_pl_BranchNil. trivial. Qed.

    (*
Section PLInduction1.
  Context
    (trunk: Branch M)
    (in_node_fn : PathLoc -> Node M -> Prop)
    (in_branch_fn : PathLoc -> Branch M -> Prop)
    (in_node_fn_proper : ∀ pl, Proper ((≡) ==> (impl)) (in_node_fn pl))
    (in_branch_fn_proper : ∀ pl, Proper ((≡) ==> (impl)) (in_branch_fn pl))
    (node_fn : PathLoc -> Node M -> Prop)
    (branch_fn : PathLoc -> Branch M -> Prop)
    (ns: ∀ pl, in_node_fn pl (node_of_pl trunk pl))
    (bs: ∀ pl, in_branch_fn pl (branch_of_pl trunk pl))
    (node_ind : ∀ p i cell branch ,
        branch_fn (p ++ [i], 0) branch ->
        in_node_fn (p, i) (CellNode cell branch) ->
        node_fn (p, i) (CellNode cell branch))
    (branch_ind : ∀ p i node branch ,
        branch_fn (p, S i) branch ->
        node_fn (p, i) node ->
        in_branch_fn (p, i) (BranchCons node branch) ->
        branch_fn (p, i) (BranchCons node branch))
    (branchnil_ind : ∀ pl, branch_fn pl BranchNil)
  .
  
  Lemma node_pl_induction_1 (node: Node M) p i
    (nn: node ≡ node_of_pl trunk (p, i)) : node_fn (p, i) node
  with branch_pl_induction_1 (branch: Branch M) p i
    (bb: branch ≡ branch_of_pl trunk (p, i)) : branch_fn (p, i) branch.
  Proof using EqDecision0 M TPCM0 branch_fn branch_ind branchnil_ind bs in_branch_fn
    in_branch_fn_proper in_node_fn in_node_fn_proper node_fn node_ind ns trunk.
    - destruct node.
      have IHb := branch_pl_induction_1 b.
      clear node_pl_induction_1.
      clear branch_pl_induction_1.
      setoid_rewrite cellnode_pl in nn. inversion nn.
      apply node_ind; trivial.
      + apply IHb; trivial.
      + setoid_rewrite H0. setoid_rewrite H. setoid_rewrite <- cellnode_pl. apply ns.
    - destruct branch.
      + have IHb := branch_pl_induction_1 branch.
        have IHn := node_pl_induction_1 n.
        clear node_pl_induction_1.
        clear branch_pl_induction_1.
        setoid_rewrite branchcons_pl in bb. inversion bb.
        apply branch_ind; trivial.
        * apply IHb; trivial.
        * apply IHn; trivial.
        * setoid_rewrite H0. setoid_rewrite H. setoid_rewrite <- branchcons_pl. apply bs.
      + apply branchnil_ind.
   Qed.
    
  Lemma pl_induction_1
    : branch_fn ([], 0) trunk.
  Proof using EqDecision0 M TPCM0 branch_fn branch_ind branchnil_ind bs in_branch_fn
    in_branch_fn_proper in_node_fn in_node_fn_proper node_fn node_ind ns trunk.
  apply branch_pl_induction_1. apply branch_of_pl_zero. Qed.
End PLInduction1.
*)

Lemma branchnil_of_cell_triv c b
  (n1triv : CellNode c b ≡ triv_node)
  : b ≡ BranchNil.
Proof. unfold triv_node, "≡", cell_equiv, node_equiv in n1triv. intuition.
Qed.
  
Lemma branchnil_of_parent_triv node branch
  (bb1 : BranchNil ≡ BranchCons node branch)
  : branch ≡ BranchNil.
Proof. unfold "≡", branch_equiv, branch_trivial in bb1.
  apply branch_equiv_of_trivial; intuition.
  unfold branch_trivial. trivial. Qed.
  
Lemma nodetriv_of_parent_triv node branch
  (bb1 : BranchNil ≡ BranchCons node branch)
  : node ≡ triv_node.
Proof. apply node_equiv_of_trivial.
  - unfold "≡", branch_equiv, branch_trivial in bb1. intuition.
  - unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
Qed.

Section PLInduction2.
  Context
    (trunk1: Branch M)
    (trunk2: Branch M)
    (in_node_fn : list nat -> nat -> Node M -> Node M -> Prop)
    (in_branch_fn : list nat -> nat -> Branch M -> Branch M -> Prop)
    (in_node_fn_proper : ∀ p i, Proper ((≡) ==> (≡) ==> (impl)) (in_node_fn p i))
    (in_branch_fn_proper : ∀ p i, Proper ((≡) ==> (≡) ==> (impl)) (in_branch_fn p i))
    (node_fn : list nat -> nat -> Node M -> Node M -> Prop)
    (branch_fn : list nat -> nat -> Branch M -> Branch M -> Prop)
    (branch_fn_proper : ∀ p i, Proper ((≡) ==> (≡) ==> (impl)) (branch_fn p i))
    (ns: ∀ p i, in_node_fn p i (node_of_pl trunk1 (p, i)) (node_of_pl trunk2 (p, i)))
    (bs: ∀ p i, in_branch_fn p i (branch_of_pl trunk1 (p, i)) (branch_of_pl trunk2 (p, i)))
    (node_ind : ∀ p i cell1 branch1 cell2 branch2 ,
        branch_fn (p ++ [i]) 0 branch1 branch2 ->
        in_node_fn p i (CellNode cell1 branch1) (CellNode cell2 branch2) ->
        node_fn p i (CellNode cell1 branch1) (CellNode cell2 branch2))
    (branch_ind : ∀ p i node1 branch1 node2 branch2 ,
        branch_fn p (S i) branch1 branch2 ->
        node_fn p i node1 node2 ->
        in_branch_fn p i (BranchCons node1 branch1) (BranchCons node2 branch2) ->
        branch_fn p i (BranchCons node1 branch1) (BranchCons node2 branch2))
    (branchnil_ind : ∀ p i, branch_fn p i BranchNil BranchNil)
  .
    
  Lemma node_pl_induction_2_helper (node1 node2: Node M) p i
    (nn1: node1 ≡ node_of_pl trunk1 (p, i))
    (nn2: node2 ≡ node_of_pl trunk2 (p, i))
    (n1triv : node1 ≡ triv_node)
      : node_fn p i node1 node2
  with branch_pl_induction_2_helper (branch1 branch2: Branch M) p i
    (bb1: branch1 ≡ branch_of_pl trunk1 (p, i))
    (bb2: branch2 ≡ branch_of_pl trunk2 (p, i))
    (b1triv : branch1 ≡ BranchNil)
      : branch_fn p i branch1 branch2.
  Proof using EqDecision0 M TPCM0 branch_fn branch_fn_proper branch_ind branchnil_ind bs
in_branch_fn in_branch_fn_proper in_node_fn in_node_fn_proper node_fn node_ind ns trunk1
trunk2.
    - destruct node1, node2.
      have IHb := branch_pl_induction_2_helper b.
      clear node_pl_induction_2_helper.
      clear branch_pl_induction_2_helper.
      setoid_rewrite cellnode_pl in nn1. inversion nn1.
      setoid_rewrite cellnode_pl in nn2. inversion nn2.
      apply node_ind; trivial.
      + apply IHb; trivial. apply branchnil_of_cell_triv with (c := c). trivial.
      + setoid_rewrite H0. setoid_rewrite H.
        setoid_rewrite H1. setoid_rewrite H2.
        setoid_rewrite <- cellnode_pl. apply ns.
    - destruct branch2.
      + have IHb := branch_pl_induction_2_helper _ branch2.
        have IHn := node_pl_induction_2_helper _ n.
        clear node_pl_induction_2_helper.
        clear branch_pl_induction_2_helper.
        setoid_rewrite branchcons_pl in bb1.
        setoid_rewrite branchcons_pl in bb2. inversion bb2.
        setoid_rewrite bb1.
        apply branch_ind; trivial.
        * apply IHb; trivial. setoid_rewrite b1triv in bb1.
            eapply branchnil_of_parent_triv. apply bb1.
        * apply IHn; trivial. setoid_rewrite b1triv in bb1.
            eapply nodetriv_of_parent_triv. apply bb1.
        * setoid_rewrite H0. setoid_rewrite H. setoid_rewrite <- branchcons_pl. apply bs.
      + setoid_rewrite b1triv.
        apply branchnil_ind.
   Qed.
  
  Lemma node_pl_induction_2 (node1 node2: Node M) p i
    (nn1: node1 ≡ node_of_pl trunk1 (p, i))
    (nn2: node2 ≡ node_of_pl trunk2 (p, i))
      : node_fn p i node1 node2
  with branch_pl_induction_2 (branch1 branch2: Branch M) p i
    (bb1: branch1 ≡ branch_of_pl trunk1 (p, i))
    (bb2: branch2 ≡ branch_of_pl trunk2 (p, i))
      : branch_fn p i branch1 branch2.
  Proof using EqDecision0 M TPCM0 branch_fn branch_fn_proper branch_ind branchnil_ind bs
in_branch_fn in_branch_fn_proper in_node_fn in_node_fn_proper node_fn node_ind ns trunk1
trunk2.
    - destruct node1, node2.
      have IHb := branch_pl_induction_2 b.
      clear node_pl_induction_2.
      clear branch_pl_induction_2.
      setoid_rewrite cellnode_pl in nn1. inversion nn1.
      setoid_rewrite cellnode_pl in nn2. inversion nn2.
      apply node_ind; trivial.
      + apply IHb; trivial.
      + setoid_rewrite H0. setoid_rewrite H.
        setoid_rewrite H1. setoid_rewrite H2.
        setoid_rewrite <- cellnode_pl. apply ns.
    - destruct branch1.
      + have IHb := branch_pl_induction_2 branch1.
        have IHn := node_pl_induction_2 n.
        clear node_pl_induction_2.
        clear branch_pl_induction_2.
        setoid_rewrite branchcons_pl in bb1. inversion bb1.
        setoid_rewrite branchcons_pl in bb2.
        setoid_rewrite bb2.
        apply branch_ind; trivial.
        * apply IHb; trivial.
        * apply IHn; trivial.
        * setoid_rewrite H0. setoid_rewrite H. setoid_rewrite <- branchcons_pl. apply bs.
      + apply branch_pl_induction_2_helper; trivial.
   Qed.
    
  Lemma pl_induction_2
    : branch_fn [] 0 trunk1 trunk2.
  Proof using EqDecision0 M TPCM0 branch_fn branch_fn_proper branch_ind branchnil_ind bs
in_branch_fn in_branch_fn_proper in_node_fn in_node_fn_proper node_fn node_ind ns trunk1
trunk2.
  apply branch_pl_induction_2.
   - rewrite <- branch_of_pl_zero. trivial.
   - rewrite <- branch_of_pl_zero. trivial.
  Qed.
End PLInduction2.


Lemma equiv_extensionality_cells
    (branch1: Branch M) (branch2: Branch M)
    (ext_eq : forall pl , (cell_of_pl branch1 pl) ≡ (cell_of_pl branch2 pl))
    : branch1 ≡ branch2. 
Proof. apply pl_induction_2 with (trunk1 := branch1) (trunk2 := branch2)
  (branch_fn := λ p i branch1 branch2 , branch1 ≡ branch2)
  (node_fn := λ p i node1 node2 , node1 ≡ node2)
  (in_node_fn := λ p i node1 node2 , cell_of_node node1 ≡ cell_of_node node2)
  (in_branch_fn := λ p i branch1 branch2 , True).
 - intro. unfold Proper, "==>", impl. intros. setoid_rewrite <- H. setoid_rewrite <- H0.
    trivial.
 - intro. unfold Proper, "==>", impl. trivial.
 - intro. unfold Proper, "==>", impl. intros. setoid_rewrite <- H. setoid_rewrite <- H0.
    trivial.
 - intros. apply ext_eq.
 - trivial.
 - intros. unfold cell_of_node in H0. setoid_rewrite H. setoid_rewrite H0. trivial.
 - intros. setoid_rewrite H0. setoid_rewrite H. trivial.
 - trivial.
Qed.

Lemma branch_of_pl_cons_eq p i n b trunk
  (bop : branch_of_pl trunk (p, i) = BranchCons n b)
  : (branch_of_pl trunk (p, S i)) = b.
Proof.
  unfold branch_of_pl in *. cbn [walk]. rewrite bop. trivial. Qed.

Section PLReverseInduction1.
  Context
    (trunk: Branch M)
    (branch_fn: PathLoc -> Branch M -> Prop)
    (node_fn: PathLoc -> Node M -> Prop)
    (b_base: branch_fn ([], 0) trunk)
    (node_ind : ∀ p i cell branch ,
        node_fn (p, i) (CellNode cell branch) ->
        branch_fn (p ++ [i], 0) branch
    )
    (branch_ind : ∀ p i node branch ,
        branch_fn (p, i) (BranchCons node branch) ->
        branch_fn (p, S i) branch /\ node_fn (p, i) node
    )
    (branchnil_ind : ∀ pl, branch_fn pl BranchNil)
    (trivnode_ind : ∀ pl, node_fn pl triv_node)
  .
  
  Lemma pl_reverse_induction1
    : ∀ pl , node_fn pl (node_of_pl trunk pl) /\ branch_fn pl (branch_of_pl trunk pl).
  Proof using EqDecision0 M TPCM0 b_base branch_fn branch_ind branchnil_ind node_fn node_ind
      trivnode_ind trunk.
  intro. destruct pl. rename l into p. rename n into i. generalize i. clear i.
  induction p as [p IHp] using (induction_ltof1 _ (@length _)); unfold ltof in IHp.
  induction i as [i IHi] using lt_wf_ind.
  
  enough (branch_fn (p, i) (branch_of_pl trunk (p, i))).
   - split; trivial.
     destruct (branch_of_pl trunk (p, i)) eqn:bop.
      + assert (n = node_of_branch (BranchCons n b)) by trivial.
        rewrite <- bop in H0.
        unfold node_of_pl. rewrite <- H0.
        have jr := branch_ind p i n b. intuition.
      + unfold node_of_pl. rewrite bop. unfold node_of_branch.
        apply trivnode_ind.
   - destruct i.
      + have h : Decision (p = []) by solve_decision. destruct h.
        * subst p. rewrite <- branch_of_pl_zero. trivial.
        * have jr := node_ind (removelast p) (List.last p 0)
            (cell_of_pl trunk (removelast p, List.last p 0))
            (branch_of_pl trunk (p, 0)).
          rewrite <- app_removelast_last in jr; trivial. apply jr.
          replace (p, 0) with (removelast p ++ [List.last p 0], 0).
          -- rewrite <- cellnode_pl. apply IHp.
            replace (length p) with (length (removelast p ++ [List.last p 0])).
            ++ rewrite app_length. simpl. lia.
            ++ f_equal. rewrite <- app_removelast_last; trivial.
          -- f_equal. rewrite <- app_removelast_last; trivial.
      + destruct (branch_of_pl trunk (p, i)) eqn:bop.
        * assert (b = branch_of_branch (BranchCons n b)) by trivial.
          rewrite <- bop in H.
          have bopce := branch_of_pl_cons_eq p i n b trunk bop.
          rewrite bopce.
          have jr := branch_ind p i n b. apply jr.
          rewrite <- bop. apply IHi. lia.
        * unfold branch_of_pl. unfold branch_of_pl in bop. cbn [walk].
            rewrite bop. unfold branch_of_branch. trivial.
  Qed. 
  
  Lemma pl_reverse_induction1_node
    : ∀ pl , node_fn pl (node_of_pl trunk pl).
  Proof using EqDecision0 M TPCM0 b_base branch_fn branch_ind branchnil_ind node_fn node_ind
      trivnode_ind trunk.
  apply pl_reverse_induction1. Qed.
  
End PLReverseInduction1.

Lemma forall_branch_all_total_in_refinement_domain roi branch lt
  : branch_all_total_in_refinement_domain roi branch lt 0
    -> forall pl, node_all_total_in_refinement_domain roi (node_of_pl branch pl) lt (plend pl).
Proof. 
  intros.
    apply pl_reverse_induction1 with
    (trunk := branch)
    (branch_fn := λ pl b , branch_all_total_in_refinement_domain roi b lt (plend pl))
    (node_fn := λ pl n , node_all_total_in_refinement_domain roi n lt (plend pl)).
   - unfold plend. trivial.
   - intros. cbn [node_all_total_in_refinement_domain] in H0. intuition.
   - intros. unfold branch_all_total_in_refinement_domain in H0. intuition.
   - intros. unfold branch_all_total_in_refinement_domain. trivial.
   - intros. apply node_all_total_in_refinement_domain_of_trivial.
      unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
Qed.

(*
Lemma forall_equiv_branch_all_total_in_refinement_domain roi branch lt idx
  : branch_all_total_in_refinement_domain roi branch lt idx
    <-> forall pl, node_all_total_in_refinement_domain roi (node_of_pl branch pl) lt (plend pl). *)

End Indexing.

Definition plsplit (ln: list nat) : PathLoc := (removelast ln, List.last ln 0).

Lemma plsplit_app p i : plsplit (p ++ [i]) = (p, i).
Proof.
  unfold plsplit. rewrite removelast_last. rewrite last_last. trivial. Qed.
