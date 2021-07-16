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

Definition PathLoc : Type := list nat * nat.
Definition plend (pl: PathLoc) := match pl with (_, l) => l end.

Section Indexing.

(*Context {M: Type}  `{!EqDecision M}.*)
(*Context `{!EqDecision RefinementIndex}.
Context {refinement_of_index : RefinementIndex -> Refinement M M}.*)

Context {M} `{!EqDecision M, !TPCM M}.

Fixpoint branch_step_branch (branch: Branch M) (idx: nat) :=
  match branch, idx with
  | BranchNil, _ => BranchNil
  | BranchCons _ sub, (S idx) => branch_step_branch sub idx
  | BranchCons (CellNode _ b) _, 0 => b
  end.
  
Definition triv_cell : Cell M := CellCon unit empty.
Definition triv_node : Node M := CellNode triv_cell BranchNil.

Fixpoint branch_step_node (branch: Branch M) (idx: nat) :=
  match branch, idx with
  | BranchNil, _ => triv_node
  | BranchCons _ sub, (S idx) => branch_step_node sub idx
  | BranchCons n _, 0 => n
  end.
  
Fixpoint node_of_pl' (branch: Branch M) (p: list nat) (i: nat) : Node M :=
  match p with
  | [] => branch_step_node branch i
  | (x :: p0) => node_of_pl' (branch_step_branch branch x) p0 i
  end.
  
Definition node_of_pl (branch: Branch M) (pl: PathLoc) : Node M :=
  match pl with
  | (p, i) => node_of_pl' branch p i
  end.
    
Definition cell_of_pl (branch: Branch M) (pl: PathLoc) : Cell M :=
  match node_of_pl branch pl with CellNode c _ => c end.
    
    (*
Definition every_node {M} `{!EqDecision M, !TPCM M}
    (branch: Branch M) (fn : Node M -> nat -> Prop) : Prop. Admitted.

Lemma every_node_equiv_forall {M} `{!EqDecision M, !TPCM M}
    (branch : Branch M) (fn : Node M -> nat -> Prop)
    (rtriv: ∀ n idx , node_trivial n -> fn n idx)
  : (every_node branch fn) <-> (forall pl , fn (node_of_pl branch pl) (plend pl)). Admitted.
  *)
  
Lemma node_trivial_triv_node : node_trivial triv_node.
Proof. unfold node_trivial, triv_node, cell_trivial, triv_cell. crush.
Qed.
  
Lemma branch_step_node_op branch1 branch2 i
  : branch_step_node branch1 i ⋅ branch_step_node branch2 i
      ≡ branch_step_node (branch1 ⋅ branch2) i.
Proof.
  generalize branch1, branch2. clear branch1. clear branch2.
  induction i.
  - intros. unfold "⋅", node_op, branch_op, branch_step_node. destruct branch1, branch2.
     + unfold "⋅". trivial.
     + apply op_trivial_node. apply node_trivial_triv_node.
     + setoid_rewrite node_op_comm.
       apply op_trivial_node. apply node_trivial_triv_node.
     + apply op_trivial_node. apply node_trivial_triv_node.
  - intros. unfold "⋅", node_op, branch_op, branch_step_node. destruct branch1, branch2.
     + fold branch_step_node. fold node_op. apply IHi.
     + fold branch_step_node. fold node_op.
        setoid_rewrite op_trivial_node; trivial. apply node_trivial_triv_node.
     + fold branch_step_node. fold node_op.
        setoid_rewrite node_op_comm.
        setoid_rewrite op_trivial_node; trivial. apply node_trivial_triv_node.
     + fold branch_step_node. fold node_op.
        setoid_rewrite op_trivial_node; trivial. apply node_trivial_triv_node.
Qed.

Lemma branch_step_branch_op branch1 branch2 i
  : branch_step_branch branch1 i ⋅ branch_step_branch branch2 i
      ≡ branch_step_branch (branch1 ⋅ branch2) i.
Proof.
  generalize branch1, branch2. clear branch1. clear branch2.
  induction i.
  - intros. unfold "⋅". unfold branch_op, branch_step_node. destruct branch1, branch2.
     + fold branch_op. unfold branch_step_branch. destruct n. destruct n0. unfold "⋅".
        trivial.
     + fold branch_op. cbn [branch_step_branch]. destruct n. apply op_trivial_branch.
        unfold branch_trivial. trivial.
     + fold branch_op. cbn [branch_step_branch]. destruct n. unfold branch_op. trivial.
     + fold branch_op. cbn [branch_step_branch]. unfold branch_op. trivial.
  - intros. unfold "⋅". unfold node_op, branch_op, branch_step_branch. destruct branch1, branch2.
     + destruct n. destruct n0. fold branch_op. fold branch_step_branch. fold node_op. unfold "⋅". unfold node_op. apply IHi.
     + destruct n. fold branch_op. fold branch_step_branch.
        setoid_rewrite op_trivial_branch; trivial. unfold branch_trivial. trivial.
     + destruct n. fold branch_op. fold branch_step_branch. trivial.
     + trivial.
Qed.

Lemma node_of_pl_op (branch1 : Branch M) (branch2 : Branch M) pl
  : (node_of_pl branch1 pl) ⋅ (node_of_pl branch2 pl) ≡ node_of_pl (branch1 ⋅ branch2) pl.
Proof.
  generalize branch1, branch2. clear branch1. clear branch2.
  destruct pl. rename l into p. rename n into i.
  induction p.
  - intros. unfold node_of_pl, node_of_pl'. apply branch_step_node_op.
  - intros.
      unfold node_of_pl in *. cbn [node_of_pl'].
      setoid_rewrite <- branch_step_branch_op.
  

Lemma cell_of_pl_op {M} `{!EqDecision M, !TPCM M}
    (branch1 : Branch M) (branch2 : Branch M)
  : forall pl , (cell_of_pl branch1 pl) ⋅ (cell_of_pl branch2 pl) ≡ cell_of_pl (branch1 ⋅ branch2) pl.
Admitted.



Lemma equiv_extensionality_cells {M} `{!EqDecision M, !TPCM M}
    (branch1: Branch M) (branch2: Branch M)
    (ext_eq : forall pl , (cell_of_pl branch1 pl) ≡ (cell_of_pl branch2 pl))
    : branch1 ≡ branch2. Admitted.
  
End Indexing.
