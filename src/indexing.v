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
Require Import coq_tricks.Deex.

Definition PathLoc : Type := list nat * nat.
Definition plend (pl: PathLoc) := match pl with (_, l) => l end.

Section Indexing.

(*Context {M: Type}  `{!EqDecision M}.*)
(*Context `{!EqDecision RefinementIndex}.
Context {refinement_of_index : RefinementIndex -> Refinement M M}.*)

Context {M} `{!EqDecision M, !TPCM M}.

Fixpoint step_node (branch: Branch M) (idx: nat) :=
  match branch, idx with
  | BranchNil, _ => triv_node
  | BranchCons _ sub, (S idx) => step_node sub idx
  | BranchCons n _, 0 => n
  end.

Definition step_branch (branch: Branch M) (idx: nat) :=
  match step_node branch idx with
  | CellNode _ b => b
  end.
  
Fixpoint node_of_pl' (branch: Branch M) (p: list nat) (i: nat) : Node M :=
  match p with
  | [] => step_node branch i
  | (x :: p0) => node_of_pl' (step_branch branch x) p0 i
  end.
  
Definition node_of_pl (branch: Branch M) (pl: PathLoc) : Node M :=
  match pl with
  | (p, i) => node_of_pl' branch p i
  end.
  
Definition branch_of_pl (branch: Branch M) (pl: PathLoc) : Branch M. Admitted.
    
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

Lemma node_trivial_step_node : ∀ i branch ,
  (branch_trivial branch) -> node_trivial (step_node branch i).
Proof.
  induction i.
  - intros. unfold node_trivial, step_node; destruct branch; trivial.
    + destruct H. trivial.
    + apply node_trivial_triv_node.
  - intros. unfold step_node. unfold node_trivial; destruct branch; trivial.
    + apply IHi. destruct H; trivial.
    + apply node_trivial_triv_node.
Qed.

Lemma step_node_equiv branch1 branch2 i
  (equ: branch1 ≡ branch2) : step_node branch1 i ≡ step_node branch2 i.
Proof.
  generalize equ. generalize branch1, branch2. clear equ. clear branch1. clear branch2.
  induction i.
  - intros. unfold step_node. destruct branch1, branch2.
    + unfold "≡", branch_equiv in equ. destruct_ands; trivial.
    + unfold "≡" in *. unfold branch_equiv, node_equiv in *.
        unfold branch_trivial in equ. destruct_ands. apply node_equiv_of_trivial; trivial.
        apply node_trivial_triv_node.
    + unfold "≡" in *. unfold branch_equiv in *. unfold branch_trivial in equ.
        destruct_ands. apply node_equiv_of_trivial; trivial.
        apply node_trivial_triv_node.
    + trivial.
  - intros. unfold step_node. destruct branch1, branch2.
    + apply IHi. destruct equ. trivial.
    + apply node_equiv_of_trivial.
      * fold step_node. apply node_trivial_step_node. destruct equ. trivial.
      * apply node_trivial_triv_node.
    + apply node_equiv_of_trivial.
      * apply node_trivial_triv_node.
      * fold step_node. apply node_trivial_step_node. destruct equ. trivial.
    + trivial.
Qed.

Global Instance step_node_equiv_proper : Proper ((≡) ==> (=) ==> (≡)) step_node.
Proof. unfold Proper, "==>". intros. rewrite H0. apply step_node_equiv. trivial. Defined.

Lemma step_branch_equiv branch1 branch2 i
  (equ: branch1 ≡ branch2) : step_branch branch1 i ≡ step_branch branch2 i.
Proof.
  assert (step_node branch1 i ≡ step_node branch2 i) by (apply step_node_equiv; trivial).
  unfold step_branch. destruct (step_node branch1 i).
      destruct (step_node branch2 i).
      unfold "≡", node_equiv in H. destruct_ands; trivial.
Qed.

Global Instance step_branch_equiv_proper : Proper ((≡) ==> (=) ==> (≡)) step_branch.
Proof. unfold Proper, "==>". intros. rewrite H0. apply step_branch_equiv. trivial. Defined.

Definition node_of_pl'_equiv p : ∀ branch1 branch2 i ,
  (branch1 ≡ branch2) -> node_of_pl' branch1 p i ≡ node_of_pl' branch2 p i.
Proof.
  induction p.
   - unfold node_of_pl'. apply step_node_equiv.
   - unfold node_of_pl'. fold node_of_pl'. intros.
      apply IHp. apply step_branch_equiv. trivial.
Qed.

Global Instance node_of_pl'_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) node_of_pl'.
Proof. unfold Proper, "==>". intros. rewrite H1. rewrite H0. apply node_of_pl'_equiv. trivial. Defined.

Definition node_of_pl_equiv : ∀ branch1 branch2 pl ,
  (branch1 ≡ branch2) -> node_of_pl branch1 pl ≡ node_of_pl branch2 pl.
Proof. intros. unfold node_of_pl. destruct pl. apply node_of_pl'_equiv. trivial. Qed.

Global Instance node_of_pl_proper : Proper ((≡) ==> (=) ==> (≡)) node_of_pl.
Proof. unfold Proper, "==>". intros. rewrite H0. apply node_of_pl_equiv. trivial. Defined.

Global Instance cell_of_pl_proper : Proper ((≡) ==> (=) ==> (≡)) cell_of_pl. Admitted.

Lemma step_node_op branch1 branch2 i
  : step_node branch1 i ⋅ step_node branch2 i
      ≡ step_node (branch1 ⋅ branch2) i.
Proof.
  generalize branch1, branch2. clear branch1. clear branch2.
  induction i.
  - intros. unfold "⋅", node_op, branch_op, step_node. destruct branch1, branch2.
     + unfold "⋅". trivial.
     + apply op_trivial_node. apply node_trivial_triv_node.
     + setoid_rewrite node_op_comm.
       apply op_trivial_node. apply node_trivial_triv_node.
     + apply op_trivial_node. apply node_trivial_triv_node.
  - intros. unfold "⋅", node_op, branch_op, step_node. destruct branch1, branch2.
     + fold step_node. fold node_op. apply IHi.
     + fold step_node. fold node_op.
        setoid_rewrite op_trivial_node; trivial. apply node_trivial_triv_node.
     + fold step_node. fold node_op.
        setoid_rewrite node_op_comm.
        setoid_rewrite op_trivial_node; trivial. apply node_trivial_triv_node.
     + fold step_node. fold node_op.
        setoid_rewrite op_trivial_node; trivial. apply node_trivial_triv_node.
Qed.

Lemma step_branch_op branch1 branch2 i
  : step_branch branch1 i ⋅ step_branch branch2 i
      ≡ step_branch (branch1 ⋅ branch2) i.
Proof.
  assert (step_node branch1 i ⋅ step_node branch2 i ≡ step_node (branch1 ⋅ branch2) i)
      by (apply step_node_op; trivial).
  unfold step_branch. 
  destruct (step_node branch1 i).
  destruct (step_node branch2 i).
  destruct (step_node (branch1 ⋅ branch2) i).
  unfold "≡", "⋅", cell_op in H. unfold node_equiv, node_op in H. destruct_ands. trivial.
Qed.

Lemma node_of_pl'_op (branch1 : Branch M) (branch2 : Branch M) p i
  : (node_of_pl' branch1 p i) ⋅ (node_of_pl' branch2 p i) ≡ node_of_pl' (branch1 ⋅ branch2) p i.
Proof.
  generalize branch1, branch2. clear branch1. clear branch2.
  induction p.
  - intros. unfold node_of_pl'. apply step_node_op.
  - intros.
      unfold node_of_pl in *. cbn [node_of_pl'].
      setoid_rewrite <- step_branch_op.
      apply IHp.
Qed.

Lemma node_of_pl_op (branch1 : Branch M) (branch2 : Branch M) pl
  : (node_of_pl branch1 pl) ⋅ (node_of_pl branch2 pl) ≡ node_of_pl (branch1 ⋅ branch2) pl.
Proof.
  unfold node_of_pl. destruct pl. apply node_of_pl'_op. Qed.

Lemma cell_of_pl_op (branch1 : Branch M) (branch2 : Branch M) pl
  : (cell_of_pl branch1 pl) ⋅ (cell_of_pl branch2 pl) ≡ cell_of_pl (branch1 ⋅ branch2) pl.
Proof.
  assert ((node_of_pl branch1 pl) ⋅ (node_of_pl branch2 pl) ≡ node_of_pl (branch1 ⋅ branch2) pl) as ce by (apply node_of_pl_op).
  unfold cell_of_pl.
  destruct (node_of_pl branch1 pl).
  destruct (node_of_pl branch2 pl).
  destruct (node_of_pl (branch1 ⋅ branch2) pl).
  unfold "≡","⋅",node_equiv,node_op in ce. destruct_ands; trivial.
Qed.

(*Lemma pl_induction (branch: Branch M)
  (node_fn : Node M -> Prop) 
  (branch_fn : Node M -> Prop) 
  (branch_fn_nil : ∀ pl, branch_fn BranchNil pl)
  (∀ pl , node_fn (node_of_pl branch pl) pl)
  (node_ind : 
  *)

Lemma equiv_extensionality_cells
    (branch1: Branch M) (branch2: Branch M)
    (ext_eq : forall pl , (cell_of_pl branch1 pl) ≡ (cell_of_pl branch2 pl))
    : branch1 ≡ branch2. Admitted.
    
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
  
Lemma rec_branch_branch_triv t p i
  : branch_trivial (branch_of_pl t (p, i)) ->
    branch_trivial (branch_of_pl t (p, S i)). Admitted.
    
Lemma rec_branch_node_triv t p i
  : branch_trivial (branch_of_pl t (p, i)) ->
    node_trivial (node_of_pl t (p, i)). Admitted.
    
Lemma rec_node_branch_triv t p i
  : node_trivial (node_of_pl t (p, i)) ->
    branch_trivial (branch_of_pl t (p++[i], 0)). Admitted.
    Lemma branch_nil_of_n_child t p i :
    branch_trivial (branch_of_pl t (p, i)) -> BranchNil ≡ branch_of_pl t (p ++ [i], 0).
    Admitted.
    
Lemma branch_nil_of_b_child t p i :
    branch_trivial (branch_of_pl t (p, i)) -> BranchNil ≡ branch_of_pl t (p, S i).
    Admitted.
    
Lemma node_triv_of_triv_branch t p i
    : (branch_trivial (branch_of_pl t (p, i))) -> (node_of_pl t (p, i)) ≡ triv_node.
    Admitted.

  
End Indexing.
