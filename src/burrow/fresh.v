From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.rollup.
Require Import Burrow.locations.
Require Import Burrow.indexing.

From stdpp Require Import countable.

Section Fresh.

Context {M} `{!EqDecision M} `{!TPCM M}.

Fixpoint node_no_idx (node: Node M) (f: nat) (idx: nat) : Prop :=
  match node with
  | CellNode _ branch =>
         f ≠ idx
      /\ branch_no_idx branch f 0
  end
with branch_no_idx (branch: Branch M) (f: nat) (idx: nat) : Prop :=
  match branch with
  | BranchNil => True
  | BranchCons node branch =>
         node_no_idx node f idx
      /\ branch_no_idx branch f (S idx)
  end
.

Fixpoint node_max_idx (node: Node M) (idx: nat) : nat :=
  match node with
  | CellNode _ branch =>
         idx `max` branch_max_idx branch 0
  end
with branch_max_idx (branch: Branch M) (idx: nat) : nat :=
  match branch with
  | BranchNil => 1
  | BranchCons node branch =>
         node_max_idx node idx `max` branch_max_idx branch (S idx)
  end
.

Lemma node_no_idx_rewrite (node: Node M) (f: nat) (idx: nat)
    : node_no_idx node f idx =
  match node with
  | CellNode _ branch =>
         f ≠ idx
      /\ branch_no_idx branch f 0
  end. Proof. unfold node_no_idx, branch_no_idx. destruct node. trivial. Qed.
  
Lemma branch_no_idx_rewrite (branch: Branch M) (f: nat) (idx: nat)
    : branch_no_idx branch f idx =
  match branch with
  | BranchNil => True
  | BranchCons node branch =>
         node_no_idx node f idx
      /\ branch_no_idx branch f (S idx)
  end
.
Proof. unfold branch_no_idx, node_no_idx. destruct branch; trivial. Qed.

Lemma node_max_idx_rewrite (node: Node M) (idx: nat)
  : node_max_idx node idx =
  match node with
  | CellNode _ branch =>
         idx `max` branch_max_idx branch 0
  end.
Proof. unfold branch_max_idx, node_max_idx. destruct node; trivial. Qed.
  
Lemma branch_max_idx_rewrite (branch: Branch M) (idx: nat)
  : branch_max_idx branch idx =
  match branch with
  | BranchNil => 1
  | BranchCons node branch =>
         node_max_idx node idx `max` branch_max_idx branch (S idx)
  end
.
Proof. unfold branch_no_idx, node_no_idx. destruct branch; trivial. Qed.

Lemma node_no_idx_of_gt_max (node: Node M) (idx: nat) (t: nat)
    (gt: t > node_max_idx node idx) : node_no_idx node t idx
with branch_no_idx_of_gt_max (branch: Branch M) (idx: nat) (t: nat)
    (gt: t > branch_max_idx branch idx) : branch_no_idx branch t idx.
Proof.
  - destruct node.
    have ihb := branch_no_idx_of_gt_max b.
    clear node_no_idx_of_gt_max.
    clear branch_no_idx_of_gt_max.
    rewrite node_no_idx_rewrite. rewrite node_max_idx_rewrite in gt. split.
    + lia.
    + apply ihb. lia.
  - destruct branch.
    + have ihb := branch_no_idx_of_gt_max branch.
      have ihn := node_no_idx_of_gt_max n.
      clear node_no_idx_of_gt_max.
      clear branch_no_idx_of_gt_max.
      rewrite branch_no_idx_rewrite. rewrite branch_max_idx_rewrite in gt.
      split.
      * apply ihn. lia.
      * apply ihb. lia.
    + unfold branch_no_idx. trivial.
Qed.
  
Definition is_fresh_nat (b: Branch M) (f: nat) : Prop := branch_no_idx b f 0.

Definition alloc_alpha
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  : Branch M -> RI -> nat. Admitted.

Lemma is_fresh_alloc
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
    (branch: Branch M) (ri: RI)
    : is_fresh_nat branch (nat_of_extstep (alloc_alpha branch ri) ri). Admitted.

Lemma is_fresh_alloc_base branch
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
    : is_fresh_nat branch
    (nat_of_basestep RI (alloc_alpha branch (triv_ri RI))). Admitted.

Lemma trivial_node_at_fresh (b: Branch M) p i
  (is_fresh: is_fresh_nat b i)
  : node_trivial (node_of_pl b (p, i)). Admitted.
  
Lemma node_no_idx_of_op (node1 node2 : Node M) (f: nat) (idx: nat)
  (nni: node_no_idx (node1 ⋅ node2) f idx) : node_no_idx node2 f idx
with branch_no_idx_of_op (branch1 branch2 : Branch M) (f: nat) (idx: nat)
  (bni: branch_no_idx (branch1 ⋅ branch2) f idx) : branch_no_idx branch2 f idx.
Proof.
  - destruct node2.
    have ihb := branch_no_idx_of_op _ b.
    clear node_no_idx_of_op.
    clear branch_no_idx_of_op.
    rewrite node_no_idx_rewrite. rewrite node_no_idx_rewrite in nni. destruct node1.
      unfold "⋅", node_op in nni. destruct_ands. split; trivial.
      apply ihb with (b0 := b0). trivial.
  - destruct branch2.
    + have ihb := branch_no_idx_of_op _ branch2.
      have ihn := node_no_idx_of_op _ n.
      clear node_no_idx_of_op.
      clear branch_no_idx_of_op.
      rewrite branch_no_idx_rewrite. rewrite branch_no_idx_rewrite in bni. destruct branch1.
      * unfold "⋅", branch_op in bni. destruct_ands. split; trivial.
        -- apply ihn with (n0 := n0). trivial.
        -- apply ihb with (b := branch1). trivial.
      * unfold "⋅", branch_op in bni. trivial.
    + unfold branch_no_idx. trivial.
Qed.
  
Lemma is_fresh_nat_of_op (a b : Branch M) (i: nat)
  : is_fresh_nat (a ⋅ b) i -> is_fresh_nat b i. 
Proof.
  unfold is_fresh_nat.
  apply branch_no_idx_of_op.
Qed.

End Fresh.
