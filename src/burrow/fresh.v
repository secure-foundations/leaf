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
    + right. intros. have r := H j.
      have u := decide (j = i). destruct u.
        *** solve_decision.
        *** rewrite <- e in H0. lia.
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
    + intros. have r := H x. lia.
    ** contradiction.
Qed.

Lemma exists_fresh_alloc
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
    (branch: Branch M) (ri: RI)
    : ∃ alpha , is_fresh_nat branch (nat_of_extstep alpha ri).
Proof.
  unfold is_fresh_nat.
  assert (∃ alpha : nat, nat_of_extstep alpha ri > branch_max_idx branch 0).
   - apply value_above_bound.
     intros. unfold nat_of_extstep in H.
     have j := encode_nat_inj _ _ H. inversion j. trivial.
   - deex. exists alpha.
     apply branch_no_idx_of_gt_max. trivial.
Qed.

Lemma exists_fresh_alloc_base branch
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
    : ∃ alpha , is_fresh_nat branch
    (nat_of_basestep RI alpha).
Proof.
  unfold is_fresh_nat.
  assert (∃ alpha : nat, nat_of_basestep RI alpha > branch_max_idx branch 0).
   - apply value_above_bound.
     intros. unfold nat_of_extstep in H.
     have j := encode_nat_inj _ _ H. inversion j. trivial.
   - deex. exists alpha.
     apply branch_no_idx_of_gt_max. trivial.
Qed.

Lemma trivial_node_at_fresh (b: Branch M) p i
  (is_fresh: is_fresh_nat b i)
  : node_trivial (node_of_pl b (p, i)).
Proof.
  unfold is_fresh_nat in *.
  enough (node_trivial (node_of_pl b (p, i)) \/ let (p,idx) := (p, i) in node_no_idx (node_of_pl b (p, i)) i idx).
  - destruct H.
    + trivial.
    + unfold node_no_idx in *. destruct (node_of_pl b (p, i)). destruct_ands. contradiction.
  - apply (pl_reverse_induction1_node
    (b)
    (λ pl b , branch_trivial b \/ let (p,idx) := pl in branch_no_idx b i idx)
    (λ pl n , node_trivial n \/ let (p,idx) := pl in node_no_idx n i idx)).
    + right. trivial.
    + intros. inversion H.
      * left. unfold node_trivial in H0. intuition.
      * right. unfold node_no_idx in H0. intuition.
    + intros. inversion H.
      * unfold branch_trivial in H0. intuition.
      * unfold branch_no_idx in H0. intuition.
    + intros. destruct pl. right. unfold branch_no_idx. trivial.
    + intros. left. unfold node_trivial, triv_node, cell_trivial, triv_cell. intuition.
Qed.
  
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
