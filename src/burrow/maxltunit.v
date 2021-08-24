From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.rollup.
Require Import Burrow.indexing.
Require Import Burrow.gmap_utils.
Require Import Burrow.tactics.

From stdpp Require Import countable.
From stdpp Require Import gmap.

Section MaxLTUnit.

Context {M} `{!EqDecision M} `{!TPCM M}.

Definition listset_max `{EqDecision A} (se : listset A) (fn: A -> nat)
 := (set_fold (λ r k, k `max` fn r) 0 se).

Lemma elem_le_listset_max `{EqDecision A} (se : listset A) (fn: A -> nat) (a: A)
  (in_set : a ∈ se)
  : fn a ≤ listset_max se fn.
Proof.
  unfold listset_max.
  unfold set_fold, "∘".
  assert (a ∈ elements se).
  - rewrite elem_of_elements. trivial.
  - full_generalize (elements se) as l. generalize H. clear H. induction l.
    + intros. inversion H.
    + intros. inversion H.
      * subst. cbn [foldr]. lia.
      * subst. cbn [foldr]. have ih := IHl H2. lia.
Qed.

Definition rmaxltfn := (λ ent : (Lifetime * M) , match ent with (lt, _) => max_ltunit_in_lt lt end).

Definition max_ltunit_in_cell (c: Cell M) : nat :=
  match c with
  | CellCon _ rset => listset_max rset rmaxltfn
  end.

Fixpoint max_ltunit_in_branch (b: Branch M) : nat :=
  match b with
  | BranchCons n b => max_ltunit_in_node n `max` max_ltunit_in_branch b
  | BranchNil => 0
  end
with max_ltunit_in_node (n: Node M) : nat :=
  match n with
  | CellNode c b => max_ltunit_in_cell c `max` max_ltunit_in_branch b
  end
.

Lemma lt_singleton_not_eq_to_cell_lt ltunit b pl
  (isgreater: ltunit > max_ltunit_in_branch b)
  : match cell_of_pl b pl with CellCon _ rset =>
    ∀ r , r ∈ rset -> match r with (lt, _) => ¬(multiset_in lt ltunit) end
    end.
Proof.
  apply (pl_reverse_induction1_node
    (b)
    (λ pl b , ltunit > max_ltunit_in_branch b)
    (λ pl n , 
      match cell_of_node n with CellCon _ rset =>
        ∀ r , r ∈ rset -> match r with (lt, _) => ¬(multiset_in lt ltunit) end
      end
      /\ ltunit > max_ltunit_in_node n
    )).
  - trivial.
  - intros. destruct_ands. cbn [max_ltunit_in_node] in H0. lia.
  - intros. repeat split.
    + cbn [max_ltunit_in_branch] in H. lia.
    + destruct node. unfold cell_of_node. destruct c.
        cbn [max_ltunit_in_branch] in H.
        cbn [max_ltunit_in_node] in H.
        intro. destruct r. intro.
        unfold max_ltunit_in_cell in H.
        assert (rmaxltfn (m0, m1) ≤ listset_max l rmaxltfn) as r.
        * apply elem_le_listset_max. trivial.
        * unfold rmaxltfn in r at 1.
          intro mi.
          have mlilg := max_ltunit_in_lt_ge m0 ltunit mi.
          lia.
    + cbn [max_ltunit_in_branch] in H. lia.
  - intros. simpl. lia.
  - intros. unfold max_ltunit_in_node, triv_node.
      unfold max_ltunit_in_cell, triv_cell.
      unfold listset_max. rewrite set_fold_empty.
      split.
      + unfold cell_of_node. intro. rewrite elem_of_empty. intuition.
      + lia.
Qed.

End MaxLTUnit. 
