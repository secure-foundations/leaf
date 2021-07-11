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

Definition PathLoc := list nat.

Context {M: Type} `{!EqDecision M, !TPCM M} `{!Countable M}.
Context `{!EqDecision RefinementIndex}.
Context {refinement_of_index : RefinementIndex -> Refinement M M}.

Definition node_of_pl (node: Node M) (pl: PathLoc) : Node M. Admitted.
Definition every_node (node: Node M) (fn : Node M -> Prop) : Prop. Admitted.

Lemma every_node_equiv_forall
    (node : Node M) (fn : Node M -> Prop) (rtriv: ∀ n , node_trivial n -> fn n)
  : (every_node node fn) <-> (forall pl , fn (node_of_pl node pl)). Admitted.

Lemma forall_node_op
    (node1 : Node M) (node2 : Node M)
  : forall pl , (node_of_pl node1 pl) ⋅ (node_of_pl node2 pl) ≡ node_of_pl (node1 ⋅ node2) pl.
Admitted.

Lemma equiv_existentiality_cells
    (node1 : Node M) (node2 : Node M)
  : forall pl , (node_of_pl node
  
