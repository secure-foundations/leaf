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

(*Context {M: Type}  `{!EqDecision M, !Countable M}.*)
(*Context `{!EqDecision RefinementIndex}.
Context {refinement_of_index : RefinementIndex -> Refinement M M}.*)

Definition node_of_pl {M} `{!EqDecision M, !Countable M, !TPCM M}
    (branch: Branch M) (pl: PathLoc) : Node M. Admitted.
    
Definition cell_of_pl {M} `{!EqDecision M, !Countable M, !TPCM M}
    (branch: Branch M) (pl: PathLoc) : Cell M := match node_of_pl branch pl with CellNode c _ => c end.
    
Definition every_node {M} `{!EqDecision M, !Countable M, !TPCM M}
    (branch: Branch M) (fn : Node M -> nat -> Prop) : Prop. Admitted.

Lemma every_node_equiv_forall {M} `{!EqDecision M, !Countable M, !TPCM M}
    (branch : Branch M) (fn : Node M -> nat -> Prop)
    (rtriv: ∀ n idx , node_trivial n -> fn n idx)
  : (every_node branch fn) <-> (forall pl , fn (node_of_pl branch pl) (plend pl)). Admitted.

Lemma forall_node_op {M} `{!EqDecision M, !Countable M, !TPCM M}
    (branch1 : Branch M) (branch2 : Branch M)
  : forall pl , (node_of_pl branch1 pl) ⋅ (node_of_pl branch2 pl) ≡ node_of_pl (branch1 ⋅ branch2) pl.
Admitted.

Lemma forall_cell_op {M} `{!EqDecision M, !Countable M, !TPCM M}
    (branch1 : Branch M) (branch2 : Branch M)
  : forall pl , (cell_of_pl branch1 pl) ⋅ (cell_of_pl branch2 pl) ≡ cell_of_pl (branch1 ⋅ branch2) pl.
Admitted.



Lemma equiv_extensionality_cells {M} `{!EqDecision M, !Countable M, !TPCM M}
    (branch1: Branch M) (branch2: Branch M)
    (ext_eq : forall pl , (cell_of_pl branch1 pl) ≡ (cell_of_pl branch2 pl))
    : branch1 ≡ branch2. Admitted.
  
End Indexing.
