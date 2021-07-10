Require Import Burrow.CpdtTactics.
Require Import Burrow.rollup.

Context {M} `{!EqDecision M, !TPCM M}.
Context `{!EqDecision RefinementIndex}.
Context {refinement_of_index : RefinementIndex -> Refinement M M}.

Definition PathLoc := list nat.

Print Implicit Cell.
Print Node.
Print Implicit Node.

Print Comm.
Print Cell.

Print Implicit Node.

Print Cell.
Print Node.
Print CellNode.
Print Node.
Print EqDecision0.

Definition node_of_loc (node: @Node M) (pl: PathLoc) : Cell := match node with | CellNode cell b => cell end.

Print node_of_loc.

Definition x {A} := list A.

Definition y A := list A.
Print x.
Print y.

Print Node.
Print Cell.

Definition H := TPCM0.
Print Node.
Definition node_of_loc1 (node: Node) (pl: PathLoc) : Cell := match node with | CellNode cell b => cell end.

Print node_of_loc.
