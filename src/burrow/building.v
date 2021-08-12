From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Coq.Lists.List.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.gmap_utils.
Require Import Burrow.rollup.
Require Import Burrow.indexing.
Require Import Burrow.locations.

Definition build {RI} `{!EqDecision RI} `{!Countable RI} {M} `{!EqDecision M, !TPCM M}
    (loc: Loc RI) (cell: Cell M) : Branch M. Admitted.
    
Lemma build_spec {RI} `{!EqDecision RI} `{!Countable RI} {M} `{!EqDecision M, !TPCM M}
    (loc: Loc RI) (cell: Cell M)
  : (∀ pl , pl ∈ pls_of_loc loc -> cell_of_pl (build loc cell) pl ≡ cell). Admitted.
  
Lemma build_rest_triv
        {M} `{!EqDecision M, !TPCM M}
        {RI} `{!EqDecision RI, !Countable RI}
    (loc: Loc RI) (cell: Cell M)
  : (∀ pl , ¬(pl ∈ pls_of_loc loc) -> cell_of_pl (build loc cell) pl ≡ triv_cell). Admitted.

Global Instance build_proper
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (loc: Loc RI) : Proper ((≡) ==> (≡)) (build loc). Admitted.

Lemma branch_is_trivial_build_triv_cell
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (loc: Loc RI) : branch_trivial (build loc triv_cell). Admitted.

Lemma build_op
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
    (i: Loc RI) (x y: Cell M) : build i (x ⋅ y) ≡ build i x ⋅ build i y.
Admitted.

Lemma node_of_pl_build_eq
  {M} `{!EqDecision M, !TPCM M}
  {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI} `{!RefinementIndex M RI}
  (pl1 pl2: PathLoc) (loc l1: Loc RI) (c1: Cell M)
  (pl1_in: pl1 ∈ pls_of_loc loc)
  (pl2_in: pl2 ∈ pls_of_loc loc)
  : node_of_pl (build l1 c1) pl1 ≡ node_of_pl (build l1 c1) pl2. Admitted.
