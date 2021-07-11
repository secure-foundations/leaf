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
Require Import Burrow.indexing.
Require Import Burrow.locations.

Definition live
    {M} `{!EqDecision M, !Countable M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI}
    (loc: Loc RI) (m: M) :=
      StateCon empty_lifetime (build loc (CellCon m empty)).
    
Definition reserved
    {M} `{!EqDecision M, !Countable M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI}
    (lt: Lifetime) (loc: Loc RI) (m:M) :=
      StateCon empty_lifetime (build loc (CellCon unit {[ (lt,m) ]} )).
    
Definition active
    {M} `{!EqDecision M, !Countable M, !TPCM M}
    (lt: Lifetime) : State M :=
      StateCon lt BranchNil.

(****************************************************************)
(****************************************************************)
(****************************************************************)
(****************************************************************)
(* live(gamma, m) dot live(gamma, n) equiv live(gamma, m dot n) *)

Lemma live_dot_live
    {M} `{!EqDecision M, !Countable M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI}
    (gamma: Loc RI) (m1 m2: M)
    : live gamma m1 ⋅ live gamma m2 ≡ live gamma (dot m1 m2).
Proof.
  unfold "≡", state_equiv, live. unfold "⋅", state_op. split.
  - apply empty_add_empty_eq_empty.
  - apply equiv_extensionality_cells. intro.
      setoid_rewrite <- forall_cell_op.
      assert (Decision (pl ∈ pls_of_loc gamma)) by solve_decision.
      unfold Decision in H. destruct H.
      + repeat (rewrite build_spec); trivial. unfold "≡", "⋅", cell_equiv, cell_op.
          split; trivial. set_solver.
      + repeat (rewrite build_rest_triv); trivial.
          unfold triv_cell, "≡", cell_equiv, "⋅", cell_op. split.
          * apply unit_dot. * set_solver.
Qed.
