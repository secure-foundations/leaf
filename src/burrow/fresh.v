From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.rollup.
Require Import Burrow.locations.
Require Import Burrow.indexing.

From stdpp Require Import countable.

Section Fresh.

Context {M} `{!EqDecision M} `{!TPCM M}.

Definition is_fresh_nat : Branch M -> nat -> Prop. Admitted.

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
  
Lemma is_fresh_nat_of_op (a b : Branch M) (i: nat)
  : is_fresh_nat (a ⋅ b) i -> is_fresh_nat b i. Admitted.


End Fresh.
