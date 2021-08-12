From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.rollup.
Require Import Burrow.indexing.
Require Import Burrow.gmap_utils.

From stdpp Require Import countable.

Section MaxLTUnit.

Context {M} `{!EqDecision M} `{!TPCM M}.

Definition max_ltunit_in_branch (b: Branch M) : nat. Admitted.

Lemma lt_singleton_not_eq_to_cell_lt ltunit b pl
  (isgreater: ltunit > max_ltunit_in_branch b)
  : match cell_of_pl b pl with CellCon _ rset =>
    ∀ r , r ∈ rset -> match r with (lt, _) => ¬(multiset_in lt ltunit) end
    end. Admitted.

End MaxLTUnit. 
