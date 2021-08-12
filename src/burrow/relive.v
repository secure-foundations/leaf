From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.rollup.
Require Import Burrow.locations.
Require Import Burrow.indexing.
Require Import Burrow.gmap_utils.

From stdpp Require Import countable.

Section Relive.

Context {M} `{!EqDecision M} `{!TPCM M}.

Definition reserved_get_or_unit_relive (reserved: Lifetime * M) (old: Lifetime) (new: Lifetime) : M :=
  match reserved with
  | (my_lt, m) => if decide (multiset_le my_lt old /\ ¬ multiset_le my_lt new) then m else unit
  end.

Definition sum_reserved_over_lifetime_relive (reserved: listset (Lifetime * M)) (old: Lifetime) (new: Lifetime) :=
  set_fold (λ reserved m , dot m (reserved_get_or_unit_relive reserved old new)) unit reserved.
  
Global Instance sum_reserved_over_lifetime_relive_proper :
  Proper ((≡) ==> (=) ==> (=) ==> (=)) (sum_reserved_over_lifetime_relive). Admitted.

Definition relive_cell (cell: Cell M) (old: Lifetime) (new: Lifetime) : Cell M :=
  match cell with
  | CellCon m res =>
      CellCon (sum_reserved_over_lifetime_relive res old new) ∅
  end.
  
Definition relive_cell_exc (cell: Cell M) (old: Lifetime) (new: Lifetime) (exc: Lifetime * M)
      : Cell M :=
  match cell with
  | CellCon m res =>
      CellCon (sum_reserved_over_lifetime_relive (res ∖ {[ exc ]}) old new) ∅
  end.

Global Instance relive_cell_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) relive_cell. Admitted.
  
End Relive.
