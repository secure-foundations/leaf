From iris.prelude Require Import options.
Require Import cpdt.CpdtTactics.
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
  Proper ((≡) ==> (=) ==> (=) ==> (=)) (sum_reserved_over_lifetime_relive).
Proof.
  unfold sum_reserved_over_lifetime_relive.
  unfold Proper, "==>". intros. subst.
  have p := set_fold_proper (=) ((λ (reserved : Lifetime * M) (m : M), dot m (reserved_get_or_unit_relive reserved y0 y1))).
  unfold Proper in p. unfold "==>" in p. 
  eapply p.
  ** typeclasses eauto.
  ** typeclasses eauto.
  ** intros. crush.
  ** intros. rewrite <- tpcm_assoc. rewrite <- tpcm_assoc.
      f_equal. apply tpcm_comm.
  ** trivial.
Qed.

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

Global Instance relive_cell_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) relive_cell.
Proof.
  unfold Proper, "==>". intros. subst. unfold relive_cell. destruct x, y.
  inversion H. setoid_rewrite H1. trivial.
Qed.

Global Instance relive_cell_exc_proper : Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) relive_cell_exc.
Proof.
  unfold Proper, "==>". intros. subst. unfold relive_cell_exc. destruct x, y.
  inversion H. setoid_rewrite H1. trivial.
Qed.

Lemma relive_cell_triv old new
  : triv_cell ≡ relive_cell triv_cell old new.
Proof. trivial. Qed.
  
End Relive.
