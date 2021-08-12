From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.rollup.
Require Import Burrow.locations.
Require Import Burrow.indexing.

From stdpp Require Import countable.
From stdpp Require Import gmap.

Section Updog.

Context {M} `{!EqDecision M} `{!TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.

Definition updog (m: M) (gamma: Loc RI) (alpha: nat) (ri: RI) : (PathLoc -> M) :=
  λ (pl: PathLoc) , match pl with | (p, i) =>
        if decide (p ≠ [] /\ (plsplit p) ∈ pls_of_loc gamma /\ i < nat_of_extstep alpha ri) then
          m
        else
          unit
      end.
      
Definition updog_se (gamma: Loc RI) (alpha: nat) (ri: RI) : gset PathLoc. Admitted.

Lemma updog_se_okay (m: M) (gamma: Loc RI) (alpha: nat) (ri: RI)
  : ∀ (p : list nat) (i : nat),
    (p, i) ∉ updog_se gamma alpha ri
    → updog m gamma alpha ri (p, i) = unit.
    Admitted.

Lemma updog_eq_m p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, i)) = m. Admitted.
    
Lemma updog_eq_unit1 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, S i)) = unit. Admitted.
    
Lemma updog_eq_unit2 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p ++ [i], 0)) = unit. Admitted.

(*Lemma updog_base_eq_unit1 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p, i)) = unit. Admitted.
    
Lemma updog_base_eq_unit2 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p, S i)) = unit. Admitted.*)
    
Lemma updog_base_eq_m p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p ++ [i], 0)) = m. Admitted.
    
Lemma updog_other_eq_both p i alpha ri gamma m
  (is_not_in : (p, i) ∉ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, i)) = (updog m gamma alpha ri (p, S i)). Admitted.
    
Lemma updog_other_eq_unit p i alpha ri gamma m
  (is_not_in : (p, i) ∉ pls_of_loc gamma)
    : (updog m gamma alpha ri (p ++ [i], 0)) = unit. Admitted.


Definition updo (m: M) (gamma: Loc RI) (idx: nat) : (PathLoc -> M) :=
  λ (pl: PathLoc) , match pl with | (p, i) =>
        if decide (p ≠ [] /\ (plsplit p) ∈ pls_of_loc gamma /\ i < idx) then
          m
        else
          unit
      end.
 
Definition updo_se (gamma: Loc RI) (idx: nat) : gset PathLoc. Admitted.

Lemma updo_se_okay (m: M) (gamma: Loc RI) (idx: nat)
  : ∀ (p : list nat) (i : nat),
    (p, i) ∉ updo_se gamma idx
    → updo m gamma idx (p, i) = unit.
    Admitted.
  
Lemma updo_eq_m_left p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p, i)) = m. Admitted.
    
Lemma updo_eq_unit_left p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p++[i], 0)) = unit. Admitted.
    
Lemma updo_eq_unit2_left p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p, S i)) = unit. Admitted.
    
Lemma updo_eq_unit3_left p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p++[i], 0)) = unit. Admitted.
     
Lemma updo_eq_m_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p, i)) = m. Admitted.
    
Lemma updo_eq_unit_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p++[i], 0)) = unit. Admitted.
    
Lemma updo_eq_unit2_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p, S i)) = unit. Admitted.
    
Lemma updo_eq_unit3_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p++[i], 0)) = unit. Admitted.

Lemma updo_other_eq_both_left p i gamma1 gamma2 m
  (is_not_in : (p, i) ∉ pls_of_loc_from_left gamma1 gamma2)
  : (updo m gamma1 (nat_of_leftstep RI gamma2) (p, i)) = (updo m gamma1 (nat_of_leftstep RI gamma2) (p, S i)). Admitted.
  
Lemma updo_other_eq_both_right p i gamma1 gamma2 m
  (is_not_in : (p, i) ∉ pls_of_loc_from_right gamma1 gamma2)
  : (updo m gamma2 (nat_of_rightstep RI gamma1) (p, i)) = (updo m gamma2 (nat_of_rightstep RI gamma1) (p, S i)). Admitted.
  
Lemma updo_other_eq_unit p i idx gamma m
  (is_not_in : (p, i) ∉ pls_of_loc gamma)
    : (updo m gamma idx (p ++ [i], 0)) = unit. Admitted.
  
Lemma updo_base_eq_m p i idx gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updo m gamma idx (p ++ [i], 0)) = m. Admitted.

End Updog.
