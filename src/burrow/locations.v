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

(*Context {M: Type} `{!EqDecision M, !TPCM M}.
Context `{Countable RefinementIndex}.
Context `{EqDecision RefinementIndex}.
Context (ref_map : RefinementIndex -> Refinement M M).*)

Class RefinementIndex (M: Type) `{!EqDecision M} `{!TPCM M} (RI: Type) := {
    refinement_of : RI -> Refinement M M;
    triv_ri : RI;
    left_ri : RI;
    right_ri : RI;
    pair_up : M -> M -> M;
}.
Global Arguments triv_ri {M}%type_scope {EqDecision0 TPCM0} _ {RefinementIndex}.
Global Arguments left_ri {M}%type_scope {EqDecision0 TPCM0} _ {RefinementIndex}.
Global Arguments right_ri {M}%type_scope {EqDecision0 TPCM0} _ {RefinementIndex}.
Global Arguments pair_up {M}%type_scope {EqDecision0 TPCM0} _%type_scope {RefinementIndex} _ _.

Inductive Loc (RI: Type) `{!EqDecision RI, !Countable RI} :=
  | BaseLoc : nat -> Loc RI
  | ExtLoc : nat -> RI -> Loc RI -> Loc RI
  | CrossLoc : Loc RI -> Loc RI -> Loc RI
.
Arguments BaseLoc _%type_scope {EqDecision0 Countable0} _%nat_scope.
Arguments ExtLoc {RI}%type_scope {EqDecision0 Countable0} _%nat_scope _ _.
Arguments CrossLoc {RI}%type_scope {EqDecision0 Countable0} _ _.

Global Instance loc_eqdec RI `{!EqDecision RI} `{!Countable RI} : EqDecision (Loc RI).
Proof. solve_decision. Defined.

Global Instance loc_countable RI `{!EqDecision RI} `{!Countable RI} : Countable (Loc RI). Admitted.

Inductive StepDesc (RI: Type) `{!EqDecision RI, !Countable RI} :=
  | SDBase : nat -> StepDesc RI
  | SDExt : nat -> RI -> StepDesc RI
  | SDLeft : Loc RI -> StepDesc RI
  | SDRight : Loc RI -> StepDesc RI
.
(*Arguments SDBase {_}%type_scope {EqDecision0 Countable0} _%nat_scope.*)
Arguments SDExt {_}%type_scope {EqDecision0 Countable0} _%nat_scope _.
Arguments SDLeft {_}%type_scope {EqDecision0 Countable0} _.
Arguments SDRight {_}%type_scope {EqDecision0 Countable0} _.

Global Instance stepdesc_eqdec RI `{!EqDecision RI} `{!Countable RI} : EqDecision (StepDesc RI). Proof. solve_decision. Defined.

Global Instance stepdesc_countable RI `{!EqDecision RI} `{!Countable RI} : Countable (StepDesc RI). Admitted.

Definition nat_of_basestep RI `{!EqDecision RI, !Countable RI} (alpha:nat) : nat :=
  encode_nat (SDBase RI alpha).

Definition nat_of_extstep {RI} `{!EqDecision RI, !Countable RI} (alpha:nat) (ri: RI) : nat :=
  encode_nat (SDExt alpha ri).

Definition nat_of_leftstep RI `{!EqDecision RI, !Countable RI} (gamma2: Loc RI) : nat :=
  encode_nat (SDLeft gamma2).

Definition nat_of_rightstep RI `{!EqDecision RI, !Countable RI} (gamma1: Loc RI) : nat :=
  encode_nat (SDRight gamma1).

Fixpoint pls_of_loc {RI} `{!EqDecision RI} `{!Countable RI}
    (loc: Loc RI) : (listset PathLoc).

Definition build {RI} `{!EqDecision RI} `{!Countable RI} {M} `{!EqDecision M, !TPCM M}
    (loc: Loc RI) (cell: Cell M) : Branch M. Admitted.
    
Lemma build_spec {RI} `{!EqDecision RI} `{!Countable RI} {M} `{!EqDecision M, !TPCM M}
    (loc: Loc RI) (cell: Cell M)
  : (∀ pl , pl ∈ pls_of_loc loc -> cell_of_pl (build loc cell) pl = cell). Admitted.
  
Lemma build_rest_triv
        {M} `{!EqDecision M, !TPCM M}
        {RI} `{!EqDecision RI, !Countable RI}
    (loc: Loc RI) (cell: Cell M)
  : (∀ pl , ¬(pl ∈ pls_of_loc loc) -> cell_of_pl (build loc cell) pl = triv_cell). Admitted.

Definition ri_of_nat (RI : Type) `{!EqDecision RI, !Countable RI} : nat -> RI. Admitted.

Definition refinement_of_nat
        M `{!EqDecision M, !TPCM M}
        RI `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
        (idx: nat) : Refinement M M := refinement_of (ri_of_nat RI idx).

Lemma leftproject_le_left
        {M} `{!EqDecision M, !TPCM M}
        {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
        (m1 m2 c : M)
  (rdef: rel_defined M M (refinement_of (left_ri RI)) (dot (pair_up RI m1 m2) c))
  : tpcm_le m1 (rel M M (refinement_of (left_ri RI)) (dot (pair_up RI m1 m2) c)). Admitted.
  
Lemma rightproject_le_right
        {M} `{!EqDecision M, !TPCM M}
        {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
        (m1 m2 c : M)
  (rdef: rel_defined M M (refinement_of (right_ri RI)) (dot (pair_up RI m1 m2) c))
  : tpcm_le m2 (rel M M (refinement_of (right_ri RI)) (dot (pair_up RI m1 m2) c)). Admitted.
(*
Global Instance loc_eqdec : EqDecision Loc.
Proof. solve_decision. Defined.

Global Instance loc_countable : Countable Loc.
Proof.
  set (enc :=
    fix go l :=
      match l with
      | BaseLoc i => GenLeaf (inl i)
      | ExtLoc i ri linner => GenNode 0 [GenLeaf (inr (i, ri)); go linner]
      | CrossLoc l1 l2 => GenNode 1 [go l1; go l2]
      end
  ).
  set (dec :=
    fix go e :=
      match e with
      | GenLeaf (inl i) => BaseLoc i
      | GenNode 0 [GenLeaf (inr (i, ri)); einner] => ExtLoc i ri (go einner)
      | GenNode 1 [e1; e2] => CrossLoc (go e1) (go e2)
      | _ => BaseLoc 0 (* dummy *)
      end
  ).
  refine (inj_countable' enc dec _).
  refine (fix go (e : Loc) {struct e} := _).
  - destruct e as [| | ]; simpl; f_equal; trivial.
Qed.

Inductive ILoc
*)

Global Instance build_proper
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (loc: Loc RI) : Proper ((≡) ==> (≡)) (build loc). Admitted.

Definition pls_of_loc_from_left
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (l r: Loc RI) : gset PathLoc. Admitted.

Definition pls_of_loc_from_right
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (l r: Loc RI) : gset PathLoc. Admitted.

Lemma branch_is_trivial_build_triv_cell
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (loc: Loc RI) : branch_trivial (build loc triv_cell). Admitted.

Lemma build_op
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
    (i: Loc RI) (x y: Cell M) : build i (x ⋅ y) ≡ build i x ⋅ build i y.
Admitted.

Section LocationsLemmas.

Context {M} `{!EqDecision M, !TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.

Definition any_pl_of_loc
    (loc: Loc RI) : PathLoc. Admitted.

Lemma any_pl_of_loc_is_of_loc
  (loc: Loc RI) : any_pl_of_loc loc ∈ pls_of_loc loc. Admitted.

Lemma pl_not_in_of_pl_in_extloc
    pl alpha (ri: RI) gamma
  : pl ∈ pls_of_loc (ExtLoc alpha ri gamma) -> pl ∉ pls_of_loc gamma. Admitted.
  
Lemma refinement_of_nat_eq_refinement_of_of_in_pls_of_loc
    p i alpha ri gamma
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : refinement_of_nat M RI i = refinement_of ri.
    Admitted.

Lemma pl_in_pls_of_loc_extloc
  p i alpha ri (gamma: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma)
  : (p++[i], nat_of_extstep alpha ri) ∈ pls_of_loc (ExtLoc alpha ri gamma).
Admitted.

Lemma pl_in_pls_of_loc_cross_left
  p i (gamma1 gamma2: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma1)
  : (p++[i], nat_of_leftstep RI gamma2) ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Admitted.

Lemma pl_in_pls_of_loc_cross_right
  p i (gamma1 gamma2: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma2)
  : (p++[i], nat_of_rightstep RI gamma1) ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Admitted.

Lemma ri_of_nat_nat_of_extstep
  alpha (ri: RI)
  : (ri_of_nat RI (nat_of_extstep alpha ri) = ri). Admitted.
  
Lemma ri_of_nat_nat_of_leftstep
  (gamma2 : Loc RI)
  : (ri_of_nat RI (nat_of_leftstep RI gamma2)) = left_ri RI. Admitted.
  
Lemma ri_of_nat_nat_of_rightstep
  (gamma1 : Loc RI)
  : (ri_of_nat RI (nat_of_rightstep RI gamma1)) = right_ri RI. Admitted.

Lemma i_value_of_pls_of_loc_ext p i gamma alpha (ri: RI)
  (in_pls: (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
  : i = nat_of_extstep alpha ri. Admitted.
  
Lemma i_value_of_pls_of_base p i alpha
  (in_pls: (p, i) ∈ pls_of_loc (BaseLoc RI alpha))
  : i = nat_of_basestep RI alpha. Admitted.

Lemma ri_of_nat_nat_of_basestep alpha
  : ri_of_nat RI (nat_of_basestep RI alpha) = triv_ri RI. Admitted.
  
Lemma rel_refinement_of_triv_ri_defined (m: M)
  : rel_defined M M (refinement_of (triv_ri RI)) m. Admitted.
  
Lemma rel_refinement_of_triv_ri_eq_unit (m: M)
  : rel M M (refinement_of (triv_ri RI)) m = unit. Admitted.


Lemma pl_not_in_left_of_pl_in_left pl gamma1 gamma2
  : pl ∈ pls_of_loc_from_left gamma1 gamma2 -> pl ∉ pls_of_loc gamma1. Admitted.
  
Lemma pl_not_in_right_of_pl_in_left pl gamma1 gamma2
  : pl ∈ pls_of_loc_from_left gamma1 gamma2 -> pl ∉ pls_of_loc gamma2. Admitted.
  
Lemma pl_not_in_right_of_pl_in_right pl gamma1 gamma2
  : pl ∈ pls_of_loc_from_right gamma1 gamma2 -> pl ∉ pls_of_loc gamma2. Admitted.
  
Lemma pl_not_in_left_of_pl_in_right pl gamma1 gamma2
  : pl ∈ pls_of_loc_from_right gamma1 gamma2 -> pl ∉ pls_of_loc gamma1. Admitted.
  
Lemma pl_in_crossloc_of_pl_in_left pl gamma1 gamma2
  : pl ∈ pls_of_loc_from_left gamma1 gamma2 -> pl ∈ pls_of_loc (CrossLoc gamma1 gamma2). Admitted.
  
Lemma pl_in_crossloc_of_pl_in_right pl gamma1 gamma2
  : pl ∈ pls_of_loc_from_right gamma1 gamma2 -> pl ∈ pls_of_loc (CrossLoc gamma1 gamma2). Admitted.

Lemma y_is_pair_of_rel_defined_refinement_of_left x y
  (rd: rel_defined M M (refinement_of (left_ri RI)) (dot x y))
  : ∃ k1 k2 , y = (pair_up RI k1 k2). Admitted.
  
Lemma y_is_pair_of_rel_defined_refinement_of_right x y
  (rd: rel_defined M M (refinement_of (right_ri RI)) (dot x y))
  : ∃ k1 k2 , y = (pair_up RI k1 k2). Admitted.

Lemma dot_pair_up m1 m2 k1 k2
  : dot (pair_up RI m1 m2) (pair_up RI k1 k2) = pair_up RI (dot m1 k1) (dot m2 k2).
  Admitted.
   
Lemma refinement_of_left_pair_up a b
  : rel M M (refinement_of (left_ri RI)) (pair_up RI a b) = a. Admitted.
  
Lemma refinement_of_right_pair_up a b
  : rel M M (refinement_of (right_ri RI)) (pair_up RI a b) = b. Admitted.

Lemma rel_defined_refinement_of_left_pair_up a b
  (aval: m_valid a)
  (bval: m_valid b)
    : (rel_defined M M (refinement_of (left_ri RI)) (pair_up RI a b)). Admitted.
    
Lemma rel_defined_refinement_of_right_pair_up a b
  (aval: m_valid a)
  (bval: m_valid b)
    : (rel_defined M M (refinement_of (right_ri RI)) (pair_up RI a b)). Admitted.
    
Lemma m_valid_left_of_rel_defined_refinement_of_left_pair_up a b
  (rd: rel_defined M M (refinement_of (left_ri RI)) (pair_up RI a b))
  : m_valid a. Admitted.
  
Lemma m_valid_right_of_rel_defined_refinement_of_left_pair_up a b
  (rd: rel_defined M M (refinement_of (left_ri RI)) (pair_up RI a b))
  : m_valid b. Admitted.
  
Lemma m_valid_left_of_rel_defined_refinement_of_right_pair_up a b
  (rd: rel_defined M M (refinement_of (right_ri RI)) (pair_up RI a b))
  : m_valid a. Admitted.


Lemma i_value_of_pls_of_loc_from_left p i gamma1 gamma2
  (in_pls: (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
  : i = nat_of_leftstep RI gamma2. Admitted.
  
Lemma i_value_of_pls_of_loc_from_right p i gamma1 gamma2
  (in_pls: (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
  : i = nat_of_rightstep RI gamma2. Admitted.

Lemma node_of_pl_build_eq (pl1 pl2: PathLoc) (loc l1: Loc RI) (c1: Cell M)
  (pl1_in: pl1 ∈ pls_of_loc loc)
  (pl2_in: pl2 ∈ pls_of_loc loc)
  : node_of_pl (build l1 c1) pl1 ≡ node_of_pl (build l1 c1) pl2. Admitted.
  
Lemma exists_in_pls_of_loc_from_left gamma1 gamma2
  : ∃ pl, pl ∈ pls_of_loc_from_left gamma1 gamma2. Admitted.
  
Lemma exists_in_pls_of_loc_from_right gamma1 gamma2
  : ∃ pl, pl ∈ pls_of_loc_from_right gamma1 gamma2. Admitted.

Lemma plsplit_in_of_pls_of_loc_from_left gamma1 gamma2 p i
  (pi_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
  : plsplit p ∈ pls_of_loc gamma1. Admitted.
  
Lemma plsplit_in_of_pls_of_loc_from_right gamma1 gamma2 p i
  (pi_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
  : plsplit p ∈ pls_of_loc gamma2. Admitted.
  
Lemma q_eq_pi_of_plsplit_cross (gamma1 gamma2: Loc RI) (q p: list nat) i j
  (q_in: (q, j) ∈ pls_of_loc (CrossLoc gamma1 gamma2) )
  (eq: plsplit q = (p, i))
  : q = p ++ [i]. Admitted.

Lemma pl_not_in_pls_of_loc_cross_from_in_left pl (gamma1 gamma2: Loc RI)
  (pl_in : pl ∈ pls_of_loc gamma1)
  : pl ∉ pls_of_loc (CrossLoc gamma1 gamma2). Admitted.
  
Lemma pl_not_in_pls_of_loc_cross_from_in_right pl (gamma1 gamma2: Loc RI)
  (pl_in : pl ∈ pls_of_loc gamma2)
  : pl ∉ pls_of_loc (CrossLoc gamma1 gamma2). Admitted.

Lemma pl_not_in_pls_of_loc_cross_from_not_in_both pl gamma1 gamma2
  (not_in_l : pl ∉ pls_of_loc_from_left gamma1 gamma2)
  (not_in_r : pl ∉ pls_of_loc_from_right gamma1 gamma2)
        : (pl ∉ pls_of_loc (CrossLoc gamma1 gamma2)). Admitted.

End LocationsLemmas.
