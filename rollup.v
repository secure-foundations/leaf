From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import CpdtTactics.

From stdpp Require Import gmap.

Section stuff.

Class TPCM (M : Type) `{EqDecision M} :=
{
  valid : M -> bool ;
  dot : M -> M -> M ;
  mov : M -> M -> bool ;
  unit : M ;
  
  valid_monotonic : forall x y , valid (dot x y) -> valid x ;
  unit_valid : valid unit ;
  unit_dot : forall x , dot x unit = x ;
  comm : forall x y , dot x y = dot y x ;
  assoc : forall x y z , dot x (dot y z) = dot (dot x y) z ;
  reflex : forall x , mov x x ;
  trans : forall x y z , mov x y -> mov y z -> mov x z ;
  mov_monotonic : forall x y z ,
      mov x y -> valid (dot x z) -> valid (dot y z) -> mov (dot x z) (dot y z)
}.

Class Refinement R M `{ TPCM R , TPCM M } :=
{
  rel : R -> M -> bool ;
  
  rel_unit : rel unit unit ;
  mov_refines : forall b b' q , mov b b' -> rel b q -> exists q' , rel b' q' /\ mov q q' ;
  rel_self : forall b q q' , rel b q -> rel b q' -> mov q q' ;
}.

Variables TPCMIndex : Type.
Variables RefinementIndex : Type.

Variables tpcm_of_index : TPCMIndex -> Type.
Variables eqdec_inst_f : forall i , EqDecision (tpcm_of_index i).
Instance eqdec_inst i : EqDecision (tpcm_of_index i) := eqdec_inst_f i.
Variables tpcm_inst_f : forall i , TPCM (tpcm_of_index i).
Instance tpcm_inst i : TPCM (tpcm_of_index i) := tpcm_inst_f i.

Variables refinement_of_index : RefinementIndex -> TPCMIndex.
Variables base_of_index : RefinementIndex -> TPCMIndex.
Variables ref_inst_f : forall r ,
    Refinement
      (tpcm_of_index (refinement_of_index r))
      (tpcm_of_index (base_of_index r)).
      
Instance ref_inst r : 
    Refinement
      (tpcm_of_index (refinement_of_index r))
      (tpcm_of_index (base_of_index r)) := ref_inst_f r.
      
Definition L := nat.
      
Inductive Loc :=
  | LBase : L -> TPCMIndex -> Loc
  | LExt : L -> RefinementIndex -> Loc
 .


Instance eqindex : EqDecision TPCMIndex. Admitted.
Instance eqrindex : EqDecision RefinementIndex. Admitted.

Instance eqloc : EqDecision Loc.
solve_decision. Defined.

Instance countableloc : Countable Loc. Admitted.

Definition change_type : forall i1 i2 , i1 = i2 -> tpcm_of_index i2 -> tpcm_of_index i1 :=
  λ (i1 i2 : TPCMIndex) (H : i1 = i2) (X : tpcm_of_index i2),
    eq_rect_r tpcm_of_index X H.

Definition Lifetime := gset nat.
Definition lifetime_intersect (l: Lifetime) (m: Lifetime) := gset_union l m.
Definition lifetime_included (l: Lifetime) (m: Lifetime) := subseteq m l.

Lemma fresh_borrow_inst : ∀ (l : Lifetime) , ∃ b , ∀ t, gset_elem_of t l -> t < b.
Proof.
apply set_ind.
 - by intros ?? ->%leibniz_equiv_iff.
 - exists 0. intro. unfold gset_elem_of.
 Abort.
 
Inductive BorrowObject i : Type :=
  | BorrowO : Lifetime -> Loc -> (tpcm_of_index i) -> BorrowObject i
.

Instance eqdec_borrow_object i : EqDecision (BorrowObject i). solve_decision. Defined.
Instance countable_borrow_object i : Countable (BorrowObject i). Admitted.

Inductive LifetimeStatus := LSNone | LSActive | LSFail.

Record AllState : Type := {
  active_lifetimes: nat -> LifetimeStatus;
  borrows: forall i, BorrowObject i -> bool;
  live_objects: forall i, Loc -> tpcm_of_index i;
  reserved_objects: forall i , Lifetime -> Loc -> tpcm_of_index i -> bool;
}.

Record InvState : Type := {
  locs_in_use: gset Loc;
  max_lt_index: nat; 
  
  ltotal : forall i, Loc -> tpcm_of_index i;
  view: forall i, Loc -> Lifetime -> tpcm_of_index i -> bool ;
}.
  
Instance allstate_equiv : Equiv AllState := λ x y , x = y.

Print merge.
Definition merge_lifetime_status (x: LifetimeStatus) (y: LifetimeStatus) :=
  match x, y with
  | LSNone, m => m
  | LSActive, LSNone => LSActive
  | LSActive, LSActive => LSFail
  | LSActive, LSFail => LSFail
  | LSFail, _ => LSFail
  end.
  
Definition merge_active (x : nat -> LifetimeStatus) (y : nat -> LifetimeStatus) :=
  λ n, merge_lifetime_status (x n) (y n).
  
Definition merge_borrows (x : forall i, BorrowObject i -> bool)
                         (y : forall i, BorrowObject i -> bool) :=
  λ i bo, orb (x i bo) (y i bo).
  
Definition merge_live_objects (x : forall i, Loc -> tpcm_of_index i)
                              (y : forall i, Loc -> tpcm_of_index i) :=
  λ i lo , dot (x i lo) (y i lo).

Definition merge_reserved_objects
    (x : forall i, Lifetime -> Loc -> tpcm_of_index i -> bool)
    (y : forall i, Lifetime -> Loc -> tpcm_of_index i -> bool) :=
  λ i l lo m , orb (x i l lo m) (y i l lo m).

Instance alls_op_instance : Op AllState := λ x y,
  {|
    active_lifetimes := merge_active (active_lifetimes x) (active_lifetimes y);
    borrows := merge_borrows (borrows x) (borrows y);
    live_objects := merge_live_objects (live_objects x) (live_objects y);
    reserved_objects := merge_reserved_objects (reserved_objects x) (reserved_objects y)
  |} .
  
Instance alls_pcore_instance : PCore AllState := λ x,
  Some({|
    active_lifetimes := λ _ , LSNone;
    borrows := borrows x;
    live_objects := λ _ _ , unit;
    reserved_objects := reserved_objects x
  |}) .
  
Definition Live (i: TPCMIndex) (s: AllState) (loc: Loc) :=
    live_objects s i loc.
    
Definition ReservedHere (i: TPCMIndex) (s: AllState) (u: InvState) (loc: Loc) :=
    set_fold (λ l m , dot m (
    
Instance alls_valid_instance : Valid AllState := λ x, True.
  
Definition allstate_ra_mixin : RAMixin AllState.
split. 

Print Proper.
Print relation.


end.
