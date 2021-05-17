From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Import gmap_utils.

Section stuff.

Class TPCM (M : Type) `{EqDecision M} :=
{
  valid : M -> Prop ;
  dot : M -> M -> M ;
  mov : M -> M -> Prop ;
  unit : M ;
  
  valid_monotonic : forall x y , valid (dot x y) -> valid x ;
  unit_valid : valid unit ;
  unit_dot : forall x , dot x unit = x ;
  comm : forall x y , dot x y = dot y x ;
  assoc : forall x y z , dot x (dot y z) = dot (dot x y) z ;
  reflex : forall x , mov x x ;
  trans : forall x y z , mov x y -> mov y z -> mov x z ;
  mov_monotonic : forall x y z ,
      mov x y -> valid (dot x z) -> valid (dot y z) /\ mov (dot x z) (dot y z)
}.

Definition tpcm_le `{TPCM M} (a : M) (b : M) := ∃ c , dot a c = b.

Record Refinement R M `{ TPCM R , TPCM M } :=
{
  (*rel : R -> M -> bool ;
  
  rel_valid : forall r m , rel r m -> valid r /\ valid m ;
  rel_unit : rel unit unit ;
  mov_refines : forall b b' q , mov b b' -> rel b q -> exists q' , rel b' q' /\ mov q q' ;
  rel_self : forall b q q' , rel b q -> rel b q' -> mov q q' ;*)
  
  rel : R -> option M ;
  rel_valid_left : forall r m , rel r = Some m -> valid r ;
  rel_valid_right : forall r m , rel r = Some m -> valid m ;
  rel_unit : rel unit = Some unit ;
  mov_refines : forall b b' q , mov b b' -> rel b = Some q -> exists q' , rel b' = Some q' /\ mov q q' ;
}.

Context `{TPCM M}.

Context `{EqDecision RefinementIndex}.
Variables refinement_of_index : RefinementIndex -> Refinement M M.

Definition L := nat.
      
Inductive Loc :=
  | LBase : L -> Loc
  | LExt : L -> RefinementIndex -> Loc -> Loc
 .

Instance eqloc : EqDecision Loc. solve_decision. Defined.

Instance countableloc : Countable Loc. Admitted.

Definition Lifetime := gset nat.
Definition lifetime_intersect (l: Lifetime) (m: Lifetime) := gset_union l m.
Definition lifetime_included (l: Lifetime) (m: Lifetime) := subseteq m l.

Instance lifetime_included_dec l m : Decision (lifetime_included l m). unfold lifetime_included. solve_decision. Defined.

(*Lemma fresh_borrow_inst : ∀ (l : Lifetime) , ∃ b , ∀ t, gset_elem_of t l -> t < b.
Proof.
apply set_ind.
 - by intros ?? ->%leibniz_equiv_iff.
 - exists 0. intro. unfold gset_elem_of.
 Abort.*)
 
(*Inductive BorrowObject : Type :=
  | BorrowO : Lifetime -> Loc -> M -> BorrowObject
.
Instance eqdec_borrow_object : EqDecision BorrowObject. solve_decision. Defined.
Instance countable_borrow_object : Countable BorrowObject. Admitted.*)
 
Inductive BorrowObject : Type :=
  | BorrowO : Lifetime -> M -> BorrowObject
.
Instance eqdec_borrow_object : EqDecision BorrowObject. solve_decision. Defined.
Instance countable_borrow_object : Countable BorrowObject. Admitted.

Inductive LifetimeStatus := LSNone | LSActive | LSFail.

Inductive Cell : Type :=
  | CellCon : M
      -> option RefinementIndex
      -> (BorrowObject -> bool)
      -> gmap nat M
      -> Cell.

Inductive Node: Type :=
  | CellNode : Cell -> Branch -> Node
  | FailNode : Node
with Branch: Type :=
  | BranchCons : nat -> Node -> Branch -> Branch
  | BranchNil : Branch.

Definition gmap_get_or_unit (reserved: gmap nat M) (lu: nat) :=
  match reserved !! lu with
  | Some m => m
  | None => unit
  end.

Definition sum_reserved_over_lifetime (reserved: gmap nat M) (lifetime: Lifetime) :=
  set_fold (λ lu m , dot m (gmap_get_or_unit reserved lu)) unit lifetime.
  
Definition cell_total (cell: Cell) (lifetime: Lifetime) :=
  match cell with
  | CellCon m _ _ reserved => dot m (sum_reserved_over_lifetime reserved lifetime)
  end.

Fixpoint node_total (node: Node) (lifetime: Lifetime) : M :=
  match node with
  | CellNode cell branch => dot (cell_total cell lifetime) (branch_total branch lifetime)
  | FailNode => unit
  end
with branch_total (branch: Branch) (lifetime: Lifetime) : M :=
  match branch with
  | BranchNil => unit
  | BranchCons _ node branch => dot (project (node_total node lifetime)) (branch_total branch lifetime)
  end
.

Definition umbrella : M -> (M -> Prop) := tpcm_le.

Definition umbrella_unit : (M -> Prop) := λ _ , True.

Definition intersect_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , a m /\ b m.

Definition conjoin_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , ∃ x y , a x /\ b y /\ dot x y = m.

Definition project_umbrella
    (refinement: Refinement M M) (umbrella : M -> Prop) : (M -> Prop) :=
    λ m , ∃ r t , umbrella r /\ (rel M M refinement r = Some t) /\ tpcm_le t m.
    
Definition conjoin_reserved_over_lifetime (reserved: gmap nat M) (lifetime: Lifetime) : (M -> Prop) :=
  set_fold (λ lu um , conjoin_umbrella um (umbrella (gmap_get_or_unit reserved lu)))
      umbrella_unit lifetime.

Definition cell_view (cell: Cell) (lifetime: Lifetime) : (M -> Prop) :=
  match cell with
  | CellCon m _ _ reserved => conjoin_reserved_over_lifetime reserved lifetime
  end.

Fixpoint node_view (node: Node) (lifetime: Lifetime) : (M -> Prop) :=
  match node with
  | CellNode cell branch => conjoin_umbrella (cell_view cell lifetime) (branch_view branch lifetime)
  | FailNode => umbrella_unit
  end
with branch_view (branch: Branch) (lifetime: Lifetime) : (M -> Prop) :=
  match branch with
  | BranchNil => umbrella_unit
  | BranchCons _ node branch => conjoin_umbrella (node_view node lifetime) (branch_view branch lifetime)
  end
.

Definition view_sat (umbrella : M -> Prop) (m : M) := umbrella m.

Lemma sum_reserved_over_lifetime_monotonic (g: gmap nat M) (lt1: Lifetime) (lt2: Lifetime)
  (lt1_le_lt2 : subseteq lt1 lt2)
  : tpcm_le
        (sum_reserved_over_lifetime g lt1)
        (sum_reserved_over_lifetime g lt2). Admitted.

Lemma view_sat_reserved_over_lifetime (g: gmap nat M) (lt: Lifetime)
  : view_sat (conjoin_reserved_over_lifetime g lt)
             (sum_reserved_over_lifetime g lt). Admitted.


Lemma cell_view_le_total (cell: Cell) (lt: Lifetime) (active: Lifetime)
    (lt_is_active : lifetime_included active lt)
    : view_sat (cell_view cell lt) (cell_total cell active).
Proof.
  unfold cell_view. destruct cell. unfold cell_total.
    have sub : subseteq lt active.
       - unfold lifetime_included in lt_is_active. trivial.
  - have ineq1 := sum_reserved_over_lifetime_monotonic g lt active sub.
    have ineq2 := view_sat_reserved_over_lifetime g lt.



