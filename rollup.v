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
 
Inductive BorrowObject : Type :=
  | BorrowO : Lifetime -> Loc -> M -> BorrowObject
.
Instance eqdec_borrow_object : EqDecision BorrowObject. solve_decision. Defined.
Instance countable_borrow_object : Countable BorrowObject. Admitted.

Inductive LifetimeStatus := LSNone | LSActive | LSFail.

Record AllState : Type := {
  active_lifetimes: nat -> LifetimeStatus;
  borrows: BorrowObject -> bool;
  live_objects: Loc -> M;
  reserved_objects: gset BorrowObject;
}.

Record InvState : Type := {
  locs_in_use: gset Loc;
  max_lt_index: nat; 
  
  ltotal : Loc -> M;
  view: Loc -> Lifetime -> M -> Prop ;
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
  
Definition merge_borrows (x y : BorrowObject -> bool) :=
  λ bo, orb (x bo) (y bo).
  
Definition merge_live_objects (x y : Loc -> M) :=
  λ lo , dot (x lo) (y lo).

Definition merge_reserved_objects (x y : (gset (BorrowObject))) :=
  union x y.

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
    live_objects := λ _ , unit;
    reserved_objects := reserved_objects x
  |}) .
  
Definition Live (s: AllState) (loc: Loc) :=
    live_objects s loc.

Definition borrow_object_has_loc (loc: Loc) (bo: BorrowObject) :=
  match bo with
  BorrowO _ loc1 _ => loc = loc1
  end
.
Definition borrow_object_has_loc_dec loc : ∀ bo, Decision (borrow_object_has_loc loc bo). intro. unfold borrow_object_has_loc. destruct bo. solve_decision. Defined.

Definition borrow_object_has_loc_over_lt (loc: Loc) (borrow_lt: Lifetime) (reserve_object: BorrowObject) :=
  match reserve_object with
  BorrowO reserve_lt loc1 _ => loc = loc1 /\ lifetime_included borrow_lt reserve_lt
  end
.
Definition borrow_object_has_loc_over_lt_dec loc borrow_lt : ∀ reserve_object , Decision (borrow_object_has_loc_over_lt loc borrow_lt reserve_object). intro. unfold borrow_object_has_loc_over_lt. destruct reserve_object. solve_decision. Defined.

Definition ReservedHere (s: AllState) (u: InvState) (loc: Loc) :=
    set_fold (λ reserveObject m, (match reserveObject with BorrowO _ _ k => dot m k end))
    unit
    (
      set_filter
          (borrow_object_has_loc loc)
          (borrow_object_has_loc_dec loc)
          (reserved_objects s)
    ).
    
Definition ReservedHereOver (s: AllState) (u: InvState) (loc: Loc) (lt: Lifetime) :=
    set_fold (λ reserveObject m, (match reserveObject with BorrowO _ _ k => dot m k end))
    unit
    (
      set_filter
          (borrow_object_has_loc_over_lt loc lt)
          (borrow_object_has_loc_over_lt_dec loc lt)
          (reserved_objects s)
    ).
    
Definition IsLocExt (l: Loc) (lext: Loc) : Prop :=
  match lext with
  | LBase _ => False
  | LExt _ _ subl => l = subl
  end.
  
Definition is_loc_ext_dec loc : ∀ lext, Decision (IsLocExt loc lext). intro. unfold IsLocExt. destruct lext; solve_decision. Defined.
  
Definition rel_total `{TPCM R, TPCM M} (ref : Refinement R M) (r: R) := match (rel R M ref) r with | Some t => t | None => unit end.

Definition get_ref_idx (loc: Loc) (extloc: Loc) (ile: IsLocExt loc extloc) : RefinementIndex.
unfold IsLocExt in ile. destruct extloc in ile.
  - contradiction.
  - apply r.
Defined.

Definition Project (extloc: Loc) (m: M) : M :=
  match extloc with
  | LBase _ => m (* for totality *)
  | LExt _ ri _ => rel_total (refinement_of_index ri) m
  end
.

Definition fold_over_locs {A}
    (map_fn: Loc -> A)
    (reduce_fn: A -> A -> A)
    (unit_a: A)
    (loc_domain: gset Loc) 
    (base_loc: Loc) : A :=
   set_fold (λ extloc a , reduce_fn a (map_fn extloc))
    unit_a
    (
      set_filter (IsLocExt base_loc) (is_loc_ext_dec base_loc) loc_domain
    ).

Definition FoldProjectTotal (u : InvState) (loc : Loc) :=
  fold_over_locs (λ lext , ltotal u lext) dot unit (locs_in_use u) loc.

Definition Unlive (s: AllState) (u: InvState) (loc: Loc) :=
  dot (ReservedHere s u loc) (FoldProjectTotal u loc).

Definition inv_loc_total_identity (s : AllState) (u : InvState) (loc: Loc) : Prop :=
  (ltotal u loc) = dot (Live s loc) (Unlive s u loc).

Definition umbrella : M -> (M -> Prop) := tpcm_le.

Definition umbrella_unit : (M -> Prop) := λ _ , True.

Definition intersect_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , a m /\ b m.

Definition conjoin_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , ∃ x y , a x /\ b y /\ dot x y = m.

Definition project_umbrella
    (refinement: Refinement M M) (umbrella : M -> Prop) : (M -> Prop) :=
    λ m , ∃ r t , umbrella r /\ (rel M M refinement r = Some t) /\ tpcm_le t m.
  
Definition ProjectFancy (extloc : Loc) (umbrella : M -> Prop) : (M -> Prop) :=
  match extloc with
  | LBase _ => umbrella (* for totality *)
  | LExt _ ri _ => project_umbrella (refinement_of_index ri) umbrella
  end
.

Definition FoldProjectFancyView (u : InvState) (loc : Loc) (lt : Lifetime) :=
  fold_over_locs (λ lext , view u loc lt) conjoin_umbrella umbrella_unit (locs_in_use u) loc.

Definition inv_loc_lt_view_identity (s : AllState) (u : InvState)
    (loc: Loc) (lt: Lifetime) : Prop :=
  (view u loc lt)


  
    
Instance alls_valid_instance : Valid AllState := λ x, True.
  
Definition allstate_ra_mixin : RAMixin AllState.
split. 

Print Proper.
Print relation.*)

