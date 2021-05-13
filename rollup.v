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
 

Inductive TaggedElement : Type :=
  | Element : forall idx , tpcm_of_index idx -> TaggedElement
  | TEFail : TaggedElement
.

Definition tagged_element_index (te : TaggedElement) : option TPCMIndex :=
  match te with
  | Element i _ => Some i
  | TEFail => None
  end
. 

(* make it total for convenience *)
Definition tagged_element_get (te : TaggedElement) (i : TPCMIndex) : tpcm_of_index i :=
  match te with
  | TEFail => unit
  | Element j m => match decide (i = j) with
    | left ieq =>
      change_type i j ieq m
    | right _ => unit
    end
  end
.

Definition merge_tagged_element (te1 : TaggedElement) (te2 : TaggedElement) : TaggedElement :=
  match tagged_element_index te1, tagged_element_index te2 with
  | None, _ => TEFail
  | Some _, None => TEFail
  | Some i1, Some i2 =>
      match decide (i1 = i2) with
      | left ieq =>
        Element i1 (dot (tagged_element_get te1 i1) (tagged_element_get te2 i1))
      | right _ => TEFail
      end
  end
.

Lemma comm_merge_tagged_element (te1 : TaggedElement) (te2 : TaggedElement) : 
    merge_tagged_element te1 te2 = merge_tagged_element te2 te1.
Proof. 
  unfold merge_tagged_element. destruct (tagged_element_index te1); destruct (tagged_element_index te2); trivial.
  - case_decide.
    + case_decide.
      * rewrite H. rewrite comm. trivial.
      * symmetry in H. contradiction.
    + case_decide.
      * symmetry in H0. contradiction.
      * trivial.
Qed. 

Lemma tagged_element_get_of_element_helper (i : TPCMIndex) (H : i = i) : (match H in (_ = y) return (y = i) with
    | eq_refl => eq_refl
    end) = eq_refl.
Proof using RefinementIndex TPCMIndex base_of_index ref_inst_f refinement_of_index.
apply proof_irrel. Qed.

Lemma tagged_element_get_of_element (i : TPCMIndex) (m : tpcm_of_index i) :
    tagged_element_get (Element i m) i = m.
Proof. 
  unfold tagged_element_get. case_decide.
    * unfold change_type. unfold eq_rect_r.
      unfold eq_rect. unfold eq_sym. rewrite tagged_element_get_of_element_helper . trivial.
    * contradiction. Qed.
  

Lemma assoc_merge_tagged_element (x : TaggedElement) (y : TaggedElement) (z : TaggedElement) :
    merge_tagged_element (merge_tagged_element x y) z =
    merge_tagged_element x (merge_tagged_element y z).
Proof. 
  unfold merge_tagged_element.
    destruct (tagged_element_index x);
    destruct (tagged_element_index y);
    destruct (tagged_element_index z); trivial.
  - case_decide.
    + unfold tagged_element_index. case_decide.
      * case_decide.
        -- case_decide.
          ++ rewrite <- H. repeat (rewrite tagged_element_get_of_element). rewrite assoc. trivial.
          ++ contradiction.
        -- rewrite <- H in H1. contradiction.
      * case_decide; trivial. rewrite H1 in H. contradiction.
    + unfold tagged_element_index. case_decide.
      * case_decide; trivial. contradiction.
      * trivial.
  - case_decide; unfold tagged_element_index; trivial.
Qed.

Inductive BorrowObject : Type :=
  | BorrowO : Lifetime -> Loc -> TaggedElement -> BorrowObject
.

Instance eqdec_te : EqDecision TaggedElement.
  unfold EqDecision.
  intros. unfold Decision. destruct x; destruct y.
    - have h : Decision (idx = idx0).
      + apply eqindex.
      + unfold Decision in h. destruct h.
        * have q : Decision (t = tagged_element_get (Element idx0 t0) idx).
          ++ apply (eqdec_inst idx).
          ++ destruct q.
            ** left. rewrite e0.
                have j : Element idx (tagged_element_get (Element idx0 t0) idx) 
                      = Element idx0 (tagged_element_get (Element idx0 t0) idx0).
                 --- rewrite e. trivial.
                 --- rewrite j. rewrite tagged_element_get_of_element. trivial.
            ** right. intro. rewrite <- H in n. rewrite tagged_element_get_of_element in n. contradiction.
        * right. injection. trivial.
   - right. intro. crush.
   - right. intro. crush.
   - left. trivial. Defined.
   
Instance countable_te : Countable TaggedElement. Admitted.


Instance eqdec_borrow_object : EqDecision BorrowObject. solve_decision. Defined.
Instance countable_borrow_object : Countable BorrowObject. Admitted.

Inductive LifetimeStatus := LSActive | LSFail.

Record AllState : Type := {
  active_lifetimes: gmap nat LifetimeStatus;
  borrows: gset BorrowObject;
  live_objects: gmap Loc TaggedElement;
  reserved_objects: gset (Lifetime * Loc * TaggedElement);
}.
  
Instance opt_tagged_instance : Equiv (option TaggedElement) := λ x y ,
  match x, y with
  | None, None => True
  | None, Some TEFail => False
  | None, Some (Element i m) => m = unit
  | Some TEFail, None => False
  | Some TEFail, Some TEFail => True
  | Some TEFail, Some (Element _ _) => False
  | Some (Element i m), None => m = unit
  | Some (Element i m), Some TEFail => False
  | Some (Element i1 m1), Some (Element i2 m2) => (m1 = unit /\ m2 = unit) \/ x = y
  end
 .
 
Instance opt_gmap_tagged_instance : Equiv (gmap Loc TaggedElement) :=
    λ m1 m2, ∀ i, m1 !! i ≡ m2 !! i.

Instance allstate_equiv : Equiv AllState := λ x y ,
     (active_lifetimes x) = (active_lifetimes y)
  /\ (borrows x) = (borrows y)
  /\ (live_objects x) ≡ (live_objects y)
  /\ (reserved_objects x) = (reserved_objects y).

Print merge.
Definition merge_opt_lifetime_status (x: option LifetimeStatus) (y: option LifetimeStatus) :=
  match x, y with
  | None, m => m
  | Some l, None => Some l
  | Some l, Some m => Some LSFail
  end.
Definition merge_active (x : gmap nat LifetimeStatus) (y : gmap nat LifetimeStatus) :=
  merge merge_opt_lifetime_status x y.
  
Definition merge_borrows (x : gset BorrowObject) (y : gset BorrowObject) :=
  union x y.
  
Definition merge_opt_tagged_element (x: option TaggedElement) (y: option TaggedElement) :=
  match x, y with
  | None, y => y
  | Some t, None => Some t
  | Some t, Some u => Some (merge_tagged_element t u)
  end.
  
Definition merge_live_objects (x : gmap Loc TaggedElement) (y : gmap Loc TaggedElement) :=
  merge merge_opt_tagged_element x y.

Definition merge_reserved_objects
    (x : gset (Lifetime * Loc * TaggedElement))
    (y : gset (Lifetime * Loc * TaggedElement)) := union x y.

Instance alls_op_instance : Op AllState := λ x y,
  {|
    active_liftimes: merge_active (active_lifetimes x) (active_lifetimes y);
    borrows: merge_borrows (borrows x) (borrows y);
  
  
Instance alls_valid_instance : Valid AllState := λ x, True.
Instance alls_pcore_instance : PCore AllState := λ _, None.
  
Definition allstate_ra_mixin : RAMixin AllState.
split. 

Print Proper.
Print relation.


end.
