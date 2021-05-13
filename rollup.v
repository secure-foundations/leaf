From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import CpdtTactics.

From stdpp Require Import gmap.

Section stuff.

(*Inductive Loc : Type :=
  | LBase : nat -> Loc
  | LExt : nat -> Loc -> Loc
 . *)
 
(*Global Instance loc_eq_dec : EqDecision Loc.
Proof. solve_decision. Defined.

Global Instance loc_countable : Countable Loc.
Admitted.*)

Class TPCM (M : Type) :=
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
      
(*Inductive Loc i :=
  | LBase : L -> Loc i
  | LExt : forall r , L -> Loc (base_of_index r) -> refinement_of_index r = i -> Loc i
 . *)
 
Inductive Loc :=
  | LBase : L -> TPCMIndex -> Loc
  | LExt : L -> RefinementIndex -> Loc
 .
 
Inductive Entry :=
  | LocEntry : forall i , Loc -> tpcm_of_index i -> Entry
  | FailEntry
.

Instance eqindex : EqDecision TPCMIndex. Admitted.
Instance eqrindex : EqDecision RefinementIndex. Admitted.

Instance eqloc : EqDecision Loc.
Proof. solve_decision. Admitted.

Instance countableloc : Countable Loc. Admitted.

Definition change_type : forall i1 i2 , i1 = i2 -> tpcm_of_index i2 -> tpcm_of_index i1 :=
  λ (i1 i2 : TPCMIndex) (H : i1 = i2) (X : tpcm_of_index i2),
    eq_rect_r tpcm_of_index X H.


Print change_type.
(* change_type = 
λ (i1 i2 : TPCMIndex) (H : i1 = i2) (X : tpcm_of_index i2),
  (λ _evar_0_ : tpcm_of_index i2,
     eq_rect_r (λ _pattern_value_ : TPCMIndex, tpcm_of_index _pattern_value_) _evar_0_ H) X
*)

Definition loc_entry_merge e1 e2 :=
  match e1, e2 with
  | FailEntry, _ => FailEntry
  | LocEntry _ _ _, FailEntry => FailEntry
  | LocEntry i1 l1 m1, LocEntry i2 l2 m2 =>
      match decide (i1 = i2) with
      | left ieq =>
        if decide (l1 = l2) then
          LocEntry i1 l1 (dot m1 (change_type i1 i2 ieq m2))
        else
          FailEntry
      | right _ => FailEntry
      end
  end
.

Definition Lifetime := gset nat.
Definition lifetime_intersect (l: Lifetime) (m: Lifetime) := gset_union l m.
Definition lifetime_included (l: Lifetime) (m: Lifetime) := subseteq m l.

Lemma fresh_borrow_inst : ∀ (l : Lifetime) , ∃ b , ∀ t, gset_elem_of t l -> t < b.
Proof.
apply set_ind.
 - by intros ?? ->%leibniz_equiv_iff.
 - exists 0. intro. unfold gset_elem_of.
 Abort.
 
(*Print NoDup.
Inductive mymap K V :=
  | mymap_of_list : list (K * V) -> mymap K V
. *)

(*Print FinMap.
Print gmap.
Instance gmap2_finmap `{Countable K} : FinMap K (gmap K).Admitted.

Instance mymap_finmap `{Countable K} : FMap (mymap K).
unfold FMap.



Instance mymap_finmap `{Countable K} : FinMap K (mymap K).

Instance mymap_inst : FinMap K (mymap K).*)
 
(*Inductive Node : Type :=
  | MNode :
    forall i , tpcm_of_index i
        -> gmap Lifetime (tpcm_of_index i)
        -> list ((L * RefinementIndex) * Node) -> Node
  | MFail 
.

Lemma merge_node (n: Node) (m: Node)
  match e1, e2
    MFail, _ => MFail
    MNode _ _ _ _, MFail => MFail
    MNode i1 m1 l1 children1, MNode i2 m2 l2 children2*)


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

Definition tagged_element_merge (te1 : TaggedElement) (te2 : TaggedElement) : TaggedElement :=
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

Lemma comm_tagged_element_merge (te1 : TaggedElement) (te2 : TaggedElement) : 
    tagged_element_merge te1 te2 = tagged_element_merge te2 te1.
Proof. 
  unfold tagged_element_merge. destruct (tagged_element_index te1); destruct (tagged_element_index te2); trivial.
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
  

Lemma assoc_tagged_element_merge (x : TaggedElement) (y : TaggedElement) (z : TaggedElement) :
    tagged_element_merge (tagged_element_merge x y) z =
    tagged_element_merge x (tagged_element_merge y z).
Proof. 
  unfold tagged_element_merge.
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
    

(*
Inductive Loc M :=
  | LBase : nat -> Loc M
  | LExt : forall A `{ TPCM A, Refinement M A } , nat -> Loc A -> Loc M
. 

Inductive Entry :=
  | LocEntry : forall M `{ TPCM M } , M -> Loc M -> Entry
  | Fail : Entry
. 

Definition loc_entry_merge e1 e2 :=
  match e1, e2 with
  | Fail, _ => Fail
  | LocEntry _ _ _, Fail => Fail
  | LocEntry M m l, LocEntry M' m' l' => if M = M' then
      (if l = l' then Fail else Fail) else Fail
  end
 . 
 
Definition Lifetime := Z.




Inductive MonoidElement :=
  Element : forall M: Type, M -> MonoidElement
 . 
  
  

Definition m := gmap Loc MonoidElement.


(*Local Instance frac_valid_instance : Valid frac := λ x, (x ≤ 1)%Qp.
Local Instance frac_pcore_instance : PCore frac := λ _, None.
Local Instance frac_op_instance : Op frac := λ x y, (x + y)%Qp.*)

end.
*)

end.
