From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.

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
  refl : forall x , mov x x ;
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

Definition change_type : forall i1 i2 , i1 = i2 -> tpcm_of_index i2 -> tpcm_of_index i1.
Proof. intros. rewrite H. trivial. Defined.

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
 
Print NoDup.
Inductive mymap K V :=
  | mymap_of_list : list (K * V) -> mymap K V
. 

(*Print FinMap.
Print gmap.
Instance gmap2_finmap `{Countable K} : FinMap K (gmap K).Admitted.

Instance mymap_finmap `{Countable K} : FMap (mymap K).
unfold FMap.



Instance mymap_finmap `{Countable K} : FinMap K (mymap K).

Instance mymap_inst : FinMap K (mymap K).*)
 
Inductive Node : Type :=
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
    MNode i1 m1 l1 children1, MNode i2 m2 l2 children2


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
