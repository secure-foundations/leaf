From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import gmap_utils.

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
  mov_onotonic : forall x y z ,
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
  
Definition rel_project `{TPCM R, TPCM M} (ref : Refinement R M) (r: R) :=
    match (rel R M ref) r with | Some t => t | None => unit end.

Definition get_ref (ri: option RefinementIndex) : Refinement M M. Admitted.
 
Definition project (node: Node) (m: M) : M :=
  match node with
  | CellNode (CellCon _ ref _ _) _ => rel_project (get_ref ref) m
  | FailNode => unit
  end
.

Fixpoint node_total (node: Node) (lifetime: Lifetime) : M :=
  match node with
  | CellNode cell branch => dot (cell_total cell lifetime) (branch_total branch lifetime)
  | FailNode => unit
  end
with branch_total (branch: Branch) (lifetime: Lifetime) : M :=
  match branch with
  | BranchNil => unit
  | BranchCons _ node branch => dot (project node (node_total node lifetime)) (branch_total branch lifetime)
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

Definition umbrella_is_closed (umb: M -> Prop) := ∀ a b , umb a -> umb (dot a b).
    
Definition conjoin_reserved_over_lifetime (reserved: gmap nat M) (lifetime: Lifetime) : (M -> Prop) :=
  set_fold (λ lu um , conjoin_umbrella um (umbrella (gmap_get_or_unit reserved lu)))
      umbrella_unit lifetime.

Definition cell_view (cell: Cell) (lifetime: Lifetime) : (M -> Prop) :=
  match cell with
  | CellCon m _ _ reserved => conjoin_reserved_over_lifetime reserved lifetime
  end.

Definition rel_project_fancy (ref : Refinement M M) (um: M -> Prop) :=
    λ x , ∃ a b , tpcm_le a x /\ rel M M ref b = Some a /\ um b.
  
Definition project_fancy (node: Node) (um: M -> Prop) : (M -> Prop) :=
  match node with
  | CellNode (CellCon _ ref _ _) _ => rel_project_fancy (get_ref ref) um
  | FailNode => umbrella_unit
  end
.

Fixpoint node_view (node: Node) (lifetime: Lifetime) : (M -> Prop) :=
  match node with
  | CellNode cell branch => conjoin_umbrella (cell_view cell lifetime) (branch_view branch lifetime)
  | FailNode => umbrella_unit
  end
with branch_view (branch: Branch) (lifetime: Lifetime) : (M -> Prop) :=
  match branch with
  | BranchNil => umbrella_unit
  | BranchCons _ node branch => conjoin_umbrella (project_fancy node (node_view node lifetime)) (branch_view branch lifetime)
  end
.

Definition view_sat (umbrella : M -> Prop) (m : M) := umbrella m.

Lemma self_le_self a : tpcm_le a a.
Proof. unfold tpcm_le. exists unit. rewrite unit_dot. trivial. Qed.

Lemma unit_view_sat_unit : view_sat umbrella_unit unit.
Proof. unfold view_sat. unfold umbrella_unit. trivial. Qed.

Lemma le_add_both_sides a b c : tpcm_le a b -> tpcm_le (dot a c) (dot b c).
Proof.  unfold tpcm_le. intros. destruct H0. exists x. rewrite comm. rewrite assoc.
    rewrite comm in H0. rewrite H0. trivial. Qed.
    
Lemma le_add_right_side a b c : tpcm_le a b -> tpcm_le a (dot b c).
Proof.  unfold tpcm_le. intros. destruct H0. exists (dot x c). rewrite assoc.
    rewrite H0. trivial. Qed.

Lemma umbrella_closed_umbrella_unit : umbrella_is_closed umbrella_unit.
Proof. unfold umbrella_is_closed. unfold umbrella_unit. intros. trivial. Qed.

Lemma umbrella_closed_umbrella a : umbrella_is_closed (umbrella a).
Proof. unfold umbrella_is_closed. unfold umbrella. intros. apply le_add_right_side. trivial.
Qed.

Lemma umbrella_closed_conjoin um1 um2 : umbrella_is_closed um1 -> umbrella_is_closed um2 ->
    umbrella_is_closed (conjoin_umbrella um1 um2).
Proof. unfold umbrella_is_closed. unfold conjoin_umbrella. intros.
  destruct H2. destruct H2. destruct H2. destruct H3. exists x. exists (dot x0 b). split.
    - trivial.
    - split.
      + apply H1. trivial.
      + rewrite <- H4. apply assoc.
Qed.

Lemma sum_reserved_over_lifetime_monotonic (g: gmap nat M) (lt1: Lifetime) (lt2: Lifetime)
  (lt1_le_lt2 : subseteq lt1 lt2)
  : tpcm_le
        (sum_reserved_over_lifetime g lt1)
        (sum_reserved_over_lifetime g lt2).
Proof. unfold sum_reserved_over_lifetime.
  unfold Lifetime in lt1, lt2.
  apply (gset_subset_relate tpcm_le).
  - apply self_le_self.
  - trivial.
  - intros. apply le_add_both_sides. trivial.
  - intros. apply le_add_right_side. trivial.
  - intros. rewrite <- assoc. rewrite <- assoc. f_equal. apply comm.
Qed.

Lemma view_sat_reserved_over_lifetime (g: gmap nat M) (lt: Lifetime)
  : view_sat (conjoin_reserved_over_lifetime g lt)
             (sum_reserved_over_lifetime g lt).
Proof.
  unfold conjoin_reserved_over_lifetime, sum_reserved_over_lifetime.
  apply (gset_relate view_sat).
  - apply unit_view_sat_unit.
  - intros. unfold view_sat in *. unfold conjoin_umbrella.
      exists c. exists (gmap_get_or_unit g a). repeat split.
    + trivial.
    + unfold umbrella. apply self_le_self.
Qed.

Lemma view_sat_with_le (umb: M -> Prop) (a : M) (b : M)
    (closed: umbrella_is_closed umb)
    (vs: view_sat umb a)
    (mle: tpcm_le a b) : view_sat umb b.
Proof. unfold view_sat in *. intros. unfold umbrella_is_closed in closed.
    unfold tpcm_le in mle. destruct mle. rewrite <- H0. apply closed. trivial.
Qed.

Lemma conjoin_reserved_over_lifetime_is_closed (reserved: gmap nat M) (lt: Lifetime)
    : umbrella_is_closed (conjoin_reserved_over_lifetime reserved lt).
Proof. unfold cell_view. unfold conjoin_reserved_over_lifetime.
  apply (gset_easy_induct umbrella_is_closed).
  - apply umbrella_closed_umbrella_unit.
  - intros. apply umbrella_closed_conjoin.
    + trivial.
    + apply umbrella_closed_umbrella.
Qed.

Lemma cell_view_le_total (cell: Cell) (lt: Lifetime) (active: Lifetime)
    (lt_is_active : lifetime_included active lt)
    : view_sat (cell_view cell lt) (cell_total cell active).
Proof.
  unfold cell_view. destruct cell. unfold cell_total.
    apply view_sat_with_le with (a := (sum_reserved_over_lifetime g lt)).
    + apply conjoin_reserved_over_lifetime_is_closed.
    + apply view_sat_reserved_over_lifetime.
    + rewrite comm. apply le_add_right_side.
        apply sum_reserved_over_lifetime_monotonic.
        unfold lifetime_included in lt_is_active. trivial.
Qed.

Lemma view_sat_conjoin (um1 um2 : M -> Prop) (m1 m2 : M)
    (vs1: view_sat um1 m1)
    (vs2: view_sat um2 m2)
    : view_sat (conjoin_umbrella um1 um2) (dot m1 m2).
Proof. unfold view_sat in *. unfold conjoin_umbrella. exists m1. exists m2. repeat split; trivial. Qed.

Definition in_refinement_domain (ref: Refinement M M) (m : M) :=
  match rel M M ref m with | Some _ => True | None => False end.

Fixpoint node_all_total_in_refinement_domain (node: Node) (lifetime: Lifetime) : Prop :=
  match node with
  | CellNode (CellCon _ ref _ _) branch =>
         in_refinement_domain (get_ref ref) (node_total node lifetime)
      /\ branch_all_total_in_refinement_domain branch lifetime
  | FailNode => false
  end
with branch_all_total_in_refinement_domain (branch: Branch) (lifetime: Lifetime) : Prop :=
  match branch with
  | BranchNil => True
  | BranchCons _ node branch =>
         node_all_total_in_refinement_domain node lifetime
      /\ branch_all_total_in_refinement_domain branch lifetime
  end
.

Definition view_sat_projections (ref: Refinement M M) (view : M -> Prop) (m : M)
    (vrv : in_refinement_domain ref m)
    (vs: view_sat view m)
      : view_sat
        (rel_project_fancy ref view) (*(node_view (CellNode (CellCon m o b0 g) b) lt))*)
        (rel_project       ref m). (*(node_total (CellNode (CellCon m o b0 g) b) active))*)
Proof. 
  unfold rel_project_fancy. unfold rel_project. unfold view_sat. unfold tpcm_le.
  exists (match rel M M ref m with | Some t => t | None => unit end).
  exists m.
  repeat split.
  - exists unit. apply unit_dot.
  - unfold in_refinement_domain in vrv. destruct (rel M M ref m).
    + trivial.
    + contradiction.
  - unfold view_sat in vs. trivial.
Qed.

Lemma node_view_le_total (node: Node) (lt: Lifetime) (active: Lifetime)
    (lt_is_active : lifetime_included active lt)
    (ird: node_all_total_in_refinement_domain node active)
    : view_sat (node_view node lt) (node_total node active)
with branch_view_le_total (branch: Branch) (lt: Lifetime) (active: Lifetime)
    (lt_is_active : lifetime_included active lt)
    (ird: branch_all_total_in_refinement_domain branch active)
    : view_sat (branch_view branch lt) (branch_total branch active).
Proof.
 - destruct node.
      + unfold node_view. unfold node_total. apply view_sat_conjoin.
        * apply cell_view_le_total. trivial.
        * apply branch_view_le_total; trivial.
          unfold node_all_total_in_refinement_domain in ird.
              fold branch_all_total_in_refinement_domain in ird.
              destruct c in ird. destruct ird. trivial.
      + unfold node_view. unfold node_total. apply unit_view_sat_unit.
 - destruct branch.
      + unfold branch_view. unfold branch_total. apply view_sat_conjoin.
        * fold node_view. fold node_total.
            unfold project_fancy. unfold project.
            (* instantiate inductive hypotheses here, so the prover can 
               infer decreasing arguments *)
            have ind_node := node_view_le_total n0. clear node_view_le_total.
            have ind_branch := branch_view_le_total branch. clear branch_view_le_total.
            destruct n0.
          -- destruct c. apply view_sat_projections.
              ++ unfold branch_all_total_in_refinement_domain in ird. destruct ird.
                  destruct H0. trivial.
              ++ apply ind_node; trivial. 
                  unfold branch_all_total_in_refinement_domain in ird. crush.
          -- apply unit_view_sat_unit.
        * apply branch_view_le_total; trivial.
            unfold branch_all_total_in_refinement_domain in ird. crush.
      + unfold view_sat, branch_view, branch_total. unfold umbrella_unit. trivial.
Qed.

Definition cell_trivial (cell: Cell) :=
  match cell with
  | CellCon m _ borrows reserves => (∀ b , borrows b = false) /\ reserves = empty /\ m = unit
  end
.

Fixpoint node_trivial (node: Node) :=
  match node with
  | CellNode cell branch => cell_trivial cell /\ branch_trivial branch
  | FailNode => False
  end
with branch_trivial (branch: Branch) :=
  match branch with
  | BranchNil => True
  | BranchCons _ node branch => node_trivial node /\ branch_trivial branch
  end
.

Fixpoint node_equiv (node1: Node) (node2: Node) :=
  match node1, node2 with
    | FailNode, FailNode => True
    | FailNode, CellNode _ _ => False
    | CellNode _ _, FailNode => False
    | CellNode cell1 branch1, CellNode cell2 branch2 =>
           cell1 = cell2
        /\ branch_equiv branch1 branch2
  end
with branch_equiv (branch1: Branch) : Branch -> Prop :=
  fix inner_branch_equiv (branch2: Branch) :=
    match branch1 with
      | BranchNil => branch_trivial branch2
      | BranchCons id1 n1 br1 =>
          match branch2 with
          | BranchNil => branch_trivial branch1
          | BranchCons id2 n2 br2 =>
               ((id1 = id2) /\ node_equiv n1 n2 /\ branch_equiv br1 br2)
            \/ (node_trivial n1 /\ branch_equiv br1 branch2)
            \/ (node_trivial n2 /\ inner_branch_equiv br2)
          end
    end
.

Instance inst_node_equiv : Equiv Node := node_equiv.

Inductive State :=
  | StateCon : Lifetime -> Node -> State
  | StateFail
.

