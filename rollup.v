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
      
(*Inductive Loc :=
  | LBase : L -> Loc
  | LExt : L -> RefinementIndex -> Loc -> Loc
 .

Instance eqloc : EqDecision Loc. solve_decision. Defined.

Instance countableloc : Countable Loc. Admitted.*)

(*Inductive PathId :=
  | NormalId : nat -> PathId.

Definition id_lt (p1: PathId) (p2: PathId) : bool :=
  match p1, p2 with
  | NormalId id1, NormalId id2 => id1 <? id2
  end.

Inductive Trichotomy :=
  | TrichFirstLtSecond : Trichotomy
  | TrichSecondLtFirst : Trichotomy
  | TrichEq : Trichotomy
.

Definition path_id_trichotomy (p1: PathId) (p2: PathId) : Trichotomy :=
  if id_lt p1 p2 then TrichFirstLtSecond
  else if id_lt p2 p1 then TrichSecondLtFirst
  else TrichEq.*)

(*Definition path_id_trichotomy (p1: PathId) (p2: PathId) :
    (id_lt p1 p2 \/ id_lt p2 p1) \/ p1 = p2.
Proof.
  destruct p1, p2. unfold id_lt.
  have j : (NormalId n = NormalId n0) <-> n = n0.
   - split; crush.
   - rewrite j. lia.
Defined.*)

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

(*Inductive LifetimeStatus := LSNone | LSActive | LSFail.*)

Inductive RI :=
  | TrivialRI : RI
  | NormalRI : RefinementIndex -> RI.

Definition nat_to_ref: nat -> Refinement M M. Admitted.
  
Instance eqdec_ri: EqDecision RI. solve_decision. Defined.

Inductive Cell : Type :=
  | CellCon :
      M ->
      (*RI ->*)
      (BorrowObject -> bool) ->
      gmap nat (option M) ->
          Cell.

Inductive Node: Type :=
  | CellNode : Cell -> Branch -> Node
with Branch: Type :=
  | BranchCons : Node -> Branch -> Branch
  | BranchNil : Branch.

Definition gmap_get_or_unit (reserved: gmap nat (option M)) (lu: nat) :=
  match reserved !! lu with
  | Some (Some m) => m
  | Some None => unit
  | None => unit
  end.
  
Definition sum_reserved_over_lifetime (reserved: gmap nat (option M)) (lifetime: Lifetime) :=
  set_fold (λ lu m , dot m (gmap_get_or_unit reserved lu)) unit lifetime.
  
Definition cell_total (cell: Cell) (lifetime: Lifetime) :=
  match cell with
  | CellCon m _ reserved => dot m (sum_reserved_over_lifetime reserved lifetime)
  end.
  
Definition rel_project `{TPCM R, TPCM M} (ref : Refinement R M) (r: R) :=
    match (rel R M ref) r with | Some t => t | None => unit end.

Definition get_ref (ri: RI) : Refinement M M. Admitted.
 
Definition project (idx: nat) (m: M) : M :=
  rel_project (nat_to_ref idx) m
.

Fixpoint node_total (node: Node) (lifetime: Lifetime) : M :=
  match node with
  | CellNode cell branch => dot (cell_total cell lifetime) (branch_total branch lifetime 0)
  end
with branch_total (branch: Branch) (lifetime: Lifetime) (idx: nat) : M :=
  match branch with
  | BranchNil => unit
  | BranchCons node branch => dot (project idx (node_total node lifetime))
      (branch_total branch lifetime (S idx))
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
    
Definition conjoin_reserved_over_lifetime (reserved: gmap nat (option M)) (lifetime: Lifetime) : (M -> Prop) :=
  set_fold (λ lu um , conjoin_umbrella um (umbrella (gmap_get_or_unit reserved lu)))
      umbrella_unit lifetime.

Definition cell_view (cell: Cell) (lifetime: Lifetime) : (M -> Prop) :=
  match cell with
  | CellCon m _ reserved => conjoin_reserved_over_lifetime reserved lifetime
  end.

Definition rel_project_fancy (ref : Refinement M M) (um: M -> Prop) :=
    λ x , ∃ a b , tpcm_le a x /\ rel M M ref b = Some a /\ um b.
  
Definition project_fancy (idx: nat) (um: M -> Prop) : (M -> Prop) :=
  rel_project_fancy (nat_to_ref idx) um
.

Fixpoint node_view (node: Node) (lifetime: Lifetime) : (M -> Prop) :=
  match node with
  | CellNode cell branch => conjoin_umbrella (cell_view cell lifetime) (branch_view branch lifetime 0)
  end
with branch_view (branch: Branch) (lifetime: Lifetime) (idx: nat) : (M -> Prop) :=
  match branch with
  | BranchNil => umbrella_unit
  | BranchCons node branch => conjoin_umbrella (project_fancy idx (node_view node lifetime)) (branch_view branch lifetime (S idx))
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

Lemma sum_reserved_over_lifetime_monotonic (g: gmap nat (option M)) (lt1: Lifetime) (lt2: Lifetime)
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

Lemma view_sat_reserved_over_lifetime (g: gmap nat (option M)) (lt: Lifetime)
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

Lemma conjoin_reserved_over_lifetime_is_closed (reserved: gmap nat (option M)) (lt: Lifetime)
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

Fixpoint node_all_total_in_refinement_domain (node: Node) (lifetime: Lifetime) (idx: nat) : Prop :=
  match node with
  | CellNode (CellCon _ _ _) branch =>
         in_refinement_domain (nat_to_ref idx) (node_total node lifetime)
      /\ branch_all_total_in_refinement_domain branch lifetime 0
  end
with branch_all_total_in_refinement_domain (branch: Branch) (lifetime: Lifetime) (idx: nat) : Prop :=
  match branch with
  | BranchNil => True
  | BranchCons node branch =>
         node_all_total_in_refinement_domain node lifetime idx
      /\ branch_all_total_in_refinement_domain branch lifetime (S idx)
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

Lemma node_view_le_total (node: Node) (lt: Lifetime) (active: Lifetime) (idx: nat)
    (lt_is_active : lifetime_included active lt)
    (ird: node_all_total_in_refinement_domain node active idx)
    : view_sat (node_view node lt) (node_total node active)
with branch_view_le_total (branch: Branch) (lt: Lifetime) (active: Lifetime) (idx: nat)
    (lt_is_active : lifetime_included active lt)
    (ird: branch_all_total_in_refinement_domain branch active idx)
    : view_sat (branch_view branch lt idx) (branch_total branch active idx).
Proof.
 - destruct node.
      + unfold node_view. unfold node_total. apply view_sat_conjoin.
        * apply cell_view_le_total. trivial.
        * apply branch_view_le_total; trivial.
          unfold node_all_total_in_refinement_domain in ird.
              fold branch_all_total_in_refinement_domain in ird.
              destruct c in ird. destruct ird. trivial.
 - destruct branch.
      + unfold branch_view. unfold branch_total. apply view_sat_conjoin.
        * fold node_view. fold node_total.
            unfold project_fancy. unfold project.
            (* instantiate inductive hypotheses here, so the prover can 
               infer decreasing arguments *)
            have ind_node := node_view_le_total n. clear node_view_le_total.
            have ind_branch := branch_view_le_total branch. clear branch_view_le_total.
            destruct n.
          -- destruct c. apply view_sat_projections.
              ++ unfold branch_all_total_in_refinement_domain in ird. destruct ird.
                  destruct H0. trivial.
              ++ apply ind_node with (idx := idx); trivial. 
                  unfold branch_all_total_in_refinement_domain in ird. crush.
        * apply branch_view_le_total; trivial.
            unfold branch_all_total_in_refinement_domain in ird. crush.
      + unfold view_sat, branch_view, branch_total. unfold umbrella_unit. trivial.
Qed.

Fixpoint node_borrows_valid (node: Node) : Prop :=
  match node with
  | CellNode cell branch =>
    branch_borrows_valid branch
    /\ match cell with
    | CellCon _ borrows _ =>
      ∀ b , borrows b ->
        match b with
          | BorrowO lt m => node_view node lt m
        end
     end
  end
with branch_borrows_valid (branch: Branch) : Prop :=
  match branch with
  | BranchCons node branch => node_borrows_valid node /\ node_borrows_valid node
  | BranchNil => True
  end
.

Fixpoint node_reserved_valid (node: Node) : Prop :=
  match node with
  | CellNode cell branch =>
    branch_reserved_valid branch
    /\ match cell with
      | CellCon _ _ reserved =>
        ∀ r , match reserved !! r with
          | None => True
          | Some None => False
          | Some (Some _) => True
        end
       end
  end
with branch_reserved_valid (branch: Branch) : Prop :=
  match branch with
  | BranchCons node branch => node_reserved_valid node /\ node_reserved_valid node
  | BranchNil => True
  end
.



Definition cell_trivial (cell: Cell) :=
  match cell with
  | CellCon m borrows reserves => (∀ b , borrows b = false) /\ reserves = empty /\ m = unit
  end
.

Fixpoint node_trivial (node: Node) :=
  match node with
  | CellNode cell branch => cell_trivial cell /\ branch_trivial branch
  end
with branch_trivial (branch: Branch) :=
  match branch with
  | BranchNil => True
  | BranchCons node branch => node_trivial node /\ branch_trivial branch
  end
.

Definition equiv_func {A} {B} (f g: A -> B) := ∀ x , f x = g x.

Definition cell_equiv (cell1: Cell) (cell2: Cell) :=
  match cell1, cell2 with
  | CellCon m1 b1 g1, CellCon m2 b2 g2 =>
      (m1 = m2) /\ equiv_func b1 b2 /\ g1 = g2
  end
.

Fixpoint node_equiv (node1: Node) (node2: Node) :=
  match node1, node2 with
    | CellNode cell1 branch1, CellNode cell2 branch2 =>
           cell_equiv cell1 cell2
        /\ branch_equiv branch1 branch2
  end
with branch_equiv (branch1: Branch) (branch2: Branch) :=
    match branch1, branch2 with
      | BranchNil, _ => branch_trivial branch2
      | BranchCons _ _, BranchNil => branch_trivial branch1
      | BranchCons n1 b1, BranchCons n2 b2 =>
          node_equiv n1 n2 /\ branch_equiv b1 b2
  end 
.

(*Definition cell_core (cell: Cell) : Cell :=
  match cell with
  | CellCon m borrows reserved => CellCon unit borrows reserved
  end.

Fixpoint node_core (node: Node) : Node :=
  match node with
  | CellNode cell branch => CellNode (cell_core cell) (branch_core branch)
  end
with branch_core (branch: Branch) : Branch :=
  match branch with
  | BranchNil => BranchNil
  | BranchCons node branch => BranchCons (node_core node) (branch_core branch)
  end
.*)

Instance inst_node_equiv : Equiv Node := node_equiv.

Inductive State :=
  | StateCon : Lifetime -> Node -> State
  | StateFail
.


(*Definition cell_basic_valid (cell: Cell) : Prop :=
  match cell with
  | CellCon _ _ reserved => forall x ,
      match reserved !! x
      with
      | Some None => False
      | Some (Some _) => True
      | None => True
      end
  end
.

Fixpoint node_basic_valid (node: Node) : Prop :=
  match node with
  | CellNode cell branch -> cell_basic_valid cell /\ branch_basic_valid branch
  | *)

(*Instance state_pcore : PCore State := λ state , 
  match state with
  | StateFail => Some StateFail
  | StateCon lt node => Some (StateCon empty (node_core node))
  end
.*)

Instance state_pcore : PCore State := λ state , None.

Definition bool_or_func {A} (x y : A -> bool) : (A -> bool) :=
  λ b , orb (x b) (y b).

Definition rmerge_one (a: option (option M)) (b: option (option M)) :=
  match a, b with
  | None, _ => b
  | Some m, None => Some m
  | Some None, Some _ => Some None
  | Some (Some _), Some None => Some None
  | Some (Some m), Some (Some p) => if decide (m = p) then Some (Some m) else Some None
  end.
Instance rmerge_one_diagnone : DiagNone rmerge_one. unfold DiagNone. unfold rmerge_one. trivial. Defined.
Definition rmerge (f: gmap nat (option M)) (g: gmap nat (option M)) :=
  merge rmerge_one f g.

Definition cell_op (x: Cell) (y: Cell) : Cell :=
  match x, y with
  | CellCon m1 borrows1 reserved1,
    CellCon m2 borrows2 reserved2 =>
      CellCon (dot m1 m2)
              (bool_or_func borrows1 borrows2)
              (rmerge reserved1 reserved2)
  end
.

Fixpoint node_op (x: Node) (y: Node) : Node :=
  match x, y with
  | CellNode cell1 branch1, CellNode cell2 branch2 =>
      CellNode (cell_op cell1 cell2) (branch_op branch1 branch2)
  end 
with branch_op (branch1: Branch) (branch2: Branch) : Branch :=
    match branch1, branch2 with
    | BranchNil, _ => branch2
    | BranchCons _ _, BranchNil => branch1
    | BranchCons n1 subbranch1 , BranchCons n2 subbranch2 =>
        BranchCons (node_op n1 n2) (branch_op subbranch1 subbranch2)
    end
.

Instance state_op : Op State := λ x y ,
  match x, y with
  | StateFail, _ => StateFail
  | StateCon _ _, StateFail => StateFail
  | StateCon active1 node1, StateCon active2 node2 =>
    match decide (active1 ∩ active2 = empty) with
      | left _ => StateCon (active1 ∪ active2) (node_op node1 node2)
      | right _ => StateFail
    end
  end.
  
Instance state_equiv : Equiv State := λ x y ,
  match x, y with
  | StateFail, StateFail => True
  | StateFail, StateCon _ _ => False
  | StateCon _ _, StateFail => False
  | StateCon lt1 node1, StateCon lt2 node2 =>
      (lt1 = lt2 /\ node1 ≡ node2)
  end.
  
Lemma equiv_rmerge_emptyset (g: gmap nat (option M)) :
     (rmerge g ∅) = g.
Proof. unfold rmerge. apply map_eq. intros. rewrite lookup_merge. rewrite lookup_empty.
    unfold rmerge_one. destruct (g !! i); trivial. destruct o; trivial.
Qed.

Lemma equiv_refl_cell (cell: Cell) : cell_equiv cell cell.
Proof. destruct cell. unfold cell_equiv. repeat split. Qed.
    
Lemma equiv_refl_node (node: Node) : node_equiv node node
with equiv_refl_branch (branch: Branch) : branch_equiv branch branch.
 - destruct node. unfold node_equiv. repeat split.
  + apply equiv_refl_cell.
  + apply equiv_refl_branch.
 - destruct branch.
  + unfold branch_equiv. repeat split.
    * apply equiv_refl_node.
    * apply equiv_refl_branch.
  + unfold branch_equiv. unfold branch_trivial. trivial.
Qed.

Lemma op_trivial_node (node1: Node) (node2: Node)
  (istriv: node_trivial node2) : (node_equiv (node_op node1 node2) node1)
with op_trivial_branch (branch1: Branch) (branch2: Branch)
  (istriv: branch_trivial branch2) : (branch_equiv (branch_op branch1 branch2) branch1).
Proof.
  - destruct node1; destruct node2.
    + have hyp := op_trivial_branch b b0. clear op_trivial_node. clear op_trivial_branch.
    unfold node_op. fold branch_op. destruct c. destruct c0.
        unfold node_equiv. fold branch_equiv. unfold cell_op. unfold cell_equiv.
            unfold node_trivial in istriv. fold branch_trivial in istriv.
            destruct istriv. unfold cell_trivial in *. destruct H0. destruct H2. repeat split.
        -- rewrite H3. apply unit_dot.
        -- unfold equiv_func, bool_or_func. crush.
        -- rewrite H2. apply equiv_rmerge_emptyset.
        -- apply hyp; trivial.
  - destruct branch1; destruct branch2.
    + have hyp_branch := op_trivial_branch branch1 branch2. clear hyp_branch.
      have hyp_node := op_trivial_node n n0. clear hyp_node.
      crush.
    + crush.
      * apply equiv_refl_node.
      * apply equiv_refl_branch.
    + crush.
    + crush.
Qed.

Lemma cell_equiv_comm (cell1: Cell) (cell2: Cell)
  (iseq: cell_equiv cell1 cell2) : (cell_equiv cell2 cell1).
Proof. unfold cell_equiv in *. destruct cell1, cell2. destruct iseq. destruct H1. repeat split.
  * symmetry; trivial.  * unfold equiv_func in *. intros. symmetry. apply H1.
  * symmetry; trivial.
Qed.

Lemma node_equiv_comm (node1: Node) (node2: Node)
  (iseq: node_equiv node1 node2) : (node_equiv node2 node1)
with branch_equiv_comm (branch1: Branch) (branch2: Branch)
  (iseq: branch_equiv branch1 branch2) : (branch_equiv branch2 branch1).
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_equiv_comm b b0. clear node_equiv_comm. clear branch_equiv_comm.
        unfold node_equiv. fold branch_equiv. repeat split.
        * apply cell_equiv_comm. unfold node_equiv in iseq. destruct iseq; trivial.
        * unfold node_equiv in iseq. destruct iseq. apply ind_hyp; trivial.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_equiv_comm branch1 branch2.
      have ind_hyp_node := node_equiv_comm n n0.
      unfold branch_equiv in *. fold node_equiv in *. fold branch_equiv in *. split.
        * apply ind_hyp_node. destruct iseq; trivial.
        * apply ind_hyp_branch. destruct iseq; trivial.
    + unfold branch_equiv in *. trivial.
    + unfold branch_equiv in *. trivial.
    + trivial.
Qed.

Lemma cell_op_equiv (c c0 c1 : Cell)
  (eq1: cell_equiv c0 c1)
  : (cell_equiv (cell_op c c0) (cell_op c c1)).
Proof.
  destruct c0, c1, c. unfold cell_op. unfold cell_equiv in *. destruct eq1.
      destruct H1. repeat split.
  + rewrite H0. trivial.
  + unfold equiv_func in *. unfold bool_or_func. crush.
  + rewrite H2. trivial.
Qed.

Lemma node_op_equiv (nodeLeft: Node) (nodeRight1 : Node) (nodeRight2: Node)
    (node_eq: node_equiv nodeRight1 nodeRight2)
    : (node_equiv (node_op nodeLeft nodeRight1) (node_op nodeLeft nodeRight2))
with branch_op_equiv (branchLeft: Branch) : ∀ (branchRight1 : Branch) (branchRight2: Branch)
    (branch_eq: branch_equiv branchRight1 branchRight2) ,
    (branch_equiv (branch_op branchLeft branchRight1) (branch_op branchLeft branchRight2)).
  - destruct nodeLeft, nodeRight1, nodeRight2.
    + have ind_hyp := branch_op_equiv b b0 b1. clear node_op_equiv. clear branch_op_equiv.
        crush.
        apply cell_op_equiv; trivial.
  - intros. destruct branchLeft; destruct branchRight1; destruct branchRight2.
    + have hyp_node := node_op_equiv n n0 n1. clear node_op_equiv.
      have hyp_branch := branch_op_equiv branchLeft branchRight1 branchRight2. clear branch_op_equiv.
      crush.
    + clear node_op_equiv. clear branch_op_equiv. crush.
      * apply op_trivial_node; trivial.
      * apply op_trivial_branch; trivial.
    + clear node_op_equiv. clear branch_op_equiv. crush.
      * apply node_equiv_comm. apply op_trivial_node; trivial.
      * apply branch_equiv_comm. apply op_trivial_branch; trivial.
    + apply equiv_refl_branch.
    + unfold branch_op. trivial.
    + unfold branch_op. trivial.
    + unfold branch_op. trivial.
    + unfold branch_op. trivial.
Qed.

Lemma state_op_equiv (stateLeft: State) (stateRight1: State) (stateRight2: State)
    (state_eq: state_equiv stateRight1 stateRight2)
    : (state_equiv (state_op stateLeft stateRight1) (state_op stateLeft stateRight2)).
Proof. unfold state_op. unfold state_equiv in *. destruct stateLeft, stateRight1, stateRight2.
  + destruct state_eq. repeat case_decide.
    * repeat split.
      - rewrite H0. trivial.
      - apply node_op_equiv; trivial.
    * rewrite H0 in H2. contradiction.
    * rewrite H0 in H2. contradiction.
    * trivial.
  + contradiction. + contradiction.
  + trivial. + trivial. + trivial. + trivial. + trivial.
Qed.

Lemma rmerge_comm (f: gmap nat (option M)) (g: gmap nat (option M)) :
  rmerge f g = rmerge g f.
Proof. 
  unfold rmerge. apply map_eq. intro. rewrite lookup_merge. rewrite lookup_merge.
      unfold rmerge_one. destruct (f !! i), (g !! i).
    * destruct o; destruct o0.
      -- repeat case_decide.
        ** rewrite H0. trivial.
        ** symmetry in H0; contradiction.
        ** symmetry in H1; contradiction.
        ** trivial.
      -- trivial.
      -- trivial.
      -- trivial.
    * destruct o; trivial.
    * destruct o; trivial.
    * trivial.
Qed.

Lemma cell_op_comm (cell1: Cell) (cell2: Cell)
  : cell_equiv (cell_op cell1 cell2) (cell_op cell2 cell1).
Proof.
  destruct cell1, cell2; unfold cell_op. unfold cell_equiv. repeat split.
    - apply comm.
    - unfold bool_or_func. unfold equiv_func. crush.
    - apply rmerge_comm.
Qed.

Lemma node_op_comm (node1: Node) (node2: Node)
  : node_equiv (node_op node1 node2) (node_op node2 node1)
with branch_op_comm (branch1: Branch) (branch2: Branch)
  : branch_equiv (branch_op branch1 branch2) (branch_op branch2 branch1).
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_op_comm b b0. clear node_op_comm. clear branch_op_comm.
      crush. apply cell_op_comm.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_op_comm branch1 branch2.
      have ind_hyp_node := node_op_comm n n0.
      clear node_op_comm. clear branch_op_comm.
      crush.
    + unfold branch_op. apply equiv_refl_branch.
    + unfold branch_op. apply equiv_refl_branch.
    + apply equiv_refl_branch.
Qed.

Lemma rmerge_one_assoc (f g h: option (option M)) :
  rmerge_one f (rmerge_one g h) = rmerge_one (rmerge_one f g) h.
Proof. unfold rmerge_one.
  * destruct f; trivial.
    + destruct o; trivial.
      - destruct g; trivial.
        ** destruct o; trivial.
          ++ destruct h; trivial.
            -- destruct o; trivial.
              *** repeat case_decide; trivial.
                --- rewrite H0 in H1. contradiction.
                --- rewrite H1 in H2. contradiction.
              *** case_decide; trivial.
            -- case_decide; trivial.
          ++ destruct h; trivial.
      - destruct g; trivial.
        ** destruct o; trivial.
          ++ destruct h; trivial.
           -- destruct o; trivial.
            *** case_decide; trivial.
          ++ destruct h; trivial.
Qed.

Lemma rmerge_assoc (f: gmap nat (option M)) (g: gmap nat (option M)) (h: gmap nat (option M)) :
  rmerge f (rmerge g h) = rmerge (rmerge f g) h.
Proof. 
  unfold rmerge. apply map_eq. intro.
      rewrite lookup_merge. rewrite lookup_merge.
      rewrite lookup_merge. rewrite lookup_merge.
      apply rmerge_one_assoc.
Qed.

Lemma cell_op_assoc (cell1: Cell) (cell2: Cell) (cell3: Cell)
  : cell_equiv (cell_op cell1 (cell_op cell2 cell3))
               (cell_op (cell_op cell1 cell2) cell3).
Proof.
  destruct cell1, cell2, cell3; unfold cell_op. unfold cell_equiv. repeat split.
    - apply assoc.
    - unfold bool_or_func. unfold equiv_func. crush.
    - apply rmerge_assoc.
Qed.

Lemma node_op_assoc (node1: Node) (node2: Node) (node3: Node)
  : node_equiv (node_op node1 (node_op node2 node3))
               (node_op (node_op node1 node2) node3)
with branch_op_assoc (branch1: Branch) (branch2: Branch) (branch3: Branch)
  : branch_equiv (branch_op branch1 (branch_op branch2 branch3))
                 (branch_op (branch_op branch1 branch2) branch3).
Proof.
  - destruct node1, node2, node3.
    + have ind_hyp := branch_op_assoc b b0 b1. clear node_op_assoc. clear branch_op_assoc.
      crush. apply cell_op_assoc.
  - destruct branch1, branch2, branch3.
    + have ind_hyp_branch := branch_op_assoc branch1 branch2 branch3.
      have ind_hyp_node := node_op_assoc n n0 n1.
      clear node_op_assoc. clear branch_op_assoc.
      crush.
    + unfold branch_op. apply equiv_refl_branch.
    + unfold branch_op. apply equiv_refl_branch.
    + unfold branch_op. apply equiv_refl_branch.
    + unfold branch_op. apply equiv_refl_branch.
    + unfold branch_op. apply equiv_refl_branch.
    + unfold branch_op. apply equiv_refl_branch.
    + apply equiv_refl_branch.
Qed.

Definition state_inv (state: State) :=
  match state with
  | StateCon active node =>
        node_reserved_valid node
      /\ node_borrows_valid node
      /\ node_all_total_in_refinement_domain node active 0
  | StateFail => False
  end
.

Instance alls_valid_instance : Valid State := λ x, exists y , state_inv (state_op x y).

Lemma node_reserved_valid_of_trivial (n: Node)
    (triv: node_trivial n) : node_reserved_valid n
with branch_reserved_valid_of_trivial (b: Branch)
    (triv: branch_trivial b) : branch_reserved_valid b.
Proof.
  - destruct n.
    + have ind_hyp := branch_reserved_valid_of_trivial b.
      clear node_reserved_valid_of_trivial. clear branch_reserved_valid_of_trivial.
      crush.
      unfold cell_trivial in *. destruct c. destruct H0. destruct H3. rewrite H3. intro. rewrite lookup_empty. trivial.
  - destruct b.
    + have ind_hyp_branch := branch_reserved_valid_of_trivial b.
      have ind_hyp_node := node_reserved_valid_of_trivial n.
      clear node_reserved_valid_of_trivial. clear branch_reserved_valid_of_trivial.
      crush. 
    + unfold branch_reserved_valid. trivial.
Qed.

Lemma node_reserved_valid_of_equiv (node1: Node) (node2: Node)
    (eq: node_equiv node1 node2)
    (rv: node_reserved_valid node1) : (node_reserved_valid node2)
with
  branch_reserved_valid_of_equiv (branch1: Branch) (branch2: Branch)
    (eq: branch_equiv branch1 branch2)
    (rv: branch_reserved_valid branch1) : (branch_reserved_valid branch2).
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_reserved_valid_of_equiv b b0. clear node_reserved_valid_of_equiv. clear branch_reserved_valid_of_equiv. destruct c0. crush.
        destruct c. unfold cell_equiv in *. crush. apply H3.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_reserved_valid_of_equiv branch1 branch2.
      have ind_hyp_node := node_reserved_valid_of_equiv n n0.
      crush.
    + unfold branch_reserved_valid. trivial.
    + unfold branch_equiv in eq. apply branch_reserved_valid_of_trivial. trivial.
    + unfold branch_reserved_valid. trivial.
Qed.

Lemma cell_view_of_trivial (cell: Cell) (lifetime: Lifetime)
  (eq: cell_trivial cell) (m: M) : cell_view cell lifetime m.
Proof. destruct cell. unfold cell_view. unfold cell_trivial in *.
  unfold conjoin_reserved_over_lifetime.
  apply gset_easy_induct with (R := λ b , b m).
  - unfold umbrella_unit. trivial.
  - intros. destruct eq. destruct H2. rewrite H2.
    replace (gmap_get_or_unit ∅ a) with unit.
    * unfold conjoin_umbrella. exists m. exists unit. repeat split; trivial.
      + unfold umbrella. apply self_le_self.
      + apply unit_dot.
    * unfold gmap_get_or_unit. rewrite lookup_empty. trivial.
Qed.

Lemma node_view_of_trivial (node: Node) (lifetime: Lifetime)
  (eq: node_trivial node) (m: M)
  : node_view node lifetime m
with branch_view_of_trivial (branch: Branch) (lifetime: Lifetime) (idx: nat)
  (eq: branch_trivial branch) (m: M)
  : branch_view branch lifetime idx m.
Proof.
  - destruct node.
    + have ind_hyp := branch_view_of_trivial b.
      clear node_view_of_trivial. clear branch_view_of_trivial.
      crush.
      unfold conjoin_umbrella. exists m. exists unit. crush.
      * apply cell_view_of_trivial. trivial.
      * apply unit_dot.
  - destruct branch.
    + have ind_hyp_branch := branch_view_of_trivial branch.
      have ind_hyp_node := node_view_of_trivial n.
      clear node_view_of_trivial. clear branch_view_of_trivial.
      crush. 
      unfold conjoin_umbrella. exists unit. exists m. repeat split.
      * unfold project_fancy. unfold rel_project_fancy. exists unit. exists unit. repeat split.
        -- apply self_le_self.
        -- apply rel_unit.
        -- apply ind_hyp_node. trivial.
      * apply ind_hyp_branch. trivial.
      * rewrite comm. apply unit_dot.
    + unfold branch_view. unfold umbrella_unit. trivial.
Qed.

Lemma cell_view_of_equiv (cell1: Cell) (cell2: Cell) (lifetime: Lifetime)
  (eq: cell_equiv cell1 cell2) (m: M)
  : cell_view cell1 lifetime m = cell_view cell2 lifetime m.
Proof. destruct cell1, cell2. unfold cell_equiv in *. unfold cell_view.
    unfold conjoin_reserved_over_lifetime.
      replace (set_fold
    (λ (lu : nat) (um : M → Prop), conjoin_umbrella um (umbrella (gmap_get_or_unit g lu)))
    umbrella_unit lifetime) with (set_fold
    (λ (lu : nat) (um : M → Prop), conjoin_umbrella um (umbrella (gmap_get_or_unit g0 lu)))
    umbrella_unit lifetime); trivial.
    apply set_fold_equiv_funcs. destruct eq. destruct H1. rewrite H2. intros; trivial.
Qed.

Lemma node_view_of_equiv (node1: Node) (node2: Node) (lifetime: Lifetime)
  (eq: node_equiv node1 node2) (m: M)
  : node_view node1 lifetime m <-> node_view node2 lifetime m
with branch_view_of_equiv (branch1: Branch) (branch2: Branch) (lifetime: Lifetime) (idx: nat)
  (eq: branch_equiv branch1 branch2) (m: M)
  : branch_view branch1 lifetime idx m <-> branch_view branch2 lifetime idx m.
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_view_of_equiv b b0.
    crush.
      * unfold conjoin_umbrella in *. destruct H2. destruct H2. exists x. exists x0.
        rewrite <- ind_hyp; trivial. rewrite <- (cell_view_of_equiv c c0); trivial.
      * unfold conjoin_umbrella in *. destruct H2. destruct H2. exists x. exists x0.
        rewrite ind_hyp; trivial. rewrite (cell_view_of_equiv c c0); trivial.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_view_of_equiv branch1 branch2.
      have ind_hyp_node := node_view_of_equiv n n0.
      clear branch_view_of_equiv. clear node_view_of_equiv.
      crush.
      * unfold conjoin_umbrella in *. unfold project_fancy in *.
          unfold rel_project_fancy in *.
          destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
          exists x. exists x0. split.
          ** exists x1. exists x2. rewrite <- ind_hyp_node; trivial.
          ** rewrite <- ind_hyp_branch; trivial.
      * unfold conjoin_umbrella in *. unfold project_fancy in *.
          unfold rel_project_fancy in *.
          destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
          exists x. exists x0. split.
          ** exists x1. exists x2. rewrite ind_hyp_node; trivial.
          ** rewrite ind_hyp_branch; trivial.
    + unfold branch_equiv in *. fold node_equiv in *. fold branch_equiv in *.
      split.
        * intros. unfold branch_view. unfold umbrella_unit. trivial.
        * intros. apply branch_view_of_trivial. trivial.
    + unfold branch_equiv in *. fold node_equiv in *. fold branch_equiv in *.
      split.
        * intros. apply branch_view_of_trivial. trivial.
        * intros. unfold branch_view. unfold umbrella_unit. trivial.
    + trivial.
Qed.
  
Lemma node_borrows_valid_of_trivial (n: Node)
    (triv: node_trivial n) : node_borrows_valid n
with branch_borrows_valid_of_trivial (b: Branch)
    (triv: branch_trivial b) : branch_borrows_valid b.
Proof.
  - destruct n.
    + have ind_hyp := branch_borrows_valid_of_trivial b.
      clear node_borrows_valid_of_trivial. clear branch_borrows_valid_of_trivial.
      crush.
      unfold cell_trivial in *. destruct c.
      intros.
      destruct H0. have h := H0 b1. rewrite h in H3. contradiction.
  - destruct b.
    + have ind_hyp_branch := branch_borrows_valid_of_trivial b.
      have ind_hyp_node := node_borrows_valid_of_trivial n.
      clear node_borrows_valid_of_trivial. clear branch_borrows_valid_of_trivial.
      crush. 
    + unfold branch_borrows_valid. trivial.
Qed.

Lemma node_borrows_valid_of_equiv (node1: Node) (node2: Node)
    (eq: node_equiv node1 node2)
    (rv: node_borrows_valid node1) : (node_borrows_valid node2)
with
  branch_borrows_valid_of_equiv (branch1: Branch) (branch2: Branch)
    (eq: branch_equiv branch1 branch2)
    (rv: branch_borrows_valid branch1) : (branch_borrows_valid branch2).
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_borrows_valid_of_equiv b b0. clear node_borrows_valid_of_equiv. clear branch_borrows_valid_of_equiv.
      unfold node_borrows_valid in *. fold branch_borrows_valid in *.
      unfold node_equiv in eq. fold branch_equiv in *. destruct eq.
      split.
       * apply ind_hyp; trivial. destruct rv. trivial.
       * unfold node_view in *. fold branch_view in *.
        destruct c0. destruct rv. destruct c. intro. have h := H3 b3.
        replace (b1 b3) with (b2 b3).
        ** destruct b3.
          unfold conjoin_umbrella in *.
          intro.
          have j := h H4. destruct j. destruct H5.
          exists x. exists x0.
          rewrite <- (cell_view_of_equiv (CellCon m0 b2 g0) (CellCon m b1 g)); trivial.
          rewrite <- (branch_view_of_equiv b); trivial.
        ** unfold cell_equiv in H0. unfold equiv_func in H0. crush.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_borrows_valid_of_equiv branch1 branch2.
      have ind_hyp_node := node_borrows_valid_of_equiv n n0. 
      crush.
    + unfold branch_borrows_valid. trivial.
    + unfold branch_equiv in *. apply branch_borrows_valid_of_trivial. trivial.
    + trivial.
Qed.


Lemma cell_total_of_trivial (cell: Cell) (lifetime: Lifetime)
  (eq: cell_trivial cell) : cell_total cell lifetime = unit.
Proof. destruct cell. unfold cell_total. unfold cell_trivial in *.
  replace (sum_reserved_over_lifetime g lifetime) with unit.
  - destruct eq. destruct H1. rewrite H2. apply unit_dot.
  - unfold sum_reserved_over_lifetime.
  apply gset_easy_induct with (R := λ b , unit = b).
   * trivial.
   * intros. rewrite <- H0. unfold gmap_get_or_unit.
      destruct eq. destruct H2. rewrite H2. rewrite lookup_empty.
      rewrite unit_dot. trivial.
Qed.

Lemma node_total_of_trivial (node: Node) (lifetime: Lifetime)
  (eq: node_trivial node)
  : node_total node lifetime = unit
with branch_total_of_trivial (branch: Branch) (lifetime: Lifetime) (idx: nat)
  (eq: branch_trivial branch)
  : branch_total branch lifetime idx = unit.
Proof.
  - destruct node.
    + have ind_hyp := branch_total_of_trivial b.
      clear node_total_of_trivial. clear branch_total_of_trivial.
      crush.
      rewrite cell_total_of_trivial; trivial. apply unit_dot.
  - destruct branch.
    + have ind_hyp_branch := branch_total_of_trivial branch.
      have ind_hyp_node := node_total_of_trivial n.
      clear node_total_of_trivial. clear branch_total_of_trivial.
      crush. 
      unfold project. unfold rel_project. rewrite rel_unit. apply unit_dot.
    + unfold branch_total. trivial.
Qed.

Lemma cell_total_of_equiv (cell1: Cell) (cell2: Cell) (lifetime: Lifetime)
  (eq: cell_equiv cell1 cell2)
  : cell_total cell1 lifetime = cell_total cell2 lifetime.
Proof. destruct cell1, cell2. unfold cell_equiv in *. unfold cell_total.
    destruct eq. destruct H1. rewrite H0. f_equal.
    unfold sum_reserved_over_lifetime.
      apply set_fold_equiv_funcs.
      intros. rewrite H2. trivial.
Qed.

Lemma node_total_of_equiv (node1: Node) (node2: Node) (lifetime: Lifetime)
  (eq: node_equiv node1 node2)
  : node_total node1 lifetime = node_total node2 lifetime
with branch_total_of_equiv (branch1: Branch) (branch2: Branch) (lifetime: Lifetime) (idx: nat)
  (eq: branch_equiv branch1 branch2)
  : branch_total branch1 lifetime idx = branch_total branch2 lifetime idx.
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_total_of_equiv b b0.
    crush.
      rewrite (cell_total_of_equiv c c0); trivial. 
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_total_of_equiv branch1 branch2.
      have ind_hyp_node := node_total_of_equiv n n0.
      clear branch_total_of_equiv. clear node_total_of_equiv.
      crush.
    + unfold branch_equiv in eq. rewrite branch_total_of_trivial; trivial. 
    + unfold branch_equiv in eq. rewrite branch_total_of_trivial.
      * rewrite branch_total_of_trivial; trivial.
      * unfold branch_trivial. trivial.
    + unfold branch_total. trivial.
Qed.


Lemma node_all_total_in_refinement_domain_of_trivial (n: Node) (lifetime: Lifetime) (idx: nat)
    (triv: node_trivial n) : node_all_total_in_refinement_domain n lifetime idx
with branch_all_total_in_refinement_domain_of_trivial (b: Branch) (lifetime: Lifetime) (idx: nat)
    (triv: branch_trivial b) : branch_all_total_in_refinement_domain b lifetime idx.
Proof.
  - destruct n.
    + have ind_hyp := branch_all_total_in_refinement_domain_of_trivial b.
      clear node_all_total_in_refinement_domain_of_trivial. clear branch_all_total_in_refinement_domain_of_trivial.
      crush.
      rewrite cell_total_of_trivial; trivial.
      rewrite branch_total_of_trivial; trivial.
      rewrite unit_dot.
      destruct c. split.
      * unfold in_refinement_domain. rewrite rel_unit. trivial.
      * apply ind_hyp. trivial.
  - destruct b.
    + have ind_hyp_branch := branch_all_total_in_refinement_domain_of_trivial b.
      have ind_hyp_node := node_all_total_in_refinement_domain_of_trivial n.
      clear node_all_total_in_refinement_domain_of_trivial. clear branch_all_total_in_refinement_domain_of_trivial.
      crush. 
    + unfold branch_all_total_in_refinement_domain. trivial.
Qed.

Lemma node_all_total_in_refinement_domain_of_equiv (node1: Node) (node2: Node)
      (lifetime: Lifetime) (idx: nat)
    (eq: node_equiv node1 node2)
    (rv: node_all_total_in_refinement_domain node1 lifetime idx)
    : (node_all_total_in_refinement_domain node2 lifetime idx)
with
  branch_all_total_in_refinement_domain_of_equiv (branch1: Branch) (branch2: Branch)
      (lifetime: Lifetime) (idx: nat)
    (eq: branch_equiv branch1 branch2)
    (rv: branch_all_total_in_refinement_domain branch1 lifetime idx)
    : (branch_all_total_in_refinement_domain branch2 lifetime idx).
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_all_total_in_refinement_domain_of_equiv b b0. clear node_all_total_in_refinement_domain_of_equiv. clear branch_all_total_in_refinement_domain_of_equiv.
      unfold node_all_total_in_refinement_domain in *. fold branch_all_total_in_refinement_domain in *.
      unfold node_equiv in eq. fold branch_equiv in *. destruct eq.
      split.
       * apply ind_hyp; trivial. destruct rv. trivial.
       * unfold node_view in *. fold branch_view in *.
        destruct c0. destruct rv. destruct c. intro. have h := H3 b3.
        replace (b1 b3) with (b2 b3).
        ** destruct b3.
          unfold conjoin_umbrella in *.
          intro.
          have j := h H4. destruct j. destruct H5.
          exists x. exists x0.
          rewrite <- (cell_view_of_equiv (CellCon m0 b2 g0) (CellCon m b1 g)); trivial.
          rewrite <- (branch_view_of_equiv b); trivial.
        ** unfold cell_equiv in H0. unfold equiv_func in H0. crush.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_all_total_in_refinement_domain_of_equiv branch1 branch2.
      have ind_hyp_node := node_all_total_in_refinement_domain_of_equiv n n0. 
      crush.
    + unfold branch_all_total_in_refinement_domain. trivial.
    + unfold branch_equiv in *. apply branch_all_total_in_refinement_domain_of_trivial. trivial.
    + trivial.
Qed.




Lemma state_inv_of_equiv (s: State) (t: State)
    (eq: state_equiv s t)
    (inv_s: state_inv s) : state_inv t.
Proof.
  unfold state_inv in *. destruct t; destruct s.

Definition allstate_ra_mixin : RAMixin State.
Proof. split.
  - unfold Proper, "==>". intros. apply state_op_equiv. trivial.
  - unfold pcore. unfold state_pcore. intros. crush.
  - unfold cmra.valid. unfold "==>", alls_valid_instance. unfold impl, Proper. intros.
     destruct H1. exists x0.
