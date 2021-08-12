From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.gmap_utils.
Require Import Burrow.tactics.
Require Import coq_tricks.Deex.

Class TPCM (M : Type) `{EqDecision M} :=
{
  m_valid : M -> Prop ;
  dot : M -> M -> M ;
  mov : M -> M -> Prop ;
  unit : M ;
  
  valid_monotonic : forall x y , m_valid (dot x y) -> m_valid x ;
  unit_valid : m_valid unit ;
  unit_dot : forall x , dot x unit = x ;
  tpcm_comm : forall x y , dot x y = dot y x ;
  tpcm_assoc : forall x y z , dot x (dot y z) = dot (dot x y) z ;
  reflex : forall x , mov x x ;
  trans : forall x y z , mov x y -> mov y z -> mov x z ;
  mov_monotonic : forall x y z ,
      mov x y -> m_valid (dot x z) -> m_valid (dot y z) /\ mov (dot x z) (dot y z)
}.

Definition tpcm_le `{TPCM M} (a : M) (b : M) := ∃ c , dot a c = b.

Record Refinement R M `{ TPCM R , TPCM M } :=
{
  (*rel : R -> M -> bool ;
  
  rel_valid : forall r m , rel r m -> m_valid r /\ m_valid m ;
  rel_unit : rel unit unit ;
  mov_refines : forall b b' q , mov b b' -> rel b q -> exists q' , rel b' q' /\ mov q q' ;
  rel_self : forall b q q' , rel b q -> rel b q' -> mov q q' ;*)
  
  rel_defined : R -> Prop ;
  rel : R -> M ;
  rel_valid_left : forall r , rel_defined r -> m_valid r ;
  (*rel_valid_right : forall r m , rel r = Some m -> m_valid m ;*)
  rel_defined_unit : rel_defined unit ;
  rel_unit : rel unit = unit ;
  mov_refines : forall b b' , mov b b' -> rel_defined b ->
      rel_defined b' /\ mov (rel b) (rel b') ;
}.

Definition Lifetime := multiset nat.

Global Instance eqdec_lifetime : EqDecision Lifetime.
  Proof. unfold EqDecision. intros. solve_decision. Defined.

Global Instance countable_lifetime : Countable Lifetime. 
  refine (inj_countable'
      (λ l, match l with MS _ g => g end)
      (λ g, MS nat g) _).
  intros. destruct x. trivial. Qed.

Definition lifetime_intersect (l: Lifetime) (m: Lifetime) := multiset_add l m.
Definition lifetime_included (l: Lifetime) (m: Lifetime) := multiset_le m l.
Definition empty_lifetime : Lifetime := empty_multiset.

Inductive Cell M `{!EqDecision M} `{!TPCM M} : Type :=
  | CellCon :
      M ->
      listset (Lifetime * M) ->
          Cell M.
Arguments CellCon {M}%type_scope {EqDecision0 TPCM0} _ _.

Inductive Node M `{!EqDecision M} `{!TPCM M} : Type :=
  | CellNode : Cell M -> Branch M -> Node M
with Branch M `{!EqDecision M} `{!TPCM M} : Type :=
  | BranchCons : Node M -> Branch M -> Branch M
  | BranchNil : Branch M.
Arguments CellNode {M}%type_scope {EqDecision0 TPCM0} _ _.
Arguments BranchCons {M}%type_scope {EqDecision0 TPCM0} _ _.
Arguments BranchNil {M}%type_scope {EqDecision0 TPCM0}.

Definition cell_of_node {M} `{!EqDecision M} `{!TPCM M} (n: Node M) := match n with | CellNode c _ => c end.

Definition triv_cell `{!EqDecision M} `{!TPCM M} : Cell M := CellCon unit empty.
Definition triv_node `{!EqDecision M} `{!TPCM M} : Node M := CellNode triv_cell BranchNil.

Section RollupRA.

Context {M : Type}.
Context `{!EqDecision M}.
Context `{!TPCM M}.

Definition reserved_get_or_unit (reserved: Lifetime * M) (lifetime: Lifetime) : M :=
  match reserved with
  | (my_lt, m) => if decide (multiset_le my_lt lifetime) then m else unit
  end.

Definition sum_reserved_over_lifetime (reserved: listset (Lifetime * M)) (lifetime: Lifetime) :=
  set_fold (λ reserved m , dot m (reserved_get_or_unit reserved lifetime)) unit reserved.
  
Definition cell_total (cell: Cell M) (lifetime: Lifetime) :=
  match cell with
  | CellCon m reserved => dot m (sum_reserved_over_lifetime reserved lifetime)
  end.
  
Definition cell_live (cell: Cell M) :=
  match cell with
  | CellCon m reserved => m
  end.
  
Definition cell_total_minus_live (cell: Cell M) (lifetime: Lifetime) :=
  match cell with
  | CellCon m reserved => (sum_reserved_over_lifetime reserved lifetime)
  end.
  
Definition cell_reserved (cell: Cell M) :=
  match cell with
  | CellCon m reserved => reserved
  end.
 
Definition umbrella : M -> (M -> Prop) := tpcm_le.

Definition umbrella_unit : (M -> Prop) := λ _ , True.

Definition intersect_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , a m /\ b m.

Definition conjoin_umbrella (a b : (M -> Prop)) : (M -> Prop) :=
  λ m , ∃ x y , a x /\ b y /\ dot x y = m.


Definition umbrella_is_closed (umb: M -> Prop) := ∀ a b , umb a -> umb (dot a b).
    
Definition conjoin_reserved_over_lifetime (reserved: listset (Lifetime * M)) (lifetime: Lifetime) : (M -> Prop) :=
  set_fold (λ reserved um , conjoin_umbrella um (umbrella (reserved_get_or_unit reserved lifetime)))
      umbrella_unit reserved.

Definition cell_view (cell: Cell M) (lifetime: Lifetime) : (M -> Prop) :=
  match cell with
  | CellCon m reserved => conjoin_reserved_over_lifetime reserved lifetime
  end.

Definition view_sat (umbrella : M -> Prop) (m : M) := umbrella m.

Lemma self_le_self a : tpcm_le a a.
Proof. unfold tpcm_le. exists unit. rewrite unit_dot. trivial. Qed.

Lemma unit_le a : tpcm_le unit a.
Proof. unfold tpcm_le. exists a. rewrite tpcm_comm. rewrite unit_dot. trivial. Qed.

Lemma unit_view_sat_unit : view_sat umbrella_unit unit.
Proof. unfold view_sat. unfold umbrella_unit. trivial. Qed.

Lemma le_add_both_sides a b c : tpcm_le a b -> tpcm_le (dot a c) (dot b c).
Proof.  unfold tpcm_le. intros. destruct H. exists x. rewrite tpcm_comm. rewrite tpcm_assoc.
    rewrite tpcm_comm in H. rewrite H. trivial. Qed.
    
Lemma le_add2 a b c d : tpcm_le a c -> tpcm_le b d -> tpcm_le (dot a b) (dot c d).
Proof.  unfold tpcm_le. intros. destruct H. destruct H0.
exists (dot x x0). rewrite <- H. rewrite <- H0.
  rewrite <- (tpcm_assoc a b). rewrite <- (tpcm_assoc a x). f_equal.
  rewrite tpcm_assoc. rewrite tpcm_assoc. f_equal.
  apply tpcm_comm; trivial.
Qed.

Lemma unit_dot_left a : dot unit a = a. 
Proof. rewrite tpcm_comm. apply unit_dot. Qed.

Lemma dot_comm_right2 (j a k : M) : dot (dot j a) k = dot (dot j k) a.
Proof.  rewrite <- tpcm_assoc. rewrite <- tpcm_assoc. f_equal. apply tpcm_comm. Qed.
    
Lemma le_add_right_side a b c : tpcm_le a b -> tpcm_le a (dot b c).
Proof.  unfold tpcm_le. intros. destruct H. exists (dot x c). rewrite tpcm_assoc.
    rewrite H. trivial. Qed.

Lemma umbrella_closed_umbrella_unit : umbrella_is_closed umbrella_unit.
Proof. unfold umbrella_is_closed. unfold umbrella_unit. intros. trivial. Qed.

Lemma umbrella_closed_umbrella a : umbrella_is_closed (umbrella a).
Proof. unfold umbrella_is_closed. unfold umbrella. intros. apply le_add_right_side. trivial.
Qed.

Lemma umbrella_closed_conjoin um1 um2 :
  umbrella_is_closed um1 ->
    umbrella_is_closed (conjoin_umbrella um1 um2).
Proof. unfold umbrella_is_closed. unfold conjoin_umbrella. intros.
  deex. destruct_ands. subst. exists (dot x b). exists y.
  repeat split; trivial.
  - apply H. trivial.
  - apply dot_comm_right2.
Qed.

Lemma sum_reserved_over_lifetime_monotonic (g: listset (Lifetime * M)) (lt1: Lifetime) (lt2: Lifetime)
  (lt1_le_lt2 : multiset_le lt1 lt2)
  : tpcm_le
        (sum_reserved_over_lifetime g lt1)
        (sum_reserved_over_lifetime g lt2).
Proof. unfold sum_reserved_over_lifetime.
  unfold Lifetime in lt1, lt2.
  apply (set_subset_relate tpcm_le).
  - apply self_le_self.
  - trivial.
  - intros. apply le_add2; trivial.
    unfold reserved_get_or_unit. destruct a. case_decide; case_decide.
      * apply self_le_self.
      * exfalso. apply H1. apply multiset_le_transitive with (y := lt1); trivial.
      * apply unit_le.
      * apply self_le_self.
  - intros. apply le_add_right_side. trivial.
  - intros. rewrite <- tpcm_assoc. rewrite <- tpcm_assoc. f_equal. apply tpcm_comm.
Qed.


Lemma umbrella_reserved_get_or_unit_monotonic l (m:M) (lt1: Lifetime) (lt2: Lifetime) y
  (lt1_le_lt2 : multiset_le lt1 lt2) :
  umbrella (reserved_get_or_unit (l, m) lt2) y ->
  umbrella (reserved_get_or_unit (l, m) lt1) y.
Proof.
  intro.
  unfold reserved_get_or_unit in *. repeat (case_decide); trivial.
  - unfold umbrella. unfold tpcm_le. exists y. apply unit_dot_left.
  - assert (multiset_le l lt2).
    + apply multiset_le_transitive with (y0 := lt1); trivial.
    + contradiction.
Qed.

Lemma conjoin_umbrella_monotonic (a b a' b' : M -> Prop)
  (att: ∀ y , a y -> a' y)
  (btt: ∀ y , b y -> b' y)
  : ∀ y , conjoin_umbrella a b y -> conjoin_umbrella a' b' y.
Proof.
  intro. unfold conjoin_umbrella. intro. deex.
  exists x. exists y0. destruct_ands. repeat split; trivial.
  - apply att; trivial.
  - apply btt; trivial.
Qed.

Lemma conjoin_reserved_over_lifetime_monotonic (g: listset (Lifetime * M)) (lt1: Lifetime) (lt2: Lifetime)
  (lt1_le_lt2 : multiset_le lt1 lt2)
  : ∀ y ,
        (conjoin_reserved_over_lifetime g lt2 y) ->
        (conjoin_reserved_over_lifetime g lt1 y).
Proof.
  unfold conjoin_reserved_over_lifetime.
  have ss := set_relate (λ (a:M->Prop) (b:M->Prop) , ∀ (y:M), a y -> b y) g
    (λ (reserved : Lifetime * M) (um : M → Prop),
         conjoin_umbrella um (umbrella (reserved_get_or_unit reserved lt2)))
    (λ (reserved : Lifetime * M) (um : M → Prop),
           conjoin_umbrella um (umbrella (reserved_get_or_unit reserved lt1))).
  apply ss.
  - intro. trivial.
  - intros. clear ss. destruct a.
    have urg := umbrella_reserved_get_or_unit_monotonic l m lt1 lt2 _ lt1_le_lt2.
    full_generalize (umbrella (reserved_get_or_unit (l, m) lt1)) as u1.
    full_generalize (umbrella (reserved_get_or_unit (l, m) lt2)) as u2.
    apply conjoin_umbrella_monotonic with (a := b) (b := u2); trivial.
Qed.

Lemma cell_view_inclusion lt1 lt2 cell
  (li: multiset_le lt1 lt2)
  : (∀ y, cell_view cell lt2 y -> cell_view cell lt1 y).
Proof.
  destruct cell. unfold cell_view in *.
  intro. apply conjoin_reserved_over_lifetime_monotonic with (lt2 := lt2); trivial.
Qed.

Lemma view_sat_reserved_over_lifetime (reserved: listset (Lifetime * M)) (lt: Lifetime)
  : view_sat (conjoin_reserved_over_lifetime reserved lt)
             (sum_reserved_over_lifetime reserved lt).
Proof.
  unfold conjoin_reserved_over_lifetime, sum_reserved_over_lifetime.
  apply (set_relate view_sat).
  - apply unit_view_sat_unit.
  - intros. unfold view_sat in *. unfold conjoin_umbrella.
      exists c. exists (reserved_get_or_unit a lt). repeat split.
    + trivial.
    + unfold umbrella. apply self_le_self.
Qed.

Lemma view_sat_with_le (umb: M -> Prop) (a : M) (b : M)
    (closed: umbrella_is_closed umb)
    (vs: view_sat umb a)
    (mle: tpcm_le a b) : view_sat umb b.
Proof. unfold view_sat in *. intros. unfold umbrella_is_closed in closed.
    unfold tpcm_le in mle. destruct mle. rewrite <- H. apply closed. trivial.
Qed.

Lemma conjoin_reserved_over_lifetime_is_closed (reserved: listset (Lifetime * M)) (lt: Lifetime)
    : umbrella_is_closed (conjoin_reserved_over_lifetime reserved lt).
Proof. unfold cell_view. unfold conjoin_reserved_over_lifetime.
  apply (set_easy_induct umbrella_is_closed).
  - apply umbrella_closed_umbrella_unit.
  - intros. apply umbrella_closed_conjoin.
    + trivial.
Qed.

Lemma cell_view_closed (c: Cell M) x y lt
  : cell_view c lt y -> cell_view c lt (dot x y).
Proof. intro. unfold cell_view in *. destruct c.
  have j := conjoin_reserved_over_lifetime_is_closed l lt.
  unfold umbrella_is_closed in j.
  rewrite tpcm_comm. apply j. trivial.
Qed.

Lemma cell_view_le_total (cell: Cell M) (lt: Lifetime) (active: Lifetime)
    (lt_is_active : lifetime_included active lt)
    : view_sat (cell_view cell lt) (cell_total cell active).
Proof.
  unfold cell_view. destruct cell. unfold cell_total.
    apply view_sat_with_le with (a := (sum_reserved_over_lifetime l lt)).
    + apply conjoin_reserved_over_lifetime_is_closed.
    + apply view_sat_reserved_over_lifetime.
    + rewrite tpcm_comm. apply le_add_right_side.
        apply sum_reserved_over_lifetime_monotonic.
        unfold lifetime_included in lt_is_active. trivial.
Qed.

Lemma view_sat_conjoin (um1 um2 : M -> Prop) (m1 m2 : M)
    (vs1: view_sat um1 m1)
    (vs2: view_sat um2 m2)
    : view_sat (conjoin_umbrella um1 um2) (dot m1 m2).
Proof. unfold view_sat in *. unfold conjoin_umbrella. exists m1. exists m2. repeat split; trivial. Qed.

Definition cell_trivial (cell: Cell M) :=
  match cell with
  | CellCon m reserves => reserves ≡ empty /\ m = unit
  end
.

Fixpoint node_trivial (node: Node M) :=
  match node with
  | CellNode cell branch => cell_trivial cell /\ branch_trivial branch
  end
with branch_trivial (branch: Branch M) :=
  match branch with
  | BranchNil => True
  | BranchCons node branch => node_trivial node /\ branch_trivial branch
  end
.

Definition equiv_func {A} {B} (f g: A -> B) := ∀ x , f x = g x.

Global Instance cell_equiv : Equiv (Cell M) := λ (cell1: Cell M) (cell2: Cell M) ,
  match cell1, cell2 with
  | CellCon m1 g1, CellCon m2 g2 =>
      (m1 = m2) /\ g1 ≡ g2
  end
.

Fixpoint internal_node_equiv (node1: Node M) (node2: Node M) :=
  let _ : Equiv (Node M) := internal_node_equiv in
  let _ : Equiv (Branch M) := internal_branch_equiv in
  match node1, node2 with
    | CellNode cell1 branch1, CellNode cell2 branch2 =>
           cell1 ≡ cell2
        /\ branch1 ≡ branch2
  end
with internal_branch_equiv (branch1: Branch M) (branch2: Branch M) :=
  let _ : Equiv (Node M) := internal_node_equiv in  
  let _ : Equiv (Branch M) := internal_branch_equiv in
  match branch1, branch2 with
    | BranchNil, _ => branch_trivial branch2
    | BranchCons _ _, BranchNil => branch_trivial branch1
    | BranchCons n1 b1, BranchCons n2 b2 =>
        n1 ≡ n2 /\ b1 ≡ b2
  end 
.

(* black magic for defining recursive instances
   https://github.com/coq/coq/issues/7913 *)
Definition node_equiv : Equiv (Node M)
  := Eval cbv [internal_node_equiv internal_branch_equiv] in internal_node_equiv.
Definition branch_equiv : Equiv (Branch M)
  := Eval cbv [internal_node_equiv internal_branch_equiv] in internal_branch_equiv.
Global Existing Instances node_equiv branch_equiv.

(*
Global Instance state_pcore : PCore (State M) := λ state , None.
*)

Global Instance cell_op : Op (Cell M) := λ (x: Cell M) (y: Cell M) ,
  match x, y with
  | CellCon m1 reserved1,
    CellCon m2 reserved2 =>
      CellCon (dot m1 m2)
              (reserved1 ∪ reserved2)
  end
.

Fixpoint internal_node_op (x: Node M) (y: Node M) : Node M :=
  let _ : Op (Node M) := internal_node_op in
  let _ : Op (Branch M) := internal_branch_op in
  match x, y with
  | CellNode cell1 branch1, CellNode cell2 branch2 =>
      CellNode (cell1 ⋅ cell2) (branch1 ⋅ branch2)
  end 
with internal_branch_op (branch1: Branch M) (branch2: Branch M) : Branch M :=
  let _ : Op (Node M) := internal_node_op in
  let _ : Op (Branch M) := internal_branch_op in
  match branch1, branch2 with
  | BranchNil, _ => branch2
  | BranchCons _ _, BranchNil => branch1
  | BranchCons n1 subbranch1 , BranchCons n2 subbranch2 =>
      BranchCons (n1 ⋅ n2) (subbranch1 ⋅ subbranch2)
  end
.

(* black magic for defining recursive instances
   https://github.com/coq/coq/issues/7913 *)
Definition node_op : Op (Node M)
  := Eval cbv [internal_node_op internal_branch_op] in internal_node_op.
Definition branch_op : Op (Branch M)
  := Eval cbv [internal_node_op internal_branch_op] in internal_branch_op.
Global Existing Instances node_op branch_op.

(*
Global Instance state_op : Op (State M) := λ x y ,
  match x, y with
  | StateCon active1 node1, StateCon active2 node2 =>
      StateCon (multiset_add active1 active2) (node1 ⋅ node2)
  end.
  
Global Instance state_equiv : Equiv (State M) := λ x y ,
  match x, y with
  | StateCon lt1 node1, StateCon lt2 node2 =>
      (lt1 = lt2 /\ node1 ≡ node2)
  end.
*)
  
Lemma cell_equiv_refl (cell: Cell M) : cell_equiv cell cell.
Proof. destruct cell. unfold cell_equiv. split; trivial. Qed.

Global Instance inst_cell_equiv_refl : Reflexive cell_equiv.
unfold Reflexive. intro. apply cell_equiv_refl. Defined.
    
Lemma node_equiv_refl (node: Node M) : node_equiv node node
with branch_equiv_refl (branch: Branch M) : branch_equiv branch branch.
Proof.
 - destruct node. unfold node_equiv. repeat split.
  + apply cell_equiv_refl.
  + apply branch_equiv_refl.
 - destruct branch.
  + unfold branch_equiv. repeat split.
    * apply node_equiv_refl.
    * apply branch_equiv_refl.
  + unfold branch_equiv. unfold branch_trivial. trivial.
Qed.

Global Instance inst_node_equiv_refl : Reflexive node_equiv.
unfold Reflexive. intro. apply node_equiv_refl. Defined.

Global Instance inst_branch_equiv_refl : Reflexive branch_equiv.
unfold Reflexive. intro. apply branch_equiv_refl. Defined.

Lemma op_trivial_cell (cell1: Cell M) (cell2: Cell M)
  (istriv: cell_trivial cell2) : ((cell1 ⋅ cell2) ≡ cell1). 
Proof. unfold "⋅", "≡", cell_equiv, cell_op. destruct cell1, cell2.
    unfold cell_trivial in istriv. destruct_ands. subst. split; trivial.
    - apply unit_dot. - set_solver. Qed.

Lemma op_trivial_node (node1: Node M) (node2: Node M)
  (istriv: node_trivial node2) : ((node1 ⋅ node2) ≡ node1)
with op_trivial_branch (branch1: Branch M) (branch2: Branch M)
  (istriv: branch_trivial branch2) : ((branch1 ⋅ branch2) ≡ branch1).
Proof.
  - destruct node1; destruct node2.
    + have hyp := op_trivial_branch b b0. clear op_trivial_node. clear op_trivial_branch.
        unfold "≡", "⋅".
    unfold node_op. fold branch_op. destruct c. destruct c0.
        unfold node_equiv. fold branch_equiv. unfold cell_op. unfold cell_equiv.
            unfold node_trivial in istriv. fold branch_trivial in istriv.
            destruct istriv. unfold cell_trivial in *. destruct H. repeat split.
        -- rewrite H1. apply unit_dot.
        -- rewrite H. set_solver.
        -- set_solver.
        -- apply hyp; trivial.
  - destruct branch1; destruct branch2.
    + have hyp_branch := op_trivial_branch branch1 branch2. clear op_trivial_branch.
      have hyp_node := op_trivial_node n n0. clear op_trivial_node.
      unfold "≡". unfold branch_equiv. crush.
    + unfold "⋅". unfold branch_op. apply branch_equiv_refl.
    + unfold "⋅". unfold branch_op. unfold "≡". unfold branch_equiv. trivial.
    + unfold "⋅". unfold branch_op. apply branch_equiv_refl.
Qed.

Lemma cell_equiv_symm (cell1: Cell M) (cell2: Cell M)
  (iseq: cell_equiv cell1 cell2) : (cell_equiv cell2 cell1).
Proof. unfold cell_equiv in *. destruct cell1, cell2. destruct iseq. destruct H. repeat split.
  * set_solver.
  * set_solver.
Qed.

Global Instance inst_cell_equiv_symm : Symmetric cell_equiv.
unfold Symmetric. intro. apply cell_equiv_symm. Defined.

Lemma node_equiv_symm (node1: Node M) (node2: Node M)
  (iseq: node_equiv node1 node2) : (node_equiv node2 node1)
with branch_equiv_symm (branch1: Branch M) (branch2: Branch M)
  (iseq: branch_equiv branch1 branch2) : (branch_equiv branch2 branch1).
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_equiv_symm b b0. clear node_equiv_symm. clear branch_equiv_symm.
        unfold node_equiv. fold branch_equiv. repeat split.
        * apply cell_equiv_symm. unfold node_equiv in iseq. destruct iseq; trivial.
        * unfold node_equiv in iseq. destruct iseq. apply ind_hyp; trivial.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_equiv_symm branch1 branch2.
      have ind_hyp_node := node_equiv_symm n n0.
      unfold branch_equiv in *. fold node_equiv in *. fold branch_equiv in *. split.
        * apply ind_hyp_node. destruct iseq; trivial.
        * apply ind_hyp_branch. destruct iseq; trivial.
    + unfold branch_equiv in *. trivial.
    + unfold branch_equiv in *. trivial.
    + trivial.
Qed.

Global Instance inst_node_equiv_symm : Symmetric node_equiv := node_equiv_symm.

Global Instance inst_branch_equiv_symm : Symmetric branch_equiv := branch_equiv_symm.

(*
Lemma state_equiv_symm (state1 state2: State M)
  (seq : state_equiv state1 state2) : (state_equiv state2 state1).
Proof.
  destruct state1, state2; unfold state_equiv in *; trivial.
    - destruct seq; split. * symmetry; trivial. * apply branch_equiv_symm; trivial.
Qed.

Global Instance inst_state_equiv_symm : Symmetric state_equiv := state_equiv_symm.
*)

Lemma cell_equiv_trans (cell1: Cell M) (cell2: Cell M) (cell3: Cell M)
  (iseq: cell_equiv cell1 cell2)
  (iseq2: cell_equiv cell2 cell3)
  : (cell_equiv cell1 cell3).
Proof. unfold cell_equiv in *. destruct cell1, cell2, cell3. unfold equiv_func in *. crush. Qed.

Global Instance inst_cell_equiv_trans : Transitive cell_equiv := cell_equiv_trans.

Lemma cell_trivial_of_equiv (cell1: Cell M) (cell2: Cell M)
  (iseq: cell1 ≡ cell2)
  (istriv: cell_trivial cell1)
  : cell_trivial cell2.
Proof.
  unfold "≡", cell_equiv, cell_trivial in *.  destruct cell1, cell2; crush. set_solver.
Qed.

Global Instance inst_cell_trivial_of_equiv : Proper (equiv ==> impl) cell_trivial.
Proof.
unfold Proper, equiv, impl, "==>". intros. apply cell_trivial_of_equiv with (cell1 := x).
  + unfold "≡"; trivial. + trivial.
Qed.

Lemma node_trivial_of_equiv (node1: Node M) (node2: Node M)
  (iseq: node1 ≡ node2)
  (istriv: node_trivial node1)
  : node_trivial node2
with branch_trivial_of_equiv (branch1: Branch M) (branch2: Branch M)
  (iseq: branch1 ≡ branch2)
  (istriv: branch_trivial branch1)
  : branch_trivial branch2.
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_trivial_of_equiv b b0. clear node_trivial_of_equiv. clear branch_trivial_of_equiv.
      cbn [node_trivial]. cbn [node_trivial] in istriv. destruct istriv. 
      unfold "≡" in iseq. unfold node_equiv in iseq. destruct iseq.
      split.
       * rewrite <- H1. trivial.
       * apply ind_hyp; trivial.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_trivial_of_equiv branch1 branch2.
      have ind_hyp_node := node_trivial_of_equiv n n0.
      clear branch_trivial_of_equiv. clear node_trivial_of_equiv.
      cbn [branch_trivial]; split.
      * apply ind_hyp_node; trivial. ** unfold "≡" in *. crush. ** crush.
      * unfold "≡" in *. crush.
    + unfold branch_trivial. trivial.
    + unfold branch_equiv in iseq. trivial.
    + unfold branch_trivial. trivial.
Qed.

Global Instance inst_node_trivial_of_equiv : Proper (equiv ==> impl) node_trivial.
Proof.
unfold Proper, equiv, impl, "==>". intros. apply node_trivial_of_equiv with (node1 := x).
  + unfold "≡"; trivial. + trivial.
Qed.

Global Instance inst_branch_trivial_of_equiv : Proper (equiv ==> impl) branch_trivial.
Proof.
unfold Proper, equiv, impl, "==>". intros. apply branch_trivial_of_equiv with (branch1 := x).
  + unfold "≡"; trivial. + trivial.
Qed.

Lemma node_equiv_of_trivial (node1: Node M) (node2: Node M)
  (istriv1: node_trivial node1)
  (istriv: node_trivial node2)
  : node1 ≡ node2
with branch_equiv_of_trivial (branch1: Branch M) (branch2: Branch M)
  (istriv1: branch_trivial branch1)
  (istriv: branch_trivial branch2)
  : branch1 ≡ branch2.
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_equiv_of_trivial b b0. clear node_equiv_of_trivial. clear branch_equiv_of_trivial.
      unfold "≡". crush.
      unfold cell_equiv in *. unfold cell_trivial. destruct c0, c. unfold "≡". split; set_solver.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_equiv_of_trivial branch1 branch2.
      have ind_hyp_node := node_equiv_of_trivial n n0.
      clear branch_equiv_of_trivial. clear node_equiv_of_trivial.
      unfold "≡". crush.
    + unfold branch_trivial. trivial.
    + unfold branch_equiv. trivial.
    + unfold branch_equiv. trivial.
Qed.

Lemma node_equiv_trans (node1: Node M) (node2: Node M) (node3: Node M)
  (iseq: node1 ≡ node2)
  (iseq2: node2 ≡ node3)
   : (node1 ≡ node3)
with branch_equiv_trans (branch1: Branch M) (branch2: Branch M) (branch3: Branch M)
  (iseq: branch_equiv branch1 branch2)
  (iseq2: branch_equiv branch2 branch3)
   : (branch_equiv branch1 branch3).
Proof.
  - unfold "≡" in *.
    destruct node1, node2, node3.
    + have ind_hyp := branch_equiv_trans b b0 b1. clear node_equiv_trans. clear branch_equiv_trans.
      crush.
  - unfold "≡" in *.
    destruct branch1, branch2, branch3.
    + have ind_hyp_branch := branch_equiv_trans branch1 branch2 branch3.
      have ind_hyp_node := node_equiv_trans n n0 n1.
      clear branch_equiv_trans. clear node_equiv_trans.
      crush.
    + unfold branch_equiv. unfold branch_equiv in iseq2.
        apply branch_trivial_of_equiv with (branch1 := BranchCons n0 branch2); trivial.
    + unfold branch_equiv in iseq. unfold branch_equiv in iseq2.
      apply branch_equiv_of_trivial; trivial.
    + trivial.
    + unfold branch_equiv. unfold branch_equiv in iseq.
        apply branch_trivial_of_equiv with (branch1 := BranchCons n branch2); trivial.
    + unfold branch_equiv. unfold branch_trivial. trivial.
    + trivial.
    + trivial.
Qed.

Global Instance inst_node_equiv_trans : Transitive node_equiv := node_equiv_trans.
Global Instance inst_branch_equiv_trans : Transitive branch_equiv := branch_equiv_trans.

Global Instance branch_equiv_preorder : PreOrder branch_equiv.
Proof. split; typeclasses eauto. Defined.

(*
Lemma state_equiv_trans (state1: State M) (state2: State M) (state3: State M)
  (iseq: state1 ≡ state2)
  (iseq2: state2 ≡ state3)
   : (state1 ≡ state3).
Proof.
  unfold "≡" in *.
  unfold state_equiv in *. destruct state1, state2, state3; trivial.
    - split; crush.
Qed.

Global Instance inst_state_equiv_trans : Transitive state_equiv := state_equiv_trans.
*)

Lemma cell_op_equiv (c c0 c1 : Cell M)
  (eq1: c0 ≡ c1)
  : ((c ⋅ c0) ≡ (c ⋅ c1)).
Proof.
  destruct c0, c1, c. unfold cell_op. unfold cell_equiv in *. destruct eq1.
      unfold "≡", "⋅". split; set_solver.
Qed.

Lemma node_op_equiv (nodeLeft: Node M) (nodeRight1 : Node M) (nodeRight2: Node M)
    (node_eq: nodeRight1 ≡ nodeRight2)
    : (nodeLeft ⋅ nodeRight1) ≡ (nodeLeft ⋅ nodeRight2)
with branch_op_equiv (branchLeft: Branch M) : ∀ (branchRight1 : Branch M) (branchRight2: Branch M)
    (branch_eq: branchRight1 ≡ branchRight2) ,
    (branchLeft ⋅ branchRight1) ≡ (branchLeft ⋅ branchRight2).
Proof.
  - unfold "⋅" in *. unfold "≡" in *.
    destruct nodeLeft, nodeRight1, nodeRight2.
    + have ind_hyp := branch_op_equiv b b0 b1. clear node_op_equiv. clear branch_op_equiv.
        crush.
        apply cell_op_equiv; trivial.
  - unfold "⋅" in *. unfold "≡" in *.
    intros. destruct branchLeft; destruct branchRight1; destruct branchRight2.
    + have hyp_node := node_op_equiv n n0 n1. clear node_op_equiv.
      have hyp_branch := branch_op_equiv branchLeft branchRight1 branchRight2. clear branch_op_equiv.
      crush.
    + clear node_op_equiv. clear branch_op_equiv. crush.
      * apply op_trivial_node; trivial.
      * apply op_trivial_branch; trivial.
    + clear node_op_equiv. clear branch_op_equiv. crush.
      * apply node_equiv_symm. apply op_trivial_node; trivial.
      * apply branch_equiv_symm. apply op_trivial_branch; trivial.
    + apply branch_equiv_refl.
    + unfold branch_op. trivial.
    + unfold branch_op. trivial.
    + unfold branch_op. trivial.
    + unfold branch_op. trivial.
Qed.

(*
Lemma state_op_equiv (stateLeft: State M) (stateRight1: State M) (stateRight2: State M)
    (state_eq: stateRight1 ≡ stateRight2)
    : ((stateLeft ⋅ stateRight1) ≡ (stateLeft ⋅ stateRight2)).
Proof. unfold state_op. unfold state_equiv in *. destruct stateLeft, stateRight1, stateRight2.
  + unfold "⋅", "≡" in *. destruct state_eq. repeat case_decide.
    * repeat split; trivial.
      - rewrite H; trivial.
      - apply branch_op_equiv; trivial.
Qed.
*)

Lemma cell_op_comm (cell1: Cell M) (cell2: Cell M)
  : (cell1 ⋅ cell2) ≡ (cell2 ⋅ cell1).
Proof.
  destruct cell1, cell2; unfold cell_op. unfold cell_equiv. repeat split.
    - apply tpcm_comm.
    - set_solver.
    - set_solver.
Qed.

Global Instance inst_cell_op_comm : Comm cell_equiv cell_op := cell_op_comm.

Lemma node_op_comm (node1: Node M) (node2: Node M)
  : (node1 ⋅ node2) ≡ (node2 ⋅ node1)
with branch_op_comm (branch1: Branch M) (branch2: Branch M)
  : (branch1 ⋅ branch2) ≡ (branch2 ⋅ branch1).
Proof.
  - unfold "⋅", "≡" in *. destruct node1, node2.
    + have ind_hyp := branch_op_comm b b0. clear node_op_comm. clear branch_op_comm.
      crush. apply cell_op_comm.
  - unfold "⋅", "≡" in *. destruct branch1, branch2.
    + have ind_hyp_branch := branch_op_comm branch1 branch2.
      have ind_hyp_node := node_op_comm n n0.
      clear node_op_comm. clear branch_op_comm.
      crush.
    + unfold branch_op. apply branch_equiv_refl.
    + unfold branch_op. apply branch_equiv_refl.
    + apply branch_equiv_refl.
Qed.

Global Instance inst_node_op_comm : Comm node_equiv node_op := node_op_comm.
Global Instance inst_branch_op_comm : Comm branch_equiv branch_op := branch_op_comm.

(*
Lemma state_op_comm (state1: State M) (state2: State M)
  : (state1 ⋅ state2) ≡ (state2 ⋅ state1).
Proof.
  unfold "⋅","≡" in *.
  unfold state_equiv, state_op. destruct state1, state2; trivial. split.
  * apply multiset_add_comm.
  * apply branch_op_comm.
Qed.

Global Instance inst_state_op_comm : Comm state_equiv state_op := state_op_comm.

Lemma state_op_equiv_left (stateLeft1: State M) (stateLeft2: State M) (stateRight: State M)
    (state_eq: stateLeft1 ≡ stateLeft2)
    : (stateLeft1 ⋅ stateRight) ≡ (stateLeft2 ⋅ stateRight).
Proof.
  setoid_rewrite (state_op_comm stateLeft2 stateRight).
  setoid_rewrite (state_op_comm stateLeft1 stateRight).
  apply state_op_equiv. trivial.
Qed.
*)

Lemma cell_op_assoc (cell1: Cell M) (cell2: Cell M) (cell3: Cell M)
  : (cell1 ⋅ (cell2 ⋅ cell3)) ≡ ((cell1 ⋅ cell2) ⋅ cell3).
Proof.
  unfold "⋅", "≡".
  destruct cell1, cell2, cell3; unfold cell_op. unfold cell_equiv. repeat split.
    - apply tpcm_assoc.
    - set_solver.
    - set_solver.
Qed.

Global Instance inst_cell_op_assoc : Assoc equiv cell_op := cell_op_assoc.

Lemma node_op_assoc (node1: Node M) (node2: Node M) (node3: Node M)
  : (node1 ⋅ (node2 ⋅ node3)) ≡ ((node1 ⋅ node2) ⋅ node3)
with branch_op_assoc (branch1: Branch M) (branch2: Branch M) (branch3: Branch M)
  : (branch1 ⋅ (branch2 ⋅ branch3)) ≡ ((branch1 ⋅ branch2) ⋅ branch3).
Proof.
  - unfold "⋅", "≡". destruct node1, node2, node3.
    + have ind_hyp := branch_op_assoc b b0 b1. clear node_op_assoc. clear branch_op_assoc.
      crush. apply cell_op_assoc.
  - unfold "⋅", "≡". destruct branch1, branch2, branch3.
    + have ind_hyp_branch := branch_op_assoc branch1 branch2 branch3.
      have ind_hyp_node := node_op_assoc n n0 n1.
      clear node_op_assoc. clear branch_op_assoc.
      crush.
    + unfold branch_op. apply branch_equiv_refl.
    + unfold branch_op. apply branch_equiv_refl.
    + unfold branch_op. apply branch_equiv_refl.
    + unfold branch_op. apply branch_equiv_refl.
    + unfold branch_op. apply branch_equiv_refl.
    + unfold branch_op. apply branch_equiv_refl.
    + apply branch_equiv_refl.
Qed.

Global Instance inst_node_op_assoc : Assoc equiv node_op := node_op_assoc.
Global Instance inst_branch_op_assoc : Assoc equiv branch_op := branch_op_assoc.

(*
Lemma state_op_assoc (state1: State M) (state2: State M) (state3: State M)
  : (state1 ⋅ (state2 ⋅ state3)) ≡ ((state1 ⋅ state2) ⋅ state3).
Proof.
  unfold "⋅", "≡".
  destruct state1, state2, state3; unfold state_op.
  unfold state_equiv. split.
  * apply multiset_add_assoc.
  * apply branch_op_assoc.
Qed.

Global Instance inst_state_op_assoc : Assoc equiv state_op := state_op_assoc.
*)

(*Lemma conjoin_umbrella_comm a b x
  : conjoin_umbrella a b x = conjoin_umbrella b a x.
  
Lemma conjoin_umbrella_assoc a b c x
  : conjoin_umbrella (conjoin_umbrella a b) c x
  = conjoin_umbrella a (conjoin_umbrella b c) x. *)
  
Lemma conjoin_umbrella_cassoc_uni a b c x :
  conjoin_umbrella (conjoin_umbrella a b) c x ->
  conjoin_umbrella (conjoin_umbrella a c) b x.
Proof.
  unfold conjoin_umbrella. intro. deex. destruct_ands. deex. destruct_ands. subst.
    exists (dot x1 y). exists y0. repeat split; trivial.
    - exists x1. exists y. repeat split; trivial.
    - apply dot_comm_right2. Qed.

Lemma conjoin_umbrella_cassoc a b c x :
  conjoin_umbrella (conjoin_umbrella a b) c x <->
  conjoin_umbrella (conjoin_umbrella a c) b x.
Proof.
  split; intro; apply conjoin_umbrella_cassoc_uni; trivial.
Qed.

(*Instance eqinst {A} : Equivalence (respectful eq iff)%signature.*)
Local Instance eqinst : Equivalence (λ f g : M → Prop, ∀ x2 y2 : M, x2 = y2 → f x2 ↔ g y2).
Proof.  apply Build_Equivalence.
  - unfold Reflexive. crush.
  - unfold Symmetric. crush. have r := H y2 y2. crush.
  - unfold Transitive. crush. have r := H0 y2 y2. have q := H y2 y2. crush.
Qed.

Global Instance conjoin_reserved_over_lifetime_proper :
  Proper ((≡) ==> (=) ==> (=) ==> iff) (conjoin_reserved_over_lifetime).
Proof.
  unfold conjoin_reserved_over_lifetime.
  unfold Proper, "==>". intros.
  assert (∀ (a1 a2 : Lifetime * M) (b : M → Prop),
                   (eq ==> iff)%signature
                     (conjoin_umbrella
                        (conjoin_umbrella b (umbrella (reserved_get_or_unit a2 x0)))
                        (umbrella (reserved_get_or_unit a1 x0)))
                     (conjoin_umbrella
                        (conjoin_umbrella b (umbrella (reserved_get_or_unit a1 x0)))
                        (umbrella (reserved_get_or_unit a2 x0)))).
   * intros. unfold "==>". intros. rewrite H2. unfold iff. apply conjoin_umbrella_cassoc.
   * have p := set_fold_proper (respectful (=) (iff)) (λ (reserved : Lifetime * M) (um : M → Prop),
       conjoin_umbrella um (umbrella (reserved_get_or_unit reserved x0)))
       umbrella_unit H2.
    + rewrite <- H0. rewrite <- H1.
    unfold Proper in p.
    eapply p.
     ** typeclasses eauto.
     ** unfold "==>". typeclasses eauto.
     ** unfold "==>". intros. rewrite H3. rewrite H5.
        unfold conjoin_umbrella. split.
          *** intro. deex. exists x5. exists y5. rewrite <- (H4 x5); trivial.
          *** intro. deex. exists x5. exists y5. rewrite (H4 x5); trivial. trivial.
     ** rewrite H. trivial.
     ** trivial.
Qed. 

Global Instance sum_reserved_over_lifetime_proper :
  Proper ((≡) ==> (=) ==> (=)) (sum_reserved_over_lifetime).
Proof.
  unfold sum_reserved_over_lifetime.
  unfold Proper, "==>". intros.
  have p := set_fold_proper (=) ((λ (reserved : Lifetime * M) (m : M), dot m (reserved_get_or_unit reserved x0))).
  unfold Proper in p. unfold "==>" in p. rewrite <- H0. eapply p.
  ** typeclasses eauto.
  ** typeclasses eauto.
  ** intros. crush.
  ** intros. rewrite <- tpcm_assoc. rewrite <- tpcm_assoc.
      f_equal. apply tpcm_comm.
  ** trivial.
Qed.

Lemma cell_view_of_trivial (cell: Cell M) (lifetime: Lifetime)
  (eq: cell_trivial cell) (m: M) : cell_view cell lifetime m.
Proof. destruct cell. unfold cell_view. unfold cell_trivial in *.
  destruct_ands. setoid_rewrite H.
  unfold conjoin_reserved_over_lifetime.
  rewrite set_fold_empty.
    unfold umbrella_unit. trivial.
Qed.

Lemma cell_view_of_equiv (cell1: Cell M) (cell2: Cell M) (lifetime: Lifetime)
  (eq: cell1 ≡ cell2) (m: M)
  : cell_view cell1 lifetime m <-> cell_view cell2 lifetime m.
Proof. destruct cell1, cell2. unfold cell_equiv in *. unfold cell_view.
    unfold "≡" in eq. destruct_ands.
    setoid_rewrite H0.
    trivial.
Qed.
  
Lemma cell_total_of_trivial (cell: Cell M) (lifetime: Lifetime)
  (eq: cell_trivial cell) : cell_total cell lifetime = unit.
Proof. destruct cell. unfold cell_total. unfold cell_trivial in *.
  replace (sum_reserved_over_lifetime l lifetime) with unit.
  - destruct eq. rewrite H0. apply unit_dot.
  - destruct_ands. setoid_rewrite H.
    unfold sum_reserved_over_lifetime. rewrite set_fold_empty. trivial.
Qed.

Lemma cell_total_of_equiv (cell1: Cell M) (cell2: Cell M) (lifetime: Lifetime)
  (eq: cell1 ≡ cell2)
  : cell_total cell1 lifetime = cell_total cell2 lifetime.
Proof. destruct cell1, cell2. unfold cell_equiv in *. unfold cell_total.
    destruct eq. setoid_rewrite H0. rewrite H. trivial.
Qed.

Lemma cell_view_le_op (c c1: Cell M) y lt
  : cell_view (c ⋅ c1) lt y -> cell_view c lt y.
Proof. intro. unfold cell_view in *. destruct c, c1. unfold "⋅", cell_op in H.
  unfold conjoin_reserved_over_lifetime in *.
  have j := conjoin_reserved_over_lifetime_is_closed l lt.
  unfold umbrella_is_closed in j.
  apply ( set_subset_relate (λ (b c: M -> Prop) , ∀ (x: M) , c x -> b x) l (l ∪ l0)
    (λ (reserved : Lifetime * M) (um : M → Prop),
           conjoin_umbrella um (umbrella (reserved_get_or_unit reserved lt)))
    (λ (reserved : Lifetime * M) (um : M → Prop),
       conjoin_umbrella um (umbrella (reserved_get_or_unit reserved lt)))
    umbrella_unit umbrella_unit
  ).
  - trivial.
  - set_solver.
  - intros. apply conjoin_umbrella_monotonic with (a := c) (b := (umbrella (reserved_get_or_unit a lt))); trivial.
  - intros. apply H0. unfold conjoin_umbrella in H1. deex. Admitted.

Context (refs: nat -> Refinement M M).

Definition project (idx: nat) (r: M) := rel M M (refs idx) r.

Fixpoint node_total (node: Node M) (lifetime: Lifetime) : M :=
  match node with
  | CellNode cell branch => dot (cell_total cell lifetime) (branch_total branch lifetime 0)
  end
with branch_total (branch: Branch M) (lifetime: Lifetime) (idx: nat) : M :=
  match branch with
  | BranchNil => unit
  | BranchCons node branch => dot (project idx (node_total node lifetime))
      (branch_total branch lifetime (S idx))
  end
.

Lemma node_total_unfold (node: Node M) (lifetime: Lifetime) :
    node_total node lifetime = 
    match node with
    | CellNode cell branch => dot (cell_total cell lifetime) (branch_total branch lifetime 0)
    end.
Proof. destruct node. unfold node_total. trivial. Qed.
    
Lemma branch_total_unfold (branch: Branch M) (lifetime: Lifetime) (idx: nat) :
    branch_total branch lifetime idx =
  match branch with
  | BranchNil => unit
  | BranchCons node branch => dot (project idx (node_total node lifetime))
      (branch_total branch lifetime (S idx))
  end.
Proof. destruct branch; unfold branch_total; trivial. Qed.

Definition node_live (node: Node M) : M :=
  match node with
  | CellNode cell branch => cell_live cell
  end.
  
Definition node_total_minus_live (node: Node M) (lifetime: Lifetime) : M :=
  match node with
  | CellNode cell branch => dot (cell_total_minus_live cell lifetime) (branch_total branch lifetime 0)
  end.
  
Lemma cell_live_plus_cell_total_minus_live (c: Cell M) (lifetime: Lifetime)
  : dot (cell_live c) (cell_total_minus_live c lifetime) = (cell_total c lifetime).
Proof.
  unfold cell_live, cell_total_minus_live, cell_total. destruct c. trivial.
Qed.

Lemma node_live_plus_node_total_minus_live (node: Node M) (lifetime: Lifetime)
    : dot (node_live node) (node_total_minus_live node lifetime) = node_total node lifetime.
Proof.
  unfold node_live, node_total_minus_live, node_total. destruct node. fold branch_total.
  rewrite <- cell_live_plus_cell_total_minus_live. apply tpcm_assoc. Qed.

Definition project_umbrella
    (refinement: Refinement M M) (umbrella : M -> Prop) : (M -> Prop) :=
    λ m , ∃ r , umbrella r /\ (rel_defined M M refinement r) /\ tpcm_le (rel M M refinement r) m.
    
Definition rel_project_fancy (idx: nat) (um: M -> Prop) :=
    λ x , ∃ b , tpcm_le (rel M M (refs idx) b) x /\ rel_defined M M (refs idx) b /\ um b.
  
Definition project_fancy (idx: nat) (um: M -> Prop) : (M -> Prop) :=
  rel_project_fancy idx um
.

Fixpoint node_view (node: Node M) (lifetime: Lifetime) : (M -> Prop) :=
  match node with
  | CellNode cell branch => conjoin_umbrella (cell_view cell lifetime) (branch_view branch lifetime 0)
  end
with branch_view (branch: Branch M) (lifetime: Lifetime) (idx: nat) : (M -> Prop) :=
  match branch with
  | BranchNil => umbrella_unit
  | BranchCons node branch => conjoin_umbrella (project_fancy idx (node_view node lifetime)) (branch_view branch lifetime (S idx))
  end
.

Lemma branch_view_rewrite (branch: Branch M) (lifetime: Lifetime) (idx: nat)
  : branch_view branch lifetime idx =
  match branch with
  | BranchNil => umbrella_unit
  | BranchCons node branch => conjoin_umbrella (project_fancy idx (node_view node lifetime)) (branch_view branch lifetime (S idx))
  end
.
Proof. unfold branch_view. destruct branch; trivial. Qed.

Lemma node_view_rewrite (node: Node M) (lifetime: Lifetime)
  : node_view node lifetime =
    match node with
    | CellNode cell branch => conjoin_umbrella (cell_view cell lifetime) (branch_view branch lifetime 0)
    end.
Proof. unfold node_view. destruct node. trivial. Qed.

Definition in_refinement_domain (idx: nat) (m : M) :=
  rel_defined M M (refs idx) m.
  
Fixpoint node_all_total_in_refinement_domain (node: Node M) (lifetime: Lifetime) (idx: nat) : Prop :=
  match node with
  | CellNode _ branch =>
         in_refinement_domain idx (node_total node lifetime)
      /\ branch_all_total_in_refinement_domain branch lifetime 0
  end
with branch_all_total_in_refinement_domain (branch: Branch M) (lifetime: Lifetime) (idx: nat) : Prop :=
  match branch with
  | BranchNil => True
  | BranchCons node branch =>
         node_all_total_in_refinement_domain node lifetime idx
      /\ branch_all_total_in_refinement_domain branch lifetime (S idx)
  end
.
 
Lemma node_all_total_in_refinement_domain_unfold (node: Node M) (lifetime: Lifetime) (idx: nat) :
  node_all_total_in_refinement_domain node lifetime idx =
  match node with
  | CellNode _ branch =>
         in_refinement_domain idx (node_total node lifetime)
      /\ branch_all_total_in_refinement_domain branch lifetime 0
  end.
Proof. unfold node_all_total_in_refinement_domain. destruct node. trivial. Qed.

Lemma branch_all_total_in_refinement_domain_unfold (branch: Branch M) (lifetime: Lifetime) (idx: nat) :
  branch_all_total_in_refinement_domain branch lifetime idx =
  match branch with
  | BranchNil => True
  | BranchCons node branch =>
         node_all_total_in_refinement_domain node lifetime idx
      /\ branch_all_total_in_refinement_domain branch lifetime (S idx)
  end.
Proof. unfold branch_all_total_in_refinement_domain; destruct branch; trivial. Qed.

Definition view_sat_projections (idx: nat) (view : M -> Prop) (m : M)
    (vrv : in_refinement_domain idx m)
    (vs: view_sat view m)
      : view_sat
        (rel_project_fancy idx view)
        (project           idx m).
Proof. 
  unfold rel_project_fancy. unfold project. unfold view_sat. unfold tpcm_le.
  exists m.
  repeat split.
  - exists unit. apply unit_dot.
  - unfold in_refinement_domain in vrv. trivial.
  - unfold view_sat in vs. trivial.
Qed.

Lemma node_view_le_total (node: Node M) (lt: Lifetime) (active: Lifetime) (idx: nat)
    (lt_is_active : lifetime_included active lt)
    (ird: node_all_total_in_refinement_domain node active idx)
    : view_sat (node_view node lt) (node_total node active)
with branch_view_le_total (branch: Branch M) (lt: Lifetime) (active: Lifetime) (idx: nat)
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
                  destruct H. trivial.
              ++ apply ind_node with (idx := idx); trivial. 
                  unfold branch_all_total_in_refinement_domain in ird. crush.
        * apply branch_view_le_total; trivial.
            unfold branch_all_total_in_refinement_domain in ird. crush.
      + unfold view_sat, branch_view, branch_total. unfold umbrella_unit. trivial.
Qed.

Lemma cell_view_le_total_minus_live (cell: Cell M) (lt: Lifetime) (active: Lifetime)
    (lt_is_active : lifetime_included active lt)
    : view_sat (cell_view cell lt) (cell_total_minus_live cell active).
Proof.
  unfold cell_view. destruct cell. unfold cell_total_minus_live.
    apply view_sat_with_le with (a := (sum_reserved_over_lifetime l lt)).
    + apply conjoin_reserved_over_lifetime_is_closed.
    + apply view_sat_reserved_over_lifetime.
    + apply sum_reserved_over_lifetime_monotonic.
        unfold lifetime_included in lt_is_active. trivial.
Qed.

Lemma node_view_le_total_minus_live (node: Node M) (lt: Lifetime) (active: Lifetime) (idx: nat)
    (lt_is_active : lifetime_included active lt)
    (ird: node_all_total_in_refinement_domain node active idx)
    : view_sat (node_view node lt) (node_total_minus_live node active).
Proof.
  destruct node.
  unfold node_view. unfold node_total. apply view_sat_conjoin.
        * apply cell_view_le_total_minus_live. trivial.
        * apply branch_view_le_total; trivial.
          unfold node_all_total_in_refinement_domain in ird.
              fold branch_all_total_in_refinement_domain in ird.
              destruct c in ird. destruct ird. trivial.
Qed.

(*
Definition state_inv (state: State M) :=
  match state with
  | StateCon active branch =>
       branch_all_total_in_refinement_domain branch active 0
       /\
       multiset_no_dupes active
  end
.

Global Instance state_valid : Valid (State M) := λ x, exists y , state_inv (state_op x y).
*)


Lemma node_view_of_trivial (node: Node M) (lifetime: Lifetime)
  (eq: node_trivial node) (m: M)
  : node_view node lifetime m
with branch_view_of_trivial (branch: Branch M) (lifetime: Lifetime)
  (eq: branch_trivial branch) (m: M) (idx: nat)
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
      * unfold project_fancy. unfold rel_project_fancy. exists unit. repeat split.
        -- rewrite rel_unit. apply self_le_self.
        -- apply rel_defined_unit.
        -- apply ind_hyp_node. trivial.
      * apply ind_hyp_branch. trivial.
      * rewrite tpcm_comm. apply unit_dot.
    + unfold branch_view. unfold umbrella_unit. trivial.
Qed.

Lemma node_view_of_equiv (node1: Node M) (node2: Node M) (lifetime: Lifetime)
  (eq: node_equiv node1 node2) (m: M)
  : node_view node1 lifetime m <-> node_view node2 lifetime m
with branch_view_of_equiv (branch1: Branch M) (branch2: Branch M) (lifetime: Lifetime)
  (eq: branch_equiv branch1 branch2) (m: M) (idx: nat)
  : branch_view branch1 lifetime idx m <-> branch_view branch2 lifetime idx m.
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_view_of_equiv b b0.
    crush.
      * unfold conjoin_umbrella in *. destruct H1. destruct H1. exists x. exists x0.
        rewrite <- ind_hyp; trivial. rewrite <- (cell_view_of_equiv c c0); trivial.
      * unfold conjoin_umbrella in *. destruct H1. destruct H1. exists x. exists x0.
        rewrite ind_hyp; trivial. rewrite (cell_view_of_equiv c c0); trivial.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_view_of_equiv branch1 branch2.
      have ind_hyp_node := node_view_of_equiv n n0.
      clear branch_view_of_equiv. clear node_view_of_equiv.
      crush.
      * unfold conjoin_umbrella in *. unfold project_fancy in *.
          unfold rel_project_fancy in *.
          destruct H1. destruct H1. destruct H1. destruct H1. destruct H1.
          exists x. exists x0. destruct_ands. split.
          ** exists x1. repeat split; trivial. rewrite <- ind_hyp_node; trivial.
          ** rewrite <- ind_hyp_branch; trivial. split; trivial.
      * unfold conjoin_umbrella in *. unfold project_fancy in *.
          unfold rel_project_fancy in *.
          destruct H1. destruct H1. destruct H1. destruct H1. destruct H1.
          exists x. exists x0. destruct_ands. split.
          ** exists x1. repeat split; trivial. rewrite ind_hyp_node; trivial.
          ** rewrite ind_hyp_branch; trivial. split; trivial.
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

Lemma node_total_of_trivial (node: Node M) (lifetime: Lifetime)
  (eq: node_trivial node)
  : node_total node lifetime = unit
with branch_total_of_trivial (branch: Branch M) (lifetime: Lifetime)
  (eq: branch_trivial branch) (idx: nat)
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
      unfold project. unfold project. rewrite rel_unit. apply unit_dot.
    + unfold branch_total. trivial.
Qed.


Lemma node_total_of_equiv (node1: Node M) (node2: Node M) (lifetime: Lifetime)
  (eq: node1 ≡ node2)
  : node_total node1 lifetime = node_total node2 lifetime
with branch_total_of_equiv (branch1: Branch M) (branch2: Branch M) (lifetime: Lifetime)
  (eq: branch_equiv branch1 branch2) (idx: nat)
  : branch_total branch1 lifetime idx = branch_total branch2 lifetime idx.
Proof.
  - unfold "≡" in *. destruct node1, node2.
    + have ind_hyp := branch_total_of_equiv b b0.
    crush.
      rewrite (cell_total_of_equiv c c0); trivial. 
  - unfold "≡" in *. destruct branch1, branch2.
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


Lemma node_all_total_in_refinement_domain_of_trivial (n: Node M) (lifetime: Lifetime) (idx: nat)
    (triv: node_trivial n) : node_all_total_in_refinement_domain n lifetime idx
with branch_all_total_in_refinement_domain_of_trivial (b: Branch M) (lifetime: Lifetime) (idx: nat)
    (triv: branch_trivial b) : branch_all_total_in_refinement_domain b lifetime idx.
Proof.
  - destruct n.
    + have ind_hyp := branch_all_total_in_refinement_domain_of_trivial b.
      clear node_all_total_in_refinement_domain_of_trivial. clear branch_all_total_in_refinement_domain_of_trivial.
      crush.
      rewrite cell_total_of_trivial; trivial.
      rewrite branch_total_of_trivial; trivial.
      rewrite unit_dot.
      destruct c. unfold in_refinement_domain. apply rel_defined_unit.
  - destruct b.
    + have ind_hyp_branch := branch_all_total_in_refinement_domain_of_trivial b.
      have ind_hyp_node := node_all_total_in_refinement_domain_of_trivial n.
      clear node_all_total_in_refinement_domain_of_trivial. clear branch_all_total_in_refinement_domain_of_trivial.
      crush. 
    + unfold branch_all_total_in_refinement_domain. trivial.
Qed.

Lemma node_all_total_in_refinement_domain_of_equiv (node1: Node M) (node2: Node M)
      (lifetime: Lifetime) (idx: nat)
    (eq: node_equiv node1 node2)
    (rv: node_all_total_in_refinement_domain node1 lifetime idx)
    : (node_all_total_in_refinement_domain node2 lifetime idx)
with
  branch_all_total_in_refinement_domain_of_equiv (branch1: Branch M) (branch2: Branch M)
      (lifetime: Lifetime) (idx: nat)
    (eq: branch_equiv branch1 branch2)
    (rv: branch_all_total_in_refinement_domain branch1 lifetime idx)
    : (branch_all_total_in_refinement_domain branch2 lifetime idx).
Proof.
  - destruct node1, node2.
    + have ind_hyp := branch_all_total_in_refinement_domain_of_equiv b b0. clear node_all_total_in_refinement_domain_of_equiv. clear branch_all_total_in_refinement_domain_of_equiv.
      unfold node_all_total_in_refinement_domain in *. fold branch_all_total_in_refinement_domain in *.
      unfold node_total. fold node_total. fold branch_total.
      unfold node_equiv in eq. fold branch_equiv in *. destruct eq.
      split.
       * rewrite <- (cell_total_of_equiv c c0); trivial.
         rewrite <- (branch_total_of_equiv b b0); trivial.
         unfold node_total in rv.
            destruct rv. trivial.
       * apply ind_hyp; trivial. destruct rv. trivial.
  - destruct branch1, branch2.
    + have ind_hyp_branch := branch_all_total_in_refinement_domain_of_equiv branch1 branch2.
      have ind_hyp_node := node_all_total_in_refinement_domain_of_equiv n n0. 
      crush.
    + unfold branch_all_total_in_refinement_domain. trivial.
    + unfold branch_equiv in *. apply branch_all_total_in_refinement_domain_of_trivial. trivial.
    + trivial.
Qed.

(*
Lemma state_inv_of_equiv (s: State M) (t: State M)
    (eq: state_equiv s t)
    (inv_s: state_inv s) : state_inv t.
Proof.
  unfold state_inv in *. unfold state_equiv in *. destruct t; destruct s; trivial.
  + split.
    * destruct inv_s. trivial. destruct eq. rewrite <- H1.
        apply branch_all_total_in_refinement_domain_of_equiv with (branch1 := b0).
        ** unfold "≡" in H2. trivial.
        ** trivial.
    * destruct inv_s. destruct eq. rewrite <- H1. trivial.
Qed.

Definition state_ra_mixin : RAMixin (State M).
Proof. split.
  - unfold Proper, "==>". intros. apply state_op_equiv. trivial.
  - unfold pcore. unfold state_pcore. intros. crush.
  - unfold cmra.valid. unfold "==>", state_valid. unfold impl, Proper. intros.
     destruct H0. exists x0. apply state_inv_of_equiv with (s := state_op x x0).
     * apply state_op_equiv_left. trivial.
     * trivial.
  - unfold Assoc. intros. apply state_op_assoc.
  - unfold Comm. intros. apply state_op_comm.
  - unfold pcore. unfold state_pcore. crush.
  - unfold pcore. unfold state_pcore. crush.
  - unfold pcore. unfold state_pcore. crush.
  - intros. unfold "✓" in *. unfold state_valid in *.
      destruct H. exists (state_op y x0). unfold op in H.
        apply state_inv_of_equiv with (s := (state_op (state_op x y) x0)); trivial.
        apply state_equiv_symm.
        apply state_op_assoc.
Qed.
*)

Global Instance branch_all_total_in_refinement_domain_proper :
    Proper ((≡) ==> (=) ==> (=) ==> impl) (branch_all_total_in_refinement_domain).
    Proof. unfold Proper, equiv, "==>", impl. intros. subst.
    apply branch_all_total_in_refinement_domain_of_equiv with (branch1 := x); trivial.
    Qed.
    
Global Instance node_all_total_in_refinement_domain_proper :
    Proper ((≡) ==> (=) ==> (=) ==> impl) (node_all_total_in_refinement_domain).
    Proof. unfold Proper, equiv, "==>", impl. intros. subst.
    apply node_all_total_in_refinement_domain_of_equiv with (node1 := x); trivial.
    Qed.
    
Global Instance branch_total_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (=)) branch_total.
    Proof. unfold Proper, equiv, "==>", impl. intros. subst.
    apply branch_total_of_equiv. trivial. Qed.
    
Global Instance node_total_proper :
    Proper ((≡) ==> (=) ==> (=)) node_total.
    Proof. unfold Proper, equiv, "==>", impl. intros. subst.
    apply node_total_of_equiv. trivial. Qed.
    
Global Instance cell_total_minus_live_proper :
    Proper ((≡) ==> (=) ==> (=)) cell_total_minus_live.
Proof. unfold Proper, equiv, "==>", impl. intros. subst.
  unfold cell_total_minus_live. destruct x, y. unfold cell_equiv in H.
  destruct_ands.
  setoid_rewrite H0. trivial.
Qed.
    
Global Instance node_total_minus_live_proper :
    Proper ((≡) ==> (=) ==> (=)) (node_total_minus_live).
Proof. unfold Proper, equiv, "==>", impl. intros. subst.
    unfold node_total_minus_live. destruct x, y.
    unfold node_equiv in H. destruct_ands.
    setoid_rewrite H. setoid_rewrite H0. trivial.
Qed.
    
Lemma node_total_minus_live_triv active
 : node_total_minus_live triv_node active = unit.
Proof.
  unfold node_total_minus_live, triv_node.
    unfold branch_total. unfold cell_total_minus_live, triv_cell.
    unfold sum_reserved_over_lifetime. rewrite set_fold_empty.
    apply unit_dot. Qed.

Lemma project_fancy_preserves_inclusion idx (a b : M -> Prop)
  (inc: ∀ y : M, a y -> b y)
  : ∀ y : M, project_fancy idx a y → project_fancy idx b y.
Proof.
  unfold project_fancy, rel_project_fancy. intros.
    deex. destruct_ands. unfold tpcm_le in H. deex.
        subst y. exists b0. repeat split.
  - unfold tpcm_le. exists c. trivial.
  - trivial.
  - apply inc; trivial.
Qed.
 
Lemma node_view_inclusion lt1 lt2 node (li: multiset_le lt1 lt2)
  : (∀ y, node_view node lt2 y -> node_view node lt1 y)
with branch_view_inclusion lt1 lt2 branch idx (li: multiset_le lt1 lt2)
  : (∀ y, branch_view branch lt2 idx y -> branch_view branch lt1 idx y).
Proof.
 - destruct node.
    have Ib := branch_view_inclusion lt1 lt2 b 0 li.
    clear node_view_inclusion. clear branch_view_inclusion.
    repeat (rewrite node_view_rewrite).
    apply conjoin_umbrella_monotonic; trivial.
    apply cell_view_inclusion; trivial.
 - destruct branch.
  + have Ib := branch_view_inclusion lt1 lt2 branch (S idx) li.
    have In := node_view_inclusion lt1 lt2 n li.
    clear node_view_inclusion. clear branch_view_inclusion.
    unfold branch_view. fold branch_view. fold node_view.
    apply conjoin_umbrella_monotonic; trivial.
    apply project_fancy_preserves_inclusion; trivial.
  + intro. unfold branch_view. intro. trivial.
Qed.

Lemma node_view_le a b lt y : node_view (a ⋅ b) lt y -> node_view a lt y
with branch_view_le a b lt i y : branch_view (a ⋅ b) lt i y -> branch_view a lt i y.
Proof.
  - intro. destruct a, b.
    have IHb := branch_view_le b0 b lt 0. clear node_view_le. clear branch_view_le.
    unfold "⋅", cell_op, node_op in H.
    rewrite node_view_rewrite.
    rewrite node_view_rewrite in H.
    apply conjoin_umbrella_monotonic
        with (a := cell_view (c ⋅ c0) lt) (b := branch_view (b0 ⋅ b) lt 0); trivial.
    + intros. eapply cell_view_le_op. apply H0.
  - intro. destruct a, b.
    + have IHb := branch_view_le a b lt (S i). clear branch_view_le.
      have IHn := node_view_le n n0 lt. clear node_view_le.
      rewrite branch_view_rewrite.
      rewrite branch_view_rewrite in H. unfold "⋅", branch_op in H.
      apply conjoin_umbrella_monotonic
        with (a := (project_fancy i (node_view (n ⋅ n0) lt)))
        (b := (branch_view (a ⋅ b) lt (S i))); trivial.
      apply project_fancy_preserves_inclusion. trivial. 
    + unfold "⋅", branch_op in H. trivial.
    + unfold "⋅", branch_op. unfold branch_view, umbrella_unit. trivial.
    + unfold "⋅", branch_op. unfold branch_view, umbrella_unit. trivial.
Qed.

Lemma node_view_le2 a lt y z : node_view a lt y -> node_view a lt (dot y z).
Proof. rewrite node_view_rewrite. destruct a.
  have t := umbrella_closed_conjoin (cell_view c lt) (branch_view b lt 0).
  unfold umbrella_is_closed in t. apply t.
  intros. rewrite tpcm_comm. apply cell_view_closed. trivial.
Qed.

Lemma cell_view_of_node_view node lt y :
  node_view node lt y -> cell_view (cell_of_node node) lt y.
Proof. destruct node. unfold cell_of_node. rewrite node_view_rewrite.
  intro.
  unfold conjoin_umbrella in H. deex. destruct_ands.
  subst y. rewrite tpcm_comm.
  eapply cell_view_closed. trivial.
Qed.

End RollupRA.

(*
Print alls_valid_instance.

Context {M : Type}.
Context `{!EqDecision M}.
Context `{!TPCM M}.
Context {ref: Refinement M M}.


Local Instance valid_state : Valid (State M) := alls_valid_instance ref.

Definition a (x: State M) := ✓ x.
*)

Global Instance cell_live_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (=)) cell_live.
Proof. unfold Proper, "≡", cell_live, "==>". intros. destruct x, y.
  unfold cell_equiv in H. destruct_ands. trivial.
Qed.

Global Instance node_live_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (=)) node_live.
Proof.
  unfold Proper, "≡", "==>", node_live. intros. destruct x, y.
  unfold node_equiv in H. destruct_ands. setoid_rewrite H. trivial. Qed.

Global Instance branch_op_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (≡) ==> (≡)) (branch_op).
Proof.
  unfold Proper, "==>". intros.
  apply branch_equiv_trans with (branch2 := branch_op x y0).
  - apply branch_op_equiv. trivial.
  - apply branch_equiv_trans with (branch2 := branch_op y0 x).
    + apply branch_op_comm.
    + apply branch_equiv_trans with (branch2 := branch_op y0 y).
      * apply branch_op_equiv. trivial.
      * apply branch_op_comm.
Qed.
    
Global Instance node_op_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (≡) ==> (≡)) node_op.
Proof.
  unfold Proper, "==>". intros.
  apply node_equiv_trans with (node2 := node_op x y0).
  - apply node_op_equiv. trivial.
  - apply node_equiv_trans with (node2 := node_op y0 x).
    + apply node_op_comm.
    + apply node_equiv_trans with (node2 := node_op y0 y).
      * apply node_op_equiv. trivial.
      * apply node_op_comm.
Qed.
    
Global Instance cell_op_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (≡) ==> (≡)) cell_op.
Proof.
  unfold Proper, "==>". intros.
  apply cell_equiv_trans with (cell2 := cell_op x y0).
  - apply cell_op_equiv. trivial.
  - apply cell_equiv_trans with (cell2 := cell_op y0 x).
    + apply cell_op_comm.
    + apply cell_equiv_trans with (cell2 := cell_op y0 y).
      * apply cell_op_equiv. trivial.
      * apply cell_op_comm.
Qed.

Global Instance node_view_proper {M : Type} `{!EqDecision M} `{!TPCM M} roi :
    Proper ((≡) ==> (=) ==> (=) ==> impl) (node_view roi).
Proof.
  unfold Proper, "==>", impl. intros.
  apply node_view_of_equiv with (node1 := x); trivial.
  subst. trivial.
Qed.
    
Global Instance branch_view_proper {M : Type} `{!EqDecision M} `{!TPCM M} roi :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> impl) (branch_view roi).
Proof.
  unfold Proper, "==>", impl. intros.
  apply branch_view_of_equiv with (branch1 := x); trivial.
  subst. trivial.
Qed.
    
Global Instance cell_total_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (=) ==> (=)) cell_total.
Proof.
  unfold Proper, "==>", impl. intros.
  unfold cell_total. destruct x, y.
  unfold "≡", cell_equiv in H. destruct_ands.
  subst. setoid_rewrite H1. trivial.
Qed.
    
Lemma cell_total_split {M : Type} `{!EqDecision M} `{!TPCM M} (cell: Cell M) lt :
  cell_total cell lt = dot (cell_live cell) (cell_total_minus_live cell lt).
Proof.
  rewrite <- cell_live_plus_cell_total_minus_live. trivial. Qed.

Definition valid_totals {M : Type} `{!EqDecision M} `{!TPCM M} (refs: nat -> Refinement M M) (b: Branch M) (active: Lifetime) :=
    branch_all_total_in_refinement_domain refs b active 0
    /\ m_valid (branch_total refs b active 0).
    
Global Instance valid_totals_proper {M : Type} `{!EqDecision M} `{!TPCM M} roi :
    Proper ((≡) ==> (=) ==> impl) (valid_totals roi).
Proof. unfold Proper, "==>", impl, valid_totals. intros.
  destruct_ands. subst. split.
  - setoid_rewrite H in H1. trivial.
  - setoid_rewrite H in H2. trivial.
Qed.

Lemma cell_live_op {M : Type} `{!EqDecision M} `{!TPCM M} (c1 c2 : Cell M)
    : cell_live (c1 ⋅ c2) = dot (cell_live c1) (cell_live c2).
Proof.
  unfold cell_live, "⋅", cell_op. destruct c1, c2. trivial. Qed.
 
Lemma node_live_op {M : Type} `{!EqDecision M} `{!TPCM M} (n1 n2 : Node M) : node_live (n1 ⋅ n2) = dot (node_live n1) (node_live n2).
Proof.
  unfold node_live, "⋅", node_op. destruct n1, n2. apply cell_live_op. Qed.

Global Instance cell_reserved_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (≡)) cell_reserved.
Proof.
  unfold Proper, "==>", impl. intros.
  unfold cell_reserved. destruct x, y.
  unfold "≡", cell_equiv in H. intuition.
Qed.

Global Instance cell_view_proper {M : Type} `{!EqDecision M} `{!TPCM M} :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) cell_view. Admitted.
