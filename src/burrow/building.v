From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Coq.Lists.List.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.gmap_utils.
Require Import Burrow.rollup.
Require Import Burrow.indexing.
Require Import Burrow.locations.

Section BuildOne.
  Context {M} `{!EqDecision M, !TPCM M}.

  Fixpoint unwalk (j: nat) (b: Branch M) :=
    match j with
    | 0 => b
    | S j => unwalk j (BranchCons triv_node b)
    end.
  
  Definition unhop (j: nat) (b: Branch M) :=
    unwalk j (BranchCons (CellNode triv_cell b) BranchNil).
  
  Fixpoint unhops (js: list nat) (b: Branch M) :=
    match js with
    | [] => b
    | (j :: ks) => unhop j (unhops ks b)
    end.
  
  Definition build_of_branch (branch: Branch M) (pl: PathLoc) : Branch M :=
    match pl with
    | (p, i) => unhops p (unwalk i branch)
    end.
  
  Definition build_of_node (node: Node M) (pl: PathLoc) : Branch M :=
    build_of_branch (BranchCons node BranchNil) pl.
    
  Definition build_of_cell (cell: Cell M) (pl: PathLoc) : Branch M :=
    build_of_node (CellNode cell BranchNil) pl.
    
  Lemma walk_unwalk (branch: Branch M) j
    : walk j (unwalk j branch) = branch.
  Proof.
    generalize branch. clear branch.
    induction j; trivial.
    cbn [walk]. cbn [unwalk]. intro. rewrite IHj. unfold branch_of_branch. trivial. Qed.
    
  Lemma hop_unhop (branch: Branch M) j
    : hop j (unhop j branch) = branch.
  Proof.
    unfold hop, unhop. rewrite walk_unwalk. unfold node_of_branch, branch_of_node.
    trivial. Qed.
    
  Lemma hops_unhops (branch: Branch M) js
    : hops js (unhops js branch) = branch.
  Proof.
    generalize branch. clear branch.
    induction js; trivial.
    cbn [hops]. cbn [unhops]. intro. rewrite hop_unhop. rewrite IHjs. trivial. Qed.
    
  Lemma branch_of_pl_build_of_branch (branch: Branch M) (pl: PathLoc)
    : branch_of_pl (build_of_branch branch pl) pl = branch.
  Proof.
    unfold branch_of_pl, build_of_branch. destruct pl. rewrite hops_unhops.
      rewrite walk_unwalk. trivial. Qed.
    
  Lemma node_of_pl_build_of_node (node: Node M) (pl: PathLoc)
    : node_of_pl (build_of_node node pl) pl = node.
  Proof.
    unfold node_of_pl, build_of_node.
    rewrite branch_of_pl_build_of_branch. unfold node_of_branch. trivial. Qed.
    
  Lemma cell_of_pl_build_of_cell (cell: Cell M) (pl: PathLoc)
    : cell_of_pl (build_of_cell cell pl) pl = cell.
  Proof.
    unfold cell_of_pl. unfold build_of_cell. rewrite node_of_pl_build_of_node.
    unfold cell_of_node. trivial. Qed.
    
  Lemma unwalk_add p q b
  : unwalk (p + q) b = unwalk q (unwalk p b).
  Proof. generalize b. clear b. induction p.
    - trivial.
    - intro. replace (S p + q) with (S (p + q)) by lia.
      cbn [unwalk]. rewrite IHp. trivial.
  Qed.
  
  Lemma node_of_branch_unwalk_nonzero j b
    (nz: j ≠ 0) : node_of_branch (unwalk j b) = triv_node.
  Proof.
    generalize b. clear b. induction j.
    - contradiction.
    - cbn [unwalk]. destruct j.
      + unfold unwalk. unfold node_of_branch. trivial.
      + intro. apply IHj. lia.
  Qed.
  
  Lemma walk_eq_BranchNil_nonzero j n
    (nz: j ≠ 0) : (walk j (BranchCons n BranchNil)) = BranchNil.
  Proof.
    induction j.
    - contradiction.
    - cbn [walk]. destruct j.
      + trivial.
      + rewrite IHj; trivial. lia.
  Qed.

  Lemma node_of_branch_walk_nonzero j n
    (nz: j ≠ 0) : node_of_branch (walk j (BranchCons n BranchNil)) = triv_node.
  Proof.
    rewrite walk_eq_BranchNil_nonzero; trivial.
  Qed.

  Lemma node_of_branch_walk_unwalk_i_ne (n: Node M) (i i': nat)
    (ne : i ≠ i')
    : node_of_branch (walk i (unwalk i' (BranchCons n BranchNil))) = triv_node.
  Proof.
    have h : Decision (i < i') by solve_decision. destruct h.
    - replace i' with ((i' - i) + i) by lia.
      rewrite unwalk_add. rewrite walk_unwalk.
      apply node_of_branch_unwalk_nonzero. lia.
    - replace i with (i' + (i - i')) by lia.
      rewrite walk_add. rewrite walk_unwalk.
      apply node_of_branch_walk_nonzero. lia.
  Qed.
    
  Lemma node_of_pl_build_of_cell_i_ne (node: Node M) (p : list nat) (i i' : nat)
    (ne: i ≠ i')
    : node_of_pl (build_of_node node (p, i')) (p, i) = triv_node.
  Proof.
    unfold node_of_pl, build_of_node. 
    unfold branch_of_pl, build_of_branch.
    rewrite hops_unhops. apply node_of_branch_walk_unwalk_i_ne. trivial.
  Qed.
    
  Lemma cell_of_pl_build_of_cell_i_ne (cell: Cell M) (p : list nat) (i i' : nat)
    (ne: i ≠ i')
    : cell_of_pl (build_of_cell cell (p, i')) (p, i) = triv_cell.
  Proof.
    unfold cell_of_pl, build_of_cell. rewrite node_of_pl_build_of_cell_i_ne; trivial.
  Qed.
    
  Lemma cell_of_pl_build_of_cell_p_ne (cell: Cell M) (p p' : list nat) (i i' : nat)
    (ne: p ≠ p')
    : cell_of_pl (build_of_cell cell (p, i')) (p', i) = triv_cell. Admitted.
    
  Lemma cell_of_pl_build_of_cell_ne (cell: Cell M) (pl pl': PathLoc)
    (ne: pl ≠ pl')
    : cell_of_pl (build_of_cell cell pl') pl = triv_cell.
  Proof.
    generalize ne. generalize pl'. clear ne. clear pl'.
    destruct pl. rename l into p. rename n into i.
    destruct pl'. rename l into p'. rename n into i'.
    intro.
    have h : Decision (p = p') by solve_decision. destruct h.
    - subst p'. assert (i ≠ i') by intuition.
      apply cell_of_pl_build_of_cell_i_ne; trivial.
    - apply cell_of_pl_build_of_cell_p_ne; trivial. crush.
  Qed.
    
End BuildOne.

Section Build.
  Context {RI} `{!EqDecision RI} `{!Countable RI} {M} `{!EqDecision M, !TPCM M}.

  Definition buildfn cell : PathLoc -> Branch M -> Branch M :=
      (λ pl b , b ⋅ build_of_cell cell pl).

  Definition build (loc: Loc RI) (cell: Cell M) : Branch M :=
    set_fold (buildfn cell) BranchNil (pls_of_loc loc).
    
  Lemma cell_of_pl_set_fold_not_in (cell: Cell M) (s: gset PathLoc) (pl: PathLoc)
    (is_in: pl ∉ s)
    : cell_of_pl (set_fold (buildfn cell) BranchNil s) pl ≡ triv_cell.
  Proof. apply set_easy_induct_strong.
    - unfold cell_of_pl. unfold node_of_pl. setoid_rewrite branch_of_pl_BranchNil.
        unfold node_of_branch. unfold cell_of_node, triv_node. trivial.
    - intros. unfold buildfn. setoid_rewrite <- cell_of_pl_op.
      assert (pl ≠ a) by crush.
      rewrite cell_of_pl_build_of_cell_ne; trivial.
      setoid_rewrite H0. apply op_trivial_cell. unfold cell_trivial, triv_cell. intuition.
  Qed.

  Lemma cell_of_pl_set_fold_in (cell: Cell M) (s: gset PathLoc) (pl: PathLoc)
    (is_in: pl ∈ s)
    : cell_of_pl (set_fold (buildfn cell) BranchNil s) pl ≡ cell. Admitted.
    
  Lemma build_spec
      (loc: Loc RI) (cell: Cell M)
    : (∀ pl , pl ∈ pls_of_loc loc -> cell_of_pl (build loc cell) pl ≡ cell).
  Proof.
    intros. unfold build. apply cell_of_pl_set_fold_in. trivial. Qed.
  
  Lemma build_rest_triv
      (loc: Loc RI) (cell: Cell M)
    : (∀ pl , ¬(pl ∈ pls_of_loc loc) -> cell_of_pl (build loc cell) pl ≡ triv_cell).
  Proof.
    intros. unfold build. apply cell_of_pl_set_fold_not_in. trivial. Qed.
End Build.

Global Instance build_proper
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (loc: Loc RI) : Proper ((≡) ==> (≡)) (build loc). Admitted.

Lemma branch_is_trivial_build_triv_cell
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
  (loc: Loc RI) : branch_trivial (build loc triv_cell). Admitted.

Lemma build_op
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
    (i: Loc RI) (x y: Cell M) : build i (x ⋅ y) ≡ build i x ⋅ build i y.
Admitted.

Lemma node_of_pl_build_eq
  {M} `{!EqDecision M, !TPCM M}
  {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI} `{!RefinementIndex M RI}
  (pl1 pl2: PathLoc) (loc l1: Loc RI) (c1: Cell M)
  (pl1_in: pl1 ∈ pls_of_loc loc)
  (pl2_in: pl2 ∈ pls_of_loc loc)
  : node_of_pl (build l1 c1) pl1 ≡ node_of_pl (build l1 c1) pl2. Admitted.
