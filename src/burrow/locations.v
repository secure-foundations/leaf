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

(*Context {M: Type} `{!EqDecision M, !TPCM M}.
Context `{Countable RefinementIndex}.
Context `{EqDecision RefinementIndex}.
Context (ref_map : RefinementIndex -> Refinement M M).*)

Class RefinementIndex (M: Type) `{!EqDecision M} `{!TPCM M} (RI: Type) := {
    refinement_of : RI -> Refinement M M;
    triv_ri : RI;
    left_ri : RI;
    right_ri : RI;
    pair_up : M -> M -> M;
    
    self_eq_pair : ∀ m , m = pair_up
        (rel M M (refinement_of left_ri) m)
        (rel M M (refinement_of right_ri) m) ;
    refinement_of_left_pair_up : ∀ a b ,
     (rel M M (refinement_of (left_ri)) (pair_up a b)) = a ;
    refinement_of_right_pair_up : ∀ a b ,
     (rel M M (refinement_of (right_ri)) (pair_up a b)) = b ;
    dot_pair_up : ∀ a b c d ,
      dot (pair_up a b) (pair_up c d) = pair_up (dot a c) (dot b d) ;
}.
Global Arguments triv_ri {M}%type_scope {EqDecision0 TPCM0} _ {RefinementIndex}.
Global Arguments left_ri {M}%type_scope {EqDecision0 TPCM0} _ {RefinementIndex}.
Global Arguments right_ri {M}%type_scope {EqDecision0 TPCM0} _ {RefinementIndex}.
Global Arguments pair_up {M}%type_scope {EqDecision0 TPCM0} _%type_scope {RefinementIndex} _ _.

Inductive Loc (RI: Type) `{!EqDecision RI, !Countable RI} :=
  | BaseLoc : nat -> Loc RI
  | ExtLoc : nat -> RI -> Loc RI -> Loc RI
  | CrossLoc : Loc RI -> Loc RI -> Loc RI
.
Arguments BaseLoc _%type_scope {EqDecision0 Countable0} _%nat_scope.
Arguments ExtLoc {RI}%type_scope {EqDecision0 Countable0} _%nat_scope _ _.
Arguments CrossLoc {RI}%type_scope {EqDecision0 Countable0} _ _.

Global Instance loc_eqdec RI `{!EqDecision RI} `{!Countable RI} : EqDecision (Loc RI).
Proof. solve_decision. Defined.

Global Instance loc_countable RI `{!EqDecision RI} `{!Countable RI} : Countable (Loc RI).
Proof.
  set (enc :=
    fix go e :=
      match e with
      | BaseLoc _ i => GenNode 0 [GenLeaf (inl i)]
      | ExtLoc i ri l => GenNode 1 [GenLeaf (inl i) ; GenLeaf (inr ri) ; go l]
      | CrossLoc l1 l2 => GenNode 2 [go l1; go l2]
      end : gen_tree (nat + RI)
    ).
  set (dec :=
    fix go e :=
      match e with
      | GenNode 0 [GenLeaf (inl i)] => BaseLoc RI i
      | GenNode 1 [GenLeaf (inl i) ; GenLeaf (inr ri) ; e] => ExtLoc i ri (go e)
      | GenNode 2 [e1; e2] => CrossLoc (go e1) (go e2)
      | _ => BaseLoc RI 0 (* dummy *)
      end
    ).
 refine (inj_countable' enc dec _).
 refine (fix go (e : Loc RI) {struct e} := _).
 destruct e; simpl; f_equal; apply go.
Qed.

Inductive StepDesc (RI: Type) `{!EqDecision RI, !Countable RI} :=
  | SDBase : nat -> StepDesc RI
  | SDExt : nat -> RI -> StepDesc RI
  | SDLeft : Loc RI -> StepDesc RI
  | SDRight : Loc RI -> StepDesc RI
.
(*Arguments SDBase {_}%type_scope {EqDecision0 Countable0} _%nat_scope.*)
Arguments SDExt {_}%type_scope {EqDecision0 Countable0} _%nat_scope _.
Arguments SDLeft {_}%type_scope {EqDecision0 Countable0} _.
Arguments SDRight {_}%type_scope {EqDecision0 Countable0} _.

Global Instance stepdesc_eqdec RI `{!EqDecision RI} `{!Countable RI} : EqDecision (StepDesc RI). Proof. solve_decision. Defined.

Global Instance stepdesc_countable RI `{!EqDecision RI} `{!Countable RI} : Countable (StepDesc RI).
Proof.
  set (enc :=
    fix go e :=
      match e with
      | SDBase _ i => inl i
      | SDExt i ri => inr (inl (i, ri))
      | SDLeft l => inr (inr (inl l))
      | SDRight l => inr (inr (inr l))
      end : nat + ((nat * RI) + (Loc RI + Loc RI))
    ).
  set (dec :=
    fix go e :=
      match e with
      | inl i => SDBase RI i
      | inr (inl (i, ri)) => SDExt i ri
      | inr (inr (inl l)) => SDLeft l
      | inr (inr (inr l)) => SDRight l
      end
    ).
 refine (inj_countable' enc dec _).
 intro.
 destruct x; simpl; f_equal.
Qed.

Definition nat_of_basestep RI `{!EqDecision RI, !Countable RI} (alpha:nat) : nat :=
  encode_nat (SDBase RI alpha).

Definition nat_of_extstep {RI} `{!EqDecision RI, !Countable RI} (alpha:nat) (ri: RI) : nat :=
  encode_nat (SDExt alpha ri).

Definition nat_of_leftstep RI `{!EqDecision RI, !Countable RI} (gamma2: Loc RI) : nat :=
  encode_nat (SDLeft gamma2).

Definition nat_of_rightstep RI `{!EqDecision RI, !Countable RI} (gamma1: Loc RI) : nat :=
  encode_nat (SDRight gamma1).

Definition augment (j: nat) (pl: PathLoc) := match pl with (p, i) => (p++[i], j) end.

Fixpoint pls_of_loc {RI} `{!EqDecision RI} `{!Countable RI}
    (loc: Loc RI) : (gset PathLoc) :=
  match loc with
  | BaseLoc _ alpha => {[ ([], nat_of_basestep RI alpha) ]}
  | ExtLoc alpha ri base => set_map (augment (nat_of_extstep alpha ri)) (pls_of_loc base) 
  | CrossLoc l r =>
        set_map (augment (nat_of_leftstep RI r)) (pls_of_loc l)
      ∪ set_map (augment (nat_of_rightstep RI l)) (pls_of_loc r)
  end.
    

Definition ri_of_nat (RI : Type)
    {M} `{!EqDecision M, !TPCM M}
    {RI} `{!EqDecision RI} `{!Countable RI} `{!RefinementIndex M RI}
    (n: nat) : RI :=
  match decode_nat n with
  | None => triv_ri RI
  | Some (SDBase _ _) => triv_ri RI
  | Some (SDExt _ ri) => ri
  | Some (SDLeft _) => left_ri RI
  | Some (SDRight _) => right_ri RI
  end.

Definition refinement_of_nat
        M `{!EqDecision M, !TPCM M}
        RI `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
        (idx: nat) : Refinement M M := refinement_of (ri_of_nat RI idx).

Lemma leftproject_le_left
        {M} `{!EqDecision M, !TPCM M}
        {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
        (m1 m2 c : M)
  (rdef: rel_defined M M (refinement_of (left_ri RI)) (dot (pair_up RI m1 m2) c))
  : tpcm_le m1 (rel M M (refinement_of (left_ri RI)) (dot (pair_up RI m1 m2) c)).
Proof.
  rewrite (self_eq_pair c). rewrite dot_pair_up.
  rewrite refinement_of_left_pair_up.
  apply le_add_right_side. apply self_le_self.
Qed.
  
Lemma rightproject_le_right
        {M} `{!EqDecision M, !TPCM M}
        {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}
        (m1 m2 c : M)
  (rdef: rel_defined M M (refinement_of (right_ri RI)) (dot (pair_up RI m1 m2) c))
  : tpcm_le m2 (rel M M (refinement_of (right_ri RI)) (dot (pair_up RI m1 m2) c)).
Proof.
  rewrite (self_eq_pair c). rewrite dot_pair_up.
  rewrite refinement_of_right_pair_up.
  apply le_add_right_side. apply self_le_self.
Qed.

Definition pls_of_loc_from_left
    {RI} `{!EqDecision RI, !Countable RI}
  (l r: Loc RI) : gset PathLoc :=
    set_map (augment (nat_of_leftstep RI r)) (pls_of_loc l).

Definition pls_of_loc_from_right
    {RI} `{!EqDecision RI, !Countable RI}
  (l r: Loc RI) : gset PathLoc :=
  set_map (augment (nat_of_rightstep RI l)) (pls_of_loc r).

Section LocationsLemmas.

Context {RI} `{!EqDecision RI, !Countable RI}.

(*Context {M} `{!EqDecision M, !TPCM M}.
Context {!RefinementIndex M RI}.*)

Fixpoint any_pl_of_loc
    (loc: Loc RI) : PathLoc :=
  match loc with
  | BaseLoc _ alpha => ([], nat_of_basestep RI alpha)
  | ExtLoc alpha ri base => augment (nat_of_extstep alpha ri) (any_pl_of_loc base)
  | CrossLoc l r =>
        augment (nat_of_leftstep RI r) (any_pl_of_loc l)
  end.

Lemma any_pl_of_loc_is_of_loc
  (loc: Loc RI) : any_pl_of_loc loc ∈ pls_of_loc loc.
Proof.
  induction loc.
  - unfold any_pl_of_loc, pls_of_loc. set_solver.
  - unfold any_pl_of_loc, pls_of_loc. rewrite elem_of_map.
      exists (any_pl_of_loc loc). split; trivial.
  - unfold any_pl_of_loc, pls_of_loc. rewrite elem_of_union. left. rewrite elem_of_map.
      exists (any_pl_of_loc loc1). split; trivial.
Qed.

Lemma false_of_single_eq_augment i x pl : ([], i) = augment pl x -> False.
Proof. unfold augment. destruct x. intro. inversion H.
  assert (length [] = length (l ++ [n])) by (f_equal; trivial).
  simpl in H0. rewrite app_length in H0. simpl in H0. lia.
Qed.

Lemma eq_of_augment_eq a x a' x' : augment a x = augment a' x' -> a = a' /\ x = x'.
Proof.
  intros. unfold augment in H. destruct x, x'. inversion H. subst. split; trivial.
  assert ((List.last (l ++ [n]) 0) = n) by (apply last_last).
  assert ((List.last (l0 ++ [n0]) 0) = n0) by (apply last_last).
  assert ((List.removelast (l ++ [n])) = l) by (apply removelast_last).
  assert ((List.removelast (l0 ++ [n0])) = l0) by (apply removelast_last).
  rewrite H1 in H0. rewrite H1 in H3.
  crush.
Qed.

Lemma locs_equal_of_pl_in
  : ∀ (loc1 loc2: Loc RI) pl ,
  (pl ∈ pls_of_loc loc1) -> (pl ∈ pls_of_loc loc2) -> loc1 = loc2.
Proof.
induction loc1.
  - intro. intro. unfold pls_of_loc. rewrite elem_of_singleton. intro. subst. destruct loc2.
    + rewrite elem_of_singleton. intro.  inversion H. unfold nat_of_basestep in H1.
      generalize H1. rewrite inj_iff. crush.
    + rewrite elem_of_map. intro. deex. destruct_ands.
        exfalso. eapply false_of_single_eq_augment. apply H.
    + rewrite elem_of_union. rewrite elem_of_map. rewrite elem_of_map. intro. destruct H.
      * deex. destruct_ands. exfalso. eapply false_of_single_eq_augment. apply H.
      * deex. destruct_ands. exfalso. eapply false_of_single_eq_augment. apply H.
  - intro. intro. unfold pls_of_loc. rewrite elem_of_map. intros. deex. destruct_ands.
      subst pl. destruct loc2.
    + generalize H0. rewrite elem_of_singleton. clear H0. intro.
      exfalso. symmetry in H. eapply false_of_single_eq_augment. apply H.
    + generalize H0. rewrite elem_of_map. intro. clear H0. deex. destruct_ands.
      have j := eq_of_augment_eq _ _ _ _ H. destruct_ands.
        unfold nat_of_extstep in H2.
        generalize H2. rewrite inj_iff. intro. inversion H4. subst. f_equal.
        apply IHloc1 with (pl:=x0); trivial.
    + generalize H0. clear H0.
      rewrite elem_of_union. rewrite elem_of_map. rewrite elem_of_map. intro. destruct H.
      * deex. destruct_ands.
        have j := eq_of_augment_eq _ _ _ _ H. unfold nat_of_extstep, nat_of_leftstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. discriminate.
      * deex. destruct_ands.
        have j := eq_of_augment_eq _ _ _ _ H. unfold nat_of_extstep, nat_of_rightstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. discriminate.
   - intro. intro. unfold pls_of_loc. rewrite elem_of_union. rewrite elem_of_map.
     rewrite elem_of_map. destruct loc2.
     + intro. rewrite elem_of_singleton. destruct H.
      * deex. destruct_ands. intro. subst pl.
          exfalso. eapply false_of_single_eq_augment. symmetry in H1. apply H1.
      * deex. destruct_ands. intro. subst pl.
          exfalso. eapply false_of_single_eq_augment. symmetry in H1. apply H1.
     + intro. rewrite elem_of_map. intro. deex. destruct_ands. destruct H.
      * deex. destruct_ands. subst pl.
        have j := eq_of_augment_eq _ _ _ _ H0. unfold nat_of_extstep, nat_of_leftstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. discriminate.
      * deex. destruct_ands. subst pl.
        have j := eq_of_augment_eq _ _ _ _ H0. unfold nat_of_extstep, nat_of_rightstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. discriminate.
     + rewrite elem_of_union. rewrite elem_of_map. rewrite elem_of_map. intros.
        destruct H; destruct H0; deex; destruct_ands.
      * subst pl.
        have j := eq_of_augment_eq _ _ _ _ H0. unfold nat_of_leftstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. inversion H. subst. f_equal.
        apply IHloc1_1 with (pl := x); trivial.
      * deex. destruct_ands. subst pl.
        have j := eq_of_augment_eq _ _ _ _ H0. unfold nat_of_leftstep, nat_of_rightstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. discriminate.
      * deex. destruct_ands. subst pl.
        have j := eq_of_augment_eq _ _ _ _ H0. unfold nat_of_leftstep, nat_of_rightstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. discriminate.
      * subst pl.
        have j := eq_of_augment_eq _ _ _ _ H0. unfold nat_of_rightstep in j.
        generalize j. rewrite inj_iff. intro. destruct_ands. inversion H. subst. f_equal.
        apply IHloc1_2 with (pl := x); trivial.
Qed.

Ltac derive_contra_own_child pr elem :=
    let X := fresh in
    let J := fresh in
    generalize pr; generalize elem; intro X; induction X; try discriminate;
    intro J; inversion J; subst; intuition.
  
Lemma pl_not_in_of_pl_in_extloc
    pl alpha (ri: RI) gamma
  : pl ∈ pls_of_loc (ExtLoc alpha ri gamma) -> pl ∉ pls_of_loc gamma.
Proof.
  intros. intro. have j:= locs_equal_of_pl_in _ _ _ H H0.
  
    (*generalize j; generalize gamma; intro X; induction X; try discriminate.
    intro J; inversion J. subst; intuition.*)
  
    derive_contra_own_child j gamma.
Qed.

Lemma refinement_of_nat_eq_refinement_of_of_in_pls_of_loc
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
    p i alpha ri gamma
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : refinement_of_nat M RI i = refinement_of ri.
Proof. unfold refinement_of_nat. f_equal.
    unfold pls_of_loc in is_in. generalize is_in. clear is_in.
    rewrite elem_of_map. intro. deex. destruct_ands. unfold augment in H.
    destruct x. inversion H. subst i. unfold ri_of_nat, nat_of_extstep.
    rewrite decode_encode_nat. trivial.
Qed.

Lemma pl_in_pls_of_loc_extloc
  p i alpha ri (gamma: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma)
  : (p++[i], nat_of_extstep alpha ri) ∈ pls_of_loc (ExtLoc alpha ri gamma).
Proof. unfold pls_of_loc. rewrite elem_of_map. exists (p, i). split; trivial. Qed.

Lemma pl_in_pls_of_loc_cross_left
  p i (gamma1 gamma2: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma1)
  : (p++[i], nat_of_leftstep RI gamma2) ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Proof. unfold pls_of_loc. rewrite elem_of_union.
  rewrite elem_of_map. rewrite elem_of_map. left. exists (p, i). split; trivial. Qed.

Lemma pl_in_pls_of_loc_cross_right
  p i (gamma1 gamma2: Loc RI)
  (pi_in: (p, i) ∈ pls_of_loc gamma2)
  : (p++[i], nat_of_rightstep RI gamma1) ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Proof. unfold pls_of_loc. rewrite elem_of_union.
  rewrite elem_of_map. rewrite elem_of_map. right. exists (p, i). split; trivial. Qed.

Lemma ri_of_nat_nat_of_extstep
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  alpha (ri: RI)
  : (ri_of_nat RI (nat_of_extstep alpha ri) = ri).
Proof. unfold ri_of_nat, nat_of_extstep. rewrite decode_encode_nat. trivial. Qed.
  
Lemma ri_of_nat_nat_of_leftstep
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  (gamma2 : Loc RI)
  : (ri_of_nat RI (nat_of_leftstep RI gamma2)) = left_ri RI.
Proof. unfold ri_of_nat, nat_of_leftstep. rewrite decode_encode_nat. trivial. Qed.
  
Lemma ri_of_nat_nat_of_rightstep
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  (gamma1 : Loc RI)
  : (ri_of_nat RI (nat_of_rightstep RI gamma1)) = right_ri RI.
Proof. unfold ri_of_nat, nat_of_rightstep. rewrite decode_encode_nat. trivial. Qed.

Lemma i_value_of_pls_of_loc_ext p i gamma alpha (ri: RI)
  (in_pls: (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
  : i = nat_of_extstep alpha ri.
Proof. unfold pls_of_loc in in_pls. generalize in_pls. clear in_pls.
    rewrite elem_of_map. intro. deex. destruct_ands. unfold augment in H.
    destruct x. inversion H. trivial. Qed.
  
Lemma i_value_of_pls_of_base p i alpha
  (in_pls: (p, i) ∈ pls_of_loc (BaseLoc RI alpha))
  : i = nat_of_basestep RI alpha.
Proof. unfold pls_of_loc in in_pls. generalize in_pls. clear in_pls.
    rewrite elem_of_singleton. intro. deex. destruct_ands. unfold augment in H.
    inversion H. trivial. Qed.

Lemma ri_of_nat_nat_of_basestep
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
    alpha
  : ri_of_nat RI (nat_of_basestep RI alpha) = triv_ri RI.
Proof.
  unfold ri_of_nat, nat_of_basestep. rewrite decode_encode_nat. trivial. Qed.
  
Lemma rel_refinement_of_triv_ri_defined
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
     (m: M)
    (isval: m_valid m)
  : rel_defined M M (refinement_of (triv_ri RI)) m.
  Admitted.
  
Lemma rel_refinement_of_triv_ri_eq_unit
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  (m: M)
  : rel M M (refinement_of (triv_ri RI)) m = unit. Admitted.
  
Lemma pl_in_crossloc_of_pl_in_left pl (gamma1 gamma2: Loc RI)
  : pl ∈ pls_of_loc_from_left gamma1 gamma2 -> pl ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Proof.
  unfold pls_of_loc_from_left, pls_of_loc. rewrite elem_of_union. intuition.
Qed.
  
Lemma pl_in_crossloc_of_pl_in_right
  pl (gamma1 gamma2: Loc RI)
  : pl ∈ pls_of_loc_from_right gamma1 gamma2 -> pl ∈ pls_of_loc (CrossLoc gamma1 gamma2).
Proof.
  unfold pls_of_loc_from_left, pls_of_loc. rewrite elem_of_union. intuition.
Qed.

Lemma pl_not_in_left_of_pl_in_left
    pl (gamma1 gamma2: Loc RI)
  : pl ∈ pls_of_loc_from_left gamma1 gamma2 -> pl ∉ pls_of_loc gamma1.
Proof.
  intros. intro.
  have k := pl_in_crossloc_of_pl_in_left _ _ _ H.
  have j := locs_equal_of_pl_in _ _ _ k H0.
  derive_contra_own_child j gamma1.
Qed.
  
Lemma pl_not_in_right_of_pl_in_left
    pl (gamma1 gamma2: Loc RI)
  : pl ∈ pls_of_loc_from_left gamma1 gamma2 -> pl ∉ pls_of_loc gamma2.
Proof.
  intros. intro.
  have k := pl_in_crossloc_of_pl_in_left _ _ _ H.
  have j := locs_equal_of_pl_in _ _ _ k H0.
  derive_contra_own_child j gamma2.
Qed.
  
Lemma pl_not_in_right_of_pl_in_right
  pl (gamma1 gamma2: Loc RI)
  : pl ∈ pls_of_loc_from_right gamma1 gamma2 -> pl ∉ pls_of_loc gamma2.
Proof.
  intros. intro.
  have k := pl_in_crossloc_of_pl_in_right _ _ _ H.
  have j := locs_equal_of_pl_in _ _ _ k H0.
  derive_contra_own_child j gamma2.
Qed.
  
Lemma pl_not_in_left_of_pl_in_right
  pl (gamma1 gamma2: Loc RI)
  : pl ∈ pls_of_loc_from_right gamma1 gamma2 -> pl ∉ pls_of_loc gamma1.
Proof.
  intros. intro.
  have k := pl_in_crossloc_of_pl_in_right _ _ _ H.
  have j := locs_equal_of_pl_in _ _ _ k H0.
  derive_contra_own_child j gamma1.
Qed.
  
Lemma y_is_pair_of_rel_defined_refinement_of_left
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
    x y
  (rd: rel_defined M M (refinement_of (left_ri RI)) (dot x y))
  : ∃ k1 k2 , y = (pair_up RI k1 k2). Admitted.
  
Lemma y_is_pair_of_rel_defined_refinement_of_right
    {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
    x y
  (rd: rel_defined M M (refinement_of (right_ri RI)) (dot x y))
  : ∃ k1 k2 , y = (pair_up RI k1 k2). Admitted.

Lemma rel_defined_refinement_of_left_pair_up
  {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  a b
  (aval: m_valid a)
  (bval: m_valid b)
    : (rel_defined M M (refinement_of (left_ri RI)) (pair_up RI a b)). Admitted.
    
Lemma rel_defined_refinement_of_right_pair_up
  {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  a b
  (aval: m_valid a)
  (bval: m_valid b)
    : (rel_defined M M (refinement_of (right_ri RI)) (pair_up RI a b)). Admitted.
    
Lemma m_valid_left_of_rel_defined_refinement_of_left_pair_up
  {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  a b
  (rd: rel_defined M M (refinement_of (left_ri RI)) (pair_up RI a b))
  : m_valid a. Admitted.
  
Lemma m_valid_right_of_rel_defined_refinement_of_left_pair_up
  {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  a b
  (rd: rel_defined M M (refinement_of (left_ri RI)) (pair_up RI a b))
  : m_valid b. Admitted.
  
Lemma m_valid_left_of_rel_defined_refinement_of_right_pair_up
  {M} `{!EqDecision M, !TPCM M} `{!RefinementIndex M RI}
  a b
  (rd: rel_defined M M (refinement_of (right_ri RI)) (pair_up RI a b))
  : m_valid a. Admitted.

Lemma i_value_of_pls_of_loc_from_left
  (p: list nat) (i: nat) (gamma1 gamma2: Loc RI)
  (in_pls: (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
  : i = nat_of_leftstep RI gamma2.
Proof. unfold pls_of_loc in in_pls. generalize in_pls. clear in_pls.
    rewrite elem_of_map. intro. deex. destruct_ands. unfold augment in H.
    destruct x. inversion H. trivial. Qed.
  
Lemma i_value_of_pls_of_loc_from_right
  p i gamma1 gamma2
  (in_pls: (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
  : i = nat_of_rightstep RI gamma1.
Proof. unfold pls_of_loc in in_pls. generalize in_pls. clear in_pls.
    rewrite elem_of_map. intro. deex. destruct_ands. unfold augment in H.
    destruct x. inversion H. trivial. Qed.
  
Lemma exists_in_pls_of_loc_from_left
  (gamma1 gamma2: Loc RI)
  : ∃ pl, pl ∈ pls_of_loc_from_left gamma1 gamma2.
Proof.
  unfold pls_of_loc_from_left.
  exists (augment (nat_of_leftstep RI gamma2) (any_pl_of_loc gamma1)).
  rewrite elem_of_map. exists (any_pl_of_loc gamma1). split; trivial.
  apply any_pl_of_loc_is_of_loc.
Qed.
  
Lemma exists_in_pls_of_loc_from_right
  (gamma1 gamma2: Loc RI)
  : ∃ pl, pl ∈ pls_of_loc_from_right gamma1 gamma2.
Proof.
  unfold pls_of_loc_from_right.
  exists (augment (nat_of_rightstep RI gamma1) (any_pl_of_loc gamma2)).
  rewrite elem_of_map. exists (any_pl_of_loc gamma2). split; trivial.
  apply any_pl_of_loc_is_of_loc.
Qed.

Lemma plsplit_in_of_pls_of_loc_from_left (gamma1 gamma2: Loc RI) (p: list nat) (i: nat)
  (pi_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
  : plsplit p ∈ pls_of_loc gamma1.
Proof.
  unfold pls_of_loc_from_left in pi_in.
  generalize pi_in. clear pi_in. rewrite elem_of_map. intro pi_in. deex. destruct_ands.
  unfold augment in H. destruct x. inversion H. subst. rewrite plsplit_app.
  trivial.
Qed.
  
Lemma plsplit_in_of_pls_of_loc_from_right (gamma1 gamma2: Loc RI) p i
  (pi_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
  : plsplit p ∈ pls_of_loc gamma2.
Proof.
  unfold pls_of_loc_from_left in pi_in.
  generalize pi_in. clear pi_in. rewrite elem_of_map. intro pi_in. deex. destruct_ands.
  unfold augment in H. destruct x. inversion H. subst. rewrite plsplit_app.
  trivial.
Qed.
  
Lemma q_eq_pi_of_plsplit_cross (gamma1 gamma2: Loc RI) (q p: list nat) i j
  (q_in: (q, j) ∈ pls_of_loc (CrossLoc gamma1 gamma2) )
  (eq: plsplit q = (p, i))
  : q = p ++ [i].
Admitted.

Lemma pl_not_in_pls_of_loc_cross_from_in_left pl (gamma1 gamma2: Loc RI)
  (pl_in : pl ∈ pls_of_loc gamma1)
  : pl ∉ pls_of_loc (CrossLoc gamma1 gamma2).
Proof.
  intros. intro.
  have j := locs_equal_of_pl_in _ _ _ pl_in H.
  derive_contra_own_child j gamma1.
Qed.
  
Lemma pl_not_in_pls_of_loc_cross_from_in_right pl (gamma1 gamma2: Loc RI)
  (pl_in : pl ∈ pls_of_loc gamma2)
  : pl ∉ pls_of_loc (CrossLoc gamma1 gamma2).
Proof.
  intros. intro.
  have j := locs_equal_of_pl_in _ _ _ pl_in H.
  derive_contra_own_child j gamma2.
Qed.

Lemma pl_not_in_pls_of_loc_cross_from_not_in_both pl (gamma1 gamma2: Loc RI)
  (not_in_l : pl ∉ pls_of_loc_from_left gamma1 gamma2)
  (not_in_r : pl ∉ pls_of_loc_from_right gamma1 gamma2)
        : (pl ∉ pls_of_loc (CrossLoc gamma1 gamma2)).
Proof.
  unfold pls_of_loc_from_left in *.
  unfold pls_of_loc_from_right in *.
  unfold pls_of_loc in *.
  rewrite elem_of_union.
  intuition.
Qed.

Lemma resolve_p_i_in_ExtLoc
  p i alpha ri (gamma: Loc RI) :
  ((p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma)) ->
    (p ≠ [] ∧ plsplit p ∈ pls_of_loc gamma ∧ i = nat_of_extstep alpha ri). Admitted.
    
Lemma resolve_p_i_in_ExtLoc_rev
  p i alpha ri (gamma: Loc RI) :
    (p ≠ []) -> (plsplit p ∈ pls_of_loc gamma) -> (i = nat_of_extstep alpha ri) ->
    ((p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma)). Admitted.
    
Lemma resolve_p_i_in_Left
  p i (gamma1 gamma2: Loc RI) :
  ((p, i) ∈ pls_of_loc_from_left gamma1 gamma2) ->
    (p ≠ [] ∧ plsplit p ∈ pls_of_loc gamma1 ∧ i = nat_of_leftstep RI gamma2). Admitted.
    
Lemma resolve_p_i_in_Left_rev
  p i (gamma1 gamma2: Loc RI) :
  (p ≠ []) -> (plsplit p ∈ pls_of_loc gamma1) -> (i = nat_of_leftstep RI gamma2) ->
    ((p, i) ∈ pls_of_loc_from_left gamma1 gamma2). Admitted.
     
Lemma resolve_p_i_in_Right
  p i (gamma1 gamma2: Loc RI) :
  ((p, i) ∈ pls_of_loc_from_right gamma1 gamma2) ->
    (p ≠ [] ∧ plsplit p ∈ pls_of_loc gamma2 ∧ i = nat_of_rightstep RI gamma1). Admitted.
    
Lemma resolve_p_i_in_Right_rev
  p i (gamma1 gamma2: Loc RI) :
  (p ≠ []) -> (plsplit p ∈ pls_of_loc gamma2) -> (i = nat_of_rightstep RI gamma1) ->
    ((p, i) ∈ pls_of_loc_from_right gamma1 gamma2). Admitted.

Lemma plsplit_app_and_self_contra
  p i (gamma: Loc RI)
  : plsplit (p ++ [i]) ∈ pls_of_loc gamma -> p ≠ [] -> plsplit p ∈ pls_of_loc gamma
  -> False. Admitted.
  
Lemma plsplit_app_right_contra
  p (gamma1: Loc RI)
  : plsplit (p ++ [nat_of_rightstep RI gamma1]) ∈ pls_of_loc gamma1 -> False.
  Admitted.
  
Lemma plsplit_app_left_contra
  p (gamma2: Loc RI)
  : plsplit (p ++ [nat_of_leftstep RI gamma2]) ∈ pls_of_loc gamma2 -> False.
  Admitted.
  
Lemma append_to_pl_in_loc p1 i1 p2 i2 (loc: Loc RI) p i
  (pl1_in : (p1, i1) ∈ pls_of_loc loc)
  (pl2_in : (p2, i2) ∈ pls_of_loc loc)
  : (∃ (loc' : Loc RI) ,
    (p1 ++ [i1] ++ p, i) ∈ pls_of_loc loc' /\ (p2 ++ [i2] ++ p, i) ∈ pls_of_loc loc'
  ) \/ (
   ∀ (loc' : Loc RI) ,
    (p1 ++ [i1] ++ p, i) ∉ pls_of_loc loc' /\ (p2 ++ [i2] ++ p, i) ∉ pls_of_loc loc'
  ).
  Admitted.


End LocationsLemmas.
