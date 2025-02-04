Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.algebra Require Import gmap.
From iris.algebra Require Import gmultiset.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop boxes.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

(** Leaf Lifetime Logic. Based loosely on RustBelt's lifetime logic. *)

(* begin hide *)

Inductive BorState :=
  | Borrow : gset nat → gset nat → BorState
  | Unborrow : gset nat → BorState
.

Definition borrow_map := gmap slice_name BorState.

Inductive LtRa :=
  | LtOk :
      (* Alive set, Dead set, unborrows, borrows *)
      (option (gset nat * gset nat * borrow_map)) →
      (* alive tokens (2 each) *)
      gmultiset nat →
      (* dead tokens (persistent) *)
      gset nat →
      borrow_map →
      LtRa
  | LtFail.

(*
Print gmap_merge.
Definition merge_fb (fb1 fb2 : gmap (gset nat * gset nat) (gmultiset gname))
  := gmap_merge (λ fb1_entry fb2_entry,
    match fb1_entry, fb2_entry with
      | None, None => None
      | Some x, None => Some x
      | None, Some y => Some y
      | Some x, Some y => Some (x ⊎ y)
    end.
    *)
    
Local Instance lt_op : Op LtRa := λ a b , match a, b with
  | LtOk (Some o) a1 d1 bm1, LtOk None a2 d2 bm2 =>
      if decide (map_disjoint bm1 bm2) then
        LtOk (Some o) (a1 ⊎ a2) (d1 ∪ d2) (map_union bm1 bm2)
      else
        LtFail
  | LtOk None a1 d1 bm1, LtOk (Some o) a2 d2 bm2 =>
      if decide (map_disjoint bm1 bm2) then
        LtOk (Some o) (a1 ⊎ a2) (d1 ∪ d2) (map_union bm1 bm2)
      else
        LtFail
  | LtOk None a1 d1 bm1, LtOk None a2 d2 bm2 =>
      if decide (map_disjoint bm1 bm2) then
        LtOk None (a1 ⊎ a2) (d1 ∪ d2) (map_union bm1 bm2)
      else
        LtFail
  | _, _ => LtFail
end.

Definition lt_inv (a: LtRa) := match a with
  | LtOk (Some (sa, sd, sbm)) a d bm =>
      sd = d ∧ sa ∩ sd = ∅
      ∧ (∀ m , (m ∈ sa → multiplicity m a = 2) ∧ (m ∉ sa → multiplicity m a = 0))
      ∧ sbm = bm
  | _ => False
end.

Instance lt_valid : Valid LtRa := λ a , ∃ b , lt_inv (a ⋅ b).

Instance lt_equiv : Equiv LtRa := λ a b , a = b.

Instance lt_pcore : PCore LtRa := λ a , match a with
  | LtOk o1 a1 d1 bm1 => Some (LtOk None ∅ d1 ∅)
  | LtFail => Some LtFail
end.

Lemma lt_assoc : Assoc (=) lt_op.
Proof. Admitted. (*
  unfold Assoc. intros x y z. unfold lt_op.
  destruct x as [[o|] a d|], y as [[o1|] a1 d1|], z as [[o2|] a2 d2|]; trivial; f_equiv; (try set_solver); rewrite gmultiset_disj_union_assoc; trivial.
Qed. *)
  
Lemma lt_comm : Comm (=) lt_op.
Proof. Admitted. (*
  unfold Comm. intros x y. unfold lt_op.
  destruct x as [[o|] a d|], y as [[o1|] a1 d1|]; trivial; f_equiv; (try set_solver); rewrite gmultiset_disj_union_comm; trivial.
Qed. *)

Lemma LtOk_incl_3 a b d1 d2 bm
  (d_incl: d1 ⊆ d2)
  : LtOk a b d1 bm ≼ LtOk a b d2 bm.
Proof. Admitted. (*
  exists (LtOk None ∅ d2). destruct a as [a|]; unfold "⋅", lt_op; f_equiv; try set_solver.
Qed. *)
  
Lemma multiset_subseteq_of_LtOk_incl o0 a0 d0 bm0 o1 a1 d1 bm1 o2 a2 d2 bm2
  (incl: LtOk o0 a0 d0 bm0 ≡ LtOk o1 a1 d1 bm1 ⋅ LtOk o2 a2 d2 bm2)
  : d1 ⊆ d0.
Proof. Admitted. (*
  unfold "⋅", lt_op in incl; destruct o1, o2; inversion incl; set_solver.
Qed. *)

Definition lt_ra_mixin : RAMixin LtRa.
Proof. Admitted. (*split.
  - typeclasses eauto.
  - intros a b cx abe. rewrite abe. intros t. exists cx. intuition.
  - typeclasses eauto.
  - unfold Assoc. intros. apply lt_assoc.
  - unfold Comm. intros. apply lt_comm.
  - intros x cx peq. unfold pcore, lt_pcore in peq. destruct x as [o|].
    + inversion peq. subst cx. unfold "⋅", lt_op. destruct o; f_equiv; set_solver.
    + inversion peq. subst cx. trivial.
  - intros x cx peq. unfold pcore, lt_pcore in peq. destruct x.
    + inversion peq. subst cx. trivial.
    + inversion peq. subst cx. trivial.
    
  - intros x y cx xley peq.
      destruct x as [o a d|], y as [o1 a1 d1|]; destruct xley as [[o2 a2 d2|] equ];
      unfold pcore, lt_pcore; unfold pcore, lt_pcore in peq; inversion peq; subst cx.
      + exists (LtOk None ∅ d1); intuition.  apply LtOk_incl_3.
          eapply multiset_subseteq_of_LtOk_incl. apply equ.
      + unfold "⋅", lt_op in equ. inversion equ. destruct o; discriminate.
      + exists LtFail. intuition. exists LtFail. trivial.
      + exists LtFail. intuition. exists LtFail. trivial.
      + unfold "⋅", lt_op in equ. inversion equ.
      + unfold "⋅", lt_op in equ. inversion equ.
      + exists LtFail. intuition. exists LtFail. trivial.
      + exists LtFail. intuition. exists LtFail. trivial.
  - intros x y. unfold "✓", lt_valid. intros t. destruct t as [b t].
      rewrite <- lt_assoc in t. exists (lt_op y b). apply t.
Qed. *)

Canonical Structure ltO
  := discreteO LtRa.
  
Canonical Structure ltR := discreteR LtRa lt_ra_mixin.

Global Instance lt_cmra_discrete : CmraDiscrete ltR.
Proof. apply discrete_cmra_discrete. Qed.

Global Instance lt_unit : Unit LtRa := LtOk None ∅ ∅ ∅.

Definition lt_ucmra_mixin : UcmraMixin LtRa.
split; trivial. Admitted. (*
  - exists (LtOk (Some (∅, ∅, ∅)) ∅ ∅ ∅). unfold lt_inv. simpl. set_solver.
  - intro x. destruct x as [o a d|]; simpl; trivial.
      destruct o; trivial.
      + unfold ε, lt_unit, "⋅", lt_op. f_equiv; set_solver.
      + unfold ε, lt_unit, "⋅", lt_op. f_equiv; set_solver.
Qed. *)

Canonical Structure ltUR := Ucmra LtRa lt_ucmra_mixin.

(* end hide *)

Class llft_logicGpreS Σ := { llft_logic_inG : inG Σ ltUR ; exclG : inG Σ (exclR unitO) }.
Class llft_logicGS Σ := LlftLogicG {
  llft_inG : llft_logicGpreS Σ;
  llft_name: gname;
}.
Local Existing Instance llft_logic_inG.
Local Existing Instance exclG.
Local Existing Instance llft_inG.

Definition llft_logicΣ : gFunctors := #[ GFunctor ltUR ; GFunctor (exclR unitO) ].

Global Instance subG_lt_logicΣ Σ : subG llft_logicΣ Σ → llft_logicGpreS Σ.
Proof.
  solve_inG.
Qed.

Section LlftHelperResources.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGpreS Σ}.
  Context `{!invGS Σ}.
  
  (* begin hide *)

  Definition lt_state (sa sd : gset nat) (bm: borrow_map) := LtOk (Some (sa, sd, bm)) ∅ sd ∅.
  Definition LtState γlt (sa sd : gset nat) (bm: borrow_map): iProp Σ := own γlt (lt_state sa sd bm).

  Definition dead (k: nat) := LtOk None ∅ ({[ k ]}) ∅.
  Definition Dead γlt (k: nat) : iProp Σ := own γlt (dead k).

  Definition alive (k: nat) := LtOk None ({[+ k +]}) ∅ ∅.
  Definition Alive γlt (k: nat) : iProp Σ := own γlt (alive k).
  
  Definition rawbor (sn: slice_name) (k_alive k_dead : gset nat) :=
      LtOk None ∅ ∅ {[ sn := Borrow k_alive k_dead ]}.
  Definition RawBor γlt (sn: slice_name) (k_alive k_dead : gset nat) :=
      own γlt (rawbor sn k_alive k_dead).
      
  Definition unbor (sn: slice_name) (k : gset nat) := LtOk None ∅ ∅ {[ sn := Unborrow k ]}.
  Definition UnBor γlt (sn: slice_name) (k : gset nat) := own γlt (unbor sn k).
  
  Local Lemma lt_alloc :
    ⊢ |==> ∃ γ , LtState γ ∅ ∅ ∅.
  Proof.
    apply own_alloc. unfold "✓", cmra_valid, ltR, lt_valid.
    exists (LtOk None ∅ ∅ ∅). Admitted. (* simpl; set_solver.
  Qed. *)

  Local Lemma update_helper (a b : LtRa)
    (cond: ∀ z : ltR, lt_inv (a ⋅ z) → lt_inv (b ⋅ z))
    : a ~~> b.
  Proof.
    rewrite cmra_discrete_total_update.
    intros y ay. destruct ay as [t ay]. rewrite <- lt_assoc in ay.
    have co := cond _ ay. exists t. rewrite <- lt_assoc. apply co.
  Qed.

  Local Lemma update_helper2 (x y : LtRa)
    (cond: ∀ o a d bm , lt_inv (x ⋅ LtOk o a d bm) → lt_inv (y ⋅ LtOk o a d bm))
    : x ~~> y.
  Proof.
    apply update_helper. intros z. destruct z as [o a d|].
    - apply cond.
    - intros lti. unfold lt_inv in lti.
      replace (x ⋅ LtFail) with LtFail in lti. { contradiction. }
      destruct x as [o a d|]; trivial. destruct o; trivial.
  Qed.

  Local Lemma new_lt γlt k sa sd :
    (k ∉ sa) → (k ∉ sd) →
    LtState γlt sa sd ==∗ LtState γlt (sa ∪ {[ k ]}) sd ∗ Alive γlt k ∗ Alive γlt k.
  Proof.
    intros k_sa k_sd.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.

    intros o a d lti. destruct o as [s|].
    - contradiction. (*unfold "⋅", lt_op, lt_state, lt_inv in lti. contradiction.*)
    - simpl in lti. destruct lti as [sd_d [no_int fm]].
      simpl. split. { set_solver. }
      split. { set_solver. }
      intro m. split. {
          intro m_in. have fmm := fm m. destruct fmm as [fmm1 fmm2].
          rewrite elem_of_union in m_in. destruct m_in as [m_in|m_k].
          + rewrite gmultiset_disj_union_left_id.
            rewrite multiplicity_disj_union.
            have fmm11 := fmm1 m_in.
            rewrite gmultiset_disj_union_left_id in fmm11. rewrite fmm11.
            rewrite multiplicity_disj_union.
            rewrite multiplicity_singleton_ne. { trivial. }
            intro mk. subst m. apply k_sa. apply m_in.
          + rewrite gmultiset_disj_union_left_id.
            rewrite multiplicity_disj_union.
            rewrite multiplicity_disj_union.
            rewrite elem_of_singleton in m_k. rewrite m_k.
            rewrite multiplicity_singleton.
            have fmk := fm k. destruct fmk as [_ fmk0].
            rewrite gmultiset_disj_union_left_id in fmk0.
            rewrite fmk0; trivial.
          }
          intros m_not_in. rewrite not_elem_of_union in m_not_in.
          destruct m_not_in as [m_sa m_k].
          rewrite gmultiset_disj_union_left_id.
          rewrite multiplicity_disj_union.
          rewrite multiplicity_disj_union.
          have fmm := fm m. destruct fmm as [_ fmm0]. 
          rewrite gmultiset_disj_union_left_id in fmm0. rewrite fmm0; trivial.
          rewrite not_elem_of_singleton in m_k.
          rewrite multiplicity_singleton_ne; trivial.
  Qed.

  Local Lemma double_incl_lt_inv a b z' :
    (a ≼ z') → (b ≼ z') → (✓ z') → ∃ z, a ≼ z ∧ b ≼ z ∧ lt_inv z.
  Proof.
    intros az bz valz. destruct valz as [t valz]. exists (z' ⋅ t).
    split.
    { destruct az as [t1 az]. rewrite az. exists (t1 ⋅ t). rewrite <- lt_assoc. trivial. }
    split.
    { destruct bz as [t1 bz]. rewrite bz. exists (t1 ⋅ t). rewrite <- lt_assoc. trivial. }
    trivial.
  Qed.

  Local Lemma lt_state_incl_lt_ok sa sd sa1 sd1 a d 
    : (lt_state sa sd ≼ LtOk (Some (sa1, sd1)) a d) → sa = sa1 ∧ sd = sd1.
  Proof.
    intros lts. destruct lts as [t lts].
    destruct t as [[o|] a1 d1|].
    - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts.
    - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts. split; trivial.
    - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts.
  Qed.

  Local Lemma alive_incl_lt_ok k sa1 sd1 a d
    : (alive k ≼ LtOk (Some (sa1, sd1)) a d) → lt_inv (LtOk (Some (sa1, sd1)) a d) → k ∈ sa1.
  Proof.
    intros lts lti. destruct lts as [t lts].
    destruct t as [[o|] a1 d1|].
    - unfold alive in lts. unfold "⋅", lt_op in lts. inversion lts.
        unfold lt_inv in lti. destruct lti as [_ [_ fm]]. have fmk := fm k.
        have h : Decision (k ∈ sa1) by solve_decision. destruct h as [h|n]; trivial.
        exfalso.
        destruct fmk as [_ fmk]. have fmk1 := fmk n. subst a.
        rewrite multiplicity_disj_union in fmk1.
        rewrite multiplicity_singleton in fmk1. lia.
    - inversion lts.
    - inversion lts.
  Qed.

  Local Lemma dead_incl_lt_ok k sa1 sd1 a d
    : (dead k ≼ LtOk (Some (sa1, sd1)) a d) → lt_inv (LtOk (Some (sa1, sd1)) a d) → k ∈ sd1.
  Proof.
    intros lts lti. destruct lts as [t lts].
    destruct t as [[o|] a1 d1|].
    - unfold dead in lts. unfold "⋅", lt_op in lts. inversion lts.
        unfold lt_inv in lti. destruct lti as [sde _]. subst d. set_solver.
    - inversion lts.
    - inversion lts.
  Qed.

  Local Lemma alive_dead_contradiction k sa sd a d
    : (lt_inv (LtOk (Some (sa, sd)) a d)) → (k ∈ sa) → (k ∈ sd) → False.
  Proof.
    intros lts lti. destruct lts as [_ [no_int _]]. set_solver.
  Qed.

  Local Lemma lt_state_alive γlt k sa sd :
    LtState γlt sa sd ∧ Alive γlt k ⊢ ⌜ k ∈ sa ⌝.
  Proof.
    iIntros "P". iDestruct (and_own_discrete_ucmra with "P") as (z') "[o [%incl1 %incl2]]".
    iDestruct (own_valid with "o") as "%valz".
    iPureIntro.
    have di := double_incl_lt_inv _ _ _ incl1 incl2 valz.
    destruct di as [z [inc1 [inc2 lti]]].
    destruct z as [[[sa1 sd1]|] a d|]; try contradiction.
    have j := lt_state_incl_lt_ok _ _ _ _ _ _ inc1. destruct j as [j1 j2]. subst sa.
    apply (alive_incl_lt_ok _ _ _ _ _ inc2). apply lti.
  Qed.

  Local Lemma lt_state_dead γlt k sa sd :
    LtState γlt sa sd ∧ Dead γlt k ⊢ ⌜ k ∈ sd ⌝.
  Proof.
    iIntros "P". iDestruct (and_own_discrete_ucmra with "P") as (z') "[o [%incl1 %incl2]]".
    iDestruct (own_valid with "o") as "%valz".
    iPureIntro.
    have di := double_incl_lt_inv _ _ _ incl1 incl2 valz.
    destruct di as [z [inc1 [inc2 lti]]].
    destruct z as [[[sa1 sd1]|] a d|]; try contradiction.
    have j := lt_state_incl_lt_ok _ _ _ _ _ _ inc1. destruct j as [j1 j2]. subst sd.
    apply (dead_incl_lt_ok _ _ _ _ _ inc2). apply lti.
  Qed.

  Local Lemma lt_alive_dead_false γlt k :
    Alive γlt k ∧ Dead γlt k ⊢ False.
  Proof.
    iIntros "P". iDestruct (and_own_discrete_ucmra with "P") as (z') "[o [%incl1 %incl2]]".
    iDestruct (own_valid with "o") as "%valz".
    iPureIntro.
    have di := double_incl_lt_inv _ _ _ incl1 incl2 valz.
    destruct di as [z [inc1 [inc2 lti]]].
    destruct z as [[[sa1 sd1]|] a d|]; try contradiction.
    have j1 := alive_incl_lt_ok _ _ _ _ _ inc1.
    have j2 := dead_incl_lt_ok _ _ _ _ _ inc2.
    eapply alive_dead_contradiction. { apply lti. } { apply j1. apply lti. } { apply j2. apply lti. }
  Qed.

  Local Lemma kill_lt γlt k sa sd :
    LtState γlt sa sd ∗ Alive γlt k ∗ Alive γlt k ==∗
        LtState γlt (sa ∖ {[ k ]}) (sd ∪ {[ k ]}) ∗ Dead γlt k.
  Proof.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.

    intros o a d lti. destruct o as [s|].
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int fm]].
      simpl. split. { set_solver. }
      split. { set_solver. }
      intro m. split. {
          intro m_in. have fmm := fm m. destruct fmm as [fmm1 fmm2].
          rewrite gmultiset_disj_union_left_id.
          rewrite gmultiset_disj_union_left_id.
          rewrite gmultiset_disj_union_left_id in fmm1.
          rewrite multiplicity_disj_union in fmm1.
          rewrite multiplicity_disj_union in fmm1.
          rewrite elem_of_difference in m_in. destruct m_in as [m_in mk].
          rewrite elem_of_singleton in mk.
          rewrite multiplicity_singleton_ne in fmm1; trivial.
          apply fmm1. apply m_in.
      }
          intro m_in. have fmm := fm m. destruct fmm as [fmm1 fmm2].
          rewrite gmultiset_disj_union_left_id.
          rewrite gmultiset_disj_union_left_id.
          rewrite gmultiset_disj_union_left_id in fmm2.
          rewrite multiplicity_disj_union in fmm1.
          rewrite multiplicity_disj_union in fmm1.
          rewrite not_elem_of_difference in m_in.
          have h : Decision (m ∈ sa) by solve_decision. destruct h as [h|n].
          + destruct m_in as [m_not_in_sa|mk].
            * exfalso. apply m_not_in_sa. apply h.
            * rewrite multiplicity_disj_union in fmm1.
              have fmm1i := fmm1 h.
              rewrite elem_of_singleton in mk. subst m. rewrite multiplicity_singleton in fmm1i.
                rewrite multiplicity_empty in fmm1i. lia.
          + have fmm2i := fmm2 n.
            rewrite multiplicity_disj_union in fmm2i.
            rewrite multiplicity_disj_union in fmm2i. lia.
  Qed.

  Local Lemma bigSepS_alive_equiv_own γlt a
    (ne_emp: a ≠ ∅)
      : ([∗ set] k ∈ a, Alive γlt k) ⊣⊢ own γlt (LtOk None (list_to_set_disj (elements a)) ∅).
  Proof.
    induction a as [|x T ? IH] using set_ind_L. 
    - contradiction.
    - have h : Decision (T = ∅) by solve_decision. destruct h as [h|n]; trivial.
      + subst T. rewrite big_sepS_union; last by set_solver.
        rewrite big_sepS_empty. rewrite big_sepS_singleton. unfold Alive, alive.
        rewrite union_empty_r. rewrite elements_singleton. unfold list_to_set_disj.
        rewrite bi.sep_emp. rewrite gmultiset_disj_union_right_id. trivial.
      + rewrite big_sepS_union; last by set_solver.
        rewrite (IH n). rewrite big_sepS_singleton. unfold Alive, alive.
          rewrite <- own_op.
          f_equiv.
          unfold "⋅", cmra_op, ltR, lt_op. f_equiv; last by set_solver.
          rewrite elements_union_singleton; trivial.
  Qed.

  Local Lemma lt_ok_none_left o a1 d1 a2 d2
      : LtOk None a1 d1 ⋅ LtOk o a2 d2 = LtOk o (a1 ⊎ a2) (d1 ∪ d2).
  Proof.
    destruct o as [o|]; trivial.
  Qed.

  Local Lemma mult_list_to_set_disj_not_in (a: gset nat) (x: nat)
    (not_in: x ∉ a) : multiplicity x (list_to_set_disj (elements a)) = 0.
  Proof.
  induction a as [|y b ? IH] using set_ind_L. 
  - trivial.
  - rewrite elements_union_singleton; trivial. rewrite list_to_set_disj_cons.
      rewrite multiplicity_disj_union. rewrite IH; last by set_solver.
      assert (x ≠ y) by set_solver. rewrite multiplicity_singleton_ne; trivial.
  Qed.

  Local Lemma mult_list_to_set_disj_in (a: gset nat) (x: nat)
    (is_in: x ∈ a) : multiplicity x (list_to_set_disj (elements a)) = 1.
  Proof.
  induction a as [|y b ? IH] using set_ind_L. 
  - rewrite elem_of_empty in is_in. contradiction.
  - rewrite elements_union_singleton; trivial. rewrite list_to_set_disj_cons.
      rewrite multiplicity_disj_union.
      rewrite elem_of_union in is_in. destruct is_in as [ix|ib].
      + rewrite elem_of_singleton in ix. subst x. rewrite mult_list_to_set_disj_not_in; trivial.
          rewrite multiplicity_singleton. trivial.
      + rewrite (IH ib). rewrite multiplicity_singleton_ne; trivial. intro x_eq_y.
          subst x. contradiction.
  Qed.

  Local Lemma multiplicity_le o1 a1 d1 o2 a2 d2 x
    : LtOk o1 a1 d1 ≼ LtOk o2 a2 d2 → multiplicity x a1 ≤ multiplicity x a2.
  Proof.
    intro incl. destruct incl as [t incl]. destruct t as [o3 a3 d3|].
    - assert (a2 = a1 ⊎ a3) as X.
        + unfold "⋅", lt_op in incl. destruct o1; destruct o3.
          * inversion incl. * inversion incl; trivial. * inversion incl; trivial.
          * inversion incl; trivial.
        + subst a2. rewrite multiplicity_disj_union. lia.
    - unfold "⋅", lt_op in incl. destruct o1; inversion incl.
  Qed.

  Local Lemma own_and_alive γlt (a1 a2 : gset nat)
    : own γlt (LtOk None (list_to_set_disj (elements a1)) ∅)
      ∧ own γlt (LtOk None (list_to_set_disj (elements a2)) ∅)
      ⊢ own γlt (LtOk None (list_to_set_disj (elements (a1 ∪ a2))) ∅).
  Proof.
    iIntros "x".
    iDestruct (and_own_discrete_ucmra_specific with "x") as "y"; last by iFrame "y".
    intros w valw incl1 incl2.
    destruct w as [o a d|].
    - exists (LtOk o (a ∖ (list_to_set_disj (elements (a1 ∪ a2)))) d).
      rewrite lt_ok_none_left. f_equiv.
      + rewrite gmultiset_eq. intros x.
          rewrite multiplicity_disj_union.
          rewrite multiplicity_difference.
          enough ((multiplicity x a ≥ multiplicity x (list_to_set_disj (elements (a1 ∪ a2))))).
          { lia. }
          have t1 := multiplicity_le _ _ _ _ _ _ x incl1.
          have t2 := multiplicity_le _ _ _ _ _ _ x incl2.
          have h : Decision (x ∈ a1) by solve_decision. destruct h as [h1|n1]; trivial.
            *  rewrite mult_list_to_set_disj_in in t1; trivial.
              rewrite mult_list_to_set_disj_in; last by set_solver.
              lia.
          * have q : Decision (x ∈ a2) by solve_decision. destruct q as [h2|n2]; trivial.
            -- rewrite mult_list_to_set_disj_in in t2; trivial.
              rewrite mult_list_to_set_disj_in; last by set_solver.
              lia.
            -- rewrite mult_list_to_set_disj_not_in; last by set_solver.
              lia.
      + set_solver.
    - unfold "✓", cmra_valid, ucmra_cmraR, ucmra_valid, ltUR, lt_valid in valw.
      destruct valw as [b valw].
      replace (LtFail ⋅ b) with LtFail in valw. { contradiction. }
      destruct b; trivial.
  Qed.

  Local Lemma alive_and_bigSepS γlt (a1 a2 : gset nat)
    : ([∗ set] k ∈ a1, Alive γlt k) ∧ ([∗ set] k ∈ a2, Alive γlt k)
      ⊢ [∗ set] k ∈ a1 ∪ a2, Alive γlt k.
  Proof.
    have h: Decision (a1 = ∅) by solve_decision. destruct h as [h1|n1].
    { subst a1. rewrite big_sepS_empty. rewrite bi.emp_and.
        rewrite big_sepS_union; last by set_solver.
        rewrite big_sepS_empty. rewrite bi.emp_sep. trivial. }
    have h: Decision (a2 = ∅) by solve_decision. destruct h as [h2|n2].
    { subst a2. rewrite big_sepS_empty. rewrite bi.and_emp.
        rewrite big_sepS_union; last by set_solver.
        rewrite big_sepS_empty. rewrite bi.sep_emp. trivial. }
    rewrite bigSepS_alive_equiv_own; trivial.
    rewrite bigSepS_alive_equiv_own; trivial.
    rewrite bigSepS_alive_equiv_own; last by set_solver.
    apply own_and_alive.
  Qed.

  Local Instance pers_dead γlt k : Persistent (Dead γlt k).
  Proof.
    apply own_core_persistent. unfold CoreId. trivial.
  Qed.

  Local Lemma LtState_entails_Dead γlt k sa sd : (k ∈ sd) → LtState γlt sa sd ⊢ Dead γlt k.
  Proof.
    intros ksd.
    unfold LtState.
    replace (lt_state sa sd) with (lt_state sa sd ⋅ dead k).
    { rewrite own_op. iIntros "[A B]". iFrame "B". }
    unfold dead, lt_state, "⋅", lt_op. f_equal. set_solver.
  Qed.

  Local Lemma LtState_disjoint γlt sa sd : LtState γlt sa sd ⊢ ⌜ sa ∩ sd = ∅ ⌝.
  Proof.
    iIntros "T". iDestruct (own_valid with "T") as "%val". iPureIntro.
    destruct val as [t lts].
    destruct t as [[o|] a d|].
    - inversion lts.
    - simpl in lts. intuition.
    - inversion lts.
  Qed.

  Local Definition Cancel (γ: gname) : iProp Σ := own γ (Excl ()).
  Local Lemma new_cancel : ⊢ |==> ∃ γ , Cancel γ.
  Proof.
    iIntros. iDestruct (own_alloc (Excl ())) as "H"; first done. unfold Cancel. iFrame "H".
  Qed.
  Local Lemma cancel_cancel_false (γc : gname) : Cancel γc ∗ Cancel γc ⊢ False.
  Proof.
    iIntros "X". unfold Cancel. rewrite <- own_op.
    iDestruct (own_valid with "X") as "%J". contradiction.
  Qed.

  Local Lemma not_subset_eq_get (a b : gset nat) : (a ⊈ b) → ∃ k , k ∈ a ∧ k ∉ b.
  Proof.
    assert (∀ r , list_to_set r ⊈ b → ∃ u: nat , u ∈ ((list_to_set r) : gset nat) ∧ u ∉ b) as X.
    { intro r. induction r as [|a0 r IHr].
      - intros emp. rewrite list_to_set_nil in emp. set_solver.
      - intros not_in. rewrite list_to_set_cons in not_in.
        destruct (decide (a0 ∈ b)); trivial.
        + assert (list_to_set r ⊈ b) as K by set_solver.
          have IHr2 := IHr K. destruct IHr2 as [u IHr2]. exists u. set_solver.
        + exists a0. intuition. rewrite list_to_set_cons. set_solver.
    }
    intro a_not_in_b.
    have X1 := X (elements (Elements := gset_elements) a).
    assert (list_to_set (elements a) ⊈ b) as Y. { set_solver. }
    have Z := X1 Y. destruct Z as [u [Z1 Z2]]. exists u. split; trivial.
    rewrite list_to_set_elements in Z1. trivial.
  Qed.
End LlftHelperResources.

Section LlftLogic.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.

  (*** Lifetime logic ***)

  (* end hide *)
  Definition NLLFT := nroot .@ "leaf-lifetime".

  (** A Lifetime κ is defined as a [gset nat]. Though this should technically be
  an implementation detail, this makes it easy to export the basic properties of [Lifetime]
  (EqDecidable, Countable) and [⊓] (associativity, commutativity). *)
  
  Definition Lifetime := gset nat.

  Global Instance llft_intersect : Meet Lifetime := λ κ1 κ2, κ1 ∪ κ2.
  Definition llft_empty : Lifetime := ∅.
  (* begin hide *)

  Local Definition llft_alive_def (κ : Lifetime) : iProp Σ := [∗ set] k ∈ κ , Alive llft_name k.
  Local Definition llft_dead_def (κ : Lifetime) : iProp Σ := ∃ k , ⌜ k ∈ κ ⌝ ∗ Dead llft_name k.

  Local Definition llft_ctx_def :=
    (True &&{↑NLLFT}&&> ∃ sa sd , LtState llft_name sa sd ∗ llft_alive_def sa).

  Local Definition llft_alive_aux : seal (@llft_alive_def). Proof. by eexists. Qed.
  Local Definition llft_dead_aux : seal (@llft_dead_def). Proof. by eexists. Qed.
  Local Definition llft_ctx_aux : seal (@llft_ctx_def). Proof. by eexists. Qed.

  (* end hide *)
  
  (** Definitions of the lifetime tokens. Note that these aren't fractional since you
  use Leaf concepts instead. *)
  
  Definition llft_alive (κ : Lifetime) : iProp Σ. exact (llft_alive_aux.(unseal) κ). Defined.
  Definition llft_dead (κ : Lifetime) : iProp Σ. exact (llft_dead_aux.(unseal) κ). Defined.
  Definition llft_ctx : iProp Σ. exact (llft_ctx_aux.(unseal)). Defined.
  (* begin hide *)

  Local Definition llft_alive_unseal :
      @llft_alive = @llft_alive_def := llft_alive_aux.(seal_eq).
  Local Definition llft_dead_unseal :
      @llft_dead = @llft_dead_def := llft_dead_aux.(seal_eq).
  Local Definition llft_ctx_unseal :
      @llft_ctx = @llft_ctx_def := llft_ctx_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?llft_alive_unseal /llft_alive_def
    ?llft_dead_unseal /llft_dead_def
    ?llft_ctx_unseal /llft_ctx_def.
    
  Local Instance pers_dead2 γlt k : Persistent (Dead γlt k).
  Proof. apply pers_dead. Qed.

  (* end hide *)

  Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
  
  (** Lifetime inclusion is, by definition, a guard proposition. This provides us with
  an analogue of RustBelt's "dynamic lifetime inclusion": to derive new lifetime inclusions
  we can use Leaf to derive new guard propositions. *)
  
  Definition llft_incl (κ1 κ2 : Lifetime) : iProp Σ :=
      @[ κ1 ] &&{↑NLLFT}&&> @[ κ2 ].
  
  Infix "⊑" := llft_incl (at level 70) : bi_scope.
  
  (** The lifetime logic *)

  Global Instance pers_llft_ctx : Persistent llft_ctx.
  Proof. unseal. typeclasses eauto. Qed.
  
  Global Instance pers_llft_dead κ : Persistent ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_alive κ : Timeless (@[ κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_dead κ : Timeless ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Lemma llftl_not_own_end κ : @[ κ ] ∗ [† κ ] ⊢ False.
  Proof.
    unseal. iIntros "[A D]". iDestruct "D" as (k) "[%kk D]".
    iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. }
    iApply (lt_alive_dead_false llft_name k). iSplit; iFrame.
  Qed.

  Lemma llftl_not_own_end_and κ : @[ κ ] ∧ [† κ ] ⊢ False.
  Proof.
    unseal. iIntros "AD". unfold llft_dead. rewrite bi.and_exist_l. iDestruct "AD" as (k) "AD".
    iApply (lt_alive_dead_false llft_name k).
    iAssert (⌜k ∈ κ⌝)%I as "%kk". { iDestruct "AD" as "[_ [D _]]".  iFrame. }
    iSplit; iFrame.
    { iDestruct "AD" as "[A _]".
      iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. } iFrame. }
    { iDestruct "AD" as "[_ [_ D]]". iFrame. }
  Qed.

  Lemma llftl_begin :
      llft_ctx ⊢ |={↑NLLFT}=> ∃ κ, @[ κ ] ∗ (@[ κ ] ={↑NLLFT}=∗ [† κ ]).
  Proof.
      unseal. iIntros "#ctx".  unfold llft_ctx.
      iDestruct (guards_open (True)%I _ (↑NLLFT) (↑NLLFT) with "[ctx]") as "J". { set_solver. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd) "[State Alive]".

      assert (∃ k , k ∉ (sa ∪ sd)) as Fres. { exists (fresh (sa ∪ sd)). apply is_fresh. }
      destruct Fres as [k Fres].
      iMod (new_lt llft_name k sa sd with "[State]") as "T".
      { set_solver. } { set_solver. } { iFrame. }
      iDestruct "T" as "[State [A1 A2]]".
      iMod ("back" with "[Alive State A1]").
      { iExists (sa ∪ {[k]}). iExists sd. iFrame.
        unfold llft_alive.
        replace ((sa ∪ {[k]})) with (({[k]} ∪ sa)).
        { unseal. rewrite big_sepS_insert. { iFrame. } set_solver. } set_solver.
      }
      iModIntro.
      iExists ({[ k ]}). unfold llft_alive. 
      rewrite big_sepS_singleton. iFrame "A2".
      iIntros "token".

      (* ending the lifetime *)
      iDestruct (guards_open (True)%I _ (↑NLLFT) (↑NLLFT) with "[ctx]") as "J". { set_solver. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa1 sd1) "[State Alive]".
      iAssert (⌜k ∈ sa1⌝)%I as "%k_sa1".
      { iApply (lt_state_alive llft_name k sa1 sd1). iSplit. { iFrame "State". } iFrame "token". }
      unseal. rewrite (big_sepS_delete _ sa1 k); trivial.
      iDestruct "Alive" as "[token2 Alive]".
      iMod (kill_lt llft_name k sa1 sd1 with "[State token token2]") as "[State dead]". { iFrame. }
      iMod ("back" with "[State Alive]") as "X".
      { iExists (sa1 ∖ {[k]}). iExists (sd1 ∪ {[k]}). iFrame. }
      iModIntro. unfold llft_dead. iExists k. iFrame "dead". iPureIntro. set_solver.
  Qed.

  Lemma llftl_borrow_shared κ (P : iProp Σ) :
      ▷ P ={↑NLLFT}=∗ (@[ κ ] &&{↑NLLFT}&&> ▷ P) ∗ ([† κ ] ={↑NLLFT}=∗ ▷ P).
  Proof.
    iIntros "P".
    iMod new_cancel as (γc) "c1".
    iMod (guards_alloc_with_inv (NLLFT) (↑NLLFT) ((P ∨ (llft_dead κ ∗ Cancel γc))) with "[P]") as "[#Tinv #Tguard]".
    { iNext. iLeft. iFrame "P". }
    iModIntro.
    iSplit.
    { 
      iAssert (llft_alive κ &&{ ↑NLLFT ∪ ↑NLLFT }&&> ▷ P) as "H".
      { iApply
        (guards_cancel_or (llft_alive κ) (llft_alive κ) (llft_dead κ ∗ Cancel γc) (▷ P)).
        { iIntros "t". iApply (llftl_not_own_end_and κ). iSplit.
          { iDestruct "t" as "[t _]". iFrame "t". }
          { iDestruct "t" as "[_ [t _]]". iFrame "t". }
        }
        iSplit. { iApply guards_refl. }
        { setoid_replace (llft_dead κ ∗ Cancel γc ∨ ▷ P)%I
            with (▷ P ∨ llft_dead κ ∗ Cancel γc)%I.
          { iDestruct (guards_true (↑NLLFT) (llft_alive κ)) as "gt".
            iDestruct (guards_transitive (↑NLLFT) (llft_alive κ)%I with "[gt Tguard]") as "J".
            { iFrame "Tguard". iFrame "gt". }
            rewrite bi.later_or.
            iDestruct (guards_remove_later_or_r (llft_dead κ ∗ Cancel γc) (▷ P) (↑NLLFT)) as "X".
            iDestruct (guards_transitive (↑NLLFT) (llft_alive κ)%I with "[J X]") as "R".
            { iFrame "J". iFrame "X". }
            iFrame "R".
          }
          rewrite bi.or_comm. trivial.
        }
      }
      rewrite subseteq_union_1_L. { iFrame "H". } set_solver.
    }
    iIntros "deadk".
    iDestruct (guards_open (True)%I (▷ (P ∨ llft_dead κ ∗ Cancel γc))%I (↑ NLLFT) (↑ NLLFT) with "[Tguard]") as "J". { set_solver. }
    { iFrame "Tguard". }
    iMod "J" as "[J K]". rewrite bi.later_or. iDestruct "J" as "[P|J]".
    { iDestruct ("K" with "[deadk c1]") as "K". { iRight. iFrame. }
        iMod "K" as "K". iModIntro. iFrame "P". }
    iDestruct "J" as "[_ c2]". iMod "c2".
    iDestruct (cancel_cancel_false γc with "[c1 c2]") as "J". { iFrame. } iExFalso. iFrame "J".
  Qed.

  Lemma llftl_incl_dead_implies_dead κ κ' :
      ⊢ llft_ctx ∗ κ ⊑ κ' ∗ [† κ' ] ={↑NLLFT}=∗ [† κ ].
  Proof.
    iIntros "[#ctx [#incl #dead]]". unseal.

    unfold llft_incl.

    leaf_hyp "incl" rhs to (False)%I as "G2".
    {
      leaf_by_sep. iIntros "a". iExFalso.
      iApply (llftl_not_own_end κ'). iFrame. unseal. iFrame "dead".
    }
    unfold llft_ctx.
    leaf_hyp "ctx" rhs to ((∃ sa sd : gset nat, ⌜ κ ⊆ sa ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa)
        ∨ (∃ sa sd : gset nat, ⌜ ¬(κ ⊆ sa) ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa) )%I
        as "ctx2".
    {
      leaf_by_sep. iIntros "T". iSplitL.
        - iDestruct "T" as (sa sd) "state_alive".
          have h : Decision (κ ⊆ sa) by solve_decision. destruct h as [h|n]; trivial.
          + unseal. iLeft. iExists sa. iExists sd. iFrame. iPureIntro. trivial.
          + unseal. iRight. iExists sa. iExists sd. iFrame. iPureIntro. trivial.
        - iIntros "T". iDestruct "T" as "[T|T]".
          + iDestruct "T" as (sa sd) "[_ T]". iExists sa. iExists sd. unseal. iFrame.
          + iDestruct "T" as (sa sd) "[_ T]". iExists sa. iExists sd. unseal. iFrame.
      }

      iAssert (True &&{ ↑NLLFT}&&> (∃ sa sd : gset nat, ⌜κ ⊈ sa⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa)) as "G3".
        { iApply guards_cancel_or_by_chaining. iFrame "ctx2". 
          leaf_goal rhs to (llft_alive κ). { iFrame "G2". }
          leaf_by_sep.
          { iIntros "T". 
              iDestruct "T" as (sa sd) "[%ksa [state alive]]".
                unseal. unfold llft_alive_def.
                replace sa with (κ ∪ (sa ∖ κ)) at 2.
                { setoid_rewrite big_sepS_union.
                  { iDestruct "alive" as "[alive1 alive2]". iFrame "alive1".
                    iIntros "rest".
                    iExists sa. iExists sd. iFrame.
                    iCombine "rest alive2" as "alive".
                    setoid_rewrite <- big_sepS_union.
                    { replace (κ ∪ sa ∖ κ) with sa. { iFrame. iPureIntro. trivial. }
                    rewrite <- union_difference_L; trivial.
                }
                set_solver.
              }
              set_solver.
          } rewrite <- union_difference_L; trivial.
        }
      }            

      leaf_open "G3" with "[]" as "[J back]". { set_solver. } { done. }

      iDestruct "J" as (sa sd) "[%k_sa [State alive]]".
      have the_k := not_subset_eq_get κ sa k_sa. destruct the_k as [k [k_in k_not_in]].
      have h : Decision (k ∈ sd) by solve_decision. destruct h as [h|n]; trivial.
        - iDestruct (LtState_entails_Dead llft_name k sa sd with "State") as "#deadk"; trivial.
          iMod ("back" with "[State alive]") as "true". { iExists sa. iExists sd. iFrame. iPureIntro; trivial. } iModIntro. unfold llft_dead. iExists k. iFrame "deadk". iPureIntro. apply k_in.
        - (* weird technicality, if k was never made alive in the first place;
            first create it, then immediately kill it *)
          iMod (new_lt llft_name k sa sd with "State") as "[State [al1 al2]]"; trivial.
          iMod (kill_lt llft_name k (sa ∪ {[ k ]}) sd with "[State al1 al2]") as "[State deadk]".
            { iFrame. }
          iMod ("back" with "[State alive]") as "J".
          { iExists sa. iExists (sd ∪ {[k]}). iFrame.
            replace (((sa ∪ {[k]}) ∖ {[k]})) with sa.
            { iFrame. iPureIntro. trivial. } set_solver.
          }
          iModIntro. unfold llft_dead. iExists k. iFrame "deadk". iPureIntro; trivial.
  Qed.

  Lemma llftl_incl_intersect κ κ' : ⊢ (κ ⊓ κ') ⊑ κ.
  Proof.
    leaf_by_sep. unseal. iIntros "Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1". iIntros "A3". iFrame.
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.

  Lemma llftl_incl_glb κ κ' κ'' :
      κ ⊑ κ' ∗ κ ⊑ κ'' ⊢ κ ⊑ (κ' ⊓ κ'').
  Proof.
    apply guards_and_point.
    - unseal. unfold llft_alive_def. apply factoring_props.point_prop_big_sepS.
        intros x xi. apply factoring_props.point_prop_own.
    - unseal. unfold llft_alive_def. apply alive_and_bigSepS.
  Qed.

  Lemma llftl_tok_inter_l κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ ].
  Proof.
    iIntros "Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - unseal. rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1".
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.

  Lemma llftl_tok_inter_r κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ' ].
  Proof.
    replace (κ ⊓ κ') with (κ' ⊓ κ).
    - apply llftl_tok_inter_l. 
    - unfold meet, llft_intersect. set_solver.
  Qed.

  Lemma llftl_tok_inter_and κ κ' :
      @[ κ ⊓ κ' ] ⊣⊢ @[ κ ] ∧ @[ κ' ].
  Proof.
    iIntros. iSplit.
    - iIntros "t". iSplit.
      + iApply llftl_tok_inter_l. iFrame "t".
      + iApply llftl_tok_inter_r. iFrame "t".
  - unseal. iIntros. iApply alive_and_bigSepS. iFrame.
  Qed.

  Lemma llftl_end_inter κ κ' :
      [† κ ⊓ κ'] ⊣⊢ [† κ ] ∨ [† κ' ].
  Proof.
    unseal. iIntros. iSplit.
    - iIntros "t".  iDestruct "t" as (k) "[%kin t]".
      unfold llft_intersect in kin. rewrite elem_of_union in kin. destruct kin as [h|h].
      + iLeft. iExists k. iFrame "t". iPureIntro. trivial.
      + iRight. iExists k. iFrame "t". iPureIntro. trivial.
    - iIntros "t". iDestruct "t" as "[h|h]".
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold llft_intersect. set_solver.
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold llft_intersect. set_solver.
  Qed.

  Lemma llftl_tok_unit :
      ⊢ @[ llft_empty ].
  Proof.
    unseal. unfold llft_empty. rewrite big_sepS_empty. iIntros. done.
  Qed.

  Lemma llftl_end_unit :
      [† llft_empty ] ⊢ False.
  Proof.
    unseal. unfold llft_empty.
    iIntros "t". iDestruct "t" as (k) "[%p t]".
    rewrite elem_of_empty in p. contradiction.
  Qed.
End LlftLogic.

Lemma llft_alloc {Σ: gFunctors} `{!llft_logicGpreS Σ} `{!invGS Σ} E
  : ⊢ |={E}=> ∃ _ : llft_logicGS Σ, llft_ctx.
Proof.
  iIntros. iMod lt_alloc as (γ) "J".
  iMod (guards_alloc_with_inv (NLLFT) E
      (∃ sa sd : gset nat, LtState γ sa sd ∗ [∗ set] k ∈ sa , Alive γ k) with "[J]") as "[_ K]".
   { iModIntro. iExists ∅. iExists ∅. iFrame. done. }
  iModIntro.
  iExists (LlftLogicG _ _ γ).
  rewrite llft_ctx_unseal /llft_ctx_def.
  iDestruct (guards_remove_later_rhs with "K") as "K2".
  unfold llft_alive_def. iFrame "K2".
Qed.
