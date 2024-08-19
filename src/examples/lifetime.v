Require Import guarding.base_storage_opt.
Require Import guarding.protocol.
Require Import guarding.inved.
Require Import guarding.guard.
Require Import guarding.conjunct_own_rule2.
Require Import guarding.tactics.

Require Import cpdt.CpdtTactics.
Require Import coq_tricks.Deex.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

Inductive LtRa :=
  | LtOk : (option (gset nat * gset nat)) → gmultiset nat → gset nat → LtRa
  | LtFail.
  
Instance lt_op : Op LtRa := λ a b , match a, b with
  | LtOk (Some o) a1 d1, LtOk None a2 d2 =>
      LtOk (Some o) (a1 ⊎ a2) (d1 ∪ d2)
  | LtOk None a1 d1, LtOk (Some o) a2 d2 =>
      LtOk (Some o) (a1 ⊎ a2) (d1 ∪ d2)
  | LtOk None a1 d1, LtOk None a2 d2 =>
      LtOk None (a1 ⊎ a2) (d1 ∪ d2)
  | _, _ => LtFail
end.

Definition lt_inv (a: LtRa) := match a with
  | LtOk (Some (sa, sd)) a d =>
      sd = d ∧ sa ∩ sd = ∅
      ∧ ∀ m , (m ∈ sa → multiplicity m a = 2) ∧ (m ∉ sa → multiplicity m a = 0)
  | _ => False
end.

Instance lt_valid : Valid LtRa := λ a , ∃ b , lt_inv (a ⋅ b).

Instance lt_equiv : Equiv LtRa := λ a b , a = b.

Instance lt_pcore : PCore LtRa := λ a , match a with
  | LtOk o1 a1 d1 => Some (LtOk None ∅ d1)
  | LtFail => Some LtFail
end.

Lemma lt_assoc : Assoc (=) lt_op.
Proof.
  unfold Assoc. intros x y z. unfold lt_op.
  destruct x as [[o|] a d|], y as [[o1|] a1 d1|], z as [[o2|] a2 d2|]; trivial; f_equiv; (try set_solver); rewrite gmultiset_disj_union_assoc; trivial.
Qed.
  
Lemma lt_comm : Comm (=) lt_op.
Proof.
  unfold Comm. intros x y. unfold lt_op.
  destruct x as [[o|] a d|], y as [[o1|] a1 d1|]; trivial; f_equiv; (try set_solver); rewrite gmultiset_disj_union_comm; trivial.
Qed.

Lemma LtOk_incl_3 a b d1 d2
  (d_incl: d1 ⊆ d2)
  : LtOk a b d1 ≼ LtOk a b d2.
Proof.
  exists (LtOk None ∅ d2). destruct a as [a|]; unfold "⋅", lt_op; f_equiv; try set_solver.
Qed.
  
Lemma multiset_subseteq_of_LtOk_incl o0 a0 d0 o1 a1 d1 o2 a2 d2
  (incl: LtOk o0 a0 d0 ≡ LtOk o1 a1 d1 ⋅ LtOk o2 a2 d2)
  : d1 ⊆ d0.
Proof.
  unfold "⋅", lt_op in incl; destruct o1, o2; inversion incl; set_solver.
Qed.

Definition lt_ra_mixin : RAMixin LtRa.
Proof. split.
  - typeclasses eauto.
  - intros a b cx abe. rewrite abe. intros t. exists cx. intuition.
  - typeclasses eauto.
  - unfold Assoc. intros. apply lt_assoc.
  - unfold Comm. intros. apply lt_comm.
  - intros x cx peq. unfold pcore, lt_pcore in peq. destruct x.
    + inversion peq. subst cx. unfold "⋅", lt_op. destruct o; f_equiv; set_solver.
    + inversion peq. subst cx. trivial.
  - intros x cx peq. unfold pcore, lt_pcore in peq. destruct x.
    + inversion peq. subst cx. trivial.
    + inversion peq. subst cx. trivial.
    
  - intros x y cx xley peq. destruct x, y; destruct xley as [t equ]; destruct t;
      unfold pcore, lt_pcore; unfold pcore, lt_pcore in peq; inversion peq; subst cx.
      + exists (LtOk None ∅ g2); intuition.  apply LtOk_incl_3.
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
Qed.

Canonical Structure ltO
  := discreteO LtRa.
  
Canonical Structure ltR := discreteR LtRa lt_ra_mixin.

Global Instance lt_cmra_discrete : CmraDiscrete ltR.
Proof. apply discrete_cmra_discrete. Qed.

Global Instance lt_unit : Unit LtRa := LtOk None ∅ ∅.

Definition lt_ucmra_mixin : UcmraMixin LtRa.
split; trivial.
  - exists (LtOk (Some (∅, ∅)) ∅ ∅). unfold lt_inv. simpl; set_solver.
  - intro x. destruct x; simpl; trivial.
      destruct o; trivial.
      + unfold ε, lt_unit, "⋅", lt_op. f_equiv; set_solver.
      + unfold ε, lt_unit, "⋅", lt_op. f_equiv; set_solver.
Qed.

Canonical Structure ltUR := Ucmra LtRa lt_ucmra_mixin.

Class lt_logicG Σ := { lt_logic_inG : inG Σ ltUR ; exclG : inG Σ (exclR unitO) }.
Local Existing Instance lt_logic_inG.
Local Existing Instance exclG.

Definition lt_logicΣ : gFunctors := #[ GFunctor ltUR ; GFunctor (exclR unitO) ].

Global Instance subG_lt_logicΣ Σ : subG lt_logicΣ Σ → lt_logicG Σ.
Proof.
  solve_inG.
Qed.

Section LtResource.

Context {Σ: gFunctors}.
Context `{!lt_logicG Σ}.
Context `{!invGS Σ}.

Context (γlt : gname).

Definition lt_state (sa sd : gset nat) := LtOk (Some (sa, sd)) ∅ sd.
Definition LtState (sa sd : gset nat) : iProp Σ := own γlt (lt_state sa sd).

Definition dead (k: nat) := LtOk None ∅ ({[ k ]}).
Definition Dead (k: nat) : iProp Σ := own γlt (dead k).

Definition alive (k: nat) := LtOk None ({[+ k +]}) ∅.
Definition Alive (k: nat) : iProp Σ := own γlt (alive k).

Lemma update_helper (a b : LtRa)
  (cond: ∀ z : ltR, lt_inv (a ⋅ z) → lt_inv (b ⋅ z))
  : a ~~> b.
Proof.
  rewrite cmra_discrete_total_update.
  intros y ay. destruct ay as [t ay]. rewrite <- lt_assoc in ay.
  have co := cond _ ay. exists t. rewrite <- lt_assoc. apply co.
Qed.

Lemma update_helper2 (x y : LtRa)
  (cond: ∀ o a d , lt_inv (x ⋅ LtOk o a d) → lt_inv (y ⋅ LtOk o a d))
  : x ~~> y.
Proof.
  apply update_helper. intros z. destruct z as [o a d|].
  - apply cond.
  - intros lti. unfold lt_inv in lti.
    replace (x ⋅ LtFail) with LtFail in lti. { contradiction. }
    destruct x; trivial. destruct o; trivial.
Qed.

Lemma new_lt k sa sd :
  (k ∉ sa) → (k ∉ sd) →
  LtState sa sd ==∗ LtState (sa ∪ {[ k ]}) sd ∗ Alive k ∗ Alive k.
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

Lemma double_incl_lt_inv a b z' :
  (a ≼ z') → (b ≼ z') → (✓ z') → ∃ z, a ≼ z ∧ b ≼ z ∧ lt_inv z.
Proof.
  intros az bz valz. destruct valz as [t valz]. exists (z' ⋅ t).
  split.
  { destruct az as [t1 az]. rewrite az. exists (t1 ⋅ t). rewrite <- lt_assoc. trivial. }
  split.
  { destruct bz as [t1 bz]. rewrite bz. exists (t1 ⋅ t). rewrite <- lt_assoc. trivial. }
  trivial.
Qed.

Lemma lt_state_incl_lt_ok sa sd sa1 sd1 a d 
  : (lt_state sa sd ≼ LtOk (Some (sa1, sd1)) a d) → sa = sa1 ∧ sd = sd1.
Proof.
  intros lts. destruct lts as [t lts].
  destruct t as [[o|] a1 d1|].
  - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts.
  - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts. split; trivial.
  - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts.
Qed.
  
Lemma alive_incl_lt_ok k sa1 sd1 a d
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
  
Lemma dead_incl_lt_ok k sa1 sd1 a d
  : (dead k ≼ LtOk (Some (sa1, sd1)) a d) → lt_inv (LtOk (Some (sa1, sd1)) a d) → k ∈ sd1.
Proof.
  intros lts lti. destruct lts as [t lts].
  destruct t as [[o|] a1 d1|].
  - unfold dead in lts. unfold "⋅", lt_op in lts. inversion lts.
      unfold lt_inv in lti. destruct lti as [sde _]. subst d. set_solver.
  - inversion lts.
  - inversion lts.
Qed.
  
Lemma alive_dead_contradiction k sa sd a d
  : (lt_inv (LtOk (Some (sa, sd)) a d)) → (k ∈ sa) → (k ∈ sd) → False.
Proof.
  intros lts lti. destruct lts as [_ [no_int _]]. set_solver.
Qed.

Lemma lt_state_alive k sa sd :
  LtState sa sd ∧ Alive k ⊢ ⌜ k ∈ sa ⌝.
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

Lemma lt_state_dead k sa sd :
  LtState sa sd ∧ Dead k ⊢ ⌜ k ∈ sd ⌝.
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

Lemma lt_alive_dead_false k :
  Alive k ∧ Dead k ⊢ False.
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

Lemma kill_lt k sa sd :
  LtState sa sd ∗ Alive k ∗ Alive k ==∗ LtState (sa ∖ {[ k ]}) (sd ∪ {[ k ]}) ∗ Dead k.
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
    
        
Local Instance pers_dead k : Persistent (Dead k).
Proof.
  apply own_core_persistent. unfold CoreId. trivial.
Qed.

Lemma LtState_entails_Dead k sa sd : (k ∈ sd) → LtState sa sd ⊢ Dead k.
Proof.
  intros ksd.
  unfold LtState.
  replace (lt_state sa sd) with (lt_state sa sd ⋅ dead k).
  { rewrite own_op. iIntros "[A B]". iFrame "B". }
  unfold dead, lt_state, "⋅", lt_op. f_equal. set_solver.
Qed.

Lemma LtState_disjoint sa sd : LtState sa sd ⊢ ⌜ sa ∩ sd = ∅ ⌝.
Proof.
  iIntros "T". iDestruct (own_valid with "T") as "%val". iPureIntro.
  destruct val as [t lts].
  destruct t as [[o|] a d|].
  - inversion lts.
  - simpl in lts. intuition.
  - inversion lts.
Qed.

Definition NLLFT := nroot .@ "leaf-lifetime".

Definition Lifetime := gset nat.

Definition llft_intersect (κ1 κ2 : Lifetime) : Lifetime := κ1 ∪ κ2.
Definition llft_empty : Lifetime := ∅.

Definition llft_alive (κ : Lifetime) : iProp Σ := [∗ set] k ∈ κ , Alive k.
Definition llft_dead (κ : Lifetime) : iProp Σ := ∃ k , ⌜ k ∈ κ ⌝ ∗ Dead k.

Definition llft_incl (κ1 κ2 : Lifetime) : iProp Σ :=
    llft_alive κ1 &&{↑NLLFT}&&> llft_alive κ2.

Definition llftctx :=
  (True &&{↑NLLFT}&&> ∃ sa sd , LtState sa sd ∗ llft_alive sa).
  
Global Instance pers_llft_dead κ : Persistent (llft_dead κ).
Proof.
  typeclasses eauto.
Qed.
  
Lemma llftl_not_own_end κ : llft_alive κ ∗ llft_dead κ ⊢ False.
Proof.
  iIntros "[A D]". iDestruct "D" as (k) "[%kk D]".
  iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. }
  iApply (lt_alive_dead_false k). iSplit; iFrame.
Qed.

Lemma llftl_not_own_end_and κ : llft_alive κ ∧ llft_dead κ ⊢ False.
Proof.
  iIntros "AD". unfold llft_dead. rewrite bi.and_exist_l. iDestruct "AD" as (k) "AD".
  iApply (lt_alive_dead_false k).
  iAssert (⌜k ∈ κ⌝)%I as "%kk". { iDestruct "AD" as "[_ [D _]]".  iFrame. }
  iSplit; iFrame.
  { iDestruct "AD" as "[A _]".
    iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. } iFrame. }
  { iDestruct "AD" as "[_ [_ D]]". iFrame. }
Qed.

Definition Cancel (γ: gname) : iProp Σ := own γ (Excl ()).
Lemma new_cancel : ⊢ |==> ∃ γ , Cancel γ.
Proof.
  iIntros. iDestruct (own_alloc (Excl ())) as "H"; first done. unfold Cancel. iFrame "H".
Qed.
  
Lemma cancel_cancel_false (γc : gname) : Cancel γc ∗ Cancel γc ⊢ False.
Proof.
  iIntros "X". unfold Cancel. rewrite <- own_op.
  iDestruct (own_valid with "X") as "%J". contradiction.
Qed.

Lemma llftl_begin :
    llftctx ⊢ |={↑NLLFT}=> ∃ κ, llft_alive κ ∗ (llft_alive κ ={↑NLLFT}=∗ llft_dead κ).
Proof.
    iIntros "#ctx".  unfold llftctx.
    iDestruct (guards_open (True)%I _ (↑NLLFT) (↑NLLFT) with "[ctx]") as "J". { set_solver. }
    { iFrame "ctx". }
    iMod "J" as "[J back]". iDestruct "J" as (sa sd) "[State Alive]".
    
    assert (∃ k , k ∉ (sa ∪ sd)) as Fres. { exists (fresh (sa ∪ sd)). apply is_fresh. }
    destruct Fres as [k Fres].
    iMod (new_lt k sa sd with "[State]") as "T".
    { set_solver. } { set_solver. } { iFrame. }
    iDestruct "T" as "[State [A1 A2]]".
    iMod ("back" with "[Alive State A1]").
    { iExists (sa ∪ {[k]}). iExists sd. iFrame.
      unfold llft_alive.
      replace ((sa ∪ {[k]})) with (({[k]} ∪ sa)).
      { rewrite big_sepS_insert. { iFrame. } set_solver. } set_solver.
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
    { iApply (lt_state_alive k sa1 sd1). iSplit. { iFrame "State". } iFrame "token". }
    rewrite (big_sepS_delete _ sa1 k); trivial.
    iDestruct "Alive" as "[token2 Alive]".
    iMod (kill_lt k sa1 sd1 with "[State token token2]") as "[State dead]". { iFrame. }
    iMod ("back" with "[State Alive]") as "X".
    { iExists (sa1 ∖ {[k]}). iExists (sd1 ∪ {[k]}). iFrame. }
    iModIntro. unfold llft_dead. iExists k. iFrame "dead". iPureIntro. set_solver.
Qed.
  
Lemma llftl_borrow_shared κ (P : iProp Σ) :
    ▷ P ={↑NLLFT}=∗ (llft_alive κ &&{↑NLLFT}&&> ▷ P) ∗ (llft_dead κ ={↑NLLFT}=∗ ▷ P).
Proof.
  iIntros "P".
  iMod new_cancel as (γc) "c1".
  iMod (inv_alloc_with_guard (NLLFT) (↑NLLFT) ((P ∨ (llft_dead κ ∗ Cancel γc))) with "[P]") as "[#Tinv #Tguard]".
  { iNext. iLeft. iFrame "P". }
  iModIntro.
  iSplit.
  { 
    iAssert (llft_alive κ &&{ ↑NLLFT ∪ ↑NLLFT }&&> ▷ P) as "H".
    { iApply
      (guards_or (llft_alive κ) (llft_alive κ) (llft_dead κ ∗ Cancel γc) (▷ P)).
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

Lemma not_subset_eq_get (a b : gset nat) : (a ⊈ b) → ∃ k , k ∈ a ∧ k ∉ b.
Proof.
  assert (∀ r , list_to_set r ⊈ b → ∃ u: nat , u ∈ ((list_to_set r) : gset nat) ∧ u ∉ b) as X.
  { induction r.
    - intros emp. rewrite list_to_set_nil in emp. set_solver.
    - intros not_in. rewrite list_to_set_cons in not_in.
      have h : Decision (a0 ∈ b) by solve_decision. destruct h as [h|n]; trivial.
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

Lemma llftl_incl_dead_implies_dead κ κ' :
    ⊢ llftctx ∗ llft_incl κ κ' ∗ llft_dead κ' ={↑NLLFT}=∗ llft_dead κ.
Proof.
  iIntros "[#ctx [#incl #dead]]".
  
  unfold llft_incl.
  
  leaf_hyp "incl" rhs to (False)%I as "G2".
  {
    leaf_by_sep. iIntros "a". iExFalso.
    iApply (llftl_not_own_end κ'). iFrame. iFrame "dead".
  }
  unfold llftctx.
  leaf_hyp "ctx" rhs to ((∃ sa sd : gset nat, ⌜ κ ⊆ sa ⌝ ∗ LtState sa sd ∗ llft_alive sa)
      ∨ (∃ sa sd : gset nat, ⌜ ¬(κ ⊆ sa) ⌝ ∗ LtState sa sd ∗ llft_alive sa) )%I
      as "ctx2".
  {
    leaf_by_sep. iIntros "T". iSplitL.
      - iDestruct "T" as (sa sd) "state_alive".
        have h : Decision (κ ⊆ sa) by solve_decision. destruct h as [h|n]; trivial.
        + iLeft. iExists sa. iExists sd. iFrame. iPureIntro. trivial.
        + iRight. iExists sa. iExists sd. iFrame. iPureIntro. trivial.
      - iIntros "T". iDestruct "T" as "[T|T]".
        + iDestruct "T" as (sa sd) "[_ T]". iExists sa. iExists sd. iFrame.
        + iDestruct "T" as (sa sd) "[_ T]". iExists sa. iExists sd. iFrame.
    }
  
    iAssert (True &&{ ↑NLLFT}&&> (∃ sa sd : gset nat, ⌜κ ⊈ sa⌝ ∗ LtState sa sd ∗ llft_alive sa)) as "G3".
      { iApply guards_or_guards_false. iFrame "ctx2". 
        leaf_goal rhs to (llft_alive κ). { iFrame "G2". }
        leaf_by_sep.
        { iIntros "T". 
            iDestruct "T" as (sa sd) "[%ksa [state alive]]".
              unfold llft_alive.
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
      - iDestruct (LtState_entails_Dead k sa sd with "State") as "#deadk"; trivial.
        iMod ("back" with "[State alive]") as "true". { iExists sa. iExists sd. iFrame. iPureIntro; trivial. } iModIntro. unfold llft_dead. iExists k. iFrame "deadk". iPureIntro. apply k_in.
      - (* weird technicality, if k was never made alive in the first place;
          first create it, then immediately kill it *)
        iMod (new_lt k sa sd with "State") as "[State [al1 al2]]"; trivial.
        iMod (kill_lt k (sa ∪ {[ k ]}) sd with "[State al1 al2]") as "[State deadk]".
          { iFrame. }
        iMod ("back" with "[State alive]") as "J".
        { iExists sa. iExists (sd ∪ {[k]}). iFrame.
          replace (((sa ∪ {[k]}) ∖ {[k]})) with sa.
          { iFrame. iPureIntro. trivial. } set_solver.
        }
        iModIntro. unfold llft_dead. iExists k. iFrame "deadk". iPureIntro; trivial.
Qed.

End LtResource.
