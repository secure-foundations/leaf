Require Import guarding.own_and.
Require Import guarding.lib.boxes.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.algebra Require Import dfrac_agree.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

(* Leaf Lifetime Logic. Based loosely on RustBelt's lifetime logic. *)

(* We represent borrows in 2 states:

 - `Borrow al de` is a borrow which is "active" whenever `al` is alive (i.e., every
   unit of `al` is alive) AND `de` is dead (i.e., at least one unit of `de` is dead).
   This conveniently lets us represent borrows and inheritances with
   one unified representation. Whenever we start a new borrow for prop P at lifetime
   κ, we can create two Borrows:

      Borrow κ {[default_dead]},    <-- the main borrow
      Borrow ∅ κ.                   <-- the inheritance
   
   You can see that the borrow is active as long as κ is alive; but once κ is dead,
   the inheritance becomes active (which lets the user regain ownership of P).
   (Here `default_dead` is some dummy lifetime unit that is always dead.)
   
   Likewise, we can handle reborrows in a similar way. Given a borrow:

      Borrow κ {[default_dead]}
   
   We can "split" it:
   
      Borrow (κ ∪ κ') {[default_dead]}    <-- the new borrow at κ ⊓ κ'
      Borrow κ κ'                         <-- the inheritance

 - Unborrow bl al de
 
   An "unborrow" is what happens when you exchange a lifetime token for the
   proposition P behind a borrow (e.g., in llftl_bor_acc).
   Specifically, you can exchange `Borrow al de` for `Unborrow bl al de` where `bl` is
   the "blocked" set - the lifetime tokens that are exchanged.
   The idea is that, since these blocked tokens are exchanged, we know that these blocked
   tokens must outlive the unborrow.
   
   Why is `bl` separate from `al`? The reason is to deal with lifetime inclusions.
   A full borrow `&κ P` is actually encoded as:
   
      ∃ κ' , κ ⊑ κ' * OwnBor _ (Borrow κ' {[default_dead]})
   
   In other words, to the user it looks like the borrow is at κ, but in our internal model
   it's at κ'. In this case, we would have bl = κ and al = κ'.
   
   The last thing we need for this system to work is to be able to enforce the constraint
   "if bl is alive, then al is alive". (Because what we have is that `bl` outlives the unborrow,
   but what we need is that `al` outlives the unborrow.)
   To do this, we can make use of the lifetime inclusion κ ⊑ κ'.
   This requires us to maintain a set of "outlives" constraints, and all the lifetime inclusions
   needed to enforce these constraints.
 
 **Notes about the Resource**
 
   Our resource defines, essentially, an "authoritative map" of all BorStates, indexed
   by slices_names:
   
      Definition gmap_bor_state := gmap slice_name BorState.
   
   along with individual fragments, each given by a pair (slice_name, BorState).
   
   However, these do not *exactly* match up, for a couple of reasons:
   
   1. You're always allowed to create `Borrow al de` fragments as long as they are
      permanently dead (i.e., `al` is already dead)
   
   2. Even for borrows that are active, the value of `de` in the fragment and in the
      authoritative map might differ as long as they'll always be consistent in the future.
   
   In the essence, the authoritative map and the fragments are only allowed to differ in
   ways that can't be observed now or in the future, based on the current alive/dead state.
   See the `consistent_modulo` definition in this file.
*)

Inductive BorState :=
  | Borrow : gset nat → gset nat → BorState
  | Unborrow : gset nat → gset nat → gset nat → BorState.

Global Instance eq_dec_bor_state : EqDecision BorState.
Proof. solve_decision. Qed.

Global Instance countable_bor_state : Countable BorState.
Proof.
  set (enc bs := match bs with
    | Borrow a b => inl (a, b)
    | Unborrow a b c => inr (a, b, c)
    end).
  set (dec y := Some match y with
    | inl (a, b) => Borrow a b
    | inr (a, b, c) => Unborrow a b c
    end).
  refine (inj_countable enc dec _). by intros []. 
Qed.

Definition gmap_bor_state := gmap slice_name BorState.
Definition gmultiset_bor_state := gmultiset (slice_name * BorState).
Definition gmap_props Σ := gmap slice_name (iProp Σ).

Inductive LtRa :=
  | LtOk : (option (gset nat * gset nat)) → gmultiset nat → gset nat →
            option gmap_bor_state → gmultiset_bor_state →
            LtRa
  | LtFail.
  
Instance lt_op : Op LtRa := λ a b , match a, b with
  | LtOk (Some _) _ _ _ _, LtOk (Some _) _ _ _ _ => LtFail
  | LtOk _ _ _ (Some _) _, LtOk _ _ _ (Some _) _ => LtFail
  | LtOk o1 a1 d1 m1 ms1, LtOk o2 a2 d2 m2 ms2 =>
      LtOk
        (match o1, o2 with Some o, _ => Some o | _, o => o end)
        (a1 ⊎ a2)
        (d1 ∪ d2)
        (match m1, m2 with Some m, _ => Some m | _, m => m end)
        (ms1 ⊎ ms2)
  | _, _ => LtFail
end.

Definition is_not_permanently_dead (sd : gset nat) (bs: BorState) :=
    match bs with
        | Borrow al de => al ## sd
        | Unborrow _ _ _ => True
    end. 

Definition consistent_bs (sd: gset nat) (bs bs': BorState) :=
    match bs, bs' with
        | Borrow al de, Borrow al' de' =>
            al = al'
            ∧ (de = de' ∨ (¬(de' ## sd) ∧ ¬(de ## sd)))
        | _, _ => bs = bs'
    end.

Definition consistent_modulo (sd : gset nat) (g : gmap_bor_state) (gs: gmultiset_bor_state)
  := (∀ sn bs' bs ,
        g !! sn = Some bs' →
        is_not_permanently_dead sd bs →
        (sn, bs) ∈ gs →
        consistent_bs sd bs bs' ∧ multiplicity (sn, bs) gs = 1
     )
     ∧ (∀ sn bs ,
        (sn, bs) ∈ gs → 
        is_not_permanently_dead sd bs →
        ∃ bs' ,
        g !! sn = Some bs' ∧ consistent_bs sd bs bs')
     ∧ (∀ sn bs1 bs2 ,
        is_not_permanently_dead sd bs1 →
        is_not_permanently_dead sd bs2 →
        (sn, bs1) ∈ gs →
        (sn, bs2) ∈ gs →
        bs1 = bs2
     ).
             
(*Lemma consistent_modulo_for_new_lt sa sd g gs k :
  consistent_modulo sd g gs →
  consistent_modulo sd g gs.*)
  
Lemma consistent_bs_on_kill sd bs bs' k :
  (consistent_bs sd bs bs' → consistent_bs (sd ∪ {[k]}) bs bs').
Proof.
  destruct bs as [al de|bl al de]; destruct bs' as [al' de'|bl' al' de']; try discriminate.
  - unfold consistent_bs. set_solver.
  - unfold consistent_bs. trivial.
Qed.

Lemma is_not_permanently_dead_on_kill sd bs' k :
  (is_not_permanently_dead (sd ∪ {[k]}) bs' → is_not_permanently_dead sd bs').
Proof.
  unfold is_not_permanently_dead. destruct bs'; set_solver.
Qed.

Lemma consistent_modulo_for_kill_lt sd g gs k :
  consistent_modulo sd g gs →
  consistent_modulo (sd ∪ {[k]}) g gs.
Proof.
  intros [Hfwd [Hrev Hunique]]. split.
  { intros sn bs' bs. have Hf := Hfwd sn bs' bs.
    have Hx := consistent_bs_on_kill sd bs bs' k.
    have Hy := is_not_permanently_dead_on_kill sd bs k.
    intuition.
  }
  split.
  { intros sn bs Hin Hnotperm.
    assert (is_not_permanently_dead sd bs) as X. {
      apply is_not_permanently_dead_on_kill with (k := k). trivial.
    }
    have Hr := Hrev sn bs Hin X.
    destruct Hr as [bs' Hr]. exists bs'.
    have Hx := consistent_bs_on_kill sd bs bs' k.
    intuition.
  }
  {
    intros sn bs1 bs2. have Hu := Hunique sn bs1 bs2.
    have Hy := is_not_permanently_dead_on_kill sd bs1 k.
    have Hz := is_not_permanently_dead_on_kill sd bs2 k.
    intuition.
  }
Qed.

Lemma consistent_modulo_for_alloc_bs sd mbs gs sn bs bs' :
  mbs !! sn = None →
  consistent_bs sd bs bs' →
  consistent_modulo sd mbs gs →
  consistent_modulo sd (<[sn:=bs']> mbs) ({[+ (sn, bs) +]} ⊎ gs).
Proof.
  intros Hnone Hcon [Hfwd [Hrev Hunique]]. split.
  { intros sn0 bs'0 bs0. destruct (decide (sn = sn0)).
    - subst sn0. intros Hsome. rewrite lookup_insert in Hsome. inversion Hsome. subst bs'0.
      intros Hnotperm Hinm.
      assert ((sn, bs0) ∉ gs) as Hnotin. {
        intros Hin. have Hr := Hrev sn bs0 Hin Hnotperm. destruct Hr as [bsx [Ha Hb]].
        rewrite Hnone in Ha. discriminate.
      }
      rewrite gmultiset_elem_of_disj_union in Hinm.
      destruct Hinm as [Hinm|]; last by set_solver.
      rewrite gmultiset_elem_of_singleton in Hinm. inversion Hinm. subst bs0.
      split; trivial. rewrite multiplicity_disj_union.
      rewrite elem_of_multiplicity in Hnotin.
      rewrite multiplicity_singleton. lia.
    - intros Hsome Hnotperm Helem. rewrite lookup_insert_ne in Hsome; trivial.
      rewrite gmultiset_elem_of_disj_union in Helem. destruct Helem as [Helem|Helem].
      + rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst sn0. contradiction.
      + have Hf := Hfwd sn0 bs'0 bs0 Hsome Hnotperm Helem.
        destruct Hf as [Hcons Hmul]. split; trivial.
        rewrite multiplicity_disj_union.
        rewrite multiplicity_singleton_ne. { lia. }
        intro Heq. inversion Heq. subst sn0. contradiction.
  } split. {
    intros sn0 bs0 Helem Hnotperm. rewrite gmultiset_elem_of_disj_union in Helem.
    destruct Helem as [Helem|Helem].
    - rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst sn0. subst bs0.
      exists bs'. split; trivial. rewrite lookup_insert. trivial.
    - have Hr := Hrev sn0 bs0 Helem Hnotperm.
      destruct Hr as [bs0' [Hr Hcons]]. exists bs0'. rewrite lookup_insert_ne; intuition.
      subst sn0. rewrite Hnone in Hr. discriminate.
  } {
    intros sn0 bs1 bs2 Hnotperm1 Hnotperm2 Helem1 Helem2.
    rewrite gmultiset_elem_of_disj_union in Helem1.
    rewrite gmultiset_elem_of_disj_union in Helem2.
    destruct Helem1 as [Helem1|Helem1]; destruct Helem2 as [Helem2|Helem2].
    - rewrite gmultiset_elem_of_singleton in Helem1. inversion Helem1. subst bs1.
      rewrite gmultiset_elem_of_singleton in Helem2. inversion Helem2. subst bs2.
      trivial.
    - rewrite gmultiset_elem_of_singleton in Helem1. inversion Helem1. subst bs1. subst sn0.
      have Hr := Hrev sn bs2 Helem2 Hnotperm2. destruct Hr as [bs2' [Hr Hcons]].
      rewrite Hnone in Hr. discriminate.
    - rewrite gmultiset_elem_of_singleton in Helem2. inversion Helem2. subst bs2. subst sn0.
      have Hr := Hrev sn bs1 Helem1 Hnotperm1. destruct Hr as [bs1' [Hr Hcons]].
      rewrite Hnone in Hr. discriminate.
    - apply (Hunique sn0); trivial.
  }
Qed.

Lemma consistent_bs_refl sd bs :
  consistent_bs sd bs bs.
Proof.
  unfold consistent_bs; destruct bs; trivial. split; trivial. left. trivial.
Qed.

Lemma consistent_modulo_for_alloc_fake sd g gs sn bs :
  (¬(is_not_permanently_dead sd bs)) →
  consistent_modulo sd g gs →
  consistent_modulo sd g ({[+ (sn, bs) +]} ⊎ gs).
Proof.
  intros Hcon [Hfwd [Hrev Hunique]]. split.
  { intros sn0 bs'0 bs0 Hsome Hnotperm Helem.
    rewrite gmultiset_elem_of_disj_union in Helem. destruct Helem as [Helem|Helem].
      - rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst bs0.
        contradiction.
      - have Hf := Hfwd sn0 bs'0 bs0 Hsome Hnotperm Helem. destruct Hf as [Hcons Hmult].
        split; trivial. rewrite multiplicity_disj_union.
        assert (¬ (0 < multiplicity (sn0, bs0) {[+ (sn, bs) +]})) as X. {
          rewrite <- elem_of_multiplicity.
          intro Heq. rewrite gmultiset_elem_of_singleton in Heq. inversion Heq. subst bs0.
          contradiction.
        }
        assert (multiplicity (sn0, bs0) {[+ (sn, bs) +]} = 0) as Y by lia.
        rewrite Y. rewrite Hmult. lia.
 } split. {
    intros sn0 bs0 Helem Hnotperm. rewrite gmultiset_elem_of_disj_union in Helem.
    destruct Helem as [Helem|Helem].
    - rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst bs0. contradiction.
    - have Hr := Hrev sn0 bs0 Helem Hnotperm.
      destruct Hr as [bs0' [Hr Hcons]]. exists bs0'. intuition.
 } {
   intros sn0 bs1 bs2 Hnotperm1 Hnotperm2 Helem1 Helem2.
   rewrite gmultiset_elem_of_disj_union in Helem1.
   rewrite gmultiset_elem_of_disj_union in Helem2.
   destruct Helem1 as [Helem1|Helem1].
   { rewrite gmultiset_elem_of_singleton in Helem1. inversion Helem1. subst bs1. contradiction. }
   destruct Helem2 as [Helem2|Helem2].
   { rewrite gmultiset_elem_of_singleton in Helem2. inversion Helem2. subst bs2. contradiction. }
   apply (Hunique sn0); trivial.
 }
Qed.

Local Instance decide_is_not_permanently_dead sd bs : Decision (is_not_permanently_dead sd bs).
Proof.
  destruct bs; unfold is_not_permanently_dead; solve_decision.
Qed.

Lemma lemma_is_mult_1 (gs : gmultiset_bor_state) (p p1 : slice_name * BorState) :
  p ∈ gs →
  multiplicity p ({[+ p1 +]} ⊎ gs) = 1 →
  multiplicity p gs = 1.
Proof.
  intros Hin Hmult. rewrite multiplicity_disj_union in Hmult.
  assert ((0 < multiplicity p gs)) as X. { rewrite <- elem_of_multiplicity. trivial. }
  lia.
Qed.

Lemma mult_union_1_contra (p : slice_name * BorState) (gs : gmultiset_bor_state) :
  p ∈ gs →
  multiplicity p ({[+ p +]} ⊎ gs) = 1 →
  False.
Proof.
  intros Hin Hmult.
  rewrite multiplicity_disj_union in Hmult. rewrite multiplicity_singleton in Hmult.
  assert ((0 < multiplicity p gs)) as X. { rewrite <- elem_of_multiplicity. trivial. }
  lia.
Qed.

Lemma get_mult_singleton_union_1 (p : slice_name * BorState) (gs : gmultiset_bor_state) :
  p ∉ gs →
  multiplicity p ({[+ p +]} ⊎ gs) = 1.
Proof.
  intros Hnotin.
  rewrite multiplicity_disj_union. rewrite multiplicity_singleton.
  assert (¬(0 < multiplicity p gs)) as X. { rewrite <- elem_of_multiplicity. trivial. }
  lia.
Qed.

Lemma consistent_modulo_for_alloc_mono sd g gs sn bs :
  consistent_modulo sd g ({[+ (sn, bs) +]} ⊎ gs) →
  consistent_modulo sd g gs.
Proof.
  intros [Hfwd [Hrev Hunique]]. split.
  { intros sn0 bs'0 bs0 Hsome Hnotperm Helem.
    assert ((sn0, bs0) ∈ {[+ (sn, bs) +]} ⊎ gs) as X by set_solver.
    have Hf := Hfwd sn0 bs'0 bs0 Hsome Hnotperm X. destruct Hf as [Hf1 Hf2]. split; trivial.
    eapply lemma_is_mult_1; trivial. apply Hf2.
  } split. {
    intros sn0 bs0 Helem Hnotperm. apply Hrev; trivial. set_solver.
  } {
    intros sn0 bs1 bs2 Hperm1 Hperm2 Helem1 Helem2.
    apply (Hunique sn0); trivial; set_solver.
  }
Qed.

Lemma consistent_perserves_notperm sd bs1 bs2 :
  consistent_bs sd bs2 bs1 →
  is_not_permanently_dead sd bs1 →
  is_not_permanently_dead sd bs2.
Proof. unfold consistent_bs, is_not_permanently_dead. destruct bs1, bs2; set_solver. Qed.

Lemma consistent_perserves_notperm_rev sd bs1 bs2 :
  consistent_bs sd bs2 bs1 →
  ¬ is_not_permanently_dead sd bs1 →
  ¬ is_not_permanently_dead sd bs2.
Proof. unfold consistent_bs, is_not_permanently_dead. destruct bs1, bs2; set_solver. Qed.


Lemma consistent_bs_trans sd bs1 bs2 bs3 :
  consistent_bs sd bs1 bs2 →
  consistent_bs sd bs2 bs3 →
  consistent_bs sd bs1 bs3.
Proof.
  unfold consistent_bs; destruct bs1, bs2, bs3; set_solver.
Qed.

Lemma get_not_in sd mbs gs sn bs1 bs2 :
  (is_not_permanently_dead sd bs1) →
  (is_not_permanently_dead sd bs2) →
  consistent_modulo sd mbs ({[+ (sn, bs1) +]} ⊎ gs) →
  (sn, bs2) ∉ gs.
Proof.
  intros Hnotperm1 Hnotperm2 [Hfwd [Hrev Hunique]] Helem.
  assert ((sn, bs2) ∈ {[+ (sn, bs1) +]} ⊎ gs) as X. { set_solver. }
  have Hr := Hrev sn bs2 X Hnotperm2. destruct Hr as [bs0' [Hsome' Hcons]].
  have Hf := Hfwd sn bs0' bs2 Hsome' Hnotperm2 X.
  destruct Hf as [Hf1 Hf2].
  assert (bs2 ≠ bs1) as Hne1. {
    intro Heq. subst bs1.
    apply (mult_union_1_contra _ _ Helem Hf2).
  }
  assert (bs2 = bs1) as Heq1. {
    apply (Hunique sn); trivial. set_solver.
  }
  contradiction.
Qed.
 
Lemma consistent_modulo_for_fix sd g gs sn bs1 bs2 :
  consistent_bs sd bs2 bs1 →
  consistent_modulo sd g ({[+ (sn, bs1) +]} ⊎ gs) →
  consistent_modulo sd g ({[+ (sn, bs2) +]} ⊎ gs).
Proof.
  destruct (decide (is_not_permanently_dead sd bs1)) as [Hpermdead_bs1|Hnotpermdead_bs1].
  {
    intros Hcon [Hfwd [Hrev Hunique]].
    have Hpermdead_bs2 := consistent_perserves_notperm sd bs1 bs2 Hcon Hpermdead_bs1.
    split.
    { intros sn0 bs'0 bs0 Hsome Hnotperm Helem.
      destruct (decide (sn = sn0)).
      - subst sn0.
        rewrite gmultiset_elem_of_disj_union in Helem. 
        
        destruct (decide ((sn, bs0) ∈ gs)) as [Hin|Hout].
        {
          exfalso. apply (get_not_in sd g gs sn bs1 bs0); trivial.
          unfold consistent_modulo; split; trivial; split; trivial.
        }
        destruct Helem as [Helem|Helem]; last by contradiction.
        rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst bs2.
        assert ((sn, bs1) ∈ {[+ (sn, bs1) +]} ⊎ gs) as X. { set_solver. }
        have Hr := Hrev sn bs1 X Hpermdead_bs1. destruct Hr as [bs' [Hsome' Hcons]].
        have Hf := Hfwd sn bs'0 bs1 Hsome Hpermdead_bs1 X.
        rewrite Hsome in Hsome'. inversion Hsome'. subst bs'.
        destruct Hf as [Hcons2 Hmult]. split.
        + apply (consistent_bs_trans sd bs0 bs1 bs'0); trivial.
        + apply get_mult_singleton_union_1; trivial.
     - rewrite gmultiset_elem_of_disj_union in Helem. 
       destruct Helem as [Helem|Helem]. {
          rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst sn0.
          contradiction.
       }
       assert ((sn0, bs0) ∈ {[+ (sn, bs1) +]} ⊎ gs) as Helem2 by set_solver.
       have Hf := Hfwd sn0 bs'0 bs0 Hsome Hnotperm Helem2. destruct Hf as [Hcons Hmult].
        split; trivial. rewrite multiplicity_disj_union.
        rewrite multiplicity_disj_union in Hmult.
        rewrite multiplicity_singleton_ne.
        + rewrite multiplicity_singleton_ne in Hmult; trivial.
          intro Heq. inversion Heq. subst sn. contradiction.
        + intro Heq. inversion Heq. subst sn. contradiction.
   } split. {
    intros sn0 bs Helem Hnotperm.
    rewrite gmultiset_elem_of_disj_union in Helem. destruct Helem as [Helem|Helem].
    - rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst sn0. subst bs.
      assert ((sn, bs1) ∈ {[+ (sn, bs1) +]} ⊎ gs) as Helem2 by set_solver.
      have Hr := Hrev sn bs1 Helem2 Hpermdead_bs1. destruct Hr as [bs' [Hgsn Hcons]].
      exists bs'. split; trivial.
      apply (consistent_bs_trans sd bs2 bs1 bs'); trivial.
    - apply Hrev; trivial. set_solver.
  } {
    intros sn0 bs3 bs4 Hnotperm3 Hnotperm4 Helem3 Helem4.
    rewrite gmultiset_elem_of_disj_union in Helem3. 
    rewrite gmultiset_elem_of_disj_union in Helem4. 
    destruct Helem3 as [Helem3|Helem3]; destruct Helem4 as [Helem4|Helem4].
    - rewrite gmultiset_elem_of_singleton in Helem3. inversion Helem3.
      rewrite gmultiset_elem_of_singleton in Helem4. inversion Helem4. trivial.
    - rewrite gmultiset_elem_of_singleton in Helem3. inversion Helem3. subst sn0.
      exfalso. apply (get_not_in sd g gs sn bs1 bs4); trivial.
      unfold consistent_modulo; split; trivial; split; trivial.
    - rewrite gmultiset_elem_of_singleton in Helem4. inversion Helem4. subst sn0.
      exfalso. apply (get_not_in sd g gs sn bs1 bs3); trivial.
      unfold consistent_modulo; split; trivial; split; trivial.
   - apply (Hunique sn0); trivial; set_solver.
  }
  }
  intros Hcon Hx.
  have Hnotpermdead_bs2 := consistent_perserves_notperm_rev sd bs1 bs2 Hcon Hnotpermdead_bs1.
  apply consistent_modulo_for_alloc_fake; trivial.
  eapply consistent_modulo_for_alloc_mono. apply Hx.
Qed.

Lemma consistent_modulo_for_update sd mbs gs sn bs1 bs2 :
  (is_not_permanently_dead sd bs1) →
  consistent_modulo sd mbs ({[+ (sn, bs1) +]} ⊎ gs) →
  consistent_modulo sd (<[sn:=bs2]> mbs) ({[+ (sn, bs2) +]} ⊎ gs).
Proof.
    intros Hnotperm1 [Hfwd [Hrev Hunique]].
    split.
    { intros sn0 bs'0 bs0 Hsome Hnotperm Helem.
      destruct (decide (sn = sn0)).
      - subst sn0.
        rewrite gmultiset_elem_of_disj_union in Helem. 
        rewrite lookup_insert in Hsome. inversion Hsome. subst bs'0.
        destruct (decide ((sn, bs0) ∈ gs)) as [Hin|Hout].
        {
          exfalso. apply (get_not_in sd mbs gs sn bs1 bs0); trivial.
          unfold consistent_modulo; split; trivial; split; trivial.
        }
        destruct Helem as [Helem|Helem]; last by contradiction.
        rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst bs2.
        assert ((sn, bs1) ∈ {[+ (sn, bs1) +]} ⊎ gs) as X. { set_solver. }
        have Hr := Hrev sn bs1 X Hnotperm1. destruct Hr as [bs' [Hsome' Hcons]].
        have Hf := Hfwd sn bs' bs1 Hsome' Hnotperm1 X.
        destruct Hf as [Hcons2 Hmult]. split.
        + apply consistent_bs_refl.
        + apply get_mult_singleton_union_1; trivial.
     - rewrite gmultiset_elem_of_disj_union in Helem. 
       destruct Helem as [Helem|Helem]. {
          rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst sn0.
          contradiction.
       }
       assert ((sn0, bs0) ∈ {[+ (sn, bs1) +]} ⊎ gs) as Helem2 by set_solver.
       rewrite lookup_insert_ne in Hsome; trivial.
       have Hf := Hfwd sn0 bs'0 bs0 Hsome Hnotperm Helem2. destruct Hf as [Hcons Hmult].
        split; trivial. rewrite multiplicity_disj_union.
        rewrite multiplicity_disj_union in Hmult.
        rewrite multiplicity_singleton_ne.
        + rewrite multiplicity_singleton_ne in Hmult; trivial.
          intro Heq. inversion Heq. subst sn. contradiction.
        + intro Heq. inversion Heq. subst sn. contradiction.
   } split. {
    intros sn0 bs Helem Hnotperm.
    rewrite gmultiset_elem_of_disj_union in Helem. destruct Helem as [Helem|Helem].
    - rewrite gmultiset_elem_of_singleton in Helem. inversion Helem. subst sn0. subst bs.
      assert ((sn, bs1) ∈ {[+ (sn, bs1) +]} ⊎ gs) as Helem2 by set_solver.
      have Hr := Hrev sn bs1 Helem2 Hnotperm1. destruct Hr as [bs' [Hgsn Hcons]].
      exists bs2. split; trivial.
      + apply lookup_insert.
      + apply consistent_bs_refl.
    - destruct (decide (sn = sn0)).
       + exfalso. subst sn0. apply (get_not_in sd mbs gs sn bs1 bs); trivial.
         unfold consistent_modulo; split; trivial; split; trivial.
       + rewrite lookup_insert_ne; trivial. apply Hrev; trivial. set_solver.
  } {
    intros sn0 bs3 bs4 Hnotperm3 Hnotperm4 Helem3 Helem4.
    rewrite gmultiset_elem_of_disj_union in Helem3. 
    rewrite gmultiset_elem_of_disj_union in Helem4. 
    destruct Helem3 as [Helem3|Helem3]; destruct Helem4 as [Helem4|Helem4].
    - rewrite gmultiset_elem_of_singleton in Helem3. inversion Helem3.
      rewrite gmultiset_elem_of_singleton in Helem4. inversion Helem4. trivial.
    - rewrite gmultiset_elem_of_singleton in Helem3. inversion Helem3. subst sn0.
      exfalso. apply (get_not_in sd mbs gs sn bs1 bs4); trivial.
      unfold consistent_modulo; split; trivial; split; trivial.
    - rewrite gmultiset_elem_of_singleton in Helem4. inversion Helem4. subst sn0.
      exfalso. apply (get_not_in sd mbs gs sn bs1 bs3); trivial.
      unfold consistent_modulo; split; trivial; split; trivial.
   - apply (Hunique sn0); trivial; set_solver.
  }
Qed.

Lemma consistent_modulo_for_delete sd mbs gs sn bs :
  (is_not_permanently_dead sd bs) →
  consistent_modulo sd mbs ({[+ (sn, bs) +]} ⊎ gs) →
  consistent_modulo sd (delete sn mbs) gs.
Proof.
    intros Hnotperm1 [Hfwd [Hrev Hunique]].
    split.
    { intros sn0 bs'0 bs0 Hsome Hnotperm Helem.
      destruct (decide (sn = sn0)).
      - subst sn0.
        exfalso. apply (get_not_in sd mbs gs sn bs bs0); trivial.
        unfold consistent_modulo; split; trivial; split; trivial.
     - assert ((sn0, bs0) ∈ {[+ (sn, bs) +]} ⊎ gs) as Helem2 by set_solver.
       rewrite lookup_delete_ne in Hsome; trivial.
       have Hf := Hfwd sn0 bs'0 bs0 Hsome Hnotperm Helem2. destruct Hf as [Hcons Hmult].
        split; trivial.
        rewrite multiplicity_disj_union in Hmult.
        rewrite multiplicity_singleton_ne in Hmult; trivial.
        intro Heq. inversion Heq. subst sn. contradiction.
   } split. {
    intros sn0 bs0 Helem Hnotperm.
    destruct (decide (sn = sn0)).
       + exfalso. subst sn0. apply (get_not_in sd mbs gs sn bs bs0); trivial.
         unfold consistent_modulo; split; trivial; split; trivial.
       + rewrite lookup_delete_ne; trivial. apply Hrev; trivial. set_solver.
  } {
    intros sn0 bs3 bs4 Hnotperm3 Hnotperm4 Helem3 Helem4.
   - apply (Hunique sn0); trivial; set_solver.
  }
Qed.

Lemma consistent_modulo_for_agree sd mbs gs sn bs :
  (is_not_permanently_dead sd bs) →
  consistent_modulo sd mbs ({[+ (sn, bs) +]} ⊎ gs) →
  ∃ bs' : BorState, mbs !! sn = Some bs' ∧ consistent_bs sd bs bs'.
Proof.
  intros Hcon [Hfwd [Hrev Hunique]].
  apply Hrev; trivial. rewrite gmultiset_elem_of_disj_union. left.
  rewrite gmultiset_elem_of_singleton. trivial.
Qed.

Lemma consistent_modulo_for_distinct sd mbs gs sn1 sn2 bs1 bs2 :
  (is_not_permanently_dead sd bs1) →
  (is_not_permanently_dead sd bs2) →
  consistent_modulo sd mbs ({[+ (sn1, bs1) +]} ⊎ {[+ (sn2, bs2) +]} ⊎ gs) →
  sn1 ≠ sn2.
Proof.
  intros Hnotperm1 Hnotperm2 [Hfwd [Hrev Hunique]].
  intro Heq. subst sn2.
  assert (bs1 = bs2) as Hbseq. {
    apply (Hunique sn1); trivial.
    - rewrite gmultiset_elem_of_disj_union. left.
      rewrite gmultiset_elem_of_disj_union. left.
      rewrite gmultiset_elem_of_singleton. trivial.
    - rewrite gmultiset_elem_of_disj_union. left.
      rewrite gmultiset_elem_of_disj_union. right.
      rewrite gmultiset_elem_of_singleton. trivial.
  }
  subst bs2.
  assert ((sn1, bs1) ∈ {[+ (sn1, bs1); (sn1, bs1) +]} ⊎ gs) as X. {
    - rewrite gmultiset_elem_of_disj_union. left.
      rewrite gmultiset_elem_of_disj_union. left.
      rewrite gmultiset_elem_of_singleton. trivial.
  }
  have Hr := Hrev sn1 bs1 X Hnotperm1. destruct Hr as [bs' [Hsome Hcons]].
  have Hf := Hfwd sn1 bs' bs1 Hsome Hnotperm1 X.
  destruct Hf as [Hcons2 Hmult].
  rewrite multiplicity_disj_union in Hmult.
  rewrite multiplicity_disj_union in Hmult.
  rewrite multiplicity_singleton in Hmult. lia.
Qed.

Definition lt_inv (a: LtRa) := match a with
  | LtOk (Some (sa, sd)) a d (Some g) gs =>
      sd = d ∧ sa ∩ sd = ∅
      ∧ (∀ m , (m ∈ sa → multiplicity m a = 2) ∧ (m ∉ sa → multiplicity m a = 0))
      ∧ consistent_modulo sd g gs
  | _ => False
end.

Instance lt_valid : Valid LtRa := λ a , ∃ b , lt_inv (a ⋅ b).

Instance lt_equiv : Equiv LtRa := λ a b , a = b.

Instance lt_pcore : PCore LtRa := λ a , match a with
  | LtOk o1 a1 d1 m1 ms2 => Some (LtOk None ∅ d1 None ∅)
  | LtFail => Some LtFail
end.

Lemma lt_assoc : Assoc (=) lt_op.
Proof.
  unfold Assoc. intros x y z. unfold lt_op.
  destruct x as [[o|] a d [m|] ms|], y as [[o1|] a1 d1 [m1|] ms1|], z as [[o2|] a2 d2 [m2|] ms2|]; trivial; f_equiv; (try set_solver); rewrite gmultiset_disj_union_assoc; trivial.
Qed.
  
Lemma lt_comm : Comm (=) lt_op.
Proof.
  unfold Comm. intros x y. unfold lt_op.
  destruct x as [[o|] a d [m|] ms|], y as [[o1|] a1 d1 [m1|] ms1|]; trivial; f_equiv; (try set_solver); rewrite gmultiset_disj_union_comm; trivial.
Qed.

Lemma LtOk_incl_3 a b d1 d2 m ms
  (d_incl: d1 ⊆ d2)
  : LtOk a b d1 m ms ≼ LtOk a b d2 m ms.
Proof.
  exists (LtOk None ∅ d2 None ∅). destruct a as [a|]; destruct m as [m|]; unfold "⋅", lt_op; f_equiv; try set_solver.
Qed.
  
Lemma multiset_subseteq_of_LtOk_incl o0 a0 d0 m0 ms0 o1 a1 d1 m1 ms1 o2 a2 d2 m2 ms2
  (incl: LtOk o0 a0 d0 m0 ms0 ≡ LtOk o1 a1 d1 m1 ms1 ⋅ LtOk o2 a2 d2 m2 ms2)
  : d1 ⊆ d0.
Proof.
  unfold "⋅", lt_op in incl; destruct o1, o2, m1, m2; inversion incl; set_solver.
Qed.

Definition lt_ra_mixin : RAMixin LtRa.
Proof. split.
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
      destruct x as [o a d m ms|], y as [o1 a1 d1 m1 ms1|]; destruct xley as [[o2 a2 d2 m2 ms2|] equ];
      unfold pcore, lt_pcore; unfold pcore, lt_pcore in peq; inversion peq; subst cx.
      + exists (LtOk None ∅ d1 None ∅); intuition.  apply LtOk_incl_3.
          eapply multiset_subseteq_of_LtOk_incl. apply equ.
      + unfold "⋅", lt_op in equ. inversion equ. destruct o, m; discriminate.
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

Global Instance lt_unit : Unit LtRa := LtOk None ∅ ∅ None ∅.

Definition lt_ucmra_mixin : UcmraMixin LtRa.
split; trivial.
  - exists (LtOk (Some (∅, ∅)) ∅ ∅ (Some ∅) ∅). unfold lt_inv. simpl.
      unfold consistent_modulo. set_solver.
  - intro x. destruct x as [o a d|]; simpl; trivial.
      destruct o; trivial.
      + unfold ε, lt_unit, "⋅", lt_op. f_equiv; set_solver.
      + unfold ε, lt_unit, "⋅", lt_op. f_equiv; set_solver.
Qed.

Canonical Structure ltUR := Ucmra LtRa lt_ucmra_mixin.

Definition outlives_set := gset (gset nat * nat).
  
Class llft_logicGpreS Σ := {
  llft_logic_inG : inG Σ ltUR ;
  exclG : inG Σ (exclR unitO) ;
  outlivesG : inG Σ (dfrac_agreeR (leibnizO outlives_set)) ;
  delayedG : inG Σ (dfrac_agreeR (leibnizO (option (nat * gset nat)))) ;
  llft_boxG : boxG Σ
}.
Class llft_logicGS Σ := LlftLogicG {
  llft_inG : llft_logicGpreS Σ;
  llft_name: gname;
  o_name: gname;
  d_name: gname;
}.
Global Existing Instance llft_logic_inG.
Global Existing Instance exclG.
Global Existing Instance outlivesG.
Global Existing Instance delayedG.
Global Existing Instance llft_inG.
Global Existing Instance llft_boxG.

Definition llft_logicΣ : gFunctors := #[
  GFunctor ltUR ;
  GFunctor (exclR unitO) ;
  GFunctor (dfrac_agreeR (leibnizO outlives_set)) ;
  GFunctor (dfrac_agreeR (leibnizO (option (nat * gset nat)))) ;
  boxΣ
].

Global Instance subG_lt_logicΣ Σ : subG llft_logicΣ Σ → llft_logicGpreS Σ.
Proof.
  solve_inG.
Qed.

Section LlftHelperResources.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGpreS Σ}.
  
  Definition lt_state (sa sd : gset nat) := LtOk (Some (sa, sd)) ∅ sd None ∅.
  Definition LtState γlt (sa sd : gset nat) : iProp Σ := own γlt (lt_state sa sd).

  Definition dead (k: nat) := LtOk None ∅ ({[ k ]}) None ∅.
  Definition Dead γlt (k: nat) : iProp Σ := own γlt (dead k).

  Definition alive (k: nat) := LtOk None ({[+ k +]}) ∅ None ∅.
  Definition Alive γlt (k: nat) : iProp Σ := own γlt (alive k).
  
  Definition auth_bor_state (mbs: gmap_bor_state) := LtOk None ∅ ∅ (Some mbs) ∅.
  Definition own_bor_state (sn: slice_name) (bs: BorState) := LtOk None ∅ ∅ None {[+ (sn, bs) +]}.
  
  Definition AuthBorState (γlt: gname) (mbs: gmap_bor_state) : iProp Σ :=
      own γlt (auth_bor_state mbs).
  Definition OwnBorState (γlt: gname) (sn: slice_name) (bs: BorState) : iProp Σ :=
      own γlt (own_bor_state sn bs).
  
  Definition default_dead : nat := 0.
  
  Lemma lt_alloc :
    ⊢ |==> ∃ γ , LtState γ ∅ ∅ ∗ AuthBorState γ ∅.
  Proof.
    unfold LtState, AuthBorState.
    setoid_rewrite <- own_op. apply own_alloc. unfold "✓", cmra_valid, ltR, lt_valid.
    exists (LtOk None ∅ ∅ None ∅). simpl. unfold consistent_modulo. set_solver.
  Qed.

  Lemma update_helper (a b : LtRa)
    (cond: ∀ z : ltR, lt_inv (a ⋅ z) → lt_inv (b ⋅ z))
    : a ~~> b.
  Proof.
    rewrite cmra_discrete_total_update.
    intros y ay. destruct ay as [t ay]. rewrite <- lt_assoc in ay.
    have co := cond _ ay. exists t. rewrite <- lt_assoc. apply co.
  Qed.

  Lemma update_helper2 (x y : LtRa)
    (cond: ∀ o a d m ms , lt_inv (x ⋅ LtOk o a d m ms) → lt_inv (y ⋅ LtOk o a d m ms))
    : x ~~> y.
  Proof.
    apply update_helper. intros z. destruct z as [o a d m ms|].
    - apply cond.
    - intros lti. unfold lt_inv in lti.
      replace (x ⋅ LtFail) with LtFail in lti. { contradiction. }
      destruct x as [o a d m ms|]; trivial. destruct o, m; trivial.
  Qed.
    
  Lemma alloc_bor_state γlt sn mbs bs :
      (mbs !! sn = None) →
      AuthBorState γlt mbs
      ⊢ |==> AuthBorState γlt (<[ sn := bs ]> mbs) ∗ OwnBorState γlt sn bs.
  Proof.
    intros Hnone.
    setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [[sa sd]|], g as [g|].
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_alloc_bs; trivial.
      apply consistent_bs_refl; trivial.
    - contradiction.
    - contradiction.
  Qed.
      
  Lemma alloc_bor_state2 γlt sn mbs sa sd al de de' :
      (mbs !! sn = None) →
      (de = de' ∨ (¬(de' ## sd) ∧ ¬(de ## sd))) →
      LtState γlt sa sd ∗ AuthBorState γlt mbs
      ⊢ |==> LtState γlt sa sd ∗ AuthBorState γlt (<[ sn := Borrow al de' ]> mbs) ∗ OwnBorState γlt sn (Borrow al de).
  Proof.
    intros Hnone Hconsistent.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [s|], g as [g|].
    - contradiction.
    - contradiction.
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id. rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_alloc_bs; trivial.
      unfold consistent_bs. split; trivial.
  Qed.
      
  (*Lemma alloc_fake_bor_state_tok γlt sn (alive dead : gset nat) k :
      (k ∈ alive) →
      Dead γlt k ⊢ |==> OwnBorState γlt sn (Borrow alive dead).*)
      
  Lemma alloc_fake_bor_state_lts γlt sn (sa sd: gset nat) (alive dead : gset nat) :
      ¬(alive ## sd) →
      LtState γlt sa sd
       ⊢ |==> LtState γlt sa sd ∗ OwnBorState γlt sn (Borrow alive dead).
  Proof.
    intros Hnotdisj.
    setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [s|], g as [g|].
    - contradiction.
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_alloc_fake; trivial.
    - contradiction.
  Qed.
  
  Lemma update_bor_state_borrow_fix_dead_helper γlt sn al de de' k k' :
      (k ∈ de) →
      (k' ∈ de') →
      Dead γlt k ∗ Dead γlt k' ∗ OwnBorState γlt sn (Borrow al de) ==∗ Dead γlt k ∗ Dead γlt k' ∗ OwnBorState γlt sn (Borrow al de').
  Proof.
    intros Hk Hk'.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [[sa sd]|], g as [g|].
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id. rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm. rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_fix with (bs1 := Borrow al de); trivial.
      unfold consistent_bs. split; trivial.
      right. split. { set_solver. } { set_solver. }
    - contradiction.
    - contradiction.
    - contradiction.
  Qed.

  Lemma update_bor_state_borrow_fix_dead γlt sn al de de' k k' :
      (k ∈ de) →
      (k' ∈ de') →
      Dead γlt k ∗ Dead γlt k' ∗ OwnBorState γlt sn (Borrow al de) ==∗ OwnBorState γlt sn (Borrow al de').
  Proof.
    intros Hk Hk'. iIntros "D".
    iMod (update_bor_state_borrow_fix_dead_helper with "D") as "[D1 [D2 X]]"; trivial.
    trivial.
  Qed.
      
  Lemma update_bor_state_borrow_fix_dead_lts γlt sa sd sn al de de' :
      ¬(de ## sd) →
      ¬(de' ## sd) →
      LtState γlt sa sd ∗ OwnBorState γlt sn (Borrow al de) ==∗ LtState γlt sa sd ∗ OwnBorState γlt sn (Borrow al de').
  Proof.
    intros Hk Hk'.
    setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [s|], g as [g|].
    - contradiction.
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_fix with (bs1 := Borrow al de); trivial.
      unfold consistent_bs. split; trivial.
      right. split. { set_solver. } { set_solver. }
    - contradiction.
  Qed.
      
  Lemma update_bor_state_borrow_lts γlt sn mbs sa sd alive dead bs' :
      (alive ## sd) →
      LtState γlt sa sd ∗ AuthBorState γlt mbs ∗ OwnBorState γlt sn (Borrow alive dead)
      ⊢ |==> LtState γlt sa sd ∗ AuthBorState γlt (<[ sn := bs' ]> mbs) ∗ OwnBorState γlt sn bs'.
  Proof.
    intros Hdisj.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [s|], g as [g|].
    - contradiction.
    - contradiction.
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id. rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm. rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_update with (bs1 := Borrow alive dead); trivial.
  Qed.
  
  (*Lemma update_bor_state_borrow_tok γlt sn mbs alive dead bs' :
      ([∗ set] k ∈ alive , Alive γlt k)
          ∗ AuthBorState γlt mbs ∗ OwnBorState γlt sn (Borrow alive dead)
      ⊢ |==> AuthBorState γlt (<[ sn := bs' ]> mbs) ∗ OwnBorState γlt sn bs'.*)
      
  (*Lemma update_bor_state_unborrow γlt sn mbs bl al de bs' :
      AuthBorState γlt mbs ∗ OwnBorState γlt sn (Unborrow bl al de)
      ⊢ |==> AuthBorState γlt (<[ sn := bs' ]> mbs) ∗ OwnBorState γlt sn bs'.
      *)
  
  Lemma delete_bor_state_borrow_lts γlt sn mbs sa sd al de :
      (al ## sd) →
      LtState γlt sa sd ∗ AuthBorState γlt mbs ∗ OwnBorState γlt sn (Borrow al de)
        ⊢ |==> 
      LtState γlt sa sd ∗ AuthBorState γlt (delete sn mbs).
  Proof.
    intros Hdisj.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [s|], g as [g|].
    - contradiction.
    - contradiction.
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm. rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_delete with (bs := Borrow al de); trivial.
  Qed.
      
  Lemma delete_bor_state_unborrow γlt sn mbs bl al de :
      AuthBorState γlt mbs ∗ OwnBorState γlt sn (Unborrow bl al de)
      ⊢ |==> AuthBorState γlt (delete sn mbs).
  Proof.
    setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.
    intros o a d g gs lti. destruct o as [[sa sd]|], g as [g|].
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. } split. { set_solver. } split. { set_solver. }
      rewrite gmultiset_disj_union_left_id.
      rewrite gmultiset_disj_union_left_id in cm.
      apply consistent_modulo_for_delete with (bs := Unborrow bl al de); trivial.
      unfold is_not_permanently_dead. trivial.
    - contradiction.
    - contradiction.
  Qed.
      
  (*Lemma agree_bor_state_borrow_tok γlt sn mbs (alive dead : gset nat) :
      ([∗ set] k ∈ alive , Alive γlt k)
          ∗ AuthBorState γlt mbs ∗ OwnBorState γlt sn (Borrow alive dead)
      ⊢ |==> ⌜mbs !! sn = Some (Borrow alive dead)⌝.
      *)
      
  Lemma agree_bor_state_borrow_lts γlt sn mbs (sa sd al de : gset nat) :
      (al ## sd) →
      LtState γlt sa sd
          ∗ AuthBorState γlt mbs ∗ OwnBorState γlt sn (Borrow al de)
      ⊢ ∃ de' , ⌜mbs !! sn = Some (Borrow al de') ∧ (de = de' ∨ (¬(de' ## sd) ∧ ¬(de ## sd)))⌝.
  Proof.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    intros Hal. iIntros "H". iDestruct (own_valid with "H") as "%val". iPureIntro.
    unfold valid, cmra_valid, ltR, lt_valid in val. destruct val as [b lti].
    destruct b as [o a d g gs|]; try contradiction.
    destruct o as [s|], g as [g|]; try contradiction.
    simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
    rewrite gmultiset_disj_union_left_id in cm. rewrite gmultiset_disj_union_left_id in cm.
    destruct (consistent_modulo_for_agree sd mbs gs sn (Borrow al de)) as [bs' x]; trivial.
    destruct bs' as [al' de'|].
    - exists de'. unfold consistent_bs in x. destruct x as [Ha [Hb Hc]]. subst al'. intuition.
    - unfold consistent_bs in x. destruct x as [Ha Hb]. discriminate.
  Qed.
      
  Lemma agree_bor_state_unborrow γlt sn mbs bl al de :
      AuthBorState γlt mbs ∗ OwnBorState γlt sn (Unborrow bl al de)
      ⊢ ⌜mbs !! sn = Some (Unborrow bl al de)⌝.
  Proof.
    setoid_rewrite <- own_op.
    iIntros "H". iDestruct (own_valid with "H") as "%val". iPureIntro.
    unfold valid, cmra_valid, ltR, lt_valid in val. destruct val as [b lti].
    destruct b as [o a d g gs|]; try contradiction.
    destruct o as [[sa sd]|], g as [g|]; try contradiction.
    simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
    rewrite gmultiset_disj_union_left_id in cm.
    destruct (consistent_modulo_for_agree sd mbs gs sn (Unborrow bl al de)) as [bs' x]; trivial.
    { unfold is_not_permanently_dead. trivial. }
    destruct bs' as [|bl' al' de'].
    - unfold consistent_bs in x. destruct x as [Ha Hb]. discriminate.
    - unfold consistent_bs in x. destruct x as [Ha Hb]. rewrite Hb. trivial.
  Qed.
      
  Lemma distinct_bor_state_borrow_borrow_lts γlt sn1 sn2 al1 de1 al2 de2 sa sd :
      (al1 ## sd) →
      (al2 ## sd) →
      LtState γlt sa sd
        ∗ OwnBorState γlt sn1 (Borrow al1 de1)
        ∗ OwnBorState γlt sn2 (Borrow al2 de2)
      ⊢ ⌜sn1 ≠ sn2⌝.
  Proof.
    intros Hal1 Hal2.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "H". iDestruct (own_valid with "H") as "%val". iPureIntro.
    unfold valid, cmra_valid, ltR, lt_valid in val. destruct val as [b lti].
    destruct b as [o a d g gs|]; try contradiction.
    destruct o as [s|], g as [g|]; try contradiction.
    simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
    rewrite gmultiset_disj_union_left_id in cm.
    apply (consistent_modulo_for_distinct sd g gs sn1 sn2 (Borrow al1 de1) (Borrow al2 de2)); trivial.
  Qed.
  
  Local Instance pers_dead2 γlt k : Persistent (Dead γlt k).
  Proof.
    apply own_core_persistent. unfold CoreId. trivial.
  Qed.
      
  Lemma get_all_deads γlt sa sd :
      LtState γlt sa sd ==∗ LtState γlt sa sd ∗ (∀ d , ⌜d ∈ sd⌝ -∗ Dead γlt d).
  Proof.
    unfold LtState, lt_state. iIntros "o". 
    iModIntro.
    iAssert (∀ d : nat, ⌜d ∈ sd⌝ -∗ Dead γlt d)%I with "[o]" as "#H".
    - iIntros (d) "%Hsd".
      replace (LtOk (Some (sa, sd)) ∅ sd None ∅) with (LtOk (Some (sa, sd)) ∅ sd None ∅ ⋅ LtOk None ∅ {[d]} None ∅).
      + iDestruct "o" as "[o1 o2]". iFrame "o2".
      + unfold "⋅", lt_op. f_equal. set_solver.
    - iFrame. iFrame "#".
  Qed.

  (* basics *)

  Lemma new_lt γlt k sa sd :
    (k ∉ sa) → (k ∉ sd) →
    LtState γlt sa sd ==∗ LtState γlt (sa ∪ {[ k ]}) sd ∗ Alive γlt k ∗ Alive γlt k.
  Proof.
    intros k_sa k_sd.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.

    intros o a d g gs lti. destruct o as [s|], g as [g|].
    - contradiction. (*unfold "⋅", lt_op, lt_state, lt_inv in lti. contradiction.*)
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. }
      split. { set_solver. }
      split. {
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
      }
      { replace ((∅ ⊎ (∅ ⊎ ∅) ⊎ gs)) with (∅ ⊎ gs) by set_solver. trivial. }
    - contradiction.
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

  Lemma lt_state_incl_lt_ok sa sd sa1 sd1 a d g gs
    : (lt_state sa sd ≼ LtOk (Some (sa1, sd1)) a d g gs) → sa = sa1 ∧ sd = sd1.
  Proof.
    intros lts. destruct lts as [t lts].
    destruct t as [[o|] a1 d1|].
    - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts.
    - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts. split; trivial.
    - unfold lt_state in lts. unfold "⋅", lt_op in lts. inversion lts.
  Qed.

  Lemma alive_incl_lt_ok k sa1 sd1 a d g gs
    : (alive k ≼ LtOk (Some (sa1, sd1)) a d g gs) → lt_inv (LtOk (Some (sa1, sd1)) a d g gs) → k ∈ sa1.
  Proof.
    intros lts lti. destruct lts as [t lts].
    destruct t as [[o|] a1 d1 g1 gs1|].
    - unfold alive in lts. unfold "⋅", lt_op in lts. inversion lts.
        unfold lt_inv in lti.
        destruct g; try contradiction.
        destruct lti as [_ [_ [fm cm]]]. have fmk := fm k.
        have h : Decision (k ∈ sa1) by solve_decision. destruct h as [h|n]; trivial.
        exfalso.
        destruct fmk as [_ fmk]. have fmk1 := fmk n. subst a.
        rewrite multiplicity_disj_union in fmk1.
        rewrite multiplicity_singleton in fmk1. lia.
    - inversion lts.
    - inversion lts.
  Qed.

  Lemma dead_incl_lt_ok k sa1 sd1 a d g gs
    : (dead k ≼ LtOk (Some (sa1, sd1)) a d g gs) → lt_inv (LtOk (Some (sa1, sd1)) a d g gs) → k ∈ sd1.
  Proof.
    intros lts lti. destruct lts as [t lts].
    destruct t as [[o|] a1 d1|].
    - unfold dead in lts. unfold "⋅", lt_op in lts. inversion lts.
        unfold lt_inv in lti. destruct g; try contradiction.
        destruct lti as [sde _]. subst d. set_solver.
    - inversion lts.
    - inversion lts.
  Qed.

  Lemma alive_dead_contradiction k sa sd a d g gs
    : (lt_inv (LtOk (Some (sa, sd)) a d g gs)) → (k ∈ sa) → (k ∈ sd) → False.
  Proof.
    intros lts lti.
    destruct g; try contradiction.
    destruct lts as [_ [no_int _]]. set_solver.
  Qed.

  Lemma lt_state_alive γlt k sa sd :
    LtState γlt sa sd ∧ Alive γlt k ⊢ ⌜ k ∈ sa ⌝.
  Proof.
    iIntros "P". iDestruct (and_own_discrete_ucmra with "P") as (z') "[o [%incl1 %incl2]]".
    iDestruct (own_valid with "o") as "%valz".
    iPureIntro.
    have di := double_incl_lt_inv _ _ _ incl1 incl2 valz.
    destruct di as [z [inc1 [inc2 lti]]].
    destruct z as [[[sa1 sd1]|] a d|]; try contradiction.
    have j := lt_state_incl_lt_ok _ _ _ _ _ _ _ _ inc1. destruct j as [j1 j2]. subst sa.
    apply (alive_incl_lt_ok _ _ _ _ _ _ _ inc2). apply lti.
  Qed.
        
  Lemma lt_state_alive_set γlt lt sa sd :
    LtState γlt sa sd ∗ ([∗ set] k ∈ lt, Alive γlt k) ⊢ ⌜ lt ⊆ sa ⌝.
  Proof.
    iIntros "[State Alive]". unfold "⊆", set_subseteq_instance. iIntros (x) "%Hxlt".
    rewrite (big_sepS_delete _ _ x); trivial. iDestruct "Alive" as "[Alive _]".
    iApply lt_state_alive. iSplit. { iFrame "State". } { iFrame "Alive". }
  Qed.

  Lemma lt_state_dead γlt k sa sd :
    LtState γlt sa sd ∧ Dead γlt k ⊢ ⌜ k ∈ sd ⌝.
  Proof.
    iIntros "P". iDestruct (and_own_discrete_ucmra with "P") as (z') "[o [%incl1 %incl2]]".
    iDestruct (own_valid with "o") as "%valz".
    iPureIntro.
    have di := double_incl_lt_inv _ _ _ incl1 incl2 valz.
    destruct di as [z [inc1 [inc2 lti]]].
    destruct z as [[[sa1 sd1]|] a d|]; try contradiction.
    have j := lt_state_incl_lt_ok _ _ _ _ _ _ _ _ inc1. destruct j as [j1 j2]. subst sd.
    apply (dead_incl_lt_ok _ _ _ _ _ _ _ inc2). apply lti.
  Qed.

  Lemma lt_alive_dead_false γlt k :
    Alive γlt k ∧ Dead γlt k ⊢ False.
  Proof.
    iIntros "P". iDestruct (and_own_discrete_ucmra with "P") as (z') "[o [%incl1 %incl2]]".
    iDestruct (own_valid with "o") as "%valz".
    iPureIntro.
    have di := double_incl_lt_inv _ _ _ incl1 incl2 valz.
    destruct di as [z [inc1 [inc2 lti]]].
    destruct z as [[[sa1 sd1]|] a d|]; try contradiction.
    have j1 := alive_incl_lt_ok _ _ _ _ _ _ _ inc1.
    have j2 := dead_incl_lt_ok _ _ _ _ _ _ _ inc2.
    eapply alive_dead_contradiction. { apply lti. } { apply j1. apply lti. } { apply j2. apply lti. }
  Qed.
  
  Lemma alive_alive_alive_false γlt k :
    Alive γlt k ∗ Alive γlt k ∗ Alive γlt k ⊢ False.
  Proof.
    unfold Alive. rewrite <- own_op. rewrite <- own_op. iIntros "H".
    iDestruct (own_valid with "H") as "%Hv". exfalso.
    unfold "⋅", cmra_op, ltR, "✓", cmra_valid, alive, lt_op, lt_valid in Hv.
    unfold "⋅", cmra_op, ltR, lt_op in Hv.
    destruct Hv as [b Hv]. destruct b as [[[sa sd]|] a d [g|] gs|].
    - unfold lt_inv in Hv. destruct Hv as [Hsd [Hdisj [Hfm Hcm]]].
      have Hm := Hfm k. destruct Hm as [Hm1 Hm2]. destruct (decide (k ∈ sa)) as [e|e].
      + have Hm := Hm1 e.
        rewrite multiplicity_disj_union in Hm.
        rewrite multiplicity_disj_union in Hm.
        rewrite multiplicity_disj_union in Hm.
        rewrite multiplicity_singleton in Hm. lia.
      + have Hm := Hm2 e.
        rewrite multiplicity_disj_union in Hm.
        rewrite multiplicity_disj_union in Hm.
        rewrite multiplicity_singleton in Hm. lia.
    - unfold lt_inv in Hv. contradiction.
    - unfold lt_inv in Hv. contradiction.
    - unfold lt_inv in Hv. contradiction.
    - unfold lt_inv in Hv. contradiction.
  Qed.

  Lemma kill_lt γlt k sa sd :
    LtState γlt sa sd ∗ Alive γlt k ∗ Alive γlt k ==∗
        LtState γlt (sa ∖ {[ k ]}) (sd ∪ {[ k ]}) ∗ Dead γlt k.
  Proof.
    setoid_rewrite <- own_op. setoid_rewrite <- own_op.
    iIntros "a". iApply own_update. 2: { iFrame "a". } apply update_helper2.

    intros o a d g gs lti. destruct o as [s|], g as [g|].
    - contradiction.
    - contradiction.
    - simpl in lti. destruct lti as [sd_d [no_int [fm cm]]].
      simpl. split. { set_solver. }
      split. { set_solver. }
      split. {
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
      }
      { replace ((∅ ⊎ ∅ ⊎ gs)) with (∅ ⊎ (∅ ⊎ ∅) ⊎ gs) by set_solver.
        apply consistent_modulo_for_kill_lt. trivial.
      }
    - contradiction.
  Qed.

  Lemma bigSepS_alive_equiv_own γlt a
    (ne_emp: a ≠ ∅)
      : ([∗ set] k ∈ a, Alive γlt k) ⊣⊢ own γlt (LtOk None (list_to_set_disj (elements a)) ∅ None ∅).
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
          unfold "⋅", cmra_op, ltR, lt_op. f_equiv.
           * rewrite elements_union_singleton; trivial.
           * set_solver.
           * set_solver.
  Qed.

  Lemma lt_ok_none_left o a1 d1 a2 d2 g gs1 gs2
      : LtOk None a1 d1 None gs1 ⋅ LtOk o a2 d2 g gs2 = LtOk o (a1 ⊎ a2) (d1 ∪ d2) g (gs1 ⊎ gs2).
  Proof.
    destruct o as [o|]; trivial.
  Qed.

  Lemma mult_list_to_set_disj_not_in (a: gset nat) (x: nat)
    (not_in: x ∉ a) : multiplicity x (list_to_set_disj (elements a)) = 0.
  Proof.
  induction a as [|y b ? IH] using set_ind_L. 
  - trivial.
  - rewrite elements_union_singleton; trivial. rewrite list_to_set_disj_cons.
      rewrite multiplicity_disj_union. rewrite IH; last by set_solver.
      assert (x ≠ y) by set_solver. rewrite multiplicity_singleton_ne; trivial.
  Qed.

  Lemma mult_list_to_set_disj_in (a: gset nat) (x: nat)
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

  Lemma multiplicity_le o1 a1 d1 g1 gs1 o2 a2 d2 g2 gs2 x
    : LtOk o1 a1 d1 g1 gs1 ≼ LtOk o2 a2 d2 g2 gs2 → multiplicity x a1 ≤ multiplicity x a2.
  Proof.
    intro incl. destruct incl as [t incl]. destruct t as [o3 a3 d3 g3 gs3|].
    - assert (a2 = a1 ⊎ a3) as X.
        + unfold "⋅", lt_op in incl. destruct o1; destruct o3.
          * destruct g1; inversion incl.
          * destruct g1, g3; inversion incl; trivial.
          * destruct g1, g3; inversion incl; trivial.
          * destruct g1, g3; inversion incl; trivial.
        + subst a2. rewrite multiplicity_disj_union. lia.
    - unfold "⋅", lt_op in incl. destruct o1, g1; inversion incl.
  Qed.

  Lemma own_and_alive γlt (a1 a2 : gset nat)
    : own γlt (LtOk None (list_to_set_disj (elements a1)) ∅ None ∅)
      ∧ own γlt (LtOk None (list_to_set_disj (elements a2)) ∅ None ∅)
      ⊢ own γlt (LtOk None (list_to_set_disj (elements (a1 ∪ a2))) ∅ None ∅).
  Proof.
    iIntros "x".
    iDestruct (and_own_discrete_ucmra_specific with "x") as "y"; last by iFrame "y".
    intros w valw incl1 incl2.
    destruct w as [o a d g gs|].
    - exists (LtOk o (a ∖ (list_to_set_disj (elements (a1 ∪ a2)))) d g gs).
      rewrite lt_ok_none_left. f_equiv.
      + rewrite gmultiset_eq. intros x.
          rewrite multiplicity_disj_union.
          rewrite multiplicity_difference.
          enough ((multiplicity x a ≥ multiplicity x (list_to_set_disj (elements (a1 ∪ a2))))).
          { lia. }
          have t1 := multiplicity_le _ _ _ _ _ _ _ _ _ _ x incl1.
          have t2 := multiplicity_le _ _ _ _ _ _ _ _ _ _ x incl2.
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
      + set_solver.
    - unfold "✓", cmra_valid, ucmra_cmraR, ucmra_valid, ltUR, lt_valid in valw.
      destruct valw as [b valw].
      replace (LtFail ⋅ b) with LtFail in valw. { contradiction. }
      destruct b; trivial.
  Qed.

  Lemma alive_and_bigSepS γlt (a1 a2 : gset nat)
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

  Lemma LtState_entails_Dead γlt k sa sd : (k ∈ sd) → LtState γlt sa sd ⊢ Dead γlt k.
  Proof.
    intros ksd.
    unfold LtState.
    replace (lt_state sa sd) with (lt_state sa sd ⋅ dead k).
    { rewrite own_op. iIntros "[A B]". iFrame "B". }
    unfold dead, lt_state, "⋅", lt_op. f_equal. set_solver.
  Qed.

  Lemma LtState_disjoint γlt sa sd : LtState γlt sa sd ⊢ ⌜ sa ∩ sd = ∅ ⌝.
  Proof.
    iIntros "T". iDestruct (own_valid with "T") as "%val". iPureIntro.
    destruct val as [t lts].
    destruct t as [[o|] a d|].
    - inversion lts.
    - simpl in lts. intuition. destruct o0; intuition.
    - inversion lts.
  Qed.

  Definition CCancel (γ: gname) : iProp Σ := own γ (Excl ()).
  Lemma new_cancel : ⊢ |==> ∃ γ , CCancel γ.
  Proof.
    iIntros. iDestruct (own_alloc (Excl ())) as "H"; first done. unfold CCancel. iFrame "H".
  Qed.
  Lemma cancel_cancel_false (γc : gname) : CCancel γc ∗ CCancel γc ⊢ False.
  Proof.
    iIntros "X". unfold CCancel. rewrite <- own_op.
    iDestruct (own_valid with "X") as "%J". contradiction.
  Qed.

  Lemma not_subset_eq_get (a b : gset nat) : (a ⊈ b) → ∃ k , k ∈ a ∧ k ∉ b.
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
  
  Definition Outlives γo (outlives: outlives_set) : iProp Σ :=
      own γo (to_frac_agree (A:=leibnizO outlives_set) (1/2)%Qp outlives).
      
  Lemma outlives_alloc o :
      ⊢ |==> ∃ γo, Outlives γo o ∗ Outlives γo o.
  Proof.
      unfold Outlives.
      iMod (own_alloc
          (to_frac_agree (A:=leibnizO outlives_set) (1 / 2) o ⋅ to_frac_agree (A:=leibnizO outlives_set) (1 / 2) o)) as (γo) "[Ho Ho2]".
        - rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial.
        - iModIntro. iExists γo. iFrame.
  Qed.
      
  Lemma outlives_agree γo o1 o2 :
      Outlives γo o1 ∗ Outlives γo o2 ⊢ ⌜o1 = o2⌝.
  Proof.
    unfold Outlives. rewrite <- own_op. iIntros "H". iDestruct (own_valid with "H") as "%v".
    iPureIntro. rewrite dfrac_agree_op_valid in v. intuition.
  Qed.
    
  Lemma outlives_update γo o1 o2 o :
      Outlives γo o1 ∗ Outlives γo o2 ==∗ Outlives γo o ∗ Outlives γo o.
  Proof.
    unfold Outlives. rewrite <- own_op. rewrite <- own_op.
    iIntros "H". iDestruct (own_update with "H") as "H"; last by iFrame "H".
    apply frac_agree_update_2. apply Qp.half_half.
  Qed.
  
  Definition Delayed γd (opt_k: option (nat * gset nat)) : iProp Σ :=
      own γd (to_frac_agree (A:=leibnizO (option (nat * gset nat))) (1/2)%Qp opt_k).
  
  Lemma delayed_alloc d :
      ⊢ |==> ∃ γd, Delayed γd d ∗ Delayed γd d.
  Proof.
      unfold Outlives.
      iMod (own_alloc
          (to_frac_agree (A:=leibnizO (option (nat * gset nat))) (1 / 2) d ⋅ to_frac_agree (A:=leibnizO (option (nat * gset nat))) (1 / 2) d)) as (γd) "[Ho Ho2]".
        - rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial.
        - iModIntro. iExists γd. iFrame.
  Qed.
      
  Lemma delayed_agree γd d1 d2 :
      Delayed γd d1 ∗ Delayed γd d2 ⊢ ⌜d1 = d2⌝.
  Proof.
    unfold Delayed. rewrite <- own_op. iIntros "H". iDestruct (own_valid with "H") as "%v".
    iPureIntro. rewrite dfrac_agree_op_valid in v. intuition.
  Qed.
      
  Lemma delayed_update γd (d1 d2 d : option (nat * gset nat)) :
      Delayed γd d1 ∗ Delayed γd d2 ==∗ Delayed γd d ∗ Delayed γd d.
  Proof.
    unfold Delayed. rewrite <- own_op. rewrite <- own_op.
    iIntros "H". iDestruct (own_update with "H") as "H"; last by iFrame "H".
    apply frac_agree_update_2. apply Qp.half_half.
  Qed.
End LlftHelperResources.

