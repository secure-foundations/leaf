From iris.prelude Require Import options.
Require Import cpdt.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.trees.
Require Import Burrow.locations.
Require Import Burrow.indexing.
Require Import Burrow.gmap_utils.

From stdpp Require Import countable.
From stdpp Require Import gmap.

Section Updog.

Lemma app_nonempty {T} (p: list T) (i: T)
  : p ++ [i] ≠ [].
Proof.
  intro. assert (length (p ++ [i]) = length []) by (f_equal; trivial).
  rewrite app_length in H0. simpl in H0. lia.
Qed.

Context {M} `{!EqDecision M} `{!TPCM M}.
Context {RI} `{!EqDecision RI, !Countable RI, !RefinementIndex M RI}.

Definition updo (m: M) (gamma: Loc RI) (idx: nat) : (PathLoc -> M) :=
  λ (pl: PathLoc) , match pl with | (p, i) =>
        if decide (p ≠ [] /\ (plsplit p) ∈ pls_of_loc gamma /\ i ≤ idx) then
          m
        else
          unit
      end.
 
Definition updo_se (gamma: Loc RI) (idx: nat) : gset PathLoc :=
  set_set_map (pls_of_loc gamma) (λ pl: PathLoc , match pl with (p, i) =>
    set_map (λ j: nat, (p ++ [i], j)) (set_seq 0 (idx+1) : gset nat)
  end).

Lemma updo_se_okay (m: M) (gamma: Loc RI) (idx: nat)
  : ∀ (p : list nat) (i : nat),
    (p, i) ∉ updo_se gamma idx
    → updo m gamma idx (p, i) = unit.
Proof.
  intros. unfold updo. case_decide; trivial. exfalso. destruct_ands.
  apply H. unfold updo_se. apply lookup_set_set_map. exists (plsplit p). split; trivial.
  destruct (plsplit p) eqn:psp.
  rewrite elem_of_map. exists i. split.
  - f_equal.
    unfold plsplit in psp. inversion psp.
    apply app_removelast_last. trivial.
  - rewrite elem_of_set_seq. lia.
Qed.

Definition updog (m: M) (gamma: Loc RI) (alpha: nat) (ri: RI) : (PathLoc -> M) :=
  updo m gamma (nat_of_extstep alpha ri).
      
Definition updog_se (gamma: Loc RI) (alpha: nat) (ri: RI) : gset PathLoc :=
  updo_se gamma (nat_of_extstep alpha ri).

Lemma updog_se_okay (m: M) (gamma: Loc RI) (alpha: nat) (ri: RI)
  : ∀ (p : list nat) (i : nat),
    (p, i) ∉ updog_se gamma alpha ri
    → updog m gamma alpha ri (p, i) = unit.
Proof. unfold updog, updog_se. apply updo_se_okay. Qed.
    
Lemma updog_eq_m p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, i)) = m.
Proof. unfold updog, updo. case_decide; trivial. exfalso. apply H.
  have j := resolve_p_i_in_ExtLoc _ _ _ _ _ is_in. destruct_ands. repeat split; trivial.
  lia.
Qed.
    
Lemma updog_eq_unit1 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, S i)) = unit.
Proof.
  unfold updog, updo. case_decide; trivial. exfalso.
  have j := resolve_p_i_in_ExtLoc _ _ _ _ _ is_in. destruct_ands. subst i.
  lia.
Qed.
    
Lemma updog_eq_unit2 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p ++ [i], 0)) = unit.
Proof.
  unfold updog, updo. case_decide; trivial. exfalso.
  have j := resolve_p_i_in_ExtLoc _ _ _ _ _ is_in. destruct_ands.
  eapply plsplit_app_and_self_contra.
  - apply H3. - apply H0. - apply H1.
Qed.

(*Lemma updog_base_eq_unit1 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p, i)) = unit.
    
Lemma updog_base_eq_unit2 p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p, S i)) = unit.*)
    
Lemma updog_base_eq_m p i alpha ri gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updog m gamma alpha ri (p ++ [i], 0)) = m.
Proof.
  unfold updog, updo. case_decide; trivial. exfalso. apply H. repeat split.
  - apply app_nonempty.
  - rewrite plsplit_app. trivial.
  - lia.
Qed.
    
Lemma updog_other_eq_both p i alpha ri gamma m
  (is_not_in : (p, i) ∉ pls_of_loc (ExtLoc alpha ri gamma))
    : (updog m gamma alpha ri (p, i)) = (updog m gamma alpha ri (p, S i)).
Proof.
  unfold updog, updo. case_decide; case_decide; trivial.
  - destruct_ands. exfalso. apply H0. repeat split; trivial.
    enough (i ≠ nat_of_extstep alpha ri) by lia.
    intro. apply is_not_in. apply resolve_p_i_in_ExtLoc_rev; trivial.
  - destruct_ands. exfalso. apply H. repeat split; trivial.
    enough (i ≠ nat_of_extstep alpha ri) by lia.
    intro. apply is_not_in. apply resolve_p_i_in_ExtLoc_rev; trivial.
Qed.
    
Lemma updog_other_eq_unit p i alpha ri gamma m
  (is_not_in : (p, i) ∉ pls_of_loc gamma)
    : (updog m gamma alpha ri (p ++ [i], 0)) = unit.
Proof.
  unfold updog, updo. case_decide; trivial. destruct_ands.
  rewrite plsplit_app in H0. contradiction.
Qed.

  
Lemma updo_eq_m_left p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p, i)) = m. 
Proof.
  unfold updo. case_decide; trivial. exfalso. apply H.
  have j := resolve_p_i_in_Left _ _ _ _ is_in. destruct_ands. repeat split; trivial. lia.
Qed.
    
Lemma updo_eq_unit_left p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p++[i], 0)) = unit.
Proof.
  unfold updo. case_decide; trivial. exfalso. destruct_ands.
  have j := resolve_p_i_in_Left _ _ _ _ is_in. destruct_ands. subst i.
  eapply plsplit_app_and_self_contra.
  - apply H0. - apply H2. - trivial.
Qed.
    
Lemma updo_eq_unit2_left p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p, S i)) = unit.
Proof.
  unfold updo. case_decide; trivial. exfalso. destruct_ands.
  have j := resolve_p_i_in_Left _ _ _ _ is_in. lia.
Qed.

Lemma updo_eq_unit3_left (p: list nat) i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma1 (nat_of_leftstep RI gamma2) (p++[i], 0)) = unit.
Proof.
  unfold updo. case_decide; trivial. exfalso. destruct_ands.
  have j := resolve_p_i_in_Right _ _ _ _ is_in. destruct_ands. subst i.
  eapply plsplit_app_right_contra. apply H0.
Qed.

Lemma updo_eq_m_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p, i)) = m.
Proof.
  unfold updo. case_decide; trivial. exfalso. apply H.
  have j := resolve_p_i_in_Right _ _ _ _ is_in. destruct_ands. repeat split; trivial. lia.
Qed.

Lemma updo_eq_unit_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p++[i], 0)) = unit.
Proof.
  unfold updo. case_decide; trivial. exfalso. destruct_ands.
  have j := resolve_p_i_in_Right _ _ _ _ is_in. destruct_ands. subst i.
  eapply plsplit_app_and_self_contra.
  - apply H0. - apply H2. - trivial.
Qed.
    
Lemma updo_eq_unit2_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_right gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p, S i)) = unit.
Proof.
  unfold updo. case_decide; trivial. exfalso. destruct_ands.
  have j := resolve_p_i_in_Right _ _ _ _ is_in. lia.
Qed.
    
Lemma updo_eq_unit3_right p i gamma1 gamma2 m
  (is_in : (p, i) ∈ pls_of_loc_from_left gamma1 gamma2)
    : (updo m gamma2 (nat_of_rightstep RI gamma1) (p++[i], 0)) = unit.
Proof.
  unfold updo. case_decide; trivial. exfalso. destruct_ands.
  have j := resolve_p_i_in_Left _ _ _ _ is_in. destruct_ands. subst i.
  eapply plsplit_app_left_contra. apply H0.
Qed.

Lemma updo_other_eq_both_left p i gamma1 gamma2 m
  (is_not_in : (p, i) ∉ pls_of_loc_from_left gamma1 gamma2)
  : (updo m gamma1 (nat_of_leftstep RI gamma2) (p, i)) = (updo m gamma1 (nat_of_leftstep RI gamma2) (p, S i)).
Proof.
  unfold updo. case_decide; case_decide; trivial.
  - destruct_ands. exfalso. apply H0. repeat split; trivial.
    enough (i ≠ nat_of_leftstep RI gamma2) by lia.
    intro. apply is_not_in. apply resolve_p_i_in_Left_rev; trivial.
  - destruct_ands. exfalso. apply H. repeat split; trivial.
    enough (i ≠ nat_of_leftstep RI gamma2) by lia.
    intro. apply is_not_in. apply resolve_p_i_in_Left_rev; trivial.
Qed.
  
Lemma updo_other_eq_both_right p i gamma1 gamma2 m
  (is_not_in : (p, i) ∉ pls_of_loc_from_right gamma1 gamma2)
  : (updo m gamma2 (nat_of_rightstep RI gamma1) (p, i)) = (updo m gamma2 (nat_of_rightstep RI gamma1) (p, S i)).
Proof.
  unfold updo. case_decide; case_decide; trivial.
  - destruct_ands. exfalso. apply H0. repeat split; trivial.
    enough (i ≠ nat_of_rightstep RI gamma1) by lia.
    intro. apply is_not_in. apply resolve_p_i_in_Right_rev; trivial.
  - destruct_ands. exfalso. apply H. repeat split; trivial.
    enough (i ≠ nat_of_rightstep RI gamma1) by lia.
    intro. apply is_not_in. apply resolve_p_i_in_Right_rev; trivial.
Qed.
  
Lemma updo_other_eq_unit p i idx gamma m
  (is_not_in : (p, i) ∉ pls_of_loc gamma)
    : (updo m gamma idx (p ++ [i], 0)) = unit.
Proof.
  unfold updo. case_decide; trivial. destruct_ands.
  rewrite plsplit_app in H0. contradiction.
Qed.
  
Lemma updo_base_eq_m p i idx gamma m
  (is_in : (p, i) ∈ pls_of_loc gamma)
    : (updo m gamma idx (p ++ [i], 0)) = m.
Proof.
  unfold updo. case_decide; trivial. exfalso. apply H. repeat split.
  - apply app_nonempty.
  - rewrite plsplit_app. trivial.
  - lia.
Qed.

End Updog.
