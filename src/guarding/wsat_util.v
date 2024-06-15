From stdpp Require Export coPset.
From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Export wsat.
From iris.prelude Require Import options.
Import uPred.
From iris.algebra Require Import functions.

Require Import guarding.conjunct_own_rule.

Section wsat_util.

Context `{!wsatGS.wsatGS Σ}.
Implicit Types P : iProp Σ.

Lemma own_updateP2 `{i : !inG Σ A} (P : A -> Prop) γ (a: A) :
    a ~~>: P →
    own.iRes_singleton γ a ~~>: (λ y : iResUR Σ, ∃ a' : A, y = own.iRes_singleton γ a' ∧ P a').
Proof.
    intros aP.
    apply (discrete_fun_singleton_updateP _ (λ m, ∃ x,
      m = {[ γ := x ]} ∧ ∃ x', 
      x = own.inG_unfold x' ∧ ∃ a', 
      x' = cmra_transport inG_prf a' ∧ P a')); [|naive_solver].
    apply singleton_updateP', (iso_cmra_updateP' own.inG_fold).
    { apply own.inG_unfold_fold. }
    { apply (cmra_morphism_op _). }
    { apply own.inG_unfold_validN. }
    by apply cmra_transport_updateP'.
Qed.

Lemma valN_transport `{i : !inG Σ A} n (a: A) :
  ✓{n} a →
  ✓{n} cmra_transport inG_prf a.
Proof.
  destruct inG_prf. trivial.
Qed.

          
Lemma alloc_ok1 `{i : !inG Σ A} `{j : !inG Σ B} n (mz : iResUR Σ) γ γ' (a': A) (b: B) :
  (γ' ≠ γ) →
  (mz (inG_id j) !! γ' = None) →
  ✓{n} b →
  ✓{n} (own.iRes_singleton γ a' ⋅? Some mz) →
  ✓{n} (own.iRes_singleton γ a' ⋅ own.iRes_singleton γ' b ⋅? Some mz).
Proof.
  unfold "⋅?". intros ne mznone valb valn.
  rewrite <- cmra_assoc.
  setoid_replace (own.iRes_singleton γ' b ⋅ mz) with 
      (mz ⋅ own.iRes_singleton γ' b) by (apply cmra_comm).
  rewrite cmra_assoc.
  rewrite /own.iRes_singleton.
  unfold validN, cmra_validN. unfold ucmra_cmraR, ucmra_validN, iResUR, discrete_funUR.
  unfold discrete_fun_validN_instance. intros x.
  unfold validN, cmra_validN. unfold ucmra_cmraR, ucmra_validN, iResUR, gmapUR.
  unfold gmap_validN_instance. intros γ2.
  unfold "⋅", cmra_op, ucmra_op, discrete_fun_op_instance.
  rewrite lookup_op.
  
  unfold validN, cmra_validN, ucmra_cmraR, ucmra_validN, iResUR, discrete_funUR,
      discrete_fun_validN_instance,
      validN, cmra_validN, ucmra_cmraR, ucmra_validN, iResUR, gmapUR, gmap_validN_instance
      in valn.
  unfold own.iRes_singleton in valn.
  
  have h : Decision (inG_id j = x) by solve_decision. destruct h as [h1|h1].
   - have h : Decision (γ' = γ2) by solve_decision. destruct h as [h2|h2].
     + have h : Decision (inG_id i = x) by solve_decision. destruct h as [h3|h3].
       * rewrite <- h3.
         rewrite discrete_fun_lookup_singleton.
         rewrite lookup_op.
         rewrite lookup_singleton_ne. 2: { subst γ2. symmetry. trivial. }
         rewrite ucmra_unit_left_id. subst γ2. subst x.
         rewrite h3. rewrite mznone.
         rewrite ucmra_unit_left_id.
         
         rewrite discrete_fun_lookup_singleton.
         rewrite lookup_singleton.
         
         unfold validN, cmra_validN, optionR, option_validN_instance.
         rewrite own.inG_unfold_validN.
         apply valN_transport. trivial.
       * rewrite lookup_op.
         rewrite discrete_fun_lookup_singleton_ne; trivial.
          rewrite lookup_empty. rewrite ucmra_unit_left_id.
          subst γ2. subst x. rewrite mznone.
         rewrite ucmra_unit_left_id.
          rewrite discrete_fun_lookup_singleton.
          rewrite lookup_singleton.

          unfold validN, cmra_validN, optionR, option_validN_instance.
          rewrite own.inG_unfold_validN.
          apply valN_transport. trivial.
    + rewrite <- h1.
      rewrite discrete_fun_lookup_singleton.
      rewrite lookup_singleton_ne; trivial.
      rewrite ucmra_unit_right_id.
      apply valn.
  - rewrite cmra_comm.
    rewrite discrete_fun_lookup_singleton_ne; trivial.
    rewrite lookup_empty.
    rewrite ucmra_unit_left_id.
    apply valn.
Qed.
   
Lemma alloc_ok2 `{i : !inG Σ A} `{j : !inG Σ B} n γ γ' (a': A) (b: B) :
  (γ' ≠ γ) →
  ✓{n} b →
  ✓{n} (own.iRes_singleton γ a' ⋅? None) →
  ✓{n} (own.iRes_singleton γ a' ⋅ own.iRes_singleton γ' b ⋅? None).
Proof.
  unfold "⋅?". intros ne valb valn.
  rewrite /own.iRes_singleton.
  unfold validN, cmra_validN. unfold ucmra_cmraR, ucmra_validN, iResUR, discrete_funUR.
  unfold discrete_fun_validN_instance. intros x.
  unfold validN, cmra_validN. unfold ucmra_cmraR, ucmra_validN, iResUR, gmapUR.
  unfold gmap_validN_instance. intros γ2.
  unfold "⋅", cmra_op, ucmra_op, discrete_fun_op_instance.
  rewrite lookup_op.
  
  unfold validN, cmra_validN, ucmra_cmraR, ucmra_validN, iResUR, discrete_funUR,
      discrete_fun_validN_instance,
      validN, cmra_validN, ucmra_cmraR, ucmra_validN, iResUR, gmapUR, gmap_validN_instance
      in valn.
  unfold own.iRes_singleton in valn.
  
  have h : Decision (inG_id j = x) by solve_decision. destruct h as [h1|h1].
   - have h : Decision (γ' = γ2) by solve_decision. destruct h as [h2|h2].
     + have h : Decision (inG_id i = x) by solve_decision. destruct h as [h3|h3].
       * rewrite <- h3.
         rewrite discrete_fun_lookup_singleton.
         rewrite lookup_singleton_ne. 2: { subst γ2. symmetry. trivial. }
         rewrite ucmra_unit_left_id.
         
         subst x. rewrite h3.
         rewrite discrete_fun_lookup_singleton.
         subst γ2. rewrite lookup_singleton.
         
         unfold validN, cmra_validN, optionR, option_validN_instance.
         rewrite own.inG_unfold_validN.
         apply valN_transport. trivial.
       * rewrite discrete_fun_lookup_singleton_ne; trivial.
          rewrite lookup_empty. rewrite ucmra_unit_left_id.
          rewrite <- h1.
          rewrite discrete_fun_lookup_singleton.
          subst γ2. rewrite lookup_singleton.
          
          unfold validN, cmra_validN, optionR, option_validN_instance.
          rewrite own.inG_unfold_validN.
          apply valN_transport. trivial.
    + rewrite <- h1.
      rewrite discrete_fun_lookup_singleton.
      rewrite lookup_singleton_ne; trivial.
      rewrite ucmra_unit_right_id.
      apply valn.
  - rewrite cmra_comm.
    rewrite discrete_fun_lookup_singleton_ne; trivial.
    rewrite lookup_empty.
    rewrite ucmra_unit_left_id.
    apply valn.
Qed.
          
Lemma updates_inf_1 `{i : !inG Σ A} `{j : !inG Σ B} (mz : iResUR Σ) (P : A → gname → Prop) γ (a: A) :
  (∀ (n : nat) (mz : option A) (N : gname → Prop),
           ✓{n} (a ⋅? mz)
           → pred_finite N → ∃ (y : A) (γ' : gname), P y γ' ∧ ✓{n} (y ⋅? mz) ∧ ¬ N γ') →
  a ~~>: (λ a0 : A, ∃ γ' : gname, P a0 γ' ∧ mz (inG_id j) !! γ' = None ∧ γ' ≠ γ).
Proof.
  unfold "~~>:". intros Hx n mz0 valn.
  assert (pred_finite (λ γ' : gname, mz (inG_id j) !! γ' ≠ None ∨ γ' = γ)) as X.
  {
    assert (set_finite (dom (mz (inG_id j) : gmap _ _))) as X. { apply dom_finite. }
    unfold set_finite, pred_finite in X. destruct X as [xs X].
    unfold pred_finite.
    exists (γ :: xs).
    intros x cond.
    destruct cond as [cond|cond].
    - rewrite elem_of_cons. right. apply X.
      rewrite elem_of_dom.
      destruct (mz (inG_id j) !! x) eqn:ee.
      + rewrite ee. trivial.
      + contradiction.
    - rewrite elem_of_cons. left. trivial.
  }
  have t := Hx n mz0 (λ γ', mz (inG_id j) !! γ' ≠ None ∨ γ' = γ) valn X.
  destruct t as [y [γ' [t [u v]]]].
  exists y. split; trivial. exists γ'. split; trivial.
  split.
  + destruct (mz (inG_id j) !! γ') eqn:ee.
    - exfalso. apply v. left. intro. discriminate.
    - trivial.
  + intuition.
Qed.

Lemma updates_inf_2 `{i : !inG Σ A} (P : A → gname → Prop) γ (a: A) :
  (∀ (n : nat) (mz : option A) (N : gname → Prop),
           ✓{n} (a ⋅? mz)
           → pred_finite N → ∃ (y : A) (γ' : gname), P y γ' ∧ ✓{n} (y ⋅? mz) ∧ ¬ N γ') →
  a ~~>: (λ a0 : A, ∃ γ' : gname, P a0 γ' ∧ γ' ≠ γ).
Proof.
  unfold "~~>:". intros Hx n mz valn.
  assert (pred_finite (λ γ' : gname, γ' = γ)) as X.
  {
    unfold pred_finite. exists (γ :: nil).
    intros x. intro eq. subst x. rewrite elem_of_cons. left; trivial.
  }
  have t := Hx n mz (λ γ', γ' = γ) valn X.
  destruct t as [y [γ' [t [u v]]]].
  exists y. split; trivial. exists γ'. split; trivial.
Qed.

Lemma own_updateP_extra `{i : !inG Σ A} `{j : !inG Σ B} (P : A → gname → Prop) γ (a : A) (b : B) :
    (∀ (n : nat) (mz : option A) (N : gname → Prop) , ✓{n} (a ⋅? mz) → pred_finite N → ∃ (y: A) (γ': gname), P y γ' ∧ ✓{n} (y ⋅? mz) ∧ ¬ N γ') →
    (✓ b) →
    own γ a ⊢ |==> ∃ a' γ', ⌜P a' γ'⌝ ∗ own γ a' ∗ own γ' b.
Proof using H Σ.
  intros Hupd Hvalb. rewrite !own.own_eq.
  rewrite -(bupd_mono (∃ m,
    ⌜ ∃ a' γ', m = (own.iRes_singleton γ a' ⋅ own.iRes_singleton γ' b) ∧ P a' γ' ⌝ ∧ uPred_ownM m)%I).
  - apply bupd_ownM_updateP. unfold "~~>:". intros n mz Hvaln.
    destruct mz as [mz|].
      + enough (a ~~>: (λ a : A, ∃ γ' : gname, P a γ' ∧ mz (inG_id j) !! γ' = None ∧ γ' ≠ γ)) as X.
        {
          have t := @own_updateP2 A i (λ a, ∃ γ', P a γ' ∧ mz (inG_id j) !! γ' = None ∧ γ' ≠ γ) γ a X.
          unfold "~~>:" in t.
          have s := t n (Some mz) Hvaln.
          destruct s as [y [[a' [oa [γ' [s [mzn ne]]]]] q]].
          exists (y ⋅ own.iRes_singleton γ' b). split.
          { exists a'. exists γ'. rewrite oa. split; trivial. }
          rewrite oa. rewrite oa in q. apply alloc_ok1; trivial.
          apply cmra_valid_validN. trivial.
        }
        {
          apply updates_inf_1; trivial.
        }
      + enough (a ~~>: (λ a : A, ∃ γ' : gname, P a γ' ∧ γ' ≠ γ)) as X.
        {
          have t := @own_updateP2 A i (λ a, ∃ γ', P a γ' ∧ γ' ≠ γ) γ a X.
          unfold "~~>:" in t.
          have s := t n None Hvaln.
          destruct s as [y [[a' [oa [γ' [s ne]]]] q]].
          exists (y ⋅ own.iRes_singleton γ' b). split.
          { exists a'. exists γ'. rewrite oa. split; trivial. }
          rewrite oa. rewrite oa in q. apply alloc_ok2; trivial.
          apply cmra_valid_validN. trivial.
        }
        {
          apply updates_inf_2; trivial.
        }
   - apply exist_elim=> m.
      iIntros "[%s t]".
      destruct s as [a' [γ' [s p]]].
      iExists a'. iExists γ'. rewrite s.
      iSplit. { iPureIntro. trivial. }
      unfold own.own_def.
      rewrite ownM_op. iFrame.
Qed.

Lemma ownI_alloc φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P.
Proof. 
  iIntros (Hfresh) "[Hw HP]". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) wsat.wsatGS.disabled_name) as "HE".
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_and_simultaneous_own_alloc_ns (P : positive -> iProp Σ) `{ing : !inG Σ A} (a:A) (from: coPset) (inf: set_infinite from) :
  (✓ a) ->
  wsat ==∗ ∃ i, ⌜ i ∈ from ⌝ ∗ (▷ P i -∗ wsat) ∗ ownI i (P i) ∗ own i a.
Proof.
  intro valid_a.
  iIntros "Hw". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw HI]".
  
  iMod (own_unit (gset_disjUR positive) wsat.wsatGS.disabled_name) as "HE".
  
  iMod (own_updateP_extra (λ a i, (a = GSet {[i]}) ∧ I !! i = None ∧ i ∈ from) wsat.wsatGS.disabled_name ε a  with "[$]") as "HE".
  {
    intros n mz N val_mz finiteN.
    assert (set_finite (dom I)) as sFin. { apply dom_finite. }
    unfold pred_finite in finiteN. destruct finiteN as [xs finiteN].
    unfold set_infinite, pred_infinite in inf.
    unfold set_finite, pred_finite in sFin.
    destruct sFin as [xs2 sFin].
    
    destruct mz as [mz|].
    + destruct mz as [mz|].
      * assert (set_finite mz) as mzFin. { apply fin_set_finite. }
        unfold set_finite, pred_finite in mzFin.
        destruct mzFin as [xs3 mzFin].
    
        have inf2 := inf (xs ++ xs2 ++ xs3). destruct inf2 as [x [x_in_from x_not_in_xs]].
        rewrite not_elem_of_app in x_not_in_xs.
        rewrite not_elem_of_app in x_not_in_xs.
        destruct x_not_in_xs as [x_not_in_xs [x_not_in_xs2 x_not_in_xs3]].
        exists (GSet {[x]}).
        exists x. split; trivial.
        - split; trivial. split; trivial.
          rewrite <- not_elem_of_dom. intro x_in_dom. apply x_not_in_xs2. apply sFin. trivial.
        - split; trivial.
          ++ unfold "⋅?".  generalize n. rewrite <- cmra_valid_validN.
              rewrite gset_disj_valid_op. rewrite disjoint_singleton_l.
              intro xmz. apply x_not_in_xs3. apply mzFin. trivial.
          ++ intro Nx. apply x_not_in_xs. apply finiteN. trivial.
     * unfold "⋅?" in val_mz. rewrite ucmra_unit_left_id in val_mz.
        unfold validN, cmra_validN, gset_disjR, discrete_validN_instance, valid, gset_disj_valid_instance in val_mz. contradiction.
    + have inf2 := inf (xs ++ xs2). destruct inf2 as [x [x_in_from x_not_in_xs]].
        rewrite not_elem_of_app in x_not_in_xs.
        destruct x_not_in_xs as [x_not_in_xs x_not_in_xs2].
        exists (GSet {[x]}).
        exists x. split; trivial.
        - split; trivial. split; trivial.
          rewrite <- not_elem_of_dom. intro x_in_dom. apply x_not_in_xs2. apply sFin. trivial.
        - split; trivial.
          intro Nx. apply x_not_in_xs. apply finiteN. trivial.
  }
  { trivial. }
  
  iDestruct "HE" as (X i) "[[%Xi [%HIi %gfrom]] [Hi HE]]".
  
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  iFrame.
  iIntros "latP".
  iExists (<[i:=P i]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iLeft. iFrame. rewrite /ownD. rewrite Xi. iFrame.
Qed.

End wsat_util.
