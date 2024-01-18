From stdpp Require Export coPset.
From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Export wsat.
From iris.prelude Require Import options.

Section wsat_util.

Context `{!wsatGS.wsatGS Σ}.
Implicit Types P : iProp Σ.

Lemma ownI_alloc_and_simultaneous_own_alloc (P : positive -> iProp Σ) `{ing : !inG Σ A} (a: A) :
  (✓ a) ->
  wsat ==∗ ∃ i, (▷ P i -∗ wsat) ∗ ownI i (P i) ∗ own i a.
Proof.
  intro valid_a.
  iIntros "Hw". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  
  iMod (own_alloc_cofinite a (dom I)) as "ow". { trivial. }
  iDestruct "ow" as (i) "[%ni ow]".
  
  assert (I !! i = None) as HIi by (apply not_in_dom_to_none; trivial).
  
  assert (i ∈ (⊤ ∖ gset_to_coPset (dom I))) as in_comp. { apply not_in_dom. trivial. }
  have du := diff_union _ _ in_comp.
  rewrite du.
  
  iDestruct (ownD_op with "Hd") as "[Hd HE]". { set_solver. }
  
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  
  iModIntro. iExists i.
  
  rewrite /ownI.
  iDestruct (bi.persistent_sep_dup with "HiP") as "[HiP HiP2]".
  iFrame "HiP". iFrame "ow".
  iIntros "laterp".
  iExists (<[i:=P i]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  
  rewrite diff_domm_inserted. iFrame "Hd".
  
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iFrame "HiP2". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_and_simultaneous_own_alloc_ns (P : positive -> iProp Σ) `{ing : !inG Σ A} (a:A) (from: coPset) (inf: ¬set_finite from) :
  (✓ a) ->
  wsat ==∗ ∃ i, ⌜ i ∈ from ⌝ ∗ (▷ P i -∗ wsat) ∗ ownI i (P i) ∗ own i a.
Proof.
  intro valid_a.
  iIntros "Hw". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  
  iMod (own_alloc_strong a (λ i , i ∉ dom I ∧ i ∈ from)) as "ow".
  {
    unfold pred_infinite.
    intro xs.
    assert (set_infinite (from ∖ (gset_to_coPset (dom I)) ∖ list_to_set xs)) as infi.
    - apply difference_infinite.
      + apply difference_infinite.
        * rewrite coPset_infinite_finite. trivial.
        * apply gset_to_coPset_finite.
      + apply list_to_set_finite.
    - exists (coPpick (from ∖ (gset_to_coPset (dom I)) ∖ list_to_set xs)).
      assert (
          (coPpick (from ∖ (gset_to_coPset (dom I)) ∖ list_to_set xs))
          ∈
          (from ∖ gset_to_coPset (dom I) ∖ list_to_set xs)
      ) as IN. { apply coPpick_elem_of. rewrite <- coPset_infinite_finite. trivial. }
      generalize IN.
      rewrite elem_of_difference.
      rewrite elem_of_difference.
      rewrite elem_of_list_to_set.
      rewrite elem_of_gset_to_coPset.
      rewrite elem_of_dom.
      intuition.
  }
  { trivial. }
  
  iDestruct "ow" as (i) "[%ni ow]".
  destruct ni as [ni in_from].
  
  assert (I !! i = None) as HIi by (apply not_in_dom_to_none; trivial).
  
  assert (i ∈ (⊤ ∖ gset_to_coPset (dom I))) as in_comp. { apply not_in_dom. trivial. }
  have du := diff_union _ _ in_comp.
  rewrite du.
  
  iDestruct (ownD_op with "Hd") as "[Hd HE]". { set_solver. }
  
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  
  iModIntro. iExists i.
  
  rewrite /ownI.
  iDestruct (bi.persistent_sep_dup with "HiP") as "[HiP HiP2]".
  iFrame "HiP". iFrame "ow".
  iSplitL "". { iPureIntro. trivial. }
  iIntros "laterp".
  iExists (<[i:=P i]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  
  rewrite diff_domm_inserted. iFrame "Hd".
  
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iFrame "HiP2". iLeft. by rewrite /ownD; iFrame.
Qed. 

(*
Lemma ownI_alloc_open_and_simultaneous_own_alloc (P : positive -> iProp Σ) `{ing : !inG Σ A} (a: A) :
  (✓ a) ->
  wsat ==∗ ∃ i, (ownE {[i]} -∗ wsat) ∗ ownI i (P i) ∗ ownD {[i]} ∗ own i a.
Proof.
  iIntros (valid_a) "Hw". rewrite /wsat -!lock. iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  
  iMod (own_alloc_cofinite a (dom _ I)) as "ow". { trivial. }
  iDestruct "ow" as (i) "[%ni ow]".
  
  (*have is_f := Hfresh (@dom _ (gset positive) (gset_dom) I).
  destruct is_f as [i [ni phi]].*)
  assert (I !! i = None) as HIi by (apply not_in_dom_to_none; trivial).
  assert (i ∈ (⊤ ∖ gmap_dom_coPset I)) as in_comp. { apply not_in_dom. trivial. }
  have du := diff_union _ _ in_comp.
  rewrite du.
  iDestruct (ownD_op with "Hd") as "[Hd HD]". { set_solver. }
  
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro. iExists i.
  iDestruct (bi.persistent_sep_dup with "HiP") as "[HiP HiP2]".
  rewrite /ownI; iFrame "HiP".
  rewrite -/(ownD _). iFrame "HD". iFrame "ow".
  iIntros "HE". iExists (<[i:=P i]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  
  rewrite diff_domm_inserted. iFrame "Hd".
  
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iFrame "HiP2". by iRight.
Qed.
*)

Lemma ownI_alloc_open_or_alloc i :
  ⊢ wsat ∗ ownE {[i]} ==∗ ∃ P , wsat ∗ ownD {[i]} ∗ ownI i P ∗ ▷ P.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & HiE)". iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  destruct (I !! i) eqn:HIi.
  + (* case 1: invariant exists; open it *)
    iDestruct (big_sepM_delete _ _ i with "HI") as "[[Ho [[HQ $]|HiE']] HI]"; eauto.
    - iExists u. iFrame "HQ". rewrite /ownI.
      iDestruct (bi.persistent_sep_dup with "Ho") as "[Ho1 Ho2]".
      iFrame "Ho1".
      iExists I. iFrame "Hw". iFrame "Hd". iApply (big_sepM_delete _ _ i); eauto.
      iFrame "HI"; eauto.
    - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
  + (* case 2: invariant doesn't exist; alloc a new one *)
    iExists ((True)%I : iProp Σ).
    assert (i ∈ (⊤ ∖ gset_to_coPset (dom I))) as in_comp. { apply not_in_dom. trivial. }

    have du := diff_union _ _ in_comp.
    rewrite du.
    iDestruct (ownD_op with "Hd") as "[Hd HD]". { set_solver. }

    iMod (own_update with "Hw") as "[Hw HiP]".
    { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
      by rewrite /= lookup_fmap HIi. }
    iModIntro.
    iFrame "HD".
      iDestruct (bi.persistent_sep_dup with "HiP") as "[HiP1 HiP2]".
    iFrame "HiP1".
    
    iSplitL.
    * iExists (<[i:= ((True)%I : iProp Σ)]>I); iSplitL "Hw".
      { by rewrite fmap_insert. }
      rewrite diff_domm_inserted. iFrame "Hd".

      iApply (big_sepM_insert _ I); first done.
      iFrame "HI". rewrite /ownI. iFrame "HiP2". by iRight.
    * iModIntro. done.
Qed.

End wsat_util.
