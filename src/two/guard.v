From iris.algebra Require Export cmra.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.base_logic.lib Require Export wsat invariants.

From iris.algebra Require Import auth.

From iris.proofmode Require Export tactics.

Section Guard.

Context {Σ: gFunctors}.
Context `{!invGS Σ}. 

Definition storage_inv (i: positive) : iProp Σ := ∃ P , ownI i P ∗ ▷ P.

Definition storage_bulk_inv (m: gset positive) : iProp Σ :=
    [∗ map] i ↦ unused ∈ gset_to_gmap () m, storage_inv i.
    
Lemma storage_bulk_inv_empty :
  True ⊢ storage_bulk_inv ∅.
Proof.
  unfold storage_bulk_inv.
  replace (gset_to_gmap () ∅ : gmap positive ()) with (∅ : gmap positive ()).
  - rewrite big_sepM_empty. trivial.
  - apply map_eq. intros. rewrite lookup_empty. rewrite lookup_gset_to_gmap. trivial.
Qed.

Lemma storage_bulk_inv_singleton i
  : storage_bulk_inv ({[i]}) ⊣⊢ storage_inv i.
Proof.
  unfold storage_bulk_inv.
  replace (gset_to_gmap () {[i]}) with ( {[ i := () ]} : gmap positive () ).
  - apply big_sepM_singleton.
  - apply map_eq. intros.
      have h : Decision (i = i0) by solve_decision. destruct h.
      + subst i0. rewrite lookup_singleton.
        rewrite lookup_gset_to_gmap. unfold mguard, option_guard.
            destruct (decide_rel elem_of i {[i]}); trivial.
            generalize n. rewrite elem_of_singleton. contradiction.
      + rewrite lookup_singleton_ne; trivial.
        rewrite lookup_gset_to_gmap. unfold mguard, option_guard.
            destruct (decide_rel elem_of i0 {[i]}); trivial.
            generalize e. rewrite elem_of_singleton. intros. subst i. contradiction.
Qed.

Lemma gset_to_gmap_union (E F : gset positive)
  : gset_to_gmap () (E ∪ F) = gset_to_gmap () E ∪ gset_to_gmap () F.
  Proof.
  apply map_eq. intros. rewrite lookup_union.
    rewrite lookup_gset_to_gmap.
    rewrite lookup_gset_to_gmap.
    rewrite lookup_gset_to_gmap.
    unfold union_with, option_union_with, mguard, option_guard.
    destruct (decide_rel elem_of i E);
    destruct (decide_rel elem_of i F);
    destruct (decide_rel elem_of i (E ∪ F)); trivial; set_solver.
Qed.
  
Lemma gset_to_gmap_disj (E F : gset positive) (disj : E ## F)
  : gset_to_gmap () E ##ₘ gset_to_gmap () F.
Proof.
  unfold "##ₘ", map_relation. intros.  unfold option_relation.
    destruct (gset_to_gmap () E !! i) eqn:x;
    destruct (gset_to_gmap () F !! i) eqn:y; trivial.
    rewrite lookup_gset_to_gmap in x.
    rewrite lookup_gset_to_gmap in y.
    unfold mguard, option_guard in x, y.
    destruct (decide_rel elem_of i E); destruct (decide_rel elem_of i F); try discriminate.
    set_solver.
Qed.

Lemma storage_bulk_inv_union (E F : gset positive) (disj: E ## F) :
  storage_bulk_inv (E ∪ F) ⊣⊢ storage_bulk_inv E ∗ storage_bulk_inv F.
Proof.
  unfold storage_bulk_inv. rewrite gset_to_gmap_union.
  apply big_sepM_union. apply gset_to_gmap_disj. trivial.
Qed.

Lemma storage_bulk_inv_singleton_union i X
  (not_in : i ∉ X)
  : storage_bulk_inv ({[i]} ∪ X) ⊣⊢ storage_inv i ∗ storage_bulk_inv X.
Proof.
  rewrite storage_bulk_inv_union.
  - rewrite storage_bulk_inv_singleton. trivial.
  - set_solver.
Qed.

Definition guards_with (P Q X : iProp Σ) :=
    (∀ (T: iProp Σ), (P ∗ (P -∗ X ∗ T) ={∅}=∗ Q ∗ (Q -∗ X ∗ T))) % I.

Definition fguards (P Q : iProp Σ) (m: gset positive) : iProp Σ :=
    guards_with P Q (storage_bulk_inv m).
    
Notation "P &&{ E }&&$> Q" := (fguards P Q E)
  (at level 99, E at level 50, Q at level 200).
  
Lemma fguards_refl E P : ⊢ P &&{ E }&&$> P.
Proof.
  unfold fguards, guards_with. iIntros (T) "x". iModIntro. iFrame.
Qed.

Lemma fguards_transitive E P Q R :
    (P &&{ E }&&$> Q) ∗ (Q &&{ E }&&$> R) ⊢ (P &&{E}&&$> R).
Proof.
  unfold fguards, guards_with.
  iIntros "[a b]". iIntros (T) "p".
  iMod ("a" with "p") as "q".
  iMod ("b" with "q") as "r".
  iModIntro. iFrame.
Qed.
  
Lemma twoway_assoc (P Q R : iProp Σ)
  : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R).
Proof. iIntros. iSplit. { iIntros "[[p q] r]". iFrame. }
    { iIntros "[p [q r]]". iFrame. } Qed.

Lemma fguards_superset E F P Q (disj: E ## F) :
    (P &&{ E }&&$> Q) ⊢ (P &&{ E ∪ F }&&$> Q).
Proof.
  unfold fguards, guards_with.
  iIntros "a".
  iIntros (T).
  rewrite storage_bulk_inv_union; trivial.
  assert ((storage_bulk_inv E ∗ storage_bulk_inv F) ∗ T
      ⊣⊢ storage_bulk_inv E ∗ (storage_bulk_inv F ∗ T)) as asso by apply twoway_assoc.
    rewrite asso.
    iApply "a".
Qed.

Lemma fguards_weaken E P Q : ⊢ (P ∗ Q) &&{ E }&&$> P.
Proof.
  unfold fguards, guards_with. iIntros (T) "[[p q] x]". iModIntro.
  iFrame. iIntros "p".
  iDestruct ("x" with "[p q]") as "m". { iFrame. }
  iFrame.
Qed.

Lemma copset_diff_union (E E': gset positive) (su: E ⊆ E') : E' = (E ∪ (E' ∖ E)).
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E) by solve_decision. destruct h; set_solver.
Qed.

Lemma fguards_mask_weaken (P Q: iProp Σ) E E'
    (su: E ⊆ E')
    : (P &&{ E }&&$> Q) ⊢ (P &&{ E' }&&$> Q).
Proof.
  unfold fguards, guards_with.
  iIntros "x".
  iIntros (T) "[p q]".
  rewrite (copset_diff_union E E'); trivial.
  iDestruct ("x" $! (T ∗ storage_bulk_inv (E' ∖ E))%I) as "x".
  rewrite storage_bulk_inv_union.
  {
    iDestruct ("x" with "[p q]") as "x".
    {
      iFrame "p".
      iIntros "p".
      iDestruct ("q" with "p") as "[[e diff] t]".
      iFrame.
    }
    {
      iMod "x" as "[q k]". iModIntro.
      iFrame "q".
      iIntros "q".
      iDestruct ("k" with "q") as "[e [t diff]]".
      iFrame.
    }
  }
  set_solver.
Qed.

Lemma wsat_split_one_union x E 
    (not_in: x ∉ E) :
   ⊢ |={E ∪ {[ x ]}, E}=> (storage_inv x) ∗ (storage_inv x ={E, E ∪ {[ x ]}}=∗ True).
Proof.
  assert (E ## {[x]}) as disj by set_solver.
  rewrite uPred_fupd_eq. unfold uPred_fupd_def.
  iIntros "[w e]".
  iDestruct (ownE_op with "e") as "[ee e]". { trivial. }
  iMod (ownI_alloc_open_or_alloc x with "[w e]") as (P) "[w [d [i p]]]". { iFrame. }
  unfold storage_inv.
  iMod (ownE_empty) as "oemp".
  iModIntro. iModIntro. iFrame.
  iSplitL "i p".
  { iExists P. iFrame. }
  iIntros "op [w e]".
  iDestruct "op" as (P0) "op".
  iDestruct (ownI_close x P0 with "[w op d]") as "[w l]".
  { iFrame. }
  iModIntro. iModIntro. rewrite ownE_op. { iFrame. } trivial.
Qed.

Lemma elem_diff_union_singleton (x: positive) (E: coPset)
  (eo: x ∈ E) : ((E ∖ {[ x ]}) ∪ {[ x ]} = E).
Proof.
  apply set_eq. intros.  rewrite elem_of_union.
          rewrite elem_of_difference. rewrite elem_of_singleton.
          intuition. { subst x. trivial. }
          have h : Decision (x0 = x) by solve_decision. destruct h; intuition.
Qed.

Lemma wsat_split_one_diff E x
    (eo: x ∈ E) :
   ⊢ |={E, (E ∖ {[ x ]})}=> (storage_inv x) ∗ (storage_inv x ={E ∖ {[ x ]}, E}=∗ True).
Proof.
  assert ((E ∖ {[ x ]}) ∪ {[ x ]} = E) as ue.
      { apply elem_diff_union_singleton; trivial. }
  rewrite <- ue at 1. 
  rewrite <- ue at 4. 
  apply wsat_split_one_union.
  set_solver.
Qed.

Lemma wsat_split_main E F E'
    (ss: ∀ x , x ∈ F \/ x ∈ E' <-> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ E' -> False) :
   ⊢ |={E,E'}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={E',E}=∗ True).
Proof.
  generalize ss. clear ss. generalize di. clear di. generalize E. clear E.
  eapply (@set_ind_L positive (gset positive)) with (P := λ F , 
    ∀ E : coPset,
    (∀ x : positive, x ∈ F ∧ x ∈ E' → False)
    → (∀ x : positive, x ∈ F ∨ x ∈ E' ↔ x ∈ E)
      → ⊢ |={E,E'}=> storage_bulk_inv F ∗ (storage_bulk_inv F ={E',E}=∗ True)
  ).
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. assert (E = E') by set_solver. subst E'.
        iIntros. iModIntro. iSplitL.
        { iDestruct storage_bulk_inv_empty as "x". iApply "x". done. }
        { iIntros. iModIntro. done. }
    - intros x X not_in m E di ss.
      iIntros.
      iMod (wsat_split_one_diff E x) as "[si back]".
      { apply ss. left. set_solver. }
      iMod (m (E ∖ {[x]})) as "[sbi back2]".
      { intuition. apply di with (x0 := x0). set_solver. }
      { intro x0. have ss0 := ss x0. set_solver. }
      rewrite storage_bulk_inv_singleton_union; trivial.
      iModIntro. iFrame "si sbi".
      iIntros "[si sbi]".
      iMod ("back2" with "sbi") as "l".
      iMod ("back" with "si") as "q".
      iModIntro. done.
Qed.

Lemma wsat_split_superset E F E'
    (ss: ∀ x , x ∈ F \/ x ∈ E' -> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ E' -> False) :
   ⊢ |={E,E'}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={E',E}=∗ True).
Proof.
  iIntros.
  iMod (fupd_mask_subseteq (gset_to_coPset F ∪ E')) as "back".
  { unfold "⊆". unfold set_subseteq_instance. intro.
      rewrite elem_of_union.
      rewrite elem_of_gset_to_coPset.
      intro. apply ss. trivial. }
  iMod (wsat_split_main (gset_to_coPset F ∪ E') F E') as "[sbi back2]".
  { intros. have j := ss x. rewrite elem_of_union. rewrite elem_of_gset_to_coPset.
      intuition. }
  { apply di. }
  iModIntro. iFrame "sbi". iIntros "sbi". iMod ("back2" with "sbi") as "_".
  iMod "back" as "_". iModIntro. done.
Qed.

Lemma wsat_split_empty E F
    (ss: ∀ x , x ∈ F -> x ∈ E) :
   ⊢ |={E,∅}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={∅,E}=∗ True).
Proof.
  apply wsat_split_superset.
  - intro. rewrite elem_of_empty. intuition.
  - intro. rewrite elem_of_empty. intuition.
Qed.

Lemma guards_apply_persistent (P Q: iProp Σ) F E
    (ss: ∀ x , x ∈ F -> x ∈ E)
    : (P &&{ F }&&$> □ Q) ⊢ P ={E}=∗ □ Q.
Proof.
  unfold fguards, guards_with. iIntros "g p".
  (*rewrite uPred_fupd_eq. unfold uPred_fupd_def.*)
  iDestruct ("g" $! P) as "g".
  iMod (wsat_split_empty E F) as "[sb back]"; trivial.
  iMod ("g" with "[p sb]") as "t".
  { iFrame. iIntros. iFrame. }
  iDestruct "t" as "[q t]".
  iDestruct (bi.intuitionistically_sep_dup with "q") as "[q q1]".
  iDestruct ("t" with "q") as "[t p]".
  iMod ("back" with "t").
  iModIntro.
  iFrame.
Qed.

Lemma fguards_apply (P Q X Y : iProp Σ) E F D
    (ss1: ∀ x , x ∈ F -> x ∈ E)
    (ss2: ∀ x , x ∈ D -> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ D -> False)
    : (Q ∗ X ={D}=∗ Q ∗ Y) ∗ (P &&{ F }&&$> Q) ⊢ (P ∗ X ={E}=∗ P ∗ Y).
Proof.
  unfold fguards, guards_with. iIntros "[upd g] [p x]".
  iDestruct ("g" $! P) as "g".
  iMod (wsat_split_superset E F D) as "[sb back]"; trivial.
  { intro. have j1 := ss1 x. have j2 := ss2 x. intuition. }
  iDestruct ("g" with "[p sb]") as "g".
  { iFrame. iIntros. iFrame. }
  
  iDestruct (fupd_mask_frame_r _ _ D _ with "g") as "g".
  { apply disjoint_empty_l. }
  replace (∅ ∪ D) with D by set_solver.
  iMod "g" as "[q g]".
  iMod ("upd" with "[q x]") as "[q y]". { iFrame. }
  iDestruct ("g" with "q") as "[g p]".
  iMod ("back" with "g") as "g".
  iModIntro.
  iFrame.
Qed.

Lemma fguards_remove_later (P : iProp Σ) E
    (tl: Timeless P)
    : ⊢ (▷ P) &&{E}&&$> P.
Proof.
  unfold fguards, guards_with.
  iIntros (T) "[p g]".
  iMod "p" as "p".
  iModIntro.
  iFrame.
  iIntros "p". iApply "g". iModIntro. iFrame.
Qed.

Lemma fguards_persistent (P Q R : iProp Σ) E F
    (pers: Persistent R)
    (f_subset_e : ∀ x , x ∈ F -> x ∈ E)
    : ⊢ (P ∗ (P &&{F}&&$> Q) ∗ (Q -∗ R)) ={E}=∗ P ∗ R.
Proof.
  iIntros "[p [g qr]]".
  iAssert (P ∗ True ={E}=∗ P ∗ R)%I with "[g qr]" as "X".
  { iApply (fguards_apply _ Q _ _ E F ∅); trivial.
      { intro. rewrite elem_of_empty. contradiction. }
      { intro. rewrite elem_of_empty. intuition. }
    iFrame "g".
    iIntros "[q _]".
    iDestruct ("qr" with "q") as "#r".
    iModIntro. iFrame "q". iFrame "r".
  }
  iDestruct ("X" with "[p]") as "X". { iFrame. }
  iMod "X" as "[p r]". iModIntro. iFrame "r". iFrame "p".
Qed.
(*
  iIntros "[p [g qr]]".
  unfold fguards, guards_with.
  iMod (wsat_split_superset E F ∅) as "x".
  { intro. have j := f_subset_e x. rewrite elem_of_empty.
      intuition. }
  { intro. rewrite elem_of_empty. intuition. }
  iDestruct ("g" $! P) as "g".
  iDestruct "x" as "[se x]".
  iAssert ((P ∗ (P -∗ storage_bulk_inv F ∗ P))%I) with "[p se]" as "J".
  { iFrame "p". iIntros. iFrame. }
  iMod ("g" with "J") as "[q g]".
  iDestruct ("qr" with "q") as "#r".
  iModIntro. iFrame "r". i
  *)

Lemma fguards_open (P Q : iProp Σ) (E E' : coPset) F
    (ss: ∀ x , x ∈ F \/ x ∈ E' -> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ E' -> False)
    : ⊢ P ∗ (P &&{F}&&$> Q) ={E, E'}=∗
        Q ∗ (Q ={E', E}=∗ P).
Proof.
  iIntros "[p g]".
  unfold fguards, guards_with.
  iMod (wsat_split_superset E F E') as "[inv_f back]"; trivial.
  iDestruct ("g" $! P) as "g".
  
  iAssert ((P ∗ (P -∗ storage_bulk_inv F ∗ P))%I) with "[p inv_f]" as "J".
  { iFrame "p". iIntros. iFrame. }
  
  iDestruct ("g" with "J") as "g".
  
  iDestruct (fupd_mask_frame_r ∅ ∅ E' _ with "g") as "g". { set_solver. }
  replace (∅ ∪ E') with E' by set_solver.
  iMod "g" as "[q g]". iModIntro.
  
  iFrame "q".
  
  iIntros "q".
  iDestruct ("g" with "q") as "[inv_f p]".
  iMod ("back" with "inv_f") as "x".
  iModIntro.
  iFrame "p".
Qed.

(**** guards ****)

Definition guards (P Q : iProp Σ) (E: coPset) : iProp Σ :=
    ∃ m , ⌜ ∀ x , x ∈ m -> x ∈ E ⌝ ∗ fguards P Q m.
    
Notation "P &&{ E }&&> Q" := (guards P Q E)
  (at level 99, E at level 50, Q at level 200).

Lemma guards_refl E P : ⊢ P &&{ E }&&> P.
Proof.
  unfold guards.
  iIntros. iExists ∅. iSplit.
  { iPureIntro. intro. rewrite elem_of_empty. contradiction. }
  iApply fguards_refl.
Qed.


Lemma guards_transitive E P Q R :
    (P &&{ E }&&> Q) ∗ (Q &&{ E }&&> R) ⊢ (P &&{E}&&> R).
Proof.
  unfold guards.
  iIntros "[x y]".
  iDestruct "x" as (mx) "[%condx x]".
  iDestruct "y" as (my) "[%condy y]".
  iDestruct (fguards_mask_weaken _ _ _ (mx ∪ my) with "x") as "x". { set_solver. }
  iDestruct (fguards_mask_weaken _ _ _ (mx ∪ my) with "y") as "y". { set_solver. }
  iExists (mx ∪ my).
  iSplit.
  { iPureIntro. set_solver. }
  iApply (fguards_transitive _ _ Q). iFrame.
Qed.
  
Lemma guards_mask_weaken (P Q: iProp Σ) E E'
    (su: E ⊆ E')
    : (P &&{ E }&&> Q) ⊢ (P &&{ E' }&&> Q).
Proof.
  unfold guards.
  iIntros "x".
  iDestruct "x" as (m) "[%cond x]".
  iExists m. iFrame "x". iPureIntro. set_solver.
Qed.

Lemma guards_weaken E P Q : ⊢ (P ∗ Q) &&{ E }&&> P.
Proof.
  unfold guards. iIntros. iExists ∅. iSplit.
  { iPureIntro. set_solver. }
  iApply fguards_weaken.
Qed.

Lemma guards_apply (P Q X Y : iProp Σ) E F
    (disj: E ## F)
    : (Q ∗ X ={E}=∗ Q ∗ Y) ∗ (P &&{ F }&&> Q) ⊢ (P ∗ X ={E ∪ F}=∗ P ∗ Y).
Proof.
  unfold guards.
  iIntros "[upd g]".
  iDestruct "g" as (m) "[%cond g]".
  iDestruct (fguards_apply P Q X Y (E ∪ F) m E with "[upd g]") as "q".
  { set_solver. }
  { set_solver. }
  { set_solver. }
  { iFrame. }
  iFrame.
Qed.

Lemma guards_remove_later (P : iProp Σ) E
    (tl: Timeless P)
    : ⊢ (▷ P) &&{E}&&> P.
Proof.
  unfold guards.
  iIntros. iExists ∅.
  iSplit.
  { iPureIntro. set_solver. }
  iApply fguards_remove_later.
Qed.

Lemma guards_persistent (P Q R : iProp Σ) E F
    (pers: Persistent R)
    (su: F ⊆ E)
    : ⊢ (P ∗ (P &&{F}&&> Q) ∗ (Q -∗ R)) ={E}=∗ P ∗ R.
Proof.
  unfold guards.
  iIntros "[p [g impl]]".
  iDestruct "g" as (m) "[%cond g]".
  iApply (fguards_persistent P Q R E m).
  { set_solver. }
  iFrame.
Qed.

Lemma guards_open (P Q : iProp Σ) (E F : coPset)
    (su: F ⊆ E)
    : ⊢ P ∗ (P &&{F}&&> Q) ={E, E ∖ F}=∗
        Q ∗ (Q ={E ∖ F, E}=∗ P).
Proof. 
  unfold guards.
  iIntros "[p g]".
  iDestruct "g" as (m) "[%cond g]".
  iDestruct (fguards_open P Q E (E ∖ F) m) as "x".
  { set_solver. }
  { set_solver. }
  iApply "x". iFrame.
Qed.
  
End Guard.

Notation "P &&{ E }&&$> Q" := (fguards P Q E)
  (at level 99, E at level 50, Q at level 200).

Notation "P &&{ E }&&> Q" := (guards P Q E)
  (at level 99, E at level 50, Q at level 200).
