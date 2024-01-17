From iris.algebra Require Export cmra.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.base_logic.lib Require Export wsat invariants.

From iris.algebra Require Import auth.

From iris.proofmode Require Export tactics.
Require Import guarding.point_props.

Section Guard.

Context {Σ: gFunctors}.
Context `{!invGS Σ}. 

Definition storage_inv (i: positive) : iProp Σ := ∃ P , ownI i P ∗ ▷ P.

Definition know_inv (i: positive) : iProp Σ := ∃ P , ownI i P.

Definition storage_bulk_inv (m: gset positive) : iProp Σ :=
    [∗ map] i ↦ unused ∈ gset_to_gmap () m, storage_inv i.
    
Definition know_bulk_inv (m: gset positive) : iProp Σ :=
    [∗ map] i ↦ unused ∈ gset_to_gmap () m, know_inv i.
    
Lemma know_bulk_inv_empty :
  True ⊢ know_bulk_inv ∅.
Proof.
  unfold know_bulk_inv.
  replace (gset_to_gmap () ∅ : gmap positive ()) with (∅ : gmap positive ()).
  - rewrite big_sepM_empty. trivial.
  - apply map_eq. intros. rewrite lookup_empty. (*rewrite lookup_gset_to_gmap.*) trivial.
Qed.
    
Lemma storage_bulk_inv_empty :
  True ⊢ storage_bulk_inv ∅.
Proof.
  unfold storage_bulk_inv.
  replace (gset_to_gmap () ∅ : gmap positive ()) with (∅ : gmap positive ()).
  - rewrite big_sepM_empty. trivial.
  - apply map_eq. intros. rewrite lookup_empty. (*rewrite lookup_gset_to_gmap.*) trivial.
Qed.

Lemma know_bulk_inv_singleton i
  : know_bulk_inv ({[i]}) ⊣⊢ know_inv i.
Proof.
  unfold know_bulk_inv.
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

Lemma know_bulk_inv_union (E F : gset positive) (disj: E ## F) :
  know_bulk_inv (E ∪ F) ⊣⊢ know_bulk_inv E ∗ know_bulk_inv F.
Proof.
  unfold know_bulk_inv. rewrite gset_to_gmap_union.
  apply big_sepM_union. apply gset_to_gmap_disj. trivial.
Qed.

Lemma storage_bulk_inv_union (E F : gset positive) (disj: E ## F) :
  storage_bulk_inv (E ∪ F) ⊣⊢ storage_bulk_inv E ∗ storage_bulk_inv F.
Proof.
  unfold storage_bulk_inv. rewrite gset_to_gmap_union.
  apply big_sepM_union. apply gset_to_gmap_disj. trivial.
Qed.

Lemma know_bulk_inv_singleton_union i X
  (not_in : i ∉ X)
  : know_bulk_inv ({[i]} ∪ X) ⊣⊢ know_inv i ∗ know_bulk_inv X.
Proof.
  rewrite know_bulk_inv_union.
  - rewrite know_bulk_inv_singleton. trivial.
  - set_solver.
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
    (∀ (T: iProp Σ), (P ∗ (P -∗ X ∗ T) -∗ ◇ (Q ∗ (Q -∗ X ∗ T)))) % I.

Definition fguards (P Q : iProp Σ) (m: gset positive) : iProp Σ :=
    guards_with P Q (storage_bulk_inv m) ∗ know_bulk_inv m.
    
Notation "P &&{ E }&&$> Q" := (fguards P Q E)
  (at level 99, E at level 50, Q at level 200).
  
Global Instance guards_with_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) guards_with.
Proof.
  unfold Proper, "==>", guards_with. intros x y Q x0 y0 Q0 x1 y1 Q1.
  setoid_rewrite Q. setoid_rewrite Q0. setoid_rewrite Q1.  trivial.
Qed.

Global Instance fguards_with_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) fguards.
Proof.
  unfold fguards. unfold Proper, "==>". intros x y Q x0 y0 Q0 x1 y1 Q1.
  unfold storage_bulk_inv.
  assert (x1 = y1) as H. {
      apply set_eq. intro. setoid_rewrite Q1. trivial.
  }
  setoid_rewrite Q. setoid_rewrite Q0. rewrite H. trivial.
Qed.

Definition fguards_impl (P Q S : iProp Σ) F
    (point: point_prop S)
    (qrx: (Q ⊢ S))
    : (
      (P &&{F}&&$> Q)
      ⊢
      (P &&{F}&&$> S)
    ). 
Proof.
  iIntros "[pq kf]".
  unfold fguards, guards_with.
  iFrame "kf".
  iIntros (T).
  iDestruct ("pq" $! T) as "pq".
  iIntros "k".
  iAssert (P ∗ (P -∗ storage_bulk_inv F ∗ T) -∗ ◇ S)%I with "[pq]" as "X".
  {
    iIntros "l".
    iAssert (◇ Q)%I with "[pq l]" as "J". {
      iMod ("pq" with "l") as "[q j]". iModIntro. iFrame "q".
    }
    iMod "J" as "J". iModIntro. iApply qrx. iFrame "J".
  } 
  iDestruct (own_separates_out_except0_point _ S with "[X k]") as "J".
  { trivial. }
  { iFrame "X". iFrame "k". }
  iDestruct "J" as "[J T]".
  iMod "J" as "J".
  iModIntro.
  iFrame "J".
  iIntros "o".
  iDestruct ("T" with "o") as "[p m]".
  iApply "m".
  iFrame "p".
Qed.

Definition fguards_and (P Q R S : iProp Σ) F
    (point: point_prop S)
    (qrx: (Q ∧ R ⊢ S))
    : (
      (P &&{F}&&$> Q) ∗ (P &&{F}&&$> R)
      ⊢
      (P &&{F}&&$> S)
    ). 
Proof.
  iIntros "[[pq kf] [pr _]]".
  unfold fguards, guards_with.
  iFrame "kf".
  iIntros (T).
  iDestruct ("pq" $! T) as "pq".
  iDestruct ("pr" $! T) as "pr".
  iIntros "k".
  iAssert (P ∗ (P -∗ storage_bulk_inv F ∗ T) -∗ ◇ S)%I with "[pq pr]" as "X".
  {
    iIntros "l".
    iAssert (◇ (Q ∧ R))%I with "[pq pr l]" as "J". {
      rewrite bi.except_0_and.
      iSplit.
      { iMod ("pq" with "l") as "[q j]". iModIntro. iFrame "q". }
      { iMod ("pr" with "l") as "[r j]". iModIntro. iFrame "r". }
    }
    iMod "J" as "J". iModIntro. iApply qrx. iFrame "J".
  } 
  iDestruct (own_separates_out_except0_point _ S with "[X k]") as "J".
  { trivial. }
  { iFrame "X". iFrame "k". }
  iDestruct "J" as "[J T]".
  iMod "J" as "J".
  iModIntro.
  iFrame "J".
  iIntros "o".
  iDestruct ("T" with "o") as "[p m]".
  iApply "m".
  iFrame "p".
Qed.
  
Lemma fguards_refl P : ⊢ P &&{ ∅ }&&$> P.
Proof.
  unfold fguards, guards_with. iSplit.
    { iIntros (T) "x". iFrame. }
    iApply know_bulk_inv_empty. done.
Qed.

Lemma fguards_transitive E P Q R :
    (P &&{ E }&&$> Q) ∗ (Q &&{ E }&&$> R) ⊢ (P &&{E}&&$> R).
Proof.
  unfold fguards, guards_with.
  iIntros "[[a ke] [b _]]". iFrame "ke". iIntros (T) "p".
  iMod ("a" with "p") as "q".
  iDestruct ("b" with "q") as "r".
  iFrame.
Qed.
  
Lemma twoway_assoc (P Q R : iProp Σ)
  : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R).
Proof. iIntros. iSplit. { iIntros "[[p q] r]". iFrame. }
    { iIntros "[p [q r]]". iFrame. } Qed.

(*
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
*)

Lemma fguards_weaken P Q : ⊢ (P ∗ Q) &&{ ∅ }&&$> P.
Proof.
  unfold fguards, guards_with.
  iSplit. {
      iIntros (T) "[[p q] x]".
      iFrame. iModIntro. iIntros "p".
      iDestruct ("x" with "[p q]") as "m". { iFrame. }
      iFrame.
  }
  iApply know_bulk_inv_empty. done.
Qed.

Lemma gset_diff_union (E E': gset positive) (su: E ⊆ E') : E' = (E ∪ (E' ∖ E)).
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E) by solve_decision. destruct h; set_solver.
Qed.

Lemma copset_diff_union (E E': coPset) (su: E ⊆ E') : E' = (E ∪ (E' ∖ E)).
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E) by solve_decision. destruct h; set_solver.
Qed.

Lemma union_diff_eq_union (E1 E2 : gset positive) : E1 ∪ (E2 ∖ E1) = E1 ∪ E2.
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E1) by solve_decision. destruct h; set_solver.
Qed.

Lemma intersect_union_diff_eq (E1 E2 : gset positive) : ((E2 ∩ E1) ∪ (E2 ∖ E1)) = E2.
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E1) by solve_decision. destruct h; set_solver.
Qed.

(*
Lemma fguards_mask_weaken (P Q: iProp Σ) E E'
    (su: E ⊆ E')
    : (P &&{ E }&&$> Q) ⊢ (P &&{ E' }&&$> Q).
Proof.
  unfold fguards, guards_with.
  iIntros "x".
  iIntros (T) "[p q]".
  rewrite (gset_diff_union E E'); trivial.
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
      iMod "x" as "[q k]".
      iFrame "q".
      iModIntro. iIntros "q".
      iDestruct ("k" with "q") as "[e [t diff]]".
      iFrame.
    }
  }
  set_solver.
Qed.
*)

Lemma wsat_split_one_union x E 
    (not_in: x ∉ E) :
   know_inv x 
   ⊢ |={E ∪ {[ x ]}, E}=> (storage_inv x) ∗ (storage_inv x ={E, E ∪ {[ x ]}}=∗ True).
Proof.
  assert (E ## {[x]}) as disj by set_solver.
  rewrite uPred_fupd_unseal. unfold uPred_fupd_def.
  iIntros "#kx [w e]".
  iDestruct (ownE_op with "e") as "[ee e]". { trivial. }
  (*iMod (ownI_alloc_open_or_alloc x with "[w e]") as (P) "[w [d [i p]]]". { iFrame. }*)
  unfold know_inv. iDestruct "kx" as (P) "i".
  iDestruct (ownI_open with "[i w e]") as "[w [p d]]".
  { iFrame "w". iFrame "i". iFrame "e". }
  unfold storage_inv.
  iMod (ownE_empty) as "oemp".
  iModIntro. iModIntro. iFrame.
  iSplitL "i p".
  { iExists P. iFrame "p". iFrame "i". }
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
   know_inv x 
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
   know_bulk_inv F
   ⊢ |={E,E'}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={E',E}=∗ True).
Proof.
  generalize ss. clear ss. generalize di. clear di. generalize E. clear E.
  eapply (@set_ind_L positive (gset positive)) with (P := λ F , 
    ∀ E : coPset,
    (∀ x : positive, x ∈ F ∧ x ∈ E' → False)
    → (∀ x : positive, x ∈ F ∨ x ∈ E' ↔ x ∈ E)
      → know_bulk_inv F ⊢ |={E,E'}=> storage_bulk_inv F ∗ (storage_bulk_inv F ={E',E}=∗ True)
  ).
    - typeclasses eauto.
    - typeclasses eauto.
    - intros. assert (E = E') by set_solver. subst E'.
        iIntros. iModIntro. iSplitL.
        { iDestruct storage_bulk_inv_empty as "x". iApply "x". done. }
        { iIntros. iModIntro. done. }
    - intros x X not_in m E di ss.
      iIntros "kbulk".
      rewrite know_bulk_inv_singleton_union; trivial.
      iDestruct "kbulk" as "[kx kbulk]".
      iMod (wsat_split_one_diff E x with "[kx]") as "[si back]".
      { apply ss. left. set_solver. }
      { iFrame. }
      iMod (m (E ∖ {[x]}) with "kbulk") as "[sbi back2]".
      { intuition. apply di with (x := x0). set_solver. }
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
   know_bulk_inv F
   ⊢ |={E,E'}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={E',E}=∗ True).
Proof.
  iIntros "#ki".
  iMod (fupd_mask_subseteq (gset_to_coPset F ∪ E')) as "back".
  { unfold "⊆". unfold set_subseteq_instance. intro.
      rewrite elem_of_union.
      rewrite elem_of_gset_to_coPset.
      intro. apply ss. trivial. }
  iMod (wsat_split_main (gset_to_coPset F ∪ E') F E' with "ki") as "[sbi back2]".
  { intros. have j := ss x. rewrite elem_of_union. rewrite elem_of_gset_to_coPset.
      intuition. }
  { apply di. }
  iModIntro. iFrame "sbi". iIntros "sbi". iMod ("back2" with "sbi") as "_".
  iMod "back" as "_". iModIntro. done.
Qed.

Lemma wsat_split_empty E F
    (ss: ∀ x , x ∈ F -> x ∈ E) :
   know_bulk_inv F
   ⊢ |={E,∅}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={∅,E}=∗ True).
Proof.
  apply wsat_split_superset.
  - intro. rewrite elem_of_empty. intuition.
  - intro. rewrite elem_of_empty. intuition.
Qed.

Lemma fguards_apply_persistent (P Q: iProp Σ) F E
    (ss: ∀ x , x ∈ F -> x ∈ E)
    : (P &&{ F }&&$> □ Q) ⊢ P ={E}=∗ □ Q.
Proof.
  unfold fguards, guards_with. iIntros "[g kf] p".
  (*rewrite uPred_fupd_eq. unfold uPred_fupd_def.*)
  iDestruct ("g" $! P) as "g".
  iMod (wsat_split_empty E F with "kf") as "[sb back]"; trivial.
  rewrite uPred_fupd_unseal. unfold uPred_fupd_def. iIntros "[w eo]".
  iDestruct ("g" with "[p sb]") as "t".
  { iFrame. iIntros. iFrame. }
  iMod "t" as "[q t]".
  iDestruct (bi.intuitionistically_sep_dup with "q") as "[q q1]".
  iDestruct ("t" with "q") as "[t p]".
  iDestruct ("back" with "t [w eo]") as "b". { iFrame. }
  iMod "b" as "b". iModIntro.
  iMod "b" as "b". iModIntro.
  iDestruct "b" as "[w [oe t]]".
  iFrame.
Qed.

Lemma fguards_apply (P Q X Y : iProp Σ) E F D
    (ss1: ∀ x , x ∈ F -> x ∈ E)
    (ss2: ∀ x , x ∈ D -> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ D -> False)
    : (Q ∗ X ={D}=∗ Q ∗ Y) ∗ (P &&{ F }&&$> Q) ⊢ (P ∗ X ={E}=∗ P ∗ Y).
Proof.
  unfold fguards, guards_with. iIntros "[upd [g kf]] [p x]".
  iDestruct ("g" $! (P)%I) as "g".
  iMod (wsat_split_superset E F D with "kf") as "[sb back]"; trivial.
  { intro. have j1 := ss1 x. have j2 := ss2 x. intuition. }
  rewrite uPred_fupd_unseal. unfold uPred_fupd_def. iIntros "[w eo]".
  iMod ("g" with "[p sb]") as "[q g]".
  { iFrame. iIntros. iFrame. }
  
  (*
  iDestruct (fupd_mask_frame_r _ _ D _ with "g") as "g".
  { apply disjoint_empty_l. }
  replace (∅ ∪ D) with D by set_solver.
  *)
  
  iMod ("upd" with "[q x] [w eo]") as "[>w [>ed [>q >y]]]". { iFrame. } { iFrame. }
  iDestruct ("g" with "q") as "[f p]".
  iDestruct ("back" with "f") as "back".
  iDestruct ("back" with "[w ed]") as "back". { iFrame. }
  
  iMod "back". iModIntro.
  iMod "back". iModIntro.
  iDestruct "back" as "[w [e t]]". iFrame.
Qed.

Lemma fguards_remove_later (P : iProp Σ)
    (tl: Timeless P)
    : ⊢ (▷ P) &&{∅}&&$> P.
Proof.
  unfold fguards, guards_with.
  iIntros. iSplit.
  {
    iIntros (T) "[p g]".
    iMod "p" as "p".
    iModIntro.
    iFrame.
    iIntros "p". iApply "g". iModIntro. iFrame.
  }
  iApply know_bulk_inv_empty. done.
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

Lemma fguards_open (P Q : iProp Σ) (E E' : coPset) F
    (ss: ∀ x , x ∈ F \/ x ∈ E' -> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ E' -> False)
    : ⊢ P ∗ (P &&{F}&&$> Q) ={E, E'}=∗
        Q ∗ (Q ={E', E}=∗ P).
Proof.
  unfold fguards, guards_with.
  iIntros "[p [g kf]]".
  iMod (wsat_split_superset E F E' with "kf") as "[inv_f back]"; trivial.
  iDestruct ("g" $! P) as "g".
  
  iAssert ((P ∗ (P -∗ storage_bulk_inv F ∗ P))%I) with "[p inv_f]" as "J".
  { iFrame "p". iIntros. iFrame. }
  
  iDestruct ("g" with "J") as "g".
  
  iDestruct (fupd_mask_frame_r ∅ ∅ E' _ with "g") as "g". { set_solver. }
  replace (∅ ∪ E') with E' by set_solver.
  iMod "g" as "[q g]".
  iMod "q" as "q".
  iMod "g" as "g".
  iModIntro.
  
  iFrame "q".
  
  iIntros "q".
  iDestruct ("g" with "q") as "[inv_f p]".
  iMod ("back" with "inv_f") as "x".
  iModIntro.
  iFrame "p".
Qed.

Lemma fguards_include_pers (P X Q : iProp Σ) F
    (pers: Persistent P) :
  P ∗ □ (X &&{ F }&&$> Q) ⊢ □ (X &&{ F }&&$> (Q ∗ P)).
Proof.
  iIntros "[#p [#g #kf]]".
  iModIntro.
  unfold fguards, guards_with.
  iSplit. {
    iIntros (T) "xk".
    iMod ("g" $! T with "xk") as "[q m]".
    iModIntro.
    iFrame "q". iFrame "p".
    iIntros "[q _]".
    iApply "m". iFrame "q".
  }
  iFrame "kf".
Qed.

Lemma fguards_weaken_mask_1 P1 P2 E1 E2 :
  (P1 &&{ E1 }&&$> P2) ∗ (know_bulk_inv E2) ⊢
  (P1 &&{ E1 ∪ E2 }&&$> P2).
Proof.
  unfold fguards, guards_with.
  iIntros "[[x k1] k2]".
  iSplit. {
    iIntros (T) "[p q]".
    rewrite (gset_diff_union E1 (E1 ∪ E2)).
    {
      iDestruct ("x" $! (T ∗ storage_bulk_inv ((E1 ∪ E2) ∖ E1))%I) as "x".
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
          iMod "x" as "[q k]".
          iFrame "q".
          iModIntro. iIntros "q".
          iDestruct ("k" with "q") as "[e [t diff]]".
          iFrame.
        }
      }
      set_solver.
    }
    set_solver.
  }
  replace E2 with ((E2 ∩ E1) ∪ (E2 ∖ E1)) at 1.
  - rewrite know_bulk_inv_union.
     + iDestruct "k2" as "[_ k2]".
        replace (E1 ∪ E2) with (E1 ∪ (E2 ∖ E1)).
        * rewrite know_bulk_inv_union. { iFrame "k1". iFrame "k2". } 
          set_solver.
        * apply union_diff_eq_union.
     + set_solver.
  - apply intersect_union_diff_eq.
Qed.

Lemma fguards_weaken_mask_2 P1 P2 Q1 Q2 E1 E2 :
  (P1 &&{ E1 }&&$> P2) ∗ (Q1 &&{ E2 }&&$> Q2) ⊢
  (P1 &&{ E1 ∪ E2 }&&$> P2) ∗ (Q1 &&{ E1 ∪ E2 }&&$> Q2).
Proof.
  unfold fguards.
  iIntros "[[g1 #k1] [g2 #k2]]".
  iSplitL "g1".
  { iApply fguards_weaken_mask_1. iFrame "k2". unfold fguards.
        iFrame "g1". iFrame "k1". }
  { replace (E1 ∪ E2) with (E2 ∪ E1) by set_solver.
    iApply fguards_weaken_mask_1. iFrame "k1". unfold fguards.
        iFrame "g2". iFrame "k2". }
Qed.

(* TODO can we find a counterexample to this? *)

(*
Lemma fguards_sep_disjoint P1 P2 Q1 Q2 E1 E2
  (disjoint: E1 ## E2) :
  (P1 &&{ E1 }&&$> P2) ∗ (Q1 &&{ E2 }&&$> Q2) ⊢ (P1 ∗ Q1 &&{ E1 ∪ E2 }&&$> P2 ∗ Q2).
Proof.
  unfold fguards.
  iIntros "[[g1 #k1] [g2 #k2]]".
  rewrite know_bulk_inv_union; trivial. iFrame "k1". iFrame "k2".
  unfold guards_with. iIntros (T) "[[p1 q1] j]".
  *)



(**** guards ****)

Definition guards (P Q : iProp Σ) (E: coPset) : iProp Σ :=
    □ (∃ m , ⌜ ∀ x , x ∈ m -> x ∈ E ⌝ ∗ fguards P Q m).
    
Notation "P &&{ E }&&> Q" := (guards P Q E)
  (at level 99, E at level 50, Q at level 200).
  
Global Instance guards_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) guards.
Proof.
  unfold Proper, "==>", guards. intros x y Q x0 y0 Q0 x1 y1 Q1.
  setoid_rewrite Q. setoid_rewrite Q0. setoid_rewrite Q1.  trivial.
Qed.

Global Instance persistent_guards P Q E :
    Persistent (P &&{E}&&> Q).
Proof.
  unfold guards. apply _.
Qed.

(* Guard-Refl *)

Lemma guards_refl E P : ⊢ P &&{ E }&&> P.
Proof.
  unfold guards.
  iIntros. iModIntro. iExists ∅. iSplit.
  { iPureIntro. intro. rewrite elem_of_empty. contradiction. }
  iApply fguards_refl.
Qed.

(* Guard-Trans *)

Lemma guards_transitive E P Q R :
    (P &&{ E }&&> Q) ∗ (Q &&{ E }&&> R) ⊢ (P &&{E}&&> R).
Proof.
  unfold guards.
  iIntros "[#x #y]".
  iModIntro.
  iDestruct "x" as (mx) "[%condx x]".
  iDestruct "y" as (my) "[%condy y]".
  iDestruct (fguards_weaken_mask_2 P Q Q R mx my with "[x y]") as "[x1 y1]".
  { iFrame "x". iFrame "y". }
  iExists (mx ∪ my).
  iSplit.
  { iPureIntro. set_solver. }
  iApply (fguards_transitive _ _ Q). iFrame "#".
Qed.

(* Guard-Weaken-Mask *)
  
Lemma guards_mask_weaken (P Q: iProp Σ) E E'
    (su: E ⊆ E')
    : (P &&{ E }&&> Q) ⊢ (P &&{ E' }&&> Q).
Proof.
  unfold guards.
  iIntros "x".
  iDestruct "x" as (m) "[%cond #x]".
  iExists m. iFrame "x". iPureIntro. set_solver.
Qed.

(* Guard-Split *)

Lemma guards_weaken_l E P Q : ⊢ (P ∗ Q) &&{ E }&&> P.
Proof.
  unfold guards. iIntros. iModIntro. iExists ∅. iSplit.
  { iPureIntro. set_solver. }
  iApply fguards_weaken.
Qed.

Lemma guards_weaken_r E P Q : ⊢ (P ∗ Q) &&{ E }&&> Q.
Proof.
  setoid_rewrite bi.sep_comm.
  apply guards_weaken_l.
Qed.

Lemma guards_weaken_rhs_l E P Q R :
    (P &&{ E }&&> (Q ∗ R))%I ⊢ P &&{ E }&&> Q.
Proof.
  iIntros "g".
  iDestruct (guards_weaken_l E Q R) as "g2".
  iApply guards_transitive.
  iFrame "g". iFrame "g2".
Qed.

Lemma guards_weaken_rhs_r E P Q R :
    (P &&{ E }&&> (Q ∗ R))%I ⊢ P &&{ E }&&> R.
Proof.
  iIntros "g".
  iDestruct (guards_weaken_r E Q R) as "g2".
  iApply guards_transitive.
  iFrame "g". iFrame "g2".
Qed.

(* Guard-Upd *)

Lemma guards_apply (P Q X Y : iProp Σ) E F
    (disj: E ## F)
    : (Q ∗ X ={E}=∗ Q ∗ Y) ∗ (P &&{ F }&&> Q) ⊢ (P ∗ X ={E ∪ F}=∗ P ∗ Y).
Proof.
  unfold guards.
  iIntros "[upd #g]".
  iDestruct "g" as (m) "[%cond g]".
  iDestruct (fguards_apply P Q X Y (E ∪ F) m E with "[upd g]") as "q".
  { set_solver. }
  { set_solver. }
  { set_solver. }
  { iFrame "g". iFrame "upd". }
  iFrame.
Qed.

(* Later-Guard *)

Lemma guards_remove_later (P : iProp Σ) E
    (tl: Timeless P)
    : ⊢ (▷ P) &&{E}&&> P.
Proof.
  unfold guards.
  iIntros. iModIntro. iExists ∅.
  iSplit.
  { iPureIntro. set_solver. }
  iApply fguards_remove_later.
Qed.

Lemma guards_remove_later2 (X P : iProp Σ) E
    (tl: Timeless P)
    : (X &&{E}&&> ▷ P) ⊢ (X &&{E}&&> P).
Proof.
  iIntros "a".
  iDestruct (guards_remove_later P E) as "b".
  iApply guards_transitive. iFrame "a". iFrame "b".
Qed.

Lemma guards_persistent (P Q R : iProp Σ) E F
    (pers: Persistent R)
    (su: F ⊆ E)
    : ⊢ (P ∗ (P &&{F}&&> Q) ∗ (Q -∗ R)) ={E}=∗ P ∗ R.
Proof.
  unfold guards.
  iIntros "[p [#g impl]]".
  iDestruct "g" as (m) "[%cond g]".
  iApply (fguards_persistent P Q R E m).
  { set_solver. }
  iFrame "g". iFrame.
Qed.

Lemma guards_persistent2 (X P Q R : iProp Σ) E F
    (pers: Persistent R)
    (su: F ⊆ E)
    : ⊢ (X ∗ P ∗ (P &&{F}&&> Q) ∗ (X ∗ Q -∗ R)) ={E}=∗ X ∗ P ∗ R.
Proof.
  iIntros "[x [p [g impl]]]".
  iAssert (Q ∗ X ={∅}=∗ Q ∗ (X ∗ R))%I with "[impl]" as "m".
  {
    iIntros "[q x]". iModIntro.
        iDestruct ("impl" with "[x q]") as "#r". { iFrame. } 
        iFrame. iFrame "#".
  }
  iDestruct (guards_apply P Q X (X ∗ R) ∅ F with "[m g]") as "newg".
  { set_solver. } { iFrame. }
  iDestruct ("newg" with "[x p]") as "newg". { iFrame. }
  iDestruct (fupd_mask_frame_r _ _ (E ∖ F) with "newg") as "l".
  { set_solver. }
  replace (∅ ∪ F ∪ E ∖ F) with E. { iMod "l" as "[p [x r]]". iModIntro. iFrame. }
  have j := copset_diff_union F E.
  set_solver.
Qed.

(* Unguard-Pers *)

Lemma unguard_pers (A B C G : iProp Σ) (pers: Persistent C) E
  (hyp: A ∗ B ⊢ C)
  : G ∗ (G &&{E}&&> A) ∗ B ={E}=∗ G ∗ (G &&{E}&&> A) ∗ B ∗ C.
Proof.
  iIntros "[g [#gu b]]".
  iMod (guards_persistent2 B G A C E E with "[g b]") as "[b [g c]]".
  { set_solver. } { iFrame. iFrame "gu". iIntros "[a b]". iApply hyp. iFrame. }
  iModIntro. iFrame. iFrame "gu".
Qed.

Lemma guards_open (P Q : iProp Σ) (E F : coPset)
    (su: F ⊆ E)
    : ⊢ P ∗ (P &&{F}&&> Q) ={E, E ∖ F}=∗
        Q ∗ (Q ={E ∖ F, E}=∗ P).
Proof. 
  unfold guards.
  iIntros "[p #g]".
  iDestruct "g" as (m) "[%cond g]".
  iDestruct (fguards_open P Q E (E ∖ F) m) as "x".
  { set_solver. }
  { set_solver. }
  iApply "x". iFrame "g". iFrame "p".
Qed.

(* Guard-Pers *)
    
Definition guards_include_pers (P X Q : iProp Σ) F
    (pers: Persistent P) :
  P ∗ (X &&{ F }&&> Q) ⊢ (X &&{ F }&&> (Q ∗ P)).
Proof.
  unfold guards.
  iIntros "[p #g]".
  iDestruct "g" as (m) "[%cond g]".
  iDestruct (fguards_include_pers P X Q m with "[p g]") as "#newg".
  { iFrame "p". iFrame "g". }
  iModIntro.
  iExists m.
  iSplit.
  { iPureIntro. trivial. }
  iFrame "newg".
Qed.

Lemma guards_include_pers_simple (C : iProp Σ) E
    (per: Persistent C)
    : C ⊢ (True &&{E}&&> C).
Proof.
  iIntros "r".
  iDestruct (guards_include_pers C (True)%I (True)%I E with "[r]") as "g".
  { iFrame "r". iApply guards_refl. }
  iDestruct (guards_weaken_rhs_r with "g") as "g". iFrame "g".
Qed.

(* Guard-Implies *)

Definition guards_impl_point (P Q S : iProp Σ) F
    (point: point_prop S)
    (qrx: (Q ⊢ S))
    : (
      (P &&{F}&&> Q)
      ⊢
      (P &&{F}&&> S)
    ).
Proof.
  iIntros "#q". unfold guards.
  iDestruct "q" as (m1) "[%cond1 q]".
  iExists (m1).
  iModIntro. iSplit.
  { iPureIntro. set_solver. }
  iApply (fguards_impl P Q S m1); trivial.
Qed.

(* Guard-And *)

Definition guards_and_point (P Q R S : iProp Σ) F
    (point: point_prop S)
    (qrx: (Q ∧ R ⊢ S))
    : (
      (P &&{F}&&> Q) ∗ (P &&{F}&&> R)
      ⊢
      (P &&{F}&&> S)
    ).
Proof.
  iIntros "[#q #r]". unfold guards.
  iDestruct "q" as (m1) "[%cond1 q]".
  iDestruct "r" as (m2) "[%cond2 r]".
  iExists (m1 ∪ m2).
  iModIntro. iSplit.
  { iPureIntro. set_solver. }
  iDestruct (fguards_weaken_mask_2 P Q P R m1 m2 with "[q r]") as "[q1 r1]". 
  { iFrame "q". iFrame "r". }
  iApply (fguards_and P Q R S (m1 ∪ m2)); trivial.
  iFrame "#".
Qed.

Definition guards_and (P Q R : iProp Σ) {A} `{ing : inG Σ A} γ (x: A) F
    (qrx: (Q ∧ R ⊢ own γ x))
    : (
      (P &&{F}&&> Q) ∗ (P &&{F}&&> R)
      ⊢
      (P &&{F}&&> own γ x)
    ). 
Proof.
  apply guards_and_point; trivial.
  apply point_prop_own.
Qed.

Definition guards_and_sep_union (P1 P2 Q R : iProp Σ) {A} `{ing : inG Σ A} γ (x: A) F1 F2
    (qrx: (Q ∧ R ⊢ own γ x))
    : (
      (P1 &&{F1}&&> Q) ∗ (P2 &&{F2}&&> R)
      ⊢
      (P1 ∗ P2 &&{F1 ∪ F2}&&> own γ x)
    ). 
Proof.
  iIntros "[a b]".
  iDestruct (guards_weaken_l (F1 ∪ F2) P1 P2) as "a1".
  iDestruct (guards_weaken_r (F1 ∪ F2) P1 P2) as "b1".
  iDestruct (guards_mask_weaken _ _ _ (F1 ∪ F2) with "a") as "a". { set_solver. }
  iDestruct (guards_mask_weaken _ _ _ (F1 ∪ F2) with "b") as "b". { set_solver. }
  iDestruct (guards_transitive (F1 ∪ F2) (P1 ∗ P2) P1 Q with "[a1 a]") as "a".
    { iFrame "a". iFrame "a1". }
  iDestruct (guards_transitive (F1 ∪ F2) (P1 ∗ P2) P2 R with "[b1 b]") as "b".
    { iFrame "b". iFrame "b1". }
  iDestruct (guards_and (P1 ∗ P2) Q R γ x (F1 ∪ F2) with "[a b]") as "t"; trivial.
  iFrame.
Qed.

End Guard.

Notation "P &&{ E }&&$> Q" := (fguards P Q E)
  (at level 99, E at level 50, Q at level 200).

Notation "P &&{ E }&&> Q" := (guards P Q E)
  (at level 99, E at level 50, Q at level 200).
