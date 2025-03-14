From iris.prelude Require Import options.
From iris.algebra Require Import gmap auth.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop wsat invariants.
From iris.base_logic.lib Require Import fancy_updates fancy_updates_from_vs.
From iris.proofmode Require Export tactics.
Require Import guarding.factoring_props.

Section Guard.

Context {Σ: gFunctors}.
Context `{!invGS_gen hlc Σ}. 

(* begin hide *)
Local Definition storage_inv (i: positive) : iProp Σ := ∃ P , ownI i P ∗ ▷ P.

Local Definition know_inv (i: positive) : iProp Σ := ∃ P , ownI i P.

Local Definition storage_bulk_inv (m: gset positive) : iProp Σ :=
    [∗ map] i ↦ unused ∈ gset_to_gmap () m, storage_inv i.
    
Local Definition know_bulk_inv (m: gset positive) : iProp Σ :=
    [∗ map] i ↦ unused ∈ gset_to_gmap () m, know_inv i.
    
Local Lemma know_bulk_inv_empty :
  True ⊢ know_bulk_inv ∅.
Proof.
  unfold know_bulk_inv.
  replace (gset_to_gmap () ∅ : gmap positive ()) with (∅ : gmap positive ()).
  - rewrite big_sepM_empty. trivial.
  - apply map_eq. intros. rewrite lookup_empty. (*rewrite lookup_gset_to_gmap.*) trivial.
Qed.
    
Local Lemma storage_bulk_inv_empty :
  True ⊢ storage_bulk_inv ∅.
Proof.
  unfold storage_bulk_inv.
  replace (gset_to_gmap () ∅ : gmap positive ()) with (∅ : gmap positive ()).
  - rewrite big_sepM_empty. trivial.
  - apply map_eq. intros. rewrite lookup_empty. (*rewrite lookup_gset_to_gmap.*) trivial.
Qed.

Local Lemma know_bulk_inv_singleton i
  : know_bulk_inv ({[i]}) ⊣⊢ know_inv i.
Proof.
  unfold know_bulk_inv.
  replace (gset_to_gmap () {[i]}) with ( {[ i := () ]} : gmap positive () ).
  - apply big_sepM_singleton.
  - apply map_eq. intros i0.
      have h : Decision (i = i0) by solve_decision. destruct h.
      + subst i0. rewrite lookup_singleton.
        rewrite lookup_gset_to_gmap. unfold guard.
            destruct (decide (i ∈ {[i]})) as [e|e]; trivial.
            rewrite elem_of_singleton in e. contradiction.
      + rewrite lookup_singleton_ne; trivial.
        rewrite lookup_gset_to_gmap. unfold guard.
            destruct (decide (i0 ∈ {[i]})) as [e|e]; trivial.
            exfalso. rewrite elem_of_singleton in e. subst i. contradiction.
Qed.

Local Lemma storage_bulk_inv_singleton i
  : storage_bulk_inv ({[i]}) ⊣⊢ storage_inv i.
Proof.
  unfold storage_bulk_inv.
  replace (gset_to_gmap () {[i]}) with ( {[ i := () ]} : gmap positive () ).
  - apply big_sepM_singleton.
  - apply map_eq. intros i0.
      have h : Decision (i = i0) by solve_decision. destruct h.
      + subst i0. rewrite lookup_singleton.
      rewrite lookup_gset_to_gmap. unfold guard.
            destruct (decide (i ∈ {[i]})) as [e|e]; trivial.
            rewrite elem_of_singleton in e. contradiction.
      + rewrite lookup_singleton_ne; trivial.
        rewrite lookup_gset_to_gmap. unfold guard.
            destruct (decide (i0 ∈ {[i]})) as [e|e]; trivial.
            exfalso. rewrite elem_of_singleton in e. subst i. contradiction.
Qed.

Local Lemma gset_to_gmap_union (E F : gset positive)
  : gset_to_gmap () (E ∪ F) = gset_to_gmap () E ∪ gset_to_gmap () F.
  Proof.
  apply map_eq. intros i. rewrite lookup_union.
    rewrite lookup_gset_to_gmap.
    rewrite lookup_gset_to_gmap.
    rewrite lookup_gset_to_gmap.
    unfold union_with, option_union_with, guard.
    destruct (decide (i ∈ E));
    destruct (decide (i ∈ F));
    destruct (decide (i ∈ (E ∪ F))); trivial; set_solver.
Qed.
  
Local Lemma gset_to_gmap_disj (E F : gset positive) (disj : E ## F)
  : gset_to_gmap () E ##ₘ gset_to_gmap () F.
Proof.
  unfold "##ₘ", map_relation. intros i.  unfold option_relation.
    destruct (gset_to_gmap () E !! i) eqn:x;
    destruct (gset_to_gmap () F !! i) eqn:y; trivial.
    rewrite lookup_gset_to_gmap in x.
    rewrite lookup_gset_to_gmap in y.
    unfold guard in x, y.
    destruct (decide (i ∈ E)); destruct (decide (i ∈ F)); try discriminate.
    set_solver.
Qed.

Local Lemma know_bulk_inv_union (E F : gset positive) (disj: E ## F) :
  know_bulk_inv (E ∪ F) ⊣⊢ know_bulk_inv E ∗ know_bulk_inv F.
Proof.
  unfold know_bulk_inv. rewrite gset_to_gmap_union.
  apply big_sepM_union. apply gset_to_gmap_disj. trivial.
Qed.

Local Lemma storage_bulk_inv_union (E F : gset positive) (disj: E ## F) :
  storage_bulk_inv (E ∪ F) ⊣⊢ storage_bulk_inv E ∗ storage_bulk_inv F.
Proof.
  unfold storage_bulk_inv. rewrite gset_to_gmap_union.
  apply big_sepM_union. apply gset_to_gmap_disj. trivial.
Qed.

Local Lemma know_bulk_inv_singleton_union i X
  (not_in : i ∉ X)
  : know_bulk_inv ({[i]} ∪ X) ⊣⊢ know_inv i ∗ know_bulk_inv X.
Proof.
  rewrite know_bulk_inv_union.
  - rewrite know_bulk_inv_singleton. trivial.
  - set_solver.
Qed.

Local Lemma storage_bulk_inv_singleton_union i X
  (not_in : i ∉ X)
  : storage_bulk_inv ({[i]} ∪ X) ⊣⊢ storage_inv i ∗ storage_bulk_inv X.
Proof.
  rewrite storage_bulk_inv_union.
  - rewrite storage_bulk_inv_singleton. trivial.
  - set_solver.
Qed.

Local Definition lguards_with (P Q X : iProp Σ) (n: nat) :=
    (∀ (T: iProp Σ), (P ∗ (P -∗ X ∗ T) -∗ ▷^n ◇ (Q ∗ (Q -∗ X ∗ T)))) % I.
    
Local Definition lfguards (P Q : iProp Σ) (m: gset positive) (n: nat) : iProp Σ :=
    lguards_with P Q (storage_bulk_inv m) n ∗ know_bulk_inv m.
    
Local Notation "P &&{ E ; n }&&$> Q" := (lfguards P Q E n)
  (at level 99, E at level 50, Q at level 200).
  
Local Instance lguards_with_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (=) ==> (≡)) lguards_with.
Proof.
  unfold Proper, "==>", lguards_with. intros x y Q x0 y0 Q0 x1 y1 Q1 x2 y2 x2_eq_y2.
  subst x2. setoid_rewrite Q. setoid_rewrite Q0. setoid_rewrite Q1.  trivial.
Qed.

Local Instance lfguards_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (=) ==> (≡)) lfguards.
Proof.
  unfold lfguards. unfold Proper, "==>". intros x y Q x0 y0 Q0 x1 y1 Q1 x2 y2 x2_eq_y2.
  unfold storage_bulk_inv.
  assert (x1 = y1) as H. {
      apply set_eq. intro. setoid_rewrite Q1. trivial.
  }
  subst x2. setoid_rewrite Q. setoid_rewrite Q0. rewrite H. trivial.
Qed.

Local Lemma lfguards_and (P Q R S : iProp Σ) F (n: nat)
    (point: point_prop S)
    (qrx: (Q ∧ R ⊢ S))
    : (
      (P &&{F ; n}&&$> Q) ∗ (P &&{F ; n}&&$> R)
      ⊢
      (P &&{F ; n}&&$> S)
    ). 
Proof.
  iIntros "[[pq kf] [pr _]]".
  unfold lfguards, lguards_with.
  iFrame "kf".
  iIntros (T).
  iDestruct ("pq" $! T) as "pq".
  iDestruct ("pr" $! T) as "pr".
  iIntros "k".
  iAssert (P ∗ (P -∗ storage_bulk_inv F ∗ T) -∗ ▷^n ◇ S)%I with "[pq pr]" as "X".
  {
    iIntros "l".
    iAssert (▷^n ◇ (Q ∧ R))%I with "[pq pr l]" as "J". {
      rewrite bi.except_0_and.
      iSplit.
      { iDestruct ("pq" with "l") as "[q j]". iFrame "q". }
      { iDestruct ("pr" with "l") as "[r j]". iFrame "r". }
    }
    iNext.
    iMod "J" as "J". iModIntro. iApply qrx. iFrame "J".
  } 
  iDestruct (own_separates_out_except0_point_later _ S with "[X k]") as "J".
  { trivial. }
  { iFrame "X". iFrame "k". }
  iDestruct "J" as "[J T]".
  iNext. iMod "J" as "J".
  iModIntro.
  iFrame "J".
  iIntros "o".
  iDestruct ("T" with "o") as "[p m]".
  iApply "m".
  iFrame "p".
Qed.

Local Lemma lfguards_exists_strengthen X (P Q : iProp Σ) (S R : X -> iProp Σ) F n
    (pr_impl_s: (∀ x, Q ∧ R x ⊢ S x))
    (pers: ∀ x, Persistent (S x))
    : (
      (P &&{F; n}&&$> Q) ∗
      (P &&{F; n}&&$> (∃ (x: X), R x))
      ⊢
      (P &&{F; n}&&$> (∃ (x: X), R x ∗ S x))
    ). 
Proof.
  iIntros "[[pq _] [prs kf]]".
  unfold lfguards, lguards_with.
  iFrame "kf". iIntros (T). iDestruct ("prs" $! T) as "prs". iIntros "k".
  iAssert (▷^n ((◇ Q) ∧ (◇ ((∃ x, R x) ∗ ((∃ x, R x) -∗ storage_bulk_inv F ∗ T)))))%I with "[pq prs k]" as "X".
  { iSplit.
     { iDestruct ("pq" with "k") as "[dq _]". iFrame "dq". }
     { iDestruct ("prs" with "k") as "rs". iFrame "rs". } }
  rewrite <- bi.except_0_and. iNext. iMod "X" as "X". iModIntro.
  rewrite bi.sep_exist_r. rewrite bi.and_exist_l. iDestruct "X" as (x) "X".
  iAssert (S x) with "[X]" as "#s". { iApply pr_impl_s. iSplit.
      { iDestruct "X" as "[X _]". iFrame "X". }
      { iDestruct "X" as "[_ [r _]]". iFrame "r". } }
  iDestruct "X" as "[_ [r back]]".
  iSplitL "r". { iExists x. iFrame "r". iFrame "s". }
  iIntros "j". iDestruct "j" as (x0) "[r s2]". iApply "back". iExists x0. iFrame "r".
Qed.

Local Lemma lfguards_weaken_except0 P Q n
  : □(P -∗ ▷^n ◇ (Q ∗ (Q -∗ P))) ⊢ P &&{ ∅ ; n }&&$> Q.
Proof.
  unfold lfguards, lguards_with. iIntros "#pq". iSplit.
  {
    iIntros (T) "[p g]".
    iDestruct ("pq" with "p") as "[latq back]".
    setoid_rewrite (bi.except_0_sep) at 2. iFrame.
    iModIntro. iMod "back". iModIntro.
    iIntros "q". iApply "g". iApply "back". iFrame.
  }
  iApply know_bulk_inv_empty. done.
Qed.
  
Local Lemma lfguards_refl P n : ⊢ P &&{ ∅ ; n }&&$> P.
Proof.
  unfold lfguards, lguards_with. iSplit.
    { iIntros (T) "x". iNext. iFrame. }
    iApply know_bulk_inv_empty. done.
Qed.

Local Lemma lfguards_transitive E P Q R n m :
    (P &&{ E ; n }&&$> Q) ∗ (Q &&{ E ; m }&&$> R) ⊢ (P &&{ E ; n + m }&&$> R).
Proof.
  iIntros "[[a ke] [b _]]". iFrame "ke". iIntros (T) "p".
  iApply bi.laterN_add.
  iDestruct ("a" with "p") as "q".
  iNext.
  destruct m.
  { rewrite bi.laterN_0. iMod "q" as "q".
    iDestruct ("b" with "q") as "r". iFrame. }
  unfold "◇" at 1. iDestruct "q" as "[q|q]".
  { iNext. iExFalso. iFrame. }
  iDestruct ("b" with "q") as "r". iFrame.
Qed.

Local Lemma lfguards_or_guards_false E P Q S n m :
    (P &&{ E ; n }&&$> Q ∨ S) ∗ (Q &&{ E ; m }&&$> False) ⊢ (P &&{ E ; n + m }&&$> S).
Proof.
  iIntros "[[a ke] [b _]]". iFrame "ke". iIntros (T) "p".
  iApply bi.laterN_add.
  iDestruct ("a" with "p") as "q".
  iNext.
  destruct m.
  { rewrite bi.laterN_0.
      iMod "q" as "[q_or_s q_or_s_back]".
      iDestruct "q_or_s" as "[q|s]".
      + unfold lguards_with.
        iDestruct ("b" $! T with "[q q_or_s_back]") as "j".
        * iFrame "q". iIntros "q". iApply "q_or_s_back". iLeft. iFrame "q".
        * iMod "j" as "[f _]". iExFalso. iFrame "f".
      + iModIntro. iFrame "s". iIntros "s". iApply "q_or_s_back". iRight. iFrame "s".
  }
  unfold "◇" at 1. iDestruct "q" as "[q|q]".
  { iNext. iExFalso. iFrame. }
  { iDestruct "q" as "[q_or_s q_or_s_back]".
      iDestruct "q_or_s" as "[q|s]".
      + unfold lguards_with.
        iDestruct ("b" $! T with "[q q_or_s_back]") as "j".
        * iFrame "q". iIntros "q". iApply "q_or_s_back". iLeft. iFrame "q".
        * iNext. iNext. iMod "j" as "[f _]". iExFalso. iFrame "f".
      + iFrame "s". iNext. iNext. iModIntro. iIntros "s". iApply "q_or_s_back". iRight. iFrame "s".
  }
Qed.
  
Local Lemma twoway_assoc (P Q R : iProp Σ)
  : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R).
Proof. iIntros. iSplit. { iIntros "[[p q] r]". iFrame. }
    { iIntros "[p [q r]]". iFrame. } Qed.

Local Lemma lfguards_weaken_sep P Q n : ⊢ (P ∗ Q) &&{ ∅ ; n }&&$> P.
Proof.
  unfold lfguards, lguards_with.
  iSplit. {
      iIntros (T) "[[p q] x]".
      iFrame. iNext. iModIntro. iIntros "p".
      iDestruct ("x" with "[p q]") as "m". { iFrame. }
      iFrame.
  }
  iApply know_bulk_inv_empty. done.
Qed.

Local Lemma lfguards_weaken_later (P Q : iProp Σ) E n m : n ≤ m ->
    (P &&{ E ; n }&&$> Q) ⊢ (P &&{ E ; m }&&$> Q).
Proof.
  unfold lfguards, lguards_with. intro n_le_m.
  iIntros "[g kbi]". iFrame. iIntros (T) "[p q]".
  iDestruct ("g" $! T) as "g".
  replace m with ((m-n) + n) by lia.
  iApply bi.laterN_add. iModIntro. iApply "g". iFrame.
Qed.

Local Lemma gset_diff_union (E E': gset positive) (su: E ⊆ E') : E' = (E ∪ (E' ∖ E)).
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E) by solve_decision. destruct h; set_solver.
Qed.

Local Lemma copset_diff_union (E E': coPset) (su: E ⊆ E') : E' = (E ∪ (E' ∖ E)).
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E) by solve_decision. destruct h; set_solver.
Qed.

Local Lemma union_diff_eq_union (E1 E2 : gset positive) : E1 ∪ (E2 ∖ E1) = E1 ∪ E2.
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E1) by solve_decision. destruct h; set_solver.
Qed.

Local Lemma intersect_union_diff_eq (E1 E2 : gset positive) : ((E2 ∩ E1) ∪ (E2 ∖ E1)) = E2.
Proof.
  apply set_eq. intro x.
  have h : Decision (x ∈ E1) by solve_decision. destruct h; set_solver.
Qed.

Local Lemma wsat_split_one_union x E 
    (not_in: x ∉ E) :
   know_inv x 
   ⊢ |={E ∪ {[ x ]}, E}=> (storage_inv x) ∗ (storage_inv x ={E, E ∪ {[ x ]}}=∗ True).
Proof.
  assert (E ## {[x]}) as disj by set_solver.
  rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
  iIntros "#kx [w e]".
  iDestruct (ownE_op with "e") as "[ee e]". { trivial. }
  unfold know_inv. iDestruct "kx" as (P) "i".
  iDestruct (ownI_open with "[i w e]") as "[w [p d]]".
  { iFrame "w". iFrame "i". iFrame "e". }
  unfold storage_inv.
  iMod (ownE_empty) as "oemp".
  iModIntro. iModIntro. iFrame "i". iFrame "w". iFrame "ee". iFrame "p".
  iIntros "op [w e]".
  iDestruct "op" as (P0) "op".
  iDestruct (ownI_close x P0 with "[w op d]") as "[w l]".
  { iFrame. }
  iModIntro. iModIntro. rewrite ownE_op. { iFrame. } trivial.
Qed.

Local Lemma elem_diff_union_singleton (x: positive) (E: coPset)
  (eo: x ∈ E) : ((E ∖ {[ x ]}) ∪ {[ x ]} = E).
Proof.
  apply set_eq. intros x0.  rewrite elem_of_union.
          rewrite elem_of_difference. rewrite elem_of_singleton.
          intuition. { subst x. trivial. }
          have h : Decision (x0 = x) by solve_decision. destruct h; intuition.
Qed.

Local Lemma wsat_split_one_diff E x
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

Local Lemma wsat_split_main E F E'
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
    - intros E H1 H2. assert (E = E') by set_solver. subst E'.
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
      { intros x0. intuition. apply di with (x := x0). set_solver. }
      { intro x0. have ss0 := ss x0. set_solver. }
      rewrite storage_bulk_inv_singleton_union; trivial.
      iModIntro. iFrame "si sbi".
      iIntros "[si sbi]".
      iMod ("back2" with "sbi") as "l".
      iMod ("back" with "si") as "q".
      iModIntro. done.
Qed.

Local Lemma wsat_split_superset E F E'
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
  { intros x. have j := ss x. rewrite elem_of_union. rewrite elem_of_gset_to_coPset.
      intuition. }
  { apply di. }
  iModIntro. iFrame "sbi". iIntros "sbi". iMod ("back2" with "sbi") as "_".
  iMod "back" as "_". iModIntro. done.
Qed.

Local Lemma wsat_split_empty E F
    (ss: ∀ x , x ∈ F -> x ∈ E) :
   know_bulk_inv F
   ⊢ |={E,∅}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={∅,E}=∗ True).
Proof.
  apply wsat_split_superset.
  - intro. rewrite elem_of_empty. intuition.
  - intro. rewrite elem_of_empty. intuition.
Qed.

Local Lemma lfguards_open (P Q : iProp Σ) (E E' : coPset) F n
    (ss: ∀ x , x ∈ F \/ x ∈ E' -> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ E' -> False)
    : ⊢ P ∗ (P &&{F ; n}&&$> Q) ={E, E'}=∗
        ▷^n (|={E', E'}=> (Q ∗ (Q ={E', E}=∗ P))).
Proof.
  unfold lfguards, lguards_with.
  iIntros "[p [g kf]]".
  iMod (wsat_split_superset E F E' with "kf") as "[inv_f back]"; trivial.
  iDestruct ("g" $! P) as "g".
  
  iAssert ((P ∗ (P -∗ storage_bulk_inv F ∗ P))%I) with "[p inv_f]" as "J".
  { iFrame "p". iIntros. iFrame. }
  
  iDestruct ("g" with "J") as "g".
  
  iDestruct (fupd_mask_frame_r ∅ ∅ E' _ with "g") as "g". { set_solver. }
  replace (∅ ∪ E') with E' by set_solver.
  iMod "g" as "[q g]".
  iModIntro. iNext. iIntros.
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

Local Lemma lfguards_open_two_simultaneously (P Q R : iProp Σ) (E E' : coPset) F n
    (ss: ∀ x , x ∈ F \/ x ∈ E' -> x ∈ E)
    (di: ∀ x , x ∈ F /\ x ∈ E' -> False)
    : ⊢ P ∗ (P &&{F;n}&&$> Q) ∗ (P &&{F;n}&&$> R) ={E, E'}=∗
        ∃ T, T
            ∗ (T -∗ ▷^n ◇ (Q ∗ (Q -∗ T)))
            ∗ (T -∗ ▷^n ◇ (R ∗ (R -∗ T)))
            ∗ (T ={E', E}=∗ P).
Proof.
  unfold lfguards, lguards_with.
  iIntros "[p [[g kf] [g2 _]]]".
  iMod (wsat_split_superset E F E' with "kf") as "[inv_f back]"; trivial.
  iDestruct ("g" $! P) as "g".
  iDestruct ("g2" $! P) as "g2".
  
  iAssert ((P ∗ (P -∗ storage_bulk_inv F ∗ P))%I) with "[p inv_f]" as "J".
  { iFrame "p". iIntros. iFrame. }
  
  iModIntro.
  iExists (P ∗ (P -∗ storage_bulk_inv F ∗ P))%I.
  iFrame.
  
  iSplitL "g".
  { iIntros "x". iDestruct ("g" with "x") as "t". iNext. iMod "t" as "[a b]". iModIntro. iFrame "a".
      iIntros "q". iDestruct ("b" with "q") as "[b p]". iFrame "p".
      iIntros. iFrame. }
  iSplitL "g2".
  { iIntros "x". iDestruct ("g2" with "x") as "t". iNext. iMod "t" as "[a b]". iModIntro. iFrame "a".
      iIntros "q". iDestruct ("b" with "q") as "[b p]". iFrame "p".
      iIntros. iFrame. }
  iIntros "[p x]". 
  iDestruct ("x" with "p") as "[x p]".
  iMod ("back" with "x") as "back".
  iModIntro. iFrame "p".
Qed.

Local Lemma lfguards_include_pers (P X Q : iProp Σ) F n
    (pers: Persistent P) :
  P ∗ □ (X &&{ F ; n }&&$> Q) ⊢ □ (X &&{ F; n }&&$> (Q ∗ P)).
Proof.
  iIntros "[#p [#g #kf]]".
  iModIntro.
  unfold lfguards, lguards_with.
  iSplit. {
    iIntros (T) "xk".
    iDestruct ("g" $! T with "xk") as "[q m]".
    iNext. iMod "q" as "q". iMod "m" as "m". iModIntro.
    iFrame "q". iFrame "p".
    iIntros "[q _]".
    iApply "m". iFrame "q".
  }
  iFrame "kf".
Qed.

Local Lemma lfguards_weaken_mask_1 P1 P2 E1 E2 n :
  (P1 &&{ E1 ; n }&&$> P2) ∗ (know_bulk_inv E2) ⊢
  (P1 &&{ E1 ∪ E2 ; n }&&$> P2).
Proof.
  unfold lfguards, lguards_with.
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
          iNext. iMod "x" as "[q k]".
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

Local Lemma lfguards_weaken_mask_2 P1 P2 Q1 Q2 E1 E2 n m :
  (P1 &&{ E1 ; n }&&$> P2) ∗ (Q1 &&{ E2 ; m }&&$> Q2) ⊢
  (P1 &&{ E1 ∪ E2 ; n }&&$> P2) ∗ (Q1 &&{ E1 ∪ E2 ; m }&&$> Q2).
Proof.
  unfold lfguards.
  iIntros "[[g1 #k1] [g2 #k2]]".
  iSplitL "g1".
  { iApply lfguards_weaken_mask_1. iFrame "k2". unfold lfguards.
        iFrame "g1". iFrame "k1". }
  { replace (E1 ∪ E2) with (E2 ∪ E1) by set_solver.
    iApply lfguards_weaken_mask_1. iFrame "k1". unfold lfguards.
        iFrame "g2". iFrame "k2". }
Qed.

Local Lemma lfguards_exists {X} (x0: X) (F: X -> iProp Σ) (P: iProp Σ) E n
  : (∀ x , (F x) &&{E; n}&&$> P)%I ⊢ (∃ x , F x) &&{E; n}&&$> P.
Proof.
  unfold lfguards, lguards_with.
  iIntros "a".
  iAssert (know_bulk_inv E) as "#kbi".
  { iDestruct ("a" $! x0) as "[a b]".  iFrame "b". }
  iSplitL.
  { iIntros (T) "[j1 j2]".
    iDestruct "j1" as (x) "j1".
    iDestruct ("a" $! x) as "[a1 a2]".
    iDestruct ("a1" $! T) as "a1".
    iDestruct ("a1" with "[j1 j2]") as "k".
    { iFrame "j1". iIntros "fx". iApply "j2". iExists x. iFrame "fx". }
    iFrame "k".
  }
  iFrame "kbi".
Qed.

Local Lemma ownIagree (γ : gname) (X Y : iProp Σ) : ownI γ X ∗ ownI γ Y ⊢ (▷ X ≡ ▷ Y).
Proof.
  unfold ownI.
  rewrite <- own_op.
  iIntros "x".
  iDestruct (own_valid with "x") as "v".
  rewrite gmap_view_frag_op_validI.
  iDestruct "v" as "[#v iu]".
  rewrite agree_validI.
  rewrite agree_equivI.
  unfold invariant_unfold.
  iDestruct (later_equivI_1 with "iu") as "iu".
  iDestruct (f_equivI_contractive (λ x , (▷ x)%I) with "iu") as "iu".
  iFrame "iu".
Qed.

Local Lemma fguards_from_inv (P: iProp Σ) i
    : ownI i P ⊢ True &&{ {[i]}; 0 }&&$> (▷ P).
Proof.
  unfold lfguards, lguards_with.
  iIntros "#oi". iSplit.
  { iIntros (T) "[t X]". iDestruct ("X" with "t") as "[X t]".
    rewrite storage_bulk_inv_singleton.
    unfold storage_inv. iDestruct "X" as (P0) "[X P]".
    iDestruct (ownIagree i P0 P with "[X]") as "equ". { iFrame. iFrame "#". }
    iRewrite "equ" in "P".
    iModIntro. iFrame.
    iIntros "latP". iExists P. iFrame. iFrame "#".
  }
  rewrite know_bulk_inv_singleton. unfold know_inv. iExists P. iFrame "#".
Qed.

(* 
This lemma isn't possible; see the counterexample in the extended Leaf paper:
https://arxiv.org/abs/2309.04851

Lemma fguards_sep_disjoint P1 P2 Q1 Q2 E1 E2
  (disjoint: E1 ## E2) :
  (P1 &&{ E1 }&&$> P2) ∗ (Q1 &&{ E2 }&&$> Q2) ⊢ (P1 ∗ Q1 &&{ E1 ∪ E2 }&&$> P2 ∗ Q2).
*)

(**** guards ****)


Local Definition guards_def (n: nat) (E: coPset) (P Q : iProp Σ) : iProp Σ :=
    □ (∃ m , ⌜ ∀ x , x ∈ m -> x ∈ E ⌝ ∗ lfguards P Q m n).

Local Definition guards_aux : seal (@guards_def). Proof. by eexists. Qed.
(* end hide *)

(** Definition of [guards] and the notation.
[P &&{ E }&&> Q] is the guards arrow; [E] is the "mask".
The "later count" can be provided with a semicolon as in [P &&{ E ; n }&&> Q].
*)

Definition guards (n: nat) (E: coPset) (P Q : iProp Σ) : iProp Σ. exact (guards_aux.(unseal) n E P Q). Defined.
(* begin hide *)
Local Definition guards_unseal : @guards = @guards_def := guards_aux.(seal_eq).
(* end hide *)
    
(*
Definition guards (P Q : iProp Σ) (E: coPset) : iProp Σ := lguards P Q E 0.
*)
    
Notation "P &&{ E }&&> Q" := (guards 0 E P Q)
  (at level 99, E at level 50, Q at level 200).
  
Notation "P &&{ E ; n }&&> Q" := (guards n E P Q)
  (at level 99, E at level 50, Q at level 200).
  
(** Global instances for guards.
[P &&{ E; n }&&> Q] is persisent. It is proper in both its arguments,
and it is nonexpansive in both its arguments.
Also, when [n ≥ 0], it is contractive in the right-hand side.
*)

Global Instance guards_proper n E :
    Proper ((≡) ==> (≡) ==> (≡)) (guards n E).
Proof.
  unfold Proper, "==>". rewrite guards_unseal. unfold guards_def.
  intros x y Q x0 y0 Q0.
  setoid_rewrite Q. setoid_rewrite Q0. trivial.
Qed.

Global Instance guards_persistent n E P Q :
    Persistent (P &&{E; n}&&> Q).
Proof.
  rewrite guards_unseal. unfold guards_def. apply _.
Qed.

Global Instance guards_nonexpansive2 n E :
    NonExpansive2 (guards n E).
Proof.
    rewrite guards_unseal. unfold guards_def. unfold lfguards. unfold lguards_with.
    solve_proper.
Qed.

Global Instance guards_contractive_right_if_n_ge_1 P E n (n_ge_1: n ≥ 1) :
    Contractive (guards n E P).
Proof.
    rewrite guards_unseal. unfold guards_def. unfold lfguards. unfold lguards_with.
    replace n with (S (n-1)) by lia. unfold bi_laterN. solve_contractive.
Qed.

(** Reflexivity. **)

Lemma guards_refl E P n : ⊢ P &&{ E ; n }&&> P.
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros. iModIntro. iExists ∅. iSplit.
  { iPureIntro. intro. rewrite elem_of_empty. contradiction. }
  iApply lfguards_refl.
Qed.

(** Transitivity. **)

Lemma guards_transitive_additive E P Q R n m :
    (P &&{ E ; n }&&> Q) ∗ (Q &&{ E ; m }&&> R) ⊢ (P &&{ E ; n + m }&&> R).
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros "[#x #y]". iModIntro.
  iDestruct "x" as (mx) "[%condx x]".
  iDestruct "y" as (my) "[%condy y]".
  iDestruct (lfguards_weaken_mask_2 P Q Q R mx my with "[x y]") as "[x1 y1]".
  { iFrame "x". iFrame "y". }
  iExists (mx ∪ my). iSplit.
  { iPureIntro. set_solver. }
  iApply (lfguards_transitive _ _ Q). iFrame "#".
Qed.

Lemma guards_transitive_left E P Q R n :
    (P &&{ E ; n }&&> Q) ∗ (Q &&{ E }&&> R) ⊢ (P &&{ E ; n }&&> R).
Proof.
  have h := guards_transitive_additive E P Q R n 0.
  replace (n + 0) with n in h by lia. apply h.
Qed.

Lemma guards_transitive_right E P Q R m :
    (P &&{ E }&&> Q) ∗ (Q &&{ E ; m }&&> R) ⊢ (P &&{ E ; m }&&> R).
Proof.
  have h := guards_transitive_additive E P Q R 0 m.
  replace (0 + m) with m in h by lia. apply h.
Qed.

Lemma guards_transitive E P Q R :
    (P &&{ E }&&> Q) ∗ (Q &&{ E }&&> R) ⊢ (P &&{E}&&> R).
Proof.
  have h := guards_transitive_additive E P Q R 0 0.
  replace (0 + 0) with 0 in h by lia. apply h.
Qed.

(** Weakening **)

Lemma guards_weaken_mask E E' (P Q: iProp Σ) n
    (is_subset: E ⊆ E')
    : (P &&{ E ; n }&&> Q) ⊢ (P &&{ E' ; n }&&> Q).
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros "x". iDestruct "x" as (m) "[%cond #x]".
  iExists m. iFrame "x". iPureIntro. set_solver.
Qed.

Lemma lguards_weaken_later (P Q : iProp Σ) E n m : n ≤ m ->
    (P &&{ E ; n }&&> Q) ⊢ (P &&{ E ; m }&&> Q).
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros "%n_le_m #J". iDestruct "J" as (m0) "[%k J]".
  iModIntro. iExists m0. iSplit; trivial.
  iApply (lfguards_weaken_later _ _ _ n m); trivial.
Qed.

(* Weaken-by-separation rules *)

Lemma guards_weaken_sep_l E P Q n : ⊢ (P ∗ Q) &&{ E ; n }&&> P.
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros. iModIntro. iExists ∅. iSplit.
  { iPureIntro. set_solver. } iApply lfguards_weaken_sep.
Qed.

Lemma guards_weaken_sep_r E P Q n : ⊢ (P ∗ Q) &&{ E; n }&&> Q.
Proof.
  setoid_rewrite bi.sep_comm.
  apply guards_weaken_sep_l.
Qed.

Lemma guards_weaken_rhs_sep_l E P Q R n :
    (P &&{ E ; n }&&> (Q ∗ R))%I ⊢ P &&{ E ; n }&&> Q.
Proof.
  iIntros "g".
  iDestruct (guards_weaken_sep_l E Q R) as "g2".
  iApply guards_transitive_left.
  iFrame "g". iFrame "g2".
Qed.

Lemma guards_weaken_rhs_sep_r E P Q R n :
    (P &&{ E ; n }&&> (Q ∗ R))%I ⊢ P &&{ E ; n }&&> R.
Proof.
  iIntros "g".
  iDestruct (guards_weaken_sep_r E Q R) as "g2".
  iApply guards_transitive_left.
  iFrame "g". iFrame "g2".
Qed.

Lemma guards_weaken_lhs_sep_l E P Q R n :
    (P &&{ E ; n }&&> Q)%I ⊢ (P ∗ R) &&{ E ; n }&&> Q.
Proof.
  iIntros "g".
  iDestruct (guards_weaken_sep_l E P R) as "g2".
  iApply guards_transitive_right.
  iFrame "g". iFrame "g2".
Qed.

Lemma guards_weaken_lhs_sep_r E P Q R n :
    (P &&{ E ; n }&&> Q)%I ⊢ (R ∗ P) &&{ E ; n }&&> Q.
Proof.
  iIntros "g".
  iDestruct (guards_weaken_sep_r E R P) as "g2".
  iApply guards_transitive_right.
  iFrame "g". iFrame "g2".
Qed.

Lemma guards_true E P n : ⊢ P &&{ E ; n }&&> True.
Proof.
  setoid_replace P with (P ∗ True)%I.
  { iApply guards_weaken_sep_r. }
  iIntros. iSplit. { iIntros. iFrame. } { iIntros "[p _]". iFrame. }
Qed.

(** _Opening guards_.

Opening a guard ([guards_open]) is a lot like opening an invariant;
it decreases the current mask
and gives you a view-shift wand to close it back up again.

[guards_upd] is what you get if you use [guards_open], apply some update, and close
it back up again. This lemma is meant to capture the intuition that a guard
[P &&{_}&&> Q] let you "use [P] as a read-only [Q]". In most cases, though, it's
probably easier to use [guards_open] directly.

[guards_open_two_simultaneously] is a quirky operation needed to construct storage protocols;
it helps you when you'd otherwise have a mask conflict.  **)


Lemma guards_open_later (P Q : iProp Σ) (E F : coPset) n
    (su: F ⊆ E)
    : ⊢ P ∗ (P &&{F; n}&&> Q) ={E, E ∖ F}=∗
      ▷^n |={E ∖ F}=> (Q ∗ (Q ={E ∖ F, E}=∗ P)).
Proof. 
  rewrite guards_unseal. unfold guards_def.
  iIntros "[p #g]".
  iDestruct "g" as (m) "[%cond g]".
  iDestruct (lfguards_open P Q E (E ∖ F) m) as "x".
  { set_solver. } { set_solver. }
  iApply "x". iFrame "g". iFrame "p".
Qed.

Lemma guards_open (P Q : iProp Σ) (E F : coPset)
    (su: F ⊆ E)
    : ⊢ P ∗ (P &&{F}&&> Q) ={E, E ∖ F}=∗
        Q ∗ (Q ={E ∖ F, E}=∗ P).
Proof. 
  iIntros "a". iDestruct (guards_open_later P Q E F 0 su with "a") as "b".
  iMod "b". iMod "b". iModIntro. iFrame "b".
Qed.

Lemma guards_upd_later (P Q X Y : iProp Σ) E F n
    (disj: E ## F)
    : (Q ∗ X ={E}=∗ Q ∗ Y) ∗ (P &&{ F ; n }&&> Q) ⊢ (P ∗ X ={E ∪ F, E}=∗ ▷^n (|={E, E ∪ F}=> P ∗ Y)).
Proof.
  iIntros "[Upd #G] [P X]".
  iDestruct ((guards_open_later P Q (E ∪ F) F n) with "[P G]") as "Opened".
    { set_solver. } { iFrame "P". iFrame "G". }
  replace ((E ∪ F) ∖ F) with E by set_solver.
  iMod "Opened". iModIntro. iNext. iMod "Opened". iDestruct "Opened" as "[Q back]".
  iMod ("Upd" with "[Q X]") as "[Q Y]". { iFrame. }
  iMod ("back" with "Q") as "P".
  iModIntro. iFrame.
Qed.

Lemma guards_upd (P Q X Y : iProp Σ) E F
    (disj: E ## F)
    : (Q ∗ X ={E}=∗ Q ∗ Y) ∗ (P &&{ F }&&> Q) ⊢ (P ∗ X ={E ∪ F}=∗ P ∗ Y).
Proof.
  iIntros "a b". iDestruct (guards_upd_later with "a b") as "x"; trivial.
  iMod "x". iMod "x". iModIntro. iFrame "x".
Qed.

Lemma lguards_open_two_simultaneously (P Q R : iProp Σ) (E F : coPset) (n: nat)
    (su: F ⊆ E)
    : ⊢ P ∗ (P &&{F; n}&&> Q) ∗ (P &&{F; n}&&> R) ={E, E ∖ F}=∗ (
      ∃ T, T ∗ (T -∗ ▷^n ◇ (Q ∗ (Q -∗ T))) ∗ (T -∗ ▷^n ◇ (R ∗ (R -∗ T)))
                ∗ (T ={E ∖ F, E}=∗ P)).
Proof. 
  rewrite guards_unseal. unfold guards_def.
  iIntros "[p [#q #r]]".
  iDestruct "q" as (m1) "[%cond1 q]".
  iDestruct "r" as (m2) "[%cond2 r]".
  iDestruct (lfguards_weaken_mask_2 P Q P R m1 m2 with "[q r]") as "[q1 r1]". { iFrame "#". }
  iDestruct (lfguards_open_two_simultaneously P Q R E (E ∖ F) (m1 ∪ m2) with "[p q1 r1]") as "j".
  { set_solver. } { set_solver. } { iFrame "p". iFrame "q1". iFrame "r1". }
  iMod "j". iModIntro. iFrame.
Qed.

Lemma guards_open_two_simultaneously (P Q R : iProp Σ) (E F : coPset)
    (su: F ⊆ E)
    : ⊢ P ∗ (P &&{F}&&> Q) ∗ (P &&{F}&&> R) ={E, E ∖ F}=∗
      ∃ T, T ∗ (T -∗ ◇ (Q ∗ (Q -∗ T))) ∗ (T -∗ ◇ (R ∗ (R -∗ T)))
                ∗ (T ={E ∖ F, E}=∗ P).
Proof. 
  iIntros "a". iDestruct (lguards_open_two_simultaneously P Q R E F 0 su with "a") as "b".
  iMod "b". iModIntro. iFrame.
Qed.

(** More general variants of sep-weakening **)

Lemma lguards_weaken_except0 (P Q : iProp Σ) n E
  : □(P -∗ ▷^n ◇ (Q ∗ (Q -∗ P))) ⊢ P &&{ E ; n }&&> Q.
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros. iModIntro. iExists ∅. iSplit. { iPureIntro. set_solver. }
  iApply lfguards_weaken_except0. iFrame "#".
Qed.

Lemma lguards_equiv_except0 (P Q : iProp Σ) n E
  : □(P -∗ ▷^n ◇ Q) ∗ □(Q -∗ P) ⊢ P &&{ E ; n }&&> Q.
Proof.
  iIntros "[#A #B]". iApply lguards_weaken_except0.
  iModIntro. iIntros "P". iDestruct ("A" with "P") as "Q". iNext. iMod "Q". iModIntro.
  iFrame "Q". iFrame "B".
Qed.

Lemma lguards_weaken (P Q : iProp Σ) n E
  : □(P -∗ ▷^n (Q ∗ (Q -∗ P))) ⊢ P &&{ E ; n }&&> Q.
Proof.
  iIntros "#T". iApply lguards_weaken_except0.
  iModIntro. iIntros "P". iDestruct ("T" with "P") as "P". iNext. iModIntro. iFrame.
Qed.

Lemma guards_weaken (P Q : iProp Σ) E
  : □(P -∗ (Q ∗ (Q -∗ P))) ⊢ P &&{ E ; 0 }&&> Q.
Proof.
  iIntros "#T". iApply lguards_weaken_except0.
  iModIntro. iIntros "P". iModIntro. iApply "T". iFrame "P".
Qed.

(** Guarding and laters **)

Lemma guards_later_add_1 (P : iProp Σ) E
  : ⊢ (▷ P) &&{E ; 1}&&> P.
Proof.
  iIntros. iApply lguards_weaken. iModIntro. iIntros "P".
  iNext. iFrame "P". iIntros "P". iModIntro. iFrame "P".
Qed.

Lemma guards_later_add_n (P : iProp Σ) E n
  : ⊢ (▷^n P) &&{E ; n}&&> P.
Proof.
  iIntros. iApply lguards_weaken. iModIntro. iIntros "P".
  iNext. iFrame "P". iIntros "P". iModIntro. iFrame "P".
Qed.

Lemma guards_remove_later_or_r (P Q : iProp Σ) E
    (tl: Timeless P)
    : ⊢ (Q ∨ ▷ P) &&{E}&&> Q ∨ P.
Proof.
  iIntros. iApply lguards_equiv_except0. iSplit.
  { iModIntro. iIntros "[q|p]". { iLeft. iFrame. } { iRight. iMod "p". iModIntro. iFrame. } }
  { iModIntro. iIntros "[q|p]". { iLeft. iFrame. } { iRight. iNext. iFrame. } }
Qed.

Lemma guards_remove_later (P : iProp Σ) E
    (tl: Timeless P)
    : ⊢ (▷ P) &&{E}&&> P.
Proof.
  iIntros.
  iApply lguards_equiv_except0. iSplit.
  - iModIntro. iIntros "a". unfold Timeless in tl. iApply tl. iFrame "a".
  - iModIntro. iIntros "a". iModIntro. iFrame.
Qed.

Lemma guards_remove_later_rhs (X P : iProp Σ) E
    (tl: Timeless P)
    : (X &&{E}&&> ▷ P) ⊢ (X &&{E}&&> P).
Proof.
  iIntros "a".
  iDestruct (guards_remove_later P E) as "b".
  iApply guards_transitive. iFrame "a". iFrame "b".
Qed.

Lemma lguards0_eq_guards (P Q : iProp Σ) E : (P &&{ E ; 0 }&&> Q) ⊣⊢ (P &&{ E }&&> Q).
Proof.
  trivial.
Qed.

(** Extracting persistent propositions from guards. Really, these just follow from
[guards_open] and [guards_open_later]. **)

Lemma guards_extract_persistent_later (P Q R : iProp Σ) E F n
    (pers: Persistent R)
    (su: F ⊆ E)
    : ⊢ (P ∗ (P &&{F ; n}&&> Q) ∗ (Q -∗ R)) ={E,E ∖ F}=∗ ▷^n (|={E ∖ F,E}=> P ∗ R).
Proof.
  iIntros "[P [#G QtoR]]".
  iDestruct ((guards_open_later P Q E F n) with "[P G]") as "Opened".
      { trivial. } { iFrame "P". iFrame "G". }
  iMod "Opened". iModIntro. iNext. iMod "Opened" as "[Q back]".
  iDestruct ("QtoR" with "Q") as "#R".
  iMod ("back" with "Q") as "P". iModIntro. iFrame "P". iFrame "R".
Qed.

Lemma guards_extract_persistent (P Q R : iProp Σ) E F
    (pers: Persistent R)
    (su: F ⊆ E)
    : ⊢ (P ∗ (P &&{F}&&> Q) ∗ (Q -∗ R)) ={E}=∗ P ∗ R.
Proof.
  iIntros "a". iDestruct (guards_extract_persistent_later P Q R E F with "a") as "b"; trivial.
  iMod "b". iMod "b". iModIntro. iFrame "b".
Qed.

Lemma guards_extract_persistent2_later (X P Q R : iProp Σ) E F n
    (pers: Persistent R)
    (su: F ⊆ E)
    : ⊢ (X ∗ P ∗ (P &&{F ; n}&&> Q) ∗ (X ∗ Q -∗ R)) ={E, E ∖ F}=∗ ▷^n (|={E ∖ F, E}=> X ∗ P ∗ R).
Proof.
  iIntros "[x [p [g impl]]]".
  iAssert (Q ∗ X ={∅}=∗ Q ∗ (X ∗ R))%I with "[impl]" as "m".
  {
    iIntros "[q x]". iModIntro.
        iDestruct ("impl" with "[x q]") as "#r". { iFrame. } 
        iFrame. iFrame "#".
  }
  iDestruct (guards_upd_later P Q X (X ∗ R)%I ∅ F with "[m g]") as "newg".
  { set_solver. } { iFrame. }
  iDestruct ("newg" with "[x p]") as "newg". { iFrame. }
  iDestruct (fupd_mask_frame_r _ _ (E ∖ F) with "newg") as "l".
  { set_solver. }
  replace (∅ ∪ F ∪ E ∖ F) with E.
  { replace (∅ ∪ E ∖ F) with (E ∖ F) by set_solver.
    iMod "l". iModIntro. iNext.
    iDestruct (fupd_mask_frame_r _ _ (E ∖ F) with "l") as "l". { set_solver. }
    replace (∅ ∪ E ∖ F) with (E ∖ F) by set_solver.
    replace (∅ ∪ F ∪ E ∖ F) with E.
    { iMod "l". iDestruct "l" as "[p [x r]]". iModIntro. iFrame. }
      have j := copset_diff_union F E. set_solver.
    }
  have j := copset_diff_union F E. set_solver.
Qed.

Lemma guards_extract_persistent2 (X P Q R : iProp Σ) E F
    (pers: Persistent R)
    (su: F ⊆ E)
    : ⊢ (X ∗ P ∗ (P &&{F}&&> Q) ∗ (X ∗ Q -∗ R)) ={E}=∗ X ∗ P ∗ R.
Proof.
  iIntros "a".
  iDestruct (guards_extract_persistent2_later X P Q R E F with "a") as "b"; trivial.
  iMod "b". iMod "b". iModIntro. iFrame "b".
Qed.

Lemma unguard_pers_later (A B C G : iProp Σ) (pers: Persistent C) E n
  (hyp: A ∗ B ⊢ C)
  : G ∗ (G &&{E; n}&&> A) ∗ B ={E,∅}=∗ ▷^n |={∅,E}=> G ∗ (G &&{E; n}&&> A) ∗ B ∗ C.
Proof.
  iIntros "[g [#gu b]]".
  iDestruct (guards_extract_persistent2_later B G A C E E with "[g b]") as "x".
  { set_solver. } { iFrame. iFrame "gu". iIntros "[a b]". iApply hyp. iFrame. }
  replace (E ∖ E) with (@empty coPset coPset_empty) by set_solver.
  iMod "x". iModIntro. iNext. iMod "x". iModIntro.
  iDestruct "x" as "[b [g c]]". iFrame. iFrame "gu".
Qed.

(* Unguard-Pers *)

Lemma unguard_pers (A B C G : iProp Σ) (pers: Persistent C) E
  (hyp: A ∗ B ⊢ C)
  : G ∗ (G &&{E}&&> A) ∗ B ={E}=∗ G ∗ (G &&{E}&&> A) ∗ B ∗ C.
Proof.
  iIntros "a". iDestruct (unguard_pers_later A B C G pers E with "a") as "b"; trivial.
  iMod "b". iMod "b". iModIntro. iFrame "b".
Qed.

(** Moving persistent propositions into guards. **)

Lemma guards_include_pers (P X Q : iProp Σ) F n
    (pers: Persistent P) :
  P ∗ (X &&{ F; n }&&> Q) ⊢ (X &&{ F; n }&&> (Q ∗ P)).
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros "[p #g]".
  iDestruct "g" as (m) "[%cond g]".
  iDestruct (lfguards_include_pers P X Q m with "[p g]") as "#newg".
  { iFrame "p". iFrame "g". }
  iModIntro. iExists m. iSplit. { iPureIntro. trivial. } iFrame "newg".
Qed.

Lemma guards_include_pers_simple (C : iProp Σ) E n
    (per: Persistent C)
    : C ⊢ (True &&{E; n}&&> C).
Proof.
  iIntros "r".
  iDestruct (guards_include_pers C (True)%I (True)%I E with "[r]") as "g".
  { iFrame "r". iApply guards_refl. }
  iDestruct (guards_weaken_rhs_sep_r with "g") as "g". iFrame "g".
Qed.

(** Conjunction and factoring **)

(* Guard-Implies *)

Lemma guards_point (P Q : iProp Σ) E n
    (point: point_prop Q)
    (p_entails_q: P ⊢ Q)
    : ⊢ (P &&{E; n}&&> Q).
Proof.
  iIntros.
  iApply lguards_weaken. iModIntro. iIntros "P". iModIntro.
  iApply factoring_props.own_separates_out_point; trivial. iFrame "P".
  iIntros "P". iApply p_entails_q. iFrame.
Qed.

Lemma guards_weaken_rhs_point (P Q S : iProp Σ) F n
    (point: point_prop S)
    (qrx: (Q ⊢ S))
    : (
      (P &&{F; n}&&> Q)
      ⊢
      (P &&{F; n}&&> S)
    ).
Proof.
  iIntros "g".
  iDestruct (guards_point Q S F 0) as "g2"; trivial.
  iApply guards_transitive_left.
  iFrame "g". iFrame "g2".
Qed.

Lemma guards_and_point (P Q R S : iProp Σ) F n
    (point: point_prop S)
    (qrx: (Q ∧ R ⊢ S))
    : (
      (P &&{F; n}&&> Q) ∗ (P &&{F; n}&&> R)
      ⊢
      (P &&{F; n}&&> S)
    ).
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros "[#q #r]".
  iDestruct "q" as (m1) "[%cond1 q]".
  iDestruct "r" as (m2) "[%cond2 r]".
  iExists (m1 ∪ m2).
  iModIntro. iSplit.
  { iPureIntro. set_solver. }
  iDestruct (lfguards_weaken_mask_2 P Q P R m1 m2 with "[q r]") as "[q1 r1]". 
  { iFrame "q". iFrame "r". }
  iApply (lfguards_and P Q R S (m1 ∪ m2)); trivial.
  iFrame "#".
Qed.

(* Guard-And *)

Lemma guards_and_own (P Q R : iProp Σ) {A} `{ing : inG Σ A} γ (x: A) F n
    (qrx: (Q ∧ R ⊢ own γ x))
    : (
      (P &&{F ; n}&&> Q) ∗ (P &&{F ; n}&&> R)
      ⊢
      (P &&{F ; n}&&> own γ x)
    ). 
Proof.
  apply guards_and_point; trivial.
  apply point_prop_own.
Qed.

Lemma guards_and_own_sep_union (P1 P2 Q R : iProp Σ) {A} `{ing : inG Σ A} γ (x: A) F1 F2
    (qrx: (Q ∧ R ⊢ own γ x))
    : (
      (P1 &&{F1}&&> Q) ∗ (P2 &&{F2}&&> R)
      ⊢
      (P1 ∗ P2 &&{F1 ∪ F2}&&> own γ x)
    ). 
Proof.
  iIntros "[a b]".
  iDestruct (guards_weaken_sep_l (F1 ∪ F2) P1 P2) as "a1".
  iDestruct (guards_weaken_sep_r (F1 ∪ F2) P1 P2) as "b1".
  iDestruct (guards_weaken_mask _ (F1 ∪ F2) _ _ with "a") as "a". { set_solver. }
  iDestruct (guards_weaken_mask _ (F1 ∪ F2) _ _ with "b") as "b". { set_solver. }
  iDestruct (guards_transitive (F1 ∪ F2) (P1 ∗ P2) P1 Q with "[a1 a]") as "a".
    { iFrame "a". iFrame "a1". }
  iDestruct (guards_transitive (F1 ∪ F2) (P1 ∗ P2) P2 R with "[b1 b]") as "b".
    { iFrame "b". iFrame "b1". }
  iDestruct (guards_and_own (P1 ∗ P2) Q R γ x (F1 ∪ F2) with "[a b]") as "t"; trivial.
  iFrame.
Qed.

(** Guarding and disjunction **)

Lemma guards_strengthen_exists X (P Q : iProp Σ) (S R : X -> iProp Σ) F n
    (pr_impl_s: (∀ x, Q ∧ R x ⊢ S x))
    (pers: ∀ x, Persistent (S x))
    : (
      (P &&{F; n}&&> Q) ∗
      (P &&{F; n}&&> (∃ (x: X), R x))
      ⊢
      (P &&{F; n}&&> (∃ (x: X), R x ∗ S x))
    ). 
Proof. 
  rewrite guards_unseal. unfold guards_def.
  iIntros "[#a #b]".
  iDestruct "a" as (m1) "[%cond1 q]".
  iDestruct "b" as (m2) "[%cond2 r]".
  iExists (m1 ∪ m2).
  iModIntro. iSplit.
  { iPureIntro. set_solver. }
  iDestruct (lfguards_weaken_mask_2 P Q P (∃ x, R x) m1 m2 with "[q r]") as "[q1 r1]". 
  { iFrame "q". iFrame "r". }
  iApply (lfguards_exists_strengthen X P Q S R (m1 ∪ m2)); trivial.
  iFrame "#".
Qed.

Lemma guards_strengthen_exists_with_lhs X (P : iProp Σ) (S R : X -> iProp Σ) F n
    (pr_impl_s: (∀ x, P ∧ R x ⊢ S x))
    (pers: ∀ x, Persistent (S x))
    : (
      (P &&{F; n}&&> (∃ (x: X), R x))
      ⊢
      (P &&{F; n}&&> (∃ (x: X), R x ∗ S x))
    ). 
Proof.
  iIntros "#G".
  iApply (guards_strengthen_exists X P P S R F n); trivial. iFrame "G".
  iApply guards_refl.
Qed.

Lemma guards_cancel_or (P Q R S : iProp Σ) F1 F2 n
    (qrx: (Q ∧ R ⊢ False))
    : (
      (P &&{F1; n}&&> Q) ∗ (P &&{F2; n}&&> (R ∨ S))
      ⊢
      (P &&{F1 ∪ F2; n}&&> S)
    ). 
Proof.
  assert (R ∨ S ⊣⊢ (∃ (b: bool), if b then R else S)) as He1.
  { iIntros. iSplit.
    - iIntros "RS". iDestruct "RS" as "[R|S]".
      + iExists true. iFrame. + iExists false. iFrame.
    - iIntros "RS". iDestruct "RS" as (b) "RS". destruct b.
      + iLeft. iFrame. + iRight. iFrame.
  }
  iIntros "[#G1 #G2]".
  iDestruct (guards_weaken_mask F1 (F1 ∪ F2) P Q n with "G1") as "#H1". { set_solver. }
  iDestruct (guards_weaken_mask F2 (F1 ∪ F2) P (R ∨ S) n with "G2") as "#H2". { set_solver. }
  setoid_rewrite He1.
  iDestruct (guards_strengthen_exists bool P Q
    (λ b, ⌜b = false⌝)%I (λ b, if b then R else S) (F1 ∪ F2) n with "[]") as "A".
  { intros b. iIntros "H". destruct b.
      - iExFalso. iApply qrx. iFrame "H".
      - iPureIntro. trivial.
  }
  { iFrame "#". }
  assert (S ⊣⊢ (∃ x : bool, (if x then R else S) ∗ ⌜x = false⌝)) as He2.
  { iIntros. iSplit.
    - iIntros "S". iExists false. iFrame. iPureIntro. trivial.
    - iIntros "S". iDestruct "S" as (b) "[S %xf]". rewrite xf. iFrame.
  }
  setoid_rewrite <- He2. iFrame "A".
Qed.

Lemma guards_cancel_or_with_lhs (P R S : iProp Σ) F n
    (pr_impl_false: (P ∧ R ⊢ False))
    : (
      (P &&{F; n}&&> (R ∨ S))
      ⊢
      (P &&{F; n}&&> S)
    ). 
Proof.
  iIntros "#G".
  iDestruct (guards_cancel_or P P R S F F n with "[]") as "J"; trivial.
  { iFrame "G". iApply guards_refl. }
  replace (F ∪ F) with F by set_solver. iFrame "J".
Qed.

(*
Lemma guards_exists {X} (x0: X) (F: X -> iProp Σ) (P: iProp Σ) E
  : (∀ x , (F x) &&{E}&&> P)%I ⊢ (∃ x , F x) &&{E}&&> P.
Proof.
  unfold guards.
  iIntros "#g". iModIntro.
  *)



Lemma guards_cancel_or_by_chaining_additive E P Q S n m :
    (P &&{ E ; n }&&> Q ∨ S) ∗ (Q &&{ E ; m }&&> False) ⊢ (P &&{ E ; n + m }&&> S).
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros "[#x #y]". iModIntro.
  iDestruct "x" as (mx) "[%condx x]".
  iDestruct "y" as (my) "[%condy y]".
  iDestruct (lfguards_weaken_mask_2 P (Q ∨ S) Q False mx my with "[x y]") as "[x1 y1]".
  { iFrame "x". iFrame "y". }
  iExists (mx ∪ my).
  iDestruct (lfguards_or_guards_false (mx ∪ my) P Q S n m with "[x y]") as "g2".
  { iFrame "x1". iFrame "y1". }
  iFrame "g2".
  iPureIntro. set_solver.
Qed.

Lemma guards_cancel_or_by_chaining E P Q S :
    (P &&{ E }&&> Q ∨ S) ∗ (Q &&{ E }&&> False) ⊢ (P &&{ E }&&> S).
Proof.
  apply guards_cancel_or_by_chaining_additive.
Qed.

(** The relationship between guarding and invariants **)

Lemma guards_from_ownI (P: iProp Σ) i E
    (i_in_e: i ∈ E)
    : ownI i P ⊢ True &&{ E }&&> (▷ P).
Proof.
  rewrite guards_unseal. unfold guards_def.
  iIntros "#o". iModIntro. iExists {[ i ]}. iSplit.
  { iPureIntro. set_solver. }
  { iApply fguards_from_inv. iFrame "o". }
Qed.

Lemma inv_from_guards (P: iProp Σ) (N: namespace)
    : (True &&{ ↑N }&&> (▷ P)) ⊢ inv N P.
Proof.
  rewrite invariants.inv_unseal. unfold invariants.inv_def.
  iIntros "#G". iModIntro. iIntros (E) "%NinE".
  iMod (guards_open (True) (▷ P) E (↑N) with "[G]") as "[P back]".
    { trivial. } { iFrame "G". }
  iModIntro. iFrame.
Qed.

Lemma guards_alloc E N P : ▷ P ={E}=∗ (True &&{↑N}&&> ▷ P).
Proof.
  iIntros "HP".
  iMod (own_inv_alloc N E P with "HP") as "#HP".
  unfold own_inv.
  iDestruct "HP" as (i) "[%i_in_N OI]".
  iModIntro.
  iApply (guards_from_ownI P i (↑N)); trivial.
Qed.

Lemma guards_alloc_with_inv N E P : ▷ P ={E}=∗ inv N P ∗ (True &&{↑N}&&> ▷ P).
Proof.
  iIntros "HP".
  iMod (guards_alloc E N P with "HP") as "#G".
  iModIntro.
  iFrame "G". iApply (inv_from_guards P N). iFrame "G".
Qed.

End Guard.
(* begin hide *)

Notation "P &&{ E }&&> Q" := (guards 0 E P Q)
  (at level 99, E at level 50, Q at level 200).
  
Notation "P &&{ E ; n }&&> Q" := (guards n E P Q)
  (at level 99, E at level 50, Q at level 200).
