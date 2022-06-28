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

Definition guards_with (P Q X : iProp Σ) :=
    (∀ (T: iProp Σ), (P ∗ (P -∗ X ∗ T) ={∅}=∗ Q ∗ (Q -∗ X ∗ T))) % I.

Definition guards (P Q : iProp Σ) (m: gset positive) : iProp Σ :=
    guards_with P Q (storage_bulk_inv m).

Notation "P &&{ E }&&> Q" := (guards P Q E)
  (at level 99, E at level 50, Q at level 200).
  
Lemma guards_refl E P : ⊢ P &&{ E }&&> P.
Proof.
  unfold guards, guards_with. iIntros (T) "x". iModIntro. iFrame.
Qed.

Lemma guards_transitive E P Q R :
    (P &&{ E }&&> Q) ∗ (Q &&{ E }&&> R) ⊢ (P &&{E}&&> R).
Proof.
  unfold guards, guards_with.
  iIntros "[a b]". iIntros (T) "p".
  iMod ("a" with "p") as "q".
  iMod ("b" with "q") as "r".
  iModIntro. iFrame.
Qed.

Lemma gset_to_gmap_union (E F : gset positive)
  : gset_to_gmap () (E ∪ F) = gset_to_gmap () E ∪ gset_to_gmap () F. Admitted.
  
Lemma gset_to_gmap_disj (E F : gset positive) (disj : E ## F)
  : gset_to_gmap () E ##ₘ gset_to_gmap () F. Admitted.

Lemma storage_bulk_inv_union (E F : gset positive) (disj: E ## F) :
  storage_bulk_inv (E ∪ F) ⊣⊢ storage_bulk_inv E ∗ storage_bulk_inv F.
Proof.
  unfold storage_bulk_inv. rewrite gset_to_gmap_union.
  apply big_sepM_union. apply gset_to_gmap_disj. trivial.
Qed.
  
  (*
Lemma union_eq_union_diff (E F : gmap positive ())
  : (E ∪ F = E ∪ (F ∖ E)). Admitted.
  
Lemma is_disjoint 
  E ##ₘ F ∖ E
  *)
  
Lemma twoway_assoc (P Q R : iProp Σ)
  : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R).
Proof. iIntros. iSplit. { iIntros "[[p q] r]". iFrame. }
    { iIntros "[p [q r]]". iFrame. } Qed.

Lemma guards_superset E F P Q (disj: E ## F) :
    (P &&{ E }&&> Q) ⊢ (P &&{ E ∪ F }&&> Q).
Proof.
  unfold guards, guards_with.
  iIntros "a".
  iIntros (T).
  rewrite storage_bulk_inv_union; trivial.
  assert ((storage_bulk_inv E ∗ storage_bulk_inv F) ∗ T
      ⊣⊢ storage_bulk_inv E ∗ (storage_bulk_inv F ∗ T)) as asso by apply twoway_assoc.
    rewrite asso.
    iApply "a".
Qed.

Lemma guards_weaken E P Q : ⊢ (P ∗ Q) &&{ E }&&> P.
Proof.
  unfold guards, guards_with. iIntros (T) "[[p q] x]". iModIntro.
  iFrame. iIntros "p".
  iDestruct ("x" with "[p q]") as "m". { iFrame. }
  iFrame.
Qed.

(*
Lemma wsat_split E F :
  (wsat ∗ ownE E) ⊢ (storage_bulk_inv F) ∗ (storage_bulk_inv F -∗ wsat ∗ ownE E).
Admitted.
*)

Lemma wsat_split E F
    (ss: ∀ x , x ∈ F -> x ∈ E) :
   ⊢ |={E,∅}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={∅,E}=∗ True).
Admitted.

Lemma wsat_split2 E F E'
    (ss: ∀ x , x ∈ F -> x ∈ E) :
   ⊢ |={E,E'}=> (storage_bulk_inv F) ∗ (storage_bulk_inv F ={E',E}=∗ True).
Admitted.

Lemma apply_guard_persistent (P Q: iProp Σ) F E
    (ss: ∀ x , x ∈ F -> x ∈ E)
    : (P &&{ F }&&> □ Q) ⊢ P ={E}=∗ □ Q.
Proof.
  unfold guards, guards_with. iIntros "g p".
  (*rewrite uPred_fupd_eq. unfold uPred_fupd_def.*)
  iDestruct ("g" $! P) as "g".
  iMod (wsat_split E F) as "[sb back]"; trivial.
  iMod ("g" with "[p sb]") as "t".
  { iFrame. iIntros. iFrame. }
  iDestruct "t" as "[q t]".
  iDestruct (bi.intuitionistically_sep_dup with "q") as "[q q1]".
  iDestruct ("t" with "q") as "[t p]".
  iMod ("back" with "t").
  iModIntro.
  iFrame.
Qed.

Lemma apply_guard (P Q X Y : iProp Σ) E F D
    (ss: ∀ x , x ∈ F -> x ∈ E)
    : (Q ∗ X ={D}=∗ Q ∗ Y) ∗ (P &&{ F }&&> Q) ⊢ (P ∗ X ={E}=∗ P ∗ Y).
Proof.
  unfold guards, guards_with. iIntros "[upd g] [p x]".
  iDestruct ("g" $! P) as "g".
  iMod (wsat_split2 E F D) as "[sb back]"; trivial.
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
  
End Guard.
