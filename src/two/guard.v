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

Definition storage_inv (i: positive) : iProp Σ := ∃ P , ownI i P ∗ P.

Definition storage_bulk_inv (m: gmap positive ()) : iProp Σ :=
    [∗ map] i ↦ u ∈ m, storage_inv i.

Definition guards_with (P Q X : iProp Σ) :=
    (∀ (T: iProp Σ), (P ∗ (P -∗ X ∗ T) ={∅}=∗ Q ∗ (Q -∗ X ∗ T))) % I.

Definition guards (P Q : iProp Σ) (m: gmap positive ()) : iProp Σ :=
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

Lemma storage_bulk_inv_union (E F : gmap positive ()) (disj: E ##ₘ  F) :
  storage_bulk_inv (E ∪ F) ⊣⊢ storage_bulk_inv E ∗ storage_bulk_inv F.
  Admitted.
  
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

Lemma guards_superset E F P Q (disj: E ##ₘ  F) :
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

  
End Guard.
