From iris.algebra Require Export cmra.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop wsat invariants.
From iris.proofmode Require Export tactics.
Require Import guarding.guard.

(** Say you have [P &&{E}&&> (▷ Q)] and you want to eliminate the [▷].
If [Q] is timeless, you can do this with [guards_remove_later].

What if [Q] is the conjunction of a timeless part and a persistent part?
Persistent props can be moved in and out of guards easily.
Thus you can eliminate the [▷] by moving the persistent part out,
eliminating the later, then moving the persistent part back in.
This file contains some type classes to automate this. *)

Section GuardLaterPers.

Class LaterGuardExtractable {Σ: gFunctors} (P : iProp Σ) := {
  extract_pers : iProp Σ;
  extract_timeless : iProp Σ;
  lg_pers : Persistent extract_pers;
  lg_timeless : Timeless extract_timeless;
  lg_split: P ⊣⊢ (extract_timeless ∗ extract_pers) % I
}.

#[refine]
Global Instance later_guard_extractable_pers {Σ: gFunctors} (P : iProp Σ) {pers: Persistent P}
    : LaterGuardExtractable P := {
  extract_timeless := True ;
  extract_pers := P ;
}.
Proof.
  iIntros. iSplit. { iIntros "p". iFrame "p". }
  { iIntros "[t p]". iFrame. }
Qed.

#[refine]
Global Instance later_guard_extractable_timeless {Σ: gFunctors} (T : iProp Σ) {timeless: Timeless T}
    : LaterGuardExtractable T := {
  extract_timeless := T ;
  extract_pers := True ;
}.
Proof.
  iIntros. iSplit. { iIntros "p". iFrame "p". }
  { iIntros "[t p]". iFrame. }
Qed.

#[refine]
Global Instance later_guard_extractable_sep {Σ: gFunctors} (P1 P2 : iProp Σ)
    {lg1: LaterGuardExtractable P1}
    {lg2: LaterGuardExtractable P2}
    : LaterGuardExtractable (P1 ∗ P2) := {
  extract_timeless := @extract_timeless _ _ lg1 ∗ @extract_timeless _ _ lg2;
  extract_pers := @extract_pers _ _ lg1 ∗ @extract_pers _ _ lg2;
}.
Proof.
  - apply bi.sep_persistent.
    + apply lg_pers.
    + apply lg_pers.
  - apply bi.sep_timeless.
    + apply lg_timeless.
    + apply lg_timeless.
  - iIntros. iSplit.
      + iIntros "[p1 p2]".
        iDestruct (@lg_split Σ P1 lg1 with "p1") as "[p1a p1b]".
        iDestruct (@lg_split Σ P2 lg2 with "p2") as "[p2a p2b]".
        iFrame.
      + iIntros "[[p1a p2a] [p1b p2b]]".
        iDestruct (@lg_split Σ P1 lg1 with "[p1a p1b]") as "x". { iFrame. }
        iDestruct (@lg_split Σ P2 lg2 with "[p2a p2b]") as "y". { iFrame. }
        iFrame.
Qed.

Context {Σ: gFunctors}.
Context `{!invGS Σ}. 

(* Later-Pers-Guard *)
    
Lemma extract_later1 (X T P : iProp Σ) E F
    (pers: Persistent P)
    (tl: Timeless T)
    (su: F ⊆ E)
    : ⊢ (X ∗ (X &&{F}&&> ▷ (T ∗ P))) ={E}=∗
        (X ∗ ▷ (X &&{F}&&> (T ∗ P))).
Proof.
  iIntros "[x #g]".
  iMod (guards_persistent X (▷ (T ∗ P)) (▷ P) E F with "[x g]") as "[x p]"; trivial.
  { iFrame "x". iFrame "g". iIntros "[_ latp]". iFrame "latp". }
  
  iDestruct (guards_persistent X (▷ (T ∗ P)) (▷ P) E F with "[x g]") as "r"; trivial.
  { iFrame "x". iFrame "g". iIntros "[_ latp]". iFrame "latp". }
  
  iDestruct (guards_weaken_l F (▷ T) (▷ P)) as "g1".
  iDestruct (guards_remove_later T F) as "g2".
  iDestruct (guards_transitive F X _ (▷ T) with "[g g1]") as "g3".
    { iFrame "g". setoid_rewrite bi.later_sep at 2. iFrame "g1". }
  iDestruct (guards_transitive F X (▷ T) T with "[g3 g2]") as "g4". { iFrame "g2". iFrame "g3". }
  iMod "r" as "[x p2]". iModIntro. iFrame "x". iNext. 
  iApply guards_include_pers.
  iFrame "p". iFrame "g4".
Qed.

Lemma extract_later (X S : iProp Σ) E F
    (ex: LaterGuardExtractable S)
    (su: F ⊆ E)
    : ⊢ (X ∗ (X &&{F}&&> ▷ S)) ={E}=∗
        (X ∗ ▷ (X &&{F}&&> S)).
Proof.
  setoid_rewrite (@lg_split Σ S ex).
  apply extract_later1; trivial.
  - apply lg_pers.
  - apply lg_timeless.
Qed.

End GuardLaterPers.
