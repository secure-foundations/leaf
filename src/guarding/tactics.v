Require Import guarding.guard.
From iris.prelude Require Import options.

Section TacticsHelpers.

Context {Σ: gFunctors}.
Context `{!invGS Σ}. 
 
Local Lemma guard_weaken_helper_right (A B C : iProp Σ) (E: coPset) (n: nat)
    : (A &&{E; n}&&> B) -∗ (B &&{E}&&> C) -∗ (A &&{E; n}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (n + 0) with n by trivial. iFrame "z".
Qed.

Local Lemma guard_weaken_helper_right_laters_plus (A B C : iProp Σ) (E: coPset) (n m: nat)
    : (A &&{E; n}&&> B) -∗ (B &&{E; m}&&> C) -∗ (A &&{E; n + m}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (n + 0) with n by trivial. iFrame "z".
Qed.

Local Lemma guard_weaken_helper_left (A B C : iProp Σ) (E: coPset) (n: nat)
    : (B &&{E; n}&&> C) -∗ (A &&{E}&&> B) -∗ (A &&{E; n}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (0 + n) with n by trivial. iFrame "z".
Qed.

Local Lemma guard_weaken_helper_left_laters_plus (A B C : iProp Σ) (E: coPset) (n m: nat)
    : (B &&{E; n}&&> C) -∗ (A &&{E; m}&&> B) -∗ (A &&{E; n + m}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (n + m) with (m + n) by lia. iFrame "z".
Qed.
 
Local Lemma guard_goal_helper_right (A B C : iProp Σ) (E: coPset) (n: nat)
    : (A &&{E}&&> B) -∗ (B &&{E; n}&&> C) -∗ (A &&{E; n}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (0 + n) with (n) by lia. iFrame "z".
Qed.

Local Lemma guard_goal_helper_left (A B C : iProp Σ) (E: coPset) (n: nat)
    : (B &&{E}&&> C) -∗ (A &&{E; n}&&> B) -∗ (A &&{E; n}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (n + 0) with (n) by trivial. iFrame "z".
Qed.

Local Lemma guard_goal_helper_right_laters_minus (A B C : iProp Σ) (E: coPset) (n m: nat)
  (le: m ≤ n)
    : (A &&{E; m}&&> B) -∗ (B &&{E; n-m}&&> C) -∗ (A &&{E; n}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (m + (n-m)) with (n) by lia. iFrame "z".
Qed.

Local Lemma guard_goal_helper_left_laters_minus (A B C : iProp Σ) (E: coPset) (n m: nat)
  (le: m ≤ n)
    : (B &&{E; m}&&> C) -∗ (A &&{E; n-m}&&> B) -∗ (A &&{E; n}&&> C).
Proof.
  iIntros "x y". iDestruct (guards_transitive_additive _ A B C with "[x y]") as "z".
  - iFrame "x". iFrame "y". - replace (n - m + m) with (n) by lia. iFrame "z".
Qed.

Local Lemma lguards_open_helper (P Q : iProp Σ) (E F : coPset) n
    (su: F ⊆ E)
    : (P &&{F; n}&&> Q) -∗ P ={E, E ∖ F}=∗
      ▷^n |={E ∖ F}=> (Q ∗ (Q ={E ∖ F, E}=∗ P)).
Proof.
  iIntros "x y". iApply guards_open_later; trivial. iFrame.
Qed.

Local Lemma guards_open_helper (P Q : iProp Σ) (E F : coPset)
    (su: F ⊆ E)
    : (P &&{F}&&> Q) -∗ P ={E, E ∖ F}=∗
      (Q ∗ (Q ={E ∖ F, E}=∗ P)).
Proof.
  iIntros "x y". iApply guards_open; trivial. iFrame.
Qed.

End TacticsHelpers.

Tactic Notation "leaf_hyp" constr(g1) "rhs" "to" open_constr(Q) "as" constr(g2) :=
  iPoseProof (guard_weaken_helper_right _ _ Q with (String.append g1 " []")) as g2.
  
Tactic Notation "leaf_hyp" constr(g1) "rhs" "to" open_constr(Q) "laters" "plus" open_constr(n) "as" constr(g2) :=
  iPoseProof (guard_weaken_helper_right_laters_plus _ _ Q _ _ n with (String.append g1 " []")) as g2.
  
Tactic Notation "leaf_hyp" constr(g1) "lhs" "to" open_constr(Q) "as" constr(g2) :=
  iPoseProof (guard_weaken_helper_left Q with (String.append g1 " []")) as g2.
  
Tactic Notation "leaf_hyp" constr(g1) "lhs" "to" open_constr(Q) "laters" "plus" open_constr(n) "as" constr(g2) :=
  iPoseProof (guard_weaken_helper_left_laters_plus Q _ _ _ _ n with (String.append g1 " []")) as g2.
  
Tactic Notation "leaf_hyp" constr(g1) "mask" "to" open_constr(E) "as" constr(g2) :=
  iPoseProof (guards_weaken_mask _ E _ _ with g1) as g2.
  
Tactic Notation "leaf_hyp" constr(g1) "laters" "to" open_constr(n) "as" constr(g2) :=
  iPoseProof (lguards_weaken_later _ _ _ _ n with g1) as g2.
  
Tactic Notation "leaf_goal" "rhs" "to" open_constr(Q) :=
  iApply (guard_goal_helper_left _ Q).
  
Tactic Notation "leaf_goal" "lhs" "to" open_constr(Q) "laters" "minus" open_constr(n) :=
  iApply (guard_goal_helper_right_laters_minus _ Q _ _ _ n).
  
Tactic Notation "leaf_goal" "rhs" "to" open_constr(Q) "laters" "minus" open_constr(n) :=
  iApply (guard_goal_helper_left_laters_minus _ Q _ _ _ n).
  
Tactic Notation "leaf_goal" "lhs" "to" open_constr(Q) :=
  iApply (guard_goal_helper_right _ Q).
  
Tactic Notation "leaf_goal" "mask" "to" open_constr(E) :=
  iApply (guards_weaken_mask E).
  
Tactic Notation "leaf_goal" "laters" "to" open_constr(n) :=
  iApply (lguards_weaken_later _ _ _ n).
  
Tactic Notation "leaf_by_sep" :=
  iApply lguards_weaken; iModIntro.
  
Tactic Notation "leaf_by_sep_except0" :=
  iApply lguards_weaken_except0; iModIntro.
  
Tactic Notation "leaf_open" constr(g) "with" constr(sel) "as" constr(pat) :=
  iMod (guards_open_helper with (String.append g (String.append " " sel))) as pat.
   
Tactic Notation "leaf_open_laters" constr(g) "with" constr(sel) "as" constr(pat) :=
  iMod (lguards_open_helper with (String.append g (String.append " " sel))) as pat.

Section TacticsTests.
  
Context {Σ: gFunctors}.
Context `{!invGS Σ}. 
  
Local Lemma test_leaf_hyp (A B C D : iProp Σ) E
    : (A &&{∅ ; 3}&&> B ∗ C) ⊢ (A ∗ D &&{E ; 20}&&> B).
Proof.
  iIntros "g".
  leaf_hyp "g" rhs to (B) as "g1".
    { leaf_by_sep. iIntros "[b c]". iFrame. iIntros. done. }
  leaf_hyp "g1" lhs to (A ∗ D)%I as "g2".
    { leaf_by_sep. iIntros "[a d]". iFrame. iIntros. done. }
  leaf_hyp "g2" mask to E as "g3". { set_solver. }
  leaf_hyp "g3" laters to 20 as "g4". { lia. }
  iFrame.
Qed.

Local Lemma test_leaf_hyp2 (A B C D : iProp Σ)
    : (A &&{∅ ; 3}&&> B ∗ C) ⊢ (A ∗ D &&{∅ ; 20}&&> B).
Proof.
  iIntros "g".
  leaf_hyp "g" rhs to (B) laters plus 2 as "g1".
    { leaf_by_sep. iIntros "[b c]". iModIntro. iModIntro. iFrame. iIntros. done. }
  leaf_hyp "g1" lhs to (A ∗ D)%I laters plus 4 as "g2".
    { leaf_by_sep. iIntros "[a d]". iFrame. iModIntro. iModIntro. iModIntro. iModIntro. iIntros. done. }
  leaf_hyp "g2" laters to 20 as "g4". { lia. }
  iFrame.
Qed.

Local Lemma test_leaf_goal (A B C D : iProp Σ) E
    : (A &&{∅ ; 3}&&> B ∗ C) ⊢ (A ∗ D &&{E ; 20}&&> B).
Proof.
  iIntros.
  leaf_goal rhs to (B ∗ C)%I.
    { leaf_by_sep. iIntros "[b c]". iFrame. iIntros. done. }
  leaf_goal lhs to (A)%I.
    { leaf_by_sep_except0. iIntros "[a d]". iModIntro. iFrame. iIntros. done. }
  leaf_goal mask to ∅. { set_solver. }
  leaf_goal laters to 3. { lia. }
  iFrame "#".
Qed.

Local Lemma test_leaf_goal2 (A B C D : iProp Σ) E
    : (A &&{∅ ; 3}&&> B ∗ C) ⊢ (A ∗ D &&{E ; 20}&&> B).
Proof.
  iIntros "#g".
  leaf_goal lhs to (A)%I laters minus 1. { lia. }
    { leaf_by_sep. iIntros "[b c]". iModIntro. iFrame. iIntros. done. }
  leaf_goal rhs to (B ∗ C)%I laters minus 3. { lia. }
    { leaf_by_sep. iIntros "[b c]". iModIntro. iModIntro. iModIntro. iFrame. iIntros. done. }
  leaf_goal mask to ∅. { set_solver. }
  leaf_goal laters to 3. { lia. }
  iFrame "#".
Qed.

Local Lemma test_leaf_open (A B C D : iProp Σ) E
    : (A &&{E}&&> □(B → C)) ∗ A ∗ B ={E}=∗ C.
Proof.
  iIntros "[#g [a b]]".
  leaf_open "g" with "a" as "[#bc back]". { set_solver. }
  iDestruct ("bc" with "b") as "c".
  iMod ("back" with "[bc]") as "j". { iModIntro. iFrame "#". }
  iModIntro. iFrame.
Qed.
  
Local Lemma test_leaf_open2 (A B C D : iProp Σ) E n
    : (A &&{E; n}&&> □(B → C)) ∗ A ∗ B ⊢ |={E,∅}=> ▷^n |={∅,E}=> C.
Proof.
  iIntros "[#g [a b]]".
  leaf_open_laters "g" with "a" as "lats". { set_solver. }
  replace (E ∖ E) with (∅ : coPset) by set_solver.
  iModIntro. iNext. iMod "lats" as "[#bc back]".
  iDestruct ("bc" with "b") as "c".
  iMod ("back" with "[bc]") as "j". { iModIntro. iFrame "#". }
  iModIntro. iFrame.
Qed.

End TacticsTests.
