From stdpp Require Import namespaces strings.

Section tests.
Implicit Types (N : namespace) (E : coPset).

Lemma test1 N1 N2 :
  N1 ## N2 → ↑N1 ⊆@{coPset} ⊤ ∖ ↑N2.
Proof. solve_ndisj. Qed.

Lemma test2 N1 N2 :
  N1 ## N2 → ↑N1.@"x" ⊆@{coPset} ⊤ ∖ ↑N1.@"y" ∖ ↑N2.
Proof. solve_ndisj. Qed.

Lemma test3 N :
  ⊤ ∖ ↑N ⊆@{coPset} ⊤ ∖ ↑N.@"x".
Proof. solve_ndisj. Qed.

Lemma test4 N :
  ⊤ ∖ ↑N ⊆@{coPset} ⊤ ∖ ↑N.@"x" ∖ ↑N.@"y".
Proof. solve_ndisj. Qed.

Lemma test5 N1 N2 :
  ⊤ ∖ ↑N1 ∖ ↑N2 ⊆@{coPset} ⊤ ∖ ↑N1.@"x" ∖ ↑N2 ∖ ↑N1.@"y".
Proof. solve_ndisj. Qed.

Lemma test_ndisjoint_difference_l N : ⊤ ∖ ↑N ##@{coPset} ↑N.
Proof. solve_ndisj. Qed.
Lemma test_ndisjoint_difference_r N : ↑N ##@{coPset} ⊤ ∖ ↑N.
Proof. solve_ndisj. Qed.

Lemma test6 E N :
  ↑N ⊆ E → ↑N ⊆ ⊤ ∖ (E ∖ ↑N).
Proof. solve_ndisj. Qed.

Lemma test7 N :
  ↑N ⊆@{coPset} ⊤ ∖ ∅.
Proof. solve_ndisj. Qed.

Lemma test8 N1 N2 :
  ⊤ ∖ (↑N1 ∪ ↑N2) ⊆@{coPset} ⊤ ∖ ↑N1.@"counter".
Proof. solve_ndisj. Qed.

Lemma test9 N1 N2 :
  ⊤ ∖ (↑N1 ∪ ↑N2) ⊆@{coPset} ⊤ ∖ ↑N1.@"counter" ∖ ↑N1.@"state" ∖ ↑N2.
Proof. solve_ndisj. Qed.

Lemma test10 N1 N2 E :
  ↑N1 ∪ E ## ⊤ ∖ ↑N1 ∖ ↑N2 ∖ E.
Proof. solve_ndisj. Qed.

Lemma test11 N :
  ↑N.@"other" ⊆@{coPset} ⊤ ∖ (↑N.@"this" ∪ ↑N.@"that").
Proof. solve_ndisj. Qed.

Lemma test12 N :
  ↑N.@"other" ##@{coPset} ↑N.@"this" ∪ ↑N.@"that" ∧
  ↑N.@"other" ∪ ↑N.@"this" ##@{coPset} ↑N.@"that".
Proof. split; solve_ndisj. Qed.

Lemma test13 E N :
  ↑N ⊆ E →
  ⊤ ∖ E ⊆ ⊤ ∖ (E ∖ ↑N) ∖ ↑N.
Proof. solve_ndisj. Qed.
