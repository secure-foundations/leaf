From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics monpred.
From iris.base_logic Require Import base_logic lib.fancy_updates.

Section base_logic_tests.
  Context {M : ucmra}.
  Implicit Types P Q R : uPred M.

  (* Test scopes for bupd *)
  Definition use_bupd_uPred (n : nat) : uPred M :=
    □ |==> ∃ m : nat , ⌜ n = 2 ⌝.
  Definition use_plainly_uPred (n : nat) : uPred M :=
    ■ |==> ∃ m : nat , ⌜ n = 2 ⌝.

  (* Test scopes inside big-ops *)
  Definition big_op_scope_uPred_1 (xs : list nat) : uPred M :=
    [∗ list] _ ↦ x ∈ xs, True.
  Definition big_op_scope_uPred_2 (xs : list nat) : uPred M :=
    [∗ list] x; y ∈ xs; xs, True.
  Definition big_op_scope_uPred_3 (m : gmap nat nat) : uPred M :=
    [∗ map] _ ↦ x ∈ m, True.
  Definition big_op_scope_uPred_4 (m : gmap nat nat) : uPred M :=
    [∗ map] x; y ∈ m; m, True.
End base_logic_tests.

Section iris_tests.
  Context `{!invGS_gen hlc Σ}.
  Implicit Types P Q R : iProp Σ.

  (* Test scopes for bupd and fupd *)
  Definition use_bupd_iProp (n : nat) : iProp Σ :=
    □ |==> ∃ m : nat , ⌜ n = 2 ⌝.
  Definition use_fupd_iProp (n : nat) : iProp Σ :=
    □ |={⊤}=> ∃ m : nat , ⌜ n = 2 ⌝.

  (* Test scopes inside big-ops *)
  Definition big_op_scope_iProp_1 (xs : list nat) : iProp Σ :=
    [∗ list] _ ↦ x ∈ xs, True.
  Definition big_op_scope_iProp_2 (xs : list nat) : iProp Σ :=
    [∗ list] x; y ∈ xs; xs, True.
  Definition big_op_scope_iProp_3 (m : gmap nat nat) : iProp Σ :=
    [∗ map] _ ↦ x ∈ m, True.
  Definition big_op_scope_iProp_4 (m : gmap nat nat) : iProp Σ :=
    [∗ map] x; y ∈ m; m, True.
End iris_tests.
