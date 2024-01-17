From stdpp Require Import list.

(** Test that Coq does not infer [x ∈ xs] as [False] by eagerly using
[False_dec] on a goal with unresolved type class instances. *)
Example issue_165 (x : nat) :
  ¬ ∃ xs : list nat, (guard (x ∈ xs); Some x) ≠ None.
Proof.
  intros [xs Hxs]. case_option_guard; [|done].
  Fail done. (* Would succeed if the instance backing [x ∈ xs] is infered as
  [False]. *)
Abort.
