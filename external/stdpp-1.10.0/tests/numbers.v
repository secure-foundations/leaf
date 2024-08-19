From stdpp Require Import list.

(** Simple example of measure induction on lists using [Nat.lt_wf_0_projected]. *)
Fixpoint evens {A} (l : list A) : list A :=
  match l with
  | x :: _ :: l => x :: evens l
  | [x] => [x]
  | _ => []
  end.

Fixpoint odds {A} (l : list A) : list A :=
  match l with
  | _ :: y :: l => y :: odds l
  | _ => []
  end.

Lemma lt_wf_projected_induction_sample {A} (l : list A) :
  evens l ++ odds l ≡ₚ l.
Proof.
  (** Note that we do not use [induction .. using ..]. The term
  [Nat.lt_wf_0_projected length l] has type [Acc ..], so we perform induction
  on the [Acc] predicate. *)
  induction (Nat.lt_wf_0_projected length l) as [l _ IH].
  destruct l as [|x [|y l]]; simpl; [done..|].
  rewrite <-Permutation_middle. rewrite IH by (simpl; lia). done.
Qed.
