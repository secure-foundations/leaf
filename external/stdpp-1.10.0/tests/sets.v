From stdpp Require Import sets gmap.

Lemma foo `{Set_ A C} (x : A) (X Y : C) : x ∈ X ∩ Y → x ∈ X.
Proof. intros Hx. set_unfold in Hx. tauto. Qed.

(** Test [set_unfold_list_bind]. *)
Lemma elem_of_list_bind_again {A B} (x : B) (l : list A) f :
  x ∈ l ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ l.
Proof. set_solver. Qed.

(** Should not leave any evars, see issue #163 *)
Goal {[0]} ∪ dom (∅ : gmap nat nat) ≠ ∅.
Proof. set_solver. Qed.

(** Check that [set_solver] works with [set_Exists] and [set_Forall]. Test cases
from issue #178. *)
Lemma set_Exists_set_solver : set_Exists (.= 10) ({[ 10 ]} : gset nat).
Proof. set_solver. Qed.

Lemma set_Forall_set_solver `{Set_ A C} (X : C) x : set_Forall (.≠ x) X ↔ x ∉ X.
Proof. set_solver. Qed.

Lemma set_guard_case_guard `{MonadSet M} `{Decision P} A (x : A) (X : M A) :
  x ∈ (guard P;; X) ↔ P ∧ x ∈ X.
Proof.
  (* Test that [case_guard] works for sets and indeed generates two goals *)
  case_guard; [set_solver|set_solver].
Restart. Proof.
  (* Test that [set_solver] supports [guard]. *)
  set_solver.
Qed.
