From stdpp Require Import tactics strings.
Unset Mangle Names.

Section test.
  Context (section_variable : nat).

  Axiom axiom : nat.

  Check "is_closed_term_test".
  Lemma is_closed_term_test :
    ∀ x y (P : Prop),
      let a := 10 in
      a = a →
      let b := (a + 11) in
      x + y = y + x.
  Proof.
    intros x y P a H b.
    (* Constructors are closed. *)
    is_closed_term 1.

    (* Functions on closed terms are closed. *)
    is_closed_term (1 + 1).

    (* Variables bound in the context are not closed. *)
    Fail is_closed_term x.
    Fail is_closed_term (x + 1).
    Fail is_closed_term (x + y).

    (* Section variables are not closed. *)
    Fail is_closed_term section_variable.
    Fail is_closed_term (section_variable + 1).

    (* Axioms are considered closed. (Arguably this is a bug, but
    there is nothing we can do about it.) *)
    is_closed_term axiom.
    is_closed_term (axiom + 1).

    (* Let-bindings are considered closed. *)
    is_closed_term a.
    is_closed_term (a + 1).
    is_closed_term b.
    is_closed_term (b + 1).

    (* is_closed_term also works for propositions. *)
    is_closed_term True.
    is_closed_term (True ∧ True).
    Fail is_closed_term P.
    Fail is_closed_term (P ∧ True).

    lia.
  Qed.
End test.
