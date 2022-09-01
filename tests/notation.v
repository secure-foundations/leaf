From stdpp Require Import base tactics fin_maps gmultiset.

(** Test parsing of variants of [(≡)] notation. *)
Lemma test_equiv_annot_sections `{!Equiv A, !Equivalence (≡@{A})} (x : A) :
  x ≡@{A} x ∧ (≡@{A}) x x ∧ (x ≡.) x ∧ (.≡ x) x ∧
  ((x ≡@{A} x)) ∧ ((≡@{A})) x x ∧ ((x ≡.)) x ∧ ((.≡ x)) x ∧
  ( x ≡@{A} x) ∧ ( x ≡.) x ∧
  (x ≡@{A} x ) ∧ (≡@{A} ) x x ∧ (.≡ x ) x.
Proof. naive_solver. Qed.

(** Test that notations for maps with multiple elements can be parsed and printed correctly. *)
Section map_notations.
  Context `{FinMap nat M}.

  Definition test_2 : M (M nat) := {[ 10 := {[ 10 := 1 ]}; 20 := {[ 20 := 2]} ]}.
  Definition test_3 : M (M nat) := {[ 10 := {[ 10 := 1 ]}; 20 := {[ 20 := 2]};
    30 := {[ 30 := 3]} ]}.
  Definition test_4 : M (M nat) := {[ 10 := {[ 10 := 1 ]}; 20 := {[ 20 := 2]};
    30 := {[ 30 := 3]}; 40 := {[ 40 := 4 ]} ]}.

  Definition test_op_2 : M (M nat) := {[ 10 := {[pow 10 2 := 99]};
    10 + 1 := {[ 10 - 100 := 42 * 1337 ]} ]}.

  Definition test_op_3 : M (M (list nat)) := {[ 10 := {[ 20 - 2 := [11]; 1 := [22] ]};
    20 := {[ 99 + length ([1]) := [1;2;3] ]}; 4 := {[ 4:=[4] ]} ; 5 := {[ 5 := [5] ]} ]}.

  Definition test_op_4 : M (M (list nat)) :=
    ({[ 10 := {[ 20 - 2 := [11]; 1 := [22]; 3 := [23]; 4:=[1;2;3;4;5;6;7;8;9]]};
      20 := {[ 99 + length ([1]) := [1;2;3] ]}; 4 := {[ 4:=[4] ]} ; 5 := {[ 5 := [5] ]} ]}).

  Print test_2.
  Print test_3.
  Print test_4.
  Print test_op_2.
  Print test_op_3.
  Print test_op_4.
End map_notations.

(** Test that notations for maps with multiple elements can be parsed and printed correctly. *)
Section multiset_notations.
  Definition test_gmultiset_1 : gmultiset nat := {[+ 10 +]}.
  Definition test_gmultiset_2 : gmultiset nat := {[+ 10; 11 +]}.
  Definition test_gmultiset_3 : gmultiset nat := {[+ 10; 11; 2 - 2 +]}.
  Definition test_gmultiset_4 : gmultiset (gmultiset nat) :=
    {[+ {[+ 10 +]}; ∅; {[+ 2 - 2; 10 +]} +]}.

  Print test_gmultiset_1.
  Print test_gmultiset_2.
  Print test_gmultiset_3.
  Print test_gmultiset_4.
End multiset_notations.