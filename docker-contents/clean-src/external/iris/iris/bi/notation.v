From iris.prelude Require Import options.
(** Just reserve the notation. *)

(** * Turnstiles *)
Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P '⊢@{' PROP } Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "(⊢)".
Reserved Notation "'(⊢@{' PROP } )".
Reserved Notation "( P ⊣⊢.)".
Reserved Notation "(.⊣⊢ Q )".

Reserved Notation "P ⊣⊢ Q" (at level 95, no associativity).
Reserved Notation "P '⊣⊢@{' PROP } Q" (at level 95, no associativity).
Reserved Notation "(⊣⊢)".
Reserved Notation "'(⊣⊢@{' PROP } )".
Reserved Notation "(.⊢ Q )".
Reserved Notation "( P ⊢.)".

Reserved Notation "⊢ Q" (at level 20, Q at level 200).
Reserved Notation "'⊢@{' PROP } Q" (at level 20, Q at level 200).
(** The definition must coincide with "'⊢@{' PROP } Q". *)
Reserved Notation "'(⊢@{' PROP } Q )".
(**
Rationale:
Notation [( '⊢@{' PROP } )] prevents parsing [(⊢@{PROP} Q)] using the
[⊢@{PROP} Q] notation; since the latter parse arises from composing two
notations, it is missed by the automatic left-factorization.

To fix that, we force left-factorization by explicitly composing parentheses with
['⊢@{' PROP } Q] into the new notation [( '⊢@{' PROP } Q )],
which successfully undergoes automatic left-factoring. *)


(** * BI connectives *)
Reserved Notation "'emp'".
Reserved Notation "'⌜' φ '⌝'" (at level 1, φ at level 200, format "⌜ φ ⌝").
Reserved Notation "P ∗ Q" (at level 80, right associativity).
Reserved Notation "P -∗ Q"
  (at level 99, Q at level 200, right associativity,
   format "'[' P  '/' -∗  Q ']'").

Reserved Notation "⎡ P ⎤".

(** Modalities *)
Reserved Notation "'<pers>' P" (at level 20, right associativity).
Reserved Notation "'<pers>?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'<pers>?' p  P").

Reserved Notation "▷ P" (at level 20, right associativity).
Reserved Notation "▷? p P" (at level 20, p at level 9, P at level 20,
   format "▷? p  P").
Reserved Notation "▷^ n P" (at level 20, n at level 9, P at level 20,
   format "▷^ n  P").

Reserved Infix "∗-∗" (at level 95, no associativity).

Reserved Notation "'<affine>' P" (at level 20, right associativity).
Reserved Notation "'<affine>?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'<affine>?' p  P").

Reserved Notation "'<absorb>' P" (at level 20, right associativity).
Reserved Notation "'<absorb>?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'<absorb>?' p  P").

Reserved Notation "□ P" (at level 20, right associativity).
Reserved Notation "'□?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'□?' p  P").

Reserved Notation "◇ P" (at level 20, right associativity).

Reserved Notation "■ P" (at level 20, right associativity).
Reserved Notation "■? p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "■? p  P").

Reserved Notation "'<obj>' P" (at level 20, right associativity).
Reserved Notation "'<subj>' P" (at level 20, right associativity).

(** * Update modalities *)
Reserved Notation "|==> Q" (at level 99, Q at level 200, format "|==>  Q").
Reserved Notation "P ==∗ Q"
  (at level 99, Q at level 200, format "'[' P  '/' ==∗  Q ']'").

Reserved Notation "|={ E1 , E2 }=> Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q").
Reserved Notation "P ={ E1 , E2 }=∗ Q"
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "'[' P  '/' ={ E1 , E2 }=∗  Q ']'").

Reserved Notation "|={ E }=> Q"
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }=>  Q").
Reserved Notation "P ={ E }=∗ Q"
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  '/' ={ E }=∗  Q ']'").

(** Step-taking fancy updates *)
Reserved Notation "|={ E1 } [ E2 ]▷=> Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 } [ E2 ]▷=>  Q").
Reserved Notation "P ={ E1 } [ E2 ]▷=∗ Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "'[' P  '/' ={ E1 } [ E2 ]▷=∗  Q ']'").
Reserved Notation "|={ E }▷=> Q"
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }▷=>  Q").
Reserved Notation "P ={ E }▷=∗ Q"
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  '/' ={ E }▷=∗  Q ']'").

(** Multi-step-taking fancy updates *)
Reserved Notation "|={ E1 } [ E2 ]▷=>^ n Q"
  (at level 99, E1, E2 at level 50, n at level 9, Q at level 200,
   format "|={ E1 } [ E2 ]▷=>^ n  Q").
Reserved Notation "P ={ E1 } [ E2 ]▷=∗^ n Q"
  (at level 99, E1, E2 at level 50, n at level 9, Q at level 200,
   format "P  ={ E1 } [ E2 ]▷=∗^ n  Q").
Reserved Notation "|={ E }▷=>^ n Q"
  (at level 99, E at level 50, n at level 9, Q at level 200,
   format "|={ E }▷=>^ n  Q").
Reserved Notation "P ={ E }▷=∗^ n Q"
  (at level 99, E at level 50, n at level 9, Q at level 200,
   format "P  ={ E }▷=∗^ n  Q").

(** * Big Ops *)
Reserved Notation "'[∗' 'list]' k ↦ x ∈ l , P"
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∗  list]  k ↦ x  ∈  l ,  P").
Reserved Notation "'[∗' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∗  list]  x  ∈  l ,  P").

Reserved Notation "'[∗' 'list]' k ↦ x1 ; x2 ∈ l1 ; l2 , P"
  (at level 200, l1, l2 at level 10, k, x1, x2 at level 1, right associativity,
   format "[∗  list]  k ↦ x1 ; x2  ∈  l1 ; l2 ,  P").
Reserved Notation "'[∗' 'list]' x1 ; x2 ∈ l1 ; l2 , P"
  (at level 200, l1, l2 at level 10, x1, x2 at level 1, right associativity,
   format "[∗  list]  x1 ; x2  ∈  l1 ; l2 ,  P").

Reserved Notation "'[∗]' Ps" (at level 20).

Reserved Notation "'[∧' 'list]' k ↦ x ∈ l , P"
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∧  list]  k ↦ x  ∈  l ,  P").
Reserved Notation "'[∧' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∧  list]  x  ∈  l ,  P").

Reserved Notation "'[∧]' Ps" (at level 20).

Reserved Notation "'[∨' 'list]' k ↦ x ∈ l , P"
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∨  list]  k ↦ x  ∈  l ,  P").
Reserved Notation "'[∨' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∨  list]  x  ∈  l ,  P").

Reserved Notation "'[∨]' Ps" (at level 20).

Reserved Notation "'[∗' 'map]' k ↦ x ∈ m , P"
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[∗  map]  k ↦ x  ∈  m ,  P").
Reserved Notation "'[∗' 'map]' x ∈ m , P"
  (at level 200, m at level 10, x at level 1, right associativity,
   format "[∗  map]  x  ∈  m ,  P").

Reserved Notation "'[∗' 'map]' k ↦ x1 ; x2 ∈ m1 ; m2 , P"
  (at level 200, m1, m2 at level 10, k, x1, x2 at level 1, right associativity,
   format "[∗  map]  k ↦ x1 ; x2  ∈  m1 ; m2 ,  P").
Reserved Notation "'[∗' 'map]' x1 ; x2 ∈ m1 ; m2 , P"
  (at level 200, m1, m2 at level 10, x1, x2 at level 1, right associativity,
   format "[∗  map]  x1 ; x2  ∈  m1 ; m2 ,  P").

Reserved Notation "'[∗' 'set]' x ∈ X , P"
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  set]  x  ∈  X ,  P").

Reserved Notation "'[∗' 'mset]' x ∈ X , P"
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  mset]  x  ∈  X ,  P").

(** Define the scope *)
Declare Scope bi_scope.
Delimit Scope bi_scope with I.
