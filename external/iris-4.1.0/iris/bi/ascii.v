From iris.bi Require Import interface derived_connectives updates.
From iris.prelude Require Import options.

Notation "P |- Q" := (P ⊢ Q)
  (at level 99, Q at level 200, right associativity, only parsing) : stdpp_scope.
Notation "P '|-@{' PROP } Q" := (P ⊢@{PROP} Q)
  (at level 99, Q at level 200, right associativity, only parsing)
  : stdpp_scope.
Notation "(|-)" := (⊢) (only parsing) : stdpp_scope.
Notation "'(|-@{' PROP } )" := (⊢@{PROP}) (only parsing) : stdpp_scope.

Notation "|- Q" := (⊢ Q%I) (at level 20, Q at level 200, only parsing) : stdpp_scope.
Notation "'|-@{' PROP } Q" := (⊢@{PROP} Q) (at level 20, Q at level 200, only parsing) : stdpp_scope.
(** Work around parsing issues: see [notation.v] for details. *)
Notation "'(|-@{' PROP } Q )" := (⊢@{PROP} Q) (only parsing) : stdpp_scope.

Notation "P -|- Q" := (P ⊣⊢ Q) (at level 95, no associativity, only parsing) : stdpp_scope.
Notation "P '-|-@{' PROP } Q" := (P ⊣⊢@{PROP} Q)
  (at level 95, no associativity, only parsing) : stdpp_scope.
Notation "(-|-)" := (⊣⊢) (only parsing) : stdpp_scope.
Notation "'(-|-@{' PROP } )" := (⊣⊢@{PROP}) (only parsing) : stdpp_scope.

Notation "P -* Q" := (P ⊢ Q)%stdpp
  (at level 99, Q at level 200, right associativity, only parsing)
  : stdpp_scope.

(* FIXME: Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp) : bi_scope. *)
Notation "P /\ Q" := (P ∧ Q)%I (only parsing) : bi_scope.
Notation "(/\)" := bi_and (only parsing) : bi_scope.
Notation "P \/ Q" := (P ∨ Q)%I (only parsing) : bi_scope.
Notation "(\/)" := bi_or (only parsing) : bi_scope.
Notation "P -> Q" := (P → Q)%I (only parsing) : bi_scope.
Notation "~ P" := (P → False)%I (only parsing) : bi_scope.

Notation "P ** Q" := (P ∗ Q)%I
  (at level 80, right associativity, only parsing) : bi_scope.
Notation "(**)" := bi_sep (only parsing) : bi_scope.
Notation "P -* Q" := (P -∗ Q)%I
  (at level 99, Q at level 200, right associativity, only parsing) : bi_scope.

(* ∀ x .. y , P *)
Notation "'forall' x .. y , P" :=
  (bi_forall (fun x => .. (bi_forall (fun y => P%I)) ..))
  (at level 200, x binder, right associativity, only parsing) : bi_scope.
(* ∃ x .. y , P *)
Notation "'exists' x .. y , P" :=
  (bi_exist (fun x => .. (bi_exist (fun y => P%I)) ..))
  (at level 200, x binder, right associativity, only parsing) : bi_scope.

Notation "|> P" := (▷ P)%I
  (at level 20, right associativity, only parsing) : bi_scope.
Notation "|>? p P" := (▷?p P)%I (at level 20, p at level 9, P at level 20,
   only parsing) : bi_scope.
Notation "|>^ n P" := (▷^n P)%I (at level 20, n at level 9, P at level 20,
   only parsing) : bi_scope.

Notation "P <-> Q" := (P ↔ Q)%I
  (at level 95, no associativity, only parsing) : bi_scope.

Notation "P *-* Q" := (P ∗-∗ Q)%I
  (at level 95, no associativity, only parsing) : bi_scope.

Notation "'<#>' P" := (□ P)%I
  (at level 20, right associativity, only parsing) : bi_scope.
Notation "'<#>?' p P" := (□?p P)%I (at level 20, p at level 9, P at level 20,
   right associativity, only parsing) : bi_scope.

Notation "'<except_0>' P" := (◇ P)%I
  (at level 20, right associativity, only parsing) : bi_scope.

Notation "mP -*? Q" := (mP -∗? Q)%I
  (at level 99, Q at level 200, right associativity, only parsing) : bi_scope.

Notation "P ==* Q" := (P ==∗ Q)%stdpp
  (at level 99, Q at level 200, only parsing) : stdpp_scope.
Notation "P ==* Q" := (P ==∗ Q)%I
  (at level 99, Q at level 200, only parsing) : bi_scope.

Notation "P ={ E1 , E2 }=* Q" := (P ={E1,E2}=∗ Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200, only parsing) : bi_scope.
Notation "P ={ E1 , E2 }=* Q" := (P ={E1,E2}=∗ Q)
  (at level 99, E1,E2 at level 50, Q at level 200, only parsing) : stdpp_scope.

Notation "P ={ E }=* Q" := (P ={E}=∗ Q)%I
  (at level 99, E at level 50, Q at level 200, only parsing) : bi_scope.
Notation "P ={ E }=* Q" := (P ={E}=∗ Q)
  (at level 99, E at level 50, Q at level 200, only parsing) : stdpp_scope
.

Notation "P ={ E1 } [ E2 ]|>=* Q" := (P ={E1}[E2]▷=∗ Q)
  (at level 99, E1,E2 at level 50, Q at level 200, only parsing) : stdpp_scope.
Notation "P ={ E1 } [ E2 ]|>=* Q" := (P ={E1}[E2]▷=∗ Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200, only parsing) : bi_scope.

Notation "|={ E }|>=> Q" := (|={E}▷=> Q)%I
  (at level 99, E at level 50, Q at level 200, only parsing) : bi_scope.
Notation "P ={ E }|>=* Q" := (P ={E}▷=∗ Q)%I
  (at level 99, E at level 50, Q at level 200, only parsing) : bi_scope.
Notation "|={ E1 } [ E2 ]|>=>^ n Q" := (|={E1}[E2]▷=>^n Q)%I
  (at level 99, E1,E2 at level 50, n at level 9, Q at level 200, only parsing)
  : bi_scope.
Notation "P ={ E1 } [ E2 ]|>=*^ n Q" := (P ={E1}[E2]▷=∗^n Q)%I
  (at level 99, E1,E2 at level 50, n at level 9, Q at level 200, only parsing)
   : stdpp_scope.
Notation "P ={ E1 } [ E2 ]|>=*^ n Q" := (P ={E1}[E2]▷=∗^n Q)%I
  (at level 99, E1,E2 at level 50, n at level 9, Q at level 200, only parsing)
  : bi_scope.
