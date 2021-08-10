From stdpp Require Import list.
From stdpp Require Import sets.
From stdpp Require Import listset.
Require Import CpdtTactics.

Inductive SetoidSet A :=
| SS (listset A) -> SetoidSet A.

Print listset_intersection.

Print SemiSet.

Print "∈".
