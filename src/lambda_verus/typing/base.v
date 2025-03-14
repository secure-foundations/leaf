From Coq.Program Require Import Tactics.
From lrust.lang Require Export proofmode.

(* Last, so that we make sure we shadow the defintion of delete for
   sets coming from the prelude. *)
From lrust.lang.lib Require Export new_delete.

Open Scope Z_scope.

Create HintDb lrust_typing.
Create HintDb lrust_typing_merge.

(* We first try to solve everything without the merging rules, and
   then start from scratch with them.

   The reason is that we want we want the search proof search for
   [tctx_extract_hasty] to suceed even if the type is an evar, and
   merging makes it diverge in this case. *)
Ltac solve_typing :=
  (typeclasses eauto with lrust_typing typeclass_instances core; fail) ||
  (typeclasses eauto with lrust_typing lrust_typing_merge typeclass_instances core; fail).

Global Hint Constructors Forall Forall2 elem_of_list : lrust_typing.
Global Hint Resolve submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : lrust_typing.

Global Hint Extern 1 (@eq nat _ (Z.to_nat _)) =>
  (etrans; [symmetry; exact: Nat2Z.id | reflexivity]) : lrust_typing.
Global Hint Extern 1 (@eq nat (Z.to_nat _) _) =>
  (etrans; [exact: Nat2Z.id | reflexivity]) : lrust_typing.

Global Hint Resolve <- elem_of_app : lrust_typing.

(* done is there to handle equalities with constants *)
Global Hint Extern 100 (_ ≤ _) => simpl; first [done|lia] : lrust_typing.
Global Hint Extern 100 (@eq Z _ _) => simpl; first [done|lia] : lrust_typing.
Global Hint Extern 100 (@eq nat _ _) => simpl; first [done|lia] : lrust_typing.
