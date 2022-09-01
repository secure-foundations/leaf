From Coq.ssr Require Export ssreflect.
From stdpp Require Export prelude.
From iris.prelude Require Import options.
Global Open Scope general_if_scope.
Global Set SsrOldRewriteGoalsOrder. (* See Coq issue #5706 *)
Ltac done := stdpp.tactics.done.

(** Iris itself and many dependencies still rely on this coercion. *)
Coercion Z.of_nat : nat >-> Z.

(* No Hint Mode set in stdpp because of Coq bugs #5735 and #9058, only
fixed in Coq >= 8.12, which Iris depends on. *)
Global Hint Mode Equiv ! : typeclass_instances.
