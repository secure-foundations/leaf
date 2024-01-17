From stdpp Require Export ssreflect.
From iris.prelude Require Import options.

(** Iris itself and many dependencies still rely on this coercion. *)
Coercion Z.of_nat : nat >-> Z.
