From iris.bi Require Export bi.
From iris.base_logic Require Export derived proofmode algebra.
From iris.prelude Require Import options.

(* The trick of having multiple [uPred] modules, which are all exported in
another [uPred] module is by Jason Gross and described in:
https://sympa.inria.fr/sympa/arc/coq-club/2016-12/msg00069.html *)
Module Import uPred.
  Export base_logic.bi.uPred.
  Export derived.uPred.
  Export bi.bi.
End uPred.
