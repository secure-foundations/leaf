From iris.bi Require Export derived_laws derived_laws_later big_op.
From iris.bi Require Export updates internal_eq plainly embedding.
From iris.prelude Require Import options.

Module Import bi.
  (** Get universes into the desired scope *)
  Universe Logic.
  Constraint Logic = bi.interface.universes.Logic.
  Universe Quant.
  Constraint Quant = bi.interface.universes.Quant.
  (** Get other symbols into the desired scope *)
  Export bi.interface.bi.
  Export bi.derived_laws.bi.
  Export bi.derived_laws_later.bi.
End bi.
