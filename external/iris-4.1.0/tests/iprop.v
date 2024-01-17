(** Make sure these universe constraints do not conflict with Iris's definition
of [gFunctors]:
See [!782](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/782) *)

From Coq Require Import Logic.Eqdep.

(** A [sigT] that is partially applied and template-polymorphic causes universe
inconsistency errors, which is why [sigT] should be avoided for the definition
of [gFunctors].

The following constructs a partially applied [sigT] that generates bad universe
constraints. This causes a universe inconsistency when [gFunctors] are
to be defined with [sigT]. *)
Definition foo :=
  eq_dep
    ((Type -> Type) -> Type)
    (sigT (A:=Type -> Type)).

From iris.base_logic Require Import iprop.

Lemma bi_ofeO_iProp Σ : bi_ofeO (iPropI Σ) = iPropO Σ.
Proof. reflexivity. Qed.
Lemma bi_cofe_iProp Σ : bi_cofe (iPropI Σ) = @uPred_cofe (iResUR Σ).
Proof. reflexivity. Qed.