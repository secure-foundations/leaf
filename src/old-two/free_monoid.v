From iris.proofmode Require Import base.
From iris.algebra Require Import cmra.

Record free (M: Type) : Type := Free {
    free_list : list M
}.
Global Arguments free_list {_}%type_scope _.
   
Global Instance free_equiv `{Equiv M} : Equiv (free M) :=
    λ a b , (free_list a) ≡ₚ (free_list b).

Global Instance free_op {M} : Op (free M) :=
    λ a b , {| free_list := free_list a ++ free_list b |}.
