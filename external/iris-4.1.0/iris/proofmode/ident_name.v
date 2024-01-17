From stdpp Require Import base.
From iris.prelude Require Import options.

(** [ident_name] is a way to remember an identifier within the binder of a
(trivial) function, which can be constructed and retrieved with Ltac but is easy
to forward around opaquely in Gallina (through typeclasses, for example) *)
Definition ident_name := unit → unit.

(** [to_ident_name id] returns a constr of type [ident_name] that holds [id] in
the binder name *)
Ltac to_ident_name id :=
  eval cbv in (ltac:(clear; intros id; assumption) : unit → unit).

(** to_ident_name is a Gallina-level version of [to_ident_name] for constructing
    [ident_name] literals. *)
Notation to_ident_name id := (λ id:unit, id) (only parsing).

(** The idea of [AsIdentName] is to convert the binder in [f] to an [ident_name]
representing the name of the binder. If [f] is not a lambda, this typeclass can
produce the fallback identifier [__unknown]. For example, if the user writes
[bi_exist Φ], there is no binder anywhere to extract.

This class has only one instance, a [Hint Extern] which implements that
conversion to resolve [name] in Ltac (see [solve_as_ident_name]). *)
Class AsIdentName {A B} (f : A → B) (name : ident_name) := as_ident_name {}.
Global Arguments as_ident_name {A B f} name : assert.

Ltac solve_as_ident_name :=
  lazymatch goal with
  (* The [H] here becomes the default name if the binder is anonymous. We use
     [H] with the idea that an unnamed and unused binder is likely to be a
     proposition. *)
  | |- AsIdentName (λ H, _) _ =>
    let name := to_ident_name H in
    notypeclasses refine (as_ident_name name)
  | |- AsIdentName _ _ =>
     let name := to_ident_name ident:(__unknown) in
     notypeclasses refine (as_ident_name name)
  | |- _ => fail "solve_as_ident_name: goal should be `AsIdentName`"
  end.

Global Hint Extern 1 (AsIdentName _ _) => solve_as_ident_name : typeclass_instances.
