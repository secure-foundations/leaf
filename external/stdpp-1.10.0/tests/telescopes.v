From stdpp Require Import tactics telescopes.

Local Unset Mangle Names. (* for stable goal printing *)

Section universes.
(** This test would fail without [Unset Universe Minimization ToSet] in [telescopes.v]. *)
Lemma texist_exist_universes (X : Type) (P : TeleS (λ _ : X, TeleO) → Prop) :
  texist P ↔ ex P.
Proof. by rewrite texist_exist. Qed.

(** [tele_arg t] should live at the same universe
as the types inside of [t] because [tele_arg t]
is essentially just a (dependent) product.
 *)
Definition no_bump@{u} (t : tele@{u}) : Type@{u} := tele_arg@{u} t.

(* Assert that telescopes are cumulatively universe polymorphic.
   See https://gitlab.mpi-sws.org/iris/iris/-/issues/461
 *)
Section cumulativity.
Monomorphic Universes Quant local.
Monomorphic Constraint local < Quant.
Example cumul (t : tele@{local}) : tele@{Quant} := t.
End cumulativity.
End universes.

Section accessor.
(* This is like Iris' accessors, but in Prop.  Just to play with telescopes. *)
Definition accessor {X : tele} (α β γ : X → Prop) : Prop :=
  ∃.. x, α x ∧ (β x → γ x).

(* Working with abstract telescopes. *)
Section tests.
Context {X : tele}.
Implicit Types α β γ : X → Prop.

Lemma acc_mono α β γ1 γ2 :
  (∀.. x, γ1 x → γ2 x) →
  accessor α β γ1 → accessor α β γ2.
Proof.
  unfold accessor. rewrite tforall_forall, !texist_exist.
  intros Hγ12 Hacc. destruct Hacc as [x' [Hα Hclose]]. exists x'.
  split; [done|]. intros Hβ. apply Hγ12, Hclose. done.
Qed.

Lemma acc_mono_disj α β γ1 γ2 :
  accessor α β γ1 → accessor α β (λ.. x, γ1 x ∨ γ2 x).
Proof.
  Show.
  apply acc_mono. Show.
  rewrite tforall_forall. intros x Hγ. rewrite tele_app_bind. Show.
  left. done.
Qed.
End tests.
End accessor.

(* Type inference for tele_app-based notation.
(Relies on [&] bidirectionality hint of tele_app.) *)
Definition test {TT : tele} (t : TT → Prop) : Prop :=
  ∀.. x, t x ∧ t x.
Notation "'[TEST'  x .. z ,  P ']'" :=
  (test (TT:=(TeleS (fun x => .. (TeleS (fun z => TeleO)) ..)))
        (tele_app (λ x, .. (λ z, P) ..)))
  (x binder, z binder).
Check [TEST (x y : nat), x = y].

(** [tele_arg ..] notation tests.
    These tests mainly test type annotations and casts in the [tele_arg]
    notations.
    We test that Coq can typecheck literal telescope arguments in two ways:
    - tactic unification/old unification using [exact]
    - evarconv/new unification using [refine]
 *)
Example tele_arg_notation_0 : [tele].
assert_succeeds exact [tele_arg].
assert_succeeds refine [tele_arg].
Abort.

Example tele_arg_notation_1 : [tele (_:nat)].
assert_succeeds exact [tele_arg 0].
assert_succeeds refine [tele_arg 0].
Abort.

Example tele_arg_notation_2 : [tele (_ : bool) (_ : nat)].
assert_succeeds exact [tele_arg true; 0].
assert_succeeds refine [tele_arg true; 0].
Abort.

Example tele_arg_notation_2_dep : [tele (b : bool) (_ : if b then nat else False)].
assert_succeeds exact [tele_arg true; 0].
assert_succeeds refine [tele_arg true; 0].
Abort.
