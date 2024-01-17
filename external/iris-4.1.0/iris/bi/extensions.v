(** This file defines various extensions to the base BI interface, via
typeclasses that BIs can optionally implement. *)

From iris.bi Require Export derived_connectives.
From iris.prelude Require Import options.

Class BiAffine (PROP : bi) := absorbing_bi (Q : PROP) : Affine Q.
Global Hint Mode BiAffine ! : typeclass_instances.
Global Existing Instance absorbing_bi | 0.

Class BiPositive (PROP : bi) :=
  bi_positive (P Q : PROP) : <affine> (P ∗ Q) ⊢ <affine> P ∗ Q.
Global Hint Mode BiPositive ! : typeclass_instances.

(** The class [BiLöb] is required for the [iLöb] tactic. However, for most BI
logics [BiLaterContractive] should be used, which gives an instance of [BiLöb]
automatically (see [derived_laws_later]). A direct instance of [BiLöb] is useful
when considering a BI logic with a discrete OFE, instead of an OFE that takes
step-indexing of the logic in account.

The internal/"strong" version of Löb [(▷ P → P) ⊢ P] is derivable from [BiLöb].
It is provided by the lemma [löb] in [derived_laws_later]. *)
Class BiLöb (PROP : bi) :=
  löb_weak (P : PROP) : (▷ P ⊢ P) → (True ⊢ P).
Global Hint Mode BiLöb ! : typeclass_instances.
Global Arguments löb_weak {_ _} _ _.

Class BiLaterContractive (PROP : bi) :=
  later_contractive :> Contractive (bi_later (PROP:=PROP)).

(** The class [BiPersistentlyForall] states that universal quantification
commutes with the persistently modality. The reverse direction of the entailment
described by this type class is derivable, so it is not included. *)
Class BiPersistentlyForall (PROP : bi) :=
  persistently_forall_2 : ∀ {A} (Ψ : A → PROP), (∀ a, <pers> (Ψ a)) ⊢ <pers> (∀ a, Ψ a).
Global Hint Mode BiPersistentlyForall ! : typeclass_instances.

(** The class [BiPureForall] states that universal quantification commutes with
the embedding of pure propositions. The reverse direction of the entailment
described by this type class is derivable, so it is not included.

An instance of [BiPureForall] itself is derivable if we assume excluded middle
in Coq, see the lemma [bi_pure_forall_em] in [derived_laws]. *)
Class BiPureForall (PROP : bi) :=
  pure_forall_2 : ∀ {A} (φ : A → Prop), (∀ a, ⌜ φ a ⌝) ⊢@{PROP} ⌜ ∀ a, φ a ⌝.
Global Hint Mode BiPureForall ! : typeclass_instances.
