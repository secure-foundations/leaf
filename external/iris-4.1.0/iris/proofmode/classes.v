From stdpp Require Import namespaces.
From iris.bi Require Export bi.
From iris.proofmode Require Import base.
From iris.proofmode Require Export ident_name modalities.
From iris.prelude Require Import options.
Import bi.

(** Use this as precondition on "failing" instances of typeclasses that have
pure preconditions (such as [ElimModal]), if you want a nice error to be shown
when this instances is picked as part of some proof mode tactic. *)
Inductive pm_error (s : string) := .

Class FromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
  from_assumption : □?p P ⊢ Q.
Global Arguments FromAssumption {_} _ _%I _%I : simpl never.
Global Arguments from_assumption {_} _ _%I _%I {_}.
Global Hint Mode FromAssumption + + - - : typeclass_instances.

Class KnownLFromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
  knownl_from_assumption :> FromAssumption p P Q.
Global Arguments KnownLFromAssumption {_} _ _%I _%I : simpl never.
Global Arguments knownl_from_assumption {_} _ _%I _%I {_}.
Global Hint Mode KnownLFromAssumption + + ! - : typeclass_instances.

Class KnownRFromAssumption {PROP : bi} (p : bool) (P Q : PROP) :=
  knownr_from_assumption :> FromAssumption p P Q.
Global Arguments KnownRFromAssumption {_} _ _%I _%I : simpl never.
Global Arguments knownr_from_assumption {_} _ _%I _%I {_}.
Global Hint Mode KnownRFromAssumption + + - ! : typeclass_instances.

Class IntoPure {PROP : bi} (P : PROP) (φ : Prop) :=
  into_pure : P ⊢ ⌜φ⌝.
Global Arguments IntoPure {_} _%I _%type_scope : simpl never.
Global Arguments into_pure {_} _%I _%type_scope {_}.
Global Hint Mode IntoPure + ! - : typeclass_instances.

(* [IntoPureT] is a variant of [IntoPure] with the argument in [Type] to avoid
some shortcoming of unification in Coq's type class search. An example where we
use this workaround is to repair the following instance:

  Global Instance into_exist_and_pure P Q (φ : Prop) :
    IntoPure P φ → IntoExist (P ∧ Q) (λ _ : φ, Q).

Coq is unable to use this instance: [class_apply] -- which is used by type class
search -- fails with the error that it cannot unify [Prop] and [Type]. This is
probably caused because [class_apply] uses an ancient unification algorith. The
[refine] tactic -- which uses a better unification algorithm -- succeeds to
apply the above instance.

Since we do not want to define [Hint Extern] declarations using [refine] for
any instance like [into_exist_and_pure], we factor this out in the class
[IntoPureT]. This way, we only have to declare a [Hint Extern] using [refine]
once, and use [IntoPureT] in any instance like [into_exist_and_pure].

TODO: Report this as a Coq bug, or wait for https://github.com/coq/coq/pull/991
to be finished and merged someday. *)
Class IntoPureT {PROP : bi} (P : PROP) (φ : Type) :=
  into_pureT : ∃ ψ : Prop, φ = ψ ∧ IntoPure P ψ.
Lemma into_pureT_hint {PROP : bi} (P : PROP) (φ : Prop) : IntoPure P φ → IntoPureT P φ.
Proof. by exists φ. Qed.
Global Hint Extern 0 (IntoPureT _ _) =>
  notypeclasses refine (into_pureT_hint _ _ _) : typeclass_instances.

(** [FromPure a P φ] is used when introducing a pure assertion. It is used by
[iPureIntro] and the [[%]] specialization pattern.

The Boolean [a] specifies whether introduction of [P] needs [emp] in addition
to [φ]. Concretely, for the [iPureIntro] tactic, this means it specifies whether
the spatial context should be empty or not.

Note that the Boolean [a] is not needed for the (dual) [IntoPure] class, because
there we can just ask that [P] is [Affine]. *)
Class FromPure {PROP : bi} (a : bool) (P : PROP) (φ : Prop) :=
  from_pure : <affine>?a ⌜φ⌝ ⊢ P.
Global Arguments FromPure {_} _ _%I _%type_scope : simpl never.
Global Arguments from_pure {_} _ _%I _%type_scope {_}.
Global Hint Mode FromPure + - ! - : typeclass_instances.

Class FromPureT {PROP : bi} (a : bool) (P : PROP) (φ : Type) :=
  from_pureT : ∃ ψ : Prop, φ = ψ ∧ FromPure a P ψ.
Lemma from_pureT_hint {PROP : bi} (a : bool) (P : PROP) (φ : Prop) :
  FromPure a P φ → FromPureT a P φ.
Proof. by exists φ. Qed.
Global Hint Extern 0 (FromPureT _ _ _) =>
  notypeclasses refine (from_pureT_hint _ _ _ _) : typeclass_instances.

Class IntoInternalEq `{BiInternalEq PROP} {A : ofe} (P : PROP) (x y : A) :=
  into_internal_eq : P ⊢ x ≡ y.
Global Arguments IntoInternalEq {_ _ _} _%I _%type_scope _%type_scope : simpl never.
Global Arguments into_internal_eq {_ _ _} _%I _%type_scope _%type_scope {_}.
Global Hint Mode IntoInternalEq + - - ! - - : typeclass_instances.

Class IntoPersistent {PROP : bi} (p : bool) (P Q : PROP) :=
  into_persistent : <pers>?p P ⊢ <pers> Q.
Global Arguments IntoPersistent {_} _ _%I _%I : simpl never.
Global Arguments into_persistent {_} _ _%I _%I {_}.
Global Hint Mode IntoPersistent + + ! - : typeclass_instances.

(** The [FromModal φ M sel P Q] class is used by the [iModIntro] tactic to
transform a goal [P] into a modality [M] and proposition [Q], under additional
pure assumptions [φ].

The inputs are [P] and [sel] and the outputs are [M] and [Q].

The input [sel] can be used to specify which modality to introduce in case there
are multiple choices to turn [P] into a modality. For example, given [⎡|==> R⎤],
[sel] can be either [|==> ?e] or [⎡ ?e ⎤], which turn it into an update modality
or embedding, respectively. In case there is no need to specify the modality to
introduce, [sel] should be an evar.

For modalities [N] that do not need to augment the proof mode environment, one
can define an instance [FromModal True modality_id (N P) P]. Defining such an
instance only imposes the proof obligation [P ⊢ N P]. Examples of such
modalities [N] are [bupd], [fupd], [except_0], [monPred_subjectively] and
[bi_absorbingly]. *)
Class FromModal {PROP1 PROP2 : bi} {A}
    (φ : Prop) (M : modality PROP1 PROP2) (sel : A) (P : PROP2) (Q : PROP1) :=
  from_modal : φ → M Q ⊢ P.
Global Arguments FromModal {_ _ _} _ _ _%I _%I _%I : simpl never.
Global Arguments from_modal {_ _ _} _ _ _ _%I _%I {_}.
Global Hint Mode FromModal - + - - - - ! - : typeclass_instances.

(** The [FromAffinely P Q] class is used to add an [<affine>] modality to the
proposition [Q].

The input is [Q] and the output is [P]. *)
Class FromAffinely {PROP : bi} (P Q : PROP) :=
  from_affinely : <affine> Q ⊢ P.
Global Arguments FromAffinely {_} _%I _%I : simpl never.
Global Arguments from_affinely {_} _%I _%I {_}.
Global Hint Mode FromAffinely + - ! : typeclass_instances.

(** The [IntoAbsorbingly P Q] class is used to add an [<absorb>] modality to
the proposition [Q].

The input is [Q] and the output is [P]. *)
Class IntoAbsorbingly {PROP : bi} (P Q : PROP) :=
  into_absorbingly : P ⊢ <absorb> Q.
Global Arguments IntoAbsorbingly {_} _%I _%I.
Global Arguments into_absorbingly {_} _%I _%I {_}.
Global Hint Mode IntoAbsorbingly + - ! : typeclass_instances.

(** Converting an assumption [R] into a wand [P -∗ Q] is done in three stages:

- Strip modalities and universal quantifiers of [R] until an arrow or a wand
  has been obtained.
- Balance modalities in the arguments [P] and [Q] to match the goal (which used
  for [iApply]) or the premise (when used with [iSpecialize] and a specific
  hypothesis).
- Instantiate the premise of the wand or implication. *)
Class IntoWand {PROP : bi} (p q : bool) (R P Q : PROP) :=
  into_wand : □?p R ⊢ □?q P -∗ Q.
Global Arguments IntoWand {_} _ _ _%I _%I _%I : simpl never.
Global Arguments into_wand {_} _ _ _%I _%I _%I {_}.
Global Hint Mode IntoWand + + + ! - - : typeclass_instances.

Class IntoWand' {PROP : bi} (p q : bool) (R P Q : PROP) :=
  into_wand' : IntoWand p q R P Q.
Global Arguments IntoWand' {_} _ _ _%I _%I _%I : simpl never.
Global Hint Mode IntoWand' + + + ! ! - : typeclass_instances.
Global Hint Mode IntoWand' + + + ! - ! : typeclass_instances.

Class FromWand {PROP : bi} (P Q1 Q2 : PROP) := from_wand : (Q1 -∗ Q2) ⊢ P.
Global Arguments FromWand {_} _%I _%I _%I : simpl never.
Global Arguments from_wand {_} _%I _%I _%I {_}.
Global Hint Mode FromWand + ! - - : typeclass_instances.

Class FromImpl {PROP : bi} (P Q1 Q2 : PROP) := from_impl : (Q1 → Q2) ⊢ P.
Global Arguments FromImpl {_} _%I _%I _%I : simpl never.
Global Arguments from_impl {_} _%I _%I _%I {_}.
Global Hint Mode FromImpl + ! - - : typeclass_instances.

Class FromSep {PROP : bi} (P Q1 Q2 : PROP) := from_sep : Q1 ∗ Q2 ⊢ P.
Global Arguments FromSep {_} _%I _%I _%I : simpl never.
Global Arguments from_sep {_} _%I _%I _%I {_}.
Global Hint Mode FromSep + ! - - : typeclass_instances. (* For iSplit{L,R} *)

Class FromAnd {PROP : bi} (P Q1 Q2 : PROP) := from_and : Q1 ∧ Q2 ⊢ P.
Global Arguments FromAnd {_} _%I _%I _%I : simpl never.
Global Arguments from_and {_} _%I _%I _%I {_}.
Global Hint Mode FromAnd + ! - - : typeclass_instances.

(** The [IntoAnd p P Q1 Q2] class is used to handle some [[H1 H2]] intro
patterns:
- [IntoAnd true] is used for such patterns in the intuitionistic context
- [IntoAnd false] is used for such patterns where one of the two sides is
  discarded (e.g. [[_ H]]) or where the left-hand side is pure as in [[% H]]
  (via an [IntoExist] fallback).

The inputs are [p P] and the outputs are [Q1 Q2]. *)
Class IntoAnd {PROP : bi} (p : bool) (P Q1 Q2 : PROP) :=
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2).
Global Arguments IntoAnd {_} _ _%I _%I _%I : simpl never.
Global Arguments into_and {_} _ _%I _%I _%I {_}.
Global Hint Mode IntoAnd + + ! - - : typeclass_instances.

(** The [IntoSep P Q1 Q2] class is used to handle [[H1 H2]] intro patterns in
the spatial context, except:
- when one side is [_], then [IntoAnd] is tried first (but [IntoSep] is used as
  fallback)
- when the left-hand side is [%], then [IntoExist] is used)

The input is [P] and the outputs are [Q1 Q2]. *)
Class IntoSep {PROP : bi} (P Q1 Q2 : PROP) :=
  into_sep : P ⊢ Q1 ∗ Q2.
Global Arguments IntoSep {_} _%I _%I _%I : simpl never.
Global Arguments into_sep {_} _%I _%I _%I {_}.
Global Hint Mode IntoSep + ! - - : typeclass_instances.

Class FromOr {PROP : bi} (P Q1 Q2 : PROP) := from_or : Q1 ∨ Q2 ⊢ P.
Global Arguments FromOr {_} _%I _%I _%I : simpl never.
Global Arguments from_or {_} _%I _%I _%I {_}.
Global Hint Mode FromOr + ! - - : typeclass_instances.

Class IntoOr {PROP : bi} (P Q1 Q2 : PROP) := into_or : P ⊢ Q1 ∨ Q2.
Global Arguments IntoOr {_} _%I _%I _%I : simpl never.
Global Arguments into_or {_} _%I _%I _%I {_}.
Global Hint Mode IntoOr + ! - - : typeclass_instances.

Class FromExist {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :=
  from_exist : (∃ x, Φ x) ⊢ P.
Global Arguments FromExist {_ _} _%I _%I : simpl never.
Global Arguments from_exist {_ _} _%I _%I {_}.
Global Hint Mode FromExist + - ! - : typeclass_instances.

Class IntoExist {PROP : bi} {A} (P : PROP) (Φ : A → PROP) (name: ident_name) :=
  into_exist : P ⊢ ∃ x, Φ x.
Global Arguments IntoExist {_ _} _%I _%I _ : simpl never.
Global Arguments into_exist {_ _} _%I _%I _ {_}.
Global Hint Mode IntoExist + - ! - - : typeclass_instances.

Class IntoForall {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :=
  into_forall : P ⊢ ∀ x, Φ x.
Global Arguments IntoForall {_ _} _%I _%I : simpl never.
Global Arguments into_forall {_ _} _%I _%I {_}.
Global Hint Mode IntoForall + - ! - : typeclass_instances.

Class FromForall {PROP : bi} {A} (P : PROP) (Φ : A → PROP) (name : ident_name) :=
  from_forall : (∀ x, Φ x) ⊢ P.
Global Arguments FromForall {_ _} _%I _%I _ : simpl never.
Global Arguments from_forall {_ _} _%I _%I _ {_}.
Global Hint Mode FromForall + - ! - - : typeclass_instances.

Class IsExcept0 {PROP : bi} (Q : PROP) := is_except_0 : ◇ Q ⊢ Q.
Global Arguments IsExcept0 {_} _%I : simpl never.
Global Arguments is_except_0 {_} _%I {_}.
Global Hint Mode IsExcept0 + ! : typeclass_instances.

(** [CombineSepAs], [MaybeCombineSepAs] and [CombineSepGives] are all used for
  the [iCombine] tactic.

These three classes take two hypotheses [P] and [Q] as input, and return a
(possibly simplified) new hypothesis [R]. [CombineSepAs P Q R] means that [R]
may be obtained by deleting both [P] and [Q], and that [R] is not a trivial
combination. [MaybeCombineSepAs P Q R progress] is like [CombineSepAs], but
[R] can be the trivial combination [P ∗ Q], and the [progress] parameter 
indicates whether this trivial combination is used. [CombineSepGives P Q R] 
means that [□ R] may be obtained 'for free' from [P] and [Q]. The result [R] of 
[CombineSepAs] and [MaybeCombineSepAs] will not contain the observations 
from [CombineSepGives].

We deliberately use separate typeclasses [CombineSepAs] and [CombineSepGives].
This allows one to (1) combine hypotheses and get additional persistent
information, (2) only combine the hypotheses, without the additional persistent
information, (3) only get the additional persistent information, while keeping
the original hypotheses. A possible alternative would have been something like
[CombineSepAsGives P1 P2 P R := combine_as_gives : P1 ∗ P2 ⊢ P ∗ □ R],
but this was deemed to be harder to use. Specifically, this would force you to
always specify both [P] and [R], even though one might only have a good
candidate for [P], but not [R], or the other way around.

Note that [FromSep] and [CombineSepAs] have nearly the same definition. However,
they have different Hint Modes and are used for different tactics. [FromSep] is
used to compute the two new goals obtained after applying [iSplitL]/[iSplitR],
taking the current goal as input. [CombineSepAs] is used to combine two
hypotheses into one.

In terms of costs, note that the [AsFractional] instance for [CombineSepAs]
has cost 50. If that instance should take priority over yours, make sure to use
a higher cost. *)
Class CombineSepAs {PROP : bi} (P Q R : PROP) := combine_sep_as : P ∗ Q ⊢ R.
Global Arguments CombineSepAs {_} _%I _%I _%I : simpl never.
Global Arguments combine_sep_as {_} _%I _%I _%I {_}.
Global Hint Mode CombineSepAs + ! ! - : typeclass_instances.

(** The [progress] parameter is of the following [progress_indicator] type: *)
Inductive progress_indicator := MadeProgress | NoProgress.
(** This aims to make [MaybeCombineSepAs] instances easier to read than if we
had used Booleans. [NoProgress] indicates that the default instance
[maybe_combine_sep_as_default] below has been used, while [MadeProgress]
indicates that a [CombineSepAs] instance was used. *)
Class MaybeCombineSepAs {PROP : bi}
    (P Q R : PROP) (progress : progress_indicator) :=
  maybe_combine_sep_as : P ∗ Q ⊢ R.
Global Arguments MaybeCombineSepAs {_} _%I _%I _%I _ : simpl never.
Global Arguments maybe_combine_sep_as {_} _%I _%I _%I _ {_}.
Global Hint Mode MaybeCombineSepAs + ! ! - - : typeclass_instances.

Global Instance maybe_combine_sep_as_combine_sep_as {PROP : bi} (R P Q : PROP) :
  CombineSepAs P Q R → MaybeCombineSepAs P Q R MadeProgress | 20.
Proof. done. Qed.

Global Instance maybe_combine_sep_as_default {PROP : bi} (P Q : PROP) :
  MaybeCombineSepAs P Q (P ∗ Q) NoProgress | 100.
Proof. intros. by rewrite /MaybeCombineSepAs. Qed.

(** We do not have this Maybe construction for [CombineSepGives], nor do we
provide the trivial [CombineSepGives P Q True]. This is by design: when the user
writes down a 'gives' clause in the [iCombine] tactic, they intend to receive
non-trivial information. If such information cannot be found, we want to
produce an error, instead of the trivial hypothesis [True]. *)
Class CombineSepGives {PROP : bi} (P Q R : PROP) :=
  combine_sep_gives : P ∗ Q ⊢ <pers> R.
Global Arguments CombineSepGives {_} _%I _%I _%I : simpl never.
Global Arguments combine_sep_gives {_} _%I _%I _%I {_}.
Global Hint Mode CombineSepGives + ! ! - : typeclass_instances.

(** The [ElimModal φ p p' P P' Q Q'] class is used by the [iMod] tactic.

The inputs are [p], [P] and [Q], and the outputs are [φ], [p'], [P'] and [Q'].

The class is used to transform a hypothesis [P] into a hypothesis [P'], given
a goal [Q], which is simultaneously transformed into [Q']. The Booleans [p]
and [p'] indicate whether the original, respectively, updated hypothesis reside
in the persistent context (iff [true]). The proposition [φ] can be used to
express a side-condition that [iMod] will generate (if not [True]).

An example instance is:

  ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).

This instance expresses that to eliminate [|={E1,E2}=> P] the goal is
transformed from [|={E1,E3}=> Q] into [|={E2,E3}=> Q], and the resulting
hypothesis is moved into the spatial context (regardless of where it was
originally). A corresponding [ElimModal] instance for the Iris 1/2-style update
modality, would have a side-condition [φ] on the masks. *)
Class ElimModal {PROP : bi} (φ : Prop) (p p' : bool) (P P' : PROP) (Q Q' : PROP) :=
  elim_modal : φ → □?p P ∗ (□?p' P' -∗ Q') ⊢ Q.
Global Arguments ElimModal {_} _ _ _ _%I _%I _%I _%I : simpl never.
Global Arguments elim_modal {_} _ _ _ _%I _%I _%I _%I {_}.
Global Hint Mode ElimModal + - ! - ! - ! - : typeclass_instances.

(* Used by the specialization pattern [ > ] in [iSpecialize] and [iAssert] to
add a modality to the goal corresponding to a premise/asserted proposition. *)
Class AddModal {PROP : bi} (P P' : PROP) (Q : PROP) :=
  add_modal : P ∗ (P' -∗ Q) ⊢ Q.
Global Arguments AddModal {_} _%I _%I _%I : simpl never.
Global Arguments add_modal {_} _%I _%I _%I {_}.
Global Hint Mode AddModal + - ! ! : typeclass_instances.

Lemma add_modal_id {PROP : bi} (P Q : PROP) : AddModal P P Q.
Proof. by rewrite /AddModal wand_elim_r. Qed.

(** We use the classes [IsCons] and [IsApp] to make sure that instances such as
[frame_big_sepL_cons] and [frame_big_sepL_app] cannot be applied repeatedly
often when having [ [∗ list] k ↦ x ∈ ?e, Φ k x] with [?e] an evar. *)
Class IsCons {A} (l : list A) (x : A) (k : list A) := is_cons : l = x :: k.
Class IsApp {A} (l k1 k2 : list A) := is_app : l = k1 ++ k2.
Global Hint Mode IsCons + ! - - : typeclass_instances.
Global Hint Mode IsApp + ! - - : typeclass_instances.

Global Instance is_cons_cons {A} (x : A) (l : list A) : IsCons (x :: l) x l.
Proof. done. Qed.
Global Instance is_app_app {A} (l1 l2 : list A) : IsApp (l1 ++ l2) l1 l2.
Proof. done. Qed.

Class Frame {PROP : bi} (p : bool) (R P Q : PROP) := frame : □?p R ∗ Q ⊢ P.
Global Arguments Frame {_} _ _%I _%I _%I.
Global Arguments frame {_} _ _%I _%I _%I {_}.
Global Hint Mode Frame + + ! ! - : typeclass_instances.

(* The boolean [progress] indicates whether actual framing has been performed.
If it is [false], then the default instance [maybe_frame_default] below has been
used. *)
Class MaybeFrame {PROP : bi} (p : bool) (R P Q : PROP) (progress : bool) :=
  maybe_frame : □?p R ∗ Q ⊢ P.
Global Arguments MaybeFrame {_} _ _%I _%I _%I _.
Global Arguments maybe_frame {_} _ _%I _%I _%I _ {_}.
Global Hint Mode MaybeFrame + + ! - - - : typeclass_instances.

Global Instance maybe_frame_frame {PROP : bi} p (R P Q : PROP) :
  Frame p R P Q → MaybeFrame p R P Q true.
Proof. done. Qed.

Global Instance maybe_frame_default_persistent {PROP : bi} (R P : PROP) :
  MaybeFrame true R P P false | 100.
Proof. intros. rewrite /MaybeFrame /=. by rewrite sep_elim_r. Qed.
Global Instance maybe_frame_default {PROP : bi} (R P : PROP) :
  TCOr (Affine R) (Absorbing P) → MaybeFrame false R P P false | 100.
Proof. intros. rewrite /MaybeFrame /=. apply: sep_elim_r. Qed.

Class IntoExcept0 {PROP : bi} (P Q : PROP) := into_except_0 : P ⊢ ◇ Q.
Global Arguments IntoExcept0 {_} _%I _%I : simpl never.
Global Arguments into_except_0 {_} _%I _%I {_}.
Global Hint Mode IntoExcept0 + ! - : typeclass_instances.
Global Hint Mode IntoExcept0 + - ! : typeclass_instances.

(* The class [MaybeIntoLaterN] has only two instances:

- The default instance [MaybeIntoLaterN n P P], i.e. [▷^n P -∗ P]
- The instance [IntoLaterN n P Q → MaybeIntoLaterN n P Q], where [IntoLaterN]
  is identical to [MaybeIntoLaterN], but is supposed to make progress, i.e. it
  should actually strip a later.

The point of using the auxilary class [IntoLaterN] is to ensure that the
default instance is not applied deeply inside a term, which may result in too
many definitions being unfolded (see issue #55).

For binary connectives we have the following instances:

<<
IntoLaterN n P P'       MaybeIntoLaterN n Q Q'
------------------------------------------
     IntoLaterN n (P /\ Q) (P' /\ Q')


      IntoLaterN n Q Q'
-------------------------------
IntoLaterN n (P /\ Q) (P /\ Q')
>>

The Boolean [only_head] indicates whether laters should only be stripped in
head position or also below other logical connectives. For [iNext] it should
strip laters below other logical connectives, but this should not happen while
framing, e.g. the following should succeed:

<<
Lemma test_iFrame_later_1 P Q : P ∗ ▷ Q -∗ ▷ (P ∗ ▷ Q).
Proof. iIntros "H". iFrame "H". Qed.
>>
*)
Class MaybeIntoLaterN {PROP : bi} (only_head : bool) (n : nat) (P Q : PROP) :=
  maybe_into_laterN : P ⊢ ▷^n Q.
Global Arguments MaybeIntoLaterN {_} _ _%nat_scope _%I _%I.
Global Arguments maybe_into_laterN {_} _ _%nat_scope _%I _%I {_}.
Global Hint Mode MaybeIntoLaterN + + + - - : typeclass_instances.

Class IntoLaterN {PROP : bi} (only_head : bool) (n : nat) (P Q : PROP) :=
  into_laterN :> MaybeIntoLaterN only_head n P Q.
Global Arguments IntoLaterN {_} _ _%nat_scope _%I _%I.
Global Hint Mode IntoLaterN + + + ! - : typeclass_instances.

Global Instance maybe_into_laterN_default {PROP : bi} only_head n (P : PROP) :
  MaybeIntoLaterN only_head n P P | 1000.
Proof. apply laterN_intro. Qed.
(* In the case both parameters are evars and n=0, we have to stop the
   search and unify both evars immediately instead of looping using
   other instances. *)
Global Instance maybe_into_laterN_default_0 {PROP : bi} only_head (P : PROP) :
  MaybeIntoLaterN only_head 0 P P | 0.
Proof. apply _. Qed.

(** The class [IntoEmbed P Q] is used to transform hypotheses while introducing
embeddings using [iModIntro].

Input: the proposition [P], output: the proposition [Q] so that [P ⊢ ⎡Q⎤]. *)
Class IntoEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} (P : PROP') (Q : PROP) :=
  into_embed : P ⊢ ⎡Q⎤.
Global Arguments IntoEmbed {_ _ _} _%I _%I.
Global Arguments into_embed {_ _ _} _%I _%I {_}.
Global Hint Mode IntoEmbed + + + ! -  : typeclass_instances.

(* We use two type classes for [AsEmpValid], in order to avoid loops in
   typeclass search. Indeed, the [as_emp_valid_embed] instance would try
   to add an arbitrary number of embeddings. To avoid this, the
   [AsEmpValid0] type class cannot handle embeddings, and therefore
   [as_emp_valid_embed] only tries to add one embedding, and we never try
   to insert nested embeddings. This has the additional advantage of
   always trying [as_emp_valid_embed] as a second option, so that this
   instance is never used when the BI is unknown.

   No Hint Modes are declared here. The appropriate one would be
   [Hint Mode - ! -], but the fact that Coq ignores primitive
   projections for hints modes would make this fail.*)
Class AsEmpValid {PROP : bi} (φ : Prop) (P : PROP) :=
  as_emp_valid : φ ↔ ⊢ P.
Global Arguments AsEmpValid {_} _%type _%I.
Class AsEmpValid0 {PROP : bi} (φ : Prop) (P : PROP) :=
  as_emp_valid_0 : AsEmpValid φ P.
Global Arguments AsEmpValid0 {_} _%type _%I.
Global Existing Instance as_emp_valid_0 | 0.

Lemma as_emp_valid_1 (φ : Prop) {PROP : bi} (P : PROP) `{!AsEmpValid φ P} :
  φ → ⊢ P.
Proof. by apply as_emp_valid. Qed.
Lemma as_emp_valid_2 (φ : Prop) {PROP : bi} (P : PROP) `{!AsEmpValid φ P} :
  (⊢ P) → φ.
Proof. by apply as_emp_valid. Qed.

(* Input: [P]; Outputs: [N],
   Extracts the namespace associated with an invariant assertion. Used for [iInv]. *)
Class IntoInv {PROP : bi} (P: PROP) (N: namespace).
Global Arguments IntoInv {_} _%I _.
Global Hint Mode IntoInv + ! - : typeclass_instances.

(** Accessors.
    This definition only exists for the purpose of the proof mode; a truly
    usable and general form would use telescopes and also allow binders for the
    closing view shift.  [γ] is an [option] to make it easy for ElimAcc
    instances to recognize the [emp] case and make it look nicer. *)
Definition accessor {PROP : bi} {X : Type} (M1 M2 : PROP → PROP)
           (α β : X → PROP) (mγ : X → option PROP) : PROP :=
  M1 (∃ x, α x ∗ (β x -∗ M2 (default emp (mγ x))))%I.

(* Typeclass for assertions around which accessors can be eliminated.
   Inputs: [Q], [E1], [E2], [α], [β], [γ]
   Outputs: [Q'], [φ]

   Elliminates an accessor [accessor E1 E2 α β γ] in goal [Q'], turning the goal
   into [Q'] with a new assumption [α x], where [φ] is a side-condition at the
   Cow level that needs to hold. *)
Class ElimAcc {PROP : bi} {X : Type} (φ : Prop) (M1 M2 : PROP → PROP)
      (α β : X → PROP) (mγ : X → option PROP)
      (Q : PROP) (Q' : X → PROP) :=
  elim_acc : φ → ((∀ x, α x -∗ Q' x) -∗ accessor M1 M2 α β mγ -∗ Q).
Global Arguments ElimAcc {_} {_} _ _%I _%I _%I _%I _%I _%I : simpl never.
Global Arguments elim_acc {_} {_} _ _%I _%I _%I _%I _%I _%I {_}.
Global Hint Mode ElimAcc + ! - ! ! ! ! ! ! - : typeclass_instances.

(* Turn [P] into an accessor.
   Inputs:
   - [Pacc]: the assertion to be turned into an accessor (e.g. an invariant)
   Outputs:
   - [Pin]: additional logic assertion needed for starting the accessor.
   - [φ]: additional Coq assertion needed for starting the accessor.
   - [X] [α], [β], [γ]: the accessor parameters.
   - [M1], [M2]: the two accessor modalities (they will typically still have
     some evars though, e.g. for the masks)
*)
Class IntoAcc {PROP : bi} {X : Type} (Pacc : PROP) (φ : Prop) (Pin : PROP)
      (M1 M2 : PROP → PROP) (α β : X → PROP) (mγ : X → option PROP) :=
  into_acc : φ → Pacc -∗ Pin -∗ accessor M1 M2 α β mγ.
Global Arguments IntoAcc {_} {_} _%I _ _%I _%I _%I _%I _%I _%I : simpl never.
Global Arguments into_acc {_} {_} _%I _ _%I _%I _%I _%I _%I _%I {_} : simpl never.
Global Hint Mode IntoAcc + - ! - - - - - - - : typeclass_instances.

(* The typeclass used for the [iInv] tactic.
   Input: [Pinv]
   Other Arguments:
   - [Pinv] is an invariant assertion
   - [Pin] is an additional logic assertion needed for opening an invariant
   - [φ] is an additional Coq assertion needed for opening an invariant
   - [Pout] is the assertion obtained by opening the invariant
   - [Pclose] is the closing view shift.  It must be (Some _) or None
     when doing typeclass search as instances are allowed to make a
     case distinction on whether the user wants a closing view-shift or not.
   - [Q] is a goal on which iInv may be invoked
   - [Q'] is the transformed goal that must be proved after opening the invariant.

   Most users will never want to instantiate this; there is a general instance
   based on [ElimAcc] and [IntoAcc].  However, logics like Iris 2 that support
   invariants but not mask-changing fancy updates can use this class directly to
   still benefit from [iInv].
*)
Class ElimInv {PROP : bi} {X : Type} (φ : Prop)
      (Pinv Pin : PROP) (Pout : X → PROP) (mPclose : option (X → PROP))
      (Q : PROP) (Q' : X → PROP) :=
  elim_inv : φ → Pinv ∗ Pin ∗ (∀ x, Pout x ∗ (default (λ _, emp) mPclose) x -∗ Q' x) ⊢ Q.
Global Arguments ElimInv {_} {_} _ _%I _%I _%I _%I _%I _%I : simpl never.
Global Arguments elim_inv {_} {_} _ _%I _%I _%I _%I _%I _%I {_}.
Global Hint Mode ElimInv + - - ! - - ! ! - : typeclass_instances.

(** We make sure that tactics that perform actions on *specific* hypotheses or
parts of the goal look through the [tc_opaque] connective, which is used to make
definitions opaque for type class search. For example, when using [iDestruct],
an explicit hypothesis is affected, and as such, we should look through opaque
definitions. However, when using [iFrame] or [iNext], arbitrary hypotheses or
parts of the goal are affected, and as such, type class opacity should be
respected.

This means that there are [tc_opaque] instances for all proofmode type classes
with the exception of:

- [FromAssumption] used by [iAssumption]
- [Frame] and [MaybeFrame] used by [iFrame]
- [MaybeIntoLaterN] and [FromLaterN] used by [iNext]
- [IntoPersistent] used by [iIntuitionistic]
*)
Global Instance into_pure_tc_opaque {PROP : bi} (P : PROP) φ :
  IntoPure P φ → IntoPure (tc_opaque P) φ := id.
Global Instance from_pure_tc_opaque {PROP : bi} (a : bool) (P : PROP) φ :
  FromPure a P φ → FromPure a (tc_opaque P) φ := id.
Global Instance from_wand_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  FromWand P Q1 Q2 → FromWand (tc_opaque P) Q1 Q2 := id.
Global Instance into_wand_tc_opaque {PROP : bi} p q (R P Q : PROP) :
  IntoWand p q R P Q → IntoWand p q (tc_opaque R) P Q := id.

(* This instance has a very high cost. The tactic [iCombine] will look for
[FromSep ?P Q1 Q2]. If the cost of this instance is low (and in particular,
lower than the default instance [from_sep_sep], which picks [?P := Q1 * Q2]),
then TC search would diverge. *)
Global Instance from_sep_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  FromSep P Q1 Q2 → FromSep (tc_opaque P) Q1 Q2 | 102 := id.

Global Instance from_and_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  FromAnd P Q1 Q2 → FromAnd (tc_opaque P) Q1 Q2 := id.
Global Instance into_and_tc_opaque {PROP : bi} p (P Q1 Q2 : PROP) :
  IntoAnd p P Q1 Q2 → IntoAnd p (tc_opaque P) Q1 Q2 := id.
Global Instance into_sep_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  IntoSep P Q1 Q2 → IntoSep (tc_opaque P) Q1 Q2 := id.
Global Instance from_or_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  FromOr P Q1 Q2 → FromOr (tc_opaque P) Q1 Q2 := id.
Global Instance into_or_tc_opaque {PROP : bi} (P Q1 Q2 : PROP) :
  IntoOr P Q1 Q2 → IntoOr (tc_opaque P) Q1 Q2 := id.
Global Instance from_exist_tc_opaque {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :
  FromExist P Φ → FromExist (tc_opaque P) Φ := id.
Global Instance into_exist_tc_opaque {PROP : bi} {A} (P : PROP) (Φ : A → PROP) (name: ident_name) :
  IntoExist P Φ name → IntoExist (tc_opaque P) Φ name := id.
Global Instance from_forall_tc_opaque {PROP : bi} {A} (P : PROP) (Φ : A → PROP) (name : ident_name) :
  FromForall P Φ name → FromForall (tc_opaque P) Φ name := id.
Global Instance into_forall_tc_opaque {PROP : bi} {A} (P : PROP) (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (tc_opaque P) Φ := id.
Global Instance from_modal_tc_opaque {PROP1 PROP2 : bi} {A}
    φ M (sel : A) (P : PROP2) (Q : PROP1) :
  FromModal φ M sel P Q → FromModal φ M sel (tc_opaque P) Q := id.
Global Instance elim_modal_tc_opaque {PROP : bi} φ p p' (P P' Q Q' : PROP) :
  ElimModal φ p p' P P' Q Q' → ElimModal φ p p' (tc_opaque P) P' Q Q' := id.
Global Instance into_inv_tc_opaque {PROP : bi} (P : PROP) N :
  IntoInv P N → IntoInv (tc_opaque P) N := id.
Global Instance elim_inv_tc_opaque {PROP : bi} {X} φ Pinv Pin Pout Pclose Q Q' :
  ElimInv (PROP:=PROP) (X:=X) φ Pinv Pin Pout Pclose Q Q' →
  ElimInv φ (tc_opaque Pinv) Pin Pout Pclose Q Q' := id.
