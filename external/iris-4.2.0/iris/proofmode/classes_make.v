(** The [MakeX] classes are "smart constructors" for the logical connectives
and modalities that perform some trivial logical simplifications to give "clean"
results.

For example, when framing below logical connectives/modalities, framing should
remove connectives/modalities if the result of framing is [emp]. For example,
when framing [P] (using [iFrame]) in goal [P ∗ Q], the result should be [Q]. The
result should not be [emp ∗ Q], where [emp] would be the result of (recursively)
framing [P] in [P]. Hence, in the recursive calls, the framing machinery uses
the class [MakeSep P Q PQ]. If either [P] or [Q] is [emp] (or [True] in case of
appropriate assumptions w.r.t. affinity), the result [PQ] is [Q] or [P],
respectively. In other cases, the result is [PQ] is simply [P ∗ Q].

The [MakeX] classes are used in each recursive step of the framing machinery.
Hence, they should be "constant time", which means that the number of steps in
the inference search for [MakeX] should not depend on the size of the inputs.
This implies that [MakeX] instances should not be recursive, and [MakeX]
instances should not have premises of other classes with recursive instances. In
particular, [MakeX] instances should not have [Affine] or [Absorbing] premises
(because these could invoke a recursive search). Instances for [MakeX] instances
typically look only at the top-level symbol of the input, or check if the whole
BI is affine (via the [BiAffine] class) -- the latter can be linear in
the size of [PROP] itself, but is still independent of the size of the term.

One could imagine a smarter way of "cleaning up", as implemented in
https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/450 for some modalities,
but that makes framing less predictable and might have some performance impact
(i.e., not be constant time). Hence, we only perform such cleanup for [True]
and [emp].

For each of the [MakeX] class, there is a [KnownMakeX] variant, which only
succeeds if the parameter(s) is not an evar. In the case the parameter(s) is an
evar, then [MakeX] will not instantiate it arbitrarily.

The reason for this is that if given an evar, these classes would typically
try to instantiate this evar with some arbitrary logical constructs such as
[emp] or [True]. Therefore, we use a [Hint Mode] to disable all the instances
that would have this behavior.

In practice this means that usually only the default instance should use [MakeX],
and most specialized instances should use [KnownMakeX]. *)
From iris.bi Require Export bi.
From iris.prelude Require Import options.

(** Aliases for [Affine] and [Absorbing], but the instances are severely
restricted. They only inspect the top-level symbol or check if the whole BI
is affine. *)
Class QuickAffine {PROP : bi} (P : PROP) := quick_affine : Affine P.
Global Hint Mode QuickAffine + ! : typeclass_instances.
Class QuickAbsorbing {PROP : bi} (P : PROP) := quick_absorbing : Absorbing P.
Global Hint Mode QuickAbsorbing + ! : typeclass_instances.

Class MakeEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} (P : PROP) (Q : PROP') :=
  make_embed : ⎡P⎤ ⊣⊢ Q.
Global Arguments MakeEmbed {_ _ _} _%I _%I.
Global Hint Mode MakeEmbed + + + - - : typeclass_instances.
Class KnownMakeEmbed {PROP PROP' : bi} `{BiEmbed PROP PROP'} (P : PROP) (Q : PROP') :=
  #[global] known_make_embed :: MakeEmbed P Q.
Global Arguments KnownMakeEmbed {_ _ _} _%I _%I.
Global Hint Mode KnownMakeEmbed + + + ! - : typeclass_instances.

Class MakeSep {PROP : bi} (P Q PQ : PROP) := make_sep : P ∗ Q ⊣⊢ PQ .
Global Arguments MakeSep {_} _%I _%I _%I.
Global Hint Mode MakeSep + - - - : typeclass_instances.
Class KnownLMakeSep {PROP : bi} (P Q PQ : PROP) :=
  #[global] knownl_make_sep :: MakeSep P Q PQ.
Global Arguments KnownLMakeSep {_} _%I _%I _%I.
Global Hint Mode KnownLMakeSep + ! - - : typeclass_instances.
Class KnownRMakeSep {PROP : bi} (P Q PQ : PROP) :=
  #[global] knownr_make_sep :: MakeSep P Q PQ.
Global Arguments KnownRMakeSep {_} _%I _%I _%I.
Global Hint Mode KnownRMakeSep + - ! - : typeclass_instances.

Class MakeAnd {PROP : bi} (P Q PQ : PROP) :=  make_and_l : P ∧ Q ⊣⊢ PQ.
Global Arguments MakeAnd {_} _%I _%I _%I.
Global Hint Mode MakeAnd + - - - : typeclass_instances.
Class KnownLMakeAnd {PROP : bi} (P Q PQ : PROP) :=
  #[global] knownl_make_and :: MakeAnd P Q PQ.
Global Arguments KnownLMakeAnd {_} _%I _%I _%I.
Global Hint Mode KnownLMakeAnd + ! - - : typeclass_instances.
Class KnownRMakeAnd {PROP : bi} (P Q PQ : PROP) :=
  #[global] knownr_make_and :: MakeAnd P Q PQ.
Global Arguments KnownRMakeAnd {_} _%I _%I _%I.
Global Hint Mode KnownRMakeAnd + - ! - : typeclass_instances.

Class MakeOr {PROP : bi} (P Q PQ : PROP) := make_or_l : P ∨ Q ⊣⊢ PQ.
Global Arguments MakeOr {_} _%I _%I _%I.
Global Hint Mode MakeOr + - - - : typeclass_instances.
Class KnownLMakeOr {PROP : bi} (P Q PQ : PROP) :=
  #[global] knownl_make_or :: MakeOr P Q PQ.
Global Arguments KnownLMakeOr {_} _%I _%I _%I.
Global Hint Mode KnownLMakeOr + ! - - : typeclass_instances.
Class KnownRMakeOr {PROP : bi} (P Q PQ : PROP) := #[global] knownr_make_or :: MakeOr P Q PQ.
Global Arguments KnownRMakeOr {_} _%I _%I _%I.
Global Hint Mode KnownRMakeOr + - ! - : typeclass_instances.

Class MakeAffinely {PROP : bi} (P Q : PROP) :=
  make_affinely : <affine> P ⊣⊢ Q.
Global Arguments MakeAffinely {_} _%I _%I.
Global Hint Mode MakeAffinely + - - : typeclass_instances.
Class KnownMakeAffinely {PROP : bi} (P Q : PROP) :=
  #[global] known_make_affinely :: MakeAffinely P Q.
Global Arguments KnownMakeAffinely {_} _%I _%I.
Global Hint Mode KnownMakeAffinely + ! - : typeclass_instances.

Class MakeIntuitionistically {PROP : bi} (P Q : PROP) :=
  make_intuitionistically : □ P ⊣⊢ Q.
Global Arguments MakeIntuitionistically {_} _%I _%I.
Global Hint Mode MakeIntuitionistically + - - : typeclass_instances.
Class KnownMakeIntuitionistically {PROP : bi} (P Q : PROP) :=
  #[global] known_make_intuitionistically :: MakeIntuitionistically P Q.
Global Arguments KnownMakeIntuitionistically {_} _%I _%I.
Global Hint Mode KnownMakeIntuitionistically + ! - : typeclass_instances.

Class MakeAbsorbingly {PROP : bi} (P Q : PROP) :=
  make_absorbingly : <absorb> P ⊣⊢ Q.
Global Arguments MakeAbsorbingly {_} _%I _%I.
Global Hint Mode MakeAbsorbingly + - - : typeclass_instances.
Class KnownMakeAbsorbingly {PROP : bi} (P Q : PROP) :=
  #[global] known_make_absorbingly :: MakeAbsorbingly P Q.
Global Arguments KnownMakeAbsorbingly {_} _%I _%I.
Global Hint Mode KnownMakeAbsorbingly + ! - : typeclass_instances.

Class MakePersistently {PROP : bi} (P Q : PROP) :=
  make_persistently : <pers> P ⊣⊢ Q.
Global Arguments MakePersistently {_} _%I _%I.
Global Hint Mode MakePersistently + - - : typeclass_instances.
Class KnownMakePersistently {PROP : bi} (P Q : PROP) :=
  #[global] known_make_persistently :: MakePersistently P Q.
Global Arguments KnownMakePersistently {_} _%I _%I.
Global Hint Mode KnownMakePersistently + ! - : typeclass_instances.

Class MakeLaterN {PROP : bi} (n : nat) (P lP : PROP) :=
  make_laterN : ▷^n P ⊣⊢ lP.
Global Arguments MakeLaterN {_} _%nat _%I _%I.
Global Hint Mode MakeLaterN + + - - : typeclass_instances.
Class KnownMakeLaterN {PROP : bi} (n : nat) (P lP : PROP) :=
  #[global] known_make_laterN :: MakeLaterN n P lP.
Global Arguments KnownMakeLaterN {_} _%nat _%I _%I.
Global Hint Mode KnownMakeLaterN + + ! - : typeclass_instances.

Class MakeExcept0 {PROP : bi} (P Q : PROP) :=
  make_except_0 : ◇ P ⊣⊢ Q.
Global Arguments MakeExcept0 {_} _%I _%I.
Global Hint Mode MakeExcept0 + - - : typeclass_instances.
Class KnownMakeExcept0 {PROP : bi} (P Q : PROP) :=
  #[global] known_make_except_0 :: MakeExcept0 P Q.
Global Arguments KnownMakeExcept0 {_} _%I _%I.
Global Hint Mode KnownMakeExcept0 + ! - : typeclass_instances.
