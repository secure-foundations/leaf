# Iris Proof Guide

This work-in-progress document serves to explain how Iris proofs are typically
carried out in Coq: what are the common patterns and conventions, what are the
common pitfalls.  This complements the tactic documentation for the
[proof mode](./proof_mode.md) and [HeapLang](./heap_lang.md).

## Order of `Requires`

In Coq, declarations in modules imported later may override the
previous definition. Therefore, in order to make sure the most
relevant declarations and notations always take priority, we recommend
importing dependencies from the furthest to the closest.

In particular, when importing Iris, Stdpp and Coq stdlib modules, we
recommend importing in the following order:
- Coq
- stdpp
- iris.algebra
- iris.bi
- iris.proofmode
- iris.base_logic
- iris.program_logic
- iris.heap_lang

## Resolving mask mismatches

Sometimes, `fupd` masks are not exactly what they need to be to make progress.
There are two situations to distinguish here.

#### Eliminating a [fupd] with a mask smaller than the current one

When your goal is `|={E,_}=> _` and you want to do `iMod` on an `|={E',_}=> _`, Coq will complain even if `E' ⊆ E`.
To resolve this, you first need to explicitly weaken your mask from `E` to `E'` by doing:
```coq
iMod (fupd_mask_subseteq E') as "Hclose".
{ (* Resolve subset sidecondition. *) }
```
Later, you can `iMod "Hclose" as "_"` to restore the mask back from `E'` to `E`.

Notice that this will make the invariants in `E' ∖ E` unavailable until you use `Hclose`.
Usually this is not a problem, but there are theoretical situations where using `fupd_mask_subseteq` like this can prevent you from proving a goal.
In that case, you will have to experiment with rules like `fupd_mask_frame`, but those are not very convenient to use.

#### Introducing a [fupd] when the masks are not yet the same

When your goal is `|={E,E'}=> _` and you want to do `iModIntro`, Coq will complain even if `E' ⊆ E`.
This arises, for example, in clients of TaDA-style logically atomic specifications.
To resolve this, do:
```coq
iApply fupd_mask_intro.
{ (* Resolve subset sidecondition. *) }
iIntros "Hclose".
```
Later, you can `iMod "Hclose" as "_"` to restore the mask back from `E'` to `E`.

## Canonical structures and type classes

In Iris, we use both canonical structures and type classes, and some careful
tweaking is necessary to make the two work together properly.  The details of
this still need to be written up properly, but here is some background material:

* [Type Classes for Mathematics in Type Theory](http://www.eelis.net/research/math-classes/mscs.pdf)
* [Canonical Structures for the working Coq user](https://hal.inria.fr/hal-00816703v1/document)

## Implicit generalization

We often use the implicit generalization feature of Coq, triggered by a backtick:
`` `{!term A B}`` means that an implicit argument of type `term A B` is added,
and if any of the identifiers that are used here is not yet bound, it gets added
as well.  Usually, `term` will be some existing type class or similar, and we
use this syntax to also generalize over `A` and `B`; then the above is
equivalent to `{A B} {Hterm: term A B}`.  The `!` in front of the term disables
an even stronger form of generalization, where if `term` is a type class then
all missing arguments get implicitly generalized as well.  This is sometimes
useful, e.g. we can write `` `{Countable C}`` instead of `` `{!EqDecision C,
!Countable C}``.  However, generally it is more important to be aware of the
assumptions you are making, so implicit generalization without `!` should be
avoided.

## Type class resolution control

When you are writing a module that exports some Iris term for others to use
(e.g., `join_handle` in the [spawn module](../theories/heap_lang/lib/spawn.v)), be
sure to mark these terms as opaque for type class search at the *end* of your
module (and outside any section):
```coq
Typeclasses Opaque join_handle.
```
This makes sure that the proof mode does not "look into" your definition when it
is used by clients.

## Library type class assumptions

When a parameterized library needs to make some type class assumptions about its
parameters, it is convenient to add those to the `libG` class that the library
will likely need anyway (see the [resource algebra docs](resource_algebras.md)
for further details on `libG` classes).  For example, the STS library is
parameterized by an STS and assumes that the STS state space is inhabited:
```coq
Class stsG Σ (sts : stsT) := {
  sts_inG :> inG Σ (stsR sts);
  sts_inhabited :> Inhabited (sts.state sts);
}.
```
In this case, the `Instance` for this `libG` class has more than just a `subG`
assumption:
```coq
Instance subG_stsΣ Σ sts :
  subG (stsΣ sts) Σ → Inhabited (sts.state sts) → stsG Σ sts.
Proof. solve_inG. Qed.
```

One subtle detail here is that the `subG` assumption comes first in
`subG_stsΣ`, i.e., it appears before the `Inhabited`.  This is important because
otherwise, `sts_inhabited` and `subG_stsΣ` form an instance cycle that makes
type class search diverge.

## Notations

Notations starting with `(` or `{` should be left at their default level (`0`),
and inner subexpressions that are bracketed by delimiters should be left at
their default level (`200`).

Moreover, correct parsing of notations sometimes relies on Coq's automatic
left-factoring, which can require coordinating levels of certain "conflicting"
notations and their subexpressions.  For instance, to disambiguate `(⊢@{ PROP
})` and `(⊢@{ PROP } P)`, Coq must factor out a nonterminal for `⊢@{ PROP }`,
but it can only do so if all occurrences of `⊢@{ PROP }` agree on the
precedences for all subexpressions. This also requires using the same
tokenization in all cases, i.e., the notation has to consistently be declared as
`(⊢@{` or `('⊢@{'`, but not a mixture of the two. The latter form of using
explicit tokenization with `'` is preferred to avoid relying on Coq's default.

For details, consult [the Coq manual](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#simple-factorization-rules).

## Naming conventions for variables/arguments/hypotheses

### small letters

* a : A = cmra or ofe
* b : B = cmra or ofe
* c
* d
* e : expr = expressions
* f = some generic function
* g = some generic function
* h : heap
* i
* j
* k
* l
* m* = prefix for option ("maybe")
* n
* o
* p
* q
* r : iRes = (global) resources inside the Iris model
* s = state (STSs)
* s = stuckness bits
* t
* u
* v : val = values of language
* w
* x
* y
* z 

### capital letters

* A : Type, cmra or ofe
* B : Type, cmra or ofe
* C
* D
* E : coPset = mask of fancy update or WP
* F = a functor
* G
* H = hypotheses
* I = indexing sets
* J
* K : ectx = evaluation contexts
* K = keys of a map
* L
* M = maps / global CMRA
* N : namespace
* O 
* P : uPred, iProp or Prop
* Q : uPred, iProp or Prop
* R : uPred, iProp or Prop
* S : set state = state sets in STSs
* T : set token = token sets in STSs
* U
* V
* W
* X : sets
* Y : sets
* Z : sets

### small greek letters

* γ : gname = name of ghost state instance
* σ : state = state of language
* φ : Prop = pure proposition embedded into uPred or iProp

### capital greek letters

* Φ : general predicate (in uPred, iProp or Prop)
* Ψ : general predicate (in uPred, iProp or Prop)

## Naming conventions for algebraic classes

### Suffixes

* O: OFEs
* R: cameras
* UR: unital cameras or resources algebras
* F: functors (can be combined with all of the above, e.g. OF is an OFE functor)
* G: global camera functor management (typeclass; see the [resource algebra docs](resource_algebras.md))
* GS: global singleton (a `*G` type class with extra data that needs to be unique in a proof)
* GpreS: collecting preconditions to instantiate the corresponding `*GS`
* I: bunched implication logic (of type `bi`)
* SI: step-indexed bunched implication logic (of type `sbi`)
* T: canonical structures for algebraic classes (for example ofe for OFEs, cmra for cameras)
* Σ: global camera functor management (`gFunctors`; see the [resource algebra docs](resource_algebras.md))
