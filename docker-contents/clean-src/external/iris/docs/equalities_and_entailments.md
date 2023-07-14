# Equalities in Iris

Using Iris involves dealing with a few subtly different equivalence and equality
relations, especially among propositions.
This document summarizes these relations and the subtle distinctions among them.
This is not a general introduction to Iris: instead, we discuss the different
Iris equalities and the interface to their Coq implementation. In particular, we
discuss:
- Equality ("=") in the *on-paper* Iris metatheory
- Coq's Leibniz equality (`=`) and std++'s setoid equivalence (`≡`);
- N-equivalence on OFEs (`≡{n}≡`);
- Iris internal equality (`≡` in `bi_scope`);
- Iris entailment and bi-entailment (`⊢`, `⊣⊢`).

We use `code font` for Coq notation and "quotes" for paper notation.

## Leibniz equality and setoids

First off, in the metalogic (Coq) we have both the usual propositional (or
Leibniz) equality `=`, and setoid equality `equiv` / `≡` (defined in `stdpp`).
Both of these are metalogic connectives from the perspective of Iris, and as
such are declared in Coq scope `stdpp_scope`.

Setoid equality for a type `A` is defined by the instance of `Equiv A`.  This
should be accompanied by an `Equivalence` instance which proves that the given
relation indeed is an equivalence relation.  The handling of setoidsis based on
Coq's
[generalized rewriting](https://coq.inria.fr/refman/addendum/generalized-rewriting.html)
facilities.

Setoid equality can coincide with Leibniz equality, which is reflected by the
`LeibnizEquiv` typeclass. We say that types with this property are "Leibniz
types". `equivL` provides a convenient way to define a setoid with Leibniz
equality. The tactics `fold_leibniz` and `unfold_leibniz` can be used to
automatically turn all equalities of Leibniz types into `≡` or `=`.

Given setoids `A` and `B` and a function `f : A → B`, an instance `Proper ((≡)
==> (≡)) f` declares that `f` respects setoid equality, as usual in Coq. Such
instances enable rewriting with setoid equalities.

Here, stdpp adds the following facilities:
- `solve_proper` for automating proofs of `Proper` instances.
- `f_equiv` generalizes `f_equal` to setoids (and indeed arbitrary relations
  registered with Coq's generalized rewriting). It will for instance turn the
  goal `f a ≡ f b` into `a ≡ b` given an appropriate `Proper` instance (here,
  `Proper ((≡) ==> (≡)) f`).

## Equivalences on OFEs

On paper, OFEs involve two relations, equality "=" and distance "=_n". In Coq,
equality "=" is formalized as setoid equality, written `≡` or `equiv`, as before;
distance "=_n" is formalized as relation `dist n`, also written `≡{n}≡`.
Tactics `solve_proper` and `f_equiv` also support distance. There is no
correspondence to Coq's `=` on paper.

Some OFE constructors choose interesting equalities.
- `discreteO` constructs discrete OFEs (where distance coincides with setoid equality).
- `leibnizO` constructs discrete OFEs (like `discreteO`) but using `equivL`, so
  that both distance and setoid equality coincide with Leibniz equality. This
  should only be used for types that do not have a setoid equality registered.

Given OFEs `A` and `B`, non-expansive functions from `A` to `B` are functions
`f : A → B` with a proof of `NonExpansive f` (which is notation for `∀ n, Proper
(dist n ==> dist n) f`).

The type `A -n> B` packages a function with a non-expansiveness proof. This is
useful because `A -n> B` is itself an OFE, but should be avoided whenever
possible as it requires the caller to specifically package up function and proof
(which works particularly badly for lambda expressions).

When an OFE structure on a function type is required but the domain is discrete,
one can use the type `A -d> B`.  This has the advantage of not bundling any
proofs, i.e., this is notation for a plain Coq function type. See the
`discrete_fun` documentation in [`iris.algebra.ofe`](../iris/algebra/ofe.v)
for further details.

In both OFE function spaces (`A -n> B` and `A -d> B`), setoid equality is
defined to be pointwise equality, so that functional extensionality holds for `≡`.

## Inside the Iris logic

Next, we introduce notions internal to the Iris logic. Such notions often
overload symbols used for external notions; however, those overloaded notations
are declared in scope `bi_scope`. When writing `(P)%I`, notations in `P` are
resolved in `bi_scope`; this is done implicitly for the arguments of all
variants of Iris entailments.

The Iris logic has an internal concept of equality: if `a` and `b` are Iris
terms of type `A`, then their internal equality is written (on paper) "a =_A b";
in Coq, that's written `(a ≡@{A} b)%I` (notation for `bi_internal_eq` in scope
`bi_scope`). You can leave away the `@{A}` to let Coq infer the type.

As shown in the Iris appendix, an internal equality `(a ≡ b)%I` is interpreted using
OFE distance at the current step-index. Many types have `_equivI` lemmas
characterizing internal equality on them. For instance, if `f, g : A -d> B`,
lemma `discrete_fun_equivI` shows that `(f ≡ g)%I` is equivalent to
`(∀ x, f x ≡ g x)%I`.

An alternative to internal equality is to embed Coq equality into the Iris logic
using `⌜ _ ⌝%I`.  For discrete types, `(a ≡ b)%I` is equivalent to `⌜a ≡ b⌝%I`,
and the latter can be moved into the Coq context, making proofs more convenient.
For types with Leibniz equality, we can even equivalently write `⌜a = b⌝%I`, so
no `Proper` is needed for rewriting.  Note that there is no on-paper equivalent
to using these embedded Coq equalities for types that are not discrete/Leibniz.

## Relations among Iris propositions

In this section, we discuss relations among internal propositions, and in particular equality/equivalence of propositions themselves.
Even though some of these notes generalize to all internal logics (other
`bi`s), we focus on Iris propositions (`iProp`), to discuss both their proof
theory and their model.
As Iris propositions form a separation logic, we assume some familiarity with
separation logics, connectives such as `-∗`, `∗`, `emp` and `→`, and the idea
that propositions in separation logics are interpreted with predicates over
resources (see for instance Sec. 2.1 of the MoSEL paper).

In the metalogic, Iris defines the entailment relation between uniform
predicates: intuitively, `P` entails `Q` (written `P ⊢ Q`) means that `P`
implies `Q` on _every_ resource and at all step-indices (for details see Iris appendix [Sec. 6]).
Entailment `P ⊢ Q` is distinct from the magic wand, `(P -∗ Q)%I`: the former is
a Coq-level statement of type `Prop`, the latter an Iris-level statement of type
`iProp`.  However, the two are closely related: `P ⊢ Q` is equivalent to `emp ⊢
P -∗ Q` (per Iris lemmas `entails_wand` and `wand_entails`).  Iris also defines
a "unary" form of entailment, `⊢ P`, which is short for `emp ⊢ P`.
We can also use bi-entailment `P ⊣⊢ Q` to express that both `P ⊢ Q` and `Q ⊢ P` hold.

On paper, uniform predicates are defined by quotienting by an equivalence
relation ([Iris appendix, Sec. 3.3]); in Coq, that relation is chosen as the
setoid equivalent for the type of Iris propositions.
This equivalence is actually equivalent to bi-entailment, per lemma `equiv_spec`:
```coq
Lemma equiv_spec P Q : P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P).
```
Relying on this equivalence, bi-entailment `P ⊣⊢ Q` is defined as notation for `≡`.

## Internal equality of Iris propositions

Inside the logic, we can use internal equality `(≡)%I` on any type, including
propositions themselves.  However, there is a pitfall here: internal equality
`≡` is in general strictly stronger than `∗-∗` (the bidirectional version of the
magic wand), because `Q1 ≡ Q2` means that `Q1` and `Q2` are equivalent
_independently of the available resources_. This makes `≡` even stronger than `□
(_ ∗-∗ _)`, because `□` does permit the usage of some resources (namely, the RA
core of the available resources can still be used).

The two notions of internal equivalence and equality of propositions are related
by the following law of propositional extensionality:
```coq
Lemma prop_ext P Q : P ≡ Q ⊣⊢ ■ (P ∗-∗ Q).
```
This uses the plainly modality `■` to reflect that equality corresponds to
equivalence without any resources available: `■ R` says that `R` holds
independent of any resources that we might own (but still taking into account
the current step-index).
