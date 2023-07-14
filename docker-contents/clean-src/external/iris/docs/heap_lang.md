# HeapLang overview

HeapLang is the example language that gets shipped with Iris.  It is not the
only language you can reason about with Iris, but meant as a reasonable demo
language for simple examples.

## Language

HeapLang is a lambda-calculus with operations to allocate individual locations,
`load`, `store`, `CmpXchg` (compare-and-exchange) and `FAA` (fetch-and-add). Moreover,
it has a `fork` construct to spawn new threads.  In terms of values, we have
integers, booleans, unit, heap locations, as well as (binary) sums and products.

Recursive functions are the only binders, so the sum elimination (`Case`)
expects both branches to be of function type and passes them the data component
of the sum.

For technical reasons, the only terms that are considered values are those that
begin with the `Val` expression former.  This means that, for example, `Pair
(Val a) (Val b)` is *not* a value -- it reduces to `Val (PairV a b)`, which is.
This leads to some administrative redexes, and to a distinction between "value
pairs", "value sums", "value closures" and their "expression" counterparts.

However, this also makes values syntactically uniform, which we exploit in the
definition of substitution which just skips over `Val` terms, because values
should be closed and hence not affected by substitution.  As a consequence, we
can entirely avoid even talking about "closed terms", that notion just does not
have to come up anywhere.  We also exploit this when writing specifications,
because we can just write lemmas involving terms of the form `Val ?v` and Coq
can determine `?v` by unification (because all values start with the `Val`
constructor).

## Notation

Notation for writing HeapLang terms is defined in
[`notation.v`](../theories/heap_lang/notation.v).  There are two scopes, `%E` for
expressions and `%V` for values.  For example, `(a, b)%E` is an expression pair
and `(a, b)%V` a value pair.  The `e` of a `WP e {{ Q }}` is implicitly in `%E`
scope.

We define a whole lot of short-hands, such as non-recursive functions (`λ:`),
let-bindings, sequential composition, and a more conventional `match:` that has
binders in both branches.

The widely used `#` is a short-hand to turn a basic literal (an integer, a
location, a boolean literal or a unit value) into a value.  Since values coerce
to expressions, `#` is widely used whenever a Coq value needs to be placed into
a HeapLang term.

## Tactics

HeapLang comes with a bunch of tactics that facilitate stepping through HeapLang
programs as part of proving a weakest precondition.  All of these tactics assume
that the current goal is of the shape `WP e @ E {{ Q }}`.

Tactics to take one or more pure program steps:

- `wp_pure`: Perform one pure reduction step.  Pure steps are defined by the
  `PureExec` typeclass and include beta reduction, projections, constructors, as
  well as unary and binary arithmetic operators.
- `wp_pures`: Perform as many pure reduction steps as possible. This
  tactic will **not** reduce lambdas/recs that are hidden behind a definition.
  If the computation reaches a value, the `WP` will be entirely removed and the
  postcondition becomes the new goal.
- `wp_rec`, `wp_lam`: Perform a beta reduction.  Unlike `wp_pure`, this will
  also reduce lambdas that are hidden behind a definition.
- `wp_let`, `wp_seq`: Reduce a let-binding or a sequential composition.
- `wp_proj`: Reduce a projection.
- `wp_if_true`, `wp_if_false`, `wp_if`: Reduce a conditional expression. The
  discriminant must already be `true` or `false`.
- `wp_unop`, `wp_binop`, `wp_op`: Reduce a unary, binary or either kind of
  arithmetic operator.
- `wp_case`, `wp_match`: Reduce `Case`/`match:` constructs.
- `wp_inj`, `wp_pair`, `wp_closure`: Reduce constructors that turn expression
  sums/pairs/closures into their value counterpart.

Tactics for the heap:

- `wp_alloc l as "H"`: Reduce an allocation instruction and call the new
  location `l` (in the Coq context) and the points-to assertion `H` (in the
  spatial context).  You can leave out the `as "H"` to introduce it as an
  anonymous assertion, which is equivalent to `as "?"`.
- `wp_load`: Reduce a load operation.  This automatically finds the points-to
  assertion in the spatial context, and fails if it cannot be found.
- `wp_store`: Reduce a store operation.  This automatically finds the points-to
  assertion in the spatial context, and fails if it cannot be found.
- `wp_cmpxchg_suc`, `wp_cmpxchg_fail`: Reduce a succeeding/failing CmpXchg.  This
  automatically finds the points-to assertion.  It also automatically tries to
  solve the (in)equality to show that the CmpXchg succeeds/fails, and opens a new
  goal if it cannot prove this goal.
- `wp_cmpxchg as H1 | H2`: Reduce a CmpXchg, performing a case distinction over whether
  it succeeds or fails.  This automatically finds the points-to assertion.  The
  proof of equality in the first new subgoal will be called `H1`, and the proof
  of the inequality in the second new subgoal will be called `H2`.
- `wp_faa`: Reduce a FAA.  This automatically finds the points-to assertion.

Further tactics:

- `wp_bind pat`: Apply the bind rule to "focus" the term matching `pat`.  For
  example, `wp_bind (!_)%E` focuses a load operation.  This is useful in
  particular when accessing invariants, which is only possible when the `WP` in
  the goal is for a single, atomic operation -- `wp_bind` can be used to bring
  the goal into the right shape.
- `wp_apply pm_trm`: Apply a lemma whose conclusion is a `WP`, automatically
  applying `wp_bind` as needed.  See the [ProofMode docs](./proof_mode.md) for an
  explanation of `pm_trm`.

There is no tactic for `Fork`, just do `wp_apply wp_fork`.

To verify a recursive function, use `iLöb`.  Make sure you do `wp_pures` before
running `iLöb`; otherwise the induction hypothesis will likely not be applicable
when you need it.  (This makes sure that all administrative redexes are reduced
in your induction hypothesis, just like we state our `WP` specifications with
all of the redexes reduced.)

## Notation and lemmas for derived notions involving a thunk

Sometimes, it is useful to define a derived notion in HeapLang that involves
thunks.  For example, the parallel composition `e1 ||| e2` is definable in
HeapLang, but that requires thunking `e1` and `e2` before passing them to
`par`. (This is defined in [`par.v`](theories/heap_lang/lib/par.v).)  However,
this is somewhat subtle because of the distinction between expression lambdas
and value lambdas.

The normal `e1 ||| e2` notation uses expression lambdas, because clearly we want
`e1` and `e2` to behave normal under substitution (which they would not in a
value lambda).  However, the *specification* for parallel composition should use
value lambdas, because prior to applying it the term will be reduced as much as
possible to achieve a normal form.  To facilitate this, we define a copy of the
`e1 ||| e2` notation in the value scope that uses value lambdas.
This is not actually a value, but we still put it in the value scope to
differentiate from the other notation that uses expression lambdas.  (In the
future, we might decide to add a separate scope for this.)  Then, we write the
canonical specification using the notation in the value scope.

This works very well for non-recursive notions.  For `while` loops, the
situation is unfortunately more complex and proving the desired specification
will likely be more involved than expected, see this [discussion].

[discussion]: https://gitlab.mpi-sws.org/iris/iris/merge_requests/210#note_32842
