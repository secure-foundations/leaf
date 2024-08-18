# Tactics

Leaf supplies various tactics for use in Iris Proof Mode.

`src/guarding/tactics.v` provides example uses of these tactics.

### `leaf_hyp`

`leaf_hyp` makes it easy to use a guard proposition from the context
to produce a related guard proposition.
It takes one of the following forms:

```
leaf_hyp "H" lhs to P' as "G".
leaf_hyp "H" rhs to Q' as "G".
leaf_hyp "H" mask to E' as "G".
leaf_hyp "H" laters to n' as "G".
```

Assuming that `"H"` is a proposition in the persistent context
of the form `P &&{ E; n }&&> Q` or `P &&{ E }&&> Q`.
The idea is that you specify a guard proposition and which element you
want to modify, either:

 * The lhs, weakening it to `P'`. This creates a subgoal `P' &&{E}&&> P`.
 * The rhs, weakening it to `Q'`. This creates a subgoal `Q &&{E}&&> Q'`.
 * The mask, weakening it to `E'`. This creates a subgoal `E ⊆ E'`
 * The later-count, weakening it to `n'`. This creates a subgoal `n ≤ n'`

It places the resulting weakened guard proposition in the persistent context
with the specified name (here `"G'`).

When operating on the lhs or rhs, you can also weaken the later count at the same time.

```
leaf_hyp "H" lhs to P' laters plus m as "G".
leaf_hyp "H" rhs to Q' laters plus m as "G".
```

The first creates a subgoal `P' &&{ E; m }&&> P`,
and produces `P' &&{ e; n + m }&&> Q`.

Likewise for the rhs, it creates a subgoal `Q &&{ E; m }&&> Q'`
and produces `P &&{ e; n + m }&&> Q'`.

### `leaf_goal`

Similar to the above, except it strengthens the goal rather than weakens a hypothesis.

```
leaf_goal lhs to P'.
leaf_goal rhs to Q'.
leaf_goal mask to E'.
leaf_goal laters to n'.
```

Again, you specify a particular element of the proposition and specify what you want
to change that element to:

 * The lhs, strengthening it to `P'`. This creates a subgoal `P &&{E}&&> P'`.
 * The rhs, strengthening it to `Q'`. This creates a subgoal `Q' &&{E}&&> Q`.
 * The mask, strengthening it to `E'`. This creates a subgoal `E' ⊆ E`
 * The later-count, strengthening it to `n'`. This creates a subgoal `n' ≤ n`

Again, you can modify the later count while operating on the lhs and rhs.
This time, the later-count decreases:

```
leaf_hyp "H" lhs to P' laters minus m as "G".
leaf_hyp "H" rhs to Q' laters minus m as "G".
```

### `leaf_by_sep`

```
leaf_by_sep.
```

When the goal is `P &&{E}&&> Q`,
the `leaf_by_sep` tactic reduces it to a goal `□ (P -∗ (Q ∗ (Q -∗ P)))`.

This is useful when:

 * Your goal is `P &&{E}&&> Q`, where `P ⊣⊢ Q`
 * Your goal is `(A ∗ B) &&{E}&&> A` 
 * Your goal is `P &&{E}&&> Q`, where `P` and `Q` are equivalent under assumptions
    in the persistent context.

When the goal is `P &&{ E ; n }&&> Q`, the goal becomes
`P -∗ ▷^n (Q ∗ (Q -∗ P))`.

### `leaf_by_sep_except0`

```
leaf_by_sep_except0.
```

This is like `leaf_by_sep` except it produces the goal with an extra except-0 modality:
`P -∗ ▷^n ◇ (Q ∗ (Q -∗ P))`.

This is useful if you want to remove laters from timeless propositions. E.g., you can show
`P &&{E}&&> ▷ P` for timeless `P` this way.

### `leaf_open` and `leaf_open_laters`

Wrapper around `guards_open` and `lguards_open`.

```
leaf_open "G" with "A" as "X"
leaf_open_laters "G" with "A" as "X"
```

 * `"G"` is the name of guards proposition, say `"G": P &&{E}&&> Q`. 
 * `"A"` is a specialization pattern used to fulfill the `P` obligation.
 * `"X"` is an introduction pattern where the resulting `Q` goes.
