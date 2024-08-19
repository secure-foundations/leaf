# Iris proof style

**Warning:** this document is still in development and rather incomplete.
If you run across a question of style (for example, something comes
up in an MR) and it's not on this list, please do reach out to us on Mattermost
so we can add it.

## Basic syntax

### Binders

**Good:** `(a : B)`
**Bad:** `(a:B)`, `(a: B)`

**TODO**: Prefer `(a : B)` to `a : B`

This applies to Context, Implicit Types, and definitions

### Patterns

#### Disjunctions & branches

Always mark the disjuncts when destructuring a disjunctive pattern, even if you don't bind anything, to indicate that the proof branches

**Good:**
```coq
Lemma foo : ∀ b : bool, b = true ∨ b = false.
Proof.
  intros [|].
  ...
```

**Bad:**
```coq
Lemma foo : ∀ b : bool, b = true ∨ b = false.
Proof.
  intros [].
  ...
```

#### Uncategorized

**TODO:** Use `"[H1 H2]"` when possible otherwise do `"(H1 & H2 & H3)"`

### Unicode

Always use Unicode variants of forall, exists, ->, <=, >=

**Good:** `∀ ∃ → ≤ ≥`
**Bad:** `forall exists -> <= >=`

### Equivalent vernacular commands

Use `Context`, never `Variable`

**TODO:** Use `Implicit Types`, never `Implicit Type`

Use `Lemma`, not `Theorem` (or the other variants: `Fact`, `Corollary`,
`Remark`)

**TODO:** Always add `Global` or `Local` to `Hint`, `Arguments`, and `Instance`.

### `Require`

Never put `Require` in the middle of a file. All `Require` must be at the top.
If you only want to *import* a certain module in some specific place (for instance, in a `Section` or other `Module`), you can do something like:

```coq
From lib Require component.

(* ... *)

Import component.
```

### Ltac

We prefer `first [ t1 | fail 1 "..." ]` to `t1 || fail "..."` because the latter will fail if `t1` doesn't make progress. See https://gitlab.mpi-sws.org/iris/iris/-/issues/216. Note that `first [ t1 | fail "..."]` is simply incorrect; the failure message will never show up and will be replaced with a generic failure.

### Coqdoc comments

Module-level comments (covering the entire file) go at the top of the file, before the `Require`.

### Uncategorized

Indent the body of a match by one space:

**Good:**
```coq
match foo with
| Some x =>
   long line here using x
```

*RJ*: This is odd, usually everything is in (multiples of) 2 spaces, I think.

*Tej*: https://gitlab.mpi-sws.org/iris/iris/-/blob/920bc3d97b8830139045e1780f2aff4d05b910cd/iris_heap_lang/proofmode.v#L194

Avoid using the extra square brackets around an Ltac match:

**Good:**
```coq
match goal with
| |- ?g => idtac g
end
```

**Bad:**
```coq
match goal with
| [ |- ?g ] => idtac g
end
```

Use coqdoc syntax in comments for Coq identifiers and inline code, e.g. `[cmraT]`

Put proofs either all on one line (`Proof. reflexivity. Qed.`) or split up the usual way with indentation.

**Bad:**

```coq
Lemma foo : 2 + 2 = 4 ∧ 1 + 2 = 3.
Proof. split.
  - reflexivity.
  - done.
Qed.
```

Put the entire theorem statement on one line or one premise per line, indented by 2 spaces.

**Bad:**

```coq
Lemma foo x y z :
    x < y → y < z →
    x < z.
```

**Good:**

```coq
Lemma foo x y z : x < y → y < z → x < z.
```

**Good:** (particularly if premises are longer)

```coq
Lemma foo x y z :
  x < y →
  y < z →
  x < z.
```

If the parameters before the `:` become too long, indent later lines by 4 spaces and always have a newline after `:`:

**Bad:**

```coq
Lemma foo (very_long_name : has_a_very_long_type)
(even_longer_name : has_an_even_longer_type) : x < y → y < z →
  x < z.
```

**Good:**

```coq
Lemma foo (very_long_name : has_a_very_long_type)
    (even_longer_name : has_an_even_longer_type) :
  x < y → y < z → x < z.
```

For definitions that don't fit into one line, put `:=` before the linebreak, not after.


**Bad:**

```coq
Definition foo (arg1 arg2 arg3 : name_of_the_type)
  := the body that is very long.
```

**Good:**

```coq
Definition foo (arg1 arg2 arg3 : name_of_the_type) :=
  the body that is very long.
```

For tests with output put `Check "theorem name in a string"` before it so that the output from different tests is separated.

For long `t1; t2; t3` and `t; [t1 | t2 | t3]` split them like this, and indent by 2 spaces:

**Good:**
```coq
t;
  [t1
  |t2
  |t3].
```

```coq
t;
  t1;
  t2.
```


**TODO:** Keep all `Require`, `Import` and `Export` at the top of the file.


## File organization
theories/algebra is for primitive ofe/RA/CMRA constructions
theories/algebra/lib is for derived constructions
theories/base_logic/lib is for constructions in the base logic (using own)

## Naming
* `*_ctx` for persistent facts (often an invariant) needed by everything in a library
* `*_interp` for a function from some representation to iProp
* If you have lemma `foo` which is an iff and you want single direction versions, name them `foo_1` (forward) and `foo_2` (backward)
* If you have a lemma `foo` parametrized by an equivalence relation, you might want a version specialized to Leibniz equality for better rewrite support; name that version `foo_L` and state it with plain equality (e.g., `dom_empty_L` in stdpp). You might take an assumption `LeibnizEquiv A` if the original version took an equivalence (say the OFE equivalence) to assume that the provided equivalence is plain equality.
* Lower-case theorem names, lower-case types, upper-case constructors
* **TODO:** how should `f (g x) = f' (g' x)` be named?
* `list_lookup_insert` is named by context (the type involved), then the two functions outside-in on the left-hand-side, so it has the type `lookup (insert …) = …` where the `insert` is on a list. Notations mean it doesn’t actually look like this and the insert is textually first.
* Operations that "extract" from the data structure (`lookup`, `elem_of`, ...) should come before operations that "alter" the data structure (`filter`, `insert`, `union`, `fmap`). For example, use `map_lookup_filter` instead of `map_filter_lookup`.
* Injectivity theorems are instances of `Inj` and then are used with `inj`
* Suffixes `_l` and `_r` when we have binary `op x y` and a theorem related to the left or right. For example, `sep_mono_l` says bi_sep is monotonic in its left argument (holding the right constant).
* Suffix `'` (prime) is used when `foo'` is a corollary of `foo`. Try to avoid
  these since the name doesn't convey how `foo'` is related to `foo`.
* Given a polymorphic function/relation `f` (e.g., `eq`, `equiv`, `subseteq`), the instance of type `A` is called `A_f_instance`, and we add a lemma `A_f` that characterizes the instance. In case of many instances, this lemma is proved by unfolding the definition of the instance, e.g., `frac_op`, `frac_valid`. However, in some cases, e.g., `list_eq`, `map_eq`, `set_eq` this lemma might require non-trivial proof work.
* For lemmas involving modalities, we usually follow this naming scheme:
    ```
    M1_into_M2: M1 P ⊢ M2 P
    M1_M2_elim: M1 (M2 P) ⊣⊢ M1 P
    M1_elim_M2: M1 (M2 P) ⊣⊢ M2 P
    M1_M2: M1 (M2 P) ⊣⊢ M2 (M1 P)
    ```
* Monotonicity lemmas where the relation can be ambiguous are called `<f>_<relation>_mono`, e.g. `Some_included_mono`.
* For lemmas `f x = g ...` that give a definition of function `f` in terms of `g`, we use `f_as_g`. For example, `map_compose_as_omap : m ∘ₘ n = omap (m !!.) n`.

### Naming algebra libraries

**TODO:** describe any conclusions we came to with the `mono_nat` library

## Parameter order and implicitness for lemmas

* Parameter order is usually from more higher-order to less higher-order (types, functions, plain values), and otherwise follows the order in which variables appear in the lemma statement.
* In new lemmas, arguments should be marked as implicit when they can be inferred by unification in all intended usage scenarios. (If an argument can *sometimes* be inferred, we do not have a clear guideline yet -- consider on a case-by-case basis, for now.)

## Lemma statements

### Iris lemmas: `-∗` vs `⊢`

* For low-level lemmas, in particular if there is a high likelyhood someone would want to rewrite with it / use them in non-proofmode goals (e.g. modality intro rules), use `⊢`
  * `P ⊢ |==£> P`
  * `(|==£> |==£> P) ⊢ |==£> P`
  * `▷ own γ a ⊢ ◇ ∃ b, own γ b ∧ ▷ (a ≡ b)`
  * `(P -∗ Q) i ⊢ (P i -∗ Q i)`
* If a lemma is a Coq implication of Iris entailments (where the entailments are visible, not hidden behind e.g. `Persistent`), then use `⊢`
  * `(P1 ⊢ P2) → recv l P1 ⊢ recv l P2`
* Else use -∗
  * `a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'` (curried and hence not rewrite-friendly)

## Metavariables
**TODO:** move these to the right place

* `P` `Q` for bi:PROP (or specifically `iProp Σ`)
* `Φ` and `Ψ` for (?A -> iProp), like postconditions
* `φ` and `ψ` for `Prop`
* `A` `B` for types, ofeT, or cmraT

Suffixes like O, R, UR (already documented)
