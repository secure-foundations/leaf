This file lists "large-ish" changes to the std++ Coq library, but not every
API-breaking change is listed.

## std++ master

- Remove singleton notations `{[ x,y ]}` and `{[ x,y,z ]}` for `{[ (x,y) ]}`
  and `{[ (x,y,z) ]}`. They date back to the time we used the `singleton` class
  with a product for maps (there's now the `singletonM` class).
- Add map notations `{[ k1 := x1 ; .. ; kn := xn ]}` up to arity 13.
  (by Lennard Gäher)
- Add multiset literal notation `{[+ x1; .. ; xn +]}`.
  + Add a new type class `SingletonMS` (with projection `{[+ x +]}` for
    multiset singletons.
  + Define `{[+ x1; .. ; xn +]}` as notation for `{[+ x1 +]} ⊎ .. ⊎ {[+ xn +]}`.
- Remove the `Singleton` and `Semiset` instances for multisets to avoid
  accidental use.
  + This means the notation `{[ x1; .. ; xn ]}` no longer works for multisets
    (previously, its definition was wrong, since it used `∪` instead of `⊎`).
  + Add lemmas for `∈` and `∉` specific for multisets, since the set lemmas no
    longer work for multisets.
- Make `Qc_of_Z'` not an implicit coercion (from `Z` to `Qc`) any more.
- Make `Z.of_nat'` not an implicit coercion (from `nat` to `Z`) any more.
- Rename `decide_left` → `decide_True_pi` and `decide_right` → `decide_False_pi`.
- Add `option_guard_True_pi`.
- Add lemma `surjective_finite`. (by Alix Trieu)
- Add type classes `TCFalse`, `TCUnless`, `TCExists`, and `TCFastDone`. (by
  Michael Sammler)
- Add various results about bit representations of `Z`. (by Michael Sammler)
- Add tactic `learn_hyp`. (by Michael Sammler)
- Add `Countable` instance for decidable Sigma types. (by Simon Gregersen)
- Add tactics `compute_done` and `compute_by` for solving goals by computation.
- Add `Inj` instances for `fmap` on option and maps.
- Various changes to `Permutation` lemmas:
  + Rename `Permutation_nil` → `Permutation_nil_r`,
    `Permutation_singleton` → `Permutation_singleton_r`, and
    `Permutation_cons_inv` → `Permutation_cons_inv_r`.
  + Add lemmas `Permutation_nil_l`, `Permutation_singleton_l`, and
    `Permutation_cons_inv_l`.
  + Add new instance `cons_Permutation_inj_l : Inj (=) (≡ₚ) (.:: k).`.
  + Add lemma `Permutation_cross_split`.
  + Make lemma `elem_of_Permutation` a biimplication
- Add function `kmap` to transform the keys of finite maps.
- Set `Hint Mode` for the classes `PartialOrder`, `TotalOrder`, `MRet`, `MBind`,
  `MJoin`, `FMap`, `OMap`, `MGuard`, `SemiSet`, `Set_`, `TopSet`, and `Infinite`.
- Strengthen the extensionality lemmas `map_filter_ext` and
  `map_filter_strong_ext`:
  + Rename `map_filter_strong_ext` → `map_filter_strong_ext_1` and
    `map_filter_ext` → `map_filter_ext_1`.
  + Add new bidirectional lemmas `map_filter_strong_ext` and `map_filter_ext`.
  + Add `map_filter_strong_ext_2` and `map_filter_ext_2`.
- Make collection of lemmas for filter + union/disjoint consistent for sets and
  maps:
  + Sets: Add lemmas `disjoint_filter`, `disjoint_filter_complement`, and
    `filter_union_complement`.
  + Maps: Rename `map_disjoint_filter` → `map_disjoint_filter_complement` and
    `map_union_filter` → `map_filter_union_complement` to be consistent with sets.
  + Maps: Add lemmas `map_disjoint_filter` and `map_filter_union` analogous to
    sets.
- Add cross split lemma `map_cross_split` for maps
- Setoid results for options:
  + Add instance `option_fmap_equiv_inj`.
  + Add `Proper` instances for `union`, `union_with`, `intersection_with`, and
    `difference_with`.
  + Rename instances `option_mbind_proper` → `option_bind_proper` and
    `option_mjoin_proper` → `option_join_proper` to be consistent with similar
    instances for sets and lists.
  + Rename `equiv_None` → `None_equiv_eq`.
  + Replace `equiv_Some_inv_l`, `equiv_Some_inv_r`, `equiv_Some_inv_l'`, and
    `equiv_Some_inv_r'` by new lemma `Some_equiv_eq` that follows the pattern of
    other `≡`-inversion lemmas: it uses a `↔` and puts the arguments of `≡` and
    `=` in consistent order.
- Setoid results for lists:
  + Add `≡`-inversion lemmas `nil_equiv_eq`, `cons_equiv_eq`,
    `list_singleton_equiv_eq`,  and `app_equiv_eq`.
  + Add lemmas `Permutation_equiv` and `equiv_Permutation`.
- Setoid results for maps:
  + Add instances `map_singleton_equiv_inj` and `map_fmap_equiv_inj`.
  + Add and generalize many `Proper` instances.
  + Add lemma `map_equiv_lookup_r`.
  + Add lemma `map_equiv_iff`.
  + Rename `map_equiv_empty` → `map_empty_equiv_eq`.
  + Add `≡`-inversion lemmas `insert_equiv_eq`, `delete_equiv_eq`,
    `map_union_equiv_eq`, etc.
- Drop `DiagNone` precondition of `lookup_merge` rule of `FinMap` interface.
  + Drop `DiagNone` class.
  + Add `merge_proper` instance.
  + Simplify lemmas about `merge` by dropping the `DiagNone` precondition.
  + Generalize lemmas `partial_alter_merge`, `partial_alter_merge_l`, and
    `partial_alter_merge_r`.
  + Drop unused `merge_assoc'` instance.
- Improvements to `head` and `tail` functions for lists:
  + Define `head` as notation that prints (Coq defines it as `parsing only`)
    similar to `tail`.
  + Declare `tail` as `simpl nomatch`.
  + Add lemmas about `head` and `tail`.
- Add and extend equivalences between closure operators:
  - Add `↔` lemmas that relate `rtc`, `tc`, `nsteps`, and `bsteps`.
  - Rename `→` lemmas `rtc_nsteps` → `rtc_nsteps_1`,
    `nsteps_rtc` → `rtc_nsteps_2`, `rtc_bsteps` → `rtc_bsteps_1`, and
    `bsteps_rtc` → `rtc_bsteps_2`.
  - Add lemmas that relate `rtc`, `tc`, `nsteps`, and `bsteps` to path
    representations as lists.
- Remove explicit equality from cross split lemmas so that they become easier
  to use in forward-style proofs.
- Add lemmas for finite maps: `dom_map_zip_with`, `dom_map_zip_with_L`,
  `map_filter_id`, `map_filter_subseteq`, and `map_lookup_zip_Some`.
- Add lemmas for sets: `elem_of_weaken` and `not_elem_of_weaken`.
- Rename `insert_delete` → `insert_delete_insert`; add new `insert_delete` that
  is consistent with `delete_insert`.
- Fix statement of `sum_inhabited_r`. (by Paolo G. Giarrusso)

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E '
s/\bdecide_left\b/decide_True_pi/g
s/\bdecide_right\b/decide_False_pi/g
# Permutation
s/\bPermutation_nil\b/Permutation_nil_r/g
s/\bPermutation_singleton\b/Permutation_singleton_r/g
s/\Permutation_cons_inv\b/Permutation_cons_inv_r/g
# Filter
s/\bmap_disjoint_filter\b/map_disjoint_filter_complement/g
s/\bmap_union_filter\b/map_filter_union_complement/g
# mbind
s/\boption_mbind_proper\b/option_bind_proper/g
s/\boption_mjoin_proper\b/option_join_proper/g
# relations
s/\brtc_nsteps\b/rtc_nsteps_1/g
s/\bnsteps_rtc\b/rtc_nsteps_2/g
s/\brtc_bsteps\b/rtc_bsteps_1/g
s/\bbsteps_rtc\b/rtc_bsteps_2/g
# setoid
s/\bequiv_None\b/None_equiv_eq/g
s/\bmap_equiv_empty\b/map_empty_equiv_eq/g
# insert_delete
s/\binsert_delete\b/insert_delete_insert/g
# filter extensionality lemmas
s/\bmap_filter_ext\b/map_filter_ext_1/g
s/\bmap_filter_strong_ext\b/map_filter_strong_ext_1/g
' $(find theories -name "*.v")
```

## std++ 1.5.0 (2021-02-16)

Coq 8.13 is newly supported by this release, Coq 8.8 and 8.9 are no longer
supported.

This release of std++ was managed by Ralf Jung and Robbert Krebbers, with
contributions by Alix Trieu, Dan Frumin, Hugo Herbelin, Paulo Emílio de Vilhena,
Simon Friis Vindum, and Tej Chajed.  Thanks a lot to everyone involved!

- Overhaul of the theory of positive rationals `Qp`:
  + Add `max` and `min` operations for `Qp`.
  + Add the orders `Qp_le` and `Qp_lt`.
  + Rename `Qp_plus` into `Qp_add` and `Qp_mult` into `Qp_mul` to be consistent
    with the corresponding names for `nat`, `N`, and `Z`.
  + Add a function `Qp_inv` for the multiplicative inverse.
  + Define the division function `Qp_div` in terms of `Qp_inv`, and generalize
    the second argument from `positive` to `Qp`.
  + Add a function `pos_to_Qp` that converts a `positive` into a positive
    rational `Qp`.
  + Add many lemmas and missing type class instances, especially for orders,
    multiplication, multiplicative inverse, division, and the conversion.
  + Remove the coercion from `Qp` to `Qc`. This follows our recent tradition of
    getting rid of coercions since they are more often confusing than useful.
  + Rename the conversion from `Qp_car : Qp → Qc` into `Qp_to_Qc` to be
    consistent with other conversion functions in std++. Also rename the lemma
    `Qp_eq` into `Qp_to_Qc_inj_iff`.
  + Use `let '(..) = ...` in the definitions of `Qp_plus`, `Qp_mult`, `Qp_inv`,
    `Qp_le` and `Qp_lt` to avoid Coq tactics (like `injection`) to unfold these
    definitions eagerly.
  + Define the `Qp` literals 1, 2, 3, 4 in terms of `pos_to_Qp` instead of
    iterated addition.
  + Rename and restate many lemmas so as to be consistent with the conventions
    for Coq's number types `nat`, `N`, and `Z`.
- Add `rename select <pat> into <name>` tactic to find a hypothesis by pattern
  and give it a fixed name.
- Add `eunify` tactic that lifts Coq's `unify` tactic to `open_constr`.
- Generalize `omap_insert`, `omap_singleton`, `map_size_insert`, and
  `map_size_delete` to cover the `Some` and `None` case. Add `_Some` and `_None`
  versions of the lemmas for the specific cases.
- Rename `dom_map filter` → `dom_filter`, `dom_map_filter_L` → `dom_filter_L`,
  and `dom_map_filter_subseteq` → `dom_filter_subseteq` for consistency's sake.
- Remove unused notations `∪**`, `∪*∪**`, `∖**`, `∖*∖**`, `⊆**`, `⊆1*`, `⊆2*`,
  `⊆1**`, `⊆2**"`, `##**`, `##1*`, `##2*`, `##1**`, `##2**` for nested
  `zip_with` and `Forall2` versions of `∪`, `∖`, and `##`.
- Remove unused type classes `DisjointE`, `DisjointList`, `LookupE`, and
  `InsertE`.
- Fix a bug where `pretty 0` was defined as `""`, the empty string. It now
  returns `"0"` for `N`, `Z`, and `nat`.
- Remove duplicate `map_fmap_empty` of `fmap_empty`, and rename
  `map_fmap_empty_inv` into `fmap_empty_inv` for consistency's sake.
- Rename `seq_S_end_app` to `seq_S`. (The lemma `seq_S` is also in Coq's stdlib
  since Coq 8.12.)
- Remove `omega` import and hint database in `tactics` file.
- Remove unused `find_pat` tactic that was made mostly obsolete by `select`.
- Rename `_11` and `_12` into `_1_1` and `_1_2`, respectively. These suffixes
  are used for `A → B1` and `A → B2` variants of `A ↔ B1 ∧ B2` lemmas.
- Rename `Forall_Forall2` → `Forall_Forall2_diag` to be consistent with the
  names for big operators in Iris.
- Rename set equality and equivalence lemmas:
  `elem_of_equiv_L` → `set_eq`,
  `set_equiv_spec_L` → `set_eq_subseteq`,
  `elem_of_equiv` → `set_equiv`,
  `set_equiv_spec` → `set_equiv_subseteq`.
- Remove lemmas `map_filter_iff` and `map_filter_lookup_eq` in favor of the stronger
  extensionality lemmas `map_filter_ext` and `map_filter_strong_ext`.

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i -E '
s/\bQp_plus\b/Qp_add/g
s/\bQp_mult\b/Qp_mul/g
s/\bQp_mult_1_l\b/Qp_mul_1_l/g
s/\bQp_mult_1_r\b/Qp_mul_1_r/g
s/\bQp_plus_id_free\b/Qp_add_id_free/g
s/\bQp_not_plus_ge\b/Qp_not_add_le_l/g
s/\bQp_le_plus_l\b/Qp_le_add_l/g
s/\bQp_mult_plus_distr_l\b/Qp_mul_add_distr_r/g
s/\bQp_mult_plus_distr_r\b/Qp_mul_add_distr_l/g
s/\bmap_fmap_empty\b/fmap_empty/g
s/\bmap_fmap_empty_inv\b/fmap_empty_inv/g
s/\bseq_S_end_app\b/seq_S/g
s/\bomap_insert\b/omap_insert_Some/g
s/\bomap_singleton\b/omap_singleton_Some/g
s/\bomap_size_insert\b/map_size_insert_None/g
s/\bomap_size_delete\b/map_size_delete_Some/g
s/\bNoDup_cons_11\b/NoDup_cons_1_1/g
s/\bNoDup_cons_12\b/NoDup_cons_1_2/g
s/\bmap_filter_lookup_Some_11\b/map_filter_lookup_Some_1_1/g
s/\bmap_filter_lookup_Some_12\b/map_filter_lookup_Some_1_2/g
s/\bmap_Forall_insert_11\b/map_Forall_insert_1_1/g
s/\bmap_Forall_insert_12\b/map_Forall_insert_1_2/g
s/\bmap_Forall_union_11\b/map_Forall_union_1_1/g
s/\bmap_Forall_union_12\b/map_Forall_union_1_2/g
s/\bForall_Forall2\b/Forall_Forall2_diag/g
s/\belem_of_equiv_L\b/set_eq/g
s/\bset_equiv_spec_L\b/set_eq_subseteq/g
s/\belem_of_equiv\b/set_equiv/g
s/\bset_equiv_spec\b/set_equiv_subseteq/g
' $(find theories -name "*.v")
```

## std++ 1.4.0 (released 2020-07-15)

Coq 8.12 is newly supported by this release, and Coq 8.7 is no longer supported.

This release of std++ received contributions by Gregory Malecha, Michael
Sammler, Olivier Laurent, Paolo G. Giarrusso, Ralf Jung, Robbert Krebbers,
sarahzrf, and Tej Chajed.

- Rename `Z2Nat_inj_div` and `Z2Nat_inj_mod` to `Nat2Z_inj_div` and
  `Nat2Z_inj_mod` to follow the naming convention of `Nat2Z` and
  `Z2Nat`. Re-purpose the names `Z2Nat_inj_div` and `Z2Nat_inj_mod` for be the
  lemmas they should actually be.
- Add `rotate` and `rotate_take` functions for accessing a list with
  wrap-around. Also add `rotate_nat_add` and `rotate_nat_sub` for
  computing indicies into a rotated list.
- Add the `select` and `revert select` tactics for selecting and
  reverting a hypothesis based on a pattern.
- Extract `list_numbers.v` from `list.v` and `numbers.v` for
  functions, which operate on lists of numbers (`seq`, `seqZ`,
  `sum_list(_with)` and `max_list(_with)`). `list_numbers.v` is
  exported by the prelude. This is a breaking change if one only
  imports `list.v`, but not the prelude.
- Rename `drop_insert` into `drop_insert_gt` and add `drop_insert_le`.
- Add `Countable` instance for `Ascii.ascii`.
- Make lemma `list_find_Some` more apply friendly.
- Add `filter_app` lemma.
- Add tactic `multiset_solver` for solving goals involving multisets.
- Rename `fin_maps.singleton_proper` into `singletonM_proper` since it concerns
  `singletonM` and to avoid overlap with `sets.singleton_proper`.
- Add `wn R` for weakly normalizing elements w.r.t. a relation `R`.
- Add `encode_Z`/`decode_Z` functions to encode elements of a countable type
  as integers `Z`, in analogy with `encode_nat`/`decode_nat`.
- Fix list `Datatypes.length` and string `strings.length` shadowing (`length`
  should now always be `Datatypes.length`).
- Change the notation for pattern matching monadic bind into `'pat ← x; y`. It
  was `''pat ← x; y` (with double `'`) due to a shortcoming of Coq ≤8.7.

## std++ 1.3.0 (released 2020-03-18)

Coq 8.11 is supported by this release.

This release of std++ received contributions by Amin Timany, Armaël Guéneau,
Dan Frumin, David Swasey, Jacques-Henri Jourdan, Michael Sammler, Paolo G.
Giarrusso, Pierre-Marie Pédrot, Ralf Jung, Robbert Krebbers, Simon Friis Vindum,
Tej Chajed, and William Mansky

Noteworthy additions and changes:

- Rename `dom_map_filter` into `dom_map_filter_subseteq` and repurpose
  `dom_map_filter` for the version with the equality. This follows the naming
  convention for similar lemmas.
- Generalize `list_find_Some` and `list_find_None` to become bi-implications.
- Disambiguate Haskell-style notations for partially applied operators. For
  example, change `(!! i)` into `(.!! x)` so that `!!` can also be used as a
  prefix, as done in VST. A sed script to perform the renaming can be found at:
  https://gitlab.mpi-sws.org/iris/stdpp/merge_requests/93
- Add type class `TopSet` for sets with a `⊤` element. Provide instances for
  `boolset`, `propset`, and `coPset`.
- Add `set_solver` support for `dom`.
- Rename `vec_to_list_of_list` into `vec_to_list_to_vec`, and add new lemma
  `list_to_vec_to_list` for the converse.
- Rename `fin_of_nat` into `nat_to_fin`, `fin_to_of_nat` into
  `fin_to_nat_to_fin`, and `fin_of_to_nat` into `nat_to_fin_to_nat`, to follow
  the conventions.
- Add `Countable` instance for `vec`.
- Introduce `destruct_or{?,!}` to repeatedly destruct disjunctions in
  assumptions. The tactic can also be provided an explicit assumption name;
  `destruct_and{?,!}` has been generalized accordingly and now can also be
  provided an explicit assumption name.
  Slight breaking change: `destruct_and` no longer handle `False`;
  `destruct_or` now handles `False` while `destruct_and` handles `True`,
  as the respective units of disjunction and conjunction.
- Add tactic `set_unfold in H`.
- Set `Hint Mode` for `TCAnd`, `TCOr`, `TCForall`, `TCForall2`, `TCElemOf`,
  `TCEq`, and `TCDiag`.
- Add type class `LookupTotal` with total lookup operation `(!!!) : M → K → A`.
  Provide instances for `list`, `fin_map`, and `vec`, as well as corresponding
  lemmas for the operations on these types. The instance for `vec` replaces the
  ad-hoc `!!!` definition. As a consequence, arguments of `!!!` are no longer
  parsed in `vec_scope` and `fin_scope`, respectively. Moreover, since `!!!`
  is overloaded, coercions around `!!!` no longer work.
- Make lemmas for `seq` and `seqZ` consistent:
  + Rename `fmap_seq` → `fmap_S_seq`
  + Add `fmap_add_seq`, and rename `seqZ_fmap` → `fmap_add_seqZ`
  + Rename `lookup_seq` → `lookup_seq_lt`
  + Rename `seqZ_lookup_lt` → `lookup_seqZ_lt`,
    `seqZ_lookup_ge` → `lookup_seqZ_ge`, and `seqZ_lookup` → `lookup_seqZ`
  + Rename `lookup_seq_inv` → `lookup_seq` and generalize it to a bi-implication
  + Add `NoDup_seqZ` and `Forall_seqZ`

The following `sed` script should perform most of the renaming
(on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i '
s/\bdom_map_filter\b/dom_map_filter_subseteq/g
s/\bfmap_seq\b/fmap_S_seq/g
s/\bseqZ_fmap\b/fmap_add_seqZ/g
s/\blookup_seq\b/lookup_seq_lt/g
s/\blookup_seq_inv\b/lookup_seq/g
s/\bseqZ_lookup_lt\b/lookup_seqZ_lt/g
s/\bseqZ_lookup_ge\b/lookup_seqZ_ge/g
s/\bseqZ_lookup\b/lookup_seqZ/g
s/\bvec_to_list_of_list\b/vec_to_list_to_vec/g
s/\bfin_of_nat\b/nat_to_fin/g
s/\bfin_to_of_nat\b/fin_to_nat_to_fin/g
s/\bfin_of_to_nat\b/nat_to_fin_to_nat/g
' $(find theories -name "*.v")
```

## std++ 1.2.1 (released 2019-08-29)

This release of std++ received contributions by Dan Frumin, Michael Sammler,
Paolo G. Giarrusso, Paulo Emílio de Vilhena, Ralf Jung, Robbert Krebbers,
Rodolphe Lepigre, and Simon Spies.

Noteworthy additions and changes:

- Introduce `max` and `min` infix notations for `N` and `Z` like we have for `nat`.
- Make `solve_ndisj` tactic more powerful.
- Add type class `Involutive`.
- Improve `naive_solver` performance in case the goal is trivially solvable.
- Add a bunch of new lemmas for list, set, and map operations.
- Rename `lookup_imap` into `map_lookup_imap`.

## std++ 1.2.0 (released 2019-04-26)

Coq 8.9 is supported by this release, but Coq 8.6 is no longer supported. Use
std++ 1.1 if you have to use Coq 8.6. The repository moved to a new location at
https://gitlab.mpi-sws.org/iris/stdpp and automatically generated Coq-doc of
master is available at https://plv.mpi-sws.org/coqdoc/stdpp/.

This release of std++ received contributions by Dan Frumin, Hai Dang, Jan-Oliver
Kaiser, Mackie Loeffel, Maxime Dénès, Ralf Jung, Robbert Krebbers, and Tej
Chajed.

New features:

- New notations `=@{A}`, `≡@{A}`, `∈@{A}`, `∉@{A}`, `##@{A}`, `⊆@{A}`, `⊂@{A}`,
  `⊑@{A}`, `≡ₚ@{A}` for being explicit about the type.
- A definition of basic telescopes `tele` and some theory about them.
- A simple type class based canceler `NatCancel` for natural numbers.
- A type `binder` for anonymous and named binders to be used in program language
  definitions with string-based binders.
- More results about `set_fold` on sets and multisets.
- Notions of infinite and finite predicates/sets and basic theory about them.
- New operation `map_seq`.
- The symmetric and reflexive/transitive/symmetric closure of a relation (`sc`
  and `rtsc`, respectively).
- Different notions of confluence (diamond property, confluence, local
  confluence) and the relations between these.
- A `size` function for finite maps and prove some properties.
- More results about `Qp` fractions.
- More miscellaneous results about sets, maps, lists, multisets.
- Various type class utilities, e.g. `TCEq`, `TCIf`, `TCDiag`, `TCNoBackTrack`,
  and `tc_to_bool`.
- Generalize `gset_to_propset` to `set_to_propset` for any `SemiSet`.

Changes:

- Consistently use `lia` instead of `omega` everywhere.
- Consistently block `simpl` on all `Z` operations.
- The `Infinite` class is now defined using a function `fresh : list A → A`
  that given a list `xs`, gives an element `fresh xs ∉ xs`.
- Make `default` an abbreviation for `from_option id` (instead of just swapping
  the argument order of `from_option`).
- More efficient `Countable` instance for `list` that is linear instead of
  exponential.
- Improve performance of `set_solver` significantly by introducing specialized
  type class `SetUnfoldElemOf` for propositions involving `∈`.
- Make `gset` a `Definition` instead of a `Notation` to improve performance.
- Use `disj_union` (notation `⊎`) for disjoint union on multisets (that adds the
  multiplicities). Repurpose `∪` on multisets for the actual union (that takes
  the max of the multiplicities).
- Set `Hint Mode` for `pretty`.

Naming:

- Consistently use the `set` prefix instead of the `collection` prefix for
  definitions and lemmas.
- Renaming of classes:
  + `Collection` into `Set_` (`_` since `Set` is a reserved keyword)
  + `SimpleCollection` into `SemiSet`
  + `FinCollection` into `FinSet`
  + `CollectionMonad` into `MonadSet`
- Types:
  + `set A := A → Prop` into `propset`
  + `bset := A → bool` into `boolset`.
- Files:
  + `collections.v` into `sets.v`
  + `fin_collections.v` into `fin_sets.v`
  + `bset` into `boolset`
  + `set` into `propset`
- Consistently use the naming scheme `X_to_Y` for conversion functions, e.g.
  `list_to_map` instead of the former `map_of_list`.

The following `sed` script should perform most of the renaming:

```
sed '
s/SimpleCollection/SemiSet/g;
s/FinCollection/FinSet/g;
s/CollectionMonad/MonadSet/g;
s/Collection/Set\_/g;
s/collection\_simple/set\_semi\_set/g;
s/fin\_collection/fin\_set/g;
s/collection\_monad\_simple/monad\_set\_semi\_set/g;
s/collection\_equiv/set\_equiv/g;
s/\bbset/boolset/g;
s/mkBSet/BoolSet/g;
s/mkSet/PropSet/g;
s/set\_equivalence/set\_equiv\_equivalence/g;
s/collection\_subseteq/set\_subseteq/g;
s/collection\_disjoint/set\_disjoint/g;
s/collection\_fold/set\_fold/g;
s/collection\_map/set\_map/g;
s/collection\_size/set\_size/g;
s/collection\_filter/set\_filter/g;
s/collection\_guard/set\_guard/g;
s/collection\_choose/set\_choose/g;
s/collection\_ind/set\_ind/g;
s/collection\_wf/set\_wf/g;
s/map\_to\_collection/map\_to\_set/g;
s/map\_of\_collection/set\_to\_map/g;
s/map\_of\_list/list\_to\_map/g;
s/map\_of\_to_list/list\_to\_map\_to\_list/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/\bof\_list/list\_to\_set/g;
s/\bof\_option/option\_to\_set/g;
s/elem\_of\_of\_list/elem\_of\_list\_to\_set/g;
s/elem\_of\_of\_option/elem\_of\_option\_to\_set/g;
s/collection\_not\_subset\_inv/set\_not\_subset\_inv/g;
s/seq\_set/set\_seq/g;
s/collections/sets/g;
s/collection/set/g;
s/to\_gmap/gset\_to\_gmap/g;
s/of\_bools/bools\_to\_natset/g;
s/to_bools/natset\_to\_bools/g;
s/coPset\.of_gset/gset\_to\_coPset/g;
s/coPset\.elem\_of\_of\_gset/elem\_of\_gset\_to\_coPset/g;
s/of\_gset\_finite/gset\_to\_coPset\_finite/g;
s/set\_seq\_S\_disjoint/set\_seq\_S\_end\_disjoint/g;
s/set\_seq\_S\_union/set\_seq\_S\_end\_union/g;
s/map\_to\_of\_list/map\_to\_list\_to\_map/g;
s/of\_bools/bools\_to\_natset/g;
s/to\_bools/natset\_to\_bools/g;
' -i $(find -name "*.v")
```

## std++ 1.1.0 (released 2017-12-19)

Coq 8.5 is no longer supported by this release of std++.  Use std++ 1.0 if you
have to use Coq 8.5.

New features:

- Many new lemmas about lists, vectors, sets, maps.
- Equivalence proofs between std++ functions and their alternative in the the
  Coq standard library, e.g. `List.nth`, `List.NoDop`.
- Typeclass versions of the logical connectives and list predicates:
  `TCOr`, `TCAnd`, `TCTrue`, `TCForall`, `TCForall2`.
- A function `tc_opaque` to make definitions type class opaque.
- A type class `Infinite` for infinite types.
- A generic implementation to obtain fresh elements of infinite types.
- More theory about curry and uncurry functions on `gmap`.
- A generic `filter` and `zip_with` operation on finite maps.
- A type of generic trees for showing that arbitrary types are countable.

Changes:

- Get rid of `Automatic Coercions Import`, it is deprecated.
  Also get rid of `Set Asymmetric Patterns`.
- Various changes and improvements to `f_equiv` and `solve_proper`.
- `Hint Mode` is now set for all operational type classes to make instance
  search less likely to diverge.
- New type class `RelDecision` for decidable relations, and `EqDecision` is
  defined in terms of it. This class allows to set `Hint Mode` properly.
- Use the flag `assert` of `Arguments` to make it more robust.
- The functions `imap` and `imap2` on lists are defined so that they enjoy more
  definitional equalities.
- Theory about `fin` is moved to its own file `fin.v`.
- Rename `preserving` → `mono`.

Changes to notations:

- Operational type classes for lattice notations: `⊑`,`⊓`, `⊔`, `⊤` `⊥`.
- Replace `⊥` for disjointness with `##`, so that `⊥` can be used for the
  bottom lattice element.
- All notations are now in `stdpp_scope` with scope key `stdpp`
  (formerly `C_scope` and `C`).
- Higher precedence for `.1` and `.2` that is compatible with ssreflect.
- Various changes to monadic notations to improve compatibility with Mtac2:
  + Pattern matching notation for monadic bind `'pat ← x; y` where `pat` can
    be any Coq pattern.
  + Change the level of the do-notation.
  + `<$>` is left associative.
  + Notation `x ;; y` for `_ ← x; y`.

## History

Coq-std++ has originally been developed by Robbert Krebbers as part of his
formalization of the C programming language in his PhD thesis, called
[CH2O](http://robbertkrebbers.nl/thesis.html). After that, Coq-std++ has been
part of the [Iris project](http://iris-project.org), and has continued to be
developed by Robbert Krebbers, Ralf Jung, and Jacques Henri-Jourdan.
