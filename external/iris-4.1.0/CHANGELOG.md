In this changelog, we document "large-ish" changes to Iris that affect even the
way the logic is used on paper.  We also document changes in the Coq
development; every API-breaking change should be listed, but not every new
lemma.

## Iris 4.1.0 (2023-10-11)

This Iris release mostly features quality-of-life improvements, such as smarter
handling of `->`/`<-` patters by `iDestruct`, support for an arbitrary number of
Coq intro patterns in the Iris proofmode tactics (`iIntros`, `iDestruct`, etc.),
and support for immediately introducing the postcondition of a WP specification
via `wp_apply lemma as "Hpost"`.

The biggest changes and new features are:
* Logically atomic triples now support private (non-atomic) postconditions, and
  the notation was changed to not clash with Autosubst any more. Existing users
  of logically atomic specifications have to update their notation, see the full
  CHANGELOG for more details.
* The meaning of `P -∗ Q` as a Coq proposition has changed from `P ⊢ Q` to
  `⊢ P -∗ Q`. If you are only using the Iris proofmode, this will not make a
  difference, but when writing proof scripts or tactics that `rewrite` or
  `apply` Iris lemmas, the exact position of the `⊢ P -∗ Q` matters and this
  will now always be visible in lemma statements.
* `iCombine` is starting to gain support for a `gives` clause, which yields
  persistent facts gained from combining the resources. So far, this remains
  mostly experimental. We support `↦` and the connectives of ghost theories in
  `base_logic/lib`, but support for `own` and custom cameras is minimal and will
  be improved in future releases.
* Some initial refactoring prepares Iris for eventually supporting transfinite step-indexing.
* New resources algebras have been added: `Z`, `max_Z`, `mono_Z`, and `mra` (the
  monotone resource algebra of https://iris-project.org/pdfs/2021-CPP-monotone-final.pdf)

Iris 4.1 supports Coq 8.16-Coq 8.18. Coq 8.13-8.15 are no longer supported.

This release was managed by Ralf Jung, Robbert Krebbers, and Johannes Hostert,
with contributions from Amin Timany, Arthur Azevedo de Amorim, Armaël Guéneau,
Benjamin Peters, Dan Frumin, Dorian Lesbre, Ike Mulder, Isaac van Bakel, Jaemin
Choi, Janine Lohse, Jan-Oliver Kaiser, Jonas Kastberg Hinrichsen, Lennard Gäher,
Mathias Adam Møller, Michael Sammler, Paolo Giarrusso, Pierre Roux, Rodolphe
Lepigre, Simcha van Collem, Simon Friis Vindum, Simon Spies, Tej Chajed, Yicuan
Chen, and Yusuke Matsushita. Thanks a lot to everyone involved!


**Changes in `prelude`:**

* Re-export `stdpp.options` from `iris.prelude.options`. This enables 'light'
  name mangling, which prefixes auto-generated names with `__`. This only
  affects developments that explicitly opt-in to following the Iris
  configuration by importing `iris.prelude.options`.

**Changes in `algebra`:**

* Add (basic) support for `gset` and `gset_disj` cameras to `set_solver`.
* Rename `sig_{equiv,dist}_alt` into `sig_{equiv,dist}_def` and state these
  lemmas using `=` instead of `<->`.
* Add custom entry `dfrac` that can be used for `{dq}` / `□` / `{# q}`
  annotation of connectives with a discardable fraction.
* Add an RA on the `Z` type of integers, using addition for `⋅`.
* Prepare Iris to generalize the type of step-indices. This is a large series of
  changes; more changes will follow later. More documentation will follow as
  part of
  [this merge request](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/888).
  - Change the definition of `dist_later` to an equivalent definition that is
    future-proof with respect to general step-indices.
  - Change the definition of the properties of an `ofe` to be slightly more
    general and future proof (i.e., change `dist_S` into `dist_lt`).
  - Adapt `f_contractive` to work with the new definition of `dist_later`.
    For backwards compatibility for existing developments, the tactic
    `f_contractive_fin` is provided. It uses the old definition of `dist_later`,
    now called `dist_later_fin`.
  - If you need to deal with a `dist_later`/`dist_later_fin` in a manual proof,
    use the tactic `dist_later_intro`/`dist_later_fin_intro` to introduce it.
  (by Michael Sammler, Lennard Gäher, and Simon Spies)
* Add `max_Z` and `mono_Z` cameras.
* Add `dfrac_valid`.
* Rename `Some_included_2` to `Some_included_mono`.
* Consistently use `Some x ≼ Some y` to express the reflexive closure of
  `x ≼ y`. This changes the statements of some lemmas: `singleton_included`,
  `local_update_valid0`, `local_update_valid`. Also add various new
  `Some_included` lemmas to help deal with these assertions.
* Add hints for `a ≼ a ⋅ _` / `a ≼ _ ⋅ a` / `ε ≼ _` / `_ ≼ CsumBot` /
  `_ ≼ ExclBot` with cost 0, which means they are used by `done` to finish
  proofs. (by Ike Mulder)
* Rename `singleton_mono` to `singleton_included_mono`.
* Use `Strategy expand` for CMRA/UCMRA coercions and most projections to improve
  performance of type-checking some large CMRA/OFE types. (by Ike Mulder)
* Add monotone resource algebra, `algebra/mra.v`, to enable reasoning about
  monotonicity with respect to an arbitrary preorder relation: the extension order
  of `mra R` is designed to embed the preorder relation `R`. (by Amin Timany)
* Rename instances `union_with_proper` → `union_with_ne`,
  `map_fmap_proper` → `map_fmap_ne`, `map_zip_with_proper` → `map_zip_with_ne`.
* Rename `dist_option_Forall2` → `option_dist_Forall2`. Add similar lemma
  `list_dist_Forall2`.
* Add instances `option_fmap_dist_inj` and `list_fmap_dist_inj`.
* Rename `list_dist_cons_inv_r` → `cons_dist_eq` and remove
  `list_dist_cons_inv_l` to be consistent with `cons_equiv_eq` in std++.
  (If you needed `list_dist_cons_inv_l`, you can apply `symmetry` and
  then use `cons_dist_eq`.)
  Add similar lemmas `nil_dist_eq`, `app_dist_eq`, `list_singleton_dist_eq`,
  `dist_Permutation`.

**Changes in `bi`:**

* Use `binder` in notations for big ops. This means one can write things such
  as `[∗ map] '(k,_) ↦ '(_,y) ∈ m, ⌜ k = y ⌝`.
* Add constructions `bi_tc`/`bi_nsteps` to create the transitive/`n`-step
  closure of a PROP-level binary relation. (by Simcha van Collem)
* Make the `unseal` tactic of `monPred` more consistent with `uPred`:
  + Rename `MonPred.unseal` → `monPred.unseal`
  + No longer unfold derived BI connectives `<affine>`, `<absorb>` and `◇`.
  * Make `monPred.unseal` tactic more robust by using types to unfold the right
    BI projections.
* Add `unseal` tactic for `siProp`.
* Add compatibility lemmas for `big_sepL <-> big_sepL2`, `big_sepM <-> big_sepM2`
  with list/maps of pairs; and `big_sepM <-> big_sepL` via `list_to_map` and
  `map_to_list`. (by Dorian Lesbre)
* Make `persistently_True` a bi-entailment; this changes the default `rewrite`
  direction.
* Make `BiLaterContractive` a class instead of a notation.
* Make projections of `Bupd`/`Fupd`/`InternalEq`/`Plainly` operational type
  classes `Typeclasses Opaque`.
* Make BI relations (`bi_rtc`, `bi_tc`, `bi_nsteps`) typeclasses opaque (they
  were accidentally transparent).
* Make the `P -∗ Q` notation in stdpp_scope (i.e., outside of bi_scope) a
  shorthand for `⊢ P -∗ Q` rather than `P ⊢ Q`. This means that any BI notation
  used in stdpp_scope will be sugar for adding a leading `⊢` (`bi_emp_valid`).
  It also means that `apply` becomes sensitive to the difference between `P ⊢ Q`
  and `P -∗ Q`, and `rewrite` will only work with lemmas that are explicitly
  written using `⊢`.
  When a proof breaks, there are generally 3 options:
  - Try to find the `-∗` that should be turned into a `⊢` so that things work
    like before.
  - Adjust the proof to use proof mode tactics rather than Coq tactics (in
    particular, replace `apply` by `iApply`).
  - Add some `apply bi.entails_wand`/`apply bi.wand_entails` to 'convert'
    between the old and new way of interpreting `P -∗ Q`.
* Add `auto` hint to introduce the BI version of `↔`.
* Change `big_sepM2_alt` to use `dom m1 = dom2 m2` instead of
  `∀ k, is_Some (m1 !! k) ↔ is_Some (m2 !! k)`. The old lemma is still
  available as `big_sepM2_alt_lookup`.
* Overhaul `Fractional`/`AsFractional`:
  - Remove `AsFractional → Fractional` instance.
  - No longer use `AsFractional P Φ q` backwards, from `Φ` and `q` to `P` -- just
    use `Φ q` instead.
  - Remove multiplication instances (that also go from `AsFractional` to
    `Fractional`, making it very hard to reason about search termination).
  - Rewrite `frame_fractional` lemma using the new `FrameFractionalQp` typeclass
    for `Qp` reasoning.
  - Change statements of `fractional_split`, `fractional_half`, and
    `fractional_merge` to avoid using `AsFractional` backwards, and only keep
    the bi-directional versions (remove `fractional_split_1`,
    `fractional_split_2`, `fractional_half_1`, `fractional_half_2`).
    `iDestruct`/`iCombine`/`iSplitL`/`iSplitR` should be used instead.
* Add missing transitivity, symmetry and reflexivity lemmas about the `↔`, `→`,
  `-∗` and `∗-∗` connectives. (by Ike Mulder)
* Add `∗-∗` as notation in `stdpp_scope` similar to `-∗`. This means `P ∗-∗ Q`
  can be directly used as lemma statement, and is syntactic sugar for `⊢ P ∗-∗ Q`.
* Add `≼` connective (`internal_included`) on the BI level. (by Ike Mulder)
* Move laws of persistence modality out of `BiMixin` into `BiPersistentlyMixin`.
* Provide smart constructor `bi_persistently_mixin_discrete` for
  `BiPersistentlyMixin`: Given a discrete BI that enjoys the existential
  property, a trivial definition of the persistence modality can be given.
* Fix `greatest_fixpoint_ne'` accidentally being about the least fixpoint.
* Add `Plain` instance for `|==> P` when `P` is plain.
* Rename `bupd_plain` → `bupd_elim`.
* Change notation for atomic updates and atomic accessors to use `<{ ... }>`
  instead of `<< ... >>`. This avoids a conflict with Autosubst.

**Changes in `proofmode`:**

* The proof mode introduction patterns "<-" and "->" are considered
  intuitionistic. This means that tactics such as `iDestruct ... as "->"` will
  not dispose of hypotheses to perform the rewrite.
* Remove tactic `iSolveTC` in favor of `tc_solve` in std++.
* The result of `iCombine` is no longer computed with the `FromSep` typeclass,
  but with a new `CombineSepAs` typeclass. If you provide custom `FromSep`
  instances and use the `iCombine` tactic, you will need to define additional
  `CombineSepAs` instances. This is done in preparation for making `iCombine`
  combine propositions in ways that are not appropriate for how `FromSep` is used.
  Note that `FromSep` is still used for determining the new goals when applying
  the `iSplitL` and `iSplitR` tactics.
* The `iCombine` tactic now accepts an (optional) 'gives' clause, with which one
  can learn persistent facts from the combination of two hypotheses. One can
  register such 'gives' clauses by providing instances of the new
  `CombineSepGives` typeclass. The 'gives' clause is still experimental;
  in future versions of Iris it will combine `own` connectives based on the
  validity rules for cameras.
* Make sure that `iStartProof` fails with a proper error message on goals with
  `let`. These `let`s should either be `simpl`ed or introduced into the Coq
  context using `intros x`, `iIntros (x)`, or `iIntros "%x"`.
  This can break some proofs that did `iIntros "?"` on a goal of the shape
  `let ... in P ⊢ Q`.
* Make `iApply`/`iPoseProof`/`iDestruct` more reliable for lemmas whose
  statement involves `let`.
* Remove `string_to_ident`; use `string_to_ident_cps` instead which is in CPS
  form and hence does not require awful hacks.
* The `iFrame` tactic now removes some conjunctions and disjunctions with `False`,
  since additional `MakeOr` and `MakeAnd` instances were provided. If you use these
  classes, their results may have become more concise.
* Support n-ary versions of `iIntros`, `iRevert`, `iExists`, `iDestruct`, `iMod`,
  `iFrame`, `iRevertIntros`, `iPoseProof`, `iInduction`, `iLöb`, `iInv`, and
  `iAssert`. (by Jan-Oliver Kaiser and Rodolphe Lepigre)
* Add tactics `ltac1_list_iter` and `ltac1_list_rev_iter` to iterate over
  lists of `ident`s/`simple intropatterns`/`constr`/etc using Ltac1. See
  [proofmode/base.v](iris/proofmode/base.v) for documentation on how
  to use these tactics to convert your own fixed arity tactics to an n-ary
  variant.
* Improve the `IntoPure` instance for internal equality. Whenever possible,
  `a ≡ b` will now be simplified to `a = b` upon introduction into the pure 
  context. This will break but simplify some existing proofs: 
  `iIntros (H%leibniz_equiv)` should be replaced by `iIntros (H)`. (by Ike Mulder)

**Changes in `base_logic`:**

* Add `mono_Z` library for monotone non-negative integers.
  (This has exactly the same lemmas as `mono_nat`. It is useful in cases
  where one wants to avoid `nat` entirely and use `Z` throughout.)
* Add `IsExcept0` instance for invariants, allowing you to remove laters of
  timeless hypotheses when proving an invariant (without an update).
* Make `uPred.unseal` tactic more robust by using types to unfold the right
  BI projections.
* Turn `internal_eq_entails` into a bi-implication.
* Add lemmas to relate internal/external non-expansiveness and contractiveness.
* Refactor soundness lemmas: `bupd_plain_soundness` → `bupd_soundness`,
  `soundness` → `laterN_soundness` + `pure_soundness`; removed
  `consistency_modal`.
* Strengthen `cmra_valid_elim` to `✓ a ⊢ ⌜ ✓{0} a ⌝`; make `discrete_valid` a
  derived law.
* Remove `frac_validI`. Instead, move to the pure context (with `%` in the proof
  mode or `uPred.discrete_valid` in manual proofs) and use `frac_valid`.

**Changes in `program_logic`:**

* Change the notation for logically atomic triples: we add support for specifying private (non-atomic) postconditions,
  and we avoid a notation conflict with Autosubst. The new notation looks as follows:
  `<<{ ∀∀ x, atomic_pre x }>> code @ ∅ <<{ ∃∃ y, atomic_post x y | z, RET v, non_atomic_post x y z }>>`.
  To keep the notation without private postcondition consistent, the way the return value is specified changes slightly
  even when there is no private postcondition:
  `<<{ ∀∀ x, atomic_pre x }>> code @ ∅ <<{ ∃∃ y, atomic_post x y | RET v }>>`.

**Changes in `heap_lang`:**

* Move operations and lemmas about locations into a module `Loc`.
* Extend `wp_apply` and `wp_smart_apply` to support immediately introducing the
  postcondition into the context via `as (x1 ... xn) "ipat1 ... ipatn"`.
* Add comparison `≤` and `<` for locations. (by Arthur Azevedo de Amorim)
* Make the generic `lock` interface a typeclass and make sure the lock code
  does not depend on `Σ`. Code that is generic about lock implementations, or
  that instantiates that specification, needs adjustment. See
  [iris_heap_lang/lib/lock.v](iris_heap_lang/lib/lock.v) for documentation on
  how to work with this specification.
* Adjust the generic `atomic_heap` interface to follow the same pattern as
  `lock`.
* Add a generic `rwlock` interface and a spinning implementation.
  (by Isaac van Bakel)

**LaTeX changes:**

- Rename `\Alloc` to `\AllocN` and `\Ref` to `\Alloc` for better consistency
  with the Coq names and to avoid clash with hyperref package.

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# iSolveTC
s/iSolveTC\b/tc_solve/g
# _alt -> _def
s/\bsig_equiv_alt\b/sig_equiv_def/g
s/\bsig_dist_alt\b/sig_dist_def/g
# Loc
s/\bloc_add(_assoc|_0|_inj|)\b/Loc.add\1/g
s/\bfresh_locs(_fresh|)\b/Loc.fresh\1/g
# unseal
s/\bMonPred\.unseal\b/monPred\.unseal/g
# big op
s/\bbig_sepM2_alt\b/big_sepM2_alt_lookup/g
s/\bbupd_plain\b/bupd_elim/g
# Logical atomicity (will break Autosubst notation!)
s/<<</<<\{/g
s/>>>/\}>>/g
# option and list
s/\bdist_option_Forall2\b/option_dist_Forall2/g
s/\blist_dist_cons_inv_r\b/cons_dist_eq/g
EOF
```

The following sed script helps adjust LaTeX documents to these changes:
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- *.tex <<EOF
# Alloc & Ref
s/\\Alloc\b/\\AllocN/g
s/\\Ref\b/\\Alloc/g
EOF
```


## Iris 4.0.0 (2022-08-18)

The highlight of Iris 4.0 is the *later credits* mechanism, which provides a new
way to eliminate later modalities.

This new mechanism complements the existing techniques of taking program steps,
exploiting timelessness, and various modality commuting rules. At each program
step, one obtains a credit `£ 1`, which is an ownable Iris resource. These
credits don't have to be used at the present step, but can be saved up, and used
to eliminate laters at any point in the verification using the fancy update
modality. Later credits are particularly useful in proofs where there is not a
one-to-one correspondence between program steps and later eliminations, for
example, logical atomicity proofs. As a consequence, we have been able to
simplify the definition of logical atomicity by removing the 'laterable'
mechanism.

The later credit mechanism is described in detail in the
[ICFP'22 paper](https://plv.mpi-sws.org/later-credits/) and there is a
[small tutorial](https://gitlab.mpi-sws.org/iris/iris/-/blob/iris-4.0.0/tests/later_credits_paper.v)
in the Iris repository. The
[examples](https://gitlab.mpi-sws.org/iris/examples/) repository contains some
logically atomic case studies that make use of later credits: the counter with a
backup (Section 4 of the later credits paper), as well as the elimination stack,
conditional increment, and RDCSS.

Iris 4.0 supports Coq 8.13 - 8.16.

This release was managed by Ralf Jung, Robbert Krebbers, and Lennard Gäher, with
contributions from Glen Mével, Gregory Malecha, Ike Mulder, Irene Yoon,
Jan-Oliver Kaiser, Jonas Kastberg Hinrichsen, Lennard Gäher, Michael Sammler,
Niklas Mück, Paolo G. Giarrusso, Ralf Jung, Robbert Krebbers, Simon Spies,
and Tej Chajed. Thanks a lot to everyone involved!

**General changes:**

- Rename "unsealing" lemmas from `_eq` to `_unseal`. This particularly
  affects `envs_entails_eq`, which is commonly used in the definition of
  custom proof mode tactics. All other unsealing lemmas should be internal, so
  in principle you should not rely on them.
- Rename `coq-iris-staging` package to `coq-iris-unstable`, and also change the
  import path from `iris.staging` to `iris.unstable`.

**Changes in `algebra`:**

* Add some missing algebra functors: `dfrac_agreeRF`, `excl_authURF`, `excl_authRF`,
  `frac_authURF`, `frac_authRF`, `ufrac_authURF`, `ufrac_authRF`, `max_prefix_listURF`,
  `max_prefix_listRF`, `mono_listURF`, and `mono_listRF`.
* Make validy lemmas for `excl_auth` more consistent with `auth`.
  - Rename `excl_auth_frag_validN_op_1_l` into `excl_auth_frag_op_validN` and
    `excl_auth_frag_valid_op_1_l` into `excl_auth_frag_op_valid` (similar to
    `auth_auth_op_valid`), and make them bi-implications.
  - Add `excl_auth_auth_op_validN` and `excl_auth_auth_op_valid`.
* Make validy lemmas for `(u)frac_auth` more consistent with `auth`.
  - Remove unidirectional lemmas with `1` fraction `frac_auth_frag_validN_op_1_l`
    and `frac_auth_frag_valid_op_1_l`
  - Add `frac_auth_frag_op_validN` and `frac_auth_frag_op_valid`, which are
    bi-implications with arbitrary fractions.
  - Add `ufrac_auth_frag_op_validN` and `ufrac_auth_frag_op_valid`.
* Remove `mono_list_lb_is_op` instance for `IsOp' (◯ML l) (◯ML l) (◯ML l)`; we
  don't usually have such instances for duplicable resources and it was added by
  accident.
* Rename `pos_op_plus` into `pos_op_add`.

**Changes in `bi`:**

* Generalize `big_op` lemmas that were previously assuming `Absorbing`ness of
  some assertion: they now take any of (`TCOr`) an `Affine` instance or an
  `Absorbing` instance. This breaks uses where an `Absorbing` instance was
  provided without relying on TC search (e.g. in `by apply ...`; a possible fix
  is `by apply: ...`). (by Glen Mével, Bedrock Systems)
* Change statement of `affinely_True_emp` to also remove the affinely modality.
* Rename `absorbingly_True_emp` to `absorbingly_emp_True` and make statement
  consistent with `affinely_True_emp`: `<absorb> emp ⊣⊢ True`.
* Change the notation for atomic updates and atomic accessors (`AU`, `AACC`) to
  swap the quantifiers: the first quantifier is logically an existential, the
  second a universal, so let's use the appropriate notation. Also use double
  quantifiers (`∀∀`, `∃∃`) to make it clear that these are not normal
  quantifiers (the latter change was also applied to logically atomic triples).
* Add some lemmas to show properties of functions defined via monotonoe fixpoints:
  `least_fixpoint_affine`, `least_fixpoint_absorbing`,
  `least_fixpoint_persistent_affine`, `least_fixpoint_persistent_absorbing`,
  `greatest_fixpoint_absorbing`.
* Rename `laterN_plus` into `laterN_add`.
* Remove `make_laterable` from atomic updates. This relies on Iris now having
  support for later credits (see below).
* Add `Fractional` and `AsFractional` instances for `embed` such that the
  embedding of something fractional is also fractional. (by Simon Friis Vindum).

**Changes in `proofmode`:**

* Change `iAssumption` to no longer instantiate evar premises with `False`. This
  used to occur when the conclusion contains variables that are not in scope of
  the evar, thus blocking the default behavior of instantiating the premise with
  the conclusion. The old behavior can be emulated with`iExFalso. iExact "H".`
* In `iInduction`, support induction schemes that involve `Forall` and
  `Forall2` (for example, for trees with finite branching).
* Change `iRevert` of a pure hypothesis to generate a magic wand instead of an
  implication.
* Change `of_envs` such that when the persistent context is empty, the
  persistence modality no longer appears at all. This is a step towards using
  the proofmode in logics without a persistence modality.
  The lemma `of_envs_alt` shows equivalence with the old version.
* Adjust `IntoWand` instances for non-affine BIs: in many cases where
  `iSpecialize`/`iApply` of an implication previously failed, it will now
  instead add an `<affine>` modality to the newly generated goal. In some rare
  cases it might stop working or add an `<affine>` modality where previously
  none was added.

**Changes in `base_logic`:**

* Make the `inG` instances for `libG` fields local, so they are only used inside
  the library that defines the `libG`.
* Add infrastructure for supporting later credits, by adding a resource `£ n`
  describing ownership of `n` credits that can be eliminated at fancy updates.
  + To retain backwards compatibility with the interaction laws of fancy updates
    with the plainly modality (`BiFUpdPlainly`), which are incompatible with
    later credits, the logic has a new parameter of type `has_lc`, which is
    either `HasLc` or `HasNoLc`. The parameter is an index of the `invGS_gen`
    typeclass; the old `invGS` is an alias for `invGS_gen HasLc` so that
    developments default to having later credits available. Libraries that want
    to be generic over whether credits are available or not, and proofs that
    need `BiFUpdPlainly`, need to be changed to use `invGS_gen` rather than
    `invGS`.
  + The core soundness lemma `step_fupdN_soundness_gen` similarly takes a `has_lc`
    parameter to control how the logic is supposed to be instantiated. The lemma
    always generates credits, but they cannot be used in any meaningful way unless
    `HasLc` is picked.
* Add discardable fractions `dfrac` to `saved_anything_own`, `saved_prop_own`,
  and `saved_pred_own`, so they can be updated. The previous persistent versions
  can be recovered with the fraction `DfracDiscarded`. Allocation lemmas now take
  a `dq` parameter to define the initial fraction.
* Remove an unused fraction argument to `dfrac_valid_discarded`.

**Changes in `program_logic`:**

* The definition of the weakest precondition has been changed to generate later credits
  (see `base_logic`) for each step:
  + The member `num_laters_per_step` of the `irisGS` class now also determines the number
    of later credits that are generated: `S (num_laters_per_step ns)` if `ns` steps
    have been taken.
  + The weakest precondition offers credits after a `prim_step` has been proven.
  + All lifting lemmas have been altered to provide credits.
    `wp_lift_step_fupdN` provides `S (num_laters_per_step ns)` credits, while all other
    lemmas always provide one credit.
* In line with the support for later credits (see `base_logic`), `irisGS_gen`
  now also has a `has_lc` parameter and the adequacy statements have been
  changed to account for that:
  + The lemma `twp_total` (total adequacy) provides `irisGS_gen HasNoLc`. Clients
    of the adequacy proof will need to make sure to be either generic over the
    choice of `has_lc` or explicitly opt-out of later credits.
  + The adequacy lemmas for the partial WP, in particular `wp_adequacy`,
    `wp_strong_adequacy` and `wp_invariance`, are now available in two flavors:
    the old names generate `irisGS` (a short-hand for `irisGS_gen HasLc`); new
    lemmas with a `_gen` suffix leave the choice of `has_lc` to the user.
  + The parameter for the stuckness bit `s` in `wp_strong_adequacy{_lc, _no_lc}` has
    moved up and is now universally quantified in the lemma instead of being existentially
    quantified at the Iris-level. For clients that already previously quantified over `s`
    at the Coq level, the only required change should be to remove the instantiation
    of the existential quantifier.

**Changes in `iris_heap_lang`:**

* Change the `num_laters_per_step` of `heap_lang` to `λ n, n`, signifying that
  each step of the weakest precondition strips `n` laters, where `n` is the
  number of steps taken so far. This number is tied to ghost state in the state
  interpretation, which is exposed, updated, and used with new lemmas
  `wp_lb_init`, `wp_lb_update`, and `wp_step_fupdN_lb`. (by Jonas Kastberg Hinrichsen)
* Make pattern argument of `wp_pure` tactic optional (defaults to wildcard
  pattern, matching all redexes).
* In line with the support for later credits (see `base_logic`), the tactic
  `wp_pure` now takes an optional parameter `credit:"H"` which generates a
  hypothesis `H` for a single later credit `£ 1` that can be eliminated using
  `lc_fupd_elim_later`.
  The typeclass `heapGS_gen` now takes an additional `has_lc` parameter, and
  `heapGS` is a short-hand for `heapGS_gen HasLc`. The adequacy statements for
  HeapLang have been changed accordingly:
  + `heap_adequacy` provides `heapGS`, thus enabling the use of later credits.
    This precludes usage of the laws in `BiFUpdPlainly` in the HeapLang instance of Iris.
  + `heap_total` provides `heapGS_gen HasNoLc`.

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# excl_auth
s/\bexcl_auth_frag_validN_op_1_l\b/excl_auth_frag_op_validN/g
s/\bexcl_auth_frag_valid_op_1_l\b/excl_auth_frag_op_valid/g
# staging → unstable
s/\biris\.staging\b/iris.unstable/g
# plus → add
s/\blaterN_plus\b/laterN_add/g
s/\bpos_op_plus\b/pos_op_add/g
EOF
```

## Iris 3.6.0 (2022-01-22)

The highlights and most notable changes of this release are:

* Coq 8.15 is now supported, while Coq 8.13 and Coq 8.14 remain supported.
  Coq 8.12 is no longer supported.
* Support for discardable fractions (`dfrac`) has been added to `gmap_view`
  authoritative elements, and to the `mono_nat` library. See below for other
  `dfrac`-related changes.
* A new `mono_list` algebra provides monotonically growing lists with an
  exclusive authoritative element and persistent prefix witnesses. See
  `iris/algebra/lib/mono_list.v` for details. An experimental logic-level
  library wrapping the algebra is available at
  `iris_staging/base_logic/mono_list.v`; if you use it, please give feedback on
  the tracking issue
  [iris/iris#439](https://gitlab.mpi-sws.org/iris/iris/-/issues/439).

This release was managed by Ralf Jung, Robbert Krebbers, and Tej Chajed, with
contributions from Dan Frumin, Jonas Kastberg Hinrichsen, Lennard Gäher,
Matthieu Sozeau, Michael Sammler, Paolo G. Giarrusso, Ralf Jung, Robbert
Krebbers, Simon Friis Vindum, Tej Chajed, and Vincent Siles. Thanks a lot to
everyone involved!

**Changes in `algebra`**

* Define non-expansive instance for `dom`. This, in particular, makes it
  possible to `iRewrite` below `dom` (even if the `dom` appears in `⌜ _ ⌝`).
* Generalize the authorative elements of `gmap_view` to be parameterized by a
  [discardable fraction](iris/algebra/dfrac.v) (`dfrac`) instead of a fraction
  (`frac`). Lemmas affected by this have been renamed such that the "frac" in
  their name has been changed into "dfrac". (by Simon Friis Vindum)
* Change `ufrac_auth` notation to not use curly braces, since these fractions do
  not behave like regular fractions (and cannot be made `dfrac`).
  Old: `●U{q} a`, `◯U{q} b`; new: `●U_q a`, `◯U_q b`.
* Equip `frac_agree` with support for `dfrac` and rename it to `dfrac_agree`.
  The old `to_frac_agree` and its lemmas still exist, except that the
  `frac_agree_op_valid` lemmas are made bi-directional.
* Rename typeclass instance `Later_inj` -> `Next_inj`.
* Remove `view_auth_frac_op`, `auth_auth_frac_op`, `gmap_view_auth_frac_op`; the
  corresponding `dfrac` lemmas can be used instead (together with `dfrac_op_own`
  if needed).
* Equip `mono_nat` algebra with support for `dfrac`, make API more consistent,
  and add notation for algebra elements. See `iris/algebra/lib/mono_nat.v` for
  details. This affects some existing terms and lemmas:
  - `mono_nat_auth` now takes a `dfrac`, but the recommendation is to port to the notation.
  - `mono_nat_lb_op`: direction of equality is swapped.
  - `mono_nat_auth_frac_op`, `mono_nat_auth_frac_op_valid`,
    `mono_nat_auth_frac_valid`, `mono_nat_both_frac_valid`: use `dfrac` variant
    instead.
* Add `mono_list` algebra for monotonically growing lists with an exclusive
  authoritative element and persistent prefix witnesses. See
  `iris/algebra/lib/mono_list.v` for details.

**Changes in `bi`:**

* Rename `least_fixpoint_ind` into `least_fixpoint_iter`,
  rename `greatest_fixpoint_coind` into `greatest_fixpoint_coiter`,
  rename `least_fixpoint_strong_ind` into `least_fixpoint_ind`,
  add lemmas `least_fixpoint_{ind_wf, ne', strong_mono}`, and
  add lemmas `greatest_fixpoint_{coind, paco, ne', strong_mono}`.
* Move `persistently_forall_2` (`∀ <pers> ⊢ <pers> ∀`) out of the BI interface
  into a new typeclass, `BiPersistentlyForall`. The BI interface instead just
  demands the equivalent property for conjunction (`(<pers> P) ∧ (<pers> Q) ⊢
  <pers> (P ∧ Q)`). This enables the IPM to support logics where the
  persistently modality is defined with an existential quantifier. This also
  necessitates removing `persistently_impl_plainly` from `BiPlainly` into a new
  typeclass `BiPersistentlyImplPlainly`.
  Proofs that are generic in `PROP` might have to add those new classes as
  assumptions to remain compatible, and code that instantiates the BI interface
  needs to provide instances for the new classes.
* Make `frame_fractional` not an instance any more; instead fractional
  propositions that want to support framing are expected to register an
  appropriate instance themselves. HeapLang and gen_heap `↦` still support
  framing, but the other fractional propositions in Iris do not.
* Strenghten the `Persistent`/`Affine`/`Timeless` results for big ops. Add a `'`
  to the name of the weaker results, which remain to be used as instances.

**Changes in `heap_lang`:**

* The `is_closed_expr` predicate is formulated in terms of a
  set of binders (as opposed to a list of binders).

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# least/greatest fixpoint renames
s/\bleast_fixpoint_ind\b/least_fixpoint_iter/g
s/\bgreatest_fixpoint_coind\b/greatest_fixpoint_coiter/g
s/\bleast_fixpoint_strong_ind\b/least_fixpoint_ind/g
# gmap_view renames from frac to dfrac
s/\bgmap_view_(auth|both)_frac_(op_invN|op_inv|op_inv_L|valid|op_validN|op_valid|op_valid_L)\b/gmap_view_\1_dfrac_\2/g
s/\bgmap_view_persist\b/gmap_view_frag_persist/g
# frac_agree with dfrac
s/\bfrac_agreeR\b/dfrac_agreeR/g
EOF
```

## Iris 3.5.0 (2021-11-05)

The highlights and most notable changes of this release are:

* Coq 8.14 is now supported, while Coq 8.12 and Coq 8.13 remain supported.
* The proof mode now has native support for pure names `%H` in intro patterns,
  without installing
  [iris/string-ident](https://gitlab.mpi-sws.org/iris/string-ident). If you had
  the plugin installed, to migrate simply uninstall the plugin and stop
  importing it.
* The proof mode now supports destructing existentials with the `"[%x ...]"`
  pattern.
* `iMod` and `iModIntro` now report an error message for mask mismatches.
* Performance improvements for the proof mode in `iFrame` in non-affine
  logics, `iPoseProof`, and `iDestruct` (by Paolo G. Giarrusso, Bedrock Systems,
  and Armaël Guéneau).
* The new `ghost_map` logic-level library supports a ghost `gmap K V` with an
  authoritative view and per-element points-to facts written `k ↪[γ] w`.
* Weakest preconditions now support a flexible number of laters per
  physical step of the operational semantics. See merge request
  [!585](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/595) (by
  Jacques-Henri Jourdan and Yusuke Matsushita).
* HeapLang now has an atomic `Xchg` (exchange) operation (by Simon Hudon,
  Google).

This release was managed by Ralf Jung, Robbert Krebbers, and Tej Chajed, with
contributions from Amin Timany, Armaël Guéneau, Dan Frumin, Dmitry Khalanskiy,
Hoang-Hai Dang, Jacques-Henri Jourdan, Lennard Gäher, Michael Sammler, Paolo G.
Giarrusso, Ralf Jung, Robbert Krebbers, Simon Friis Vindum, Simon Hudon, Tej
Chajed, and Yusuke Matsushita. Thanks a lot to everyone involved!

**Changes in `algebra`:**

* Generalize the authorative elements of the `view`, `auth` and `gset_bij`
  cameras to be parameterized by a [discardable fraction](iris/algebra/dfrac.v)
  (`dfrac`) instead of a fraction (`frac`). Normal fractions are now denoted
  `●{#q} a` and `●V{#q} a`. Lemmas affected by this have been renamed such that
  the "frac" in their name has been changed into "dfrac". (by Simon Friis Vindum)
* Generalize `namespace_map` to `reservation_map` which enhances `gmap positive
  A` with a notion of 'tokens' that enable allocating a particular name in the
  map. See [algebra.reservation_map](iris/algebra/reservation_map.v) for further
  information.
* Add `dyn_reservation_map` which further extends `reservation_map` with the
  ability to dynamically allocate an infinite set of tokens. This is useful to
  perform synchronized allocation of the same name in two maps/APIs without
  dedicated support from one of the involved maps/APIs. See
  [algebra.dyn_reservation_map](iris/algebra/dyn_reservation_map.v) for further
  information.
* Demote the Camera structure on `list` to `iris_staging` since its composition
  is not very well-behaved.
* Extend `gmap_view` with lemmas for "big" operations on maps.
* Typeclasses instances triggering a canonical structure search such as `Equiv`,
  `Dist`, `Op`, `Valid`, `ValidN`, `Unit`, `PCore` now use an `Hint Extern`
  based on `refine` instead of `apply`, in order to use Coq's newer unification
  algorithm.
* Set `Hint Mode` for the classes `OfeDiscrete`, `Dist`, `Unit`, `CmraMorphism`,
  `rFunctorContractive`, `urFunctorContractive`.
* Set `Hint Mode` for the stdpp class `Equiv`. This might require few spurious
  type annotations until
  [Coq bug #14441](https://github.com/coq/coq/issues/14441) is fixed.
* Add `max_prefix_list` RA on lists whose composition is only defined when one
  operand is a prefix of the other. The result is the longer list.
* Add `NonExpansive` instances for `curry` and friends.

**Changes in `bi`:**

* Add new lemmas `big_sepM2_delete_l` and `big_sepM2_delete_r`.
* Rename `big_sepM2_lookup_1` → `big_sepM2_lookup_l` and
  `big_sepM2_lookup_2` → `big_sepM2_lookup_r`.
* Add lemmas for swapping nested big-ops: `big_sep{L,M,S,MS}_sep{L,M,S,MS}`.
* Rename `big_sep{L,L2,M,M2,S}_intuitionistically_forall` →
  `big_sep{L,L2,M,M2,S}_intro`, and `big_orL_lookup` → `big_orL_intro`.
* Rename `bupd_forall` to `bupd_plain_forall`, and add
  `{bupd,fupd}_{and,or,forall,exist}`.
* Decouple `Wp` and `Twp` typeclasses from the `program_logic.language`
  interface. The typeclasses are now parameterized over an expression and a
  value type, instead of a language. This requires extra type annotations or
  explicit coercions in a few cases, in particular `WP v {{ Φ }}` must now be
  written `WP (of_val v) {{ Φ }}`.
* Improve `make_laterable`:
  - Adjust definition such that `Laterable P` iff `P ⊢ make_laterable P`.
    As a consequence, `make_laterable_elim` got weaker: elimination now requires
    an except-0 modality (`make_laterable P -∗ ◇ P`).
  - Add `iModIntro` support for `make_laterable`.
* Improvements to `BiMonoPred`:
  - Use `□`/`-∗` instead of `<pers>`/`→`.
  - Strengthen to ensure that functions for recursive calls are non-expansive.
* Add `big_andM` (big conjunction on finite maps) with lemmas similar to `big_andL`.
* Add transitive embedding that constructs an embedding of `PROP1` into `PROP3`
  by combining the embeddings of `PROP1` into `PROP2` and `PROP2` into `PROP3`.
  This construct is *not* declared as an instance to avoid TC search divergence.
  (by Hai Dang, BedRock Systems)
* Improve notation printing around magic wands, view shifts, `WP`, Texan
  triples, and logically atomic triples.
* Slight change to the `AACC` notation for atomic accessors (which is usually
  only printed, not parsed): added a `,` before `ABORT`, for consistency with `COMM`.
* Add the lemmas `big_sepM_impl_strong` and `big_sepM_impl_dom_subseteq` that
  generalize the existing `big_sepM_impl` lemma. (by Simon Friis Vindum)
* Add new instance `fractional_big_sepL2`. (by Paolo G. Giarrusso, BedRock Systems)

**Changes in `proofmode`:**

* Add support for pure names `%H` in intro patterns. This is now natively
  supported whereas the previous experimental support required installing
  https://gitlab.mpi-sws.org/iris/string-ident. (by Tej Chajed)
* Add support for destructing existentials with the intro pattern `[%x ...]`.
  (by Tej Chajed)
* `iMod`/`iModIntro` show proper error messages when they fail due to mask
  mismatches. To support this, the proofmode typeclass `FromModal` now takes an
  additional pure precondition.
* Fix performance of `iFrame` in logics without `BiAffine`.
  To adjust your code if you use such logics and define `Frame` instances,
  ensure these instances to have priority at least 2: they should have either at
  least 2 (non-dependent) premises, or an explicit priority.
  References: docs for `frame_here_absorbing` in
  [iris/proofmode/frame_instances.v](iris/proofmode/frame_instances.v) and
  https://coq.inria.fr/refman/addendum/type-classes.html#coq:cmd.Instance. (by
  Paolo G. Giarrusso, BedRock Systems)
* Rename the main entry point module for the proofmode from
  `iris.proofmode.tactics` to `iris.proofmode.proofmode`. Under normal
  circumstances, this should be the only proofmode file you need to import.
* Improve performance of the `iIntoEmpValid` tactic used by `iPoseProof`,
  especially in the case of large goals and lemmas with many forall quantifiers.
  (by Armaël Guéneau)
* Improve performance of the `iDestruct` tactic, by using user-provided names
  more eagerly in order to avoid later calls to `iRename`.
  (by Armaël Guéneau)

**Changes in `bi`:**

* Add lemmas characterizing big-ops over pure predicates (`big_sep*_pure*`).
* Move `BiAffine`, `BiPositive`, `BiLöb`, and `BiPureForall` from
  `bi.derived_connectives` to `bi.extensions`.
* Strengthen `persistent_fractional` to support propositions that are persistent
  and either affine or absorbing. (by Paolo G. Giarrusso, BedRock Systems)

**Changes in `base_logic`:**

* Add `ghost_map`, a logic-level library for a `gmap K V` with an authoritative
  view and per-element points-to facts written `k ↪[γ] w`.
* Generalize the soundness lemma of the base logic `step_fupdN_soundness`.
  It applies even if invariants stay open accross an arbitrary number of laters.
  (by Jacques-Henri Jourdan)
* Rename those `*G` typeclasses that must be global singletons to `*GS`, and
  their corresponding `preG` class to `GpreS`. Affects `invG`, `irisG`,
  `gen_heapG`, `inv_heapG`, `proph_mapG`, `ownPG`, `heapG`.

**Changes in `program_logic`:**

* Change definition of weakest precondition to use a variable number of laters
  (i.e., logical steps) for each physical step of the operational semantics,
  depending on the number of physical steps executed since the begining of the
  execution of the program. See merge request [!595](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/595).
  This implies several API-breaking changes, which can be easily fixed in client
  formalizations in a backward compatible manner as follows:
   - Ignore the new parameter `ns` in the state interpretation, which
     corresponds to a step counter.
   - Use the constant function "0" for the new field `num_laters_per_step` of
     `irisG`.
   - Use `fupd_intro _ _` for the new field `state_interp_mono` of `irisG`.
   - Some proofs using lifting lemmas and adequacy theorems need to be adapted
     to ignore the new step counter.
  (by Jacques-Henri Jourdan)
* Remove `wp_frame_wand_l`; add `wp_frame_wand` as more symmetric replacement.
* Swap the polarity of the mask in logically atomic triples, so that it matches
  regular `WP` masks.
* Rename `iris_invG` to `iris_invGS`.

**Changes in `heap_lang`:**

* Rename `Build_loc` constructor for `loc` type to `Loc`.
* Add atomic `Xchg` ("exchange"/"swap") operation. (by Simon Hudon, Google LLC)

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# auth and view renames from frac to dfrac
s/\b(auth|view)_(auth|both|update)_frac_(is_op|op_invN|op_inv|inv_L|validN|op_validN|valid|op_valid|valid_2|valid_discrete|includedN|included|alloc|validI|validI_2|validI_1|validI|)\b/\1_\2_dfrac_\3/g
s/\bgset_bij_auth_frac_(\w*)\b/gset_bij_auth_dfrac_\1/g
s/\bgset_bij_auth_empty_frac_valid\b/gset_bij_auth_empty_dfrac_valid/g
s/\bbij_both_frac_valid\b/bij_both_dfrac_valid/g
# big_sepM renames
s/\bbig_sepM2_lookup_1\b/big_sepM2_lookup_l/g
s/\bbig_sepM2_lookup_2\b/big_sepM2_lookup_r/g
# big_*_intro
s/\bbig_sep(L|L2|M|M2|S)_intuitionistically_forall\b/big_sep\1_intro/g
s/\bbig_orL_lookup\b/big_orL_intro/g
s/\bbupd_forall\b/bupd_plain_forall/g
# "global singleton" rename
s/\b(inv|iris|(gen|inv)_heap|(Gen|Inv)Heap|proph_map|ProphMap|[oO]wnP|[hH]eap)G\b/\1GS/g
s/\b([iI]nv|iris|(gen|inv)_heap|(Gen|Inv)Heap|proph_map|ProphMap|[oO]wnP|[hH]eap)PreG\b/\1GpreS/g
# iris.proofmode.tactics → iris.proofmode.proofmode
s/\bproofmode\.tactics\b/proofmode.proofmode/
s/(From +iris\.proofmode +Require +(Import|Export).*)\btactics\b/\1proofmode/
# iris_invG → iris_invGS
s/\biris_invG\b/iris_invGS/g
EOF
```

## Iris 3.4.0 (released 2021-02-16)

The highlights and most notable changes of this release are as follows:
* Coq 8.13 is now supported; the old Coq 8.9 and Coq 8.10 are not supported any
  more.
* The new `view` RA construction generalizes `auth` to user-defined abstraction
  relations. (thanks to Gregory Malecha for the inspiration)
* The new `dfrac` RA extends `frac` (fractions `0 < q ≤ 1`) with support for
  "discarding" some part of the fraction in exchange for a persistent witness
  that discarding has happened. This can be used to easily generalize fractional
  permissions with support for persistently owning "any part" of the resource.
  (by Simon Friis Vindum)
* The new `gmap_view` RA provides convenient lemmas for ghost ownership
  of heap-like structures with an "authoritative" view. Thanks to `dfrac`, it
  supports both exclusive (mutable) and persistent (immutable) ownership of
  individual map elements.
* With this release we are beginning to provide logic-level abstractions for
  ghost state, which have the advantage that the user does not have to directly
  interact with RAs to use them.
  - `ghost_var` provides a logic-level abstraction of ghost variables: a mutable
    "variable" with fractional ownership.
  - `mono_nat` provides a "monotone counter" with a persistent witnesses
    representing a lower bound of the current counter value. (by Tej Chajed)
  - `gset_bij` provides a monotonically growing partial bijection; this is
    useful in particular when building binary logical relations for languages
    with a heap.
* HeapLang provides a persistent read-only points-to assertion `l ↦□ v`.
  (by Simon Friis Vindum)
* We split Iris into multiple opam packages: `coq-iris` no longer contains
  HeapLang, which is now in a separate package `coq-iris-heap-lang`. The two
  packages `coq-iris-deprecated` (for old modules that we eventually plan to
  remove entirely) and `coq-iris-staging` (for new modules that are not yet
  ready for prime time) exist only as development versions, so they are not part
  of this release.
* The proofmode now does a better job at picking reasonable names when moving
  variables into the Coq context without a name being explicitly given by the
  user. However, the exact variable names remain unspecified. (by Tej Chajed)

Further details are given in the changelog below.

This release of Iris was managed by Ralf Jung and Robbert Krebbers, with
contributions by Arthur Azevedo de Amorim, Dan Frumin, Enrico Tassi, Hai Dang,
Michael Sammler, Paolo G. Giarrusso, Rodolphe Lepigre, Simon Friis Vindum, Tej
Chajed, and Yusuke Matsushita.  Thanks a lot to everyone involved!

**Changes in `algebra`:**

* Add constructions to define a camera through restriction of the validity predicate
  (`iso_cmra_mixin_restrict`) and through an isomorphism (`iso_cmra_mixin`).
* Add a `frac_agree` library which encapsulates `frac * agree A` for some OFE
  `A`, and provides some useful lemmas.
* Add the view camera `view`, which generalizes the authoritative camera
  `auth` by being parameterized by a relation that relates the authoritative
  element with the fragments.
* Add the camera of discardable fractions `dfrac`. This is a generalization of
  the normal fractional camera.
  See [algebra.dfrac](iris/algebra/dfrac.v) for further information.
* Add `gmap_view`, a camera providing a "view of a `gmap`". The authoritative
  element is any `gmap`; the fragment provides fractional ownership of a single
  key, including support for persistent read-only ownership through `dfrac`.
  See [algebra.lib.gmap_view](iris/algebra/lib/gmap_view.v) for further information.
* Add `mono_nat`, a wrapper for `auth max_nat`. The result is an authoritative
  `nat` where a fragment is a lower bound whose ownership is persistent.
  See [algebra.lib.mono_nat](iris/algebra/lib/mono_nat.v) for further information.
* Add the `gset_bij` resource algebra for monotone partial bijections.
  See [algebra.lib.gset_bij](iris/algebra/lib/gset_bij.v) for further information.
* Rename `agree_op_inv'` → `to_agree_op_inv`,
  `agree_op_invL'` → `to_agree_op_inv_L`, and add `to_agree_op_invN`.
* Rename `auth_auth_frac_op_invL` → `auth_auth_frac_op_inv_L`,
  `excl_auth_agreeL` → `excl_auth_agree_L`,
  `frac_auth_agreeL` → `frac_auth_agree_L`, and
  `ufrac_auth_agreeL` → `ufrac_auth_agree_L`.
* Fix direction of `auth_auth_validN` to make it consistent with similar lemmas,
  e.g., `auth_auth_valid`. The direction is now `✓{n} (● a) ↔ ✓{n} a`.
* Rename `auth_both_valid` to `auth_both_valid_discrete` and
  `auth_both_frac_valid` to `auth_both_frac_valid_discrete`. The old name is
  used for new, stronger lemmas that do not assume discreteness.
* Redefine the authoritative camera in terms of the view camera. As part of this
  change, we have removed lemmas that leaked implementation details. Hence, the
  only way to construct elements of `auth` is via the elements `●{q} a` and
  `◯ b`. The constructor `Auth`, and the projections `auth_auth_proj` and
  `auth_frag_proj` no longer exist. Lemmas that referred to these constructors
  have been removed, in particular: `auth_equivI`, `auth_validI`,
  `auth_included`, `auth_valid_discrete`, and `auth_both_op`.  For validity, use
  `auth_auth_valid*`, `auth_frag_valid*`, or `auth_both_valid*` instead.
* Rename `auth_update_core_id` into `auth_update_frac_alloc`.
* Rename `cmra_monotone_valid` into `cmra_morphism_valid` (this rename was
  forgotten in !56).
* Move the `*_validI` and `*_equivI` lemmas to a new module, `base_logic.algebra`.
  That module is exported by `base_logic.base_logic` so it should usually be
  available everywhere without further changes.
* The authoritative fragment `✓ (◯ b : auth A)` is no longer definitionally
  equal to `✓ b`.
* Change `*_valid` lemma statements involving fractions to use `Qp` addition and
  inequality instead of RA composition and validity (also in `base_logic` and
  the higher layers).
* Move `algebra.base` module to `prelude.prelude`.
* Strengthen `cmra_op_discrete` to assume only `✓{0} (x1 ⋅ x2)` instead of `✓
  (x1 ⋅ x2)`.
* Rename the types `ofeT`→`ofe`, `cmraT`→`cmra`, `ucmraT`→`ucmra`, and the
  constructors `OfeT`→`Ofe`, `CmraT`→`Cmra`, and `UcmraT`→`Ucmra` since the `T`
  suffix is not needed. This change makes these names consistent with `bi`,
  which also does not have a `T` suffix.
* Rename typeclass instances of CMRA operational typeclasses (`Op`, `Core`,
  `PCore`, `Valid`, `ValidN`, `Unit`) to have a `_instance` suffix, so that
  their original names are available to use as lemma names.
* Rename `frac_valid'`→`frac_valid`, `frac_op'`→`frac_op`,
  `ufrac_op'`→`ufrac_op`, `coPset_op_union` → `coPset_op`, `coPset_core_self` →
  `coPset_core`, `gset_op_union` → `gset_op`, `gset_core_self` → `gset_core`,
  `gmultiset_op_disj_union` → `gmultiset_op`, `gmultiset_core_empty` →
  `gmultiset_core`, `nat_op_plus` → `nat_op`, `max_nat_op_max` →
  `max_nat_op`. Those names were previously blocked by typeclass instances.

**Changes in `bi`:**

* Add big op lemmas `big_op{L,L2,M,M2,S}_intuitionistically_forall` and
  `big_sepL2_forall`, `big_sepMS_forall`, `big_sepMS_impl`, and `big_sepMS_dup`.
* Add lemmas to big-ops that provide ownership of a single element and permit
  changing the quantified-over predicate when re-assembling the big-op:
  `big_sepL_lookup_acc_impl`, `big_sepL2_lookup_acc_impl`,
  `big_sepM_lookup_acc_impl`, `big_sepM2_lookup_acc_impl`,
  `big_sepS_elem_of_acc_impl`, `big_sepMS_elem_of_acc_impl`.
* Add lemmas `big_sepM_filter'` and `big_sepM_filter` matching the corresponding
  `big_sepS` lemmas.
* Add lemmas for big-ops of magic wands: `big_sepL_wand`, `big_sepL2_wand`,
  `big_sepM_wand`, `big_sepM2_wand`, `big_sepS_wand`, `big_sepMS_wand`.
* Add notation `¬ P` for `P → False` to `bi_scope`.
* Add `fupd_mask_intro` which can be conveniently `iApply`ed to goals of the
  form `|={E1,E2}=>` to get rid of the `fupd` in the goal if `E2 ⊆ E1`. The
  lemma `fupd_mask_weaken Enew` can be `iApply`ed to shrink the first mask to
  `Enew` without getting rid of the modality; the same effect can also be
  obtained slightly more conveniently by using `iMod` with `fupd_mask_subseteq
  Enew`. To make the new names work, rename some existing lemmas:
  `fupd_intro_mask` → `fupd_mask_intro_subseteq`,
  `fupd_intro_mask'` → `fupd_mask_subseteq` (implicit arguments also changed
  here), `fupd_mask_weaken` → `fupd_mask_intro_discard`. Remove `fupd_mask_same`
  since it was unused and obscure.  In the `BiFUpd` axiomatization, rename
  `bi_fupd_mixin_fupd_intro_mask` to `bi_fupd_mixin_fupd_mask_subseteq` and
  weaken the lemma to be specifically about `emp` (the stronger version can be
  derived).
* Remove `bi.tactics` with tactics that predate the proofmode (and that have not
  been working properly for quite some time).
* Strengthen `persistent_sep_dup` to support propositions that are persistent
  and either affine or absorbing.
* Fix the statement of the lemma `fupd_plainly_laterN`; the old lemma was a
  duplicate of `fupd_plain_laterN`.
* Strengthen `big_sepL2_app_inv` by weakening a premise (it is sufficient for
  one of the two pairs of lists to have equal length).
* Rename `equiv_entails` → `equiv_entails_1_1`,
  `equiv_entails_sym` → `equiv_entails_1_2`, and `equiv_spec` → `equiv_entails`.
* Remove the laws `pure_forall_2 : (∀ a, ⌜ φ a ⌝) ⊢ ⌜ ∀ a, φ a ⌝` from the BI
  interface and factor it into a type class `BiPureForall`.

**Changes in `proofmode`:**

* The proofmode now preserves user-supplied names for existentials when using
  `iDestruct ... as (?) "..."`. This is backwards-incompatible if you were
  relying on the previous automatic names (which were always "H", possibly
  freshened). It also requires some changes if you were implementing `IntoExist`
  yourself, since the typeclass now forwards names. If your instance transforms
  one `IntoExist` into another, you can generally just forward the name from the
  premise.
* The proofmode also preserves user-supplied names in `iIntros`, for example
  with `iIntros (?)` and `iIntros "%"`, as described for destructing
  existentials above. As part of this change, it now uses a base name of `H` for
  pure facts rather than the previous default of `a`. This also requires some
  changes if you were implementing `FromForall`, in order to forward names.
* Make `iFrame` "less" smart w.r.t. clean up of modalities. It now consistently
  removes the modalities `<affine>`, `<absorbing>`, `<persistent>` and `□` only
  if the result after framing is `True` or `emp`. In particular, it no longer
  removes `<affine>` if the result after framing is affine, and it no longer
  removes `□` if the result after framing is intuitionistic.
* Allow framing below an `<affine>` modality if the hypothesis that is framed is
  affine. (Previously, framing below `<affine>` was only possible if the
  hypothesis that is framed resides in the intuitionistic context.)
* Add Coq side-condition `φ` to class `ElimAcc` (similar to what we already had
  for `ElimInv` and `ElimModal`).
* Add a tactic `iSelect pat tac` (similar to `select` in std++) which runs the
  tactic `tac H` with the name `H` of the last hypothesis of the intuitionistic
  or spatial context matching `pat`. The tactic `iSelect` is used to implement:
  + `iRename select (pat)%I into name` which renames the matching hypothesis,
  + `iDestruct select (pat)%I as ...` which destructs the matching hypothesis,
  + `iClear select (pat)%I` which clears the matching hypothesis,
  + `iRevert select (pat)%I` which reverts the matching hypothesis,
  + `iFrame select (pat)%I` which cancels the matching hypothesis.

**Changes in `base_logic`:**

* Add a `ghost_var` library that provides (fractional) ownership of a ghost
  variable of arbitrary `Type`.
* Define a ghost state library on top of the `mono_nat` resource algebra.
  See [base_logic.lib.mono_nat](iris/base_logic/lib/mono_nat.v) for further
  information.
* Define a ghost state library on top of the `gset_bij` resource algebra.
  See [base_logic.lib.gset_bij](iris/base_logic/lib/gset_bij.v) for further
  information.
* Extend the `gen_heap` library with read-only points-to assertions using
  [discardable fractions](iris/algebra/dfrac.v).
  + The `mapsto` connective now takes a `dfrac` rather than a `frac` (i.e.,
    positive rational number `Qp`).
  + The notation `l ↦{ dq } v` is generalized to discardable fractions
    `dq : dfrac`.
  + The new notation `l ↦{# q} v` is used for a concrete fraction `q : frac`
    (e.g., to enable writing `l ↦{# 1/2} v`).
  + The new notation `l ↦□ v` is used for the discarded fraction. This
    persistent proposition provides read-only access to `l`.
  + The lemma `mapsto_persist : l ↦{dq} v ==∗ l ↦□ v` is used for making the
    location `l` read-only.
  + See the [changes to HeapLang](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/554)
    for an indication on how to adapt your language.
  + See the [changes to iris-examples](https://gitlab.mpi-sws.org/iris/examples/-/commit/a8425b708ec51d918d5cf6eb3ab6fde88f4e2c2a)
    for an indication on how to adapt your development. In particular, instead
    of `∃ q, l ↦{q} v` you likely want to use `l ↦□ v`, which has the advantage
    of being persistent (rather than just duplicable).
* Change type of some ghost state lemmas (mostly about allocation) to use `∗`
  instead of `∧` (consistent with our usual style).  This affects the following
  lemmas: `own_alloc_strong_dep`, `own_alloc_cofinite_dep`, `own_alloc_strong`,
  `own_alloc_cofinite`, `own_updateP`, `saved_anything_alloc_strong`,
  `saved_anything_alloc_cofinite`, `saved_prop_alloc_strong`,
  `saved_prop_alloc_cofinite`, `saved_pred_alloc_strong`,
  `saved_pred_alloc_cofinite`, `auth_alloc_strong`, `auth_alloc_cofinite`,
  `auth_alloc`.
* Change `uPred_mono` to only require inclusion at the smaller step-index.
* Put `iProp`/`iPreProp`-isomorphism into the `own` construction. This affects
  clients that define higher-order ghost state constructions. Concretely, when
  defining an `inG`, the functor no longer needs to be applied to `iPreProp`,
  but should be applied to `iProp`. This avoids clients from having to push
  through the `iProp`/`iPreProp`-isomorphism themselves, which is now handled
  once and for all by the `own` construction.
* Rename `gen_heap_ctx` to `gen_heap_interp`, since it is meant to be used in
  the state interpretation of WP and since `_ctx` is elsewhere used as a suffix
  indicating "this is a persistent assumption that clients should always have in
  their context". Likewise, rename `proph_map_ctx` to `proph_map_interp`.
* Move `uPred.prod_validI`, `uPred.option_validI`, and
  `uPred.discrete_fun_validI` to the new `base_logic.algebra` module. That
  module is exported by `base_logic.base_logic` so these names are now usually
  available everywhere, and no longer inside the `uPred` module.
* Remove the `gen_heap` notations `l ↦ -` and `l ↦{q} -`. They were barely used
  and looked very confusing in context: `l ↦ - ∗ P` looks like a magic wand.
* Change `gen_inv_heap` notation `l ↦□ I` to `l ↦_I □`, so that `↦□` can be used
  by `gen_heap`.
* Strengthen `mapsto_valid_2` conclusion from `✓ (q1 + q2)%Qp` to
  `⌜✓ (q1 + q2)%Qp ∧ v1 = v2⌝`.
* Change `gen_heap_init` to also return ownership of the points-to facts for the
  initial heap.
* Rename `mapsto_mapsto_ne` to `mapsto_frac_ne`, and add a simpler
  `mapsto_ne` that does not require reasoning about fractions.
* Deprecate the `auth` and `sts` modules. These were logic-level wrappers around
  the underlying RAs; as far as we know, they are unused since they were not
  flexible enough for practical use.
* Deprecate the `viewshift` module, which defined a binary view-shift connective
  with an implicit persistence modality. It was unused and too easily confused
  with `={_}=∗`, the binary view-shift (fancy update) *without* a persistence
  modality.

**Changes in `program_logic`:**

* `wp_strong_adequacy` now applies to an initial state with multiple
  threads instead of only a single thread. The derived adequacy lemmas
  are unchanged.
* `pure_exec_fill` is no longer registered as an instance for `PureExec`, to
  avoid TC search attempting to apply this instance all the time.
* Merge `wp_value_inv`/`wp_value_inv'` into `wp_value_fupd`/`wp_value_fupd'` by
  making the lemmas bidirectional.
* Generalize HeapLang's `mapsto` (`↦`), `array` (`↦∗`), and atomic heap
  connectives to discardable fractions. See the CHANGELOG entry in the category
  `base_logic` for more information.
* Opening an invariant or eliminating a mask-changing update modality around a
  non-atomic weakest precondition creates a side-condition `Atomic ...`.
  Before, this would fail with the unspecific error "iMod: cannot eliminate
  modality (|={E1,E2}=> ...) in (WP ...)".
* In `Ectx_step` and `step_atomic`, mark the parameters that are determined by
  the goal as implicit.
* Deprecate the `hoare` module to prevent accidental usage; the recommended way
  to write Hoare-style specifications is to use Texan triples.

**Changes in `heap_lang`:**

* `wp_pures` now turns goals of the form `WP v {{ Φ }}` into `Φ v`.
* Fix `wp_bind` in case of a NOP (i.e., when the given expression pattern is
  already at the top level).
* The `wp_` tactics now preserve the possibility of doing a fancy update when
  the expression reduces to a value.
* Move `IntoVal`, `AsVal`, `Atomic`, `AsRecV`, and `PureExec` instances to their
  own file [heap_lang.class_instances](iris_heap_lang/class_instances.v).
* Move `inv_head_step` tactic and `head_step` auto hints (now part of new hint
  database `head_step`) to [heap_lang.tactics](iris_heap_lang/tactics.v).
* The tactic `wp_apply` no longer performs `wp_pures` before applying the given
  lemma. The new tactic `wp_smart_apply` repeatedly performs single `wp_pure`
  steps until the lemma matches the goal.

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E -f- $(find theories -name "*.v") <<EOF
# agree and L suffix renames
s/\bagree_op_inv'/to_agree_op_inv/g
s/\bagree_op_invL'/to_agree_op_inv_L/g
s/\bauth_auth_frac_op_invL\b/auth_auth_frac_op_inv_L/g
s/\b(excl|frac|ufrac)_auth_agreeL/\1_auth_agree_L/g
# auth_both_valid
s/\bauth_both_valid\b/auth_both_valid_discrete/g
s/\bauth_both_frac_valid\b/auth_both_frac_valid_discrete/g
# gen_heap_ctx and proph_map_ctx
s/\bgen_heap_ctx\b/gen_heap_interp/g
s/\bproph_map_ctx\b/proph_map_interp/g
# other gen_heap changes
s/\bmapsto_mapsto_ne\b/mapsto_frac_ne/g
# remove Ts in algebra
s/\bofeT\b/ofe/g
s/\bOfeT\b/Ofe/g
s/\bcmraT\b/cmra/g
s/\bCmraT\b/Cmra/g
s/\bucmraT\b/ucmra/g
s/\bUcmraT\b/Ucmra/g
# _op/valid/core lemmas
s/\b(u?frac_(op|valid))'/\1/g
s/\b((coPset|gset)_op)_union\b/\1/g
s/\b((coPset|gset)_core)_self\b/\1/g
s/\b(gmultiset_op)_disj_union\b/\1/g
s/\b(gmultiset_core)_empty\b/\1/g
s/\b(nat_op)_plus\b/\1/g
s/\b(max_nat_op)_max\b/\1/g
# equiv_spec
s/\bequiv_entails\b/equiv_entails_1_1/g
s/\bequiv_entails_sym\b/equiv_entails_1_2/g
s/\bequiv_spec\b/equiv_entails/g
EOF
```

## Iris 3.3.0 (released 2020-07-15)

This release does not have any outstanding highlights, but contains a large
number of improvements all over the board.  For instance:

* `heap_lang` now supports deallocation as well as better reasoning about
  "invariant locations" (locations that perpetually satisfy some Coq-level
  invariant).
* Invariants (`inv N P`) are more flexible, now also supporting splitting
  and merging of invariants with respect to separating conjunction.
* Performance of the proofmode for BIs constructed on top of other BIs (e.g.,
  `monPred`) was greatly improved, leading to up to 70% speedup in individual
  files. As part of this refactoring, the proofmode can now also be instantiated
  with entirely "logical" notion of BIs that do not have a (non-trivial) metric
  structure, and still support reasoning about ▷.
* The proof mode now provides experimental support for naming pure facts in
  intro patterns.  See
  [iris/string-ident](https://gitlab.mpi-sws.org/iris/string-ident) for details.
* Iris now provides official ASCII notation. We still recommend using the
  Unicode notation for better consistency and interoperability with other Iris
  libraries, but provide ASCII notation for when Unicode is not an option.
* We removed several coercions, fixing "ambiguous coercion path" warnings and
  solving some readability issues.
* Coq 8.10, 8.11, and 8.12 are newly supported by this release, and Coq 8.7 and
  8.8 are no longer supported.

Further details are given in the changelog below. We always first list the
potentially breaking changes, then (some of) the additions.

This release of Iris received contributions by Abel Nieto, Amin Timany, Dan
Frumin, Derek Dreyer, Dmitry Khalanskiy, Gregory Malecha, Jacques-Henri Jourdan,
Jonas Kastberg, Jules Jacobs, Matthieu Sozeau, Maxime Dénès, Michael Sammler,
Paolo G. Giarrusso, Ralf Jung, Robbert Krebbers, Simon Friis Vindum, Simon
Spies, and Tej Chajed.  Thanks a lot to everyone involved!

**Changes in `heap_lang`:**

* Remove global `Open Scope Z_scope` from `heap_lang.lang`, and leave it up to
  reverse dependencies if they want to `Open Scope Z_scope` or not.
* Fix all binary operators performing pointer arithmetic (instead of just the
  dedicated `OffsetOp` operator doing that).
* Rename `heap_lang.lifting` to `heap_lang.primitive_laws`. There now also
  exists `heap_lang.derived_laws`.
* Make lemma names for `fill` more consistent
  - Use the `_inv` suffix for the the backwards directions:
   `reducible_fill` → `reducible_fill_inv`,
   `reducible_no_obs_fill` → `reducible_no_obs_fill_inv`,
   `not_stuck_fill` → `not_stuck_fill_inv`.
  - Use the non-`_inv` names (that freed up) for the forwards directions:
   `reducible_fill`, `reducible_no_obs_fill`, `irreducible_fill_inv`.
* Remove namespace `N` from `is_lock`.

* Add support for deallocation of locations via the `Free` operation.
* Add a fraction to the heap_lang `array` assertion.
* Add `lib.array` module for deallocating, copying and cloning arrays.
* Add TWP (total weakest-pre) lemmas for arrays.
* Add a library for "invariant locations": heap locations that will not be
  deallocated (i.e., they are GC-managed) and satisfy some pure, Coq-level
  invariant.  See `iris.base_logic.lib.gen_inv_heap` for details.
* Add the ghost state for "invariant locations" to `heapG`.  This affects the
  statement of `heap_adequacy`, which is now responsible for initializing the
  "invariant locations" invariant.
* Add lemma `mapsto_mapsto_ne : ¬ ✓(q1 + q2)%Qp → l1 ↦{q1} v1 -∗ l2 ↦{q2} v2 -∗ ⌜l1 ≠ l2⌝`.
* Add lemma `is_lock_iff` and show that `is_lock` is contractive.

**Changes in `program_logic`:**

* In the axiomatization of ectx languages, replace the axiom of positivity of
  context composition with an axiom that says if `fill K e` takes a head step,
  then either `K` is the empty evaluation context or `e` is a value.

**Changes in the logic (`base_logic`, `bi`):**

* Rename some accessor-style lemmas to consistently use the suffix `_acc`
  instead of `_open`:
  `inv_open` → `inv_acc`, `inv_open_strong` → `inv_acc_strong`,
  `inv_open_timeless` → `inv_acc_timeless`, `na_inv_open` → `na_inv_acc`,
  `cinv_open` → `cinv_acc`, `cinv_open_strong` → `cinv_acc_strong`,
  `auth_open` → `auth_acc`, `sts_open` → `sts_acc`.
  To make this work, also rename `inv_acc` → `inv_alter`.
  (Most developments should be unaffected as the typical way to invoke these
  lemmas is through `iInv`, and that does not change.)
* Change `inv_iff`, `cinv_iff` and `na_inv_iff` to make order of arguments
  consistent and more convenient for `iApply`. They are now of the form
  `inv N P -∗ ▷ □ (P ↔ Q) -∗ inv N Q` and (similar for `na_inv_iff` and
  `cinv_iff`), following e.g., `inv_alter` and `wp_wand`.
* Rename `inv_sep_1` → `inv_split_1`, `inv_sep_2` → `inv_split_2`, and
  `inv_sep` → `inv_split` to be consistent with the naming convention in boxes.
* Update the strong variant of the accessor lemma for cancellable invariants to
  match that of regular invariants, where you can pick the mask at a later time.
  (The other part that makes it strong is that you get back the token for the
  invariant immediately, not just when the invariant is closed again.)
* Rename `iProp`/`iPreProp` to `iPropO`/`iPrePropO` since they are `ofeT`s.
  Introduce `iProp` for the `Type` carrier of `iPropO`.
* Flatten the BI hierarchy by merging the `bi` and `sbi` canonical structures.
  This gives significant performance benefits on developments that construct BIs
  from BIs (e.g., use `monPred`). For, example it gives a performance gain of 37%
  overall on lambdarust-weak, with improvements for individual files up to 72%,
  see Iris issue #303. The concrete changes are as follows:
  + The `sbi` canonical structure has been removed.
  + The `bi` canonical structure contains the later modality. It does not
    require the later modality to be contractive or to satisfy the Löb rule, so
    we provide a smart constructor `bi_later_mixin_id` to get the later axioms
    "for free" if later is defined to be the identity function.
  + There is a separate class `BiLöb`, and a "free" instance of that class if
    the later modality is contractive. A `BiLöb` instance is required for the
    `iLöb` tactic, and for timeless instances of implication and wand.
  + There is a separate type class `BiInternalEq` for BIs with a notion of
    internal equality (internal equality was part of `sbi`). An instance of this
    class is needed for the `iRewrite` tactic, and the various lemmas about
    internal equality.
  + The class `SbiEmbed` has been removed and been replaced by classes
    `BiEmbedLater` and `BiEmbedInternalEq`.
  + The class `BiPlainly` has been generalized to BIs without internal equality.
    As a consequence, there is a separate class `BiPropExt` for BIs with
    propositional extensionality (i.e., `■ (P ∗-∗ Q) ⊢ P ≡ Q`).
  + The class `BiEmbedPlainly` is a bi-entailment (i.e., `⎡■ P⎤ ⊣⊢ ■ ⎡P⎤`
    instead of `■ ⎡P⎤ ⊢ ⎡■ P⎤`) as it has been generalized to BIs without a
    internal equality. In the past, the left-to-right direction was obtained for
    "free" using the rules of internal equality.
* Remove coercion from `iProp` (and other MoSeL propositions) to `Prop`.
  Instead, use the new unary notation `⊢ P`, or `⊢@{PROP} P` if the proposition
  type cannot be inferred. This also means that `%I` should not be necessary any
  more when stating lemmas, as `P` above is automatically parsed in scope `%I`.
* Some improvements to the `bi/lib/core` construction:
  + Rename `coreP_wand` into `coreP_entails` since it does not involve wands.
  + Generalize `coreP_entails` to non-affine BIs, and prove more convenient
    version `coreP_entails'` for `coreP P` with `P` affine.
  + Add instance `coreP_affine P : Affine P → Affine (coreP P)` and
    lemma `coreP_wand P Q : <affine> ■ (P -∗ Q) -∗ coreP P -∗ coreP Q`.
* Remove notation for 3-mask step-taking updates, and made 2-mask notation less
  confusing by distinguishing it better from mask-changing updates.
  Old: `|={Eo,Ei}▷=> P`. New: `|={Eo}[Ei]▷=> P`.
  Here, `Eo` is the "outer mask" (used at the beginning and end) and `Ei` the
  "inner mask" (used around the ▷ in the middle).
  As part of this, the lemmas about the 3-mask variant were changed to be about
  the 2-mask variant instead, and `step_fupd_mask_mono` now also has a more
  consistent argument order for its masks.

* Add a counterexample showing that sufficiently powerful cancellable invariants
  with a linear token subvert the linearity guarantee (see
  `bi.lib.counterexmples` for details).
* Redefine invariants as "semantic invariants" so that they support
  splitting and other forms of weakening.
* Add lemmas `inv_combine` and `inv_combine_dup_l` for combining invariants.
* Add the type `siProp` of "plain" step-indexed propositions, together with
  basic proofmode support.
* New ASCII versions of Iris notations. These are marked parsing only and
  can be made available using `Require Import iris.bi.ascii`. The new
  notations are (notations marked [†] are disambiguated using notation scopes):
  - entailment: `|-` for `⊢` and `-|-` for `⊣⊢`
  - logic[†]: `->` for `→`, `/\\` for `∧`, `\\/` for `∨`, and `<->` for `↔`
  - quantifiers[†]: `forall` for `∀` and `exists` for `∃`
  - separation logic: `**` for `∗`, `-*` for `-∗`, and `*-*` for `∗-∗`
  - step indexing: `|>` for `▷`
  - modalities: `<#>` for `□` and `<except_0>` for `◇`
  - most derived notations can be computed from previous notations using the
    substitutions above, e.g. replace `∗` with `*` and `▷` with `|>`. Examples
    include the following:
    - `|={E1,E2}=* P` for `|={E1,E2}=∗`
    - `P ={E}=* Q` for `P ={E}=∗ Q`
    - `P ={E1,E2}=* Q` for `P ={E1,E2}=∗ Q`
    - `|={E1}[E2]|>=> Q` for `|={E1}[E2]▷=> Q`
    The full list can be found in [theories/bi/ascii.v](theories/bi/ascii.v),
    where the ASCII notations are defined in terms of the unicode notations.
* Add affine, absorbing, persistent and timeless instances for telescopes.
* Add a construction `bi_rtc` to create reflexive transitive closures of
  PROP-level binary relations.
* Slightly strengthen the lemmas `big_sepL_nil'`, `big_sepL2_nil'`,
  `big_sepM_nil'` `big_sepM2_empty'`, `big_sepS_empty'`, and `big_sepMS_empty'`.
  They now only require that the argument `P` is affine instead of the whole BI
  being affine.
* Add `big_sepL_insert_acc`, a variant of `big_sepL_lookup_acc` which allows
  updating the value.
* Add many missing `Proper`/non-expansiveness lemmas for big-ops.
* Add `big_*_insert_delete` lemmas to split a `<[i:=x]> m` map into `i` and the rest.
* Seal the definitions of `big_opS`, `big_opMS`, `big_opM` and `big_sepM2`
  to prevent undesired simplification.
* Fix `big_sepM2_fmap*` only working for `nat` keys.

**Changes in `proofmode`:**

* Make use of `notypeclasses refine` in the implementation of `iPoseProof` and
  `iAssumption`, see <https://gitlab.mpi-sws.org/iris/iris/merge_requests/329>.
  This has two consequences:
  1. Coq's "new" unification algorithm (the one in `refine`, not the "old" one
     in `apply`) is used more often by the proof mode tactics.
  2. Due to the use of `notypeclasses refine`, TC constraints are solved less
     eagerly, see <https://github.com/coq/coq/issues/6583>.
  In order to port your development, it is often needed to instantiate evars
  explicitly (since TC search is performed less eagerly), and in few cases it is
  needed to unfold definitions explicitly (due to new unification algorithm
  behaving differently).
* Strengthen the tactics `iDestruct`, `iPoseProof`, and `iAssert`:
  - They succeed in certain cases where they used to fail.
  - They keep certain hypotheses in the intuitionistic context, where they were
    moved to the spatial context before.
  The latter can lead to stronger proof mode contexts, and therefore to
  backwards incompatibility. This can usually be fixed by manually clearing some
  hypotheses. A more detailed description of the changes can be found in
  <https://gitlab.mpi-sws.org/iris/iris/merge_requests/341>.
* Remove the long-deprecated `cofeT` alias (for `ofeT`) and `dec_agree` RA (use
  `agree` instead).

* Add `auto` hint for `∗-∗`.
* Add new tactic `iStopProof` to turn the proof mode entailment into an ordinary
  Coq goal `big star of context ⊢ proof mode goal`.
* Add new introduction pattern `-# pat` that moves a hypothesis from the
  intuitionistic context to the spatial context.
* The tactic `iAssumption` also recognizes assumptions `⊢ P` in the Coq context.
* Better support for telescopes in the proof mode, i.e., all tactics should
  recognize and distribute telescopes now.
* The proof mode now supports names for pure facts in intro patterns. Support
  requires implementing `string_to_ident`. Without this tactic such patterns
  will fail. We provide one implementation using Ltac2 which works with Coq 8.11
  and can be installed with opam; see
  [iris/string-ident](https://gitlab.mpi-sws.org/iris/string-ident) for details.

**Changes in `algebra`:**

* Remove `Core` type class for defining the total core; it is now always
  defined in terms of the partial core. The only user of this type class was the
  STS RA.
* The functions `{o,r,ur}Functor_diag` are no longer coercions, and renamed into
  `{o,r,ur}Functor_apply` to better match their intent. This fixes "ambiguous
  coercion path" warnings.
* Rename `{o,r,ur}Functor_{ne,id,compose,contractive}` into
  `{o,r,ur}Functor_map_{ne,id,compose,contractive}`.
* Move derived camera constructions (`frac_auth` and `ufrac_auth`) to the folder
  `algebra/lib`.
* Rename `mnat` to `max_nat` and "box" it by creating a separate type for it.
* Move the RAs for `nat` and `positive` and the `mnat` RA into a separate
  module. They must now be imported from `From iris.algebra Require Import
  numbers`.
* Make names of `f_op`/`f_core` rewrite lemmas more consistent by always making
  `_core`/`_op` the suffix:
  `op_singleton` → `singleton_op`, `core_singleton` → `singleton_core`,
  `discrete_fun_op_singleton` → `discrete_fun_singleton_op`,
  `discrete_fun_core_singleton` → `discrete_fun_singleton_core`,
  `list_core_singletonM` → `list_singleton_core`,
  `list_op_singletonM` → `list_singleton_op`,
  `sts_op_auth_frag` → `sts_auth_frag_op`,
  `sts_op_auth_frag_up` → `sts_auth_frag_up_op`,
  `sts_op_frag` → `sts_frag_op`,
  `list_op_length` → `list_length_op`,
  `list_core_singletonM` → `list_singletonM_core`,
  `list_op_singletonM` → `list_singletonM_op`.
* All list "map singleton" lemmas consistently use `singletonM` in their name:
  `list_singleton_valid` → `list_singletonM_valid`,
  `list_singleton_core_id` → `list_singletonM_core_id`,
  `list_singleton_snoc` → `list_singletonM_snoc`,
  `list_singleton_updateP` → `list_singletonM_updateP`,
  `list_singleton_updateP'` → `list_singletonM_updateP'`,
  `list_singleton_update` → `list_singletonM_update`,
  `list_alloc_singleton_local_update` → `list_alloc_singletonM_local_update`.
* Remove `auth_both_op` and rename `auth_both_frac_op` into `auth_both_op`.
* Add lemma `singleton_included : {[ i := x ]} ≼ ({[ i := y ]} ↔ x ≡ y ∨ x ≼ y`,
  and rename existing asymmetric lemmas (with a singleton on just the LHS):
  `singleton_includedN` → `singleton_includedN_l`,
  `singleton_included` → `singleton_included_l`,
  `singleton_included_exclusive` → `singleton_included_exclusive_l`.

* Add notion `ofe_iso A B` that states that OFEs `A` and `B` are
  isomorphic. This is used in the COFE solver.
* Add `{o,r,ur}Functor_oFunctor_compose` for composition of functors.
* Add `pair_op_1` and `pair_op_2` to split a pair where one component is the unit.
* Add derived camera construction `excl_auth A` for `auth (option (excl A))`.
* Make lemma `Excl_included` a bi-implication.
* Make `auth_update_core_id` work with any fraction of the authoritative
  element.
* Add `min_nat`, an RA for natural numbers with `min` as the operation.
* Add many missing `Proper`/non-expansiveness lemmas for maps and lists.
* Add `list_singletonM_included` and `list_lookup_singletonM_{lt,gt}` lemmas
  about singletons in the list RA.
* Add `list_core_id'`, a stronger version of `list_core_id` which only talks
  about elements that are actually in the list.

The following `sed` script helps adjust your code to the renaming (on macOS,
replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`).
Note that the script is not idempotent, do not run it twice.
```
sed -i -E '
# functor renames
s/\b(o|r|ur)Functor_(ne|id|compose|contractive)\b/\1Functor_map_\2/g
# singleton_included renames
s/\bsingleton_includedN\b/singleton_includedN_l/g
s/\bsingleton_included\b/singleton_included_l/g
s/\bsingleton_included_exclusive\b/singleton_included_exclusive_l/g
# f_op/f_core renames
s/\b(op|core)_singleton\b/singleton_\1/g
s/\bdiscrete_fun_(op|core)_singleton\b/discrete_fun_singleton_\1/g
s/\bsts_op_(auth_frag|auth_frag_up|frag)\b/sts_\1_op/g
s/\blist_(op|core)_singletonM\b/list_singletonM_\1/g
s/\blist_op_length\b/list_length_op/g
# list "singleton map" renames
s/\blist_singleton_valid\b/list_singletonM_valid/g
s/\blist_singleton_core_id\b/list_singletonM_core_id/g
s/\blist_singleton_snoc\b/list_singletonM_snoc/g
s/\blist_singleton_updateP\b/list_singletonM_updateP/g
s/\blist_singleton_update\b/list_singletonM_update/g
s/\blist_alloc_singleton_local_update\b/list_alloc_singletonM_local_update/g
# inv renames
s/\binv_sep(|_1|_2)\b/inv_split\1/g
s/\binv_acc\b/inv_alter/g
s/\binv_open(|_strong|_timeless)\b/inv_acc\1/g
s/\bcinv_open(|_strong)\b/cinv_acc\1/g
s/\b(na_inv|auth|sts)_open\b/\1_acc/g
# miscellaneous
s/\bauth_both_frac_op\b/auth_both_op/g
s/\bmnat\b/max_nat/g
s/\bcoreP_wand\b/coreP_entails/g
' $(find theories -name "*.v")
```

## Iris 3.2.0 (released 2019-08-29)

The highlight of this release is the completely re-engineered interactive proof
mode.  Not only did many tactics become more powerful; the entire proof mode can
now be used not just for Iris but also for other separation logics satisfying
the proof mode interface (e.g., [Iron] and [GPFSL]). Also see the
[accompanying paper][MoSeL].

[Iron]: https://iris-project.org/iron/
[GPFSL]: https://gitlab.mpi-sws.org/iris/gpfsl/
[MoSeL]: https://iris-project.org/mosel/

Beyond that, the Iris program logic gained the ability to reason about
potentially stuck programs, and a significantly strengthened adequacy theorem
that unifies the three previously separately presented theorems.  There are now
also Hoare triples for total program correctness (but with very limited support
for invariants) and logical atomicity.

And finally, our example language HeapLang was made more realistic
(Compare-and-set got replaced by compare-exchange and limited to only compare
values that can actually be compared atomically) and more powerful, with added
support for arrays and prophecy variables.

Further details are given in the changelog below.

This release of Iris received contributions by Aleš Bizjak, Amin Timany, Dan
Frumin, Glen Mével, Hai Dang, Hugo Herbelin, Jacques-Henri Jourdan, Jan Menz,
Jan-Oliver Kaiser, Jonas Kastberg Hinrichsen, Joseph Tassarotti, Mackie Loeffel,
Marianna Rapoport, Maxime Dénès, Michael Sammler, Paolo G. Giarrusso,
Pierre-Marie Pédrot, Ralf Jung, Robbert Krebbers, Rodolphe Lepigre, and Tej
Chajed. Thanks a lot to everyone involved!

**Changes in the theory of Iris itself:**

* Change in the definition of WP, so that there is a fancy update between
  the quantification over the next states and the later modality. This makes it
  possible to prove more powerful lifting lemmas: The new versions feature an
  "update that takes a step".
* Add weakest preconditions for total program correctness.
* "(Potentially) stuck" weakest preconditions and the "plainly modality" are no
  longer considered experimental.
* Add the notion of an "observation" to the language interface, so that
  every reduction step can optionally be marked with an event, and an execution
  trace has a matching list of events.  Change WP so that it is told the entire
  future trace of observations from the beginning.
* The Löb rule is now a derived rule; it follows from later-intro, later
  being contractive and the fact that we can take fixpoints of contractive
  functions.
* Add atomic updates and logically atomic triples, including tactic support.
  See `heap_lang/lib/increment.v` for an example.
* Extend the state interpretation with a natural number that keeps track of
  the number of forked-off threads, and have a global fixed proposition that
  describes the postcondition of each forked-off thread (instead of it being
  `True`).
* A stronger adequacy statement for weakest preconditions that involves
  the final state, the post-condition of forked-off threads, and also applies if
  the main-thread has not terminated.
* The user-chosen functor used to instantiate the Iris logic now goes from
  COFEs to Cameras (it was OFEs to Cameras).

**Changes in heap_lang:**

* CAS (compare-and-set) got replaced by CmpXchg (compare-exchange).  The
  difference is that CmpXchg returns a pair consisting of the old value and a
  boolean indicating whether the comparison was successful and hence the
  exchange happened.  CAS can be obtained by simply projecting to the second
  component, but also providing the old value more closely models the primitive
  typically provided in systems languages (C, C++, Rust).
  The comparison by this operation also got weakened to be efficiently
  implementable: CmpXchg may only be used to compare "unboxed" values that can
  be represented in a single machine word. It is sufficient if one of the two
  compared values is unboxed.
* For consistency, the restrictions CmpXchg imposes on comparison also apply to
  the `=` binary operator. This also fixes the long-standing problem that that
  operator allowed compared closures with each other.
* Implement prophecy variables using the new support for "observations". The
  erasure theorem (showing that prophecy variables do not alter program
  behavior) can be found [in the iris/examples repository][prophecy-erasure].
* heap_lang now uses right-to-left evaluation order. This makes it
  significantly easier to write specifications of curried functions.
* heap_lang values are now injected in heap_lang expressions via a specific
  constructor of the expr inductive type. This simplifies much the tactical
  infrastructure around the language. In particular, this allow us to get rid
  the reflection mechanism that was needed for proving closedness, atomicity and
  "valueness" of a term. The price to pay is the addition of new
  "administrative" reductions in the operational semantics of the language.
* heap_lang now has support for allocating, accessing and reasoning about arrays
  (continuously allocated regions of memory).
* One can now assign "meta" data to heap_lang locations.

[prophecy-erasure]: https://gitlab.mpi-sws.org/iris/examples/blob/3f33781fe6e19cfdb25259c8194d34403f1134d5/theories/logatom/proph_erasure.v

**Changes in Coq:**

* An all-new generalized proof mode that abstracts away from Iris!  Major new
  features:
  - The proof mode can now be used with logics derived from Iris (like iGPS),
    with non-step-indexed logics and even with non-affine (i.e., linear) logics.
  - `iModIntro` is more flexible and more powerful, it now also subsumes
    `iNext` and `iAlways`.
  - General infrastructure for deriving a logic for monotone predicates over
    an existing logic (see the paper for more details).
    Developments instantiating the proof mode typeclasses may need significant
    changes.  For developments just using the proof mode tactics, porting should
    not be too much effort.  Notable things to port are:
  - All the BI laws moved from the `uPred` module to the `bi` module.  For
    example, `uPred.later_equivI` became `bi.later_equivI`.
  - Big-ops are automatically imported, imports of `iris.base_logic.big_op` have
    to be removed.
  - The ⊢ notation can sometimes infer different (but convertible) terms when
    searching for the BI to use, which (due to Coq limitations) can lead to
    failing rewrites, in particular when rewriting at function types.
* The `iInv` tactic can now be used without the second argument (the name for
  the closing update).  It will then instead add the obligation to close the
  invariant to the goal.
* The new `iEval` tactic can be used to execute a simplification or rewriting
  tactic on some specific part(s) of the proofmode goal.
* Added support for defining derived connectives involving n-ary binders using
  telescopes.
* The proof mode now more consistently "prettifies" the goal after each tactic.
  Prettification also simplifies some BI connectives, like conditional
  modalities and telescope quantifiers.
* Improved pretty-printing of Iris connectives (in particular WP and fancy
  updates) when Coq has to line-wrap the output.  This goes hand-in-hand with an
  improved test suite that also tests pretty-printing.
* Added a `gmultiset` RA.
* Rename `timelessP` → `timeless` (projection of the `Timeless` class)
* The CMRA axiom `cmra_extend` is now stated in `Type`, using `sigT` instead of
  in `Prop` using `exists`. This makes it possible to define the function space
  CMRA even for an infinite domain.
* Rename proof mode type classes for laters:
  - `IntoLaterN` → `MaybeIntoLaterN` (this one _may_ strip a later)
  - `IntoLaterN'` → `IntoLaterN` (this one _should_ strip a later)
  - `IntoLaterNEnv` → `MaybeIntoLaterNEnv`
  - `IntoLaterNEnvs` → `MaybeIntoLaterNEnvs`
* Rename:
  - `frag_auth_op` → `frac_auth_frag_op`
  - `cmra_opM_assoc` → `cmra_op_opM_assoc`
  - `cmra_opM_assoc_L` → `cmra_op_opM_assoc_L`
  - `cmra_opM_assoc'` → `cmra_opM_opM_assoc`
* `namespaces` has been moved to std++.
* Changed `IntoVal` to be directly usable for rewriting `e` into `of_val v`, and
  changed `AsVal` to be usable for rewriting via the `[v <-]` destruct pattern.
* `wp_fork` is now written in curried form.
* `PureExec`/`wp_pure` now supports taking multiple steps at once.
* A new tactic, `wp_pures`, executes as many pure steps as possible, excluding
  steps that would require unlocking subterms. Every impure wp_ tactic executes
  this tactic before doing anything else.
* Add `big_sepM_insert_acc`.
* Add big separating conjunctions that operate on pairs of lists (`big_sepL2`)
  and on pairs of maps (`big_sepM2`). In the former case the lists are required
  to have the same length, and in the latter case the maps are required to
  have the same domains.
* The `_strong` lemmas (e.g. `own_alloc_strong`) work for all infinite
  sets, instead of just for cofinite sets. The versions with cofinite
  sets have been renamed to use the `_cofinite` suffix.
* Remove locked value lambdas. The value scope notations `rec: f x := e` and
  `(λ: x, e)` no longer add a `locked`. Instead, we made the `wp_` tactics
  smarter to no longer unfold lambdas/recs that occur behind definitions.
* Export the fact that `iPreProp` is a COFE.
* The CMRA `auth` now can have fractional authoritative parts. So now `auth` has
  3 types of elements: the fractional authoritative `●{q} a`, the full
  authoritative `● a ≡ ●{1} a`, and the non-authoritative `◯ a`. Updates are
  only possible with the full authoritative element `● a`, while fractional
  authoritative elements have agreement: `✓ (●{p} a ⋅ ●{q} b) ⇒ a ≡ b`. As a
  consequence, `auth` is no longer a COFE and does not preserve Leibniz
  equality.
* Add a COFE construction (and functor) on dependent pairs `sigTO`, dual to
  `discrete_funO`.
* Rename in `auth`:
  - Use `auth_auth_proj`/`auth_frag_proj` for the projections of `auth`:
    `authoritative` → `auth_auth_proj` and `auth_own` → `auth_frag_proj`.
  - Use `auth_auth` and `auth_frag` for the injections into authoritative
    elements and non-authoritative elements respectively.
  - Lemmas for the projections and injections are renamed accordingly.
    For examples:
    + `authoritative_validN` → `auth_auth_proj_validN`
    + `auth_own_validN` → `auth_frag_proj_validN`
    + `auth_auth_valid` was not renamed because it was already used for the
      authoritative injection.
  - `auth_both_valid` → `auth_both_valid_2`
  - `auth_valid_discrete_2` → `auth_both_valid`
* Add the camera `ufrac` for unbounded fractions (i.e. without fractions that
  can be `> 1`) and the camera `ufrac_auth` for a variant of the authoritative
  fractional camera (`frac_auth`) with unbounded fractions.
* Changed `frac_auth` notation from `●!`/`◯!` to `●F`/`◯F`. sed script:
  `s/◯!/◯F/g; s/●!/●F/g;`.
* Lemma `prop_ext` works in both directions; its default direction is the
  opposite of what it used to be.
* Make direction of `f_op` rewrite lemmas more consistent: Flip `pair_op`,
  `Cinl_op`, `Cinr_op`, `cmra_morphism_op`, `cmra_morphism_pcore`,
  `cmra_morphism_core`.
* Rename lemmas `fupd_big_sep{L,M,S,MS}` into `big_sep{L,M,S,MS}_fupd` to be
  consistent with other such big op lemmas. Also add such lemmas for `bupd`.
* Rename `C` suffixes into `O` since we no longer use COFEs but OFEs. Also
  rename `ofe_fun` into `discrete_fun` and the corresponding notation `-c>` into
  `-d>`. The renaming can be automatically done using the following script
  (on macOS, replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i '
s/\bCofeMor/OfeMor/g;
s/\-c>/\-d>/g;
s/\bcFunctor/oFunctor/g;
s/\bCFunctor/OFunctor/g;
s/\b\%CF/\%OF/g;
s/\bconstCF/constOF/g;
s/\bidCF/idOF/g
s/\bdiscreteC/discreteO/g;
s/\bleibnizC/leibnizO/g;
s/\bunitC/unitO/g;
s/\bprodC/prodO/g;
s/\bsumC/sumO/g;
s/\bboolC/boolO/g;
s/\bnatC/natO/g;
s/\bpositiveC/positiveO/g;
s/\bNC/NO/g;
s/\bZC/ZO/g;
s/\boptionC/optionO/g;
s/\blaterC/laterO/g;
s/\bofe\_fun/discrete\_fun/g;
s/\bdiscrete\_funC/discrete\_funO/g;
s/\bofe\_morC/ofe\_morO/g;
s/\bsigC/sigO/g;
s/\buPredC/uPredO/g;
s/\bcsumC/csumO/g;
s/\bagreeC/agreeO/g;
s/\bauthC/authO/g;
s/\bnamespace_mapC/namespace\_mapO/g;
s/\bcmra\_ofeC/cmra\_ofeO/g;
s/\bucmra\_ofeC/ucmra\_ofeO/g;
s/\bexclC/exclO/g;
s/\bgmapC/gmapO/g;
s/\blistC/listO/g;
s/\bvecC/vecO/g;
s/\bgsetC/gsetO/g;
s/\bgset\_disjC/gset\_disjO/g;
s/\bcoPsetC/coPsetO/g;
s/\bgmultisetC/gmultisetO/g;
s/\bufracC/ufracO/g
s/\bfracC/fracO/g;
s/\bvalidityC/validityO/g;
s/\bbi\_ofeC/bi\_ofeO/g;
s/\bsbi\_ofeC/sbi\_ofeO/g;
s/\bmonPredC/monPredO/g;
s/\bstateC/stateO/g;
s/\bvalC/valO/g;
s/\bexprC/exprO/g;
s/\blocC/locO/g;
s/\bdec\_agreeC/dec\_agreeO/g;
s/\bgnameC/gnameO/g;
s/\bcoPset\_disjC/coPset\_disjO/g;
' $(find theories -name "*.v")
```

## Iris 3.1.0 (released 2017-12-19)

**Changes in and extensions of the theory:**

* Define `uPred` as a quotient on monotone predicates `M -> SProp`.
* Get rid of some primitive laws; they can be derived:
  `True ⊢ □ True` and `□ (P ∧ Q) ⊢ □ (P ∗ Q)`
* Camera morphisms have to be homomorphisms, not just monotone functions.
* Add a proof that `f` has a fixed point if `f^k` is contractive.
* Constructions for least and greatest fixed points over monotone predicates
  (defined in the logic of Iris using impredicative quantification).
* Add a proof of the inverse of `wp_bind`.
* [Experimental feature] Add new modality: ■ ("plainly").
* [Experimental feature] Support verifying code that might get stuck by
  distinguishing "non-stuck" vs. "(potentially) stuck" weakest
  preconditions. (See [Swasey et al., OOPSLA '17] for examples.) The non-stuck
  `WP e @ E {{ Φ }}` ensures that, as `e` runs, it does not get stuck. The stuck
  `WP e @ E ?{{ Φ }}` ensures that, as usual, all invariants are preserved while
  `e` runs, but it permits execution to get stuck. The former implies the
  latter. The full judgment is `WP e @ s; E {{ Φ }}`, where non-stuck WP uses
  *stuckness bit* `s = NotStuck` while stuck WP uses `s = MaybeStuck`.

**Changes in Coq:**

* Move the `prelude` folder to its own project:
  [coq-std++](https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp)
* Some extensions/improvements of heap_lang:
  - Improve handling of pure (non-state-dependent) reductions.
  - Add fetch-and-add (`FAA`) operation.
  - Add syntax for all Coq's binary operations on `Z`.
* Generalize `saved_prop` to let the user choose the location of the type-level
  later.  Rename the general form to `saved_anything`.  Provide `saved_prop` and
  `saved_pred` as special cases.
* Improved big operators:
  + They are no longer tied to cameras, but work on any monoid
  + The version of big operations over lists was redefined so that it enjoys
    more definitional equalities.
* Rename some things and change notation:
  - The unit of a camera: `empty` -> `unit`, `∅` -> `ε`
  - Disjointness: `⊥` -> `##`
  - A proof mode type class `IntoOp` -> `IsOp`
  - OFEs with all elements being discrete: `Discrete` -> `OfeDiscrete`
  - OFE elements whose equality is discrete: `Timeless` -> `Discrete`
  - Timeless propositions: `TimelessP` -> `Timeless`
  - Camera elements such that `core x = x`: `Persistent` -> `CoreId`
  - Persistent propositions: `PersistentP` -> `Persistent`
  - The persistent modality: `always` -> `persistently`
  - Adequacy for non-stuck weakestpre: `adequate_safe` -> `adequate_not_stuck`
  - Consistently SnakeCase identifiers:
    + `CMRAMixin` -> `CmraMixin`
    + `CMRAT` -> `CmraT`
    + `CMRATotal` -> `CmraTotal`
    + `CMRAMorphism` -> `CmraMorphism`
    + `CMRADiscrete` -> `CmraDiscrete`
    + `UCMRAMixin` -> `UcmraMixin`
    + `UCMRAT` -> `UcmraT`
    + `DRAMixin` -> `DraMixin`
    + `DRAT` -> `DraT`
    + `STS` -> `Sts`
  - Many lemmas also changed their name.  `always_*` became `persistently_*`,
    and furthermore: (the following list is not complete)
    + `impl_wand` -> `impl_wand_1` (it only involves one direction of the
      equivalent)
    + `always_impl_wand` -> `impl_wand`
    + `always_and_sep_l` -> `and_sep_l`
    + `always_and_sep_r` -> `and_sep_r`
    + `always_sep_dup` -> `sep_dup`
    + `wand_impl_always` -> `impl_wand_persistently` (additionally,
      the direction of this equivalence got swapped for consistency's sake)
    + `always_wand_impl` -> `persistently_impl_wand` (additionally, the
      direction of this equivalence got swapped for consistency's sake)
  The following `sed` snippet should get you most of the way (on macOS you will
  have to replace `sed` by `gsed`, installed via e.g. `brew install gnu-sed`):
```
sed -i 's/\bPersistentP\b/Persistent/g; s/\bTimelessP\b/Timeless/g; s/\bCMRADiscrete\b/CmraDiscrete/g; s/\bCMRAT\b/CmraT/g; s/\bCMRAMixin\b/CmraMixin/g; s/\bUCMRAT\b/UcmraT/g; s/\bUCMRAMixin\b/UcmraMixin/g; s/\bSTS\b/Sts/g' $(find -name "*.v")
```
* `PersistentL` and `TimelessL` (persistence and timelessness of lists of
  propositions) are replaces by `TCForall` from std++.
* Fix a bunch of consistency issues in the proof mode, and make it overall more
  usable.  In particular:
  - All proof mode tactics start the proof mode if necessary; `iStartProof` is
    no longer needed and should only be used for building custom proof mode
    tactics.
  - Change in the grammar of specialization patterns: `>[...]` -> `[> ...]`
  - Various new specification patterns for `done` and framing.
  - There is common machinery for symbolic execution of pure reductions. This
    is provided by the type classes `PureExec` and `IntoVal`.
  - There is a new connective `tc_opaque`, which can be used to make definitions
    opaque for type classes, and thus opaque for most tactics of the proof
    mode.
  - Define Many missing type class instances for distributing connectives.
  - Implement the tactics `iIntros (?)` and `iIntros "!#"` (i.e. `iAlways`)
    using type classes. This makes them more generic, e.g., `iIntros (?)` also
    works when the universal quantifier is below a modality, and `iAlways` also
    works for the plainness modality.  A breaking change, however, is that these
    tactics now no longer work when the universal quantifier or modality is
    behind a type class opaque definition.  Furthermore, this can change the
    name of anonymous identifiers introduced with the "%" pattern.
* Make `ofe_fun` dependently typed, subsuming `iprod`.  The latter got removed.
* Define the generic `fill` operation of the `ectxi_language` construct in terms
  of a left fold instead of a right fold. This gives rise to more definitional
  equalities.
* The language hierarchy (`language`, `ectx_language`, `ectxi_language`) is now
  fully formalized using canonical structures instead of using a mixture of
  type classes and canonical structures. Also, it now uses explicit mixins. The
  file `program_logic/ectxi_language` contains some documentation on how to
  setup Iris for your language.
* Restore the original, stronger notion of atomicity alongside the weaker
  notion. These are `Atomic a e` where the stuckness bit `s` indicates whether
  expression `e` is weakly (`a = WeaklyAtomic`) or strongly
  (`a = StronglyAtomic`) atomic.
* Various improvements to `solve_ndisj`.
* Use `Hint Mode` to prevent Coq from making arbitrary guesses in the presence
  of evars, which often led to divergence. There are a few places where type
  annotations are now needed.
* The rules `internal_eq_rewrite` and `internal_eq_rewrite_contractive` are now
  stated in the logic, i.e., they are `iApply`-friendly.

## Iris 3.0.0 (released 2017-01-11)

* There now is a deprecation process.  The modules `*.deprecated` contain
  deprecated notations and definitions that are provided for backwards
  compatibility and will be removed in a future version of Iris.
* View shifts are radically simplified to just internalize frame-preserving
  updates.  Weakestpre is defined inside the logic, and invariants and view
  shifts with masks are also coded up inside Iris.  Adequacy of weakestpre is
  proven in the logic. The old ownership of the entire physical state is
  replaced by a user-selected predicate over physical state that is maintained
  by weakestpre.
* Use OFEs instead of COFEs everywhere.  COFEs are only used for solving the
  recursive domain equation.  As a consequence, CMRAs no longer need a proof of
  completeness.  (The old `cofeT` is provided by `algebra.deprecated`.)
* Implement a new agreement construction.  Unlike the old one, this one
  preserves discreteness.  dec_agree is thus no longer needed and has been moved
  to algebra.deprecated.
* Renaming and moving things around: uPred and the rest of the base logic are in
  `base_logic`, while `program_logic` is for everything involving the general
  Iris notion of a language.
* Renaming in prelude.list: Rename `prefix_of` -> `prefix` and `suffix_of` ->
  `suffix` in lemma names, but keep notation ``l1 `prefix_of` l2`` and ``l1
  `suffix_of` l2``.  `` l1 `sublist` l2`` becomes ``l1 `sublist_of` l2``. Rename
  `contains` -> `submseteq` and change `` l1 `contains` l2`` to ``l1 ⊆+ l2``.
* Slightly weaker notion of atomicity: an expression is atomic if it reduces in
  one step to something that does not reduce further.
* Changed notation for embedding Coq assertions into Iris.  The new notation is
  ⌜φ⌝.  Also removed `=` and `⊥` from the Iris scope.  (The old notations are
  provided in `base_logic.deprecated`.)
* Up-closure of namespaces is now a notation (↑) instead of a coercion.
* With invariants and the physical state being handled in the logic, there is no
  longer any reason to demand the CMRA unit to be discrete.
* The language can now fork off multiple threads at once.
* Local Updates (for the authoritative monoid) are now a 4-way relation with
  syntax-directed lemmas proving them.

## Iris 2.0

* [heap_lang] No longer use dependent types for expressions.  Instead, values
  carry a proof of closedness.  Substitution, closedness and value-ness proofs
  are performed by computation after reflecting into a term langauge that knows
  about values and closed expressions.
* [program_logic/language] The language does not define its own "atomic"
  predicate.  Instead, atomicity is defined as reducing in one step to a value.
* [program_logic] Due to a lack of maintenance and usefulness, lifting lemmas
  for Hoare triples are removed.

## Iris 2.0-rc2

This version matches the final ICFP 2016 paper.

* [algebra] Make the core of an RA or CMRA a partial function.
* [program_logic/lifting] Lifting lemmas no longer round-trip through a
  user-chosen predicate to define the configurations we can reduce to; they
  directly relate to the operational semantics.  This is equivalent and
  much simpler to read.

## Iris 2.0-rc1

This is the Coq development and Iris Documentation as submitted to ICFP 2016.
