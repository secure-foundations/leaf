## Global resource algebra management

The type of Iris propositions `iProp Σ` is parameterized by a *global* list `Σ:
gFunctors` of resource algebras that the proof may use.  (Actually this list
contains functors instead of resource algebras, but you only need to worry about
that when dealing with higher-order ghost state -- see "Camera functors" below.)

In our proofs, we always keep the `Σ` universally quantified to enable composition of proofs.
Each proof just assumes that some particular resource algebras are contained in that global list.
This is expressed via the `inG Σ R` typeclass, which roughly says that `R ∈ Σ`
("`R` is in the `G`lobal list of RAs `Σ` -- hence the `G`).

Libraries typically bundle the `inG` they need in a `libG` typeclass, so they do
not have to expose to clients what exactly their resource algebras are. For
example, in the [one-shot example](../tests/one_shot.v), we have:
```coq
Class one_shotG Σ := { one_shot_inG : inG Σ one_shotR }.
Local Existing Instances one_shot_inG.
```
Here, the projection `one_shot_inG` is registered as an instance for type-class
resolution. If you need several resource algebras, just add more `inG` fields.
If you are using another module as part of yours, add a field like
`one_shot_other : otherG Σ`. All of these fields should be added to the
`Local Existing Instances` command.

The code above enables these typeclass instances only in the surrounding file
where they are used to define the new abstractions by the library. The
interface of these abstractions will only depend on the `one_shotG` class.
Since `one_shot_inG` will be hidden from clients, they will not accidentally
rely on it in their code.

Having defined the type class, we need to provide a way to instantiate it.  This
is an important step, as not every resource algebra can actually be used: if
your resource algebra refers to `Σ`, the definition becomes recursive.  That is
actually legal under some conditions (see "Camera functors" below), but for now
we will ignore that case.  We have to define a list that contains all the
resource algebras we need:
```coq
Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
```
This time, there is no `Σ` in the context, so we cannot accidentally introduce a
bad dependency.  If you are using another module as part of yours, add their
`somethingΣ` to yours, as in `#[GFunctor one_shotR; somethingΣ]`.  (The
`#[F1; F2; ...]` syntax *appends* the functor lists `F1`, `F2`, ... to each
other; together with a coercion from a single functor to a singleton list, this
means lists can be nested arbitrarily.)

Now we can define the one and only instance that our type class will ever need:
```coq
Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.
```
The `subG` assumption here says that the list `one_shotΣ` is a sublist of the
global list `Σ`.  Typically, this should be the only assumption your instance
needs, showing that the assumptions of the module (and all the modules it
uses internally) can trivially be satisfied by picking the right `Σ`.

Now you can add `one_shotG` as an assumption to all your module definitions and
proofs.  We typically use a section for this:
```coq
Section proof.
Context `{!heapGS Σ, !one_shotG Σ}.
```
Notice that besides our own assumptions `one_shotG`, we also assume `heapGS`,
which are assumptions that every HeapLang proof makes (they are related to
defining the `↦` connective as well as the basic Iris infrastructure for
invariants and WP).  For this purpose, `heapGS` contains not only assumptions
about `Σ`, it also contains some ghost names to refer to particular ghost state
(see "global ghost state instances" below).

The backtick (`` ` ``) is used to make anonymous assumptions and to automatically
generalize the `Σ`.  When adding assumptions with backtick, you should most of
the time also add a `!` in front of every assumption.  If you do not then Coq
will also automatically generalize all indices of type-classes that you are
assuming.  This can easily lead to making more assumptions than you are aware
of, and often it leads to duplicate assumptions which breaks type class
resolutions.

## Resource algebra combinators

Defining a new resource algebra `one_shotR` for each new proof and verifying all
the algebra laws would be quite cumbersome, so instead Iris provides a rich set
of resource algebra combinators that one can use to build up the desired
resource algebras. For example, `one_shotR` is defined as follows:

```coq
Definition one_shotR := csumR (exclR unitO) (agreeR ZO).
```

The suffixes `R` and `O` indicate that we are not working on the level of Coq
types here, but on the level of `R`esource algebras and `O`FEs,
respectively. Unfortunately this means we cannot use Coq's usual type notation
(such as `*` for products and `()` for the unit type); we have to spell out the
underlying OFE or resource algebra names instead.

## Obtaining a closed proof

To obtain a closed Iris proof, i.e., a proof that does not make assumptions like
`inG`, you have to assemble a list of functors of all the involved modules,
and if your proof relies on some singleton (most do, at least indirectly; also
see the next section), you have to call the respective initialization or
adequacy lemma.  [For example](tests/one_shot.v):
```coq
Section client.
  Context `{!heapGS Σ, !one_shotG Σ, !spawnG Σ}.

  Lemma client_safe : WP client {{ _, True }}%I.
  (* ... *)
End client.

(** Assemble all functors needed by the [client_safe] proof. *)
Definition clientΣ : gFunctors := #[ heapΣ; one_shotΣ; spawnΣ ].

(** Apply [heap_adequacy] with this list of all functors. *)
Lemma client_adequate σ : adequate NotStuck client σ (λ _ _, True).
Proof. apply (heap_adequacy clientΣ)=> ?. apply client_safe. Qed.
```

## Advanced topic: Ghost state singletons

Some Iris modules involve a form of "global state".  For example, defining the
`↦` for HeapLang involves a piece of ghost state that matches the current
physical heap.  The `gname` of that ghost state must be picked once when the
proof starts, and then globally known everywhere.  Hence `gen_heapGS`, the type
class for the generalized heap module, bundles the usual `inG` assumptions
together with the `gname`:
```coq
Class gen_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heapGpreS_heap : ghost_mapG Σ L V;
}.
Local Existing Instances gen_heapGpreS_heap.
Class gen_heapGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapGS {
  gen_heap_inG : gen_heapGpreS L V Σ;
  gen_heap_name : gname;
}.
Local Existing Instances gen_heap_inG.
```
The trailing `S` here is for "singleton", because the idea is that only one
instance of `gen_heapGS` ever exists. This is important, since two instances
might have different `gname`s, so `↦` based on these two distinct instances
would be incompatible with each other.

The `gen_heapGpreS` typeclass (without the singleton data) is relevant for
initialization, i.e., to create an instance of `gen_heapGS`. This is happening as
part of [`heap_adequacy`](iris_heap_lang/adequacy.v) using the
initialization lemma for `gen_heapGS` from
[`gen_heap_init`](iris/base_logic/lib/gen_heap.v):
```coq
Lemma gen_heap_init `{gen_heapGpreS L V Σ} σ :
  (|==> ∃ _ : gen_heapGS L V Σ, gen_heap_ctx σ)%I.
```
These lemmas themselves only make assumptions the way normal modules (those
without global state) do. Just like in the normal case, `somethingGpreS` type
classes have an `Instance` showing that a `subG` is enough to instantiate them:
```coq
Global Instance subG_gen_heapGpreS {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapGpreS L V Σ.
Proof. solve_inG. Qed.
```
The initialization lemma then shows that the `somethingGpreS` type class is
enough to create an instance of the main `somethingGS` class *below a view
shift*.  This is written with an existential quantifier in the lemma because the
statement after the view shift (`gen_heap_ctx σ` in this case) depends on having
an instance of `gen_heapGS` in the context.

Given that these global ghost state instances are singletons, they must be
assumed explicitly everywhere.  Bundling `heapGS` in a (non-singleton) module
type class like `one_shotG` would lose track of the fact that there exists just
one `heapGS` instance that is shared by everyone.

## Advanced topic: Camera functors and higher-order ghost state

As we already alluded to, `Σ` actually consists of functors, not resource
algebras. This enables you to use *higher-order ghost state*: ghost state that
recursively refers to `iProp`.

**Background: Iris Model.** To understand how this works, we have to dig a bit
into the model of Iris. In Iris, the type of propositions `iProp` is described
by the solution to the recursive domain equation:

```coq
iProp ≅ uPred (F (iProp))
```

Here, `uPred M` describes "propositions with resources of type `M`".  The
peculiar aspect of this definition is that the notion of resources can itself
refer to the set propositions that we are just defining; that dependency is
expressed by `F`.  `F` is a user-chosen locally contractive bifunctor from COFEs
to unital Cameras (a step-indexed generalization of unital resource
algebras). Having just a single fixed `F` would however be rather inconvenient,
so instead we have a list `Σ`, and then we define the global functor `F_global`
roughly as follows:

```coq
F_global X := Π_{F ∈ Σ} gmap nat (F X)
```

In other words, each functor in `Σ` is applied to the recursive argument `X`,
wrapped in a finite partial function, and then we take a big product of all of
that.  The product ensures that all `F ∈ Σ` are available, and the `gmap` is
needed to provide the proof rule `own_alloc`, which lets you create new
instances of the given type of resource any time.

However, this on its own would be too restrictive, as it requires all
occurrences of `X` to be in positive positions (otherwise the functor laws
would not hold for `F`).  To mitigate this, we instead work with "bifunctors":
functors that take two arguments, `X` and `X⁻`, where `X⁻` is used for
negative positions.  This leads us to the following domain equation:

```coq
iProp ≅ uPred (F_global (iProp,iProp))
F_global (X,X⁻) := Π_{F ∈ Σ} gmap nat (F (X,X⁻))
```

To make this equation well-defined, the bifunctors `F ∈ Σ` need to be "contractive".
For further details, see §7.4 of
[The Iris Documentation](http://plv.mpi-sws.org/iris/appendix-3.3.pdf); here we
describe the user-side Coq aspects of this approach.

Below, when we say "functor", we implicitly mean "bifunctor".

**Higher-order ghost state.** To use higher-order ghost state, you need to give
a functor whose "hole" will later be filled with `iProp` itself. For example,
let us say you would like to have ghost state of type `gmap K (agree (nat *
later iProp))`, using the "type-level" `later` operator which ensures
contractivity.  Then you will have to define a functor such as:

```coq
F (X,X⁻) := gmap K (agree (nat * ▶ X))
```

To make it convenient to construct such functors and prove their contractivity,
we provide a number of abstractions:

- [`oFunctor`](iris/algebra/ofe.v): functors from COFEs to OFEs.
- [`rFunctor`](iris/algebra/cmra.v): functors from COFEs to cameras.
- [`urFunctor`](iris/algebra/cmra.v): functors from COFEs to unital
  cameras.

Besides, there are the classes `oFunctorContractive`, `rFunctorContractive`, and
`urFunctorContractive` which describe the subset of the above functors that are
contractive.

To compose these functors, we provide a number of combinators, e.g.:

- `constOF (A : ofe) : oFunctor            := λ (B,B⁻), A `
- `idOF : oFunctor                         := λ (B,B⁻), B`
- `prodOF (F1 F2 : oFunctor) : oFunctor    := λ (B,B⁻), F1 (B,B⁻) * F2 (B,B⁻)`
- `ofe_morOF (F1 F2 : oFunctor) : oFunctor := λ (B,B⁻), F1 (B⁻,B) -n> F2 (B,B⁻)`
- `laterOF (F : oFunctor) : oFunctor       := λ (B,B⁻), later (F (B,B⁻))`
- `agreeRF (F : oFunctor) : rFunctor       := λ (B,B⁻), agree (F (B,B⁻))`
- `gmapURF K (F : rFunctor) : urFunctor    := λ (B,B⁻), gmap K (F (B,B⁻))`

Note in particular how the functor for the function space, `ofe_morOF`, swaps
`B` and `B⁻` for the functor `F1` describing the domain.  This reflects the fact
that that functor is used in a negative position.

Using these combinators, one can easily construct bigger functors in point-free
style and automatically infer their contractivity, e.g:

```coq
F := gmapURF K (agreeRF (prodOF (constOF natO) (laterOF idOF)))
```

which effectively defines the desired example functor
`F := λ (B,B⁻), gmap K (agree (nat * later B))`.

To make it a little bit more convenient to write down such functors, we make
the constant functors (`constOF`, `constRF`, and `constURF`) a coercion, and
provide the usual notation for products, etc. So the above functor can be
written as follows:

```coq
F := gmapRF K (agreeRF (natO * ▶ ∙))
```

Basically, the functor can be written "as if" you were writing a resource
algebra, except that there need to be extra "F" suffixes to indicate that we are
working with functors, and the desired recursive `iProp` is replaced by the
"hole" `∙`.

Putting it all together, the `libG` typeclass and `libΣ` list of functors for
your example would look as follows:

```coq
Class libG Σ := { lib_inG : inG Σ (gmapR K (agreeR (prodO natO (laterO (iPropO Σ))))) }.
Local Existing Instance lib_inG.

Definition libΣ : gFunctors := #[GFunctor (gmapRF K (agreeRF (natO * ▶ ∙)))].
Instance subG_libΣ {Σ} : subG libΣ Σ → libG Σ.
Proof. solve_inG. Qed.
```

It is instructive to remove the `▶` and see what happens: the `libG` class still
works just fine, but `libΣ` complains that the functor is not contractive. This
demonstrates the importance of always defining a `libΣ` alongside the `libG` and
proving their relation.
