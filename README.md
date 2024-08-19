# Leaf

Leaf is an experimental new [Iris](https://iris-project.org/)
separation logic library that targets reasoning about
"temporarily shared state" and especially "temporarily shared, _read-only_ state."
The goal is to find the "right core logic" for temporarily shared state. In Leaf,
our logic is centered around an operator called _guards_, which indicates that
one proposition is the "read-only" version of another proposition.
For example, the relationship between a fractional proposition and the "unique, whole"
version of that proposition can be expressed as a _guard_:

![Graphic illustrating "G guards P" and a specific example, "l points to v with fraction 1/2" guards "l points to v"](/guide/guards-graphic.png)

Leaf supports paradigms such as fractional permissions and counting permissions.
Crucially, Leaf does not require the chosen permission system to be "built in" to
the resources of interest. For example, given any proposition _P_, Leaf lets us construct
a "fractional version" of _P_ after the fact.
This is in direct contrast to current idioms, where, for example, points-to propositions
`l ↦ v` are almost always explicitly constructed out of fractional resources.
In Leaf, you can use fractional points-to propositions without needing to build them in from the get-go.
This empowers us to design novel permission systems because we are never "locked in" to a single one.

A core goal of Leaf is that specifications and proofs operating over shared resources
should do so agnostically to the "sharing mechanism".
Instead of saying "I take a fractional _P_", an interface should instead say
"I take some _G_ such that _G_ guards _P_".

In a pedantic sense, Leaf can do anything fractional permissions can do — but a
more interesting question is if anything expressible thorugh fractional permissions
can be expressed in this mechanism-agnostic way. My experience so far suggests "mostly, yes".

Here are some things Leaf can do or is good at:

 * Support the sharing of _memory resources_ (like the points-to assertions).
 * Support the sharing of _ghost resources_ (like `own γ x`).
 * Support resources that alternate between states of "unique, writeable access"
    and "shared, read-only access". A prototypical example is a reader-writer lock.
 * Support resources that are permanently read-only.
 * Support "cancellable invariants"
 * Support a variation on the "fractional borrows" and "lifetime tokens" of RustBelt's lifetime logic.

## Latest updates

We originally introduced Leaf in the paper
_Leaf: Modularity for Temporary Sharing in Separation Logic_ ([OOPSLA paper](https://dl.acm.org/doi/10.1145/3622798))
([extended version](https://arxiv.org/abs/2309.04851)).
If you are looking for the paper's artifact you can find it [here](https://zenodo.org/records/8327489)
or on the [oopsla2023-artifact](https://github.com/secure-foundations/leaf/tree/oopsla2023-artifact) branch.
However, since the paper and artifact were published, we have made a number of simplifications and extensions,
so I would not recommend trying to build on the artifact.

The Leaf paper centers around a framework called the "storage protocol", which is positioned as a key pillar
of Leaf required to do anything "nontrivial". However, storage protocols are somewhat complicated.
Fortunately, the latest version of Leaf has a simpler core logic, with storage protocols proved correct from those
core logic rules.
In many cases, it may be easier to use the core logic directly rather than implementing a storage protocol.
This also makes it easier to implement more advanced constructions on top of Leaf.

## Work that builds on Leaf

Leaf's storage protocols have been encoded into IronSync, a Dafny-based verification library for concurrent
code, and Verus, a verification tool for Rust.
We have used Leaf to prove that this encoding is sound, even in conjunction with many other important features
of Rust/Verus, via a "logical type soundness" approach.

IronSync and Verus are both tools that make heavy use of SMT verification;
Verus also has developer utilities for specifying and automating the construction of storage protocols.
Using this technology, we have shown that storage protocols are useful for:

 * Verifying complicated implementations of _reader-writer locks_.
 * Verifying a NUMA-optimized concurrent queue.
 * Verifying reference-counted pointers, like Rust's [Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html) or [Rc](https://doc.rust-lang.org/std/rc/struct.Rc.html).
 * Verifying a concurrent memory allocator.

# Getting started

Leaf works with Iris 4.2.0 and is tested with Coq 8.19.1.
See [the Iris docs](https://gitlab.mpi-sws.org/iris/iris/) for more information about installing Iris.

Make sure you have the right versions:

```
opam pin coq 8.19.1
opam pin coq-iris 4.2.0
```

## Documentation and further reading

 * If you're going to be using Leaf, most logic rules you need are in `src/guarding/guard.v`.  You should also check out `tactics.md`.
 * The [paper and appendix](https://arxiv.org/pdf/2309.04851) provides motivation and technical notes.
 * Our [OOPSLA talk](https://www.youtube.com/watch?v=ZvwW16KT9yo) is also online.
 * The [paper artifact](https://github.com/secure-foundations/leaf/tree/oopsla2023-artifact) has some more information about the structure of the source code,
      though it applies to an old version.
 * [Travis's PhD thesis](https://tjhance.github.io/travis_hance_thesis.pdf) explains how storage protocols are adapted to Verus and how Leaf is used to prove the encoding sound.

## Source code

 * `src/guarding/` has the core leaf rules.
    * `guard.v` - most rules
    * `protocol.v` - storage protocol definition matching the paper
    * `protocol_relational.v` - slightly stronger definition
 * `src/examples/` examples
    * lifetime logic
    * fractional permissions
    * counting permissions
    * ad hoc "RwLock" permissions

Leaf is a resource logic, thus not specific to a particular program logic,
but this codebase ships with a program logic for a language based on
[iris-simp-lang](https://github.com/tchajed/iris-simp-lang).
