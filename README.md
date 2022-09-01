# IRIS COQ DEVELOPMENT [[coqdoc]](https://plv.mpi-sws.org/coqdoc/iris/)

This is the Coq development of the [Iris Project](http://iris-project.org),
which includes [MoSeL](http://iris-project.org/mosel/), a general proof mode
for carrying out separation logic proofs in Coq.

For using the Coq library, check out the
[API documentation](https://plv.mpi-sws.org/coqdoc/iris/).

For understanding the theory of Iris, a LaTeX version of the core logic
definitions and some derived forms is available in
[tex/iris.tex](tex/iris.tex).  A compiled PDF version of this document is
[available online](http://plv.mpi-sws.org/iris/appendix-3.4.pdf).

## Side-effects

Importing Iris has some side effects as the library sets some global options.

* First of all, Iris imports std++, so the
  [std++ side-effects](https://gitlab.mpi-sws.org/iris/stdpp/#side-effects)
  apply.
* On top of that, Iris imports ssreflect, which replaces the default `rewrite`
  tactic with the ssreflect version. However, `done` is overwritten to keep
  using the std++ version of the tactic.  We also set `SsrOldRewriteGoalsOrder`
  and re-open `general_if_scope` to un-do some effects of ssreflect.

## Building Iris

### Prerequisites

This version is known to compile with:

 - Coq 8.12.2 / 8.13.2
 - A development version of [std++](https://gitlab.mpi-sws.org/iris/stdpp)

If you need to work with Coq 8.9 or Coq 8.10, you can use the
[iris-3.3 branch](https://gitlab.mpi-sws.org/iris/iris/tree/iris-3.3).
For a version compatible with Coq 8.11, check out the
[iris-3.4 branch](https://gitlab.mpi-sws.org/iris/iris/tree/iris-3.4).

### Working *with* Iris

To use Iris in your own proofs, we recommend you install Iris via opam (2.0.0 or
newer).  To obtain the latest stable release, you have to add the Coq opam
repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

To obtain a development version, also add the Iris opam repository:

    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Either way, you can now install Iris:
- `opam install coq-iris` will install the libraries making up the Iris logic,
  but leave it up to you to instantiate the `program_logic.language` interface
  to define a programming language for Iris to reason about.
- `opam install coq-iris-heap-lang` will additionally install HeapLang, the
  default language used by various Iris projects.

To fetch updates later, run `opam update && opam upgrade`.

#### Be notified of breaking changes

We do not guarantee backwards-compatibility, so upgrading Iris may break your
Iris-using developments.  If you want to be notified of breaking changes, please
let us know your account name on the
[MPI-SWS GitLab](https://gitlab.mpi-sws.org/) so we can add you to the
notification group.  Note that this excludes the "staging" and "deprecated"
packages (see below).

#### Use of Iris in submitted artifacts

If you are using Iris as part of an artifact submitted for publication with a
paper, we recommend you make the artifact self-contained so that it can be built
in the future without relying in any other server to still exist. However, if
that is for some reason not possible, and if you are using opam to obtain the
right version of Iris and you used a `dev.*` version, please let us know which
exact Iris version you artifact relies on so that we can
[add it to this wiki page](https://gitlab.mpi-sws.org/iris/iris/-/wikis/Pinned-Iris-package-versions)
and avoid removing it from our opam repository in the future.

### Working *on* Iris

See the [contribution guide](CONTRIBUTING.md) for information on how to work on
the Iris development itself.

## Directory Structure

Iris is structured into multiple *packages*, some of which contain multiple
modules in separate folders.

* The [iris](iris) package contains the language-independent parts of Iris.
  + The folder [prelude](iris/prelude) contains modules imported everywhere in
    Iris.
  + The folder [algebra](iris/algebra) contains the COFE and CMRA
    constructions as well as the solver for recursive domain equations.
    - The subfolder [lib](iris/algebra/lib) contains some general derived RA
      constructions.
  + The folder [bi](iris/bi) contains the BI++ laws, as well as derived
    connectives, laws and constructions that are applicable for general BIs.
    - The subfolder [lib](iris/bi/lib) contains some general derived logical
      constructions.
  + The folder [proofmode](iris/proofmode) contains
    [MoSeL](http://iris-project.org/mosel/), which extends Coq with contexts for
    intuitionistic and spatial BI++ assertions. It also contains tactics for
    interactive proofs. Documentation can be found in
    [proof_mode.md](docs/proof_mode.md).
  + The folder [base_logic](iris/base_logic) defines the Iris base logic and
    the primitive connectives.  It also contains derived constructions that are
    entirely independent of the choice of resources.
    - The subfolder [lib](iris/base_logic/lib) contains some generally useful
      derived constructions.  Most importantly, it defines composable
      dynamic resources and ownership of them; the other constructions depend
      on this setup.
  + The folder [program_logic](iris/program_logic) specializes the base logic
    to build Iris, the program logic.   This includes weakest preconditions that
    are defined for any language satisfying some generic axioms, and some derived
    constructions that work for any such language.
  + The folder [si_logic](iris/si_logic) defines a "plain" step-indexed logic
    and shows that it is an instance of the BI interface.
* The [iris_heap_lang](iris_heap_lang) package defines the ML-like concurrent
  language HeapLang and provides tactic support and proof mode integration.
  + The subfolder [lib](iris_heap_lang/lib) contains a few derived
    constructions within this language, e.g., parallel composition.
    For more examples of using Iris and heap_lang, have a look at the
    [Iris Examples](https://gitlab.mpi-sws.org/iris/examples).
* The [iris_staging](iris_staging) package contains libraries that are not yet
  ready for inclusion in Iris proper. For each library, there is a corresponding
  "tracking issue" in the Iris issue tracker (also linked from the library
  itself) which tracks the work that still needs to be done before moving the
  library to Iris. No stability guarantees whatsoever are made for this package.
* The [iris_deprecated](iris_deprecated) package contains libraries that have been
  removed from Iris proper, but are kept around to give users some more time to
  switch to their intended replacements. The individual libraries come with comments
  explaining the deprecation and making recommendations for what to use
  instead. No stability guarantees whatsoever are made for this package.
* The folder [tests](tests) contains modules we use to test our
  infrastructure. These modules are not installed by `make install`, and should
  not be imported.

## Case Studies

The following is a (probably incomplete) list of case studies that use Iris, and
that should be compatible with this version:

* [Iris Examples](https://gitlab.mpi-sws.org/iris/examples) is where we
  collect miscellaneous case studies that do not have their own repository.
* [LambdaRust](https://gitlab.mpi-sws.org/iris/lambda-rust) is a Coq
  formalization of the core Rust type system.
* [GPFSL](https://gitlab.mpi-sws.org/iris/gpfsl) is a logic for release-acquire
  and relaxed memory.
* [Iron](https://gitlab.mpi-sws.org/iris/iron) is a linear separation logic
  built on top of Iris for precise reasoning about resources (such as making
  sure there are no memory leaks).
* [Actris](https://gitlab.mpi-sws.org/iris/actris) is a separation logic
  built on top of Iris for session-type based reasoning of message-passing
  programs.

## Further Resources

Getting along with Iris in Coq:

* Iris proof patterns and conventions are documented in the
  [proof guide](docs/proof_guide.md).
* Various notions of equality and logical entailment in Iris and their Coq
  interface are described in the
  [equality docs](docs/equalities_and_entailments.md).
* The Iris tactics are described in the
  [the Iris Proof Mode (IPM) / MoSeL documentation](docs/proof_mode.md) as well as the
  [HeapLang documentation](docs/heap_lang.md).
* The generated coqdoc is [available online](https://plv.mpi-sws.org/coqdoc/iris/).

Contacting the developers:

* Discussion about the Iris Coq development happens on the mailing list
  [iris-club@lists.mpi-sws.org](https://lists.mpi-sws.org/listinfo/iris-club)
  and in the [Iris Chat](https://iris-project.org/chat.html).  This is also the
  right place to ask questions.
* If you want to report a bug, please use the
  [issue tracker](https://gitlab.mpi-sws.org/iris/iris/issues), which requires
  an MPI-SWS GitLab account. The [chat page](https://iris-project.org/chat.html)
  describes how to create such an account.
* To contribute to Iris itself, see the [contribution guide](CONTRIBUTING.md).

Miscellaneous:

* Information on how to set up your editor for unicode input and output is
  collected in [editor.md](docs/editor.md).
* If you are writing a paper that uses Iris in one way or another, you could use
  the [Iris LaTeX macros](tex/iris.sty) for typesetting the various Iris
  connectives.
