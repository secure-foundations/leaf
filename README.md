# Intro

This contains the Coq development validating the core technical contributions of the paper _Leaf: Modularity for Temporary Sharing in Separation Logic_.
As documented in the paper (see the last paragraph of Sec. 7) it should contain:

 * Definitions of Leaf concepts and proofs of Leaf inference rules
 * Instantiation of Leaf for a simple heap-based language with atomic heap operations
 * Derivation of fractional permissions and counting permissions within Leaf
 * The reader-writer lock example
 * The hash table example

Note that this Coq development does **not** include most of the content of the supplementary
appendix. In particular it does not include:

 * Instantiation of Leaf for a language with non-atomic memory
 * The more advanced (multiple counter) reader-writer lock example
 * Counterexamples for potential Leaf rules that turned out to be unsound

# Getting Started

Confirm that Coq accepts all of the source files. If successful, Coq will output
`Closed under the global context` after checking the last file, `src/examples/main.v`.
This should take about 10-20 minutes.

### With Docker

Install Docker, then build the container:

```
docker build -t leaf .
```

Run the following command to get an interactive shell:
```
docker run -it leaf /bin/bash
```

Within the shell, run:

```
make -j4
```

(You need to use the shell in order to get the right Coq environment)

### Manually

Install Coq 8.13.2, then run `make -j4`.

# Detailed instructions for evaluation

# Artifact contents

This contains:

 * The Leaf Coq development
   * Its main dependency, the Iris library, which is open source (https://gitlab.mpi-sws.org/iris/iris)
   * A modified version of the open-source "iris-simp-lang" (https://github.com/tchajed/iris-simp-lang)
 * Our technical appendix, appendix.pdf

### Source guide

  * src/guarding/

      Contains the definition of the guarding operator, storage protocols, and
      proofs of all the rules from the paper.

      A lot of the notation is different, but each rule is labelled with a comment
      giving its name in the paper.

      The guarding operator is denoted by `P &&{ E }&&> Q`.
      Protocol ghost state is given by `p_own`
      The `sto` function is here called `maps`.

      guard.v contains the definition of guarding and most of the rules
      protocol.v contains most of the other rules.

  * src/lang/

      Definition of a simple heap-based programming language
      with an instantiation of the Iris program logic.

      lang.v contains the language syntax
      primitive_laws.v contains the heap proof rules (e.g., Heap-Read-Shared)

  * src/examples/

      + Fractional
      + Counting
      + Forever
      + RwLock
      + HashTable
      + main.v contains a function that calls a few hash table functions
        and applies the Iris adequacy theorem.
