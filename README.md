# Intro

This contains the Coq development validating the core technical contributions of the paper _Leaf: Modularity for Temporary Sharing in Separation Logic_.
As documented in the paper (see the last paragraph of Sec. 7) it should contain:

 * Definitions of Leaf concepts and proofs of Leaf inference rules
 * Instantiation of Leaf for a simple heap-based language with atomic heap operations
 * Derivation of fractional permissions and counting permissions within Leaf
 * The reader-writer lock example
 * The hash table example

Note that this Coq development does _not_ include most of the supplementary content 
of the appendix.

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

First, check that Coq accepts the Leaf source code, as detailed above.  Then, check that our source code supports the expected claims.

Lemmas in the Coq source that correspond to proof rules from the paper are annotated with a comment indicating the name used in the paper.

### Note about notation

 * The "guard operator" (the funny right arrow) looks like `P &&{E}&&> Q` in the Coq source.
 * Standard Iris Ghost state (the dashed box) is denoted by `own γ x`
 * Leaf ghost state (angle brackets) is denoted by `p_own γ x`
 * The function called `sto` in the paper is called `maps` in the Coq source.

### Leaf rules

 * Basic ghost state rules (Fig. 3)
   * `PCM-And`, found in `src/guarding/conjunct_own_rule.v`.
   * Remaining rules are standard
 * Deduction rules for guard operator (Fig. 4)
   * `src/guarding/guard.v`
   * `src/guarding/point_props.v`
 * Storage protocol definitions (Fig. 5)
   * `src/guarding/protocol.v`
 * Rules related to later modality (Sec. 3.5)
   * `src/guarding/guard.v`
   * `src/guarding/guard_later.v`

### Application to programming language with atomic heap operations

 * Language syntax and operational semantics
    * `src/lang/lang.v`
 * Derived proof rules (Section 3.3)
    * `src/lang/primitive_laws.v`

### Example storage protocols

 * Fractional (Example 3.2)
   * `src/examples/fractional.v`
 * Forever (Example 3.4)
   * `src/examples/forever.v`
 * Counting
   * `src/examples/counting.v`

### Example programs

 * RwLock (Section 4)
   * RwLock storage protocol and ghost resources (Fig. 8)
     * `src/examples/rwlock_logic.v`
   * RwLock implementation, specification (Fig. 1), and proofs
     * `src/examples/rwlock.v`
 * HashTable (Section 5)
   * HashTable ghost resources (Sec. 5, under the heading "Linear-Probing Hash Table Logic"")
     * `src/examples/hash_table_logic.v`
   * HashTable implementation, specification, and proofs
     * `src/examples/hash_table.v`
 * HashTable client, adequacy theorem
   * `src/examples/main.v`

# Artifact contents

This artifact contains:

 * The Leaf Coq development
   * Its main dependency, the Iris library, which is open source (https://gitlab.mpi-sws.org/iris/iris)
   * A modified version of the open-source "iris-simp-lang" (https://github.com/tchajed/iris-simp-lang)
 * Our technical appendix, appendix.pdf
