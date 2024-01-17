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

Install Coq 8.18.0, then run `make -j4`.

# Detailed instructions for evaluation

First, check that Coq accepts the Leaf source code, as detailed above.  Then, check that our source code supports the expected claims.

Lemmas in the Coq source that correspond to proof rules from the paper are annotated with a comment indicating the name used in the paper.

### Note about notation

 * The "guard operator" (the funny right arrow) looks like `P &&{E}&&> Q` in the Coq source.
 * Standard Iris Ghost state (the dashed box) is denoted by `own γ x`
 * Leaf ghost state (angle brackets) is denoted by `p_own γ x`
 * The function called `sto` in the paper is called `maps` in the Coq source.

Also note that the paper uses a notation `[X] {P} e {Q}`.
This notation is defined (Sec. 2.1) as `forall (G: iProp) . { P * G * (G guards X) } e { Q * G }`.
The bracket-notation doesn't exist in the Coq code, which always uses the expanded form instead.

### Leaf rules

 * Basic ghost state rules (Fig. 3)
   * `PCM-And`, found in `src/guarding/conjunct_own_rule.v`.
   * Remaining rules are standard and from the Iris library
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
   * HashTable ghost resources (Sec. 5, under the heading "Linear-Probing Hash Table Logic")
     * `src/examples/hash_table_logic.v`
   * HashTable implementation, specification, and proofs
     * `src/examples/hash_table.v`
 * HashTable client, adequacy theorem
   * `src/examples/main.v`
   
Note the following minor differences you can expect compared to the paper version:

 * RwLock
   * What the paper calls "Fields" is called `Central` in Coq.
   * What the paper calls "RwFamily" is called `rw_lock_inst` in Coq
 * HashTable
   * The paper version of the hash table is slightly simplified for presentation; the paper version aborts in some cases, whereas the Coq code either handles the case (for Query) or returns an optional value (for Update).  This slightly complicates the spec, proof, and the specification for Update.
   * Where the paper uses a big-asterisk to take a conjunct of many "slot" predicates,
     the Coq code uses a single element (usually called `r`) and a predicate
     called `full r k i j` that effectively says the element is equivalent to that
     conjunction for the range `[i, j)`.

Finally, note that (as is typical for Iris papers), the mask sets (`\mathcal{E}`)
and later modalities (triangles) are sometimes elided from the paper examples to avoid clutter.
However, they are necessarily included in the Coq code.

### Instantiating the adequacy theorem

We instantiate the Iris adequacy theorem on the hash table client.
This is done in the `main_returns_value` theorem of `src/examples/main.v`

The `main_returns_value` theorem _statement_ is a statement about program executions,
and this statement does not make any reference to the Iris logic or to any Leaf-specific concepts.
However, its _proof_ depends on the HashTable and the RwLock proofs, and thus also on most of the Leaf proof rules.  This confirms that our examples use the Leaf rules for their intended purpose.

Furthermore, the end of the `main.v` file executes `Print Assumptions main_returns_value.`. This confirms that no holes in its proof.

# Artifact contents

This artifact contains:

 * The Leaf Coq development
 * Its dependencies:
   * The Iris library (https://gitlab.mpi-sws.org/iris/iris)
   * The `stdpp` library (https://gitlab.mpi-sws.org/iris/stdpp)
   * Tactic library from CPDT
   * A modified version of the open-source "iris-simp-lang" (https://github.com/tchajed/iris-simp-lang)
 * Our supplementary appendix, appendix.pdf

### Source code overview

Structure of the artifact, by file. For information organized by structure of the paper, see the description above.

 * `external/` - Vendored dependencies (as outlined above)
 * `src/guarding/` - Primary Leaf rules and their proofs.
   * `auth_frag_util.v` - Misc. internal lemmas
   * `base_storage_opt.v` - Defines a common form for the "storage monoid"
   * `conjunct_own_rule.v` - Proof of `PCM-And`
   * `guard.v` - Most basic rules of the guard operator
   * `guard_later.v` - Proof of `Later-Pers-Guard`, with type classes to make it easier to use
   * `inved.v` - Internal detail for implementing storage protocols
   * `point_props.v` - Proofs relating to point props
   * `protocol.v` - Proofs and definitions relating to storage protocols
 * `src/lang/`
   * `adequacy.v` - The main adequacy theorem (theorem about program executions whose statement does not dependent on the Iris logic)
   * `class_instances.v` - Helper class instances for Iris Proof Mode
   * `heap_ra.v` - Where we define what the paper calls `\mathcal{H}`
   * `lang.v` - Language syntax and operational semantics
   * `notation.v` - Notation for writing programs as Coq values.
   * `primitive_laws.v` - Proof rules about heap operations.
   * `proofmode.v` - Setup for Iris Proof Mode
   * `simp.v` - Gathers up imports
   * `tactics.v` - More tactics for Iris Proof Mode
 * `src/examples/`
   * `counting.v` - Counting permissions (storage protocol)
   * `forever.v` - Forever (storage protocol)
   * `fractional.v` - Fractional permissions (storage protocol)
   * `gmap_option.v` - Some internal lemmas about gmaps
   * `hash_table.v` - Implementations, specifications, and proofs for the Hash Table example
   * `hash_table_logic.v` - Ghost resources for the hash table proofs
   * `hash_table_raw.v` - Lemmas about the hash table ghost resources
   * `main.v` - Top level "main" function that acts as a client to the hash table. Instantiates adequacy theorem.
   * `misc_tactics.v` - Internal tactics
   * `rwlock.v` - Implementations, specifications, and proofs for the RwLock example
   * `rwlock_logic.v` - Ghost resources for the RwLock proofs
   * `seqs.v` - Miscellaneous helper lemmas for handling cons-lists
 
