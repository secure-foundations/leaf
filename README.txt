This contains:

 * The Leaf Coq development
   * Its main dependency, the Iris library, which is open source (https://gitlab.mpi-sws.org/iris/iris)
   * A modified version of the open-source "iris-simp-lang" (https://github.com/tchajed/iris-simp-lang)
 * Our technical appendix, appendix.pdf

To verify all the proofs, just run `make`. This has been tested on Coq 8.13.2.

The main directories of interest:

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
