From iris.base_logic.lib Require Import gen_inv_heap invariants.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Import lang adequacy proofmode notation.
(* Import lang *again*. This used to break notation. *)
From iris.heap_lang Require Import lang.
From iris.prelude Require Import options.

Unset Mangle Names.

Section printing_tests.
  Context `{!heapGS Σ}.

  Lemma ref_print :
    True -∗ WP let: "f" := (λ: "x", "x") in ref ("f" #10) {{ _, True }}.
  Proof.
    iIntros "_". Show.
  Abort.

  (* These terms aren't even closed, but that's not what this is about.  The
  length of the variable names etc. has been carefully chosen to trigger
  particular behavior of the Coq pretty printer. *)

  Lemma wp_print_long_expr (fun1 fun2 fun3 : expr) :
    True -∗ WP let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"  {{ _, True }}.
  Proof.
    iIntros "_". Show.
    wp_bind (fun1 #()). Show.
  Abort.

  Lemma wp_print_long_expr (fun1 fun2 fun3 : expr) long_post :
    True -∗ WP let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "v" := fun3 "v" in
       if: "v" = "v" then "v" else "v"
    {{ _, long_post ∗ long_post ∗ long_post ∗ long_post ∗ long_post ∗ long_post ∗ long_post }}.
  Proof.
    iIntros "_". Show.
    wp_bind (fun1 #()). Show.
  Abort.

  Lemma wp_print_long_expr (l1 : loc) (fun2 fun3 : expr) long_post N E_long :
    ↑N ⊆ E_long →
    inv N True -∗ WP let: "val1" := ! #l1 in
       let: "val2" := fun2 "val1" in
       let: "v" := fun3 "v" in
       if: "v" = "v" then "v" else "v"
    @ E_long
    {{ _, long_post ∗ long_post ∗ long_post ∗ long_post ∗ long_post ∗ long_post ∗ long_post }}.
  Proof.
    iIntros (?) "Hinv". Show.
    wp_bind (! #l1)%E. Show.
    iInv "Hinv" as "_". Show.
  Abort.

  Lemma texan_triple_long_expr (fun1 fun2 fun3 : expr) :
    {{{ True }}}
       let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"
    {{{ (x y : val) (z : Z), RET (x, y, #z); True }}}.
  Proof. Show. Abort.

  Lemma texan_triple_long_expr_mask (fun1 fun2 fun3 : expr) E_mask_is_long_too :
    {{{ True }}}
       let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"
    @ E_mask_is_long_too
    {{{ (x y : val) (z : Z), RET (x, y, #z); True }}}.
  Proof. Show. Abort.

  Lemma texan_triple_long_expr_mask_post (fun1 fun2 fun3 : expr) long_post E_mask_is_long_too :
    {{{ True }}}
       let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"
    @ E_mask_is_long_too
    {{{ (x y : val) (z : Z), RET (x, y, #z); long_post ∗ long_post ∗ long_post ∗ long_post ∗ long_post }}}.
  Proof. Show. Abort.

End printing_tests.
