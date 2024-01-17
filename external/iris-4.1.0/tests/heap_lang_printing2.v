(* Test another way of importing heap_lang modules that used to break printing *)
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Export primitive_laws notation.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Unset Mangle Names.

Section printing_tests.
  Context `{!heapGS Σ}.

  Lemma vs_print (P Q : iProp Σ) :
    P ={⊤}=∗ Q.
  Proof. Show. Abort.

  Lemma wp_print_long_expr (fun1 fun2 fun3 : expr) :
    True -∗ WP let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"  {{ _, True }}.
  Proof.
    iIntros "_". Show.
  Abort.

  Lemma texan_triple_long_expr (fun1 fun2 fun3 : expr) :
    {{{ True }}}
       let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"
    {{{ (x y : val) (z : Z), RET (x, y, #z); True }}}.
  Proof. Show. Abort.

End printing_tests.
