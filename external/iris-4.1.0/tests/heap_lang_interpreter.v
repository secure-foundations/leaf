From iris.heap_lang Require Import notation.
From iris.unstable.heap_lang Require Import interpreter.

Example test_1 :
  exec 1000 ((λ: "x", "x" + #1) #2) = inl #3.
Proof. reflexivity. Qed.

Check "ex1".
Eval vm_compute in
    exec 1000 (let: "x" := ref #() in
               let: "y" := ref #() in
               !"y").

Check "ex3".
(** eval order *)
Eval vm_compute in
    exec 1000 (let: "x" := ref #1 in
               let: "y" := ref #2 in
               ("y" <- !"x",
                (* this runs first, so the result is 2 *)
                "x" <- !"y");;
               !"x").

(* print a location *)
Check "ex4".
Eval vm_compute in
    exec 1000 (ref #();; ref #()).

Check "ex5".
Eval vm_compute in
    exec 1000 (let: "x" := ref #() in
               let: "y" := ref #() in
               "x" = "y").

(* a bad case where the interpreter runs a program which is actually stuck,
because this program guesses an allocation that happens to be correct in the
interpreter *)
Check "ex6".
Eval vm_compute in
    exec 1000 (let: "x" := ref #1 in
              #(LitLoc {|loc_car := 1|}) <- #2;;
              !"x").

(** * Failing executions *)

Check "fail app non-function".
Eval vm_compute in
    exec 1000 (#2 #4).

(* locations can only be compared with other locations *)
Check "fail loc order".
Eval vm_compute in
    exec 1000 (let: "x" := ref #() in
               let: "y" := #1 in
               "x" < "y").

Check "fail compare pairs".
Eval vm_compute in
    exec 1000 ((#0, #1) = (#0, #1)).

Check "fail free var".
Eval vm_compute in exec 100 "x".

Check "fail out of fuel".
(** infinite loop *)
Eval vm_compute in exec 100 (rec: "foo" <> := "foo" #()).
