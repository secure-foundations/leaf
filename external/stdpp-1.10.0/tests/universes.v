From stdpp Require Import gmap.

(** Make sure that [gmap] and [gset] do not bump the universe. Since [Z : Set],
the types [gmap Z Z] and [gset Z] should have universe [Set] too. *)

Check (gmap Z Z : Set).
Check (gset Z : Set).
