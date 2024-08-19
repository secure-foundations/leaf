(** Coq configuration for Iris (not meant to leak to clients).
If you are a user of Iris, note that importing this file means
you are implicitly opting-in to every new option we will add here
in the future. We are *not* guaranteeing any kind of stability here.
Instead our advice is for you to have your own options file; then
you can re-export the Iris file there but if we ever add an option
you disagree with you can easily overwrite it in one central location. *)
(* Everything here should be [Export Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)
From stdpp Require Export options.

#[export] Set Suggest Proof Using. (* also warns about forgotten [Proof.] *)

(* We always annotate hints with locality ([Global] or [Local]). This enforces
that at least global hints are annotated. *)
#[export] Set Warnings "+deprecated-hint-without-locality".

(* "Fake" import to whitelist this file for the check that ensures we import
this file everywhere.
From iris.prelude Require Import options.
*)
