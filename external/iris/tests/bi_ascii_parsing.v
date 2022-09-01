Require Import Coq.Strings.String.
Require Import iris.bi.bi.
Require Import iris.bi.ascii.

Local Open Scope string_scope.

(* this file demonstrates that the [|-] notation does not
   conflict with the ltac notation.
 *)
Section with_bi.
  Context {PROP : bi}.
  Variables P Q R : PROP.

  Local Open Scope stdpp_scope.

  Ltac pg :=
    match goal with
    | |- ?X => idtac X
    end.

  Ltac foo g :=
    lazymatch g with
    | |- ?T => idtac T
    | ?U |- ?T => idtac U T
    end.

  Ltac bar :=
    match goal with
    | |- ?G => foo G
    end.

  Check "test1".
  Lemma test1 : |-@{PROP} True.
  Proof. bar. pg. Abort.

  Check "test2".
  Lemma test2 : False |-@{PROP} True.
  Proof. bar. pg. Abort.
End with_bi.
