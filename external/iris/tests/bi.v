From iris.bi Require Import bi plainly.

(** See https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/610 *)
Lemma test_impl_persistent_1 `{!BiPlainly PROP} :
  Persistent (PROP:=PROP) (True → True).
Proof. apply _. Qed.
Lemma test_impl_persistent_2 `{!BiPlainly PROP} :
  Persistent (PROP:=PROP) (True → True → True).
Proof. apply _. Qed.

(* Test that the right scopes are used. *)
Lemma test_bi_scope {PROP : bi} : True.
Proof.
  (* [<affine> True] is implicitly in %I scope. *)
  pose proof (bi.wand_iff_refl (PROP:=PROP) (<affine> True)).
Abort.
