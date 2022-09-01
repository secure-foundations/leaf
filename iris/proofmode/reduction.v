From iris.bi Require Import bi telescopes.
From iris.proofmode Require Import base environments.
From iris.prelude Require Import options.

(** Called by all tactics to perform computation to lookup items in the
    context.  We avoid reducing anything user-visible here to make sure we
    do not reduce e.g. before unification happens in [iApply].*)
Declare Reduction pm_eval := cbv [
  (* base *)
  base.negb base.beq
  base.Pos_succ base.ascii_beq base.string_beq base.positive_beq base.ident_beq
  (* environments *)
  env_lookup env_lookup_delete env_delete env_app env_replace
  env_dom env_intuitionistic env_spatial env_counter env_spatial_is_nil envs_dom
  envs_lookup envs_lookup_delete envs_delete envs_snoc envs_app
  envs_simple_replace envs_replace envs_split
  envs_clear_spatial envs_clear_intuitionistic envs_incr_counter
  envs_split_go envs_split
  env_to_prop_go env_to_prop env_to_prop_and_go env_to_prop_and
  (* PM list and option functions *)
  pm_app pm_option_bind pm_from_option pm_option_fun
].
Ltac pm_eval t :=
  eval pm_eval in t.
Ltac pm_reduce :=
  (* Use [change_no_check] instead of [change] to avoid performing the
  conversion check twice. *)
  match goal with |- ?u => let v := pm_eval u in change_no_check v end.
Ltac pm_reflexivity := pm_reduce; exact eq_refl.

(** Called by many tactics for redexes that are created by instantiation.
    This cannot create any envs redexes so we just do the cbn part. *)
Declare Reduction pm_prettify := cbn [
  (* telescope combinators *)
  tele_fold tele_bind tele_app
  (* BI connectives *)
  bi_persistently_if bi_affinely_if bi_absorbingly_if bi_intuitionistically_if
  bi_wandM bi_laterN
  bi_tforall bi_texist
].
Ltac pm_prettify :=
  (* Use [change_no_check] instead of [change] to avoid performing the
  conversion check twice. *)
  match goal with |- ?u => let v := eval pm_prettify in u in change_no_check v end.
