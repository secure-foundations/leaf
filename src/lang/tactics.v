From stdpp Require Import fin_maps.
From lang Require Import lang.
From iris Require Import options.

(*|
This file implements some low-level tactics used to implement simp_lang.
`reshape_expr` is used to implement the proofmode support (especially tactics
like `wp_bind` and `wp_pure`) while `inv_head_step` is convenient automation for
proving typeclass instances that describe simp_lang's reduction rules.
|*)

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K] A fully-constructed item is inserted into [K] by calling
     [add_item]. *)
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => add_item (AppLCtx v) K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) K e2
    | HeapOp ?op ?e (Val ?v2) (Val ?v3)       => add_item (HeapOpLCtx op v2 v3) K e
    | HeapOp ?op ?e1 ?e2 (Val ?v)     => add_item (HeapOpMCtx op e1 v) K e2
    | HeapOp ?op ?e1 ?e2 ?e3          => add_item (HeapOpRCtx op e1 e2) K e3
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    end
  with add_item Ki K e := go (Ki :: K) e
  in go (@nil ectx_item) e.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb head_step.
Global Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : head_step.
Global Hint Extern 0 (head_step (HeapOp AllocOp _ _ _) _ _ _ _ _) => apply alloc_fresh : head_step.
