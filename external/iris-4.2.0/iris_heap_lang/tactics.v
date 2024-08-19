From stdpp Require Import fin_maps.
From iris.heap_lang Require Export lang.
From iris.prelude Require Import options.
Import heap_lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K], and a list of pairs of values [vs] (prophecy identifier and
     resolution value) that is only non-empty if a [ResolveLCtx] item (maybe
     having several levels) is in the process of being constructed. Note that
     a fully-constructed item is inserted into [K] by calling [add_item], and
     that is only the case when a non-[ResolveLCtx] item is built. When [vs]
     is non-empty, [add_item] also wraps the item under several [ResolveLCtx]
     constructors: one for each pair in [vs]. *)
  let rec go K vs e :=
    match e with
    | _                               => lazymatch vs with [] => tac K e | _ => fail end
    | App ?e (Val ?v)                 => add_item (AppLCtx v) vs K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) vs K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) vs K e
    | BinOp ?op ?e (Val ?v)           => add_item (BinOpLCtx op v) vs K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpRCtx op e1) vs K e2
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) vs K e0
    | Pair ?e (Val ?v)                => add_item (PairLCtx v) vs K e
    | Pair ?e1 ?e2                    => add_item (PairRCtx e1) vs K e2
    | Fst ?e                          => add_item FstCtx vs K e
    | Snd ?e                          => add_item SndCtx vs K e
    | InjL ?e                         => add_item InjLCtx vs K e
    | InjR ?e                         => add_item InjRCtx vs K e
    | Case ?e0 ?e1 ?e2                => add_item (CaseCtx e1 e2) vs K e0
    | AllocN ?e (Val ?v)              => add_item (AllocNLCtx v) vs K e
    | AllocN ?e1 ?e2                  => add_item (AllocNRCtx e1) vs K e2
    | Free ?e                         => add_item FreeCtx vs K e
    | Load ?e                         => add_item LoadCtx vs K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) vs K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) vs K e2
    | Xchg ?e (Val ?v)                => add_item (XchgLCtx v) vs K e
    | Xchg ?e1 ?e2                    => add_item (XchgRCtx e1) vs K e2
    | CmpXchg ?e0 (Val ?v1) (Val ?v2) => add_item (CmpXchgLCtx v1 v2) vs K e0
    | CmpXchg ?e0 ?e1 (Val ?v2)       => add_item (CmpXchgMCtx e0 v2) vs K e1
    | CmpXchg ?e0 ?e1 ?e2             => add_item (CmpXchgRCtx e0 e1) vs K e2
    | FAA ?e (Val ?v)                 => add_item (FaaLCtx v) vs K e
    | FAA ?e1 ?e2                     => add_item (FaaRCtx e1) vs K e2
    | Resolve ?ex (Val ?v1) (Val ?v2) => go K ((v1,v2) :: vs) ex
    | Resolve ?ex ?e1 (Val ?v2)       => add_item (ResolveMCtx ex v2) vs K e1
    | Resolve ?ex ?e1 ?e2             => add_item (ResolveRCtx ex e1) vs K e2
    end
  with add_item Ki vs K e :=
    lazymatch vs with
    | []               => go (Ki :: K) (@nil (val * val)) e
    | (?v1,?v2) :: ?vs => add_item (ResolveLCtx Ki v1 v2) vs K e
    end
  in
  go (@nil ectx_item) (@nil (val * val)) e.

(** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_base_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : base_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb base_step.
Global Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : base_step.
Global Hint Extern 0 (base_reducible_no_obs _ _) => eexists _, _, _; simpl : base_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (base_step _ _ _ _ _ _) => econstructor : base_step.
Global Hint Extern 0 (base_step (CmpXchg _ _ _) _ _ _ _ _) => eapply CmpXchgS : base_step.
Global Hint Extern 0 (base_step (AllocN _ _) _ _ _ _ _) => apply alloc_fresh : base_step.
Global Hint Extern 0 (base_step NewProph _ _ _ _ _) => apply new_proph_id_fresh : base_step.
