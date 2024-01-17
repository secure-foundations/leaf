From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

(* The [IsOp a b1 b2] class is used in two directions: to "split" input [a] into
outputs [b1] and [b2], and to "merge" inputs [b1] and [b2] into output [a],
where in both cases we have [a ≡ b1 ⋅ b2].

Since the [IsOp a b1 b2] class is used in two directions, there are some
subtleties we need to account for:

- If we want to "merge", we want the "op" instance to be used *last*. That is,
  before using [IsOp (b1 ⋅ b2) b1 b2], we want to traverse the structure of the
  term to merge constructors, and we want it to combine terms like [q/2] and
  [q/2] into [q] instead of [q/2 ⋅ q/2].
- If we want to "split", we want the "op" instance to be used *first*. That is,
  we want to use [IsOp (b1 ⋅ b2) b1 b2] eagerly, so that for instance, a term
  like [q1 ⋅ q2] is turned into [q1] and [q2] and not two times [(q1 ⋅ q2) / 2].

To achieve this, there are various classes with different modes:

- [IsOp a b1 b2]. This class has no mode, so it can be used even to
  combine/merge evars. This class has only one direct instance
  [IsOp (a ⋅ b) a b] with cost 100 (so it is used last), ensuring that the
  "op" rule is used last when merging.
- [IsOp' a b1 b2]. This class requires either [a] OR both [b1] and [b2] to be inputs.
  All usual instances should be of this class to avoid loops.
- [IsOp'LR a b1 b2]. This class requires [a] to be an input and has just one
  instance [IsOp'LR (a ⋅ b) a b] with cost 0. This ensures that the "op"
  rule is used first when splitting.
*)
Class IsOp {A : cmra} (a b1 b2 : A) := is_op : a ≡ b1 ⋅ b2.
Global Arguments is_op {_} _ _ _ {_}.
Global Hint Mode IsOp + - - - : typeclass_instances.

Global Instance is_op_op {A : cmra} (a b : A) : IsOp (a ⋅ b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : cmra} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Global Hint Mode IsOp' + ! - - : typeclass_instances.
Global Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : cmra} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Global Existing Instance is_op_lr | 0.
Global Hint Mode IsOp'LR + ! - - : typeclass_instances.
Global Instance is_op_lr_op {A : cmra} (a b : A) : IsOp'LR (a ⋅ b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

(* FromOp *)
(* TODO: Worst case there could be a lot of backtracking on these instances,
try to refactor. *)
Global Instance is_op_pair {A B : cmra} (a b1 b2 : A) (a' b1' b2' : B) :
  IsOp a b1 b2 → IsOp a' b1' b2' → IsOp' (a,a') (b1,b1') (b2,b2').
Proof. by constructor. Qed.
Global Instance is_op_pair_core_id_l {A B : cmra} (a : A) (a' b1' b2' : B) :
  CoreId a → IsOp a' b1' b2' → IsOp' (a,a') (a,b1') (a,b2').
Proof. constructor=> //=. by rewrite -core_id_dup. Qed.
Global Instance is_op_pair_core_id_r {A B : cmra} (a b1 b2 : A) (a' : B) :
  CoreId a' → IsOp a b1 b2 → IsOp' (a,a') (b1,a') (b2,a').
Proof. constructor=> //=. by rewrite -core_id_dup. Qed.

Global Instance is_op_Some {A : cmra} (a : A) b1 b2 :
  IsOp a b1 b2 → IsOp' (Some a) (Some b1) (Some b2).
Proof. by constructor. Qed.
