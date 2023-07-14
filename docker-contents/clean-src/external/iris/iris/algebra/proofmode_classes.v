From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

(* There are various versions of [IsOp] with different modes:

- [IsOp a b1 b2]: this one has no mode, it can be used regardless of whether
  any of the arguments is an evar. This class has only one direct instance:
  [IsOp (a ⋅ b) a b].
- [IsOp' a b1 b2]: requires either [a] to start with a constructor, OR [b1] and
  [b2] to start with a constructor. All usual instances should be of this
  class to avoid loops.
- [IsOp'LR a b1 b2]: requires either [a] to start with a constructor. This one
  has just one instance: [IsOp'LR (a ⋅ b) a b] with a very low precendence.
  This is important so that when performing, for example, an [iDestruct] on
  [own γ (q1 + q2)] where [q1] and [q2] are fractions, we actually get
  [own γ q1] and [own γ q2] instead of [own γ ((q1 + q2)/2)] twice.
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
