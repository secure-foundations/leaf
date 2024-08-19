From stdpp Require Import tactics option.

(** Make sure that [done] is not called recursively when solving [is_Some],
which might leave an unresolved evar before performing ex falso. *)
Goal False → is_Some (@None nat).
Proof. done. Qed.
Goal ∀ mx, mx = Some 10 → is_Some mx.
Proof. done. Qed.
Goal ∀ mx, Some 10 = mx → is_Some mx.
Proof. done. Qed.
