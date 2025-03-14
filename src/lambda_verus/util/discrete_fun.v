From iris.algebra Require Import cmra auth functions.

(* TODO : move all that to Iris *)

(** * Utility for [discrete_fun] *)

Notation ".<[ x := a ]>" := (discrete_fun_insert x a)
  (at level 5, format ".<[ x  :=  a ]>").
Notation ".{[ x := a ]}" := (discrete_fun_singleton x a)
  (at level 1, format ".{[ x  :=  a ]}").

Section ucmra.
Context `{!EqDecision A} {B: A → ucmra}.
Implicit Type (f g: discrete_fun B) (x y: A).

Lemma discrete_fun_insert_insert f x a b :
  .<[x:=a]> $ .<[x:=b]> f ≡ .<[x:=a]> f.
Proof.
  move=> y. rewrite /discrete_fun_insert. by case (decide (x = y))=> [?|?].
Qed.

Lemma discrete_fun_singleton_valid x (a: B _) : ✓ .{[x:=a]} ↔ ✓ a.
Proof.
  split.
  - move/(.$ x). by rewrite discrete_fun_lookup_singleton.
  - move=> ? y. rewrite /discrete_fun_singleton /discrete_fun_insert.
    case (decide (x = y))=> [?|?]; by [subst|apply ucmra_unit_valid].
Qed.

Lemma discrete_fun_insert_local_update f g x a b :
  (f x, g x) ~l~> (a, b) → (f, g) ~l~> (.<[x:=a]> f, .<[x:=b]> g).
Proof.
  move=> /local_update_unital Upd. rewrite local_update_unital => n h Val Eqv.
  destruct (Upd n (h x)) as [??]; [by apply Val|by apply Eqv|]. split.
  - move=> y. rewrite /discrete_fun_insert.
    case (decide (x = y))=> [?|?]; by [subst|].
  - move=> y. rewrite discrete_fun_lookup_op /discrete_fun_insert.
    case (decide (x = y))=> [?|?]; by [subst|apply Eqv].
Qed.

Lemma discrete_fun_singleton_local_update_any f x b a' b' :
  (f x, b) ~l~> (a', b') → (f, .{[x:=b]}) ~l~> (.<[x:=a']> f, .{[x:=b']}).
Proof.
  move=> ?.
  rewrite /discrete_fun_singleton -(discrete_fun_insert_insert _ _ b' b).
  apply discrete_fun_insert_local_update. by rewrite discrete_fun_lookup_insert.
Qed.
End ucmra.
