From stdpp Require Import tactics telescopes.

Local Unset Mangle Names. (* for stable goal printing *)

Section accessor.
(* This is like Iris' accessors, but in Prop.  Just to play with telescopes. *)
Definition accessor {X : tele} (α β γ : X → Prop) : Prop :=
  ∃.. x, α x ∧ (β x → γ x).

(* Working with abstract telescopes. *)
Section tests.
Context {X : tele}.
Implicit Types α β γ : X → Prop.

Lemma acc_mono α β γ1 γ2 :
  (∀.. x, γ1 x → γ2 x) →
  accessor α β γ1 → accessor α β γ2.
Proof.
  unfold accessor. rewrite tforall_forall, !texist_exist.
  intros Hγ12 Hacc. destruct Hacc as [x' [Hα Hclose]]. exists x'.
  split; [done|]. intros Hβ. apply Hγ12, Hclose. done.
Qed.

Lemma acc_mono_disj α β γ1 γ2 :
  accessor α β γ1 → accessor α β (λ.. x, γ1 x ∨ γ2 x).
Proof.
  Show.
  apply acc_mono. Show.
  rewrite tforall_forall. intros x Hγ. rewrite tele_app_bind. Show.
  left. done.
Qed.
End tests.
End accessor.
