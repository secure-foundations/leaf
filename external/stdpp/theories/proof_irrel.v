(** This file collects facts on proof irrelevant types/propositions. *)
From stdpp Require Export base.
From stdpp Require Import options.

Global Hint Extern 200 (ProofIrrel _) => progress (lazy beta) : typeclass_instances.

Global Instance True_pi: ProofIrrel True.
Proof. intros [] []; reflexivity. Qed.
Global Instance False_pi: ProofIrrel False.
Proof. intros []. Qed.
Global Instance unit_pi: ProofIrrel ().
Proof. intros [] []; reflexivity. Qed.
Global Instance and_pi (A B : Prop) :
  ProofIrrel A → ProofIrrel B → ProofIrrel (A ∧ B).
Proof. intros ?? [??] [??]. f_equal; trivial. Qed.
Global Instance prod_pi (A B : Type) :
  ProofIrrel A → ProofIrrel B → ProofIrrel (A * B).
Proof. intros ?? [??] [??]. f_equal; trivial. Qed.
Global Instance eq_pi {A} (x : A) `{∀ z, Decision (x = z)} (y : A) :
  ProofIrrel (x = y).
Proof.
  set (f z (H : x = z) :=
    match decide (x = z) return x = z with
    | left H => H | right H' => False_rect _ (H' H)
    end).
  assert (∀ z (H : x = z),
    eq_trans (eq_sym (f x (eq_refl x))) (f z H) = H) as help.
  { intros ? []. destruct (f x eq_refl); tauto. }
  intros p q. rewrite <-(help _ p), <-(help _ q).
  unfold f at 2 4. destruct (decide _); [reflexivity|]. exfalso; tauto.
Qed.
Global Instance Is_true_pi (b : bool) : ProofIrrel (Is_true b).
Proof. destruct b; simpl; apply _. Qed.
Lemma sig_eq_pi `(P : A → Prop) `{∀ x, ProofIrrel (P x)}
  (x y : sig P) : x = y ↔ `x = `y.
Proof.
  split; [intros <-; reflexivity|].
  destruct x as [x Hx], y as [y Hy]; simpl; intros; subst.
  f_equal. apply proof_irrel.
Qed.
Global Instance proj1_sig_inj `(P : A → Prop) `{∀ x, ProofIrrel (P x)} :
  Inj (=) (=) (proj1_sig (P:=P)).
Proof. intros ??. apply (sig_eq_pi P). Qed.
Lemma exists_proj1_pi `(P : A → Prop) `{∀ x, ProofIrrel (P x)}
  (x : sig P) p : `x ↾ p = x.
Proof. apply (sig_eq_pi _); reflexivity. Qed.
