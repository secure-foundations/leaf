From stdpp Require Import finite.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates.
From iris.prelude Require Import options.

Definition discrete_fun_insert `{EqDecision A} {B : A → ofe}
    (x : A) (y : B x) (f : discrete_fun B) : discrete_fun B := λ x',
  match decide (x = x') with left H => eq_rect _ B y _ H | right _ => f x' end.
Global Instance: Params (@discrete_fun_insert) 5 := {}.

Definition discrete_fun_singleton `{EqDecision A} {B : A → ucmra}
  (x : A) (y : B x) : discrete_fun B := discrete_fun_insert x y ε.
Global Instance: Params (@discrete_fun_singleton) 5 := {}.

Section ofe.
  Context `{Heqdec : EqDecision A} {B : A → ofe}.
  Implicit Types x : A.
  Implicit Types f g : discrete_fun B.

  Global Instance discrete_funO_ofe_discrete :
    (∀ i, OfeDiscrete (B i)) → OfeDiscrete (discrete_funO B).
  Proof. intros HB f f' Heq i. apply HB, Heq. Qed.

  (** Properties of discrete_fun_insert. *)
  Global Instance discrete_fun_insert_ne x :
    NonExpansive2 (discrete_fun_insert (B:=B) x).
  Proof.
    intros n y1 y2 ? f1 f2 ? x'; rewrite /discrete_fun_insert.
    by destruct (decide _) as [[]|].
  Qed.
  Global Instance discrete_fun_insert_proper x :
    Proper ((≡) ==> (≡) ==> (≡)) (discrete_fun_insert (B:=B) x) := ne_proper_2 _.

  Lemma discrete_fun_lookup_insert f x y : (discrete_fun_insert x y f) x = y.
  Proof.
    rewrite /discrete_fun_insert; destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
  Lemma discrete_fun_lookup_insert_ne f x x' y :
    x ≠ x' → (discrete_fun_insert x y f) x' = f x'.
  Proof. by rewrite /discrete_fun_insert; destruct (decide _). Qed.

  Global Instance discrete_fun_insert_discrete f x y :
    Discrete f → Discrete y → Discrete (discrete_fun_insert x y f).
  Proof.
    intros ?? g Heq x'; destruct (decide (x = x')) as [->|].
    - rewrite discrete_fun_lookup_insert.
      apply: discrete. by rewrite -(Heq x') discrete_fun_lookup_insert.
    - rewrite discrete_fun_lookup_insert_ne //.
      apply: discrete. by rewrite -(Heq x') discrete_fun_lookup_insert_ne.
  Qed.
End ofe.

Section cmra.
  Context `{EqDecision A} {B : A → ucmra}.
  Implicit Types x : A.
  Implicit Types f g : discrete_fun B.

  Global Instance discrete_funR_cmra_discrete:
    (∀ i, CmraDiscrete (B i)) → CmraDiscrete (discrete_funR B).
  Proof. intros HB. split; [apply _|]. intros x Hv i. apply HB, Hv. Qed.

  Global Instance discrete_fun_singleton_ne x :
    NonExpansive (discrete_fun_singleton x : B x → _).
  Proof.
    intros n y1 y2 ?; apply discrete_fun_insert_ne; [done|].
    by apply equiv_dist.
  Qed.
  Global Instance discrete_fun_singleton_proper x :
    Proper ((≡) ==> (≡)) (discrete_fun_singleton x) := ne_proper _.

  Lemma discrete_fun_lookup_singleton x (y : B x) : (discrete_fun_singleton x y) x = y.
  Proof. by rewrite /discrete_fun_singleton discrete_fun_lookup_insert. Qed.
  Lemma discrete_fun_lookup_singleton_ne x x' (y : B x) :
    x ≠ x' → (discrete_fun_singleton x y) x' = ε.
  Proof. intros; by rewrite /discrete_fun_singleton discrete_fun_lookup_insert_ne. Qed.

  Global Instance discrete_fun_singleton_discrete x (y : B x) :
    (∀ i, Discrete (ε : B i)) →  Discrete y → Discrete (discrete_fun_singleton x y).
  Proof. apply _. Qed.

  Lemma discrete_fun_singleton_validN n x (y : B x) : ✓{n} discrete_fun_singleton x y ↔ ✓{n} y.
  Proof.
    split; [by move=>/(_ x); rewrite discrete_fun_lookup_singleton|].
    move=>Hx x'; destruct (decide (x = x')) as [->|];
      rewrite ?discrete_fun_lookup_singleton ?discrete_fun_lookup_singleton_ne //.
    by apply ucmra_unit_validN.
  Qed.

  Lemma discrete_fun_singleton_core x (y : B x) :
    core (discrete_fun_singleton x y) ≡ discrete_fun_singleton x (core y).
  Proof.
    move=>x'; destruct (decide (x = x')) as [->|];
      by rewrite discrete_fun_lookup_core ?discrete_fun_lookup_singleton
      ?discrete_fun_lookup_singleton_ne // (core_id_core ∅).
  Qed.

  Global Instance discrete_fun_singleton_core_id x (y : B x) :
    CoreId y → CoreId (discrete_fun_singleton x y).
  Proof. by rewrite !core_id_total discrete_fun_singleton_core=> ->. Qed.

  Lemma discrete_fun_singleton_op (x : A) (y1 y2 : B x) :
    discrete_fun_singleton x y1 ⋅ discrete_fun_singleton x y2 ≡ discrete_fun_singleton x (y1 ⋅ y2).
  Proof.
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton.
    - by rewrite discrete_fun_lookup_op !discrete_fun_lookup_singleton_ne // left_id.
  Qed.

  Lemma discrete_fun_insert_updateP x (P : B x → Prop) (Q : discrete_fun B → Prop) g y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (discrete_fun_insert x y2 g)) →
    discrete_fun_insert x y1 g ~~>: Q.
  Proof.
    intros Hy1 HP; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hy1 n (Some (gf x))) as (y2&?&?).
    { move: (Hg x). by rewrite discrete_fun_lookup_op discrete_fun_lookup_insert. }
    exists (discrete_fun_insert x y2 g); split; [auto|].
    intros x'; destruct (decide (x' = x)) as [->|];
      rewrite discrete_fun_lookup_op ?discrete_fun_lookup_insert //; [].
    move: (Hg x'). by rewrite discrete_fun_lookup_op !discrete_fun_lookup_insert_ne.
  Qed.

  Lemma discrete_fun_insert_updateP' x (P : B x → Prop) g y1 :
    y1 ~~>: P →
    discrete_fun_insert x y1 g ~~>: λ g', ∃ y2, g' = discrete_fun_insert x y2 g ∧ P y2.
  Proof. eauto using discrete_fun_insert_updateP. Qed.
  Lemma discrete_fun_insert_update g x y1 y2 :
    y1 ~~> y2 → discrete_fun_insert x y1 g ~~> discrete_fun_insert x y2 g.
  Proof.
    rewrite !cmra_update_updateP; eauto using discrete_fun_insert_updateP with subst.
  Qed.

  Lemma discrete_fun_singleton_updateP x (P : B x → Prop) (Q : discrete_fun B → Prop) y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (discrete_fun_singleton x y2)) →
    discrete_fun_singleton x y1 ~~>: Q.
  Proof. rewrite /discrete_fun_singleton; eauto using discrete_fun_insert_updateP. Qed.
  Lemma discrete_fun_singleton_updateP' x (P : B x → Prop) y1 :
    y1 ~~>: P →
    discrete_fun_singleton x y1 ~~>: λ g, ∃ y2, g = discrete_fun_singleton x y2 ∧ P y2.
  Proof. eauto using discrete_fun_singleton_updateP. Qed.
  Lemma discrete_fun_singleton_update x (y1 y2 : B x) :
    y1 ~~> y2 → discrete_fun_singleton x y1 ~~> discrete_fun_singleton x y2.
  Proof. eauto using discrete_fun_insert_update. Qed.

  Lemma discrete_fun_singleton_updateP_empty x (P : B x → Prop) (Q : discrete_fun B → Prop) :
    ε ~~>: P → (∀ y2, P y2 → Q (discrete_fun_singleton x y2)) → ε ~~>: Q.
  Proof.
    intros Hx HQ; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hx n (Some (gf x))) as (y2&?&?); first apply Hg.
    exists (discrete_fun_singleton x y2); split; [by apply HQ|].
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton.
    - rewrite discrete_fun_lookup_op discrete_fun_lookup_singleton_ne //. apply Hg.
  Qed.
  Lemma discrete_fun_singleton_updateP_empty' x (P : B x → Prop) :
    ε ~~>: P → ε ~~>: λ g, ∃ y2, g = discrete_fun_singleton x y2 ∧ P y2.
  Proof. eauto using discrete_fun_singleton_updateP_empty. Qed.
  Lemma discrete_fun_singleton_update_empty x (y : B x) :
    ε ~~> y → ε ~~> discrete_fun_singleton x y.
  Proof.
    rewrite !cmra_update_updateP;
      eauto using discrete_fun_singleton_updateP_empty with subst.
  Qed.
End cmra.
