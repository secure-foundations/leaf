From iris.bi Require Export bi.
From iris.proofmode Require Import classes class_instances.
From iris.prelude Require Import options.

Class Fractional {PROP : bi} (Φ : Qp → PROP) :=
  fractional p q : Φ (p + q)%Qp ⊣⊢ Φ p ∗ Φ q.
Global Arguments Fractional {_} _%I : simpl never.

Class AsFractional {PROP : bi} (P : PROP) (Φ : Qp → PROP) (q : Qp) := {
  as_fractional : P ⊣⊢ Φ q;
  as_fractional_fractional :> Fractional Φ
}.
Global Arguments AsFractional {_} _%I _%I _%Qp.

Global Arguments fractional {_ _ _} _ _.

Global Hint Mode AsFractional - + - - : typeclass_instances.
(* To make [as_fractional_fractional] a useful instance, we have to
allow [q] to be an evar. *)
Global Hint Mode AsFractional - - + - : typeclass_instances.

Section fractional.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.
  Implicit Types Φ : Qp → PROP.
  Implicit Types q : Qp.

  Global Instance Fractional_proper :
    Proper (pointwise_relation _ (≡) ==> iff) (@Fractional PROP).
  Proof.
    rewrite /Fractional.
    intros Φ1 Φ2 Hequiv.
    by setoid_rewrite Hequiv.
  Qed.

  Lemma fractional_split P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P ⊣⊢ P1 ∗ P2.
  Proof. by move=>-[-> ->] [-> _] [-> _]. Qed.
  Lemma fractional_split_1 P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P -∗ P1 ∗ P2.
  Proof. intros. by rewrite -(fractional_split P). Qed.
  Lemma fractional_split_2 P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P1 -∗ P2 -∗ P.
  Proof. intros. apply bi.wand_intro_r. by rewrite -(fractional_split P). Qed.

  Lemma fractional_merge P1 P2 Φ q1 q2 `{!Fractional Φ} :
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P1 -∗ P2 -∗ Φ (q1 + q2)%Qp.
  Proof. move=>-[-> _] [-> _]. rewrite fractional. apply bi.wand_intro_r. done. Qed.

  Lemma fractional_half P P12 Φ q :
    AsFractional P Φ q → AsFractional P12 Φ (q/2) →
    P ⊣⊢ P12 ∗ P12.
  Proof. by rewrite -{1}(Qp_div_2 q)=>-[->->][-> _]. Qed.
  Lemma fractional_half_1 P P12 Φ q :
    AsFractional P Φ q → AsFractional P12 Φ (q/2) →
    P -∗ P12 ∗ P12.
  Proof. intros. by rewrite -(fractional_half P). Qed.
  Lemma fractional_half_2 P P12 Φ q :
    AsFractional P Φ q → AsFractional P12 Φ (q/2) →
    P12 -∗ P12 -∗ P.
  Proof. intros. apply bi.wand_intro_r. by rewrite -(fractional_half P). Qed.

  (** Fractional and logical connectives *)
  Global Instance persistent_fractional P :
    Persistent P → Absorbing P → Fractional (λ _, P).
  Proof. intros ?? q q'. apply: bi.persistent_sep_dup. Qed.

  Global Instance fractional_sep Φ Ψ :
    Fractional Φ → Fractional Ψ → Fractional (λ q, Φ q ∗ Ψ q)%I.
  Proof.
    intros ?? q q'. rewrite !fractional -!assoc. f_equiv.
    rewrite !assoc. f_equiv. by rewrite comm.
  Qed.

  Global Instance fractional_big_sepL {A} l Ψ :
    (∀ k (x : A), Fractional (Ψ k x)) →
    Fractional (PROP:=PROP) (λ q, [∗ list] k↦x ∈ l, Ψ k x q)%I.
  Proof. intros ? q q'. rewrite -big_sepL_sep. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepM `{Countable K} {A} (m : gmap K A) Ψ :
    (∀ k (x : A), Fractional (Ψ k x)) →
    Fractional (PROP:=PROP) (λ q, [∗ map] k↦x ∈ m, Ψ k x q)%I.
  Proof. intros ? q q'. rewrite -big_sepM_sep. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepS `{Countable A} (X : gset A) Ψ :
    (∀ x, Fractional (Ψ x)) →
    Fractional (PROP:=PROP) (λ q, [∗ set] x ∈ X, Ψ x q)%I.
  Proof. intros ? q q'. rewrite -big_sepS_sep. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepMS `{Countable A} (X : gmultiset A) Ψ :
    (∀ x, Fractional (Ψ x)) →
    Fractional (PROP:=PROP) (λ q, [∗ mset] x ∈ X, Ψ x q)%I.
  Proof. intros ? q q'. rewrite -big_sepMS_sep. by setoid_rewrite fractional. Qed.

  (** Mult instances *)

  Global Instance mul_fractional_l Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (q * p)) → Fractional Φ.
  Proof.
    intros H q q'. rewrite ->!as_fractional, Qp_mul_add_distr_r. by apply H.
  Qed.
  Global Instance mul_fractional_r Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (p * q)) → Fractional Φ.
  Proof.
    intros H q q'. rewrite ->!as_fractional, Qp_mul_add_distr_l. by apply H.
  Qed.

  (* REMARK: These two instances do not work in either direction of the
     search:
       - In the forward direction, they make the search not terminate
       - In the backward direction, the higher order unification of Φ
         with the goal does not work. *)
  Local Instance mul_as_fractional_l P Φ p q :
    AsFractional P Φ (q * p) → AsFractional P (λ q, Φ (q * p)%Qp) q.
  Proof.
    intros H. split; first apply H. eapply (mul_fractional_l _ Φ p).
    split; first done. apply H.
  Qed.
  Local Instance mul_as_fractional_r P Φ p q :
    AsFractional P Φ (p * q) → AsFractional P (λ q, Φ (p * q)%Qp) q.
  Proof.
    intros H. split; first apply H. eapply (mul_fractional_r _ Φ p).
    split; first done. apply H.
  Qed.

  (** Proof mode instances *)
  Global Instance from_and_fractional_fwd P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    FromSep P P1 P2.
  Proof. by rewrite /FromSep=>-[-> ->] [-> _] [-> _]. Qed.
  Global Instance from_sep_fractional_bwd P P1 P2 Φ q1 q2 :
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 → AsFractional P Φ (q1 + q2) →
    FromSep P P1 P2 | 10.
  Proof. by rewrite /FromSep=>-[-> _] [-> <-] [-> _]. Qed.

  Global Instance from_sep_fractional_half_fwd P Q Φ q :
    AsFractional P Φ q → AsFractional Q Φ (q/2) →
    FromSep P Q Q | 10.
  Proof. by rewrite /FromSep -{1}(Qp_div_2 q)=>-[-> ->] [-> _]. Qed.
  Global Instance from_sep_fractional_half_bwd P Q Φ q :
    AsFractional P Φ (q/2) → AsFractional Q Φ q →
    FromSep Q P P.
  Proof. rewrite /FromSep=>-[-> <-] [-> _]. by rewrite Qp_div_2. Qed.

  Global Instance into_sep_fractional P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    IntoSep P P1 P2.
  Proof. intros. rewrite /IntoSep [P]fractional_split //. Qed.

  Global Instance into_sep_fractional_half P Q Φ q :
    AsFractional P Φ q → AsFractional Q Φ (q/2) →
    IntoSep P Q Q | 100.
  Proof. intros. rewrite /IntoSep [P]fractional_half //. Qed.

  (* The instance [frame_fractional] can be tried at all the nodes of
     the proof search. The proof search then fails almost always on
     [AsFractional R Φ r], but the slowdown is still noticeable.  For
     that reason, we factorize the three instances that could have been
     defined for that purpose into one. *)
  Inductive FrameFractionalHyps
      (p : bool) (R : PROP) (Φ : Qp → PROP) (RES : PROP) : Qp → Qp → Prop :=
    | frame_fractional_hyps_l Q q q' r:
       Frame p R (Φ q) Q →
       MakeSep Q (Φ q') RES →
       FrameFractionalHyps p R Φ RES r (q + q')
    | frame_fractional_hyps_r Q q q' r:
       Frame p R (Φ q') Q →
       MakeSep Q (Φ q) RES →
       FrameFractionalHyps p R Φ RES r (q + q')
    | frame_fractional_hyps_half q :
       AsFractional RES Φ (q/2) →
       FrameFractionalHyps p R Φ RES (q/2) q.
  Existing Class FrameFractionalHyps.
  Global Existing Instances frame_fractional_hyps_l frame_fractional_hyps_r
    frame_fractional_hyps_half.

  Global Instance frame_fractional p R r Φ P q RES:
    AsFractional R Φ r → AsFractional P Φ q →
    FrameFractionalHyps p R Φ RES r q →
    Frame p R P RES.
  Proof.
    rewrite /Frame=>-[HR _][->?]H.
    revert H HR=>-[Q q0 q0' r0|Q q0 q0' r0|q0].
    - rewrite fractional /Frame /MakeSep=><-<-. by rewrite assoc.
    - rewrite fractional /Frame /MakeSep=><-<-=>_.
      by rewrite (comm _ Q (Φ q0)) !assoc (comm _ (Φ _)).
    - move=>-[-> _]->. by rewrite bi.intuitionistically_if_elim -fractional Qp_div_2.
  Qed.
End fractional.
