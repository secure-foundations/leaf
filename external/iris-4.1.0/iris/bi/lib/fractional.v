From iris.bi Require Export bi.
From iris.proofmode Require Import classes classes_make proofmode.
From iris.prelude Require Import options.

Class Fractional {PROP : bi} (Φ : Qp → PROP) :=
  fractional p q : Φ (p + q)%Qp ⊣⊢ Φ p ∗ Φ q.
Global Arguments Fractional {_} _%I : simpl never.
Global Arguments fractional {_ _ _} _ _.

(** The [AsFractional] typeclass eta-expands a proposition [P] into [Φ q] such
that [Φ] is a fractional predicate. This is needed because higher-order
unification cannot be relied upon to guess the right [Φ].

[AsFractional] should generally be used in APIs that work with fractional
predicates (instead of [Fractional]): when the user provides the original
resource [P], have a premise [AsFractional P Φ 1] to convert that into some
fractional predicate.

The equivalence in [as_fractional] should hold definitionally; various typeclass
instances assume that [Φ q] will un-do the eta-expansion performed by
[AsFractional]. *)
Class AsFractional {PROP : bi} (P : PROP) (Φ : Qp → PROP) (q : Qp) := {
  as_fractional : P ⊣⊢ Φ q;
  as_fractional_fractional : Fractional Φ
}.
Global Arguments AsFractional {_} _%I _%I _%Qp.
Global Hint Mode AsFractional - ! - - : typeclass_instances.

(** The class [FrameFractionalQp] is used for fractional framing, it substracts
the fractional of the hypothesis from the goal: it computes [r := qP - qR].
See [frame_fractional] for how it is used. *)
Class FrameFractionalQp (qR qP r : Qp) :=
  frame_fractional_qp : qP = (qR + r)%Qp.
Global Hint Mode FrameFractionalQp ! ! - : typeclass_instances.

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

  (* Every [Fractional] predicate admits an obvious [AsFractional] instance.

  Ideally, this instance would mean that a user never has to define a manual
  [AsFractional] instance for a [Fractional] predicate (even if it's of the
  form [λ q, Φ a1 ‥ q ‥ an] for some n-ary predicate [Φ].) However, Coq's
  lack of guarantees for higher-order unification mean this instance wouldn't
  guarantee to apply for every [AsFractional] goal.

  Therefore, this instance is not global to avoid conflicts with existing instances
  defined by our users, since we can't ask users to universally delete their
  manually-defined [AsFractional] instances for their own [Fractional] predicates.

  (We could just support this instance for predicates with the fractional argument
  in the final position, but that was felt to be a bit of a foot-gun - users would
  have to remember to *not* define an [AsFractional] some of the time.) *)
  Local Instance fractional_as_fractional Φ q :
    Fractional Φ → AsFractional (Φ q) Φ q.
  Proof. done. Qed.

  (** This lemma is meant to be used when [P] is known. But really you should be
   using [iDestruct "H" as "[H1 H2]"], which supports splitting at fractions. *)
  Lemma fractional_split P Φ q1 q2 :
    AsFractional P Φ (q1 + q2) →
    P ⊣⊢ Φ q1 ∗ Φ q2.
  Proof. by move=>-[-> ->]. Qed.
  (** This lemma is meant to be used when [P] is known. But really you should be
   using [iDestruct "H" as "[H1 H2]"], which supports halving fractions. *)
  Lemma fractional_half P Φ q :
    AsFractional P Φ q →
    P ⊣⊢ Φ (q/2)%Qp ∗ Φ (q/2)%Qp.
  Proof. by rewrite -{1}(Qp.div_2 q)=>-[->->]. Qed.
  (** This lemma is meant to be used when [P1], [P2] are known. But really you
   should be using [iCombine "H1 H2" as "H"] (for forwards reasoning) or
   [iSplitL]/[iSplitR] (for goal-oriented reasoning), which support merging
   fractions. *)
  Lemma fractional_merge P1 P2 Φ q1 q2 `{!Fractional Φ} :
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P1 ∗ P2 ⊣⊢ Φ (q1 + q2)%Qp.
  Proof. move=>-[-> _] [-> _]. rewrite fractional //. Qed.

  (** Fractional and logical connectives *)
  Global Instance persistent_fractional (P : PROP) :
    Persistent P → TCOr (Affine P) (Absorbing P) → Fractional (λ _, P).
  Proof. intros ?? q q'. apply: bi.persistent_sep_dup. Qed.

  (** We do not have [AsFractional] instances for [∗] and the big operators
  because the [iDestruct] tactic already turns [P ∗ Q] into [P] and [Q],
  [[∗ list] k↦x ∈ y :: l, Φ k x] into [Φ 0 i] and [[∗ list] k↦x ∈ l, Φ (S k) x],
  etc. Hence, an [AsFractional] instance would cause ambiguity because for
  example [l ↦{1} v ∗ l' ↦{1} v'] could be turned into [l ↦{1} v] and
  [l' ↦{1} v'], or into two times [l ↦{1/2} v ∗ l' ↦{1/2} v'].

  We do provide the [Fractional] instances so that when one defines a derived
  connection in terms of [∗] or a big operator (and makes that opaque in some
  way), one could choose to split along the [∗] or along the fraction. *)
  Global Instance fractional_sep Φ Ψ :
    Fractional Φ → Fractional Ψ → Fractional (λ q, Φ q ∗ Ψ q)%I.
  Proof.
    intros ?? q q'. rewrite !fractional -!assoc. f_equiv.
    rewrite !assoc. f_equiv. by rewrite comm.
  Qed.

  Global Instance fractional_embed `{!BiEmbed PROP PROP'} Φ :
    Fractional Φ → Fractional (λ q, ⎡ Φ q ⎤ : PROP')%I.
  Proof. intros ???. by rewrite fractional embed_sep. Qed.

  Global Instance as_fractional_embed `{!BiEmbed PROP PROP'} P Φ q :
    AsFractional P Φ q → AsFractional (⎡ P ⎤) (λ q, ⎡ Φ q ⎤)%I q.
  Proof. intros [??]; split; [by f_equiv|apply _]. Qed.

  Global Instance fractional_big_sepL {A} (l : list A) Ψ :
    (∀ k x, Fractional (Ψ k x)) →
    Fractional (PROP:=PROP) (λ q, [∗ list] k↦x ∈ l, Ψ k x q)%I.
  Proof. intros ? q q'. rewrite -big_sepL_sep. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepL2 {A B} (l1 : list A) (l2 : list B) Ψ :
    (∀ k x1 x2, Fractional (Ψ k x1 x2)) →
    Fractional (PROP:=PROP) (λ q, [∗ list] k↦x1; x2 ∈ l1; l2, Ψ k x1 x2 q)%I.
  Proof. intros ? q q'. rewrite -big_sepL2_sep. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepM `{Countable K} {A} (m : gmap K A) Ψ :
    (∀ k x, Fractional (Ψ k x)) →
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

  (** Proof mode instances *)
  Global Instance from_sep_fractional P Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → FromSep P (Φ q1) (Φ q2).
  Proof. rewrite /FromSep=>-[-> ->] //. Qed.
  Global Instance combine_sep_as_fractional P1 P2 Φ q1 q2 :
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    CombineSepAs P1 P2 (Φ (q1 + q2)%Qp) | 50.
  (* Explicit cost, to make it easier to provide instances with higher or
     lower cost. Higher-cost instances exist to combine (for example)
     [l ↦{q1} v1] with [l ↦{q2} v2] where [v1] and [v2] are not unifiable. *)
  Proof. rewrite /CombineSepAs =>-[-> _] [-> <-] //. Qed.

  Global Instance from_sep_fractional_half P Φ q :
    AsFractional P Φ q → FromSep P (Φ (q / 2)%Qp) (Φ (q / 2)%Qp) | 10.
  Proof. rewrite /FromSep -{1}(Qp.div_2 q). intros [-> <-]. rewrite Qp.div_2 //. Qed.
  Global Instance combine_sep_as_fractional_half P Φ q :
    AsFractional P Φ (q/2) → CombineSepAs P P (Φ q) | 50.
  (* Explicit cost, to make it easier to provide instances with higher or
     lower cost. Higher-cost instances exist to combine (for example)
     [l ↦{q1} v1] with [l ↦{q2} v2] where [v1] and [v2] are not unifiable. *)
  Proof. rewrite /CombineSepAs=>-[-> <-]. by rewrite Qp.div_2. Qed.

  Global Instance into_sep_fractional P Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → IntoSep P (Φ q1) (Φ q2).
  Proof. intros [??]. rewrite /IntoSep [P]fractional_split //. Qed.

  Global Instance into_sep_fractional_half P Φ q :
    AsFractional P Φ q → IntoSep P (Φ (q / 2)%Qp) (Φ (q / 2)%Qp) | 100.
  Proof. intros [??]. rewrite /IntoSep [P]fractional_half //. Qed.

  Global Instance frame_fractional_qp_add_l q q' : FrameFractionalQp q (q + q') q'.
  Proof. by rewrite /FrameFractionalQp. Qed.
  Global Instance frame_fractional_qp_add_r q q' : FrameFractionalQp q' (q + q') q.
  Proof. by rewrite /FrameFractionalQp Qp.add_comm. Qed.
  Global Instance frame_fractional_qp_half q : FrameFractionalQp (q/2) q (q/2).
  Proof. by rewrite /FrameFractionalQp Qp.div_2. Qed.

  (* Not an instance because of performance; you can locally add it if you are
  willing to pay the cost. We have concrete instances for certain fractional
  assertions such as ↦.

  Coq is sometimes unable to infer the [Φ], hence it might be useful to write
  [apply: (frame_fractional (λ q, ...))] when using the lemma to prove your
  custom instance. See also https://github.com/coq/coq/issues/17688 *)
  Lemma frame_fractional Φ p R P qR qP r :
    AsFractional R Φ qR →
    AsFractional P Φ qP →
    FrameFractionalQp qR qP r →
    Frame p R P (Φ r).
  Proof.
    rewrite /Frame /FrameFractionalQp=> -[-> _] [-> ?] ->.
    by rewrite bi.intuitionistically_if_elim fractional.
  Qed.
End fractional.

(** Marked [tc_opaque] instead [Typeclasses Opaque] so that you can use
[iDestruct] to eliminate and [iModIntro] to introduce [internal_fractional],
while still preventing [iFrame] and [iNext] from unfolding. *)
Definition internal_fractional {PROP : bi} (Φ : Qp → PROP) : PROP :=
  tc_opaque (□ ∀ p q, Φ (p + q)%Qp ∗-∗ Φ p ∗ Φ q)%I.
Global Instance: Params (@internal_fractional) 1 := {}.

Section internal_fractional.
  Context {PROP : bi}.
  Implicit Types Φ Ψ : Qp → PROP.
  Implicit Types q : Qp.

  Global Instance internal_fractional_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@internal_fractional PROP).
  Proof. solve_proper. Qed.
  Global Instance internal_fractional_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@internal_fractional PROP).
  Proof. solve_proper. Qed.

  Global Instance internal_fractional_affine Φ : Affine (internal_fractional Φ).
  Proof. rewrite /internal_fractional /=. apply _. Qed.
  Global Instance internal_fractional_persistent Φ :
    Persistent (internal_fractional Φ).
  Proof. rewrite /internal_fractional /=. apply _. Qed.

  Lemma fractional_internal_fractional Φ :
    Fractional Φ → ⊢ internal_fractional Φ.
  Proof.
    intros. iIntros "!>" (q1 q2).
    rewrite [Φ (q1 + q2)%Qp]fractional //=; auto.
  Qed.

  Lemma internal_fractional_iff Φ Ψ:
    □ (∀ q, Φ q ∗-∗ Ψ q) ⊢ internal_fractional Φ -∗ internal_fractional Ψ.
  Proof.
    iIntros "#Hiff #HΦdup !>" (p q).
    iSplit.
    - iIntros "H".
      iDestruct ("Hiff" with "H") as "HΦ".
      iDestruct ("HΦdup" with "HΦ") as "[H1 ?]".
      iSplitL "H1"; iApply "Hiff"; iFrame.
    - iIntros "[H1 H2]".
      iDestruct ("Hiff" with "H1") as "HΦ1".
      iDestruct ("Hiff" with "H2") as "HΦ2".
      iApply "Hiff".
      iApply "HΦdup".
      iFrame.
  Qed.
End internal_fractional.
