From stdpp Require Import nat_cancel.
From iris.bi Require Import bi.
From iris.proofmode Require Import modality_instances classes.
From iris.prelude Require Import options.
Import bi.

Section class_instances_later.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

(** FromAssumption *)
Global Instance from_assumption_later p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (▷ Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply later_intro. Qed.
Global Instance from_assumption_laterN n p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (▷^n Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply laterN_intro. Qed.
Global Instance from_assumption_except_0 p P Q :
  FromAssumption p P Q → KnownRFromAssumption p P (◇ Q).
Proof. rewrite /KnownRFromAssumption /FromAssumption=>->. apply except_0_intro. Qed.

(** FromPure *)
Global Instance from_pure_later a P φ : FromPure a P φ → FromPure a (▷ P) φ.
Proof. rewrite /FromPure=> ->. apply later_intro. Qed.
Global Instance from_pure_laterN a n P φ : FromPure a P φ → FromPure a (▷^n P) φ.
Proof. rewrite /FromPure=> ->. apply laterN_intro. Qed.
Global Instance from_pure_except_0 a P φ : FromPure a P φ → FromPure a (◇ P) φ.
Proof. rewrite /FromPure=> ->. apply except_0_intro. Qed.

(** IntoWand *)
Global Instance into_wand_later p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷ R) (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand /= => HR.
  by rewrite !later_intuitionistically_if_2 -later_wand HR.
Qed.
Global Instance into_wand_later_args p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷ P) (▷ Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !later_intuitionistically_if_2
             (later_intro (□?p R)) -later_wand HR.
Qed.
Global Instance into_wand_laterN n p q R P Q :
  IntoWand p q R P Q → IntoWand p q (▷^n R) (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand /= => HR.
  by rewrite !laterN_intuitionistically_if_2 -laterN_wand HR.
Qed.
Global Instance into_wand_laterN_args n p q R P Q :
  IntoWand p q R P Q → IntoWand' p q R (▷^n P) (▷^n Q).
Proof.
  rewrite /IntoWand' /IntoWand /= => HR.
  by rewrite !laterN_intuitionistically_if_2
             (laterN_intro _ (□?p R)) -laterN_wand HR.
Qed.

(** FromAnd *)
Global Instance from_and_later P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromAnd=> <-. by rewrite later_and. Qed.
Global Instance from_and_laterN n P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromAnd=> <-. by rewrite laterN_and. Qed.
Global Instance from_and_except_0 P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromAnd=><-. by rewrite except_0_and. Qed.

(** FromSep *)
Global Instance from_sep_later P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromSep=> <-. by rewrite later_sep. Qed.
Global Instance from_sep_laterN n P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromSep=> <-. by rewrite laterN_sep. Qed.
Global Instance from_sep_except_0 P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromSep=><-. by rewrite except_0_sep. Qed.

(** IntoAnd *)
Global Instance into_and_later p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷ P) (▷ Q1) (▷ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply intuitionistically_if_intro'.
  by rewrite later_intuitionistically_if_2 HP
             intuitionistically_if_elim later_and.
Qed.
Global Instance into_and_laterN n p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (▷^n P) (▷^n Q1) (▷^n Q2).
Proof.
  rewrite /IntoAnd=> HP. apply intuitionistically_if_intro'.
  by rewrite laterN_intuitionistically_if_2 HP
             intuitionistically_if_elim laterN_and.
Qed.
Global Instance into_and_except_0 p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p (◇ P) (◇ Q1) (◇ Q2).
Proof.
  rewrite /IntoAnd=> HP. apply intuitionistically_if_intro'.
  by rewrite except_0_intuitionistically_if_2 HP
             intuitionistically_if_elim except_0_and.
Qed.

(** IntoSep *)
Global Instance into_sep_later P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoSep=> ->. by rewrite later_sep. Qed.
Global Instance into_sep_laterN n P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /IntoSep=> ->. by rewrite laterN_sep. Qed.
Global Instance into_sep_except_0 P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /IntoSep=> ->. by rewrite except_0_sep. Qed.

(* FIXME: This instance is overly specific, generalize it. *)
Global Instance into_sep_affinely_later `{!Timeless (PROP:=PROP) emp} P Q1 Q2 :
  IntoSep P Q1 Q2 → Affine Q1 → Affine Q2 →
  IntoSep (<affine> ▷ P) (<affine> ▷ Q1) (<affine> ▷ Q2).
Proof.
  rewrite /IntoSep /= => -> ??.
  rewrite -{1}(affine_affinely Q1) -{1}(affine_affinely Q2) later_sep !later_affinely_1.
  rewrite -except_0_sep /bi_except_0 affinely_or. apply or_elim, affinely_elim.
  rewrite -(idemp bi_and (<affine> ▷ False)%I) persistent_and_sep_1.
  by rewrite -(False_elim Q1) -(False_elim Q2).
Qed.

(** FromOr *)
Global Instance from_or_later P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /FromOr=><-. by rewrite later_or. Qed.
Global Instance from_or_laterN n P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /FromOr=><-. by rewrite laterN_or. Qed.
Global Instance from_or_except_0 P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /FromOr=><-. by rewrite except_0_or. Qed.

(** IntoOr *)
Global Instance into_or_later P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷ P) (▷ Q1) (▷ Q2).
Proof. rewrite /IntoOr=>->. by rewrite later_or. Qed.
Global Instance into_or_laterN n P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (▷^n P) (▷^n Q1) (▷^n Q2).
Proof. rewrite /IntoOr=>->. by rewrite laterN_or. Qed.
Global Instance into_or_except_0 P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr (◇ P) (◇ Q1) (◇ Q2).
Proof. rewrite /IntoOr=>->. by rewrite except_0_or. Qed.

(** FromExist *)
Global Instance from_exist_later {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (▷ P) (λ a, ▷ (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply later_mono, exist_intro.
Qed.
Global Instance from_exist_laterN {A} n P (Φ : A → PROP) :
  FromExist P Φ → FromExist (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof.
  rewrite /FromExist=> <-. apply exist_elim=>x. apply laterN_mono, exist_intro.
Qed.
Global Instance from_exist_except_0 {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist (◇ P) (λ a, ◇ (Φ a))%I.
Proof. rewrite /FromExist=> <-. by rewrite except_0_exist_2. Qed.

(** IntoExist *)
Global Instance into_exist_later {A} P (Φ : A → PROP) name :
  IntoExist P Φ name → Inhabited A → IntoExist (▷ P) (λ a, ▷ (Φ a))%I name.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP later_exist. Qed.
Global Instance into_exist_laterN {A} n P (Φ : A → PROP) name :
  IntoExist P Φ name → Inhabited A → IntoExist (▷^n P) (λ a, ▷^n (Φ a))%I name.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP laterN_exist. Qed.
Global Instance into_exist_except_0 {A} P (Φ : A → PROP) name :
  IntoExist P Φ name → Inhabited A → IntoExist (◇ P) (λ a, ◇ (Φ a))%I name.
Proof. rewrite /IntoExist=> HP ?. by rewrite HP except_0_exist. Qed.

(** IntoForall *)
Global Instance into_forall_later {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (▷ P) (λ a, ▷ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP later_forall. Qed.

Global Instance into_forall_laterN {A} P (Φ : A → PROP) n :
  IntoForall P Φ → IntoForall (▷^n P) (λ a, ▷^n (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP laterN_forall. Qed.

Global Instance into_forall_except_0 {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall (◇ P) (λ a, ◇ (Φ a))%I.
Proof. rewrite /IntoForall=> HP. by rewrite HP except_0_forall. Qed.

(** FromForall *)
Global Instance from_forall_later {A} P (Φ : A → PROP) name :
  FromForall P Φ name → FromForall (▷ P) (λ a, ▷ (Φ a))%I name.
Proof. rewrite /FromForall=> <-. by rewrite later_forall. Qed.

Global Instance from_forall_laterN {A} P (Φ : A → PROP) n name :
      FromForall P Φ name → FromForall (▷^n P) (λ a, ▷^n (Φ a))%I name.
Proof. rewrite /FromForall => <-. by rewrite laterN_forall. Qed.

Global Instance from_forall_except_0 {A} P (Φ : A → PROP) name :
  FromForall P Φ name → FromForall (◇ P) (λ a, ◇ (Φ a))%I name.
Proof. rewrite /FromForall=> <-. by rewrite except_0_forall. Qed.

(** IsExcept0 *)
Global Instance is_except_0_except_0 P : IsExcept0 (◇ P).
Proof. by rewrite /IsExcept0 except_0_idemp. Qed.
Global Instance is_except_0_later P : IsExcept0 (▷ P).
Proof. by rewrite /IsExcept0 except_0_later. Qed.

(** FromModal *)
Global Instance from_modal_later P :
  FromModal True (modality_laterN 1) (▷^1 P) (▷ P) P.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_laterN n P :
  FromModal True (modality_laterN n) (▷^n P) (▷^n P) P.
Proof. by rewrite /FromModal. Qed.
Global Instance from_modal_except_0 P :
  FromModal True modality_id (◇ P) (◇ P) P.
Proof. by rewrite /FromModal /= -except_0_intro. Qed.

(** IntoExcept0 *)
Global Instance into_except_0_except_0 P : IntoExcept0 (◇ P) P.
Proof. by rewrite /IntoExcept0. Qed.
Global Instance into_except_0_later P : Timeless P → IntoExcept0 (▷ P) P.
Proof. by rewrite /IntoExcept0. Qed.
Global Instance into_except_0_later_if p P : Timeless P → IntoExcept0 (▷?p P) P.
Proof. rewrite /IntoExcept0. destruct p; auto using except_0_intro. Qed.

Global Instance into_except_0_affinely P Q :
  IntoExcept0 P Q → IntoExcept0 (<affine> P) (<affine> Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_affinely_2. Qed.
Global Instance into_except_0_intuitionistically P Q :
  IntoExcept0 P Q → IntoExcept0 (□ P) (□ Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_intuitionistically_2. Qed.
Global Instance into_except_0_absorbingly P Q :
  IntoExcept0 P Q → IntoExcept0 (<absorb> P) (<absorb> Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_absorbingly. Qed.
Global Instance into_except_0_persistently P Q :
  IntoExcept0 P Q → IntoExcept0 (<pers> P) (<pers> Q).
Proof. rewrite /IntoExcept0=> ->. by rewrite except_0_persistently. Qed.

(** ElimModal *)
Global Instance elim_modal_timeless p P P' Q :
  IntoExcept0 P P' → IsExcept0 Q → ElimModal True p p P P' Q Q.
Proof.
  intros. rewrite /ElimModal (except_0_intro (_ -∗ _)) (into_except_0 P).
  by rewrite except_0_intuitionistically_if_2 -except_0_sep wand_elim_r.
Qed.

(** AddModal *)
(* High priority to add a [▷] rather than a [◇] when [P] is timeless. *)
Global Instance add_modal_later_except_0 P Q :
  Timeless P → AddModal (▷ P) P (◇ Q) | 0.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)) (timeless P).
  by rewrite -except_0_sep wand_elim_r except_0_idemp.
Qed.
Global Instance add_modal_later P Q :
  Timeless P → AddModal (▷ P) P (▷ Q) | 0.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)) (timeless P).
  by rewrite -except_0_sep wand_elim_r except_0_later.
Qed.
Global Instance add_modal_except_0 P Q : AddModal (◇ P) P (◇ Q) | 1.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)).
  by rewrite -except_0_sep wand_elim_r except_0_idemp.
Qed.
Global Instance add_modal_except_0_later P Q : AddModal (◇ P) P (▷ Q) | 1.
Proof.
  intros. rewrite /AddModal (except_0_intro (_ -∗ _)).
  by rewrite -except_0_sep wand_elim_r except_0_later.
Qed.

(** IntoAcc *)
(* TODO: We could have instances from "unfolded" accessors with or without
   the first binder. *)

(** IntoLater *)
Global Instance into_laterN_0 only_head P : IntoLaterN only_head 0 P P.
Proof. by rewrite /IntoLaterN /MaybeIntoLaterN. Qed.
Global Instance into_laterN_later only_head n n' m' P Q lQ :
  NatCancel n 1 n' m' →
  (** If canceling has failed (i.e. [1 = m']), we should make progress deeper
  into [P], as such, we continue with the [IntoLaterN] class, which is required
  to make progress. If canceling has succeeded, we do not need to make further
  progress, but there may still be a left-over (i.e. [n']) to cancel more deeply
  into [P], as such, we continue with [MaybeIntoLaterN]. *)
  TCIf (TCEq 1 m') (IntoLaterN only_head n' P Q) (MaybeIntoLaterN only_head n' P Q) →
  MakeLaterN m' Q lQ →
  IntoLaterN only_head n (▷ P) lQ | 2.
Proof.
  rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel.
  move=> Hn [_ ->|->] <-;
    by rewrite -later_laterN -laterN_plus -Hn Nat.add_comm.
Qed.
Global Instance into_laterN_laterN only_head n m n' m' P Q lQ :
  NatCancel n m n' m' →
  TCIf (TCEq m m') (IntoLaterN only_head n' P Q) (MaybeIntoLaterN only_head n' P Q) →
  MakeLaterN m' Q lQ →
  IntoLaterN only_head n (▷^m P) lQ | 1.
Proof.
  rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel.
  move=> Hn [_ ->|->] <-; by rewrite -!laterN_plus -Hn Nat.add_comm.
Qed.

Global Instance into_laterN_and_l n P1 P2 Q1 Q2 :
  IntoLaterN false n P1 Q1 → MaybeIntoLaterN false n P2 Q2 →
  IntoLaterN false n (P1 ∧ P2) (Q1 ∧ Q2) | 10.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> -> ->. by rewrite laterN_and. Qed.
Global Instance into_laterN_and_r n P P2 Q2 :
  IntoLaterN false n P2 Q2 → IntoLaterN false n (P ∧ P2) (P ∧ Q2) | 11.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_and -(laterN_intro _ P).
Qed.

Global Instance into_laterN_forall {A} n (Φ Ψ : A → PROP) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN laterN_forall=> ?. by apply forall_mono. Qed.
Global Instance into_laterN_exist {A} n (Φ Ψ : A → PROP) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN -laterN_exist_2=> ?. by apply exist_mono. Qed.

Global Instance into_laterN_or_l n P1 P2 Q1 Q2 :
  IntoLaterN false n P1 Q1 → MaybeIntoLaterN false n P2 Q2 →
  IntoLaterN false n (P1 ∨ P2) (Q1 ∨ Q2) | 10.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> -> ->. by rewrite laterN_or. Qed.
Global Instance into_laterN_or_r n P P2 Q2 :
  IntoLaterN false n P2 Q2 →
  IntoLaterN false n (P ∨ P2) (P ∨ Q2) | 11.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_or -(laterN_intro _ P).
Qed.

Global Instance into_later_affinely n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (<affine> P) (<affine> Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_affinely_2. Qed.
Global Instance into_later_intuitionistically n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (□ P) (□ Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_intuitionistically_2. Qed.
Global Instance into_later_absorbingly n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (<absorb> P) (<absorb> Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_absorbingly. Qed.
Global Instance into_later_persistently n P Q :
  IntoLaterN false n P Q → IntoLaterN false n (<pers> P) (<pers> Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_persistently. Qed.

Global Instance into_laterN_sep_l n P1 P2 Q1 Q2 :
  IntoLaterN false n P1 Q1 → MaybeIntoLaterN false n P2 Q2 →
  IntoLaterN false n (P1 ∗ P2) (Q1 ∗ Q2) | 10.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> -> ->. by rewrite laterN_sep. Qed.
Global Instance into_laterN_sep_r n P P2 Q2 :
  IntoLaterN false n P2 Q2 →
  IntoLaterN false n (P ∗ P2) (P ∗ Q2) | 11.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite laterN_sep -(laterN_intro _ P).
Qed.

Global Instance into_laterN_big_sepL n {A} (Φ Ψ : nat → A → PROP) (l: list A) :
  (∀ x k, IntoLaterN false n (Φ k x) (Ψ k x)) →
  IntoLaterN false n ([∗ list] k ↦ x ∈ l, Φ k x) ([∗ list] k ↦ x ∈ l, Ψ k x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opL_commute. by apply big_sepL_mono.
Qed.
Global Instance into_laterN_big_sepL2 n {A B} (Φ Ψ : nat → A → B → PROP) l1 l2 :
  (∀ x1 x2 k, IntoLaterN false n (Φ k x1 x2) (Ψ k x1 x2)) →
  IntoLaterN false n ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2)
    ([∗ list] k ↦ y1;y2 ∈ l1;l2, Ψ k y1 y2).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite -big_sepL2_laterN_2. by apply big_sepL2_mono.
Qed.
Global Instance into_laterN_big_sepM n `{Countable K} {A}
    (Φ Ψ : K → A → PROP) (m : gmap K A) :
  (∀ x k, IntoLaterN false n (Φ k x) (Ψ k x)) →
  IntoLaterN false n ([∗ map] k ↦ x ∈ m, Φ k x) ([∗ map] k ↦ x ∈ m, Ψ k x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opM_commute. by apply big_sepM_mono.
Qed.
Global Instance into_laterN_big_sepM2 n `{Countable K} {A B}
    (Φ Ψ : K → A → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
  (∀ x1 x2 k, IntoLaterN false n (Φ k x1 x2) (Ψ k x1 x2)) →
  IntoLaterN false n ([∗ map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2) ([∗ map] k ↦ x1;x2 ∈ m1;m2, Ψ k x1 x2).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> HΦΨ.
  rewrite -big_sepM2_laterN_2. by apply big_sepM2_mono.
Qed.
Global Instance into_laterN_big_sepS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gset A) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n ([∗ set] x ∈ X, Φ x) ([∗ set] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opS_commute. by apply big_sepS_mono.
Qed.
Global Instance into_laterN_big_sepMS n `{Countable A}
    (Φ Ψ : A → PROP) (X : gmultiset A) :
  (∀ x, IntoLaterN false n (Φ x) (Ψ x)) →
  IntoLaterN false n ([∗ mset] x ∈ X, Φ x) ([∗ mset] x ∈ X, Ψ x).
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN=> ?.
  rewrite big_opMS_commute. by apply big_sepMS_mono.
Qed.
End class_instances_later.
