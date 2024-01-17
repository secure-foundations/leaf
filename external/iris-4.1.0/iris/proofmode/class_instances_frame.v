From iris.bi Require Import telescopes.
From iris.proofmode Require Import classes classes_make.
From iris.prelude Require Import options.
Import bi.

(** This file defines the instances that make up the framing machinery. *)

Section class_instances_frame.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

(** When framing [R] against itself, we leave [True] if possible (via
[frame_here_absorbing] or [frame_affinely_here_absorbing]) since it is a weaker
goal. Otherwise we leave [emp] via [frame_here].
Only if all those options fail, we start decomposing [R], via instances like
[frame_exist]. To ensure that, all other instances must have cost > 1. *)
Global Instance frame_here_absorbing p R : Absorbing R → Frame p R R True | 0.
Proof. intros. by rewrite /Frame intuitionistically_if_elim sep_elim_l. Qed.
Global Instance frame_here p R : Frame p R R emp | 1.
Proof. intros. by rewrite /Frame intuitionistically_if_elim sep_elim_l. Qed.
Global Instance frame_affinely_here_absorbing p R :
  Absorbing R → Frame p (<affine> R) R True | 0.
Proof.
  intros. rewrite /Frame intuitionistically_if_elim affinely_elim.
  apply sep_elim_l, _.
Qed.
Global Instance frame_affinely_here p R : Frame p (<affine> R) R emp | 1.
Proof.
  intros. rewrite /Frame intuitionistically_if_elim affinely_elim.
  apply sep_elim_l, _.
Qed.

Global Instance frame_here_pure_persistent a φ Q :
  FromPure a Q φ → Frame true ⌜φ⌝ Q emp | 2.
Proof.
  rewrite /FromPure /Frame /= => <-. rewrite right_id.
  by rewrite -affinely_affinely_if intuitionistically_affinely.
Qed.
Global Instance frame_here_pure a φ Q :
  FromPure a Q φ →
  TCOr (TCEq a false) (BiAffine PROP) →
  Frame false ⌜φ⌝ Q emp | 2. (* Same cost as default. *)
Proof.
  rewrite /FromPure /Frame => <- [->|?] /=.
  - by rewrite right_id.
  - by rewrite right_id -affinely_affinely_if affine_affinely.
Qed.

Global Instance frame_embed `{!BiEmbed PROP PROP'} p P Q (Q' : PROP') R :
  Frame p R P Q → MakeEmbed Q Q' →
  Frame p ⎡R⎤ ⎡P⎤ Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakeEmbed => <- <-.
  rewrite embed_sep embed_intuitionistically_if_2 => //.
Qed.
Global Instance frame_pure_embed `{!BiEmbed PROP PROP'} p P Q (Q' : PROP') φ :
  Frame p ⌜φ⌝ P Q → MakeEmbed Q Q' →
  Frame p ⌜φ⌝ ⎡P⎤ Q' | 2. (* Same cost as default. *)
Proof. rewrite /Frame /MakeEmbed -embed_pure. apply (frame_embed p P Q). Qed.

Global Instance frame_sep_persistent_l progress R P1 P2 Q1 Q2 Q' :
  Frame true R P1 Q1 → MaybeFrame true R P2 Q2 progress → MakeSep Q1 Q2 Q' →
  Frame true R (P1 ∗ P2) Q' | 9.
Proof.
  rewrite /Frame /MaybeFrame /MakeSep /= => <- <- <-.
  rewrite {1}(intuitionistically_sep_dup R).
  by rewrite !assoc -(assoc _ _ _ Q1) -(comm _ Q1) assoc -(comm _ Q1).
Qed.
Global Instance frame_sep_l R P1 P2 Q Q' :
  Frame false R P1 Q → MakeSep Q P2 Q' → Frame false R (P1 ∗ P2) Q' | 9.
Proof. rewrite /Frame /MakeSep => <- <-. by rewrite assoc. Qed.
Global Instance frame_sep_r p R P1 P2 Q Q' :
  Frame p R P2 Q → MakeSep P1 Q Q' → Frame p R (P1 ∗ P2) Q' | 10.
Proof.
  rewrite /Frame /MakeSep => <- <-. by rewrite assoc -(comm _ P1) assoc.
Qed.

Global Instance frame_big_sepL_cons {A} p (Φ : nat → A → PROP) R Q l x l' :
  IsCons l x l' →
  Frame p R (Φ 0 x ∗ [∗ list] k ↦ y ∈ l', Φ (S k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q | 2. (* Same cost as default. *)
Proof. rewrite /IsCons=>->. by rewrite /Frame big_sepL_cons. Qed.
Global Instance frame_big_sepL_app {A} p (Φ : nat → A → PROP) R Q l l1 l2 :
  IsApp l l1 l2 →
  Frame p R (([∗ list] k ↦ y ∈ l1, Φ k y) ∗
           [∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q | 2. (* Same cost as default. *)
Proof. rewrite /IsApp=>->. by rewrite /Frame big_sepL_app. Qed.

Global Instance frame_big_sepL2_cons {A B} p (Φ : nat → A → B → PROP)
    R Q l1 x1 l1' l2 x2 l2' :
  IsCons l1 x1 l1' → IsCons l2 x2 l2' →
  Frame p R (Φ 0 x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ l1';l2', Φ (S k) y1 y2) Q →
  Frame p R ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) Q. (* Default cost > 1. *)
Proof. rewrite /IsCons=>-> ->. by rewrite /Frame big_sepL2_cons. Qed.
Global Instance frame_big_sepL2_app {A B} p (Φ : nat → A → B → PROP)
    R Q l1 l1' l1'' l2 l2' l2'' :
  IsApp l1 l1' l1'' → IsApp l2 l2' l2'' →
  Frame p R (([∗ list] k ↦ y1;y2 ∈ l1';l2', Φ k y1 y2) ∗
           [∗ list] k ↦ y1;y2 ∈ l1'';l2'', Φ (length l1' + k) y1 y2) Q →
  Frame p R ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) Q.
Proof. rewrite /IsApp /Frame=>-> -> ->. apply wand_elim_l', big_sepL2_app. Qed.

Global Instance frame_big_sepMS_disj_union `{Countable A} p (Φ : A → PROP) R Q X1 X2 :
  Frame p R (([∗ mset] y ∈ X1, Φ y) ∗ [∗ mset] y ∈ X2, Φ y) Q →
  Frame p R ([∗ mset] y ∈ X1 ⊎ X2, Φ y) Q | 2.
Proof. by rewrite /Frame big_sepMS_disj_union. Qed.

(* For framing below [∧], we can frame [R] away in *both* conjuncts
(unlike with [∗] where we can only frame it in one conjunct).
We require at least one of those to make progress though. *)
Global Instance frame_and p progress1 progress2 R P1 P2 Q1 Q2 Q' :
  MaybeFrame p R P1 Q1 progress1 →
  MaybeFrame p R P2 Q2 progress2 →
  TCEq (progress1 || progress2) true →
  MakeAnd Q1 Q2 Q' →
  Frame p R (P1 ∧ P2) Q' | 9.
Proof.
  rewrite /MaybeFrame /Frame /MakeAnd => <- <- _ <-.
  apply and_intro; [rewrite and_elim_l|rewrite and_elim_r]; done.
Qed.

(** We could in principle write the instance [frame_or_spatial] by a bunch of
instances (omitting the parameter [p = false]):

  Frame R P1 Q1 → Frame R P2 Q2 → Frame R (P1 ∨ P2) (Q1 ∨ Q2)
  Frame R P1 True → Frame R (P1 ∨ P2) P2
  Frame R P2 True → Frame R (P1 ∨ P2) P1

The problem here is that Coq will try to infer [Frame R P1 ?] and [Frame R P2 ?]
multiple times, whereas the current solution makes sure that said inference
appears at most once.

If Coq would memorize the results of type class resolution, the solution with
multiple instances would be preferred (and more Prolog-like). *)

Global Instance frame_or_spatial progress1 progress2 R P1 P2 Q1 Q2 Q :
  MaybeFrame false R P1 Q1 progress1 → MaybeFrame false R P2 Q2 progress2 →
  TCOr (TCEq (progress1 && progress2) true) (TCOr
    (TCAnd (TCEq progress1 true) (TCEq Q1 True%I))
    (TCAnd (TCEq progress2 true) (TCEq Q2 True%I))) →
  MakeOr Q1 Q2 Q →
  Frame false R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => <- <- _ <-. by rewrite -sep_or_l. Qed.

Global Instance frame_or_persistent progress1 progress2 R P1 P2 Q1 Q2 Q :
  MaybeFrame true R P1 Q1 progress1 → MaybeFrame true R P2 Q2 progress2 →
  TCEq (progress1 || progress2) true →
  MakeOr Q1 Q2 Q → Frame true R (P1 ∨ P2) Q | 9.
Proof. rewrite /Frame /MakeOr => <- <- _ <-. by rewrite -sep_or_l. Qed.

Global Instance frame_wand p R P1 P2 Q2 :
  Frame p R P2 Q2 → Frame p R (P1 -∗ P2) (P1 -∗ Q2) | 2.
Proof.
  rewrite /Frame=> ?. apply wand_intro_l.
  by rewrite assoc (comm _ P1) -assoc wand_elim_r.
Qed.

Global Instance frame_affinely p R P Q Q' :
  TCOr (TCEq p true) (Affine R) →
  Frame p R P Q → MakeAffinely Q Q' →
  Frame p R (<affine> P) Q'. (* Default cost > 1 *)
Proof.
  rewrite /Frame /MakeAffinely=> -[->|?] <- <- /=;
    by rewrite -{1}(affine_affinely (_ R)) affinely_sep_2.
Qed.

Global Instance frame_intuitionistically R P Q Q' :
  Frame true R P Q → MakeIntuitionistically Q Q' →
  Frame true R (□ P) Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakeIntuitionistically=> <- <- /=.
  rewrite -intuitionistically_sep_2 intuitionistically_idemp //.
Qed.

Global Instance frame_absorbingly p R P Q Q' :
  Frame p R P Q → MakeAbsorbingly Q Q' →
  Frame p R (<absorb> P) Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakeAbsorbingly=> <- <- /=. by rewrite absorbingly_sep_r.
Qed.

Global Instance frame_persistently R P Q Q' :
  Frame true R P Q → MakePersistently Q Q' →
  Frame true R (<pers> P) Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakePersistently=> <- <- /=.
  rewrite -persistently_and_intuitionistically_sep_l.
  by rewrite -persistently_sep_2 -persistently_and_sep_l_1
    persistently_affinely_elim persistently_idemp.
Qed.

Global Instance frame_exist {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∃ x, Φ x) (∃ x, Ψ x) | 2.
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_texist {TT : tele} p R (Φ Ψ : TT → PROP) :
  (∀ x, Frame p R (Φ x) (Ψ x)) → Frame p R (∃.. x, Φ x) (∃.. x, Ψ x) | 2.
Proof. rewrite /Frame !bi_texist_exist. apply frame_exist. Qed.
Global Instance frame_forall {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∀ x, Φ x) (∀ x, Ψ x) | 2.
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.
Global Instance frame_tforall {TT : tele} p R (Φ Ψ : TT → PROP) :
  (∀ x, Frame p R (Φ x) (Ψ x)) → Frame p R (∀.. x, Φ x) (∀.. x, Ψ x) | 2.
Proof. rewrite /Frame !bi_tforall_forall. apply frame_forall. Qed.

Global Instance frame_impl_persistent R P1 P2 Q2 :
  Frame true R P2 Q2 → Frame true R (P1 → P2) (P1 → Q2) | 2.
Proof.
  rewrite /Frame /= => ?. apply impl_intro_l.
  by rewrite -persistently_and_intuitionistically_sep_l assoc (comm _ P1) -assoc impl_elim_r
             persistently_and_intuitionistically_sep_l.
Qed.
Global Instance frame_impl R P1 P2 Q2 :
  Persistent P1 → Absorbing P1 →
  Frame false R P2 Q2 → Frame false R (P1 → P2) (P1 → Q2). (* Default cost > 1 *)
Proof.
  rewrite /Frame /==> ???. apply impl_intro_l.
  rewrite {1}(persistent P1) persistently_and_intuitionistically_sep_l assoc.
  rewrite (comm _ (□ P1)%I) -assoc -persistently_and_intuitionistically_sep_l.
  rewrite persistently_elim impl_elim_r //.
Qed.

Global Instance frame_eq_embed `{!BiEmbed PROP PROP', !BiInternalEq PROP,
    !BiInternalEq PROP', !BiEmbedInternalEq PROP PROP'}
    p P Q (Q' : PROP') {A : ofe} (a b : A) :
  Frame p (a ≡ b) P Q → MakeEmbed Q Q' →
  Frame p (a ≡ b) ⎡P⎤ Q'. (* Default cost > 1 *)
Proof. rewrite /Frame /MakeEmbed -embed_internal_eq. apply (frame_embed p P Q). Qed.

Global Instance frame_later p R R' P Q Q' :
  TCNoBackTrack (MaybeIntoLaterN true 1 R' R) →
  Frame p R P Q → MakeLaterN 1 Q Q' →
  Frame p R' (▷ P) Q'. (* Default cost > 1 *)
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite later_intuitionistically_if_2 later_sep.
Qed.
Global Instance frame_laterN p n R R' P Q Q' :
  TCNoBackTrack (MaybeIntoLaterN true n R' R) →
  Frame p R P Q → MakeLaterN n Q Q' →
  Frame p R' (▷^n P) Q'. (* Default cost > 1 *)
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite laterN_intuitionistically_if_2 laterN_sep.
Qed.

Global Instance frame_bupd `{!BiBUpd PROP} p R P Q :
  Frame p R P Q → Frame p R (|==> P) (|==> Q) | 2.
Proof. rewrite /Frame=><-. by rewrite bupd_frame_l. Qed.
Global Instance frame_fupd `{!BiFUpd PROP} p E1 E2 R P Q :
  Frame p R P Q → Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q) | 2.
Proof. rewrite /Frame=><-. by rewrite fupd_frame_l. Qed.

Global Instance frame_except_0 p R P Q Q' :
  Frame p R P Q → MakeExcept0 Q Q' →
  Frame p R (◇ P) Q' | 2. (* Same cost as default *)
Proof.
  rewrite /Frame /MakeExcept0=><- <-.
  by rewrite except_0_sep -(except_0_intro (□?p R)).
Qed.
End class_instances_frame.
