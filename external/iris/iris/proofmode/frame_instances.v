From stdpp Require Import nat_cancel.
From iris.bi Require Import bi telescopes.
From iris.proofmode Require Import classes.
From iris.prelude Require Import options.
Import bi.

(** This file defines the instances that make up the framing machinery. *)

(** When framing below logical connectives/modalities, framing will perform
some "clean up" to remove connectives/modalities if the result of framing is
[True] or [emp]. For example, framing [P] in [P ∗ Q] or [<affine> P] will
result in [Q] and [emp], respectively, instead of [emp ∗ Q] and [<affine> emp],
respectively. One could imagine a smarter way of cleaning up, as implemented in
https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/450 for some modalities,
but that makes framing less predictable and might have some performance impact.
Hence, we only perform such cleanup for [True] and [emp]. *)

Section bi.
Context {PROP : bi}.
Implicit Types P Q R : PROP.
(* Frame *)
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
  FromPure a Q φ → Frame true ⌜φ⌝ Q emp.
Proof.
  rewrite /FromPure /Frame /= => <-. rewrite right_id.
  by rewrite -affinely_affinely_if intuitionistically_affinely.
Qed.
Global Instance frame_here_pure a φ Q :
  FromPure a Q φ →
  TCOr (TCEq a false) (BiAffine PROP) →
  Frame false ⌜φ⌝ Q emp.
Proof.
  rewrite /FromPure /Frame => <- [->|?] /=.
  - by rewrite right_id.
  - by rewrite right_id -affinely_affinely_if affine_affinely.
Qed.

Global Instance make_embed_pure `{BiEmbed PROP PROP'} φ :
  KnownMakeEmbed (PROP:=PROP) ⌜φ⌝ ⌜φ⌝.
Proof. apply embed_pure. Qed.
Global Instance make_embed_emp `{BiEmbedEmp PROP PROP'} :
  KnownMakeEmbed (PROP:=PROP) emp emp.
Proof. apply embed_emp. Qed.
Global Instance make_embed_default `{BiEmbed PROP PROP'} P :
  MakeEmbed P ⎡P⎤ | 100.
Proof. by rewrite /MakeEmbed. Qed.

Global Instance frame_embed `{BiEmbed PROP PROP'} p P Q (Q' : PROP') R :
  Frame p R P Q → MakeEmbed Q Q' → Frame p ⎡R⎤ ⎡P⎤ Q'.
Proof.
  rewrite /Frame /MakeEmbed => <- <-.
  rewrite embed_sep embed_intuitionistically_if_2 => //.
Qed.
Global Instance frame_pure_embed `{BiEmbed PROP PROP'} p P Q (Q' : PROP') φ :
  Frame p ⌜φ⌝ P Q → MakeEmbed Q Q' → Frame p ⌜φ⌝ ⎡P⎤ Q'.
Proof. rewrite /Frame /MakeEmbed -embed_pure. apply (frame_embed p P Q). Qed.

Global Instance make_sep_emp_l P : KnownLMakeSep emp P P.
Proof. apply left_id, _. Qed.
Global Instance make_sep_emp_r P : KnownRMakeSep P emp P.
Proof. apply right_id, _. Qed.
Global Instance make_sep_true_l P : Absorbing P → KnownLMakeSep True P P.
Proof. intros. apply True_sep, _. Qed.
Global Instance make_sep_true_r P : Absorbing P → KnownRMakeSep P True P.
Proof. intros. by rewrite /KnownRMakeSep /MakeSep sep_True. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ∗ Q) | 100.
Proof. by rewrite /MakeSep. Qed.

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
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsCons=>->. by rewrite /Frame big_sepL_cons. Qed.
Global Instance frame_big_sepL_app {A} p (Φ : nat → A → PROP) R Q l l1 l2 :
  IsApp l l1 l2 →
  Frame p R (([∗ list] k ↦ y ∈ l1, Φ k y) ∗
           [∗ list] k ↦ y ∈ l2, Φ (length l1 + k) y) Q →
  Frame p R ([∗ list] k ↦ y ∈ l, Φ k y) Q.
Proof. rewrite /IsApp=>->. by rewrite /Frame big_sepL_app. Qed.

Global Instance frame_big_sepL2_cons {A B} p (Φ : nat → A → B → PROP)
    R Q l1 x1 l1' l2 x2 l2' :
  IsCons l1 x1 l1' → IsCons l2 x2 l2' →
  Frame p R (Φ 0 x1 x2 ∗ [∗ list] k ↦ y1;y2 ∈ l1';l2', Φ (S k) y1 y2) Q →
  Frame p R ([∗ list] k ↦ y1;y2 ∈ l1;l2, Φ k y1 y2) Q.
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
  Frame p R ([∗ mset] y ∈ X1 ⊎ X2, Φ y) Q.
Proof. by rewrite /Frame big_sepMS_disj_union. Qed.

Global Instance make_and_true_l P : KnownLMakeAnd True P P.
Proof. apply left_id, _. Qed.
Global Instance make_and_true_r P : KnownRMakeAnd P True P.
Proof. by rewrite /KnownRMakeAnd /MakeAnd right_id. Qed.
Global Instance make_and_emp_l P : Affine P → KnownLMakeAnd emp P P.
Proof. intros. by rewrite /KnownLMakeAnd /MakeAnd emp_and. Qed.
Global Instance make_and_emp_r P : Affine P → KnownRMakeAnd P emp P.
Proof. intros. by rewrite /KnownRMakeAnd /MakeAnd and_emp. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rewrite /MakeAnd. Qed.

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

Global Instance make_or_true_l P : KnownLMakeOr True P True.
Proof. apply left_absorb, _. Qed.
Global Instance make_or_true_r P : KnownRMakeOr P True True.
Proof. by rewrite /KnownRMakeOr /MakeOr right_absorb. Qed.
Global Instance make_or_emp_l P : Affine P → KnownLMakeOr emp P emp.
Proof. intros. by rewrite /KnownLMakeOr /MakeOr emp_or. Qed.
Global Instance make_or_emp_r P : Affine P → KnownRMakeOr P emp emp.
Proof. intros. by rewrite /KnownRMakeOr /MakeOr or_emp. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. by rewrite /MakeOr. Qed.

(* We could in principle write the instance [frame_or_spatial] by a bunch of
instances, i.e. (omitting the parameter [p = false]):

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
  Frame p R P2 Q2 → Frame p R (P1 -∗ P2) (P1 -∗ Q2).
Proof.
  rewrite /Frame=> ?. apply wand_intro_l.
  by rewrite assoc (comm _ P1) -assoc wand_elim_r.
Qed.

Global Instance make_affinely_emp : @KnownMakeAffinely PROP emp emp | 0.
Proof. by rewrite /KnownMakeAffinely /MakeAffinely affinely_emp. Qed.
Global Instance make_affinely_True : @KnownMakeAffinely PROP True emp | 0.
Proof. by rewrite /KnownMakeAffinely /MakeAffinely affinely_True_emp affinely_emp. Qed.
Global Instance make_affinely_default P : MakeAffinely P (<affine> P) | 100.
Proof. by rewrite /MakeAffinely. Qed.

Global Instance frame_affinely p R P Q Q' :
  TCOr (TCEq p true) (Affine R) →
  Frame p R P Q → MakeAffinely Q Q' → Frame p R (<affine> P) Q'.
Proof.
  rewrite /Frame /MakeAffinely=> -[->|?] <- <- /=;
    by rewrite -{1}(affine_affinely (_ R)) affinely_sep_2.
Qed.

Global Instance make_intuitionistically_emp :
  @KnownMakeIntuitionistically PROP emp emp | 0.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_emp.
Qed.
Global Instance make_intuitionistically_True :
  @KnownMakeIntuitionistically PROP True emp | 0.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_True_emp.
Qed.
Global Instance make_intuitionistically_default P :
  MakeIntuitionistically P (□ P) | 100.
Proof. by rewrite /MakeIntuitionistically. Qed.

Global Instance frame_intuitionistically R P Q Q' :
  Frame true R P Q → MakeIntuitionistically Q Q' → Frame true R (□ P) Q'.
Proof.
  rewrite /Frame /MakeIntuitionistically=> <- <- /=.
  rewrite -intuitionistically_sep_2 intuitionistically_idemp //.
Qed.

Global Instance make_absorbingly_emp : @KnownMakeAbsorbingly PROP emp True | 0.
Proof.
  by rewrite /KnownMakeAbsorbingly /MakeAbsorbingly
     -absorbingly_True_emp absorbingly_pure.
Qed.
Global Instance make_absorbingly_True : @KnownMakeAbsorbingly PROP True True | 0.
Proof. by rewrite /KnownMakeAbsorbingly /MakeAbsorbingly absorbingly_pure. Qed.
Global Instance make_absorbingly_default P : MakeAbsorbingly P (<absorb> P) | 100.
Proof. by rewrite /MakeAbsorbingly. Qed.

Global Instance frame_absorbingly p R P Q Q' :
  Frame p R P Q → MakeAbsorbingly Q Q' → Frame p R (<absorb> P) Q'.
Proof.
  rewrite /Frame /MakeAbsorbingly=> <- <- /=. by rewrite absorbingly_sep_r.
Qed.

Global Instance make_persistently_emp : @KnownMakePersistently PROP emp True.
Proof.
  by rewrite /KnownMakePersistently /MakePersistently
     -persistently_True_emp persistently_pure.
Qed.
Global Instance make_persistently_True : @KnownMakePersistently PROP True True.
Proof. by rewrite /KnownMakePersistently /MakePersistently persistently_pure. Qed.
Global Instance make_persistently_default P :
  MakePersistently P (<pers> P) | 100.
Proof. by rewrite /MakePersistently. Qed.

Global Instance frame_persistently R P Q Q' :
  Frame true R P Q → MakePersistently Q Q' → Frame true R (<pers> P) Q'.
Proof.
  rewrite /Frame /MakePersistently=> <- <- /=.
  rewrite -persistently_and_intuitionistically_sep_l.
  by rewrite -persistently_sep_2 -persistently_and_sep_l_1
    persistently_affinely_elim persistently_idemp.
Qed.

Global Instance frame_exist {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∃ x, Φ x) (∃ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_exist_l; apply exist_mono. Qed.
Global Instance frame_texist {TT : tele} p R (Φ Ψ : TT → PROP) :
  (∀ x, Frame p R (Φ x) (Ψ x)) → Frame p R (∃.. x, Φ x) (∃.. x, Ψ x).
Proof. rewrite /Frame !bi_texist_exist. apply frame_exist. Qed.
Global Instance frame_forall {A} p R (Φ Ψ : A → PROP) :
  (∀ a, Frame p R (Φ a) (Ψ a)) → Frame p R (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /Frame=> ?. by rewrite sep_forall_l; apply forall_mono. Qed.
Global Instance frame_tforall {TT : tele} p R (Φ Ψ : TT → PROP) :
  (∀ x, Frame p R (Φ x) (Ψ x)) → Frame p R (∀.. x, Φ x) (∀.. x, Ψ x).
Proof. rewrite /Frame !bi_tforall_forall. apply frame_forall. Qed.

Global Instance frame_impl_persistent R P1 P2 Q2 :
  Frame true R P2 Q2 → Frame true R (P1 → P2) (P1 → Q2).
Proof.
  rewrite /Frame /= => ?. apply impl_intro_l.
  by rewrite -persistently_and_intuitionistically_sep_l assoc (comm _ P1) -assoc impl_elim_r
             persistently_and_intuitionistically_sep_l.
Qed.
Global Instance frame_impl R P1 P2 Q2 :
  Persistent P1 → Absorbing P1 →
  Frame false R P2 Q2 → Frame false R (P1 → P2) (P1 → Q2).
Proof.
  rewrite /Frame /==> ???. apply impl_intro_l.
  rewrite {1}(persistent P1) persistently_and_intuitionistically_sep_l assoc.
  rewrite (comm _ (□ P1)%I) -assoc -persistently_and_intuitionistically_sep_l.
  rewrite persistently_elim impl_elim_r //.
Qed.

Global Instance frame_eq_embed `{!BiEmbed PROP PROP', !BiInternalEq PROP,
    !BiInternalEq PROP', !BiEmbedInternalEq PROP PROP'}
    p P Q (Q' : PROP') {A : ofe} (a b : A) :
  Frame p (a ≡ b) P Q → MakeEmbed Q Q' → Frame p (a ≡ b) ⎡P⎤ Q'.
Proof. rewrite /Frame /MakeEmbed -embed_internal_eq. apply (frame_embed p P Q). Qed.

Global Instance make_laterN_true n : @KnownMakeLaterN PROP n True True | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_emp `{!BiAffine PROP} n :
  @KnownMakeLaterN PROP n emp emp | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_emp. Qed.
Global Instance make_laterN_default n P : MakeLaterN n P (▷^n P) | 100.
Proof. by rewrite /MakeLaterN. Qed.

Global Instance frame_later p R R' P Q Q' :
  TCNoBackTrack (MaybeIntoLaterN true 1 R' R) →
  Frame p R P Q → MakeLaterN 1 Q Q' → Frame p R' (▷ P) Q'.
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite later_intuitionistically_if_2 later_sep.
Qed.
Global Instance frame_laterN p n R R' P Q Q' :
  TCNoBackTrack (MaybeIntoLaterN true n R' R) →
  Frame p R P Q → MakeLaterN n Q Q' → Frame p R' (▷^n P) Q'.
Proof.
  rewrite /Frame /MakeLaterN /MaybeIntoLaterN=>-[->] <- <-.
  by rewrite laterN_intuitionistically_if_2 laterN_sep.
Qed.

Global Instance frame_bupd `{BiBUpd PROP} p R P Q :
  Frame p R P Q → Frame p R (|==> P) (|==> Q).
Proof. rewrite /Frame=><-. by rewrite bupd_frame_l. Qed.
Global Instance frame_fupd `{BiFUpd PROP} p E1 E2 R P Q :
  Frame p R P Q → Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q).
Proof. rewrite /Frame=><-. by rewrite fupd_frame_l. Qed.

Global Instance make_except_0_True : @KnownMakeExcept0 PROP True True.
Proof. by rewrite /KnownMakeExcept0 /MakeExcept0 except_0_True. Qed.
Global Instance make_except_0_default P : MakeExcept0 P (◇ P) | 100.
Proof. by rewrite /MakeExcept0. Qed.

Global Instance frame_except_0 p R P Q Q' :
  Frame p R P Q → MakeExcept0 Q Q' → Frame p R (◇ P) Q'.
Proof.
  rewrite /Frame /MakeExcept0=><- <-.
  by rewrite except_0_sep -(except_0_intro (□?p R)).
Qed.
End bi.
