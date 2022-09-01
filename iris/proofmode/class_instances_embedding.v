From iris.bi Require Import bi.
From iris.proofmode Require Import modality_instances classes.
From iris.prelude Require Import options.
Import bi.

(** We add a useless hypothesis [BiEmbed PROP PROP'] in order to make sure this
instance is not used when there is no embedding between [PROP] and [PROP']. The
first [`{BiEmbed PROP PROP'}] is not considered as a premise by Coq TC search
mechanism because the rest of the hypothesis is dependent on it. *)
Global Instance as_emp_valid_embed `{!BiEmbed PROP PROP'} (φ : Prop) (P : PROP) :
  BiEmbed PROP PROP' →
  AsEmpValid0 φ P → AsEmpValid φ ⎡P⎤.
Proof. rewrite /AsEmpValid0 /AsEmpValid=> _ ->. rewrite embed_emp_valid //. Qed.

Section class_instances_embedding.
Context `{!BiEmbed PROP PROP'}.
Implicit Types P Q R : PROP.

Global Instance into_pure_embed P φ :
  IntoPure P φ → IntoPure ⎡P⎤ φ.
Proof. rewrite /IntoPure=> ->. by rewrite embed_pure. Qed.

Global Instance from_pure_embed a P φ :
  FromPure a P φ → FromPure a ⎡P⎤ φ.
Proof. rewrite /FromPure=> <-. by rewrite -embed_pure embed_affinely_if_2. Qed.

Global Instance into_persistent_embed p P Q :
  IntoPersistent p P Q → IntoPersistent p ⎡P⎤ ⎡Q⎤ | 0.
Proof.
  rewrite /IntoPersistent -embed_persistently -embed_persistently_if=> -> //.
Qed.

(* When having a modality nested in an embedding, e.g. [ ⎡|==> P⎤ ], we prefer
the embedding over the modality. *)
Global Instance from_modal_embed P :
  FromModal True (@modality_embed PROP PROP' _) ⎡P⎤ ⎡P⎤ P.
Proof. by rewrite /FromModal. Qed.

Global Instance from_modal_id_embed φ `(sel : A) P Q :
  FromModal φ modality_id sel P Q →
  FromModal φ modality_id sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ. Qed.

Global Instance from_modal_affinely_embed φ `(sel : A) P Q :
  FromModal φ modality_affinely sel P Q →
  FromModal φ modality_affinely sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // embed_affinely_2. Qed.
Global Instance from_modal_persistently_embed φ `(sel : A) P Q :
  FromModal φ modality_persistently sel P Q →
  FromModal φ modality_persistently sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // embed_persistently. Qed.
Global Instance from_modal_intuitionistically_embed φ `(sel : A) P Q :
  FromModal φ modality_intuitionistically sel P Q →
  FromModal φ modality_intuitionistically sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // embed_intuitionistically_2. Qed.

Global Instance into_wand_embed p q R P Q :
  IntoWand p q R P Q → IntoWand p q ⎡R⎤ ⎡P⎤ ⎡Q⎤.
Proof. by rewrite /IntoWand !embed_intuitionistically_if_2 -embed_wand=> ->. Qed.

(* There are two versions for [IntoWand ⎡R⎤ ...] with the argument being
[<affine> ⎡P⎤]. When the wand [⎡R⎤] resides in the intuitionistic context
the result of wand elimination will have the affine modality. Otherwise, it
won't. Note that when the wand [⎡R⎤] is under an affine modality, the instance
[into_wand_affine] would already have been used. *)
Global Instance into_wand_affine_embed_true q P Q R :
  IntoWand true q R P Q → IntoWand true q ⎡R⎤ (<affine> ⎡P⎤) (<affine> ⎡Q⎤) | 100.
Proof.
  rewrite /IntoWand /=.
  rewrite -(intuitionistically_idemp ⎡ _ ⎤) embed_intuitionistically_2=> ->.
  apply bi.wand_intro_l. destruct q; simpl.
  - rewrite affinely_elim  -(intuitionistically_idemp ⎡ _ ⎤).
    rewrite embed_intuitionistically_2 intuitionistically_sep_2 -embed_sep.
    by rewrite wand_elim_r intuitionistically_affinely.
  - by rewrite intuitionistically_affinely affinely_sep_2 -embed_sep wand_elim_r.
Qed.
Global Instance into_wand_affine_embed_false q P Q R :
  IntoWand false q R (<affine> P) Q →
  IntoWand false q ⎡R⎤ (<affine> ⎡P⎤) ⎡Q⎤ | 100.
Proof.
  rewrite /IntoWand /= => ->.
  by rewrite embed_affinely_2 embed_intuitionistically_if_2 embed_wand.
Qed.

Global Instance from_wand_embed P Q1 Q2 :
  FromWand P Q1 Q2 → FromWand ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromWand -embed_wand => <-. Qed.

Global Instance from_impl_embed P Q1 Q2 :
  FromImpl P Q1 Q2 → FromImpl ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromImpl -embed_impl => <-. Qed.

Global Instance from_and_embed P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromAnd -embed_and => <-. Qed.

Global Instance from_sep_embed P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromSep -embed_sep => <-. Qed.

Global Instance into_and_embed p P Q1 Q2 :
  IntoAnd p P Q1 Q2 → IntoAnd p ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof.
  rewrite /IntoAnd -embed_and=> HP. apply intuitionistically_if_intro'.
  by rewrite embed_intuitionistically_if_2 HP intuitionistically_if_elim.
Qed.

Global Instance into_sep_embed P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. rewrite /IntoSep -embed_sep=> -> //. Qed.

Global Instance from_or_embed P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /FromOr -embed_or => <-. Qed.

Global Instance into_or_embed P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr ⎡P⎤ ⎡Q1⎤ ⎡Q2⎤.
Proof. by rewrite /IntoOr -embed_or => <-. Qed.

Global Instance from_exist_embed {A} P (Φ : A → PROP) :
  FromExist P Φ → FromExist ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /FromExist -embed_exist => <-. Qed.

Global Instance into_exist_embed {A} P (Φ : A → PROP) name :
  IntoExist P Φ name → IntoExist ⎡P⎤ (λ a, ⎡Φ a⎤%I) name.
Proof. by rewrite /IntoExist -embed_exist => <-. Qed.

Global Instance into_forall_embed {A} P (Φ : A → PROP) :
  IntoForall P Φ → IntoForall ⎡P⎤ (λ a, ⎡Φ a⎤%I).
Proof. by rewrite /IntoForall -embed_forall => <-. Qed.

Global Instance from_forall_embed {A} P (Φ : A → PROP) name :
  FromForall P Φ name → FromForall ⎡P⎤ (λ a, ⎡Φ a⎤%I) name.
Proof. by rewrite /FromForall -embed_forall => <-. Qed.

Global Instance into_inv_embed P N : IntoInv P N → IntoInv ⎡P⎤ N := {}.

Global Instance is_except_0_embed `{!BiEmbedLater PROP PROP'} P :
  IsExcept0 P → IsExcept0 ⎡P⎤.
Proof. by rewrite /IsExcept0 -embed_except_0=>->. Qed.

Global Instance from_modal_later_embed `{!BiEmbedLater PROP PROP'} φ `(sel : A) n P Q :
  FromModal φ (modality_laterN n) sel P Q →
  FromModal φ (modality_laterN n) sel ⎡P⎤ ⎡Q⎤.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // embed_laterN. Qed.

Global Instance from_modal_plainly_embed
    `{!BiPlainly PROP, !BiPlainly PROP', !BiEmbedPlainly PROP PROP'} φ `(sel : A) P Q :
  FromModal φ modality_plainly sel P Q →
  FromModal φ (PROP2:=PROP') modality_plainly sel ⎡P⎤ ⎡Q⎤ | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // embed_plainly. Qed.

Global Instance into_internal_eq_embed
    `{!BiInternalEq PROP, !BiInternalEq PROP', !BiEmbedInternalEq PROP PROP'}
    {A : ofe} (x y : A) (P : PROP) :
  IntoInternalEq P x y → IntoInternalEq (⎡P⎤ : PROP')%I x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite embed_internal_eq. Qed.

Global Instance into_except_0_embed `{!BiEmbedLater PROP PROP'} P Q :
  IntoExcept0 P Q → IntoExcept0 ⎡P⎤ ⎡Q⎤.
Proof. rewrite /IntoExcept0=> ->. by rewrite embed_except_0. Qed.

Global Instance elim_modal_embed_bupd_goal
    `{!BiBUpd PROP, !BiBUpd PROP', !BiEmbedBUpd PROP PROP'}
    p p' φ (P P' : PROP') (Q Q' : PROP) :
  ElimModal φ p p' P P' (|==> ⎡Q⎤)%I (|==> ⎡Q'⎤)%I →
  ElimModal φ p p' P P' ⎡|==> Q⎤ ⎡|==> Q'⎤.
Proof. by rewrite /ElimModal !embed_bupd. Qed.
Global Instance elim_modal_embed_bupd_hyp
    `{!BiBUpd PROP, !BiBUpd PROP', !BiEmbedBUpd PROP PROP'}
    p p' φ (P : PROP) (P' Q Q' : PROP') :
  ElimModal φ p p' (|==> ⎡P⎤)%I P' Q Q' →
  ElimModal φ p p' ⎡|==> P⎤ P' Q Q'.
Proof. by rewrite /ElimModal !embed_bupd. Qed.

Global Instance elim_modal_embed_fupd_goal
    `{!BiFUpd PROP, !BiFUpd PROP', !BiEmbedFUpd PROP PROP'}
    p p' φ E1 E2 E3 (P P' : PROP') (Q Q' : PROP) :
  ElimModal φ p p' P P' (|={E1,E3}=> ⎡Q⎤)%I (|={E2,E3}=> ⎡Q'⎤)%I →
  ElimModal φ p p' P P' ⎡|={E1,E3}=> Q⎤ ⎡|={E2,E3}=> Q'⎤.
Proof. by rewrite /ElimModal !embed_fupd. Qed.
Global Instance elim_modal_embed_fupd_hyp
    `{!BiFUpd PROP, !BiFUpd PROP', !BiEmbedFUpd PROP PROP'}
    p p' φ E1 E2 (P : PROP) (P' Q Q' : PROP') :
  ElimModal φ p p' (|={E1,E2}=> ⎡P⎤)%I P' Q Q' →
  ElimModal φ p p' ⎡|={E1,E2}=> P⎤ P' Q Q'.
Proof. by rewrite /ElimModal embed_fupd. Qed.

Global Instance add_modal_embed_bupd_goal
    `{!BiBUpd PROP, !BiBUpd PROP', !BiEmbedBUpd PROP PROP'}
    (P P' : PROP') (Q : PROP) :
  AddModal P P' (|==> ⎡Q⎤)%I → AddModal P P' ⎡|==> Q⎤.
Proof. by rewrite /AddModal !embed_bupd. Qed.

Global Instance add_modal_embed_fupd_goal
    `{!BiFUpd PROP, !BiFUpd PROP', !BiEmbedFUpd PROP PROP'}
    E1 E2 (P P' : PROP') (Q : PROP) :
  AddModal P P' (|={E1,E2}=> ⎡Q⎤)%I → AddModal P P' ⎡|={E1,E2}=> Q⎤.
Proof. by rewrite /AddModal !embed_fupd. Qed.

Global Instance into_embed_embed P : IntoEmbed ⎡P⎤ P.
Proof. by rewrite /IntoEmbed. Qed.
Global Instance into_embed_affinely
    `{!BiBUpd PROP, !BiBUpd PROP', !BiEmbedBUpd PROP PROP'} (P : PROP') (Q : PROP) :
  IntoEmbed P Q → IntoEmbed (<affine> P) (<affine> Q).
Proof. rewrite /IntoEmbed=> ->. by rewrite embed_affinely_2. Qed.

Global Instance into_later_embed`{!BiEmbedLater PROP PROP'} n P Q :
  IntoLaterN false n P Q → IntoLaterN false n ⎡P⎤ ⎡Q⎤.
Proof. rewrite /IntoLaterN /MaybeIntoLaterN=> ->. by rewrite embed_laterN. Qed.
End class_instances_embedding.
