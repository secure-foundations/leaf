From iris.bi Require Import bi.
From iris.proofmode Require Export classes.
From iris.prelude Require Import options.
Import bi.

Section modalities.
  Context {PROP : bi}.

  Lemma modality_persistently_mixin :
    modality_mixin (@bi_persistently PROP) MIEnvId MIEnvClear.
  Proof.
    split; simpl; eauto using equiv_entails_1_2, persistently_intro,
      persistently_mono, persistently_sep_2 with typeclass_instances.
  Qed.
  Definition modality_persistently :=
    Modality _ modality_persistently_mixin.

  Lemma modality_affinely_mixin :
    modality_mixin (@bi_affinely PROP) MIEnvId (MIEnvForall Affine).
  Proof.
    split; simpl; eauto using equiv_entails_1_2, affinely_intro, affinely_mono,
      affinely_sep_2 with typeclass_instances.
  Qed.
  Definition modality_affinely :=
    Modality _ modality_affinely_mixin.

  Lemma modality_intuitionistically_mixin :
    modality_mixin (@bi_intuitionistically PROP) MIEnvId MIEnvIsEmpty.
  Proof.
    split; simpl; eauto using equiv_entails_1_2, intuitionistically_emp,
      affinely_mono, persistently_mono, intuitionistically_idemp,
      intuitionistically_sep_2 with typeclass_instances.
  Qed.
  Definition modality_intuitionistically :=
    Modality _ modality_intuitionistically_mixin.

  Lemma modality_embed_mixin `{BiEmbed PROP PROP'} :
    modality_mixin (@embed PROP PROP' _)
      (MIEnvTransform IntoEmbed) (MIEnvTransform IntoEmbed).
  Proof.
    split; simpl; split_and?;
      eauto using equiv_entails_1_2, embed_emp_2, embed_sep, embed_and.
    - intros P Q. rewrite /IntoEmbed=> ->. by rewrite embed_intuitionistically_2.
    - by intros P Q ->.
  Qed.
  Definition modality_embed `{BiEmbed PROP PROP'} :=
    Modality _ modality_embed_mixin.

  Lemma modality_plainly_mixin `{BiPlainly PROP} :
    modality_mixin (@plainly PROP _) (MIEnvForall Plain) MIEnvClear.
  Proof.
    split; simpl; split_and?; eauto using equiv_entails_1_2, plainly_intro,
      plainly_mono, plainly_and, plainly_sep_2 with typeclass_instances.
  Qed.
  Definition modality_plainly `{BiPlainly PROP} :=
    Modality _ modality_plainly_mixin.

  Lemma modality_laterN_mixin n :
    modality_mixin (@bi_laterN PROP n)
      (MIEnvTransform (MaybeIntoLaterN false n)) (MIEnvTransform (MaybeIntoLaterN false n)).
  Proof.
    split; simpl; split_and?; eauto using equiv_entails_1_2, laterN_intro,
      laterN_mono, laterN_and, laterN_sep with typeclass_instances.
    rewrite /MaybeIntoLaterN=> P Q ->. by rewrite laterN_intuitionistically_2.
  Qed.
  Definition modality_laterN n :=
    Modality _ (modality_laterN_mixin n).
End modalities.
