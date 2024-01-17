(** IMPORTANT: Read the comment in [classes_make] about the "constant time"
requirements of these instances. *)
From iris.proofmode Require Export classes_make.
From iris.prelude Require Import options.
Import bi.

Section class_instances_make.
Context {PROP : bi}.
Implicit Types P Q R : PROP.

(** Affine *)
Global Instance bi_affine_quick_affine P : BiAffine PROP → QuickAffine P.
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance False_quick_affine : @QuickAffine PROP False.
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance emp_quick_affine : @QuickAffine PROP emp.
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance affinely_quick_affine P : QuickAffine (<affine> P).
Proof. rewrite /QuickAffine. apply _. Qed.
Global Instance intuitionistically_quick_affine P : QuickAffine (□ P).
Proof. rewrite /QuickAffine. apply _. Qed.

(** Absorbing *)
Global Instance bi_affine_quick_absorbing P : BiAffine PROP → QuickAbsorbing P.
Proof. rewrite /QuickAbsorbing. apply _. Qed.
Global Instance pure_quick_absorbing φ : @QuickAbsorbing PROP ⌜ φ ⌝.
Proof. rewrite /QuickAbsorbing. apply _. Qed.
Global Instance absorbingly_quick_absorbing P : QuickAbsorbing (<absorb> P).
Proof. rewrite /QuickAbsorbing. apply _. Qed.
Global Instance persistently_quick_absorbing P : QuickAbsorbing (<pers> P).
Proof. rewrite /QuickAbsorbing. apply _. Qed.

(** Embed *)
Global Instance make_embed_pure {PROP'} `{!BiEmbed PROP PROP'} φ :
  KnownMakeEmbed (PROP:=PROP) ⌜φ⌝ ⌜φ⌝.
Proof. apply embed_pure. Qed.
Global Instance make_embed_emp {PROP'} `{!BiEmbed PROP PROP'} `{!BiEmbedEmp PROP PROP'} :
  KnownMakeEmbed (PROP:=PROP) emp emp.
Proof. apply embed_emp. Qed.
Global Instance make_embed_default {PROP'} `{!BiEmbed PROP PROP'} P :
  MakeEmbed P ⎡P⎤ | 100.
Proof. by rewrite /MakeEmbed. Qed.

(** Sep *)
Global Instance make_sep_emp_l P : KnownLMakeSep emp P P.
Proof. apply left_id, _. Qed.
Global Instance make_sep_emp_r P : KnownRMakeSep P emp P.
Proof. apply right_id, _. Qed.
Global Instance make_sep_true_l P : QuickAbsorbing P → KnownLMakeSep True P P.
Proof. rewrite /QuickAbsorbing /KnownLMakeSep /MakeSep=> ?. by apply True_sep. Qed.
Global Instance make_sep_true_r P : QuickAbsorbing P →  KnownRMakeSep P True P.
Proof. rewrite /QuickAbsorbing /KnownLMakeSep /MakeSep=> ?. by apply sep_True. Qed.
Global Instance make_sep_default P Q : MakeSep P Q (P ∗ Q) | 100.
Proof. by rewrite /MakeSep. Qed.

(** And *)
Global Instance make_and_true_l P : KnownLMakeAnd True P P.
Proof. apply left_id, _. Qed.
Global Instance make_and_true_r P : KnownRMakeAnd P True P.
Proof. by rewrite /KnownRMakeAnd /MakeAnd right_id. Qed.
Global Instance make_and_emp_l P : QuickAffine P → KnownLMakeAnd emp P P.
Proof. apply emp_and. Qed.
Global Instance make_and_emp_r P : QuickAffine P → KnownRMakeAnd P emp P.
Proof. apply and_emp. Qed.
Global Instance make_and_false_l P : KnownLMakeAnd False P False.
Proof. apply left_absorb, _. Qed.
Global Instance make_and_false_r P : KnownRMakeAnd P False False.
Proof. by rewrite /KnownRMakeAnd /MakeAnd right_absorb. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rewrite /MakeAnd. Qed.

(** Or *)
Global Instance make_or_true_l P : KnownLMakeOr True P True.
Proof. apply left_absorb, _. Qed.
Global Instance make_or_true_r P : KnownRMakeOr P True True.
Proof. by rewrite /KnownRMakeOr /MakeOr right_absorb. Qed.
Global Instance make_or_emp_l P : QuickAffine P → KnownLMakeOr emp P emp.
Proof. apply emp_or. Qed.
Global Instance make_or_emp_r P : QuickAffine P → KnownRMakeOr P emp emp.
Proof. apply or_emp. Qed.
Global Instance make_or_false_l P : KnownLMakeOr False P P.
Proof. apply left_id, _. Qed.
Global Instance make_or_false_r P : KnownRMakeOr P False P.
Proof. by rewrite /KnownRMakeOr /MakeOr right_id. Qed.
Global Instance make_or_default P Q : MakeOr P Q (P ∨ Q) | 100.
Proof. by rewrite /MakeOr. Qed.

(** Affinely

- [make_affinely_affine] adds no modality, but only if the argument is affine.
- [make_affinely_True] turns [True] into [emp]. For an affine BI this instance
  overlaps with [make_affinely_affine], since [True] is affine. Since we prefer
  to avoid [emp] in goals involving affine BIs, we give [make_affinely_affine]
  a lower cost than [make_affinely_True].
- [make_affinely_default] adds the modality. This is the default instance since
  it can always be used, and thus has the highest cost.
  (For this last point, the cost of the [KnownMakeAffinely] instances does not
  actually matter, since this is a [MakeAffinely] instance, i.e. an instance of
  a different class. What really matters is that the [known_make_affinely]
  instance has a lower cost than [make_affinely_default].) *)

Global Instance make_affinely_affine P :
  QuickAffine P → KnownMakeAffinely P P | 0.
Proof. apply affine_affinely. Qed.
Global Instance make_affinely_True : @KnownMakeAffinely PROP True emp | 1.
Proof. by rewrite /KnownMakeAffinely /MakeAffinely affinely_True_emp. Qed.
Global Instance make_affinely_default P : MakeAffinely P (<affine> P) | 100.
Proof. by rewrite /MakeAffinely. Qed.

(** Absorbingly

- [make_absorbingly_absorbing] adds no modality, but only if the argument is
  absorbing.
- [make_absorbingly_emp] turns [emp] into [True]. For an affine BI this instance
  overlaps with [make_absorbingly_absorbing], since [emp] is absorbing. For
  consistency, we give this instance the same cost as [make_affinely_True], but
  it does not really matter since goals in affine BIs typically do not contain
  occurrences of [emp] to start with.
- [make_absorbingly_default] adds the modality. This is the default instance
  since it can always be used, and thus has the highest cost.
  (For this last point, the cost of the [KnownMakeAbsorbingly] instances does not
  actually matter, since this is a [MakeAbsorbingly] instance, i.e. an instance of
  a different class. What really matters is that the [known_make_absorbingly]
  instance has a lower cost than [make_absorbingly_default].) *)

Global Instance make_absorbingly_absorbing P :
  QuickAbsorbing P → KnownMakeAbsorbingly P P | 0.
Proof. apply absorbing_absorbingly. Qed.
Global Instance make_absorbingly_emp : @KnownMakeAbsorbingly PROP emp True | 1.
Proof.
  by rewrite /KnownMakeAbsorbingly /MakeAbsorbingly -absorbingly_emp_True.
Qed.
Global Instance make_absorbingly_default P : MakeAbsorbingly P (<absorb> P) | 100.
Proof. by rewrite /MakeAbsorbingly. Qed.

(** Persistently *)
Global Instance make_persistently_emp :
  @KnownMakePersistently PROP emp True | 0.
Proof.
  by rewrite /KnownMakePersistently /MakePersistently
     -persistently_True_emp persistently_pure.
Qed.
Global Instance make_persistently_True :
  @KnownMakePersistently PROP True True | 0.
Proof. by rewrite /KnownMakePersistently /MakePersistently persistently_pure. Qed.
Global Instance make_persistently_default P :
  MakePersistently P (<pers> P) | 100.
Proof. by rewrite /MakePersistently. Qed.

(** Intuitionistically *)
Global Instance make_intuitionistically_emp :
  @KnownMakeIntuitionistically PROP emp emp | 0.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_emp.
Qed.
(** For affine BIs, we would prefer [□ True] to become [True] rather than [emp],
so we have this instance with lower cost than the next. *)
Global Instance make_intuitionistically_True_affine :
  BiAffine PROP →
  @KnownMakeIntuitionistically PROP True True | 0.
Proof.
  intros. rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_True_emp True_emp //.
Qed.
Global Instance make_intuitionistically_True :
  @KnownMakeIntuitionistically PROP True emp | 1.
Proof.
  by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
    intuitionistically_True_emp.
Qed.
Global Instance make_intuitionistically_default P :
  MakeIntuitionistically P (□ P) | 100.
Proof. by rewrite /MakeIntuitionistically. Qed.

(** Later *)
Global Instance make_laterN_true n : @KnownMakeLaterN PROP n True True | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_True. Qed.
Global Instance make_laterN_emp `{!BiAffine PROP} n :
  @KnownMakeLaterN PROP n emp emp | 0.
Proof. by rewrite /KnownMakeLaterN /MakeLaterN laterN_emp. Qed.
Global Instance make_laterN_default n P : MakeLaterN n P (▷^n P) | 100.
Proof. by rewrite /MakeLaterN. Qed.

(** Except-0 *)
Global Instance make_except_0_True : @KnownMakeExcept0 PROP True True.
Proof. by rewrite /KnownMakeExcept0 /MakeExcept0 except_0_True. Qed.
Global Instance make_except_0_default P : MakeExcept0 P (◇ P) | 100.
Proof. by rewrite /MakeExcept0. Qed.
End class_instances_make.
