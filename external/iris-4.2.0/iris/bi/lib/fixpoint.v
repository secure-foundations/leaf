From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
Import bi.

(** Least and greatest fixpoint of a monotone function, defined entirely inside
    the logic.  *)
Class BiMonoPred {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) := {
  bi_mono_pred Φ Ψ :
    NonExpansive Φ →
    NonExpansive Ψ →
    □ (∀ x, Φ x -∗ Ψ x) -∗ ∀ x, F Φ x -∗ F Ψ x;
  bi_mono_pred_ne Φ : NonExpansive Φ → NonExpansive (F Φ)
}.
Global Arguments bi_mono_pred {_ _ _ _} _ _.
Local Existing Instance bi_mono_pred_ne.

Definition bi_least_fixpoint {PROP : bi} {A : ofe}
    (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  tc_opaque (∀ Φ : A -n> PROP, □ (∀ x, F Φ x -∗ Φ x) -∗ Φ x)%I.
Global Arguments bi_least_fixpoint : simpl never.

Definition bi_greatest_fixpoint {PROP : bi} {A : ofe}
    (F : (A → PROP) → (A → PROP)) (x : A) : PROP :=
  tc_opaque (∃ Φ : A -n> PROP, □ (∀ x, Φ x -∗ F Φ x) ∗ Φ x)%I.
Global Arguments bi_greatest_fixpoint : simpl never.

(* Both non-expansiveness lemmas do not seem to be interderivable.
  FIXME: is there some lemma that subsumes both? *)
Lemma least_fixpoint_ne' {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)):
  (∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) → NonExpansive (bi_least_fixpoint F).
Proof. solve_proper. Qed.
Global Instance least_fixpoint_ne {PROP : bi} {A : ofe} n :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (dist n)) ==>
          dist n ==> dist n) bi_least_fixpoint.
Proof. solve_proper. Qed.
Global Instance least_fixpoint_proper {PROP : bi} {A : ofe} :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (≡)) ==>
          (≡) ==> (≡)) bi_least_fixpoint.
Proof. solve_proper. Qed.

Section least.
  Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.

  Lemma least_fixpoint_unfold_2 x : F (bi_least_fixpoint F) x ⊢ bi_least_fixpoint F x.
  Proof using Type*.
    rewrite /bi_least_fixpoint /=. iIntros "HF" (Φ) "#Hincl".
    iApply "Hincl". iApply (bi_mono_pred _ Φ with "[#] HF"); [solve_proper|].
    iIntros "!>" (y) "Hy". iApply ("Hy" with "[# //]").
  Qed.

  Lemma least_fixpoint_unfold_1 x :
    bi_least_fixpoint F x ⊢ F (bi_least_fixpoint F) x.
  Proof using Type*.
    iIntros "HF". iApply ("HF" $! (OfeMor (F (bi_least_fixpoint F))) with "[#]").
    iIntros "!>" (y) "Hy /=". iApply (bi_mono_pred with "[#] Hy").
    iIntros "!>" (z) "?". by iApply least_fixpoint_unfold_2.
  Qed.

  Corollary least_fixpoint_unfold x :
    bi_least_fixpoint F x ≡ F (bi_least_fixpoint F) x.
  Proof using Type*.
    apply (anti_symm _); auto using least_fixpoint_unfold_1, least_fixpoint_unfold_2.
  Qed.

  (**
    The basic induction principle for least fixpoints: as inductive hypothesis,
    it allows to assume the statement to prove below exactly one application of [F].
   *)
  Lemma least_fixpoint_iter (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, F Φ y -∗ Φ y) -∗ ∀ x, bi_least_fixpoint F x -∗ Φ x.
  Proof.
    iIntros "#HΦ" (x) "HF". by iApply ("HF" $! (OfeMor Φ) with "[#]").
  Qed.

  Lemma least_fixpoint_affine :
    (∀ x, Affine (F (λ _, emp%I) x)) →
    ∀ x, Affine (bi_least_fixpoint F x).
  Proof.
    intros ?. rewrite /Affine. iApply least_fixpoint_iter.
    by iIntros "!> %y HF".
  Qed.

  Lemma least_fixpoint_absorbing :
    (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    ∀ x, Absorbing (bi_least_fixpoint F x).
  Proof using Type*.
    intros ? x. rewrite /Absorbing /bi_absorbingly.
    apply wand_elim_r'. revert x.
    iApply least_fixpoint_iter; first solve_proper.
    iIntros "!> %y HF Htrue". iApply least_fixpoint_unfold.
    iAssert (F (λ x : A, True -∗ bi_least_fixpoint F x) y)%I with "[-]" as "HF".
    { by iClear "Htrue". }
    iApply (bi_mono_pred with "[] HF"); first solve_proper.
    iIntros "!> %x HF". by iApply "HF".
  Qed.

 Lemma least_fixpoint_persistent_affine :
    (∀ Φ, (∀ x, Affine (Φ x)) → (∀ x, Affine (F Φ x))) →
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) →
    ∀ x, Persistent (bi_least_fixpoint F x).
  Proof using Type*.
    intros ?? x. rewrite /Persistent -intuitionistically_into_persistently_1.
    revert x. iApply least_fixpoint_iter; first solve_proper.
    iIntros "!> %y #HF !>". iApply least_fixpoint_unfold.
    iApply (bi_mono_pred with "[] HF"); first solve_proper.
    by iIntros "!> %x #?".
  Qed.

 Lemma least_fixpoint_persistent_absorbing :
    (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    (∀ Φ, (∀ x, Persistent (Φ x)) → (∀ x, Persistent (F Φ x))) →
    ∀ x, Persistent (bi_least_fixpoint F x).
  Proof using Type*.
    intros ??. pose proof (least_fixpoint_absorbing _). unfold Persistent.
    iApply least_fixpoint_iter; first solve_proper.
    iIntros "!> %y #HF !>". rewrite least_fixpoint_unfold.
    iApply (bi_mono_pred with "[] HF"); first solve_proper.
    by iIntros "!> %x #?".
  Qed.
End least.

Lemma least_fixpoint_strong_mono
    {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}
    (G : (A → PROP) → (A → PROP)) `{!BiMonoPred G} :
  □ (∀ Φ x, F Φ x -∗ G Φ x) -∗
  ∀ x, bi_least_fixpoint F x -∗ bi_least_fixpoint G x.
Proof.
  iIntros "#Hmon". iApply least_fixpoint_iter.
  iIntros "!>" (y) "IH". iApply least_fixpoint_unfold.
  by iApply "Hmon".
Qed.

(** In addition to [least_fixpoint_iter], we provide two derived, stronger
induction principles:

- [least_fixpoint_ind] allows to assume [F (λ x, Φ x ∧ bi_least_fixpoint F x) y]
  when proving the inductive step.
  Intuitively, it does not only offer the induction hypothesis ([Φ] under an
  application of [F]), but also the induction predicate [bi_least_fixpoint F]
  itself (under an application of [F]).
- [least_fixpoint_ind_wf] intuitively corresponds to a kind of well-founded
  induction. It provides the hypothesis [F (bi_least_fixpoint (λ Ψ a, Φ a ∧ F Ψ a)) y]
  and thus allows to assume the induction hypothesis not just below one
  application of [F], but below any positive number (by unfolding the least
  fixpoint). The unfolding lemma [least_fixpoint_unfold] as well as
  [least_fixpoint_strong_mono] can be useful to work with the hypothesis. *)

Section least_ind.
  Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.

  Local Lemma Private_wf_pred_mono `{!NonExpansive Φ} :
    BiMonoPred (λ (Ψ : A → PROP) (a : A), Φ a ∧ F Ψ a)%I.
  Proof using Type*.
    split; last solve_proper.
    intros Ψ Ψ' Hne Hne'. iIntros "#Mon" (x) "Ha". iSplit; first by iDestruct "Ha" as "[$ _]".
    iDestruct "Ha" as "[_ Hr]". iApply (bi_mono_pred with "[] Hr"). by iModIntro.
  Qed.
  Local Existing Instance Private_wf_pred_mono.

  Lemma least_fixpoint_ind_wf (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, F (bi_least_fixpoint (λ Ψ a, Φ a ∧ F Ψ a)) y -∗ Φ y) -∗
    ∀ x, bi_least_fixpoint F x -∗ Φ x.
  Proof using Type*.
    iIntros "#Hmon" (x). rewrite least_fixpoint_unfold. iIntros "Hx".
    iApply "Hmon". iApply (bi_mono_pred with "[] Hx").
    iModIntro. iApply least_fixpoint_iter.
    iIntros "!> %y Hy". rewrite least_fixpoint_unfold.
    iSplit; last done. by iApply "Hmon".
  Qed.

  Lemma least_fixpoint_ind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, F (λ x, Φ x ∧ bi_least_fixpoint F x) y -∗ Φ y) -∗
    ∀ x, bi_least_fixpoint F x -∗ Φ x.
  Proof using Type*.
    iIntros "#Hmon". iApply least_fixpoint_ind_wf. iIntros "!> %y Hy".
    iApply "Hmon". iApply (bi_mono_pred with "[] Hy"). { solve_proper. }
    iIntros "!> %x Hx". iSplit.
    - rewrite least_fixpoint_unfold. iDestruct "Hx" as "[$ _]".
    - iApply (least_fixpoint_strong_mono with "[] Hx"). iIntros "!>" (??) "[_ $]".
  Qed.
End least_ind.


Lemma greatest_fixpoint_ne_outer {PROP : bi} {A : ofe}
    (F1 : (A → PROP) → (A → PROP)) (F2 : (A → PROP) → (A → PROP)):
  (∀ Φ x n, F1 Φ x ≡{n}≡ F2 Φ x) → ∀ x1 x2 n,
  x1 ≡{n}≡ x2 → bi_greatest_fixpoint F1 x1 ≡{n}≡ bi_greatest_fixpoint F2 x2.
Proof.
  intros HF x1 x2 n Hx. rewrite /bi_greatest_fixpoint /=.
  do 3 f_equiv; last solve_proper. repeat f_equiv. apply HF.
Qed.

(* Both non-expansiveness lemmas do not seem to be interderivable.
  FIXME: is there some lemma that subsumes both? *)
Lemma greatest_fixpoint_ne' {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)):
  (∀ Φ, NonExpansive Φ → NonExpansive (F Φ)) → NonExpansive (bi_greatest_fixpoint F).
Proof. solve_proper. Qed.
Global Instance greatest_fixpoint_ne {PROP : bi} {A : ofe} n :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (dist n)) ==>
          dist n ==> dist n) bi_greatest_fixpoint.
Proof. solve_proper. Qed.
Global Instance greatest_fixpoint_proper {PROP : bi} {A : ofe} :
  Proper (pointwise_relation (A → PROP) (pointwise_relation A (≡)) ==>
          (≡) ==> (≡)) bi_greatest_fixpoint.
Proof. solve_proper. Qed.

Section greatest.
  Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.

  Lemma greatest_fixpoint_unfold_1 x :
    bi_greatest_fixpoint F x ⊢ F (bi_greatest_fixpoint F) x.
  Proof using Type*.
    iDestruct 1 as (Φ) "[#Hincl HΦ]".
    iApply (bi_mono_pred Φ (bi_greatest_fixpoint F) with "[#]").
    - iIntros "!>" (y) "Hy". iExists Φ. auto.
    - by iApply "Hincl".
  Qed.

  Lemma greatest_fixpoint_unfold_2 x :
    F (bi_greatest_fixpoint F) x ⊢ bi_greatest_fixpoint F x.
  Proof using Type*.
    iIntros "HF". iExists (OfeMor (F (bi_greatest_fixpoint F))).
    iSplit; last done. iIntros "!>" (y) "Hy /=". iApply (bi_mono_pred with "[#] Hy").
    iIntros "!>" (z) "?". by iApply greatest_fixpoint_unfold_1.
  Qed.

  Corollary greatest_fixpoint_unfold x :
    bi_greatest_fixpoint F x ≡ F (bi_greatest_fixpoint F) x.
  Proof using Type*.
    apply (anti_symm _); auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
  Qed.

  (**
    The following lemma provides basic coinduction capabilities,
    by requiring to reestablish the coinduction hypothesis after exactly one step.
   *)
  Lemma greatest_fixpoint_coiter (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, Φ y -∗ F Φ y) -∗ ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
  Proof. iIntros "#HΦ" (x) "Hx". iExists (OfeMor Φ). auto. Qed.

  Lemma greatest_fixpoint_absorbing :
    (∀ Φ, (∀ x, Absorbing (Φ x)) → (∀ x, Absorbing (F Φ x))) →
    ∀ x, Absorbing (bi_greatest_fixpoint F x).
  Proof using Type*.
    intros ?. rewrite /Absorbing.
    iApply greatest_fixpoint_coiter; first solve_proper.
    iIntros "!> %y >HF". iDestruct (greatest_fixpoint_unfold with "HF") as "HF".
    iApply (bi_mono_pred with "[] HF"); first solve_proper.
    by iIntros "!> %x HF !>".
  Qed.

End greatest.

Lemma greatest_fixpoint_strong_mono {PROP : bi} {A : ofe}
  (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}
  (G : (A → PROP) → (A → PROP)) `{!BiMonoPred G} :
  □ (∀ Φ x, F Φ x -∗ G Φ x) -∗
  ∀ x, bi_greatest_fixpoint F x -∗ bi_greatest_fixpoint G x.
Proof using Type*.
  iIntros "#Hmon". iApply greatest_fixpoint_coiter.
  iIntros "!>" (y) "IH". rewrite greatest_fixpoint_unfold.
  by iApply "Hmon".
Qed.

(** In addition to [greatest_fixpoint_coiter], we provide two derived, stronger
coinduction principles:

- [greatest_fixpoint_coind] requires to prove
  [F (λ x, Φ x ∨ bi_greatest_fixpoint F x) y] in the coinductive step instead of
  [F Φ y] and thus instead allows to prove the original fixpoint again, after
  taking one step.
- [greatest_fixpoint_paco] allows for so-called parameterized coinduction, a
  stronger coinduction principle, where [F (bi_greatest_fixpoint (λ Ψ a, Φ a ∨ F Ψ a)) y]
  needs to be established in the coinductive step. It allows to prove the
  hypothesis [Φ] not just after one step, but after any positive number of
  unfoldings of the greatest fixpoint. This encodes a way of accumulating
  "knowledge" in the coinduction hypothesis: if you return to the "initial
  point" [Φ] of the coinduction after some number of unfoldings (not just one),
  the proof is done. (Interestingly, this is the dual to [least_fixpoint_ind_wf]).
  The unfolding lemma [greatest_fixpoint_unfold] and
  [greatest_fixpoint_strong_mono] may be useful when using this lemma.

*Example use case:*

Suppose that [F] defines a coinductive simulation relation, e.g.,
  [F rec '(e_t, e_s) :=
    (is_val e_s ∧ is_val e_t ∧ post e_t e_s) ∨
    (safe e_t ∧ ∀ e_t', step e_t e_t' → ∃ e_s', step e_s e_s' ∧ rec e_t' e_s')],
and [sim e_t e_s := bi_greatest_fixpoint F].
Suppose you want to show a simulation of two loops,
  [sim (while ...) (while ...)],
i.e., [Φ '(e_t, e_s) := e_t = while ... ∧ e_s = while ...].
Then the standard coinduction principle [greatest_fixpoint_iter] requires to
establish the coinduction hypothesis [Φ] after precisely one unfolding of [sim],
which is clearly not strong enough if the loop takes multiple steps of
computation per iteration. But [greatest_fixpoint_paco] allows to establish a
fixpoint to which [Φ] has been added as a disjunct. This fixpoint can be
unfolded arbitrarily many times, allowing to establish the coinduction
hypothesis after any number of steps. This enables to take multiple simulation
steps, before closing the coinduction by establishing the hypothesis [Φ]
again. *)

Section greatest_coind.
  Context {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) `{!BiMonoPred F}.

  Local Lemma Private_paco_mono `{!NonExpansive Φ} :
    BiMonoPred (λ (Ψ : A → PROP) (a : A), Φ a ∨ F Ψ a)%I.
  Proof using Type*.
    split; last solve_proper.
    intros Ψ Ψ' Hne Hne'. iIntros "#Mon" (x) "[H1|H2]"; first by iLeft.
    iRight. iApply (bi_mono_pred with "[] H2"). by iModIntro.
  Qed.
  Local Existing Instance Private_paco_mono.

  Lemma greatest_fixpoint_paco (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, Φ y -∗ F (bi_greatest_fixpoint (λ Ψ a, Φ a ∨ F Ψ a)) y) -∗
    ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
  Proof using Type*.
    iIntros "#Hmon" (x) "HΦ". iDestruct ("Hmon" with "HΦ") as "HF".
    rewrite greatest_fixpoint_unfold. iApply (bi_mono_pred with "[] HF").
    iIntros "!>" (y) "HG". iApply (greatest_fixpoint_coiter with "[] HG").
    iIntros "!>" (z) "Hf". rewrite greatest_fixpoint_unfold.
    iDestruct "Hf" as "[HΦ|$]". by iApply "Hmon".
  Qed.

  Lemma greatest_fixpoint_coind (Φ : A → PROP) `{!NonExpansive Φ} :
    □ (∀ y, Φ y -∗ F (λ x, Φ x ∨ bi_greatest_fixpoint F x) y) -∗
    ∀ x, Φ x -∗ bi_greatest_fixpoint F x.
  Proof using Type*.
    iIntros "#Ha". iApply greatest_fixpoint_paco. iModIntro.
    iIntros (y) "Hy". iSpecialize ("Ha" with "Hy").
    iApply (bi_mono_pred with "[] Ha"). { solve_proper. }
    iIntros "!> %x [Hphi | Hgfp]".
    - iApply greatest_fixpoint_unfold. eauto.
    - iApply (greatest_fixpoint_strong_mono with "[] Hgfp"); eauto.
  Qed.
End greatest_coind.
