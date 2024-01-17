From stdpp Require Import gmap.
From iris.algebra Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export own.
From iris.bi Require Import fractional.
From iris.prelude Require Import options.
Import uPred.

(* "Saved anything" -- this can give you saved propositions, saved predicates,
   saved whatever-you-like. *)

Class savedAnythingG (Σ : gFunctors) (F : oFunctor) := SavedAnythingG {
  saved_anything_inG : inG Σ (dfrac_agreeR (oFunctor_apply F (iPropO Σ)));
  saved_anything_contractive : oFunctorContractive F (* NOT an instance to avoid cycles with [subG_savedAnythingΣ]. *)
}.
Local Existing Instance saved_anything_inG.

Definition savedAnythingΣ (F : oFunctor) `{!oFunctorContractive F} : gFunctors :=
  #[ GFunctor (dfrac_agreeRF F) ].

Global Instance subG_savedAnythingΣ {Σ F} `{!oFunctorContractive F} :
  subG (savedAnythingΣ F) Σ → savedAnythingG Σ F.
Proof. solve_inG. Qed.

Definition saved_anything_own `{!savedAnythingG Σ F}
    (γ : gname) (dq : dfrac) (x : oFunctor_apply F (iPropO Σ)) : iProp Σ :=
  own γ (to_dfrac_agree dq x).
Global Typeclasses Opaque saved_anything_own.
Global Instance: Params (@saved_anything_own) 4 := {}.

Section saved_anything.
  Context `{!savedAnythingG Σ F}.
  Implicit Types x y : oFunctor_apply F (iPropO Σ).
  Implicit Types (γ : gname) (dq : dfrac).

  Global Instance saved_anything_discarded_persistent γ x :
    Persistent (saved_anything_own γ DfracDiscarded x).
  Proof. rewrite /saved_anything_own; apply _. Qed.

  Global Instance saved_anything_ne γ dq : NonExpansive (saved_anything_own γ dq).
  Proof. solve_proper. Qed.
  Global Instance saved_anything_proper γ dq : Proper ((≡) ==> (≡)) (saved_anything_own γ dq).
  Proof. solve_proper. Qed.

  Global Instance saved_anything_fractional γ x : Fractional (λ q, saved_anything_own γ (DfracOwn q) x).
  Proof. intros q1 q2. rewrite /saved_anything_own -own_op -dfrac_agree_op //. Qed.
  Global Instance saved_anything_as_fractional γ x q :
    AsFractional (saved_anything_own γ (DfracOwn q) x) (λ q, saved_anything_own γ (DfracOwn q) x) q.
  Proof. split; [done|]. apply _. Qed.

  (** Allocation *)
  Lemma saved_anything_alloc_strong x (I : gname → Prop) dq :
    ✓ dq →
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_anything_own γ dq x.
  Proof. intros ??. by apply own_alloc_strong. Qed.

  Lemma saved_anything_alloc_cofinite x (G : gset gname) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_anything_own γ dq x.
  Proof. intros ?. by apply own_alloc_cofinite. Qed.

  Lemma saved_anything_alloc x dq :
    ✓ dq →
    ⊢ |==> ∃ γ, saved_anything_own γ dq x.
  Proof. intros ?. by apply own_alloc. Qed.

  (** Validity *)
  Lemma saved_anything_valid γ dq x :
    saved_anything_own γ dq x -∗ ⌜✓ dq⌝.
  Proof.
    rewrite /saved_anything_own own_valid dfrac_agree_validI //. eauto.
  Qed.
  Lemma saved_anything_valid_2 γ dq1 dq2 x y :
    saved_anything_own γ dq1 x -∗ saved_anything_own γ dq2 y -∗ ⌜✓ (dq1 ⋅ dq2)⌝ ∗ x ≡ y.
  Proof.
    iIntros "Hx Hy". rewrite /saved_anything_own.
    iCombine "Hx Hy" gives "Hv".
    rewrite dfrac_agree_validI_2. iDestruct "Hv" as "[$ $]".
  Qed.
  Lemma saved_anything_agree γ dq1 dq2 x y :
    saved_anything_own γ dq1 x -∗ saved_anything_own γ dq2 y -∗ x ≡ y.
  Proof. iIntros "Hx Hy". iPoseProof (saved_anything_valid_2 with "Hx Hy") as "[_ $]". Qed.

  Global Instance saved_anything_combine_gives γ dq1 dq2 x y :
    CombineSepGives (saved_anything_own γ dq1 x) (saved_anything_own γ dq2 y)
      (⌜✓ (dq1 ⋅ dq2)⌝ ∗ x ≡ y).
  Proof.
    rewrite /CombineSepGives. iIntros "[Hx Hy]".
    iPoseProof (saved_anything_valid_2 with "Hx Hy") as "[% #$]". eauto.
  Qed.

  Global Instance saved_anything_combine_as γ dq1 dq2 x y :
    CombineSepAs (saved_anything_own γ dq1 x) (saved_anything_own γ dq2 y)
      (saved_anything_own γ (dq1 ⋅ dq2) x).
  (* higher cost than the Fractional instance, which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[Hx Hy]".
    iCombine "Hx Hy" gives "[_ #H]".
    iRewrite -"H" in "Hy". rewrite /saved_anything_own.
    iCombine "Hx Hy" as "Hxy". by rewrite -dfrac_agree_op.
  Qed.

  (** Make an element read-only. *)
  Lemma saved_anything_persist γ dq v :
    saved_anything_own γ dq v ==∗ saved_anything_own γ DfracDiscarded v.
  Proof.
    iApply own_update. apply dfrac_agree_persist.
  Qed.

  (** Updates *)
  Lemma saved_anything_update y γ x :
    saved_anything_own γ (DfracOwn 1) x ==∗ saved_anything_own γ (DfracOwn 1) y.
  Proof.
    iApply own_update. apply cmra_update_exclusive. done.
  Qed.
  Lemma saved_anything_update_2 y γ q1 q2 x1 x2 :
    (q1 + q2 = 1)%Qp →
    saved_anything_own γ (DfracOwn q1) x1 -∗ saved_anything_own γ (DfracOwn q2) x2 ==∗
    saved_anything_own γ (DfracOwn q1) y ∗ saved_anything_own γ (DfracOwn q2) y.
  Proof.
    intros Hq. rewrite -own_op. iApply own_update_2.
    apply dfrac_agree_update_2.
    rewrite dfrac_op_own Hq //.
  Qed.
  Lemma saved_anything_update_halves y γ x1 x2 :
    saved_anything_own γ (DfracOwn (1/2)) x1 -∗
    saved_anything_own γ (DfracOwn (1/2)) x2 ==∗
    saved_anything_own γ (DfracOwn (1/2)) y ∗ saved_anything_own γ (DfracOwn (1/2)) y.
  Proof. iApply saved_anything_update_2. apply Qp.half_half. Qed.
End saved_anything.

(** Provide specialized versions of this for convenience. **)

(* Saved propositions. *)
Notation savedPropG Σ := (savedAnythingG Σ (▶ ∙)).
Notation savedPropΣ := (savedAnythingΣ (▶ ∙)).

Section saved_prop.
  Context `{!savedPropG Σ}.

  Definition saved_prop_own (γ : gname) (dq : dfrac) (P: iProp Σ) :=
    saved_anything_own (F := ▶ ∙) γ dq (Next P).

  Global Instance saved_prop_own_contractive γ dq :
    Contractive (saved_prop_own γ dq).
  Proof. solve_contractive. Qed.

  Global Instance saved_prop_discarded_persistent γ P :
    Persistent (saved_prop_own γ DfracDiscarded P).
  Proof. apply _. Qed.

  Global Instance saved_prop_fractional γ P : Fractional (λ q, saved_prop_own γ (DfracOwn q) P).
  Proof. apply _. Qed.
  Global Instance saved_prop_as_fractional γ P q :
    AsFractional (saved_prop_own γ (DfracOwn q) P) (λ q, saved_prop_own γ (DfracOwn q) P) q.
  Proof. apply _. Qed.

  (** Allocation *)
  Lemma saved_prop_alloc_strong (I : gname → Prop) (P: iProp Σ) dq :
    ✓ dq →
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_prop_own γ dq P.
  Proof. intros ??. by apply saved_anything_alloc_strong. Qed.

  Lemma saved_prop_alloc_cofinite (G : gset gname) (P: iProp Σ) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_prop_own γ dq P.
  Proof. by apply saved_anything_alloc_cofinite. Qed.

  Lemma saved_prop_alloc (P : iProp Σ) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, saved_prop_own γ dq P.
  Proof. apply saved_anything_alloc. Qed.

  (** Validity *)
  Lemma saved_prop_valid γ dq P :
    saved_prop_own γ dq P -∗ ⌜✓ dq⌝.
  Proof. apply saved_anything_valid. Qed.
  Lemma saved_prop_valid_2 γ dq1 dq2 P Q :
    saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ⌜✓ (dq1 ⋅ dq2)⌝ ∗ ▷ (P ≡ Q).
  Proof.
    iIntros "HP HQ".
    iCombine "HP HQ" gives "($ & Hag)".
    by iApply later_equivI.
  Qed.
  Lemma saved_prop_agree γ dq1 dq2 P Q :
    saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ ▷ (P ≡ Q).
  Proof. iIntros "HP HQ". iCombine "HP" "HQ" gives "[_ $]". Qed.

  (** Make an element read-only. *)
  Lemma saved_prop_persist γ dq P :
    saved_prop_own γ dq P ==∗ saved_prop_own γ DfracDiscarded P.
  Proof. apply saved_anything_persist. Qed.

  (** Updates *)
  Lemma saved_prop_update Q γ P :
    saved_prop_own γ (DfracOwn 1) P ==∗ saved_prop_own γ (DfracOwn 1) Q.
  Proof. apply saved_anything_update. Qed.
  Lemma saved_prop_update_2 Q γ q1 q2 P1 P2 :
    (q1 + q2 = 1)%Qp →
    saved_prop_own γ (DfracOwn q1) P1 -∗ saved_prop_own γ (DfracOwn q2) P2 ==∗
    saved_prop_own γ (DfracOwn q1) Q ∗ saved_prop_own γ (DfracOwn q2) Q.
  Proof. apply saved_anything_update_2. Qed.
  Lemma saved_prop_update_halves Q γ P1 P2 :
    saved_prop_own γ (DfracOwn (1/2)) P1 -∗
    saved_prop_own γ (DfracOwn (1/2)) P2 ==∗
    saved_prop_own γ (DfracOwn (1/2)) Q ∗ saved_prop_own γ (DfracOwn (1/2)) Q.
  Proof. apply saved_anything_update_halves. Qed.
End saved_prop.

(* Saved predicates. *)
Notation savedPredG Σ A := (savedAnythingG Σ (A -d> ▶ ∙)).
Notation savedPredΣ A := (savedAnythingΣ (A -d> ▶ ∙)).

Section saved_pred.
  Context `{!savedPredG Σ A}.

  Definition saved_pred_own (γ : gname) (dq : dfrac) (Φ : A → iProp Σ) :=
    saved_anything_own (F := A -d> ▶ ∙) γ dq (Next ∘ Φ).

  Global Instance saved_pred_own_contractive `{!savedPredG Σ A} γ dq :
    Contractive (saved_pred_own γ dq : (A -d> iPropO Σ) → iProp Σ).
  Proof.
    solve_proper_core ltac:(fun _ => first [ intros ?; progress simpl | by auto | f_contractive | f_equiv ]).
  Qed.

  Global Instance saved_pred_discarded_persistent γ Φ :
    Persistent (saved_pred_own γ DfracDiscarded Φ).
  Proof. apply _. Qed.

  Global Instance saved_pred_fractional γ Φ : Fractional (λ q, saved_pred_own γ (DfracOwn q) Φ).
  Proof. apply _. Qed.
  Global Instance saved_pred_as_fractional γ Φ q :
    AsFractional (saved_pred_own γ (DfracOwn q) Φ) (λ q, saved_pred_own γ (DfracOwn q) Φ) q.
  Proof. apply _. Qed.

  (** Allocation *)
  Lemma saved_pred_alloc_strong (I : gname → Prop) (Φ : A → iProp Σ) dq :
    ✓ dq →
    pred_infinite I →
    ⊢ |==> ∃ γ, ⌜I γ⌝ ∗ saved_pred_own γ dq Φ.
  Proof. intros ??. by apply saved_anything_alloc_strong. Qed.

  Lemma saved_pred_alloc_cofinite (G : gset gname) (Φ : A → iProp Σ) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ saved_pred_own γ dq Φ.
  Proof. by apply saved_anything_alloc_cofinite. Qed.

  Lemma saved_pred_alloc (Φ : A → iProp Σ) dq :
    ✓ dq →
    ⊢ |==> ∃ γ, saved_pred_own γ dq Φ.
  Proof. apply saved_anything_alloc. Qed.

  (** Validity *)
  Lemma saved_pred_valid γ dq Φ :
    saved_pred_own γ dq Φ -∗ ⌜✓ dq⌝.
  Proof. apply saved_anything_valid. Qed.
  Lemma saved_pred_valid_2 γ dq1 dq2 Φ Ψ x :
    saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ⌜✓ (dq1 ⋅ dq2)⌝ ∗ ▷ (Φ x ≡ Ψ x).
  Proof.
    iIntros "HΦ HΨ".
    iCombine "HΦ HΨ" gives "($ & Hag)".
    iApply later_equivI. by iApply (discrete_fun_equivI with "Hag").
  Qed.
  Lemma saved_pred_agree γ dq1 dq2 Φ Ψ x :
    saved_pred_own γ dq1 Φ -∗ saved_pred_own γ dq2 Ψ -∗ ▷ (Φ x ≡ Ψ x).
  Proof. iIntros "HΦ HΨ". iPoseProof (saved_pred_valid_2 with "HΦ HΨ") as "[_ $]". Qed.

  (** Make an element read-only. *)
  Lemma saved_pred_persist γ dq Φ :
    saved_pred_own γ dq Φ ==∗ saved_pred_own γ DfracDiscarded Φ.
  Proof. apply saved_anything_persist. Qed.

  (** Updates *)
  Lemma saved_pred_update Ψ γ Φ :
    saved_pred_own γ (DfracOwn 1) Φ ==∗ saved_pred_own γ (DfracOwn 1) Ψ.
  Proof. apply saved_anything_update. Qed.
  Lemma saved_pred_update_2 Ψ γ q1 q2 Φ1 Φ2 :
    (q1 + q2 = 1)%Qp →
    saved_pred_own γ (DfracOwn q1) Φ1 -∗ saved_pred_own γ (DfracOwn q2) Φ2 ==∗
    saved_pred_own γ (DfracOwn q1) Ψ ∗ saved_pred_own γ (DfracOwn q2) Ψ.
  Proof. apply saved_anything_update_2. Qed.
  Lemma saved_pred_update_halves Ψ γ Φ1 Φ2 :
    saved_pred_own γ (DfracOwn (1/2)) Φ1 -∗
    saved_pred_own γ (DfracOwn (1/2)) Φ2 ==∗
    saved_pred_own γ (DfracOwn (1/2)) Ψ ∗ saved_pred_own γ (DfracOwn (1/2)) Ψ.
  Proof. apply saved_anything_update_halves. Qed.
End saved_pred.
