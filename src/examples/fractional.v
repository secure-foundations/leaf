From iris.base_logic.lib Require Import invariants.
From lang Require Import lang simp adequacy primitive_laws.
From examples Require Import rwlock_logic.
Require Import cpdt.CpdtTactics.

Require Import guarding.guard.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import reduction.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import class_instances.
From iris.program_logic Require Import ectx_lifting.
From lang Require Import notation tactics class_instances.
From lang Require Import heap_ra.
From lang Require Import lang.
From iris Require Import options.

Require Import guarding.guard_later.
Require Import examples.misc_tactics.
Require Import guarding.protocol.
Require Import guarding.inved.
From iris.algebra Require Import auth.

Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qround.
Require Import Coq.QArith.Qcanon.
Require Import Coq.ZArith.Int.

Context {Σ: gFunctors}.
Context `{!simpGS Σ}.

Definition FRAC_NAMESPACE := nroot .@ "fractional".

Definition frac := option Qp.

Definition is_int (q: Qp) :=
    inject_Z (Qceiling (Qp_to_Qc q)) == Qp_to_Qc q.

Global Instance frac_inv : PInv frac := λ t , match t with
  | None => True
  | Some q => is_int q
end.

Lemma ceil_ge_1 (q: Qp) : (Qceiling (Qp_to_Qc q) >= 1)%Z.
Proof.
  have h := Qle_ceiling (Qp_to_Qc q).
  have h2 := Qp_prf q.
  assert (¬((Qceiling (Qp_to_Qc q)) <= 0)%Z) as X. {
    intro R.
    rewrite Zle_Qle in R.
    unfold Qclt in h2.
    replace (Q2Qc 0 : Q) with (inject_Z 0) in h2 by trivial.
    have k := Qle_trans _ _ _ h R.
    have j := Qlt_not_le _ _ h2.
    apply j. trivial.
  }
  lia.
Qed.

Lemma main_guard_lemma (q r: Qp)
  : is_int (q + r) -> (Qceiling (Qp_to_Qc (q + r)) >= 1)%Z.
Proof.
  unfold is_int.
  

Definition trivial_protocol_mixin : ProtocolMixin (option Qp).
Proof. split.
  - apply trivial_ra_mixin.
  - unfold LeftId. intro. destruct x; trivial.
  - intro p. destruct p. intro. trivial.
  - unfold Proper, "==>", impl. intros x y. destruct y. trivial.
Qed.

Definition trivial_storage_mixin : StorageMixin Trivial (Exc ()).
Proof. split.
  - apply trivial_protocol_mixin.
  - apply exc_ra_mixin.
  - unfold LeftId. intro x. destruct x; trivial.
  - unfold Proper, "==>". intros x y. destruct x, y. trivial.
  - intros. destruct p. trivial.
Qed.

Class forever_logicG Σ :=
    {
      forever_logic_inG :> inG Σ 
        (authUR (inved_protocolUR (protocol_mixin (Trivial) (Exc ()) (trivial_storage_mixin))))
    }.


Definition forever_logicΣ : gFunctors := #[
  GFunctor
        (authUR (inved_protocolUR (protocol_mixin (Trivial) (Exc ()) (trivial_storage_mixin))))
].

Global Instance subG_forever_logicΣ {Σ} : subG forever_logicΣ Σ → forever_logicG Σ.
Proof. solve_inG. Qed.

Section Forever.

Context {Σ: gFunctors}.
Context `{@forever_logicG Σ}.
Context `{!invGS Σ}.

Definition family (Q: iProp Σ) (e: Exc ()) : iProp Σ :=
  match e with
    | Unknown => (True)%I
    | Yes _ => Q
    | Fail => (False)%I
  end. 
  
Lemma wf_prop_map_family (Q: iProp Σ) : wf_prop_map (family Q).
Proof.
  split.
    { unfold Proper, "==>", family. intros x y. destruct x, y; trivial; intro K;
        unfold "≡", exc_equiv in K; contradiction. }
    split.
    { trivial. }
    { intros a b is_val. destruct a, b; trivial; unfold "⋅", exc_op, family.
      - iIntros. iSplit; done.
      - iIntros. iSplit. { iIntros "q". iFrame. } { iIntros "[t q]". iFrame. }
      - iIntros. iSplit. { iIntros "q". iFrame. } { iIntros "[t q]". iFrame. }
      - iIntros. iSplit. { iIntros "q". iFrame. } { iIntros "[t q]". iFrame. }
      - unfold "⋅", exc_op, "✓", exc_valid in is_val. contradiction.
      - unfold "⋅", exc_op, "✓", exc_valid in is_val. contradiction.
      - unfold "⋅", exc_op, "✓", exc_valid in is_val. contradiction.
      - unfold "⋅", exc_op, "✓", exc_valid in is_val. contradiction.
      - unfold "⋅", exc_op, "✓", exc_valid in is_val. contradiction.
    }
Qed.

Lemma storage_protocol_guards_triv
  : storage_protocol_guards (ε: Trivial) (Yes ()).
Proof.
  unfold storage_protocol_guards. intro q. destruct q. unfold "⋅", trivial_op. unfold interp.
  unfold trivial_interp. intro. unfold "≼". exists ε. trivial.
Qed.

Lemma make_forever (Q: iProp Σ) (E: coPset)
  : ⊢ Q ={E}=∗ (True &&{↑ FOREVER_NAMESPACE : coPset}&&> ▷ Q).
Proof using H invGS0 Σ.
  iIntros "q".
  replace (Q) with (family Q (interp ε)) at 1 by trivial.
  assert (@pinv Trivial trivial_pinv ε) as J.
  { unfold pinv, ε, trivial_unit, trivial_pinv. trivial. }
  iMod (logic_init_ns (ε : Trivial) (family Q) E (FOREVER_NAMESPACE) J with "q") as "r".
  { apply wf_prop_map_family. }
  iDestruct "r" as (γ) "[%inns [#m p]]".
  iDestruct (logic_guard (ε : Trivial) (Yes ()) γ (↑ FOREVER_NAMESPACE) (family Q) with "m")
      as "g".
  { apply storage_protocol_guards_triv. }
  { trivial. }
  unfold family at 2.
  iDestruct (p_own_unit with "m") as "u".
  iDestruct (guards_refl (↑FOREVER_NAMESPACE) (True)%I) as "tt".
  iDestruct (guards_include_pers (□ p_own γ ε) (True)%I (True)%I
      (↑FOREVER_NAMESPACE) with "[u tt]") as "tu".
      { iFrame "tt". iModIntro. iFrame "u". }
  assert ((True ∗ □ p_own γ (ε: Trivial))%I ⊣⊢ ((p_own γ ε) ∗ □ p_own γ ε)%I) as Z.
  { iIntros. iSplit. { iIntros "[t #o]". iFrame "o". } { iIntros "[p #o]". iFrame "o". } }
  rewrite Z.
  iDestruct (guards_weaken_rhs_l with "tu") as "tk".
  iModIntro.
  iApply guards_transitive.
  { iFrame "tk". iFrame "g". }
Qed.

End Forever.
