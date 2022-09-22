From iris.base_logic.lib Require Import invariants.
From twolang Require Import lang simp adequacy primitive_laws.
From Two Require Import rwlock.
Require Import cpdt.CpdtTactics.

Require Import Two.guard.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import reduction.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import class_instances.
From iris.program_logic Require Import ectx_lifting.
From twolang Require Import notation tactics class_instances.
From twolang Require Import heap_ra.
From twolang Require Import lang.
From iris Require Import options.

Require Import Two.guard_later.
Require Import TwoExamples.misc_tactics.
Require Import Two.protocol.
Require Import Two.inved.
From iris.algebra Require Import auth.

Context {Σ: gFunctors}.
Context `{!simpGS Σ}.

Definition FOREVER_NAMESPACE := nroot .@ "forever".

Inductive Trivial := Triv.

Global Instance exc_valid {A} : Valid (Exc A) := λ t ,
    match t with
    | Unknown => True
    | Yes _ => True
    | Fail => False
    end. 
    
Global Instance exc_equiv {A} `{Equiv A} : Equiv (Exc A) := λ a b ,
    match (a, b) with
      | (Unknown, Unknown) => True
      | (Yes x, Yes y) => x ≡ y
      | (Fail, Fail) => True
      | _ => False
    end. 
    
Global Instance exc_unit {A} `{Equiv A} : Unit (Exc A) := Unknown.
    
Global Instance exc_pcore A : PCore (Exc A) := λ a , None.

Global Instance equ_exc : @Equivalence (Exc ()) (≡).
Proof. split.
  - unfold Reflexive. intro x. destruct x; trivial.
  - unfold Symmetric. intro x. destruct x, y; trivial.
  - unfold Transitive. intro x. destruct x, y, z; trivial.
Qed.

Definition exc_ra_mixin {A} `{Equiv A} `{@Equivalence A (≡)} : RAMixin (Exc A).
Proof. split.
 - intros. unfold Proper, "==>".  intros x0 y. destruct x0, x, y; trivial.
    unfold "⋅", exc_op. intro. unfold "≡", exc_equiv. trivial.
 - unfold pcore, exc_pcore. intros. discriminate.
 - unfold Proper, equiv, "==>", valid, exc_equiv, exc_valid, impl. intros x y.
      destruct x; destruct y; trivial.
 - unfold Assoc. intros. unfold "⋅", exc_op. destruct x, y, z; trivial;
    unfold "≡", exc_equiv; trivial.
 - unfold Comm. intros. unfold "⋅", exc_op. destruct x, y; trivial;
    unfold "≡", exc_equiv; trivial.
 - unfold pcore, exc_pcore. intros. discriminate.
 - unfold pcore, exc_pcore. intros. discriminate.
 - unfold pcore, exc_pcore. intros. discriminate.
 - intros x y. unfold "✓", exc_valid, "⋅", exc_op. destruct x, y; trivial.
Qed.

Global Instance trivial_eqdec : EqDecision Trivial.
Proof. solve_decision. Qed.
Global Instance trivial_equiv : Equiv Trivial := λ a b , a = b.
Global Instance trivial_pcore : PCore Trivial := λ a , None.
Global Instance trivial_valid : Valid Trivial := λ a , True.
Global Instance trivial_op : Op Trivial := λ a b , Triv.
Global Instance trivial_pinv : PInv Trivial := λ a , True.

Instance trivial_unit : Unit Trivial := Triv.

Global Instance trivial_interp : Interp Trivial (Exc ()) := λ t , Yes ().

Lemma trivial_valid_interp (p: Trivial) : ✓ (interp p : Exc ()).
Proof. unfold "✓", exc_valid, interp, trivial_interp. trivial. Qed.

Definition trivial_ra_mixin : RAMixin Trivial.
Proof. split.
  - typeclasses eauto.
  - unfold pcore, trivial_pcore. intros. discriminate.
  - typeclasses eauto.
  - unfold Assoc. intros. trivial.
  - unfold Comm. intros. trivial.
  - unfold pcore, trivial_pcore. intros. discriminate.
  - unfold pcore, trivial_pcore. intros. discriminate.
  - unfold pcore, trivial_pcore. intros. discriminate.
  - trivial.
Qed.

Definition trivial_protocol_mixin : ProtocolMixin Trivial.
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
