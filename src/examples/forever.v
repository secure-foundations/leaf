From iris.base_logic.lib Require Import invariants.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import reduction.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import class_instances.
From iris.program_logic Require Import ectx_lifting.
From iris Require Import options.

Require Import guarding.guard.
Require Import guarding.tactics.
Require Import examples.misc_tactics.
Require Import guarding.storage_protocol.protocol.
From iris.algebra Require Import auth.

(** This file shows how to derive the rule

```
Q ={E}=∗ (True &&{↑ N}&&> ▷ Q)
```

using a storage protocol. However, this rule is now part of the Leaf core logic, so it's
only useful academically for an understanding of how storage protocols work.
*)

Definition FOREVER_NAMESPACE := nroot .@ "forever".

Inductive Trivial := Triv.

Inductive Exc (S: Type) :=
  | Unknown : Exc S
  | Yes : S -> Exc S
  | Fail : Exc S
.
Arguments Unknown {_}%type_scope.
Arguments Yes {_}%type_scope _.
Arguments Fail {_}%type_scope.

Instance exc_op {S} : Op (Exc S) := λ a b , match a, b with
  | Unknown, y => y
  | Fail, y => Fail
  | Yes m, Unknown => Yes m
  | Yes _, _ => Fail
  end
.

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
  - unfold Symmetric. intros x y. destruct x, y; trivial.
  - unfold Transitive. intros x y z. destruct x, y, z; trivial.
Qed.

Definition exc_ra_mixin {A} `{Equiv A} `{@Equivalence A (≡)} : RAMixin (Exc A).
Proof. split.
 - intros x. unfold Proper, "==>".  intros x0 y. destruct x0, x, y; trivial.
    unfold "⋅", exc_op. intro. unfold "≡", exc_equiv. trivial.
 - unfold pcore, exc_pcore. intros. discriminate.
 - unfold Proper, equiv, "==>", valid, exc_equiv, exc_valid, impl. intros x y.
      destruct x; destruct y; trivial.
 - unfold Assoc. intros x y z. unfold "⋅", exc_op. destruct x, y, z; trivial;
    unfold "≡", exc_equiv; trivial.
 - unfold Comm. intros x y. unfold "⋅", exc_op. destruct x, y; trivial;
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
Global Instance trivial_pinv : SPInv Trivial := λ a , True.

Instance trivial_unit : Unit Trivial := Triv.

Global Instance trivial_interp : SPInterp Trivial (Exc ()) := λ t , Yes ().

Lemma trivial_valid_interp (p: Trivial) : ✓ (sp_interp p : Exc ()).
Proof. unfold "✓", exc_valid, sp_interp, trivial_interp. trivial. Qed.

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

Definition trivial_storage_mixin_ii : StorageMixinII Trivial (Exc ()).
Proof. split.
  - apply trivial_ra_mixin.
  - apply exc_ra_mixin.
  - unfold LeftId. intro x. destruct x; trivial.
  - unfold LeftId. intro x. destruct x; trivial.
  - intro p. destruct p. intro. trivial.
  - unfold Proper, "==>", impl. intros x y. destruct y. trivial.
  - intros p. destruct p. trivial.
Qed.

Class forever_logicG Σ :=
    {
      #[local] forever_sp_inG ::
        sp_logicG (storage_mixin_from_ii trivial_storage_mixin_ii) Σ
    }.

Definition forever_logicΣ : gFunctors := #[
  sp_logicΣ (storage_mixin_from_ii trivial_storage_mixin_ii)
].

Global Instance subG_forever_logicΣ {Σ} : subG forever_logicΣ Σ → forever_logicG Σ.
Proof. solve_inG. Qed.

Section Forever.

Context {Σ: gFunctors}.
Context `{f_in_Σ: @forever_logicG Σ}.
Context `{!invGS_gen hlc Σ}.

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
  unfold storage_protocol_guards. intro q. destruct q. unfold "⋅", trivial_op.
  intros t [spr speq]. exists (ε). setoid_rewrite <- speq. trivial.
Qed.

Lemma make_forever (Q: iProp Σ) (E: coPset)
  : ⊢ Q ={E}=∗ (True &&{↑ FOREVER_NAMESPACE : coPset}&&> ▷ Q).
Proof using f_in_Σ.
  iIntros "q".
  replace (Q) with (family Q (sp_interp ε)) at 1 by trivial.
  assert (@sp_inv Trivial trivial_pinv ε) as J.
  { unfold sp_inv, ε, trivial_unit, trivial_pinv. trivial. }
  iMod (sp_alloc_ns (ε : Trivial) (Yes ()) (family Q) E (FOREVER_NAMESPACE) with "q") as "r". { split; trivial. }
  { apply wf_prop_map_family. }
  iDestruct "r" as (γ) "[%inns [#m p]]".
  iDestruct (sp_guard (ε : Trivial) (Yes ()) γ (↑ FOREVER_NAMESPACE) (family Q) with "m")
      as "g".
  { apply storage_protocol_guards_triv. }
  { trivial. }
  unfold family at 2.
  iDestruct (sp_own_unit with "m") as "u".
  leaf_hyp "g" lhs to (True)%I as "g1".
  - leaf_by_sep. iIntros. iFrame "#". iIntros. done.
  - iFrame "g1". iModIntro. done.
Qed.

End Forever.
