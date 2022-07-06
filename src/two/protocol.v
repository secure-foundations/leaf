From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

From iris.base_logic.lib Require Export invariants.

From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export fancy_updates_from_vs.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export wsat.

From iris.bi Require Import derived_laws.

(*
Context {Σ: gFunctors}.
Context `{!invGS Σ}.
*)

Class Inv (A : Type) := inv : A → Prop.
Global Hint Mode Inv ! : typeclass_instances.
Global Instance: Params (@inv) 2 := {}.

Record ProtocolMixin P B
    `{Equiv P, PCore P, Op P, Valid P, Inv P, Unit P}
    {equ: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
:= {
    protocol_ra_mixin: RAMixin P;
    base_ra_mixin: RAMixin B; (* completely ignore core *)
    
    protocol_unit_valid : ✓ (ε : P);
    protocol_unit_left_id : LeftId equiv (ε : P) op;
    protocol_pcore_unit : pcore (ε : P) ≡ Some (ε : P);
    
    interp: P -> B;

    inv_implies_valid: ∀ (p: P) , inv p -> ✓ p;
    inv_proper: Proper ((≡) ==> impl) (@inv P _);
    interp_proper: Proper ((≡) ==> (≡)) (@inv P _);
}. 

Inductive InvedProtocol (P: Type) :=
  | Inved : P -> InvedProtocol P.
Global Arguments Inved {_} _.

Global Instance inved_protocol_equiv P `{Equiv P} : Equiv (InvedProtocol P) :=
    λ x y , match x with Inved a => match y with Inved b => a ≡ b end end.
    
Global Instance inved_protocol_pcore P `{PCore P} : PCore (InvedProtocol P) :=
    λ x , match x with Inved a => 
        match pcore a with
          | Some t => Some (Inved t)
          | None => None
        end end.

Global Instance inved_protocol_valid P `{Inv P} `{Op P} : Valid (InvedProtocol P) :=
   λ x , match x with Inved a => ∃ b , inv (a ⋅ b) end.
   
Global Instance inved_protocol_op P `{Inv P} `{Op P} : Op (InvedProtocol P) :=
   λ x y , match x with Inved a => match y with Inved b => Inved (a ⋅ b) end end.
   
   (*
Lemma whatever (x y z : A)
  : (x ≡ z) -> (x ⋅ y ≡ z ⋅ y).
Proof.
  intros. setoid_rewrite H. trivial.
Qed.
*)

Lemma inved_incl_to_incl {P} 
    `{Equiv P, Op P, Inv P}
    (a b : P) (mle : Inved a ≼ Inved b) : a ≼ b.
Proof.
  unfold "≼".
  unfold "≼" in mle.
  destruct mle as [z mle].
  destruct z.
  exists p.
  unfold "≡", inved_protocol_equiv, "⋅", inved_protocol_op in mle. trivial.
Qed.

Lemma incl_to_inved_incl {P} 
    `{Equiv P, Op P, Inv P}
    (a b : P) (mle : a ≼ b) : Inved a ≼ Inved b.
Proof.
  unfold "≼".
  unfold "≼" in mle.
  destruct mle as [z mle].
  exists (Inved z).
  unfold "≡". unfold inved_protocol_equiv. unfold "⋅". unfold inved_protocol_op. trivial.
Qed.

Definition inved_protocol_ra_mixin {P B}
    `{Equiv P, PCore P, Op P, Inv P, Valid P, Unit P}
    {equ: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
    (pm: ProtocolMixin P B) : RAMixin (InvedProtocol P).
Proof.
  destruct pm.
  destruct protocol_ra_mixin0.
  split.
 - intro. destruct x. unfold Proper, equiv, "==>".
    unfold inved_protocol_equiv.
    intros a b. destruct a; destruct b. unfold "⋅", inved_protocol_op. intro e.
    eapply ra_op_proper; trivial.
 - intros x y cx e p.
    destruct x, y, cx.
    unfold "≡", inved_protocol_equiv in e.
    have t := ra_core_proper p0 p1 p2 e.
    
    unfold pcore, inved_protocol_pcore in p.
    destruct (pcore p0) eqn:q.
    
    + assert (Some p3 = Some p2) as pe. { f_equal. inversion p. trivial. }
      have t0 := t pe. destruct t0 as [cy [t0 t1]]. exists (Inved cy). split.
      * unfold pcore. unfold inved_protocol_pcore. rewrite t0. trivial.
      * unfold "≡", inved_protocol_equiv. trivial.
    + discriminate.
 - unfold Proper, equiv, impl, "==>". intros x y ipe. unfold "✓", inved_protocol_valid.
    destruct x; destruct y. intro h. destruct h as [b ipb]. exists b.
    unfold inved_protocol_equiv in ipe.
    
    eapply inv_proper0. Focus 2. apply ipb. 
    
    assert (p ⋅ b ≡ b ⋅ p) as X. { eapply ra_comm. }
    assert (p0 ⋅ b ≡ b ⋅ p0) as Y. { eapply ra_comm. }
    setoid_rewrite X. setoid_rewrite Y.
    eapply ra_op_proper. trivial.
 - unfold Assoc. intros. destruct x, y, z. unfold "⋅". unfold inved_protocol_op.
    unfold "≡". unfold inved_protocol_equiv. apply ra_assoc.
 - unfold Comm. intros. destruct x, y. unfold "⋅". unfold inved_protocol_op.
    unfold "≡". unfold inved_protocol_equiv. apply ra_comm.
 - intros x cx pc. destruct x, cx.
    unfold "⋅". unfold inved_protocol_op. unfold "≡". unfold inved_protocol_equiv.
    unfold pcore, inved_protocol_pcore in pc. destruct (pcore p) eqn:pp.
    + have t := ra_pcore_l p p1 pp. inversion pc. subst p0. trivial.
    + discriminate.
 - intros x cx pc. destruct x, cx.
    unfold pcore, inved_protocol_pcore in pc. destruct (pcore p) eqn:pp; try discriminate.
    have t := ra_pcore_idemp p p1 pp.
    inversion pc. subst p0.
    unfold pcore, inved_protocol_pcore. destruct (pcore p1) eqn:pp1.
    + unfold "≡". unfold option_equiv. apply Some_Forall2. unfold "≡".
      unfold inved_protocol_equiv. inversion t. trivial.
    + inversion t.
 - intros x y cx mle pc.
    destruct x, y, cx.
    unfold pcore, inved_protocol_pcore in pc. destruct (pcore p) eqn:pp; try discriminate.
    have mle2 := inved_incl_to_incl _ _ mle.
    inversion pc. subst p2.
    have t := ra_pcore_mono p p0 p1 mle2 pp.
    destruct t as [cy [t1 t2]].
    exists (Inved cy).
    split.
    + unfold pcore, inved_protocol_pcore. rewrite t1. trivial.
    + apply incl_to_inved_incl. trivial.
 - intros x y.  unfold "✓". unfold inved_protocol_valid. destruct x, y.
    assert (Inved p ⋅ Inved p0 = Inved (p ⋅ p0)) as X by trivial. rewrite X.
    intro eb.
    destruct eb as [b eb].
    exists (p0 ⋅ b).
    
    eapply inv_proper0. Focus 2. apply eb.
    
    symmetry. apply ra_assoc.
Qed.

Global Instance inved_protocol_equivalence
    {P}
    `{Equiv P}
    {equ: Equivalence (≡@{P})}
    : Equivalence (≡@{InvedProtocol P}).
Proof.
  split.
  - unfold Reflexive. intros. unfold "≡", inved_protocol_equiv. destruct x. trivial.
  - unfold Symmetric. intros x y. unfold "≡", inved_protocol_equiv. destruct x, y.
      intro. symmetry. trivial.
  - unfold Transitive. intros x y z. 
      unfold "≡", inved_protocol_equiv. destruct x, y, z.
      intros a1 a2. setoid_rewrite a1. trivial.
Qed.

Canonical Structure inved_protocolO
    {P}
    `{Equiv P}
    {equ: Equivalence (≡@{P})}
    := discreteO (InvedProtocol P).
    
Canonical Structure inved_protocolR
    `{Equiv P, PCore P, Op P, Inv P, Valid P, Unit P}
    {equ: Equivalence (≡@{P})}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
    (pm: ProtocolMixin P B)
    :=
   discreteR (InvedProtocol P) (inved_protocol_ra_mixin pm). 

Global Instance inved_protocol_unit P `{Unit P} : Unit (InvedProtocol P) := Inved (ε : P).

Definition inved_protocol_ucmra_mixin 
    `{Equiv P, PCore P, Op P, Inv P, Valid P, Unit P}
    {equ: Equivalence (≡@{P})}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
    (pm: ProtocolMixin P B) : UcmraMixin (InvedProtocol P).
Proof.
  destruct pm.
  split.
  - unfold "✓", inved_protocol_valid, ε, inved_protocol_unit. 
  
  

    
Context {Σ: gFunctors}.
Context `{!invGS Σ}.
Context `{!inG Σ (authR (inved_protocolR prot))}.

    
  
