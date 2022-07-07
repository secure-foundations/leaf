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

Require Import Two.inved.
Require Import Two.guard.

(*
Context {Σ: gFunctors}.
Context `{!invGS Σ}.
*)

Record StorageMixin P B
    `{Equiv P, PCore P, Op P, Valid P, Inv P}
    {equ: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B}
:= {
    protocol_mixin: ProtocolMixin P;
    base_ra_mixin: RAMixin B; (* completely ignore core *)
    
    interp: P -> B;

    interp_proper: Proper ((≡) ==> (≡)) (@inv P _);
}. 

Section PropMap.
  Context {Σ: gFunctors}.
  
  Context `{Equiv B, Op B, Valid B, Unit B}.
  
  Definition wf_prop_map (f: B -> iProp Σ) :=
      Proper ((≡) ==> (≡)) f
      /\ f ε ≡ (True)%I
      /\ (∀ a b , ✓(a ⋅ b) -> f (a ⋅ b) ≡ (f a ∗ f b) % I).
      
  
End PropMap.

Section StorageDefs.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{Equiv P, PCore P, Op P, Inv P, Valid P}.
  Context {equ: Equivalence (≡@{P})}.
  Context {storage_mixin: StorageMixin P B}.

  Definition storage_protocol_guards (p: P) (b: B) :=
      ∀ q , inv (p ⋅ q) -> b ≼ interp P B storage_mixin (p ⋅ q).
  
End StorageDefs.

Section StorageLogic.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{Equiv P, PCore P, Op P, Inv P, Valid P}.
  Context {equ: Equivalence (≡@{P})}.
  Context {storage_mixin: StorageMixin P B}.
  
  Context {Σ: gFunctors}.
  Context `{!inG Σ (authUR (inved_protocolUR (protocol_mixin P B storage_mixin)))}.
  Context `{!invGS Σ}.
  
  Definition maps (γ: gname) (f: B -> iProp Σ) : iProp Σ :=
      ⌜ wf_prop_map f ⌝ ∗
      ownI γ (
        ∃ (state: P) ,
          own γ (● (Inved state))
          ∗ ⌜ inv state ⌝
          ∗ (f (interp P B storage_mixin state))
      ). 
  
  Definition p_own (γ: gname) (p: P) : iProp Σ := own γ (◯ (Inved p)).
  
  Lemma logic_guard (p: P) (b: B)
    (g: storage_protocol_guards p b)
    : maps γ f ⊢ p_own γ p &&{ {[ γ ]} }&&> f b.
      

Print own.
    
  
End Storage.
