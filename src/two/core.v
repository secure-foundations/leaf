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

Require Import Two.own_updates.

Context (Σ : gFunctors).

Context (C: ucmra).
Context (Interp : C -> iProp Σ).
Context (inv_n : nat -> C -> Prop).
Context (inv_n_monotonic : ∀ c n1 n2 , inv_n n1 c -> n2 ≤ n1 -> inv_n n2 c).

Program Definition Inv_nPred (c : C) : nPred :=
  {| nPred_holds n := inv_n n c |}.
Next Obligation. 
intros. apply inv_n_monotonic with (n1 := n1); trivial.
Qed.

Definition Inv (c: C) : iProp Σ := uPred_of_nPred (Inv_nPred c).

(* draft 1 *)

Definition protocol_update x x' (P Q : iProp Σ) : Prop := ∀ (n: nat) (y: C) ,
    inv_n n (x ⋅ y) -> (inv_n n (x' ⋅ y) ∧
        (Interp (x ⋅ y) ∗ P)%I ≡{n}≡ (Interp (x' ⋅ y) ∗ Q)%I).
        
Lemma protocol_update_in_logic x x' (P Q : iProp Σ) : protocol_update x x' P Q ->
    ∀ y , Inv (x ⋅ y) ⊢ Inv (x' ⋅ y) ∧
        (Interp (x ⋅ y) ∗ P) ≡ (Interp (x' ⋅ y) ∗ Q).
Proof.
    intros.
    split.
   
    intros.
    unfold protocol_update in H.
    unfold uPred_holds.
    have q := H n y H1.
    generalize q.
    uPred.unseal.
    intuition.
Qed.

Definition protocol_update_with_b x x' b (P Q : iProp Σ) : Prop := ∀ (n: nat) (y: C) ,
    inv_n n (x ⋅ b ⋅ y) -> (inv_n n (x' ⋅ b ⋅ y) ∧
        (Interp (x ⋅ b ⋅ y) ∗ P)%I ≡{n}≡ (Interp (x' ⋅ b ⋅ y) ∗ Q)%I).

Lemma protocol_update_with_b_in_logic x x' b (P Q : iProp Σ) : protocol_update_with_b x x' b P Q ->
    ∀ y , Inv (x ⋅ b ⋅ y) ⊢ Inv (x' ⋅ b ⋅ y) ∧
        (Interp (x ⋅ b ⋅ y) ∗ P) ≡ (Interp (x' ⋅ b ⋅ y) ∗ Q).
Proof.
    intros.
    split.
   
    intros.
    unfold protocol_update in H.
    unfold uPred_holds.
    have q := H n y H1.
    generalize q.
    uPred.unseal.
    intuition.
Qed.

Definition upd_n (Q: iProp Σ) x (n: nat) :=
    ∀ k yf , k ≤ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ uPred_holds Q k x'.
      
Definition wand_n (P: iProp Σ) (Q: iProp Σ) x (n: nat) :=
   ∀ n' x', n' ≤ n → ✓{n'} (x ⋅ x') → uPred_holds P n' x' → uPred_holds Q n' (x ⋅ x').
   
(*
Definition wand_upd_n (P: iProp Σ) (Q: iProp Σ) x (n: nat) :=
    uPred_holds (P ==∗ Q)%I n x.
    *)

Definition wand_upd_n (P: iProp Σ) (Q: iProp Σ) x (n: nat) :=
   ∀ n' x', n' ≤ n → ✓{n'} (x ⋅ x') → uPred_holds P n' x' →
    ∀ k yf , k ≤ n' → ✓{k} (x ⋅ x' ⋅ yf) → ∃ x'', ✓{k} (x'' ⋅ yf) ∧ uPred_holds Q k x''.

Notation "P ={ n }=> Q" := (∀ x , wand_upd_n P Q x n)
  (at level 70).

(*
(* set x=unit *)
Definition wand_upd_n (P: iProp Σ) (Q: iProp Σ) (n: nat) :=
   ∀ n' x', n' ≤ n → ✓{n'} (x') → uPred_holds P n' x' →
    ∀ k yf , k ≤ n' → ✓{k} (x' ⋅ yf) → ∃ x'', ✓{k} (x'' ⋅ yf) ∧ uPred_holds Q k x''.

Notation "P ={ n }=> Q" := (wand_upd_n P Q n)
  (at level 70).
  *)
  
Definition protocol_update_with_upd x x' (P Q : iProp Σ) : Prop := ∀ (n: nat) (y: C) ,
    inv_n n (x ⋅ y) -> (inv_n n (x' ⋅ y) ∧
        (Interp (x ⋅ y) ∗ P)%I ={n}=> (Interp (x' ⋅ y) ∗ Q)%I).
        
Lemma protocol_update_with_upd_in_logic x x' (P Q : iProp Σ) : protocol_update_with_upd x x' P Q ->
    ∀ y , Inv (x ⋅ y) ⊢ Inv (x' ⋅ y) ∧
        (Interp (x ⋅ y) ∗ P) ==∗ (Interp (x' ⋅ y) ∗ Q).
Proof.
    intros.
    split.
    
   
    intros.
    unfold protocol_update_with_upd in H.
    unfold uPred_holds.
    
    
    have q := H n y H1.
    generalize q. clear q.
    uPred.unseal.
    intuition.
    
    unfold uPred_bupd_def. unfold uPred_holds.
    unfold uPred_sep_def.
    
    unfold wand_upd_n in H3. 
    unfold uPred_bupd_def in H3. unfold uPred_holds in H3.
    unfold uPred_sep_def in H3.
    
    apply H3; trivial.
    
    unfold uPred_and_def in H6. unfold uPred_sep_def in H6. unfold uPred_holds in H6.
    
    intuition.
Qed.
    
    
    
    
    unfold 
Qed.

  
  
  

Definition protocol_update_with_b x x' b (P Q : iProp Σ) : Prop := ∀ (n: nat) (y: C) ,
    inv_n n (x ⋅ b ⋅ y) -> (inv_n n (x' ⋅ b ⋅ y) ∧
        (Interp (x ⋅ b ⋅ y) ∗ P)%I ={n}=> (Interp (x' ⋅ b ⋅ y) ∗ Q)%I).

Lemma protocol_update_with_b_in_logic2 x x' b (P Q : iProp Σ) : protocol_update_with_b x x' b P Q ->
    ∀ y , Inv (x ⋅ b ⋅ y) ⊢ Inv (x' ⋅ b ⋅ y) ∧
        (Interp (x ⋅ b ⋅ y) ∗ P) ==∗ (Interp (x' ⋅ b ⋅ y) ∗ Q).
Proof.
  uPred.unseal.
  

    intros.
    split.
   
    intros.
    unfold protocol_update in H.
    unfold uPred_holds.
    have q := H n y H1.
    generalize q.
    uPred.unseal.
    intuition.
Qed.



(*
Context (C : ofe -> ucmra).
Context (Interp : ∀ (o: ofe), C o -> iProp Σ).

Class myG Σ := MyG { my_tokG :> inG Σ (authUR (C (iPropO Σ))) }.
Context `{!myG Σ}.
*)

(*
Print ofe.
Print OfeMixin.

Context (T: Type -> ucmra).

Context (F: Type -> ucmra).


Class myG Σ := MyG { my_tokG :> inG Σ (authUR (F (laterO (iPropO Σ)))) }.
Context `{!myG Σ}.

Print Σ.
Unset Printing Notations.
Print iPropO.
Print iProp.

Print uPred.
Print uPredO.
Print iProp.
Print iPropO.

Print uPred.
Print Ofe.

Definition f := F (iProp Σ).

Program Definition Inv_nPred (a : F (iProp Σ)) : nPred :=
  {| nPred_holds n := inv n |}.
Next Obligation. 
intros. trivial.
Qed.

*)
