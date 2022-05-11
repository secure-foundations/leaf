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

Require Import Two.auth_frag_util.
Require Import Two.own_updates2.

(* easiest, user-facing definition of a protocol *)

(*
Record SimpleProtocol A `{Op A} := {
  
}.
*)

(* my stuff *)


Print ofe.
Record ProtocolMixin (P: Type -> Type) := {
    protocol_dist: ∀ (A: ofe) , Dist (P A);
    protocol_equiv: ∀ (A: ofe) , Equiv (P A);
    protocol_pcore: ∀ (A: ofe) , PCore (P A);
    protocol_op: ∀ (A: ofe) , Op (P A);
    protocol_valid: ∀ (A: ofe) , Valid (P A);
    protocol_validN: ∀ (A: ofe) , ValidN (P A);
    protocol_unit: ∀ (A: ofe) , Unit (P A);
    
    protocol_ofe_mixin: ∀ (A: ofe) , OfeMixin (P A);
    protocol_cmra_mixin: ∀ (A: ofe) , CmraMixin (P A);
    protocol_ucmra_mixin: ∀ (A: ofe) , UcmraMixin (P A);
    
    protocol_map : ∀ {A B: Type} (f : A → B) , (P A) -> P B;
}.

Print protocol_dist.
Print protocol_dist.

Context (protocol: Type -> Type).
Context {protocol_mixin: ProtocolMixin protocol}.

Section protocol.
    Context {A: ofe}.

    Local Instance inst_protocol_dist : Dist (protocol A) :=
        protocol_dist protocol protocol_mixin A.
    Local Instance inst_protocol_equiv : Equiv (protocol A) :=
        protocol_equiv protocol protocol_mixin A.
    Local Instance inst_protocol_pcore : PCore (protocol A) :=
        protocol_pcore protocol protocol_mixin A.
    Local Instance inst_protocol_op : Op (protocol A) :=
        protocol_op protocol protocol_mixin A.
    Local Instance inst_protocol_valid : Valid (protocol A) :=
        protocol_valid protocol protocol_mixin A.
    Local Instance inst_protocol_validN : ValidN (protocol A) :=
        protocol_validN protocol protocol_mixin A.
    Local Instance inst_protocol_unit : Unit (protocol A) :=
        protocol_unit protocol protocol_mixin A.
    
    Canonical Structure protocolO := Ofe (protocol A)
        (protocol_ofe_mixin protocol protocol_mixin A).
    
    Canonical Structure protocolR : cmra := Cmra (protocol A)
        (protocol_cmra_mixin protocol protocol_mixin A).
        
    Canonical Structure protocolUR : ucmra := Ucmra (protocol A)
        (protocol_ucmra_mixin protocol protocol_mixin A).

End protocol.

Global Arguments protocolO : clear implicits.
Global Arguments protocolR : clear implicits.
Global Arguments protocolUR : clear implicits.

Program Definition protocol_map1 {A B} (f : A → B) (x : protocol A) : protocol B
  := protocol_map protocol protocol_mixin f x.

Section protocol_map.
  Context {A B : ofe} (f : A → B) {Hf: NonExpansive f}.
  Global Instance protocol_map_ne : NonExpansive (protocol_map1 f). Admitted.
  
    (*
  Local Instance protocol_map_proper : Proper ((≡) ==> (≡)) (protocol_map1 f) := ne_proper _.
  
  Global Instance protocol_map_morphism : CmraMorphism (protocol_map1 f).
  *)
End protocol_map.

Definition protocolO_map {A B} (f : A -n> B) : protocolO A -n> protocolO B :=
  OfeMor (protocol_map1 f : protocolO A → protocolO B). 
  
Global Instance protocolO_map_ne A B : NonExpansive (@protocolO_map A B).  Admitted.

(*
Program Definition protocolRF (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := protocolR (oFunctor_car F A B); 
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := protocolO_map (oFunctor_map F fg) 
|}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
*)

Program Definition protocolURF (F : oFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := protocolUR (oFunctor_car F A B); 
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg := protocolO_map (oFunctor_map F fg) 
|}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Global Instance protocolURF_contractive F : 
  oFunctorContractive F → urFunctorContractive (protocolURF F). 
  Admitted.


Class mylibG Σ := { mylib_inG : inG Σ (authUR (protocolUR (laterO (iPropO Σ)))) }.
Local Existing Instance mylib_inG.

Print "▶".
Definition mylibΣ : gFunctors := #[GFunctor (authRF (protocolURF (laterOF ∙)))].
Instance mysubG_libΣ {Σ} : subG mylibΣ Σ → mylibG Σ.
Proof. solve_inG. Qed.

(* stuff *)

Context (Σ : gFunctors).
Context `{!mylibG Σ}.

Definition C: ucmra := (protocolUR (laterO (iPropO Σ))).

Context (Interp : C -> iProp Σ).
Context (inv_n : nat -> C -> Prop).
Context (inv_n_monotonic : ∀ c n1 n2 , inv_n n1 c -> n2 ≤ n1 -> inv_n n2 c).


Lemma valid_defn n (a: C) : ✓{n} a <-> ∃ b , inv_n n (a ⋅ b). Admitted.

Instance proper_inv_1_n n : Proper ((≡{n}≡) ==> impl) (inv_n n). Admitted.

Instance proper_inv_2_n n : Proper (equiv ==> impl) (inv_n n).
Proof.
    unfold Proper, "==>", impl. intros.
    assert (x ≡{n}≡ y) as q.
    { setoid_rewrite H. trivial. }
    setoid_rewrite <- q. trivial.
Qed.

Instance non_expansive_interp : NonExpansive Interp.
Admitted.



Program Definition Inv_nPred (c : C) : nPred :=
  {| nPred_holds n := inv_n n c |}.
Next Obligation. 
intros. apply inv_n_monotonic with (n1 := n1); trivial.
Qed.

Definition Inv (c: C) : iProp Σ := uPred_of_nPred (Inv_nPred c).

Instance non_expansive_inv : NonExpansive Inv.
Proof.
  split. intros. unfold Inv. unfold uPred_holds, uPred_of_nPred.
  unfold nPred_holds, Inv_nPred.
  enough (x ≡{n'}≡ y) as eq.
  { split.
    { intro. setoid_rewrite <- eq. trivial. }
    { intro. setoid_rewrite eq. trivial. }
  }
  apply dist_le with (n0 := n); trivial.
Qed.
  

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
        ((Interp (x ⋅ b ⋅ y) ∗ P) ≡ (Interp (x' ⋅ b ⋅ y) ∗ Q)).
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
        ((Interp (x ⋅ y) ∗ P) ==∗ (Interp (x' ⋅ y) ∗ Q)).
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
    
    unfold uPred_bupd_def.
    unfold uPred_sep_def. unfold uPred_wand_def.
    unfold uPred_holds.
    
    unfold wand_upd_n in H3. 
    unfold uPred_bupd_def in H3. unfold uPred_holds in H3.
    unfold uPred_sep_def in H3.
    
    apply H3; trivial.
Qed.

Instance persistent_inv a : Persistent (Inv a).
Proof.
  split. intros. uPred.unseal. trivial.
Qed.
        
        (*
Lemma protocol_update_with_upd_in_logic_sep x x' (P Q : iProp Σ) : protocol_update_with_upd x x' P Q ->
    ∀ y , Inv (x ⋅ y) ⊢ Inv (x' ⋅ y) ∗
        ((Interp (x ⋅ y) ∗ P) ==∗ (Interp (x' ⋅ y) ∗ Q)).
Proof.
  intro. intro.
  iIntros "a".
  iDestruct (protocol_update_with_upd_in_logic x x' P Q with "a") as "a".
  { trivial. }
  iDestruct "a" as "[b c]".
  iFrame.
Qed.
*)

Definition protocol_update_with_upd_b x x' b (P Q : iProp Σ) : Prop := ∀ (n: nat) (y: C) ,
    inv_n n (x ⋅ b ⋅ y) -> (inv_n n (x' ⋅ b ⋅ y) ∧
        (Interp (x ⋅ b ⋅ y) ∗ P)%I ={n}=> (Interp (x' ⋅ b ⋅ y) ∗ Q)%I).
        
Lemma protocol_update_with_upd_b_in_logic x x' b (P Q : iProp Σ) : protocol_update_with_upd_b x x' b P Q ->
    ∀ y , Inv (x ⋅ b ⋅ y) ⊢ Inv (x' ⋅ b ⋅ y) ∧
        ((Interp (x ⋅ b ⋅ y) ∗ P) ==∗ (Interp (x' ⋅ b ⋅ y) ∗ Q)).
Proof.
    apply protocol_update_with_upd_in_logic.
Qed.
    
    
(* Class myG Σ := MyG { my_tokG :> inG Σ (authUR (F (laterO (iPropO Σ)))) }. *)

Print authUR.
Definition nondet_auth_update_inv_condition (𝛾: gname) (x x' z : C)
  (cond: ∀ y n , inv_n n (x ⋅ y) → inv_n n (x' ⋅ y)) :
    own 𝛾 (● z ⋅ ◯ x) ==∗
    ∃ p , own 𝛾 (● (x' ⋅ p) ⋅ ◯ x') ∗ (z ≡ x ⋅ p).
Proof.
  apply nondet_auth_update.
  intro y. intro n.
  rewrite valid_defn.
  rewrite valid_defn.
  intro h.
  destruct h as (b&q).
  exists b.
  setoid_replace (x' ⋅ y ⋅ b) with (x' ⋅ (y ⋅ b)).
  - setoid_replace (x ⋅ y ⋅ b) with (x ⋅ (y ⋅ b)) in q.
    + apply cond. trivial.
    + rewrite assoc. trivial.
  - rewrite assoc. trivial.
Qed.
   
Lemma internal_update 𝛾 (x x' z: C) (P Q : iProp Σ)
    : protocol_update_with_upd x x' P Q ->
      ⊢
        own 𝛾 (◯ x) ∗ P ∗
        own 𝛾 (● z) ∗ Interp z ∗ Inv z
        ==∗
        own 𝛾 (◯ x') ∗ Q ∗
        (∃ z , own 𝛾 (● z) ∗ Interp z ∗ Inv z).
Proof. 
    intro h.
    
    iIntros "[frag [p [auth interp_inv]]]".
    iMod (nondet_auth_update_inv_condition 𝛾 x x' z with "[auth frag]") as (p) "[[auth frag] eq]".
    {intros. have r := h n y. intuition. }
    { rewrite own_op. iFrame. }
    iRewrite "eq" in "interp_inv".
    iDestruct "interp_inv" as "[interp inv]".
    iDestruct (protocol_update_with_upd_in_logic x x' P Q h p with "[inv]") as "[inv t]".
    { iFrame. }
    iMod ("t" with "[interp p]") as "[interp q]".
    { iFrame. }
    iModIntro.
    iFrame.
    iExists (x' ⋅ p).
    iFrame.
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
