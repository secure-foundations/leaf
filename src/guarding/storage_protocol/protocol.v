From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

From stdpp Require Export namespaces.

Require Import guarding.internal.inved.
Require Import guarding.internal.auth_frag_util.
Require Import guarding.internal.wsat_util.
Require Import guarding.guard.
Require Import guarding.factoring_props.
Require Import guarding.own_and_own_sep.
Require Import guarding.own_and.

Class SPRel (P : Type) (B : Type) := sp_rel : P → B → Prop.

Class SPInv (P : Type) := sp_inv : P → Prop.
Class SPInterp (P : Type) (B : Type) := sp_interp : P → B.

Class StorageMixin P B
    `{Equiv P, PCore P, Op P, Valid P, Unit P}
    {equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B}
    {equ_b: @Equivalence B (≡)}
:= {
    protocol_ra_mixin: RAMixin P; (* ignore valid *)
    base_ra_mixin: RAMixin B; (* ignore core *)
    
    protocol_unit_left_id : LeftId equiv (ε : P) op;
    base_unit_left_id : LeftId equiv (ε : B) op;

    sp_rel_proper: Proper ((≡) ==> (≡) ==> (↔)) sp_rel;
    interp_val: ∀ (p: P) (b: B) , sp_rel p b → ✓ b;
}. 
Global Arguments protocol_ra_mixin (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_ra_mixin (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments protocol_unit_left_id (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_unit_left_id (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments sp_rel_proper (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments interp_val (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _} (_).

Class StorageMixinII P B
    `{Equiv P, PCore P, Op P, Valid P, Unit P}
    {equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPInv P, SPInterp P B}
    {equ_b: @Equivalence B (≡)}
:= {
    protocol_ra_mixin_ii: RAMixin P;
    base_ra_mixin_ii: RAMixin B; (* completely ignore core *)
    
    protocol_unit_left_id_ii : LeftId equiv (ε : P) op;
    base_unit_left_id_ii : LeftId equiv (ε : B) op;

    sp_inv_proper_ii: Proper ((≡) ==> (↔)) sp_inv;
    sp_interp_proper_ii: Proper ((≡) ==> (≡)) sp_interp;
    interp_val_ii: ∀ (p: P) , sp_inv p → ✓ (sp_interp p);
}.
Global Arguments protocol_ra_mixin_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_ra_mixin_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments protocol_unit_left_id_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments base_unit_left_id_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments sp_inv_proper_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments sp_interp_proper_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).
Global Arguments interp_val_ii (P B) {_ _ _ _ _ _ _ _ _ _ _ _ _ _} (_).

Section PropMap.
  Context {Σ: gFunctors}.
  Context `{Equiv B, Op B, Valid B, Unit B}.
  
  Definition wf_prop_map (f: B → iProp Σ) :=
      Proper ((≡) ==> (≡)) f
      ∧ f ε ≡ (True)%I
      ∧ (∀ a b , ✓(a ⋅ b) → f (a ⋅ b) ≡ (f a ∗ f b) % I).
End PropMap.

Section StorageRelations.
  Context `{Equiv P, PCore P, Op P, Valid P, Unit P, SPRel P B}.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  
  Definition storage_protocol_guards (p: P) (b: B) :=
      ∀ q (t: B) , sp_rel (p ⋅ q) t → b ≼ t.
      
  Definition storage_protocol_exchange (p1 p2: P) (b1 b2: B)  :=
      ∀ q t1, sp_rel (p1 ⋅ q) t1 →
          ∃ t2, sp_rel (p2 ⋅ q) t2
          ∧ ✓(t1 ⋅ b1)
          ∧ t1 ⋅ b1 ≡ t2 ⋅ b2.
          
  Definition storage_protocol_update (p1 p2: P) :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → sp_rel (p2 ⋅ q) t1.
          
  Definition storage_protocol_withdraw (p1 p2: P) (b2: B)  :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → ∃ t2, sp_rel (p2 ⋅ q) t2
          ∧ t1 ≡ t2 ⋅ b2.
          
  Definition storage_protocol_deposit (p1 p2: P) (b1: B)  :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → ∃ t2, sp_rel (p2 ⋅ q) t2
          ∧ ✓(t1 ⋅ b1)
          ∧ t1 ⋅ b1 ≡ t2.
          
  Definition storage_protocol_exchange_nondeterministic (p1: P) (b1: B) (output_ok: P → B → Prop)  :=
      ∀ q t1 , sp_rel (p1 ⋅ q) t1 → ∃ p2 b2 t2 , output_ok p2 b2
          ∧ sp_rel (p2 ⋅ q) t2
          ∧ ✓(t1 ⋅ b1)
          ∧ t1 ⋅ b1 ≡ t2 ⋅ b2.
End StorageRelations.

Section StorageRelationsII.
  Context {P B: Type}.
  Context `{Equiv P, PCore P, Op P, Valid P, Unit P, SPInv P, SPInterp P B}.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  
  Definition storage_protocol_guards_ii (p: P) (b: B) :=
      ∀ q , sp_inv (p ⋅ q) → b ≼ sp_interp (p ⋅ q).
      
  Definition storage_protocol_exchange_ii (p1 p2: P) (b1 b2: B)  :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ ✓(sp_interp (p1 ⋅ q) ⋅ b1)
          ∧ sp_interp (p1 ⋅ q) ⋅ b1 ≡ sp_interp (p2 ⋅ q) ⋅ b2.
          
  Definition storage_protocol_update_ii (p1 p2: P) :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ sp_interp (p1 ⋅ q) ≡ sp_interp (p2 ⋅ q).
          
  Definition storage_protocol_withdraw_ii (p1 p2: P) (b2: B)  :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ sp_interp (p1 ⋅ q) ≡ sp_interp (p2 ⋅ q) ⋅ b2.
          
  Definition storage_protocol_deposit_ii (p1 p2: P) (b1: B)  :=
      ∀ q , sp_inv (p1 ⋅ q) → sp_inv (p2 ⋅ q)
          ∧ ✓(sp_interp (p1 ⋅ q) ⋅ b1)
          ∧ sp_interp (p1 ⋅ q) ⋅ b1 ≡ sp_interp (p2 ⋅ q).
          
  Definition storage_protocol_exchange_nondeterministic_ii (p1: P) (b1: B) (output_ok: P → B → Prop) :=
      ∀ q , sp_inv (p1 ⋅ q) → ∃ p2 b2 , output_ok p2 b2
          ∧ sp_inv (p2 ⋅ q)
          ∧ ✓(sp_interp (p1 ⋅ q) ⋅ b1)
          ∧ sp_interp (p1 ⋅ q) ⋅ b1 ≡ sp_interp (p2 ⋅ q) ⋅ b2.
End StorageRelationsII.

Section StorageRelationsIILemmas.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{Equiv P, PCore P, Op P, Valid P, Unit P, SPInv P, SPInterp P B}.
  Context {equ_p: @Equivalence P (≡)}.
  Context {equ_b: @Equivalence B (≡)}.
  Context {storage_mixin_ii: StorageMixinII P B}.
  
  Global Instance sp_rel_of_ii : SPRel P B := λ p b , sp_inv p ∧ sp_interp p ≡ b.
          
  Local Instance base_ra_op_proper : Proper ((≡) ==> (≡) ==> (≡)) (@op B _).
  Proof using storage_mixin_ii.
    unfold Proper, "==>". intros x y Heq x0 y0 Heq0.
    enough (x ⋅ x0 ≡ y ⋅ x0) as X.
    { setoid_rewrite X.
      eapply (ra_op_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)). trivial. }
    setoid_rewrite (ra_comm _ (base_ra_mixin_ii _ _ storage_mixin_ii) x x0).
    setoid_rewrite (ra_comm _ (base_ra_mixin_ii _ _ storage_mixin_ii) y x0).
    eapply (ra_op_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)). trivial.
  Qed.
  
  Local Instance base_ra_valid_proper : Proper ((≡) ==> (↔)) (@valid B _).
  Proof using storage_mixin_ii.
    unfold Proper, "==>". intros x y Heq. split.
    - intros Hval. eapply (ra_validN_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)).
        { eapply Heq. } apply Hval.
    - intros Hval. eapply (ra_validN_proper _ (base_ra_mixin_ii _ _ storage_mixin_ii)).
        { symmetry. eapply Heq. } apply Hval.
  Qed.
  
  Lemma eq_storage_protocol_guards_ii (p: P) (b: B)
    : storage_protocol_guards p b ↔ storage_protocol_guards_ii p b.
  Proof using equ_b.
    unfold storage_protocol_guards, storage_protocol_guards_ii. split.
    - intros Q q spi. apply (Q q). split; trivial.
    - intros Q q t [Hi Heq]. destruct (Q q Hi) as [z Hj]. exists z.
      setoid_rewrite <- Heq. trivial.
  Qed.
   
  Lemma eq_storage_protocol_exchange_ii (p1 p2: P) (b1 b2: B)
    : storage_protocol_exchange p1 p2 b1 b2 ↔ storage_protocol_exchange_ii p1 p2 b1 b2.
  Proof using storage_mixin_ii.
    unfold storage_protocol_exchange, storage_protocol_exchange_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b [[Hbi Hbin] [Hc1 Hceq]]].
      + split; trivial.
      + split; trivial. split; trivial. setoid_rewrite Hbin. trivial.
    - intros Q q t1 [Hspi Heq]. exists (sp_interp (p2 ⋅ q)).
      destruct (Q q Hspi) as [Hspi2 [Hval Heq2]]. split; trivial.
      + split; trivial.
      + split; trivial.
        * setoid_rewrite <- Heq; trivial.
        * setoid_rewrite <- Heq; trivial.
  Qed.
  
  Lemma eq_storage_protocol_update_ii (p1 p2: P)
    : storage_protocol_update p1 p2 ↔ storage_protocol_update_ii p1 p2.
  Proof using equ_b.
    unfold storage_protocol_update, storage_protocol_update_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b Hb].
      + split; trivial.
      + split; trivial.
    - intros Q q t1 [Hspi Heq].
      destruct (Q q Hspi) as [Hspi2 Heq2]. split; trivial.
      + setoid_rewrite <- Heq2. trivial.
  Qed.
  
  Lemma eq_storage_protocol_withdraw_ii (p1 p2: P) (b2: B)
    : storage_protocol_withdraw p1 p2 b2 ↔ storage_protocol_withdraw_ii p1 p2 b2.
  Proof using storage_mixin_ii.
    unfold storage_protocol_withdraw, storage_protocol_withdraw_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b [[Hba Hbb] Hc]].
      + split; trivial.
      + split; trivial. setoid_rewrite Hbb. trivial.
    - intros Q q t1 [Hspi Heq]. exists (sp_interp (p2 ⋅ q)).
      destruct (Q q Hspi) as [Hspi2 Heq2]. split; trivial.
      + split; trivial.
      + setoid_rewrite <- Heq. trivial.
  Qed.
  
  Lemma eq_storage_protocol_deposit_ii (p1 p2: P) (b1: B)
    : storage_protocol_deposit p1 p2 b1 ↔ storage_protocol_deposit_ii p1 p2 b1.
  Proof using storage_mixin_ii.
    unfold storage_protocol_deposit, storage_protocol_deposit_ii. split.
    - intros Q q Hspi. destruct (Q q (sp_interp (p1 ⋅ q))) as [b [[Hbi Hbin] [Hc1 Hceq]]].
      + split; trivial.
      + split; trivial. split; trivial. setoid_rewrite Hbin. trivial.
    - intros Q q t1 [Hspi Heq]. exists (sp_interp (p2 ⋅ q)).
      destruct (Q q Hspi) as [Hspi2 [Hval Heq2]]. split; trivial.
      + split; trivial.
      + split; trivial.
        * setoid_rewrite <- Heq; trivial.
        * setoid_rewrite <- Heq; trivial.
  Qed.
  
  Lemma eq_storage_protocol_exchange_nondeterministic_ii (p1: P) (b1: B) (output_ok: P → B → Prop)
    : storage_protocol_exchange_nondeterministic p1 b1 output_ok
      ↔ storage_protocol_exchange_nondeterministic_ii p1 b1 output_ok.
  Proof using storage_mixin_ii.
    unfold storage_protocol_exchange_nondeterministic,
      storage_protocol_exchange_nondeterministic_ii. split.
     - intros Q q Hspi.
        destruct (Q q (sp_interp (p1 ⋅ q))) as [p2 [b2 [t2 [Hoo [Hrel [Hval Heq]]]]]].
      + split; trivial.
      + destruct Hrel as [Ha Hb]. exists p2. exists b2. split; trivial. split; trivial.
        split; trivial. setoid_rewrite Hb. trivial.
     - intros Q q t1 [Hinv Hint]. destruct (Q q Hinv) as [p2 [b2 [Hoo [Hspinv [Hval Heq]]]]].
        exists p2. exists b2. exists (sp_interp (p2 ⋅ q)). split; trivial.
        split.
        + split; trivial.
        + split.
          * setoid_rewrite <- Hint. trivial.
          * setoid_rewrite <- Hint. trivial.
  Qed.
End StorageRelationsIILemmas.

Global Instance storage_mixin_from_ii
  `{Equiv B, PCore B, Op B, Valid B, Unit B}
  `{Equiv P, PCore P, Op P, Valid P, Unit P, SPInv P, SPInterp P B}
  {equ_p: @Equivalence P (≡)}
  {equ_b: @Equivalence B (≡)}
  (storage_mixin_ii: StorageMixinII P B) : StorageMixin P B.
Proof.
    split.
     - apply (protocol_ra_mixin_ii P B storage_mixin_ii).
     - apply (base_ra_mixin_ii P B storage_mixin_ii).
     - apply (protocol_unit_left_id_ii P B storage_mixin_ii).
     - apply (base_unit_left_id_ii P B storage_mixin_ii).
     - intros x y Heq x0 y0 Heq0. split.
        + intros [Hinv HeqX]. split.
          * rewrite (sp_inv_proper_ii _ _ storage_mixin_ii). { apply Hinv. } symmetry.
              apply Heq.
          * setoid_rewrite Heq0 in HeqX.
            rewrite (sp_interp_proper_ii _ _ storage_mixin_ii). { apply HeqX. }
            symmetry. apply Heq.
        + intros [Hinv HeqX]. split.
          * rewrite (sp_inv_proper_ii _ _ storage_mixin_ii). { apply Hinv. }
              apply Heq.
          * setoid_rewrite <- Heq0 in HeqX.
            rewrite (sp_interp_proper_ii _ _ storage_mixin_ii). { apply HeqX. }
            apply Heq.
     - intros p b [Ha Hb]. rewrite base_ra_valid_proper. 
      { apply (interp_val_ii _ _ storage_mixin_ii). apply Ha. } { trivial. }
Qed.

Local Instance sp_rel_pinv {P B : Type} {ir: SPRel P B} : InternalPInv P :=
  λ p , ∃ b , sp_rel p b.
  
Local Definition internal_protocol_mixin_storage_mixin
    `{Equiv P, PCore P, Op P, Valid P, Unit P}
    {equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B}
    {equ_b: @Equivalence B (≡)}
    (storage_mixin: StorageMixin P B)
    : InternalProtocolMixin P.
Proof.
  destruct storage_mixin as [Q1 Q2 Q3 Q4 irp Q5]. split; trivial.
  unfold Proper, "==>", impl. intros x y Heq. unfold pinv, sp_rel_pinv.
  intros [b J]. unfold Proper, "==>", impl in irp.
  setoid_rewrite (irp x y _ b b) in J; trivial. exists b. trivial.
Qed.

Class sp_logicG
    `{Equiv P, PCore P, Op P, Valid P, Unit P} `{equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B} `{equ_b: @Equivalence B (≡)}
    (storage_mixin: StorageMixin P B) Σ
:= {
  #[local] sp_authG :: inG Σ (authUR (inved_protocolUR
                          (internal_protocol_mixin_storage_mixin storage_mixin)))
}.

Definition sp_logicΣ
    `{Equiv P, PCore P, Op P, Valid P, Unit P} `{equ_p: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B} `{equ_b: @Equivalence B (≡)}
    (storage_mixin: StorageMixin P B)
: gFunctors := #[
  GFunctor (authUR (inved_protocolUR
                          (internal_protocol_mixin_storage_mixin storage_mixin)))
].

Global Instance subG_sp_logicΣ
  `{Equiv P, PCore P, Op P, Valid P, Unit P} `{equ_p: @Equivalence P (≡)}
  `{Equiv B, PCore B, Op B, Valid B, Unit B, SPRel P B} `{equ_b: @Equivalence B (≡)}
  (storage_mixin: StorageMixin P B) Σ
    : subG (sp_logicΣ storage_mixin) Σ → sp_logicG storage_mixin Σ.
Proof.
  solve_inG.
Qed.

Section StorageLogic.
  Context {P B : Type}.
  Context `{Equiv P, PCore P, Op P, Valid P, HPUnit: Unit P, SPRel P B}.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{equ_p: @Equivalence P (≡)}.
  Context `{equ_b: @Equivalence B (≡)}.
  Context `{storage_mixin: !StorageMixin P B}.

  Local Instance sm_interp_proper
      : Proper ((≡) ==> (≡) ==> (↔)) (sp_rel).
  Proof using storage_mixin.
    destruct storage_mixin. trivial.
  Qed.
  
  Local Instance sm_pinv_proper
      : Proper ((≡) ==> (↔)) (@pinv P sp_rel_pinv).
  Proof using storage_mixin.
    unfold Proper, "==>", pinv. intros x y Heq. split.
    -  unfold sp_rel_pinv. intros [b Hx]. exists b. setoid_rewrite <- Heq. trivial.
    -  unfold sp_rel_pinv. intros [b Hy]. exists b. setoid_rewrite Heq. trivial.
  Qed.

  Local Instance inved_proper
      : Proper ((≡) ==> (≡)) (@Inved P).
  Proof.
    unfold Proper, "==>". intros.
    unfold "≡", inved_protocol_equiv. trivial.
  Qed.
                   
  Global Instance my_discrete : CmraDiscrete (inved_protocolR (internal_protocol_mixin_storage_mixin storage_mixin)).
  Proof. apply discrete_cmra_discrete. Qed.

  Context {Σ: gFunctors}.
  Context `{sp_i: !sp_logicG storage_mixin Σ}.
  Context `{!invGS Σ}.
  
  Definition sp_sto (γ: gname) (f: B → iProp Σ) : iProp Σ :=
      ⌜ wf_prop_map f ⌝ ∗
      own γ (◯ (Inved ε)) ∗
      ownI γ (
        ∃ (state_t: P * B) ,
          own γ (● (Inved (fst state_t)))
          ∗ ⌜ sp_rel (fst state_t) (snd state_t) ⌝
          ∗ (f (snd state_t))
      ). 
     
  Local Definition sp_own_def (γ: gname) (p: P) : iProp Σ := own γ (◯ (Inved p)).
  Local Definition sp_own_aux : seal (@sp_own_def). Proof. by eexists. Qed.
  Definition sp_own := sp_own_aux.(unseal).
  Local Definition sp_own_eq : @sp_own = @sp_own_def := sp_own_aux.(seal_eq).
  
  Lemma pcore_inved_unit
    : (pcore (Inved (ε : P)) ≡ Some (Inved ε)).
  Proof using equ_p storage_mixin.
    unfold pcore, inved_protocol_pcore. destruct (pcore ε) as [p|] eqn:x.
    {
      have p_ra_mixin := (protocol_ra_mixin _ _ storage_mixin).
      have k := ra_pcore_l _ p_ra_mixin (ε: P) p x.
      generalize k. rewrite ra_comm; trivial. rewrite protocol_unit_left_id; trivial.
      intro R. setoid_rewrite R. trivial.
    }
    trivial.
  Qed.
  
  Local Instance pers_own_frag_inved_unit γ : Persistent (own γ (◯ (Inved (ε: P)))).
  Proof using equ_p.
    apply own_core_persistent. apply auth_frag_core_id. unfold CoreId. apply pcore_inved_unit.
  Qed.
  
  Global Instance pers_sto γ f : Persistent (sp_sto γ f).
  Proof using equ_p. apply _. Qed.
   
  Lemma apply_timeless_rhs4 (X Y Z W V : iProp Σ) (ti: Timeless Z) (ti2: Timeless W)
      : X ∧ (Y ∗ ▷ (Z ∗ W ∗ V)) -∗ ◇ (X ∧ (Y ∗ Z ∗ W ∗ ▷ (V))).
  Proof.
      iIntros "l".
      rewrite bi.except_0_and. iSplit.
      { iDestruct "l" as "[l _]". iModIntro. iFrame. }
      iDestruct "l" as "[_ [l [lat0 [lat1 lat2]]]]".
      iMod "lat0" as "lat0".
      iMod "lat1" as "lat1".
      iModIntro. iFrame.
  Qed.
  
  Lemma and_rhs3_entails (X Y Z W V : iProp Σ)
      : (X ∧ (Y ∗ Z ∗ W ∗ V)) ⊢ W.
  Proof.
    iIntros "x". iDestruct "x" as "[_ [_ [_ [w _]]]]". iFrame.
  Qed.
  
  Lemma incl_of_inved_incl_assumes_unital (p1 p2 : P)
    (incll :
      @included (InvedProtocol P) (inved_protocol_equiv P) (inved_protocol_op P)
      (Inved p1) (Inved p2)) : p1 ≼ p2.
  Proof using storage_mixin.
    unfold "≼" in incll. destruct incll as [z incll].
    destruct z as [|p].
    - unfold "⋅", inved_protocol_op, "≡", inved_protocol_equiv in incll.
      unfold "≼". exists ε.
      setoid_rewrite (@comm P).
      + setoid_rewrite incll.
        setoid_rewrite protocol_unit_left_id; trivial. apply storage_mixin.
      + apply (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
   - unfold "≡", inved_protocol_equiv, "⋅", inved_protocol_op in incll.
      unfold "≼". exists p. trivial.
  Qed.
  
  Lemma auth_frag_conjunct_to_incl (γ: gname) (p state: P) (W: iProp Σ)
      : own γ (◯ Inved p) ∧ (own γ (● Inved state) ∗ W) ⊢ ⌜ p ≼ state ⌝. 
  Proof.
    iIntros "x".
    iAssert (((own γ (● Inved state)) ∧ (own γ (◯ Inved p)))%I) with "[x]" as "t".
    { iSplit. 
        { iDestruct "x" as "[_ [x _]]". iFrame. }
        { iDestruct "x" as "[x _]". iFrame. }
    }
    iDestruct (auth_frag_conjunct with "t") as "%incll".
    iPureIntro.
    apply incl_of_inved_incl_assumes_unital. trivial.
  Qed.
  
  (* SP-Guard *)
  
  Lemma sp_guard (p: P) (b: B) (γ: gname) (E: coPset) (f: B → iProp Σ)
    (g: storage_protocol_guards p b)
    (is_in: γ ∈ E)
    : sp_sto γ f ⊢ (sp_own γ p &&{ E }&&> ▷ f b).
  Proof using equ_p.
    unfold sp_sto. iIntros "[%wfm [#ounit #oinv]]".
    iDestruct (guards_from_inv _ _ E with "oinv") as "mg". { set_solver. }
    assert (Inhabited (P * B)) as IP. { apply populate. apply (ε, ε). }
    rewrite bi.later_exist.
    iDestruct (guards_true E (sp_own γ p)) as "gt".
    iDestruct (guards_transitive _ (sp_own γ p) True%I with "[gt mg]") as "gg".
      { iFrame "gt". iFrame "mg". }
    iDestruct (lguards_exists_with_lhs (P*B) (sp_own γ p) 
      (λ (state_t: P*B), (▷ (⌜ p ≼ state_t.1 ⌝))%I)
      (λ (state_t: P*B), (▷ (own γ (● Inved state_t.1) ∗ ⌜sp_rel state_t.1 state_t.2⌝ ∗ f state_t.2))%I)
      E 0
      with "[gg]") as "ggg".
    {
      iIntros (x) "o". rewrite sp_own_eq. unfold sp_own_def. iNext. iDestruct (auth_frag_conjunct_to_incl with "o") as "o"; trivial.
    }
    { unfold guards. iFrame "gg". }
    assert ((∃ x, ▷ (own γ (● Inved x.1) ∗ ⌜sp_rel x.1 x.2⌝ ∗ f x.2) ∗ ▷ ⌜p ≼ x.1⌝)
      ⊣⊢ (▷ f b ∗ ▷(f b -∗ ∃ x, (own γ (● Inved x.1) ∗ ⌜sp_rel x.1 x.2⌝ ∗ f x.2) ∗ ⌜p ≼ x.1⌝)))
      as Equ.
    { iIntros. iSplit. { iIntros "r".
      rewrite <- bi.later_sep. iNext.
      iDestruct "r" as (state) "[[r [%pi t]] %p_incl_x]".
      unfold storage_protocol_guards in g.
      have p_incl_x_copy := p_incl_x.
      unfold "≼" in p_incl_x. destruct p_incl_x as [z p_incl_x].
      assert (sp_rel (p ⋅ z) state.2) as pinv_pz.
          { setoid_rewrite <- p_incl_x. trivial. }
      have b_le_interp := g z (state.2) pinv_pz.
      destruct b_le_interp as [bz b_le_interp].
      
      unfold wf_prop_map in wfm.
      destruct wfm as [fprop [funit fop]].

      assert (✓ (b ⋅ bz)) as is_val.
      { destruct (base_ra_mixin _ _ storage_mixin).
          setoid_rewrite <- b_le_interp.
          apply (interp_val _ _ storage_mixin) with (p := p ⋅ z). trivial. }
          
      setoid_rewrite b_le_interp.
      setoid_rewrite fop; trivial.

      iDestruct "t" as "[fb fbz]".
      iFrame "fb".
      iIntros "fb".
      iExists state.
      
      setoid_rewrite b_le_interp.
      setoid_rewrite fop; trivial.
      iFrame. iSplit; iPureIntro; trivial.
      setoid_rewrite p_incl_x. setoid_rewrite <- b_le_interp.
      trivial.
    }
    { iIntros "[a b]". 
      iDestruct ("b" with "a") as "b".
      rewrite bi.later_exist.
      iDestruct "b" as (state) "b". iExists state.
      rewrite bi.later_sep. iFrame.
    } }    
    setoid_rewrite Equ.
    iApply guards_weaken_rhs_l. iFrame "ggg".
  Qed.
   
  Lemma own_sep_inv_incll_helper_nondet (p1 st : P) (t1 : B) (output_ok : P → P → Prop)
    (cond : ∀ (q : P) , sp_rel (p1 ⋅ q) t1 → ∃ p2 t2 , output_ok p2 q ∧ sp_rel (p2 ⋅ q) t2)
   : ∀ (z: InvedProtocol P) , sp_rel st t1 → ✓ (Inved st) → Inved p1 ⋅ z ≡ Inved st →
    ∃ p2 , output_ok p2 (match z with Inved z0 => z0 | Nah => ε end) ∧ ✓ (Inved p2 ⋅ z).
  Proof using storage_mixin.
  intros z inv v eq.
    destruct z as [|p].
    - unfold "⋅", inved_protocol_op.
      unfold "⋅", inved_protocol_op in eq.
      unfold "≡", inved_protocol_equiv in eq.
      unfold "✓", inved_protocol_valid. 
      
      setoid_rewrite <- eq in v.
      {
        unfold "✓", inved_protocol_valid in v. 
        destruct v as [v pi].
        assert (p1 ⋅ (@ε _ HPUnit) ≡ p1) as eq2.
        { 
            rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
            apply (protocol_unit_left_id P B storage_mixin).
        }
        assert (sp_rel (p1 ⋅ (@ε _ HPUnit)) t1) as pi2.
        {
          setoid_rewrite eq2. setoid_rewrite eq. trivial.
        }
        have c := cond (@ε _ HPUnit) pi2.
        destruct c as [p2 [b [oo c]]].
        exists p2.
        split. { apply oo. }
        exists ε.
        trivial.
        unfold pinv, sp_rel_pinv. exists b. apply c.
      }
      { apply (internal_protocol_mixin_storage_mixin storage_mixin). }
    - unfold "⋅", inved_protocol_op in eq.
      unfold "≡", inved_protocol_equiv in eq.
      unfold "⋅", inved_protocol_op.
      
      setoid_rewrite <- eq in v.
      {
        unfold "✓", inved_protocol_valid in v.
        unfold "✓", inved_protocol_valid.
        destruct v as [v pi].
        
        assert (sp_rel (p1 ⋅ p) t1) as pinv1. {
          setoid_rewrite eq. trivial.
        }
        have c := cond p pinv1.
        destruct c as [p2 [b [oo c]]].
        exists p2.
        split; trivial.
        exists ε.
        
        assert (p2 ⋅ p ⋅ (@ε _ HPUnit) ≡ p2 ⋅ p) as eq2.
        { 
            rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
            apply (protocol_unit_left_id _ _ storage_mixin).
        }
        setoid_rewrite eq2. exists b. trivial.
      }
      { apply (internal_protocol_mixin_storage_mixin storage_mixin). }
  Qed.
  
  Lemma op_nah (p1 state : P)
    : Inved p1 ⋅ Nah ≡ Inved state → p1 ≡ state.
  Proof. intros. trivial. Qed.
  
  Lemma op_inved_inved (p1 p2 p : P)
    : Inved p1 ⋅ Inved p2 ≡ Inved p → p1 ⋅ p2 ≡ p.
  Proof. intros. trivial. Qed.
        
  Lemma own_sep_inv_incll_nondet γ (p1 state : P) (t1: B) (output_ok: P → P → Prop)
      (cond: ∀ q , sp_rel (p1 ⋅ q) t1 → ∃ p2 t2 , output_ok p2 q ∧ sp_rel (p2 ⋅ q) t2)
      (pi: sp_rel state t1)
    : own γ (◯ Inved p1) ∗ own γ (● Inved state) ==∗
      ∃ (z p2: P) , ⌜ output_ok p2 z ∧ state ≡ p1 ⋅ z ⌝
          ∗ own γ (◯ Inved p2) ∗ own γ (● Inved (p2 ⋅ z)).
  Proof using storage_mixin.
   iIntros "[x y]".
   iDestruct (own_valid with "y") as "%val".
    iMod (own_sep_auth_incll_nondet γ (Inved p1) (Inved state)
    (λ p q , match p with
      | Inved a => output_ok a (match q with Inved b => b | Nah => ε end)
      | Nah => False
    end)
     with "[x y]") as "x".
    {
      intro z. intro equi.
      assert (✓ Inved state) as val2. { generalize val. rewrite auth_auth_valid. trivial. }
      have rr := own_sep_inv_incll_helper_nondet p1 state t1 output_ok cond z pi val2 equi.
      destruct rr as [p2 [rr v]]. exists (Inved p2). split; trivial.
    }
    { iFrame. }
    iDestruct "x" as (z p2) "[%eq [frag auth]]".
    destruct eq as [big_oo eq].
    destruct p2 as [|p2]. { intuition. }
    destruct z as [|p].
    {
      have eq0 := op_nah _ _ eq.
      assert (Inved p2 ⋅ Nah ≡ Inved p2) as eq1 by trivial.
      setoid_rewrite eq1.
      iExists (ε:P).
      assert (p2 ⋅ ε ≡ p2) as eq2.
      { 
        rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
        apply (protocol_unit_left_id _ _ storage_mixin).
      }
      iModIntro. iExists p2.
      setoid_rewrite eq2.
      iFrame.
      iPureIntro.
      split. { trivial. }
      assert (p1 ⋅ ε ≡ p1) as eq3.
      { 
        rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
        apply (protocol_unit_left_id _ _ storage_mixin).
      }
      setoid_rewrite eq3. symmetry. trivial.
    }
    {
      iExists p.
      
      assert (Inved p2 ⋅ Inved p ≡ Inved (p2 ⋅ p)) as eq0 by trivial.
      setoid_rewrite eq0.
      iModIntro. iExists p2. iFrame.
      iPureIntro. split. { apply big_oo. } symmetry. apply op_inved_inved. trivial.
    }
  Qed.
   
  Lemma own_inved_op_both (a b: P) γ :
      own γ (◯ Inved a) ∗ own γ (◯ Inved b) ⊣⊢ own γ (◯ Inved (a ⋅ b)).
  Proof.
    rewrite <- own_op.
    replace (◯ Inved a ⋅ ◯ Inved b) with (@auth_frag
          (inved_protocolUR
                          (internal_protocol_mixin_storage_mixin storage_mixin))
          (@Inved P (a ⋅ b))); trivial.
  Qed.
          
  Lemma own_inved_op (a b: P) γ :
      own γ (◯ Inved a) ∗ own γ (◯ Inved b) ⊢ own γ (◯ Inved (a ⋅ b)).
  Proof. rewrite own_inved_op_both. trivial. Qed.
      
  Lemma own_inved_op_split (a b: P) γ :
      own γ (◯ Inved (a ⋅ b)) ⊢ own γ (◯ Inved a) ∗ own γ (◯ Inved b).
  Proof. rewrite own_inved_op_both. trivial. Qed.
    
  Lemma sp_exchange_nondeterministic
    (p1: P) (b1: B) (output_ok: P → B → Prop) (γ: gname) (f: B → iProp Σ)
    (exchng: storage_protocol_exchange_nondeterministic p1 b1 output_ok)
    : sp_sto γ f ⊢
        sp_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗
          ∃ p2 b2 , ⌜ output_ok p2 b2 ⌝ ∗ sp_own γ p2 ∗ ▷ f b2.
  Proof.
    unfold sp_sto. rewrite sp_own_eq. unfold sp_own_def.
    iIntros "[%wfm [#ounit #m]] [p f]".
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iDestruct (ownI_open with "[w m oe]") as "[w [latp od]]".
    { iFrame "w". iFrame "m". iFrame "oe". }
    iMod (bi.later_exist_except_0 with "latp") as (state_t) "lat".
    iDestruct "lat" as "[ois [ps fi]]".
    iMod "ois" as "ois".
    iMod "ps" as "%ps".
    unfold sp_own.
    iMod (own_sep_inv_incll_nondet γ p1 state_t.1 state_t.2 (λ p2 q , ∃ b2 t2 , output_ok p2 b2
          ∧ sp_rel (p2 ⋅ q) t2
          ∧ ✓(state_t.2 ⋅ b1)
          ∧ state_t.2 ⋅ b1 ≡ t2 ⋅ b2) with "[p ois]")
        as (z p2) "[[%big_output_ok %incll] [p ois]]".
    { unfold storage_protocol_exchange in exchng. intros q pi.
        have exch := exchng q state_t.2 pi. destruct exch as [p2 [b2 [t2 exch]]]. exists p2. exists t2. intuition. exists b2. exists t2. intuition. }
    { trivial. }
    { iFrame. }
    destruct big_output_ok as [b2 [t2 [oo [pix [vix interp_eq]]]]].
    
    destruct wfm as [f_prop [f_unit f_op]]. (* need f Proper for the next step *)
    
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ z)) as pinv_p1_z. {
        exists (state_t.2). setoid_rewrite <- incll. trivial.
    }

    assert (✓ (t2 ⋅ b2)) as val_interp2.
    {
      destruct (base_ra_mixin _ _ storage_mixin).
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ (state0_t0 : P * B),
          own γ (● Inved state0_t0.1) ∗ ⌜sp_rel state0_t0.1 state0_t0.2⌝ ∗ f state0_t0.2)%I)
          with "[ois fi]"
          as "inv_to_return".
    {
      iModIntro. (* strip later *)
      iExists (p2 ⋅ z, t2). iFrame "ois". iFrame "fi".
      iPureIntro. trivial.
    }
    iDestruct (ownI_close γ _ with "[w m inv_to_return od]") as "[w en]".
    { iFrame "m". iFrame "inv_to_return". iFrame "w". iFrame "od". }
    iModIntro. iModIntro. iFrame.
    iPureIntro. apply oo.
  Qed.
   
  (* SP-Exchange *)
   
  Lemma sp_exchange
    (p1 p2: P) (b1 b2: B) (γ: gname) (f: B → iProp Σ)
    (exchng: storage_protocol_exchange p1 p2 b1 b2)
    : sp_sto γ f ⊢
        sp_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ sp_own γ p2 ∗ ▷ f b2.
  Proof.
    iIntros "x y".
    iDestruct (sp_exchange_nondeterministic p1 b1 (λ p b, p = p2 ∧ b = b2) γ f with "x y") as "J".
    { unfold storage_protocol_exchange in exchng.
      unfold storage_protocol_exchange_nondeterministic.
      intros q t1 pi. exists p2. exists b2.
      have ex := exchng q t1 pi. destruct ex as [t2 ex]. exists t2. intuition.
    }
    iMod "J" as (p0 b0) "[[%eq1 %eq2] t]". iModIntro. rewrite eq1. rewrite eq2. iFrame.
  Qed.
   
  Lemma sp_exchange_with_extra_guard_nondeterministic_with_later
    (p1 q: P) (b1: B) (output_ok: P → B → Prop) (γ: gname) (f: B → iProp Σ) (G: iProp Σ) E n
    (exchng: storage_protocol_exchange_nondeterministic (p1 ⋅ q) b1
        (λ p2_q b2 , ∃ p2 , p2_q = p2 ⋅ q ∧ output_ok p2 b2))
    (gname_in_e: γ ∈ E)
    : sp_sto γ f ∗ (G &&{ E ; n }&&> sp_own γ q) ⊢
        G ∗ sp_own γ p1 ∗ ▷ f b1 ={ E, ∅ }=∗ ▷^n (|={ ∅, E }=> ∃ p2 b2 ,
            ⌜ output_ok p2 b2 ⌝ ∗ G ∗ sp_own γ p2 ∗ ▷ f b2).
  Proof.
    unfold sp_sto. rewrite sp_own_eq. unfold sp_own_def.
    iIntros "[[%wfm [#ounit #m]] #gu] [g [p f]]".
    iDestruct (guards_from_inv _ _ E with "m") as "mg". { set_solver. }
    iDestruct (guards_true E G) as "gt".
    iDestruct (guards_transitive _ G True%I with "[gt mg]") as "gg".
    { iFrame "gt". iFrame "mg". }
    iDestruct (lguards_weaken_later _ _ _ 0 n with "[gg]") as "ggg". { lia. }
    { iFrame "gg". }
    iDestruct (lguards_open_two_simultaneously G _ _ E E n with "[g ggg gu]") as "opened".
    { set_solver. }
    { iFrame "g". iSplit. { iFrame "ggg". } iFrame "gu". }
    iMod "opened" as (T) "[t [tinv [town back]]]".
    
    iAssert ((▷^n (◇ own γ (◯ Inved q) ∧ (
          ◇ (▷ (∃ state_t : (P * B), own γ (● Inved state_t.1) ∗ ⌜sp_rel state_t.1 state_t.2⌝ ∗ f state_t.2) -∗ T)
          ∗
          ◇ (∃ state_t : (P * B), ▷
                (own γ (● Inved state_t.1) ∗ ⌜sp_rel state_t.1 state_t.2⌝ ∗ f state_t.2))
          )))%I)
          with "[t tinv town]" as "x".
    { iSplit. { iDestruct ("town" with "t") as "town". iNext. unfold sp_own.
        iDestruct "town" as "[x y]". iFrame "x". }
        iDestruct ("tinv" with "t") as "[tinv back]".
        iFrame "back". iNext. iMod "tinv" as "tinv".
        iMod (bi.later_exist_except_0 with "tinv") as (state0) "tinv".
        iModIntro. iExists state0. iFrame "tinv".
    }
    
    replace (E ∖ E) with (@empty coPset coPset_empty) by set_solver.
    iModIntro. iNext.
    
    rewrite <- bi.except_0_sep.
    rewrite <- bi.except_0_and.
    iMod "x" as "x".
    
    rewrite bi.sep_exist_l.
    rewrite bi.and_exist_l.
    iDestruct "x" as (state0) "x".
    iMod (apply_timeless_rhs4 with "x") as "x".
    iDestruct (and_rhs3_entails with "x") as "%pinvs".
    unfold sp_own.
    
    iAssert (own γ (◯ Inved q) ∧ own γ (● Inved state0.1) ∗ ((▷ (∃ state_t : P * B, own γ (● Inved state_t.1) ∗ ⌜sp_rel state_t.1 state_t.2⌝ ∗ f state_t.2) -∗ T) ∗ ⌜sp_rel state0.1 state0.2⌝ ∗ ▷ f state0.2))%I with "[x]" as "x".
      { iSplit. { iDestruct "x" as "[x _]". iFrame. }
          iDestruct "x" as "[_ [x [y z]]]". iFrame. }
          
    iDestruct (andsep_to_sepand_ucmra with "x") as "[x y]".
      { apply auth_frag_disjointness. }
      
    iDestruct (own_separates_out γ (◯ Inved q) (own γ (◯ Inved q) ∧ (▷ (∃ state_t : P * B, own γ (● Inved state_t.1) ∗ ⌜sp_rel state_t.1 state_t.2⌝ ∗ f state_t.2) -∗ T) ∗ ⌜sp_rel state0.1 state0.2⌝ ∗ ▷ f state0.2) with "[y]") as "[y z]".
      { iFrame "y". iIntros "[k _]". iFrame. }
      
    iDestruct (own_inved_op p1 q γ with "[p y]") as "own_p_q". { iFrame. }
    iMod (own_sep_inv_incll_nondet γ (p1 ⋅ q) state0.1 state0.2 (λ p2_q r , ∃ p2 b2 t2 , p2_q = p2 ⋅ q ∧ output_ok p2 b2
          ∧ sp_rel ((p2 ⋅ q) ⋅ r) t2
          ∧ ✓(state0.2 ⋅ b1)
          ∧ state0.2 ⋅ b1 ≡ t2 ⋅ b2) with "[own_p_q x]")
          as (z p2_q) "[%incll [own_p_q x]]".
      { unfold storage_protocol_exchange_nondeterministic in exchng.
        intro r. intro j0. have exq := exchng r state0.2 j0.
        destruct exq as [p2_q [b2 [t2 exq]]].
        destruct exq as [[p2 [eq oo]] [a b]].
        exists (p2 ⋅ q). exists t2. split.
        { exists p2. exists b2. exists t2. intuition. rewrite <- eq. apply a. }
        { rewrite <- eq. apply a. }
      }
    { trivial. }
    { iFrame. }
      
    destruct incll as [[p2 [b2 [t2 [p2_q_eq bigconj]]]] incll].
    rewrite p2_q_eq.
    iDestruct (own_inved_op_split with "own_p_q") as "[p q]".
    iDestruct ("z" with "q") as "[_ z]".

    destruct bigconj as [oo [pix [iix interp_eq]]].
       
    destruct wfm as [f_prop [f_unit f_op]]. (* need f Proper for the next step *)
    
    iDestruct "z" as "[g [_ fi]]".
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ q ⋅ z)) as pinv_p1_z. {
        setoid_rewrite <- incll. exists (state0.2).
        apply pinvs.
    }

    assert (✓ (t2 ⋅ b2)) as val_interp2.
    {
      destruct (base_ra_mixin _ _ storage_mixin).
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ state0_t : P * B,
          own γ (● Inved state0_t.1) ∗ ⌜sp_rel state0_t.1 state0_t.2⌝ ∗ f state0_t.2)%I)
          with "[x fi]"
          as "inv_to_return".
    {
      iModIntro.
      iExists (p2 ⋅ q ⋅ z, t2). iFrame "x". iFrame "fi".
      iPureIntro. trivial.
    }
    iDestruct ("g" with "inv_to_return") as "g".
    iMod ("back" with "g") as "g".
    iModIntro. iFrame. iPureIntro. trivial.
  Qed.
  
  Lemma sp_exchange_with_extra_guard_nondeterministic
    (p1 q: P) (b1: B) (output_ok: P → B → Prop) (γ: gname) (f: B → iProp Σ) (G: iProp Σ) E
    (exchng: storage_protocol_exchange_nondeterministic (p1 ⋅ q) b1
        (λ p2_q b2 , ∃ p2 , p2_q = p2 ⋅ q ∧ output_ok p2 b2))
    (gname_in_e: γ ∈ E)
    : sp_sto γ f ∗ (G &&{ E }&&> sp_own γ q) ⊢
        G ∗ sp_own γ p1 ∗ ▷ f b1 ={ E }=∗ ∃ p2 b2 ,
            ⌜ output_ok p2 b2 ⌝ ∗ G ∗ sp_own γ p2 ∗ ▷ f b2.
  Proof.
    iIntros "x y".
    iDestruct (sp_exchange_with_extra_guard_nondeterministic_with_later p1 q b1 output_ok γ f G E 0 exchng gname_in_e with "x y") as "J".
    iMod "J". iMod "J". iModIntro. iFrame.
  Qed.
  
  Lemma sp_exchange_with_extra_guard
    (p1 p2 q: P) (b1 b2: B) (γ: gname) (f: B → iProp Σ) (G: iProp Σ)
    (exchng: storage_protocol_exchange (p1 ⋅ q) (p2 ⋅ q) b1 b2)
    : sp_sto γ f ∗ (G &&{ {[ γ ]} }&&> sp_own γ q) ⊢
        G ∗ sp_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ G ∗ sp_own γ p2 ∗ ▷ f b2.
  Proof.
    iIntros "x y".
    iDestruct (sp_exchange_with_extra_guard_nondeterministic p1 q b1 (λ p b, p = p2 ∧ b = b2) γ f G {[ γ ]} with "x y") as "J".
    { unfold storage_protocol_exchange_nondeterministic.
      unfold storage_protocol_exchange in exchng.
      intros q0 t1 pi. exists (p2 ⋅ q). exists b2. have ex := exchng q0 t1 pi.
      destruct ex as [t2 ex]. exists t2.
      split. { exists p2. split; trivial. split; trivial. }
      apply ex.
    }
    { set_solver. }
    iMod "J" as (p0 b0) "[[%es %es2] L]". iModIntro. subst p0. subst b0. iFrame.
  Qed.
  
  Local Lemma inved_op (a b : P) :
      Inved (a ⋅ b) ≡ Inved a ⋅ Inved b.
  Proof using equ_p. trivial. Qed.

  (* SP-Sep *)

  Lemma sp_own_op a b γ :
      sp_own γ (a ⋅ b) ⊣⊢ sp_own γ a ∗ sp_own γ b.
  Proof.
    rewrite sp_own_eq. unfold sp_own_def.
    setoid_rewrite inved_op.
    rewrite auth_frag_op.
    apply own_op.
  Qed.
  
  (* TODO
  Lemma sp_own_and x y γ :
      sp_own γ x ∧ sp_own γ y ⊢ ∃ z , ⌜ x ≼ z ∧ y ≼ z ⌝ ∗ sp_own γ z.
  Proof.
    iIntros "H". unfold sp_own. iDestruct (and_own_discrete_ucmra with "H") as (z) "[J %t]".
    destruct t as [Hxz Hyz]. destruct z as [|p].
  Qed.
  *)
  
  Lemma op_unit (p: P) : p ⋅ ε ≡ p.
  Proof using storage_mixin.
    rewrite (ra_comm _ (protocol_ra_mixin _ _ storage_mixin)).
    apply (protocol_unit_left_id _ _ storage_mixin).
  Qed.
  
  Lemma op_unit_base (b: B) : b ⋅ ε ≡ b.
  Proof using storage_mixin.
    rewrite (ra_comm _ (base_ra_mixin _ _ storage_mixin)).
    apply (base_unit_left_id _ _ storage_mixin).
  Qed.
  
  Local Lemma auth_inved_conjure_unit γ (state: P)
      : own γ (● Inved state) ==∗ own γ (● Inved state) ∗ own γ (◯ Inved ε).
  Proof.
      apply auth_conjure_frag.
      setoid_rewrite <- inved_op.
      setoid_rewrite op_unit.
      trivial.
  Qed.
   
  Local Lemma valid_inved_of_pinv (p: P)
    : pinv p → ✓ (Inved p). 
  Proof using storage_mixin.
    intro pi. unfold "✓", inved_protocol_valid. exists ε. setoid_rewrite op_unit.
    trivial.
  Qed.

  (* SP-Unit *)
  
  Lemma sp_own_unit γ f
      : sp_sto γ f ⊢ sp_own γ ε.
  Proof.
    unfold sp_sto. rewrite sp_own_eq. unfold sp_own_def.
    iIntros "[%wfm [#ounit #m]]".
    iFrame "ounit".
  Qed.

  (* SP-Deposit *)
    
  Lemma sp_deposit
      (p1 p2: P) (b1: B) (γ: gname) (f: B → iProp Σ)
      (exchng: storage_protocol_deposit p1 p2 b1)
      : sp_sto γ f ⊢
          sp_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ sp_own γ p2.
  Proof.
    iIntros "#m pb".
    iMod (sp_exchange p1 p2 b1 (ε: B) γ f with "m pb") as "[pb u]".
    {
      unfold storage_protocol_exchange.
      unfold storage_protocol_deposit in exchng.
      intros q pi1. have t := exchng q pi1. intuition.
      setoid_rewrite op_unit_base.
      trivial.
    }
    iModIntro. iFrame "pb".
  Qed.
   
  Instance valid_proper_base : Proper ((≡) ==> impl) (@valid B _).
  Proof using storage_mixin.
    apply (ra_validN_proper _ (base_ra_mixin _ _ storage_mixin)).
  Qed.
  
  (* SP-Withdraw *)
   
  Lemma sp_withdraw
      (p1 p2: P) (b2: B) (γ: gname) (f: B → iProp Σ)
      (exchng: storage_protocol_withdraw p1 p2 b2)
      : sp_sto γ f ⊢
          sp_own γ p1 ={ {[ γ ]} }=∗ sp_own γ p2 ∗ ▷ f b2.
  Proof.
    iIntros "#m pb".
    iAssert (▷ f ε)%I as "u".
    {
      iModIntro. 
      unfold sp_sto.
      iDestruct "m" as "[%wf #m]".
      unfold wf_prop_map in wf.
      destruct wf as [wf_prop [wf_unit _]].
      setoid_rewrite wf_unit. done.
    }
    iMod (sp_exchange p1 p2 (ε: B) b2 γ f with "m [pb u]") as "[pb fb2]".
    {
      unfold storage_protocol_exchange.
      unfold storage_protocol_withdraw in exchng.
      intros q t1 pi1. have j := exchng q t1 pi1. destruct j as [t2 j].
      exists t2. intuition.
      - setoid_rewrite op_unit_base.
        destruct storage_mixin. apply (interp_val _ _ storage_mixin (p1 ⋅ q)). trivial.
      - setoid_rewrite op_unit_base. trivial.
    }
    { iFrame "pb". iFrame "u". }
    iModIntro. iFrame.
  Qed.

  (* SP-Update *)
   
  (* TODO It should be possible to do the update at mask ∅, but this requires changing
     the underlying auth resource slightly. *)
  Lemma sp_update
      (p1 p2: P) (γ: gname) (f: B → iProp Σ)
      (exchng: storage_protocol_update p1 p2)
      : sp_sto γ f ⊢
          sp_own γ p1 ={ {[ γ ]} }=∗ sp_own γ p2.
  Proof.
    iIntros "#m pb".
    iDestruct (sp_withdraw p1 p2 ε γ f with "m pb") as "pb".
    {
      unfold storage_protocol_withdraw.
      unfold storage_protocol_update in exchng.
      intros q t1 pi.
      have exch := exchng q t1.
      intuition.
      setoid_rewrite op_unit_base. exists t1. split; trivial.
    }
    iMod "pb".
    iModIntro.
    iDestruct "pb" as "[pb _]".
    iFrame.
  Qed.
 
  (* SP-Alloc *)
  
  Lemma sp_alloc_ns (p: P) (b: B) (f: B → iProp Σ) E (N: namespace)
      (pi: sp_rel p b) (wf: wf_prop_map f)
  : ⊢ f b ={E}=∗ ∃ γ , ⌜ γ ∈ (↑ N : coPset) ⌝ ∗ sp_sto γ f ∗ sp_own γ p.
  Proof.
    iIntros "f_init".
    rewrite sp_own_eq. unfold sp_own_def.
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iMod (ownI_alloc_and_simultaneous_own_alloc_ns
      (λ γ , 
        (∃ (state_t: P * B) ,
          own γ (● (Inved state_t.1))
          ∗ ⌜ sp_rel state_t.1 state_t.2 ⌝
          ∗ (f state_t.2))%I
      )
      (● (Inved p) ⋅ (◯ (Inved ε) ⋅ ◯ (Inved p)))
      (↑ N)
      with "w") as "w".
    { rewrite coPset_infinite_finite. apply nclose_infinite. }
    { 
      rewrite <- auth_frag_op.
      rewrite auth_both_valid_discrete. split; trivial.
      - replace (Inved ε ⋅ Inved p) with (Inved (ε ⋅ p)) by trivial.
        rewrite (protocol_unit_left_id _ _ storage_mixin).
        trivial.
      - apply valid_inved_of_pinv. exists b. apply pi.
    }
    
    iDestruct "w" as (γ) "[%in_ns [w [oinv [auth [u frag]]]]]".
    
    iDestruct ("w" with "[auth f_init]") as "w".
    {
      iModIntro. iExists (p, b). iFrame. iPureIntro. trivial.
    }
    
    iModIntro. iModIntro.
    iFrame "w". iFrame "oe".
    iExists γ.
    unfold sp_own. iFrame "frag".
    unfold sp_sto.
    iFrame "oinv". iFrame.
    iPureIntro. split; trivial.
  Qed.
  
  Lemma sp_alloc (p: P) (b: B) (f: B → iProp Σ) E
      (pi: sp_rel p b) (wf: wf_prop_map f)
  : ⊢ f b ={E}=∗ ∃ γ , sp_sto γ f ∗ sp_own γ p.
  Proof.
    iIntros "f_init".
    iMod (sp_alloc_ns p b f E nroot with "f_init") as (γ) "[_ t]"; trivial.
    iModIntro. iExists γ. iFrame.
  Qed.
  
  Lemma fupd_singleton_mask_frame (γ: gname) (X Y Z : iProp Σ) E
    (premise: X ⊢ Y ={ {[ γ ]} }=∗ Z) (is_in: γ ∈ E) : X ⊢ Y ={ E }=∗ Z.
  Proof.
    iIntros "x y".
    iDestruct (premise with "x y") as "p".
    iDestruct (fupd_mask_frame_r _ _ (E ∖ {[γ]}) with "p") as "p".
    { set_solver. }
    assert ({[γ]} ∪ E ∖ {[γ]} = E) as sete. {
        replace ({[γ]} ∪ E ∖ {[γ]}) with ((E ∖ {[γ]}) ∪ {[γ]}) by set_solver.
        apply guarding.guard.elem_diff_union_singleton. trivial.
    }
    rewrite sete. 
    trivial.
  Qed.
    
  Lemma sp_exchange'
    (p1 p2: P) (b1 b2: B) (γ: gname) (f: B → iProp Σ) E
    (exchng: storage_protocol_exchange p1 p2 b1 b2)
    (gname_in_e: γ ∈ E)
    : sp_sto γ f ⊢
        sp_own γ p1 ∗ ▷ f b1 ={ E }=∗ sp_own γ p2 ∗ ▷ f b2.
  Proof.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply sp_exchange; trivial.
  Qed.
   
  Lemma sp_deposit'
      (p1 p2: P) (b1: B) (γ: gname) (f: B → iProp Σ) E
      (exchng: storage_protocol_deposit p1 p2 b1)
      (gname_in_e: γ ∈ E)
      : sp_sto γ f ⊢
          sp_own γ p1 ∗ ▷ f b1 ={ E }=∗ sp_own γ p2.
  Proof.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply sp_deposit; trivial.
  Qed.

  Lemma sp_withdraw'
      (p1 p2: P) (b2: B) (γ: gname) (f: B → iProp Σ) E
      (exchng: storage_protocol_withdraw p1 p2 b2)
      (gname_in_e: γ ∈ E)
      : sp_sto γ f ⊢
          sp_own γ p1 ={ E }=∗ sp_own γ p2 ∗ ▷ f b2.
  Proof.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply sp_withdraw; trivial.
  Qed.

  Lemma sp_update'
      (p1 p2: P) (γ: gname) (f: B → iProp Σ) E
      (exchng: storage_protocol_update p1 p2)
      (gname_in_e: γ ∈ E)
      : sp_sto γ f ⊢
          sp_own γ p1 ={ E }=∗ sp_own γ p2.
  Proof.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply sp_update; trivial.
  Qed.
  
  (* SP-PointProp *)
  
  Lemma point_prop_p_own (γ: gname) (p: P) : point_prop (sp_own γ p).
  Proof.
    rewrite sp_own_eq. unfold sp_own_def. apply point_prop_own.
  Qed.
  
  (* SP-Valid *)
  
  Lemma sp_own_valid (γ: gname) (p: P)
      : (sp_own γ p) ⊢ ⌜ ∃ q b , sp_rel (p ⋅ q) b ⌝.
  Proof.
    rewrite sp_own_eq. unfold sp_own_def.
    iIntros "x".  iDestruct (own_valid with "x") as "%x". iPureIntro.
    generalize x. clear x.
    rewrite auth_frag_valid.
    trivial.
  Qed.
   
  Global Instance proper_sp_own γ : Proper ((≡) ==> (⊣⊢)) (sp_own γ).
  Proof. rewrite sp_own_eq. unfold sp_own_def. intros x y Heq.
      setoid_rewrite Heq. trivial. Qed.
  
  Global Instance timeless_sp_own γ a : Timeless (sp_own γ a).
  Proof. rewrite sp_own_eq. apply _. Qed.
  
  Lemma sp_own_mono γ a1 a2 : a2 ≼ a1 → sp_own γ a1 ⊢ sp_own γ a2.
  Proof.
    intros [t Heq]. setoid_rewrite Heq. setoid_rewrite sp_own_op.
    iIntros "[Ha Hb]". iFrame.
  Qed.
  
  Global Instance mono_sp_own' γ : Proper (flip (≼) ==> (⊢)) (sp_own γ).
  Proof.
    intros a1 a2. apply sp_own_mono.
  Qed.
  
  Lemma sp_own_core_persistent γ a : (pcore a ≡ Some a) → Persistent (sp_own γ a).
  Proof.
    rewrite sp_own_eq. unfold sp_own_def.
    intros Ha. apply own_core_persistent. apply auth_frag_core_id.
    unfold CoreId, pcore, cmra_pcore, cmra_pcore. simpl. unfold inved_protocolUR, ucmra_pcore.
    unfold inved_protocol_pcore.  destruct (pcore a) as [t|].
    - inversion Ha as [x y Hb Hc Hd|]. setoid_rewrite Hb. trivial.
    - inversion Ha.
  Qed.
End StorageLogic.
