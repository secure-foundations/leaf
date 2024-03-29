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

(*From iris.base_logic.lib Require Export wsat.*)

Require Import guarding.inved.
Require Import guarding.guard.
Require Import guarding.auth_frag_util.
Require Import guarding.point_props.
Require Import guarding.conjunct_own_rule.
Require Import guarding.wsat_util.

(*
Context {Σ: gFunctors}.
Context `{!invGS Σ}.
*)

Class Interp (P : Type) (B : Type) := interp : P → B.


Record StorageMixin P B
    `{Equiv P, PCore P, Op P, Valid P, PInv P, Unit P}
    {equ: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, Interp P B}
:= {
    protocol_mixin: ProtocolMixin P;
    base_ra_mixin: RAMixin B; (* completely ignore core *)
    
    base_unit_left_id : LeftId equiv (ε : B) op;

    interp_proper: Proper ((≡) ==> (≡)) interp;
    interp_val: ∀ p: P , pinv p -> ✓ interp p;
}. 


Section PropMap.
  Context {Σ: gFunctors}.
  
  Context `{Equiv B, Op B, Valid B, Unit B}.
  
  Definition wf_prop_map (f: B -> iProp Σ) :=
      Proper ((≡) ==> (≡)) f
      /\ f ε ≡ (True)%I
      /\ (∀ a b , ✓(a ⋅ b) -> f (a ⋅ b) ≡ (f a ∗ f b) % I).
      
  
End PropMap.

Section StorageLogic.
  Context `{Equiv B, PCore B, Op B, Valid B, Unit B}.
  Context `{Equiv P, PCore P, Op P, PInv P, Valid P, Unit P, Interp P B}.
  
  
  Definition storage_protocol_guards (p: P) (b: B) :=
      ∀ q , pinv (p ⋅ q) -> b ≼ interp (p ⋅ q).
      
  Definition storage_protocol_exchange (p1 p2: P) (b1 b2: B)  :=
      ∀ q , pinv (p1 ⋅ q) -> pinv (p2 ⋅ q)
          /\ ✓(interp (p1 ⋅ q) ⋅ b1)
          /\ interp (p1 ⋅ q) ⋅ b1 ≡ interp (p2 ⋅ q) ⋅ b2.
          
  Definition storage_protocol_update (p1 p2: P) :=
      ∀ q , pinv (p1 ⋅ q) -> pinv (p2 ⋅ q)
          /\ interp (p1 ⋅ q) ≡ interp (p2 ⋅ q).
          
  Definition storage_protocol_withdraw (p1 p2: P) (b2: B)  :=
      ∀ q , pinv (p1 ⋅ q) -> pinv (p2 ⋅ q)
          /\ interp (p1 ⋅ q) ≡ interp (p2 ⋅ q) ⋅ b2.
          
  Definition storage_protocol_deposit (p1 p2: P) (b1: B)  :=
      ∀ q , pinv (p1 ⋅ q) -> pinv (p2 ⋅ q)
          /\ ✓(interp (p1 ⋅ q) ⋅ b1)
          /\ interp (p1 ⋅ q) ⋅ b1 ≡ interp (p2 ⋅ q).
          
  Definition storage_protocol_exchange_nondeterministic (p1: P) (b1: B) (output_ok: P -> B -> Prop)  :=
      ∀ q , pinv (p1 ⋅ q) -> ∃ p2 b2 , output_ok p2 b2
          /\ pinv (p2 ⋅ q)
          /\ ✓(interp (p1 ⋅ q) ⋅ b1)
          /\ interp (p1 ⋅ q) ⋅ b1 ≡ interp (p2 ⋅ q) ⋅ b2.

          
  Context {equ: Equivalence (≡@{P})}.
  Context {equb: Equivalence (≡@{B})}.
  Context {storage_mixin: StorageMixin P B}.

  Instance sm_interp_proper
      : Proper ((≡) ==> (≡)) (interp).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ storage_mixin.
    destruct storage_mixin. trivial.
  Qed.

  Instance inved_proper
      : Proper ((≡) ==> (≡)) (@Inved P).
  Proof.
    unfold Proper, "==>". intros.
    unfold "≡", inved_protocol_equiv. trivial.
  Qed.
                   
  Global Instance my_discrete : CmraDiscrete (inved_protocolR (protocol_mixin P B storage_mixin)).
  Proof. apply discrete_cmra_discrete. Qed.

  Context {Σ: gFunctors}.
  Context `{!inG Σ (authUR (inved_protocolUR (protocol_mixin P B storage_mixin)))}.
  Context `{!invGS Σ}.
  
  Definition maps (γ: gname) (f: B -> iProp Σ) : iProp Σ :=
      ⌜ wf_prop_map f ⌝ ∗
      own γ (◯ (Inved ε)) ∗
      ownI γ (
        ∃ (state: P) ,
          own γ (● (Inved state))
          ∗ ⌜ pinv state ⌝
          ∗ (f (interp state))
      ). 
     
  Definition p_own (γ: gname) (p: P) : iProp Σ := own γ (◯ (Inved p)).
  
  Lemma pcore_inved_unit
    : (pcore (Inved (ε : P)) ≡ Some (Inved ε)).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    unfold pcore, inved_protocol_pcore. destruct (pcore ε) eqn:x.
    { destruct storage_mixin. destruct protocol_mixin0. destruct protocol_ra_mixin.
      have k := ra_pcore_l (ε: P) p x.
      generalize k. rewrite ra_comm. rewrite protocol_unit_left_id.
      intro R. setoid_rewrite R. trivial.
    }
    trivial.
  Qed.
  
  Global Instance pers_own_frag_inved_unit γ : Persistent (own γ (◯ (Inved (ε: P)))).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    apply own_core_persistent.
    apply auth_frag_core_id.
    unfold CoreId.
    apply pcore_inved_unit.
  Qed.
  
  Global Instance pers_maps γ f : Persistent (maps γ f).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
  apply _. Qed.
  
  Lemma ownIagree (γ : gname) (X Y : iProp Σ) : ownI γ X ∗ ownI γ Y ⊢ (▷ X ≡ ▷ Y).
  Proof.
    unfold ownI.
    rewrite <- own_op.
    iIntros "x".
    iDestruct (own_valid with "x") as "v".
    rewrite gmap_view_frag_op_validI.
    iDestruct "v" as "[#v iu]".
    unfold invariant_unfold.
    
    iDestruct (later_equivI_1 with "iu") as "iu".
    iDestruct (f_equivI_contractive (λ x , (▷ x)%I) with "iu") as "iu".
    iFrame.
  Qed.
  
  Lemma and_except0_r (X Y : iProp Σ)
      : X ∧ ◇ Y ⊢ ◇ (X ∧ Y).
  Proof.
    iIntros "l". rewrite bi.except_0_and. iSplit.
    { iDestruct "l" as "[l _]". iModIntro. iFrame. }
    { iDestruct "l" as "[_ l]". iFrame. }
  Qed.
  
  
  Lemma apply_timeless (X Y Z W V : iProp Σ) (ti: Timeless Z) (ti2: Timeless W)
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
  
  Lemma stuff1 (X Y Z W V : iProp Σ)
      : (X ∧ (Y ∗ Z ∗ W ∗ V)) ⊢ W.
  Proof.
    iIntros "x". iDestruct "x" as "[_ [_ [_ [w _]]]]". iFrame.
  Qed.
  
  Lemma incl_of_inved_incl_assumes_unital (p1 p2 : P)
    (incll :
      @included (InvedProtocol P) (inved_protocol_equiv P) (inved_protocol_op P)
      (Inved p1) (Inved p2)) : p1 ≼ p2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    unfold "≼" in incll. destruct incll as [z incll].
    destruct z.
    - unfold "⋅", inved_protocol_op, "≡", inved_protocol_equiv in incll.
      unfold "≼". exists ε.
      setoid_rewrite (@comm P).
      + destruct storage_mixin. destruct protocol_mixin0.
          setoid_rewrite incll.
          unfold LeftId in protocol_unit_left_id.
          symmetry.
          apply protocol_unit_left_id.
      + destruct storage_mixin. destruct protocol_mixin0. destruct protocol_ra_mixin.
          apply ra_comm.
   - unfold "≡", inved_protocol_equiv, "⋅", inved_protocol_op in incll.
      unfold "≼". exists p. trivial.
  Qed.
  
  Lemma stuff2 (γ: gname) (p state: P) (T W: iProp Σ)
      : own γ (◯ Inved p) ∧ (T ∗ own γ (● Inved state) ∗ W) ⊢ ⌜ p ≼ state ⌝. 
  Proof.
    iIntros "x".
    iAssert (((own γ (● Inved state)) ∧ (own γ (◯ Inved p)))%I) with "[x]" as "t".
    { iSplit. 
        { iDestruct "x" as "[_ [_ [x _]]]". iFrame. }
        { iDestruct "x" as "[x _]". iFrame. }
    }
    iDestruct (auth_frag_conjunct with "t") as "%incll".
    iPureIntro.
    apply incl_of_inved_incl_assumes_unital. trivial.
  Qed.
  
  (*Lemma stuff3 (γ: gname) (p0 p state: P) (T W: iProp Σ)
      : own γ (◯ Inved p0) ∗ (own γ (◯ Inved p) ∧ (T ∗ own γ (● Inved state) ∗ W)) ⊢ ⌜ p0 ⋅ p ≼ state ⌝.  *)
  
  Lemma logic_fguard (p: P) (b: B) (γ: gname) (f: B -> iProp Σ)
    (g: storage_protocol_guards p b)
    : maps γ f ⊢ (p_own γ p &&{ {[ γ ]} }&&$> ▷ f b).
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold fguards, guards_with, maps.
    iIntros "[%wf [ounit #inv]]".
    iSplit. {
      iIntros (T) "[po b]".
      rewrite storage_bulk_inv_singleton. unfold storage_inv.
      unfold p_own.
      iAssert ((own γ (◯ Inved p) ∧
          (◇ ∃ state : P, T ∗ ▷
                (own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp state))))%I)
          with "[po b]" as "x".
      { iSplit. { iFrame. } 
        iDestruct ("b" with "po") as "[ex t]".
        iDestruct "ex" as (P0) "[#own lat]".
        iDestruct (ownIagree γ P0 _ with "[inv own]") as "eq".
        { iSplitL. { iFrame "own". } iFrame "inv". }
        iRewrite "eq" in "lat".
        iMod (bi.later_exist_except_0 with "lat") as (state) "lat".
        iExists state. iFrame.
      }
      iMod (and_except0_r with "x") as "x".
      rewrite bi.and_exist_l.
      iDestruct "x" as (state) "x".
      iMod (apply_timeless with "x") as "x".
      iDestruct (stuff1 with "x") as "%pinvs".
      iDestruct (stuff2 with "x") as "%incll".
      iDestruct "x" as "[_ [t [o [p latf]]]]".

      unfold storage_protocol_guards in g.
      unfold "≼" in incll. destruct incll as [z incll].
      assert (pinv (p ⋅ z)) as pinv_pz.
          { destruct storage_mixin. destruct protocol_mixin0. setoid_rewrite <- incll. trivial. }
      have gz := g z pinv_pz.
      unfold "≼" in gz. destruct gz as [y gz].
      assert (interp state ≡ b ⋅ y) as ieqop.
      { destruct storage_mixin. unfold interp. 
          setoid_rewrite incll. trivial. }

      unfold wf_prop_map in wf.
      destruct wf as [fprop [funit fop]].

      assert (✓ (b ⋅ y)) as is_val.
      { destruct storage_mixin. destruct base_ra_mixin0.
          setoid_rewrite <- ieqop. apply interp_val0. trivial. }

      setoid_rewrite ieqop.
      setoid_rewrite fop; trivial.

      rewrite bi.later_sep. 
      iDestruct "latf" as "[fb fy]".
      iModIntro.
      iFrame "fb".
      iIntros "fb".
      iFrame "t".
      iExists ((∃ state0 : P,
                own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp state0))%I).
      iFrame "inv".
      iNext. iExists state. iFrame.
      setoid_rewrite ieqop. setoid_rewrite fop; trivial. iFrame.
    } 
    rewrite know_bulk_inv_singleton. unfold know_inv.
    iExists _. iFrame "inv".
  Qed.

  (* SP-Guard *)
  
  Lemma logic_guard (p: P) (b: B) (γ: gname) (E: coPset) (f: B -> iProp Σ)
    (g: storage_protocol_guards p b)
    (is_in: γ ∈ E)
    : maps γ f ⊢ (p_own γ p &&{ E }&&> ▷ f b).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold guards.
    iIntros "#m". iModIntro.
    iExists {[ γ ]}.
    iSplit.
    { iPureIntro. set_solver. }
    iApply logic_fguard; trivial.
  Qed.
   
  Lemma own_sep_inv_incll_helper_nondet (p1 st : P) (output_ok : P -> P -> Prop)
    (cond : ∀ q : P, pinv (p1 ⋅ q) → ∃ p2 , output_ok p2 q /\ pinv (p2 ⋅ q))
   : ∀ (z: InvedProtocol P) , pinv st -> ✓ (Inved st) -> Inved p1 ⋅ z ≡ Inved st →
    ∃ p2 , output_ok p2 (match z with Inved z0 => z0 | Nah => ε end) /\ ✓ (Inved p2 ⋅ z).
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
  intros z inv v eq.
    destruct z.
    - unfold "⋅", inved_protocol_op.
      unfold "⋅", inved_protocol_op in eq.
      unfold "≡", inved_protocol_equiv in eq.
      unfold "✓", inved_protocol_valid. 
      
      setoid_rewrite <- eq in v.
      {
        unfold "✓", inved_protocol_valid in v. 
        destruct v as [v pi].
        assert (p1 ⋅ (@ε _ H9) ≡ p1) as eq2.
        { destruct storage_mixin. destruct protocol_mixin0.
            destruct protocol_ra_mixin.
            rewrite ra_comm.
            apply protocol_unit_left_id.
        }
        assert (pinv (p1 ⋅ (@ε _ H9))) as pi2.
        {
          destruct storage_mixin.
          destruct protocol_mixin0.
          unfold Proper, "==>", impl in inv_proper.
          apply inv_proper with (x := p1); trivial.
          apply inv_proper with (x := st); trivial.
        }
        have c := cond (@ε _ H9) pi2.
        destruct c as [p2 [oo c]].
        exists p2.
        split. { apply oo. }
        exists ε.
        trivial.
      }
      { destruct storage_mixin. trivial. }
    - unfold "⋅", inved_protocol_op in eq.
      unfold "≡", inved_protocol_equiv in eq.
      unfold "⋅", inved_protocol_op.
      
      setoid_rewrite <- eq in v.
      {
        unfold "✓", inved_protocol_valid in v.
        unfold "✓", inved_protocol_valid.
        destruct v as [v pi].
        
        assert (pinv (p1 ⋅ p)) as pinv1. {
          destruct storage_mixin.
          destruct protocol_mixin0.
          unfold Proper, "==>", impl in inv_proper.
          apply inv_proper with (x := p1 ⋅ p); trivial.
          apply inv_proper with (x := st); trivial.
        }
        have c := cond p pinv1.
        destruct c as [p2 [oo c]].
        exists p2.
        split; trivial.
        exists ε.
        
        destruct storage_mixin.
        destruct protocol_mixin0.
        unfold Proper, "==>", impl in inv_proper.
        assert (p2 ⋅ p ⋅ (@ε _ H9) ≡ p2 ⋅ p) as eq2.
        { destruct storage_mixin. destruct protocol_mixin0.
            destruct protocol_ra_mixin.
            rewrite ra_comm.
            apply protocol_unit_left_id.
        }
        apply inv_proper with (x := p2 ⋅ p); trivial.
      }
      { destruct storage_mixin. trivial. }
  Qed.
  
  Lemma own_sep_inv_incll_helper (p1 p2 st : P)
    (cond : ∀ q : P, pinv (p1 ⋅ q) → pinv (p2 ⋅ q))
   : ∀ (z: InvedProtocol P) , ✓ (Inved st) -> Inved p1 ⋅ z ≡ Inved st → ✓ (Inved p2 ⋅ z).
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    intros z v eq.
    destruct z.
    - unfold "⋅", inved_protocol_op.
      unfold "⋅", inved_protocol_op in eq.
      unfold "≡", inved_protocol_equiv in eq.
      unfold "✓", inved_protocol_valid. 
      
      setoid_rewrite <- eq in v.
      {
        unfold "✓", inved_protocol_valid in v. 
        destruct v as [v pi].
        have c := cond v pi.
        exists v.
        trivial.
      }
      { destruct storage_mixin. trivial. }
    - unfold "⋅", inved_protocol_op in eq.
      unfold "≡", inved_protocol_equiv in eq.
      unfold "⋅", inved_protocol_op.
      
      setoid_rewrite <- eq in v.
      {
        unfold "✓", inved_protocol_valid in v.
        unfold "✓", inved_protocol_valid.
        destruct v as [v pi].
        
        assert (pinv (p1 ⋅ (p ⋅ v))) as pinv1. {
          destruct storage_mixin.
          destruct protocol_mixin0.
          unfold Proper, "==>", impl in inv_proper.
          apply inv_proper with (x := p1 ⋅ p ⋅ v); trivial.
          destruct protocol_ra_mixin.
          symmetry.
          apply ra_assoc.
        }
        have c := cond (p ⋅ v) pinv1.
        exists v.
        
        destruct storage_mixin.
        destruct protocol_mixin0.
        unfold Proper, "==>", impl in inv_proper.
        apply inv_proper with (x := p2 ⋅ (p ⋅ v)); trivial.
        destruct protocol_ra_mixin.
        apply ra_assoc.
      }
      { destruct storage_mixin. trivial. }
  Qed.
        
  Lemma op_nah (p1 state : P)
    : Inved p1 ⋅ Nah ≡ Inved state -> p1 ≡ state.
  Proof. intros. trivial. Qed.
  
  Lemma op_inved_inved (p1 p2 p : P)
    : Inved p1 ⋅ Inved p2 ≡ Inved p -> p1 ⋅ p2 ≡ p.
  Proof. intros. trivial. Qed.
        
  Lemma own_sep_inv_incll γ (p1 p2 state : P)
      (cond: ∀ q , pinv (p1 ⋅ q) -> pinv (p2 ⋅ q))
    : own γ (◯ Inved p1) ∗ own γ (● Inved state) ==∗
      ∃ (z: P) , ⌜ state ≡ p1 ⋅ z ⌝ ∗ own γ (◯ Inved p2) ∗ own γ (● Inved (p2 ⋅ z)).
  Proof.
    iIntros "[x y]".
    iDestruct (own_valid with "y") as "%val".
    iMod (own_sep_auth_incll γ (Inved p1) (Inved p2) (Inved state) with "[x y]") as "x".
    {
      intro.
      apply own_sep_inv_incll_helper; trivial.
      generalize val. rewrite auth_auth_valid. trivial.
    }
    { iFrame. }
    iDestruct "x" as (z) "[%eq [frag auth]]".
    destruct z.
    {
      have eq0 := op_nah _ _ eq.
      assert (Inved p2 ⋅ Nah ≡ Inved p2) as eq1 by trivial.
      setoid_rewrite eq1.
      iExists (ε:P).
      assert (p2 ⋅ ε ≡ p2) as eq2.
      { destruct storage_mixin. destruct protocol_mixin0.
          destruct protocol_ra_mixin.
          rewrite ra_comm.
          apply protocol_unit_left_id.
      }
      setoid_rewrite eq2.
      iFrame.
      iPureIntro.
      assert (p1 ⋅ ε ≡ p1) as eq3.
      { destruct storage_mixin. destruct protocol_mixin0.
          destruct protocol_ra_mixin.
          rewrite ra_comm.
          apply protocol_unit_left_id.
      }
      setoid_rewrite eq3. symmetry. trivial.
    }
    {
      iExists p.
      
      assert (Inved p2 ⋅ Inved p ≡ Inved (p2 ⋅ p)) as eq0 by trivial.
      setoid_rewrite eq0.
      iFrame.
      iPureIntro. symmetry. apply op_inved_inved. trivial.
    }
   Qed.
   
   Lemma own_sep_inv_incll_nondet γ (p1 state : P) (output_ok: P -> P -> Prop)
      (cond: ∀ q , pinv (p1 ⋅ q) -> ∃ p2 , output_ok p2 q /\ pinv (p2 ⋅ q))
      (pi: pinv state)
    : own γ (◯ Inved p1) ∗ own γ (● Inved state) ==∗
      ∃ (z p2: P) , ⌜ output_ok p2 z /\ state ≡ p1 ⋅ z ⌝
          ∗ own γ (◯ Inved p2) ∗ own γ (● Inved (p2 ⋅ z)).
   Proof.
   iIntros "[x y]".
   iDestruct (own_valid with "y") as "%val".
    iMod (own_sep_auth_incll_nondet γ (Inved p1) (Inved state)
    (λ p q , match p with
      | Inved a => output_ok a (match q with Inved b => b | Nah => ε end)
      | Nah => False
    end)
     with "[x y]") as "x".
    {
      intro. intro equi.
      assert (✓ Inved state) as val2. { generalize val. rewrite auth_auth_valid. trivial. }
      have rr := own_sep_inv_incll_helper_nondet p1 state output_ok cond z pi val2 equi.
      destruct rr as [p2 [rr v]]. exists (Inved p2). split; trivial.
    }
    { iFrame. }
    iDestruct "x" as (z p2) "[%eq [frag auth]]".
    destruct eq as [big_oo eq].
    destruct p2. { intuition. }
    rename p into p2.
    destruct z.
    {
      have eq0 := op_nah _ _ eq.
      assert (Inved p2 ⋅ Nah ≡ Inved p2) as eq1 by trivial.
      setoid_rewrite eq1.
      iExists (ε:P).
      assert (p2 ⋅ ε ≡ p2) as eq2.
      { destruct storage_mixin. destruct protocol_mixin0.
          destruct protocol_ra_mixin.
          rewrite ra_comm.
          apply protocol_unit_left_id.
      }
      iModIntro. iExists p2.
      setoid_rewrite eq2.
      iFrame.
      iPureIntro.
      split. { trivial. }
      assert (p1 ⋅ ε ≡ p1) as eq3.
      { destruct storage_mixin. destruct protocol_mixin0.
          destruct protocol_ra_mixin.
          rewrite ra_comm.
          apply protocol_unit_left_id.
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
          (@inved_protocolUR P H4 H5 H6 H7 H8 H9 equ
             (@protocol_mixin P B H4 H5 H6 H8 H7 H9 equ H H0 H1 H2 H3 H10 storage_mixin))
          (@Inved P (@op P H6 a b))); trivial.
  Qed.
          
  Lemma own_inved_op (a b: P) γ :
      own γ (◯ Inved a) ∗ own γ (◯ Inved b) ⊢ own γ (◯ Inved (a ⋅ b)).
  Proof. rewrite own_inved_op_both. trivial. Qed.
      
  Lemma own_inved_op_split (a b: P) γ :
      own γ (◯ Inved (a ⋅ b)) ⊢ own γ (◯ Inved a) ∗ own γ (◯ Inved b).
  Proof. rewrite own_inved_op_both. trivial. Qed.
    
  (* SP-Exchange *)
  
  Lemma logic_exchange
    (p1 p2: P) (b1 b2: B) (γ: gname) (f: B -> iProp Σ)
    (exchng: storage_protocol_exchange p1 p2 b1 b2)
    : maps γ f ⊢
        p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps.
    iIntros "[%wfm [#ounit #m]] [p f]".
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iDestruct (ownI_open with "[w m oe]") as "[w [latp od]]".
    { iFrame "w". iFrame "m". iFrame "oe". }
    iMod (bi.later_exist_except_0 with "latp") as (state) "lat".
    iDestruct "lat" as "[ois [ps fi]]".
    iMod "ois" as "ois".
    iMod "ps" as "%ps".
    unfold p_own.
    iMod (own_sep_inv_incll γ p1 p2 state with "[p ois]") as (z) "[%incll [p ois]]".
    { unfold storage_protocol_exchange in exchng. intros q pi.
        have exch := exchng q pi. intuition. }
    { iFrame. }
    
    destruct wfm as [f_prop [f_unit f_op]]. (* need f Proper for the next step *)
    
    assert (f (interp state)
          ≡ f(interp (p1 ⋅ z))) as equiv_interp_state.
    {
        setoid_rewrite incll. trivial.
    }
    
    setoid_rewrite equiv_interp_state.
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ z)) as pinv_p1_z. {
        destruct storage_mixin. destruct protocol_mixin0.
        setoid_rewrite <- incll. trivial.
    }

    have exch := exchng z pinv_p1_z.
    destruct exch as [pinv_p2_z [val_interp1 interp_eq]].
    assert (✓ (interp (p2 ⋅ z) ⋅ b2)) as val_interp2.
    {
      destruct storage_mixin. destruct base_ra_mixin0.
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ state0 : P,
          own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp state0))%I)
          with "[ois fi]"
          as "inv_to_return".
    {
      iModIntro. (* strip later *)
      iExists (p2 ⋅ z). iFrame "ois". iFrame "fi".
      iPureIntro. trivial.
    }
    iDestruct (ownI_close γ _ with "[w m inv_to_return od]") as "[w en]".
    { iFrame "m". iFrame "inv_to_return". iFrame "w". iFrame "od". }
    iModIntro. iModIntro. iFrame.
  Qed.
   
  Lemma logic_exchange_nondeterministic
    (p1: P) (b1: B) (output_ok: P -> B -> Prop) (γ: gname) (f: B -> iProp Σ)
    (exchng: storage_protocol_exchange_nondeterministic p1 b1 output_ok)
    : maps γ f ⊢
        p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗
          ∃ p2 b2 , ⌜ output_ok p2 b2 ⌝ ∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps.
    iIntros "[%wfm [#ounit #m]] [p f]".
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iDestruct (ownI_open with "[w m oe]") as "[w [latp od]]".
    { iFrame "w". iFrame "m". iFrame "oe". }
    iMod (bi.later_exist_except_0 with "latp") as (state) "lat".
    iDestruct "lat" as "[ois [ps fi]]".
    iMod "ois" as "ois".
    iMod "ps" as "%ps".
    unfold p_own.
    iMod (own_sep_inv_incll_nondet γ p1 state (λ p2 q , ∃ b2 , output_ok p2 b2
          /\ pinv (p2 ⋅ q)
          /\ ✓(interp (p1 ⋅ q) ⋅ b1)
          /\ interp (p1 ⋅ q) ⋅ b1 ≡ interp (p2 ⋅ q) ⋅ b2) with "[p ois]")
        as (z p2) "[[%big_output_ok %incll] [p ois]]".
    { unfold storage_protocol_exchange in exchng. intros q pi.
        have exch := exchng q pi. destruct exch as [p2 [b2 exch]]. exists p2. intuition. exists b2. intuition. }
    { trivial. }
    { iFrame. }
    destruct big_output_ok as [b2 [oo [pix [vix interp_eq]]]].
    
    destruct wfm as [f_prop [f_unit f_op]]. (* need f Proper for the next step *)
    
    assert (f (interp state)
          ≡ f(interp (p1 ⋅ z))) as equiv_interp_state.
    {
        setoid_rewrite incll. trivial.
    }
    
    setoid_rewrite equiv_interp_state.
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ z)) as pinv_p1_z. {
        destruct storage_mixin. destruct protocol_mixin0.
        setoid_rewrite <- incll. trivial.
    }

    assert (✓ (interp (p2 ⋅ z) ⋅ b2)) as val_interp2.
    {
      destruct storage_mixin. destruct base_ra_mixin0.
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ state0 : P,
          own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp state0))%I)
          with "[ois fi]"
          as "inv_to_return".
    {
      iModIntro. (* strip later *)
      iExists (p2 ⋅ z). iFrame "ois". iFrame "fi".
      iPureIntro. trivial.
    }
    iDestruct (ownI_close γ _ with "[w m inv_to_return od]") as "[w en]".
    { iFrame "m". iFrame "inv_to_return". iFrame "w". iFrame "od". }
    iModIntro. iModIntro. iFrame.
    iExists p2. iExists b2. iFrame. iPureIntro. apply oo.
  Qed.
   
  Lemma logic_exchange_with_extra_guard
    (p1 p2 q: P) (b1 b2: B) (γ: gname) (f: B -> iProp Σ) (G: iProp Σ)
    (exchng: storage_protocol_exchange (p1 ⋅ q) (p2 ⋅ q) b1 b2)
    : maps γ f ∗ □ (G &&{ {[ γ ]} }&&$> p_own γ q) ⊢
        G ∗ p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ G ∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps.
    iIntros "[[%wfm [#ounit #m]] [#gu #kbi]] [g [p f]]".
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iDestruct (ownI_open with "[w m oe]") as "[w [latp od]]".
    { iFrame "w". iFrame "m". iFrame "oe". }
    iMod (bi.later_exist_except_0 with "latp") as (state) "lat".
    unfold fguards, guards_with.
    iDestruct ("gu" $! G) as "gu2".
    
    iDestruct ("gu2" with "[g lat]") as "gu3".
    { iFrame "g". iIntros "g". iFrame "g".
        setoid_rewrite storage_bulk_inv_singleton. unfold storage_inv.
        iExists ((∃ state0 : P, own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp state0))%I).
        iFrame "m".
        setoid_rewrite know_bulk_inv_singleton. unfold know_inv.
        iModIntro. iExists state. iFrame "lat".
    }
    
    iMod "gu3" as "[po b]".
    
     iAssert ((own γ (◯ Inved q) ∧
          (◇ ∃ state : P, G ∗ ▷
                (own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp state))))%I)
          with "[po b]" as "x".
      { iSplit. { iFrame. } 
        iDestruct ("b" with "po") as "[ex t]".
        setoid_rewrite storage_bulk_inv_singleton. unfold storage_inv.
        iDestruct "ex" as (P0) "[#own lat]".
        iDestruct (ownIagree γ P0 _ with "[m own]") as "eq".
        { iSplitL. { iFrame "own". } iFrame "m". }
        iRewrite "eq" in "lat".
        iMod (bi.later_exist_except_0 with "lat") as (state0) "lat".
        iExists state0. iFrame.
      }
      iMod (and_except0_r with "x") as "x".
      rewrite bi.and_exist_l.
      iDestruct "x" as (state0) "x".
      iMod (apply_timeless with "x") as "x".
      iDestruct (stuff1 with "x") as "%pinvs".
      unfold p_own.
      (*iDestruct (stuff3 γ p1 q state0 with "[p x]") as "%incll". { iFrame. }*)
      
      iAssert (own γ (◯ Inved q) ∧ own γ (● Inved state0) ∗ (G ∗ ⌜pinv state0⌝ ∗ ▷ f (interp state0)))%I with "[x]" as "x".
      { iSplit. { iDestruct "x" as "[x _]". iFrame. }
          iDestruct "x" as "[_ [x [y z]]]". iFrame. }
      iDestruct (andsep_to_sepand_ucmra with "x") as "[x y]".
      { apply auth_frag_disjointness. }
      iDestruct (own_separates_out γ (◯ Inved q) (own γ (◯ Inved q) ∧ G ∗ ⌜pinv state0⌝ ∗ ▷ f (interp state0)) with "[y]") as "[y z]".
      { iFrame "y". iIntros "[k _]". iFrame. }
      
      iDestruct (own_inved_op p1 q γ with "[p y]") as "own_p_q". { iFrame. }
      iMod (own_sep_inv_incll γ (p1 ⋅ q) (p2 ⋅ q) state0 with "[own_p_q x]")
          as (z) "[%incll [own_p_q x]]".
      { unfold storage_protocol_exchange in exchng.
        intro q0. have exq := exchng q0. intuition. }
      { iFrame. }
      
      iDestruct (own_inved_op_split with "own_p_q") as "[p q]".
      iDestruct ("z" with "q") as "[_ z]".
       
    destruct wfm as [f_prop [f_unit f_op]]. (* need f Proper for the next step *)
    
    assert (f (interp state0)
          ≡ f(interp (p1 ⋅ q ⋅ z))) as equiv_interp_state.
    {
        setoid_rewrite incll. trivial.
    }
    
    iDestruct "z" as "[g [_ fi]]".
    setoid_rewrite equiv_interp_state.
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ q ⋅ z)) as pinv_p1_z. {
        destruct storage_mixin. destruct protocol_mixin0.
        setoid_rewrite <- incll. trivial.
    }

    have exch := exchng z pinv_p1_z.
    destruct exch as [pinv_p2_z [val_interp1 interp_eq]].
    assert (✓ (interp (p2 ⋅ q ⋅ z) ⋅ b2)) as val_interp2.
    {
      destruct storage_mixin. destruct base_ra_mixin0.
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ state0 : P,
          own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp state0))%I)
          with "[x fi]"
          as "inv_to_return".
    {
      iModIntro. (* strip later *)
      iExists (p2 ⋅ q ⋅ z). iFrame "x". iFrame "fi".
      iPureIntro. trivial.
    }
    iDestruct (ownI_close γ _ with "[w m inv_to_return od]") as "[w en]".
    { iFrame "m". iFrame "inv_to_return". iFrame "w". iFrame "od". }
    iModIntro. iModIntro. iFrame.
  Qed.

  Lemma logic_exchange_with_extra_guard_nondeterministic
    (p1 q: P) (b1: B) (output_ok: P -> B -> Prop) (γ: gname) (f: B -> iProp Σ) (G: iProp Σ)
    (exchng: storage_protocol_exchange_nondeterministic (p1 ⋅ q) b1
        (λ p2_q b2 , ∃ p2 , p2_q = p2 ⋅ q /\ output_ok p2 b2))
    : maps γ f ∗ □ (G &&{ {[ γ ]} }&&$> p_own γ q) ⊢
        G ∗ p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ ∃ p2 b2 ,
            ⌜ output_ok p2 b2 ⌝ ∗ G ∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps.
    iIntros "[[%wfm [#ounit #m]] [#gu #kbi]] [g [p f]]".
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iDestruct (ownI_open with "[w m oe]") as "[w [latp od]]".
    { iFrame "w". iFrame "m". iFrame "oe". }
    iMod (bi.later_exist_except_0 with "latp") as (state) "lat".
    unfold fguards, guards_with.
    iDestruct ("gu" $! G) as "gu2".
    
    iDestruct ("gu2" with "[g lat]") as "gu3".
    { iFrame "g". iIntros "g". iFrame "g".
        setoid_rewrite storage_bulk_inv_singleton. unfold storage_inv.
        iExists ((∃ state0 : P, own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp state0))%I).
        iFrame "m".
        setoid_rewrite know_bulk_inv_singleton. unfold know_inv.
        iModIntro. iExists state. iFrame "lat".
    }
    
    iMod "gu3" as "[po b]".
    
     iAssert ((own γ (◯ Inved q) ∧
          (◇ ∃ state : P, G ∗ ▷
                (own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp state))))%I)
          with "[po b]" as "x".
      { iSplit. { iFrame. } 
        iDestruct ("b" with "po") as "[ex t]".
        setoid_rewrite storage_bulk_inv_singleton. unfold storage_inv.
        iDestruct "ex" as (P0) "[#own lat]".
        iDestruct (ownIagree γ P0 _ with "[m own]") as "eq".
        { iSplitL. { iFrame "own". } iFrame "m". }
        iRewrite "eq" in "lat".
        iMod (bi.later_exist_except_0 with "lat") as (state0) "lat".
        iExists state0. iFrame.
      }
      iMod (and_except0_r with "x") as "x".
      rewrite bi.and_exist_l.
      iDestruct "x" as (state0) "x".
      iMod (apply_timeless with "x") as "x".
      iDestruct (stuff1 with "x") as "%pinvs".
      unfold p_own.
      (*iDestruct (stuff3 γ p1 q state0 with "[p x]") as "%incll". { iFrame. }*)
      
      iAssert (own γ (◯ Inved q) ∧ own γ (● Inved state0) ∗ (G ∗ ⌜pinv state0⌝ ∗ ▷ f (interp state0)))%I with "[x]" as "x".
      { iSplit. { iDestruct "x" as "[x _]". iFrame. }
          iDestruct "x" as "[_ [x [y z]]]". iFrame. }
      iDestruct (andsep_to_sepand_ucmra with "x") as "[x y]".
      { apply auth_frag_disjointness. }
      iDestruct (own_separates_out γ (◯ Inved q) (own γ (◯ Inved q) ∧ G ∗ ⌜pinv state0⌝ ∗ ▷ f (interp state0)) with "[y]") as "[y z]".
      { iFrame "y". iIntros "[k _]". iFrame. }
      
      iDestruct (own_inved_op p1 q γ with "[p y]") as "own_p_q". { iFrame. }
      iMod (own_sep_inv_incll_nondet γ (p1 ⋅ q) state0 (λ p2_q r , ∃ p2 b2 , p2_q = p2 ⋅ q /\ output_ok p2 b2
          /\ pinv ((p2 ⋅ q) ⋅ r)
          /\ ✓(interp ((p1 ⋅ q) ⋅ r) ⋅ b1)
          /\ interp ((p1 ⋅ q) ⋅ r) ⋅ b1 ≡ interp ((p2 ⋅ q) ⋅ r) ⋅ b2) with "[own_p_q x]")
          as (z p2_q) "[%incll [own_p_q x]]".
      { unfold storage_protocol_exchange_nondeterministic in exchng.
        intro r. intro j0. have exq := exchng r j0.
        destruct exq as [p2_q [b2 exq]].
        destruct exq as [[p2 [eq oo]] [a b]].
        exists (p2 ⋅ q). split.
        { exists p2. exists b2. intuition. { rewrite <- eq. apply a. }
            rewrite <- eq. trivial. }
        { rewrite <- eq. apply a. }
      }
      { apply pinvs. }
      { iFrame. }
      
      destruct incll as [[p2 [b2 [p2_q_eq bigconj]]] incll].
      rewrite p2_q_eq.
      iDestruct (own_inved_op_split with "own_p_q") as "[p q]".
      iDestruct ("z" with "q") as "[_ z]".
      
      destruct bigconj as [oo [pix [iix interp_eq]]].
       
    destruct wfm as [f_prop [f_unit f_op]]. (* need f Proper for the next step *)
    
    assert (f (interp state0)
          ≡ f(interp (p1 ⋅ q ⋅ z))) as equiv_interp_state.
    {
        setoid_rewrite incll. trivial.
    }
    
    iDestruct "z" as "[g [_ fi]]".
    setoid_rewrite equiv_interp_state.
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ q ⋅ z)) as pinv_p1_z. {
        destruct storage_mixin. destruct protocol_mixin0.
        setoid_rewrite <- incll. trivial.
    }

    assert (✓ (interp (p2 ⋅ q ⋅ z) ⋅ b2)) as val_interp2.
    {
      destruct storage_mixin. destruct base_ra_mixin0.
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ state0 : P,
          own γ (● Inved state0) ∗ ⌜pinv state0⌝ ∗ f (interp state0))%I)
          with "[x fi]"
          as "inv_to_return".
    {
      iModIntro. (* strip later *)
      iExists (p2 ⋅ q ⋅ z). iFrame "x". iFrame "fi".
      iPureIntro. trivial.
    }
    iDestruct (ownI_close γ _ with "[w m inv_to_return od]") as "[w en]".
    { iFrame "m". iFrame "inv_to_return". iFrame "w". iFrame "od". }
    iModIntro. iModIntro. iFrame. iExists p2. iExists b2. iFrame. iPureIntro. trivial.
  Qed.
  
  Lemma inved_op (a b : P) :
      Inved (a ⋅ b) ≡ Inved a ⋅ Inved b.
  Proof using H4 H6 H7 P equ. trivial. Qed.

  (* SP-Sep *)

  Lemma p_own_op a b γ :
      p_own γ (a ⋅ b) ⊣⊢ p_own γ a ∗ p_own γ b.
  Proof.
    unfold p_own.
    setoid_rewrite inved_op.
    rewrite auth_frag_op.
    apply own_op.
  Qed.
  
  Lemma op_unit (p: P) : p ⋅ ε ≡ p.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    destruct storage_mixin.
    destruct protocol_mixin.
    destruct protocol_ra_mixin.
    setoid_rewrite (@comm P).
    - apply protocol_unit_left_id.
    - trivial.
  Qed.
  
  Lemma op_unit_base (b: B) : b ⋅ ε ≡ b.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 storage_mixin Σ.
    destruct storage_mixin.
    destruct base_ra_mixin0.
    setoid_rewrite (@comm B).
    - apply base_unit_left_id0.
    - trivial.
  Qed.
  
  Lemma auth_inved_conjure_unit γ (state: P)
      : own γ (● Inved state) ==∗ own γ (● Inved state) ∗ own γ (◯ Inved ε).
  Proof.
      apply auth_conjure_frag.
      setoid_rewrite <- inved_op.
      setoid_rewrite op_unit.
      trivial.
  Qed.

  (* SP-Unit *)
  
  Lemma p_own_unit γ f
      : maps γ f ⊢ p_own γ ε.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps.
    iIntros "[%wfm [#ounit #m]]".
    unfold p_own.
    iFrame "ounit".
  Qed.

  (* SP-Deposit *)
    
  Lemma logic_deposit
      (p1 p2: P) (b1: B) (γ: gname) (f: B -> iProp Σ)
      (exchng: storage_protocol_deposit p1 p2 b1)
      : maps γ f ⊢
          p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ p_own γ p2.
   Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "#m pb".
    iMod (logic_exchange p1 p2 b1 (ε: B) γ f with "m pb") as "[pb u]".
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
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    destruct storage_mixin.
    destruct base_ra_mixin0.
    apply ra_validN_proper.
  Qed.
  
  Instance pinv_proper : Proper ((≡) ==> impl) (@pinv P _).
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    destruct storage_mixin.
    destruct protocol_mixin0.
    apply inv_proper.
  Qed.
  
  Lemma valid_interp (p: P)
      : pinv p -> ✓ (interp p).
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    destruct storage_mixin.
    apply interp_val0.
  Qed.

  (* SP-Withdraw *)
   
  Lemma logic_withdraw
      (p1 p2: P) (b2: B) (γ: gname) (f: B -> iProp Σ)
      (exchng: storage_protocol_withdraw p1 p2 b2)
      : maps γ f ⊢
          p_own γ p1 ={ {[ γ ]} }=∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "#m pb".
    iAssert (▷ f ε)%I as "u".
    {
      iModIntro. 
      unfold maps.
      iDestruct "m" as "[%wf #m]".
      unfold wf_prop_map in wf.
      destruct wf as [wf_prop [wf_unit _]].
      setoid_rewrite wf_unit. done.
    }
    iMod (logic_exchange p1 p2 (ε: B) b2 γ f with "m [pb u]") as "[pb fb2]".
    {
      unfold storage_protocol_exchange.
      unfold storage_protocol_withdraw in exchng.
      intros q pi1. have t := exchng q pi1. intuition.
      - setoid_rewrite op_unit_base.
        apply valid_interp. trivial.
      - setoid_rewrite op_unit_base. trivial.
    }
    { iFrame "pb". iFrame "u". }
    iModIntro. iFrame.
   Qed.

  (* SP-Update *)
   
  Lemma logic_update
      (p1 p2: P) (γ: gname) (f: B -> iProp Σ)
      (exchng: storage_protocol_update p1 p2)
      : maps γ f ⊢
          p_own γ p1 ={ {[ γ ]} }=∗ p_own γ p2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "#m pb".
    iDestruct (logic_withdraw p1 p2 ε γ f with "m pb") as "pb".
    {
      unfold storage_protocol_withdraw.
      unfold storage_protocol_update in exchng.
      intros q pi.
      have exch := exchng q.
      intuition.
      setoid_rewrite op_unit_base.
      trivial.
    }
    iMod "pb".
    iModIntro.
    iDestruct "pb" as "[pb _]".
    iFrame.
  Qed.
  
  Lemma valid_inved_of_pinv (p: P)
    : pinv p -> ✓ (Inved p). 
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    intro pi. unfold "✓", inved_protocol_valid. exists ε. setoid_rewrite op_unit.
    trivial.
  Qed.

  (* SP-Alloc *)
  
  Lemma logic_init_ns (p: P) (f: B -> iProp Σ) E (N: namespace)
      (pi: pinv p) (wf: wf_prop_map f)
  : ⊢ f (interp p) ={E}=∗ ∃ γ , ⌜ γ ∈ (↑ N : coPset) ⌝ ∗ maps γ f ∗ p_own γ p.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "f_init".
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iMod (ownI_alloc_and_simultaneous_own_alloc_ns
      (λ γ , 
        (∃ (state: P) ,
          own γ (● (Inved state))
          ∗ ⌜ pinv state ⌝
          ∗ (f (interp state)))%I
      )
      (● (Inved p) ⋅ (◯ (Inved ε) ⋅ ◯ (Inved p)))
      (↑ N)
      with "w") as "w".
    { apply nclose_infinite. }
    { 
      rewrite <- auth_frag_op.
      rewrite auth_both_valid_discrete. split; trivial.
      - replace (Inved ε ⋅ Inved p) with (Inved (ε ⋅ p)) by trivial.
        destruct storage_mixin. destruct protocol_mixin0. rewrite protocol_unit_left_id.
        trivial.
      - apply valid_inved_of_pinv. trivial.
    }
    
    iDestruct "w" as (γ) "[%in_ns [w [oinv [auth [u frag]]]]]".
    
    iDestruct ("w" with "[auth f_init]") as "w".
    {
      iModIntro. iExists p. iFrame. iPureIntro. trivial.
    }
    
    iModIntro. iModIntro.
    iFrame "w". iFrame "oe".
    iExists γ.
    unfold p_own. iFrame "frag".
    unfold maps.
    iFrame "oinv". iFrame.
    iPureIntro. split; trivial.
  Qed.
  
  Lemma logic_init (p: P) (f: B -> iProp Σ) E
      (pi: pinv p) (wf: wf_prop_map f)
  : ⊢ f (interp p) ={E}=∗ ∃ γ , maps γ f ∗ p_own γ p.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "f_init".
    iMod (logic_init_ns p f E nroot with "f_init") as (γ) "[_ t]"; trivial.
    iModIntro. iExists γ. iFrame.
  Qed.
  
  Lemma fupd_singleton_mask_frame (γ: gname) (X Y Z : iProp Σ) E
    (premise: X ⊢ Y ={ {[ γ ]} }=∗ Z) (is_in: γ ∈ E) : X ⊢ Y ={ E }=∗ Z.
  Proof using B H equb invGS0 Σ.
    iIntros "x y".
    iDestruct (premise with "x y") as "p".
    iDestruct (fupd_mask_frame_r _ _ (E ∖ {[γ]}) with "p") as "p".
    { set_solver. }
    assert ({[γ]} ∪ E ∖ {[γ]} = E) as sete. {
        replace ({[γ]} ∪ E ∖ {[γ]}) with ((E ∖ {[γ]}) ∪ {[γ]}) by set_solver.
        apply elem_diff_union_singleton. trivial.
    }
    rewrite sete. 
    trivial.
  Qed.
    
  Lemma logic_exchange'
    (p1 p2: P) (b1 b2: B) (γ: gname) (f: B -> iProp Σ) E
    (exchng: storage_protocol_exchange p1 p2 b1 b2)
    (gname_in_e: γ ∈ E)
    : maps γ f ⊢
        p_own γ p1 ∗ ▷ f b1 ={ E }=∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply logic_exchange; trivial.
  Qed.
   
  Lemma logic_deposit'
      (p1 p2: P) (b1: B) (γ: gname) (f: B -> iProp Σ) E
      (exchng: storage_protocol_deposit p1 p2 b1)
      (gname_in_e: γ ∈ E)
      : maps γ f ⊢
          p_own γ p1 ∗ ▷ f b1 ={ E }=∗ p_own γ p2.
   Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply logic_deposit; trivial.
   Qed.

  Lemma logic_withdraw'
      (p1 p2: P) (b2: B) (γ: gname) (f: B -> iProp Σ) E
      (exchng: storage_protocol_withdraw p1 p2 b2)
      (gname_in_e: γ ∈ E)
      : maps γ f ⊢
          p_own γ p1 ={ E }=∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply logic_withdraw; trivial.
  Qed.

  Lemma logic_update'
      (p1 p2: P) (γ: gname) (f: B -> iProp Σ) E
      (exchng: storage_protocol_update p1 p2)
      (gname_in_e: γ ∈ E)
      : maps γ f ⊢
          p_own γ p1 ={ E }=∗ p_own γ p2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    apply (fupd_singleton_mask_frame γ); trivial.
    apply logic_update; trivial.
  Qed.
  
  (* SP-PointProp *)
  
  Lemma point_prop_p_own (γ: gname) (p: P) : point_prop (p_own γ p).
  Proof.
    unfold p_own. apply point_prop_own.
  Qed.
  
  (* SP-Valid *)
  
  Lemma p_own_valid (γ: gname) (p: P)
      : (p_own γ p) ⊢ ⌜ ∃ q , pinv (p ⋅ q) ⌝.
  Proof.
    iIntros "x".  iDestruct (own_valid with "x") as "%x". iPureIntro.
    generalize x. clear x.
    rewrite auth_frag_valid.
    trivial.
  Qed.
 
End StorageLogic.
