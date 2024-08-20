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
Require Import guarding.internal.auth_frag_util.
Require Import guarding.factoring_props.
Require Import guarding.conjunct_own_rule.
Require Import guarding.internal.wsat_util.

(*
Context {Σ: gFunctors}.
Context `{!invGS Σ}.
*)

Class InterpRel (P : Type) (B : Type) := interp_rel : P → B → Prop.


Record StorageMixin P B
    `{Equiv P, PCore P, Op P, Valid P, PInv P, Unit P}
    {equ: @Equivalence P (≡)}
    `{Equiv B, PCore B, Op B, Valid B, Unit B, InterpRel P B}
:= {
    protocol_mixin: ProtocolMixin P;
    base_ra_mixin: RAMixin B; (* completely ignore core *)
    
    base_unit_left_id : LeftId equiv (ε : B) op;

    interp_proper: Proper ((≡) ==> (≡) ==> (↔)) interp_rel;
    interp_val: ∀ (p: P) (b: B) , interp_rel p b -> ✓ b;
    
    p_inv_equiv : ∀ (p: P) , pinv p ↔ ∃ b , interp_rel p b;
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
  Context `{Equiv P, PCore P, Op P, PInv P, Valid P, Unit P, InterpRel P B}.
  
  
  Definition storage_protocol_guards (p: P) (b: B) :=
      ∀ q (t: B) , interp_rel (p ⋅ q) t -> b ≼ t.
      
  Definition storage_protocol_exchange (p1 p2: P) (b1 b2: B)  :=
      ∀ q t1, interp_rel (p1 ⋅ q) t1 ->
          ∃ t2, interp_rel (p2 ⋅ q) t2
          /\ ✓(t1 ⋅ b1)
          /\ t1 ⋅ b1 ≡ t2 ⋅ b2.
          
  Definition storage_protocol_update (p1 p2: P) :=
      ∀ q t1 , interp_rel (p1 ⋅ q) t1 -> interp_rel (p2 ⋅ q) t1.
          
  Definition storage_protocol_withdraw (p1 p2: P) (b2: B)  :=
      ∀ q t1 , interp_rel (p1 ⋅ q) t1 -> ∃ t2, interp_rel (p2 ⋅ q) t2
          /\ t1 ≡ t2 ⋅ b2.
          
  Definition storage_protocol_deposit (p1 p2: P) (b1: B)  :=
      ∀ q t1 , interp_rel (p1 ⋅ q) t1 -> ∃ t2, interp_rel (p2 ⋅ q) t2
          /\ ✓(t1 ⋅ b1)
          /\ t1 ⋅ b1 ≡ t2.
          
  Definition storage_protocol_exchange_nondeterministic (p1: P) (b1: B) (output_ok: P -> B -> Prop)  :=
      ∀ q t1 , interp_rel (p1 ⋅ q) t1 -> ∃ p2 b2 t2 , output_ok p2 b2
          /\ interp_rel (p2 ⋅ q) t2
          /\ ✓(t1 ⋅ b1)
          /\ t1 ⋅ b1 ≡ t2 ⋅ b2.
          
  Context {equ: Equivalence (≡@{P})}.
  Context {equb: Equivalence (≡@{B})}.
  Context {storage_mixin: StorageMixin P B}.

  Instance sm_interp_proper
      : Proper ((≡) ==> (≡) ==> (↔)) (interp_rel).
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
        ∃ (state_t: P * B) ,
          own γ (● (Inved (fst state_t)))
          ∗ ⌜ interp_rel (fst state_t) (snd state_t) ⌝
          ∗ (f (snd state_t))
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
  
  Lemma logic_guard (p: P) (b: B) (γ: gname) (E: coPset) (f: B -> iProp Σ)
    (g: storage_protocol_guards p b)
    (is_in: γ ∈ E)
    : maps γ f ⊢ (p_own γ p &&{ E }&&> ▷ f b).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps. iIntros "[%wfm [#ounit #oinv]]".
    iDestruct (guards_from_inv _ _ E with "oinv") as "mg". { set_solver. }
    assert (Inhabited (P * B)) as IP. { apply populate. apply (ε, ε). }
    rewrite bi.later_exist.
    iDestruct (guards_true E (p_own γ p)) as "gt".
    iDestruct (guards_transitive _ (p_own γ p) True%I with "[gt mg]") as "gg".
      { iFrame "gt". iFrame "mg". }
    iDestruct (lguards_exists_with_lhs (P*B) (p_own γ p) 
      (λ (state_t: P*B), (▷ (⌜ p ≼ state_t.1 ⌝))%I)
      (λ (state_t: P*B), (▷ (own γ (● Inved state_t.1) ∗ ⌜interp_rel state_t.1 state_t.2⌝ ∗ f state_t.2))%I)
      E 0
      with "[gg]") as "ggg".
    {
      iIntros (x) "o". unfold p_own. iNext. iDestruct (auth_frag_conjunct_to_incl with "o") as "o"; trivial.
    }
    { unfold guards. iFrame "gg". }
    assert ((∃ x, ▷ (own γ (● Inved x.1) ∗ ⌜interp_rel x.1 x.2⌝ ∗ f x.2) ∗ ▷ ⌜p ≼ x.1⌝)
      ⊣⊢ (▷ f b ∗ ▷(f b -∗ ∃ x, (own γ (● Inved x.1) ∗ ⌜interp_rel x.1 x.2⌝ ∗ f x.2) ∗ ⌜p ≼ x.1⌝)))
      as Equ.
    { iIntros. iSplit. { iIntros "r".
      rewrite <- bi.later_sep. iNext.
      iDestruct "r" as (state) "[[r [%pi t]] %p_incl_x]".
      unfold storage_protocol_guards in g.
      have p_incl_x_copy := p_incl_x.
      unfold "≼" in p_incl_x. destruct p_incl_x as [z p_incl_x].
      assert (interp_rel (p ⋅ z) state.2) as pinv_pz.
          { destruct storage_mixin. destruct protocol_mixin0. setoid_rewrite <- p_incl_x. trivial. }
      have b_le_interp := g z (state.2) pinv_pz.
      destruct b_le_interp as [bz b_le_interp].
      
      unfold wf_prop_map in wfm.
      destruct wfm as [fprop [funit fop]].

      assert (✓ (b ⋅ bz)) as is_val.
      { destruct storage_mixin. destruct base_ra_mixin0.
          setoid_rewrite <- b_le_interp.
          apply interp_val0 with (p := p ⋅ z). trivial. }
          
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
   
  Lemma own_sep_inv_incll_helper_nondet (p1 st : P) (t1 : B) (output_ok : P -> P -> Prop)
    (cond : ∀ (q : P) , interp_rel (p1 ⋅ q) t1 → ∃ p2 t2 , output_ok p2 q /\ interp_rel (p2 ⋅ q) t2)
   : ∀ (z: InvedProtocol P) , interp_rel st t1 -> ✓ (Inved st) -> Inved p1 ⋅ z ≡ Inved st →
    ∃ p2 , output_ok p2 (match z with Inved z0 => z0 | Nah => ε end) /\ ✓ (Inved p2 ⋅ z).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 storage_mixin Σ.
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
        assert (interp_rel (p1 ⋅ (@ε _ H9)) t1) as pi2.
        {
          destruct storage_mixin.
          destruct protocol_mixin0.
          unfold Proper, "==>", impl in interp_proper0.
          rewrite <- interp_proper0 with (x := st). { apply inv. }
          { symmetry. setoid_rewrite <- eq. trivial. }
          trivial.
        }
        have c := cond (@ε _ H9) pi2.
        destruct c as [p2 [b [oo c]]].
        exists p2.
        split. { apply oo. }
        exists ε.
        trivial.
        rewrite p_inv_equiv; trivial. exists b. apply c.
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
        
        assert (interp_rel (p1 ⋅ p) t1) as pinv1. {
          destruct storage_mixin.
          destruct protocol_mixin0.
          unfold Proper, "==>", impl in interp_proper0.
          rewrite <- interp_proper0. { apply inv. }
          { symmetry. trivial. } trivial.
        }
        have c := cond p pinv1.
        destruct c as [p2 [b [oo c]]].
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
        rewrite p_inv_equiv; trivial. exists b. apply c.
      }
      { destruct storage_mixin. trivial. }
  Qed.
  
  (*
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
  *)
        
  Lemma op_nah (p1 state : P)
    : Inved p1 ⋅ Nah ≡ Inved state -> p1 ≡ state.
  Proof. intros. trivial. Qed.
  
  Lemma op_inved_inved (p1 p2 p : P)
    : Inved p1 ⋅ Inved p2 ≡ Inved p -> p1 ⋅ p2 ≡ p.
  Proof. intros. trivial. Qed.
        
  (*
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
   *)
   
   Lemma own_sep_inv_incll_nondet γ (p1 state : P) (t1: B) (output_ok: P -> P -> Prop)
      (cond: ∀ q , interp_rel (p1 ⋅ q) t1 -> ∃ p2 t2 , output_ok p2 q /\ interp_rel (p2 ⋅ q) t2)
      (pi: interp_rel state t1)
    : own γ (◯ Inved p1) ∗ own γ (● Inved state) ==∗
      ∃ (z p2: P) , ⌜ output_ok p2 z /\ state ≡ p1 ⋅ z ⌝
          ∗ own γ (◯ Inved p2) ∗ own γ (● Inved (p2 ⋅ z)).
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 storage_mixin Σ.
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
      have rr := own_sep_inv_incll_helper_nondet p1 state t1 output_ok cond z pi val2 equi.
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
    
  (*
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
  *)
   
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
    iMod (bi.later_exist_except_0 with "latp") as (state_t) "lat".
    iDestruct "lat" as "[ois [ps fi]]".
    iMod "ois" as "ois".
    iMod "ps" as "%ps".
    unfold p_own.
    iMod (own_sep_inv_incll_nondet γ p1 state_t.1 state_t.2 (λ p2 q , ∃ b2 t2 , output_ok p2 b2
          /\ interp_rel (p2 ⋅ q) t2
          /\ ✓(state_t.2 ⋅ b1)
          /\ state_t.2 ⋅ b1 ≡ t2 ⋅ b2) with "[p ois]")
        as (z p2) "[[%big_output_ok %incll] [p ois]]".
    { unfold storage_protocol_exchange in exchng. intros q pi.
        have exch := exchng q state_t.2 pi. destruct exch as [p2 [b2 [t2 exch]]]. exists p2. exists t2. intuition. exists b2. exists t2. intuition. }
    { trivial. }
    { iFrame. }
    destruct big_output_ok as [b2 [t2 [oo [pix [vix interp_eq]]]]].
    
    destruct wfm as [f_prop [f_unit f_op]]. (* need f Proper for the next step *)
    
    (*assert (f (interp state)
          ≡ f(interp (p1 ⋅ z))) as equiv_interp_state.
    {
        setoid_rewrite incll. trivial.
    }*)
    
    (*setoid_rewrite equiv_interp_state.*)
    
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ z)) as pinv_p1_z. {
        destruct storage_mixin. destruct protocol_mixin0.
        setoid_rewrite <- incll. trivial.
        rewrite p_inv_equiv; trivial. exists (state_t.2). apply ps.
    }

    assert (✓ (t2 ⋅ b2)) as val_interp2.
    {
      destruct storage_mixin. destruct base_ra_mixin0.
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ (state0_t0 : P * B),
          own γ (● Inved state0_t0.1) ∗ ⌜interp_rel state0_t0.1 state0_t0.2⌝ ∗ f state0_t0.2)%I)
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
   
  Lemma logic_exchange
    (p1 p2: P) (b1 b2: B) (γ: gname) (f: B -> iProp Σ)
    (exchng: storage_protocol_exchange p1 p2 b1 b2)
    : maps γ f ⊢
        p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "x y".
    iDestruct (logic_exchange_nondeterministic p1 b1 (λ p b, p = p2 ∧ b = b2) γ f with "x y") as "J".
    { unfold storage_protocol_exchange in exchng.
      unfold storage_protocol_exchange_nondeterministic.
      intros q t1 pi. exists p2. exists b2.
      have ex := exchng q t1 pi. destruct ex as [t2 ex]. exists t2. intuition.
    }
    iMod "J" as (p0 b0) "[[%eq1 %eq2] t]". iModIntro. rewrite eq1. rewrite eq2. iFrame.
  Qed.
   
   (*
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
  *)
  
  (*
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
  *)
  
  (*
  Lemma logic_exchange_with_extra_guard_nondeterministic2
    (p1 q: P) (b1: B) (output_ok: P -> B -> Prop) (γ: gname) (f: B -> iProp Σ) (G: iProp Σ) E
    (exchng: storage_protocol_exchange_nondeterministic (p1 ⋅ q) b1
        (λ p2_q b2 , ∃ p2 , p2_q = p2 ⋅ q /\ output_ok p2 b2))
    (gname_in_e: γ ∈ E)
    : maps γ f ∗ □ (G &&{ E }&&> p_own γ q) ⊢
        G ∗ p_own γ p1 ∗ ▷ f b1 ={ E }=∗ ∃ p2 b2 ,
            ⌜ output_ok p2 b2 ⌝ ∗ G ∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps.
    iIntros "[[%wfm [#ounit #m]] #gu] [g [p f]]".
    iDestruct (guards_from_inv _ _ E with "m") as "mg". { set_solver. }
    iDestruct (guards_true E G) as "gt".
    iDestruct (guards_transitive _ G True%I with "[gt mg]") as "gg".
    { iFrame "gt". iFrame "mg". }
    iDestruct (guards_open_two_simultaneously G _ _ E E with "[g gg gu]") as "opened".
    { set_solver. }
    { iFrame "g". iSplit. { iFrame "gg". } iFrame "gu". }
    iMod "opened" as (T) "[t [tinv [town back]]]".
    
    iAssert ((◇ own γ (◯ Inved q) ∧ (
          ◇ (▷ (∃ state : P, own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp state)) -∗ T)
          ∗
          ◇ (∃ state : P, ▷
                (own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp state)))
          ))%I)
          with "[t tinv town]" as "x".
    { iSplit. { iMod ("town" with "t") as "town". unfold p_own.
        iDestruct "town" as "[x y]". iModIntro. iFrame "x". }
        iDestruct ("tinv" with "t") as "[tinv back]".
        iFrame "back".
        iMod "tinv" as "tinv".
        iMod (bi.later_exist_except_0 with "tinv") as (state0) "tinv".
        iModIntro.
        iExists state0.
        iFrame "tinv".
    }
    
    rewrite <- bi.except_0_sep.
    rewrite <- bi.except_0_and.
    iMod "x" as "x".
    
    rewrite bi.sep_exist_l.
    rewrite bi.and_exist_l.
    iDestruct "x" as (state0) "x".
    iMod (apply_timeless with "x") as "x".
    iDestruct (stuff1 with "x") as "%pinvs".
    unfold p_own.
    
    iAssert (own γ (◯ Inved q) ∧ own γ (● Inved state0) ∗ ((▷ (∃ state : P, own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp state)) -∗ T) ∗ ⌜pinv state0⌝ ∗ ▷ f (interp state0)))%I with "[x]" as "x".
      { iSplit. { iDestruct "x" as "[x _]". iFrame. }
          iDestruct "x" as "[_ [x [y z]]]". iFrame. }
          
    iDestruct (andsep_to_sepand_ucmra with "x") as "[x y]".
      { apply auth_frag_disjointness. }
      
    iDestruct (own_separates_out γ (◯ Inved q) (own γ (◯ Inved q) ∧ (▷ (∃ state : P, own γ (● Inved state) ∗ ⌜pinv state⌝ ∗ f (interp state)) -∗ T) ∗ ⌜pinv state0⌝ ∗ ▷ f (interp state0)) with "[y]") as "[y z]".
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
      iModIntro.
      iExists (p2 ⋅ q ⋅ z). iFrame "x". iFrame "fi".
      iPureIntro. trivial.
    }
    iDestruct ("g" with "inv_to_return") as "g".
    iMod ("back" with "g") as "g".
    iModIntro. iFrame. iExists p2. iExists b2. iFrame. iPureIntro. trivial.
  Qed.
  *)
    
  Lemma logic_exchange_with_extra_guard_nondeterministic_with_later
    (p1 q: P) (b1: B) (output_ok: P -> B -> Prop) (γ: gname) (f: B -> iProp Σ) (G: iProp Σ) E n
    (exchng: storage_protocol_exchange_nondeterministic (p1 ⋅ q) b1
        (λ p2_q b2 , ∃ p2 , p2_q = p2 ⋅ q /\ output_ok p2 b2))
    (gname_in_e: γ ∈ E)
    : maps γ f ∗ (G &&{ E ; n }&&> p_own γ q) ⊢
        G ∗ p_own γ p1 ∗ ▷ f b1 ={ E, ∅ }=∗ ▷^n (|={ ∅, E }=> ∃ p2 b2 ,
            ⌜ output_ok p2 b2 ⌝ ∗ G ∗ p_own γ p2 ∗ ▷ f b2).
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    unfold maps.
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
          ◇ (▷ (∃ state_t : (P * B), own γ (● Inved state_t.1) ∗ ⌜interp_rel state_t.1 state_t.2⌝ ∗ f state_t.2) -∗ T)
          ∗
          ◇ (∃ state_t : (P * B), ▷
                (own γ (● Inved state_t.1) ∗ ⌜interp_rel state_t.1 state_t.2⌝ ∗ f state_t.2))
          )))%I)
          with "[t tinv town]" as "x".
    { iSplit. { iDestruct ("town" with "t") as "town". iNext. unfold p_own.
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
    iMod (apply_timeless with "x") as "x".
    iDestruct (stuff1 with "x") as "%pinvs".
    unfold p_own.
    
    iAssert (own γ (◯ Inved q) ∧ own γ (● Inved state0.1) ∗ ((▷ (∃ state_t : P * B, own γ (● Inved state_t.1) ∗ ⌜interp_rel state_t.1 state_t.2⌝ ∗ f state_t.2) -∗ T) ∗ ⌜interp_rel state0.1 state0.2⌝ ∗ ▷ f state0.2))%I with "[x]" as "x".
      { iSplit. { iDestruct "x" as "[x _]". iFrame. }
          iDestruct "x" as "[_ [x [y z]]]". iFrame. }
          
    iDestruct (andsep_to_sepand_ucmra with "x") as "[x y]".
      { apply auth_frag_disjointness. }
      
    iDestruct (own_separates_out γ (◯ Inved q) (own γ (◯ Inved q) ∧ (▷ (∃ state_t : P * B, own γ (● Inved state_t.1) ∗ ⌜interp_rel state_t.1 state_t.2⌝ ∗ f state_t.2) -∗ T) ∗ ⌜interp_rel state0.1 state0.2⌝ ∗ ▷ f state0.2) with "[y]") as "[y z]".
      { iFrame "y". iIntros "[k _]". iFrame. }
      
    iDestruct (own_inved_op p1 q γ with "[p y]") as "own_p_q". { iFrame. }
    iMod (own_sep_inv_incll_nondet γ (p1 ⋅ q) state0.1 state0.2 (λ p2_q r , ∃ p2 b2 t2 , p2_q = p2 ⋅ q /\ output_ok p2 b2
          /\ interp_rel ((p2 ⋅ q) ⋅ r) t2
          /\ ✓(state0.2 ⋅ b1)
          /\ state0.2 ⋅ b1 ≡ t2 ⋅ b2) with "[own_p_q x]")
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
    
    (*
    assert (f (interp state0)
          ≡ f(interp (p1 ⋅ q ⋅ z))) as equiv_interp_state.
    {
        setoid_rewrite incll. trivial.
    }*)
    
    iDestruct "z" as "[g [_ fi]]".
    (*setoid_rewrite equiv_interp_state.*)
    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    
    unfold storage_protocol_exchange in exchng.
    assert (pinv (p1 ⋅ q ⋅ z)) as pinv_p1_z. {
        destruct storage_mixin. destruct protocol_mixin0.
        setoid_rewrite <- incll. rewrite p_inv_equiv; trivial. exists (state0.2).
        apply pinvs.
    }

    assert (✓ (t2 ⋅ b2)) as val_interp2.
    {
      destruct storage_mixin. destruct base_ra_mixin0.
      setoid_rewrite <- interp_eq. trivial.
    }
    
    setoid_rewrite <- f_op; trivial.

    setoid_rewrite interp_eq.
    setoid_rewrite f_op; trivial.
    
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ state0_t : P * B,
          own γ (● Inved state0_t.1) ∗ ⌜interp_rel state0_t.1 state0_t.2⌝ ∗ f state0_t.2)%I)
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
  
  Lemma logic_exchange_with_extra_guard_nondeterministic
    (p1 q: P) (b1: B) (output_ok: P -> B -> Prop) (γ: gname) (f: B -> iProp Σ) (G: iProp Σ) E
    (exchng: storage_protocol_exchange_nondeterministic (p1 ⋅ q) b1
        (λ p2_q b2 , ∃ p2 , p2_q = p2 ⋅ q /\ output_ok p2 b2))
    (gname_in_e: γ ∈ E)
    : maps γ f ∗ (G &&{ E }&&> p_own γ q) ⊢
        G ∗ p_own γ p1 ∗ ▷ f b1 ={ E }=∗ ∃ p2 b2 ,
            ⌜ output_ok p2 b2 ⌝ ∗ G ∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H10 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "x y".
    iDestruct (logic_exchange_with_extra_guard_nondeterministic_with_later p1 q b1 output_ok γ f G E 0 exchng gname_in_e with "x y") as "J".
    iMod "J". iMod "J". iModIntro. iFrame.
  Qed.
  
  Lemma logic_exchange_with_extra_guard
    (p1 p2 q: P) (b1 b2: B) (γ: gname) (f: B -> iProp Σ) (G: iProp Σ)
    (exchng: storage_protocol_exchange (p1 ⋅ q) (p2 ⋅ q) b1 b2)
    : maps γ f ∗ (G &&{ {[ γ ]} }&&> p_own γ q) ⊢
        G ∗ p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗ G ∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "x y".
    iDestruct (logic_exchange_with_extra_guard_nondeterministic p1 q b1 (λ p b, p = p2 ∧ b = b2) γ f G {[ γ ]} with "x y") as "J".
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
  
  (*
  Lemma logic_exchange_nondeterministic
    (p1: P) (b1: B) (output_ok: P -> B -> Prop) (γ: gname) (f: B -> iProp Σ)
    (exchng: storage_protocol_exchange_nondeterministic p1 b1 output_ok)
    : maps γ f ⊢
        p_own γ p1 ∗ ▷ f b1 ={ {[ γ ]} }=∗
          ∃ p2 b2 , ⌜ output_ok p2 b2 ⌝ ∗ p_own γ p2 ∗ ▷ f b2.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "maps p_own".
    iDestruct (logic_exchange_with_extra_guard_nondeterministic p1 ε b1 output_ok γ f True {[ γ ]}) as "J".
    { unfold storage_protocol_exchange_nondeterministic in *. intros q pi.
      assert (p1 ⋅ ε ≡ p1) as X. {
        destruct storage_mixin. destruct protocol_mixin.
        rewrite ra_comm; trivial.
      }
      assert (pinv (p1 ⋅ q)) as Y. {
        destruct storage_mixin. destruct protocol_mixin.
          apply inv_proper with (x := (p1 ⋅ ε) ⋅ q); trivial.
          rewrite ra_comm; trivial.
          setoid_replace (p1 ⋅ q) with (q ⋅ p1) by (rewrite ra_comm; trivial).
          have op_proper := (ra_op_proper P protocol_ra_mixin).
          unfold Proper, "==>", impl in op_proper.
          have opp := op_proper q (p1 ⋅ ε) p1.
          apply opp. apply X.
      }
      
      have ex := exchng q Y.
      destruct ex as [p2 [b2 [oo [pi2 in2]]]].
      exists (p2 ⋅ ε). exists b2.
      
      assert (p2 ⋅ ε ≡ p2) as Z. {
        destruct storage_mixin. destruct protocol_mixin.
        rewrite ra_comm; trivial.
      }
      assert (pinv (p2 ⋅ ε ⋅ q)) as W. {
        destruct storage_mixin. destruct protocol_mixin.
          apply inv_proper with (x := (p2 ⋅ q)); trivial.
          rewrite ra_comm; trivial.
          setoid_replace (p2 ⋅ ε ⋅ q) with (q ⋅ (p2 ⋅ ε)) by (rewrite ra_comm; trivial).
          have op_proper := (ra_op_proper P protocol_ra_mixin).
          unfold Proper, "==>", impl in op_proper.
          have opp := op_proper q p2 (p2 ⋅ ε).
          apply opp. symmetry. apply Z.
      }
      intuition.
      { exists p2. split; trivial. }
   *)   

    
  
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
  
  (*Lemma valid_interp (p: P)
      : pinv p -> ✓ (interp p).
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    destruct storage_mixin.
    apply interp_val0.
  Qed.*)

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
      intros q t1 pi1. have j := exchng q t1 pi1. destruct j as [t2 j].
      exists t2. intuition.
      - setoid_rewrite op_unit_base.
        destruct storage_mixin. apply (interp_val0 (p1 ⋅ q)). trivial.
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
  
  Lemma valid_inved_of_pinv (p: P)
    : pinv p -> ✓ (Inved p). 
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ inG0 storage_mixin Σ.
    intro pi. unfold "✓", inved_protocol_valid. exists ε. setoid_rewrite op_unit.
    trivial.
  Qed.

  (* SP-Alloc *)
  
  Lemma logic_init_ns (p: P) (b: B) (f: B -> iProp Σ) E (N: namespace)
      (pi: interp_rel p b) (wf: wf_prop_map f)
  : ⊢ f b ={E}=∗ ∃ γ , ⌜ γ ∈ (↑ N : coPset) ⌝ ∗ maps γ f ∗ p_own γ p.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "f_init".
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iMod (ownI_alloc_and_simultaneous_own_alloc_ns
      (λ γ , 
        (∃ (state_t: P * B) ,
          own γ (● (Inved state_t.1))
          ∗ ⌜ interp_rel state_t.1 state_t.2 ⌝
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
        destruct storage_mixin. destruct protocol_mixin0. rewrite protocol_unit_left_id.
        trivial.
      - apply valid_inved_of_pinv. rewrite p_inv_equiv; trivial. exists b. apply pi.
    }
    
    iDestruct "w" as (γ) "[%in_ns [w [oinv [auth [u frag]]]]]".
    
    iDestruct ("w" with "[auth f_init]") as "w".
    {
      iModIntro. iExists (p, b). iFrame. iPureIntro. trivial.
    }
    
    iModIntro. iModIntro.
    iFrame "w". iFrame "oe".
    iExists γ.
    unfold p_own. iFrame "frag".
    unfold maps.
    iFrame "oinv". iFrame.
    iPureIntro. split; trivial.
  Qed.
  
  Lemma logic_init (p: P) (b: B) (f: B -> iProp Σ) E
      (pi: interp_rel p b) (wf: wf_prop_map f)
  : ⊢ f b ={E}=∗ ∃ γ , maps γ f ∗ p_own γ p.
  Proof using B H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 P equ equb inG0 invGS0 storage_mixin Σ.
    iIntros "f_init".
    iMod (logic_init_ns p b f E nroot with "f_init") as (γ) "[_ t]"; trivial.
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
        apply guarding.guard.elem_diff_union_singleton. trivial.
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
