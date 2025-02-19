Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
Require Import guarding.lib.boxes.
Require Import guarding.lib.lifetime_internals_ra.
Require Import guarding.lib.lifetime_internals_inv.

Require Import stdpp.base.
Require Import stdpp.namespaces.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

Section LlftLogic.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.
  Context `{!boxG Σ}.

  (*** Lifetime logic ***)

  (* end hide *)
  Definition NLLFT := nroot .@ "leaf_lifetime_logic".

  (** A Lifetime κ is defined as a [gset nat]. Though this should technically be
  an implementation detail, this makes it easy to export the basic properties of [Lifetime]
  (EqDecidable, Countable) and [⊓] (associativity, commutativity). *)
  
  Definition Lifetime := gset nat.

  Global Instance llft_intersect : Meet Lifetime := λ κ1 κ2, κ1 ∪ κ2.
  Definition llft_empty : Lifetime := ∅.
  (* begin hide *)

  Local Definition llft_alive_def (κ : Lifetime) : iProp Σ := [∗ set] k ∈ κ , Alive llft_name k.
  Local Definition llft_dead_def (κ : Lifetime) : iProp Σ := ∃ k , ⌜ k ∈ κ ⌝ ∗ Dead llft_name k.

  Local Definition llft_ctx_def : iProp Σ :=
    (inv NllftO (∃ outlives, Delayed llft_name None ∗ Outlives llft_name outlives
        ∗ ∀ o, ⌜o ∈ outlives⌝ -∗ (llft_alive_def o.1 &&{↑NllftG}&&> Alive llft_name o.2))) ∗
    (True &&{↑Nmain}&&>
      ∃ (sa sd blocked : gset nat),
        LtState llft_name sa sd
          ∗ llft_alive_def sa
          ∗ (▷ outer_inv llft_name sa sd blocked)
          ∗ llft_alive_def blocked
    ).

  Local Definition llft_alive_aux : seal (@llft_alive_def). Proof. by eexists. Qed.
  Local Definition llft_dead_aux : seal (@llft_dead_def). Proof. by eexists. Qed.
  Local Definition llft_ctx_aux : seal (@llft_ctx_def). Proof. by eexists. Qed.

  (* end hide *)
  
  (** Definitions of the lifetime tokens. Note that these aren't fractional since you
  use Leaf concepts instead. *)
  
  Definition llft_alive (κ : Lifetime) : iProp Σ. exact (llft_alive_aux.(unseal) κ). Defined.
  Definition llft_dead (κ : Lifetime) : iProp Σ. exact (llft_dead_aux.(unseal) κ). Defined.
  Definition llft_ctx : iProp Σ. exact (llft_ctx_aux.(unseal)). Defined.
  (* begin hide *)

  Local Definition llft_alive_unseal :
      @llft_alive = @llft_alive_def := llft_alive_aux.(seal_eq).
  Local Definition llft_dead_unseal :
      @llft_dead = @llft_dead_def := llft_dead_aux.(seal_eq).
  Local Definition llft_ctx_unseal :
      @llft_ctx = @llft_ctx_def := llft_ctx_aux.(seal_eq).

  Local Ltac unseal := rewrite
    ?llft_alive_unseal /llft_alive_def
    ?llft_dead_unseal /llft_dead_def
    ?llft_ctx_unseal /llft_ctx_def.
    
  Local Instance pers_dead2 γlt k : Persistent (Dead γlt k).
  Proof. Admitted.

  (* end hide *)

  Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
  
  (** Lifetime inclusion is, by definition, a guard proposition. This provides us with
  an analogue of RustBelt's "dynamic lifetime inclusion": to derive new lifetime inclusions
  we can use Leaf to derive new guard propositions. *)
  
  Definition llft_incl (κ1 κ2 : Lifetime) : iProp Σ :=
      @[ κ1 ] &&{↑NllftG}&&> @[ κ2 ].
  
  Infix "⊑" := llft_incl (at level 70) : bi_scope.
  
  (** The lifetime logic *)

  Global Instance pers_llft_ctx : Persistent llft_ctx.
  Proof. unseal. typeclasses eauto. Qed.
  
  Global Instance pers_llft_dead κ : Persistent ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_alive κ : Timeless (@[ κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Global Instance timeless_llft_dead κ : Timeless ([† κ ]).
  Proof. unseal. typeclasses eauto. Qed.

  Lemma llftl_not_own_end κ : @[ κ ] ∗ [† κ ] ⊢ False.
  Proof.
    unseal. iIntros "[A D]". iDestruct "D" as (k) "[%kk D]".
    iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. }
    iApply (lt_alive_dead_false llft_name k). iSplit; iFrame.
  Qed.

  Lemma llftl_not_own_end_and κ : @[ κ ] ∧ [† κ ] ⊢ False.
  Proof.
    unseal. iIntros "AD". unfold llft_dead. rewrite bi.and_exist_l. iDestruct "AD" as (k) "AD".
    iApply (lt_alive_dead_false llft_name k).
    iAssert (⌜k ∈ κ⌝)%I as "%kk". { iDestruct "AD" as "[_ [D _]]".  iFrame. }
    iSplit; iFrame.
    { iDestruct "AD" as "[A _]".
      iDestruct ((big_sepS_delete _ _ k) with "A") as "[A _]". { trivial. } iFrame. }
    { iDestruct "AD" as "[_ [_ D]]". iFrame. }
  Qed.
  
  Local Instance timeless_delayed o : Timeless (Delayed llft_name o). Admitted.
  Local Instance timeless_outlives o : Timeless (Outlives llft_name o). Admitted.

  Lemma llftl_borrow_shared κ (P : iProp Σ) :
      ▷ P ={↑NLLFT}=∗ (@[ κ ] &&{↑NllftG}&&> ▷ P) ∗ ([† κ ] ={↑NLLFT}=∗ ▷ P).
  Proof.
    iIntros "P".
    iMod new_cancel as (γc) "c1".
    iMod (guards_alloc_with_inv (NllftG) (↑NLLFT) ((P ∨ (llft_dead κ ∗ CCancel γc))) with "[P]") as "[#Tinv #Tguard]".
    { iNext. iLeft. iFrame "P". }
    iModIntro.
    iSplit.
    { 
      iAssert (llft_alive κ &&{ ↑NllftG ∪ ↑NllftG }&&> ▷ P) as "H".
      { iApply
        (guards_cancel_or (llft_alive κ) (llft_alive κ) (llft_dead κ ∗ CCancel γc) (▷ P)).
        { iIntros "t". iApply (llftl_not_own_end_and κ). iSplit.
          { iDestruct "t" as "[t _]". iFrame "t". }
          { iDestruct "t" as "[_ [t _]]". iFrame "t". }
        }
        iSplit. { iApply guards_refl. }
        { setoid_replace (llft_dead κ ∗ CCancel γc ∨ ▷ P)%I
            with (▷ P ∨ llft_dead κ ∗ CCancel γc)%I.
          { iDestruct (guards_true (↑NllftG) (llft_alive κ)) as "gt".
            iDestruct (guards_transitive (↑NllftG) (llft_alive κ)%I with "[gt Tguard]") as "J".
            { iFrame "Tguard". iFrame "gt". }
            rewrite bi.later_or.
            iDestruct (guards_remove_later_or_r (llft_dead κ ∗ CCancel γc) (▷ P) (↑NllftG)) as "X".
            iDestruct (guards_transitive (↑NllftG) (llft_alive κ)%I with "[J X]") as "R".
            { iFrame "J". iFrame "X". }
            iFrame "R".
          }
          rewrite bi.or_comm. trivial.
        }
      }
      rewrite subseteq_union_1_L. { iFrame "H". } set_solver.
    }
    iIntros "deadk".
    iDestruct (guards_open (True)%I (▷ (P ∨ llft_dead κ ∗ CCancel γc))%I (↑ NLLFT) (↑ NllftG) with "[Tguard]") as "J". { solve_ndisj. }
    { iFrame "Tguard". }
    iMod "J" as "[J K]". rewrite bi.later_or. iDestruct "J" as "[P|J]".
    { iDestruct ("K" with "[deadk c1]") as "K". { iRight. iFrame. }
        iMod "K" as "K". iModIntro. iFrame "P". }
    iDestruct "J" as "[_ c2]". iMod "c2".
    iDestruct (cancel_cancel_false γc with "[c1 c2]") as "J". { iFrame. } iExFalso. iFrame "J".
  Qed.

  Lemma llftl_incl_dead_implies_dead κ κ' :
      ⊢ llft_ctx ∗ κ ⊑ κ' ∗ [† κ' ] ={↑NllftG}=∗ [† κ ].
  Proof.
    iIntros "[#ctx [#incl #dead]]". unseal.
    iDestruct "ctx" as "[#other #ctx]".

    unfold llft_incl.

    leaf_hyp "incl" rhs to (False)%I as "G2".
    {
      leaf_by_sep. iIntros "a". iExFalso.
      iApply (llftl_not_own_end κ'). iFrame. unseal. iFrame "dead".
    }
    leaf_hyp "ctx" rhs to ((∃ sa sd blocked : gset nat, ⌜ κ ⊆ sa ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa ∗ ▷ outer_inv llft_name sa sd blocked ∗ llft_alive_def blocked)
        ∨ (∃ sa sd blocked : gset nat, ⌜ ¬(κ ⊆ sa) ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa ∗ ▷ outer_inv llft_name sa sd blocked ∗ llft_alive_def blocked) )%I
        as "ctx'".
    {
      leaf_by_sep. iIntros "T". iSplitL.
        - iDestruct "T" as (sa sd blocked) "[state_alive [alive ou]]".
          have h : Decision (κ ⊆ sa) by solve_decision. destruct h as [h|n]; trivial.
          + unseal. iLeft. iExists sa. iExists sd. iExists blocked. iFrame. iPureIntro. trivial.
          + unseal. iRight. iExists sa. iExists sd. iExists blocked. iFrame. iPureIntro. trivial.
        - iIntros "T". iDestruct "T" as "[T|T]".
          + iDestruct "T" as (sa sd blocked) "[_ T]". iExists sa. iExists sd. iExists blocked. unseal. iFrame.
          + iDestruct "T" as (sa sd blocked) "[_ T]". iExists sa. iExists sd. iExists blocked. unseal. iFrame.
      }
      leaf_hyp "ctx'" mask to (↑NllftG) as "ctx2". { solve_ndisj. }

      iAssert (True &&{ ↑NllftG }&&> (∃ sa sd blocked : gset nat, ⌜κ ⊈ sa⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa ∗ ▷ outer_inv llft_name sa sd blocked ∗ llft_alive_def blocked)) as "G3".
        { iApply guards_cancel_or_by_chaining. iFrame "ctx2". 
          leaf_goal rhs to (llft_alive κ). { iFrame "G2". }
          leaf_by_sep.
          { iIntros "T". 
              iDestruct "T" as (sa sd blocked) "[%ksa [state alive]]".
                unseal. unfold llft_alive_def.
                replace sa with (κ ∪ (sa ∖ κ)) at 2.
                { setoid_rewrite big_sepS_union.
                  { iDestruct "alive" as "[[alive1 alive2] ou]". iFrame "alive1".
                    iIntros "rest".
                    iExists sa. iExists sd. iExists blocked. iFrame.
                    iCombine "rest alive2" as "alive".
                    setoid_rewrite <- big_sepS_union.
                    { replace (κ ∪ sa ∖ κ) with sa. { iFrame. iPureIntro. trivial. }
                    rewrite <- union_difference_L; trivial.
                }
                set_solver.
              }
              set_solver.
          } rewrite <- union_difference_L; trivial.
        }
      }            

      leaf_open "G3" with "[]" as "[J back]". { set_solver. } { done. }

      iDestruct "J" as (sa sd blocked) "[%k_sa [State [alive [ou Blo]]]]".
      have the_k := not_subset_eq_get κ sa k_sa. destruct the_k as [k [k_in k_not_in]].
      have h : Decision (k ∈ sd) by solve_decision. destruct h as [h|n]; trivial.
        - iDestruct (LtState_entails_Dead llft_name k sa sd with "State") as "#deadk"; trivial.
          iMod ("back" with "[State alive ou Blo]") as "true". { iExists sa. iExists sd. iExists blocked. iFrame. iPureIntro; trivial. } iModIntro. unfold llft_dead. iExists k. iFrame "deadk". iPureIntro. apply k_in.
        - (* weird technicality, if k was never made alive in the first place;
            first create it, then immediately kill it *)
          iMod (new_lt llft_name k sa sd with "State") as "[State [al1 al2]]"; trivial.
          iMod (kill_lt llft_name k (sa ∪ {[ k ]}) sd with "[State al1 al2]") as "[State deadk]". { iFrame. }
          iDestruct (outer_instant_kill_lt llft_name sa sd blocked k with "ou") as "ou".
          { set_solver. }
          iMod (fupd_mask_mono with "ou") as "ou". { solve_ndisj. }
          
          iMod ("back" with "[State alive ou Blo]") as "J".
          { iExists sa. iExists (sd ∪ {[k]}). iExists blocked. iFrame.
            replace (((sa ∪ {[k]}) ∖ {[k]})) with sa.
            { iFrame. iPureIntro. trivial. } set_solver.
          }
          iModIntro. unfold llft_dead. iExists k. iFrame "deadk". iPureIntro; trivial.
  Qed.

  Lemma llftl_incl_intersect κ κ' : ⊢ (κ ⊓ κ') ⊑ κ.
  Proof.
    leaf_by_sep. unseal. iIntros "Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1". iIntros "A3". iFrame.
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.

  Lemma llftl_incl_glb κ κ' κ'' :
      κ ⊑ κ' ∗ κ ⊑ κ'' ⊢ κ ⊑ (κ' ⊓ κ'').
  Proof.
    apply guards_and_point.
    - unseal. unfold llft_alive_def. apply factoring_props.point_prop_big_sepS.
        intros x xi. apply factoring_props.point_prop_own.
    - unseal. unfold llft_alive_def. apply alive_and_bigSepS.
  Qed.

  Lemma llftl_tok_inter_l κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ ].
  Proof.
    iIntros "Alive".
    replace (κ ∪ κ') with (κ ∪ ((κ ∪ κ') ∖ κ)).
    - unseal. rewrite big_sepS_union.
      + iDestruct "Alive" as "[A1 A2]". iFrame "A1".
      + set_solver.
    - symmetry. apply union_difference_L. set_solver.
  Qed.

  Lemma llftl_tok_inter_r κ κ' :
      @[ κ ⊓ κ' ] ⊢ @[ κ' ].
  Proof.
    replace (κ ⊓ κ') with (κ' ⊓ κ).
    - apply llftl_tok_inter_l. 
    - unfold meet, llft_intersect. set_solver.
  Qed.

  Lemma llftl_tok_inter_and κ κ' :
      @[ κ ⊓ κ' ] ⊣⊢ @[ κ ] ∧ @[ κ' ].
  Proof.
    iIntros. iSplit.
    - iIntros "t". iSplit.
      + iApply llftl_tok_inter_l. iFrame "t".
      + iApply llftl_tok_inter_r. iFrame "t".
  - unseal. iIntros. iApply alive_and_bigSepS. iFrame.
  Qed.

  Lemma llftl_end_inter κ κ' :
      [† κ ⊓ κ'] ⊣⊢ [† κ ] ∨ [† κ' ].
  Proof.
    unseal. iIntros. iSplit.
    - iIntros "t".  iDestruct "t" as (k) "[%kin t]".
      unfold llft_intersect in kin. rewrite elem_of_union in kin. destruct kin as [h|h].
      + iLeft. iExists k. iFrame "t". iPureIntro. trivial.
      + iRight. iExists k. iFrame "t". iPureIntro. trivial.
    - iIntros "t". iDestruct "t" as "[h|h]".
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold llft_intersect. set_solver.
      + iDestruct "h" as (k) "[%kin t]".
        iExists k. iFrame "t". iPureIntro. unfold llft_intersect. set_solver.
  Qed.

  Lemma llftl_tok_unit :
      ⊢ @[ llft_empty ].
  Proof.
    unseal. unfold llft_empty. rewrite big_sepS_empty. iIntros. done.
  Qed.

  Lemma llftl_end_unit :
      [† llft_empty ] ⊢ False.
  Proof.
    unseal. unfold llft_empty.
    iIntros "t". iDestruct "t" as (k) "[%p t]".
    rewrite elem_of_empty in p. contradiction.
  Qed.
  
  Lemma llftl_begin :
      llft_ctx ⊢ |={↑NLLFT}=> ∃ κ, @[ κ ] ∗ (@[ κ ] ={↑NLLFT}[∅]▷=∗ [† κ ]).
  Proof.
      unseal. iIntros "[#other #ctx]".  unfold llft_ctx.
      iDestruct (guards_open (True)%I _ (↑NLLFT) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [Ou Blo]]]".
      
      assert (∃ k , k ∉ (sa ∪ sd)) as Fres. { exists (fresh (sa ∪ sd)). apply is_fresh. }
      destruct Fres as [k Fres].
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (outer_new_lt llft_name sa sd blocked k with "[Ou Delayed]") as "X"; trivial. { iFrame "Ou". iFrame "Delayed". }
      iMod (fupd_mask_mono with "X") as "[Ou Delayed]". { solve_ndisj. }
      iMod ("Hclose" with "[Delayed O]"). { iFrame. }
      
      iMod (new_lt llft_name k sa sd with "[State]") as "T".
      { set_solver. } { set_solver. } { iFrame. }
      iDestruct "T" as "[State [A1 A2]]".
      iMod ("back" with "[Alive State A1 Ou Blo]").
      { iExists (sa ∪ {[k]}). iExists sd. iExists blocked. iFrame.
        unfold llft_alive.
        replace ((sa ∪ {[k]})) with (({[k]} ∪ sa)).
        { unseal. rewrite big_sepS_insert. { iFrame. } set_solver. } set_solver.
      }
      iModIntro.
      iExists ({[ k ]}). unfold llft_alive. 
      rewrite big_sepS_singleton. iFrame "A2".
      iIntros "token".

      (* ending the lifetime *)
      iInv "other" as (outlives1) "[>Delayed [>O1 O2]]" "Hclose".
      
      iDestruct (guards_open (True)%I _ (↑NLLFT ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa1 sd1 blocked1) "[State Alive]".
      iAssert (⌜k ∈ sa1⌝)%I as "%k_sa1".
      { iApply (lt_state_alive llft_name k sa1 sd1). iSplit. { iFrame "State". } iFrame "token". }
      
      iDestruct (LtState_disjoint llft_name _ _ with "State") as "%Hdisj".
      
      unseal. rewrite (big_sepS_delete _ sa1 k); trivial.
      iDestruct "Alive" as "[[token2 Alive] [Ou Blo]]".
      iMod (kill_lt llft_name k sa1 sd1 with "[State token token2]") as "[State #dead]". { iFrame. }
      
      iDestruct (outer_kill_lt_step1 llft_name sa1 sd1 blocked1 k with "[Ou Delayed]") as "X"; trivial. { set_solver. } { iFrame "Ou". iFrame "Delayed". }
      iMod (fupd_mask_mono with "X") as "[Ou Delayed]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive Ou Blo]") as "true".
      { iExists (sa1 ∖ {[k]}). iExists (sd1 ∪ {[k]}). iExists blocked1. iFrame. }
      
      destruct (decide (filter (λ (o: (gset nat * nat)) , o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1 = ∅)).
      { 
        assert (∀ other , (other, k) ∈ outlives1 → ¬(other ⊆ sa1 ∖ {[k]})) as Houtlives.
        { intros other. intros Hin Hdisj2. 
          assert ((other,  k) ∈ filter (λ o : gset nat * nat, o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1) as X. { rewrite elem_of_filter. set_solver. } rewrite e in X. set_solver. }
          
       iDestruct (guards_open (True)%I _ (↑NLLFT ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa2 sd2 blocked2) "[State [Alive [Ou Blo]]]".
      
      destruct (decide (k ∈ blocked2)). {
        iDestruct (big_sepS_delete _ _ k with "Blo") as "[B Blo]"; trivial.
        iExFalso. iApply (lt_alive_dead_false llft_name k). iSplit. { iFrame. } iFrame "dead".
      }
      
      iDestruct (outer_kill_lt_step2 llft_name sa2 sd2 blocked2 outlives1 k (sa1 ∖ {[k]}) with "[Ou Delayed O1]") as "X"; trivial. { iFrame "Ou". iFrame "Delayed". iFrame "O1". iFrame "dead". }
      iDestruct (step_fupd_mask_mono _ (↑NLLFT ∖ ↑NllftO ∖ ↑Nmain) _ ∅ with
       "X") as "X". { solve_ndisj. } { solve_ndisj. } iMod "X". iModIntro.
       iNext. iMod "X". iDestruct "X" as "[Inv [Outlives Delayed]]".
       
      iMod ("back" with "[Alive State Blo Inv]") as "X". { iExists sa2. iExists sd2. iExists blocked2.
        iFrame "State". iFrame "Alive". iFrame "Inv". iFrame "Blo". }
      iMod ("Hclose" with "[Outlives Delayed O2]") as "Y".
      { iNext. iExists outlives1. iFrame "Delayed". iFrame "Outlives". iFrame "O2". }
      
      iModIntro. iExists k. iFrame "dead". iPureIntro. set_solver.
     }
     
     (* case: something violates the outlives relation. derive a contradiction. *)
     assert (∃ (x : gset nat * nat) , x ∈ filter (λ o : gset nat * nat, o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1) as Hex_x. { apply set_choose_L; trivial. }
     destruct Hex_x as [[oalive odead] Hex].
     rewrite elem_of_filter in Hex. simpl in Hex. destruct Hex as [[Hex1 Hex2] Hex3].
     subst odead.
     iMod (fupd_mask_subseteq ∅) as "Hupd". { set_solver. }
     iModIntro. iNext. iMod "Hupd" as "_".
     iDestruct ("O2" $! ((oalive, k)) with "[]") as "#Oguard". { iPureIntro; trivial. }
     iDestruct (llftl_incl_dead_implies_dead oalive {[k]} with "[]") as "#OdeadUpd".
     { unseal. iFrame "#". unfold llft_incl. unseal. rewrite big_sepS_singleton.
      iFrame "Oguard". iPureIntro. set_solver. }
     
     iMod (fupd_mask_mono with "OdeadUpd") as "#Odead".

      
      iModIntro. unfold llft_dead. iExists k. iFrame "dead". iPureIntro. set_solver.
  Qed.
End LlftLogic.

Lemma llft_alloc {Σ: gFunctors} `{!llft_logicGpreS Σ} `{!invGS Σ} E
  : ⊢ |={E}=> ∃ _ : llft_logicGS Σ, llft_ctx.
Proof.
  iIntros. iMod lt_alloc as (γ) "J".
  iMod (guards_alloc_with_inv (NLLFT) E
      (∃ sa sd : gset nat, LtState γ sa sd ∗ [∗ set] k ∈ sa , Alive γ k) with "[J]") as "[_ K]".
   { iModIntro. iExists ∅. iExists ∅. iFrame. done. }
  iModIntro.
  iExists (LlftLogicG _ _ γ).
  rewrite llft_ctx_unseal /llft_ctx_def.
  iDestruct (guards_remove_later_rhs with "K") as "K2".
  unfold llft_alive_def. iFrame "K2".
Qed.

