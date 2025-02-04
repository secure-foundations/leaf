Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
Require Import guarding.lib.boxes.
Require Import guarding.lib.lifetime_internals_ra.
Require Import guarding.lib.lifetime_internals_inv.
Require Import guarding.lib.fractional.

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

(** The Leaf Liftime Logic.

This is based on RustBelt's lifetime logic, and has many similar rules, but it incorporates
Leaf's guarding operator to handle both shared borrows and lifetime inclusions. *)

Section LlftLogic.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS_gen hlc Σ}.
  
  (** There are two namespaces to know about as the user of the logic.
      All view shifts take place at [↑Nllft] and all guards (e.g., in lifetime inclusions)
      take place at [↑NllftG]. *)

  Definition Nllft := nroot .@ "leaf_lifetime_logic".
  Definition NllftG := nroot .@ "leaf_lifetime_logic" .@ "guarding".

  (*** Lifetime logic ***)

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
    (inv NllftO (∃ outlives, Delayed d_name None ∗ Outlives o_name outlives
        ∗ ∀ o, ⌜o ∈ outlives⌝ -∗ (llft_alive_def o.1 &&{↑NllftG}&&> Alive llft_name o.2))) ∗
    (True &&{↑Nmain}&&>
      ∃ (sa sd blocked : gset nat),
        LtState llft_name sa sd
          ∗ llft_alive_def sa
          ∗ (▷ outer_inv llft_name o_name d_name sa sd blocked)
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
  Proof. apply own_core_persistent. unfold CoreId. trivial. Qed.

  (* end hide *)

  Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
  
  (** Lifetime inclusion is, by definition, a guard proposition. This provides us with
  an analogue of RustBelt's "dynamic lifetime inclusion": to derive new lifetime inclusions
  we can use Leaf to derive new guard propositions. *)
  
  Definition llft_incl (κ1 κ2 : Lifetime) : iProp Σ :=
      @[ κ1 ] &&{↑NllftG}&&> @[ κ2 ].
  
  Infix "⊑" := llft_incl (at level 70) : bi_scope.
  
  (** Lifetime tokens and their algebra *)

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

  Lemma llftl_incl_dead_implies_dead E κ κ' :
      ↑NllftG ⊆ E →
      ⊢ llft_ctx ∗ κ ⊑ κ' ∗ [† κ' ] ={E}=∗ [† κ ].
  Proof.
    intros Hmask. iIntros "[#ctx [#incl #dead]]". unseal.
    iDestruct "ctx" as "[#other #ctx]".

    unfold llft_incl.

    leaf_hyp "incl" rhs to (False)%I as "G2".
    {
      leaf_by_sep. iIntros "a". iExFalso.
      iApply (llftl_not_own_end κ'). iFrame. unseal. iFrame "dead".
    }
    leaf_hyp "ctx" rhs to ((∃ sa sd blocked : gset nat, ⌜ κ ⊆ sa ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked ∗ llft_alive_def blocked)
        ∨ (∃ sa sd blocked : gset nat, ⌜ ¬(κ ⊆ sa) ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked ∗ llft_alive_def blocked) )%I
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

      iAssert (True &&{ ↑NllftG }&&> (∃ sa sd blocked : gset nat, ⌜κ ⊈ sa⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked ∗ llft_alive_def blocked)) as "G3".
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
          iDestruct (outer_instant_kill_lt llft_name o_name d_name sa sd blocked k with "ou") as "ou".
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
  
  Lemma llftl_incl_weaken_lhs_l κ κ' κ'' :
      κ ⊑ κ' ⊢ (κ ⊓ κ'') ⊑ κ'.
  Proof.
    iIntros "#incl". leaf_goal lhs to (@[κ])%I. - iApply llftl_incl_intersect. - iFrame "#".
  Qed.
  
  Lemma llftl_incl_weaken_lhs_r κ κ' κ'' :
      κ ⊑ κ' ⊢ (κ'' ⊓ κ) ⊑ κ'.
  Proof.
      replace (κ'' ⊓ κ) with (κ ⊓ κ'') by (unfold llft_intersect; set_solver).
      apply llftl_incl_weaken_lhs_l.
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
  
  (** Allocating a new lifetime token *)
  
  Lemma llftl_begin E :
      ↑Nllft ⊆ E →
      llft_ctx ⊢ |={E}=> ∃ κ, @[ κ ] ∗ □ (@[ κ ] ={↑Nllft}[∅]▷=∗ [† κ ]).
  Proof.
      intros Hmask. unseal. iIntros "[#other #ctx]".  unfold llft_ctx.
      iDestruct (guards_open (True)%I _ E (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [Ou Blo]]]".
      
      assert (∃ k , k ∉ (sa ∪ sd)) as Fres. { exists (fresh (sa ∪ sd)). apply is_fresh. }
      destruct Fres as [k Fres].
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (outer_new_lt llft_name o_name d_name sa sd blocked k with "[Ou Delayed]") as "X"; trivial. { iFrame "Ou". iFrame "Delayed". }
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
      iModIntro. iIntros "token".

      (* ending the lifetime *)
      iInv "other" as (outlives1) "[>Delayed [>O1 O2]]" "Hclose".
      
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa1 sd1 blocked1) "[State Alive]".
      iAssert (⌜k ∈ sa1⌝)%I as "%k_sa1".
      { iApply (lt_state_alive llft_name k sa1 sd1). iSplit. { iFrame "State". } iFrame "token". }
      
      iDestruct (LtState_disjoint llft_name _ _ with "State") as "%Hdisj".
      
      unseal. rewrite (big_sepS_delete _ sa1 k); trivial.
      iDestruct "Alive" as "[[token2 Alive] [Ou Blo]]".
      iMod (kill_lt llft_name k sa1 sd1 with "[State token token2]") as "[State #dead]". { iFrame. }
      
      iDestruct (outer_kill_lt_step1 llft_name o_name d_name sa1 sd1 blocked1 k with "[Ou Delayed]") as "X"; trivial. { set_solver. } { iFrame "Ou". iFrame "Delayed". }
      iMod (fupd_mask_mono with "X") as "[Ou Delayed]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive Ou Blo]") as "true".
      { iExists (sa1 ∖ {[k]}). iExists (sd1 ∪ {[k]}). iExists blocked1. iFrame. }
      
      destruct (decide (filter (λ (o: (gset nat * nat)) , o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1 = ∅)).
      { 
        assert (∀ other , (other, k) ∈ outlives1 → ¬(other ⊆ sa1 ∖ {[k]})) as Houtlives.
        { intros other. intros Hin Hdisj2. 
          assert ((other,  k) ∈ filter (λ o : gset nat * nat, o.2 = k ∧ o.1 ⊆ sa1 ∖ {[k]}) outlives1) as X. { rewrite elem_of_filter. set_solver. } rewrite e in X. set_solver. }
          
       iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa2 sd2 blocked2) "[State [Alive [Ou Blo]]]".
      
      destruct (decide (k ∈ blocked2)). {
        iDestruct (big_sepS_delete _ _ k with "Blo") as "[B Blo]"; trivial.
        iExFalso. iApply (lt_alive_dead_false llft_name k). iSplit. { iFrame. } iFrame "dead".
      }
      
      iDestruct (outer_kill_lt_step2 llft_name o_name d_name sa2 sd2 blocked2 outlives1 k (sa1 ∖ {[k]}) with "[Ou Delayed O1]") as "X"; trivial. { iFrame "Ou". iFrame "Delayed". iFrame "O1". iFrame "dead". }
      iDestruct (step_fupd_mask_mono _ (↑Nllft ∖ ↑NllftO ∖ ↑Nmain) _ ∅ with
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
     iDestruct (llftl_incl_dead_implies_dead (↑NllftG) oalive {[k]} with "[]") as "#OdeadUpd".
     { solve_ndisj. }
     { unseal. iFrame "#". unfold llft_incl. unseal. rewrite big_sepS_singleton.
      iFrame "Oguard". iPureIntro. set_solver. }
     
     iMod (fupd_mask_mono with "OdeadUpd") as "#Odead". { solve_ndisj. }
     
     iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
     iMod "J" as "[J back]". iDestruct "J" as (sa2 sd2 blocked2) "[State [Alive [Ou Blo]]]".
     iDestruct "Ou" as (opt_k) "[>Delayed2 X]".
     iDestruct (delayed_agree with "[Delayed Delayed2]") as "%Dagree". { iFrame "Delayed". iFrame "Delayed2". }
     subst opt_k. iDestruct "X" as "[X1 [X2 [X3 >X4]]]". iDestruct "X4" as "%Hsa2eq".
     subst sa2.
     iDestruct (big_sepS_subseteq _ _ oalive with "Alive") as "Alive"; trivial.
     iExFalso. iApply (llftl_not_own_end oalive). unseal. iFrame "Alive". iFrame "Odead".
  Qed.
  
  (** Shared borrows *)
  
  Lemma llftl_borrow_shared E κ (P : iProp Σ) :
      ↑Nllft ⊆ E →
      ▷ P ={E}=∗ (@[ κ ] &&{↑NllftG}&&> ▷ P) ∗ ([† κ ] ={E}=∗ ▷ P).
  Proof.
    intros Hmask. iIntros "P".
    iMod new_cancel as (γc) "c1".
    iMod (guards_alloc_with_inv (NllftG) E ((P ∨ (llft_dead κ ∗ CCancel γc))) with "[P]") as "[#Tinv #Tguard]".
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
    iDestruct (guards_open (True)%I (▷ (P ∨ llft_dead κ ∗ CCancel γc))%I E (↑ NllftG) with "[Tguard]") as "J". { solve_ndisj. }
    { iFrame "Tguard". }
    iMod "J" as "[J K]". rewrite bi.later_or. iDestruct "J" as "[P|J]".
    { iDestruct ("K" with "[deadk c1]") as "K". { iRight. iFrame. }
        iMod "K" as "K". iModIntro. iFrame "P". }
    iDestruct "J" as "[_ c2]". iMod "c2".
    iDestruct (cancel_cancel_false γc with "[c1 c2]") as "J". { iFrame. } iExFalso. iFrame "J".
  Qed.
  
  (** Indexed borrows and full borrows *)
  
  Definition Idx: Type := slice_name * gset nat. 
  
  Definition idx_bor (κ: Lifetime) (idx: Idx) (P: iProp Σ) : iProp Σ :=
      let (sn, κ') := idx in
        κ ⊑ κ' ∗ slice Nbox sn P.
        
  Local Instance pers_idx_bor κ idx P : Persistent (idx_bor κ idx P).
  Proof. destruct idx. typeclasses eauto. Qed.
  
  Definition idx_bor_tok (idx: Idx) : iProp Σ :=
      let (sn, κ') := idx in
          OwnBorState llft_name sn (Borrow κ' {[default_dead]}).
          
  Definition full_bor (κ: Lifetime) (P: iProp Σ) : iProp Σ :=
      ∃ sn κ' ,
        κ ⊑ κ'
          ∗ slice Nbox sn P
          ∗ OwnBorState llft_name sn (Borrow κ' {[default_dead]}).
          
  Global Instance full_bor_proper κ :
    Proper ((≡) ==> (≡)) (full_bor κ).
  Proof. solve_proper. Qed.
  
  Lemma llftl_bor_idx κ P :
      full_bor κ P ⊣⊢ ∃ idx , idx_bor κ idx P ∗ idx_bor_tok idx.
  Proof.
    iIntros. iSplit.
    { iIntros "F". iDestruct "F" as (sn κ') "[F [G H]]". iExists (sn, κ'). iFrame. }
    { iIntros "F". iDestruct "F" as (idx) "[F G]". destruct idx as [sn κ'].
      iDestruct "F" as "[F H]". iFrame. }
  Qed.

  Lemma llftl_idx_shorten κ κ' idx P :
      κ' ⊑ κ -∗ idx_bor κ idx P -∗ idx_bor κ' idx P.
  Proof.
      destruct idx as [sn κ2]. iIntros "#g [#g2 #slice]". unfold idx_bor. 
      iFrame "slice".
      leaf_goal rhs to (@[κ])%I; iFrame "#".
  Qed.

  (* begin hide *) 
  Local Lemma make_everything_alive new sa sd blocked E :
      (↑Nbox ⊆ E) →
      LtState llft_name sa sd
        -∗ llft_alive_def sa
        -∗ ▷ outer_inv llft_name o_name d_name sa sd blocked
        -∗ Delayed d_name None
        -∗ |={E}=> ∃ sa' ,
        ⌜ new ⊆ sa' ∪ sd ⌝
        ∗ LtState llft_name sa' sd
        ∗ llft_alive_def sa'
        ∗ ▷ outer_inv llft_name o_name d_name sa' sd blocked
        ∗ Delayed d_name None.
  Proof.
    intros Hmask. induction new as [|x T ? IH] using set_ind_L. 
    - iIntros "State Alive OuInv Delayed". iModIntro. iExists sa. iFrame "OuInv".
      iFrame. iPureIntro. set_solver.
    - iIntros "State Alive OuInv Delayed". iMod (IH with "State Alive OuInv Delayed") as "X".
      iDestruct "X" as (sa') "[%HTin [State [Alive [OuInv Delayed]]]]".
      destruct (decide (x ∈ sa' ∪ sd)) as [Hin|Hout].
      + iModIntro. iExists sa'. iFrame "OuInv". iFrame. iPureIntro. set_solver.
      + iDestruct (outer_new_lt llft_name o_name d_name sa' sd blocked x with "[OuInv Delayed]") as "X".
        { trivial. } { iFrame "OuInv". iFrame. }
        iMod (fupd_mask_mono with "X") as "[OuInv Delayed]"; trivial.
        iMod (new_lt llft_name x sa' sd with "State") as "[State [Al1 Al2]]".
        { set_solver. } { set_solver. }
        iModIntro. iExists (sa' ∪ {[x]}). iFrame "OuInv". iFrame.
        iSplitR.
        { iPureIntro. set_solver. }
        unfold llft_alive_def. rewrite big_sepS_union; last by set_solver.
        iFrame "Alive". rewrite big_sepS_singleton. iFrame "Al1".
  Qed.
  
  Local Lemma outer_get_dead alive dead blocked
    : Delayed d_name None -∗ ▷ outer_inv llft_name o_name d_name alive dead blocked -∗ ▷ ⌜default_dead ∈ dead⌝.
  Proof.
    iIntros "Delayed1 OuInv". iNext. iDestruct "OuInv" as (opt_k) "[Delayed2 OuInv]".
    iDestruct (delayed_agree with "[Delayed1 Delayed2]") as "%Heq".
      { iFrame "Delayed1". iFrame "Delayed2". }
    subst opt_k.
    unfold inner_inv.
    iDestruct "OuInv" as (mbs mprops Ptotal outlives) "[_ [_ [_ [%W _]]]]".
    iPureIntro. unfold lifetime_internals_inv.map_wf in W. intuition.
  Qed.
  
  Local Lemma alive_alive_disjoint κ κ' sa :
    κ ⊆ sa →
    llft_alive_def sa -∗ llft_alive_def κ -∗ llft_alive_def κ' -∗ ⌜κ ## κ'⌝.
  Proof.
    unfold llft_alive_def. intros Hksa. iIntros "Set1 Set2 Set3".
    destruct (decide (κ ## κ')) as [Hdisj|Hnotdisj]; first by iPureIntro; trivial.
    assert (∃ x , x ∈ κ ∩ κ') as Hex_x. { apply set_choose_L; set_solver. }
    destruct Hex_x as [x Hxin].
    rewrite (big_sepS_delete _ sa x); last by set_solver.
    rewrite (big_sepS_delete _ κ x); last by set_solver.
    rewrite (big_sepS_delete _ κ' x); last by set_solver.
    iDestruct "Set1" as "[Alive1 _]".
    iDestruct "Set2" as "[Alive2 _]".
    iDestruct "Set3" as "[Alive3 _]".
    iExFalso. iApply alive_alive_alive_false. iFrame "Alive1". iFrame.
  Qed.
  
  Local Lemma augment_outlives sa sd blocked outlives κ κ' E :
    (κ ⊆ sa) →
    (κ' ⊆ sa) →
    (↑Nbox ⊆ E) →
    (κ ⊑ κ')
    -∗ Delayed d_name None
    -∗ ▷ (Outlives o_name outlives ∗
           ∀ o : Lifetime * nat,
             ⌜o ∈ outlives⌝ -∗ llft_alive_def o.1 &&{ ↑NllftG }&&> Alive llft_name o.2)
    -∗ ▷ outer_inv llft_name o_name d_name sa sd blocked
    -∗ LtState llft_name sa sd
    -∗ |={E}=> ∃ outlives' ,
    ⌜ ∀ k : nat, k ∈ κ' → (κ, k) ∈ outlives' ⌝
    ∗ Delayed d_name None
    ∗ ▷ (Outlives o_name outlives' ∗
           ∀ o : Lifetime * nat,
             ⌜o ∈ outlives'⌝ -∗ llft_alive_def o.1 &&{ ↑NllftG }&&> Alive llft_name o.2)
    ∗ ▷ outer_inv llft_name o_name d_name sa sd blocked
    ∗ LtState llft_name sa sd.
  Proof.
    intros Hk Hk' Hmask. iIntros "#Hincl Delayed [>Outlives #Hf] OuInv LtState".
    
    iDestruct (bi.later_mono _ _ (inv_get_outlives_condition llft_name o_name sa sd blocked outlives) with "[Outlives OuInv Delayed]") as "#>%Howf".
    { unfold outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".  iNext.
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
      
    iDestruct (bi.later_mono _ _ (inv_get_outlives_consistent llft_name o_name sa sd blocked outlives) with "[Outlives OuInv Delayed]") as "#>%Hoc".
    { unfold outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".  iNext.
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
      
    iDestruct (bi.later_mono _ _ (inv_get_alive_dead_disj llft_name o_name sa sd blocked) with "[Outlives OuInv Delayed]") as "#>%Hdisj".
    { unfold outer_inv. iDestruct "OuInv" as (opt_k) "[Delayed1 X]".  iNext.
      iDestruct (delayed_agree with "[Delayed1 Delayed]") as "%Heq".
      { iFrame "Delayed". iFrame "Delayed1". } subst opt_k. iFrame. }
    
    iDestruct (outer_augment_outlives llft_name o_name d_name sa sd blocked outlives
        (outlives ∪ (set_map (λ k, (κ, k)) κ'))
        with "[Delayed Outlives OuInv]") as "X".
    { set_solver. }
    { set_solver. }
    { unfold outlives_consistent. unfold outlives_consistent in Hoc. set_solver. }
    { iFrame. }
    
    iMod (fupd_mask_mono with "X") as "[D [OuInv X]]"; trivial.
    
    iExists (outlives ∪ (set_map (λ k, (κ, k)) κ')).
    iModIntro.
    iFrame.
    iSplitL.
    { iPureIntro. set_solver. }
    iNext.
    iIntros (o) "%Hoin". rewrite elem_of_union in Hoin.
    destruct Hoin as [Hoin_outlives|Hoin_setmap].
    - iApply "Hf". iPureIntro. trivial.
    - rewrite elem_of_map in Hoin_setmap. destruct Hoin_setmap as [x [Hoeq Hxin]]. subst o.
      simpl.
      leaf_goal rhs to (llft_alive_def κ').
      + unfold llft_alive_def. rewrite (big_sepS_delete _ _ x); trivial.
        iApply guards_weaken_sep_l.
      + unseal. unfold llft_incl. unseal. iFrame "Hincl".
  Qed.
  
  Local Lemma llftl_idx_acc_fwd E κ idx P :
      ↑Nllft ⊆ E →
      llft_ctx ∗ idx_bor κ idx P ⊢
        idx_bor_tok idx ∗ @[κ] ={E}=∗ (▷ P)
          ∗ OwnBorState llft_name (idx.1) (Unborrow κ idx.2 {[default_dead]}).
  Proof.
      unseal. intros Hmask.
      destruct idx as [sn κ']. iIntros "[[#other #ctx] [#Incl #Slice]] [OwnBor k]". unfold idx_bor_tok.
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive (κ ∪ κ' ∪ {[default_dead]}) with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct (outer_get_dead with "Delayed OuInv") as "#>%Hdd".
      iDestruct (lt_state_alive_set llft_name κ sa' sd with "[State k]") as "%Hksa'". { iFrame. }
      
      destruct (decide (κ' ⊆ sa')) as [Hk'sa'|Hk'sa'].
      { 
      iDestruct (alive_alive_disjoint with "Alive k Blo") as "%Hblocked_disj"; trivial.
      iMod (augment_outlives with "Incl Delayed O OuInv State") as (outlives') "[%Ho' [Delayed [O [OuInv State]]]]". { set_solver. } { set_solver. } { solve_ndisj. }
      iDestruct "O" as "[>Ostate Oguards]".
      
      
      iClear "other". iClear "ctx".
      
      iDestruct (outer_unborrow_start llft_name o_name d_name sa' sd blocked outlives' sn κ κ' {[default_dead]} P with "[Delayed OuInv OwnBor State Ostate]") as "X"; trivial. { set_solver. } { set_solver. } { iFrame. iFrame "Slice". }
      iMod (fupd_mask_mono with "X") as "[Delayed [OuInv [State [Ostate [OwnBor P]]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo k]"). {
        iExists sa'. iExists sd. iExists (blocked ∪ κ). iFrame "State".
        iFrame "Alive". iFrame "OuInv". unfold llft_alive_def. rewrite big_sepS_union.
        { iFrame. } set_solver.
      }
      iMod ("Hclose" with "[Delayed Ostate Oguards]"). { iNext. iExists outlives'. iFrame. }
      iModIntro. iFrame.
      }
      
      assert (∃ x , x ∈ κ' ∩ sd) as Hex_x. { apply set_choose_L.
          assert (κ' ⊆ sa' ∪ sd) as X by set_solver.
          set_solver. }
      destruct Hex_x as [x Hex].
      iDestruct (LtState_entails_Dead llft_name x sa' sd with "State") as "#Deadx". { set_solver. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
      
      iMod (llftl_incl_dead_implies_dead _ κ κ' with "[]") as "HdeadkUpd".
          { solve_ndisj. } { iFrame "#". unseal. iFrame "#". iPureIntro. set_solver. }
      iMod (fupd_mask_mono with "HdeadkUpd") as "#Hdeadk". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end κ). unseal. iFrame. iFrame "Hdeadk".
  Qed.
  
  (*Lemma llftl_idx_acc_back κ idx P :
      llft_ctx ∗ idx_bor κ idx P ⊢
        OwnBorState llft_name (idx.1) (Unborrow κ idx.2 {[default_dead]}) ∗ (▷ P)
        ={↑Nllft}=∗ idx_bor_tok idx.
  Proof.*)
  
  Local Lemma llftl_idx_acc_back_vs κ idx P Q :
      llft_ctx ∗ idx_bor κ idx P ⊢
        OwnBorState llft_name (idx.1) (Unborrow κ idx.2 {[default_dead]}) ∗ (▷ Q)
          ∗ ▷ (▷ Q ∗ [†κ] ={∅}=∗ ▷ P)
        ={↑Nllft}=∗ full_bor κ Q ∗ @[κ].
  Proof.
      unseal.
      iIntros "[[#other #ctx] #idxbor] [OwnBor [Q vs]]". destruct idx as [sn κ'].
      unfold idx_bor. iDestruct "idxbor" as "[#incl #slice]".
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      
      iDestruct (outer_inner_unborrow_end llft_name o_name d_name sa sd blocked sn κ κ' {[default_dead]} P Q with "[Delayed OuInv OwnBor slice vs Q State]") as "X". { iFrame. iFrame "#". }
      iMod (fupd_mask_mono with "X") as (sn2) "[Delayed [OuInv [State [OwnBor [#slice2 %Hbl]]]]]". { solve_ndisj. }
      
      iAssert (llft_alive_def (blocked ∖ κ) ∗ llft_alive_def κ)%I with "[Blo]" as "[Blo Ret]". {
        unfold llft_alive_def. rewrite <- big_sepS_union. { 
          replace (blocked ∖ κ ∪ κ) with blocked. { iFrame. }
          apply set_eq. intro x. destruct (decide (x ∈ κ)); set_solver.
        } set_solver.
      }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists (blocked ∖ κ). iFrame. }
      iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iFrame "Ret". unfold full_bor. iExists sn2. iExists κ'. iFrame.
      iFrame "#".
  Qed.
  (* end hide *)
  
  Lemma llftl_bor_acc E P κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ full_bor κ P -∗ @[κ] -∗ |={E}=> (▷ P) ∗
          (∀ Q, ▷ (▷ Q ∗ [†κ] ={∅}=∗ ▷ P) ∗ ▷ Q ={↑Nllft}=∗ full_bor κ Q ∗ @[κ]).
  Proof.
    intros Hmask.
    iIntros "#ctx fb alive". unfold full_bor. iDestruct "fb" as (sn κ') "[#incl [#slice OwnBor]]".
    iMod (llftl_idx_acc_fwd E κ (sn, κ') P with "[] [OwnBor alive]") as "[P OwnBor]".
      { trivial. } { iFrame "#". } { iFrame. }
    iModIntro. iFrame "P". iIntros (Q) "[vs Q]".
    iMod (llftl_idx_acc_back_vs κ (sn, κ') P Q with "[] [OwnBor Q vs]") as "[fb alive]".
      { iFrame "#". } { iFrame. }
    iModIntro. iFrame "alive". unfold full_bor. iDestruct "fb" as (sn2 κ2) "[#incl2 [#slice2 OwnBor]]".
    iExists sn2. iExists κ2.  iFrame. iFrame "#".
  Qed.
  
  Lemma llftl_bor_acc_atomic P κ :
      llft_ctx -∗ full_bor κ P -∗ |={↑Nllft, ∅}=>
          (▷ P ∗ (∀ Q, ▷ (▷ Q ∗ [†κ] ={∅}=∗ ▷ P) -∗ ▷ Q ={∅, ↑Nllft}=∗ full_bor κ Q))
          ∨ ([†κ] ∗ (|={∅, ↑Nllft}=> True)).
  Proof.
      unseal.
      iIntros "[#other #ctx] fb". unfold full_bor.
      iDestruct "fb" as (sn κ') "[#Incl [#slice OwnBor]]".
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive (κ ∪ κ') with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct (outer_get_dead with "Delayed OuInv") as "#>%Hdd".
      
      destruct (decide (κ ⊆ sa')) as [Hksa'|Hksa'].
      { 
      destruct (decide (κ' ⊆ sa')) as [Hk'sa'|Hk'sa'].
      { 
        iMod (augment_outlives with "Incl Delayed O OuInv State") as (outlives') "[%Ho' [Delayed [O [OuInv State]]]]". { set_solver. } { set_solver. } { solve_ndisj. }
        iDestruct "O" as "[>Ostate Oguards]".

        iClear "other". iClear "ctx".

        iDestruct (outer_unborrow_atomic llft_name o_name d_name sa' sd blocked outlives' sn κ κ' {[default_dead]} P with "[Delayed OuInv OwnBor State Ostate]") as "X"; trivial. { set_solver. } { iFrame. iFrame "slice". }
        iMod (fupd_mask_subseteq (↑Nbox)) as "Upd". { solve_ndisj. }

        iMod "X" as "[P X]". iModIntro. iLeft. iFrame "P".
        iIntros (Q). iDestruct ("X" $! Q) as "X".
        iIntros "Y Y2". iDestruct ("X" with "[Y Y2]") as "X". { iFrame. }

        iMod "X" as (sn2) "[Delayed [OuInv [State [Ostate [OwnBor #slice2]]]]]".
        iMod "Upd".

        iMod ("back" with "[State Alive OuInv Blo]"). {
          iExists sa'. iExists sd. iExists blocked. iFrame "State".
          iFrame "Alive". iFrame "OuInv". unfold llft_alive_def. { iFrame. } 
        }
        iMod ("Hclose" with "[Delayed Ostate Oguards]"). { iNext. iExists outlives'. iFrame. }
        iModIntro. iFrame. iFrame "#".
      }
      {
        assert (∃ x , x ∈ κ' ∩ sd) as Hex_x. { apply set_choose_L. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State") as "#Deadx". { set_solver. }

        iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
        iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
        
        iMod (llftl_incl_dead_implies_dead _ κ κ' with "[]") as "HdeadkUpd". { solve_ndisj. } { iFrame "#". unseal. iFrame "#". iPureIntro. set_solver. }
        iDestruct "HdeadkUpd" as "#Hdeadk".
        
        iMod (fupd_mask_subseteq ∅) as "Upd". { solve_ndisj. }
        iModIntro. iRight. iFrame "Upd". unseal. iFrame "Hdeadk".
      }
      }
      {
        assert (∃ x , x ∈ κ ∩ sd) as Hex_x. { apply set_choose_L. set_solver. }
        destruct Hex_x as [x Hex].
        iDestruct (LtState_entails_Dead llft_name x sa' sd with "State") as "#Deadx". { set_solver. }

        iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
        iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
        
        iMod (fupd_mask_subseteq ∅) as "Upd". { solve_ndisj. }
        iModIntro. iRight. iFrame "Upd". iExists x. iFrame "Deadx". iPureIntro. set_solver.
      }
  Qed.
  
  (* begin hide *)
  Local Lemma llftl_borrow_fwd E P κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ ▷ P -∗ |={E}=> ∃ sn1 sn2 ,
          slice Nbox sn1 P
          ∗ slice Nbox sn2 P
          ∗ OwnBorState llft_name sn1 (Borrow κ {[default_dead]})
          ∗ OwnBorState llft_name sn2 (Borrow ∅ κ).
  Proof.
      unseal. intros Hmask.
      iIntros "[#other #ctx] P".
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive κ with "State Alive OuInv Delayed") as (sa') "[%Hsa' [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct (outer_borrow_create llft_name o_name d_name sa' sd blocked κ P with "[Delayed OuInv State P]") as "X"; trivial. { iFrame. }
      iMod (fupd_mask_mono with "X") as "[Delayed X]". { solve_ndisj. }
      iDestruct "X" as (sn1 sn2) "[OuInv [State [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]".
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
      iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iExists sn1. iExists sn2. iFrame. iFrame "#".
  Qed.
  
  Local Lemma llftl_borrow_rev P κ sn :
      llft_ctx -∗ slice Nbox sn P -∗ OwnBorState llft_name sn (Borrow ∅ κ) -∗ [†κ] -∗
        |={↑Nllft}=> ▷ P.
  Proof.
      unseal.
      iIntros "[#other #ctx] P OwnBor #Dead".
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (guards_open (True)%I _ (↑Nllft ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive κ with "State Alive OuInv Delayed") as (sa') "[%Hsa' [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct "Dead" as (k) "[%Hkdead Deadkin]".
      iAssert (⌜ k ∈ sd ⌝)%I as "%Hksd". { iApply (lt_state_dead llft_name k sa' sd). iSplitL; iFrame. iFrame "#". }
      
      iDestruct "O" as "[>Ostate #Oguards]".
      
      iDestruct (outer_unborrow_start llft_name o_name d_name sa' sd blocked outlives sn ∅ ∅ κ P with "[Delayed OuInv State P Ostate OwnBor]") as "X"; trivial. { set_solver. } { set_solver. } { set_solver. } { set_solver. } { intros k0. set_solver. } { iFrame "OuInv". iFrame. }
      iMod (fupd_mask_mono with "X") as "[Delayed [OuInv [State [Ostate [OwnBor P]]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. replace (blocked ∪ ∅) with blocked by set_solver. iFrame "OuInv". iFrame. }
      iMod ("Hclose" with "[Delayed Ostate]"). { iNext. iExists outlives. iFrame. iFrame "Oguards". }
      iModIntro. iFrame "P".
  Qed.
    
  Local Lemma llftl_weaken E sn κ κ' P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ OwnBorState llft_name sn (Borrow κ {[default_dead]}) -∗ slice Nbox sn P ={E}=∗
          ∃ sn' , OwnBorState llft_name sn' (Borrow (κ ∪ κ') {[default_dead]}) ∗ slice Nbox sn' P.
  Proof.
    unseal. intros Hmask. iIntros "[#other #ctx] OwnBor #slice". unfold full_bor.
    
    iInv "other" as (outlives) "[>Delayed O]" "Hclose".
    iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
    iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
    iMod (make_everything_alive (κ') with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
    
    iDestruct (outer_reborrow llft_name o_name d_name sa' sd blocked P sn κ κ' with "[Delayed State OuInv OwnBor slice]") as "X". { trivial. } { iFrame. iFrame "slice". }
    iMod (fupd_mask_mono with "X") as (sn1 sn2) "[Delayed [OuInv [State [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]]". { solve_ndisj. }

    iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
    iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
    iModIntro.
    iExists sn1. iFrame "OwnBor1". iFrame "slice1".
  Qed.
  (* end hide *)
  
  Lemma llftl_borrow E κ P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ ▷ P -∗ |={E}=> full_bor κ P ∗ ([†κ] ={↑Nllft}=∗ ▷ P).
  Proof.
    intros Hmask. iIntros "#ctx P".
    iMod (llftl_borrow_fwd E P κ with "ctx P") as (sn1 sn2) "[#slice1 [#slice2 [OwnBor1 OwnBor2]]]". { trivial. }
    iModIntro. unfold full_bor. iSplitL "OwnBor1". { iExists sn1. iExists κ. iFrame. iFrame "slice1". iApply guards_refl. }
    iIntros "#kdead". iDestruct (llftl_borrow_rev P κ sn2 with "ctx slice2 OwnBor2 kdead") as "X". iFrame "X".
  Qed.
  
  Lemma llftl_sep_split E P Q κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ full_bor κ (P ∗ Q) ={E}=∗ full_bor κ P ∗ full_bor κ Q.
  Proof.
      unseal. intros Hmask. iIntros "[#other #ctx] fbPQ". unfold full_bor.
      iDestruct "fbPQ" as (sn κ') "[#incl [#slice OwnBor]]".
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      
      iDestruct (outer_split llft_name o_name d_name sa sd blocked sn κ' {[default_dead]} P Q
        with "[Delayed State OuInv OwnBor slice]") as "X". { iFrame. iFrame "slice". }
      iMod (fupd_mask_mono with "X") as (sn1 sn2) "[Delayed [OuInv [State [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists blocked. iFrame. }
      iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
      iModIntro.
      
      iSplitL "OwnBor1". { iExists sn1. iExists κ'. iFrame. iFrame "#". }
      { iExists sn2. iExists κ'. iFrame. iFrame "#". }
  Qed.
  
  Lemma llftl_sep_join E P Q κ :
      ↑Nllft ⊆ E →
      llft_ctx -∗ full_bor κ P -∗ full_bor κ Q ={E}=∗ full_bor κ (P ∗ Q).
  Proof.
      unseal. intros Hmask. iIntros "[#other #ctx] fbP fbQ". unfold full_bor.
      iDestruct "fbP" as (sn1 κ1) "[#incl1 [#slice1 OwnBor1]]".
      iDestruct "fbQ" as (sn2 κ2) "[#incl2 [#slice2 OwnBor2]]".
      
      iMod (llftl_weaken E sn1 κ1 κ2 with "[] OwnBor1 slice1") as (sn1') "[OwnBor1 #slice1']". { trivial. } { unseal. iFrame "#". }
      iMod (llftl_weaken E sn2 κ2 κ1 with "[] OwnBor2 slice2") as (sn2') "[OwnBor2 #slice2']". { trivial. } { unseal. iFrame "#". }
      replace (κ2 ∪ κ1) with (κ1 ∪ κ2) by set_solver.
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iMod (make_everything_alive ({[default_dead]}) with "State Alive OuInv Delayed") as (sa') "[%Hsa [State [Alive [OuInv Delayed]]]]". { solve_ndisj. }
      
      iDestruct (outer_join llft_name o_name d_name sa' sd blocked sn1' sn2' (κ1 ∪ κ2) {[default_dead]} P Q
        with "[Delayed State OuInv OwnBor1 OwnBor2]") as "X". { set_solver. } { iFrame. iFrame "#". }
      iMod (fupd_mask_mono with "X") as (sn) "[Delayed [OuInv [State [OwnBor #slice]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa'. iExists sd. iExists blocked. iFrame. }
      iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
      iModIntro.
      iExists sn. iExists (κ1 ∪ κ2). iFrame. iFrame "#".
      iApply llftl_incl_glb. iFrame "#".
  Qed.
  
  Lemma llftl_idx_bor_unnest E κ κ' idx P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ idx_bor κ idx P -∗ full_bor κ' (idx_bor_tok idx) -∗ |={E}=> full_bor (κ ⊓ κ') P.
  Proof.
      unseal. intros Hmask. unfold idx_bor. destruct idx as [sn κ2]. unfold full_bor.
      iIntros "[#other #ctx] [#incl #slice] fb".
      iDestruct "fb" as (sn' κ2') "[#incl2 [#slice2 OwnBor2]]".
      
      iInv "other" as (outlives) "[>Delayed O]" "Hclose".
      iDestruct (guards_open (True)%I _ (E ∖ ↑NllftO) (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      
      iDestruct (outer_unnest llft_name o_name d_name sa sd blocked sn sn' κ2 κ2' P with "[Delayed OuInv State OwnBor2]") as "X"; trivial. { iFrame. iFrame "#". }
      iMod (fupd_mask_mono with "X") as (sn2) "[Delayed [OuInv [State [OwnBor #slice3]]]]". { solve_ndisj. }
      
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists blocked. replace (blocked ∪ ∅) with blocked by set_solver. iFrame "OuInv". iFrame. }
      iMod ("Hclose" with "[Delayed O]"). { iNext. iExists outlives. iFrame. }
      iModIntro. iExists sn2. iExists (κ2 ∪ κ2'). 
      iFrame "#". iFrame. iApply llftl_incl_glb. iSplitL.
      - iApply llftl_incl_weaken_lhs_l. iFrame "incl".
      - iApply llftl_incl_weaken_lhs_r. iFrame "incl2".
  Qed.
  
  Lemma llftl_bor_fake E κ P :
    ↑NllftG ⊆ E →
    llft_ctx -∗ [†κ] ={E}=∗ full_bor κ P.
  Proof.
      unseal. unfold full_bor.
      intros Hmask. iIntros "[#other #ctx] #dead".
      
      iDestruct (guards_open (True)%I _ E (↑Nmain) with "[ctx]") as "J". { solve_ndisj. } { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd blocked) "[State [Alive [OuInv Blo]]]".
      iDestruct "dead" as (k) "[%HkK deadk]".
      iAssert (⌜k ∈ sd⌝)%I as "%Hksd". { iApply lt_state_dead. iSplit. { iFrame "State". } iFrame "deadk". }
      iDestruct (inner_fake llft_name sa sd blocked κ {[default_dead]} P with "State") as "X". { set_solver. }
      iMod (fupd_mask_mono with "X") as (sn) "[State [OwnBor #slice]]". { solve_ndisj. }
      iMod ("back" with "[State Alive OuInv Blo]"). { iExists sa. iExists sd. iExists blocked. iFrame "OuInv". iFrame. }
      iModIntro. iExists sn. iExists κ. iFrame. iFrame "#". iApply guards_refl.
  Qed.
  
  (** Derived rules about full borrows (all derived from the above, without using the model) *)
  
  Lemma llftl_bor_shorten κ κ' P :
      κ' ⊑ κ -∗ full_bor κ P -∗ full_bor κ' P.
  Proof.
      rewrite llftl_bor_idx. rewrite llftl_bor_idx.
      iIntros "#incl fb". iDestruct "fb" as (idx) "[idx tok]".
      iDestruct (llftl_idx_shorten κ κ' with "incl idx") as "idx". iExists idx. iFrame.
  Qed.

  Lemma llftl_reborrow E κ κ' P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ κ' ⊑ κ -∗ full_bor κ P -∗ |={E}=> full_bor κ' P ∗ ([†κ] ={↑Nllft}=∗ full_bor κ P).
  Proof.
      intros Hmask. iIntros "#ctx #incl fb". rewrite llftl_bor_idx.
      iDestruct "fb" as (idx) "[#idx tok]".
      iMod (llftl_borrow E κ' with "ctx tok") as "[tokbor back]"; trivial.
      iMod (llftl_idx_bor_unnest E κ κ' idx P with "ctx idx tokbor") as "fullbor"; trivial.
      iModIntro. iSplitL "fullbor".
      { iDestruct (llftl_bor_shorten _ κ' with "[] fullbor") as "fullbor".
        { iApply llftl_incl_glb. iFrame "incl". iApply guards_refl. } iFrame.
      }
      iIntros "#dead". 
      iMod (llftl_incl_dead_implies_dead _ κ' κ with "[]") as "#dead2". { solve_ndisj. } { iFrame "#". }
      destruct idx as [sn κ2].
      iMod ("back" with "dead2") as ">back".
      iModIntro. iExists (sn, κ2). iFrame. iFrame "#".
  Qed.
  
  Lemma llftl_bor_freeze `{!Inhabited T} E κ (P : T → iProp Σ):
      ↑Nllft ⊆ E →
      llft_ctx -∗ full_bor κ (∃ (x: T) , P x) ={E}=∗ ∃ (x: T), full_bor κ (P x).
  Proof.
      intros Hmask. iMod (fupd_mask_subseteq (↑Nllft)) as "Upd". { solve_ndisj. }
      iIntros "#ctx fb".
      iMod (llftl_bor_acc_atomic with "ctx fb") as "[[P back]|[#dead back]]".
      - iDestruct "P" as (x) "P".
        iDestruct ("back" $! (P x)) as "back".
        iDestruct ("back" with "[] P") as "back".
          { iNext. iIntros "[P k]". iModIntro. iExists x. iFrame "P". }
        iMod "back". iMod "Upd".
        iModIntro. iExists x. iFrame "back".
      - iMod "back".
        iMod (llftl_bor_fake _ κ (P (@inhabitant T _)) with "ctx dead"). { solve_ndisj. }
        iMod "Upd". iModIntro. iFrame.
  Qed.
      
  Lemma llftl_bor_pers E κ P (pers: Persistent P):
      ↑Nllft ⊆ E →
      llft_ctx -∗ full_bor κ P ={E}=∗ full_bor κ P ∗ ((▷ P) ∨ [†κ]).
  Proof.
      intros Hmask. iMod (fupd_mask_subseteq (↑Nllft)) as "Upd". { solve_ndisj. }
      iIntros "#ctx fb".
      iMod (llftl_bor_acc_atomic with "ctx fb") as "[[#P back]|[#dead back]]".
      - iMod ("back" $! (P)%I with "[] P") as "fb".
          { iNext. iIntros "[P2 dead]". iFrame. iModIntro. done. }
        iMod "Upd". iModIntro. iFrame "fb". iLeft. iFrame "P".
      - iMod "back".
        iMod (llftl_bor_fake _ κ P with "ctx dead"). { solve_ndisj. }
        iMod "Upd". iModIntro. iFrame. iRight. iFrame "dead".
  Qed.
  
  Lemma llftl_bor_unnest E κ κ' P :
      ↑Nllft ⊆ E →
      llft_ctx -∗ full_bor κ' (full_bor κ P) -∗ |={E}▷=> full_bor (κ ⊓ κ') P.
  Proof.
      intros Hmask. iIntros "#ctx fb".
      rewrite (llftl_bor_idx κ).
      
      iMod (llftl_bor_freeze with "ctx fb") as (idx) "fb"; trivial.
      iMod (llftl_sep_split with "ctx fb") as "[fb1 fb2]"; trivial.
      iMod (llftl_bor_pers with "ctx fb1") as "[fb1 [#idxbor|dead]]"; trivial.
      - iModIntro. iNext.
        iMod (llftl_idx_bor_unnest E κ κ' idx P with "ctx idxbor fb2") as "fb3". { trivial. }
        iModIntro. iFrame "fb3".
      - iMod (llftl_bor_fake _ (κ ⊓ κ') P with "ctx [dead]") as "fb3". { solve_ndisj. }
        { rewrite llftl_end_inter. iRight. iFrame. }
        iModIntro. iNext. iModIntro. iFrame. 
  Qed.
End LlftLogic.

(** Initializing the [llft_ctx] *)

Lemma llft_alloc {Σ: gFunctors} `{!llft_logicGpreS Σ} `{!invGS Σ} E
  : ⊢ |={E}=> ∃ _ : llft_logicGS Σ, llft_ctx.
Proof.
  iIntros.
  iMod lt_alloc as (γ) "[J Ab]".
  iMod (outlives_alloc ∅) as (γo) "[O1 O2]".
  iMod (delayed_alloc None) as (γd) "[D1 D2]".
  iMod (new_lt γ default_dead ∅ ∅ with "J") as "J". { set_solver. } { set_solver. }
  iMod (kill_lt γ default_dead with "J") as "[J dd]".
  iMod (guards_alloc_with_inv (Nmain) E
      (∃ sa sd blocked : gset nat, LtState γ sa sd ∗ ([∗ set] k ∈ sa , Alive γ k)
          ∗ (outer_inv γ γo γd sa sd blocked)
          ∗ ([∗ set] k ∈ blocked , Alive γ k)
      ) with "[J O1 D1 Ab]") as "[_ K]".
   { iModIntro. iExists ∅. iExists {[default_dead]}. iExists ∅. iFrame "J".
     rewrite big_sepS_empty.
     iSplitR; first by done. iSplitL; last by done.
     iExists None. iFrame "D1". iExists ∅. iExists ∅. iExists True%I. iExists ∅.
     iFrame "Ab". iFrame "O1".
     iSplitL. { unfold boxmap. rewrite fmap_empty. iApply box_alloc. }
     iSplitL. { rewrite future_vs_def. iIntros (k) "[%Hk _]". set_solver. }
     iSplitL. {
      iPureIntro. split; trivial. split.
      - unfold lifetime_internals_inv.map_wf.
        split. { set_solver. }
        split. { set_solver. }
        split. { set_solver. }
        split. { intros sn bs Hl. rewrite lookup_empty in Hl. discriminate. }
        split. { intros sn1 bs1 sn2 bs2 Hne Hl. rewrite lookup_empty in Hl. discriminate. }
        intros o Ho. set_solver.
      - intros o Ho. set_solver.
     }
     rewrite big_sepM_empty. done.
  }
  iMod (inv_alloc (NllftO) _ (∃ (outlives : outlives_set), Delayed γd None ∗ Outlives γo outlives
        ∗ ∀ (o : gset nat * nat), ⌜o ∈ outlives⌝ -∗ (([∗ set] k ∈ o.1, Alive γ k) &&{↑NllftG}&&> Alive γ o.2))%I with "[O2 D2]") as "Inv".
  {
    iNext. iExists ∅. iFrame "O2". iFrame "D2". iIntros (o) "%Ho". set_solver.
  }
  iModIntro.
  iExists (LlftLogicG _ _ γ γo γd).
  rewrite llft_ctx_unseal /llft_ctx_def.
  iSplitL "Inv". { iFrame "Inv". }
  leaf_goal rhs to _; last by iFrame "K".
  leaf_by_sep_except0.
  iIntros "A". iDestruct "A" as (sa sd blocked) "[A [B [C D]]]". iMod "A". iMod "B". iMod "D".
  iModIntro. iSplitL. {
    iExists sa. iExists sd. iExists blocked. iFrame.
  }
  iIntros "A". iDestruct "A" as (sa1 sd1 blocked1) "[A [B [C D]]]".
  iNext. iExists sa1. iExists sd1. iExists blocked1. iFrame.
Qed.

Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
Infix "⊑" := llft_incl (at level 70) : bi_scope.

(** One difference between the Leaf Lifetime Logic and the classic RustBelt lifetime logic
is that our tokens aren't fractional. This might seem limiting, for example, because
rules like [llftl_bor_acc] require relinquishing the entire lifetime token [@[κ]],
whereas in the classic lifetime logic you could instead relinquish an arbitrary fraction of it.

Is it possible to use [llftl_bor_acc] in a more fine-grained way in the Leaf Lifetime Logic?
It is, if you combine it with other guarding capabilities.

For example, here's one thing you could do, demonstrated by [llftl_split_token]:

  1. Use Leaf to split a lifetime token [@[κ]] into two half tokens, [(1/2)@[k]], where:
  
      [(1/2)@[κ] &&{↑NllftG}&&> @[κ]]
  
  2. Create fresh lifetimes κ1 and κ2. Use [llftl_borrow_shared] on these half tokens with
     these fresh lifetimes.
     
      [@[κ1] &&{↑NllftG}&&> (1/2)@[κ]]
      
      [@[κ2] &&{↑NllftG}&&> (1/2)@[κ]]
  
  3. Using transitivity, we can establish [@[κ1] &&{↑NllftG}&&> @[κ]], i.e.,
     [κ1 ⊑ κ]. Likewise, we can get [κ2 ⊑ κ].
  
  Now if we want to use [llftl_bor_acc], we can use the [@[κ1]] and [@[κ2]] tokens in place
  of [@[κ]].
*)

Lemma llftl_split_token {Σ: gFunctors} `{!llft_logicGS Σ} `{!invGS_gen hlc Σ} `{!frac_logicG Σ}
  E κ :
  ↑Nllft ⊆ E →
  llft_ctx -∗
  @[κ] ={E}=∗ ∃ κ1 κ2 ,
      κ1 ⊑ κ ∗
      κ2 ⊑ κ ∗
      @[κ1] ∗
      @[κ2] ∗
      □ (@[ κ1 ] ={↑Nllft}[∅]▷=∗ [† κ1 ]) ∗
      □ (@[ κ2 ] ={↑Nllft}[∅]▷=∗ [† κ2 ]) ∗
      ([†κ1] ∗ [†κ2] ={E}=∗ @[κ])
  .
Proof.
  intros Hmask. iIntros "#ctx aliveK".
  iMod (frac_alloc2 NllftG with "aliveK") as (γ) "[F [#back #guard]]". { solve_ndisj. }
  rewrite <- Qp.half_half at 2.
  rewrite <- frac_join.
  iDestruct "F" as "[F1 F2]".
  iMod (llftl_begin with "ctx") as (κ1) "[A1 #Kill1] ". { trivial. }
  iMod (llftl_begin with "ctx") as (κ2) "[A2 #Kill2]". { trivial. }
  iMod (llftl_borrow_shared E κ1 with "F1") as "[#G1 F1]". { trivial. }
  iMod (llftl_borrow_shared E κ2 with "F2") as "[#G2 F2]". { trivial. }
  iModIntro. iExists κ1. iExists κ2.
  iDestruct (guards_remove_later_rhs with "G1") as "G1'".
  iDestruct (guards_remove_later_rhs with "G2") as "G2'".
  iDestruct ("guard" $! (1 / 2)%Qp) as "guardHalf".
  iDestruct (guards_remove_later_rhs with "guardHalf") as "guardHalf'".
  iFrame "A1". iFrame "A2". iFrame "Kill1". iFrame "Kill2".
  iSplitR. {
    leaf_goal rhs to _; last by iFrame "G1'".
    iApply "guardHalf'".
  }
  iSplitR. {
    leaf_goal rhs to _; last by iFrame "G2'".
    iApply "guardHalf'".
  }
  iIntros "[#D1 #D2]".
  iDestruct ("F1" with "D1") as "F1". iMod "F1".
  iDestruct ("F2" with "D2") as "F2". iMod "F2".
  iCombine "F1 F2" as "F". iMod "F".
  rewrite frac_join.
  rewrite Qp.half_half.
  iDestruct ("back" with "F") as "alive".
  iMod (fupd_mask_mono with "alive") as ">alive". { solve_ndisj. }
  iModIntro. iFrame "alive".
Qed.
