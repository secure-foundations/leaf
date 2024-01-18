From stdpp Require Export coPset.
From iris.algebra Require Import gmap_view gset coPset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(** All definitions in this file are internal to [fancy_updates] with the
exception of what's in the [wsatGS] module. The module [wsatGS] is thus exported in
[fancy_updates], where [wsat] is only imported. *)
Module wsatGS.
  Class wsatGpreS (Σ : gFunctors) : Set := WsatGpreS {
    wsatGpreS_inv : inG Σ (gmap_viewR positive (laterO (iPropO Σ)));
    wsatGpreS_enabled : inG Σ coPset_disjR;
    wsatGpreS_disabled : inG Σ coPset_disjR;
  }.

  Class wsatGS (Σ : gFunctors) : Set := WsatG {
    wsat_inG : wsatGpreS Σ;
    invariant_name : gname;
    enabled_name : gname;
    disabled_name : gname;
  }.

  Definition wsatΣ : gFunctors :=
    #[GFunctor (gmap_viewRF positive (laterOF idOF));
      GFunctor coPset_disjR;
      GFunctor coPset_disjR].

  Global Instance subG_wsatΣ {Σ} : subG wsatΣ Σ → wsatGpreS Σ.
  Proof. solve_inG. Qed.
End wsatGS.
Import wsatGS.
Local Existing Instances wsat_inG wsatGpreS_inv wsatGpreS_enabled wsatGpreS_disabled.

Definition invariant_unfold {Σ} (P : iProp Σ) : later (iProp Σ) :=
  Next P.
Definition ownI `{!wsatGS Σ} (i : positive) (P : iProp Σ) : iProp Σ :=
  own invariant_name (gmap_view_frag i DfracDiscarded (invariant_unfold P)).
Global Typeclasses Opaque ownI.
Global Instance: Params (@invariant_unfold) 1 := {}.
Global Instance: Params (@ownI) 3 := {}.

Definition ownE `{!wsatGS Σ} (E : coPset) : iProp Σ :=
  own enabled_name (CoPset E).
Global Typeclasses Opaque ownE.
Global Instance: Params (@ownE) 3 := {}.

Definition ownD `{!wsatGS Σ} (E : coPset) : iProp Σ :=
  own disabled_name (CoPset E).
Global Typeclasses Opaque ownD.
Global Instance: Params (@ownD) 3 := {}.

Definition wsat `{!wsatGS Σ} : iProp Σ :=
  locked (∃ I : gmap positive (iProp Σ),
    own invariant_name (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
    ([∗ map] i ↦ Q ∈ I, (ownI i Q) ∗ (▷ Q ∗ ownD {[i]} ∨ ownE {[i]})) ∗
    (ownD (⊤ ∖ (gset_to_coPset (dom I))))
    )%I. 

Section wsat.
Context `{!wsatGS Σ}.
Implicit Types P : iProp Σ.

(* Invariants *)
Local Instance invariant_unfold_contractive : Contractive (@invariant_unfold Σ).
Proof. solve_contractive. Qed.
Global Instance ownI_contractive i : Contractive (@ownI Σ _ i).
Proof. solve_contractive. Qed.
Global Instance ownI_persistent i P : Persistent (ownI i P).
Proof. rewrite /ownI. apply _. Qed.

Lemma ownE_empty : ⊢ |==> ownE ∅.
Proof.
  rewrite /bi_emp_valid.
  by rewrite (own_unit (coPset_disjUR) enabled_name).
Qed.
Lemma ownE_op E1 E2 : E1 ## E2 → ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof. intros. by rewrite /ownE -own_op coPset_disj_union. Qed.
Lemma ownE_disjoint E1 E2 : ownE E1 ∗ ownE E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownE -own_op own_valid. by iIntros (?%coPset_disj_valid_op). Qed.
Lemma ownE_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownE_op|].
  iIntros "HE". iDestruct (ownE_disjoint with "HE") as %?.
  iSplit; first done. iApply ownE_op; by try iFrame.
Qed.
Lemma ownE_singleton_twice i : ownE {[i]} ∗ ownE {[i]} ⊢ False.
Proof. rewrite ownE_disjoint. iIntros (?); set_solver. Qed.

Lemma ownD_empty : ⊢ |==> ownD ∅.
Proof.
  rewrite /bi_emp_valid.
  by rewrite (own_unit (coPset_disjUR) disabled_name).
Qed.
Lemma ownD_op E1 E2 : E1 ## E2 → ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof. intros. by rewrite /ownD -own_op coPset_disj_union. Qed.
Lemma ownD_disjoint E1 E2 : ownD E1 ∗ ownD E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownD -own_op own_valid. by iIntros (?%coPset_disj_valid_op). Qed.
Lemma ownD_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownD_op|].
  iIntros "HE". iDestruct (ownD_disjoint with "HE") as %?.
  iSplit; first done. iApply ownD_op; by try iFrame.
Qed.
Lemma ownD_singleton_twice i : ownD {[i]} ∗ ownD {[i]} ⊢ False.
Proof. rewrite ownD_disjoint. iIntros (?); set_solver. Qed.

Lemma invariant_lookup (I : gmap positive (iProp Σ)) i P :
  own invariant_name (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
  own invariant_name (gmap_view_frag i DfracDiscarded (invariant_unfold P)) ⊢
  ∃ Q, ⌜I !! i = Some Q⌝ ∗ ▷ (Q ≡ P).
Proof.
  rewrite -own_op own_valid gmap_view_both_validI bi.and_elim_r.
  rewrite lookup_fmap option_equivI.
  case: (I !! i)=> [Q|] /=; last by eauto.
  iIntros "?". iExists Q; iSplit; first done.
  by rewrite later_equivI.
Qed.

Lemma ownI_open i P : wsat ∗ ownI i P ∗ ownE {[i]} ⊢ wsat ∗ ▷ P ∗ ownD {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HiE)". iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  iDestruct (invariant_lookup I i P with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[Ho [[HQ $]|HiE']] HI]"; eauto.
  - iSplitR "HQ"; last by iNext; iRewrite -"HPQ".
    iExists I. iFrame "Hw". iFrame "Hd". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI"; eauto.
  - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.
Lemma ownI_close i P : wsat ∗ ownI i P ∗ ▷ P ∗ ownD {[i]} ⊢ wsat ∗ ownE {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HP & HiD)". iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  iDestruct (invariant_lookup with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_sepM_delete _ _ i with "HI") as "[[Ho [[HQ ?]|$]] HI]"; eauto.
  - iDestruct (ownD_singleton_twice with "[$]") as %[].
  - iExists I. iFrame "Hw". iFrame "Hd". iApply (big_sepM_delete _ _ i); eauto.
    iFrame "HI". iFrame "Ho". iLeft. iFrame "HiD". by iNext; iRewrite "HPQ".
Qed.

Lemma not_in_dom_to_none {V} (I: gmap positive V) (i: positive)
  (HIi : i ∉ dom I) : I !! i = None.
Proof.
  generalize HIi.
  rewrite elem_of_dom.
  intros J.
  unfold is_Some in J.
  destruct (I !! i); trivial.
  exfalso. apply J. exists v. trivial.
Qed.

Lemma get_fresh {V} (g: gmap positive V) : ∃ x , g !! x = None.
Proof.
  exists (fresh (dom g)).
  assert (fresh (dom g) ∉ dom g) as H.
  {
    apply is_fresh.
  }
  apply not_in_dom_to_none. trivial.
Qed.

Lemma not_in_dom {V} (I: gmap positive V) (i: positive) :
  I !! i = None -> i ∈ (⊤ ∖ (gset_to_coPset (dom I))).
Proof.
  intro J. rewrite elem_of_difference.
  rewrite elem_of_gset_to_coPset.
  rewrite elem_of_dom.
  rewrite J. split; trivial. apply elem_of_top. trivial.
Qed.
  
Lemma diff_union (s: coPset) (i: positive) :
    i ∈ s -> s = (s ∖ {[ i ]}) ∪ {[ i ]}.
Proof.
  intro. apply set_eq. intros.  rewrite elem_of_union.
          rewrite elem_of_difference. rewrite elem_of_singleton.
          have h : Decision (x = i) by solve_decision. destruct h; intuition.
          subst i. trivial.
Qed.

Lemma gmap_dom_coPset_insert {V} (I: gmap positive V) (i: positive) (P: V)
    : gset_to_coPset (dom (<[i:=P]> I)) = (gset_to_coPset (dom I)) ∪ {[ i ]}.
Proof.
  apply set_eq.
  intro x.
  rewrite elem_of_gset_to_coPset.
  rewrite elem_of_dom.
  rewrite elem_of_union.
  rewrite elem_of_gset_to_coPset.
  rewrite elem_of_dom.
  have h : Decision (i = x) by solve_decision. destruct h.
  - subst x. rewrite elem_of_singleton. rewrite lookup_insert. intuition.
  - rewrite lookup_insert_ne; trivial. rewrite elem_of_singleton; trivial.
        intuition. subst x. contradiction.
Qed.
    
Lemma diff_domm_inserted {V} (I: gmap positive V) (i: positive) (P: V)
    : (⊤ ∖ gset_to_coPset (dom (<[i:=P]> I)))
     = (⊤ ∖ gset_to_coPset (dom I) ∖ {[ i ]}).
Proof.
  rewrite gmap_dom_coPset_insert. set_solver.
Qed.

Lemma ownI_alloc φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P.
Proof.
  iIntros (Hfresh) "[Hw HP]". rewrite /wsat -!lock.
  
  iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  
  have is_f := Hfresh (@dom _ (gset positive) (gset_dom) I). 
  destruct is_f as [i [ni phi]].
  
  assert (I !! i = None) as HIi by (apply not_in_dom_to_none; trivial).
  
  (*have is_f := get_fresh I.
  destruct is_f as [i HIi].*)
  assert (i ∈ (⊤ ∖ gset_to_coPset (dom I))) as in_comp. { apply not_in_dom. trivial. }
  have du := diff_union _ _ in_comp.
  rewrite du. 
  
  iDestruct (ownD_op with "Hd") as "[Hd HE]". { set_solver. }
  
  
  (*iMod (own_unit (coPset_disjUR) disabled_name) as "HE". 
  
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).*)
  
  
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
   iModIntro; iExists i;  iSplit; [done|].
   rewrite /ownI.
   iDestruct (bi.persistent_sep_dup with "HiP") as "[HiP HiP2]".
   iFrame "HiP". 
  
  iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  rewrite diff_domm_inserted. iFrame "Hd".
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iFrame "HiP2". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_open φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {[i]} -∗ wsat) ∗ ownI i P ∗ ownD {[i]}.
Proof.
  iIntros (Hfresh) "Hw". rewrite /wsat -!lock. iDestruct "Hw" as (I) "[Hw [HI Hd]]".
  
  have is_f := Hfresh (@dom _ (gset positive) (gset_dom) I).
  destruct is_f as [i [ni phi]].
  assert (I !! i = None) as HIi by (apply not_in_dom_to_none; trivial).
  assert (i ∈ (⊤ ∖ gset_to_coPset (dom I))) as in_comp. { apply not_in_dom. trivial. }
  have du := diff_union _ _ in_comp.
  rewrite du.
  iDestruct (ownD_op with "Hd") as "[Hd HD]". { set_solver. }
  
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply (gmap_view_alloc _ i DfracDiscarded); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|].
  iDestruct (bi.persistent_sep_dup with "HiP") as "[HiP HiP2]".
  rewrite /ownI; iFrame "HiP". 
  rewrite -/(ownD _). iFrame "HD".
  iIntros "HE". iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert. }
  rewrite diff_domm_inserted. iFrame "Hd".
  iApply (big_sepM_insert _ I); first done.
  iFrame "HI". iFrame "HiP2". by iRight.
Qed.
End wsat.

Lemma copset_diff_empty
    : (⊤ ∖ gset_to_coPset ∅) = ⊤.
Proof.
  set_solver.
Qed.

(* Allocation of an initial world *)
Lemma wsat_alloc `{!wsatGpreS Σ} : ⊢ |==> ∃ _ : wsatGS Σ, wsat ∗ ownE ⊤.
Proof.
  iIntros.
  iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γI) "HI";
    first by apply gmap_view_auth_valid.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (CoPset ⊤)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatG _ _ γI γE γD).
  rewrite /wsat /ownE /ownD -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty.
  rewrite copset_diff_empty.
  iFrame. 
Qed.
