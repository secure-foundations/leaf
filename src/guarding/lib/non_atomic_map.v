From iris.prelude Require Import options.
Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes excl gmap_view.
From iris.base_logic.lib Require Export own iprop invariants.
From iris.proofmode Require Import base ltac_tactics tactics coq_tactics.

(** Non-atomic map. **)

Inductive ReadWriteState :=
  | Reading : nat → ReadWriteState
  | Writing : ReadWriteState
.

(* begin hide *)

Section NonAtomicInternals.

  Inductive ReadWriteState' :=
    | Reading' : ReadWriteState'
    | Writing' : ReadWriteState'
  .

  Context `{!EqDecision L, !Countable L}.
  Context {V: Type}.
  Context {Σ: gFunctors}.

  Local Definition erase_count (rw: ReadWriteState) : ReadWriteState' := match rw with 
    | Reading n => Reading'
    | Writing => Writing'
  end.

  Local Definition erase_count_map {L} {V} `{!EqDecision L, !Countable L} (σ: gmap L (V * ReadWriteState)) : gmap L (V * ReadWriteState') :=
    (λ x, (x.1, erase_count x.2)) <$> σ.
    
  Local Definition heap_count (σ: gmap L (V * ReadWriteState)) (l : L) : nat :=
      match σ !! l with
        | None => 0
        | Some (v, Writing) => 0
        | Some (v, Reading n) => n
      end.
  
  Local Definition m_count (m : gmap (L * nat) (iProp Σ)) (l : L) : nat :=
      length (filter (λ p , p.1.1 = l) (map_to_list m)).
  
  Local Definition counts_agree (σ: gmap L (V * ReadWriteState)) (m : gmap (L * nat) (iProp Σ))
    : Prop := ∀ l, heap_count σ l = m_count m l.
    
  Local Lemma length_filter_ex {A}
    (P : A → Prop) (dec: ∀ x : A, Decision (P x)) (l : list A)
    : length (filter P l) ≠ 0 → ∃ a , P a ∧ a ∈ l.
  Proof.
    induction l as [|a l IHl].
    - intros lf. contradiction.
    - intros lf. rewrite filter_cons in lf.
      destruct (decide (P a)) as [h|h].
      + exists a. rewrite elem_of_cons. intuition.
      + destruct (IHl lf) as [a2 [pa al]]. exists a2. rewrite elem_of_cons. intuition.
  Qed.
  
  Local Lemma length_filter_ex_rev {A}
    (P : A → Prop) (dec: ∀ x : A, Decision (P x)) (l : list A) (a: A)
    : P a → a ∈ l → length (filter P l) ≠ 0.
  Proof.
    intros pa a_in_l lzero.
    rewrite length_zero_iff_nil in lzero.
    assert (a ∈ filter P l) as H.
    { rewrite elem_of_list_filter. split; trivial. }
    rewrite lzero in H. rewrite elem_of_nil in H. trivial.
  Qed.
  
  Local Lemma m_count_get1 (m : gmap (L * nat) (iProp Σ)) (l : L)
      : (m_count m l ≠ 0) → ∃ i j , m !! (l, i) = Some j.
  Proof.
    unfold m_count. intros ne0.
    destruct (length_filter_ex _ _ _ ne0) as [[[l1 i1] x] [sat is_in]].
    rewrite elem_of_map_to_list in is_in.
    exists i1. exists x. simpl in sat. subst l. trivial.
  Qed.
  
  Local Lemma counts_agree_insert_writing σ m l v :
    σ !! l = Some (v, Reading 0) →
    counts_agree σ m →
    counts_agree (<[l:=(v, Writing)]> σ) m.
  Proof.
    unfold counts_agree. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count. unfold heap_count in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
    
  Local Lemma counts_agree_insert_reading0 σ m l v v' :
    σ !! l = Some (v, Writing) →
    counts_agree σ m →
    counts_agree (<[l:=(v', Reading 0)]> σ) m.
  Proof.
    unfold counts_agree. intros is_in hc l1. have hcl := hc l1.
    unfold heap_count. unfold heap_count in hcl. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_in in hcl. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma m_get_fresh_index (m : gmap (L * nat) (iProp Σ)) (l: L) :
      ∃ i , m !! (l, i) = None.
  Proof.
    assert (exists x , x ∉ ((λ a , a.1.2) <$> map_to_list m)) as [x H].
    { exists (fresh ((λ a , a.1.2) <$> map_to_list m)). apply infinite_is_fresh. }
    exists x. destruct (m !! (l, x)) as [|] eqn:mlx; trivial.
    exfalso. apply H. rewrite <- elem_of_map_to_list in mlx.
    rewrite elem_of_list_fmap. exists ((l, x), u). intuition.
  Qed.
       
  Local Lemma erase_count_map_same_update_read_count (σ: gmap L (V * ReadWriteState)) l v n m :
      σ !! l = Some (v, Reading n) →
      erase_count_map (<[l:=(v, Reading m)]> σ) = erase_count_map σ.
  Proof.
    intro is_in. unfold erase_count_map. rewrite fmap_insert. simpl.
    apply map_eq. intros l1. destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite lookup_fmap. rewrite is_in. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma m_count_insert_plus1 m l i G
    (is_fresh : m !! (l, i) = None)
    : m_count m l + 1 = m_count (<[(l, i):=G]> m) l.
  Proof.
    unfold m_count. setoid_rewrite map_to_list_insert; trivial.
      rewrite filter_cons. simpl. destruct (decide (l=l)); last by contradiction.
      unfold length. lia.
  Qed.
  
  Local Lemma m_count_insert_ne_helper m l l1 i G
    (ne : l ≠ l1)
    (mot_in: m !! (l, i) = None)
    : m_count m l1 = m_count (<[(l, i):=G]> m) l1.
  Proof.
    unfold m_count. setoid_rewrite map_to_list_insert; trivial.
      rewrite filter_cons. simpl. destruct (decide (l=l)); last by contradiction.
      destruct (decide (l = l1)); trivial; contradiction.
  Qed.
    
  Local Lemma m_count_insert_ne m l l1 i G
    (ne : l ≠ l1)
    : m_count m l1 = m_count (<[(l, i):=G]> m) l1.
  Proof.
    assert (delete (l, i) m !! (l, i) = None) as H by apply lookup_delete.
    destruct (m !! (l, i)) as [G2|] eqn:m_in.
     - have t1 := m_count_insert_ne_helper (delete (l, i) m) l l1 i G ne H.
       have t2 := m_count_insert_ne_helper (delete (l, i) m) l l1 i G2 ne H.
       rewrite insert_delete in t2; trivial.
       rewrite insert_delete_insert in t1.
       rewrite t2 in t1. trivial.
     - apply m_count_insert_ne_helper; trivial.
  Qed.
    
  Local Lemma m_count_delete_minus1 m l i G
    (is_in : m !! (l, i) = Some G)
    : m_count m l - 1 = m_count (delete (l, i) m) l.
  Proof.
    assert (delete (l, i) m !! (l, i) = None) as H by apply lookup_delete.
    have j := m_count_insert_plus1 (delete (l, i) m) l i G H.
    rewrite insert_delete in j; trivial. lia.
  Qed.
    
  Local Lemma m_count_delete_ne m l l1 i
    (ne : l ≠ l1)
    : m_count m l1 = m_count (delete (l, i) m) l1.
  Proof.
    destruct (m !! (l, i)) as [G|] eqn:de.
     - have j := m_count_insert_ne (delete (l, i) m) l l1 i G ne.
       rewrite j. rewrite insert_delete; trivial.
     - rewrite delete_notin; trivial.
  Qed.
      
  Local Lemma counts_agree_insert_read
      (σ: gmap L (V * ReadWriteState))
      (m : gmap (L * nat) (iProp Σ)) l v n i G
      (is_read : σ !! l = Some (v, Reading n))
      (is_fresh : m !! (l, i) = None)
      (ca: counts_agree σ m)
    : counts_agree (<[l:=(v, Reading (n + 1))]> σ) (<[(l, i):=G]> m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert. rewrite is_read in cal. rewrite cal.
       apply m_count_insert_plus1; trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_insert_ne; trivial.
  Qed.

  Local Lemma counts_agree_delete_read
      (σ: gmap L (V * ReadWriteState))
      (m : gmap (L * nat) (iProp Σ)) l v n i G
      (is_read : σ !! l = Some (v, Reading n))
      (is_in_m: m !! (l, i) = Some G)
      (n_ge_1: n ≥ 1)
      (ca: counts_agree σ m)
   : counts_agree (<[l:=(v, Reading (n - 1))]> σ) (delete (l, i) m).
  Proof.
    intros l1. have cal := ca l1. unfold heap_count in *.
    destruct (decide (l = l1)) as [h|h].
     - subst l1. rewrite lookup_insert. rewrite is_read in cal. rewrite cal.
       apply m_count_delete_minus1 with (G := G); trivial.
     - rewrite lookup_insert_ne; trivial. rewrite <- m_count_delete_ne; trivial.
  Qed.

  Local Lemma counts_agree_alloc
    (σ: gmap L (V * ReadWriteState))
    (m : gmap (L * nat) (iProp Σ)) l v :
    σ !! l = None →
    counts_agree σ m →
    counts_agree (<[l:=(v, Reading 0)]> σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_insert. rewrite is_none in cal. trivial.
    - rewrite lookup_insert_ne; trivial.
  Qed.
  
  Local Lemma counts_agree_delete
    (σ: gmap L (V * ReadWriteState))
    (m : gmap (L * nat) (iProp Σ)) l v :
    σ !! l = Some (v, Reading 0) →
    counts_agree σ m →
    counts_agree (delete l σ) m.
  Proof.
    intros is_none ca l1. have cal := ca l1. unfold heap_count in *.
    destruct (decide (l = l1)) as [h|h].
    - subst l1. rewrite lookup_delete. rewrite is_none in cal. trivial.
    - rewrite lookup_delete_ne; trivial.
  Qed.
  
  Local Lemma m_count_ge_1_from
      (σ: gmap L (V * ReadWriteState))
      (m : gmap (L * nat) (iProp Σ)) l i G
      (m_has : m !! (l, i) = Some G)
      : m_count m l ≥ 1.
  Proof.
    enough (m_count m l ≠ 0) by lia.
    unfold m_count. 
    apply length_filter_ex_rev with (a := (l, i, G)); trivial.
    rewrite elem_of_map_to_list. trivial.
  Qed.
   
  Local Lemma counts_agree_ge1_is_reading
      (σ: gmap L (V * ReadWriteState))
      (m : gmap (L * nat) (iProp Σ)) l i G
      (m_has : m !! (l, i) = Some G)
      (ca: counts_agree σ m)
      : ∃ n v0 , σ !! l = Some (v0, Reading n) ∧ n ≥ 1.
  Proof.
    have cal := ca l.
    have j := m_count_ge_1_from σ m l i G m_has.
    have j2 := j.
    rewrite <- cal in j. unfold heap_count in j, cal.
    destruct (σ !! l) as [[v r]|]; last by lia.
    exists (m_count m l). exists v. intuition. f_equal. f_equal.
    destruct r. - subst n. trivial. - lia.
  Qed.
End NonAtomicInternals.

(* end hide *)
  
Class na_logicG L V `{!EqDecision L, !Countable L} Σ := {
  #[local] na1_inG :: inG Σ (gmap_viewR L (agreeR (leibnizO (V * ReadWriteState')))) ;
  #[local] na2_inG :: inG Σ (gmap_viewR (L * nat) (agreeR (laterO (iPropO Σ))))
}.

Definition na_logicΣ L V `{!EqDecision L, !Countable L} : gFunctors := #[
  GFunctor (gmap_viewR L (agreeR (leibnizO (V * ReadWriteState')))) ;
  GFunctor (gmap_viewRF (L * nat) (agreeRF (laterOF idOF)))
].

Global Instance subG_na_logicΣ L V `{!EqDecision L, !Countable L} Σ : subG (na_logicΣ L V) Σ → na_logicG L V Σ.
Proof.
  solve_inG.
Qed. 

Section NonAtomicMap.

  Context `{!EqDecision L, !Countable L}.
  Context {V: Type}.
  
  Context {Σ: gFunctors}.
  Context `{!na_logicG L V Σ}.
  Context `{!invGS Σ}. 
  
  Implicit Types (γ: gname) (l: L) (v: V).
  Implicit Types (G: iProp Σ).
  Implicit Types (σ: gmap L (V * ReadWriteState)).
  
  (* begin hide *)
  Local Definition γh (γ: gname) : gname := match prod_decode_fst γ with Some x => x | _ => γ end.
  Local Definition γi (γ: gname) : gname := match prod_decode_snd γ with Some x => x | _ => γ end.
  
  Local Definition points_to_def (γ: gname) (l: L) (v: V) : iProp Σ :=
      own (γh γ) (gmap_view_frag (V:=agreeR $ leibnizO (V * ReadWriteState')) l (DfracOwn 1) (to_agree (v, Reading'))).
  Local Definition points_to_aux : seal (@points_to_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition points_to γ l v : iProp Σ. exact (points_to_aux.(unseal) γ l v). Defined.
  (* begin hide *)
  Local Definition points_to_unseal :
      @points_to = @points_to_def := points_to_aux.(seal_eq).
      
  (* end hide *)
  Notation "l ↦[ γ ] v" := (points_to γ l v)
    (at level 20, format "l  ↦[ γ ]  v") : bi_scope.
    
  (* begin hide *)
      
  Local Definition points_to_w_intermediate_def (γ: gname) (l: L) (v: V) : iProp Σ :=
      own (γh γ) (gmap_view_frag (V:=agreeR $ leibnizO (V * ReadWriteState')) l (DfracOwn 1) (to_agree (v, Writing'))).
      
  Local Definition points_to_r_intermediate_def (γ: gname) (l: L) (v: V) (G: iProp Σ) : iProp Σ :=
    (∃ i, own (γi γ) (gmap_view_frag (l, i) (DfracOwn 1) (to_agree (Next G)))) ∗ (G &&{⊤}&&> (l ↦[γ] v)).
    
  Local Definition non_atomic_map_def (γ: gname) (σ: gmap L (V * ReadWriteState)) : iProp Σ
    := ∃ (m : gmap (L * nat) (iProp Σ)),
      own (γh γ) (gmap_view_auth (V:=agreeR $ leibnizO (V * ReadWriteState')) (DfracOwn 1) (to_agree <$> (erase_count_map σ)))
        ∗ own (γi γ) (gmap_view_auth (DfracOwn 1) (to_agree <$> (Next <$> m)))
        ∗ ⌜ counts_agree σ m ⌝
        ∗ [∗ map] k ↦ G ∈ m , G ∗ ∃ v, (G &&{⊤}&&> (k.1) ↦[γ] v).
      
  Local Definition points_to_w_intermediate_aux : seal (@points_to_w_intermediate_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition points_to_w_intermediate γ l v : iProp Σ. exact (points_to_w_intermediate_aux.(unseal) γ l v). Defined.
  (* begin hide *)
  Local Definition points_to_w_intermediate_unseal :
      @points_to_w_intermediate = @points_to_w_intermediate_def := points_to_w_intermediate_aux.(seal_eq).
      
  Local Definition points_to_r_intermediate_aux : seal (@points_to_r_intermediate_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition points_to_r_intermediate γ l v G : iProp Σ. exact (points_to_r_intermediate_aux.(unseal) γ l v G). Defined.
  (* begin hide *)
  Local Definition points_to_r_intermediate_unseal :
      @points_to_r_intermediate = @points_to_r_intermediate_def := points_to_r_intermediate_aux.(seal_eq).
  
          
  Local Definition non_atomic_map_aux : seal (@non_atomic_map_def). Proof. by eexists. Qed.
  (* end hide *)
  Definition non_atomic_map γ σ : iProp Σ. exact (non_atomic_map_aux.(unseal) γ σ). Defined.
  (* begin hide *)
  Local Definition non_atomic_map_unseal :
      @non_atomic_map = @non_atomic_map_def := non_atomic_map_aux.(seal_eq).
  
  Local Ltac unseal := rewrite
    ?non_atomic_map_unseal /non_atomic_map_def
    ?points_to_unseal /points_to_def
    ?points_to_r_intermediate_unseal /points_to_r_intermediate_def
    ?points_to_w_intermediate_unseal /points_to_w_intermediate_def.
    
  (* end hide *)
    
  Global Instance points_to_timeless γ l v : Timeless (l ↦[γ] v).
  Proof. unseal. apply _. Qed.
        
  Lemma non_atomic_map_alloc_empty
    : ⊢ |==> ∃ γ, non_atomic_map γ ∅.
  Proof.
    unseal. iIntros.
    iMod (@own_alloc Σ _ na1_inG
      (gmap_view_auth (V:=agreeR (leibnizO (V * ReadWriteState'))) (DfracOwn 1) ∅))
      as (γh0) "H". { apply gmap_view_auth_valid. }
    iMod (@own_alloc Σ _ na2_inG (gmap_view_auth (DfracOwn 1) ∅))
      as (γi0) "H2". { apply gmap_view_auth_valid. }
    iModIntro. iExists (prod_encode γh0 γi0). unfold non_atomic_map.
      unfold γh. unfold γi. rewrite prod_decode_encode_fst. rewrite prod_decode_encode_snd.
    iExists ∅. iFrame. iSplit.
    { iPureIntro. unfold counts_agree, heap_count, m_count. intros l.
      rewrite lookup_empty. trivial. }
    done.
  Qed.
        
  (* begin hide *)
  Local Lemma points_to_heap_agree' γ l v σ :
    (l ↦[γ] v) ∗ own (γh γ) (gmap_view_auth (V:=agreeR $ leibnizO (V * ReadWriteState')) (DfracOwn 1) (to_agree <$> erase_count_map σ)) ⊢ ⌜ ∃ n, σ !! l = Some (v, Reading n) ⌝.
  Proof.
    unseal. iIntros "[pt oh]".
    iCombine "oh pt" gives
      %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    rewrite to_agree_included_L in Hincl. 
    unfold erase_count_map in Hv'. rewrite lookup_fmap in Hv'.
    destruct (σ !! l).
    - unfold "<$>", option_fmap, option_map in Hv'.
      destruct p as [a [n|]].
      + exists n. f_equal.  f_equal. rewrite <- Hincl in Hv'. inversion Hv'. trivial.
      + rewrite <- Hincl in Hv'. inversion Hv'.
    - inversion Hv'.
  Qed.
  (* end hide *)
  
  Lemma points_to_heap_agree γ l v σ :
    (l ↦[γ] v) ∗ non_atomic_map γ σ ⊢ ⌜ ∃ n, σ !! l = Some (v, Reading n) ⌝.
  Proof.
    unseal. iIntros "[pt na]". iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    iApply points_to_heap_agree'. unseal. iFrame.
  Qed.
  
  Lemma points_to_heap_agree_w γ l v σ :
    points_to_w_intermediate γ l v ∗ non_atomic_map γ σ ⊢ ⌜ σ !! l = Some (v, Writing) ⌝.
  Proof.
    unseal. iIntros "[pt na]". iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    iCombine "oh pt" gives
      %(av' & _ & _ & Hav' & _ & Hincl)%gmap_view_both_dfrac_valid_discrete_total.
    
    iPureIntro.
    apply lookup_fmap_Some in Hav' as [v' [<- Hv']].
    rewrite to_agree_included_L in Hincl. 
    unfold erase_count_map in Hv'. rewrite lookup_fmap in Hv'.
    destruct (σ !! l).
    - unfold "<$>", option_fmap, option_map in Hv'.
      destruct p as [a [n|]].
      + rewrite <- Hincl in Hv'. inversion Hv'.
      + f_equal. f_equal. rewrite <- Hincl in Hv'. inversion Hv'. trivial.
    - inversion Hv'.
  Qed.

  Lemma points_to_heap_reading0 γ l v σ :
    ⊢ (l ↦[γ] v) ∗ non_atomic_map γ σ ={⊤}=∗
      (l ↦[γ] v) ∗ non_atomic_map γ σ ∗ ⌜ σ !! l = Some (v, Reading 0) ⌝.
  Proof.
    unseal. iIntros "[pt na]".
    
    iDestruct (points_to_heap_agree with "[pt na]") as "%is_read".
      { unseal. iFrame "pt".  iFrame "na". }
    destruct is_read as [n is_read].
    have h : Decision (n = 0) by solve_decision. destruct h as [h|h]; trivial.
    { iModIntro. iFrame. iPureIntro. subst n. trivial. }
    
    iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    
    have ca_l := ca l. unfold heap_count in ca_l. rewrite is_read in ca_l.
    rewrite ca_l in h.
    have ij := m_count_get1 m l h.
    destruct ij as [i [G mli]].
    iDestruct (big_sepM_delete with "big") as "[[g gu] _]". { apply mli. }
    iDestruct "gu" as (v0) "gu".
    leaf_open "gu" with "g" as "[pt2 back]". { set_solver. }
    
    iCombine "pt pt2" as "pt". simpl.
    iDestruct (own_valid with "pt") as %val.
    exfalso.
    rewrite gmap_view_frag_valid in val. destruct val as [val _].
    auto.
  Qed.
  
  Lemma na_write_begin γ l v σ :
    ⊢ (l ↦[γ] v) ∗ non_atomic_map γ σ ={⊤}=∗
        ⌜ σ !! l = Some (v, Reading 0) ⌝
        ∗ points_to_w_intermediate γ l v
        ∗ non_atomic_map γ (<[ l := (v, Writing) ]> σ).
  Proof.
    unseal. iIntros "[pt na]".
    iMod (points_to_heap_reading0 with "[pt na]") as "[pt [na %is_read]]".
      { unseal. iFrame "pt".  iFrame "na". }
    unseal. iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    iCombine "oh pt" as "heap".
    iMod (@own_update Σ _ na1_inG (γh γ) _ ((
      gmap_view_auth (V := agreeR (leibnizO (V * ReadWriteState')))
        (DfracOwn 1) (to_agree <$> erase_count_map (<[ l := (v, Writing) ]> σ))
      ⋅ gmap_view_frag (V := agreeR (leibnizO (V * ReadWriteState')))
        l (DfracOwn 1) (to_agree (v, Writing'))
    )) with "heap") as "[oh pt]".
    { 
      unfold erase_count_map. rewrite fmap_insert. rewrite fmap_insert.
      apply gmap_view_replace. done.
    }
    iModIntro. iFrame.
    iPureIntro. split; trivial.
    apply counts_agree_insert_writing; trivial.
  Qed.
    
  Lemma na_write_finish γ l v v' σ :
    ⊢ points_to_w_intermediate γ l v ∗ non_atomic_map γ σ ={⊤}=∗
        ⌜ σ !! l = Some (v, Writing) ⌝
        ∗ l ↦[γ] v'
        ∗ non_atomic_map γ (<[ l := (v', Reading 0) ]> σ).
  Proof.
    iIntros "[pt na]".
    iDestruct (points_to_heap_agree_w with "[pt na]") as "%is_write".
      { iFrame "pt".  iFrame "na". }
    unseal.
    iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    iCombine "oh pt" as "heap".
    iMod (@own_update Σ _ na1_inG (γh γ) _ ((
      gmap_view_auth (V := agreeR (leibnizO (V * ReadWriteState')))
        (DfracOwn 1) (to_agree <$> erase_count_map (<[ l := (v', Reading 0) ]> σ))
      ⋅ gmap_view_frag (V := agreeR (leibnizO (V * ReadWriteState')))
        l (DfracOwn 1) (to_agree (v', Reading'))
    )) with "heap") as "[oh pt]".
    { 
      unfold erase_count_map. rewrite fmap_insert. rewrite fmap_insert.
      apply gmap_view_replace. done.
    }
    iModIntro. iFrame.
    iPureIntro. split; trivial.
    apply (counts_agree_insert_reading0 _ _ _ v); trivial.
  Qed.
   
  Lemma na_read_begin γ l v σ G :
    ⊢ (G &&{⊤}&&> (l ↦[γ] v)) ∗ G ∗ non_atomic_map γ σ ={⊤}=∗
        ∃ n , ⌜ σ !! l = Some (v, Reading n) ⌝
        ∗ points_to_r_intermediate γ l v G
        ∗ non_atomic_map γ (<[ l := (v, Reading (n + 1)) ]> σ).
  Proof.
    iIntros "[#guard [g na]]".
    leaf_open "guard" with "g" as "[pt back]". { set_solver. }
    iDestruct (points_to_heap_agree with "[pt na]") as "%is_read".
      { iFrame "pt". iFrame "na". }
    unseal.
    destruct is_read as [n is_read]. iExists n.
    iMod ("back" with "pt") as "G".
    iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    destruct (m_get_fresh_index m l) as [i is_fresh].
    iMod (@own_update Σ _ na2_inG (γi γ) _ ((
      gmap_view_auth (V := (agreeR (laterO (iPropO Σ))))
        (DfracOwn 1) (to_agree <$> (Next <$> (<[ (l,i) := G ]> m)))
     ⋅ gmap_view_frag (V := (agreeR (laterO (iPropO Σ))))
        (l, i) (DfracOwn 1) (to_agree (Next G))
    )) with "oi") as "[oi ptr]".
    {
      rewrite fmap_insert. rewrite fmap_insert.
      apply gmap_view_alloc.
      { rewrite lookup_fmap. rewrite lookup_fmap. rewrite is_fresh. trivial. }
      { done. }
      { done. }
    }
    iModIntro. unfold non_atomic_map.
    iFrame "oi".
    iSplitR. { iPureIntro. trivial. }
    unfold points_to_r_intermediate. iFrame "ptr".
    rewrite (erase_count_map_same_update_read_count _ _ _ _ _ is_read). iFrame "oh".
    unseal. iFrame "guard".
    iSplitR. { iPureIntro. apply counts_agree_insert_read; trivial. }
    rewrite big_sepM_insert; trivial.
    iFrame. iExists v. iFrame "guard".
  Qed.
  
  Lemma na_read_end γ l v σ G :
    points_to_r_intermediate γ l v G ∗ non_atomic_map γ σ ⊢ ▷ |={⊤}=>
        ∃ n , ⌜ σ !! l = Some (v, Reading n) ∧ n ≥ 1 ⌝
        ∗ G
        ∗ non_atomic_map γ (<[ l := (v, Reading (n - 1)) ]> σ).
  Proof.
    unseal. iIntros "[[ptr #guard] na]".
    iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    iDestruct "ptr" as (i) "ptr".
    iAssert (∃ n G' v0, ⌜ σ !! l = Some (v0, Reading n) ∧ n ≥ 1 ∧ m !! (l, i) = Some G'⌝
        ∗ Next G ≡ Next G')%I as (n G' v0) "[%p #equ]".
    {
      iCombine "oi ptr" as "oi".
      iDestruct (own_valid with "oi") as "oi_val".
      rewrite gmap_view_both_validI_total.
      iDestruct "oi_val" as (v') "[%_valfrac1 [%_valfrac2 [%sm [val1 val2]]]]".
      rewrite lookup_fmap in sm. rewrite lookup_fmap in sm.
      
      destruct ((@lookup (prod L nat) (uPredO (iResUR Σ))
                  (@gmap (prod L nat) (@prod_eq_dec L EqDecision0 nat Nat.eq_dec)
                     (@prod_countable L EqDecision0 Countable0 nat Nat.eq_dec nat_countable)
                     (uPredO (iResUR Σ)))
                  (@gmap_lookup (prod L nat) (@prod_eq_dec L EqDecision0 nat Nat.eq_dec)
                     (@prod_countable L EqDecision0 Countable0 nat Nat.eq_dec nat_countable)
                     (uPredO (iResUR Σ))) (@pair L nat l i) m))
              as [G'|] eqn:dest_eqn; rewrite dest_eqn in sm; last by inversion sm.
     rewrite dest_eqn.
     simpl in sm. inversion sm. subst v'. 
     rewrite to_agree_includedI.
     destruct (counts_agree_ge1_is_reading σ m l i G' dest_eqn) as [n [v0 is_read]]; trivial.
     iExists n. iExists G'. iExists v0.
     iFrame "val2". { iPureIntro. intuition. }
   }
   iExists n.
   destruct p as [in_sig [n_ge1 in_m]].
   iDestruct (big_sepM_delete with "big") as "[[g gu] big]". { apply in_m. }
   iDestruct "gu" as (v1) "gu".
   rewrite later_equivI. iNext. iRewrite -"equ" in "g".
   
   leaf_open "guard" with "g" as "[pt back]". { set_solver. }
   iDestruct (points_to_heap_agree' γ l v σ with "[pt oh]") as "%in_sig2". { iFrame. }
   iMod ("back" with "pt") as "G".
   
   iCombine "oi ptr" as "oi".
   iMod (@own_update Σ _ na2_inG (γi γ) _ ((
      gmap_view_auth (V := (agreeR (laterO (iPropO Σ))))
        (DfracOwn 1) (to_agree <$> (Next <$> (delete (l, i) m)))
    )) with "oi") as "oi".
    {
      rewrite fmap_delete. rewrite fmap_delete.
      apply gmap_view_delete.
    }
    
    assert (v = v0) as veq. {
      destruct in_sig2 as [n0 in_sig2]. rewrite in_sig in in_sig2.
        inversion in_sig2. trivial.
    }
    subst v0.
    
    iModIntro. iFrame "G". iSplitR. { iPureIntro. intuition. }
    
    unfold non_atomic_map. iFrame "oi".
    
    rewrite (erase_count_map_same_update_read_count _ _ _ _ _ in_sig). iFrame "oh".
    iFrame "big".
    iPureIntro. apply (counts_agree_delete_read _ _ _ _ _ _ G'); trivial.
  Qed.

  Lemma atomic_write γ l v v' σ :
    ⊢ (l ↦[γ] v) ∗ non_atomic_map γ σ ={⊤}=∗
        ⌜ σ !! l = Some (v, Reading 0) ⌝
        ∗ (l ↦[γ] v')
        ∗ non_atomic_map γ (<[ l := (v', Reading 0) ]> σ).
  Proof.
    iIntros "a".
    iMod (na_write_begin with "a") as "[%sig [pt heap]]".
    iMod (na_write_finish with "[pt heap]") as "[%sig2 [pt heap]]".
        { iFrame "pt". iFrame "heap". }
    iModIntro. iFrame "pt". rewrite insert_insert. iFrame "heap".
    iPureIntro. apply sig.
  Qed.
    
  Lemma atomic_read γ l v σ G :
    (G &&{⊤}&&> (l ↦[γ] v)) ∗ G ∗ non_atomic_map γ σ ={⊤}=∗
        ∃ n , ⌜ σ !! l = Some (v, Reading n) ⌝
        ∗ G ∗ non_atomic_map γ σ.
  Proof.
    iIntros "[#guard [g na]]".
    leaf_open "guard" with "g" as "[pt back]". { set_solver. }
    iDestruct (points_to_heap_agree γ l v σ with "[pt na]") as (n) "%sig". { iFrame. }
    iMod ("back" with "pt") as "G".
    iModIntro. iExists n. iFrame. iPureIntro. apply sig.
  Qed.
  
  Lemma non_atomic_map_insert γ l v σ :
    (σ !! l = None) →
    non_atomic_map γ σ ={⊤}=∗ (l ↦[γ] v) ∗ non_atomic_map γ (<[ l := (v, Reading 0) ]> σ).
  Proof.
    unseal. intros not_in. iIntros "na".
    iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    iMod (@own_update Σ _ na1_inG (γh γ) _ ((
      gmap_view_auth (V := agreeR (leibnizO (V * ReadWriteState')))
        (DfracOwn 1) (to_agree <$> erase_count_map (<[ l := (v, Reading 0) ]> σ))
      ⋅ gmap_view_frag (V := agreeR (leibnizO (V * ReadWriteState')))
        l (DfracOwn 1) (to_agree (v, Reading'))
    )) with "oh") as "[oh pt]".
    { 
      unfold erase_count_map. rewrite fmap_insert. rewrite fmap_insert.
      apply gmap_view_alloc.
       - rewrite lookup_fmap. rewrite lookup_fmap. rewrite not_in. trivial.
       - done.
       - done.
    }
    iModIntro. iFrame "pt". unfold non_atomic_map. iFrame.
    iPureIntro. apply (counts_agree_alloc σ m l v not_in ca).
  Qed.
  
  Lemma non_atomic_map_delete γ l v σ :
    (l ↦[γ] v) ∗ non_atomic_map γ σ ={⊤}=∗
      ⌜ σ !! l = Some (v, Reading 0) ⌝ ∗ non_atomic_map γ (delete l σ).
  Proof.
    iIntros "a".
    iMod (points_to_heap_reading0 with "a") as "[pt [na %is_in]]".
    unseal. iDestruct "na" as (m) "[oh [oi [%ca big]]]".
    iCombine "oh pt" as "oh".
    iMod (@own_update Σ _ na1_inG (γh γ) _ ((
      gmap_view_auth (V := agreeR (leibnizO (V * ReadWriteState')))
        (DfracOwn 1) (to_agree <$> erase_count_map (delete l σ))
    )) with "oh") as "oh".
    { 
      unfold erase_count_map. rewrite fmap_delete. rewrite fmap_delete.
      apply (gmap_view_delete (V := agreeR (leibnizO (V * ReadWriteState')))).
    }
    iModIntro. unfold non_atomic_map. iFrame. iSplitL. { iPureIntro. trivial. }
    iPureIntro. apply (counts_agree_delete σ m l v); trivial.
  Qed.
End NonAtomicMap.
