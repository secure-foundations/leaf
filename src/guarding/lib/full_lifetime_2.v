Require Import guarding.guard.
Require Import guarding.own_and.
Require Import guarding.tactics.
Require Import guarding.lib.boxes.
Require Import guarding.lib.lifetime_internals_ra.

Require Import stdpp.base.
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

Section FullBorrows.
  (* (A, B) means A must end before B
      A alive ==> B alive
      B dead ==> A dead
  *)
  Definition outlives_set := gset (gset nat * nat).

  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.
  Context `{!boxG Σ}.
  
  Context {γ: gname}.
  
  Definition Nllft       : namespace := nroot .@ "leaf_lifetime_logic".
  Local Definition Nbox  : namespace := Nllft .@ "box".
  Local Definition Nmain : namespace := Nllft .@ "main".
  
  Definition Nllft_full  : namespace := nroot .@ "leaf_lifetime_logic_full".
  
  Definition Outlives (outlives: outlives_set) : iProp Σ. Admitted.
  Lemma outlives_agree o1 o2 :
      Outlives o1 ∗ Outlives o2 ⊢ ⌜o1 = o2⌝. Admitted.
  Lemma outlives_update o1 o2 o :
      Outlives o1 ∗ Outlives o2 ⊢ Outlives o ∗ Outlives o. Admitted.
  Local Instance timeless_outlives o : Timeless (Outlives o). Admitted.
      
  Definition Delayed (opt_k: option nat) : iProp Σ. Admitted.
  Lemma delayed_agree o1 o2 :
      Delayed o1 ∗ Delayed o2 ⊢ ⌜o1 = o2⌝. Admitted.
  Lemma delayed_update o1 o2 o :
      Delayed o1 ∗ Delayed o2 ⊢ Delayed o ∗ Delayed o. Admitted.
  
  Definition boxmap
      (alive dead : gset nat) (m: gmap_bor_state)
        : gmap slice_name bool :=
      (λ bs , match bs with
        | Borrow al de => bool_decide (al ⊆ alive ∧ ¬(de ## dead))
        | Unborrow _ _ _ => false
      end) <$> m.
  
  Definition outlives_consistent (dead: gset nat) (outlives : outlives_set)
    := ∀ (o: gset nat * nat) , o ∈ outlives → (o.2 ∈ dead) → ¬(o.1 ## dead).
  
  Definition map_wf
      (alive dead blocked : gset nat) (outlives : outlives_set) (m: gmap_bor_state)
    :=
    alive ## dead
    ∧ blocked ⊆ alive
    ∧ default_dead ∈ dead
    ∧ (∀ sn bs , m !! sn = Some bs → match bs with
      | Borrow al de => (al ∪ de) ⊆ (alive ∪ dead)
      | Unborrow bl al de => bl ⊆ blocked ∧ ¬(de ## dead)
          ∧ (∀ a , a ∈ al → (bl, a) ∈ outlives)
          ∧ (al ∪ de) ⊆ (alive ∪ dead)
    end)
    ∧ (∀ sn1 bs1 sn2 bs2 , sn1 ≠ sn2 → m !! sn1 = Some bs1 → m !! sn2 = Some bs2 →
        match (bs1, bs2) with
        | (Unborrow bl1 _ _, Unborrow bl2 _ _) => bl1 ## bl2
        | _ => True
        end)
    .
  
  Lemma map_wf_insert_unborrow alive dead blocked bl al de outlives mbs sn :
    (al ⊆ alive) →
    (bl ⊆ alive) →
    ¬(de ## dead) →
    (de ⊆ (alive ∪ dead)) →
    (bl ## blocked) →
    (∀ a : nat, a ∈ al → (bl, a) ∈ outlives) →
    map_wf alive dead blocked outlives mbs →
    map_wf alive dead (blocked ∪ bl) outlives (<[sn:=Unborrow bl al de]> mbs).
  Proof.
    unfold map_wf.
    intros Hal Hblalive Hde Hdewf Hbl Ho [Hdisj [Hblal [Hdd [Hf1 Hf2]]]]. 
      split; trivial.
      split. { set_solver. }
      split; trivial.
      split.
      - intros sn' bs'. destruct (decide (sn = sn')).
        + intros Hmbssn'. subst sn'. rewrite lookup_insert in Hmbssn'. inversion Hmbssn'.
          split. { set_solver. } split; trivial. split; trivial. set_solver.
        + intros Hmbssn'. rewrite lookup_insert_ne in Hmbssn'; trivial.
          have Hfa := Hf1 sn' bs' Hmbssn'. destruct bs'; trivial. set_solver.
      - intros sn1 bs1 sn2 bs2. destruct (decide (sn = sn1)).
        + subst sn1. intros Hne2 Hmbssn1 Hmbssn2.
          rewrite lookup_insert in Hmbssn1. rewrite lookup_insert_ne in Hmbssn2; trivial.
          inversion Hmbssn1. destruct bs2 as [|bl2 al2 de2]; trivial.
          subst bs1. have Hfa := Hf1 sn2 (Unborrow bl2 al2 de2) Hmbssn2. set_solver.
        + destruct (decide (sn = sn2)).
        * subst sn2. intros Hne1 Hmbssn1 Hmbssn2.
          rewrite lookup_insert in Hmbssn2. rewrite lookup_insert_ne in Hmbssn1; trivial.
          inversion Hmbssn2. destruct bs1 as [|bl1 al1 de1]; trivial.
          subst bs2. have Hfa := Hf1 sn1 (Unborrow bl1 al1 de1) Hmbssn1. set_solver.
        * intros Hne Hmbssn1 Hmbssn2.
          destruct bs1 as [|bl1 al1 de1]; destruct bs2 as [|bl2 al2 de2]; trivial.
          rewrite lookup_insert_ne in Hmbssn1; trivial.
          rewrite lookup_insert_ne in Hmbssn2; trivial.
          have Hfa := Hf2 sn1 (Unborrow bl1 al1 de1) sn2 (Unborrow bl2 al2 de2).
          intuition.
  Qed.
  
  Lemma map_wf_delete_unborrow alive dead blocked bl al de outlives mbs sn :
    (al ⊆ alive) →
    (bl ⊆ blocked) →
    (mbs !! sn = Some (Unborrow bl al de)) →
    map_wf alive dead blocked outlives mbs →
    map_wf alive dead (blocked ∖ bl) outlives (delete sn mbs).
  Proof.
    unfold map_wf.
    intros Hal Hbl Hmbssn [Hdisj [Hblal [Hdd [Hf1 Hf2]]]]. 
      split; trivial.
      split. { set_solver. }
      split; trivial.
      split.
      - intros sn' bs' Hdel. destruct (decide (sn = sn')).
        + subst sn'. rewrite lookup_delete in Hdel. discriminate.
        + rewrite lookup_delete_ne in Hdel; trivial.
          have Hfa := Hf1 sn' bs'. destruct bs'; intuition. set_solver.
      - intros sn1 bs1 sn2 bs2 Hne Hdel1 Hdel2. 
        destruct (decide (sn = sn1)). { subst sn1. rewrite lookup_delete in Hdel1. discriminate. }
        destruct (decide (sn = sn2)). { subst sn2. rewrite lookup_delete in Hdel2. discriminate. }
        rewrite lookup_delete_ne in Hdel1; trivial.
        rewrite lookup_delete_ne in Hdel2; trivial.
        apply (Hf2 sn1 bs1 sn2 bs2); trivial.
  Qed.
    
  Lemma map_wf_insert
      (alive dead blocked : gset nat) (outlives : outlives_set) (m: gmap_bor_state) sn al de :
  map_wf alive dead blocked outlives m →
  (al ∪ de) ⊆ (alive ∪ dead) →
  map_wf alive dead blocked outlives (<[sn:=Borrow al de]> m).
  Admitted.
  
  Lemma map_wf_delete
      (alive dead blocked : gset nat) (outlives : outlives_set) (m: gmap_bor_state) sn :
  map_wf alive dead blocked outlives m →
  map_wf alive dead blocked outlives (delete sn m).
  Admitted.
   
  Lemma map_wf_new_lt alive dead blocked outlives mbs k :
    (k ∉ alive ∪ dead) →
    map_wf alive dead blocked outlives mbs →
    map_wf (alive ∪ {[k]}) dead blocked outlives mbs.
  Admitted.
  
  Lemma map_wf_preserved_on_kill alive dead blocked outlives k mbs :
    (k ∉ blocked) →
    map_wf alive dead blocked outlives mbs →
    map_wf (alive ∖ {[k]}) (dead ∪ {[k]}) blocked outlives mbs.
  Proof.
    unfold map_wf. intros H [Ha [Hb [Hc [Hforall Hforall2]]]].
    split. { set_solver. } split. { set_solver. } split. { set_solver. }
    split. {
    intros sn bs Hso. have Hdx := Hforall sn bs Hso. destruct bs as [al de|bl al de].
    - intro k'. destruct (decide (k = k')); set_solver.
    - destruct Hdx as [He [Hf [Hg Hi]]]. split; trivial. split. { set_solver. }
      split; trivial.
      intro k'. destruct (decide (k = k')); set_solver.
    }
  Admitted.

  Definition llft_fb_vs (alive dead : gset nat) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ.
      Admitted.
      
  Definition borrow_sum (f: BorState → bool) (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ. Admitted.
  
  (*Lemma borrow_sum_is_empty f mbs mprops :
      (∀ i j , mbs !! i = Some j → f j = false) →
      ⊢ borrow_sum f mbs mprops. Admitted.*)
 
  Definition invalidated (alive dead : gset nat) (k: nat) (bs: BorState) := match bs with
    | Borrow al de => bool_decide (al ⊆ alive ∧ ¬(de ## dead) ∧ k ∈ al)
    | Unborrow _ al de => bool_decide (al ⊆ alive ∧ ¬(de ## dead) ∧ k ∈ al)
  end.
  
  Definition revalidated (alive dead : gset nat) (k: nat) (bs: BorState) := match bs with
    | Borrow al de => bool_decide (al ⊆ (alive ∖ {[k]}) ∧ (de ## dead) ∧ k ∈ de)
    | Unborrow _ _ _ => false
  end.
  
  Definition full_borrows_invalidated_via
    (alive dead : gset nat) (k: nat) (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
      borrow_sum (invalidated alive dead k) m mprops.
    
  Definition full_borrows_revalidated_via
    (alive dead : gset nat) (k: nat) (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
      borrow_sum (revalidated alive dead k) m mprops.
  
  Lemma borrow_sum_empty f m mprops
      : (∀ i x , m !! i = Some x → f x = false) →
      ⊢ borrow_sum f m mprops. Admitted.
      
  Lemma borrow_sum_equiv f f' m mprops
      : (∀ i x , m !! i = Some x → f x = true → f' x = true) →
      borrow_sum f' m mprops ⊢ borrow_sum f m mprops. Admitted.
    
  Lemma llft_fb_vs_def (alive dead : gset nat) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) :
    llft_fb_vs alive dead outlives m mprops ⊣⊢
    ∀ (k: nat),
      ⌜k ∈ alive ∧ outlives_consistent (dead ∪ {[k]}) outlives⌝ ∗ Dead γ k ∗
        ▷ (full_borrows_invalidated_via alive dead k m mprops)
      ={∅}=∗ ▷ (full_borrows_revalidated_via alive dead k m mprops)
           ∗ llft_fb_vs (alive ∖ {[k]}) (dead ∪ {[k]}) outlives m mprops.
  Admitted.
  
  Lemma set_ind_strong `{FinSet A C} `{!LeibnizEquiv C} (P : C → Prop) :
  (∀ X , (∀ x , x ∈ X → P (X ∖ {[ x ]})) → P X) → ∀ X, P X.
  Proof. Admitted.
  
    Lemma full_borrows_invalidated_via_insert alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      invalidated alive dead k bs = true →
      ▷ (full_borrows_invalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops))
      ⊢ ▷ (P ∗ full_borrows_invalidated_via alive dead k mbs mprops). Admitted.
      
  Lemma full_borrows_invalidated_via_insert_false alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      ▷ (full_borrows_invalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops))
      ⊢ ▷ (full_borrows_invalidated_via alive dead k mbs mprops).
   Admitted.
      
  Lemma full_borrows_invalidated_via_delete alive dead k sn mbs mprops bs P :
      (mbs !! sn = Some bs) →
      ▷ (mprops !! sn ≡ Some P)
        ∗ ▷ (full_borrows_invalidated_via alive dead k (delete sn mbs) (delete sn mprops))
        ∗ ▷ P
      ⊢ 
      full_borrows_invalidated_via alive dead k mbs mprops. Admitted.
      
  Lemma full_borrows_invalidated_via_delete_false alive dead k sn mbs mprops bs :
      (mbs !! sn = Some bs) →
      invalidated alive dead k bs = false →
      ▷ (full_borrows_invalidated_via alive dead k (delete sn mbs) (delete sn mprops))
      ⊢ 
      full_borrows_invalidated_via alive dead k mbs mprops. Admitted.
      
  Lemma full_borrows_revalidated_via_insert alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      ▷ (full_borrows_revalidated_via alive dead k mbs mprops)
      ∗ ▷ P
      ⊢
      ▷ (full_borrows_revalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops)).
 Admitted.
      
  Lemma full_borrows_revalidated_via_insert_false alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      revalidated alive dead k bs = false →
      ▷ (full_borrows_revalidated_via alive dead k mbs mprops)
      ⊢
      ▷ (full_borrows_revalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops)).
 Admitted.
 
 Lemma full_borrows_revalidated_via_delete alive dead k sn mbs mprops bs P :
      mbs !! sn = Some bs →
      revalidated alive dead k bs = true →
        ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢
        ▷ (full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops))
      ∗ ▷ P.
 Admitted.
 
 Lemma full_borrows_revalidated_via_delete_false alive dead k sn mbs mprops bs :
      mbs !! sn = Some bs →
        ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢
        ▷ (full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops)).
 Admitted.
 
 Lemma full_borrows_delete_insert_same alive dead k sn mbs mprops bs bs' P :
      (invalidated alive dead k bs = true → invalidated alive dead k bs' = true) →
      mbs !! sn = Some bs →
        ▷ (full_borrows_invalidated_via alive dead k 
            (<[sn := bs']> (delete sn mbs)) (<[sn := P]> (delete sn mprops)))
      ∗ ▷ (mprops !! sn ≡ Some P)
      ⊢ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
    intros Himpl Hmbssn.
    iIntros "[inval #Heq]".
    destruct (invalidated alive dead k bs) eqn:Hcmp.
    - iDestruct (full_borrows_invalidated_via_insert alive dead k sn (delete sn mbs) (delete sn mprops) _ P with "[inval]") as "[p inval]".
      { rewrite lookup_delete. trivial. } { apply Himpl. trivial. } { iFrame "inval". }
      iDestruct (full_borrows_invalidated_via_delete with "[inval p]") as "inval".
      { apply Hmbssn. } { iFrame "Heq". iFrame "inval". iFrame "p". } iFrame.
    - iDestruct (full_borrows_invalidated_via_insert_false alive dead k sn (delete sn mbs) (delete sn mprops) _ P with "[inval]") as "inval".
      { apply lookup_delete. } { iFrame. }
      iDestruct (full_borrows_invalidated_via_delete_false with "[inval]") as "inval".
      { apply Hmbssn. } { apply Hcmp. } { iFrame "inval". } iFrame.
  Qed.
   
  Lemma full_borrows_invalidated_preserved_in_split
    sn sn1 sn2 mbs mprops P Q alive dead k bs
    :
      (delete sn mbs !! sn1 = None) →
      (delete sn mbs !! sn2 = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn = Some bs) →
      ▷ (mprops !! sn ≡ Some (P ∗ Q)) ∗
          ▷ full_borrows_invalidated_via alive dead k
                (<[sn2:=bs]> (<[sn1:=bs]> (delete sn mbs)))
                (<[sn2:=Q]> (<[sn1:=P]> (delete sn mprops)))
      ⊢ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
    intros Hsn1 Hsn2 Hne Hmbssn. iIntros "[#Heq inval]".
    destruct (invalidated alive dead k bs) eqn:Hinvbool.
    - iDestruct (full_borrows_invalidated_via_insert with "inval") as "[q inval]".
        { rewrite lookup_insert_ne; trivial. } { trivial. }
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[p inval]".
        { trivial. } { trivial. }
      iDestruct (full_borrows_invalidated_via_delete with "[inval p q]") as "inval".
        { apply Hmbssn. } { iFrame "Heq". iFrame "inval". iFrame. }
      iFrame.
    - iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
        { rewrite lookup_insert_ne; trivial. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
        { trivial. }
      iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
        { apply Hmbssn. } { trivial. } { iFrame "inval". }
  Qed.
  
  Lemma full_borrows_revalidated_preserved_in_split
    sn sn1 sn2 mbs mprops P Q alive dead k bs
    :
      (delete sn mbs !! sn1 = None) →
      (delete sn mbs !! sn2 = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn = Some bs) →
      ▷ (mprops !! sn ≡ Some (P ∗ Q)) ∗
      ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢ ▷ full_borrows_revalidated_via alive dead k
                (<[sn2:=bs]> (<[sn1:=bs]> (delete sn mbs)))
                (<[sn2:=Q]> (<[sn1:=P]> (delete sn mprops))).
  Proof.
    intros Hsn1 Hsn2 Hne Hmbssn. iIntros "[#Heq inval]".
    destruct (revalidated alive dead k bs) eqn:Hinvbool.
    - iAssert (▷ full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops)
        ∗ ▷ (P ∗ Q))%I with "[inval]" as "[inval [P Q]]".
        { iApply full_borrows_revalidated_via_delete. { apply Hmbssn. } { trivial. } iFrame. }
      iApply full_borrows_revalidated_via_insert.
      { rewrite lookup_insert_ne; trivial. } iFrame.
      iApply full_borrows_revalidated_via_insert.
      { trivial. } iFrame.
    - iApply full_borrows_revalidated_via_insert_false.
      { rewrite lookup_insert_ne; trivial. } { trivial. }
      iApply full_borrows_revalidated_via_insert_false.
      { trivial. } { trivial. }
      iApply full_borrows_revalidated_via_delete_false.
      { apply Hmbssn. } iFrame.
  Qed.

  Lemma llfb_fb_vs_split sn sn1 sn2 (mbs : gmap_bor_state) alive dead al de outlives mprops P Q
  :
    (delete sn mbs !! sn1 = None) →
    (delete sn mbs !! sn2 = None) →
    (sn1 ≠ sn2) →
    (mbs !! sn = Some (Borrow al de)) →
    (llft_fb_vs alive dead outlives mbs mprops
        ∗ ▷ (mprops !! sn ≡ Some (P ∗ Q)))
    ⊢
      llft_fb_vs alive dead outlives
        (<[sn2:=Borrow al de]> (<[sn1:=Borrow al de]> (delete sn mbs)))
        (<[sn2:=Q]> (<[sn1:=P]> (delete sn mprops))).
  Proof.
    intros Hdel1 Hdel2 Hne Hmbssn. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead) "[Hvs #Heq]".
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def _ _ _ (<[sn2:=Borrow al de]> (<[sn1:=Borrow al de]> (delete sn mbs)))).
    iIntros (k) "[%Hin_my_alive [Dead inval]]".
    iMod ("Hvs" $! k with "[Dead inval]") as "[reval Hvs]".
    { iFrame. iSplitR. { iPureIntro. trivial. }
      iDestruct (full_borrows_invalidated_preserved_in_split sn sn1 sn2 mbs mprops P Q my_alive my_dead k (Borrow al de) Hdel1 Hdel2 Hne Hmbssn with "[inval]") as "inval". { iFrame. iFrame "Heq". }
      iFrame.
    }
    iModIntro.
    iSplitL "reval".
    { iDestruct (full_borrows_revalidated_preserved_in_split sn sn1 sn2 mbs mprops P Q my_alive my_dead k (Borrow al de) Hdel1 Hdel2 Hne Hmbssn with "[reval]") as "reval". { iFrame. iFrame "Heq". } iFrame. }
    destruct Hin_my_alive.
    iApply IH; trivial. iFrame. iFrame "#".
  Qed.
      
  Definition llft_fb_inv (alive dead blocked : gset nat) : iProp Σ :=
    ∃ (mbs: gmap_bor_state) (mprops: gmap_props Σ) Ptotal (outlives: outlives_set),
        AuthBorState γ mbs
          ∗ box Nbox (boxmap alive dead mbs) Ptotal
          ∗ llft_fb_vs alive dead outlives mbs mprops
          ∗ ⌜dom mbs = dom mprops
              ∧ map_wf alive dead blocked outlives mbs
              ∧ outlives_consistent dead outlives
             ⌝
          ∗ ([∗ map] sn ↦ Q ∈ mprops, slice Nbox sn Q)
          ∗ Outlives outlives.
          
          (*
          ∗ ([∗ set] o ∈ outlives, ([∗ set] k ∈ o.1, Alive γ k) &&{↑Nllft}&&> Dead γ o.2).
          *)
          
  Lemma llft_fb_fake (alive dead blocked al de : gset nat) Q :
    ¬(al ## dead) →
    LtState γ alive dead ⊢ |={↑Nbox}=> ∃ sn, 
    LtState γ alive dead ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn Q.
  Proof.
    intros Hnotdisj.
    iIntros "LtState".
    iDestruct (box_alloc Nbox) as "box".
    iMod (slice_insert_empty Nbox (↑Nbox) false ∅ Q (True)%I with "box") as (sn) "[H [slice box2]]".
    iMod (alloc_fake_bor_state_lts γ sn alive dead al de with "LtState") as "[LtState OwnBor]".
    { trivial. }
    iModIntro. iExists sn. iFrame.
  Qed.
  
  Lemma delete_boxmap_implies_delete_original_is_none alive dead mbs sn1 sn2
    : delete sn1 (boxmap alive dead mbs) !! sn2 = None →
      delete sn1 mbs !! sn2 = None.
  Admitted.
  
  Lemma lookup_insert_delete_boxmap_helper sn sn' sn2 alive dead mbs bs :
      <[sn:=false]> (delete sn' (boxmap alive dead mbs)) !! sn2 = None →
      <[sn:=bs]> (delete sn' mbs) !! sn2 = None. Admitted.
      
  Lemma lookup_insert_delete_boxmap_helper2 sn sn' sn2 alive dead mbs  :
      <[sn:=false]> (delete sn' (boxmap alive dead mbs)) !! sn2 = None →
      (delete sn' mbs) !! sn2 = None. Admitted.
      
  Lemma lookup_insert_boxmap_helper3 sn b alive dead mbs sn2 :
    <[sn:=b]> (boxmap alive dead mbs) !! sn2 = None →
    mbs !! sn2 = None ∧ sn ≠ sn2. Admitted.
      
  Lemma boxmap_insert_Borrow alive dead sn al de mbs
    : boxmap alive dead (<[ sn := Borrow al de ]> mbs)
      = <[ sn := bool_decide (al ⊆ alive ∧ ¬(de ## dead)) ]> (boxmap alive dead mbs).
  Admitted.
  
  Lemma boxmap_insert_Unborrow alive dead sn bl al de mbs
    : boxmap alive dead (<[ sn := Unborrow bl al de ]> mbs)
      = <[ sn := false ]> (boxmap alive dead mbs).
  Admitted.
       
  Lemma boxmap_delete alive dead sn mbs
      : boxmap alive dead (delete sn mbs)
        = delete sn (boxmap alive dead mbs). Admitted.
  
  Lemma agree_slice_with_map (mbs : gmap_bor_state) (mprops : gmap_props Σ) sn bs P :
      dom mbs = dom mprops →
      mbs !! sn = Some bs →
      slice Nbox sn P ∗ ([∗ map] sn0↦Q0 ∈ mprops, slice Nbox sn0 Q0)
        ⊢ ▷ (mprops !! sn ≡ Some P).
  Admitted.
  
  Local Instance pers_dead3 k : Persistent (Dead γ k).
    Admitted.
  
  Lemma big_sepM_insert_1 `{Countable K} {A : Type} (Φ : K → A → iProp Σ) (m : gmap K A) i x :
    (Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y)%I ⊢ ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y).
  Admitted.
            
  Lemma llft_fb_split alive dead blocked sn al de P Q :
    (▷ llft_fb_inv alive dead blocked) ∗ LtState γ alive dead
      ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn (P ∗ Q)
      ⊢ |={↑Nbox}=> ∃ sn1 sn2, (▷ llft_fb_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn1 P ∗ slice Nbox sn2 Q.
  Proof.
    iIntros "[Inv [LtState [OwnBor #slice]]]".
    destruct (decide (al ## dead)) as [Hdisj|Hnot_disj].
    2: {
      iMod (llft_fb_fake alive dead blocked al de P Hnot_disj with "LtState")
          as (sn1) "[LtState [Ob2 Slice2]]".
      iMod (llft_fb_fake alive dead blocked al de Q Hnot_disj with "LtState")
          as (sn2) "[LtState [Ob3 Slice3]]".
      iModIntro. iExists sn1. iExists sn2. iFrame.
    }
    unfold llft_fb_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices outlives]]]]]".
    iDestruct (agree_bor_state_borrow_lts γ sn mbs alive dead al de Hdisj
        with "[LtState auth OwnBor]") as (de') "[%Hmbs_sn %Hrel_de]". { iFrame. }
    
    iMod (slice_split (Nbox) (↑Nbox) true 
        (boxmap alive dead mbs)
        (Ptotal) P Q sn
        (bool_decide (al ⊆ alive ∧ ¬ de' ## dead))
        with "slice box") as (sn1 sn2) "[%Hmd1 [%Hmd2 [%Hne [#slice1 [#slice2 box]]]]]".
      { set_solver. }
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbs_sn. trivial. }
    
    assert (delete sn mbs !! sn1 = None) as Hdel1
      by ( apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hmd1) ).
    assert (delete sn mbs !! sn2 = None) as Hdel2
      by ( apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hmd2) ).
      
    iMod (delete_bor_state_borrow_lts γ sn mbs alive dead al de' Hdisj with 
        "[LtState auth OwnBor]") as "[LtState auth]". { iFrame. }
    iMod (alloc_bor_state2 γ sn1 (delete sn mbs) alive dead al de de' with "[LtState auth]") as "[LtState [auth own1]]"; trivial. { iFrame. }
    iMod (alloc_bor_state2 γ sn2 (<[sn1:=Borrow al de']> (delete sn mbs)) alive dead al de de' with "[LtState auth]") as "[LtState [auth own2]]".
      { rewrite lookup_insert_ne; trivial. } { trivial. } { iFrame. }
    
    iDestruct (bi.later_mono _ _ (llfb_fb_vs_split sn sn1 sn2 mbs alive dead al de' outlives mprops P Q Hdel1 Hdel2 Hne Hmbs_sn) with "[vs]") as "vs".
    { iFrame. iNext.
      destruct pures as [Hdom Hrest].
      iApply (agree_slice_with_map mbs mprops sn _ (P ∗ Q)%I Hdom Hmbs_sn). iFrame "#".
    }
      
    iModIntro. iExists sn1, sn2.
    iFrame "auth". iFrame "own1". iFrame "own2".
    iFrame "LtState". iFrame "slice1". iFrame "slice2".
    iNext.
    iExists (<[ sn2 := Q ]> (<[ sn1 := P ]> (delete sn mprops))).
    iExists Ptotal, outlives.
    iSplitL "box". { 
      rewrite boxmap_insert_Borrow. rewrite boxmap_insert_Borrow.
      rewrite boxmap_delete. iFrame.
    }
    iFrame "vs". iFrame "outlives".
    
    destruct pures as [Hdom [Hwf Hoc]].
    assert (al ∪ de' ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Borrow al de') Hmbs_sn).
    }
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_insert_L. rewrite dom_delete_L. rewrite dom_delete_L.
        rewrite Hdom. trivial. }
      split. { apply map_wf_insert; trivial. apply map_wf_insert; trivial.
          apply map_wf_delete; trivial. }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice2".
      iApply big_sepM_insert_1. iFrame "slice1".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
    }
  Qed. 
  
  Lemma llft_fb_vs_create_empty alive dead outlives mbs mprops sn P dd :
  ¬(dd ## dead) →
  (mbs !! sn = None) →
  llft_fb_vs alive dead outlives mbs mprops
  ⊢ llft_fb_vs alive dead outlives (<[sn:=Borrow ∅ dd]> mbs) (<[sn:=P]> mprops).
  Proof.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdd Hmbssn) "Hvs".
    
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    
    iDestruct (full_borrows_invalidated_via_insert_false my_alive my_dead k sn mbs mprops (Borrow ∅ {[default_dead]}) P with "inval") as "inval"; trivial.
    
    iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
      iPureIntro. intuition. }
    
    iModIntro.
    
    iSplitL "reval". {
      iApply full_borrows_revalidated_via_insert_false; trivial.
      unfold revalidated. rewrite bool_decide_eq_false. set_solver.
    }
    
    iApply IH; trivial. { set_solver. }
  Qed.
  
  Lemma llft_fb_borrow_create_empty alive dead blocked P :
      (▷ llft_fb_inv alive dead blocked) ∗ P
        ={↑Nbox}=∗
        ∃ sn , (▷ llft_fb_inv alive dead blocked)
            ∗ OwnBorState γ sn (Borrow ∅ {[ default_dead ]})
            ∗ slice Nbox sn P.
  Proof.
    iIntros "[Inv P]".
    unfold llft_fb_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices outlives]]]]]".
    
    iMod (slice_insert_full Nbox (↑Nbox) true (boxmap alive dead mbs) Ptotal P with "P box") as (sn) "[%Hisnone [#slice box]]"; trivial.
    assert (mbs !! sn = None) as Hmbssn. {
      destruct (mbs !! sn) eqn:Heqn; trivial.
      rewrite lookup_fmap in Hisnone. rewrite Heqn in Hisnone. discriminate.
    }
    iMod (alloc_bor_state γ sn mbs (Borrow ∅ {[ default_dead ]}) with "auth") as "[auth OwnBor]"; trivial.
    
    assert (default_dead ∈ dead) as Hdd. { unfold map_wf in pures. intuition. }
    assert (¬({[default_dead]} ## dead)) as Hdd2. { set_solver. }
    
    iDestruct (bi.later_mono _ _ (llft_fb_vs_create_empty alive dead outlives mbs mprops sn P {[default_dead]} Hdd2 Hmbssn) with "vs") as "vs".
    
    iModIntro. iExists sn. iFrame "OwnBor". iFrame "slice".
    iNext.
    iExists (<[sn:=Borrow ∅ {[default_dead]}]> mbs).
    iExists (<[sn:=P]> mprops).
    iExists (P ∗ Ptotal)%I.
    iExists outlives.
    iFrame "auth".
    iSplitL "box". { 
      rewrite boxmap_insert_Borrow.
      rewrite bool_decide_eq_true_2. { iFrame. }
      set_solver.
    }
    iFrame "vs". iFrame "outlives".
    
    destruct pures as [Hdom [Hwf Hoc]].
    
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite Hdom. trivial. }
      split. { apply map_wf_insert; trivial. set_solver. }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. trivial. }
  Qed.

  Lemma llft_fb_augment_outlives alive dead blocked outlives outlives' :
    (outlives ⊆ outlives') →
      (▷ llft_fb_inv alive dead blocked) ∗ Outlives outlives
    ⊢ (▷ llft_fb_inv alive dead blocked) ∗ Outlives outlives'.
  Admitted.
  
  Lemma llft_fb_vs_for_unborrow_start alive dead outlives mbs mprops sn bl al de de' P :
    (alive ## dead) →
    (mbs !! sn = Some (Borrow al de')) →
    (¬ de' ## dead) →
    (¬ de ## dead) →
    llft_fb_vs alive dead outlives mbs mprops
      ∗ ▷ (mprops !! sn ≡ Some P)
    ⊢
    llft_fb_vs alive dead outlives (<[sn:=Unborrow bl al de]> mbs) (<[sn:=P]> (delete sn mprops)).
  Proof.
    replace (<[sn:=Unborrow bl al de]> mbs) with 
        (<[sn:=Unborrow bl al de]> (delete sn mbs)).
      2: { apply map_eq. { intros i. destruct (decide (sn = i)).
          - subst sn. rewrite lookup_insert. rewrite lookup_insert. trivial.
          - rewrite lookup_insert_ne; trivial. rewrite lookup_insert_ne; trivial.
              rewrite lookup_delete_ne; trivial. } }
  
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hmbssn Hde' Hde) "[Hvs #Heq]".
    
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    
    iDestruct (full_borrows_delete_insert_same my_alive my_dead k sn mbs mprops (Borrow al de') (Unborrow bl al de) P with "[inval]") as "inval".
      { unfold invalidated. rewrite bool_decide_eq_true. rewrite bool_decide_eq_true.
        set_solver. }
      { trivial. } { iFrame. iFrame "#". }
      
    iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
      iPureIntro. intuition. }
    
    iModIntro.
    
    iSplitL "reval". {
      iApply full_borrows_revalidated_via_insert_false.
      { apply lookup_delete. } { unfold revalidated. trivial. }
      iApply full_borrows_revalidated_via_delete_false.
      { apply Hmbssn. } iFrame.
    }
    
    iApply IH; trivial. { set_solver. } { set_solver. } { set_solver. }
    iFrame. iFrame "#".
  Qed.
  
  Lemma llft_fb_unborrow_start alive dead blocked outlives sn (bl al de : gset nat) P :
    (al ⊆ alive) →
    ¬(de ## dead) →
    (bl ## blocked) →
    (bl ⊆ alive) →
    (∀ (k : nat) , k ∈ al → (bl, k) ∈ outlives) →
    (▷ llft_fb_inv alive dead blocked) ∗ LtState γ alive dead ∗ Outlives outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
      ⊢ |={↑Nbox}=> 
    (▷ llft_fb_inv alive dead (blocked ∪ bl)) ∗ LtState γ alive dead
        ∗ Outlives outlives
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ (▷ P).
  Proof.
    intros Hal Hde Hbl Hblalive Houtlives.
    iIntros "[Inv [LtState [Outlives [OwnBor #slice]]]]".
    unfold llft_fb_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives') "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'.
    
    assert (al ## dead) as Hdisj_al_dead. { unfold map_wf in pures; set_solver. }
    
    iDestruct (agree_bor_state_borrow_lts γ sn mbs alive dead al de Hdisj_al_dead
        with "[LtState auth OwnBor]") as (de') "[%Hmbssn %Hrel_de]". { iFrame. }
    assert (boxmap alive dead mbs !! sn = Some true) as Hboxmaptrue.
    { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
      f_equiv. rewrite bool_decide_eq_true. split; trivial.
      destruct (decide (de = de')); intuition. subst de'; intuition. }
    
    iMod (slice_empty (Nbox) (↑Nbox) true (boxmap alive dead mbs) Ptotal P sn with "slice box") as "[P box]". { set_solver. } { trivial. }
    
    iMod (update_bor_state_borrow_lts γ sn mbs alive dead al de (Unborrow bl al de) Hdisj_al_dead with "[LtState auth OwnBor]") as "[LtState [auth OwnBor]]". { iFrame. }
    
    assert (alive ## dead) as Hdisj. { unfold map_wf in pures; intuition. }
    assert (¬ de' ## dead) as Hde'. { set_solver. }
    
    iDestruct (bi.later_mono _ _ (llft_fb_vs_for_unborrow_start alive dead outlives mbs mprops sn bl al de de' P Hdisj Hmbssn Hde' Hde) with "[vs]") as "vs".
      { iFrame. iNext. iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice".
        { intuition. } { apply Hmbssn. } { iFrame "#". }
       iFrame. iFrame "#".
     }
    
    iModIntro.
    iFrame "LtState". iFrame "outlives". iFrame "Outlives". iFrame "P". iFrame "OwnBor".
    
    iNext.
    iExists (<[sn:=Unborrow bl al de]> mbs). iExists (<[sn:=P]> (delete sn mprops)).
    iExists Ptotal.
    
    iFrame "auth".
    iSplitL "box". { rewrite boxmap_insert_Unborrow. iFrame. }
    iFrame "vs".
    
    destruct pures as [Hdom [Hwf Hoc]].
    assert (al ∪ de' ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Borrow al de') Hmbssn).
    }
    iSplitL. { iPureIntro. 
      split. {
        rewrite dom_insert_L.
        rewrite dom_insert_L.
        rewrite dom_delete_L. rewrite Hdom. apply set_eq. intro x.
          destruct (decide (x = sn)); set_solver.
      }
      split. { apply map_wf_insert_unborrow; trivial. { set_solver. } }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition. }
  Qed.
    
  Lemma llft_vs_for_unborrow_end' k1 alive dead outlives mbs mprops bl al de sn sn2 Q :
    (mbs !! sn = Some (Unborrow bl al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (k1 ∈ al) →
    (k1 ∉ alive) →
    (¬(de ## dead)) →
  llft_fb_vs alive dead outlives mbs mprops
  ⊢ llft_fb_vs alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof.
    intros Hsn Hsnmbs2 Hbl_a_outlives Hk1al. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hk1alive Hde_dead) "Hvs".
    
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    
    iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { trivial. }
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hsn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
        iPureIntro. intuition. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { trivial. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. }
   Qed.
  
  Lemma llft_vs_for_unborrow_end alive dead outlives mbs mprops bl al de sn sn2 P Q :
    (mbs !! sn = Some (Unborrow bl al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (al ⊆ alive) →
    (¬(de ## dead)) →
  llft_fb_vs alive dead outlives mbs mprops
    ∗ (∀ d, ⌜d ∈ dead⌝ -∗ Dead γ d)
    ∗ (▷ Q ∗ (∃ k : nat, ⌜k ∈ bl⌝ ∗ Dead γ k) ={∅}=∗ ▷ P)
    ∗ (▷ (mprops !! sn ≡ Some P))
  ⊢
  llft_fb_vs alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof.
    intros Hsn Hsn2 Hbl_a_outlives. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hal_alive Hde_dead) "[Hvs [#Halldead [qvs #Heq]]]".
    
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    
    iAssert (∀ d : nat, ⌜d ∈ (my_dead ∪ {[ k ]})⌝ -∗ Dead γ d)%I as "#Halldead2".
      { iIntros (d) "%Hdin". rewrite elem_of_union in Hdin. destruct Hdin as [Hdin1|Hdin2].
        - iApply "Halldead". iPureIntro; trivial.
        - rewrite elem_of_singleton in Hdin2. subst k. iApply "Dead".
      }
    
    destruct (decide (k ∈ al)) as [Hin|Hout].
    
    - assert (invalidated my_alive my_dead k (Borrow al de) = true) as Hinval_true.
      { unfold invalidated. rewrite bool_decide_eq_true. intuition. }
      iDestruct ((full_borrows_invalidated_via_insert my_alive my_dead k sn2 _ _ _ _ Hsn2 Hinval_true) with "inval") as "[Q inval]".
      
      assert (¬(bl ## my_dead ∪ {[ k ]})) as Hbl_disj_my_dead_u.
      {
        have Hoc2 := Hoc (bl, k) (Hbl_a_outlives k Hin). apply Hoc2. set_solver.
      }
      assert (bl ∩ (my_dead ∪ {[ k ]}) ≠ ∅) as Hbl_disj_my_dead_u2. { set_solver. }
      assert (∃ x , x ∈ (bl ∩ (my_dead ∪ {[ k ]}))) as Hex_x. { apply set_choose_L; trivial. }
      destruct Hex_x as [x Hex_x].
      assert (x ∈ bl) as Hex_bl by set_solver.
      assert (x ∈ (my_dead ∪ {[ k ]})) as Hex_d by set_solver.
      
      iMod ("qvs" with "[Q]") as "P".
      { iFrame "Q". iExists x. iSplitL. { iPureIntro; trivial. } iApply "Halldead2".
        iPureIntro; trivial. }
        
      iDestruct (full_borrows_invalidated_via_delete my_alive my_dead k sn mbs mprops (Unborrow bl al de) P Hsn with "[Heq inval P]") as "inval".
        { iFrame. iFrame "Heq". }
      
      iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
        iPureIntro. intuition. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { apply Hsn2. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply (llft_vs_for_unborrow_end' k); trivial. { set_solver. } { set_solver. }
        { set_solver. } set_solver.
   - iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply Hsn2. }
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hsn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
        iPureIntro. intuition. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_insert_false.
          { apply Hsn2. }
          { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hsn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. }
      iFrame. iFrame "#".
  Qed.
        
  Lemma llft_fb_unborrow_end alive dead blocked sn bl al de P Q :
    (▷ llft_fb_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ slice Nbox sn P
        ∗ (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={∅}=∗ ▷ P))
        ∗ (▷ Q)
        ={↑Nbox}=∗ ∃ sn2,
          (▷ llft_fb_inv alive dead (blocked ∖ bl)) ∗ LtState γ alive dead
          ∗ OwnBorState γ sn2 (Borrow al de)
          ∗ slice Nbox sn2 Q
          ∗ ⌜bl ⊆ blocked⌝
        .
  Proof.
    iIntros "[Inv [LtState [OwnBor [#slice [qvs q]]]]]".
    unfold llft_fb_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    destruct pures as [Hdom [Hwf Houtlives]].
    iDestruct (agree_bor_state_unborrow γ sn mbs bl al de with "[auth OwnBor]") as "%Hmbssn". { iFrame. }
    assert (boxmap alive dead mbs !! sn = Some false) as Hboxmapsn. {
      unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. trivial.
    }
    assert (bl ⊆ blocked) as Hbl. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    assert (¬(de ## dead)) as Hde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    assert (al ⊆ alive) as Hal. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intros a Haal.
      destruct (decide (a ∈ alive)) as [Hin|Hout]; trivial. exfalso.
      assert (a ∈ dead) as Hadead by set_solver.
      destruct Hf as [Hx [Hy [Hz Hw]]]. have Hzz := Hz a Haal.
      have Hzzz := Houtlives (bl, a) Hzz Hadead.
      set_solver.
    }
    assert (bl ⊆ alive) as Hblalive. { unfold map_wf in Hwf. set_solver. }
    
    iMod (delete_bor_state_unborrow γ sn mbs bl al de with "[auth OwnBor]") as "auth". { iFrame. }
    iMod (slice_delete_empty Nbox (↑Nbox) true (boxmap alive dead mbs) Ptotal P sn with "slice box") as (Ptotal') "[HeqPtotal box]". { set_solver. } { trivial. }
    iMod (slice_insert_full Nbox (↑Nbox) true (delete sn (boxmap alive dead mbs)) Ptotal' Q with "q box") as (sn2) "[%Hlookup_sn2 [#slice2 box]]". { set_solver. }
    iMod (alloc_bor_state γ sn2 (delete sn mbs) (Borrow al de) with "auth") as "[auth OwnBor2]". { apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hlookup_sn2). }
    
    assert (delete sn mbs !! sn2 = None) as Hsn2. { apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hlookup_sn2). }
    
    iMod (get_all_deads with "LtState") as "[LtState #Halldeads]".
    
    assert (∀ a : nat, a ∈ al → (bl, a) ∈ outlives) as Hoforall. { 
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition.
    }
    
    iDestruct (bi.later_mono _ _ (llft_vs_for_unborrow_end alive dead outlives mbs mprops bl al de sn sn2 P Q Hmbssn Hsn2 Hoforall Hal Hde) with "[vs qvs]") as "vs".
    { iFrame. iNext.
      iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } { iFrame "#". } iFrame "EqSlice". iFrame "Halldeads".
    }
    
    iModIntro. iExists sn2. iFrame "LtState". iFrame "OwnBor2". iFrame "slice2".
    iSplitL. 2: { iPureIntro; trivial. }
    iNext.
    iExists (<[sn2:=Borrow al de]> (delete sn mbs)).
    iExists (<[sn2:=Q]> (delete sn mprops)).
    iExists (Q ∗ Ptotal')%I.
    iExists outlives.
    iFrame "auth". iFrame "outlives".
    iSplitL "box". {
      rewrite boxmap_insert_Borrow.
      rewrite boxmap_delete.
      rewrite bool_decide_eq_true_2. { iFrame. } split; trivial.
    }
    iFrame "vs".
    
    assert (al ∪ de ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Unborrow bl al de) Hmbssn).
    }
    
    iSplitL. { iPureIntro. 
      split. {
        rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_delete_L. rewrite dom_delete_L. rewrite Hdom. trivial.
      }
      split.
      { apply map_wf_insert; trivial.
        apply (map_wf_delete_unborrow alive dead blocked bl al de); trivial.
      }
      trivial.
    }
    iApply big_sepM_insert_1. iFrame "slice2".
    rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
    iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
  Qed.
  
  Lemma set_lemma1 (x y z w : gset nat) : x ∪ y ⊆ z ∪ w → x ## w → x ⊆ z.
  Proof. set_solver. Qed.
  
  Lemma llfb_fb_vs_for_reborrow1 alive dead al al' sn sn2 mbs mprops P k dd :
    (sn ≠ sn2) →
    alive ## dead →
    ¬(dd ## dead) →
    (al' ⊆ alive ∪ dead) →
    mbs !! sn = Some (Borrow al dd) →
    mbs !! sn2 = None →
  ▷ full_borrows_invalidated_via alive dead k
                (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> (delete sn mbs)))
                (<[sn2:=P]> (<[sn:=P]> (delete sn mprops)))
      ∗ ▷ (mprops !! sn ≡ Some P)
  ⊢ ▷ full_borrows_invalidated_via alive dead k mbs mprops
      ∗ (⌜ al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al' ⌝ -∗ ▷ P).
  Proof.
    iIntros (Hne Hdisj Halive Hdead Hmbssn Hmbssn2) "[inval #Heq]".
    destruct (decide (k ∈ al ∧ al ⊆ alive)) as [Hin|Hout].
    
    - destruct (decide (al' ⊆ alive)) as [Hsub|Hnotsub].
      + 
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[P inval]".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      { unfold invalidated. rewrite bool_decide_eq_true. set_solver. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply lookup_delete. }
      iDestruct (full_borrows_invalidated_via_delete with "[P inval]") as "inval".
        { apply Hmbssn. } { iFrame "Heq". iFrame "inval". iFrame "P". }
      iFrame. iIntros "%t". exfalso. set_solver.
      +
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[P inval]".
      { apply lookup_delete. }
      { unfold invalidated. rewrite bool_decide_eq_true. set_solver. }
      iDestruct (full_borrows_invalidated_via_delete with "[P inval]") as "inval".
        { apply Hmbssn. } { iFrame "Heq". iFrame "inval". iFrame "P". }
      iFrame. iIntros "%t". exfalso. set_solver.
      
    - destruct (decide (al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al')) as [Hx|Hy].
      +
      iDestruct (full_borrows_invalidated_via_insert with "inval") as "[P inval]".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      { unfold invalidated. rewrite bool_decide_eq_true. set_solver. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply lookup_delete. }
      iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn. } { unfold invalidated. rewrite bool_decide_eq_false. set_solver. }
      iFrame. iIntros "%Ht". done.
      +
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
      { apply lookup_delete. }
      iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn. } { unfold invalidated. rewrite bool_decide_eq_false. set_solver. }
      iFrame. iIntros "%Ht". exfalso. set_solver.
  Qed.
  
  Lemma llfb_fb_vs_for_reborrow2 alive dead al al' sn sn2 mbs mprops P k dd :
    (sn ≠ sn2) →
    alive ## dead →
    ¬(dd ## dead) →
    (al' ⊆ alive ∪ dead) →
    mbs !! sn = Some (Borrow al dd) →
    mbs !! sn2 = None →
    ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ∗ ▷ (mprops !! sn ≡ Some P)
      ∗ (⌜ al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al' ⌝ -∗ ▷ P)
    ⊢
    ▷ full_borrows_revalidated_via alive dead k
        (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> (delete sn mbs)))
        (<[sn2:=P]> (<[sn:=P]> (delete sn mprops))).
  Proof.
    iIntros (Hdisj Halive Hdead Hwfal' Hmbssn Hmbssn2) "[reval [#Heq P]]".
    
    iApply full_borrows_revalidated_via_insert_false.
      { rewrite lookup_insert_ne; trivial. rewrite lookup_delete_ne; trivial. }
      { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
    
    destruct (decide (al ⊆ alive ∧ k ∉ al ∧ al' ⊆ alive ∧ k ∈ al')) as [Ha|Hb].
    - iDestruct ("P" with "[%]") as "P"; trivial.
    
      iApply full_borrows_revalidated_via_insert.
        { rewrite lookup_delete; trivial. } iFrame.
        
      iApply full_borrows_revalidated_via_delete_false.
        { apply Hmbssn. } iFrame.
    -
      iApply full_borrows_revalidated_via_insert_false.
        { rewrite lookup_delete; trivial. } 
        { unfold revalidated. rewrite bool_decide_eq_false. set_solver. }
        
      iApply full_borrows_revalidated_via_delete_false.
        { apply Hmbssn. } iFrame.
   Qed.
          
  Lemma llfb_fb_vs_for_reborrow alive dead outlives mbs mprops sn sn2 al al' dd P :
    (sn ≠ sn2) →
    alive ## dead →
    ¬(dd ## dead) →
    (al' ⊆ alive ∪ dead) →
    mbs !! sn = Some (Borrow al dd) →
    mbs !! sn2 = None →
    llft_fb_vs alive dead outlives mbs mprops
      ∗ ▷ (mprops !! sn ≡ Some P)
    ⊢ 
    llft_fb_vs alive dead outlives
      (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> mbs))
      (<[sn2:=P]> (<[sn:=P]> (delete sn mprops))).
  Proof.
    replace (<[sn:=Borrow al al']> mbs) with (<[sn:=Borrow al al']> (delete sn mbs)).
      2: { apply map_eq. { intros i. destruct (decide (sn = i)).
          - subst sn. rewrite lookup_insert. rewrite lookup_insert. trivial.
          - rewrite lookup_insert_ne; trivial. rewrite lookup_insert_ne; trivial.
              rewrite lookup_delete_ne; trivial. } }
  
    intros Hne.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hdead Hwfal Hmbssn Hmbssn2) "[Hvs #Heq]".
    
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    
    iDestruct (llfb_fb_vs_for_reborrow1 my_alive my_dead al al' sn sn2 mbs mprops P k dd with "[inval]") as "[inval P]"; trivial. { iFrame. iFrame "Heq". }
     
    iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
      iPureIntro. intuition. }

    iModIntro.
    
    iSplitL "P reval". { iApply llfb_fb_vs_for_reborrow2; trivial. iFrame. iFrame "Heq". }
    
    iApply IH; trivial. { set_solver. } { set_solver. }
      { intro x. destruct (decide (x = k)); set_solver. }
    iFrame. iFrame "#".
  Qed.
      
  Lemma llfb_fb_vs_for_delete_already_dead alive dead outlives mbs mprops sn al dd :
    alive ## dead →
    ¬(al ## dead) →
    (mbs !! sn = Some (Borrow al dd)) →
      llft_fb_vs alive dead outlives mbs mprops
      ⊢
      llft_fb_vs alive dead outlives (delete sn mbs) (delete sn mprops).
  Proof.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hdead Hmbssn) "Hvs".
    
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
        iPureIntro. intuition. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hmbssn. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. }
  Qed.
    
  Lemma llfb_fb_vs_for_unnest alive dead outlives mbs mprops sn sn' al al' dd dd' :
    (mbs !! sn' = Some (Borrow al' dd')) →
    alive ## dead →
    ¬(dd ## dead) →
    al' ⊆ alive →
    (llft_fb_vs alive dead outlives mbs mprops
      ∗ (∀ d, ⌜d ∈ dead⌝ -∗ Dead γ d)
      ∗ OwnBorState γ sn (Borrow al al')
      ∗ ▷ (mprops !! sn' ≡ Some (OwnBorState γ sn (Borrow al dd)))
      ⊢ 
      llft_fb_vs alive dead outlives (delete sn' mbs) (delete sn' mprops))%I.
  Proof.
    intros Hmbssn'.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hdisj Hdd Halal'.
    iIntros "[Hvs [#Halldead [OwnBor #Heq]]]".
    
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    
    iAssert (∀ d : nat, ⌜d ∈ (my_dead ∪ {[ k ]})⌝ -∗ Dead γ d)%I as "#Halldead2".
      { iIntros (d) "%Hdin". rewrite elem_of_union in Hdin. destruct Hdin as [Hdin1|Hdin2].
        - iApply "Halldead". iPureIntro; trivial.
        - rewrite elem_of_singleton in Hdin2. subst k. iApply "Dead".
      }
    
    destruct (decide (k ∈ al')) as [Hin|Hout].
    - assert (dd ∩ my_dead ≠ ∅) as Hdisj2. { set_solver. }
      assert (∃ x , x ∈ (dd ∩ my_dead)) as Hex_x. { apply set_choose_L; trivial. }
      destruct Hex_x as [x Hex_d].
      iMod (update_bor_state_borrow_fix_dead γ sn al al' dd k x with "[OwnBor]") as "OwnBor".
        { trivial. } { set_solver. } {
          iFrame.  iFrame "Dead".
          iApply "Halldead". iPureIntro. set_solver.
        }
      
      iDestruct (full_borrows_invalidated_via_delete with "[inval OwnBor]") as "inval".
        { apply Hmbssn'. } { iFrame "Heq". iFrame "inval". iFrame "OwnBor". }
        
      iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
        iPureIntro. intuition. }
        
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hmbssn'. }
          iFrame "reval".
      }
      
      iApply (llfb_fb_vs_for_delete_already_dead _ _ outlives mbs mprops sn' al' dd').
        { set_solver. } { set_solver. } { trivial. }
      iFrame "vs".
      
    - 
     iDestruct (full_borrows_invalidated_via_delete_false with "inval") as "inval".
      { apply Hmbssn'. }
      { unfold invalidated.  rewrite bool_decide_eq_false. set_solver. }
      
      iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
        iPureIntro. intuition. }
      
      iModIntro.
      
      iSplitL "reval". {
          iApply full_borrows_revalidated_via_delete_false.
          { apply Hmbssn'. }
          iFrame.
      }
      
      iApply IH; trivial. { set_solver. } { set_solver. } { set_solver. }
      iFrame. iFrame "#".
  Qed.
        
  Lemma llft_fb_unnest alive dead blocked sn sn' al al' P :
    (▷ llft_fb_inv alive dead blocked) ∗ LtState γ alive dead 
        ∗ slice Nbox sn P
        ∗ OwnBorState γ sn' (Borrow al' {[ default_dead ]})
        ∗ slice Nbox sn' (OwnBorState γ sn (Borrow al {[ default_dead ]}))
      ={↑Nbox}=∗ ∃ sn2,
    (▷ llft_fb_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn2 (Borrow (al ∪ al') {[ default_dead ]})
        ∗ slice Nbox sn2 P.
  Proof.
    iIntros "[Inv [LtState [#sliceP [OwnBor' #sliceBorrow]]]]".
    destruct (decide ((al ∪ al') ## dead)) as [Hdisj|Hndisj].
      2: { iMod (llft_fb_fake alive dead blocked (al ∪ al') {[default_dead]} P with "LtState") as (sn2) "LtState"; trivial. iModIntro. iExists sn2. iFrame. }
    
    unfold llft_fb_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    
    assert (al ## dead) as Hdisj_al_dead. { unfold map_wf in pures; set_solver. }
    assert (al' ## dead) as Hdisj_al'_dead. { unfold map_wf in pures; set_solver. }
    assert (alive ## {[default_dead]}) as Hdisj_alive_dd. { unfold map_wf in pures. set_solver. }
    assert (alive ## dead) as Halive_disj_dead. { unfold map_wf in pures. intuition. }
    assert (default_dead ∈ dead) as Hdd. { unfold map_wf in pures. intuition. }
    
    iDestruct (agree_bor_state_borrow_lts γ sn' mbs alive dead al' {[default_dead]}
        with "[LtState auth OwnBor']") as (dd') "[%Hmbssn' %Hrel_dd']". { set_solver. } { iFrame. }
    
    assert (al' ⊆ alive) as Hal'_sub_alive. {
      destruct pures as [Hp [[Ha [Hb [Hc [Hforall Hforall2]]]] Hrest]]. 
      have Hforsn' := Hforall sn' _ Hmbssn'.
      apply (set_lemma1 _ _ _ _ Hforsn' Hdisj_al'_dead).
    }
    
    assert (boxmap alive dead mbs !! sn' = Some true) as Hboxmap_true'.
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn'. simpl.
        f_equiv. rewrite bool_decide_eq_true. 
        split. { set_solver. } unfold map_wf in pures. set_solver.
      }
    
    iMod (slice_delete_full Nbox (↑Nbox) true (boxmap alive dead mbs) Ptotal
        (OwnBorState γ sn (Borrow al {[default_dead]}))
        sn' with "sliceBorrow box") as (Ptotal') "[>OwnBor [Ptotaleq box]]"; trivial.
        
    iDestruct (agree_bor_state_borrow_lts γ sn mbs alive dead al {[default_dead]}
        with "[LtState auth OwnBor]") as (dd) "[%Hmbssn %Hrel_dd]". { set_solver. } { iFrame. }
        
    assert (al ⊆ alive) as Hal_sub_alive. {
      destruct pures as [Hp [[Ha [Hb [Hc [Hforall Hforall2]]]] Hrest]]. 
      have Hforsn := Hforall sn _ Hmbssn.
      apply (set_lemma1 _ _ _ _ Hforsn Hdisj_al_dead).
    }
    assert (dd ⊆ alive ∪ dead) as Hdd_sub_alive. {
      destruct pures as [Hp [[Ha [Hb [Hc [Hforall Hforall2]]]] Hrest]]. 
      have Hforsn := Hforall sn _ Hmbssn.
      set_solver.
    }
    assert (al ∪ al' ⊆ alive) as HalUal' by set_solver.
    assert (¬(dd ## dead)) as Hdddead. { set_solver. }
    
    assert (boxmap alive dead mbs !! sn = Some true) as Hboxmap_true.
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
        f_equiv. rewrite bool_decide_eq_true. 
        split. { set_solver. } unfold map_wf in pures. set_solver.
      }
    
    iDestruct (distinct_bor_state_borrow_borrow_lts γ sn' sn al' {[default_dead]} al {[default_dead]} alive dead with "[LtState OwnBor OwnBor']") as "%Hne"; trivial.
    { iFrame. }
    
    iMod (delete_bor_state_borrow_lts γ sn' mbs alive dead al' {[default_dead]} Hdisj_al'_dead
        with "[LtState auth OwnBor']") as "[LtState auth]". { iFrame. }
        
    iMod (update_bor_state_borrow_lts γ sn (delete sn mbs) alive dead al {[default_dead]} (Borrow al al') Hdisj_al_dead
        with "[LtState auth OwnBor]") as "[LtState [auth OwnBor]]". { iFrame. }
    
    iMod (slice_empty Nbox (↑Nbox) true (delete sn' (boxmap alive dead mbs)) Ptotal' P sn
        with "sliceP box") as "[P box]". { set_solver. } { rewrite lookup_delete_ne; trivial. }
    
    iMod (slice_insert_full Nbox (↑Nbox) true (<[sn:=false]> (delete sn' (boxmap alive dead mbs))) Ptotal' P with "P box") as (sn2) "[%Hsn2None [#slice2 box]]"; trivial.
    
    iMod (alloc_bor_state2 γ sn2 (<[sn:=Borrow al al']> (delete sn' mbs)) alive dead (al ∪ al') {[default_dead]} dd with "[LtState auth]") as "[LtState [auth OwnBor2]]".
      { eapply lookup_insert_delete_boxmap_helper. apply Hsn2None. }
      { apply Hrel_dd. } { iFrame. }
      
    iMod (get_all_deads with "LtState") as "[LtState #Halldeads]".
    
    assert (sn ≠ sn2) as Hne2.
      { intro Heq. subst sn2. rewrite lookup_insert in Hsn2None. discriminate. }
    
    iDestruct (bi.later_mono _ _ (llfb_fb_vs_for_unnest alive dead outlives mbs mprops sn sn' al al' {[default_dead]} _ Hmbssn' Halive_disj_dead Hdddead Hal'_sub_alive) with "[vs OwnBor]") as "vs".
     { iNext. iDestruct (agree_slice_with_map mbs mprops sn' _
          (OwnBorState γ sn (Borrow al dd)) with "[]") as "EqSlice".
        { intuition. } { apply Hmbssn'. } { iFrame "#". }
       iFrame. iFrame "#".
     }
     
    assert (delete sn' mbs !! sn2 = None) as Hdelsn'. {
      eapply lookup_insert_delete_boxmap_helper2. apply Hsn2None.
    }
     
    iDestruct (bi.later_mono _ _ (llfb_fb_vs_for_reborrow alive dead outlives
        (delete sn' mbs) _ sn sn2 al al' dd P Hne2 Halive_disj_dead Hdddead _ _ Hdelsn') with "[vs]") as "vs".
     { iNext. iFrame "vs". iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice".
        { intuition. } { apply Hmbssn. } { iFrame "#". }
       rewrite lookup_delete_ne; trivial. }
      
    iModIntro. iExists sn2.
    iFrame "LtState". iFrame "OwnBor2". iFrame "slice2".
    iNext.
    iExists (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> (delete sn' mbs))).
    iExists (<[sn2:=P]> (<[sn:=P]> (delete sn (delete sn' mprops)))).
    iExists (P ∗ Ptotal')%I.
    iExists outlives.
    iFrame "auth". iFrame "outlives". iFrame "vs".
    iSplitL "box". {
        rewrite boxmap_insert_Borrow. rewrite boxmap_insert_Borrow. rewrite boxmap_delete.
        rewrite bool_decide_eq_true_2.
        2: { split.  { set_solver. } unfold map_wf in pures. set_solver. }
        rewrite bool_decide_eq_false_2. 
        2: { intuition. }
        iFrame "box".
    }
    destruct pures as [Hdom [Hwf Hoc]].
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_insert_L. rewrite dom_delete_L. rewrite dom_delete_L.
        rewrite dom_delete_L.
        rewrite Hdom.
        apply set_eq. intros x.
        destruct (decide (x = sn')); destruct (decide (x = sn)); set_solver.
      }
      split. {
        apply map_wf_insert; trivial. 2: { set_solver. }
        apply map_wf_insert; trivial. 2: { set_solver. }
        apply map_wf_delete; trivial.
      }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice2".
      iApply big_sepM_insert_1. iFrame "sliceP".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm.
      rewrite lookup_delete_Some in Dm. intuition. }
    Unshelve.
    { set_solver. }
    rewrite lookup_delete_ne; trivial.
  Qed.
  
  Lemma inv_get_dead alive dead blocked
    : llft_fb_inv alive dead blocked ⊢ ⌜default_dead ∈ dead⌝.
  Admitted.
  
  Lemma lemma_set5 (al dd' alive dead : gset nat) :
    al ∪ dd' ⊆ alive ∪ dead →
    al ## dead →
    al ⊆ alive. Proof. set_solver. Qed.
    
  Lemma lemma_set6 (al' dd' alive dead : gset nat) :
    al'  ⊆ alive ∪ dead →
    al' ## dead →
    al' ⊆ alive. Proof. set_solver. Qed.
            
  Lemma llft_fb_reborrow alive dead blocked P sn al al' :
      (al' ⊆ alive ∪ dead) →
      (▷ llft_fb_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Borrow al {[default_dead]})
        ∗ slice Nbox sn P
        ={↑Nbox}=∗ ∃ sn1 sn2,
      (▷ llft_fb_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow (al ∪ al') {[default_dead]})
        ∗ OwnBorState γ sn2 (Borrow al al')
        ∗ slice Nbox sn1 P
        ∗ slice Nbox sn2 P.
  Proof.
    intros Hal'wf.
    iIntros "[Inv [LtState [OwnBor #sliceP]]]".
    destruct (decide (al ## dead)) as [Hdisj|Hndisj].
    2: {
      iMod (llft_fb_fake alive dead blocked (al ∪ al') {[default_dead]} P with "LtState") as (sn1) "[LtState [A Aslice]]". { set_solver. }
      iMod (llft_fb_fake alive dead blocked al al' P with "LtState") as (sn2) "[LtState [B Bslice]]". { set_solver. }
      iModIntro. iExists sn1. iExists sn2. iFrame.
    }
    
    destruct (decide (al' ## dead)) as [Hdisj'|Hndisj].
    2: {
      iMod (llft_fb_fake alive dead blocked (al ∪ al') {[default_dead]} P with "LtState") as (sn1) "[LtState [A Aslice]]". { set_solver. }
      
      iDestruct (inv_get_dead with "Inv") as "#X". iMod "X". iDestruct "X" as "%Hdd".
      
      assert (∃ x , x ∈ al' ∩ dead) as Hex_x. { apply set_choose_L; set_solver. }
      destruct Hex_x as [x Hex].
      iMod (get_all_deads γ alive dead with "LtState") as "[LtState #Deads]".
      iMod (update_bor_state_borrow_fix_dead γ sn al {[default_dead]} al' default_dead x with "[OwnBor]") as "OwnBor2"; trivial. { set_solver. } { set_solver. } {
        iFrame. iSplitL.
          { iApply "Deads". iPureIntro. trivial. }
          { iApply "Deads". iPureIntro. set_solver. }
      }
      
      iModIntro. iExists sn1. iExists sn. iFrame. iFrame "#".
    }
   
    unfold llft_fb_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    
    iDestruct (agree_bor_state_borrow_lts γ sn mbs alive dead al {[default_dead]}
        with "[LtState auth OwnBor]") as (dd') "[%Hmbssn %Hrel_dd]". { set_solver. } { iFrame.    }
        
    destruct pures as [Hdom [Hwf Houtlives]].
    assert (alive ## dead) as Halive_disj_dead. { unfold map_wf in Hwf. intuition. }
    assert (default_dead ∈ dead) as Hdddead. { unfold map_wf in Hwf. intuition. }
    assert (¬ dd' ## dead) as Hdd'dead. { set_solver. }
    assert (al ⊆ alive) as Halalive. { unfold map_wf in Hwf.
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn.
      apply (lemma_set5 al dd' alive dead); trivial.
    }
    assert (al' ⊆ alive) as Hal'alive. { apply (lemma_set6 al' dd' alive dead); trivial. }
    assert (dd' ⊆ alive ∪ dead) as Hdd'wf. { 
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn.
      set_solver.
    }
        
    iMod (slice_empty Nbox (↑Nbox) true (boxmap alive dead mbs) Ptotal P sn with "sliceP box")
      as "[P box]"; trivial.
    {
      unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl. f_equiv.
      rewrite bool_decide_eq_true. set_solver.
    }
        
    iMod (slice_insert_full Nbox (↑Nbox) true (<[sn:=false]> (boxmap alive dead mbs)) Ptotal P with "P box")
      as (sn2) "[%Hlookup_sn2 [#slice box]]".
    { trivial. }
    
    destruct (lookup_insert_boxmap_helper3 sn false alive dead mbs sn2 Hlookup_sn2) as [Hmbssn2 Hne].
    
    iMod (alloc_bor_state γ sn2 mbs (Borrow al al') with "auth") as "[auth OwnBor2]"; trivial.
    
    iDestruct (bi.later_mono _ _ (llfb_fb_vs_for_reborrow alive dead outlives mbs mprops sn sn2 al al' dd' P Hne Halive_disj_dead Hdd'dead Hal'wf Hmbssn Hmbssn2)
     with "[vs]") as "vs"; trivial. { iFrame. iNext.
      iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } iFrame "#". }
        
    iModIntro.
    iExists sn. iExists sn2.
    iFrame "LtState". iFrame "OwnBor". iFrame "OwnBor2". iFrame "slice". iFrame "sliceP".
    iNext.
    iExists (<[sn2:=Borrow (al ∪ al') dd']> (<[sn:=Borrow al al']> mbs)).
    iExists (<[sn2:=P]> (<[sn:=P]> (delete sn mprops))).
    iExists (P ∗ Ptotal)%I.
    iExists outlives.
    iFrame "outlives". iFrame "auth".
    iSplitL "box". {
      rewrite boxmap_insert_Borrow.
      rewrite boxmap_insert_Borrow.
      rewrite bool_decide_eq_true_2.
      - rewrite bool_decide_eq_false_2.
        + iFrame "box". 
        + set_solver.
      - set_solver.
    }
    iFrame "vs".
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_insert_L.
      rewrite dom_insert_L. rewrite dom_delete_L. rewrite Hdom.
        apply set_eq. intros x.
        destruct (decide (x = sn2)); destruct (decide (x = sn)); set_solver.
      }
      split. {
        apply map_wf_insert; trivial. 2: { set_solver. }
        apply map_wf_insert; trivial. set_solver.
      }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      iApply big_sepM_insert_1. iFrame "sliceP".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro. rewrite lookup_delete_Some in Dm. intuition.
    }
   Qed.
        
   Lemma llft_fb_borrow_create alive dead blocked lt P :
      (lt ⊆ alive ∪ dead) →
      (▷ llft_fb_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ P
        ={↑Nbox}=∗
        ∃ sn sn2, (▷ llft_fb_inv alive dead blocked)
            ∗ LtState γ alive dead
            ∗ OwnBorState γ sn (Borrow lt {[ default_dead ]})
            ∗ OwnBorState γ sn2 (Borrow ∅ lt)
            ∗ slice Nbox sn P
            ∗ slice Nbox sn2 P.
   Proof.
    intros Hlt. iIntros "[Inv [LtState P]]".
    iMod (llft_fb_borrow_create_empty alive dead blocked lt P Hlt with "[Inv P]") as (sn) "[Inv [OwnBor #slice]]". { iFrame. }
    iMod (llft_fb_reborrow alive dead blocked P sn lt {[default_dead]} Hlt with "[Inv LtState OwnBor]") as (sn1 sn2) "[Ha [Hb [Hd [He Hf]]]]".
      { iFrame. iFrame "#". }
    iModIntro. iExists sn1. iExists sn2. iFrame.
  Qed.
  
  Lemma bool_decide_equiv P Q `{Decision P, Decision Q} :
    (P ↔ Q) → bool_decide P = bool_decide Q. Admitted.
    
    
  (*Lemma set_lemma2 (k_new k: nat) (al my_alive : gset nat) :
    k_new ∉ al →
    (al ⊆ (my_alive ∪ {[k_new]}) ∖ {[k]}) →
    al ⊆ my_alive ∖ {[k]}.
  Proof. set_solver. Qed.*)
  
  Lemma set_lemma3 (k_new : nat) (alive dead al de : gset nat) :
      k_new ∉ alive →
      k_new ∉ dead →
      al ∪ de ⊆ alive ∪ dead →
      k_new ∉ al.
  Proof. set_solver. Qed.
  
  Lemma set_lemma4 (k: nat) (my_alive my_dead : gset nat) :
      (k ∈ my_alive) →
      my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]}) = my_alive ∪ my_dead. 
  Proof.
    intros k_in. apply set_eq. intro x. destruct (decide (x = k)); set_solver.
  Qed.
  
  Lemma set_lemma5 (k k_new: nat) (my_alive : gset nat) :
    (k ≠ k_new) →
    (my_alive ∖ {[k]} ∪ {[k_new]}) = (my_alive ∪ {[k_new]}) ∖ {[k]}.
  Proof.
    intros Hne. apply set_eq. intro x. destruct (decide (x = k)); set_solver.
  Qed.
  
  Lemma outlives_consistent_okay_on_kill_fresh alive dead blocked outlives m my_dead k_new :
      k_new ∉ alive →
      k_new ∉ dead →
      map_wf alive dead blocked outlives m →
      outlives_consistent (my_dead ∪ {[k_new]}) outlives →
      outlives_consistent my_dead outlives.
  Admitted.
  
  Lemma llfb_fb_vs_for_new_lt' alive dead blocked outlives my_alive my_dead mbs mprops k_new :
    map_wf alive dead blocked outlives mbs →
    my_alive ∪ my_dead = alive ∪ dead →
    my_alive ## my_dead →
    k_new ∉ alive →
    k_new ∉ dead →
    llft_fb_vs (my_alive) my_dead outlives mbs mprops 
    ⊢ llft_fb_vs (my_alive) (my_dead ∪ {[k_new]}) outlives mbs mprops.
  Proof.
    intros Hwf.
    generalize my_dead. clear my_dead.
    induction my_alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hsame Hdisj Hknew_alive Hknew_dead.
    iIntros "Hvs".
    rewrite llft_fb_vs_def.
    rewrite (llft_fb_vs_def my_alive).
    iIntros (k) "[%Hin_my_alive [Dead inval]]".
    destruct (decide (k = k_new)).
    - subst k_new. exfalso. set_solver.
    -   iMod ("Hvs" $! k with "[Dead inval]") as "[reval Hvs]".
        { iFrame. iSplitR. { iPureIntro. split. { intuition. }
          apply (outlives_consistent_okay_on_kill_fresh alive dead blocked outlives mbs (my_dead ∪ {[k]}) k_new); trivial.
          replace ((my_dead ∪ {[k]} ∪ {[k_new]})) with 
              (my_dead ∪ {[k_new]} ∪ {[k]}) by set_solver.
          intuition.
        }
          iNext. 
          unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (invalidated (my_alive) (my_dead ∪ {[k_new]}) k)).
          { intros sn bs. unfold invalidated.
            destruct bs as [al de|bl al de].
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
          }
          iFrame.
        }
        iModIntro. iSplitL "reval".
        {
          unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (revalidated my_alive my_dead k)).
          { intros sn bs Hmbssn.
            destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
            have Hf := Hforall sn bs. unfold revalidated.
            destruct bs as [al de|bl al de].
              - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true.
                intros [Hx [Hy Hz]]. split.
                + have Hf2 := Hf Hmbssn.
                  have Hg := (set_lemma3 k_new alive dead al de Hknew_alive Hknew_dead Hf2).
                  set_solver.
                + set_solver.
              - intros; trivial.
          }
          iFrame "reval".
        }
        iDestruct (IH with "Hvs") as "Hvs"; trivial.
          { set_solver. }
          { rewrite <- Hsame. apply set_lemma4. set_solver. }
          { set_solver. }
          replace ((my_dead ∪ {[k]} ∪ {[k_new]})) with 
              (my_dead ∪ {[k_new]} ∪ {[k]}) by set_solver.
          iFrame.
  Qed.
    
  Lemma llfb_fb_vs_for_new_lt alive dead blocked outlives my_alive my_dead mbs mprops k_new :
    map_wf alive dead blocked outlives mbs →
    my_alive ∪ my_dead = alive ∪ dead →
    my_alive ## my_dead →
    k_new ∉ alive →
    k_new ∉ dead →
    llft_fb_vs (my_alive) my_dead outlives mbs mprops 
    ⊢ llft_fb_vs (my_alive ∪ {[k_new]}) (my_dead) outlives mbs mprops.
  Proof.
    intros Hwf.
    generalize my_dead. clear my_dead.
    induction my_alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hsame Hdisj Hknew_alive Hknew_dead.
    iIntros "Hvs".
    rewrite (llft_fb_vs_def (my_alive ∪ {[k_new]})).
    iIntros (k) "[%Hin_my_alive [Dead inval]]".
    destruct (decide (k = k_new)).
      - subst k_new. iModIntro.
        iSplitR. {
          iApply borrow_sum_empty. intros sn bs Hmbssn. unfold revalidated.
          destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
          have Hf := Hforall sn bs.
          destruct bs as [al de|]; trivial. rewrite bool_decide_eq_false.
          set_solver.
        }
        replace ((my_alive ∪ {[k]}) ∖ {[k]}) with my_alive.
          + iApply (llfb_fb_vs_for_new_lt' alive dead blocked outlives my_alive my_dead mbs mprops k); trivial.
          + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
      - rewrite llft_fb_vs_def.
        iMod ("Hvs" $! k with "[Dead inval]") as "[reval Hvs]".
        { iFrame. iSplitR. { iPureIntro. split. { set_solver. } intuition. }
          iNext. 
          unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (invalidated (my_alive ∪ {[k_new]}) my_dead k)).
          { intros sn bs. unfold invalidated.
            destruct bs as [al de|bl al de].
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
            - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true. set_solver.
          }
          iFrame.
        }
        iModIntro. iSplitL "reval".
        {
          unfold full_borrows_invalidated_via.
          iApply (borrow_sum_equiv _ (revalidated my_alive my_dead k)).
          { intros sn bs Hmbssn.
            destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
            have Hf := Hforall sn bs. unfold revalidated.
            destruct bs as [al de|bl al de].
              - rewrite bool_decide_eq_true. rewrite bool_decide_eq_true.
                intros [Hx [Hy Hz]]. split.
                + have Hf2 := Hf Hmbssn.
                  have Hg := (set_lemma3 k_new alive dead al de Hknew_alive Hknew_dead Hf2).
                  set_solver.
                + set_solver.
              - intros; trivial.
          }
          iFrame "reval".
        }
        iDestruct (IH with "Hvs") as "Hvs"; trivial.
          { set_solver. }
          { rewrite <- Hsame. apply set_lemma4. set_solver. }
          { set_solver. }
          rewrite set_lemma5; trivial.
  Qed.
   
  Lemma llft_fb_new_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    (▷ llft_fb_inv alive dead blocked) ={↑Nbox}=∗ (▷ llft_fb_inv (alive ∪ {[ k ]}) dead blocked).
  Proof.
    intros Hk_fresh.
    iIntros "Inv".
    unfold llft_fb_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    
    iDestruct (llfb_fb_vs_for_new_lt alive dead blocked outlives alive dead mbs mprops k with "vs") as "vs"; trivial.
      { intuition. }
      { unfold map_wf in pures. intuition. }
      { set_solver. }
      { set_solver. }
    
    iModIntro. iNext.
    iExists mbs. iExists mprops. iExists Ptotal. iExists outlives.
    iFrame "auth".
    destruct pures as [Hdom [Hwf Hoc]].
    iSplitL "box". {
      replace (boxmap (alive ∪ {[k]}) dead mbs) with (boxmap alive dead mbs). { iFrame. }
      unfold boxmap. apply map_eq. intros sn.
      rewrite lookup_fmap. rewrite lookup_fmap.
      destruct (mbs !! sn) as [[al de|bl al de]|] eqn:Hmbssn.
      - rewrite Hmbssn. simpl. f_equiv. apply bool_decide_equiv.
        destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
        have Hf2 := Hforall sn (Borrow al de). set_solver.
      - rewrite Hmbssn. simpl. trivial.
      - rewrite Hmbssn. trivial.
    }
    iFrame "vs".
    iSplitR. { iPureIntro.
      split; trivial. split; trivial.
      apply map_wf_new_lt; trivial.
    }
    iFrame "slices". iFrame "outlives".
  Qed.
  
  Lemma outlives_consistent_preserved_on_kill outlives dead k :
      (∀ other : gset nat, (other, k) ∈ outlives → ¬ other ## dead) →
      (outlives_consistent dead outlives) →
      outlives_consistent (dead ∪ {[k]}) outlives.
  Proof.
    unfold outlives_consistent. intros Ho Hoc o Ho_in Ho2_dead.
    have Hoc2 := Hoc o. have Ho2 := Ho (o.1). set_solver.
  Qed.
  
    
  Lemma box_take_all_invalidate alive dead k mbs mprops Ptotal :
    box Nbox (boxmap alive dead mbs) Ptotal
        ∗ ([∗ map] sn↦Q ∈ mprops, slice Nbox sn Q)
    ={↑Nbox}=∗
    box Nbox (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
        ∗ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Admitted.
  
  Lemma box_put_all_revalidate alive dead k mbs mprops Ptotal :
    box Nbox (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
        ∗ ▷ full_borrows_revalidated_via alive dead k mbs mprops
        ∗ ([∗ map] sn↦Q ∈ mprops, slice Nbox sn Q)
    ={↑Nbox}=∗
    box Nbox (boxmap (alive ∖ {[k]}) (dead ∪ {[k]}) mbs) Ptotal.
  Admitted.
    
  Lemma llft_fb_kill_lt alive dead blocked outlives k :
    (k ∈ alive) →
    (k ∉ blocked) →
    (∀ other , (other, k) ∈ outlives → ¬(other ## dead)) →
    (▷ llft_fb_inv alive dead blocked) ∗ Outlives outlives ∗ Dead γ k
      ={↑Nbox}=∗ ▷ |={↑Nbox}=>
    (▷ llft_fb_inv (alive ∖ {[k]}) (dead ∪ {[k]}) blocked) ∗ Outlives outlives.
  Proof.
    intros Hk_alive Hk_not_blocked Houtlives_okay.
    iIntros "[Inv [Outlives Dead]]".
    iDestruct "Inv" as (mbs mprops Ptotal outlives') "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'.
    
    destruct pures as [Hp [Hwf Hrest]]. 
    
    iModIntro. iNext.
    
    iMod (box_take_all_invalidate alive dead k mbs mprops Ptotal with "[box]") as "[box inval]". { iFrame. iFrame "slices". }
    
    rewrite llft_fb_vs_def. iDestruct ("vs" $! k with "[Dead inval]") as "vs".
    { iFrame.
      { iPureIntro. split; trivial.
        apply outlives_consistent_preserved_on_kill; trivial. }
      (*{
        iNext. iApply borrow_sum_is_empty. intros sn bs isSo. unfold un_returned.
        destruct Hwf as [Ha [Hb [Hc Hforall]]].
        destruct bs as [|bl al de]; trivial.
        rewrite bool_decide_eq_false.
        have h := Hforall sn (Unborrow bl al de).
        set_solver.
      }*)
    }
    iMod (fupd_mask_mono ∅ (↑Nbox) with "vs") as "[reval vs]". { set_solver. }
   
    iMod (box_put_all_revalidate alive dead k mbs mprops Ptotal with "[box reval]") as "box".
      { iFrame.  iFrame "slices". }
   
    iModIntro. iSplitR "Outlives". 2: { iFrame. }
    iNext. unfold llft_fb_inv. iExists mbs. iExists mprops. iExists Ptotal.
    iExists outlives. iFrame. iFrame "slices". iPureIntro.
   
    split; trivial. split.
    { apply map_wf_preserved_on_kill; trivial. }
    { apply outlives_consistent_preserved_on_kill; trivial. }
  Qed.
   
      
    
    
End FullBorrows.



Section LlftLogic.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.

  (*** Lifetime logic ***)

  (* end hide *)
  Definition NLLFT := nroot .@ "leaf-lifetime".

  (** A Lifetime κ is defined as a [gset nat]. Though this should technically be
  an implementation detail, this makes it easy to export the basic properties of [Lifetime]
  (EqDecidable, Countable) and [⊓] (associativity, commutativity). *)
  
  Definition Lifetime := gset nat.

  Global Instance llft_intersect : Meet Lifetime := λ κ1 κ2, κ1 ∪ κ2.
  Definition llft_empty : Lifetime := ∅.
  (* begin hide *)

  Local Definition llft_alive_def (κ : Lifetime) : iProp Σ := [∗ set] k ∈ κ , Alive llft_name k.
  Local Definition llft_dead_def (κ : Lifetime) : iProp Σ := ∃ k , ⌜ k ∈ κ ⌝ ∗ Dead llft_name k.

  Local Definition llft_ctx_def :=
    (True &&{↑NLLFT}&&> ∃ sa sd , LtState llft_name sa sd ∗ llft_alive_def sa).

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
  Proof. apply pers_dead. Qed.

  (* end hide *)

  Notation "@[ κ ]" := (llft_alive κ) (format "@[ κ ]") : bi_scope.
  Notation "[† κ ]" := (llft_dead κ) (format "[† κ ]") : bi_scope.
  
  (** Lifetime inclusion is, by definition, a guard proposition. This provides us with
  an analogue of RustBelt's "dynamic lifetime inclusion": to derive new lifetime inclusions
  we can use Leaf to derive new guard propositions. *)
  
  Definition llft_incl (κ1 κ2 : Lifetime) : iProp Σ :=
      @[ κ1 ] &&{↑NLLFT}&&> @[ κ2 ].
  
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

  Lemma llftl_begin :
      llft_ctx ⊢ |={↑NLLFT}=> ∃ κ, @[ κ ] ∗ (@[ κ ] ={↑NLLFT}=∗ [† κ ]).
  Proof.
      unseal. iIntros "#ctx".  unfold llft_ctx.
      iDestruct (guards_open (True)%I _ (↑NLLFT) (↑NLLFT) with "[ctx]") as "J". { set_solver. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa sd) "[State Alive]".

      assert (∃ k , k ∉ (sa ∪ sd)) as Fres. { exists (fresh (sa ∪ sd)). apply is_fresh. }
      destruct Fres as [k Fres].
      iMod (new_lt llft_name k sa sd with "[State]") as "T".
      { set_solver. } { set_solver. } { iFrame. }
      iDestruct "T" as "[State [A1 A2]]".
      iMod ("back" with "[Alive State A1]").
      { iExists (sa ∪ {[k]}). iExists sd. iFrame.
        unfold llft_alive.
        replace ((sa ∪ {[k]})) with (({[k]} ∪ sa)).
        { unseal. rewrite big_sepS_insert. { iFrame. } set_solver. } set_solver.
      }
      iModIntro.
      iExists ({[ k ]}). unfold llft_alive. 
      rewrite big_sepS_singleton. iFrame "A2".
      iIntros "token".

      (* ending the lifetime *)
      iDestruct (guards_open (True)%I _ (↑NLLFT) (↑NLLFT) with "[ctx]") as "J". { set_solver. }
      { iFrame "ctx". }
      iMod "J" as "[J back]". iDestruct "J" as (sa1 sd1) "[State Alive]".
      iAssert (⌜k ∈ sa1⌝)%I as "%k_sa1".
      { iApply (lt_state_alive llft_name k sa1 sd1). iSplit. { iFrame "State". } iFrame "token". }
      unseal. rewrite (big_sepS_delete _ sa1 k); trivial.
      iDestruct "Alive" as "[token2 Alive]".
      iMod (kill_lt llft_name k sa1 sd1 with "[State token token2]") as "[State dead]". { iFrame. }
      iMod ("back" with "[State Alive]") as "X".
      { iExists (sa1 ∖ {[k]}). iExists (sd1 ∪ {[k]}). iFrame. }
      iModIntro. unfold llft_dead. iExists k. iFrame "dead". iPureIntro. set_solver.
  Qed.

  Lemma llftl_borrow_shared κ (P : iProp Σ) :
      ▷ P ={↑NLLFT}=∗ (@[ κ ] &&{↑NLLFT}&&> ▷ P) ∗ ([† κ ] ={↑NLLFT}=∗ ▷ P).
  Proof.
    iIntros "P".
    iMod new_cancel as (γc) "c1".
    iMod (guards_alloc_with_inv (NLLFT) (↑NLLFT) ((P ∨ (llft_dead κ ∗ Cancel γc))) with "[P]") as "[#Tinv #Tguard]".
    { iNext. iLeft. iFrame "P". }
    iModIntro.
    iSplit.
    { 
      iAssert (llft_alive κ &&{ ↑NLLFT ∪ ↑NLLFT }&&> ▷ P) as "H".
      { iApply
        (guards_cancel_or (llft_alive κ) (llft_alive κ) (llft_dead κ ∗ Cancel γc) (▷ P)).
        { iIntros "t". iApply (llftl_not_own_end_and κ). iSplit.
          { iDestruct "t" as "[t _]". iFrame "t". }
          { iDestruct "t" as "[_ [t _]]". iFrame "t". }
        }
        iSplit. { iApply guards_refl. }
        { setoid_replace (llft_dead κ ∗ Cancel γc ∨ ▷ P)%I
            with (▷ P ∨ llft_dead κ ∗ Cancel γc)%I.
          { iDestruct (guards_true (↑NLLFT) (llft_alive κ)) as "gt".
            iDestruct (guards_transitive (↑NLLFT) (llft_alive κ)%I with "[gt Tguard]") as "J".
            { iFrame "Tguard". iFrame "gt". }
            rewrite bi.later_or.
            iDestruct (guards_remove_later_or_r (llft_dead κ ∗ Cancel γc) (▷ P) (↑NLLFT)) as "X".
            iDestruct (guards_transitive (↑NLLFT) (llft_alive κ)%I with "[J X]") as "R".
            { iFrame "J". iFrame "X". }
            iFrame "R".
          }
          rewrite bi.or_comm. trivial.
        }
      }
      rewrite subseteq_union_1_L. { iFrame "H". } set_solver.
    }
    iIntros "deadk".
    iDestruct (guards_open (True)%I (▷ (P ∨ llft_dead κ ∗ Cancel γc))%I (↑ NLLFT) (↑ NLLFT) with "[Tguard]") as "J". { set_solver. }
    { iFrame "Tguard". }
    iMod "J" as "[J K]". rewrite bi.later_or. iDestruct "J" as "[P|J]".
    { iDestruct ("K" with "[deadk c1]") as "K". { iRight. iFrame. }
        iMod "K" as "K". iModIntro. iFrame "P". }
    iDestruct "J" as "[_ c2]". iMod "c2".
    iDestruct (cancel_cancel_false γc with "[c1 c2]") as "J". { iFrame. } iExFalso. iFrame "J".
  Qed.

  Lemma llftl_incl_dead_implies_dead κ κ' :
      ⊢ llft_ctx ∗ κ ⊑ κ' ∗ [† κ' ] ={↑NLLFT}=∗ [† κ ].
  Proof.
    iIntros "[#ctx [#incl #dead]]". unseal.

    unfold llft_incl.

    leaf_hyp "incl" rhs to (False)%I as "G2".
    {
      leaf_by_sep. iIntros "a". iExFalso.
      iApply (llftl_not_own_end κ'). iFrame. unseal. iFrame "dead".
    }
    unfold llft_ctx.
    leaf_hyp "ctx" rhs to ((∃ sa sd : gset nat, ⌜ κ ⊆ sa ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa)
        ∨ (∃ sa sd : gset nat, ⌜ ¬(κ ⊆ sa) ⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa) )%I
        as "ctx2".
    {
      leaf_by_sep. iIntros "T". iSplitL.
        - iDestruct "T" as (sa sd) "state_alive".
          have h : Decision (κ ⊆ sa) by solve_decision. destruct h as [h|n]; trivial.
          + unseal. iLeft. iExists sa. iExists sd. iFrame. iPureIntro. trivial.
          + unseal. iRight. iExists sa. iExists sd. iFrame. iPureIntro. trivial.
        - iIntros "T". iDestruct "T" as "[T|T]".
          + iDestruct "T" as (sa sd) "[_ T]". iExists sa. iExists sd. unseal. iFrame.
          + iDestruct "T" as (sa sd) "[_ T]". iExists sa. iExists sd. unseal. iFrame.
      }

      iAssert (True &&{ ↑NLLFT}&&> (∃ sa sd : gset nat, ⌜κ ⊈ sa⌝ ∗ LtState llft_name sa sd ∗ llft_alive sa)) as "G3".
        { iApply guards_cancel_or_by_chaining. iFrame "ctx2". 
          leaf_goal rhs to (llft_alive κ). { iFrame "G2". }
          leaf_by_sep.
          { iIntros "T". 
              iDestruct "T" as (sa sd) "[%ksa [state alive]]".
                unseal. unfold llft_alive_def.
                replace sa with (κ ∪ (sa ∖ κ)) at 2.
                { setoid_rewrite big_sepS_union.
                  { iDestruct "alive" as "[alive1 alive2]". iFrame "alive1".
                    iIntros "rest".
                    iExists sa. iExists sd. iFrame.
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

      iDestruct "J" as (sa sd) "[%k_sa [State alive]]".
      have the_k := not_subset_eq_get κ sa k_sa. destruct the_k as [k [k_in k_not_in]].
      have h : Decision (k ∈ sd) by solve_decision. destruct h as [h|n]; trivial.
        - iDestruct (LtState_entails_Dead llft_name k sa sd with "State") as "#deadk"; trivial.
          iMod ("back" with "[State alive]") as "true". { iExists sa. iExists sd. iFrame. iPureIntro; trivial. } iModIntro. unfold llft_dead. iExists k. iFrame "deadk". iPureIntro. apply k_in.
        - (* weird technicality, if k was never made alive in the first place;
            first create it, then immediately kill it *)
          iMod (new_lt llft_name k sa sd with "State") as "[State [al1 al2]]"; trivial.
          iMod (kill_lt llft_name k (sa ∪ {[ k ]}) sd with "[State al1 al2]") as "[State deadk]".
            { iFrame. }
          iMod ("back" with "[State alive]") as "J".
          { iExists sa. iExists (sd ∪ {[k]}). iFrame.
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
