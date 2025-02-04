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

(* This is the invariant part of the lifetime logic that's relevant for *full borrows*
(and indexed borrows).
*)

(* Namespaces: Nllft and NllftG are the masks that are part of the "public" interface.

NllftG has 2 important sub-namespaces, Nmain, which is the main invariant goes,
and Nbox, which is where box stuff goes. We want Nbox to be part of NllftG so we can
guard on stuff that is borrowed.

NlltfO is for the part of the invariant that needs to be _outside_ NllftG.
(See the explanation on outer_inv below.)
*)

Definition Nllft       : namespace := nroot .@ "leaf_lifetime_logic".
Definition NllftG      : namespace := nroot .@ "leaf_lifetime_logic" .@ "guarding".

Definition NllftO      : namespace := nroot .@ "leaf_lifetime_logic" .@ "other".
Definition Nmain       : namespace := NllftG .@ "main".
Definition Nbox        : namespace := NllftG .@ "box".

Section FullBorrows.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGpreS Σ}.
  Context `{!invGS_gen hlc Σ}.
  
  Context (γ: gname).
  Context (γo: gname).
  Context (γd: gname).
      
  Definition boxmap
      (alive dead : gset nat) (m: gmap_bor_state)
        : gmap slice_name bool :=
      (λ bs , match bs with
        | Borrow al de => bool_decide (al ⊆ alive ∧ ¬(de ## dead))
        | Unborrow _ _ _ => false
      end) <$> m.
      
  (* (A, B) means A must end before B
      A alive ==> B alive
      B dead ==> A dead
  *)
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
    ∧ (∀ o , o ∈ outlives → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead)
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
    intros Hal Hblalive Hde Hdewf Hbl Ho [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]]. 
      split; trivial.
      split. { set_solver. }
      split; trivial.
      split. {
        intros sn' bs'. destruct (decide (sn = sn')).
        + intros Hmbssn'. subst sn'. rewrite lookup_insert in Hmbssn'. inversion Hmbssn'.
          split. { set_solver. } split; trivial. split; trivial. set_solver.
        + intros Hmbssn'. rewrite lookup_insert_ne in Hmbssn'; trivial.
          have Hfa := Hf1 sn' bs' Hmbssn'. destruct bs'; trivial. set_solver.
      }
      split. {
      intros sn1 bs1 sn2 bs2. destruct (decide (sn = sn1)).
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
      }
      trivial.
  Qed.
  
  Lemma map_wf_delete_unborrow alive dead blocked bl al de outlives mbs sn :
    (al ⊆ alive) →
    (bl ⊆ blocked) →
    (mbs !! sn = Some (Unborrow bl al de)) →
    map_wf alive dead blocked outlives mbs →
    map_wf alive dead (blocked ∖ bl) outlives (delete sn mbs).
  Proof.
    unfold map_wf.
    intros Hal Hbl Hmbssn [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]]. 
      split; trivial.
      split. { set_solver. }
      split; trivial.
      split. {
      intros sn' bs' Hdel. destruct (decide (sn = sn')).
        + subst sn'. rewrite lookup_delete in Hdel. discriminate.
        + rewrite lookup_delete_ne in Hdel; trivial.
          have Hfa := Hf1 sn' bs'. destruct bs'; intuition. set_solver.
      }
      split. {
        intros sn1 bs1 sn2 bs2 Hne Hdel1 Hdel2. 
      
        destruct (decide (sn = sn1)). { subst sn1. rewrite lookup_delete in Hdel1. discriminate. }
        destruct (decide (sn = sn2)). { subst sn2. rewrite lookup_delete in Hdel2. discriminate. }
        rewrite lookup_delete_ne in Hdel1; trivial.
        rewrite lookup_delete_ne in Hdel2; trivial.
        apply (Hf2 sn1 bs1 sn2 bs2); trivial.
      }
      trivial.
  Qed.
    
  Lemma map_wf_insert
      (alive dead blocked : gset nat) (outlives : outlives_set) (m: gmap_bor_state) sn al de :
    map_wf alive dead blocked outlives m →
    (al ∪ de) ⊆ (alive ∪ dead) →
    map_wf alive dead blocked outlives (<[sn:=Borrow al de]> m).
  Proof.
    unfold map_wf. intros [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]] Halde. 
    split; trivial.
    split; trivial.
    split; trivial.
    split. {
      intros sn' bs'. destruct (decide (sn = sn')).
      + subst sn'. intros Hsn. rewrite lookup_insert in Hsn. inversion Hsn. trivial.
      + rewrite lookup_insert_ne; trivial. intros Hsn'.
        apply (Hf1 sn' bs' Hsn').
    }
    split. {
      intros sn1 bs1 sn2 bs2. destruct (decide (sn = sn1)).
      + subst sn1. intros Hne Hsn1 Hsn2. rewrite lookup_insert in Hsn1. inversion Hsn1. trivial.
      + destruct (decide (sn = sn2)).
      - subst sn2. intros Hne Hsn1 Hsn2. rewrite lookup_insert in Hsn2. inversion Hsn2. destruct bs1; trivial.
      - intros Hne Hsn1 Hsn2. 
        rewrite lookup_insert_ne in Hsn1; trivial.
        rewrite lookup_insert_ne in Hsn2; trivial.
        apply (Hf2 sn1 bs1 sn2 bs2 Hne Hsn1 Hsn2).
    }
    - trivial.
  Qed.
  
  Lemma map_wf_delete
      (alive dead blocked : gset nat) (outlives : outlives_set) (m: gmap_bor_state) sn :
    map_wf alive dead blocked outlives m →
    map_wf alive dead blocked outlives (delete sn m).
  Proof.
    unfold map_wf. intros [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]].
    split; trivial.
    split; trivial.
    split; trivial.
    split. {
      intros sn' bs'. destruct (decide (sn = sn')).
      + subst sn'. intros Hsn. rewrite lookup_delete in Hsn. discriminate.
      + rewrite lookup_delete_ne; trivial. intros Hsn'.
        apply (Hf1 sn' bs' Hsn').
    }
    split. {
      intros sn1 bs1 sn2 bs2. destruct (decide (sn = sn1)).
      + subst sn1. intros Hne Hsn1 Hsn2. rewrite lookup_delete in Hsn1. discriminate.
      + destruct (decide (sn = sn2)).
      - subst sn2. intros Hne Hsn1 Hsn2. rewrite lookup_delete in Hsn2. discriminate.
      - intros Hne Hsn1 Hsn2. 
        rewrite lookup_delete_ne in Hsn1; trivial.
        rewrite lookup_delete_ne in Hsn2; trivial.
        apply (Hf2 sn1 bs1 sn2 bs2 Hne Hsn1 Hsn2).
    }
    - trivial.
  Qed.
   
  Lemma map_wf_new_lt alive dead blocked outlives mbs k :
    (k ∉ alive ∪ dead) →
    map_wf alive dead blocked outlives mbs →
    map_wf (alive ∪ {[k]}) dead blocked outlives mbs.
  Proof.
    unfold map_wf. intros Hk [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]].
    split. { set_solver. }
    split. { set_solver. }
    split; trivial.
    split. {
      intros sn bs Hsn. have Hf := Hf1 sn bs Hsn. destruct bs; set_solver.
    }
    split. { trivial. }
    intros o. have Hf := Hf3 o. set_solver.
  Qed.
  
  Lemma map_wf_new_lt_dead alive dead blocked outlives mbs k :
    (k ∉ alive ∪ dead) →
    map_wf alive dead blocked outlives mbs →
    map_wf alive (dead ∪ {[k]}) blocked outlives mbs.
  Proof.
    unfold map_wf. intros Hk [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]].
    split. { set_solver. }
    split. { trivial. }
    split. { set_solver. }
    split. {
      intros sn bs Hsn. have Hf := Hf1 sn bs Hsn. destruct bs; set_solver.
    }
    split. { trivial. }
    intros o. have Hf := Hf3 o. set_solver.
  Qed.
  
  Lemma map_wf_preserved_on_kill alive dead blocked outlives k mbs :
    (k ∉ blocked) →
    map_wf alive dead blocked outlives mbs →
    map_wf (alive ∖ {[k]}) (dead ∪ {[k]}) blocked outlives mbs.
  Proof.
    unfold map_wf. intros H [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
    split. { set_solver. } split. { set_solver. } split. { set_solver. }
    split. {
    intros sn bs Hso. have Hdx := Hforall sn bs Hso. destruct bs as [al de|bl al de].
    - intro k'. destruct (decide (k = k')); set_solver.
    - destruct Hdx as [He [Hf [Hg Hi]]]. split; trivial. split. { set_solver. }
      split; trivial.
      intro k'. destruct (decide (k = k')); set_solver.
    }
    split. { trivial. }
    intros o Ho. have Hf := Hforall3 o Ho. split.
      - intro o2. destruct (decide (o2 = k)); set_solver.
      - destruct (decide (o.2 = k)); set_solver.
  Qed.

  Definition borrow_sum (f: BorState → bool) (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ := [∗ map] sn ↦ bs ∈ m ,
    match (f bs, mprops !! sn) with
      | (true, Some P) => P
      | _ => True%I
    end.
  
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
      ⊢ borrow_sum f m mprops.
  Proof.
    intros Hf. iIntros. iApply big_sepM_intro. iModIntro. iIntros (sn bs) "%Hsn".
    destruct (f bs) eqn:Hfbs; last by done.
    destruct (mprops !! sn) eqn:Hmprops; last by done.
    rewrite (Hf sn bs Hsn) in Hfbs. discriminate.
  Qed.
      
  Lemma borrow_sum_equiv f f' m mprops
      : (∀ i x , m !! i = Some x → f x = true → f' x = true) →
      borrow_sum f' m mprops ⊢ borrow_sum f m mprops.
  Proof.
      intros Hf. iIntros "H". iDestruct (big_sepM_impl with "H []") as "H".
      2: { iFrame "H". }
      iModIntro. iIntros (sn bs) "%Hsn R".
      destruct (f bs) eqn:Hfbs; last by done.
      destruct (f' bs) eqn:Hf'bs; first by iFrame.
      iExFalso. rewrite (Hf sn bs Hsn Hfbs) in Hf'bs. discriminate.
  Qed.
  
  (* I think this is similar in spirit to the LftVs definition in RustBelt
     (https://plv.mpi-sws.org/rustbelt/popl18/appendix.pdf, Section 4.3)
     
     The idea is basically: when an Unborrow ends, instead of returning P, you're allowed
     to return some Q that can view-shift back to P. Thus we need to maintain all these
     view shifts somewhere in the invariant. The idea for defining this is basically to say,
     "for any possible future ordering sequence of lifetime expirations, we have the view
     shifts that we need".
     
     Note that `Dead γ k` appears on the LHS of the view shift. This is useful for two reasons:
      - Because [†κ] appears in llftl_bor_acc
      - Because it's needed for unnest
  *)
  
  Fixpoint future_vs' (fuel: nat) (alive dead : gset nat) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
  match fuel with
    | 0 => True
    | S fuel' =>
      (∀ (k: nat),
        ⌜k ∈ alive ∧ outlives_consistent (dead ∪ {[k]}) outlives⌝ ∗ Dead γ k ∗
          ▷ (full_borrows_invalidated_via alive dead k m mprops)
        ={∅}=∗ ▷ (full_borrows_revalidated_via alive dead k m mprops)
            ∗ future_vs' fuel' (alive ∖ {[k]}) (dead ∪ {[k]}) outlives m mprops)
  end.
      
  Definition future_vs (alive dead : gset nat) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) : iProp Σ :=
    future_vs' (size alive) alive dead outlives m mprops.
      
  Lemma future_vs_def (alive dead : gset nat) (outlives: outlives_set) 
      (m: gmap_bor_state) (mprops: gmap_props Σ) :
    future_vs alive dead outlives m mprops ⊣⊢
    ∀ (k: nat),
      ⌜k ∈ alive ∧ outlives_consistent (dead ∪ {[k]}) outlives⌝ ∗ Dead γ k ∗
        ▷ (full_borrows_invalidated_via alive dead k m mprops)
      ={∅}=∗ ▷ (full_borrows_revalidated_via alive dead k m mprops)
           ∗ future_vs (alive ∖ {[k]}) (dead ∪ {[k]}) outlives m mprops.
  Proof.
    unfold future_vs.
    destruct (size alive) eqn:Heqn.
    - iSplit.
      + iIntros "H". iIntros (k). iIntros "[%Hk_in_alive _]".
      exfalso. rewrite size_empty_iff in Heqn. set_solver.
      + iIntros "H". unfold future_vs'. done.
    - iSplit.
      + iIntros "H" (k). iIntros "[%Hk X]".
        rewrite size_difference; last by set_solver.
        rewrite size_singleton. replace (size alive - 1) with n by lia.
        iApply "H". iFrame. iPureIntro. trivial.
      + iIntros "H" (k). iIntros "[%Hk X]".
        iDestruct ("H" $! (k)) as "H".
        rewrite size_difference; last by set_solver.
        rewrite size_singleton. replace (size alive - 1) with n by lia.
        iApply "H". iFrame. iPureIntro. trivial.
  Qed.
  
  Lemma set_ind_strong `{FinSet A C} `{!LeibnizEquiv C} (P : C → Prop) :
  (∀ X , (∀ x , x ∈ X → P (X ∖ {[ x ]})) → P X) → ∀ X, P X.
  Proof.
    intros Hind. 
    enough (∀ n Y , size Y = n → P Y) as Hall. {
      intros X. apply (Hall (set_size X)). trivial.
    }
    induction n.
     - intros Y. intros Heq0. rewrite size_empty_iff in Heq0.
       apply Hind. intros x. set_solver.
     - intros Y. intros HeqSn. apply Hind. intros x Hxy. apply IHn.
       rewrite size_difference; last by set_solver.
       rewrite HeqSn. rewrite size_singleton. lia.
  Qed.
  
  Lemma borrow_sum_insert f sn bs P mbs mprops :
      mbs !! sn = None →
      ▷ borrow_sum f (<[sn:=bs]> mbs) (<[sn:=P]> mprops)
      ⊢ ▷ ((if f bs then P else True) ∗ borrow_sum f mbs mprops).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite big_sepM_insert; trivial. iIntros "[H J]".
    iSplitL "H".
    - destruct (f bs) eqn:Hfbs; last by trivial. rewrite lookup_insert. iFrame.
    - iApply big_sepM_mono; last by iFrame "J". intros sn' bs' Hsn'. simpl.
      rewrite lookup_insert_ne; first by trivial. intros Heq. subst sn'.
      rewrite Hmbs in Hsn'. discriminate.
  Qed.
  
  Lemma borrow_sum_delete (f : BorState → bool) sn bs P mbs mprops :
      (mbs !! sn = Some bs) →
      ▷ (if f bs then mprops !! sn ≡ Some P else True)
      ∗ ▷ borrow_sum f (delete sn mbs) (delete sn mprops)
      ∗ ▷ (if f bs then P else True)
      ⊢  ▷ borrow_sum f mbs mprops.
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite (big_sepM_delete _ mbs); last by apply Hmbs.
    iIntros "[#Eq [H P]]". iNext. iSplitL "P".
    - destruct (f bs) eqn:Hfbs; last by trivial. rewrite option_equivI.
      destruct (mprops !! sn); trivial. iRewrite "Eq". iFrame.
    - iApply big_sepM_mono; last by iFrame "H". intros sn' bs' Hsn'. simpl.
      rewrite lookup_delete_ne; first by trivial. intros Heq. subst sn'.
      rewrite lookup_delete in Hsn'. discriminate.
  Qed.
  
  Lemma borrow_sum_insert_2 (f : BorState → bool) sn bs P mbs mprops :
      mbs !! sn = None →
      ▷ ((if f bs then P else True) ∗ borrow_sum f mbs mprops)
      ⊢ ▷ borrow_sum f (<[sn:=bs]> mbs) (<[sn:=P]> mprops).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite big_sepM_insert; trivial. iIntros "[H J]".
    iSplitL "H".
    - destruct (f bs) eqn:Hfbs; last by trivial. rewrite lookup_insert. iFrame.
    - iApply big_sepM_mono; last by iFrame "J". intros sn' bs' Hsn'. simpl.
      rewrite lookup_insert_ne; first by trivial. intros Heq. subst sn'.
      rewrite Hmbs in Hsn'. discriminate.
  Qed.
  
  Lemma borrow_sum_delete_2 (f : BorState → bool) sn bs P mbs mprops :
      (mbs !! sn = Some bs) →
      ▷ (if f bs then mprops !! sn ≡ Some P else True)
      ∗ ▷ borrow_sum f mbs mprops
      ⊢ ▷ borrow_sum f (delete sn mbs) (delete sn mprops)
      ∗ ▷ (if f bs then P else True).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite (big_sepM_delete _ mbs); last by apply Hmbs.
    iIntros "[#Eq [H P]]". iSplitL "P".
    - iNext. iApply big_sepM_mono; last by iFrame "P". intros sn' bs' Hsn'. simpl.
      rewrite lookup_delete_ne; first by trivial. intros Heq. subst sn'.
      rewrite lookup_delete in Hsn'. discriminate.
    - iNext. destruct (f bs) eqn:Hfbs; last by trivial. rewrite option_equivI.
      destruct (mprops !! sn); trivial. iRewrite "Eq" in "H". iFrame.
  Qed.
  
  Lemma borrow_sum_delete_3 (f : BorState → bool) sn bs  mbs mprops :
      (mbs !! sn = Some bs) →
      ▷ borrow_sum f mbs mprops
      ⊢ ▷ borrow_sum f (delete sn mbs) (delete sn mprops).
  Proof.
    intros Hmbs. unfold borrow_sum. rewrite (big_sepM_delete _ mbs); last by apply Hmbs.
    iIntros "[H P]".
    iNext. iApply big_sepM_mono; last by iFrame "P". intros sn' bs' Hsn'. simpl.
    rewrite lookup_delete_ne; first by trivial. intros Heq. subst sn'.
    rewrite lookup_delete in Hsn'. discriminate.
  Qed.
  
  Lemma full_borrows_invalidated_via_insert alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      invalidated alive dead k bs = true →
      ▷ (full_borrows_invalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops))
      ⊢ ▷ (P ∗ full_borrows_invalidated_via alive dead k mbs mprops).
  Proof.
      intros Hsn Hinv. iIntros "H".
      iDestruct (borrow_sum_insert with "H") as "H"; trivial. rewrite Hinv. iFrame.
  Qed.
      
  Lemma full_borrows_invalidated_via_insert_false alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      ▷ (full_borrows_invalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops))
      ⊢ ▷ (full_borrows_invalidated_via alive dead k mbs mprops).
  Proof.
      intros Hsn. iIntros "H".
      iDestruct (borrow_sum_insert with "H") as "[b H]"; trivial.
  Qed.
      
  Lemma full_borrows_invalidated_via_delete alive dead k sn mbs mprops bs P :
      (mbs !! sn = Some bs) →
      ▷ (mprops !! sn ≡ Some P)
        ∗ ▷ (full_borrows_invalidated_via alive dead k (delete sn mbs) (delete sn mprops))
        ∗ ▷ P
      ⊢ 
      ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
      intros Hsn. iIntros "[#Heq [H P]]".
      iDestruct (borrow_sum_delete with "[H P]") as "H"; trivial. { apply Hsn. }
        { destruct (invalidated alive dead k bs); trivial; iFrame; iFrame "#".
            iSplitL; iNext; trivial. }
  Qed.
      
  Lemma full_borrows_invalidated_via_delete_false alive dead k sn mbs mprops bs :
      (mbs !! sn = Some bs) →
      invalidated alive dead k bs = false →
      ▷ (full_borrows_invalidated_via alive dead k (delete sn mbs) (delete sn mprops))
      ⊢ 
      ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
      intros Hsn Hinv. iIntros "H".
      iDestruct (borrow_sum_delete _ _ _ True%I with "[H]") as "H"; trivial. { apply Hsn. }
        { rewrite Hinv. iFrame. iSplit; iNext; trivial. }
  Qed.
      
  Lemma full_borrows_revalidated_via_insert alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      ▷ (full_borrows_revalidated_via alive dead k mbs mprops)
      ∗ ▷ P
      ⊢
      ▷ (full_borrows_revalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops)).
  Proof.
      intros Hsn. iIntros "[H P]".
      iDestruct (borrow_sum_insert_2 with "[H P]") as "H"; trivial. { apply Hsn. }
      destruct (revalidated alive dead k bs) eqn:Heq; iFrame.
  Qed.
      
  Lemma full_borrows_revalidated_via_insert_false alive dead k sn mbs mprops bs P :
      mbs !! sn = None →
      revalidated alive dead k bs = false →
      ▷ (full_borrows_revalidated_via alive dead k mbs mprops)
      ⊢
      ▷ (full_borrows_revalidated_via alive dead k (<[sn := bs]> mbs) (<[ sn := P ]> mprops)).
  Proof.
      intros Hsn Hfalse. iIntros "H". unfold full_borrows_revalidated_via.
      iDestruct (borrow_sum_insert_2 with "[H]") as "H". { apply Hsn. }
      2: { iFrame "H". } rewrite Hfalse. iFrame.
  Qed.
 
  Lemma full_borrows_revalidated_via_delete alive dead k sn mbs mprops bs P :
      mbs !! sn = Some bs →
      revalidated alive dead k bs = true →
      ▷ (mprops !! sn ≡ Some P)
      ∗  ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢
        ▷ (full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops))
      ∗ ▷ P.
  Proof.
      intros Hsn Hinv. iIntros "[#Heq H]".
      iDestruct (borrow_sum_delete_2 _ _ _ P with "[H]") as "[H P]"; trivial. { apply Hsn. }
        { iFrame "H". rewrite Hinv. iFrame. iFrame "#". }
        rewrite Hinv. iFrame.
  Qed.
 
  Lemma full_borrows_revalidated_via_delete_false alive dead k sn mbs mprops bs :
      mbs !! sn = Some bs →
        ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢
        ▷ (full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops)).
  Proof.
      intros Hsn. iIntros "H".
      iDestruct (borrow_sum_delete_3 _ _ _ with "[H]") as "H"; trivial. { apply Hsn. }
  Qed.
 
  Lemma full_borrows_delete_insert_same alive dead k sn mbs mprops bs bs' P :
      (invalidated alive dead k bs = true → invalidated alive dead k bs' = true) →
      mbs !! sn = Some bs →
        ▷ (full_borrows_invalidated_via alive dead k 
            (<[sn := bs']> (delete sn mbs)) (<[sn := P]> (delete sn mprops)))
      ∗ ▷ (mprops !! sn ≡ Some P)
      ⊢ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof using invGS_gen0 Σ γ.
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
      
  Definition inner_inv (alive dead blocked : gset nat) : iProp Σ :=
    ∃ (mbs: gmap_bor_state) (mprops: gmap_props Σ) Ptotal (outlives: outlives_set),
        AuthBorState γ mbs
          ∗ box Nbox (boxmap alive dead mbs) Ptotal
          ∗ future_vs alive dead outlives mbs mprops
          ∗ ⌜dom mbs = dom mprops
              ∧ map_wf alive dead blocked outlives mbs
              ∧ outlives_consistent dead outlives
             ⌝
          ∗ ([∗ map] sn ↦ Q ∈ mprops, slice Nbox sn Q)
          ∗ Outlives γo outlives.
          
          (*
          ∗ ([∗ set] o ∈ outlives, ([∗ set] k ∈ o.1, Alive γ k) &&{↑Nllft}&&> Dead γ o.2).
          *)
          
  Lemma inner_fake (alive dead blocked al de : gset nat) Q :
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
  Proof.
      intros Hdel. destruct (decide (sn1 = sn2)).
      - subst sn2. rewrite lookup_delete. trivial.
      - unfold boxmap in Hdel. rewrite lookup_delete_ne in Hdel; trivial.
        rewrite lookup_fmap in Hdel. rewrite lookup_delete_ne; trivial.
        destruct (mbs !! sn2) eqn:Hmbs; rewrite Hmbs; trivial. rewrite Hmbs in Hdel.
        discriminate.
  Qed.
  
  Lemma lookup_insert_delete_boxmap_helper sn sn' sn2 alive dead mbs bs :
      <[sn:=false]> (delete sn' (boxmap alive dead mbs)) !! sn2 = None →
      <[sn:=bs]> (delete sn' mbs) !! sn2 = None.
  Proof.
      destruct (<[sn:=bs]> (delete sn' mbs) !! sn2) eqn:Heq; trivial.
      intros Ha. exfalso. unfold boxmap in Ha. destruct (decide (sn = sn2)).
      - subst sn2. rewrite lookup_insert in Ha. discriminate.
      - rewrite lookup_insert_ne in Ha; trivial.
        rewrite lookup_insert_ne in Heq; trivial. destruct (decide (sn' = sn2)).
          + subst sn2. rewrite lookup_delete in Heq. discriminate.
          + rewrite lookup_delete_ne in Ha; trivial.
            rewrite lookup_delete_ne in Heq; trivial.
            rewrite lookup_fmap in Ha. rewrite Heq in Ha. discriminate.
  Qed.
      
  Lemma lookup_insert_delete_boxmap_helper2 sn sn' sn2 alive dead mbs  :
      <[sn:=false]> (delete sn' (boxmap alive dead mbs)) !! sn2 = None →
      (delete sn' mbs) !! sn2 = None.
  Proof.
      intros Ha. destruct (decide (sn2 = sn')).
      - subst sn'. apply lookup_delete.
      - destruct (decide (sn = sn2)).
        + subst sn2. rewrite lookup_insert in Ha. discriminate.
        + rewrite lookup_insert_ne in Ha; trivial. destruct (decide (sn' = sn2)); trivial.
          * subst sn'. rewrite lookup_delete; trivial.
          * rewrite lookup_delete_ne in Ha; trivial. rewrite lookup_delete_ne; trivial.
            unfold boxmap in Ha. rewrite lookup_fmap in Ha.
            destruct (mbs !! sn2) eqn:Heq; trivial. exfalso. rewrite Heq in Ha. discriminate.
  Qed.
      
  Lemma lookup_insert_boxmap_helper3 sn b alive dead mbs sn2 :
    <[sn:=b]> (boxmap alive dead mbs) !! sn2 = None →
    mbs !! sn2 = None ∧ sn ≠ sn2.
  Proof.
    intros Ha. assert (sn ≠ sn2) as Hne.
        { intros Heq. subst sn2. rewrite lookup_insert in Ha. discriminate. }
    split; trivial. rewrite lookup_insert_ne in Ha; trivial.
    unfold boxmap in Ha. rewrite lookup_fmap in Ha.
    destruct (mbs !! sn2) eqn:Heq; trivial. exfalso. rewrite Heq in Ha. discriminate.
  Qed.
  
  Lemma delete_delete_boxmap_helper4 sn sn1 sn2 alive dead mbs :
    delete sn2 (delete sn1 (boxmap alive dead mbs)) !! sn = None →
    delete sn2 (delete sn1 mbs) !! sn = None.
  Proof.
    intro Hx.
    destruct (decide (sn2 = sn)). { subst sn2. rewrite lookup_delete. trivial. }
    rewrite lookup_delete_ne; trivial.
    rewrite lookup_delete_ne in Hx; trivial.
    destruct (decide (sn1 = sn)). { subst sn1. rewrite lookup_delete. trivial. }
    rewrite lookup_delete_ne; trivial.
    rewrite lookup_delete_ne in Hx; trivial.
    unfold boxmap in Hx. rewrite lookup_fmap in Hx.
    destruct (mbs !! sn) eqn:Hmbs; trivial.
    rewrite Hmbs in Hx. discriminate.
  Qed.
      
  Lemma boxmap_insert_Borrow alive dead sn al de mbs
    : boxmap alive dead (<[ sn := Borrow al de ]> mbs)
      = <[ sn := bool_decide (al ⊆ alive ∧ ¬(de ## dead)) ]> (boxmap alive dead mbs).
  Proof.
    unfold boxmap. rewrite fmap_insert. trivial.
  Qed.
  
  Lemma boxmap_insert_Unborrow alive dead sn bl al de mbs
    : boxmap alive dead (<[ sn := Unborrow bl al de ]> mbs)
      = <[ sn := false ]> (boxmap alive dead mbs).
  Proof.
    unfold boxmap. rewrite fmap_insert. trivial.
  Qed.
       
  Lemma boxmap_delete alive dead sn mbs
      : boxmap alive dead (delete sn mbs)
        = delete sn (boxmap alive dead mbs).
  Proof.
    unfold boxmap. rewrite fmap_delete. trivial.
  Qed.
  
  Lemma agree_slice sn P Q :
    slice Nbox sn P -∗
    slice Nbox sn Q -∗
    ▷ (Some Q ≡ Some P).
  Proof.
    unfold slice. iIntros "[s1 _] [s2 _]".
    iDestruct (box_own_agree sn P Q with "[s1 s2]") as "X". { iFrame. }
    iNext. iRewrite "X". trivial.
  Qed.
  
  Lemma agree_slice_with_map (mbs : gmap_bor_state) (mprops : gmap_props Σ) sn bs P :
      dom mbs = dom mprops →
      mbs !! sn = Some bs →
      slice Nbox sn P ∗ ([∗ map] sn0↦Q0 ∈ mprops, slice Nbox sn0 Q0)
        ⊢ ▷ (mprops !! sn ≡ Some P).
  Proof using invGS_gen0 llft_logicGpreS0 Σ γ γd γo.
    intros Hdom Hmbssn. iIntros "[#s1 #smap]".
    destruct (mprops !! sn) as [Q|] eqn:Hmpropssn.
    - rewrite (big_sepM_delete _ _ sn Q); trivial. iDestruct "smap" as "[s2 _]".
      iApply agree_slice; iFrame "#".
    - exfalso.
      assert (sn ∈ dom mbs) as X. { apply elem_of_dom. exists bs. trivial. }
      assert (sn ∉ dom mprops) as Y. { rewrite not_elem_of_dom. trivial. }
      rewrite Hdom in X. contradiction.
  Qed.
  
  Local Instance pers_dead3 k : Persistent (Dead γ k).
  Proof.
    apply own_core_persistent. unfold CoreId. trivial.
  Qed.
  
  Lemma big_sepM_insert_1 `{Countable K} {A : Type} (Φ : K → A → iProp Σ) (m : gmap K A) i x :
    (Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y)%I ⊢ ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y).
  Proof.
    rewrite big_sepM_insert_delete.
    iIntros "[Phi Op]". iFrame. iDestruct (big_sepM_subseteq with "Op") as "Op";
        last by iFrame "Op". apply delete_subseteq.
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
  Proof using invGS_gen0 Σ γ.
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
  Proof using invGS_gen0 Σ γ.
    intros Hsn1 Hsn2 Hne Hmbssn. iIntros "[#Heq inval]".
    destruct (revalidated alive dead k bs) eqn:Hinvbool.
    - iAssert (▷ full_borrows_revalidated_via alive dead k (delete sn mbs) (delete sn mprops)
        ∗ ▷ (P ∗ Q))%I with "[inval]" as "[inval [P Q]]".
        { iApply full_borrows_revalidated_via_delete. { apply Hmbssn. } { trivial. } iFrame. iFrame "#". }
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
    (future_vs alive dead outlives mbs mprops
        ∗ ▷ (mprops !! sn ≡ Some (P ∗ Q)))
    ⊢
      future_vs alive dead outlives
        (<[sn2:=Borrow al de]> (<[sn1:=Borrow al de]> (delete sn mbs)))
        (<[sn2:=Q]> (<[sn1:=P]> (delete sn mprops))).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hdel1 Hdel2 Hne Hmbssn. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead) "[Hvs #Heq]".
    rewrite future_vs_def.
    rewrite (future_vs_def _ _ _ (<[sn2:=Borrow al de]> (<[sn1:=Borrow al de]> (delete sn mbs)))).
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
            
  Lemma inner_split alive dead blocked sn al de P Q :
    (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead
      ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn (P ∗ Q)
      ⊢ |={↑Nbox}=> ∃ sn1 sn2, (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn1 P ∗ slice Nbox sn2 Q.
  Proof using invGS_gen0 Σ γ γd γo.
    iIntros "[Inv [LtState [OwnBor #slice]]]".
    destruct (decide (al ## dead)) as [Hdisj|Hnot_disj].
    2: {
      iMod (inner_fake alive dead blocked al de P Hnot_disj with "LtState")
          as (sn1) "[LtState [Ob2 Slice2]]".
      iMod (inner_fake alive dead blocked al de Q Hnot_disj with "LtState")
          as (sn2) "[LtState [Ob3 Slice3]]".
      iModIntro. iExists sn1. iExists sn2. iFrame.
    }
    unfold inner_inv.
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
      
    iMod (delete_bor_state_borrow_lts γ sn mbs alive dead al de Hdisj with 
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
       
  Lemma full_borrows_invalidated_preserved_in_join
    sn1 sn2 sn mbs mprops P Q alive dead k al de de1' de2'
    :
      (delete sn2 (delete sn1 mbs) !! sn = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn1 = Some (Borrow al de1')) →
      (mbs !! sn2 = Some (Borrow al de2')) →
      (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      ▷ (mprops !! sn1 ≡ Some P) ∗
      ▷ (mprops !! sn2 ≡ Some Q) ∗
          ▷ full_borrows_invalidated_via alive dead k
                (<[sn:=Borrow al de]> (delete sn2 (delete sn1 mbs)))
                (<[sn:=P∗Q]> (delete sn2 (delete sn1 mprops)))
      ⊢ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof using invGS_gen0 Σ γ.
    intros Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2. iIntros "[#Heq1 [#Heq2 inval]]".
    destruct (invalidated alive dead k (Borrow al de)) eqn:Hinvbool.
    - iDestruct (full_borrows_invalidated_via_insert with "inval") as "[[p q] inval]".
        { trivial. } { trivial. }
      iDestruct (full_borrows_invalidated_via_delete alive dead k sn2 (delete sn1 mbs) (delete sn1 mprops) (Borrow al de2') Q with "[inval q]") as "inval".
        { rewrite lookup_delete_ne; trivial. } { rewrite lookup_delete_ne; trivial. iFrame "Heq2". iFrame "inval". iFrame "q". }
      iDestruct (full_borrows_invalidated_via_delete alive dead k sn1 mbs mprops (Borrow al de1') P with "[inval p]") as "inval".
        { trivial. } { iFrame "Heq1". iFrame "inval". iFrame "p". }
      iFrame.
    - iDestruct (full_borrows_invalidated_via_insert_false with "inval") as "inval".
        { trivial. }
      iDestruct (full_borrows_invalidated_via_delete_false alive dead k sn2 (delete sn1 mbs) (delete sn1 mprops) with "[inval]") as "inval".
        { rewrite lookup_delete_ne; trivial. apply Hmbssn2. }
        { rewrite bool_decide_eq_false. rewrite bool_decide_eq_false in Hinvbool. set_solver. }
        { iFrame "inval". }
      iDestruct (full_borrows_invalidated_via_delete_false alive dead k sn1 mbs mprops with "[inval]") as "inval".
        { apply Hmbssn1. }
        { rewrite bool_decide_eq_false. rewrite bool_decide_eq_false in Hinvbool. set_solver. }
        { iFrame "inval". }
      iFrame.
  Qed.
  
  Lemma full_borrows_revalidated_preserved_in_join
    sn sn1 sn2 mbs mprops P Q alive dead k al de de1' de2'
    :
      (delete sn2 (delete sn1 mbs) !! sn = None) →
      (sn1 ≠ sn2) →
      (mbs !! sn1 = Some (Borrow al de1')) →
      (mbs !! sn2 = Some (Borrow al de2')) →
      (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
      ▷ (mprops !! sn1 ≡ Some P) ∗
      ▷ (mprops !! sn2 ≡ Some Q) ∗
      ▷ full_borrows_revalidated_via alive dead k mbs mprops
      ⊢ ▷ full_borrows_revalidated_via alive dead k
            (<[sn:=Borrow al de]> (delete sn2 (delete sn1 mbs)))
            (<[sn:=P∗Q]> (delete sn2 (delete sn1 mprops))).
  Proof using invGS_gen0 Σ γ.
    intros Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2. iIntros "[#Heq1 [#Heq2 inval]]".
    destruct (revalidated alive dead k (Borrow al de)) eqn:Hinvbool.
    - iAssert (▷ full_borrows_revalidated_via alive dead k (delete sn1 mbs) (delete sn1 mprops)
        ∗ ▷ P)%I with "[inval]" as "[inval P]".
        { iApply full_borrows_revalidated_via_delete. { apply Hmbssn1. }
          { rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hinvbool. set_solver. }
          iFrame. iFrame "#". }
      iAssert (▷ full_borrows_revalidated_via alive dead k (delete sn2 (delete sn1 mbs)) (delete sn2 (delete sn1 mprops))
        ∗ ▷ Q)%I with "[inval]" as "[inval Q]".
        { iApply full_borrows_revalidated_via_delete. { rewrite lookup_delete_ne; trivial. apply Hmbssn2. }
          { rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hinvbool. set_solver. }
          iFrame. iFrame "#". rewrite lookup_delete_ne; trivial. }
      iApply full_borrows_revalidated_via_insert.
      { trivial. } iFrame.
    - iApply full_borrows_revalidated_via_insert_false.
      { trivial. } { trivial. }
      iApply full_borrows_revalidated_via_delete_false.
      { rewrite lookup_delete_ne; trivial. apply Hmbssn2. } iFrame.
      iApply full_borrows_revalidated_via_delete_false.
      { apply Hmbssn1. } iFrame.
  Qed.

  Lemma llfb_fb_vs_join sn sn1 sn2 (mbs : gmap_bor_state) alive dead al de de1' de2' outlives mprops P Q
  :
    (delete sn2 (delete sn1 mbs) !! sn = None) →
    (sn1 ≠ sn2) →
    (mbs !! sn1 = Some (Borrow al de1')) →
    (mbs !! sn2 = Some (Borrow al de2')) →
    (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
    (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) →
    (future_vs alive dead outlives mbs mprops
        ∗ ▷ (mprops !! sn1 ≡ Some P)
        ∗ ▷ (mprops !! sn2 ≡ Some Q))
    ⊢
      future_vs alive dead outlives
        (<[sn:=Borrow al de]> (delete sn2 (delete sn1 mbs)))
        (<[sn:=P∗Q]> (delete sn2 (delete sn1 mprops))).
  Proof using invGS_gen0 Σ γ.
    intros Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2.
    generalize Hrel_de1. generalize Hrel_de2. generalize dead.
    clear Hrel_de1. clear Hrel_de2. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hrel_de2 Hrel_de1) "[Hvs [#Heq1 #Heq2]]".
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
    iIntros (k) "[%Hin_my_alive [Dead inval]]".
    iMod ("Hvs" $! k with "[Dead inval]") as "[reval Hvs]".
    { iFrame. iSplitR. { iPureIntro. trivial. }
      iDestruct (full_borrows_invalidated_preserved_in_join sn1 sn2 sn mbs mprops P Q my_alive my_dead k al de de1' de2' Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2 with "[inval]") as "inval". { iFrame. iFrame "#". }
      iFrame.
    }
    iModIntro.
    iSplitL "reval".
    { iDestruct (full_borrows_revalidated_preserved_in_join sn sn1 sn2 mbs mprops P Q my_alive my_dead k al de de1' de2' Hdel Hne Hmbssn1 Hmbssn2 Hrel_de1 Hrel_de2 with "[reval]") as "reval". { iFrame. iFrame "#". } iFrame. }
    destruct Hin_my_alive.
    iApply IH; trivial. 
    - replace (my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]})) with (my_alive ∪ my_dead).
      + set_solver.
      + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
    - replace (my_alive ∖ {[k]} ∪ (my_dead ∪ {[k]})) with (my_alive ∪ my_dead).
      + set_solver.
      + apply set_eq. intros x. destruct (decide (x = k)); set_solver.
    - iFrame. iFrame "#".
  Qed.
  
  Lemma bool_decide_equiv P Q `{Decision P, Decision Q} :
    (P ↔ Q) → bool_decide P = bool_decide Q.
  Proof.
    intros Hiff. destruct (bool_decide P) eqn:Hp.
    - symmetry. rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hp.
      rewrite <- Hiff. trivial.
    - symmetry. rewrite bool_decide_eq_false. rewrite bool_decide_eq_false in Hp.
      rewrite <- Hiff. trivial.
  Qed.
  
  Lemma inner_join alive dead blocked sn1 sn2 al de P Q :
    (de ⊆ alive ∪ dead) →
    (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn1 P ∗ slice Nbox sn2 Q
      ⊢ |={↑Nbox}=> ∃ sn, (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn (P ∗ Q).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hwfde.
    iIntros "[Inv [LtState [OwnBor1 [OwnBor2 [#slice1 #slice2]]]]]".
    destruct (decide (al ## dead)) as [Hdisj|Hnot_disj].
    2: {
      iMod (inner_fake alive dead blocked al de (P ∗ Q) Hnot_disj with "LtState")
          as (sn) "[LtState [Ob Slice]]".
      iModIntro. iExists sn. iFrame.
    }
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices outlives]]]]]".
    iDestruct (agree_bor_state_borrow_lts γ sn1 mbs alive dead al de Hdisj
        with "[LtState auth OwnBor1]") as (de1') "[%Hmbs_sn1 %Hrel_de1]". { iFrame. }
    iDestruct (agree_bor_state_borrow_lts γ sn2 mbs alive dead al de Hdisj
        with "[LtState auth OwnBor2]") as (de2') "[%Hmbs_sn2 %Hrel_de2]". { iFrame. }
    iDestruct (distinct_bor_state_borrow_borrow_lts γ sn1 sn2 al de al de alive dead
        with "[LtState OwnBor1 OwnBor2]") as "%Hne"; trivial. { iFrame. }
    
    iMod (slice_combine (Nbox) (↑Nbox) true 
        (boxmap alive dead mbs)
        (Ptotal) P Q sn1 sn2
        (bool_decide (al ⊆ alive ∧ ¬ de ## dead))
        with "slice1 slice2 box") as (sn) "[%Hmd [#slice box]]".
      { set_solver. } { trivial. }
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbs_sn1. simpl. f_equiv.
        apply bool_decide_equiv. set_solver. }
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbs_sn2. simpl. f_equiv.
        apply bool_decide_equiv. set_solver. }
    
    assert (delete sn2 (delete sn1 mbs) !! sn = None) as Hdel
      by ( apply (delete_delete_boxmap_helper4 sn sn1 sn2 alive dead mbs Hmd) ).

    iMod (delete_bor_state_borrow_lts γ sn1 mbs alive dead al de Hdisj with 
        "[LtState auth OwnBor1]") as "[LtState auth]". { iFrame. }
    iMod (delete_bor_state_borrow_lts γ sn2 (delete sn1 mbs) alive dead al de Hdisj with 
        "[LtState auth OwnBor2]") as "[LtState auth]". { iFrame. }
        
    iMod (alloc_bor_state2 γ sn (delete sn2 (delete sn1 mbs)) alive dead al de de with "[LtState auth]") as "[LtState [auth own]]"; trivial. { set_solver. } { iFrame. }
    
    assert (de = de1' ∨ ¬ de1' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) as Hrel_de1'.
      { intuition. }
    assert (de = de2' ∨ ¬ de2' ## dead ∧ ¬ de ## dead ∧ de ⊆ alive ∪ dead) as Hrel_de2'.
      { intuition. }
    
    iDestruct (bi.later_mono _ _ (llfb_fb_vs_join sn sn1 sn2 mbs alive dead al de de1' de2' outlives mprops P Q Hdel Hne Hmbs_sn1 Hmbs_sn2 Hrel_de1' Hrel_de2') with "[vs]") as "vs".
    { iFrame. iNext.
      destruct pures as [Hdom Hrest]. iSplitL.
      { iApply (agree_slice_with_map mbs mprops sn1 _ (P)%I Hdom Hmbs_sn1). iFrame "#". }
      { iApply (agree_slice_with_map mbs mprops sn2 _ (Q)%I Hdom Hmbs_sn2). iFrame "#". }
    }
      
    iModIntro. iExists sn.
    iFrame "auth". iFrame "own".
    iFrame "LtState". iFrame "slice".
    iNext.
    iExists (<[ sn := (P ∗ Q)%I ]> (delete sn2 (delete sn1 mprops))).
    iExists Ptotal, outlives.
    iSplitL "box". { 
      rewrite boxmap_insert_Borrow. rewrite boxmap_delete.
      rewrite boxmap_delete. iFrame.
    }
    iFrame "vs". iFrame "outlives".
    
    destruct pures as [Hdom [Hwf Hoc]].
    assert (al ∪ de ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn1 (Borrow al de1') Hmbs_sn1.
      set_solver.
    }
    iSplitL. { iPureIntro. 
      split. { rewrite dom_insert_L. rewrite dom_insert_L. rewrite dom_delete_L.
        rewrite dom_delete_L. rewrite dom_delete_L. rewrite dom_delete_L.
        rewrite Hdom. trivial. }
      split. { apply map_wf_insert; trivial. apply map_wf_delete; trivial.
          apply map_wf_delete; trivial. }
      trivial.
    }
    { iApply big_sepM_insert_1. iFrame "slice".
      rewrite big_sepM_forall. rewrite big_sepM_forall. iIntros (x R) "%Dm".
      iApply "slices". iPureIntro.
      rewrite lookup_delete_Some in Dm.
      rewrite lookup_delete_Some in Dm. intuition.
    }
  Qed.
  
  Lemma future_vs_create_empty alive dead outlives mbs mprops sn P dd :
  ¬(dd ## dead) →
  (mbs !! sn = None) →
  future_vs alive dead outlives mbs mprops
  ⊢ future_vs alive dead outlives (<[sn:=Borrow ∅ dd]> mbs) (<[sn:=P]> mprops).
  Proof using invGS_gen0 Σ γ γd γo.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdd Hmbssn) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
  
  Lemma inner_borrow_create_empty alive dead blocked P :
      (▷ inner_inv alive dead blocked) ∗ (▷ P)
        ={↑Nbox}=∗
        ∃ sn , (▷ inner_inv alive dead blocked)
            ∗ OwnBorState γ sn (Borrow ∅ {[ default_dead ]})
            ∗ slice Nbox sn P.
  Proof using invGS_gen0 Σ γ γd γo.
    iIntros "[Inv P]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices outlives]]]]]".
    
    iMod (slice_insert_full Nbox (↑Nbox) true (boxmap alive dead mbs) Ptotal P with "P box") as (sn) "[%Hisnone [#slice box]]"; trivial.
    assert (mbs !! sn = None) as Hmbssn. {
      destruct (mbs !! sn) eqn:Heqn; trivial.
      rewrite lookup_fmap in Hisnone. rewrite Heqn in Hisnone. discriminate.
    }
    iMod (alloc_bor_state γ sn mbs (Borrow ∅ {[ default_dead ]}) with "auth") as "[auth OwnBor]"; trivial.
    
    assert (default_dead ∈ dead) as Hdd. { unfold map_wf in pures. intuition. }
    assert (¬({[default_dead]} ## dead)) as Hdd2. { set_solver. }
    
    iDestruct (bi.later_mono _ _ (future_vs_create_empty alive dead outlives mbs mprops sn P {[default_dead]} Hdd2 Hmbssn) with "vs") as "vs".
    
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
  
  Lemma outlives_consistent_mono dead outlives outlives' :
    outlives ⊆ outlives' →
    outlives_consistent dead outlives' →
    outlives_consistent dead outlives.
  Proof.
    unfold outlives_consistent. intros Hsub Hoc.
    intros o. have Ho := Hoc o. set_solver.
  Qed.
  
  Lemma future_vs_augment_outlives alive dead outlives outlives' mbs mprops :
    outlives ⊆ outlives' →
    future_vs alive dead outlives mbs mprops ⊢
    future_vs alive dead outlives' mbs mprops.
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hc.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead) "Hvs".
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
    
    iIntros (k) "[[%Hin_my_alive %Hoc] [#Dead inval]]".
    iMod ("Hvs" $! k with "[inval]") as "[reval vs]". { iFrame. iFrame "Dead".
      iPureIntro. split; trivial.
      apply (outlives_consistent_mono _ _ outlives'); trivial.
    }
    iModIntro. iFrame "reval".
    iApply IH; trivial.
  Qed.
  
  Lemma map_wf_augment_outlives alive dead blocked outlives outlives' mbs :
    (∀ o , o ∈ outlives' → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead) →
    outlives ⊆ outlives' →
    map_wf alive dead blocked outlives mbs →
    map_wf alive dead blocked outlives' mbs.
  Proof.
    unfold map_wf.
    intros Ho Hsub [Hdisj [Hblal [Hdd [Hf1 [Hf2 Hf3]]]]]. 
    split; trivial.
    split; trivial.
    split; trivial.
    split. {
      intros sn bs Hmbssn. have Hf := Hf1 sn bs Hmbssn. destruct bs; trivial. set_solver.
    }
    split; trivial.
  Qed.

  Lemma inner_augment_outlives alive dead blocked outlives outlives' :
    (∀ o , o ∈ outlives' → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead) →
    (outlives ⊆ outlives') →
    (outlives_consistent dead outlives') →
      (▷ inner_inv alive dead blocked) ∗ Outlives γo outlives
    ={∅}=∗ (▷ inner_inv alive dead blocked) ∗ Outlives γo outlives'.
  Proof using invGS_gen0 Σ γ γd γo.
    intros Ho Hsub Hc.
    iIntros "[Inv Outlives]".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives2) "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives2.
    
    iMod (outlives_update γo outlives outlives outlives' with "[outlives Outlives]") as "[outlives Outlives]". { iFrame. }
    
    iModIntro. iSplitR "Outlives"; last by iFrame "Outlives".
    iNext. iExists mbs. iExists mprops. iExists Ptotal. iExists outlives'.
    iFrame "auth". iFrame "box". iFrame "outlives".
    iDestruct (future_vs_augment_outlives alive dead outlives outlives' mbs mprops with "vs") as "vs"; trivial.
    iFrame "vs".
    iSplitL. {
      destruct pures as [Hdom [Hwf Hoc]].
      iPureIntro. split; trivial. split; trivial.
      apply (map_wf_augment_outlives alive dead blocked outlives outlives'); trivial.
    }
    iFrame "slices".
  Qed.
  
  Lemma future_vs_for_unborrow_start alive dead outlives mbs mprops sn bl al de de' P :
    (alive ## dead) →
    (mbs !! sn = Some (Borrow al de')) →
    (¬ de' ## dead) →
    (¬ de ## dead) →
    future_vs alive dead outlives mbs mprops
      ∗ ▷ (mprops !! sn ≡ Some P)
    ⊢
    future_vs alive dead outlives (<[sn:=Unborrow bl al de]> mbs) (<[sn:=P]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    replace (<[sn:=Unborrow bl al de]> mbs) with 
        (<[sn:=Unborrow bl al de]> (delete sn mbs)).
      2: { apply map_eq. { intros i. destruct (decide (sn = i)).
          - subst sn. rewrite lookup_insert. rewrite lookup_insert. trivial.
          - rewrite lookup_insert_ne; trivial. rewrite lookup_insert_ne; trivial.
              rewrite lookup_delete_ne; trivial. } }
  
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hmbssn Hde' Hde) "[Hvs #Heq]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
  
  Lemma inner_unborrow_start alive dead blocked outlives sn (bl al de : gset nat) P :
    (al ⊆ alive) →
    (de ⊆ alive ∪ dead) →
    ¬(de ## dead) →
    (bl ## blocked) →
    (bl ⊆ alive) →
    (∀ (k : nat) , k ∈ al → (bl, k) ∈ outlives) →
    (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
      ⊢ |={↑Nbox}=> 
    (▷ inner_inv alive dead (blocked ∪ bl)) ∗ LtState γ alive dead
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ (▷ P).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hal Hdewf Hde Hbl Hblalive Houtlives.
    iIntros "[Inv [LtState [Outlives [OwnBor #slice]]]]".
    unfold inner_inv.
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
    
    iDestruct (bi.later_mono _ _ (future_vs_for_unborrow_start alive dead outlives mbs mprops sn bl al de de' P Hdisj Hmbssn Hde' Hde) with "[vs]") as "vs".
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
      split. { apply map_wf_insert_unborrow; trivial. }
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
  future_vs alive dead outlives mbs mprops
  ⊢ future_vs alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsnmbs2 Hbl_a_outlives Hk1al. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hk1alive Hde_dead) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
  future_vs alive dead outlives mbs mprops
    ∗ (∀ d, ⌜d ∈ dead⌝ -∗ Dead γ d)
    ∗ (▷ Q ∗ (∃ k : nat, ⌜k ∈ bl⌝ ∗ Dead γ k) ={∅}=∗ ▷ P)
    ∗ (▷ (mprops !! sn ≡ Some P))
  ⊢
  future_vs alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsn2 Hbl_a_outlives. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hal_alive Hde_dead) "[Hvs [#Halldead [qvs #Heq]]]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
  
  Lemma llft_vs_for_unborrow_end_atomic' k1 alive dead outlives mbs mprops bl al de sn sn2 Q :
    (mbs !! sn = Some (Borrow al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (k1 ∈ al) →
    (k1 ∉ alive) →
    (¬(de ## dead)) →
  future_vs alive dead outlives mbs mprops
  ⊢ future_vs alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsnmbs2 Hbl_a_outlives Hk1al. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hk1alive Hde_dead) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
  
  Lemma llft_vs_for_unborrow_end_atomic alive dead outlives mbs mprops bl al de sn sn2 P Q :
    (mbs !! sn = Some (Borrow al de)) →
    ((delete sn mbs) !! sn2 = None) →
    (∀ a, a ∈ al → (bl, a) ∈ outlives) →
    (al ⊆ alive) →
    (¬(de ## dead)) →
  future_vs alive dead outlives mbs mprops
    ∗ (∀ d, ⌜d ∈ dead⌝ -∗ Dead γ d)
    ∗ (▷ Q ∗ (∃ k : nat, ⌜k ∈ bl⌝ ∗ Dead γ k) ={∅}=∗ ▷ P)
    ∗ (▷ (mprops !! sn ≡ Some P))
  ⊢
  future_vs alive dead outlives (<[sn2:=Borrow al de]> (delete sn mbs))
    (<[sn2:=Q]> (delete sn mprops)).
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hsn Hsn2 Hbl_a_outlives. generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hal_alive Hde_dead) "[Hvs [#Halldead [qvs #Heq]]]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
        
      iDestruct (full_borrows_invalidated_via_delete my_alive my_dead k sn mbs mprops (Borrow al de) P Hsn with "[Heq inval P]") as "inval".
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
      
      iApply (llft_vs_for_unborrow_end_atomic' k); trivial. { set_solver. } { set_solver. }
        { set_solver. }
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
          
  Lemma inner_unborrow_end alive dead blocked sn bl al de P Q :
    (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ slice Nbox sn P
        ∗ (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={∅}=∗ ▷ P))
        ∗ (▷ Q)
        ={↑Nbox}=∗ ∃ sn2,
          (▷ inner_inv alive dead (blocked ∖ bl)) ∗ LtState γ alive dead
          ∗ OwnBorState γ sn2 (Borrow al de)
          ∗ slice Nbox sn2 Q
          ∗ ⌜bl ⊆ blocked⌝
        .
  Proof using invGS_gen0 Σ γ γd γo.
    iIntros "[Inv [LtState [OwnBor [#slice [qvs q]]]]]".
    unfold inner_inv.
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
  
  Lemma inner_unborrow_atomic alive dead blocked outlives sn bl al de P :
    (al ⊆ alive) →
    ¬(de ## dead) →
    (∀ (k : nat) , k ∈ al → (bl, k) ∈ outlives) →
    (▷ inner_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
        ={↑Nbox,∅}=∗ ▷ P ∗ ∀ Q, 
        (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={∅}=∗ ▷ P)) ∗ (▷ Q)
          ={∅,↑Nbox}=∗ ∃ sn2,
    (▷ inner_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn2 Q
        .
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hal Hde Houtlives.
    iIntros "[Inv [LtState [Outlives [OwnBor #slice]]]]".
    unfold inner_inv.
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
    
    iMod (slice_delete_full (Nbox) (↑Nbox) true (boxmap alive dead mbs) Ptotal P sn with "slice box") as (Ptotal') "[P [#Ptotal_eq box]]". { set_solver. } { trivial. }
    
    iMod (fupd_mask_subseteq ∅) as "Upd". { set_solver. }
    iModIntro. iFrame "P". iIntros (Q) "[qvs q]". iMod "Upd".
    
    iMod (slice_insert_full Nbox (↑Nbox) true (delete sn (boxmap alive dead mbs)) Ptotal' Q with "q box") as (sn2) "[%Hlookup_sn2 [#slice2 box]]". { set_solver. }
    
    assert (delete sn mbs !! sn2 = None) as Hsn2. { apply (delete_boxmap_implies_delete_original_is_none _ _ _ _ _ Hlookup_sn2). }
    
    destruct pures as [Hdom [Hwf Hoc]].
    assert (¬(de' ## dead)) as Hde'. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      have Hf := Hforall sn _ Hmbssn. intuition. subst de'. intuition.
    }
    
    iMod (delete_bor_state_borrow_lts γ sn mbs alive dead al de with "[LtState auth OwnBor]") as "[LtState auth]"; trivial. { iFrame. }
    
    iMod (alloc_bor_state2 γ sn2 (delete sn mbs) alive dead al de de' with "[LtState auth]") as "[LtState [auth OwnBor2]]"; trivial. { iFrame. }
    
    iMod (get_all_deads with "LtState") as "[LtState #Halldeads]".
    
    iDestruct (bi.later_mono _ _ (llft_vs_for_unborrow_end_atomic alive dead outlives mbs mprops bl al de' sn sn2 P Q Hmbssn Hsn2 Houtlives Hal Hde') with "[vs qvs]") as "vs".
    { iFrame. iNext.
      iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } { iFrame "#". } iFrame "EqSlice". iFrame "Halldeads".
    }
    
    iModIntro. iExists sn2.
    iFrame "LtState". iFrame "OwnBor2". iFrame "slice2". iFrame "Outlives". iFrame "outlives".
    iExists (<[sn2:=Borrow al de']> (delete sn mbs)).
    iExists (<[sn2:=Q]> (delete sn mprops)).
    iExists (Q ∗ Ptotal')%I.
    iNext. iFrame "auth".
    iSplitL "box". {
      rewrite boxmap_insert_Borrow.
      rewrite boxmap_delete.
      rewrite bool_decide_eq_true_2. { iFrame. } split; trivial.
    }
    iFrame "vs".
    
    assert (al ∪ de' ⊆ alive ∪ dead) as Hwfalde. {
      destruct Hwf as [Ha [Hb [Hc [Hforall Hforall2]]]].
      apply (Hforall sn (Borrow al de') Hmbssn).
    }

    iSplitL. { iPureIntro. 
      split. {
        rewrite dom_insert_L. rewrite dom_insert_L.
        rewrite dom_delete_L. rewrite dom_delete_L. rewrite Hdom. trivial.
      }
      split.
      { apply map_wf_insert; trivial.
        apply (map_wf_delete alive dead blocked outlives mbs sn); trivial.
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
  Proof using invGS_gen0 Σ γ γd γo.
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
  Proof using invGS_gen0 Σ γ γd γo.
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
    future_vs alive dead outlives mbs mprops
      ∗ ▷ (mprops !! sn ≡ Some P)
    ⊢ 
    future_vs alive dead outlives
      (<[sn2:=Borrow (al ∪ al') dd]> (<[sn:=Borrow al al']> mbs))
      (<[sn2:=P]> (<[sn:=P]> (delete sn mprops))).
  Proof using invGS_gen0 Σ γ γd γo.
    replace (<[sn:=Borrow al al']> mbs) with (<[sn:=Borrow al al']> (delete sn mbs)).
      2: { apply map_eq. { intros i. destruct (decide (sn = i)).
          - subst sn. rewrite lookup_insert. rewrite lookup_insert. trivial.
          - rewrite lookup_insert_ne; trivial. rewrite lookup_insert_ne; trivial.
              rewrite lookup_delete_ne; trivial. } }
  
    intros Hne.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hdead Hwfal Hmbssn Hmbssn2) "[Hvs #Heq]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
      future_vs alive dead outlives mbs mprops
      ⊢
      future_vs alive dead outlives (delete sn mbs) (delete sn mprops).
  Proof using invGS_gen0 Σ γ γd γo.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    iIntros (my_dead Hdisj Hdead Hmbssn) "Hvs".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
    (future_vs alive dead outlives mbs mprops
      ∗ (∀ d, ⌜d ∈ dead⌝ -∗ Dead γ d)
      ∗ OwnBorState γ sn (Borrow al al')
      ∗ ▷ (mprops !! sn' ≡ Some (OwnBorState γ sn (Borrow al dd)))
      ⊢ 
      future_vs alive dead outlives (delete sn' mbs) (delete sn' mprops))%I.
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hmbssn'.
    generalize dead. clear dead.
    induction alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hdisj Hdd Halal'.
    iIntros "[Hvs [#Halldead [OwnBor #Heq]]]".
    
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
        
  Lemma inner_unnest alive dead blocked sn sn' al al' P :
    (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead 
        ∗ slice Nbox sn P
        ∗ OwnBorState γ sn' (Borrow al' {[ default_dead ]})
        ∗ slice Nbox sn' (OwnBorState γ sn (Borrow al {[ default_dead ]}))
      ={↑Nbox}=∗ ∃ sn2,
    (▷ inner_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn2 (Borrow (al ∪ al') {[ default_dead ]})
        ∗ slice Nbox sn2 P.
  Proof using invGS_gen0 Σ γ γd γo.
    iIntros "[Inv [LtState [#sliceP [OwnBor' #sliceBorrow]]]]".
    destruct (decide ((al ∪ al') ## dead)) as [Hdisj|Hndisj].
      2: { iMod (inner_fake alive dead blocked (al ∪ al') {[default_dead]} P with "LtState") as (sn2) "LtState"; trivial. iModIntro. iExists sn2. iFrame. }
    
    unfold inner_inv.
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
    assert (¬({[default_dead]} ## dead)) as Hdefaultdead. { set_solver. }
    
    assert (boxmap alive dead mbs !! sn = Some true) as Hboxmap_true.
      { unfold boxmap. rewrite lookup_fmap. rewrite Hmbssn. simpl.
        f_equiv. rewrite bool_decide_eq_true. 
        split. { set_solver. } unfold map_wf in pures. set_solver.
      }
    
    iDestruct (distinct_bor_state_borrow_borrow_lts γ sn' sn al' {[default_dead]} al {[default_dead]} alive dead with "[LtState OwnBor OwnBor']") as "%Hne"; trivial.
    { iFrame. }
    
    iMod (delete_bor_state_borrow_lts γ sn' mbs alive dead al' {[default_dead]} Hdisj_al'_dead
        with "[LtState auth OwnBor']") as "[LtState auth]". { iFrame. }
        
    iMod (update_bor_state_borrow_lts γ sn (delete sn' mbs) alive dead al {[default_dead]} (Borrow al al') Hdisj_al_dead
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
    
    iDestruct (bi.later_mono _ _ (llfb_fb_vs_for_unnest alive dead outlives mbs mprops sn sn' al al' {[default_dead]} dd' Hmbssn' Halive_disj_dead Hdefaultdead Hal'_sub_alive) with "[vs OwnBor]") as "vs".
     { iNext. iDestruct (agree_slice_with_map mbs mprops sn' _
          (OwnBorState γ sn (Borrow al {[default_dead]})) with "[]") as "EqSlice".
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
    : inner_inv alive dead blocked ⊢ ⌜default_dead ∈ dead⌝.
  Proof.
    iIntros "Inv". iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [box [vs [%pures [#slices outlives]]]]]".
    unfold map_wf in pures. intuition.
  Qed.
  
  Lemma inv_get_alive_dead_disj alive dead blocked
    : inner_inv alive dead blocked ⊢ ⌜alive ## dead⌝.
  Proof.
    iIntros "Inv". iDestruct "Inv" as (mbs mprops Ptotal outlives) "[auth [box [vs [%pures [#slices outlives]]]]]".
    unfold map_wf in pures. intuition.
  Qed.
  
  Lemma inv_get_outlives_condition alive dead blocked outlives
    : inner_inv alive dead blocked ∗ Outlives γo outlives ⊢ 
      ⌜∀ o , o ∈ outlives → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead⌝.
  Proof.
    iIntros "[Inv Outlives]". iDestruct "Inv" as (mbs mprops Ptotal outlives') "[auth [box [vs [%pures [#slices outlives]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'. unfold map_wf in pures. intuition.
  Qed.
  
  Lemma inv_get_outlives_consistent alive dead blocked outlives
    : inner_inv alive dead blocked ∗ Outlives γo outlives ⊢ 
      ⌜outlives_consistent dead outlives⌝.
  Proof.
    iIntros "[Inv Outlives]". iDestruct "Inv" as (mbs mprops Ptotal outlives') "[auth [box [vs [%pures [#slices outlives]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'. intuition.
  Qed.
  
  Lemma lemma_set5 (al dd' alive dead : gset nat) :
    al ∪ dd' ⊆ alive ∪ dead →
    al ## dead →
    al ⊆ alive. Proof. set_solver. Qed.
    
  Lemma lemma_set6 (al' dd' alive dead : gset nat) :
    al'  ⊆ alive ∪ dead →
    al' ## dead →
    al' ⊆ alive. Proof. set_solver. Qed.
            
  Lemma inner_reborrow alive dead blocked P sn al al' :
      (al' ⊆ alive ∪ dead) →
      (▷ inner_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Borrow al {[default_dead]})
        ∗ slice Nbox sn P
        ={↑Nbox}=∗ ∃ sn1 sn2,
      (▷ inner_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow (al ∪ al') {[default_dead]})
        ∗ OwnBorState γ sn2 (Borrow al al')
        ∗ slice Nbox sn1 P
        ∗ slice Nbox sn2 P.
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hal'wf.
    iIntros "[Inv [LtState [OwnBor #sliceP]]]".
    destruct (decide (al ## dead)) as [Hdisj|Hndisj].
    2: {
      iMod (inner_fake alive dead blocked (al ∪ al') {[default_dead]} P with "LtState") as (sn1) "[LtState [A Aslice]]". { set_solver. }
      iMod (inner_fake alive dead blocked al al' P with "LtState") as (sn2) "[LtState [B Bslice]]". { set_solver. }
      iModIntro. iExists sn1. iExists sn2. iFrame.
    }
    
    destruct (decide (al' ## dead)) as [Hdisj'|Hndisj].
    2: {
      iMod (inner_fake alive dead blocked (al ∪ al') {[default_dead]} P with "LtState") as (sn1) "[LtState [A Aslice]]". { set_solver. }
      
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
   
    unfold inner_inv.
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
    iMod (update_bor_state_borrow_lts γ sn _ alive dead al {[default_dead]} (Borrow al al') with "[LtState auth OwnBor]") as "[LtState [auth OwnBor]]". { set_solver. } { iFrame "auth". iFrame. }
    
    iMod (alloc_bor_state γ sn2 (<[sn:=Borrow al al']> mbs) (Borrow (al ∪ al') dd') with "[auth]") as "[auth OwnBor2]"; trivial. { rewrite lookup_insert_ne; trivial. }
    iMod (update_bor_state_borrow_fix_dead_lts γ alive dead sn2 (al ∪ al') dd' {[default_dead]} with "[LtState OwnBor2]") as "[LtState OwnBor2]". { set_solver. } { set_solver. } { iFrame. }
    
    iDestruct (bi.later_mono _ _ (llfb_fb_vs_for_reborrow alive dead outlives mbs mprops sn sn2 al al' dd' P Hne Halive_disj_dead Hdd'dead Hal'wf Hmbssn Hmbssn2)
     with "[vs]") as "vs"; trivial. { iFrame. iNext.
      iDestruct (agree_slice_with_map mbs mprops sn _ P with "[]") as "EqSlice"; trivial.
      { apply Hmbssn. } iFrame "#". }
        
    iModIntro.
    iExists sn2. iExists sn.
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

   Lemma inner_borrow_create alive dead blocked lt P :
      (lt ⊆ alive ∪ dead) →
      (▷ inner_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ (▷ P)
        ={↑Nbox}=∗
        ∃ sn sn2, (▷ inner_inv alive dead blocked)
            ∗ LtState γ alive dead
            ∗ OwnBorState γ sn (Borrow lt {[ default_dead ]})
            ∗ OwnBorState γ sn2 (Borrow ∅ lt)
            ∗ slice Nbox sn P
            ∗ slice Nbox sn2 P.
  Proof using invGS_gen0 Σ γ γd γo.
    intros Hlt. iIntros "[Inv [LtState P]]".
    iMod (inner_borrow_create_empty alive dead blocked P with "[Inv P]") as (sn) "[Inv [OwnBor #slice]]". { iFrame. }
    iMod (inner_reborrow alive dead blocked P sn ∅ lt Hlt with "[Inv LtState OwnBor]") as (sn1 sn2) "[Ha [Hb [Hd [He Hf]]]]".
      { iFrame. iFrame "#". }
    iModIntro. iExists sn1. iExists sn2. iFrame. replace (∅ ∪ lt) with lt by set_solver.
    iFrame.
  Qed.
     
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
  Proof.
      unfold outlives_consistent, map_wf.
      intros Hal Hde Hwf Hoc o Ho_in_outlives. have Ho := Hoc o Ho_in_outlives.
      destruct Hwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
      have Hr := Hoc o Ho_in_outlives. set_solver.
  Qed.
  
  Lemma llfb_fb_vs_for_new_lt' alive dead blocked outlives my_alive my_dead mbs mprops k_new :
    map_wf alive dead blocked outlives mbs →
    my_alive ∪ my_dead = alive ∪ dead →
    my_alive ## my_dead →
    k_new ∉ alive →
    k_new ∉ dead →
    future_vs (my_alive) my_dead outlives mbs mprops 
    ⊢ future_vs (my_alive) (my_dead ∪ {[k_new]}) outlives mbs mprops.
  Proof.
    intros Hwf.
    generalize my_dead. clear my_dead.
    induction my_alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hsame Hdisj Hknew_alive Hknew_dead.
    iIntros "Hvs".
    rewrite future_vs_def.
    rewrite (future_vs_def my_alive).
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
    future_vs (my_alive) my_dead outlives mbs mprops 
    ⊢ future_vs (my_alive ∪ {[k_new]}) (my_dead) outlives mbs mprops.
  Proof.
    intros Hwf.
    generalize my_dead. clear my_dead.
    induction my_alive as [my_alive IH] using set_ind_strong. 
    intros my_dead Hsame Hdisj Hknew_alive Hknew_dead.
    iIntros "Hvs".
    rewrite (future_vs_def (my_alive ∪ {[k_new]})).
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
      - rewrite future_vs_def.
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
   
  Lemma inner_new_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    (▷ inner_inv alive dead blocked) ={↑Nbox}=∗ (▷ inner_inv (alive ∪ {[ k ]}) dead blocked).
  Proof.
    intros Hk_fresh.
    iIntros "Inv".
    unfold inner_inv.
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
  
  Lemma outlives_consistent_instant_kill alive dead blocked outlives mbs k :
    (k ∉ alive ∪ dead) →
    map_wf alive dead blocked outlives mbs →
    outlives_consistent dead outlives →
    outlives_consistent (dead ∪ {[k]}) outlives.
  Proof.
    intros Hk Hwf Hoc o. 
    destruct Hwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
    have H1 := Hoc o. have H2 := Hforall3 o. set_solver.
  Qed.
  
  Lemma inner_instant_kill_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    (▷ inner_inv alive dead blocked)
      ={∅}=∗
    (▷ inner_inv alive (dead ∪ {[k]}) blocked).
  Proof.
    intros Hk_fresh.
    iIntros "Inv".
    unfold inner_inv.
    iDestruct "Inv" as (mbs mprops Ptotal outlives) "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    
    iDestruct (llfb_fb_vs_for_new_lt' alive dead blocked outlives alive dead mbs mprops k with "vs") as "vs"; trivial.
      { intuition. }
      { unfold map_wf in pures. intuition. }
      { set_solver. }
      { set_solver. }
    
    iModIntro. iNext.
    iExists mbs. iExists mprops. iExists Ptotal. iExists outlives.
    iFrame "auth".
    destruct pures as [Hdom [Hwf Hoc]].
    iSplitL "box". {
      replace (boxmap alive (dead ∪ {[k]}) mbs) with (boxmap alive dead mbs). { iFrame. }
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
      { apply map_wf_new_lt_dead; trivial. }
      apply (outlives_consistent_instant_kill alive dead blocked outlives mbs k); trivial.
    }
    iFrame "slices". iFrame "outlives".
  Qed.
  
  Lemma outlives_consistent_preserved_on_kill outlives dead k :
      (∀ other : gset nat, (other, k) ∈ outlives → ¬ other ## (dead ∪ {[k]})) →
      (outlives_consistent dead outlives) →
      outlives_consistent (dead ∪ {[k]}) outlives.
  Proof.
    unfold outlives_consistent. intros Ho Hoc o Ho_in Ho2_dead.
    have Hoc2 := Hoc o. have Ho2 := Ho (o.1). set_solver.
  Qed.
  
  (*Lemma big_opM_imap {M: ofe} `{Countable K} {A B : Type} (h : A → B) (f : K → B → M) (m : gmap K A) : 
    ([^o map] k↦y ∈ h <$> m, f k y) ≡ ([^o map] k↦y ∈ m, f k (h y)).
  Proof.
    rewrite big_opM_unseal /big_opM_def map_to_list_fmap big_opL_fmap.
    by apply big_opL_proper=> ? [??].
  Qed. *)
  
  Lemma big_sepM_imap `{Countable K} {A B} (f : K → A → option B) (Φ : K → B → iProp Σ) (m : gmap K A) :
    ([∗ map] k↦y ∈ map_imap f m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, from_option (Φ k) emp (f k y)).
  Proof. 
    induction m as [|i x' m Hl IH] using map_ind.
    - rewrite map_imap_empty. rewrite big_sepM_empty. rewrite big_sepM_empty. trivial.
    - rewrite map_imap_insert. destruct (f i x') eqn:Hfix.
      + rewrite big_sepM_insert.
        * rewrite big_sepM_insert; trivial. rewrite IH. unfold from_option.
          rewrite Hfix. trivial.
        * rewrite map_lookup_imap. unfold mbind, option_bind. rewrite Hl. trivial.
      + replace (delete i (map_imap f m)) with (map_imap f m).
        * rewrite big_sepM_insert; trivial. rewrite Hfix. rewrite IH. unfold from_option.
          iSplit. { iIntros "A". iFrame. } { iIntros "[A B]". iFrame. }
        * rewrite <- map_imap_delete. f_equal. rewrite delete_notin; trivial.
  Qed.
  
  (*Lemma big_sepM_mono2 `{Countable K} {A B} (Φ : K → A → iProp Σ) (Ψ : K → B → iProp Σ) (m : gmap K A) (m2: gmap K B) :
    (∀ k x, m2 !! k = Some x → ∃ y, (m !! k = Some y) ∧ (Φ k y ⊢ Ψ k x)) → 
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊢ [∗ map] k ↦ x ∈ m2, Ψ k x. *)
  
  Lemma box_take_all_invalidate alive dead k mbs mprops Ptotal :
    (∀ sn bl al de , mbs !! sn = Some (Unborrow bl al de) → k ∉ al) →
    (dom mbs = dom mprops) →
    box Nbox (boxmap alive dead mbs) Ptotal
        ∗ ([∗ map] sn↦Q ∈ mprops, slice Nbox sn Q)
    ={↑Nbox}=∗
    box Nbox (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
        ∗ ▷ full_borrows_invalidated_via alive dead k mbs mprops.
  Proof.
    intros Hunb Hdom. iIntros "[box #slices]".
    unfold full_borrows_invalidated_via. unfold borrow_sum.
    iDestruct (slice_empty_many Nbox (↑Nbox) false (boxmap alive dead mbs) Ptotal
      (map_imap (λ sn bs, (if invalidated alive dead k bs
                            then Some (match mprops !! sn with
                                 | Some P => P
                                 | None => True%I
                                 end)
                            else None)) mbs) with "[] box") as "X".
    { set_solver. }
    { intros sn Q Hm. rewrite map_lookup_imap in Hm.
      unfold mbind, option_bind in Hm.
      destruct (mbs !! sn) eqn:Hmbs.
      - rewrite Hmbs in Hm. unfold boxmap. destruct (invalidated alive dead k b) eqn:Hinv.
        + rewrite lookup_fmap. rewrite Hmbs. simpl. f_equiv. unfold invalidated in Hinv.
          destruct b as [|bl al de].
          * rewrite bool_decide_eq_true. rewrite bool_decide_eq_true in Hinv. intuition.
          * rewrite bool_decide_eq_true in Hinv. have Hu := Hunb sn bl al de. set_solver.
        + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   { iIntros (sn Q) "%Hm". rewrite (big_sepM_delete _ _ sn Q);
      first by iDestruct "slices" as "[slice _]"; iFrame.
     rewrite map_lookup_imap in Hm.
     unfold mbind, option_bind in Hm. destruct (mbs !! sn) eqn:Hmbs.
     - rewrite Hmbs in Hm. destruct (invalidated alive dead k b) eqn:Hinv.
      + destruct (mprops !! sn) eqn:Hmprops.
        * rewrite Hmprops in Hm. trivial.
        * assert (sn ∈ dom mbs) as X. { eapply elem_of_dom_2; apply Hmbs. }
          rewrite <- not_elem_of_dom in Hmprops. set_solver.
      + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   iMod "X" as "[H box]". iModIntro.
   iSplitL "box". {
      replace ((boxmap (alive ∖ {[k]}) dead mbs)) with (((λ _ : iProp Σ, false) <$>
                      map_imap
                        (λ (sn : gname) (bs : BorState),
                           if invalidated alive dead k bs
                           then Some match mprops !! sn with
                                     | Some P => P
                                     | None => True
                                     end
                           else None) mbs) ∪ boxmap alive dead mbs)%I.
       { iFrame "box". }
       apply map_eq. intros sn.
       destruct (mbs !! sn) as [bs|] eqn:Hmbssn.
        - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
          rewrite lookup_fmap. rewrite lookup_fmap.
          rewrite Hmbssn. simpl.
          destruct bs as [al de|bl al de].
          + destruct (invalidated alive dead k (Borrow al de)) eqn:Hinv.
            * simpl. unfold union, option_union, union_with, option_union_with. 
              f_equiv. unfold invalidated in Hinv. rewrite bool_decide_eq_true in Hinv.
              symmetry. rewrite bool_decide_eq_false. set_solver.
            * unfold union, option_union, union_with, option_union_with. simpl. f_equiv.
              apply bool_decide_equiv. rewrite bool_decide_eq_false in Hinv.
              set_solver.
          + destruct (invalidated alive dead k (Unborrow bl al de)) eqn:Hinv.
            * trivial.
            * trivial.
        - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
          rewrite lookup_fmap. rewrite lookup_fmap.
          rewrite Hmbssn. simpl. trivial.
     }
  rewrite big_sepM_imap.
  iDestruct (big_sepM_mono with "H") as "H". 2: { iFrame "H". }
  intros sn bs Hmbssn. simpl. unfold from_option.
  destruct (invalidated alive dead k bs); trivial.
  Qed.
  
  Lemma box_put_all_revalidate alive dead k mbs (mprops : gmap slice_name (iProp Σ)) Ptotal :
    (dom mbs = dom mprops) →
    box Nbox (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
        ∗ ▷ full_borrows_revalidated_via alive dead k mbs mprops
        ∗ ([∗ map] sn↦Q ∈ mprops, slice Nbox sn Q)
    ={↑Nbox}=∗
    box Nbox (boxmap (alive ∖ {[k]}) (dead ∪ {[k]}) mbs) Ptotal.
  Proof.
    intros Hdom. iIntros "[box [reval #slices]]".
    unfold full_borrows_revalidated_via. unfold borrow_sum.
    iDestruct (slice_fill_many Nbox (↑Nbox) false (boxmap (alive ∖ {[k]}) dead mbs) Ptotal
      (map_imap (λ sn bs, (if revalidated alive dead k bs
                            then Some (match mprops !! sn with
                                 | Some P => P
                                 | None => True%I
                                 end)
                            else None)) mbs) with "[] [reval] box") as "X".
    { set_solver. }
    { intros sn Q Hm. rewrite map_lookup_imap in Hm.
      unfold mbind, option_bind in Hm.
      destruct (mbs !! sn) eqn:Hmbs.
      - rewrite Hmbs in Hm. unfold boxmap. destruct (revalidated alive dead k b) eqn:Hinv.
        + rewrite lookup_fmap. rewrite Hmbs. simpl. f_equiv. unfold revalidated in Hinv.
          destruct b as [al de|bl al de].
          * rewrite bool_decide_eq_false. rewrite bool_decide_eq_true in Hinv. intuition.
          * trivial.
        + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   { iIntros (sn Q) "%Hm". rewrite (big_sepM_delete _ _ sn Q);
      first by iDestruct "slices" as "[slice _]"; iFrame.
     rewrite map_lookup_imap in Hm.
     unfold mbind, option_bind in Hm. destruct (mbs !! sn) eqn:Hmbs.
     - rewrite Hmbs in Hm. destruct (revalidated alive dead k b) eqn:Hinv.
      + destruct (mprops !! sn) eqn:Hmprops.
        * rewrite Hmprops in Hm. trivial.
        * assert (sn ∈ dom mbs) as X. { eapply elem_of_dom_2; apply Hmbs. }
          rewrite <- not_elem_of_dom in Hmprops. set_solver.
      + discriminate.
     - rewrite Hmbs in Hm. discriminate.
   }
   {
      rewrite big_sepM_imap.
      iDestruct (big_sepM_mono with "reval") as "reval". 2: { iFrame "reval". }
      intros sn bs Hmbssn. simpl. unfold from_option.
      destruct (revalidated alive dead k bs); trivial.
   }
   replace (boxmap (alive ∖ {[k]}) (dead ∪ {[k]}) mbs) with
      ((((λ _ : iProp Σ, true) <$>
                      map_imap
                        (λ (sn : gname) (bs : BorState),
                           if revalidated alive dead k bs
                           then Some match mprops !! sn with
                                     | Some P => P
                                     | None => True%I
                                     end
                           else None) mbs) ∪ boxmap (alive ∖ {[k]}) dead mbs)).
       { iFrame "X". }
    apply map_eq. intros sn.
    destruct (mbs !! sn) as [bs|] eqn:Hmbssn.
    - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
      rewrite lookup_fmap. rewrite lookup_fmap.
      rewrite Hmbssn. simpl.
      destruct bs as [al de|bl al de].
      + destruct (revalidated alive dead k (Borrow al de)) eqn:Hinv.
        * simpl. unfold union at 1, option_union, union_with, option_union_with. 
          f_equiv. unfold revalidated in Hinv. rewrite bool_decide_eq_true in Hinv.
          symmetry. rewrite bool_decide_eq_true. split; intuition.
          set_solver.
        * unfold union at 1, option_union, union_with, option_union_with. simpl. f_equiv.
          apply bool_decide_equiv. rewrite bool_decide_eq_false in Hinv.
          set_solver.
      + destruct (revalidated alive dead k (Unborrow bl al de)) eqn:Hinv.
        * unfold revalidated in Hinv. discriminate.
        * trivial.
    - rewrite lookup_union. rewrite lookup_fmap. rewrite map_lookup_imap.
      rewrite lookup_fmap. rewrite lookup_fmap.
      rewrite Hmbssn. simpl. trivial.
  Qed.
  
  Lemma inner_kill_lt alive dead blocked outlives k :
    (k ∈ alive) →
    (k ∉ blocked) →
    (∀ other , (other, k) ∈ outlives → ¬(other ## (dead ∪ {[k]}))) →
    (▷ inner_inv alive dead blocked) ∗ Outlives γo outlives ∗ Dead γ k
      ={↑Nbox}=∗ ▷ |={↑Nbox}=>
    (▷ inner_inv (alive ∖ {[k]}) (dead ∪ {[k]}) blocked) ∗ Outlives γo outlives.
  Proof.
    intros Hk_alive Hk_not_blocked Houtlives_okay.
    iIntros "[Inv [Outlives Dead]]".
    iDestruct "Inv" as (mbs mprops Ptotal outlives') "[>auth [box [vs [>%pures [#slices >outlives]]]]]".
    iDestruct (outlives_agree with "[outlives Outlives]") as "%Hoeq". { iFrame. }
    subst outlives'.
    
    destruct pures as [Hp [Hwf Hrest]]. 
    
    iModIntro. iNext.
    
    iMod (box_take_all_invalidate alive dead k mbs mprops Ptotal with "[box]") as "[box inval]". 
    { intros sn bl al de Hmbssn Hkal. 
      destruct Hwf as [Ha [Hb [Hc [Hforall [Hforall2 Hforall3]]]]].
      have Hf := Hforall sn (Unborrow bl al de) Hmbssn.
      destruct Hf as [Hx [Hy [Hz Hw]]].
      have Hzk := Hz k Hkal. set_solver. }
    { trivial. }
    { iFrame. iFrame "slices". }
    
    rewrite future_vs_def. iDestruct ("vs" $! k with "[Dead inval]") as "vs".
    { iFrame.
      { iPureIntro. split; trivial.
        apply outlives_consistent_preserved_on_kill; trivial. }
    }
    iMod (fupd_mask_mono ∅ (↑Nbox) with "vs") as "[reval vs]". { set_solver. }
   
    iMod (box_put_all_revalidate alive dead k mbs mprops Ptotal with "[box reval]") as "box".
      { trivial. } { iFrame.  iFrame "slices". }

    iModIntro. iSplitR "Outlives". 2: { iFrame. }
    iNext. unfold inner_inv. iExists mbs. iExists mprops. iExists Ptotal.
    iExists outlives. iFrame. iFrame "slices". iPureIntro.
   
    split; trivial. split.
    { apply map_wf_preserved_on_kill; trivial. }
    { apply outlives_consistent_preserved_on_kill; trivial. }
  Qed.
  
  (* The reason for the "outer inv" is that killing a lifetime has to proceed in
     multiple "phases". I couldn't find another way to do this that doesn't require
     the nested masks NllftG ⊂ Nllft.
     
     To kill a lifetime κ = {[k]} we have to:
  
     1. Exchange the Alive k tokens for a Dead k token
     
     2. Deduce that anything dependent on k according to the 'outlives' relationship is also dead
     
     3. Invoke kill_lt on the full borrows inv
     
     In order for step 2 to work, we need to employ the rule:
        `κ' ⊑ κ -∗ [†κ] ={↑NllftG}=∗ [†κ']`
     Thus (1) has to happen before (2) (so we can get the [†κ] token)
     But (2) is also a precondition for (3). Furthermore, we have to close up the llftG mask
     in order to do (2). Hence, we need the two "phases".
     
     To track when we're in the middle of these two phases, we use the Delayed token;
     `Delayed (Some k)` basically means, "we are in the middle of killing the lifetime k",
     i.e., we have created the `Dead k` token but not yet updated the full-borrows part
     of the invariant.
     
     The reason for having the larger mask Nllft is so we have somewhere to put the
     other `Delayed None` token that is outside the NllftG mask.
  *)
  
  Definition outer_inv (alive dead blocked : gset nat) : iProp Σ :=
      ∃ opt_k , Delayed γd opt_k ∗ 
          match opt_k with
          | None => inner_inv alive dead blocked
          | Some (k, alive') =>
              inner_inv (alive ∪ {[k]}) (dead ∖ {[k]}) blocked ∗ ⌜ k ∉ alive ∧ k ∈ dead ∧ alive' = alive ⌝
          end.
          
  Lemma outer_new_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    (▷ outer_inv alive dead blocked) ∗ Delayed γd None ={↑Nbox}=∗
    (▷ outer_inv (alive ∪ {[ k ]}) dead blocked) ∗ Delayed γd None.
  Proof.
    intros Had.
    iIntros "[Inv Delayed]". iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_new_lt alive dead blocked k with "Inv") as "Inv"; trivial.
    iModIntro. iFrame. iFrame.
  Qed.
  
  Lemma outer_instant_kill_lt alive dead blocked k :
    (k ∉ alive ∪ dead) →
    (▷ outer_inv alive dead blocked) ={∅}=∗
    (▷ outer_inv alive (dead ∪ {[k]}) blocked).
  Proof.
    intros Had.
    iIntros "Inv". iDestruct "Inv" as (opt_k) "[>D Inv]".
    destruct opt_k as [[k' alive']|].
    {
      iDestruct "Inv" as "[Inv >Hndead]".
      iDestruct "Hndead" as "%Hndead".
      iMod (inner_instant_kill_lt _ _ blocked k with "Inv") as "Inv"; trivial.
      { set_solver. }
      iModIntro. iExists (Some (k', alive')). iSplitL "D". { iFrame. }
      replace ((dead ∖ {[k']} ∪ {[k]})) with ((dead ∪ {[k]}) ∖ {[k']}).
      2: { apply set_eq. intros x. set_solver. }
      iFrame. iPureIntro. set_solver.
    }
    {
      iMod (inner_instant_kill_lt alive dead blocked k with "Inv") as "Inv"; trivial.
      iModIntro. iExists None. iFrame "Inv". iFrame "D".
    }
  Qed.
  
  Lemma outer_kill_lt_step1 alive dead blocked k :
    (k ∈ alive) →
    (k ∉ dead) →
    (▷ outer_inv alive dead blocked) ∗ Delayed γd None
      ={↑Nbox}=∗
    (▷ outer_inv (alive ∖ {[k]}) (dead ∪ {[k]}) blocked) ∗ Delayed γd (Some (k, alive ∖ {[k]})).
  Proof.
    intros kalive kdead.
    iIntros "[Inv Delayed]". iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (delayed_update γd _ _ (Some (k, alive ∖ {[k]})) with "[D Delayed]") as "[D Delayed]". { iFrame "D Delayed". }
    iModIntro.
    iFrame "Delayed". iFrame "D". 
    replace (alive ∖ {[k]} ∪ {[k]}) with alive.
    - replace ((dead ∪ {[k]}) ∖ {[k]}) with dead.
      + iFrame. iPureIntro. set_solver.
      + set_solver.
    - apply set_eq. intros x. destruct (decide (x = k)); set_solver.
  Qed.
  
  Lemma set_lemma7 (other alive dead : gset nat) (k : nat) :
        k ∉ alive →
        k ∈ dead →
        other ⊈ alive →
        other ⊆ alive ∪ {[k]} ∪ dead ∖ {[k]} →
        ¬ other ## dead ∖ {[k]} ∪ {[k]}.
  Proof.
    set_solver.
  Qed.

  Lemma outer_kill_lt_step2 alive dead blocked outlives k alive' :
    (k ∉ blocked) →
    (∀ other , (other, k) ∈ outlives → ¬(other ⊆ alive')) →
    (▷ outer_inv alive dead blocked)
      ∗ Outlives γo outlives
      ∗ Dead γ k
      ∗ Delayed γd (Some (k, alive'))
      ={↑Nbox}=∗ ▷ |={↑Nbox}=>
    (▷ outer_inv alive dead blocked)
      ∗ Outlives γo outlives
      ∗ Delayed γd None.
  Proof.
    intros Hblocked Houtlives.
    iIntros "[Inv [Outlives [Dead Delayed]]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iDestruct "Inv" as "[Inv #>p]". iDestruct "p" as "[%Hkdead [%Hkalive %Heq]]". subst alive'.
    
    iDestruct (bi.later_mono _ _ (inv_get_outlives_condition (alive ∪ {[k]}) (dead ∖ {[k]}) blocked outlives) with "[Inv Outlives]") as "#>%Hoc". { iFrame "Inv". iFrame. }
    
    assert (∀ o : gset nat * nat, o ∈ outlives → o.1 ⊆ alive ∪ {[k]} ∪ dead ∖ {[k]}) as H2.
    {
      intros o. have Hoco := Hoc o. set_solver.
    }
    
    iMod (delayed_update γd _ _ None with "[D Delayed]") as "[D Delayed]".
        { iFrame "D Delayed". }
    iMod (inner_kill_lt (alive ∪ {[k]}) (dead ∖ {[k]}) blocked outlives k with "[Inv Outlives Dead]")
      as "X"; trivial. { set_solver. }
      { 
        intros other. have Ho := Houtlives other.
        have Ho2 := H2 (other, k).
        intros Hin. have Hox := Ho Hin. have Hoy := Ho2 Hin. simpl in Hoy.
        apply (set_lemma7 other alive dead k); trivial.
      } { iFrame "Dead". iFrame "Inv". iFrame "Outlives". }
    iModIntro. iNext. iMod "X". iModIntro.
    iDestruct "X" as "[X Y]".
    iFrame "Y". iSplitL "X D". {
      iExists None. iFrame "D".
      replace (((alive ∪ {[k]}) ∖ {[k]})) with alive by set_solver.
      replace ((dead ∖ {[k]} ∪ {[k]})) with dead. 2: {
        apply set_eq. intro x. destruct (decide (x = k)); set_solver.
      }
      iFrame.
    }
    iFrame "Delayed".
  Qed.
  
  Lemma outer_borrow_create alive dead blocked lt P :
      (lt ⊆ alive ∪ dead) →
      Delayed γd None
        ∗ (▷ outer_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ (▷ P)
        ={↑Nbox}=∗
      Delayed γd None ∗
      ∃ sn sn2, (▷ outer_inv alive dead blocked)
          ∗ LtState γ alive dead
          ∗ OwnBorState γ sn (Borrow lt {[ default_dead ]})
          ∗ OwnBorState γ sn2 (Borrow ∅ lt)
          ∗ slice Nbox sn P
          ∗ slice Nbox sn2 P.
  Proof.
    intros Hlt. iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_borrow_create alive dead blocked lt P Hlt with "[H Inv]") as (sn sn2) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_unborrow_start alive dead blocked outlives sn (bl al de : gset nat) P :
    (al ⊆ alive) →
    (de ⊆ alive ∪ dead) →
    ¬(de ## dead) →
    (bl ## blocked) →
    (bl ⊆ alive) →
    (∀ (k : nat) , k ∈ al → (bl, k) ∈ outlives) →
      Delayed γd None
        ∗ (▷ outer_inv alive dead blocked) ∗ LtState γ alive dead ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
      ⊢ |={↑Nbox}=> 
      Delayed γd None
        ∗ (▷ outer_inv alive dead (blocked ∪ bl)) ∗ LtState γ alive dead
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ (▷ P).
  Proof.
    intros Hal Hdewf Hde Hbl Hblal Ho. iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unborrow_start alive dead blocked outlives sn bl al de P Hal Hdewf Hde Hbl Hblal Ho with "[H Inv]") as "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_inner_unborrow_end alive dead blocked sn bl al de P Q :
      Delayed γd None
        ∗ (▷ outer_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Unborrow bl al de)
        ∗ slice Nbox sn P
        ∗ (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={∅}=∗ ▷ P))
        ∗ (▷ Q)
        ={↑Nbox}=∗ ∃ sn2,
      Delayed γd None
        ∗ (▷ outer_inv alive dead (blocked ∖ bl)) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn2 Q
        ∗ ⌜bl ⊆ blocked⌝
        .
  Proof.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unborrow_end alive dead blocked sn bl al de P Q with "[H Inv]") as (sn2) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_unnest alive dead blocked sn sn' al al' P :
    Delayed γd None
        ∗ (▷ outer_inv alive dead blocked) ∗ LtState γ alive dead 
        ∗ slice Nbox sn P
        ∗ OwnBorState γ sn' (Borrow al' {[ default_dead ]})
        ∗ slice Nbox sn' (OwnBorState γ sn (Borrow al {[ default_dead ]}))
      ={↑Nbox}=∗ ∃ sn2,
    Delayed γd None
        ∗ (▷ outer_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn2 (Borrow (al ∪ al') {[ default_dead ]})
        ∗ slice Nbox sn2 P.
  Proof.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unnest alive dead blocked sn sn' al al' P with "[H Inv]") as (sn2) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_split alive dead blocked sn al de P Q :
      Delayed γd None
      ∗ (▷ outer_inv alive dead blocked) ∗ LtState γ alive dead
      ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn (P ∗ Q)
      ⊢ |={↑Nbox}=> ∃ sn1 sn2,
      Delayed γd None
        ∗ (▷ outer_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn1 P ∗ slice Nbox sn2 Q.
  Proof.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_split alive dead blocked sn al de P Q with "[H Inv]") as (sn1 sn2) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_join alive dead blocked sn1 sn2 al de P Q :
      (de ⊆ alive ∪ dead) →
      Delayed γd None
        ∗ (▷ outer_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow al de) ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn1 P ∗ slice Nbox sn2 Q
      ⊢ |={↑Nbox}=> ∃ sn,
      Delayed γd None
        ∗ (▷ outer_inv alive dead blocked) ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Borrow al de) ∗ slice Nbox sn (P ∗ Q).
  Proof.
    intros Hdewf. iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_join alive dead blocked sn1 sn2 al de P Q Hdewf with "[H Inv]") as (sn) "[Inv H]". { iFrame. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_augment_outlives alive dead blocked outlives outlives' :
    (∀ o , o ∈ outlives' → o.1 ⊆ alive ∪ dead ∧ o.2 ∈ alive ∪ dead) →
    (outlives ⊆ outlives') →
    (outlives_consistent dead outlives') →
      Delayed γd None ∗ (▷ outer_inv alive dead blocked) ∗ Outlives γo outlives
    ⊢ |={↑Nbox}=>
      Delayed γd None ∗ (▷ outer_inv alive dead blocked) ∗ Outlives γo outlives'.
  Proof.
    intros Howf Hosub Hc.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iDestruct (inner_augment_outlives alive dead blocked outlives outlives' with "[H Inv]") as "X"; trivial. { iFrame. }
    iMod (fupd_mask_mono with "X") as "[Inv H]". { set_solver. }
    iModIntro. iFrame "Delayed H". iExists None. iFrame.
  Qed.
  
  Lemma outer_unborrow_atomic alive dead blocked outlives sn bl al de P :
    (al ⊆ alive) →
    ¬(de ## dead) →
    (∀ (k : nat) , k ∈ al → (bl, k) ∈ outlives) →
    Delayed γd None
        ∗ (▷ outer_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn (Borrow al de)
        ∗ slice Nbox sn P
        ={↑Nbox,∅}=∗ ▷ P ∗ ∀ Q, 
        (▷ (▷ Q ∗ (∃ k , ⌜ k ∈ bl ⌝ ∗ Dead γ k) ={∅}=∗ ▷ P)) ∗ (▷ Q)
          ={∅,↑Nbox}=∗ ∃ sn2,
    Delayed γd None
        ∗ (▷ outer_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ Outlives γo outlives
        ∗ OwnBorState γ sn2 (Borrow al de)
        ∗ slice Nbox sn2 Q
        .
  Proof.
    intros Hal Hde Houtlives.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_unborrow_atomic alive dead blocked outlives sn bl al de P Hal Hde with "[H Inv]") as "[P H]"; trivial. { iFrame. }
    iModIntro. iFrame "P". iIntros (Q). iDestruct ("H" $! Q) as "H". iIntros "A".
    iDestruct ("H" with "A") as "H". iMod "H" as (sn2) "H". iModIntro. iExists sn2.
    iFrame. iFrame "H".
  Qed.
    
  Lemma outer_reborrow alive dead blocked P sn al al' :
      (al' ⊆ alive ∪ dead) →
      Delayed γd None
       ∗ (▷ outer_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ OwnBorState γ sn (Borrow al {[default_dead]})
        ∗ slice Nbox sn P
        ={↑Nbox}=∗ ∃ sn1 sn2,
      Delayed γd None
        ∗ (▷ outer_inv alive dead blocked)
        ∗ LtState γ alive dead
        ∗ OwnBorState γ sn1 (Borrow (al ∪ al') {[default_dead]})
        ∗ OwnBorState γ sn2 (Borrow al al')
        ∗ slice Nbox sn1 P
        ∗ slice Nbox sn2 P.
  Proof.
    intros Hal.
    iIntros "[Delayed [Inv H]]".
    iDestruct "Inv" as (opt_k) "[>D Inv]".
    iDestruct (delayed_agree with "[D Delayed]") as "%Heq". { iFrame "D Delayed". }
    subst opt_k.
    iMod (inner_reborrow alive dead blocked P sn al al' Hal with "[H Inv]") as (sn1 sn2) "[P H]"; trivial. { iFrame. }
    iModIntro. iExists sn1. iExists sn2.
    iFrame "Delayed". iFrame "H". iExists None. iFrame.
  Qed.
End FullBorrows.


