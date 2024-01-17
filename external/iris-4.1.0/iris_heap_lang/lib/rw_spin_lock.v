From iris.algebra Require Import gmultiset.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Export fractional.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Export rw_lock.
From iris.prelude Require Import options.

Local Definition newlock : val := λ: <>, ref #0.
Local Definition try_acquire_reader : val :=
  λ: "l",
    let: "n" := !"l" in
    if: #0 ≤ "n"
      then CAS "l" "n" ("n" + #1)
      else #false.
Local Definition acquire_reader : val :=
  rec: "acquire" "l" :=
    if: try_acquire_reader "l"
      then #()
      else "acquire" "l".
Local Definition release_reader : val :=
  λ: "l", FAA "l" #(-1) ;; #().
Local Definition try_acquire_writer : val :=
  λ: "l", CAS "l" #0 #(-1).
Local Definition acquire_writer : val :=
  rec: "acquire" "l" :=
    if: try_acquire_writer "l"
      then #()
      else "acquire" "l".
Local Definition release_writer : val :=
  λ: "l", "l" <- #0.

Class rw_spin_lockG Σ := RwLockG { rwlock_tokG : inG Σ (authR (gmultisetUR Qp)) }.
Local Existing Instance rwlock_tokG.

Definition rw_spin_lockΣ : gFunctors := #[GFunctor (authR (gmultisetUR Qp)) ].
Global Instance subG_rw_spin_lockΣ {Σ} : subG rw_spin_lockΣ Σ → rw_spin_lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS_gen hlc Σ, !rw_spin_lockG Σ}.
  Let N := nroot .@ "rw_lock".

  Local Definition rw_state_inv (γ : gname) (l : loc) (Φ : Qp → iProp Σ) : iProp Σ :=
    ∃ z : Z, l ↦ #z ∗
      (* We need *some* ghost state that allows us to establish a contradiction
      in the left disjunct (where the lock is write-locked) when proving
      [release_reader_spec], so we use a fraction of the empty authoritative
      reader set (the rest goes to [writer_locked].) Any fraction would do, but
      the benefit of giving over half to [writer_locked] (and keeping less than
      half here) is that we can prove [writer_locked_exclusive]. *)
      (⌜(z = -1)%Z⌝ ∗ own γ (●{# 1/4} ∅)
      ∨ ⌜(0 ≤ z)%Z⌝ ∗ ∃ (q : Qp) (g : gmultiset Qp),
          own γ (● g) ∗
          ⌜size g = Z.to_nat z⌝ ∗
          ⌜set_fold Qp.add q g = 1%Qp⌝ ∗
          Φ q
      ).
  Local Hint Extern 0 (environments.envs_entails _ (rw_state_inv _ _ _)) =>
    unfold rw_state_inv : core.

  (* This definition is [tc_opaque] because the ▷ around [internal_fractional]
  should be preserved even when taking steps (otherwise it's more annoying to
  re-establish.) *)
  Local Definition is_rw_lock (γ : gname) (lk : val) (Φ : Qp → iProp Σ) : iProp Σ :=
    tc_opaque (▷ internal_fractional Φ ∗
      ∃ l : loc, ⌜lk = #l⌝ ∗ inv N (rw_state_inv γ l Φ))%I.
  Global Instance is_rw_lock_persistent γ lk Φ : Persistent (is_rw_lock γ lk Φ).
  Proof. unfold is_rw_lock, tc_opaque. apply _. Qed.
  Local Hint Extern 0 (environments.envs_entails _ (is_rw_lock _ _ _)) =>
    unfold is_rw_lock : core.

  Local Definition reader_locked (γ : gname) (q : Qp) : iProp Σ := own γ (◯ {[+ q +]}).

  Local Definition writer_locked (γ : gname) : iProp Σ := own γ (● {# 3/4} ∅).

  Local Lemma writer_locked_exclusive γ :
    writer_locked γ -∗ writer_locked γ -∗ False.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hvalid. exfalso.
    rewrite
      auth_auth_dfrac_op_valid
      dfrac_op_own
      dfrac_valid_own in Hvalid.
    by destruct Hvalid as [? _].
  Qed.
  Local Lemma writer_locked_not_reader_locked γ q :
    writer_locked γ -∗ reader_locked γ q -∗ False.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hvalid. exfalso.
    apply auth_both_dfrac_valid in Hvalid as (_ & Hvalid & _).
    generalize (Hvalid 0)=> /cmra_discrete_included_r /gmultiset_included /(_ q).
    rewrite multiplicity_empty multiplicity_singleton. by lia.
  Qed.

  Lemma is_rw_lock_iff γ lk Φ Ψ :
    is_rw_lock γ lk Φ -∗ ▷ □ (∀ q, Φ q ∗-∗ Ψ q) -∗ is_rw_lock γ lk Ψ.
  Proof.
    iIntros "[#HΦdup [%l [-> #Hlockinv]]] #Hiff".
    iSplitR.
    { iApply (internal_fractional_iff with "Hiff HΦdup"). }
    iExists l; iSplitR; first done.
    iApply (inv_iff with "[Hlockinv Hiff //]"); iIntros "!> !>".
    iDestruct "Hiff" as "#Hiff".
    iClear "HΦdup Hlockinv".
    iSplit.
    - iIntros "(%z & ? & Hstate)". iExists z. iFrame.
      iDestruct "Hstate" as "[?|(? & % & % & ? & ? & ? & ?)]".
      + iFrame.
      + iRight.
        iFrame.
        iExists _, _.
        iFrame.
        by iApply "Hiff".
    - iIntros "(%z & ? & Hstate)". iExists z. iFrame.
      iDestruct "Hstate" as "[?|(? & % & % & ? & ? & ? & ?)]".
      + iFrame.
      + iRight.
        iFrame.
        iExists _, _.
        iFrame.
        by iApply "Hiff".
  Qed.

  (* Some helper lemmas for "auth of a multiset" *)
  Local Lemma auth_valid_gmultiset_singleton `{Countable A} dq (v : A) (g : gmultiset A) :
    ✓ (● { dq } g ⋅ ◯ ({[+ v +]})) → v ∈ g.
  Proof.
    rewrite
      auth_both_dfrac_valid_discrete
      gmultiset_included
      gmultiset_singleton_subseteq_l.
    intros (_ & ? & _); assumption.
  Qed.
  Local Lemma own_auth_gmultiset_singleton_2 γ dq v g :
    own γ (● { dq } g) ∗ own γ (◯ ({[+ v +]})) ⊢ ⌜v ∈ g⌝.
  Proof.
    iIntros "[Hauth Hfrag]".
    iCombine "Hauth Hfrag" gives %Hvalid.
    iPureIntro.
    apply (auth_valid_gmultiset_singleton _ _ _ Hvalid).
  Qed.

  Local Lemma newlock_spec (Φ : Qp → iProp Σ) `{!AsFractional P Φ 1} :
    {{{ P }}}
      newlock #()
    {{{ lk γ, RET lk; is_rw_lock γ lk Φ }}}.
  Proof.
    iIntros (φ) "HΦ Hφ".
    wp_lam.
    iMod (own_alloc (● ∅)) as (γ) "Hγ".
    { apply auth_auth_valid; done. }
    wp_alloc l as "Hl".
    iMod (inv_alloc N _ (rw_state_inv γ l Φ) with "[-Hφ]") as "#?".
    { rewrite [P]as_fractional.
      eauto 10 with iFrame. }
    iApply "Hφ".
    iSplitR.
    { iApply fractional_internal_fractional.
      apply (as_fractional_fractional (P:=P)). }
    eauto 10.
  Qed.

  Local Lemma try_acquire_reader_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ }}}
      try_acquire_reader lk
    {{{ (b : bool), RET #b; if b then ∃ q, reader_locked γ q ∗ Φ q else True }}}.
  Proof.
    iIntros (φ) "[#HΦdup (%l & -> & #Hlockinv)] Hφ".
    wp_lam.
    wp_bind (!_)%E.
    iInv "Hlockinv" as (z) "[> Hl Hz]".
    wp_load.
    iSplitL "Hl Hz"; first by eauto with iFrame.
    iModIntro.
    wp_pures.
    destruct (Z.le_dec 0%Z z) as [Hle|?]; last first.
    { rewrite bool_decide_false //.
      wp_pures.
      iApply "Hφ".
      done. }
    rewrite bool_decide_true //.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iInv "Hlockinv" as (z') "[> Hl Hz]".
    wp_cmpxchg as [= ->]|?; last first.
    { iSplitR "Hφ".
      { eauto with iFrame. }
      iModIntro.
      wp_pures.
      by iApply "Hφ". }
    iDestruct "Hz" as "[[-> _]|(Hz_ge_0 & %q & %g & Hg)]"; first done.
    iDestruct "Hg" as "(Hauth & %Hsize & %Hfold & HΦ)".
    rewrite -[q in Φ q]Qp.div_2.
    iDestruct ("HΦdup" $! (q / 2)%Qp (q / 2)%Qp with "HΦ") as "[HΦ HΦgive]".
    iMod (own_update _ _ (●(g ⊎ {[+ (q / 2)%Qp+]}) ⋅
      ◯({[+ (q / 2)%Qp +]})) with "Hauth") as "[Hauth Hview]".
    { apply auth_update_alloc.
      rewrite -{2}[({[+ (q / 2)%Qp+]})]gmultiset_disj_union_left_id.
      apply gmultiset_local_update_alloc. }
    iSplitR "HΦgive Hview Hφ".
    { iExists (z + 1)%Z.
      iModIntro.
      iModIntro.
      iFrame.
      iRight.
      iSplitL "Hz_ge_0"; first by eauto with lia.
      iExists _, _.
      iFrame.
      iSplit.
      { iPureIntro.
        rewrite gmultiset_size_disj_union gmultiset_size_singleton.
        lia. }
      iPureIntro.
      rewrite
        gmultiset_set_fold_disj_union
        gmultiset_set_fold_singleton
        -gmultiset_set_fold_comm_acc.
        { rewrite Qp.div_2 //. }
        intros. rewrite 2!Qp.add_assoc [(_ + q/2)%Qp]Qp.add_comm //. }
    iModIntro.
    wp_pures.
    iApply "Hφ".
    eauto with iFrame.
  Qed.

  Local Lemma acquire_reader_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ }}}
      acquire_reader lk
    {{{ q, RET #(); reader_locked γ q ∗ Φ q }}}.
  Proof.
    iIntros (φ) "#Hislock Hφ".
    iLöb as "IH".
    wp_rec.
    wp_apply (try_acquire_reader_spec with "Hislock"); iIntros ([|]).
    - iIntros "[% ?]".
      wp_if_true.
      iApply "Hφ".
      eauto with iFrame.
    - iIntros.
      wp_if_false.
      iApply "IH".
      eauto.
  Qed.

  Local Lemma release_reader_spec γ lk Φ q :
    {{{ is_rw_lock γ lk Φ ∗ reader_locked γ q ∗ Φ q }}}
      release_reader lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "((#HΦdup & %l & -> & Hlockinv) & Hlocked & HΦ) Hφ".
    wp_lam.
    wp_bind (FAA _ _).
    iInv "Hlockinv" as (z) "[> Hl Hz]".
    wp_faa.
    unfold reader_locked.
    iDestruct "Hz" as "[[_ Hempty]|(%Hz_ge_0 & %q' & %g & Hg & %Hsize & %Hsum & HΦq')]".
    { iExFalso.
      iDestruct (own_auth_gmultiset_singleton_2 with "[$]") as %?.
      multiset_solver. }
    iAssert (⌜(0 < z)%Z ∧ q ∈ g⌝)%I as %?.
    { iDestruct (own_auth_gmultiset_singleton_2 with "[$]") as %?.
      iPureIntro.
      split; last assumption.
      apply Z2Nat.neq_0_pos.
      rewrite -Hsize gmultiset_size_empty_iff.
      multiset_solver. }
    iCombine "Hg Hlocked" as "Hown".
    iMod (own_update _ _ (●(g ∖ {[+ q +]})) with "Hown") as "Hown".
    { apply auth_update_dealloc.
      replace ε with ({[+ q +]} ∖ {[+ q +]} : gmultiset Qp); last first.
      { rewrite gmultiset_difference_diag //. }
      apply gmultiset_local_update_dealloc.
      multiset_solver. }
    iModIntro.
    iSplitR "Hφ".
    { iExists (z + -1)%Z.
      iFrame.
      iRight.
      iSplit.
      { eauto with lia. }
      iExists _, _.
      iDestruct ("HΦdup" $! q q' with "[$HΦ $HΦq']") as "HΦ".
      iModIntro.
      iFrame.
      iSplit.
      { iPureIntro.
        rewrite gmultiset_size_difference; last multiset_solver.
        rewrite gmultiset_size_singleton.
        lia. }
      iPureIntro.
      rewrite -Hsum gmultiset_set_fold_comm_acc; last first.
      { intros. rewrite 2!Qp.add_assoc [(_ + q)%Qp]Qp.add_comm //. }
      rewrite
        -gmultiset_set_fold_singleton
        -gmultiset_set_fold_disj_union
        gmultiset_disj_union_comm
        -gmultiset_disj_union_difference //.
      multiset_solver. }
    wp_pures.
    by iApply "Hφ".
  Qed.

  Local Lemma try_acquire_writer_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ }}}
      try_acquire_writer lk
    {{{ (b : bool), RET #b; if b then writer_locked γ ∗ Φ 1%Qp else True }}}.
  Proof.
    iIntros (φ) "(#HΦdup & %l & -> & #Hlockinv) Hφ".
    wp_lam.
    wp_bind (CmpXchg _ _ _).
    iInv ("Hlockinv") as (z) "[> Hl Hz]".
    wp_cmpxchg as [= ->]|?; last first.
    { iModIntro.
      iSplitL "Hl Hz".
      { eauto with iFrame. }
      wp_pures.
      by iApply "Hφ". }
    iDestruct "Hz" as "[[%H0_eq_1 ?]|(_ & %q & %g & Hg & %Hsize & %Hfold & HΦ)]".
    { done. }
    apply gmultiset_size_empty_inv in Hsize as ->.
    rewrite gmultiset_set_fold_empty in Hfold. subst q.
    rewrite -[in (●{# 1} _)]Qp.quarter_three_quarter.
    iDestruct "Hg" as "[Hg Hg_give]".
    iModIntro.
    iSplitL "Hl Hg".
    { eauto 10 with iFrame. }
    wp_pures.
    iApply "Hφ".
    by iFrame.
  Qed.

  Local Lemma acquire_writer_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ }}}
      acquire_writer lk
    {{{ RET #(); writer_locked γ ∗ Φ 1%Qp }}}.
  Proof.
    iIntros (φ) "#Hislock Hφ".
    iLöb as "IH".
    wp_rec.
    wp_apply (try_acquire_writer_spec with "Hislock"); iIntros ([|]).
    - iIntros.
      wp_if_true.
      iApply "Hφ".
      eauto with iFrame.
    - iIntros.
      wp_if_false.
      iApply "IH".
      eauto.
  Qed.

  Local Lemma release_writer_spec γ lk Φ :
    {{{ is_rw_lock γ lk Φ ∗ writer_locked γ ∗ Φ 1%Qp }}}
      release_writer lk
    {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "((#HΦdup & %l & -> & #Hlockinv) & Hlocked & HΦ) Hφ".
    wp_lam.
    iInv ("Hlockinv") as (z) "[> Hl Hz]".
    wp_store.
    iDestruct "Hz" as "[[? Hg]|(_ & % & % & Hg_owned & _)]"; last first.
    { iExFalso.
      iCombine "Hg_owned Hlocked" gives %Hvalid.
      rewrite
        auth_auth_dfrac_op_valid
        dfrac_op_own
        dfrac_valid_own in Hvalid.
      by destruct Hvalid as [? _]. }
    iCombine "Hg Hlocked" as "Hown".
    rewrite Qp.quarter_three_quarter.
    iSplitR "Hφ"; first by eauto 15 with iFrame.
    by iApply "Hφ".
  Qed.
End proof.

Definition rw_spin_lock : rwlock :=
  {| rw_lock.rwlockG := rw_spin_lockG;
     rw_lock.writer_locked_exclusive _ _ _ _ := writer_locked_exclusive;
     rw_lock.writer_locked_not_reader_locked _ _ _ _ := writer_locked_not_reader_locked;
     rw_lock.is_rw_lock_iff _ _ _ _ := is_rw_lock_iff;
     rw_lock.newlock_spec _ _ _ _ := newlock_spec;
     rw_lock.acquire_reader_spec _ _ _ _ := acquire_reader_spec;
     rw_lock.release_reader_spec _ _ _ _ := release_reader_spec;
     rw_lock.acquire_writer_spec _ _ _ _ := acquire_writer_spec;
     rw_lock.release_writer_spec _ _ _ _ := release_writer_spec |}.
