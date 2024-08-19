From iris.algebra Require Import excl auth gset.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Export lock.
From iris.prelude Require Import options.

Local Definition wait_loop: val :=
  rec: "wait_loop" "x" "lk" :=
    let: "o" := !(Fst "lk") in
    if: "x" = "o"
      then #() (* my turn *)
      else "wait_loop" "x" "lk".

Local Definition newlock : val :=
  λ: <>, ((* owner *) ref #0, (* next *) ref #0).

Local Definition acquire : val :=
  rec: "acquire" "lk" :=
    let: "n" := !(Snd "lk") in
    if: CAS (Snd "lk") "n" ("n" + #1)
      then wait_loop "n" "lk"
      else "acquire" "lk".

Local Definition release : val :=
  λ: "lk", (Fst "lk") <- !(Fst "lk") + #1.

(** The CMRAs we need. *)
Class tlockG Σ :=
  tlock_G : inG Σ (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))).
Local Existing Instance tlock_G.

Definition tlockΣ : gFunctors :=
  #[ GFunctor (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))) ].

Global Instance subG_tlockΣ {Σ} : subG tlockΣ Σ → tlockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS_gen hlc Σ, !tlockG Σ}.
  Let N := nroot .@ "ticket_lock".

  Local Definition lock_inv (γ : gname) (lo ln : loc) (R : iProp Σ) : iProp Σ :=
    ∃ o n : nat,
      lo ↦ #o ∗ ln ↦ #n ∗
      own γ (● (Excl' o, GSet (set_seq 0 n))) ∗
      ((own γ (◯ (Excl' o, GSet ∅)) ∗ R) ∨ own γ (◯ (ε, GSet {[ o ]}))).

  Local Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    ∃ lo ln : loc,
      ⌜lk = (#lo, #ln)%V⌝ ∗ inv N (lock_inv γ lo ln R).

  Local Definition issued (γ : gname) (x : nat) : iProp Σ :=
    own γ (◯ (ε, GSet {[ x ]})).

  Local Definition locked (γ : gname) : iProp Σ := ∃ o, own γ (◯ (Excl' o, GSet ∅)).

  Local Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof.
    iIntros "[%σ1 H1] [%σ2 H2]".
    iCombine "H1 H2" gives %[[] _]%auth_frag_op_valid_1.
  Qed.

  Local Lemma is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ∗-∗ R2) -∗ is_lock γ lk R2.
  Proof.
    iDestruct 1 as (lo ln ->) "#Hinv"; iIntros "#HR".
    iExists lo, ln; iSplit; [done|]. iApply (inv_iff with "Hinv").
    iIntros "!> !>"; iSplit; iIntros "(%o & %n & Ho & Hn & H● & H)";
      iExists o, n; iFrame "Ho Hn H●";
      (iDestruct "H" as "[[H◯ H]|H◯]"; [iLeft; iFrame "H◯"; by iApply "HR"|by iRight]).
  Qed.

  Local Lemma newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". wp_lam.
    wp_alloc ln as "Hln". wp_alloc lo as "Hlo".
    iMod (own_alloc (● (Excl' 0, GSet ∅) ⋅ ◯ (Excl' 0, GSet ∅))) as (γ) "[Hγ Hγ']".
    { by apply auth_both_valid_discrete. }
    iMod (inv_alloc _ _ (lock_inv γ lo ln R) with "[-HΦ]").
    { iNext. rewrite /lock_inv.
      iExists 0, 0. auto with iFrame. }
    wp_pures. iModIntro. iApply ("HΦ" $! (#lo, #ln)%V γ). iExists lo, ln. eauto.
  Qed.

  Local Lemma wait_loop_spec γ lk x R :
    {{{ is_lock γ lk R ∗ issued γ x }}} wait_loop #x lk {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "[Hl Ht] HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iLöb as "IH". wp_rec. subst. wp_pures. wp_bind (! _)%E.
    iInv N as (o n) "(Hlo & Hln & Ha)".
    wp_load. destruct (decide (x = o)) as [->|Hneq].
    - iDestruct "Ha" as "[Hainv [[Ho HR] | Haown]]".
      + iModIntro. iFrame "Hlo Hln Hainv Ht".
        wp_pures. case_bool_decide; [|done]. wp_if.
        iApply ("HΦ" with "[-]"). rewrite /locked. iFrame.
      + iCombine "Ht Haown"
          gives %[_ ?%gset_disj_valid_op]%auth_frag_op_valid_1.
        set_solver.
    - iModIntro. iFrame "Hlo Hln Ha".
      wp_pures. case_bool_decide; [simplify_eq |].
      wp_if. iApply ("IH" with "Ht"). iNext. by iExact "HΦ".
  Qed.

  Local Lemma acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (ϕ) "Hl HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iLöb as "IH". wp_rec. wp_bind (! _)%E. simplify_eq/=. wp_proj.
    iInv N as (o n) "[Hlo [Hln Ha]]".
    wp_load. iModIntro. iFrame "Hlo Hln Ha".
    wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as (o' n') "(>Hlo' & >Hln' & >Hauth & Haown)".
    destruct (decide (#n' = #n))%V as [[= ->%Nat2Z.inj] | Hneq].
    - iMod (own_update with "Hauth") as "[Hauth Hofull]".
      { eapply auth_update_alloc, prod_local_update_2.
        eapply (gset_disj_alloc_empty_local_update _ {[ n ]}).
        apply (set_seq_S_end_disjoint 0). }
      rewrite -(set_seq_S_end_union_L 0).
      wp_cmpxchg_suc. iModIntro. iSplitL "Hlo' Hln' Haown Hauth".
      { iNext. iExists o', (S n).
        rewrite Nat2Z.inj_succ -Z.add_1_r. by iFrame. }
      wp_pures.
      iApply (wait_loop_spec γ (#lo, #ln) with "[-HΦ]").
      + rewrite /is_lock; eauto 10.
      + by iNext.
    - wp_cmpxchg_fail. iModIntro. iFrame "Hlo' Hln' Hauth Haown".
      wp_pures. by iApply "IH"; auto.
  Qed.

  Local Lemma release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hl & Hγ & HR) HΦ". iDestruct "Hl" as (lo ln ->) "#Hinv".
    iDestruct "Hγ" as (o) "Hγo".
    wp_lam. wp_proj. wp_bind (! _)%E.
    iInv N as (o' n) "(>Hlo & >Hln & >Hauth & Haown)".
    wp_load.
    iCombine "Hauth Hγo" gives
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
    iModIntro. iFrame. wp_pures.
    iInv N as (o' n') "(>Hlo & >Hln & >Hauth & Haown)".
    iApply wp_fupd. wp_store.
    iCombine "Hauth Hγo" gives
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid_discrete.
    iDestruct "Haown" as "[[Hγo' _]|Haown]".
    { iCombine "Hγo Hγo'" gives %[[] ?]%auth_frag_op_valid_1. }
    iMod (own_update_2 with "Hauth Hγo") as "[Hauth Hγo]".
    { apply auth_update, prod_local_update_1.
      by apply option_local_update, (exclusive_local_update _ (Excl (S o))). }
    iModIntro. iSplitR "HΦ"; last by iApply "HΦ".
    iIntros "!> !>". iExists (S o), n'.
    rewrite Nat2Z.inj_succ -Z.add_1_r. auto with iFrame.
  Qed.
End proof.

Definition ticket_lock : lock :=
  {| lock.lockG := tlockG;
     lock.locked_exclusive _ _ _ _ := locked_exclusive;
     lock.is_lock_iff _ _ _ _ := is_lock_iff;
     lock.newlock_spec _ _ _ _ := newlock_spec;
     lock.acquire_spec _ _ _ _ := acquire_spec;
     lock.release_spec _ _ _ _ := release_spec |}.
