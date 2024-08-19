(** A TaDA-style logically atomic specification for a lock, derived for an
    arbitrary implementation of the lock interface. The opposite direction
    could also be derived rather easily (modulo a later in the [acquire] postcondition
    or a restriction to timeless lock invariants), as shown in the TaDA paper.

    In essence, this is an instance of the general fact that 'invariant-based'
    ("HoCAP-style") logically atomic specifications are equivalent to TaDA-style
    logically atomic specifications; see
    <https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/logatom/elimination_stack/hocap_spec.v>
    for that being worked out and explained in more detail for a stack specification.
*)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation atomic_heap lock.
From iris.prelude Require Import options.

Inductive state := Free | Locked.

Class alockG Σ := LockG { lock_tokG : ghost_varG Σ state }.
Local Existing Instance lock_tokG.
Definition alockΣ : gFunctors := #[ghost_varΣ state].
Global Instance subG_alockΣ {Σ} : subG alockΣ Σ → alockG Σ.
Proof. solve_inG. Qed.

Section tada.
  Context `{!heapGS Σ, !alockG Σ, !lock, !lockG Σ}.

  Record tada_lock_name := TadaLockName {
    tada_lock_name_state : gname;
    tada_lock_name_lock : lock_name;
  }.
  
  Definition tada_lock_state (γ : tada_lock_name) (s : state) : iProp Σ :=
    ghost_var γ.(tada_lock_name_state) (3/4) s ∗
    if s is Locked then
      locked γ.(tada_lock_name_lock) ∗ ghost_var γ.(tada_lock_name_state) (1/4) Locked
    else True.
  Definition tada_is_lock (γ : tada_lock_name) (lk : val) : iProp Σ :=
    is_lock γ.(tada_lock_name_lock) lk
      (ghost_var γ.(tada_lock_name_state) (1/4) Free).

  Global Instance tada_is_lock_persistent γ lk : Persistent (tada_is_lock γ lk).
  Proof. apply _. Qed.
  Global Instance tada_lock_state_timeless γ s : Timeless (tada_lock_state γ s).
  Proof. destruct s; apply _. Qed.

  Lemma tada_lock_state_exclusive γ s1 s2 :
    tada_lock_state γ s1 -∗ tada_lock_state γ s2 -∗ False.
  Proof.
    iIntros "[Hvar1 _] [Hvar2 _]".
    iCombine "Hvar1 Hvar2" gives %[Hval _].
    exfalso. done.
  Qed.

  Lemma newlock_tada_spec :
    {{{ True }}}
      newlock #()
    {{{ lk γ, RET lk; tada_is_lock γ lk ∗ tada_lock_state γ Free }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iMod (ghost_var_alloc Free) as (γvar) "Hvar".
    replace 1%Qp with (3/4 + 1/4)%Qp; last first.
    { rewrite Qp.three_quarter_quarter //. }
    iDestruct "Hvar" as "[Hvar1 Hvar2]".
    wp_apply (newlock_spec with "Hvar2") as (lk γlock) "Hlock".
    iApply ("HΦ" $! lk (TadaLockName _ _)).
    iFrame.
  Qed.

  Lemma acquire_tada_spec γ lk :
    tada_is_lock γ lk -∗
    <<{ ∀∀ s, tada_lock_state γ s }>>
      acquire lk @ ∅
    <<{ ⌜ s = Free ⌝ ∗ tada_lock_state γ Locked | RET #() }>>.
  Proof.
    iIntros "#Hislock %Φ AU". iApply wp_fupd.
    wp_apply (acquire_spec with "Hislock") as "[Hlocked Hvar1]".
    iMod "AU" as (s) "[[Hvar2 _] [_ Hclose]]".
    iCombine "Hvar1 Hvar2" gives %[_ <-].
    iMod (ghost_var_update_2 Locked with "Hvar1 Hvar2") as "[Hvar1 Hvar2]".
    { rewrite Qp.quarter_three_quarter //. }
    iMod ("Hclose" with "[$Hvar2 $Hlocked $Hvar1]"); done.
  Qed.

  Lemma release_tada_spec γ lk :
    tada_is_lock γ lk -∗
    <<{ tada_lock_state γ Locked }>>
      release lk @ ∅
    <<{ tada_lock_state γ Free | RET #() }>>.
  Proof.
    iIntros "#Hislock %Φ AU". iApply fupd_wp.
    iMod "AU" as "[[Hvar1 [Hlocked Hvar2]] [_ Hclose]]".
    iMod (ghost_var_update_2 Free with "Hvar1 Hvar2") as "[Hvar1 Hvar2]".
    { rewrite Qp.three_quarter_quarter //. }
    iMod ("Hclose" with "[$Hvar1]"). iModIntro.
    wp_apply (release_spec with "[$Hislock $Hlocked $Hvar2]").
    auto.
  Qed.

End tada.

Global Typeclasses Opaque tada_is_lock tada_lock_state.
