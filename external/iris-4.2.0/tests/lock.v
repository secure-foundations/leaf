From iris.heap_lang Require Import proofmode notation adequacy lib.spin_lock.
From iris.prelude Require Import options.

(* For printing tests we want stable names. *)
Unset Mangle Names.

(** Make sure the lock type class works to write generic clients and
specifications. *)
Section lock_gen.
  Context `{!lock}.

  Definition lock_client_gen : expr :=
    let: "l" := ref #10 in
    let: "lock" := newlock #() in
    acquire "lock";;
    "l" <- #42;;
    release "lock".

  Lemma wp_lock_client_gen `{!heapGS Σ, !lockG Σ} :
    ⊢ WP lock_client_gen {{ _, True }}.
  Proof.
    unfold lock_client_gen. wp_alloc l as "Hl".
    wp_smart_apply (newlock_spec (∃ n : Z, l ↦ #n) with "[Hl]")
      as (lk γ) "#Hlock"; first by eauto.
    wp_smart_apply (acquire_spec with "Hlock") as "(Hlocked & %v & Hloc)".
    wp_store.
    wp_smart_apply (release_spec with "[$Hlock $Hlocked Hloc]"); by eauto.
  Qed.
End lock_gen.

(** Make sure the lock type class works to write clients and
specifications for specific locks (here: spin lock). *)
Section lock_spin.
  Local Existing Instance spin_lock.

  Definition lock_client_spin : expr :=
    let: "l" := ref #10 in
    let: "lock" := newlock #() in
    acquire "lock";;
    "l" <- #42;;
    release "lock".

  (* Making sure that using [spin_lockG] here works, not just [lockG]. *)
  Check "wp_lock_client_spin".
  Lemma wp_lock_client_spin `{!heapGS Σ, !spin_lockG Σ} :
    ⊢ WP lock_client_spin {{ _, True }}.
  Proof.
    unfold lock_client_spin.
    (* This should not unfold the [newlock], [acquire], and [release]
    projections. That is, it should not show [spin_lock.<something>]. *)
    simpl. Show.
    wp_alloc l as "Hl".
    wp_smart_apply (newlock_spec (∃ n : Z, l ↦ #n) with "[Hl]")
      as (lk γ) "#Hlock"; first by eauto.
    wp_smart_apply (acquire_spec with "Hlock") as "(Hlocked & %v & Hloc)".
    wp_store.
    wp_smart_apply (release_spec with "[$Hlock $Hlocked Hloc]"); by eauto.
  Qed.
End lock_spin.

(** Making sure that the [lockG/spin_lockG] conditions are resolved when using adequacy. For
the generic client, we need to instantiate it with a specific lock for that to
make sense. *)
Section lock_adequacy.
  Local Existing Instance spin_lock.

  Lemma lock_client_gen_adequate σ :
    adequate NotStuck lock_client_gen σ (λ _ _, True).
  Proof.
    set (Σ := #[heapΣ; spin_lockΣ]).
    apply (heap_adequacy Σ); iIntros (?) "_".
    iApply wp_lock_client_gen.
  Qed.

  Lemma lock_client_spin_adequate σ :
    adequate NotStuck lock_client_spin σ (λ _ _, True).
  Proof.
    set (Σ := #[heapΣ; spin_lockΣ]).
    apply (heap_adequacy Σ); iIntros (?) "_".
    iApply wp_lock_client_gen.
  Qed.
End lock_adequacy.
