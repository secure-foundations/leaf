From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra.lib Require Import mono_nat.
From iris.algebra Require Import numbers.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
Set Default Proof Using "Type".

Class lrustGpreS Σ := HeapGpreS {
  lrustGpreS_iris :> invGpreS Σ;
  lrustGpreS_heap :> inG Σ (authR heapUR);
  lrustGpreS_heap_freeable :> inG Σ (authR heap_freeableUR);
  lrustGpreS_time :> timePreG Σ
}.

Definition lrustΣ : gFunctors :=
  #[invΣ; timeΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR))].
Global Instance subG_heapPreG {Σ} : subG lrustΣ Σ → lrustGpreS Σ.
Proof. solve_inG. Qed.

Definition lrust_adequacy Σ `{!lrustGpreS Σ} e σ φ :
  (∀ `{!lrustGS Σ}, time_ctx -∗ WP e {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt. intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=>?.
  iMod (own_alloc (● to_heap σ)) as (vγ) "Hvγ".
  { apply (auth_auth_valid (to_heap _)), to_heap_valid. }
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  iMod time_init as (Htime) "[TIME Htime]"; [done|].
  set (Hheap := HeapGS _ _ _ vγ fγ).
  iModIntro. iExists NotStuck, _, [_], _, _. simpl.
  iDestruct (Hwp (LRustGS _ _ Hheap Htime) with "TIME") as "$".
  iSplitL; first by auto with iFrame. iIntros ([|e' [|]]? -> ??) "//".
  iIntros "[??] [?_] _". iApply fupd_mask_weaken; [|iIntros "_ !>"]; [done|].
  iSplit; [|done]. iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.
