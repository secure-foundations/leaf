From iris.proofmode Require Import tactics.
From iris.program_logic Require Export total_adequacy.
From iris.heap_lang Require Export adequacy.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition heap_total Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total _ _); iIntros (?) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init [] σ.(used_proph_id)) as (?) "Hp".
  iModIntro.
  iExists
    (λ σ κs _, (gen_heap_interp σ.(heap) ∗ proph_map_interp κs σ.(used_proph_id))%I),
    (λ _, True%I); iFrame.
  iApply (Hwp (HeapGS _ _ _ _ _)). done.
Qed.
