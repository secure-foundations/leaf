From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Class heapGpreS Σ := HeapGpreS {
  heapGpreS_iris :> invGpreS Σ;
  heapGpreS_heap :> gen_heapGpreS loc (option val) Σ;
  heapGpreS_inv_heap :> inv_heapGpreS loc (option val) Σ;
  heapGpreS_proph :> proph_mapGpreS proph_id (val * val) Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc (option val); inv_heapΣ loc (option val); proph_mapΣ proph_id (val * val)].
Global Instance subG_heapGpreS {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (? κs) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iModIntro. iExists
    (λ σ κs, (gen_heap_interp σ.(heap) ∗ proph_map_interp κs σ.(used_proph_id))%I),
    (λ _, True%I).
  iFrame. iApply (Hwp (HeapGS _ _ _ _ _)). done.
Qed.
