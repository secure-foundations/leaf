From iris.base_logic.lib Require Import gen_inv_heap invariants.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Import lang adequacy total_adequacy proofmode notation.
From iris.prelude Require Import options.

(* For printing tests we want stable names. *)
Unset Mangle Names.

Section tests.
  Context `{!heapGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Definition simpl_test :
    ⌜(10 = 4 + 6)%nat⌝ -∗
    WP let: "x" := ref #1 in "x" <- !"x";; !"x" {{ v, ⌜v = #1⌝ }}.
  Proof.
    iIntros "?". wp_alloc l. repeat wp_pure || wp_load || wp_store.
    match goal with
    | |- context [ (10 = 4 + 6)%nat ] => done
    end.
  Qed.

  Definition val_scope_test_1 := SOMEV (#(), #()).

  Definition heap_e : expr :=
    let: "x" := ref #1 in "x" <- !"x" + #1 ;; !"x".

  Check "heap_e_spec".
  Lemma heap_e_spec E : ⊢ WP heap_e @ E {{ v, ⌜v = #2⌝ }}.
  Proof.
    iIntros "". rewrite /heap_e. Show.
    wp_alloc l as "?". wp_pures. wp_bind (!_)%E. wp_load. Show. (* No fupd was added *)
    wp_store. by wp_load.
  Qed.

  Definition heap_e2 : expr :=
    let: "x" := ref #1 in
    let: "y" := ref #1 in
    "x" <- !"x" + #1 ;; !"x".

  Check "heap_e2_spec".
  Lemma heap_e2_spec E : ⊢ WP heap_e2 @ E [{ v, ⌜v = #2⌝ }].
  Proof.
    iIntros "". rewrite /heap_e2.
    wp_alloc l as "Hl". Show. wp_alloc l'. do 2 wp_pure.
    wp_bind (!_)%E. wp_load. Show. (* No fupd was added *)
    wp_store. wp_load. done.
  Qed.

  Definition heap_e3 : expr :=
    let: "x" := #true in
    let: "f" := λ: "z", "z" + #1 in
    if: "x" then "f" #0 else "f" #1.

  Lemma heap_e3_spec E : ⊢ WP heap_e3 @ E [{ v, ⌜v = #1⌝ }].
  Proof.
    iIntros "". rewrite /heap_e3.
    by repeat (wp_pure _).
  Qed.

  Definition heap_e4 : expr :=
    let: "x" := (let: "y" := ref (ref #1) in ref "y") in
    ! ! !"x".

  Lemma heap_e4_spec : ⊢ WP heap_e4 [{ v, ⌜ v = #1 ⌝ }].
  Proof.
    rewrite /heap_e4. wp_alloc l. wp_alloc l'.
    wp_alloc l''. by repeat wp_load.
  Qed.

  Definition heap_e5 : expr :=
    let: "x" := ref (ref #1) in ! ! "x" + FAA (!"x") (#10 + #1).

  Lemma heap_e5_spec E : ⊢ WP heap_e5 @ E [{ v, ⌜v = #13⌝ }].
  Proof.
    rewrite /heap_e5. wp_alloc l. wp_alloc l'.
    wp_load. wp_faa. do 2 wp_load. by wp_pures.
  Qed.

  Definition heap_e6 : val := λ: "v", "v" = "v".

  Lemma heap_e6_spec (v : val) :
    val_is_unboxed v → ⊢ WP heap_e6 v {{ w, ⌜ w = #true ⌝ }}.
  Proof. intros ?. wp_lam. wp_op. by case_bool_decide. Qed.

  Definition heap_e7 : val := λ: "v", CmpXchg "v" #0 #1.

  Lemma heap_e7_spec_total l : l ↦ #0 -∗ WP heap_e7 #l [{_,  l ↦ #1 }].
  Proof. iIntros. wp_lam. wp_cmpxchg_suc. auto. Qed.

  Check "heap_e7_spec".
  Lemma heap_e7_spec l : ▷^2 l ↦ #0 -∗ WP heap_e7 #l {{_,  l ↦ #1 }}.
  Proof. iIntros. wp_lam. Show. wp_cmpxchg_suc. Show. auto. Qed.

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := "y" + #1 in
      if: "yp" < "x" then "pred" "x" "yp" else "y".
  Definition Pred : val :=
    λ: "x",
      if: "x" ≤ #0 then -FindPred (-"x" + #2) #0 else FindPred "x" #0.

  Lemma FindPred_spec n1 n2 E Φ :
    (n1 < n2)%Z →
    Φ #(n2 - 1) -∗ WP FindPred #n2 #n1 @ E [{ Φ }].
  Proof.
    iIntros (Hn) "HΦ".
    iInduction (Z.gt_wf n2 n1) as [n1' _] "IH" forall (Hn).
    wp_rec. wp_pures. case_bool_decide; wp_if.
    - iApply ("IH" with "[%] [%] HΦ"); lia.
    - by assert (n1' = n2 - 1)%Z as -> by lia.
  Qed.

  Lemma Pred_spec n E Φ : Φ #(n - 1) -∗ WP Pred #n @ E [{ Φ }].
  Proof.
    iIntros "HΦ". wp_lam.
    wp_op. case_bool_decide.
    - wp_smart_apply FindPred_spec; first lia. wp_pures.
      by replace (n - 1)%Z with (- (-n + 2 - 1))%Z by lia.
    - wp_smart_apply FindPred_spec; eauto with lia.
  Qed.

  Lemma Pred_user E :
    ⊢ WP let: "x" := Pred #42 in Pred "x" @ E [{ v, ⌜v = #40⌝ }].
  Proof. iIntros "". wp_apply Pred_spec. by wp_smart_apply Pred_spec. Qed.

  Definition Id : val :=
    rec: "go" "x" :=
      if: "x" = #0 then #() else "go" ("x" - #1).

  (** These tests specially test the handling of the [vals_compare_safe]
  side-condition of the [=] operator. *)
  Lemma Id_wp (n : nat) : ⊢ WP Id #n {{ v, ⌜ v = #() ⌝ }}.
  Proof.
    iInduction n as [|n] "IH"; wp_rec; wp_pures; first done.
    by replace (S n - 1)%Z with (n:Z) by lia.
  Qed.
  Lemma Id_twp (n : nat) : ⊢ WP Id #n [{ v, ⌜ v = #() ⌝ }].
  Proof.
    iInduction n as [|n] "IH"; wp_rec; wp_pures; first done.
    by replace (S n - 1)%Z with (n:Z) by lia.
  Qed.

  Definition compare_pointers : val := λ: <>,
    let: "x" := ref #0 in
    let: "y" := ref #0 in
    ("x", "y", "x" ≤ "y").

  Lemma wp_compare_pointers E :
    ⊢ WP compare_pointers #() @ E [{ v, ∃ l1 l2 : loc,
        ⌜v = (#l1, #l2,
              #(bool_decide (loc_car l1 ≤ loc_car l2)))%V⌝ }].
  Proof.
    rewrite /compare_pointers. wp_pures.
    wp_alloc l1 as "H1".
    wp_alloc l2 as "H2".
    wp_pures. by eauto.
  Qed.

  (* Make sure [wp_bind] works even when it changes nothing. *)
  Lemma wp_bind_nop (e : expr) :
    ⊢ WP e + #0 {{ _, True }}.
  Proof. wp_bind (e + #0)%E. Abort.
  Lemma wp_bind_nop (e : expr) :
    ⊢ WP e + #0 [{ _, True }].
  Proof. wp_bind (e + #0)%E. Abort.

  Check "wp_load_fail".
  Lemma wp_load_fail :
    ⊢ WP Fork #() {{ _, True }}.
  Proof. Fail wp_load. Abort.
  Lemma twp_load_fail :
    ⊢ WP Fork #() [{ _, True }].
  Proof. Fail wp_load. Abort.
  Check "wp_load_no_ptsto".
  Lemma wp_load_fail_no_ptsto (l : loc) :
    ⊢ WP ! #l {{ _, True }}.
  Proof. Fail wp_load. Abort.

  Check "wp_store_fail".
  Lemma wp_store_fail :
    ⊢ WP Fork #() {{ _, True }}.
  Proof. Fail wp_store. Abort.
  Lemma twp_store_fail :
    ⊢ WP Fork #() [{ _, True }].
  Proof. Fail wp_store. Abort.
  Check "wp_store_no_ptsto".
  Lemma wp_store_fail_no_ptsto (l : loc) :
    ⊢ WP #l <- #0 {{ _, True }}.
  Proof. Fail wp_store. Abort.

  Check "(t)wp_bind_fail".
  Lemma wp_bind_fail : ⊢ WP of_val #() {{ v, True }}.
  Proof. Fail wp_bind (!_)%E. Abort.
  Lemma twp_bind_fail : ⊢ WP of_val #() [{ v, True }].
  Proof. Fail wp_bind (!_)%E. Abort.

  Lemma wp_apply_evar e P :
    P -∗ (∀ Q Φ, Q -∗ WP e {{ Φ }}) -∗ WP e {{ _, True }}.
  Proof. iIntros "HP HW". wp_apply "HW". iExact "HP". Qed.

  Lemma wp_pures_val (b : bool) :
    ⊢ WP of_val #b {{ _, True }}.
  Proof. wp_pures. done. Qed.
  Lemma twp_pures_val (b : bool) :
    ⊢ WP of_val #b [{ _, True }].
  Proof. wp_pures. done. Qed.

  Lemma wp_cmpxchg l v :
    val_is_unboxed v →
    l ↦ v -∗ WP CmpXchg #l v v {{ _, True }}.
  Proof.
    iIntros (?) "?". wp_cmpxchg as ? | ?; done.
  Qed.

  Lemma wp_xchg l (v₁ v₂ : val) :
    {{{ l ↦ v₁ }}}
      Xchg #l v₂
    {{{ RET v₁; l ↦ v₂ }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_xchg.
    iApply "HΦ" => //.
  Qed.

   Lemma twp_xchg l (v₁ v₂ : val) :
     l ↦ v₁ -∗
       WP  Xchg #l v₂ [{ v₁, l ↦ v₂ }].
  Proof.
    iIntros "Hl".
    wp_xchg => //.
  Qed.

  Lemma wp_xchg_inv N l (v : val) :
    {{{ inv N (∃ v, l ↦ v) }}}
      Xchg #l v
    {{{ v', RET v'; True }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iInv "Hl" as (v') "Hl" "Hclose".
    wp_xchg.
    iApply "HΦ".
    iApply "Hclose".
    iExists _ => //.
  Qed.

  Lemma wp_alloc_split :
    ⊢ WP Alloc #0 {{ _, True }}.
  Proof. wp_alloc l as "[Hl1 Hl2]". Show. done. Qed.

  Lemma wp_alloc_drop :
    ⊢ WP Alloc #0 {{ _, True }}.
  Proof. wp_alloc l as "_". Show. done. Qed.

  Check "wp_nonclosed_value".
  Lemma wp_nonclosed_value :
    ⊢ WP let: "x" := #() in (λ: "y", "x")%V #() {{ _, True }}.
  Proof. wp_let. wp_lam. Fail wp_pure _. Show. Abort.

  Lemma wp_alloc_array n :
    (0 < n)%Z →
    ⊢ {{{ True }}}
        AllocN #n #0
      {{{ l, RET #l;  l ↦∗ replicate (Z.to_nat n) #0 }}}.
  Proof.
    iIntros (? Φ) "!> _ HΦ".
    wp_alloc l as "?"; first done.
    by iApply "HΦ".
  Qed.

  Lemma twp_alloc_array n :
    (0 < n)%Z →
    ⊢ [[{ True }]]
        AllocN #n #0
      [[{ l, RET #l; l ↦∗ replicate (Z.to_nat n) #0 }]].
  Proof.
    iIntros (? Φ) "!> _ HΦ".
    wp_alloc l as "?"; first done. Show.
    by iApply "HΦ".
  Qed.

  Lemma wp_load_array l :
    {{{ l ↦∗ [ #0;#1;#2 ] }}} !(#l +ₗ #1) {{{ RET #1; True }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_op.
    wp_apply (wp_load_offset _ _ _ _ 1 with "Hl"); first done.
    iIntros "Hl". by iApply "HΦ".
  Qed.

  Check "test_array_fraction_destruct".
  Lemma test_array_fraction_destruct l vs :
    l ↦∗ vs -∗ l ↦∗{#1/2} vs ∗ l ↦∗{#1/2} vs.
  Proof.
    iIntros "[Hl1 Hl2]". Show.
    by iFrame.
  Qed.

  Lemma test_array_fraction_combine l vs :
    l ↦∗{#1/2} vs -∗ l↦∗{#1/2} vs -∗ l ↦∗ vs.
  Proof.
    iIntros "Hl1 Hl2".
    iSplitL "Hl1"; by iFrame.
  Qed.

  Lemma test_array_app l vs1 vs2 :
    l ↦∗ (vs1 ++ vs2) -∗ l ↦∗ (vs1 ++ vs2).
  Proof.
    iIntros "H". iDestruct (array_app with "H") as "[H1 H2]".
    iApply array_app. iSplitL "H1"; done.
  Qed.

  Lemma test_array_app_split l vs1 vs2 :
    l ↦∗ (vs1 ++ vs2) -∗ l ↦∗{#1/2} (vs1 ++ vs2).
  Proof.
    iIntros "[$ _]". (* splits the fraction, not the app *)
  Qed.

  Lemma test_wp_free l v :
    {{{ l ↦ v }}} Free #l {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_free. iApply "HΦ". done.
  Qed.

  Lemma test_twp_free l v :
    [[{ l ↦ v }]] Free #l [[{ RET #(); True }]].
  Proof.
    iIntros (Φ) "Hl HΦ". wp_free. iApply "HΦ". done.
  Qed.

  Check "test_wp_finish_fupd".
  Lemma test_wp_finish_fupd (v : val) :
    ⊢ WP of_val v {{ v, |={⊤}=> True }}.
  Proof.
    wp_pures. Show. (* No second fupd was added. *)
  Abort.

  Check "test_twp_finish_fupd".
  Lemma test_twp_finish_fupd (v : val) :
    ⊢ WP of_val v [{ v, |={⊤}=> True }].
  Proof.
    wp_pures. Show. (* No second fupd was added. *)
  Abort.

  Check "test_heaplang_not_unfolded".
  Lemma test_heaplang_not_unfolded :
    ⊢@{iPropI Σ} |={⊤}=> True.
  Proof.
    cbn.
    Set Printing All.
    Show.
    Unset Printing All.
  Abort.

  Check "test_wp_pure_credit_succeed".
  Lemma test_wp_pure_credit_succeed P :
    ⊢ WP #42 + #420 {{ v, ▷ P ={∅}=∗ P }}.
  Proof.
    wp_pure credit:"Hcred". Show.
    iIntros "!> HP". iMod (lc_fupd_elim_later with "Hcred HP"). auto.
  Qed.

  Check "test_wp_pure_credit_fail".
  Lemma test_wp_pure_credit_fail :
    ⊢ True -∗ WP #42 + #420 {{ v, True }}.
  Proof.
    iIntros "Hcred".
    Fail wp_pure credit:"Hcred".
  Abort.

End tests.

Section mapsto_tests.
  Context `{!heapGS Σ}.

  (* Test that the different versions of mapsto work with the tactics, parses,
     and prints correctly. *)

  (* Loading from a persistent points-to predicate in the _persistent_ context. *)
  Lemma persistent_mapsto_load_persistent l v :
    {{{ l ↦□ v }}} ! #l {{{ RET v; True }}}.
  Proof. iIntros (Φ) "#Hl HΦ". Show. wp_load. by iApply "HΦ". Qed.

  (* Loading from a persistent points-to predicate in the _spatial_ context. *)
  Lemma persistent_mapsto_load_spatial l v :
    {{{ l ↦□ v }}} ! #l {{{ RET v; True }}}.
  Proof. iIntros (Φ) "Hl HΦ". wp_load. by iApply "HΦ". Qed.

  Lemma persistent_mapsto_twp_load_persistent l v :
    [[{ l ↦□ v }]] ! #l [[{ RET v; True }]].
  Proof. iIntros (Φ) "#Hl HΦ". wp_load. by iApply "HΦ". Qed.

  Lemma persistent_mapsto_twp_load_spatial l v :
    [[{ l ↦□ v }]] ! #l [[{ RET v; True }]].
  Proof. iIntros (Φ) "Hl HΦ". wp_load. by iApply "HΦ". Qed.

  Lemma persistent_mapsto_load l (n : nat) :
    {{{ l ↦ #n }}} Store #l (! #l + #5) ;; ! #l {{{ RET #(n + 5); l ↦□ #(n + 5) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    wp_load. wp_store.
    iMod (mapsto_persist with "Hl") as "#Hl".
    wp_load. by iApply "HΦ".
  Qed.

  (* Loading from the general mapsto for any [dfrac]. *)
  Lemma general_mapsto dq l v :
    [[{ l ↦{dq} v }]] ! #l [[{ RET v; True }]].
  Proof.
    iIntros (Φ) "Hl HΦ". Show. wp_load. by iApply "HΦ".
  Qed.

  (* Make sure that we can split a mapsto containing an evar. *)
  Lemma mapsto_evar_iSplit l v :
    l ↦{#1 / 2} v -∗  ∃ q, l ↦{#1 / 2 + q} v.
  Proof. iIntros "H". iExists _. iSplitL; first by iAssumption. Abort.

  Lemma mapsto_frame_1 l v q1 q2 :
    l ↦{#q1} v -∗ l ↦{#q2} v -∗ l ↦{#q1 + q2} v.
  Proof. iIntros "H1 H2". iFrame "H1". iExact "H2". Qed.

  Lemma mapsto_frame_2 l v q :
    l ↦{#q/2} v -∗ l ↦{#q/2} v -∗ l ↦{#q} v.
  Proof. iIntros "H1 H2". iFrame "H1". iExact "H2". Qed.

  Lemma mapsto_combine_2 l v1 q1 v2 q2 :
    l ↦{#q1} v1 -∗ l ↦{#q2} v2 -∗
    l ↦{#(q1 + q2)} v1 ∗ ⌜q1 + q2 ≤ 1⌝%Qp ∗ ⌜v1 = v2⌝.
  Proof. iIntros "H1 H2". by iCombine "H1 H2" as "$" gives %[? ->]. Qed.

  Lemma mapsto_combine_3 l v1 q1 v2 q2 v3 q3 :
    l ↦{#q1} v1 -∗ l ↦{#q2} v2 -∗ l ↦{#q3} v3 -∗
    l ↦{#(q1 + (q2 + q3))} v1 ∗ ⌜q1 + (q2 + q3) ≤ 1⌝%Qp ∗ ⌜v1 = v2⌝ ∗ ⌜v2 = v3⌝.
  Proof.
    iIntros "H1 H2 H3".
    by iCombine "H1 H2 H3" as "$" gives %[[_ ->] [? ->]].
  Qed.

  Lemma mapsto_combine_4 l v1 q1 v2 q2 v3 q3 v4 q4 :
    l ↦{#q1} v1 -∗ l ↦{#q2} v2 -∗ l ↦{#q3} v3 -∗ l ↦{#q4} v4 -∗
    l ↦{#(q1 + (q2 + (q3 + q4)))} v1 ∗ ⌜q1 + (q2 + (q3 + q4)) ≤ 1⌝%Qp ∗
      ⌜v1 = v2⌝ ∗ ⌜v2 = v3⌝ ∗ ⌜v3 = v4⌝.
  Proof.
    iIntros "H1 H2 H3 H4".
    iCombine "H1 H2 H3 H4" as "$" gives %H. Show.
    by destruct H as [[[_ ->] [_ ->]] [? ->]].
  Qed.
End mapsto_tests.

Section inv_mapsto_tests.
  Context `{!heapGS Σ}.

  (* Make sure these parse and type-check. *)
  Lemma inv_mapsto_own_test (l : loc) : ⊢ l ↦_(λ _, True) #5. Abort.
  Lemma inv_mapsto_test (l : loc) : ⊢ l ↦_(λ _, True) □. Abort.

  (* Make sure [setoid_rewrite] works. *)
  Lemma inv_mapsto_setoid_rewrite (l : loc) (I : val → Prop) :
    (∀ v, I v ↔ I #true) →
    ⊢ l ↦_(λ v, I v) □.
  Proof.
    iIntros (Heq). setoid_rewrite Heq. Show.
  Abort.
End inv_mapsto_tests.

Section atomic.
  Context `{!heapGS Σ}.
  Implicit Types P Q : iProp Σ.

  (* These tests check if a side-condition for [Atomic] is generated *)
  Check "wp_iMod_fupd_atomic".
  Lemma wp_iMod_fupd_atomic E1 E2 P :
    (|={E1,E2}=> P) -∗ WP #() #() @ E1 {{ _, True }}.
  Proof.
    iIntros "H". iMod "H". Show.
  Abort.

  Check "wp_iInv_atomic".
  Lemma wp_iInv_atomic N E P :
    ↑ N ⊆ E →
    inv N P -∗ WP #() #() @ E {{ _, True }}.
  Proof.
    iIntros (?) "H". iInv "H" as "H" "Hclose". Show.
  Abort.
  Check "wp_iInv_atomic_acc".
  Lemma wp_iInv_atomic_acc N E P :
    ↑ N ⊆ E →
    inv N P -∗ WP #() #() @ E {{ _, True }}.
  Proof.
    (* Test if a side-condition for [Atomic] is generated *)
    iIntros (?) "H". iInv "H" as "H". Show.
  Abort.

End atomic.

Section error_tests.
  Context `{!heapGS Σ}.

  Check "not_cmpxchg".
  Lemma not_cmpxchg :
    ⊢ WP #() #() {{ _, True }}.
  Proof.
    Fail wp_cmpxchg_suc.
  Abort.
End error_tests.

(* Test a closed proof *)
Lemma heap_e_adequate σ : adequate NotStuck heap_e σ (λ v _, v = #2).
Proof. eapply (heap_adequacy heapΣ). iIntros (?) "_". by iApply heap_e_spec. Qed.

Lemma heap_e_totally_adequate σ : sn erased_step ([heap_e], σ).
Proof.
  eapply (heap_total heapΣ NotStuck _ _ (const True)).
  iIntros (?) "_". rewrite /heap_e /=.
  wp_alloc l. wp_load. wp_store. wp_load. auto.
Qed.
