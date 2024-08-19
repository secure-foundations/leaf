From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** Provides some array utilities:

* [array_free], to deallocate an entire array in one go.
* [array_copy_to], a function which copies to an array in-place.
* Using [array_copy_to] we also implement [array_clone], which allocates a fresh
array and copies to it.
* [array_init], to create and initialize an array with a given
function. Specifically, [array_init n f] creates a new array of size
[n] in which the [i]th element is initialized with [f #i]

*)

Definition array_free : val :=
  rec: "freeN" "ptr" "n" :=
    if: "n" ≤ #0 then #()
    else Free "ptr";;
         "freeN" ("ptr" +ₗ #1) ("n" - #1).

Definition array_copy_to : val :=
  rec: "array_copy_to" "dst" "src" "n" :=
    if: "n" ≤ #0 then #()
    else "dst" <- !"src";;
         "array_copy_to" ("dst" +ₗ #1) ("src" +ₗ #1) ("n" - #1).

Definition array_clone : val :=
  λ: "src" "n",
    let: "dst" := AllocN "n" #() in
    array_copy_to "dst" "src" "n";;
    "dst".

(* [array_init_loop src i n f] initializes elements
   [i], [i+1], ..., [n] of the array [src] to
   [f #i], [f #(i+1)], ..., [f #n] *)
Local Definition array_init_loop : val :=
  rec: "loop" "src" "i" "n" "f" :=
    if: "i" = "n" then #()
    else "src" +ₗ "i" <- "f" "i";;
         "loop" "src" ("i" + #1) "n" "f".

Definition array_init : val :=
  λ: "n" "f",
    let: "src" := AllocN "n" #() in
    array_init_loop "src" #0 "n" "f";;
    "src".

Section proof.
  Context `{!heapGS_gen hlc Σ}.

  Lemma twp_array_free s E l vs (n : Z) :
    n = length vs →
    [[{ l ↦∗ vs }]] array_free #l #n @ s; E [[{ RET #(); True }]].
  Proof.
    iIntros (Hlen Φ) "Hl HΦ".
    iInduction vs as [|v vs] "IH" forall (l n Hlen); subst n; wp_rec; wp_pures.
    { iApply "HΦ". done. }
    iDestruct (array_cons with "Hl") as "[Hv Hl]".
    wp_free. wp_pures. iApply ("IH" with "[] Hl"); eauto with lia.
  Qed.
  Lemma wp_array_free s E l vs (n : Z) :
    n = length vs →
    {{{ l ↦∗ vs }}} array_free #l #n @ s; E {{{ RET #(); True }}}.
  Proof.
    iIntros (? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_free with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_array_copy_to stk E (dst src : loc) vdst vsrc dq (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
    [[{ dst ↦∗ vdst ∗ src ↦∗{dq} vsrc }]]
      array_copy_to #dst #src #n @ stk; E
    [[{ RET #(); dst ↦∗ vsrc ∗ src ↦∗{dq} vsrc }]].
  Proof.
    iIntros (Hvdst Hvsrc Φ) "[Hdst Hsrc] HΦ".
    iInduction vdst as [|v1 vdst] "IH" forall (n dst src vsrc Hvdst Hvsrc);
      destruct vsrc as [|v2 vsrc]; simplify_eq/=; try lia; wp_rec; wp_pures.
    { iApply "HΦ". auto with iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv1 Hdst]".
    iDestruct (array_cons with "Hsrc") as "[Hv2 Hsrc]".
    wp_load; wp_store.
    wp_smart_apply ("IH" with "[%] [%] Hdst Hsrc") as "[Hvdst Hvsrc]"; [ lia .. | ].
    iApply "HΦ"; by iFrame.
  Qed.
  Lemma wp_array_copy_to stk E (dst src : loc) vdst vsrc dq (n : Z) :
    Z.of_nat (length vdst) = n → Z.of_nat (length vsrc) = n →
    {{{ dst ↦∗ vdst ∗ src ↦∗{dq} vsrc }}}
      array_copy_to #dst #src #n @ stk; E
    {{{ RET #(); dst ↦∗ vsrc ∗ src ↦∗{dq} vsrc }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_copy_to with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_array_clone stk E l dq vl n :
    Z.of_nat (length vl) = n →
    (0 < n)%Z →
    [[{ l ↦∗{dq} vl }]]
      array_clone #l #n @ stk; E
    [[{ l', RET #l'; l' ↦∗ vl ∗ l ↦∗{dq} vl }]].
  Proof.
    iIntros (Hvl Hn Φ) "Hvl HΦ".
    wp_lam.
    wp_alloc dst as "Hdst"; first by auto.
    wp_smart_apply (twp_array_copy_to with "[$Hdst $Hvl]") as "[Hdst Hl]".
    - rewrite replicate_length Z2Nat.id; lia.
    - auto.
    - wp_pures.
      iApply "HΦ"; by iFrame.
  Qed.
  Lemma wp_array_clone stk E l dq vl n :
    Z.of_nat (length vl) = n →
    (0 < n)%Z →
    {{{ l ↦∗{dq} vl }}}
      array_clone #l #n @ stk; E
    {{{ l', RET #l'; l' ↦∗ vl ∗ l ↦∗{dq} vl }}}.
  Proof.
    iIntros (? ? Φ) "H HΦ". iApply (twp_wp_step with "HΦ").
    iApply (twp_array_clone with "H"); [auto..|]; iIntros (l') "H HΦ". by iApply "HΦ".
  Qed.

  Section array_init.
    Context (Q : nat → val → iProp Σ).
    Implicit Types (f v : val) (i j : nat).

    Local Lemma wp_array_init_loop stk E l i n k f  :
      n = Z.of_nat (i + k) →
      {{{
        (l +ₗ i) ↦∗ replicate k #() ∗
        [∗ list] j ∈ seq i k, WP f #(j : nat) @ stk; E {{ Q j }}
      }}}
        array_init_loop #l #i #n f @ stk; E
      {{{ vs, RET #();
        ⌜ length vs = k ⌝ ∗ (l +ₗ i) ↦∗ vs ∗ [∗ list] j↦v ∈ vs, Q (i + j) v
      }}}.
    Proof.
      iIntros (Hn Φ) "[Hl Hf] HΦ".
      iInduction k as [|k] "IH" forall (i Hn); simplify_eq/=; wp_rec; wp_pures.
      { rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
        wp_pures. iApply ("HΦ" $! []). auto. }
      rewrite bool_decide_eq_false_2; last naive_solver lia.
      iDestruct (array_cons with "Hl") as "[Hl HSl]".
      iDestruct "Hf" as "[Hf HSf]".
      wp_smart_apply (wp_wand with "Hf") as (v) "Hv". wp_store. wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      iApply ("IH" with "[%] [HSl] HSf"); first lia.
      { by rewrite Loc.add_assoc Z.add_1_r -Nat2Z.inj_succ. }
      iIntros "!>" (vs). iDestruct 1 as (<-) "[HSl Hvs]".
      iApply ("HΦ" $! (v :: vs)). iSplit; [naive_solver|]. iSplitL "Hl HSl".
      - iFrame "Hl". by rewrite Loc.add_assoc Z.add_1_r -Nat2Z.inj_succ.
      - iEval (rewrite /= Nat.add_0_r; setoid_rewrite Nat.add_succ_r). iFrame.
    Qed.
    Local Lemma twp_array_init_loop stk E l i n k f  :
      n = Z.of_nat (i + k) →
      [[{
        (l +ₗ i) ↦∗ replicate k #() ∗
        [∗ list] j ∈ seq i k, WP f #(j : nat) @ stk; E [{ Q j }]
      }]]
        array_init_loop #l #i #n f @ stk; E
      [[{ vs, RET #();
        ⌜ length vs = k ⌝ ∗ (l +ₗ i) ↦∗ vs ∗ [∗ list] j↦v ∈ vs, Q (i + j) v
      }]].
    Proof.
      iIntros (Hn Φ) "[Hl Hf] HΦ".
      iInduction k as [|k] "IH" forall (i Hn); simplify_eq/=; wp_rec; wp_pures.
      { rewrite bool_decide_eq_true_2; last (repeat f_equal; lia).
        wp_pures. iApply ("HΦ" $! []). auto. }
      rewrite bool_decide_eq_false_2; last naive_solver lia.
      iDestruct (array_cons with "Hl") as "[Hl HSl]".
      iDestruct "Hf" as "[Hf HSf]".
      wp_smart_apply (twp_wand with "Hf") as (v) "Hv". wp_store. wp_pures.
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      iApply ("IH" with "[%] [HSl] HSf"); first lia.
      { by rewrite Loc.add_assoc Z.add_1_r -Nat2Z.inj_succ. }
      iIntros (vs). iDestruct 1 as (<-) "[HSl Hvs]".
      iApply ("HΦ" $! (v :: vs)). iSplit; [naive_solver|]. iSplitL "Hl HSl".
      - iFrame "Hl". by rewrite Loc.add_assoc Z.add_1_r -Nat2Z.inj_succ.
      - iEval (rewrite /= Nat.add_0_r; setoid_rewrite Nat.add_succ_r). iFrame.
    Qed.

    Lemma wp_array_init stk E n f :
      (0 < n)%Z →
      {{{
        [∗ list] i ∈ seq 0 (Z.to_nat n), WP f #(i : nat) @ stk; E {{ Q i }}
      }}}
        array_init #n f @ stk; E
      {{{ l vs, RET #l;
        ⌜Z.of_nat (length vs) = n⌝ ∗ l ↦∗ vs ∗ [∗ list] k↦v ∈ vs, Q k v
      }}}.
    Proof.
      iIntros (Hn Φ) "Hf HΦ". wp_lam. wp_alloc l as "Hl"; first done.
      wp_smart_apply (wp_array_init_loop _ _ _ 0 n (Z.to_nat n)
        with "[Hl $Hf] [HΦ]") as "!> %vs".
      { by rewrite /= Z2Nat.id; last lia. }
      { by rewrite Loc.add_0. }
      iDestruct 1 as (Hlen) "[Hl Hvs]". wp_pures.
      iApply ("HΦ" $! _ vs). iModIntro. iSplit.
      { iPureIntro. by rewrite Hlen Z2Nat.id; last lia. }
      rewrite Loc.add_0. iFrame.
    Qed.
    Lemma twp_array_init stk E n f :
      (0 < n)%Z →
      [[{
        [∗ list] i ∈ seq 0 (Z.to_nat n), WP f #(i : nat) @ stk; E [{ Q i }]
      }]]
        array_init #n f @ stk; E
      [[{ l vs, RET #l;
        ⌜Z.of_nat (length vs) = n⌝ ∗ l ↦∗ vs ∗ [∗ list] k↦v ∈ vs, Q k v
      }]].
    Proof.
      iIntros (Hn Φ) "Hf HΦ". wp_lam. wp_alloc l as "Hl"; first done.
      wp_smart_apply (twp_array_init_loop _ _ _ 0 n (Z.to_nat n)
        with "[Hl $Hf] [HΦ]") as "%vs".
      { by rewrite /= Z2Nat.id; last lia. }
      { by rewrite Loc.add_0. }
      iDestruct 1 as (Hlen) "[Hl Hvs]". wp_pures.
      iApply ("HΦ" $! _ vs). iModIntro. iSplit.
      { iPureIntro. by rewrite Hlen Z2Nat.id; last lia. }
      rewrite Loc.add_0. iFrame.
    Qed.
  End array_init.

  Section array_init_fmap.
    Context {A} (g : A → val) (Q : nat → A → iProp Σ).
    Implicit Types (xs : list A) (f : val).

    Local Lemma big_sepL_exists_eq vs :
      ([∗ list] k↦v ∈ vs, ∃ x, ⌜v = g x⌝ ∗ Q k x) -∗
      ∃ xs, ⌜ vs = g <$> xs ⌝ ∗ [∗ list] k↦x ∈ xs, Q k x.
    Proof.
      iIntros "Hvs". iInduction vs as [|v vs] "IH" forall (Q); simpl.
      { iExists []. by auto. }
      iDestruct "Hvs" as "[(%x & -> & Hv) Hvs]".
      iDestruct ("IH" with "Hvs") as (xs ->) "Hxs".
      iExists (x :: xs). by iFrame.
    Qed.

    Lemma wp_array_init_fmap stk E n f :
      (0 < n)%Z →
      {{{
        [∗ list] i ∈ seq 0 (Z.to_nat n),
          WP f #(i : nat) @ stk; E {{ v, ∃ x, ⌜v = g x⌝ ∗ Q i x }}
      }}}
        array_init #n f @ stk; E
      {{{ l xs, RET #l;
        ⌜Z.of_nat (length xs) = n⌝ ∗ l ↦∗ (g <$> xs) ∗ [∗ list] k↦x ∈ xs, Q k x
      }}}.
    Proof.
      iIntros (Hn Φ) "Hf HΦ". iApply (wp_array_init with "Hf"); first done.
      iIntros "!>" (l vs). iDestruct 1 as (<-) "[Hl Hvs]".
      iDestruct (big_sepL_exists_eq with "Hvs") as (xs ->) "Hxs".
      iApply "HΦ". iFrame "Hl Hxs". by rewrite fmap_length.
    Qed.
    Lemma twp_array_init_fmap stk E n f :
      (0 < n)%Z →
      [[{
        [∗ list] i ∈ seq 0 (Z.to_nat n),
          WP f #(i : nat) @ stk; E [{ v, ∃ x, ⌜v = g x⌝ ∗ Q i x }]
      }]]
        array_init #n f @ stk; E
      [[{ l xs, RET #l;
        ⌜Z.of_nat (length xs) = n⌝ ∗ l ↦∗ (g <$> xs) ∗ [∗ list] k↦x ∈ xs, Q k x
      }]].
    Proof.
      iIntros (Hn Φ) "Hf HΦ". iApply (twp_array_init with "Hf"); first done.
      iIntros (l vs). iDestruct 1 as (<-) "[Hl Hvs]".
      iDestruct (big_sepL_exists_eq with "Hvs") as (xs ->) "Hxs".
      iApply "HΦ". iFrame "Hl Hxs". by rewrite fmap_length.
    Qed.
  End array_init_fmap.
End proof.
