From lrust.lang Require Export notation.
From lrust.lang Require Import heap proofmode.
Set Default Proof Using "Type".

Definition swap : val :=
  rec: "swap" ["p1";"p2";"len"] :=
    if: "len" ≤ #0 then #☠
    else let: "x" := !"p1" in
         "p1" <- !"p2";;
         "p2" <- "x";;
         "swap" ["p1" +ₗ #1 ; "p2" +ₗ #1 ; "len" - #1].

Lemma wp_swap `{!lrustGS Σ} E l1 l2 vl1 vl2 (n : Z):
  Z.of_nat (length vl1) = n → Z.of_nat (length vl2) = n →
  {{{ l1 ↦∗ vl1 ∗ l2 ↦∗ vl2 }}}
    swap [ #l1; #l2; #n] @ E
  {{{ RET #☠; l1 ↦∗ vl2 ∗ l2 ↦∗ vl1 }}}.
Proof.
  iIntros (Hvl1 Hvl2 Φ) "(Hl1 & Hl2) HΦ".
  iLöb as "IH" forall (n l1 l2 vl1 vl2 Hvl1 Hvl2). wp_rec.
  wp_op; case_bool_decide; wp_if.
  - iApply "HΦ". assert (n = O) by lia; subst.
    destruct vl1, vl2; try discriminate. by iFrame.
  - destruct vl1 as [|v1 vl1], vl2 as [|v2 vl2], n as [|n|]; try (discriminate || lia).
    revert Hvl1 Hvl2. intros [= Hvl1] [= Hvl2]; rewrite !heap_mapsto_vec_cons. subst n.
    iDestruct "Hl1" as "[Hv1 Hl1]". iDestruct "Hl2" as "[Hv2 Hl2]".
    Local Opaque Zminus.
    wp_read; wp_let; wp_read; do 2 wp_write. do 3 wp_op.
    iApply ("IH" with "[%] [%] Hl1 Hl2"); [lia..|].
    iIntros "!> [Hl1 Hl2]"; iApply "HΦ"; by iFrame.
Qed.
