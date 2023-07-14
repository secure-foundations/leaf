(** Correctness of in-place list reversal *)
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export total_weakestpre weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Unset Mangle Names.

Section list_reverse.
Context `{!heapGS Σ}.
Implicit Types l : loc.

Fixpoint is_list (hd : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_list hd' xs
  end%I.

Definition rev : val :=
  rec: "rev" "hd" "acc" :=
    match: "hd" with
      NONE => "acc"
    | SOME "l" =>
       let: "tmp1" := Fst !"l" in
       let: "tmp2" := Snd !"l" in
       "l" <- ("tmp1", "acc");;
       "rev" "tmp2" "hd"
    end.

Lemma rev_acc_wp hd acc xs ys :
  [[{ is_list hd xs ∗ is_list acc ys }]]
    rev hd acc
  [[{ w, RET w; is_list w (reverse xs ++ ys) }]].
Proof.
  iIntros (Φ) "[Hxs Hys] HΦ". Show.
  iInduction xs as [|x xs] "IH" forall (hd acc ys Φ);
    iSimplifyEq; wp_rec; wp_let.
  - Show. wp_match. by iApply "HΦ".
  - iDestruct "Hxs" as (l hd' ->) "[Hx Hxs]".
    wp_load. wp_load. wp_store.
    iApply ("IH" $! hd' (SOMEV #l) (x :: ys) with "Hxs [Hx Hys]"); simpl.
    { iExists l, acc; by iFrame. }
    iIntros (w). rewrite cons_middle assoc -reverse_cons. iApply "HΦ".
Qed.

Lemma rev_wp hd xs :
  [[{ is_list hd xs }]] rev hd NONEV [[{ w, RET w; is_list w (reverse xs) }]].
Proof.
  iIntros (Φ) "Hxs HΦ".
  iApply (rev_acc_wp hd NONEV xs [] with "[$Hxs //]").
  iIntros (w). rewrite right_id_L. iApply "HΦ".
Qed.
End list_reverse.
