From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Inductive tree :=
  | leaf : Z → tree
  | node : tree → tree → tree.

Fixpoint is_tree `{!heapGS Σ} (v : val) (t : tree) : iProp Σ :=
  match t with
  | leaf n => ⌜v = InjLV #n⌝
  | node tl tr =>
     ∃ (ll lr : loc) (vl vr : val),
       ⌜v = InjRV (#ll,#lr)⌝ ∗ ll ↦ vl ∗ is_tree vl tl ∗ lr ↦ vr ∗ is_tree vr tr
  end%I.

Fixpoint sum (t : tree) : Z :=
  match t with
  | leaf n => n
  | node tl tr => sum tl + sum tr
  end.

Definition sum_loop : val :=
  rec: "sum_loop" "t" "l" :=
    match: "t" with
      InjL "n" => "l" <- "n" + !"l"
    | InjR "tt" => "sum_loop" !(Fst "tt") "l" ;; "sum_loop" !(Snd "tt") "l"
    end.

Definition sum' : val := λ: "t",
  let: "l" := ref #0 in
  sum_loop "t" "l";;
  !"l".

Lemma sum_loop_wp `{!heapGS Σ} v t l (n : Z) :
  [[{ l ↦ #n ∗ is_tree v t }]]
    sum_loop v #l
  [[{ RET #(); l ↦ #(sum t + n) ∗ is_tree v t }]].
Proof.
  iIntros (Φ) "[Hl Ht] HΦ".
  iInduction t as [n'|tl ? tr] "IH" forall (v l n Φ); simpl; wp_rec; wp_let.
  - iDestruct "Ht" as "%"; subst.
    wp_load. wp_store.
    by iApply ("HΦ" with "[$Hl]").
  - iDestruct "Ht" as (ll lr vl vr ->) "(Hll & Htl & Hlr & Htr)".
    wp_load. wp_apply ("IH" with "Hl Htl"). iIntros "[Hl Htl]".
    wp_load. wp_apply ("IH1" with "Hl Htr"). iIntros "[Hl Htr]".
    iApply "HΦ". iSplitL "Hl".
    { by replace (sum tl + sum tr + n)%Z with (sum tr + (sum tl + n))%Z by lia. }
    iExists ll, lr, vl, vr. by iFrame.
Qed.

Lemma sum_wp `{!heapGS Σ} v t :
  [[{ is_tree v t }]] sum' v [[{ RET #(sum t); is_tree v t }]].
Proof.
  iIntros (Φ) "Ht HΦ". rewrite /sum' /=.
  wp_lam. wp_alloc l as "Hl".
  wp_smart_apply (sum_loop_wp with "[$Hl $Ht]").
  rewrite Z.add_0_r.
  iIntros "[Hl Ht]". wp_load. by iApply "HΦ".
Qed.
