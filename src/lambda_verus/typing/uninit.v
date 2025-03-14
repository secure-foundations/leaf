From lrust.typing Require Export type.
From lrust.typing Require Import product.
Set Default Proof Using "Type".

Open Scope nat.

Section uninit.
  Context `{!typeG Σ}.

  Fixpoint uninit_shr (κ: lft) (l: loc) (n: nat) (off: nat) : iProp Σ :=
    match n with
    | 0 => True
    | S m => (∃v, &frac{κ} (λ q, (l +ₗ off) ↦{q} v)) ∗ uninit_shr κ l m (S off)
    end%I.

  Global Instance uninit_shr_persistent κ l n off :
    Persistent (uninit_shr κ l n off).
  Proof. move: off. elim n; apply _. Qed.

  Lemma uninit_shr_off κ l n off :
    uninit_shr κ l n off ⊣⊢ uninit_shr κ (l +ₗ off) n 0.
  Proof.
    rewrite -{1}[off]Nat.add_0_r. move: l off 0. elim n; [done|]=>/= ? IH ???.
    f_equiv. { by rewrite shift_loc_assoc Nat2Z.inj_add. }
    rewrite -IH. f_equiv. rewrite leibniz_equiv_iff. lia.
  Qed.

  Lemma uninit_shr_add κ l m n :
    uninit_shr κ l (m + n) 0 ⊣⊢ uninit_shr κ l m 0 ∗ uninit_shr κ (l +ₗ m) n 0.
  Proof.
    move: l. elim m. { move=> ?. by rewrite shift_loc_0 left_id. }
    move=> ? IH ? /=. rewrite uninit_shr_off IH -assoc.
    f_equiv. f_equiv; [by rewrite -uninit_shr_off|].
    by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Lemma uninit_shr_shorten κ κ' l n off :
    κ' ⊑ κ -∗ uninit_shr κ l n off -∗ uninit_shr κ' l n off.
  Proof.
    iIntros "#? shr". iInduction n as [|] "IH" forall (off)=>/=; [done|].
    iDestruct "shr" as "[(%& bor) shr]". iSplit; [|by iApply "IH"].
    iExists _. by iApply frac_bor_shorten.
  Qed.

  Lemma bor_to_uninit_shr E κ l n q :
    ↑lftN ⊆ E → lft_ctx -∗ &{κ} (l ↦∗: (λ vl, ⌜length vl = n⌝)) -∗ q.[κ]
      ={E}=∗ uninit_shr κ l n 0 ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT Bor κ".
    iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor Len]"; [done|].
    iMod (bor_persistent with "LFT Len κ") as "[><- $]"; [done|].
    rewrite -{1}[l]shift_loc_0. have ->: 0%Z = 0 by done. move: 0=> off.
    iInduction vl as [|] "IH" forall (off)=>/=; [done|].
    rewrite heap_mapsto_vec_cons shift_loc_assoc.
    have ->: (off + 1)%Z = S off by lia.
    iMod (bor_sep with "LFT Bor") as "[Bor Bor']"; [done|].
    iMod ("IH" with "Bor'") as "$". iExists _.
    by iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT Bor") as "$".
  Qed.

  Lemma uninit_shr_acc E κ l n q :
    ↑lftN ⊆ E → lft_ctx -∗ uninit_shr κ l n 0 -∗ q.[κ] ={E}=∗
      ∃q' vl, ⌜length vl = n⌝ ∗ l ↦∗{q'} vl ∗ (l ↦∗{q'} vl ={E}=∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT shr κ". iInduction n as [|] "IH" forall (q l)=>/=.
    { iModIntro. iExists 1%Qp, []. rewrite heap_mapsto_vec_nil.
      do 2 (iSplit; [done|]). by iIntros. }
    iDestruct "shr" as "[(%& Bor) shr]". iDestruct "κ" as "[κ κ₊]".
    iMod (frac_bor_acc with "LFT Bor κ") as (q1) "[>↦ Toκ]"; [solve_ndisj|].
    rewrite uninit_shr_off. iMod ("IH" with "shr κ₊") as (q2 vl Eq) "[↦s Toκ₊]".
    iModIntro. case (Qp_lower_bound q1 q2) as (q0 &?&?&->&->).
    iExists q0, (_ :: vl)=>/=. iSplit; [by rewrite Eq|].
    rewrite heap_mapsto_vec_cons shift_loc_0. iDestruct "↦" as "[$ ↦r]".
    iDestruct "↦s" as "[$ ↦sr]". iIntros "[↦ ↦s]".
    iMod ("Toκ" with "[$↦ $↦r]") as "$". by iMod ("Toκ₊" with "[$↦s $↦sr]") as "$".
  Qed.

  Program Definition uninit n : type () := {|
    ty_size := n;  ty_lfts := [];  ty_E := [];
    ty_own _ _ _ vl := ⌜length vl = n⌝;
    ty_shr _ _ κ _ l := uninit_shr κ l n 0;
  |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. iIntros "* #In shr". by iApply uninit_shr_shorten. Qed.
  Next Obligation.
    iIntros "*% #LFT _ Bor κ !>". iApply step_fupdN_full_intro.
    by iApply (bor_to_uninit_shr with "LFT Bor κ").
  Qed.
  Next Obligation.
    iIntros "*% _ _ $$ !>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. iSplit.
    { iPureIntro. apply proph_dep_singleton. by case=> [][]. }
    iSplit; [done|]. by iIntros.
  Qed.
  Next Obligation.
    iIntros "*% _ _ _ _ $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. iSplit.
    { iPureIntro. apply proph_dep_singleton. by case=> [][]. }
    iSplit; [done|]. by iIntros.
  Qed.
End uninit.

Notation "↯" := uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uninit_copy n : Copy (↯ n).
  Proof.
    split; [apply _|]=>/= *. iIntros "LFT shr Na κ".
    iMod (uninit_shr_acc with "LFT shr κ") as (???) "[↦ Toκ]"; [solve_ndisj|].
    iModIntro. iExists _, _.
    iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [set_solver+|]. iFrame "↦".
    iSplit; [done|]. iIntros "Na". by iDestruct ("ToNa" with "Na") as "$".
  Qed.

  Global Instance uninit_send n : Send (↯ n).
  Proof. done. Qed.
  Global Instance uninit_sync n : Sync (↯ n).
  Proof. done. Qed.

  Lemma uninit_resolve n E L : resolve E L (↯ n) (const True).
  Proof. apply resolve_just. Qed.

  Lemma uninit_real n E L : real E L (↯ n) id.
  Proof.
    split; iIntros (?? vπ) "*% _ _ $$ !>"; iApply step_fupdN_full_intro;
    iPureIntro; exists (); fun_ext=>/= π; by case (vπ π).
  Qed.

  Lemma uninit_unit E L : eqtype E L (↯ 0) () id id.
  Proof.
    apply eqtype_id_unfold. iIntros (?) "_!>_". iSplit; [done|].
    iSplit; [iApply lft_equiv_refl|]. iSplit; iModIntro.
    - iIntros (??? vl). rewrite unit_ty_own. by case vl.
    - iIntros. by rewrite unit_ty_shr.
  Qed.
  Lemma uninit_unit_1 E L : subtype E L (↯ 0) () id.
  Proof. eapply proj1, uninit_unit. Qed.
  Lemma uninit_unit_2 E L : subtype E L () (↯ 0) id.
  Proof. eapply proj2, uninit_unit. Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L (↯ (m + n)) (↯ m * ↯ n) (const ((), ())) (const ()).
  Proof.
    apply eqtype_unfold. { split; fun_ext; by [case|case=> [[][]]]. }
    iIntros (?) "_!>_". iSplit; [done|]. iSplit; [iApply lft_equiv_refl|].
    iSplit; iModIntro=>/=.
    - iIntros (??? vl). iSplit; last first.
      { iIntros ((?&?&->&?&?)) "!%". rewrite app_length. by f_equal. }
      iIntros (?) "!%". by apply app_length_ex.
    - iIntros. rewrite -uninit_shr_add. iSplit; by iIntros.
  Qed.
  Lemma uninit_plus_prod_1 E L m n :
    subtype E L (↯ (m + n)) (↯ m * ↯ n) (const ((), ())).
  Proof. eapply proj1, uninit_plus_prod. Qed.
  Lemma uninit_plus_prod_2 E L m n :
    subtype E L (↯ m * ↯ n) (↯ (m + n)) (const ()).
  Proof. eapply proj2, uninit_plus_prod. Qed.
End typing.

Global Hint Resolve uninit_resolve uninit_real uninit_unit_1 uninit_unit_2
  uninit_plus_prod_1 uninit_plus_prod_2 : lrust_typing.
