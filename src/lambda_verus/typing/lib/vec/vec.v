From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec.
  Context `{!typeG Σ}.

  Lemma split_mt_vec {𝔄} d l' alπ Φ :
    (l' ↦∗: (λ vl, [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜vl = [ #l; #len; #ex] ∧ alπ = lapply aπl⌝ ∗ Φ d' l len ex aπl)) ⊣⊢
    [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜alπ = lapply aπl⌝ ∗ l' ↦∗ [ #l; #len; #ex] ∗ Φ d' l len ex aπl.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". case d=>// ?. iDestruct "big" as (????[->->]) "Φ".
      iExists _, _, _, _. iSplit; [done|iFrame].
    - iIntros "big". case d=>// ?. iDestruct "big" as (????->) "(↦ & ?)".
      iExists [_;_;_]. iFrame "↦". iExists _, _, _, _. by iFrame.
  Qed.

  Lemma split_mt_vec' {𝔄} l' alπ Φ :
    (l' ↦∗: (λ vl, ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜vl = [ #l; #len; #ex] ∧ alπ = lapply aπl⌝ ∗ Φ l len ex aπl)) ⊣⊢
    ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜alπ = lapply aπl⌝ ∗ l' ↦∗ [ #l; #len; #ex] ∗ Φ l len ex aπl.
  Proof.
    set Φ' := λ _: nat, Φ. have ->: Φ = Φ' 0 by done.
    by apply (split_mt_vec (S _)).
  Qed.

  (* Rust's Vec<T> *)
  Program Definition vec_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 3;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own alπ d tid vl :=
      [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
        ⌜vl = [ #l; #len; #ex] ∧ alπ = lapply aπl⌝ ∗
        ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
        (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
        freeable_sz' ((len + ex) * ty.(ty_size)) l;
    ty_shr alπ d κ tid l' :=
      [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
        ⌜alπ = lapply aπl⌝ ∗
        &frac{κ} (λ q, l' ↦∗{q} [ #l; #len; #ex]) ∗
        ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation.
    iIntros (???[]??) "vec //". by iDestruct "vec" as (????[-> _]) "?".
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 17 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 14 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|]. iIntros "#? (%&%&%&%&%&?& All)".
    iExists _, _, _, _. iSplit; [done|]. iSplit; [by iApply frac_bor_shorten|].
    rewrite !big_sepL_forall. iIntros "!> **".
    iApply ty_shr_lft_mono; by [|iApply "All"].
  Qed.
  Next Obligation.
    iIntros (???? d) "*% #LFT In Bor κ". rewrite split_mt_vec. case d.
    { by iMod (bor_persistent with "LFT Bor κ") as "[>[] _]". }
    move=> ?. do 4 (iMod (bor_exists_tok with "LFT Bor κ") as (?) "[Bor κ]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_fracture (λ q', _ ↦∗{q'} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_later_tok with "LFT Bor κ") as "Borκ"; [done|].
    iIntros "/=!>!>!>". iMod "Borκ" as "[Bor κ]".
    iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|?]) "*% LFT In vec κ/="; [done|].
    iDestruct "vec" as (????[->->]) "(↦tys & ex & †)". iIntros "!>!>!>".
    iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _. iSplit.
    { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
    iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|?]) "*% LFT In In' vec κ'/="; [done|].
    iDestruct "vec" as (????->) "[? tys]". iIntros "!>!>!>".
    iMod (ty_shr_proph_big_sepL with "LFT In In' tys κ'") as "Toκ'"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Toκ'").
    iIntros ">(%&%&%& ξl & Toκ') !>". iExists _, _. iSplit.
    { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". by iMod ("Toκ'" with "ξl") as "$".
  Qed.

  Global Instance vec_ty_ne {𝔄} : NonExpansive (@vec_ty 𝔄).
  Proof. solve_ne_type. Qed.
End vec.
