From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_util.
  Context `{!typeG Σ}.

  Definition uniq_body {𝔄} (ty: type 𝔄) (vπ: proph 𝔄) (ξi: positive) (d: nat)
      (κ: lft) (tid: thread_id) (l: loc) : iProp Σ :=
    let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in
    .VO[ξ] vπ d ∗
    &{κ} (∃vπ' d', ⧖(S d') ∗ .PC[ξ] vπ' d' ∗ l ↦∗: ty.(ty_own) vπ' d' tid).

  Lemma ty_share_uniq_body {𝔄} (ty: type 𝔄) vπ ξi d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    &{κ'} (uniq_body ty vπ ξi d κ tid l) -∗ q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      &{κ'} 1:[PrVar (𝔄 ↾ prval_to_inh vπ) ξi] ∗ ty.(ty_shr) vπ d κ' tid l ∗ q.[κ'].
  Proof.
    set ξ := PrVar _ ξi. have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iIntros (?) "#LFT #In #In' Bor κ'".
    iMod (bor_sep with "LFT Bor") as "[BorVo Bor]"; [done|].
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|]. iIntros "!>!>!>".
    iMod (bor_shorten with "[] Bor") as "Bor".
    { iApply lft_incl_glb; [done|iApply lft_incl_refl]. }
    do 2 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorPc Borty]"; [done|].
    iMod (bor_combine with "LFT BorVo BorPc") as "Bor"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ'") as "[[Vo Pc] ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod ("ToBor" with "[Vo ToPc] ξ") as "[Borξ κ']".
    { iIntros "!> >ξ !>!>". iFrame "Vo". by iApply "ToPc". }
    iMod (ty_share with "LFT [] Borty κ'") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). by iIntros "!> >[$$]".
  Qed.

  Lemma ty_own_proph_uniq_body {𝔄} (ty: type 𝔄) vπ ξi d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    uniq_body ty vπ ξi d κ tid l -∗ q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in
      ∃ζl q', ⌜vπ ./ ζl⌝ ∗ q':+[ζl ++ [ξ]] ∗
        (q':+[ζl ++ [ξ]] ={E}=∗ uniq_body ty vπ ξi d κ tid l ∗ q.[κ']).
  Proof.
    set ξ := PrVar _ ξi. have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iIntros (?) "#LFT #Inκ #? [Vo Bor] [κ' κ'₊]".
    iMod (lft_incl_acc with "Inκ κ'") as (?) "[κ' Toκ']"; [done|].
    iMod (bor_acc with "LFT Bor κ'") as "[Big ToBor]"; [done|].
    iIntros "!>!>!>". iDestruct "Big" as (??) "(#⧖ & Pc & %vl & ↦ & ty)".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod (ty_own_proph with "LFT [] ty κ'₊") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ζl & Toty) !>".
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζl ξ") as (?) "[ζlξ Toζlξ]".
    iExists _, _. iSplit; [done|]. iIntros "{$ζlξ}ζlξ".
    iDestruct ("Toζlξ" with "ζlξ") as "[ζl ξ]".
    iMod ("Toty" with "ζl") as "[ty $]". iDestruct ("ToPc" with "ξ") as "Pc".
    iMod ("ToBor" with "[Pc ↦ ty]") as "[Bor κ']".
    { iNext. iExists _, _. iFrame "Pc ⧖". iExists _. iFrame. }
    iMod ("Toκ'" with "κ'") as "$". by iFrame.
  Qed.

  Lemma resolve_uniq_body {𝔄} (ty: type 𝔄) vπ ξi d κ tid l E L q F :
    lctx_lft_alive E L κ → ↑lftN ∪ ↑prophN ⊆ F →
    lft_ctx -∗ proph_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗ llctx_interp L q -∗
    uniq_body ty vπ ξi d κ tid l ={F}=∗ |={F}▷=>^(S d) |={F}=>
      ⟨π, π (PrVar (𝔄 ↾ prval_to_inh vπ) ξi) = vπ π⟩ ∗ llctx_interp L q.
  Proof.
    iIntros (Alv ?) "#LFT PROPH In E L [Vo Bor] /=".
    iMod (Alv with "E L") as (?) "[[κ κ₊] ToL]"; [solve_ndisj|].
    iMod (bor_acc with "LFT Bor κ") as "[(%&%& ⧖ & Pc &%& ↦ & ty) ToBor]";
      [solve_ndisj|]. iIntros "!>!>!>".
    iMod (ty_own_proph with "LFT In ty κ₊") as "Upd"; [solve_ndisj|].
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Toty)".
    iMod (uniq_resolve with "PROPH Vo Pc ξl") as "($& Pc & ξl)"; [solve_ndisj..|].
    iMod ("Toty" with "ξl") as "[ty κ₊]".
    iMod ("ToBor" with "[⧖ Pc ↦ ty]") as "[_ κ]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. }
    iApply "ToL". iFrame.
  Qed.

  Lemma real_uniq_body {𝔄 𝔅} (ty: type 𝔄) vπ ξi d κ tid l E L (f: _ → 𝔅) q F :
    lctx_lft_alive E L κ → real E L ty f → ↑lftN ⊆ F →
    lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    uniq_body ty vπ ξi d κ tid l ={F}=∗ |={F}▷=>^(S d) |={F}=>
      ⌜∃v, f ∘ vπ = const v⌝ ∗ llctx_interp L q ∗ uniq_body ty vπ ξi d κ tid l.
  Proof.
    iIntros (Alv [Rlo _] ?) "#LFT #E [L L₊] [Vo Bor] /=".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as "[big ToBor]"; [done|].
    iIntros "!>!>!>". iDestruct "big" as (??) "(⧖' & Pc &%& ↦ & ty)".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iMod (Rlo with "LFT E L₊ ty") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >($&$& ty)".
    iMod ("ToBor" with "[⧖' Pc ↦ ty]") as "[Bor κ]".
    { iNext. iExists _, _. iFrame "⧖' Pc". iExists _. iFrame. }
    iMod ("ToL" with "κ") as "$". by iFrame.
  Qed.

  Lemma incl_uniq_body {𝔄} (ty ty': type 𝔄) vπ ξi d κ κ' tid l :
    κ' ⊑ κ -∗ □ (∀vπ d tid vl, ty.(ty_own) vπ d tid vl ↔ ty'.(ty_own) vπ d tid vl) -∗
    uniq_body ty vπ ξi d κ tid l -∗ uniq_body ty' vπ ξi d κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn [$ Pc]". iApply (bor_shorten with "InLft").
    iApply bor_iff; [|done]. iIntros "!>!>".
    iSplit; iDestruct 1 as (vπ' d'') "(⧖ & Pc &%vl & ↦ & ?)"; iExists vπ', d'';
    iFrame "⧖ Pc"; iExists vl; iFrame "↦"; by iApply "EqOwn".
  Qed.
End uniq_util.
