From lrust.util Require Import basic.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Section mod_ty.
  Context `{!typeG Σ}.

  Lemma split_mt_mod_ty {𝔄 𝔅} (f: 𝔄 → 𝔅) ty vπ' d tid l :
    (l ↦∗: λ vl, ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ ty.(ty_own) vπ d tid vl) ⊣⊢
    ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ l ↦∗: ty.(ty_own) vπ d tid.
  Proof.
    iSplit.
    - iIntros "(%vl &?& %vπ &->&?)". iExists vπ. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "(%vπ &->& %vl & ↦ &?)". iExists vl. iFrame "↦". iExists vπ.
      by iSplit; [done|].
  Qed.

  Program Definition mod_ty {𝔄 𝔅} (f: 𝔄 → 𝔅) (ty: type 𝔄) : type 𝔅 := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl := ∃vπ', ⌜vπ = f ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl;
    ty_shr vπ d κ tid l := ∃vπ', ⌜vπ = f ∘ vπ'⌝ ∗ ty.(ty_shr) vπ' d κ tid l;
  |}%I.
  Next Obligation. move=> *. iIntros "[%[%?]]". by iApply ty_size_eq. Qed.
  Next Obligation.
    move=> */=. iIntros "[%vπ[->?]]". iExists vπ. iSplit; [done|].
    by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "[%vπ[->?]]". iExists vπ. iSplit; [done|].
    by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#? [%vπ[->?]]". iExists vπ. iSplit; [done|].
    by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In Bor κ". rewrite split_mt_mod_ty.
    iMod (bor_exists_tok with "LFT Bor κ") as (vπ) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (ty_share with "LFT In Bor κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[? $] !>". iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In [%vπ[->ty]] κ".
    iMod (ty_own_proph with "LFT In ty κ") as "Upd"; [done|]. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q ?) "[ξl Toty]".
    iModIntro. iExists ξl, q. iSplit; [iPureIntro; by apply (proph_dep_constr _)|].
    iIntros "{$ξl}ξl". iMod ("Toty" with "ξl") as "[? $]".
    iModIntro. iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In In' [%vπ[->ty]] κ".
    iMod (ty_shr_proph with "LFT In In' ty κ") as "Upd"; [done|]. iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q ?) "[ξl Toκ]".
    iModIntro. iExists ξl, q. iSplit; [iPureIntro; by apply (proph_dep_constr _)|].
    iIntros "{$ξl}ξl". by iMod ("Toκ" with "ξl").
  Qed.

  Global Instance mod_ty_ne {𝔄 𝔅} (f: 𝔄 → 𝔅) : NonExpansive (mod_ty f).
  Proof. solve_ne_type. Qed.
End mod_ty.

Notation "<{ f }>" := (mod_ty f) (format "<{ f }>"): lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma mod_ty_own' {𝔄 𝔅} g f `{!@SemiIso 𝔄 𝔅 f g} ty vπ d tid vl :
    (<{f}> ty).(ty_own) vπ d tid vl ⊢ ty.(ty_own) (g ∘ vπ) d tid vl.
  Proof. iIntros "[%[->?]]". by rewrite compose_assoc semi_iso. Qed.
  Lemma mod_ty_own {𝔄 𝔅} g f `{!@Iso 𝔄 𝔅 f g} ty vπ d tid vl :
    (<{f}> ty).(ty_own) vπ d tid vl ⊣⊢ ty.(ty_own) (g ∘ vπ) d tid vl.
  Proof.
    iSplit; [by iApply mod_ty_own'|]. iIntros "ty". iExists _. iFrame "ty".
    by rewrite compose_assoc semi_iso.
  Qed.

  Lemma mod_ty_shr' {𝔄 𝔅} g f `{!@SemiIso 𝔄 𝔅 f g} ty vπ d κ tid l :
    (<{f}> ty).(ty_shr) vπ d κ tid l ⊢ ty.(ty_shr) (g ∘ vπ) d κ tid l.
  Proof. iIntros "[%[->?]]". by rewrite compose_assoc semi_iso. Qed.
  Lemma mod_ty_shr {𝔄 𝔅} g f `{!@Iso 𝔄 𝔅 f g} ty vπ d κ tid l :
    (<{f}> ty).(ty_shr) vπ d κ tid l ⊣⊢ ty.(ty_shr) (g ∘ vπ) d κ tid l.
  Proof.
    iSplit; [by iApply mod_ty_shr'|]. iIntros "ty". iExists _. iFrame "ty".
    by rewrite compose_assoc semi_iso.
  Qed.

  Global Instance mod_ty_type_ne {𝔄 𝔅} (f: 𝔄 → 𝔅) : TypeNonExpansive <{f}>%T.
  Proof.
    split=>/= *; by [apply type_lft_morphism_id_like| |do 3 f_equiv|do 3 f_equiv].
  Qed.

  Global Instance mod_ty_copy {𝔄 𝔅} (f: 𝔄 → 𝔅) ty : Copy ty → Copy (<{f}> ty).
  Proof.
    move=> [? ShrAcc]. split; [by apply _|]=> */=. iIntros "LFT [%vπ[->ty]] Na κ".
    iMod (ShrAcc with "LFT ty Na κ") as (q vl) "($& ↦ &?& Toκ)"; [done|done|].
    iModIntro. iExists q, vl. iFrame "↦ Toκ". iNext. iExists vπ. by iSplit.
  Qed.

  Global Instance mod_ty_send {𝔄 𝔅} (f: 𝔄 → 𝔅) ty : Send ty → Send (<{f}> ty).
  Proof. move=> ?>/=. by do 3 f_equiv. Qed.

  Global Instance mod_ty_sync {𝔄 𝔅} (f: 𝔄 → 𝔅) ty : Sync ty → Sync (<{f}> ty).
  Proof. move=> ?>/=. by do 3 f_equiv. Qed.

  Lemma mod_ty_resolve' {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty Φ :
    resolve E L ty Φ → resolve E L (<{f}> ty) (λ b, ∃a, b = f a ∧ Φ a).
  Proof.
    move=> Rslv > ?. iIntros "LFT PROPH E L (%&->& ty)".
    iMod (Rslv with "LFT PROPH E L ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). iIntros "!> >[Obs $] !>".
    iApply proph_obs_impl; [|done]=>/= ??. by eexists _.
  Qed.

  Lemma mod_ty_resolve {𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty Φ :
    resolve E L ty Φ → resolve E L (<{f}> ty) (Φ ∘ g).
  Proof.
    move=> ?. eapply resolve_impl; [by apply mod_ty_resolve'|]=>/=
    ?[?[/(f_equal g) + ?]]. by rewrite semi_iso'=> ->.
  Qed.

  Lemma mod_ty_resolve_just {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty :
    resolve E L ty (const True) → resolve E L (<{f}> ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma mod_ty_real {𝔄 𝔅 ℭ} E L f g `{!@Iso 𝔄 𝔅 f g} (h: _ → ℭ) ty :
    real E L ty h → real E L (<{f}> ty) (h ∘ g).
  Proof.
    move=> [Rlo Rls]. split.
    - iIntros "*% LFT E L ty". rewrite mod_ty_own.
      iMod (Rlo with "LFT E L ty") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). by iIntros "!> >($&$&$)".
    - iIntros "*% LFT E L ty". rewrite mod_ty_shr.
      iMod (Rls with "LFT E L ty") as "Upd"; [done|]. iIntros "!>!>".
      iApply (step_fupdN_wand with "Upd"). by iIntros ">($&$&$)".
  Qed.

  Lemma mod_ty_id {𝔄} (ty: type 𝔄) : <{id}>%T ty ≡ ty.
  Proof. split; move=>// *; by [rewrite mod_ty_own|rewrite mod_ty_shr]. Qed.

  Lemma mod_ty_compose {𝔄 𝔅 ℭ} (f: 𝔄 → 𝔅) (g: 𝔅 → ℭ) ty :
    (<{g}> (<{f}> ty) ≡ <{g ∘ f}> ty)%T.
  Proof.
    split=>// *; (iSplit=>/=; [
      iIntros "(%&->& %vπ &->&?)"; iExists vπ; by iFrame|
      iIntros "[%vπ[->?]]"; iExists (f ∘ vπ); (iSplit; [done|]); iExists vπ; by iFrame
    ]).
  Qed.

  Lemma mod_ty_in {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty : subtype E L ty (<{f}> ty) f.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>" (vπ) "*?"; iExists vπ; by iSplit.
  Qed.

  Lemma mod_ty_out {𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty :
    subtype E L (<{f}> ty) ty g.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/=[%[->?]]"; by rewrite compose_assoc semi_iso.
  Qed.

  Lemma mod_ty_inout {𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty :
    eqtype E L ty (<{f}> ty) f g.
  Proof. by split; [apply mod_ty_in|apply mod_ty_out]. Qed.
  Lemma mod_ty_outin {𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty :
    eqtype E L (<{f}> ty) ty g f.
  Proof. by apply eqtype_symm, mod_ty_inout. Qed.

  Lemma mod_ty_subtype {𝔄 𝔅 𝔄' 𝔅'} E L h
      f (f': 𝔄' → 𝔅') g `{!@SemiIso 𝔄 𝔅 f g} ty ty' :
    subtype E L ty ty' h → subtype E L (<{f}> ty) (<{f'}> ty') (f' ∘ h ∘ g).
  Proof.
    move=> ??. eapply subtype_trans; [by apply mod_ty_out|].
    eapply subtype_trans; by [|apply mod_ty_in].
  Qed.

  Lemma mod_ty_eqtype {𝔄 𝔅 𝔄' 𝔅'} E L h h' f f' g g'
      `{!@SemiIso 𝔄 𝔅 f g} `{!@SemiIso 𝔄' 𝔅' f' g'} ty ty' :
    eqtype E L ty ty' h h' →
    eqtype E L (<{f}> ty) (<{f'}> ty') (f' ∘ h ∘ g) (f ∘ h' ∘ g').
  Proof. move=> [??]. split; by apply mod_ty_subtype. Qed.
End typing.

Global Hint Resolve mod_ty_in mod_ty_out mod_ty_inout mod_ty_outin
  | 20 : lrust_typing.
Global Hint Resolve mod_ty_resolve | 5 : lrust_typing.
Global Hint Resolve mod_ty_resolve_just mod_ty_subtype mod_ty_eqtype
  : lrust_typing.
