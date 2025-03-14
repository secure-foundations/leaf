From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section shr_bor.
  Context `{!typeG Σ}.

  Program Definition shr_bor {𝔄} (κ: lft) (ty: type 𝔄) : type 𝔄 := {|
    st_size := 1;  st_lfts := κ :: ty.(ty_lfts);  st_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    st_own vπ d tid vl := [S(d') := d] [loc[l] := vl] ty.(ty_shr) vπ d' κ tid l
  |}%I.
  Next Obligation.
    move=> ????[|?]*/=; [by iIntros|]. rewrite by_just_loc_ex. by iIntros "[%[->?]]".
  Qed.
  Next Obligation.
    move=> ???[|?][|?]*; try (by iIntros); [lia|]. rewrite/= !by_just_loc_ex.
    do 3 f_equiv. apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*/=; [by iIntros|]. rewrite {1}by_just_loc_ex.
    iIntros "#LFT #? (%&->& #ty) κ' !>/=".
    iDestruct (ty_shr_proph with "LFT [] [] ty κ'") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iApply (step_fupdN_wand with "Upd"). iNext. iMod 1 as (ξl q ?) "[ξl Upd]".
    iModIntro. iExists ξl, q. iSplit; [done|]. iIntros "{$ξl}ξl".
    by iMod ("Upd" with "ξl") as "$".
  Qed.

  Global Instance shr_ne {𝔄} κ : NonExpansive (@shr_bor 𝔄 κ).
  Proof. solve_ne_type. Qed.
End shr_bor.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance shr_type_contractive {𝔄} κ : TypeContractive (@shr_bor _ _ 𝔄 κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| |].
    - move=>/= *. by do 4 f_equiv.
    - move=>/= *. do 8 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance shr_send {𝔄} κ (ty: type 𝔄) : Sync ty → Send (&shr{κ} ty).
  Proof. move=> Eq >/=. by setoid_rewrite Eq at 1. Qed.

  Global Instance shr_just_loc {𝔄} κ (ty: type 𝔄) : JustLoc (&shr{κ} ty).
  Proof. iIntros (?[|]?[|[[]|][]]) "? //". by iExists _. Qed.

  Lemma shr_resolve {𝔄} κ (ty: type 𝔄) E L : resolve E L (&shr{κ} ty) (const True).
  Proof. apply resolve_just. Qed.

  Lemma shr_real {𝔄 𝔅} κ ty E L (f: 𝔄 → 𝔅) :
    real E L ty f → real E L (&shr{κ} ty) f.
  Proof.
    move=> [_ Rl]. apply simple_type_real=>/=.
    iIntros (???[|]?[|[[]|][]]?) "LFT E L ty //=".
    by iMod (Rl with "LFT E L ty") as "$".
  Qed.

  Lemma shr_type_incl {𝔄 𝔅} κ κ' (f: 𝔄 → 𝔅) ty ty' :
    κ' ⊑ κ -∗ type_incl ty ty' f -∗ type_incl (&shr{κ} ty) (&shr{κ'} ty') f.
  Proof.
    iIntros "#? (_&#?&_& #Sub)".
    iApply type_incl_simple_type=>/=; [done|by iApply lft_intersect_mono|].
    iIntros "!>" (?[|?]??); [done|]. rewrite/= by_just_loc_ex.
    iIntros "[%[->?]]". iApply "Sub". by iApply ty_shr_lft_mono.
  Qed.

  Lemma shr_subtype {𝔄 𝔅} E L κ κ' (f: 𝔄 → 𝔅) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    subtype E L (&shr{κ} ty) (&shr{κ'} ty') f.
  Proof.
    move=> In Sub ?. iIntros "L". iDestruct (In with "L") as "#In".
    iDestruct (Sub with "L") as "#Sub". iIntros "!> #?".
    iApply shr_type_incl; by [iApply "In"|iApply "Sub"].
  Qed.

  Lemma shr_eqtype {𝔄 𝔅} E L κ κ' (f: 𝔄 → 𝔅) g ty ty' :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' f g →
    eqtype E L (&shr{κ} ty) (&shr{κ'} ty') f g.
  Proof. move=> [??] [??]. split; by apply shr_subtype. Qed.

  Lemma read_shr {𝔄} (ty: type 𝔄) κ E L :
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&shr{κ} ty) ty (&shr{κ} ty) id id.
  Proof.
    iIntros (? Alv ?[|?]???) "#LFT E Na L shr"; [done|].
    setoid_rewrite by_just_loc_ex at 1. iDestruct "shr" as (l[=->]) "#shr".
    iMod (Alv with "E L") as (q) "[κ ToL]"; [done|].
    iMod (copy_shr_acc with "LFT shr Na κ") as (q' vl) "(Na & ↦ & ty & Toκ)";
    [done|by rewrite ->shr_locsE_shrN|]. iExists l, vl, q'. iIntros "!> {$↦}".
    iSplit; [done|iSplit].
    - iApply ty_own_depth_mono; [|done]. lia.
    - iIntros "↦". iMod ("Toκ" with "Na ↦") as "[$ κ]". by iMod ("ToL" with "κ") as "$".
  Qed.
End typing.

Global Hint Resolve shr_resolve shr_subtype shr_eqtype read_shr : lrust_typing.
