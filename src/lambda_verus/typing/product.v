From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export type.
From lrust.typing Require Import mod_ty.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ 𝔇: syn_type.

Section product.
  Context `{!typeG Σ}.

  Program Definition unit0 : type (Π! []) :=
    {| ty_size := 0;  ty_lfts := [];  ty_E := [];
       ty_own vπ d tid vl := ⌜vl = []⌝;
       ty_shr vπ d κ tid l := True; |}%I.
  Next Obligation. iIntros (????) "-> //". Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. auto. Qed.
  Next Obligation. iIntros. iApply step_fupdN_full_intro. iIntros "!>!> {$∗}". Qed.
  Next Obligation.
    iIntros. iApply step_fupdN_full_intro. subst. iIntros "!>!> {$∗}".
    iExists [], 1%Qp. iSplit; [|by simpl]. iPureIntro. apply proph_dep_singleton.
    by intros [][].
  Qed.
  Next Obligation.
    iIntros "**!>!>!>". iApply step_fupdN_full_intro. iFrame.
    iExists [], 1%Qp. iSplitL; [|by simpl]. iPureIntro. apply proph_dep_singleton.
    by intros [][].
  Qed.

  Global Instance unit0_copy : Copy unit0.
  Proof.
    split. by apply _. iIntros "* _ _ _ _ Htok Hκ".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
    iExists 1%Qp, []. iModIntro. rewrite heap_mapsto_vec_nil left_id.
    iSplitR; [done|]. iFrame. iIntros "? _". by iApply "Htok".
  Qed.

  Global Instance unit0_send : Send unit0.
  Proof. done. Qed.
  Global Instance unit0_sync : Sync unit0.
  Proof. done. Qed.

  Lemma unit0_resolve E L : resolve E L unit0 (const True).
  Proof. apply resolve_just. Qed.

  Lemma unit0_real E L : real E L unit0 id.
  Proof.
    split; iIntros (?? vπ) "*% _ _ $ %"; iApply step_fupdN_full_intro;
    iPureIntro; [split; [|done]|]; exists -[]; fun_ext=>/= π; by case (vπ π).
  Qed.

  Lemma split_mt_prod {𝔄 𝔅} vπ d vπ' d' tid (ty: type 𝔄) (ty': type 𝔅) l :
    (l ↦∗: λ vl, ∃wl wl', ⌜vl = wl ++ wl'⌝ ∗
      ty.(ty_own) vπ d tid wl ∗ ty'.(ty_own) vπ' d' tid wl') ⊣⊢
    l ↦∗: ty.(ty_own) vπ d tid ∗
      (l +ₗ ty.(ty_size)) ↦∗: ty'.(ty_own) vπ' d' tid.
  Proof.
    iSplit.
    - iIntros "(%& ↦ &%&%&->& ty & ty')". rewrite heap_mapsto_vec_app.
      iDestruct "↦" as "[↦ ↦']". iDestruct (ty_size_eq with "ty") as %->.
      iSplitL "↦ ty"; iExists _; iFrame.
    - iIntros "[(%wl & ↦ & ty) (%wl' & ↦' & ty')]". iExists (wl ++ wl').
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "ty") as %->.
      iFrame "↦ ↦'". iExists wl, wl'. by iFrame.
  Qed.

  Program Definition prod_ty {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) : type (𝔄 * 𝔅) := {|
    ty_size := ty.(ty_size) + ty'.(ty_size);
    ty_lfts := ty.(ty_lfts) ++ ty'.(ty_lfts);  ty_E := ty.(ty_E) ++ ty'.(ty_E);
    ty_own vπ d tid vl := ∃wl wl', ⌜vl = wl ++ wl'⌝ ∗
      ty.(ty_own) (fst ∘ vπ) d tid wl ∗ ty'.(ty_own) (snd ∘ vπ) d tid wl';
    ty_shr vπ d κ tid l := ty.(ty_shr) (fst ∘ vπ) d κ tid l ∗
      ty'.(ty_shr) (snd ∘ vπ) d κ tid (l +ₗ ty.(ty_size))
  |}%I.
  Next Obligation.
    iIntros "* (%&%&->& H)". rewrite app_length !ty_size_eq. by iDestruct "H" as "[->->]".
  Qed.
  Next Obligation. move=>/= *. do 6 f_equiv; by apply ty_own_depth_mono. Qed.
  Next Obligation. move=>/= *. f_equiv; by apply ty_shr_depth_mono. Qed.
  Next Obligation.
    iIntros "* In [??]". iSplit; by iApply (ty_shr_lft_mono with "In").
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #? Bor [κ κ₊]". rewrite split_mt_prod.
    iMod (bor_sep with "LFT Bor") as "[Bor Bor']"; first done.
    iMod (ty_share with "LFT [] Bor κ") as "ty"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iMod (ty_share with "LFT [] Bor' κ₊") as "ty'"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iCombine "ty ty'" as "ty2". iApply (step_fupdN_wand with "ty2").
    by iIntros "!> [>[$$] >[$$]]".
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #? (%wl & %wl' &->& ty & ty') [κ κ₊]".
    iDestruct (ty_own_proph with "LFT [] ty κ") as ">Toty"; [done| |].
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iDestruct (ty_own_proph with "LFT [] ty' κ₊") as ">Toty'"; [done| |].
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iCombine "Toty Toty'" as "Toty2". iApply (step_fupdN_wand with "Toty2").
    iIntros "!> [Toty Toty']". iMod "Toty" as (???) "[ξl Toty]".
    iMod "Toty'" as (???) "[ξl' Toty']".
    iDestruct (proph_tok_combine with "ξl ξl'") as (?) "[ξl Toξl]".
    iExists _, _. iModIntro. iSplit.
    - iPureIntro. by apply proph_dep_prod.
    - iIntros "{$ξl}ξl". iDestruct ("Toξl" with "ξl") as "[ξl ξl']".
      iMod ("Toty" with "ξl") as "[?$]". iMod ("Toty'" with "ξl'") as "[?$]".
      iModIntro. iExists wl, wl'. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #In #? [ty ty'] [κ κ₊]".
    iDestruct (ty_shr_proph with "LFT In [] ty κ") as "> Toκ"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iDestruct (ty_shr_proph with "LFT In [] ty' κ₊") as "> Toκ₊"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iIntros "!>!>". iCombine "Toκ Toκ₊" as ">Toκ2".
    iApply (step_fupdN_wand with "Toκ2"). iIntros "!> [Toκ Toκ₊]".
    iMod "Toκ" as (ξl q ?) "[ξl Toκ]". iMod "Toκ₊" as (ξl' q' ?) "[ξl' Toκ₊]".
    iDestruct (proph_tok_combine with "ξl ξl'") as (q0) "[ξl Toξl]".
    iExists (ξl ++ ξl'), q0. iModIntro. iSplit.
    - iPureIntro. by apply proph_dep_prod.
    - iIntros "{$ξl}ξl". iDestruct ("Toξl" with "ξl") as "[ξl ξl']".
      iMod ("Toκ" with "ξl") as "$". by iMod ("Toκ₊" with "ξl'") as "$".
  Qed.

  Global Instance prod_ty_ne {𝔄 𝔅} : NonExpansive2 (@prod_ty 𝔄 𝔅).
  Proof. solve_ne_type. Qed.

  Fixpoint xprod_ty {𝔄l} (tyl: typel 𝔄l) : type (Π! 𝔄l) :=
    match tyl in hlist _ 𝔄l return type (Π! 𝔄l) with
    | +[] => unit0
    | ty +:: tyl' => mod_ty (𝔄:=_*Π!_) (𝔅:=Π!(_::_))
                            to_cons_prod (prod_ty ty (xprod_ty tyl'))
    end.

  Global Instance product_ne {𝔄l} : NonExpansive (@xprod_ty 𝔄l).
  Proof. move=> ???. elim; [done|]=> */=. by do 2 f_equiv. Qed.

  Definition unit_ty := (<{const ((): ()%ST)}> (xprod_ty +[]))%T.
End product.

Notation "ty * ty'" := (prod_ty ty%T ty'%T) : lrust_type_scope.
Notation "Π!" := xprod_ty : lrust_type_scope.
Notation "()" := unit_ty : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma unit_ty_own vπ d tid vl :
    ().(ty_own) vπ d tid vl ⊣⊢ ⌜vl = []⌝.
  Proof. by rewrite /unit_ty mod_ty_own. Qed.

  Lemma unit_ty_shr vπ d κ tid l :
    ().(ty_shr) vπ d κ tid l ⊣⊢ True.
  Proof. by rewrite /unit_ty mod_ty_shr. Qed.

  Lemma unit_resolve E L : resolve E L () (const True).
  Proof. apply resolve_just. Qed.

  Hint Resolve unit0_real : lrust_typing.
  Lemma unit_real E L : real E L () id.
  Proof.
    eapply real_eq.
    { apply mod_ty_real; [apply _|].
      apply (real_compose (𝔅:=Π![]) (ℭ:=()) (const ())). solve_typing. }
    fun_ext. by case.
  Qed.

  Global Instance prod_lft_morphism {𝔄 𝔅 ℭ} (T: type 𝔄 → type 𝔅) (T': type 𝔄 → type ℭ):
    TypeLftMorphism T → TypeLftMorphism T' → TypeLftMorphism (λ ty, T ty * T' ty)%T.
  Proof.
    case=> [α βs E Hα HE|α E Hα HE]; case=> [α' βs' E' Hα' HE'|α' E' Hα' HE'].
    - apply (type_lft_morphism_add _ (α ⊓ α') (βs ++ βs') (E ++ E'))=> ty.
      + rewrite lft_intersect_list_app. iApply lft_equiv_trans.
        { iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα']. }
        rewrite -!assoc (comm (⊓) (ty_lft ty) (α' ⊓ _)) -!assoc.
        repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
        iApply lft_intersect_equiv_idemp.
      + rewrite/= !elctx_interp_app HE HE' big_sepL_app -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc (comm (⊓) α' (ty_lft ty)) assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + rewrite/= !elctx_interp_app HE HE' -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs' (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite/= !elctx_interp_app HE HE' -!assoc.
    - apply (type_lft_morphism_const _ (α ⊓ α') (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite/= !elctx_interp_app HE HE'.
  Qed.

  Global Instance prod_type_ne {𝔄 𝔅 ℭ} (T: type 𝔄 → type 𝔅) (T': type 𝔄 → type ℭ) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (λ ty, T ty * T' ty)%T.
  Proof.
    move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_ne_ty_size.
    - move=> *. do 6 f_equiv; by apply type_ne_ty_own.
    - move=> ? ty ty' *. rewrite (type_ne_ty_size (T:=T) ty ty'); [|done].
      f_equiv; by apply type_ne_ty_shr.
  Qed.
  (* TODO : find a way to avoid this duplication. *)
  Global Instance prod_type_contractive {𝔄 𝔅 ℭ} (T: type 𝔄 → type 𝔅) (T': type 𝔄 → type ℭ) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty * T' ty)%T.
  Proof.
    move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_contractive_ty_size.
    - move=> *. do 6 f_equiv; by apply type_contractive_ty_own.
    - move=> ? ty ty' *. rewrite (type_contractive_ty_size (T:=T) ty ty').
      f_equiv; by apply type_contractive_ty_shr.
  Qed.

  Global Instance xprod_type_ne {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (Π! ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. apply (type_ne_ne_compose (mod_ty _) _ _ _).
  Qed.
  Global Instance xprod_type_contractive {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeContractive T → TypeContractive (Π! ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. apply (type_contractive_compose_left (mod_ty _) _ _ _).
  Qed.

  Global Instance prod_copy {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    Copy ty → Copy ty' → Copy (ty * ty').
  Proof.
    move=> ??. split; [by apply _|]=>/= > ? HF. iIntros "#LFT [ty ty'] Na [κ κ₊]".
    iMod (copy_shr_acc with "LFT ty Na κ") as (q wl) "(Na & ↦ & #ty & Toκ)";
      first done.
    { rewrite <-HF. apply shr_locsE_subseteq=>/=. lia. }
    iMod (copy_shr_acc with "LFT ty' Na κ₊") as (q' wl') "(Na & ↦' & #ty' & Toκ₊)";
      first done.
    { apply subseteq_difference_r. { symmetry. apply shr_locsE_disj. }
      move: HF. rewrite -plus_assoc shr_locsE_shift. set_solver. }
    iDestruct (na_own_acc with "Na") as "[$ ToNa]".
    { rewrite shr_locsE_shift. set_solver. }
    case (Qp_lower_bound q q')=> [q''[?[?[->->]]]]. iExists q'', (wl ++ wl').
    rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "ty") as ">->".
    iDestruct "↦" as "[$ ↦r]". iDestruct "↦'" as "[$ ↦r']". iSplitR.
    { iIntros "!>!>". iExists wl, wl'. iSplit; by [|iSplit]. }
    iIntros "!> Na [↦ ↦']". iDestruct ("ToNa" with "Na") as "Na".
    iMod ("Toκ₊" with "Na [$↦' $↦r']") as "[Na $]".
    iApply ("Toκ" with "Na [$↦ $↦r]").
  Qed.

  Global Instance prod_send {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    Send ty → Send ty' → Send (ty * ty').
  Proof. move=> >/=. by do 6 f_equiv. Qed.
  Global Instance prod_sync {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) :
    Sync ty → Sync ty' → Sync (ty * ty').
  Proof. move=> >/=. by f_equiv. Qed.

  Global Instance xprod_copy {𝔄l} (tyl: typel 𝔄l) : ListCopy tyl → Copy (Π! tyl).
  Proof. elim; apply _. Qed.
  Global Instance xprod_send {𝔄l} (tyl: typel 𝔄l) : ListSend tyl → Send (Π! tyl).
  Proof. elim; apply _. Qed.
  Global Instance xprod_sync {𝔄l} (tyl: typel 𝔄l) : ListSync tyl → Sync (Π! tyl).
  Proof. elim; apply _. Qed.

  Lemma prod_resolve {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) Φ Φ' E L :
    resolve E L ty Φ → resolve E L ty' Φ' →
    resolve E L (ty * ty') (λ '(a, b), Φ a ∧ Φ' b).
  Proof.
    iIntros (Rslv Rslv' ?? vπ ????) "#LFT #PROPH #E [L L'] (%&%&->& ty & ty')".
    iMod (Rslv with "LFT PROPH E L ty") as "ToObs"; [done|].
    iMod (Rslv' with "LFT PROPH E L' ty'") as "ToObs'"; [done|].
    iCombine "ToObs ToObs'" as "ToObs". iApply (step_fupdN_wand with "ToObs").
    iIntros "!> [>[Obs $] >[Obs' $]] !>". iCombine "Obs Obs'" as "?".
    iApply proph_obs_eq; [|done]=>/= π. by case (vπ π).
  Qed.

  Lemma prod_resolve_just {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) E L :
    resolve E L ty (const True) → resolve E L ty' (const True) →
    resolve E L (ty * ty') (const True).
  Proof. move=> ??. apply resolve_just. Qed.

  Hint Resolve prod_resolve : lrust_typing.
  Lemma xprod_resolve {𝔄l} (tyl: typel 𝔄l) Φl E L :
    resolvel E L tyl Φl →
    resolve E L (Π! tyl) (λ al, pforall (λ _, uncurry ($)) (pzip Φl al)).
  Proof.
    elim; [eapply resolve_impl; [apply resolve_just|done]|]=>/= *.
    by eapply resolve_impl; [solve_typing|]=>/= [[??][??]].
  Qed.

  Lemma xprod_resolve_just {𝔄l} (tyl: typel 𝔄l) E L :
    HForall (λ _ ty, resolve E L ty (const True)) tyl →
    resolve E L (Π! tyl) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma prod_real {𝔄 𝔅 ℭ 𝔇} ty ty' (f: 𝔄 → ℭ) (g: 𝔅 → 𝔇) E L :
    real E L ty f → real E L ty' g →
    real (𝔅:=_*_) E L (ty * ty') (prod_map f g).
  Proof.
    move=> [Rlo Rls][Rlo' Rls']. split.
    - iIntros (?? vπ) "*% #LFT #E [L L₊] (%&%&->& ty & ty')".
      iMod (Rlo with "LFT E L ty") as "Upd"; [done|].
      iMod (Rlo' with "LFT E L₊ ty'") as "Upd'"; [done|].
      iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand with "Upd").
      iIntros "!>[>(%Eq &$&?) >(%Eq' &$&?)] !>".
      iSplit; last first. { iExists _, _. by iFrame. }
      iPureIntro. move: Eq=> [a Eq]. move: Eq'=> [b Eq']. exists (a, b).
      fun_ext=>/= π. move: (equal_f Eq π) (equal_f Eq' π)=>/=.
      by case (vπ π)=>/= ??<-<-.
    - iIntros (?? vπ) "*% #LFT #E [L L₊] [ty ty']".
      iMod (Rls with "LFT E L ty") as "Upd"; [done|].
      iMod (Rls' with "LFT E L₊ ty'") as "Upd'"; [done|]. iIntros "!>!>".
      iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand with "Upd").
      iIntros "[>(%Eq &$&$) >(%Eq' &$&$)] !%".
      move: Eq=> [a Eq]. move: Eq'=> [b Eq']. exists (a, b).
      fun_ext=>/= π. move: (equal_f Eq π) (equal_f Eq' π)=>/=.
      by case (vπ π)=>/= ??<-<-.
  Qed.

  Hint Resolve prod_real : lrust_typing.
  Lemma xprod_real {𝔄l 𝔅l} tyl (fl: plist2 _ 𝔄l 𝔅l) E L :
    reall E L tyl fl → real (𝔅:=Π! _) E L (Π! tyl) (plist_map fl).
  Proof.
    elim; [solve_typing|]=>/= > Rl _ Rl'. eapply real_eq.
    { apply mod_ty_real; [by apply _|].
      apply (real_compose (𝔅:=_*Π!_) (ℭ:=Π!(_::_)) to_cons_prod). solve_typing. }
    fun_ext=>/=. by case.
  Qed.

  Lemma prod_subtype {𝔄 𝔅 𝔄' 𝔅'} E L f g
                     (ty1: type 𝔄) (ty2: type 𝔅) (ty1': type 𝔄') (ty2': type 𝔅') :
    subtype E L ty1 ty1' f → subtype E L ty2 ty2' g →
    subtype E L (ty1 * ty2) (ty1' * ty2') (prod_map f g).
  Proof.
    move=> Sub Sub' ?. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iDestruct (Sub' with "L") as "#Sub'". iIntros "!> #E".
    iDestruct ("Sub" with "E") as (Eq) "(#?& #InOwn & #InShr)".
    iDestruct ("Sub'" with "E") as (?) "(#?& #InOwn' & #InShr')".
    iSplit=>/=; [|iSplit; [|iSplit; iModIntro]].
    - iPureIntro. by f_equal.
    - rewrite !lft_intersect_list_app. by iApply lft_intersect_mono.
    - iIntros "* (%&%&->& ty &?)". iExists _, _. iSplit; [done|].
      iSplitL "ty"; by [iApply "InOwn"|iApply "InOwn'"].
    - iIntros "* #[??]". rewrite Eq. iSplit; by [iApply "InShr"|iApply "InShr'"].
  Qed.
  Lemma prod_eqtype {𝔄 𝔅 𝔄' 𝔅'} E L (f: 𝔄 → 𝔄') f' (g: 𝔅 → 𝔅') g'
        (ty1: type 𝔄) (ty2: type  𝔅) (ty1': type 𝔄') (ty2': type 𝔅') :
    eqtype E L ty1 ty1' f f' → eqtype E L ty2 ty2' g g' →
    eqtype E L (ty1 * ty2) (ty1' * ty2') (prod_map f g) (prod_map f' g').
  Proof. move=> [??][??]. split; by apply prod_subtype. Qed.

  Lemma xprod_subtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl :
    subtypel E L tyl tyl' fl → subtype E L (Π! tyl) (Π! tyl') (plist_map fl).
  Proof.
    move=> Subs. elim Subs; [solve_typing|]=> *. eapply subtype_eq.
    { apply mod_ty_subtype; [apply _|]. by apply prod_subtype. }
    fun_ext. by case.
  Qed.
  Lemma xprod_eqtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (Π! tyl) (Π! tyl') (plist_map fl) (plist_map gl).
  Proof.
    move=> /eqtypel_subtypel[??]. by split; apply xprod_subtype.
  Qed.

  Lemma prod_ty_assoc {𝔄 𝔅 ℭ} E L (ty1: type 𝔄) (ty2: type 𝔅) (ty3: type ℭ) :
    eqtype E L (ty1 * (ty2 * ty3)) ((ty1 * ty2) * ty3) prod_assoc prod_assoc'.
  Proof.
    have Eq: ∀vπ: proph (𝔄 * (𝔅 * ℭ)),
      fst ∘ (fst ∘ (prod_assoc ∘ vπ)) = fst ∘ vπ ∧
      snd ∘ (fst ∘ (prod_assoc ∘ vπ)) = fst ∘ (snd ∘ vπ) ∧
      snd ∘ (prod_assoc ∘ vπ) = snd ∘ (snd ∘ vπ).
    { move=> vπ. split; [|split]; fun_ext=>/= π; by case (vπ π)=> [?[??]]. }
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=". iSplit; [iPureIntro; lia|].
    iSplit; [rewrite (assoc (++)); by iApply lft_equiv_refl|].
    iSplit; iIntros "!>" (vπ) "*"; move: (Eq vπ)=> [->[->->]]; [iSplit|].
    - iIntros "(%wl1 & %&->&?& %wl2 & %wl3 &->&?& Own3)". iExists (wl1 ++ wl2), wl3.
      iSplit; [by rewrite assoc|]. iFrame "Own3". iExists wl1, wl2. by iFrame.
    - iIntros "(%& %wl3 &->& (%wl1 & %wl2 &->& Own1 &?) &?)". iExists wl1, (wl2 ++ wl3).
      iSplit; [by rewrite assoc|]. iFrame "Own1". iExists wl2, wl3. by iFrame.
    - rewrite -assoc shift_loc_assoc_nat. by iApply bi.equiv_iff.
  Qed.

  Lemma prod_ty_left_id {𝔄} E L (ty: type 𝔄) :
    eqtype E L (() * ty) ty prod_left_id prod_left_id'.
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [by iApply lft_equiv_refl|].
    have Eq: ∀vπ: proph (_ * 𝔄), prod_left_id ∘ vπ = snd ∘ vπ.
    { move=> vπ. fun_ext=>/= π. by case (vπ π)=> [[]?]. }
    iSplit; iIntros "!>*"; rewrite Eq.
    - iSplit.
      + by iDestruct 1 as ([|] ? -> (?&?&?)) "?".
      + iIntros. iExists [], _. iFrame. iPureIntro.
        split; [done|]. exists (λ _, -[]). split; [|done].
        fun_ext=>? /=. by destruct fst.
    - rewrite shift_loc_0. iSplit; [by iIntros "[? $]"|iIntros "$"].
      iPureIntro. exists (const -[]). rewrite right_id. fun_ext=>? /=.
      by destruct fst.
  Qed.

  Lemma prod_ty_right_id {𝔄} E L (ty: type 𝔄) :
    eqtype E L (ty * ()) ty prod_right_id prod_right_id'.
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=".
    rewrite !right_id. iSplit; [done|]. iSplit; [by iApply lft_equiv_refl|].
    have Eq: ∀vπ: proph (𝔄 * _), prod_right_id ∘ vπ = fst ∘ vπ.
    { move=> vπ. fun_ext=>/= π. by case (vπ π)=> [?[]]. }
    iSplit; iIntros "!>*"; rewrite Eq; [iSplit|].
    - iDestruct 1 as (?[|]->) "[? %H]"; [by rewrite right_id|naive_solver].
    - iIntros. iExists _, []. iFrame. iPureIntro. rewrite right_id.
      split; [done|]. exists (const -[]). split; [|done]. fun_ext=>? /=.
      by destruct snd.
    - iSplit; [by iIntros "[$ ?]"|iIntros "$"]. iPureIntro. exists (const -[]).
      rewrite right_id. fun_ext=>? /=. by destruct snd.
  Qed.

  Lemma xprod_ty_app_prod {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) :
    eqtype E L (Π! (tyl h++ tyl')) (Π! tyl * Π! tyl') psep (uncurry papp).
  Proof.
    elim: tyl=> [|> Eq].
    - eapply eqtype_eq.
      + eapply eqtype_trans; [apply eqtype_symm, prod_ty_left_id|].
        apply prod_eqtype; solve_typing.
      + done.
      + done.
    - eapply eqtype_eq.
      + eapply eqtype_trans; [by apply mod_ty_outin, _|].
        eapply eqtype_trans. { eapply prod_eqtype; [solve_typing|apply Eq]. }
        eapply eqtype_trans; [by apply prod_ty_assoc|].
        apply prod_eqtype; solve_typing.
      + fun_ext. by case.
      + fun_ext. by case=> [[??]?].
  Qed.

  Lemma prod_outlives_E {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) κ :
    ty_outlives_E (ty * ty') κ = ty_outlives_E ty κ ++ ty_outlives_E ty' κ.
  Proof. by rewrite /ty_outlives_E /= fmap_app. Qed.

  Lemma xprod_outlives_E_elctx_sat {𝔄l} E L (tyl: typel 𝔄l) κ:
    elctx_sat E L (tyl_outlives_E tyl κ) → elctx_sat E L (ty_outlives_E (Π! tyl) κ).
  Proof.
    move=> ?. eapply eq_ind; [done|]. rewrite /ty_outlives_E /=.
    elim tyl=>/= [|> IH]; [done|]. by rewrite fmap_app -IH.
  Qed.
End typing.

Global Hint Resolve prod_resolve xprod_resolve | 5 : lrust_typing.
Global Hint Resolve unit_resolve prod_resolve_just xprod_resolve_just
  unit_real prod_real xprod_real
  prod_subtype prod_eqtype xprod_subtype xprod_eqtype
  xprod_outlives_E_elctx_sat : lrust_typing.
