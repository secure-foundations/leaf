From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import type_context lft_contexts product own uniq_bor.
From lrust.typing Require Import shr_bor mod_ty uninit.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l ℭl: syn_typel).

Section product_split.
  Context `{!typeG Σ}.

  (** * General Split/Merger for Plain Pointer Types *)

  Fixpoint hasty_ptr_offsets {𝔄l} (p: path) (ptr: ∀{𝔄}, type 𝔄 → type 𝔄)
      (tyl: typel 𝔄l) (off: nat) : tctx 𝔄l :=
    match tyl with
    | +[] => +[]
    | ty +:: tyl' =>
      p +ₗ #off ◁ ptr ty +:: hasty_ptr_offsets p (@ptr) tyl' (off + ty.(ty_size))
    end.

  Lemma hasty_ptr_offsets_equiv {𝔄l} ptr p (tyl: typel 𝔄l) (off off': nat) :
    tctx_equiv (hasty_ptr_offsets (p +ₗ #off) ptr tyl off')
      (hasty_ptr_offsets p ptr tyl (off + off')).
  Proof.
    apply get_tctx_equiv=> ? vπl. move: p off off'.
    induction tyl, vπl; [done|]=>/= p ??. f_equiv; [|by rewrite IHtyl Nat.add_assoc].
    apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Definition ptr_homo_sub (ptr: ∀{𝔄}, type 𝔄 → type 𝔄) : Prop :=
    ∀E L 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅) f,
      subtype E L ty ty' f → subtype E L (ptr ty) (ptr ty') f.

  Lemma tctx_split_ptr_xprod {𝔄l} (ptr: ∀{𝔄}, type 𝔄 → type 𝔄) (tyl: typel 𝔄l) E L :
    ptr_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p ◁ ptr (ty * ty')]
          +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          (λ post '-[(a, b)], post -[a; b])) →
    ∀p, tctx_incl E L +[p ◁ ptr (Π! tyl)] (hasty_ptr_offsets p (@ptr) tyl 0)
                       (λ post '-[al], post al).
  Proof.
    move=> HSub Split. elim: tyl.
    { move=> ?.
      by eapply tctx_incl_ext; [apply tctx_incl_resolve_head|]=>/= ?[[][]]. }
    move=>/= ??? tyl IH ?.
    eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [by eapply subtype_tctx_incl, HSub, mod_ty_out, _|].
      eapply tctx_incl_trans; [by apply Split|]. apply tctx_incl_tail.
      eapply tctx_incl_trans; [by apply IH|]. rewrite -{2}[ty_size _]Nat.add_0_r.
      eapply proj1, hasty_ptr_offsets_equiv. }
    by move=>/= ?[[??][]].
  Qed.

  Lemma tctx_merge_ptr_xprod {𝔄l} (ptr: ∀{𝔄}, type 𝔄 → type 𝔄) (tyl: typel 𝔄l)
      E L `{∀𝔄 (ty: type 𝔄), JustLoc (ptr ty)} :
    ptr_homo_sub (@ptr) →
    (∀p 𝔄 𝔅 (ty: type 𝔄) (ty': type 𝔅),
        tctx_incl E L +[p +ₗ #0 ◁ ptr ty; p +ₗ #ty.(ty_size) ◁ ptr ty']
          +[p ◁ ptr (ty * ty')] (λ post '-[a; b], post -[(a, b)])) →
    𝔄l ≠ [] →
    ∀p, tctx_incl E L (hasty_ptr_offsets p (@ptr) tyl 0) +[p ◁ ptr (Π! tyl)]
                      (λ post al, post -[al]).
  Proof.
    move=> HSub Merge. elim: tyl; [done|]=> ?? ty. case=>/=.
    { move=> _ _ ?. eapply tctx_incl_ext.
      { eapply tctx_incl_trans; [apply tctx_of_shift_loc_0|].
        eapply subtype_tctx_incl, HSub, subtype_trans, mod_ty_in.
        eapply subtype_trans; [apply prod_ty_right_id|].
        apply prod_subtype; solve_typing. }
        by move=> ?[?[]]. }
    move=> ???? IH _ ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [|by eapply subtype_tctx_incl, HSub, mod_ty_in].
      eapply tctx_incl_trans; [|by apply Merge]. apply tctx_incl_tail.
      eapply tctx_incl_trans; [|by apply IH].
      apply (tctx_incl_app +[_] +[_]); [by apply tctx_to_shift_loc_0, _|].
      eapply proj2, hasty_ptr_offsets_equiv. }
    by move=>/= ?[?[??]].
  Qed.
End product_split.

Global Hint Unfold ptr_homo_sub : lrust_typing.
Notation hasty_own_offsets p n :=
  (hasty_ptr_offsets p (λ 𝔄, own_ptr (𝔄:=𝔄) n)).
Notation hasty_shr_offsets p κ :=
  (hasty_ptr_offsets p (λ 𝔄, shr_bor (𝔄:=𝔄) κ)).

Section product_split.
  Context `{!typeG Σ}.

  (** * Owning Pointers *)

  Lemma tctx_split_own_prod {𝔄 𝔅} n (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p ◁ own_ptr n (ty * ty')]
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      (λ post '-[(a, b)], post -[a; b]).
  Proof.
    split; [by intros ??? [[??][]]|].
    iIntros (??[abπ[]]?) "_ _ _ _ $ [p _] Obs".
    iDestruct "p" as ([[]|][|]Ev) "[#? own]"=>//.
    iDestruct "own" as "[(% & >↦ & (%&%&>->& ty & ty')) †]".
    rewrite heap_mapsto_vec_app -freeable_sz_split.
    iDestruct (ty_size_eq with "ty") as "#>->".
    iDestruct "↦" as "[↦ ↦']". iDestruct "†" as "[† †']". iModIntro.
    iExists -[fst ∘ abπ; snd ∘ abπ]. iSplitR "Obs"; last first.
    { iApply proph_obs_eq; [|done]=>/= π. by case (abπ π). }
    iSplitL "ty ↦ †"; [|iSplitL; [|done]]; iExists _, _;
    (iSplit; [by rewrite/= Ev|]; iSplit; [done|]); [rewrite shift_loc_0|];
    [iFrame "†"|iFrame "†'"]; iNext; iExists _; iFrame.
  Qed.

  Lemma tctx_merge_own_prod {𝔄 𝔅} n (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty']
      +[p ◁ own_ptr n (ty * ty')] (λ post '-[a; b], post -[(a, b)]).
  Proof.
    eapply tctx_incl_ext;
      [eapply tctx_incl_trans; [apply tctx_of_shift_loc_0|]
      |by intros; apply (iff_refl _)].
    split; [by intros ??? [?[?[]]]|].
    iIntros (??(?&?&[])?) "_ _ _ _ $ (p & p' &_) Obs".
    iDestruct "p" as ([[]|][|]Ev) "[⧖ own]"=>//.
    iDestruct "p'" as ([[]|][|]Ev') "[⧖' own']"=>//.
    move: Ev'. rewrite/= Ev. move=> [=<-]. iCombine "⧖ ⧖'" as "?".
    iDestruct "own" as "[(% & >↦ & ty) †]".
    iDestruct "own'" as "[(% & >↦' & ty') †']". iModIntro.
    iExists -[_]. iFrame "Obs". iSplitL; [|done]. iExists _, _.
    do 2 (iSplit; [done|]). rewrite/= -freeable_sz_split. iFrame "† †'".
    iNext. iExists (_ ++ _). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "ty") as %->. iFrame "↦ ↦'". iExists _, _.
    iSplit; [done|]. iSplitL "ty"; (iApply ty_own_depth_mono; [|done]); lia.
  Qed.

  Lemma tctx_split_own_xprod {𝔄l} n (tyl: typel 𝔄l) p E L :
    tctx_incl E L +[p ◁ own_ptr n (Π! tyl)]
      (hasty_own_offsets p n tyl 0) (λ post '-[al], post al).
  Proof.
    apply (tctx_split_ptr_xprod (λ _, own_ptr n));
    [solve_typing|move=> *; apply tctx_split_own_prod].
  Qed.

  Lemma tctx_merge_own_xprod {𝔄 𝔄l} n (tyl: typel (𝔄 :: 𝔄l)) p E L :
    tctx_incl E L (hasty_own_offsets p n tyl 0)
      +[p ◁ own_ptr n (Π! tyl)] (λ post al, post -[al]).
  Proof.
    apply (tctx_merge_ptr_xprod (λ _, own_ptr n));
    [apply _|solve_typing|move=> *; apply tctx_merge_own_prod|done].
  Qed.

  (** * Shared References *)

  Lemma tctx_split_shr_prod {𝔄 𝔅} κ (ty: type 𝔄) (ty': type 𝔅) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (ty * ty')]
      +[p +ₗ #0 ◁ &shr{κ} ty; p +ₗ #ty.(ty_size) ◁ &shr{κ} ty']
      (λ post '-[(a, b)], post -[a; b]).
  Proof.
    split; [by intros ??? [[??][]]|].
    iIntros (??[abπ[]]?) "_ _ _ _ $ [p _] Obs !>".
    iDestruct "p" as ([[]|][|]Ev) "[#? own]"=>//. iDestruct "own" as "[ty ty']".
    iExists -[fst ∘ abπ; snd ∘ abπ]. iSplitR "Obs"; last first.
    { iApply proph_obs_eq; [|done]=>/= π. by case (abπ π). }
    iSplitL "ty"; [|iSplitL; [|done]]; iExists _, _;
    (iSplit; [by rewrite/= Ev|]); [rewrite shift_loc_0|]; by iSplit.
  Qed.

  Lemma tctx_split_shr_xprod {𝔄l} κ (tyl: typel 𝔄l) p E L :
    tctx_incl E L +[p ◁ &shr{κ} (Π! tyl)]
      (hasty_shr_offsets p κ tyl 0) (λ post '-[al], post al).
  Proof.
    apply (tctx_split_ptr_xprod (λ _, &shr{κ}%T));
    [solve_typing|move=> *; apply tctx_split_shr_prod].
  Qed.

  (** * Unique References *)

  Lemma tctx_split_uniq_prod {𝔄 𝔅} κ (ty: type 𝔄) (ty': type 𝔅) E L p :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (ty * ty')]
      +[p +ₗ #0 ◁ &uniq{κ} ty; p +ₗ #ty.(ty_size) ◁ &uniq{κ} ty']
      (λ post '-[((a, b), (a', b'))], post -[(a, a'); (b, b')]).
  Proof.
    intros Alv. split; [by intros ??? [[[??][??]][]]|].
    iIntros (??[vπ[]]?) "#LFT #PROPH #UNIQ E L [p _] Obs".
    set aπ: proph 𝔄 := λ π, (vπ π).1.1. set bπ: proph 𝔅 := λ π, (vπ π).1.2.
    have ?: Inhabited 𝔄 := populate (aπ inhabitant).
    have ?: Inhabited 𝔅 := populate (bπ inhabitant).
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iDestruct "p" as ([[]|]? Ev) "[_ [#In uniq]]"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[ξVo ξBor]".
    move: Eq. (set ξ := PrVar _ ξi)=> Eq.
    iMod (bor_acc_cons with "LFT ξBor κ") as "[(%&% & >#⧖ & ξPc & ↦ty) ToBor]"; [done|].
    iMod (uniq_strip_later with "ξVo ξPc") as (<-<-) "[ξVo ξPc]".
    iMod (uniq_intro aπ with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    iMod (uniq_intro bπ with "PROPH UNIQ") as (ζ'i) "[ζ'Vo ζ'Pc]"; [done|].
    set ζ := PrVar _ ζi. set ζ' := PrVar _ ζ'i.
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ζPc)".
    iDestruct (uniq_proph_tok with "ζ'Vo ζ'Pc") as "(ζ'Vo & ζ' & ζ'Pc)".
    iMod (uniq_preresolve ξ [ζ; ζ'] (λ π, (π ζ, π ζ')) with
      "PROPH ξVo ξPc [$ζ $ζ']") as "(Obs' & (ζ & ζ' &_) & ToξPc)"; [done| |done|].
    { apply (proph_dep_prod [_] [_]); apply proph_dep_one. }
    iCombine "Obs Obs'" as "#Obs".
    iSpecialize ("ζPc" with "ζ"). iSpecialize ("ζ'Pc" with "ζ'").
    iMod ("ToBor" with "[ToξPc] [↦ty ζPc ζ'Pc]") as "[Bor κ]"; last first.
    - iMod ("ToL" with "κ") as "$".
      iMod (bor_sep with "LFT Bor") as "[Bor Bor']"; [done|]. iModIntro.
      iExists -[λ π, (aπ π, π ζ); λ π, (bπ π, π ζ')]. iSplitL; last first.
      { iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq π).
        rewrite/= /aπ /bπ. case (vπ π). by (do 2 case=>/= ??)=> <- [?[=<-<-]]. }
      rewrite lft_intersect_list_app.
      iSplitL "ζVo Bor"; [|iSplit; [|done]]; iExists _, _; iFrame "⧖";
      (iSplit; [by rewrite/= Ev|]); [rewrite shift_loc_0|];
      (iSplit; [|iExists _, _; by iFrame]); iApply lft_incl_trans;
      [|iApply lft_intersect_incl_l| |iApply lft_intersect_incl_r]; done.
    - iNext. iDestruct "↦ty" as (?) "(↦ &%&%&->& ty & ty')".
      rewrite heap_mapsto_vec_app. iDestruct "↦" as "[↦ ↦']".
      iDestruct (ty_size_eq with "ty") as %->. iSplitL "↦ ty ζPc"; iExists _, _;
      iFrame "⧖"; [iFrame "ζPc"|iFrame "ζ'Pc"]; iExists _; iFrame.
    - iClear "⧖". iIntros "!> [(%&% & ⧖ & ζPc & ↦ty) (%&% & ⧖' & ζ'Pc & ↦ty')] !>!>".
      iCombine "⧖ ⧖'" as "⧖"=>/=. iExists (pair ∘ _ ⊛ _), _. iFrame "⧖".
      iSplitR "↦ty ↦ty'".
      { iApply "ToξPc". iApply (proph_eqz_constr2 with "[ζPc] [ζ'Pc]");
        [iApply (proph_ctrl_eqz with "PROPH ζPc")|
         iApply (proph_ctrl_eqz with "PROPH ζ'Pc")]. }
      iDestruct "↦ty" as (?) "[↦ ty]". iDestruct "↦ty'" as (?) "[↦' ty']".
      iExists (_ ++ _). rewrite heap_mapsto_vec_app.
      iDestruct (ty_size_eq with "ty") as %->. iFrame "↦ ↦'". iExists _, _.
      iSplit; [done|]. iSplitL "ty"; (iApply ty_own_depth_mono; [|done]); lia.
  Qed.

  Fixpoint hasty_uniq_offsets {𝔄l} (p: path) (κ: lft)
      (tyl: typel 𝔄l) (off: nat) : tctx (map (λ 𝔄, 𝔄 * 𝔄)%ST 𝔄l) :=
    match tyl with
    | +[] => +[]
    | ty +:: tyl' =>
      p +ₗ #off ◁ &uniq{κ} ty +:: hasty_uniq_offsets p κ tyl' (off + ty.(ty_size))
    end.

  Lemma tctx_split_uniq_xprod {𝔄l} κ (tyl: typel 𝔄l) E L p :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (Π! tyl)] (hasty_uniq_offsets p κ tyl 0)
      (λ post '-[(al, al')], post (ptrans (pzip al al'))).
  Proof.
    move=> ?. move: p. elim: tyl.
    { move=>/= ?. by eapply tctx_incl_ext;
        [apply tctx_incl_resolve_head|]=>/= ?[[][]]_[]. }
    move=>/= 𝔄 𝔅l ty tyl IH p. eapply tctx_incl_ext.
    { eapply tctx_incl_trans.
      { eapply tctx_uniq_eqtype; first apply mod_ty_outin; solve_typing. }
      eapply tctx_incl_trans; [by apply tctx_split_uniq_prod|]. apply tctx_incl_tail.
      eapply tctx_incl_trans; [by apply IH|]. eapply proj1, get_tctx_equiv=> ? vπl.
      move: (ty_size _)=> off. rewrite -{2}(Nat.add_0_r off). move: off 0%nat. clear.
      induction tyl, vπl; [done|]=>/= ??. f_equiv; [|by rewrite IHtyl Nat.add_assoc].
      apply tctx_elt_interp_hasty_path=>/=. case (eval_path p)=>//.
      (do 2 case=>//)=> ?. by rewrite shift_loc_assoc Nat2Z.inj_add. }
    by move=>/= ?[[[??][??]][]].
  Qed.

  (** * Splitting with [tctx_extract_elt]. *)

  (* We do not state the extraction lemmas directly, because we want the
     automation system to be able to perform e.g., borrowing or splitting after
     splitting. *)

  Lemma tctx_extract_split_own_prod {𝔄 𝔅 ℭ 𝔇l 𝔈l} (t: tctx_elt 𝔄) n
      (ty: type 𝔅) (ty': type ℭ) (T: tctx 𝔇l) (T': tctx 𝔈l) tr p E L :
    tctx_extract_elt E L t
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty'] T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr n (ty * ty') +:: T) (T' h++ T)
      (λ post '((b, c) -:: dl), tr (λ '(a -:: el), post (a -:: el -++ dl)) -[b; c]).
  Proof.
    move=> Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; [apply tctx_split_own_prod|done]. }
    destruct Extr as [Htr _]=>/= ?[[??]?].  by apply Htr=>- [??].
  Qed.

  Lemma tctx_extract_split_own_xprod {𝔄 𝔄l 𝔅l ℭl} (t: tctx_elt 𝔄) n
      (tyl: typel 𝔄l) (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_own_offsets p n tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr n (Π! tyl) +:: T) (T' h++ T)
      (λ post '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) al).
  Proof.
    move=> Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; by [apply tctx_split_own_xprod|]. }
    destruct Extr as [Htr _]=>/= ?[??]. by apply Htr=>- [??].
  Qed.

  Lemma tctx_extract_split_shr_prod {𝔄 𝔅 ℭ 𝔇l 𝔈l} (t: tctx_elt 𝔄) κ
      (ty: type 𝔅) (ty': type ℭ) (T: tctx 𝔇l) (T': tctx 𝔈l) tr p E L :
    tctx_extract_elt E L t
      +[p +ₗ #0 ◁ &shr{κ} ty; p +ₗ #ty.(ty_size) ◁ &shr{κ} ty'] T' tr →
    tctx_extract_elt E L t (p ◁ &shr{κ} (ty * ty') +:: T)
      (p ◁ &shr{κ} (ty * ty') +:: T' h++ T) (λ post '((b, c) -:: dl),
        tr (λ '(a -:: el), post (a -:: (b, c) -:: el -++ dl)) -[b; c]).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_+::_+::_)).
      eapply tctx_incl_trans; [apply copy_tctx_incl, _|].
      eapply tctx_incl_trans; [|apply tctx_incl_swap].
      apply (tctx_incl_frame_l _ _ +[_]).
      eapply tctx_incl_trans; [apply tctx_split_shr_prod|done]. }
    by move=>/= ?[[??]?].
  Qed.

  Lemma tctx_extract_split_shr_xprod {𝔄 𝔄l 𝔅l ℭl} (t: tctx_elt 𝔄) κ
      (tyl: typel 𝔄l) (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_shr_offsets p κ tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ &shr{κ} (Π! tyl) +:: T)
      (p ◁ &shr{κ} (Π! tyl) +:: T' h++ T) (λ post '(al -:: bl),
        tr (λ '(a -:: cl), post (a -:: al -:: cl -++ bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_+::_+::_)).
      eapply tctx_incl_trans; [apply copy_tctx_incl, _|].
      eapply tctx_incl_trans; [|apply tctx_incl_swap].
      apply (tctx_incl_frame_l _ _ +[_]).
      eapply tctx_incl_trans; by [apply tctx_split_shr_xprod|]. }
    by move=>/= ?[??].
  Qed.

  Lemma tctx_extract_split_uniq_prod {𝔄 𝔅 ℭ 𝔇l 𝔈l} (t: tctx_elt 𝔄) κ
      (ty: type 𝔅) (ty': type ℭ) (T: tctx 𝔇l) (T': tctx 𝔈l) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t
      +[p +ₗ #0 ◁ &uniq{κ} ty; p +ₗ #ty.(ty_size) ◁ &uniq{κ} ty'] T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} (ty * ty') +:: T) (T' h++ T)
      (λ post '(((b, c), (b', c')) -:: dl),
        tr (λ '(a -:: el), post (a -:: el -++ dl)) -[(b, b'); (c, c')]).
  Proof.
    move=> ? Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; [by apply tctx_split_uniq_prod|done]. }
    destruct Extr as [Htr _]=>/= ?[[[??][??]]?]. by apply Htr=>- [??].
  Qed.

  Lemma tctx_extract_split_uniq_xprod {𝔄 𝔄l 𝔅l ℭl} (t: tctx_elt 𝔄) κ
      (tyl: typel 𝔄l) (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t (hasty_uniq_offsets p κ tyl 0) T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} (Π! tyl) +:: T) (T' h++ T)
      (λ post '((al, al') -:: bl),
        tr (λ '(a -:: cl), post (a -:: cl -++ bl)) (ptrans (pzip al al'))).
  Proof.
    move=> ? Extr. eapply tctx_incl_ext.
    { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
      eapply tctx_incl_trans; by [apply tctx_split_uniq_xprod|]. }
    destruct Extr as [Htr _]=>/= ?[[??]?]. by apply Htr=>- [??].
  Qed.

  (** * Merging with [tctx_extract_elt]. *)

  Lemma tctx_extract_merge_own_prod {𝔄 𝔅 ℭl 𝔇l} n (ty: type 𝔄) (ty': type 𝔅)
      (T: tctx ℭl) (T': tctx 𝔇l) tr p E L :
    tctx_extract_ctx E L
      +[p +ₗ #0 ◁ own_ptr n ty; p +ₗ #ty.(ty_size) ◁ own_ptr n ty'] T T' tr →
    tctx_extract_elt E L (p ◁ own_ptr n (ty * ty')) T T'
      (λ post, tr (λ '(a -:: b -:: dl), post ((a, b) -:: dl))).
  Proof.
    move=> Extr. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [done|]=>/=.
      apply (tctx_incl_frame_r +[_; _] +[_]), tctx_merge_own_prod. }
    destruct Extr as [Htr _]=>/= ??. apply Htr. by case=> [?[??]].
  Qed.

  Lemma tctx_extract_merge_own_xprod {𝔄 𝔄l 𝔅l ℭl} n (tyl: typel (𝔄 :: 𝔄l))
      (T: tctx 𝔅l) (T': tctx ℭl) tr p E L :
    tctx_extract_ctx E L (hasty_own_offsets p n tyl 0) T T' tr →
    tctx_extract_elt E L (p ◁ own_ptr n (Π! tyl)) T T'
      (λ post, tr (λ acl, let '(al, cl) := psep acl in post (al -:: cl))).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [done|].
      apply (tctx_incl_frame_r _ +[_]), tctx_merge_own_xprod. }
    done.
  Qed.
End product_split.

(* We do not want unification to try to unify the definition of these
   types with anything in order to try splitting or merging. *)
Global Hint Opaque tctx_extract_elt : lrust_typing_merge.

(* We make sure that splitting is tried before borrowing, so that not
   the entire product is borrowed when only a part is needed. *)
Global Hint Resolve tctx_extract_split_own_prod tctx_extract_split_own_xprod
  tctx_extract_split_uniq_prod tctx_extract_split_uniq_xprod | 5 : lrust_typing.
(* For shared references we set the cost high,
   because a shared reference to a whole product remains after split. *)
Global Hint Resolve tctx_extract_split_shr_prod tctx_extract_split_shr_xprod
  | 100 : lrust_typing.

(* Merging is also tried after everything, except
   [tctx_extract_elt_further]. Moreover, it is placed in a
   difference hint db. The reason is that it can make the proof search
   diverge if the type is an evar.

   Unfortunately, priorities are not taken into account accross hint
   databases with [typeclasses eauto], so this is useless, and some
   solve_typing get slow because of that. See:
     https://coq.inria.fr/bugs/show_bug.cgi?id=5304
*)
Global Hint Resolve tctx_extract_merge_own_prod tctx_extract_merge_own_xprod
  | 40 : lrust_typing_merge.
