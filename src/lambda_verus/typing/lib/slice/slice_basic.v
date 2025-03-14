From lrust.typing Require Export type.
From lrust.typing Require Import typing uniq_array_util.
From lrust.typing.lib.slice Require Import slice.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section slice_basic.
  Context `{!typeG Σ}.

  (* shr_slice *)

  Global Instance shr_slice_type_contractive {𝔄} κ :
    TypeContractive (shr_slice (𝔄:=𝔄) κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| |].
    - move=> > EqSz */=. rewrite EqSz. by do 12 f_equiv.
    - move=> > EqSz */=. rewrite EqSz. do 16 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance shr_slice_send {𝔄} κ (ty: type 𝔄) : Sync ty → Send (shr_slice κ ty).
  Proof. move=> >/=. by do 12 (f_equiv || move=>?). Qed.

  Lemma shr_slice_resolve {𝔄} κ (ty: type 𝔄) E L : resolve E L (shr_slice κ ty) (const True).
  Proof. apply resolve_just. Qed.

  Lemma shr_slice_real {𝔄 𝔅} κ (ty: type 𝔄) E L (f: _ → 𝔅) :
    lctx_lft_alive E L κ → real E L ty f →
    real (𝔅:=listₛ _) E L (shr_slice κ ty) (map f).
  Proof.
    move=> ??. apply simple_type_real=>/=.
    iIntros (???[|]???) "LFT E L big"; [done|]=>/=.
    iDestruct "big" as (???[->->]) "tys".
    iMod (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
    iIntros "!>!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">((%bl & %Eq)&$& tys) !>". iSplit.
    { iPureIntro. exists bl. fun_ext=> π. move: (equal_f Eq π)=>/= <-.
      by rewrite -vec_to_list_apply vec_to_list_map. }
    iExists _, _, _. by iSplit.
  Qed.

  Lemma shr_slice_subtype {𝔄 𝔅} κ κ' ty ty' (f: 𝔄 → 𝔅) E L :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    subtype E L (shr_slice κ ty) (shr_slice κ' ty') (map f).
  Proof.
    move=> Lft Sub. apply subtype_simple_type=>/=. iIntros (?) "L".
    iDestruct (Lft with "L") as "#Lft". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Lft" with "E") as "#?".
    iDestruct ("Sub" with "E") as "#(%&?&_& #?)". iSplit; [done|].
    iSplit; [by iApply lft_intersect_mono|]. iIntros (?[|]??) "big /="; [done|].
    iDestruct "big" as (?? aπl[->->]) "tys". iExists _, _, _.
    have ?: ∀(aπl: vec (proph 𝔄) _), map f ∘ lapply aπl = lapply (vmap (f ∘.) aπl).
    { move=> ?. elim; [done|]=> ??? IH. fun_ext=>/= ?. f_equal. apply (equal_f IH). }
    iSplit; [done|]. iApply incl_big_sepL_ty_shr; [done..|].
    by iApply big_sepL_ty_shr_lft_mono.
  Qed.
  Lemma shr_slice_eqtype {𝔄 𝔅} κ κ' ty ty' (f: 𝔄 → 𝔅) g E L :
    lctx_lft_eq E L κ' κ → eqtype E L ty ty' f g →
    eqtype E L (shr_slice κ ty) (shr_slice κ' ty') (map f) (map g).
  Proof. move=> [??][??]. split; (apply shr_slice_subtype; by [|split]). Qed.

  (* uniq_slice *)

  Global Instance uniq_slice_type_contractive {𝔄} κ :
    TypeContractive (uniq_slice (𝔄:=𝔄) κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| |].
    - move=> > EqSz EqLft */=. f_equiv.
      + apply equiv_dist. iDestruct EqLft as "#[??]".
        iSplit; iIntros "#In"; (iApply lft_incl_trans; [iApply "In"|done]).
      + rewrite EqSz /uniq_body. do 23 (f_contractive || f_equiv). by simpl in *.
    - move=> > EqSz */=. rewrite EqSz. do 17 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance uniq_slice_send {𝔄} κ (ty: type 𝔄) : Send ty → Send (uniq_slice κ ty).
  Proof. move=> >/=. rewrite /uniq_body. by do 24 f_equiv. Qed.

  Global Instance uniq_slice_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (uniq_slice κ ty).
  Proof. move=> >/=. by do 17 (f_equiv || move=>?). Qed.

  Lemma uniq_slice_resolve {𝔄} κ (ty: type 𝔄) E L :
    lctx_lft_alive E L κ →
    resolve E L (uniq_slice κ ty) (λ pl, lforall (λ '(a, a'), a' = a) pl).
  Proof.
    iIntros "%* LFT PROPH E L (In &%&%&%& %aπξil &(->&->&%)& uniqs)".
    iMod (resolve_big_sepL_uniq_body with "LFT PROPH In E L uniqs") as "Upd"; [done..|].
    iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
    iIntros "!> >[? $]". iApply proph_obs_impl; [|done]=>/= ?.
    elim aπξil; [done|]. move=> [??]/=?? IH [??]. split; by [|apply IH].
  Qed.

  Lemma uniq_slice_real {𝔄 𝔅} κ (ty: type 𝔄) E L (f: _ → 𝔅) :
    lctx_lft_alive E L κ → real E L ty f →
    real (𝔅:=listₛ _) E L (uniq_slice κ ty) (map (f ∘ fst)).
  Proof.
    move=> ??. split.
    - iIntros "*% LFT E L ($&%&%&%& %aπξil &(->&->&%)& uniqs)".
      iMod (real_big_sepL_uniq_body with "LFT E L uniqs") as "Upd"; [done..|].
      iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
      iIntros "!> >([%bl %Eq] &$& uniqs) !>". iSplit.
      { iPureIntro. exists (bl: list _). fun_ext=> π. move: (equal_f Eq π)=>/= <-.
        clear. elim aπξil; [done|]. by move=> [??]/=??->. }
      iExists _, _, _, _. by iFrame.
    - iIntros (??? d) "*% LFT E L big". case d; [done|]=> ?.
      iDestruct "big" as (?? aπl ? [Eq ?]) "(Bor↦ & Borξl & tys)". iIntros "!>!>!>".
      iDestruct (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand _ _ (S _) with "Upd").
      iIntros ">([%bl %Eq'] &$& tys) !>". iSplit.
      { iPureIntro. exists (bl: list _). fun_ext=>/= π. rewrite -map_map.
        move: (equal_f Eq π) (equal_f Eq' π)=>/= -><-. by elim aπl=>//= ???->. }
      iExists _, _, _, _. by iFrame.
  Qed.

  Lemma uniq_slice_subtype {𝔄} κ κ' (ty ty': type 𝔄) E L :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    subtype E L (uniq_slice κ ty) (uniq_slice κ' ty') id.
  Proof.
    move=> In /eqtype_id_unfold Eqt ?. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In". iIntros "!> #E".
    iSplit; [done|]. iDestruct ("Eqt" with "E") as (EqSz) "[[??][#EqOwn #EqShr]]".
    iSpecialize ("In" with "E"). iSplit; [by iApply lft_intersect_mono|].
    iSplit; iModIntro=>/=.
    - iIntros "* (#?&%&%&%&%&(->&->&%)& uniqs)". iSplitR.
      { iApply lft_incl_trans; [|done]. by iApply lft_incl_trans. }
      iExists _, _, _, _. iSplit; [done|]. rewrite -EqSz.
      iApply (incl_big_sepL_uniq_body with "In EqOwn uniqs").
    - iIntros (?[|?]???); [by iIntros|]. iDestruct 1 as (?????) "(?&?& tys)".
      iExists _, _, _, _. do 3 (iSplit; [done|]). iNext.
      rewrite !(big_sepL_forall (λ _ (_: proph _), _)) -EqSz. iIntros (???).
      iApply "EqShr". by iApply "tys".
  Qed.
  Lemma uniq_slice_eqtype {𝔄} κ κ' (ty ty': type 𝔄) E L :
    lctx_lft_eq E L κ' κ → eqtype E L ty ty' id id →
    eqtype E L (uniq_slice κ ty) (uniq_slice κ' ty') id id.
  Proof. move=> [??][??]. split; (apply uniq_slice_subtype; by [|split]). Qed.

  (* methods *)

  Definition slice_len: val :=
    fn: ["s"] :=
      let: "l" := !("s" +ₗ #1) in delete [ #2; "s"];;
      letalloc: "r" <- "l" in return: ["r"].

  (* Rust's [T]::len *)
  Lemma shr_slice_len_type {𝔄} (ty: type 𝔄) :
    typed_val slice_len (fn<α>(∅; shr_slice α ty) → int)
      (λ post '-[al], post (length al)).
  Proof.
    eapply type_fn; [apply _|]. move=>/= α ??[b[]]. simpl_subst.
    iIntros (?[?[]]?) "LFT TIME PROPH UNIQ E Na L C /=[bs _] #Obs".
    rewrite tctx_hasty_val. iDestruct "bs" as ([|d]) "[#⧖ box]"=>//.
    case b as [[]|]=>//=. iDestruct "box" as "[sl †]". rewrite split_mt_shr_slice.
    case d as [|d]; first by iDestruct "sl" as ">[]". wp_op.
    iDestruct "sl" as (? n ?->) "(↦ & ↦' &_)". wp_read. wp_let.
    rewrite freeable_sz_full. wp_apply (wp_delete [_;_] with "[$† ↦ ↦']"); [done| |].
    { rewrite heap_mapsto_vec_cons heap_mapsto_vec_singleton. iFrame. }
    iIntros "_". wp_seq.
    iApply (type_type +[#n ◁ int] -[const (n: Zₛ)]
      with "[] LFT TIME PROPH UNIQ E Na L C [] []").
    - iApply type_letalloc_1; [solve_extract|done|]. intro_subst.
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplit; [|done]. rewrite (tctx_hasty_val #n)/=. iExists _.
      iFrame "⧖". by iExists n.
    - iApply proph_obs_eq; [|done]=>/= π. f_equal.
      by rewrite -vec_to_list_apply vec_to_list_length.
  Qed.
End slice_basic.

Global Hint Resolve shr_slice_resolve shr_slice_real shr_slice_subtype shr_slice_eqtype
  uniq_slice_resolve uniq_slice_real uniq_slice_subtype uniq_slice_eqtype : lrust_typing.
