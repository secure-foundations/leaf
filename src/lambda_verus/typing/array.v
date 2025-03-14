From lrust.typing Require Export type.
From lrust.typing Require Import array_util product.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Section array.
  Context `{!typeG Σ}.

  Lemma split_mt_array {𝔄 n} (ty: type 𝔄) l (aπl: _ n) d tid :
    (l ↦∗: λ vl, ∃wll: vec _ _, ⌜vl = concat wll⌝ ∗
      [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2) ⊣⊢
    [∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid.
  Proof.
    rewrite trans_big_sepL_mt_ty_own. iSplit.
    - iIntros "(%&?&%&->&?)". iExists _. iFrame.
    - iIntros "(%& ↦ &?)". iExists _. iFrame "↦". iExists _. by iFrame.
  Qed.

  Program Definition array {𝔄} n (ty: type 𝔄) : type (vecₛ 𝔄 n) := {|
    ty_size := n * ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl := ∃wll: vec _ _, ⌜vl = concat wll⌝ ∗
      [∗ list] aπwl ∈ vzip (vfunsep vπ) wll, ty.(ty_own) aπwl.1 d tid aπwl.2;
    ty_shr vπ d κ tid l :=
      [∗ list] i ↦ aπ ∈ vfunsep vπ, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation.
    iIntros "* (%&->& tys)". by iApply (big_sepL_ty_own_length with "tys").
  Qed.
  Next Obligation. move=>/= *. do 6 f_equiv. by apply ty_own_depth_mono. Qed.
  Next Obligation. move=>/= *. do 3 f_equiv. by apply ty_shr_depth_mono. Qed.
  Next Obligation.
    iIntros "* #In". rewrite !big_sepL_forall. iIntros "All" (???).
    iApply (ty_shr_lft_mono with "In"). by iApply "All".
  Qed.
  Next Obligation.
    iIntros "*% LFT In Bor κ". rewrite split_mt_array.
    iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). by iIntros "!> >[$$]".
  Qed.
  Next Obligation.
    iIntros (????????? q ?) "#LFT #In (%&->& tys) κ".
    iMod (ty_own_proph_big_sepL with "LFT In tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). rewrite vapply_funsep.
    iIntros "!> >(%&%&%& ξl & Totys) !>". iExists _, _. iSplit; [done|].
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[? $]". iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros "*% LFT In In' tys κ'". rewrite -{2}[vπ]vapply_funsep.
    iMod (ty_shr_proph_big_sepL with "LFT In In' tys κ'") as "Upd"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%&%&%& ξl & Totys) !>". iExists _, _. iSplit; [done|].
    iIntros "{$ξl}ξl". by iMod ("Totys" with "ξl") as "[$$]".
  Qed.

  Global Instance array_ne {𝔄} n : NonExpansive (@array 𝔄 n).
  Proof. solve_ne_type. Qed.
End array.

(* The notation in Rust is [ty; n], but it conflicts with lists in Coq *)
Notation "[ ty ;^ n ]" := (array n ty) (format "[ ty ;^  n ]") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance array_type_ne {𝔄} n : TypeNonExpansive (@array _ _ 𝔄 n).
  Proof.
    split; [by apply type_lft_morphism_id_like|by move=>/= ??->| | ]=>/= > Sz *;
    [by do 6 f_equiv|rewrite Sz; by do 3 f_equiv].
  Qed.

  Global Instance array_copy {𝔄} n (ty: type 𝔄) : Copy ty → Copy [ty;^ n].
  Proof.
    split; [apply _|]=>/= vπ ???? F l q ? HF. iIntros "#LFT tys Na κ".
    move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl.
    iInduction aπl as [|] "IH" forall (q l F HF)=>/=.
    { iModIntro. iExists 1%Qp, []. rewrite difference_empty_L heap_mapsto_vec_nil.
      iFrame "Na κ". iSplitR; [by iExists [#]=>/=|]. by iIntros. }
    rewrite shift_loc_0. iDestruct "tys" as "[ty tys]". iDestruct "κ" as "[κ κ₊]".
    iMod (copy_shr_acc with "LFT ty Na κ") as (q' ?) "(Na & ↦ & #ty & Toκ)";
    [done| |]. { rewrite <-HF. apply shr_locsE_subseteq=>/=. lia. }
    setoid_rewrite <-shift_loc_assoc_nat.
    iMod ("IH" with "[%] tys Na κ₊") as (q'' ?) "(Na & ↦' & (%&>->& #tys) & Toκ₊)".
    { apply subseteq_difference_r. { symmetry. apply shr_locsE_disj. }
      move: HF. rewrite -plus_assoc shr_locsE_shift. set_solver. }
    case (Qp_lower_bound q' q'')=> [q'''[?[?[->->]]]]. iExists q''', (_ ++ _).
    rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "ty") as ">->".
    iDestruct "↦" as "[$ ↦r]". iDestruct "↦'" as "[$ ↦r']".
    iDestruct (na_own_acc with "Na") as "[$ ToNa]".
    { rewrite shr_locsE_shift. set_solver. }
    iSplitR.
    - iIntros "!>!>". iExists (_:::_)=>/=. iSplit; by [|iSplit].
    - iIntros "!> Na [↦ ↦']". iDestruct ("ToNa" with "Na") as "Na".
      iMod ("Toκ₊" with "Na [$↦' $↦r']") as "[Na $]". iApply ("Toκ" with "Na"). iFrame.
  Qed.

  Global Instance array_send {𝔄} n (ty: type 𝔄) : Send ty → Send [ty;^ n].
  Proof. move=> >/=. by do 6 f_equiv. Qed.
  Global Instance array_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync [ty;^ n].
  Proof. move=> >/=. by do 3 f_equiv. Qed.

  Lemma array_resolve {𝔄} (ty: type 𝔄) n Φ E L :
    resolve E L ty Φ → resolve E L [ty;^ n] (λ al, lforall Φ al).
  Proof.
    iIntros "% * LFT PROPH E L (%&->& tys)".
    iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys"); [done..|].
    by rewrite -vec_to_list_apply vapply_funsep.
  Qed.

  Lemma array_resolve_just {𝔄} (ty: type 𝔄) n E L :
    resolve E L ty (const True) → resolve E L [ty;^ n] (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma array_real {𝔄 𝔅} (ty: type 𝔄) n (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=vecₛ _ _) E L [ty;^ n] (vmap f).
  Proof.
    move=> Rl. split.
    - iIntros "*% LFT E L (%&->& tys)".
      iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). rewrite vapply_funsep.
      iIntros "!> >($&$&?) !>". iExists _. by iFrame.
    - iIntros "*% LFT E L tys".
      iMod (real_big_sepL_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      rewrite vapply_funsep. by iIntros ">($&$&$) !>".
  Qed.

  Lemma array_subtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L [ty;^ n] [ty';^ n] (vmap f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "(%Sz &?&#?&#?)".
    iSplit; [by rewrite/= Sz|]. iSplit; [done|].
    have Eq: ∀vπ, vfunsep (vmap f ∘ vπ) = vmap (f ∘.) (vfunsep vπ).
    { move=> ?? vπ. rewrite -{1}[vπ]vapply_funsep.
      move: {vπ}(vfunsep vπ)=> aπl. by elim aπl; [done|]=>/= ???<-. }
    iSplit; iIntros "!> */="; rewrite Eq.
    - iIntros "(%&->&?)". iExists _. iSplit; [done|]. by iApply incl_big_sepL_ty_own.
    - iIntros "?". by iApply incl_big_sepL_ty_shr.
  Qed.
  Lemma array_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' n E L :
    eqtype E L ty ty' f g → eqtype E L [ty;^ n] [ty';^ n] (vmap f) (vmap g).
  Proof. move=> [??]. split; by apply array_subtype. Qed.

  Lemma array_one {𝔄} (ty: type 𝔄) E L : eqtype E L [ty;^ 1] ty vhd (λ x, [#x]).
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "% _!>_".
    iSplit; [by rewrite/= Nat.add_0_r|]. iSplit; [iApply lft_equiv_refl|].
    have Eq: ∀vπ, vhd ∘ vπ = vhd (vfunsep vπ). { move=> ??? vπ.
    rewrite -{1}[vπ]vapply_funsep. move: (vfunsep vπ)=> aπl. by inv_vec aπl. }
    iSplit; iIntros "!> %vπ */="; rewrite Eq;
    move: {vπ}(vfunsep (A:=𝔄) vπ)=> aπl; inv_vec aπl=> ?; [iSplit|].
    - iIntros "(%wll &->&?)". inv_vec wll=>/= ?. by do 2 rewrite right_id.
    - iIntros "?". iExists [# _]=>/=. do 2 rewrite right_id. by iSplit.
    - rewrite right_id shift_loc_0. by iApply bi.equiv_iff.
  Qed.

  Lemma array_plus_prod {𝔄} m n (ty: type 𝔄) E L :
    eqtype E L [ty;^ m + n] ([ty;^ m] * [ty;^ n]) (vsepat m) (uncurry vapp).
  Proof.
    apply eqtype_symm, eqtype_unfold; [apply _|]. iIntros (?) "_!>_".
    iSplit; [iPureIntro=>/=; lia|]. iSplit.
    { rewrite/= lft_intersect_list_app. iApply lft_intersect_equiv_idemp. }
    have Eq: ∀vπ: proph (vec 𝔄 _ * _), vfunsep (uncurry vapp ∘ vπ) =
      vfunsep (fst ∘ vπ) +++ vfunsep (snd ∘ vπ).
    { move=> ?? vπ. have {1}<-: pair ∘ vapply (vfunsep $ fst ∘ vπ) ⊛
      vapply (vfunsep $ snd ∘ vπ) = vπ by rewrite !semi_iso' -surjective_pairing_fun.
      move: (_ $ fst ∘ _)=> aπl. by elim aπl; [by rewrite semi_iso'|]=>/= ???<-. }
    iSplit; iIntros "!> %vπ %/="; rewrite Eq; move: (vfunsep (fst ∘ vπ))=> aπl;
    move: {vπ}(vfunsep (snd ∘ vπ))=> bπl; iIntros "*"; [iSplit|].
    - iIntros "(%&%&->&(%&->&?)&(%&->&?))". iExists (_+++_).
      rewrite vzip_with_app !vec_to_list_app concat_app. by iFrame.
    - iIntros "(%wll &->& tys)". move: (vapp_ex wll)=> [?[?->]].
      rewrite vzip_with_app !vec_to_list_app concat_app. iExists _, _. iSplit; [done|].
      iDestruct "tys" as "[tys tys']". iSplitL "tys"; iExists _; by iFrame.
    - iApply bi.equiv_iff.
      rewrite vec_to_list_app big_sepL_app vec_to_list_length. do 5 f_equiv.
      by rewrite shift_loc_assoc_nat -Nat.mul_add_distr_r.
  Qed.

  Lemma array_succ_prod {𝔄} n (ty: type 𝔄) E L :
    eqtype E L [ty;^ S n] (ty * [ty;^ n]) (λ v, (vhd v, vtl v)) (uncurry (λ x, vcons x)).
  Proof.
    eapply eqtype_eq.
    - eapply eqtype_trans; [apply (array_plus_prod 1)|].
      apply prod_eqtype; [apply array_one|solve_typing].
    - done.
    - fun_ext. by case.
  Qed.
End typing.

Global Hint Resolve array_resolve | 5 : lrust_typing.
Global Hint Resolve array_resolve_just array_real array_subtype array_eqtype
  : lrust_typing.
