From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section choice.
  Context `{!typeG Σ}.

  Definition choice (b: bool) (P Q: iProp Σ) := if b then P else Q.

  Global Instance choice_proper :
    Proper ((=) ==> (⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) choice.
  Proof. move=> ? b->??????. by case b. Qed.
  Global Instance choice_ne n :
    Proper ((=) ==> dist n ==> dist n ==> dist n) choice.
  Proof. move=> ? b->??????. by case b. Qed.
  Global Instance choice_mono :
    Proper ((=) ==> (⊢) ==> (⊢) ==> (⊢)) choice.
  Proof. move=> ? b->??????. by case b. Qed.
  Global Instance choise_persistent b P Q:
    Persistent P → Persistent Q → Persistent (choice b P Q).
  Proof. case b; apply _. Qed.
End choice.

Notation "if@ b 'then' P 'else' Q" := (choice b P Q) (at level 200,
  right associativity, format "if@  b  'then'  P  'else'  Q") : bi_scope.

Section smallvec.
  Context `{!typeG Σ}.

  Lemma split_mt_smallvec {𝔄} (ty: type 𝔄) k l' tid d alπ Φ :
    (l' ↦∗: (λ vl,
      ∃(b: bool) (l: loc) (len ex: nat) wl (aπl: vec (proph 𝔄) len),
      ⌜vl = [ #b; #l; #len; #ex] ++ wl ∧ length wl = k ∧ alπ = lapply aπl⌝ ∗
      if@ b then (* array mode *)
        ∃(wll: vec _ _) wl', ⌜wl = concat wll ++ wl'⌝ ∗
          [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2
      else (* vector mode *) Φ l len ex aπl)) ⊣⊢
    ∃(b: bool) (l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜alπ = lapply aπl⌝ ∗ l' ↦∗ [ #b; #l; #len; #ex] ∗
      if@ b then (* array mode *)
        ([∗ list] i ↦ aπ ∈ aπl, (l' +ₗ 4 +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) ∗
        ∃wl', ⌜k = (len * ty.(ty_size) + length wl')%nat⌝ ∗ (l' +ₗ 4 +ₗ[ty] len) ↦∗ wl'
      else (* vector mode *)
        (∃wl, ⌜length wl = k⌝ ∗ (l' +ₗ 4) ↦∗ wl) ∗ Φ l len ex aπl.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". iDestruct "big" as (b ?????(->&?&?)) "big".
      iExists _, _, _, _, _. iSplit; [done|].
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
      iDestruct "↦" as "($&$&$&$& ↦)". case b=>/=; last first.
      { iFrame "big". iExists _. by iFrame. } iDestruct "big" as (??->) "tys/=".
      iDestruct (big_sepL_ty_own_length with "tys") as %<-.
      rewrite heap_mapsto_vec_app trans_big_sepL_mt_ty_own shift_loc_assoc.
      iDestruct "↦" as "[? ↦ex]". iSplitR "↦ex"; iExists _; iFrame.
      by rewrite -app_length.
    - iDestruct 1 as (b ?????) "(↦hd & big)". case b=>/=.
      + rewrite trans_big_sepL_mt_ty_own.
        iDestruct "big" as "[(%wll & ↦ar & tys) (%wl' &->& ↦ex)]".
        iDestruct (big_sepL_ty_own_length with "tys") as %Eqsz.
        iExists ([_;_;_;_]++_++_).
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_app !shift_loc_assoc -Eqsz.
        iDestruct "↦hd" as "($&$&$&$&_)". iFrame "↦ar ↦ex".
        iExists true, _, _, _, _, _. iSplit; [by rewrite -app_length|].
        iExists _, _. by iFrame.
      + iDestruct "big" as "[(%&%&↦tl) ?]". iExists ([_;_;_;_]++_).
        rewrite !heap_mapsto_vec_cons !shift_loc_assoc.
        iDestruct "↦hd" as "($&$&$&$&_)". iFrame "↦tl".
        iExists false, _, _, _, _, _=>/=. by iFrame.
  Qed.

  (* Rust's SmallVec<[T; n]> *)
  (* For simplicity, it always has the location and capacity *)
  Program Definition smallvec {𝔄} (n: nat) (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 4 + n * ty.(ty_size);
    ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own alπ d tid vl :=
      ∃(b: bool) (l: loc) (len ex: nat) wl (aπl: vec (proph 𝔄) len),
        ⌜vl = [ #b; #l; #len; #ex] ++ wl
          ∧ length wl = (n * ty.(ty_size))%nat ∧ alπ = lapply aπl⌝ ∗
        if@ b then (* array mode *)
          ∃(wll: vec _ _) wl', ⌜wl = concat wll ++ wl'⌝ ∗
            [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2
        else (* vector mode *)
          ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) ∗
          (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
          freeable_sz' ((len + ex) * ty.(ty_size)) l;
    ty_shr alπ d κ tid l' :=
      ∃(b: bool) (l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
        ⌜alπ = lapply aπl⌝ ∗
        &frac{κ} (λ q, l' ↦∗{q} [ #b; #l; #len; #ex]) ∗
        if@ b then (* array mode *)
          [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l' +ₗ 4 +ₗ[ty] i)
        else (* vector mode *)
          [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation. iDestruct 1 as (??????(->&Eq&_)) "svec/=". by rewrite Eq. Qed.
  Next Obligation.
    move=> */=. do 21 f_equiv; [f_equiv|]; apply ty_own_depth_mono; lia.
  Qed.
  Next Obligation.
    move=> */=. do 16 f_equiv; apply ty_shr_depth_mono; lia.
  Qed.
  Next Obligation.
    iIntros "%%* #? (%b &%&%&%&%&%&?& All)". iExists b, _, _, _, _.
    iSplit; [done|]. iSplit; [by iApply frac_bor_shorten|].
    case b=>/=; rewrite !big_sepL_forall;
    iIntros "**"; iApply ty_shr_lft_mono; by [|iApply "All"].
  Qed.
  Next Obligation.
    iIntros "*% #LFT In Bor κ". rewrite split_mt_smallvec.
    iMod (bor_exists with "LFT Bor") as (b) "Bor"; [done|].
    do 4 (iMod (bor_exists_tok with "LFT Bor κ") as (?) "[Bor κ]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_fracture (λ q', _ ↦∗{q'} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    case b=>/=.
    - iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
      iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
      iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
      iExists true, _, _, _, _. by iFrame.
    - iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
      iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
      iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
      iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
      iExists false, _, _, _, _. iFrame "Bor↦". by iSplit.
  Qed.
  Next Obligation.
    iIntros "*% LFT In svec κ". iDestruct "svec" as (b ?????(->&?&->)) "big". case b=>/=.
    - iDestruct "big" as (??->) "tys".
      iMod (ty_own_proph_big_sepL with "LFT In tys κ") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
      iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[? $]". iModIntro.
      iExists true, _, _, _, _, _. iSplit; [done|]. iExists _, _. by iFrame.
    - iDestruct "big" as "(↦tys & ex & †)".
      iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys κ") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
      iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
      iExists false, _, _, _, _, _. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    iIntros "%%*% LFT In In' svec κ'". iDestruct "svec" as (b ????->) "[? tys]".
    case b=>/=.
    - iMod (ty_shr_proph_big_sepL with "LFT In In' tys κ'") as "Upd"; [done|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">(%&%&%& ξl & Totys) !>". iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". by iMod ("Totys" with "ξl") as "[$$]".
    - iMod (ty_shr_proph_big_sepL with "LFT In In' tys κ'") as "Toκ'"; [done|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Toκ'").
      iIntros ">(%&%&%& ξl & Toκ') !>". iExists _, _. iSplit.
      { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
      iIntros "{$ξl}ξl". by iMod ("Toκ'" with "ξl") as "$".
  Qed.

  Global Instance smallvec_ne {𝔄} n : NonExpansive (@smallvec 𝔄 n).
  Proof. solve_ne_type. Qed.
End smallvec.
