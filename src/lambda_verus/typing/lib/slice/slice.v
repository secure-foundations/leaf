From lrust.typing Require Export type.
From lrust.typing Require Import typing uniq_array_util.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section slice.
  Context `{!typeG Σ}.

  Lemma split_mt_shr_slice {A} d φ Φ l' q :
    (l' ↦∗{q}: (λ vl, [S(d') := d] ∃(l: loc) (n: nat) (aπl: A n),
      ⌜vl = [ #l; #n] ∧ φ n aπl⌝ ∗ Φ d' l n aπl)) ⊣⊢
    [S(d') := d] ∃(l: loc) (n: nat) (aπl: A n),
      ⌜φ n aπl⌝ ∗ l' ↦{q} #l ∗ (l' +ₗ 1) ↦{q} #n ∗ Φ d' l n aπl.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". case d; [done|]=>/= ?.
      iDestruct "big" as (???[->?]) "?". iExists _, _, _.
      rewrite !heap_mapsto_vec_cons. iDestruct "↦" as "($&$&_)". by iFrame.
    - iIntros "big". case d; [done|]=>/= ?.
      iDestruct "big" as (????) "(↦ & ↦' & ?)". iExists [_;_].
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil. iFrame "↦ ↦'".
      iExists _, _, _. by iFrame.
  Qed.

  Lemma split_mt_shr_slice' {A} φ Φ l' q :
    (l' ↦∗{q}: (λ vl, ∃(l: loc) (n: nat) (aπl: A n),
      ⌜vl = [ #l; #n] ∧ φ n aπl⌝ ∗ Φ l n aπl)) ⊣⊢
    ∃(l: loc) (n: nat) (aπl: A n),
      ⌜φ n aπl⌝ ∗ l' ↦{q} #l ∗ (l' +ₗ 1) ↦{q} #n ∗ Φ l n aπl.
  Proof.
    set Φ' := λ _: nat, Φ. have ->: Φ = Φ' 0%nat by done.
    by apply (split_mt_shr_slice (S _)).
  Qed.

  (* Rust's &'a [T] *)
  Program Definition shr_slice {𝔄} (κ: lft) (ty: type 𝔄) : type (listₛ 𝔄) := {|
    st_size := 2;  st_lfts := κ :: ty.(ty_lfts);  st_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    st_own (alπ: proph (listₛ 𝔄)) d tid vl := [S(d') := d]
      ∃(l: loc) (n: nat) (aπl: vec (proph 𝔄) n),
        ⌜vl = [ #l; #n] ∧ alπ = lapply aπl⌝ ∗
        [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation.
    iIntros (????[|]??) "big"; [done|]. by iDestruct "big" as (???[->_]) "_".
  Qed.
  Next Obligation.
    move=> ???[|?][|?]*/=; try (by iIntros); [lia|]=>/=. do 10 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*/=; [by iIntros|].
    iIntros "#LFT #? (%&%&%&[->->]& #tys) κ' !>/=".
    iDestruct (ty_shr_proph_big_sepL with "LFT [] [] tys κ'") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iApply (step_fupdN_wand with "Upd"). iNext. iMod 1 as (ξl q ?) "[ξl Upd]".
    iModIntro. iExists ξl, q. iSplit.
    { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("Upd" with "ξl") as "$". iModIntro.
    iExists _, _, _. by iSplit.
  Qed.

  Global Instance shr_slice_ne {𝔄} κ : NonExpansive (@shr_slice 𝔄 κ).
  Proof. rewrite /shr_slice. solve_ne_type. Qed.

  Lemma split_mt_uniq_slice {A} P Ψ Φ l' q :
    (l' ↦∗{q}: (λ vl, P ∗
      ∃(l: loc) (n d': nat) (aπξil: A n),
        ⌜vl = [ #l; #n] ∧ Ψ n aπξil d'⌝ ∗ Φ l n d' aπξil)) ⊣⊢
    P ∗ ∃(l: loc) (n d': nat) aπξil,
      ⌜Ψ n aπξil d'⌝ ∗ l' ↦{q} #l ∗ (l' +ₗ 1) ↦{q} #n ∗ Φ l n d' aπξil.
  Proof.
    iSplit.
    - iIntros "(%& ↦ &$&%&%&%&%&[->%]& Φ)". iExists _, _, _, _. iSplit; [done|].
      iFrame "Φ". rewrite !heap_mapsto_vec_cons. iDestruct "↦" as "($&$&_)".
    - iIntros "($&%&%&%&%&%& ↦ & ↦' & Φ)". iExists [_;_].
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil. iFrame "↦ ↦'".
      iExists _, _, _, _. by iFrame.
  Qed.

  (* Rust's &'a mut [T] *)
  Program Definition uniq_slice {𝔄} (κ: lft) (ty: type 𝔄) : type (listₛ (𝔄 * 𝔄)) := {|
    ty_size := 2;  ty_lfts := κ :: ty.(ty_lfts);  ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    ty_own vπ d tid vl := κ ⊑ ty_lft ty ∗
      ∃(l: loc) (n d': nat) (aπξil: vec (proph 𝔄 * positive) n),
        let aaπl := vmap
          (λ aπξi π, (aπξi.1 π, π (PrVar (𝔄 ↾ prval_to_inh aπξi.1) aπξi.2): 𝔄)) aπξil in
        ⌜vl = [ #l; #n] ∧ vπ = lapply aaπl ∧ (S d' ≤ d)%nat⌝ ∗
        [∗ list] i ↦ aπξi ∈ aπξil, uniq_body ty aπξi.1 aπξi.2 d' κ tid (l +ₗ[ty] i);
    ty_shr vπ d κ' tid l' := [S(d') := d]
      ∃(l: loc) (n: nat) (aπl: vec (proph 𝔄) n) ξl,
        ⌜map fst ∘ vπ = lapply aπl ∧ map snd ∘ vπ ./ ξl⌝ ∗
        &frac{κ'} (λ q, l' ↦{q} #l ∗ (l' +ₗ 1) ↦{q} #n) ∗ &frac{κ'} (λ q, q:+[ξl]) ∗
        ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ' tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation. by iIntros "* (_&%&%&%&%&[->?]&_)". Qed.
  Next Obligation. move=>/= *. by do 14 f_equiv. Qed.
  Next Obligation.
    move=> ???[|?][|?]*/=; try (by iIntros); [lia|]. do 15 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??????[|?]*; [by iIntros|]. iIntros "#? (%&%&%&%&%&#?&#?& #All)".
    iExists _, _, _, _. iSplit; [done|].
    do 2 (iSplitL; [by iApply frac_bor_shorten|]). iNext. rewrite !big_sepL_forall.
    iIntros (???). iApply ty_shr_lft_mono; [done|]. by iApply "All".
  Qed.
  Next Obligation.
    iIntros (????? d) "*% #LFT #In Bor κ'". rewrite split_mt_uniq_slice.
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    do 3 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_exists_tok with "LFT Bor κ'") as (aπξil) "[Bor κ']"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ'") as "(>[->%] & Bor & κ')"; [done|].
    rewrite assoc. iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_fracture (λ q, _ ↦{q} _ ∗ _ ↦{q} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (ty_share_big_sepL_uniq_body with "LFT [] [] Bor κ'") as "Upd"; [done|..].
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
    iIntros "!> >(Borξl & tys &$)". set ξl := vmap _ _.
    iMod (bor_fracture (λ q, q:+[_])%I with "LFT Borξl") as "Borξl"; [done|].
    iModIntro. case d as [|]; [lia|]. iExists _, _, _, _. iFrame "Bor↦ Borξl".
    iSplit; last first.
    { iClear "#". iNext. iStopProof. do 3 f_equiv; [|done].
      iApply ty_shr_depth_mono. lia. }
    iPureIntro. split.
    - fun_ext=>/= ?. by elim aπξil; [done|]=>/= ???->.
    - rewrite /ξl. elim aπξil; [done|]=>/= ????.
      apply (proph_dep_constr2 _ _ _ [_]); [|done]. apply proph_dep_one.
  Qed.
  Next Obligation.
    iIntros "*% LFT #? (#? & %&%&%& %aπξil &(->&->&%)& uniqs) κ'".
    iMod (ty_own_proph_big_sepL_uniq_body with "LFT [] [] uniqs κ'") as "Upd"; [done|..].
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
    iIntros "!> >(%&%& %Dep & ζξl & Touniqs) !>". iExists _, _. iFrame "ζξl". iSplit.
    { iPureIntro. apply proph_dep_list_prod.
      - apply (proph_dep_constr vec_to_list) in Dep. eapply proph_dep_eq; [done|].
        fun_ext=>/= ?. by elim aπξil; [done|]=>/= ???->.
      - elim aπξil; [done|]=>/= ????.
        apply (proph_dep_constr2 _ _ _ [_]); [|done]. apply proph_dep_one. }
    iIntros "ζξl". iMod ("Touniqs" with "ζξl") as "[uniqs $]". iModIntro.
    iSplit; [done|]. iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????? d) "*% #LFT #In #In' big [κ' κ'₊]". case d; [done|]=> ?.
    iDestruct "big" as (????[Eq ?]) "(Bor↦ & #Borξl & tys)". iIntros "!>!>!>/=".
    iMod (ty_shr_proph_big_sepL with "LFT In [] tys κ'") as "Upd"; [done|..].
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iMod (lft_incl_acc with "In κ'₊") as (?) "[κ0 Toκ'₊]"; [done|].
    iMod (frac_bor_acc with "LFT Borξl κ0") as (?) "[>ξl Toκ0]"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%&%&%& ζl & Toshr) !>".
    iDestruct (proph_tok_combine with "ζl ξl") as (?) "[ζξl Toζξl]".
    iExists _, _. iFrame "ζξl". iSplit.
    { iPureIntro. apply proph_dep_list_prod; [|done]. rewrite Eq.
      rewrite -vec_to_list_apply. by apply proph_dep_constr. }
    iIntros "ζξl". iDestruct ("Toζξl" with "ζξl") as "[ζl ξl]".
    iMod ("Toshr" with "ζl") as "$". iMod ("Toκ0" with "ξl") as "κ0".
    by iMod ("Toκ'₊" with "κ0") as "$".
  Qed.

  Global Instance uniq_slice_ne {𝔄} κ : NonExpansive (@uniq_slice 𝔄 κ).
  Proof. rewrite /uniq_slice /uniq_body. solve_ne_type. Qed.
End slice.
