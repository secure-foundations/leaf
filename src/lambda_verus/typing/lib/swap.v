From iris.proofmode Require Import proofmode.
From lrust.lang.lib Require Import swap.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section swap.
  Context `{!typeG Σ}.

  Definition swap {𝔄} (ty: type 𝔄) : val :=
    fn: ["ba"; "bb"] :=
      let: "a" := !"ba" in let: "b" := !"bb" in
      delete [ #1; "ba"];; delete [ #1; "bb"];;
      swap ["a"; "b"; #ty.(ty_size)];;
      let: "r" := new [ #0] in
      return: ["r"].

  (* Rust's mem::swap *)
  Lemma swap_type {𝔄} (ty: type 𝔄) :
    typed_val (swap ty) (fn<α>(∅; &uniq{α} ty, &uniq{α} ty) → ())
      (λ post '-[(a, a'); (b, b')], a' = b → b' = a → post ()).
  Proof.
    eapply type_fn; [apply _|]=> α ??[ba[bb[]]]. simpl_subst.
    iIntros (?(vπ & vπ' &[])?) "#LFT TIME PROPH #UNIQ #E Na L C /=(ba & bb &_) #?".
    rewrite !tctx_hasty_val.
    iDestruct "ba" as ([|]) "[_ box]"=>//. iDestruct "bb" as ([|]) "[_ box']"=>//.
    case ba as [[]|]=>//. case bb as [[]|]=>//=. rewrite !split_mt_uniq_bor.
    iDestruct "box" as "[[#In (%a &%&%&>[% %Eq]& >↦ba & Vo & Bor)] †ba]".
    iDestruct "box'" as "[[_ (%b &%&%&>[% %Eq']& >↦bb & Vo' & Bor')] †bb]".
    do 2 (wp_read; wp_let). rewrite -!heap_mapsto_vec_singleton !freeable_sz_full.
    wp_apply (wp_delete with "[$↦ba $†ba]"); [done|]. iIntros "_". wp_seq.
    wp_apply (wp_delete with "[$↦bb $†bb]"); [done|]. iIntros "_".
    iMod (lctx_lft_alive_tok α with "E L") as (?) "([α α₊] & L & ToL)";
      [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[big ToBor]"; [done|].
    iMod (bor_acc with "LFT Bor' α₊") as "[big' ToBor']"; [done|]. wp_seq.
    iDestruct "big" as (??) "(#⧖ & Pc &%& ↦ & ty)".
    iDestruct "big'" as (??) "(#⧖' & Pc' &%& ↦' & ty')".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iDestruct (uniq_agree with "Vo' Pc'") as %[<-<-].
    iDestruct (ty_size_eq with "ty") as %?. iDestruct (ty_size_eq with "ty'") as %?.
    wp_apply (wp_swap with "[$↦ $↦']"); [lia..|]. iIntros "[↦ ↦']". wp_seq.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod (uniq_update with "UNIQ Vo' Pc'") as "[Vo' Pc']"; [done|].
    iMod ("ToBor" with "[Pc ↦ ty']") as "[Bor α]".
    { iNext. iExists _, _. iFrame "⧖' Pc". iExists _. iFrame. }
    iMod ("ToBor'" with "[Pc' ↦' ty]") as "[Bor' α₊]".
    { iNext. iExists _, _. iFrame "⧖ Pc'". iExists _. iFrame. }
    iMod ("ToL" with "[$α $α₊] L") as "L".
    set wπ := λ π, ((vπ' π).1, (vπ π).2).
    set wπ' := λ π, ((vπ π).1, (vπ' π).2).
    iApply (type_type +[#a ◁ &uniq{α} ty; #b ◁ &uniq{α} ty] -[wπ; wπ']
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_new; [done|]. intro_subst.
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplitL "Vo Bor"; [|iSplitL; [|done]].
      + rewrite (tctx_hasty_val #_). iExists _. iFrame "⧖' In".
        iExists _, _. move: Eq.
        rewrite (proof_irrel (prval_to_inh (fst ∘ vπ))
          (prval_to_inh (fst ∘ wπ)))=> ?. by iFrame.
      + rewrite (tctx_hasty_val #_). iExists _. iFrame "⧖ In".
        iExists _, _. move: Eq'.
        rewrite (proof_irrel (prval_to_inh (fst ∘ vπ'))
          (prval_to_inh (fst ∘ wπ')))=> ?. by iFrame.
    - iApply proph_obs_impl; [|done]=>/= π. by case (vπ π), (vπ' π).
  Qed.
End swap.
