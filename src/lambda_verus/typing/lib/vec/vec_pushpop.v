From lrust.typing Require Export type.
From lrust.typing Require Import array_util uniq_util typing.
From lrust.typing.lib Require Import option vec_util vec.vec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec_pushpop.
  Context `{!typeG Σ}.

  Definition vec_push {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"; "x"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      vec_push_core ty ["v'"; "x"];; delete [ #ty.(ty_size); "x"];;
      let: "r" := new [ #0] in return: ["r"].

  (* Rust's Vec::push *)
  Lemma vec_push_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_push ty) (fn<α>(∅; &uniq{α} (vec_ty ty), ty) → ())
      (λ post '-[(al, al'); a], al' = al ++ [a] → post ()).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[x[]]]. simpl_subst.
    iIntros (?(vπ & bπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(v & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "v" as ([|dv]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦v & [#LftIn uniq]) †v]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//=.
    iDestruct "x" as "[↦ty †x]". rewrite heap_mapsto_vec_singleton. wp_read.
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦vec) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_vec. case du as [|du]=>//=.
    iDestruct "↦vec" as (??? aπl Eq1) "(↦l & ↦tys & ↦ex & †)".
    wp_bind (delete _). rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_persistent_time_receipt with "TIME ⧖x"); [done|].
    iApply (wp_delete with "[$↦v $†v]"); [done|]. iIntros "!>_ ⧖x".
    iCombine "⧖u ⧖x" as "#⧖". wp_seq.
    wp_apply (wp_vec_push_core with "[↦l ↦tys ↦ex † ↦ty]"). { iExists _, _. iFrame. }
    iIntros "(%&%& ↦ & ↦tys & ↦ex & † & (%& %Len & ↦x))". wp_seq.
    rewrite freeable_sz_full. wp_apply (wp_delete with "[$↦x †x]"); [lia|by rewrite Len|].
    iIntros "_". wp_seq. set vπ' := λ π, (lapply (vsnoc aπl bπ) π, π ξ).
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[↦ ↦tys ↦ex † Pc]") as "[Bor α]".
    { iNext. iExists _, _. rewrite split_mt_vec. iFrame "⧖ Pc".
      iExists _, _, _, (vsnoc _ _). by iFrame. }
    iMod ("ToL" with "α L") as "L".
    iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty)] -[vπ']
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_new; [done|]. intro_subst.
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= right_id (tctx_hasty_val #_). iExists _.
      iFrame "⧖ LftIn". iExists _, _. rewrite /uniq_body.
      rewrite (proof_irrel (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ'))
        (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ))). by iFrame.
    - iApply proph_obs_impl; [|done]=> π.
      move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (vπ π)=>/= ??->-> Imp Eq.
      apply Imp. move: Eq. by rewrite vec_to_list_snoc lapply_app.
  Qed.

  Definition vec_pop {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      let: "len" := !("v'" +ₗ #1) in
      if: "len" ≤ #0 then
        let: "r" := new [ #(option_ty ty).(ty_size)] in "r" <-{Σ 0} ();;
        return: ["r"]
      else
        let: "len'" := "len" - #1 in
        "v'" +ₗ #1 <- "len'";; "v'" +ₗ #2 <- !("v'" +ₗ #2) + #1;;
        let: "r" := new [ #(option_ty ty).(ty_size)] in
        "r" <- #1;; "r" +ₗ #1 <-{ty.(ty_size)} ! (!"v'" +ₗ "len'" * #ty.(ty_size));;
        return: ["r"].

  (* Rust's Vec::pop *)
  Lemma vec_pop_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_pop ty) (fn<α>(∅; &uniq{α} (vec_ty ty)) → option_ty ty)
      (λ post '-[(al, al')], al' = removelast al → post (last_error al)).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[v _] #Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦ & [#LftIn uniq]) †]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_delete with "[$↦ $†]"); [done|]. iIntros "!>_".
    iDestruct "uniq" as (d ξi [? Eq2]) "[Vo Bor]". move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& #⧖ & Pc & ↦vec) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_vec. case d=>// ?.
    iDestruct "↦vec" as (? len ex aπl Eq1) "(↦ & ↦tys & (%wl &%& ↦ex) & †)".
    rewrite !heap_mapsto_vec_cons shift_loc_assoc. iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ &_)".
    wp_op. wp_read. wp_let. wp_op. wp_case. case len as [|].
    { iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦tys ↦ex † ⧖ Pc]") as "[Bor β]".
      { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_vec. iExists _, _, _, _.
        rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil shift_loc_assoc.
        iFrame "↦₀ ↦₁ ↦₂ ↦tys †". iSplit; [done|]. iExists _. by iFrame. }
      iMod ("ToL" with "β L") as "L".
      iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty)] -[vπ]
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst. rewrite Nat2Z.id.
        iApply (type_sum_unit +[(); ty]%T 0%fin); [done|solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= !(tctx_hasty_val #_). iSplitL; [|done]. iExists _.
        iFrame "⧖ LftIn". iExists _, _. iFrame. iPureIntro. split; [lia|done].
      - iApply proph_obs_impl; [|done]=> π. move: (equal_f Eq1 π)=>/=. clear.
        inv_vec aπl. by case (vπ π)=>/= ??->. }
    iDestruct (big_sepL_vinitlast with "↦tys") as "[↦tys (%vl & ↦last & ty)]"=>/=.
    set vπ' := λ π, (lapply (vinit aπl) π, π ξ).
    wp_op. wp_let. wp_op. wp_write. do 2 wp_op. wp_read. wp_op. wp_write.
    wp_apply wp_new; [lia|done|]. iIntros (r) "[†r ↦r]". wp_let.
    rewrite Nat2Z.id /= heap_mapsto_vec_cons. have ->: (S len - 1)%Z = len by lia.
    iDestruct "↦r" as "[↦r ↦r']". iDestruct (ty_size_eq with "ty") as %Eqvl.
    wp_write. wp_op. wp_read. do 2 wp_op. rewrite -Nat2Z.inj_mul.
    wp_apply (wp_memcpy with "[$↦r' $↦last]"); [rewrite repeat_length; lia|lia|].
    iIntros "[↦r' ↦last]". wp_seq.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦tys ↦last ↦ex † ⧖ Pc]") as "(Bor & α)".
    { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_vec.
      have ->: ∀sz, sz + (len + ex) * sz = (len + S ex) * sz by lia.
      have ->: (ex + 1)%Z = S ex by lia. iExists _, _, _, _.
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil shift_loc_assoc.
      iFrame "↦₀ ↦₁ ↦₂ ↦tys †". iSplit; [done|]. iExists (vl ++ wl).
      rewrite app_length heap_mapsto_vec_app shift_loc_assoc_nat plus_comm Eqvl.
      iSplit; [iPureIntro; lia|]. iFrame. }
    iMod ("ToL" with "α L") as "L".
    iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty); #r ◁ box (option_ty ty)]
      -[vπ'; Some ∘ _] with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_) right_id. iSplitL "Vo Bor".
      + iExists _. iFrame "⧖ LftIn". iExists _, _. rewrite /uniq_body.
        rewrite (proof_irrel (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ'))
          (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ))). by iFrame.
      + iExists _. rewrite -freeable_sz_full. iFrame "⧖ †r". iNext.
        rewrite /option_ty. setoid_rewrite mod_ty_own; [|apply _].
        rewrite split_mt_sum. iExists 1%fin, _. iSplit; [done|]. iFrame "↦r". iSplitR.
        { iExists []. rewrite heap_mapsto_vec_nil left_id. iPureIntro=>/=.
          move: ty.(ty_size)=> ?. lia. }
        iExists _. iFrame "↦r'". iApply ty_own_depth_mono; [|done]. lia.
    - iApply proph_obs_impl; [|done]=>/= π.
      move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. clear. case (vπ π)=>/= ??->->.
      have ->: last_error (lapply aπl π) = Some (vlast aπl π).
      { inv_vec aπl=> + aπl'. by elim aπl'=>/= *. }
      have ->: removelast (lapply aπl π) = lapply (vinit aπl) π.
      { inv_vec aπl=> + aπl'. elim aπl'; [done|]=>/= *. by f_equal. } done.
  Qed.
End vec_pushpop.
