From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib Require Import vec_util smallvec.smallvec.

Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section smallvec_push.
  Context `{!typeG Σ}.

  Definition smallvec_push_core {𝔄} (n: nat) (ty: type 𝔄) : val :=
    rec: BAnon ["v"; "x"] :=
      if: !"v" then (* array mode *)
        let: "len" := !("v" +ₗ #2) in "v" +ₗ #2 <- "len" + #1;;
        if: "len" + #1 ≤ #n then
          "v" +ₗ #4 +ₗ "len" * #ty.(ty_size) <-{ty.(ty_size)} !"x"
        else
          let: "l" := new [("len" + #1) * #ty.(ty_size)] in
          memcpy ["l"; "len" * #ty.(ty_size); "v" +ₗ #4];;
          "l" +ₗ "len" * #ty.(ty_size) <-{ty.(ty_size)} !"x";;
          "v" <- #false;; "v" +ₗ #1 <- "l";; "v" +ₗ #3 <- #0
      else (* vector mode *)
        vec_push_core ty ["v" +ₗ #1; "x"].

  Lemma wp_smallvec_push_core {𝔄} n (ty: type 𝔄) (v x: loc) alπ bπ du dx tid E :
    {{{
      v ↦∗: (smallvec n ty).(ty_own) alπ du tid ∗ x ↦∗: ty.(ty_own) bπ dx tid
    }}} smallvec_push_core n ty [ #v; #x] @ E {{{ RET #☠;
      v ↦∗: (smallvec n ty).(ty_own) (λ π, alπ π ++ [bπ π]) (du `max` dx) tid ∗
      x ↦∗len ty.(ty_size)
    }}}.
  Proof.
    iIntros (?) "[big (%& ↦x & ty)] ToΦ". iDestruct (ty_size_eq with "ty") as %?.
    rewrite split_mt_smallvec. iDestruct "big" as (b ? len ??->) "(↦ & big)".
    rewrite heap_mapsto_vec_cons. iDestruct "↦" as "[↦₀ ↦']". wp_rec. wp_read.
    wp_if. case b=>/=; last first.
    { iDestruct "big" as "((%&%& ↦tl) & ↦tys & ↦ex & †)". wp_op.
      iApply (wp_vec_push_core with "[↦' ↦tys ↦ex † ↦x ty]").
      { iExists _, _. iFrame "↦' † ↦ex ↦tys". iExists _. iFrame. }
      iIntros "!> (%&%& ↦' & ↦tys & ↦ex & † & ↦x)". iApply "ToΦ". iFrame "↦x".
      rewrite split_mt_smallvec. iExists false, _, _, _, _. iFrame "↦tys ↦ex †".
      iDestruct (heap_mapsto_vec_cons with "[$↦₀ $↦']") as "$".
      iSplitR; last first. { iExists _. by iFrame. } iPureIntro. fun_ext=> ?.
      by rewrite vec_to_list_snoc lapply_app. }
    rewrite !heap_mapsto_vec_cons !shift_loc_assoc. iDestruct "↦'" as "(↦₁ & ↦₂ & ↦₃ &_)".
    iDestruct "big" as "[↦tys (%wl & %EqLen & ↦tl)]".
    wp_op. wp_read. wp_let. do 2 wp_op. wp_write.
    have ->: (len + 1)%Z = S len by lia. do 2 wp_op. wp_if. case Cmp: (bool_decide _).
    - move: Cmp=>/bool_decide_eq_true ?. do 3 wp_op. rewrite -Nat2Z.inj_mul.
      have Lwl: length wl = ty.(ty_size) + (n - S len) * ty.(ty_size).
      { rewrite Nat.mul_sub_distr_r Nat.add_sub_assoc; [lia|].
        apply Nat.mul_le_mono_r. lia. }
      move: (app_length_ex wl _ _ Lwl)=> [?[?[->[Lul ?]]]].
      rewrite heap_mapsto_vec_app Lul !shift_loc_assoc. iDestruct "↦tl" as "[↦new ↦tl]".
      iApply (wp_memcpy with "[$↦new $↦x]"); [lia..|]. iIntros "!> [↦new ↦x]".
      iApply "ToΦ". iSplitR "↦x"; last first. { iExists _. by iFrame. }
      rewrite split_mt_smallvec. iExists _, _, _, _, (vsnoc _ _).
      rewrite !heap_mapsto_vec_cons !shift_loc_assoc heap_mapsto_vec_nil.
      iFrame "↦₀ ↦₁ ↦₂ ↦₃"=>/=. iSplit.
      { iPureIntro. fun_ext=> ?. by rewrite vec_to_list_snoc lapply_app. }
      iSplitR "↦tl"; last first.
      { have ->: ∀sz, (4 + (len * sz)%nat + sz = 4 + (sz + len * sz)%nat)%Z by lia.
        iExists _. iFrame "↦tl". iPureIntro. lia. }
      rewrite vec_to_list_snoc big_sepL_app big_sepL_singleton. iSplitL "↦tys".
      + iStopProof. do 6 f_equiv. apply ty_own_depth_mono. lia.
      + iExists _. iSplitL "↦new".
        * rewrite vec_to_list_length Nat.add_0_r shift_loc_assoc. iFrame.
        * iApply ty_own_depth_mono; [|done]. lia.
    - do 2 wp_op. wp_apply wp_new; [lia|done|]. iIntros (?) "[† ↦l]".
      have ->: ∀sz: nat, ((len + 1) * sz)%Z = len * sz + sz by lia.
      rewrite Nat2Z.id. wp_let. do 2 wp_op.
      rewrite repeat_app heap_mapsto_vec_app. iDestruct "↦l" as "[↦l ↦new]".
      rewrite repeat_length trans_big_sepL_mt_ty_own. iDestruct "↦tys" as (?) "[↦o tys]".
      iDestruct (big_sepL_ty_own_length with "tys") as %Lwll.
      wp_apply (wp_memcpy with "[$↦l $↦o]"); [rewrite repeat_length; lia|lia|].
      iIntros "[↦l ↦o]". wp_seq. do 2 wp_op. rewrite -Nat2Z.inj_mul.
      wp_apply (wp_memcpy with "[$↦new $↦x]"); [by rewrite repeat_length|lia|].
      iIntros "[↦new ↦x]". wp_seq. wp_write. do 2 (wp_op; wp_write).
      iApply "ToΦ". iSplitR "↦x"; last first. { iExists _. by iFrame. }
      rewrite split_mt_smallvec. iExists _, _, _, 0, (vsnoc _ _).
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
      iFrame "↦₀ ↦₁ ↦₂ ↦₃"=>/=. iSplit.
      { iPureIntro. fun_ext=> ?. by rewrite vec_to_list_snoc lapply_app. }
      rewrite Nat.add_comm Nat.add_0_r. iFrame "†". iSplitL "↦o ↦tl".
      { iExists (_++_). rewrite EqLen app_length heap_mapsto_vec_app shift_loc_assoc.
        iFrame "↦o". rewrite Lwll. by iFrame "↦tl". }
      iSplitL; last first. { iExists []. by rewrite heap_mapsto_vec_nil. }
      rewrite vec_to_list_snoc big_sepL_app big_sepL_singleton. iSplitL "tys ↦l".
      + rewrite trans_big_sepL_mt_ty_own. iExists _. iFrame "↦l". iStopProof.
        do 3 f_equiv. apply ty_own_depth_mono. lia.
      + iExists _. rewrite Nat.add_0_r vec_to_list_length. iFrame "↦new".
        iApply ty_own_depth_mono; [|done]. lia.
  Qed.

  Definition smallvec_push {𝔄} n (ty: type 𝔄) : val :=
    fn: ["v"; "x"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      smallvec_push_core n ty ["v'"; "x"];;
      delete [ #ty.(ty_size); "x"];;
      let: "r" := new [ #0] in return: ["r"].

  (* Rust's SmallVec::push *)
  Lemma smallvec_push_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_push n ty) (fn<α>(∅; &uniq{α} (smallvec n ty), ty) → ())
      (λ post '-[(al, al'); a], al' = al ++ [a] → post ()).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[x[]]]. simpl_subst.
    iIntros (?(pπ & bπ &[])?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(v & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "v" as ([|dv]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦v & [#LftIn uniq]) †v]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//=.
    iDestruct "x" as "[↦ty †x]". rewrite heap_mapsto_vec_singleton. wp_read.
    iDestruct "uniq" as (du ξi [? Eq]) "[Vo Bor]".
    move: Eq. set ξ := PrVar _ ξi=> Eq.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦sv) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    wp_apply (wp_delete with "[$↦v $†v]"); [done|]. iIntros "_".
    iCombine "⧖u ⧖x" as "#⧖". wp_seq.
    wp_apply (wp_smallvec_push_core with "[$↦sv $↦ty]").
    iIntros "[↦sv (%& %Lvl & ↦x)]". wp_seq. rewrite freeable_sz_full.
    wp_apply (wp_delete with "[$↦x †x]"); [lia|by rewrite Lvl|]. iIntros "_".
    wp_seq. set pπ' := λ π, ((pπ π).1 ++ [bπ π], π ξ).
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[Pc ↦sv]") as "[Bor α]". { iExists _, _. iFrame "⧖ Pc ↦sv". }
    iMod ("ToL" with "α L") as "L".
    iApply (type_type +[#v' ◁ &uniq{α} (smallvec n ty)] -[pπ']
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_new; [done|]. intro_subst.
      iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= right_id (tctx_hasty_val #_). iExists _.
      iFrame "⧖ LftIn". iExists _, _. rewrite /uniq_body.
      rewrite (proof_irrel (@prval_to_inh (listₛ 𝔄) (fst ∘ pπ'))
        (@prval_to_inh (listₛ 𝔄) (fst ∘ pπ))). by iFrame.
    - iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq π)=>/=.
      by case (pπ π)=>/= ??->.
  Qed.
End smallvec_push.
