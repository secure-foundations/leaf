From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec_util.
  Context `{!typeG Σ}.

  Definition vec_push_core {𝔄} (ty: type 𝔄) : val :=
    rec: BAnon ["v"; "x"] :=
      let: "l" := !"v" in
      let: "len" := !("v" +ₗ #1) in let: "ex" := !("v" +ₗ #2) in
      "v" +ₗ #1 <- "len" + #1;;
      if: "ex" ≤ #0 then
        "v" +ₗ #2 <- "len";;
        let: "l'" := new [(#2 * "len" + #1) * #ty.(ty_size)] in
        memcpy ["l'"; "len" * #ty.(ty_size); "l"];;
        delete ["len" * #ty.(ty_size); "l"];;
        "v" <- "l'";;
        "l'" +ₗ "len" * #ty.(ty_size) <-{ty.(ty_size)} !"x"
      else
        "v" +ₗ #2 <- "ex" - #1;;
        "l" +ₗ "len" * #ty.(ty_size) <-{ty.(ty_size)} !"x".

  Lemma wp_vec_push_core {𝔄}
    (ty: type 𝔄) (v x: loc) (len: nat) (aπl: vec _ len) bπ du dx tid E :
    {{{ ∃(l: loc) (ex: nat),
      v ↦∗ [ #l; #len; #ex] ∗
      ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ du tid) ∗
      (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
      freeable_sz' ((len + ex) * ty.(ty_size)) l ∗
      x ↦∗: ty.(ty_own) bπ dx tid
    }}} vec_push_core ty [ #v; #x] @ E {{{ RET #☠; ∃(l: loc) (ex: nat),
      v ↦∗ [ #l; #(S len); #ex] ∗
      ([∗ list] i ↦ aπ ∈ (vsnoc aπl bπ),
        (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ (du `max` dx) tid) ∗
      (l +ₗ[ty] S len) ↦∗len (ex * ty.(ty_size)) ∗
      freeable_sz' ((S len + ex) * ty.(ty_size)) l ∗
      x ↦∗len ty.(ty_size)
    }}}.
  Proof.
    iIntros (?) "(%&%& ↦ & ↦tys & (%vl & %Lvl & ↦ex) & † & (%& ↦x & ty)) ToΦ".
    rewrite !heap_mapsto_vec_cons shift_loc_assoc trans_big_sepL_mt_ty_own.
    iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ &_)". iDestruct "↦tys" as (?) "[↦l tys]".
    iDestruct (ty_size_eq with "ty") as %?.
    wp_rec. wp_read. wp_let. do 2 (wp_op; wp_read; wp_let). do 2 wp_op.
    wp_write. wp_op. wp_case. have ->: (len + 1)%Z = S len by lia.
    move: Lvl. case ex as [|ex]=>/= Lvl; last first.
    { move: {Lvl}(app_length_ex vl _ _ Lvl)=> [vl'[?[->[Lvl ?]]]].
      rewrite heap_mapsto_vec_app Lvl shift_loc_assoc_nat Nat.add_comm.
      iDestruct "↦ex" as "[↦new ↦ex]". have ->: len + S ex = S len + ex by lia.
      do 2 wp_op. have ->: (S ex - 1)%Z = ex by lia. wp_write. do 2 wp_op.
      rewrite -Nat2Z.inj_mul. iApply (wp_memcpy with "[$↦new $↦x]"); [lia..|].
      iIntros "!> [↦new ↦x]". iApply "ToΦ". iExists _, _.
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil !shift_loc_assoc.
      iFrame "↦₀ ↦₁ ↦₂ †". iSplitL "↦l ↦new tys ty"; last first.
      { iSplitL "↦ex"; iExists _; by iFrame. }
      rewrite vec_to_list_snoc big_sepL_app. iSplitL "↦l tys".
      - rewrite trans_big_sepL_mt_ty_own. iExists _. iFrame "↦l".
        iStopProof. do 3 f_equiv. apply ty_own_depth_mono. lia.
      - rewrite big_sepL_singleton. iExists _. rewrite Nat.add_0_r vec_to_list_length.
        iFrame "↦new". iApply ty_own_depth_mono; [|done]. lia. }
    rewrite plus_0_r. wp_op. wp_write. do 3 wp_op.
    wp_apply wp_new; [lia|done|]. iIntros (?) "[†' ↦l']". wp_let.
    have ->: ∀sz: nat, ((2 * len + 1) * sz)%Z = len * sz + (sz + len * sz) by lia.
    rewrite Nat2Z.id !repeat_app !heap_mapsto_vec_app !repeat_length shift_loc_assoc_nat.
    iDestruct "↦l'" as "(↦l' & ↦new & ↦ex')".
    iDestruct (big_sepL_ty_own_length with "tys") as %Lwll. wp_op.
    wp_apply (wp_memcpy with "[$↦l' $↦l]"); [rewrite repeat_length; lia|lia|].
    iIntros "[↦l' ↦l]". wp_seq. wp_op. rewrite -Nat2Z.inj_mul.
    wp_apply (wp_delete with "[$↦l †]"); [lia|by rewrite Lwll|]. iIntros "_".
    wp_seq. wp_write. do 2 wp_op. rewrite -Nat2Z.inj_mul.
    iApply (wp_memcpy with "[$↦new $↦x]"); [by rewrite repeat_length|lia|].
    iIntros "!> [↦new ↦x]". iApply "ToΦ". iExists _, _.
    rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil shift_loc_assoc. iFrame "↦₀ ↦₁ ↦₂".
    have ->: ∀sz, sz + (len + len) * sz = len * sz + (sz + len * sz) by lia.
    iFrame "†'". rewrite Nat.add_comm. iSplitL "↦l' ↦new tys ty"; last first.
    { iSplitR "↦x"; iExists _; iFrame; by [rewrite repeat_length|]. }
    rewrite vec_to_list_snoc big_sepL_app. iSplitL "↦l' tys".
    - rewrite trans_big_sepL_mt_ty_own. iExists _. iFrame "↦l'".
      iStopProof. do 3 f_equiv. apply ty_own_depth_mono. lia.
    - rewrite big_sepL_singleton. iExists _. rewrite Nat.add_0_r vec_to_list_length.
      iFrame "↦new". iApply ty_own_depth_mono; [|done]. lia.
  Qed.
End vec_util.
