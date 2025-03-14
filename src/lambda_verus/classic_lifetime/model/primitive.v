From lrust.lifetime.model Require Export definitions.
From iris.algebra Require Import csum auth frac gmap agree gset proofmode_classes.
From iris.base_logic.lib Require Import boxes.
From iris.bi Require Import fractional.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Section primitive.
Context `{!invGS Σ, !lftGS Σ}.
Implicit Types κ : lft.

Lemma to_borUR_included (B : gmap slice_name bor_state) i s q :
  {[i := (q%Qp, to_agree s)]} ≼ to_borUR B → B !! i = Some s.
Proof.
  rewrite singleton_included_l=> -[qs []]. unfold_leibniz.
  rewrite lookup_fmap fmap_Some_equiv=> -[s' [-> ->]].
  by move=> /Some_pair_included [_] /Some_included_total /to_agree_included=>->.
Qed.

Lemma lft_init `{!lftGpreS Σ} E :
  ↑lftN ⊆ E → ⊢ |={E}=> ∃ _ : lftGS Σ, lft_ctx.
Proof.
  iIntros (?). rewrite /lft_ctx.
  iMod (own_alloc (● ∅ : authR alftUR)) as (γa) "Ha"; first by apply auth_auth_valid.
  iMod (own_alloc (● ∅ : authR ilftUR)) as (γi) "Hi"; first by apply auth_auth_valid.
  set (HlftG := LftG _ _ _ γa _ γi _ _ _). iExists HlftG.
  iMod (inv_alloc _ _ lfts_inv with "[Ha Hi]") as "$"; last done.
  iModIntro. rewrite /lfts_inv /own_alft_auth /own_ilft_auth. iExists ∅, ∅.
  rewrite /to_alftUR /to_ilftUR !fmap_empty. iFrame.
  rewrite dom_empty_L big_sepS_empty. done.
Qed.

(** Ownership *)
Lemma own_ilft_auth_agree (I : gmap lft lft_names) κ γs :
  own_ilft_auth I -∗
    own ilft_name (◯ {[κ := to_agree γs]}) -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI Hκ". iDestruct (own_valid_2 with "HI Hκ")
    as %[[? [Hl ?]]%singleton_included_l _]%auth_both_valid_discrete.
  unfold to_ilftUR in *. simplify_map_eq.
  destruct (fmap_Some_equiv_1 _ _ _ Hl) as (?&?&?). eauto.
Qed.

Lemma own_alft_auth_agree (A : gmap atomic_lft bool) Λ b :
  own_alft_auth A -∗
    own alft_name (◯ {[Λ := to_lft_stateR b]}) -∗ ⌜A !! Λ = Some b⌝.
Proof.
  iIntros "HA HΛ".
  iDestruct (own_valid_2 with "HA HΛ") as %[HA _]%auth_both_valid_discrete.
  iPureIntro. move: HA=> /singleton_included_l [qs [/leibniz_equiv_iff]].
  rewrite lookup_fmap fmap_Some=> -[b' [? ->]] /Some_included.
  move=> [/leibniz_equiv_iff|/csum_included]; destruct b, b'; naive_solver.
Qed.

Lemma own_bor_auth I κ x : own_ilft_auth I -∗ own_bor κ x -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI"; iDestruct 1 as (γs) "[? _]".
  by iApply (own_ilft_auth_agree with "HI").
Qed.

Lemma own_bor_op κ x y : own_bor κ (x ⋅ y) ⊣⊢ own_bor κ x ∗ own_bor κ y.
Proof.
  iSplit.
  { iDestruct 1 as (γs) "[#? [Hx Hy]]"; iSplitL "Hx"; iExists γs; eauto. }
  iIntros "[Hx Hy]".
  iDestruct "Hx" as (γs) "[Hγs Hx]"; iDestruct "Hy" as (γs') "[Hγs' Hy]".
  iDestruct (own_valid_2 with "Hγs Hγs'") as %Hγs. move : Hγs.
  rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid=> /to_agree_op_inv_L <-.
  iExists γs. iSplit. done. rewrite own_op; iFrame.
Qed.
Global Instance own_bor_into_op κ x x1 x2 :
  IsOp x x1 x2 → IntoSep (own_bor κ x) (own_bor κ x1) (own_bor κ x2).
Proof.
  rewrite /IsOp /IntoSep=>-> /=. by rewrite -own_bor_op.
Qed.
Lemma own_bor_valid κ x : own_bor κ x -∗ ✓ x.
Proof. iDestruct 1 as (γs) "[#? Hx]". by iApply own_valid. Qed.
Lemma own_bor_valid_2 κ x y : own_bor κ x -∗ own_bor κ y -∗ ✓ (x ⋅ y).
Proof. apply wand_intro_r. rewrite -own_bor_op. apply own_bor_valid. Qed.
Lemma own_bor_update κ x y : x ~~> y → own_bor κ x ==∗ own_bor κ y.
Proof.
  iDestruct 1 as (γs) "[#Hκ Hx]"; iExists γs. iFrame "Hκ". by iApply own_update.
Qed.
Lemma own_bor_update_2 κ x1 x2 y :
  x1 ⋅ x2 ~~> y → own_bor κ x1 ⊢ own_bor κ x2 ==∗ own_bor κ y.
Proof.
  intros. apply wand_intro_r. rewrite -own_bor_op. by apply own_bor_update.
Qed.

Lemma own_cnt_auth I κ x : own_ilft_auth I -∗ own_cnt κ x -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI"; iDestruct 1 as (γs) "[? _]".
  by iApply (own_ilft_auth_agree with "HI").
Qed.
Lemma own_cnt_op κ x y : own_cnt κ (x ⋅ y) ⊣⊢ own_cnt κ x ∗ own_cnt κ y.
Proof.
  iSplit.
  { iDestruct 1 as (γs) "[#? [Hx Hy]]"; iSplitL "Hx"; iExists γs; eauto. }
  iIntros "[Hx Hy]".
  iDestruct "Hx" as (γs) "[Hγs Hx]"; iDestruct "Hy" as (γs') "[Hγs' Hy]".
  iDestruct (own_valid_2 with "Hγs Hγs'") as %Hγs. move: Hγs.
  rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid=> /to_agree_op_inv_L=> <-.
  iExists γs. iSplit; first done. rewrite own_op; iFrame.
Qed.
Global Instance own_cnt_into_op κ x x1 x2 :
  IsOp x x1 x2 → IntoSep (own_cnt κ x) (own_cnt κ x1) (own_cnt κ x2).
Proof.
  rewrite /IsOp /IntoSep=> ->. by rewrite -own_cnt_op.
Qed.
Lemma own_cnt_valid κ x : own_cnt κ x -∗ ✓ x.
Proof. iDestruct 1 as (γs) "[#? Hx]". by iApply own_valid. Qed.
Lemma own_cnt_valid_2 κ x y : own_cnt κ x -∗ own_cnt κ y -∗ ✓ (x ⋅ y).
Proof. apply wand_intro_r. rewrite -own_cnt_op. apply own_cnt_valid. Qed.
Lemma own_cnt_update κ x y : x ~~> y → own_cnt κ x ==∗ own_cnt κ y.
Proof.
  iDestruct 1 as (γs) "[#Hκ Hx]"; iExists γs. iFrame "Hκ". by iApply own_update.
Qed.
Lemma own_cnt_update_2 κ x1 x2 y :
  x1 ⋅ x2 ~~> y → own_cnt κ x1 -∗ own_cnt κ x2 ==∗ own_cnt κ y.
Proof.
  intros. apply wand_intro_r. rewrite -own_cnt_op. by apply own_cnt_update.
Qed.

Lemma own_inh_auth I κ x : own_ilft_auth I -∗ own_inh κ x -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI"; iDestruct 1 as (γs) "[? _]".
  by iApply (own_ilft_auth_agree with "HI").
Qed.
Lemma own_inh_op κ x y : own_inh κ (x ⋅ y) ⊣⊢ own_inh κ x ∗ own_inh κ y.
Proof.
  iSplit.
  { iDestruct 1 as (γs) "[#? [Hx Hy]]"; iSplitL "Hx"; iExists γs; eauto. }
  iIntros "[Hx Hy]".
  iDestruct "Hx" as (γs) "[Hγs Hx]"; iDestruct "Hy" as (γs') "[Hγs' Hy]".
  iDestruct (own_valid_2 with "Hγs Hγs'") as %Hγs. move: Hγs.
  rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid=> /to_agree_op_inv_L=> <-.
  iExists γs. iSplit. done. rewrite own_op; iFrame.
Qed.
Global Instance own_inh_into_op κ x x1 x2 :
  IsOp x x1 x2 → IntoSep (own_inh κ x) (own_inh κ x1) (own_inh κ x2).
Proof.
  rewrite /IsOp /IntoSep=> ->. by rewrite -own_inh_op.
Qed.
Lemma own_inh_valid κ x : own_inh κ x -∗ ✓ x.
Proof. iDestruct 1 as (γs) "[#? Hx]". by iApply own_valid. Qed.
Lemma own_inh_valid_2 κ x y : own_inh κ x -∗ own_inh κ y -∗ ✓ (x ⋅ y).
Proof. apply wand_intro_r. rewrite -own_inh_op. apply own_inh_valid. Qed.
Lemma own_inh_update κ x y : x ~~> y → own_inh κ x ==∗ own_inh κ y.
Proof.
  iDestruct 1 as (γs) "[#Hκ Hx]"; iExists γs. iFrame "Hκ". by iApply own_update.
Qed.
Lemma own_inh_update_2 κ x1 x2 y :
  x1 ⋅ x2 ~~> y → own_inh κ x1 ⊢ own_inh κ x2 ==∗ own_inh κ y.
Proof.
  intros. apply wand_intro_r. rewrite -own_inh_op. by apply own_inh_update.
Qed.

(** Alive and dead *)
Global Instance lft_alive_in_dec A κ : Decision (lft_alive_in A κ).
Proof.
  refine (cast_if (decide (set_Forall (λ Λ, A !! Λ = Some true)
                  (dom (gset atomic_lft) κ))));
    rewrite /lft_alive_in; by setoid_rewrite <-gmultiset_elem_of_dom.
Qed.
Global Instance lft_dead_in_dec A κ : Decision (lft_dead_in A κ).
Proof.
  refine (cast_if (decide (set_Exists (λ Λ, A !! Λ = Some false)
                  (dom (gset atomic_lft) κ))));
      rewrite /lft_dead_in; by setoid_rewrite <-gmultiset_elem_of_dom.
Qed.

Lemma lft_alive_or_dead_in A κ :
  (∃ Λ, Λ ∈ κ ∧ A !! Λ = None) ∨ (lft_alive_in A κ ∨ lft_dead_in A κ).
Proof.
  rewrite /lft_alive_in /lft_dead_in.
  destruct (decide (set_Exists (λ Λ, A !! Λ = None) (dom (gset _) κ)))
    as [(Λ & ?%gmultiset_elem_of_dom & HAΛ)|HA%(not_set_Exists_Forall _)]; first eauto.
  destruct (decide (set_Exists (λ Λ, A !! Λ = Some false) (dom (gset _) κ)))
    as [(Λ & HΛ%gmultiset_elem_of_dom & ?)|HA'%(not_set_Exists_Forall _)]; first eauto.
  right; left. intros Λ HΛ%gmultiset_elem_of_dom.
  move: (HA _ HΛ) (HA' _ HΛ)=> /=. case: (A !! Λ)=>[[]|]; naive_solver.
Qed.
Lemma lft_alive_and_dead_in A κ : lft_alive_in A κ → lft_dead_in A κ → False.
Proof. intros Halive (Λ&HΛ&?). generalize (Halive _ HΛ). naive_solver. Qed.

Lemma lft_alive_in_subseteq A κ κ' :
  lft_alive_in A κ → κ' ⊆ κ → lft_alive_in A κ'.
Proof. intros Halive ? Λ ?. by eapply Halive, gmultiset_elem_of_subseteq. Qed.

Lemma lft_alive_in_insert A κ Λ b :
  A !! Λ = None → lft_alive_in A κ → lft_alive_in (<[Λ:=b]> A) κ.
Proof.
  intros HΛ Halive Λ' HΛ'.
  assert (Λ ≠ Λ') by (intros ->; move:(Halive _ HΛ'); by rewrite HΛ).
  rewrite lookup_insert_ne; eauto.
Qed.
Lemma lft_alive_in_insert_false A κ Λ b :
  Λ ∉ κ → lft_alive_in A κ → lft_alive_in (<[Λ:=b]> A) κ.
Proof.
  intros HΛ Halive Λ' HΛ'.
  rewrite lookup_insert_ne; last (by intros ->); auto.
Qed.

Lemma lft_dead_in_insert A κ Λ b :
  A !! Λ = None → lft_dead_in A κ → lft_dead_in (<[Λ:=b]> A) κ.
Proof.
  intros HΛ (Λ'&?&HΛ').
  assert (Λ ≠ Λ') by (intros ->; move:HΛ'; by rewrite HΛ).
  exists Λ'. by rewrite lookup_insert_ne.
Qed.
Lemma lft_dead_in_insert_false A κ Λ :
  lft_dead_in A κ → lft_dead_in (<[Λ:=false]> A) κ.
Proof.
  intros (Λ'&?&HΛ'). destruct (decide (Λ = Λ')) as [<-|].
  - exists Λ. by rewrite lookup_insert.
  - exists Λ'. by rewrite lookup_insert_ne.
Qed.
Lemma lft_dead_in_insert_false' A κ Λ : Λ ∈ κ → lft_dead_in (<[Λ:=false]> A) κ.
Proof. exists Λ. by rewrite lookup_insert. Qed.
Lemma lft_dead_in_alive_in_union A κ κ' :
  lft_dead_in A (κ ⊓ κ') → lft_alive_in A κ → lft_dead_in A κ'.
Proof.
  intros (Λ & [Hin|Hin]%gmultiset_elem_of_disj_union & HΛ) Halive.
  - contradict HΛ. rewrite (Halive _ Hin). done.
  - exists Λ. auto.
Qed.

Lemma lft_dead_in_tok A κ:
  lft_dead_in A κ →
  own_alft_auth A ==∗ own_alft_auth A ∗ [†κ].
Proof.
  iIntros ((Λ & HΛκ & EQΛ)) "HA". unfold own_alft_auth, lft_dead.
  assert (({[Λ := Cinr ()]} ⋅ to_alftUR A) = to_alftUR A) as HAinsert.
  { unfold_leibniz=>Λ'. destruct (decide (Λ = Λ')) as [<-|Hne].
    + rewrite lookup_op lookup_fmap EQΛ lookup_singleton /=. done.
    + rewrite lookup_op lookup_fmap !lookup_insert_ne // lookup_empty left_id -lookup_fmap. done. }
  iMod (own_update _ ((● to_alftUR A)) with "HA") as "HA".
  { eapply (auth_update_alloc _ _ ({[Λ := Cinr ()]}⋅∅)), op_local_update_discrete.
    by rewrite HAinsert. }
  rewrite right_id. iDestruct "HA" as "[HA HΛ]". iSplitL "HA"; last (iExists _; by iFrame).
  by rewrite HAinsert.
Qed.

Lemma lft_inv_alive_in A κ : lft_alive_in A κ → lft_inv A κ -∗ lft_inv_alive κ.
Proof.
  rewrite /lft_inv. iIntros (?) "[[$ _]|[_ %]]".
  by destruct (lft_alive_and_dead_in A κ).
Qed.
Lemma lft_inv_dead_in A κ : lft_dead_in A κ → lft_inv A κ -∗ lft_inv_dead κ.
Proof.
  rewrite /lft_inv. iIntros (?) "[[_ %]|[$ _]]".
  by destruct (lft_alive_and_dead_in A κ).
Qed.

(** Basic rules about lifetimes  *)
Global Instance lft_inhabited : Inhabited lft := _.
Global Instance bor_idx_inhabited : Inhabited bor_idx := _.
Global Instance lft_intersect_comm : Comm (A:=lft) eq (⊓) := _.
Global Instance lft_intersect_assoc : Assoc (A:=lft) eq (⊓) := _.
Global Instance lft_intersect_inj_1 κ : Inj eq eq (κ ⊓.) := _.
Global Instance lft_intersect_inj_2 κ : Inj eq eq (.⊓ κ) := _.
Global Instance lft_intersect_left_id : LeftId eq static (⊓) := _.
Global Instance lft_intersect_right_id : RightId eq static (⊓) := _.

Lemma lft_tok_sep q κ1 κ2 : q.[κ1] ∗ q.[κ2] ⊣⊢ q.[κ1 ⊓ κ2].
Proof. by rewrite /lft_tok -big_sepMS_disj_union. Qed.

Lemma lft_dead_or κ1 κ2 : [†κ1] ∨ [†κ2] ⊣⊢ [† κ1 ⊓ κ2].
Proof.
  rewrite /lft_dead -or_exist. apply exist_proper=> Λ.
  rewrite -sep_or_r -pure_or. do 2 f_equiv. set_solver.
Qed.

Lemma lft_tok_dead q κ : q.[κ] -∗ [† κ] -∗ False.
Proof.
  rewrite /lft_tok /lft_dead. iIntros "H"; iDestruct 1 as (Λ') "[% H']".
  iDestruct (@big_sepMS_elem_of _ _ _ _ _ _ Λ' with "H") as "H"=> //.
  iDestruct (own_valid_2 with "H H'") as %Hvalid.
  move: Hvalid=> /auth_frag_valid /=; by rewrite singleton_op singleton_valid.
Qed.

Lemma lft_tok_static q : ⊢ q.[static].
Proof. by rewrite /lft_tok big_sepMS_empty. Qed.

Lemma lft_dead_static : [† static] -∗ False.
Proof. rewrite /lft_dead. iDestruct 1 as (Λ) "[% H']". set_solver. Qed.

(* Fractional and AsFractional instances *)
Global Instance lft_tok_fractional κ : Fractional (λ q, q.[κ])%I.
Proof.
  intros p q. rewrite /lft_tok -big_sepMS_sep. apply big_sepMS_proper.
  intros Λ ?. rewrite Cinl_op -singleton_op auth_frag_op own_op //.
Qed.
Global Instance lft_tok_as_fractional κ q :
  AsFractional q.[κ] (λ q, q.[κ])%I q.
Proof. split. done. apply _. Qed.
Global Instance idx_bor_own_fractional i : Fractional (λ q, idx_bor_own q i)%I.
Proof.
  intros p q. rewrite /idx_bor_own -own_bor_op /own_bor. f_equiv=>?.
  rewrite -auth_frag_op singleton_op -pair_op agree_idemp. done.
Qed.
Global Instance frame_lft_tok p κ q1 q2 RES :
  FrameFractionalHyps p q1.[κ] (λ q, q.[κ])%I RES q1 q2 →
  Frame p q1.[κ] q2.[κ] RES | 5.
Proof. apply: frame_fractional. Qed.

Global Instance idx_bor_own_as_fractional i q :
  AsFractional (idx_bor_own q i) (λ q, idx_bor_own q i)%I q.
Proof. split. done. apply _. Qed.
Global Instance frame_idx_bor_own p i q1 q2 RES :
  FrameFractionalHyps p (idx_bor_own q1 i) (λ q, idx_bor_own q i)%I RES q1 q2 →
  Frame p (idx_bor_own q1 i) (idx_bor_own q2 i) RES | 5.
Proof. apply: frame_fractional. Qed.

(** Lifetime inclusion *)
Lemma lft_incl_acc E κ κ' q :
  ↑lftN ⊆ E →
  κ ⊑ κ' -∗ q.[κ] ={E}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={E}=∗ q.[κ]).
Proof.
  rewrite /lft_incl.
  iIntros (?) "#[H _] Hq". iApply fupd_mask_mono; first done.
  iMod ("H" with "Hq") as (q') "[Hq' Hclose]". iExists q'.
  iIntros "{$Hq'} !> Hq". iApply fupd_mask_mono; first done. by iApply "Hclose".
Qed.

Lemma lft_incl_dead E κ κ' : ↑lftN ⊆ E → κ ⊑ κ' -∗ [†κ'] ={E}=∗ [†κ].
Proof.
  rewrite /lft_incl.
  iIntros (?) "#[_ H] Hq". iApply fupd_mask_mono; first done. by iApply "H".
Qed.

Lemma lft_incl_intro κ κ' :
  □ ((∀ q, q.[κ] ={↑lftN}=∗ ∃ q', q'.[κ'] ∗ (q'.[κ'] ={↑lftN}=∗ q.[κ])) ∗
      ([†κ'] ={↑lftN}=∗ [†κ])) -∗ κ ⊑ κ'.
Proof. reflexivity. Qed.

Lemma lft_intersect_incl_l κ κ' : ⊢ κ ⊓ κ' ⊑ κ.
Proof.
  unfold lft_incl. iIntros "!>". iSplitR.
  - iIntros (q). rewrite <-lft_tok_sep. iIntros "[H Hf]". iExists q. iFrame.
    rewrite <-lft_tok_sep. by iIntros "!>{$Hf}$".
  - iIntros "? !>". iApply lft_dead_or. auto.
Qed.

Lemma lft_intersect_incl_r κ κ' : ⊢ κ ⊓ κ' ⊑ κ'.
Proof. rewrite comm. apply lft_intersect_incl_l. Qed.

Lemma lft_incl_refl κ : ⊢ κ ⊑ κ.
Proof. unfold lft_incl. iIntros "!>"; iSplitR; auto 10 with iFrame. Qed.

Lemma lft_incl_trans κ κ' κ'' : κ ⊑ κ' -∗ κ' ⊑ κ'' -∗ κ ⊑ κ''.
Proof.
  rewrite /lft_incl. iIntros "#[H1 H1†] #[H2 H2†] !>". iSplitR.
  - iIntros (q) "Hκ".
    iMod ("H1" with "Hκ") as (q') "[Hκ' Hclose]".
    iMod ("H2" with "Hκ'") as (q'') "[Hκ'' Hclose']".
    iExists q''. iIntros "{$Hκ''} !> Hκ''".
    iMod ("Hclose'" with "Hκ''") as "Hκ'". by iApply "Hclose".
  - iIntros "H†". iMod ("H2†" with "H†"). by iApply "H1†".
Qed.

Lemma lft_intersect_acc κ κ' q q' :
  q.[κ] -∗ q'.[κ'] -∗ ∃ q'', q''.[κ ⊓ κ'] ∗ (q''.[κ ⊓ κ'] -∗ q.[κ] ∗ q'.[κ']).
Proof.
  iIntros "Hκ Hκ'".
  destruct (Qp_lower_bound q q') as (qq & q0 & q'0 & -> & ->).
  iExists qq. rewrite -lft_tok_sep.
  iDestruct "Hκ" as "[$ Hκ]". iDestruct "Hκ'" as "[$ Hκ']".
  iIntros "[Hκ+ Hκ'+]". iSplitL "Hκ Hκ+"; iApply fractional_split; iFrame.
Qed.

Lemma lft_incl_glb κ κ' κ'' : κ ⊑ κ' -∗ κ ⊑ κ'' -∗ κ ⊑ κ' ⊓ κ''.
Proof.
  rewrite /lft_incl. iIntros "#[H1 H1†] #[H2 H2†]!>". iSplitR.
  - iIntros (q) "[Hκ'1 Hκ'2]".
    iMod ("H1" with "Hκ'1") as (q') "[Hκ' Hclose']".
    iMod ("H2" with "Hκ'2") as (q'') "[Hκ'' Hclose'']".
    iDestruct (lft_intersect_acc with "Hκ' Hκ''") as (qq) "[Hqq Hclose]".
    iExists qq. iFrame. iIntros "!> Hqq".
    iDestruct ("Hclose" with "Hqq") as "[Hκ' Hκ'']".
    iMod ("Hclose'" with "Hκ'") as "?".
    iMod ("Hclose''" with "Hκ''") as "?". iModIntro.
    iApply fractional_half. iFrame.
  - rewrite -lft_dead_or. iIntros "[H†|H†]". by iApply "H1†". by iApply "H2†".
Qed.

Lemma lft_intersect_mono κ1 κ1' κ2 κ2' :
  κ1 ⊑ κ1' -∗ κ2 ⊑ κ2' -∗ κ1 ⊓ κ2 ⊑ κ1' ⊓ κ2'.
Proof.
  iIntros "#H1 #H2". iApply (lft_incl_glb with "[]").
  - iApply (lft_incl_trans with "[] H1"). iApply lft_intersect_incl_l.
  - iApply (lft_incl_trans with "[] H2"). iApply lft_intersect_incl_r.
Qed.

(** Basic rules about borrows *)
Lemma raw_bor_iff i P P' : ▷ □ (P ↔ P') -∗ raw_bor i P -∗ raw_bor i P'.
Proof.
  iIntros "#HPP' HP". unfold raw_bor. iDestruct "HP" as (s) "[HiP HP]".
  iExists s. iFrame. iDestruct "HP" as (P0) "[#Hiff ?]". iExists P0. iFrame.
  iNext. iModIntro. iSplit; iIntros.
  by iApply "HPP'"; iApply "Hiff". by iApply "Hiff"; iApply "HPP'".
Qed.

Lemma idx_bor_iff κ i P P' : ▷ □ (P ↔ P') -∗ &{κ,i}P -∗ &{κ,i}P'.
Proof.
  unfold idx_bor. iIntros "#HPP' [$ HP]". iDestruct "HP" as (P0) "[#HP0P Hs]".
  iExists P0. iFrame. iNext. iModIntro. iSplit; iIntros.
  by iApply "HPP'"; iApply "HP0P". by iApply "HP0P"; iApply "HPP'".
Qed.

Lemma bor_unfold_idx κ P : &{κ}P ⊣⊢ ∃ i, &{κ,i}P ∗ idx_bor_own 1 i.
Proof.
  rewrite /bor /raw_bor /idx_bor /bor_idx. iSplit.
  - iDestruct 1 as (κ') "[? Hraw]". iDestruct "Hraw" as (s) "[??]".
    iExists (κ', s). by iFrame.
  - iDestruct 1 as ([κ' s]) "[[??]?]".
    iExists κ'. iFrame. iExists s. by iFrame.
Qed.

Lemma bor_iff κ P P' : ▷ □ (P ↔ P') -∗ &{κ}P -∗ &{κ}P'.
Proof.
  rewrite !bor_unfold_idx. iIntros "#HPP' HP". iDestruct "HP" as (i) "[??]".
  iExists i. iFrame. by iApply (idx_bor_iff with "HPP'").
Qed.

Lemma bor_shorten κ κ' P : κ ⊑ κ' -∗ &{κ'}P -∗ &{κ}P.
Proof.
  rewrite /bor. iIntros "#Hκκ'". iDestruct 1 as (i) "[#? ?]".
  iExists i. iFrame. by iApply (lft_incl_trans with "Hκκ'").
Qed.

Lemma idx_bor_shorten κ κ' i P : κ ⊑ κ' -∗ &{κ',i} P -∗ &{κ,i} P.
Proof.
  rewrite /idx_bor. iIntros "#Hκκ' [#? $]". by iApply (lft_incl_trans with "Hκκ'").
Qed.

Lemma raw_bor_inI I κ P :
  own_ilft_auth I -∗ raw_bor κ P -∗ ⌜is_Some (I !! κ)⌝.
Proof.
  iIntros "HI Hbor". rewrite /raw_bor /idx_bor_own. iDestruct "Hbor" as (?) "[Hbor _]".
  iApply (own_bor_auth with "HI Hbor").
Qed.

(* Inheritance *)
Lemma lft_inh_extend E κ P Q :
  ↑inhN ⊆ E →
  ▷ lft_inh κ false Q ={E}=∗ ▷ lft_inh κ false (P ∗ Q) ∗
     (* This states that κ will henceforth always be allocated.
        That's not at all related to extending the inheritance,
        but it's useful to have it here. *)
     (∀ I, own_ilft_auth I -∗ ⌜is_Some (I !! κ)⌝) ∗
     (* This is the extraction: Always in the future, we can get
        ▷ P from whatever lft_inh is at the time. *)
     (∀ Q', ▷ lft_inh κ true Q' ={E}=∗ ∃ Q'',
            ▷ ▷ (Q' ≡ (P ∗ Q'')) ∗ ▷ P ∗ ▷ lft_inh κ true Q'').
Proof.
  rewrite {1}/lft_inh. iDestruct 1 as (PE) "[>HE Hbox]".
  iMod (slice_insert_empty _ _ true _ P with "Hbox")
    as (γE) "(% & #Hslice & Hbox)".
  iMod (own_inh_update with "HE") as "[HE HE◯]".
  { by eapply auth_update_alloc, (gset_disj_alloc_empty_local_update _ {[γE]}),
      disjoint_singleton_l, lookup_gset_to_gmap_None. }
  iModIntro. iSplitL "Hbox HE".
  { iNext. rewrite /lft_inh. iExists ({[γE]} ∪ PE).
    rewrite gset_to_gmap_union_singleton. iFrame. }
  clear dependent PE. rewrite -(left_id ε op (◯ GSet {[γE]})).
  iDestruct "HE◯" as "[HE◯' HE◯]". iSplitL "HE◯'".
  { iIntros (I) "HI". iApply (own_inh_auth with "HI HE◯'"). }
  iIntros (Q'). rewrite {1}/lft_inh. iDestruct 1 as (PE) "[>HE Hbox]".
  iDestruct (own_inh_valid_2 with "HE HE◯")
    as %[Hle%gset_disj_included _]%auth_both_valid_discrete.
  iMod (own_inh_update_2 with "HE HE◯") as "HE".
  { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
  iMod (slice_delete_full _ _ true with "Hslice Hbox")
    as (Q'') "($ & #? & Hbox)"; first by solve_ndisj.
  { rewrite lookup_gset_to_gmap_Some. set_solver. }
  iModIntro. iExists Q''. iSplit; first done.
  iNext. rewrite /lft_inh. iExists (PE ∖ {[γE]}). iFrame "HE".
  rewrite {1}(union_difference_L {[ γE ]} PE); last set_solver.
  rewrite gset_to_gmap_union_singleton delete_insert // lookup_gset_to_gmap_None.
  set_solver.
Qed.

Lemma lft_inh_kill E κ Q :
  ↑inhN ⊆ E →
  lft_inh κ false Q ∗ ▷ Q ={E}=∗ lft_inh κ true Q.
Proof.
  rewrite /lft_inh. iIntros (?) "[Hinh HQ]".
  iDestruct "Hinh" as (E') "[Hinh Hbox]".
  iMod (box_fill with "Hbox HQ") as "?"=>//.
  rewrite fmap_gset_to_gmap. iModIntro. iExists E'. by iFrame.
Qed.

(* View shifts *)
Lemma lft_vs_frame κ Pb Pi P :
  lft_vs κ Pb Pi -∗ lft_vs κ (P ∗ Pb) (P ∗ Pi).
Proof.
  rewrite !lft_vs_unfold. iDestruct 1 as (n) "[Hcnt Hvs]".
  iExists n. iFrame "Hcnt". iIntros (I'') "Hinv [$ HPb] H†".
  iApply ("Hvs" $! I'' with "Hinv HPb H†").
Qed.

Lemma lft_vs_cons κ Pb Pb' Pi :
  (▷ Pb'-∗ [†κ] ={↑lft_userN ∪ ↑borN}=∗ ▷ Pb) -∗
  lft_vs κ Pb Pi -∗ lft_vs κ Pb' Pi.
Proof.
  iIntros "Hcons Hvs". rewrite !lft_vs_unfold.
  iDestruct "Hvs" as (n) "[Hn● Hvs]". iExists n. iFrame "Hn●".
  iIntros (I). rewrite {1}lft_vs_inv_unfold.
  iIntros "(Hinv & Hκs) HPb #Hκ†".
  iMod ("Hcons" with "HPb Hκ†") as "HPb".
  iApply ("Hvs" $! I with "[Hinv Hκs] HPb Hκ†").
  rewrite lft_vs_inv_unfold. by iFrame.
Qed.
End primitive.
