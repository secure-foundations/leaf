From iris.algebra Require Import auth cmra functions gmap dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From lrust.util Require Import discrete_fun.
From lrust.prophecy Require Import prophecy.
From lrust.lifetime Require Import lifetime_sig.

Implicit Type (𝔄i: syn_typei) (𝔄: syn_type).

(** * Camera for Unique Borrowing *)

Local Definition uniq_itemR 𝔄i := dfrac_agreeR (leibnizO (proph 𝔄i * nat)).
Local Definition uniq_gmapUR 𝔄i := gmapUR positive (uniq_itemR 𝔄i).
Local Definition uniq_smryUR := discrete_funUR uniq_gmapUR.
Definition uniqUR: ucmra := authUR uniq_smryUR.

Local Definition item {𝔄i} q vπ d : uniq_itemR 𝔄i :=
  @to_frac_agree (leibnizO _) q (vπ, d).
Local Definition line ξ q vπ d : uniq_smryUR :=
  .{[ξ.(pv_ty) := {[ξ.(pv_id) := item q vπ d]}]}.
Local Definition add_line ξ q vπ d (S: uniq_smryUR) : uniq_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := item q vπ d]> (S ξ.(pv_ty))]> S.

Definition uniqΣ: gFunctors := #[GFunctor uniqUR].
Class uniqPreG Σ := UniqPreG { uniq_preG_inG :> inG Σ uniqUR }.
Class uniqG Σ := UniqG { uniq_inG :> uniqPreG Σ; uniq_name: gname }.
Global Instance subG_uniqPreG Σ : subG uniqΣ Σ → uniqPreG Σ.
Proof. solve_inG. Qed.

Definition uniqN: namespace := lft_userN .@ "uniq".

(** * Iris Propositions *)

Section defs.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ}.

(** Unique Reference Context *)
Definition uniq_inv: iProp Σ := ∃S, own uniq_name (● S).
Definition uniq_ctx: iProp Σ := inv uniqN uniq_inv.

Local Definition own_line ξ q vπ d := own uniq_name (◯ line ξ q vπ d).

(** Value Observer *)
Definition val_obs (ξ: proph_var) (vπ: proph ξ.(pv_ty)) (d: nat) : iProp Σ :=
  own_line ξ (1/2) vπ d.

(** Prophecy Controller *)
Local Definition val_obs2 ξ vπ d : iProp Σ := own_line ξ 1 vπ d.
Definition proph_ctrl (ξ: proph_var) (vπ: proph ξ.(pv_ty)) (d: nat) : iProp Σ :=
  (val_obs ξ vπ d ∗ 1:[ξ]) ∨ ((∃vπ' d', val_obs2 ξ vπ' d') ∗ (.$ ξ) :== vπ).
End defs.

Notation ".VO[ ξ ]" := (val_obs ξ) (at level 5, format ".VO[ ξ ]") : bi_scope.
Local Notation ".VO2[ ξ ]" := (val_obs2 ξ)
  (at level 5, format ".VO2[ ξ ]") : bi_scope.
Notation ".PC[ ξ ]" := (proph_ctrl ξ)
  (at level 5, format ".PC[ ξ ]") : bi_scope.

(** * Lemmas *)

Definition prval_to_inh {𝔄} (vπ: proph 𝔄) : inh_syn_type 𝔄 :=
  to_inh_syn_type (vπ inhabitant).

Section lemmas.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ}.

Global Instance uniq_ctx_persistent : Persistent uniq_ctx := _.
Global Instance val_obs_timeless ξ vπ d : Timeless (.VO[ξ] vπ d) := _.

Local Lemma own_line_agree ξ q q' vπ d vπ' d' :
  own_line ξ q vπ d -∗ own_line ξ q' vπ' d' -∗ ⌜(q + q' ≤ 1)%Qp ∧ vπ = vπ' ∧ d = d'⌝.
Proof.
  iIntros "line line'". iDestruct (own_valid_2 with "line line'") as %Val.
  iPureIntro. move: Val.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid.
  by move/frac_agree_op_valid=> [?[=??]].
Qed.

Local Lemma vo_vo2 ξ vπ d : .VO[ξ] vπ d ∗ .VO[ξ] vπ d ⊣⊢ .VO2[ξ] vπ d.
Proof.
  by rewrite -own_op -auth_frag_op discrete_fun_singleton_op singleton_op /item
    -frac_agree_op Qp_half_half.
Qed.

Local Lemma vo_pc ξ vπ d vπ' d' :
  .VO[ξ] vπ d -∗ .PC[ξ] vπ' d' -∗ ⌜vπ = vπ'⌝ ∗ ⌜d = d'⌝ ∗ .VO2[ξ] vπ d ∗ 1:[ξ].
Proof.
  iIntros "Vo [[Vo' ?]|[(%&%& Vo2) _]]";
  [|by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[_[->->]].
  do 2 (iSplit; [done|]). rewrite -vo_vo2. iFrame.
Qed.

(** Initialization *)

Lemma uniq_init `{!uniqPreG Σ} E :
  ↑uniqN ⊆ E → ⊢ |={E}=> ∃_: uniqG Σ, uniq_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "●ε"; [by apply auth_auth_valid|].
  set IUniqG := UniqG Σ _ γ. iExists IUniqG.
  iMod (inv_alloc _ _ uniq_inv with "[●ε]") as "?"; by [iExists ε|].
Qed.

Lemma uniq_intro {𝔄} (vπ: proph 𝔄) d E :
  ↑prophN ∪ ↑uniqN ⊆ E → proph_ctx -∗ uniq_ctx ={E}=∗ ∃ξi,
    let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in .VO[ξ] vπ d ∗ .PC[ξ] vπ d.
Proof.
  iIntros (?) "PROPH ?". iInv uniqN as (S) ">●S".
  set 𝔄i := 𝔄 ↾ prval_to_inh vπ. set I := dom (gset _) (S 𝔄i).
  iMod (proph_intro 𝔄i I with "PROPH") as (ξi NIn) "ξ"; [by solve_ndisj|].
  set ξ := PrVar 𝔄i ξi. set S' := add_line ξ 1 vπ d S.
  move: NIn=> /not_elem_of_dom ?.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ 1 vπ d) with "●S") as "[? Vo2]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitR "Vo2 ξ"; [by iExists S'|]. iModIntro. iExists ξi.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_strip_later ξ vπ d vπ' d' :
  ▷ .VO[ξ] vπ d -∗ ▷ .PC[ξ] vπ' d' -∗
    ◇ (⌜vπ = vπ'⌝ ∗ ⌜d = d'⌝ ∗ .VO[ξ] vπ d ∗ .PC[ξ] vπ' d').
Proof.
  iIntros ">Vo [>[Vo' ?]|[>(%&%& Vo2) _]]";
  [|by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[_[->->]]. iModIntro.
  do 2 (iSplit; [done|]). iSplitL "Vo"; [done|]. iLeft. by iSplitL "Vo'".
Qed.

Lemma uniq_agree ξ vπ d vπ' d' :
  .VO[ξ] vπ d -∗ .PC[ξ] vπ' d' -∗ ⌜vπ = vπ' ∧ d = d'⌝.
Proof.
  iIntros "Vo Pc". by iDestruct (vo_pc with "Vo Pc") as (->->) "?".
Qed.

Lemma uniq_proph_tok ξ vπ d vπ' d' :
  .VO[ξ] vπ d -∗ .PC[ξ] vπ' d' -∗ .VO[ξ] vπ d ∗ 1:[ξ] ∗ (1:[ξ] -∗ .PC[ξ] vπ' d').
Proof.
  iIntros "Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->->) "[Vo2 $]".
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iIntros "?". iLeft. iFrame.
Qed.

Lemma uniq_update ξ vπ'' d'' vπ d vπ' d' E : ↑uniqN ⊆ E →
  uniq_ctx -∗ .VO[ξ] vπ d -∗ .PC[ξ] vπ' d' ={E}=∗ .VO[ξ] vπ'' d'' ∗ .PC[ξ] vπ'' d''.
Proof.
  iIntros (?) "? Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->->) "[Vo2 ξ]".
  iInv uniqN as (S) ">●S". set S' := add_line ξ 1 vπ'' d'' S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ 1 vπ'' d'') with "●S Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
    singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2 ξ"; [by iExists S'|]. iModIntro.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_resolve ξ ζl q vπ d vπ' d' E : ↑prophN ⊆ E → vπ ./ ζl →
  proph_ctx -∗ .VO[ξ] vπ d -∗ .PC[ξ] vπ' d' -∗ q:+[ζl] ={E}=∗
    ⟨π, π ξ = vπ π⟩ ∗ .PC[ξ] vπ d ∗ q:+[ζl].
Proof.
  iIntros (??) "PROPH Vo Pc ζl". iDestruct (vo_pc with "Vo Pc") as (<-<-) "[? ξ]".
  iMod (proph_resolve with "PROPH ξ ζl") as "[#? $]"; [done|done|].
  iModIntro. iSplitR; [done|]. iRight. iSplitL; [by iExists vπ, d|].
  by iApply proph_eqz_obs.
Qed.

Lemma uniq_preresolve ξ ζl uπ q vπ d vπ'' d'' E : ↑prophN ⊆ E → uπ ./ ζl →
  proph_ctx -∗ .VO[ξ] vπ d -∗ .PC[ξ] vπ'' d'' -∗ q:+[ζl] ={E}=∗
    ⟨π, π ξ = uπ π⟩ ∗ q:+[ζl] ∗ (∀vπ' d', uπ :== vπ' -∗ .PC[ξ] vπ' d').
Proof.
  iIntros (??) "PROPH Vo Pc ζl". iDestruct (vo_pc with "Vo Pc") as (<-<-) "[? ξ]".
  iMod (proph_resolve with "PROPH ξ ζl") as "[#Obs $]"; [done|done|].
  iModIntro. iSplitR; [done|]. iIntros (??) "Eqz". iRight.
  iSplitR "Eqz"; [by iExists vπ, d|].
  by iDestruct (proph_eqz_modify with "Obs Eqz") as "?".
Qed.

Lemma proph_ctrl_eqz ξ vπ d : proph_ctx -∗ .PC[ξ] vπ d -∗ (.$ ξ) :== vπ.
Proof. iIntros "#? [[_ ?]|[_ ?]]"; by [iApply proph_eqz_token|]. Qed.
End lemmas.

Global Opaque uniq_ctx val_obs proph_ctrl.
