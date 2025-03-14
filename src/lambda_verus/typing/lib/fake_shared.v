From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section fake_shared.
  Context `{!typeG Σ}.

  Definition fake_shared_box : val :=
    fn: ["x"] := Skip ;; return: ["x"].

  Lemma fake_shared_box_type ty :
    typed_val fake_shared_box
      (fn(∀ '(α, β), ∅; &shr{α}(&shr{β} ty)) → &shr{α}(box ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #TIME #HE Hna HL Hk HT".
    rewrite tctx_interp_singleton tctx_hasty_val.
    iDestruct "HT" as (depth) "[#Hdepth HT]".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    iAssert (▷ (own_ptr 1 (&shr{α}(box ty))).(ty_own) depth tid [x])%I with "[HT]" as "HT".
    { destruct x as [[|l|]|], depth as [|depth]=>//=. iDestruct "HT" as "[H $]".
      iNext. iDestruct "H" as ([|[[]|][]]) "[H↦ H]"; try done.
      iExists _. iFrame. iDestruct "H" as (vl) "[#Hf H]".
      iNext. destruct vl as [|[[|l'|]|][]]; try done. iExists l'. iSplit.
      { iApply frac_bor_iff; last done. iIntros "!>!> *".
        rewrite heap_mapsto_vec_singleton. iSplit; auto. }
      by iApply ty_shr_mono. }
    do 2 wp_seq.
    iApply (type_type [] _ _ [ x ◁ box (&shr{α}(box ty)) ]
            with "[] LFT TIME [] Hna HL Hk [HT]"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val. auto. }
    { by rewrite /elctx_interp. }
    iApply type_jump; simpl; solve_typing.
  Qed.

  Definition fake_shared_uniq : val :=
    fn: ["x"] := Skip ;; return: ["x"].

  Lemma fake_shared_uniq_type ty :
    typed_val fake_shared_box
      (fn(∀ '(α, β), ∅; &shr{α}(&shr{β} ty)) → &shr{α}(&uniq{β} ty)).
  Proof.
    intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>".
      iIntros ([α β] ϝ ret arg). inv_vec arg=>x. simpl_subst.
    iIntros (tid) "#LFT #TIME #HE Hna HL Hk HT".
    rewrite tctx_interp_singleton tctx_hasty_val.
    iDestruct "HT" as (depth) "[#Hdepth HT]".
    iDestruct (lctx_lft_incl_incl α β with "HL HE") as "#Hαβ"; [solve_typing..|].
    (* FIXME: WTF, using &uniq{β} here does not work. *)
    iAssert (▷ (own_ptr 1 (&shr{α} (uniq_bor β ty))).(ty_own) depth tid [x])%I with "[HT]" as "HT".
    { destruct x as [[|l|]|], depth as [|depth]=>//=. iDestruct "HT" as "[H $]".
      iNext. iDestruct "H" as ([|[[]|][]]) "[H↦ H]"; try done.
      iExists _. iFrame. iDestruct "H" as (vl) "[#Hf H]".
      iNext. destruct vl as [|[[|l'|]|][]]; try done. iExists l'. iSplit.
      { iApply frac_bor_iff; last done. iIntros "!>!> *".
        rewrite heap_mapsto_vec_singleton. iSplit; auto. }
      by iApply ty_shr_mono. }
    do 2 wp_seq.
    iApply (type_type [] _ _ [ x ◁ box (&shr{α}(&uniq{β} ty)) ]
            with "[] LFT TIME [] Hna HL Hk [HT]"); last first.
    { rewrite tctx_interp_singleton tctx_hasty_val. auto. }
    { by rewrite /elctx_interp. }
    iApply type_jump; simpl; solve_typing.
  Qed.
End fake_shared.
