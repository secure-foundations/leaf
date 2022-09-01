From iris.algebra Require Import lib.excl_auth gmap agree.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From iris.prelude Require Import options.
Import uPred.

(** The CMRAs we need. *)
Class boxG Σ :=
  boxG_inG :> inG Σ (prodR
    (excl_authR boolO)
    (optionR (agreeR (laterO (iPropO Σ))))).

Definition boxΣ : gFunctors := #[ GFunctor (excl_authR boolO *
                                            optionRF (agreeRF (▶ ∙)) ) ].

Global Instance subG_boxΣ Σ : subG boxΣ Σ → boxG Σ.
Proof. solve_inG. Qed.

Section box_defs.
  Context `{!invGS Σ, !boxG Σ} (N : namespace).

  Definition slice_name := gname.

  Definition box_own_auth (γ : slice_name) (a : excl_authR boolO) : iProp Σ :=
    own γ (a, None).

  Definition box_own_prop (γ : slice_name) (P : iProp Σ) : iProp Σ :=
    own γ (ε, Some (to_agree (Next P))).

  Definition slice_inv (γ : slice_name) (P : iProp Σ) : iProp Σ :=
    ∃ b, box_own_auth γ (●E b) ∗ if b then P else True.

  Definition slice (γ : slice_name) (P : iProp Σ) : iProp Σ :=
    box_own_prop γ P ∗ inv N (slice_inv γ P).

  Definition box (f : gmap slice_name bool) (P : iProp Σ) : iProp Σ :=
    ∃ Φ : slice_name → iProp Σ,
      ▷ (P ≡ [∗ map] γ ↦ _ ∈ f, Φ γ) ∗
      [∗ map] γ ↦ b ∈ f, box_own_auth γ (◯E b) ∗ box_own_prop γ (Φ γ) ∗
                         inv N (slice_inv γ (Φ γ)).
End box_defs.

Global Instance: Params (@box_own_prop) 3 := {}.
Global Instance: Params (@slice_inv) 3 := {}.
Global Instance: Params (@slice) 5 := {}.
Global Instance: Params (@box) 5 := {}.

Section box.
Context `{!invGS Σ, !boxG Σ} (N : namespace).
Implicit Types P Q : iProp Σ.

Global Instance box_own_prop_ne γ : NonExpansive (box_own_prop γ).
Proof. solve_proper. Qed.
Global Instance box_own_prop_contractive γ : Contractive (box_own_prop γ).
Proof. solve_contractive. Qed.

Global Instance box_inv_ne γ : NonExpansive (slice_inv γ).
Proof. solve_proper. Qed.

Global Instance slice_ne γ : NonExpansive (slice N γ).
Proof. solve_proper. Qed.
Global Instance slice_contractive γ : Contractive (slice N γ).
Proof. solve_contractive. Qed.
Global Instance slice_proper γ : Proper ((≡) ==> (≡)) (slice N γ).
Proof. apply ne_proper, _. Qed.

Global Instance slice_persistent γ P : Persistent (slice N γ P).
Proof. apply _. Qed.

Global Instance box_contractive f : Contractive (box N f).
Proof. solve_contractive. Qed.
Global Instance box_ne f : NonExpansive (box N f).
Proof. apply (contractive_ne _). Qed.
Global Instance box_proper f : Proper ((≡) ==> (≡)) (box N f).
Proof. apply ne_proper, _. Qed.

Lemma box_own_auth_agree γ b1 b2 :
  box_own_auth γ (●E b1) ∗ box_own_auth γ (◯E b2) ⊢ ⌜b1 = b2⌝.
Proof.
  rewrite /box_own_prop -own_op own_valid prod_validI /= and_elim_l.
  by iDestruct 1 as %?%excl_auth_agree_L.
Qed.

Lemma box_own_auth_update γ b1 b2 b3 :
  box_own_auth γ (●E b1) ∗ box_own_auth γ (◯E b2)
  ==∗ box_own_auth γ (●E b3) ∗ box_own_auth γ (◯E b3).
Proof.
  rewrite /box_own_auth -!own_op. apply own_update, prod_update; last done.
  apply excl_auth_update.
Qed.

Lemma box_own_agree γ Q1 Q2 :
  box_own_prop γ Q1 ∗ box_own_prop γ Q2 ⊢ ▷ (Q1 ≡ Q2).
Proof.
  rewrite /box_own_prop -own_op own_valid prod_validI /= and_elim_r.
  by rewrite option_validI /= agree_validI agree_equivI later_equivI /=.
Qed.

Lemma box_alloc : ⊢ box N ∅ True.
Proof.
  iIntros. iExists (λ _, True)%I. by rewrite !big_opM_empty.
Qed.

Lemma slice_insert_empty E q f Q P :
  ▷?q box N f P ={E}=∗ ∃ γ, ⌜f !! γ = None⌝ ∗
    slice N γ Q ∗ ▷?q box N (<[γ:=false]> f) (Q ∗ P).
Proof.
  iDestruct 1 as (Φ) "[#HeqP Hf]".
  iMod (own_alloc_cofinite (●E false ⋅ ◯E false,
    Some (to_agree (Next Q))) (dom _ f))
    as (γ) "[Hdom Hγ]"; first by (split; [apply auth_both_valid_discrete|]).
  rewrite pair_split. iDestruct "Hγ" as "[[Hγ Hγ'] #HγQ]".
  iDestruct "Hdom" as % ?%not_elem_of_dom.
  iMod (inv_alloc N _ (slice_inv γ Q) with "[Hγ]") as "#Hinv".
  { iNext. iExists false; eauto. }
  iModIntro; iExists γ; repeat iSplit; auto.
  iNext. iExists (<[γ:=Q]> Φ); iSplit.
  - iNext. iRewrite "HeqP". by rewrite big_opM_fn_insert'.
  - rewrite (big_opM_fn_insert (λ _ _ P',  _ ∗ _ _ P' ∗ _ _ (_ _ P')))%I //.
    iFrame; eauto.
Qed.

Lemma slice_delete_empty E q f P Q γ :
  ↑N ⊆ E →
  f !! γ = Some false →
  slice N γ Q -∗ ▷?q box N f P ={E}=∗ ∃ P',
    ▷?q (▷ (P ≡ (Q ∗ P')) ∗ box N (delete γ f) P').
Proof.
  iIntros (??) "[#HγQ Hinv] H". iDestruct "H" as (Φ) "[#HeqP Hf]".
  iExists ([∗ map] γ'↦_ ∈ delete γ f, Φ γ')%I.
  iInv N as (b) "[>Hγ _]".
  iDestruct (big_sepM_delete _ f _ false with "Hf")
    as "[[>Hγ' #[HγΦ ?]] ?]"; first done.
  iDestruct (box_own_auth_agree γ b false with "[-]") as %->; first by iFrame.
  iModIntro. iSplitL "Hγ"; first iExists false; eauto.
  iModIntro. iNext. iSplit.
  - iDestruct (box_own_agree γ Q (Φ γ) with "[#]") as "HeqQ"; first by eauto.
    iNext. iRewrite "HeqP". iRewrite "HeqQ". by rewrite -big_opM_delete.
  - iExists Φ; eauto.
Qed.

Lemma slice_fill E q f γ P Q :
  ↑N ⊆ E →
  f !! γ = Some false →
  slice N γ Q -∗ ▷ Q -∗ ▷?q box N f P ={E}=∗ ▷?q box N (<[γ:=true]> f) P.
Proof.
  iIntros (??) "#[HγQ Hinv] HQ H"; iDestruct "H" as (Φ) "[#HeqP Hf]".
  iInv N as (b') "[>Hγ _]".
  iDestruct (big_sepM_delete _ f _ false with "Hf")
    as "[[>Hγ' #[HγΦ Hinv']] ?]"; first done.
  iMod (box_own_auth_update γ b' false true with "[$Hγ $Hγ']") as "[Hγ Hγ']".
  iModIntro. iSplitL "Hγ HQ"; first (iNext; iExists true; by iFrame).
  iModIntro; iNext; iExists Φ; iSplit.
  - by rewrite big_opM_insert_override.
  - rewrite -insert_delete_insert big_opM_insert ?lookup_delete //.
    iFrame; eauto.
Qed.

Lemma slice_empty E q f P Q γ :
  ↑N ⊆ E →
  f !! γ = Some true →
  slice N γ Q -∗ ▷?q box N f P ={E}=∗ ▷ Q ∗ ▷?q box N (<[γ:=false]> f) P.
Proof.
  iIntros (??) "#[HγQ Hinv] H"; iDestruct "H" as (Φ) "[#HeqP Hf]".
  iInv N as (b) "[>Hγ HQ]".
  iDestruct (big_sepM_delete _ f with "Hf")
    as "[[>Hγ' #[HγΦ Hinv']] ?]"; first done.
  iDestruct (box_own_auth_agree γ b true with "[-]") as %->; first by iFrame.
  iFrame "HQ".
  iMod (box_own_auth_update γ with "[$Hγ $Hγ']") as "[Hγ Hγ']".
  iModIntro. iSplitL "Hγ"; first (iNext; iExists false; by repeat iSplit).
  iModIntro; iNext; iExists Φ; iSplit.
  - by rewrite big_opM_insert_override.
  - rewrite -insert_delete_insert big_opM_insert ?lookup_delete //.
    iFrame; eauto.
Qed.

Lemma slice_insert_full E q f P Q :
  ↑N ⊆ E →
  ▷ Q -∗ ▷?q box N f P ={E}=∗ ∃ γ, ⌜f !! γ = None⌝ ∗
    slice N γ Q ∗ ▷?q box N (<[γ:=true]> f) (Q ∗ P).
Proof.
  iIntros (?) "HQ Hbox".
  iMod (slice_insert_empty with "Hbox") as (γ ?) "[#Hslice Hbox]".
  iExists γ. iFrame "%#". iMod (slice_fill with "Hslice HQ Hbox"); first done.
  - by apply lookup_insert.
  - by rewrite insert_insert.
Qed.

Lemma slice_delete_full E q f P Q γ :
  ↑N ⊆ E →
  f !! γ = Some true →
  slice N γ Q -∗ ▷?q box N f P ={E}=∗
  ∃ P', ▷ Q ∗ ▷?q ▷ (P ≡ (Q ∗ P')) ∗ ▷?q box N (delete γ f) P'.
Proof.
  iIntros (??) "#Hslice Hbox".
  iMod (slice_empty with "Hslice Hbox") as "[$ Hbox]"; try done.
  iMod (slice_delete_empty with "Hslice Hbox") as (P') "[Heq Hbox]"; first done.
  { by apply lookup_insert. }
  iExists P'. iFrame. rewrite -insert_delete_insert delete_insert ?lookup_delete //.
Qed.

Lemma box_fill E f P :
  ↑N ⊆ E →
  box N f P -∗ ▷ P ={E}=∗ box N (const true <$> f) P.
Proof.
  iIntros (?) "H HP"; iDestruct "H" as (Φ) "[#HeqP Hf]".
  iExists Φ; iSplitR; first by rewrite big_opM_fmap.
  iEval (rewrite internal_eq_iff later_iff big_sepM_later) in "HeqP".
  iDestruct ("HeqP" with "HP") as "HP".
  iCombine "Hf" "HP" as "Hf".
  rewrite -big_sepM_sep big_opM_fmap; iApply (big_sepM_fupd _ _ f).
  iApply (@big_sepM_impl with "Hf").
  iIntros "!>" (γ b' ?) "[(Hγ' & #$ & #$) HΦ]".
  iInv N as (b) "[>Hγ _]".
  iMod (box_own_auth_update γ with "[Hγ Hγ']") as "[Hγ $]"; first by iFrame.
  iModIntro. iSplitL; last done. iNext; iExists true. iFrame.
Qed.

Lemma box_empty E f P :
  ↑N ⊆ E →
  map_Forall (λ _, (true =.)) f →
  box N f P ={E}=∗ ▷ P ∗ box N (const false <$> f) P.
Proof.
  iDestruct 1 as (Φ) "[#HeqP Hf]".
  iAssert (([∗ map] γ↦b ∈ f, ▷ Φ γ) ∗
    [∗ map] γ↦b ∈ f, box_own_auth γ (◯E false) ∗  box_own_prop γ (Φ γ) ∗
      inv N (slice_inv γ (Φ γ)))%I with "[> Hf]" as "[HΦ ?]".
  { rewrite -big_sepM_sep -big_sepM_fupd. iApply (@big_sepM_impl with "[$Hf]").
    iIntros "!>" (γ b ?) "(Hγ' & #HγΦ & #Hinv)".
    assert (true = b) as <- by eauto.
    iInv N as (b) "[>Hγ HΦ]".
    iDestruct (box_own_auth_agree γ b true with "[-]") as %->; first by iFrame.
    iMod (box_own_auth_update γ true true false with "[$Hγ $Hγ']") as "[Hγ $]".
    iModIntro. iSplitL "Hγ"; first (iNext; iExists false; iFrame; eauto).
    iFrame "HγΦ Hinv". by iApply "HΦ". }
  iModIntro; iSplitL "HΦ".
  - rewrite internal_eq_iff later_iff big_sepM_later. by iApply "HeqP".
  - iExists Φ; iSplit; by rewrite big_opM_fmap.
Qed.

Lemma slice_iff E q f P Q Q' γ b :
  ↑N ⊆ E → f !! γ = Some b →
  ▷ □ (Q ↔ Q') -∗ slice N γ Q -∗ ▷?q box N f P ={E}=∗ ∃ γ' P',
    ⌜delete γ f !! γ' = None⌝ ∗ ▷?q ▷ □ (P ↔ P') ∗
    slice N γ' Q' ∗ ▷?q box N (<[γ' := b]>(delete γ f)) P'.
Proof.
  iIntros (??) "#HQQ' #Hs Hb". destruct b.
  - iMod (slice_delete_full with "Hs Hb") as (P') "(HQ & Heq & Hb)"; try done.
    iDestruct ("HQQ'" with "HQ") as "HQ'".
    iMod (slice_insert_full with "HQ' Hb") as (γ' ?) "[#Hs' Hb]"; try done.
    iExists γ', _. iIntros "{$∗ $# $%} !>". do 2 iNext. iRewrite "Heq".
    iIntros "!>". by iSplit; iIntros "[? $]"; iApply "HQQ'".
  - iMod (slice_delete_empty with "Hs Hb") as (P') "(Heq & Hb)"; try done.
    iMod (slice_insert_empty with "Hb") as (γ' ?) "[#Hs' Hb]"; try done.
    iExists γ', (Q' ∗ P')%I. iIntros "{$∗ $# $%} !>".  do 2 iNext. iRewrite "Heq".
    iIntros "!>". by iSplit; iIntros "[? $]"; iApply "HQQ'".
Qed.

Lemma slice_split E q f P Q1 Q2 γ b :
  ↑N ⊆ E → f !! γ = Some b →
  slice N γ (Q1 ∗ Q2) -∗ ▷?q box N f P ={E}=∗ ∃ γ1 γ2,
    ⌜delete γ f !! γ1 = None⌝ ∗ ⌜delete γ f !! γ2 = None⌝ ∗ ⌜γ1 ≠ γ2⌝ ∗
    slice N γ1 Q1 ∗ slice N γ2 Q2 ∗ ▷?q box N (<[γ2 := b]>(<[γ1 := b]>(delete γ f))) P.
Proof.
  iIntros (??) "#Hslice Hbox". destruct b.
  - iMod (slice_delete_full with "Hslice Hbox") as (P') "([HQ1 HQ2] & Heq & Hbox)"; try done.
    iMod (slice_insert_full with "HQ1 Hbox") as (γ1 ?) "[#Hslice1 Hbox]"; first done.
    iMod (slice_insert_full with "HQ2 Hbox") as (γ2 ?) "[#Hslice2 Hbox]"; first done.
    iExists γ1, γ2. iIntros "{$% $#} !>". iSplit; last iSplit; try iPureIntro.
    { by eapply lookup_insert_None. }
    { by apply (lookup_insert_None (delete γ f) γ1 γ2 true). }
    iNext. iApply (internal_eq_rewrite_contractive _ _ (box _ _) with "[Heq] Hbox").
    iNext. iRewrite "Heq". iPureIntro. by rewrite assoc (comm _ Q2).
  - iMod (slice_delete_empty with "Hslice Hbox") as (P') "[Heq Hbox]"; try done.
    iMod (slice_insert_empty with "Hbox") as (γ1 ?) "[#Hslice1 Hbox]".
    iMod (slice_insert_empty with "Hbox") as (γ2 ?) "[#Hslice2 Hbox]".
    iExists γ1, γ2. iIntros "{$% $#} !>". iSplit; last iSplit; try iPureIntro.
    { by eapply lookup_insert_None. }
    { by apply (lookup_insert_None (delete γ f) γ1 γ2 false). }
    iNext. iApply (internal_eq_rewrite_contractive _ _ (box _ _) with "[Heq] Hbox").
    iNext. iRewrite "Heq". iPureIntro. by rewrite assoc (comm _ Q2).
Qed.

Lemma slice_combine E q f P Q1 Q2 γ1 γ2 b :
  ↑N ⊆ E → γ1 ≠ γ2 → f !! γ1 = Some b → f !! γ2 = Some b →
  slice N γ1 Q1 -∗ slice N γ2 Q2 -∗ ▷?q box N f P ={E}=∗ ∃ γ,
    ⌜delete γ2 (delete γ1 f) !! γ = None⌝ ∗ slice N γ (Q1 ∗ Q2) ∗
    ▷?q box N (<[γ := b]>(delete γ2 (delete γ1 f))) P.
Proof.
  iIntros (????) "#Hslice1 #Hslice2 Hbox". destruct b.
  - iMod (slice_delete_full with "Hslice1 Hbox") as (P1) "(HQ1 & Heq1 & Hbox)"; try done.
    iMod (slice_delete_full with "Hslice2 Hbox") as (P2) "(HQ2 & Heq2 & Hbox)"; first done.
    { by simplify_map_eq. }
    iMod (slice_insert_full _ _ _ _ (Q1 ∗ Q2) with "[$HQ1 $HQ2] Hbox")
      as (γ ?) "[#Hslice Hbox]"; first done.
    iExists γ. iIntros "{$% $#} !>". iNext.
    iApply (internal_eq_rewrite_contractive _ _ (box _ _) with "[Heq1 Heq2] Hbox").
    iNext. iRewrite "Heq1". iRewrite "Heq2". by rewrite assoc.
  - iMod (slice_delete_empty with "Hslice1 Hbox") as (P1) "(Heq1 & Hbox)"; try done.
    iMod (slice_delete_empty with "Hslice2 Hbox") as (P2) "(Heq2 & Hbox)"; first done.
    { by simplify_map_eq. }
    iMod (slice_insert_empty with "Hbox") as (γ ?) "[#Hslice Hbox]".
    iExists γ. iIntros "{$% $#} !>". iNext.
    iApply (internal_eq_rewrite_contractive _ _ (box _ _) with "[Heq1 Heq2] Hbox").
    iNext. iRewrite "Heq1". iRewrite "Heq2". by rewrite assoc.
Qed.
End box.

Typeclasses Opaque slice box.
