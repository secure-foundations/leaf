From lrust.lifetime Require Export lifetime.
From iris.base_logic.lib Require Export na_invariants.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Definition na_bor `{!invGS Σ, !lftGS Σ, !na_invG Σ}
           (κ : lft) (tid : na_inv_pool_name) (N : namespace) (P : iProp Σ) :=
  (∃ i, &{κ,i}P ∗ na_inv tid N (idx_bor_own 1 i))%I.

Notation "&na{ κ , tid , N }" := (na_bor κ tid N)
    (format "&na{ κ , tid , N }") : bi_scope.

Section na_bor.
  Context `{!invGS Σ, !lftGS Σ, !na_invG Σ}
          (tid : na_inv_pool_name) (N : namespace) (P : iProp Σ).

  Global Instance na_bor_ne κ n : Proper (dist n ==> dist n) (na_bor κ tid N).
  Proof. solve_proper. Qed.
  Global Instance na_bor_contractive κ : Contractive (na_bor κ tid N).
  Proof. solve_contractive. Qed.
  Global Instance na_bor_proper κ : Proper ((⊣⊢) ==> (⊣⊢)) (na_bor κ tid N).
  Proof. solve_proper. Qed.

  Lemma na_bor_iff κ P' :
    ▷ □ (P ↔ P') -∗ &na{κ, tid, N} P -∗ &na{κ, tid, N} P'.
  Proof.
    iIntros "HPP' H". iDestruct "H" as (i) "[HP ?]". iExists i. iFrame.
    iApply (idx_bor_iff with "HPP' HP").
  Qed.

  Global Instance na_bor_persistent κ : Persistent (&na{κ,tid,N} P) := _.

  Lemma bor_na κ E : ↑lftN ⊆ E → &{κ}P ={E}=∗ &na{κ,tid,N}P.
  Proof.
    iIntros (?) "HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "[#? Hown]".
    iExists i. iFrame "#". iApply (na_inv_alloc tid E N with "[Hown]"). auto.
  Qed.

  Lemma na_bor_acc q κ E F :
    ↑lftN ⊆ E → ↑N ⊆ E → ↑N ⊆ F →
    lft_ctx -∗ &na{κ,tid,N}P -∗ q.[κ] -∗ na_own tid F ={E}=∗
            ▷P ∗ na_own tid (F ∖ ↑N) ∗
            (▷P -∗ na_own tid (F ∖ ↑N) ={E}=∗ q.[κ] ∗ na_own tid F).
  Proof.
    iIntros (???) "#LFT#HP Hκ Hnaown".
    iDestruct "HP" as (i) "(#Hpers&#Hinv)".
    iMod (na_inv_acc with "Hinv Hnaown") as "(>Hown&Hnaown&Hclose)"; try done.
    iMod (idx_bor_acc with "LFT Hpers Hown Hκ") as "[HP Hclose']". done.
    iIntros "{$HP $Hnaown} !> HP Hnaown".
    iMod ("Hclose'" with "HP") as "[Hown $]". iApply "Hclose". by iFrame.
  Qed.

  Lemma na_bor_shorten κ κ': κ ⊑ κ' -∗ &na{κ',tid,N}P -∗ &na{κ,tid,N}P.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (i) "[H ?]". iExists i. iFrame.
    iApply (idx_bor_shorten with "Hκκ' H").
  Qed.

  Lemma na_bor_fake E κ: ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &na{κ,tid,N}P.
  Proof.
    iIntros (?) "#LFT#H†". iApply (bor_na with "[>]"); first done.
    by iApply (bor_fake with "LFT H†").
  Qed.
End na_bor.

Global Typeclasses Opaque na_bor.
