From iris.algebra Require Import gset coPset.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From iris.prelude Require Import options.
Import uPred.

(* Non-atomic ("thread-local") invariants. *)

Definition na_inv_pool_name := gname.

Class na_invG Σ :=
  na_inv_inG :> inG Σ (prodR coPset_disjR (gset_disjR positive)).
Definition na_invΣ : gFunctors :=
  #[ GFunctor (constRF (prodR coPset_disjR (gset_disjR positive))) ].
Global Instance subG_na_invG {Σ} : subG na_invΣ Σ → na_invG Σ.
Proof. solve_inG. Qed.

Section defs.
  Context `{!invGS Σ, !na_invG Σ}.

  Definition na_own (p : na_inv_pool_name) (E : coPset) : iProp Σ :=
    own p (CoPset E, GSet ∅).

  Definition na_inv (p : na_inv_pool_name) (N : namespace) (P : iProp Σ) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧
         inv N (P ∗ own p (CoPset ∅, GSet {[i]}) ∨ na_own p {[i]}).
End defs.

Global Instance: Params (@na_inv) 3 := {}.
Typeclasses Opaque na_own na_inv.

Section proofs.
  Context `{!invGS Σ, !na_invG Σ}.

  Global Instance na_own_timeless p E : Timeless (na_own p E).
  Proof. rewrite /na_own; apply _. Qed.

  Global Instance na_inv_ne p N : NonExpansive (na_inv p N).
  Proof. rewrite /na_inv. solve_proper. Qed.
  Global Instance na_inv_proper p N : Proper ((≡) ==> (≡)) (na_inv p N).
  Proof. apply (ne_proper _). Qed.

  Global Instance na_inv_persistent p N P : Persistent (na_inv p N P).
  Proof. rewrite /na_inv; apply _. Qed.

  Lemma na_inv_iff p N P Q : na_inv p N P -∗ ▷ □ (P ↔ Q) -∗ na_inv p N Q.
  Proof.
    rewrite /na_inv. iIntros "(%i & % & HI) #HPQ".
    iExists i. iSplit; first done. iApply (inv_iff with "HI").
    iIntros "!> !>".
    iSplit; iIntros "[[? Ho]|$]"; iLeft; iFrame "Ho"; by iApply "HPQ".
  Qed.

  Lemma na_alloc : ⊢ |==> ∃ p, na_own p ⊤.
  Proof. by apply own_alloc. Qed.

  Lemma na_own_disjoint p E1 E2 : na_own p E1 -∗ na_own p E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    apply wand_intro_r.
    rewrite /na_own -own_op own_valid -coPset_disj_valid_op. by iIntros ([? _]).
  Qed.

  Lemma na_own_union p E1 E2 :
    E1 ## E2 → na_own p (E1 ∪ E2) ⊣⊢ na_own p E1 ∗ na_own p E2.
  Proof.
    intros ?. by rewrite /na_own -own_op -pair_op left_id coPset_disj_union.
  Qed.

  Lemma na_own_acc E2 E1 tid :
    E2 ⊆ E1 → na_own tid E1 -∗ na_own tid E2 ∗ (na_own tid E2 -∗ na_own tid E1).
  Proof.
    intros HF. assert (E1 = E2 ∪ (E1 ∖ E2)) as -> by exact: union_difference_L.
    rewrite na_own_union; last by set_solver+. iIntros "[$ $]". auto.
  Qed.

  Lemma na_inv_alloc p E N P : ▷ P ={E}=∗ na_inv p N P.
  Proof.
    iIntros "HP".
    iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) p) as "Hempty".
    iMod (own_updateP with "Hempty") as ([m1 m2]) "[Hm Hown]".
    { apply prod_updateP'.
      - apply cmra_updateP_id, (reflexivity (R:=eq)).
      - apply (gset_disj_alloc_empty_updateP_strong' (λ i, i ∈ (↑N:coPset))).
        intros Ef. exists (coPpick (↑ N ∖ gset_to_coPset Ef)).
        rewrite -elem_of_gset_to_coPset comm -elem_of_difference.
        apply coPpick_elem_of=> Hfin.
        eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
        apply gset_to_coPset_finite. }
    simpl. iDestruct "Hm" as %(<- & i & -> & ?).
    rewrite /na_inv.
    iMod (inv_alloc N with "[-]"); last (iModIntro; iExists i; eauto).
    iNext. iLeft. by iFrame.
  Qed.

  Lemma na_inv_acc p E F N P :
    ↑N ⊆ E → ↑N ⊆ F →
    na_inv p N P -∗ na_own p F ={E}=∗ ▷ P ∗ na_own p (F∖↑N) ∗
                       (▷ P ∗ na_own p (F∖↑N) ={E}=∗ na_own p F).
  Proof.
    rewrite /na_inv. iIntros (??) "#(%i & % & Hinv) Htoks".
    rewrite [F as X in na_own p X](union_difference_L (↑N) F) //.
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union; [|set_solver..].
    iDestruct "Htoks" as "[[Htoki $] $]".
    iInv "Hinv" as "[[$ >Hdis]|>Htoki2]" "Hclose".
    - iMod ("Hclose" with "[Htoki]") as "_"; first auto.
      iIntros "!> [HP $]".
      iInv N as "[[_ >Hdis2]|>Hitok]".
      + iDestruct (own_valid_2 with "Hdis Hdis2") as %[_ Hval%gset_disj_valid_op].
        set_solver.
      + iSplitR "Hitok"; last by iFrame. eauto with iFrame.
    - iDestruct (na_own_disjoint with "Htoki Htoki2") as %?. set_solver.
  Qed.

  Global Instance into_inv_na p N P : IntoInv (na_inv p N P) N := {}.

  Global Instance into_acc_na p F E N P :
    IntoAcc (X:=unit) (na_inv p N P)
            (↑N ⊆ E ∧ ↑N ⊆ F) (na_own p F) (fupd E E) (fupd E E)
            (λ _, ▷ P ∗ na_own p (F∖↑N))%I (λ _, ▷ P ∗ na_own p (F∖↑N))%I
              (λ _, Some (na_own p F))%I.
  Proof.
    rewrite /IntoAcc /accessor. iIntros ((?&?)) "#Hinv Hown".
    rewrite exist_unit -assoc /=.
    iApply (na_inv_acc with "Hinv"); done.
  Qed.
End proofs.
