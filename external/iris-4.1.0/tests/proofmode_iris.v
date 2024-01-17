From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics monpred.
From iris.base_logic Require Import base_logic.
From iris.base_logic.lib Require Import invariants cancelable_invariants na_invariants ghost_var.
From iris.prelude Require Import options.

Unset Mangle Names.
Set Default Proof Using "Type*".

Section base_logic_tests.
  Context {M : ucmra}.
  Implicit Types P Q R : uPred M.

  Lemma test_random_stuff (P1 P2 P3 : nat → uPred M) :
    ⊢ ∀ (x y : nat) a b,
      x ≡ y →
      □ (uPred_ownM (a ⋅ b) -∗
      (∃ y1 y2 c, P1 ((x + y1) + y2) ∧ True ∧ □ uPred_ownM c) -∗
      □ ▷ (∀ z, P2 z ∨ True → P2 z) -∗
      ▷ (∀ n m : nat, P1 n → □ ((True ∧ P2 n) → □ (⌜n = n⌝ ↔ P3 n))) -∗
      ▷ ⌜x = 0⌝ ∨ ∃ x z, ▷ P3 (x + z) ∗ uPred_ownM b ∗ uPred_ownM (core b)).
  Proof.
    iIntros (i [|j] a b ?) "!> [Ha Hb] H1 #H2 H3"; setoid_subst.
    { iLeft. by iNext. }
    iRight.
    iDestruct "H1" as (z1 z2 c) "(H1&_&#Hc)".
    iPoseProof "Hc" as "foo".
    iRevert (a b) "Ha Hb". iIntros (b a) "Hb {foo} Ha".
    iAssert (uPred_ownM (a ⋅ core a)) with "[Ha]" as "[Ha #Hac]".
    { by rewrite cmra_core_r. }
    iIntros "{$Hac $Ha}".
    iExists (S j + z1), z2.
    iNext.
    iApply ("H3" $! _ 0 with "[$]").
    - iSplit; first done. iApply "H2". iLeft. iApply "H2". by iRight.
    - done.
  Qed.

  Lemma test_iFrame_pure (x y z : M) :
    ✓ x → ⌜y ≡ z⌝ -∗ (✓ x ∧ ✓ x ∧ y ≡ z : uPred M).
  Proof. iIntros (Hv) "Hxy". by iFrame (Hv) "Hxy". Qed.

  Lemma test_iAssert_modality P : (|==> False) -∗ |==> P.
  Proof. iIntros. iAssert False%I with "[> - //]" as %[]. Qed.

  Lemma test_iStartProof_1 P : P -∗ P.
  Proof. iStartProof. iStartProof. iIntros "$". Qed.
  Lemma test_iStartProof_2 P : P -∗ P.
  Proof. iStartProof (uPred _). iStartProof (uPredI _). iIntros "$". Qed.
  Lemma test_iStartProof_3 P : P -∗ P.
  Proof. iStartProof (uPredI _). iStartProof (uPredI _). iIntros "$". Qed.
  Lemma test_iStartProof_4 P : P -∗ P.
  Proof. iStartProof (uPredI _). iStartProof (uPred _). iIntros "$". Qed.
End base_logic_tests.

Section iris_tests.
  Context `{!invGS_gen hlc Σ, !cinvG Σ, !na_invG Σ}.
  Implicit Types P Q R : iProp Σ.

  Lemma test_except_0_inv N P : ▷ False -∗ inv N P.
  Proof.
    iIntros "H". by iMod "H". (* works because invariants are [IsExcept0] *)
  Qed.

  Lemma test_masks  N E P Q R :
    ↑N ⊆ E →
    (True -∗ P -∗ inv N Q -∗ True -∗ R) -∗ P -∗ ▷ Q ={E}=∗ R.
  Proof.
    iIntros (?) "H HP HQ".
    iApply ("H" with "[% //] [$] [> HQ] [> //]").
    by iApply inv_alloc.
  Qed.

  Lemma test_iInv_0 N P: inv N (<pers> P) ={⊤}=∗ ▷ P.
  Proof.
    iIntros "#H".
    iInv N as "#H2". Show.
    iModIntro. iSplit; auto.
  Qed.

  Lemma test_iInv_0_with_close N P: inv N (<pers> P) ={⊤}=∗ ▷ P.
  Proof.
    iIntros "#H".
    iInv N as "#H2" "Hclose". Show.
    iMod ("Hclose" with "H2").
    iModIntro. by iNext.
  Qed.

  Lemma test_iInv_1 N E P:
    ↑N ⊆ E →
    inv N (<pers> P) ={E}=∗ ▷ P.
  Proof.
    iIntros (?) "#H".
    iInv N as "#H2".
    iModIntro. iSplit; auto.
  Qed.

  Lemma test_iInv_2 γ p N P:
    cinv N γ (<pers> P) ∗ cinv_own γ p ={⊤}=∗ cinv_own γ p ∗ ▷ P.
  Proof.
    Show.
    iIntros "(#?&?)".
    iInv N as "(#HP&Hown)". Show.
    iModIntro. iSplit; auto with iFrame.
  Qed.

  Check "test_iInv_2_with_close".
  Lemma test_iInv_2_with_close γ p N P:
    cinv N γ (<pers> P) ∗ cinv_own γ p ={⊤}=∗ cinv_own γ p ∗ ▷ P.
  Proof.
    iIntros "(#?&?)".
    iInv N as "(#HP&Hown)" "Hclose". Show.
    iMod ("Hclose" with "HP").
    iModIntro. iFrame. by iNext.
  Qed.

  Lemma test_iInv_3 γ p1 p2 N P:
    cinv N γ (<pers> P) ∗ cinv_own γ p1 ∗ cinv_own γ p2
      ={⊤}=∗ cinv_own γ p1 ∗ cinv_own γ p2  ∗ ▷ P.
  Proof.
    iIntros "(#?&Hown1&Hown2)".
    iInv N with "[Hown2 //]" as "(#HP&Hown2)".
    iModIntro. iSplit; auto with iFrame.
  Qed.

  Check "test_iInv_4".
  Lemma test_iInv_4 t N E1 E2 P:
    ↑N ⊆ E2 →
    na_inv t N (<pers> P) ∗ na_own t E1 ∗ na_own t E2
       ={⊤}=∗ na_own t E1 ∗ na_own t E2  ∗ ▷ P.
  Proof.
    iIntros (?) "(#?&Hown1&Hown2)".
    iInv N as "(#HP&Hown2)". Show.
    iModIntro. iSplitL "Hown2"; auto with iFrame.
  Qed.

  Check "test_iInv_4_with_close".
  Lemma test_iInv_4_with_close t N E1 E2 P:
    ↑N ⊆ E2 →
    na_inv t N (<pers> P) ∗ na_own t E1 ∗ na_own t E2
         ={⊤}=∗ na_own t E1 ∗ na_own t E2  ∗ ▷ P.
  Proof.
    iIntros (?) "(#?&Hown1&Hown2)".
    iInv N as "(#HP&Hown2)" "Hclose". Show.
    iMod ("Hclose" with "[HP Hown2]").
    { iFrame. done. }
    iModIntro. iFrame. by iNext.
  Qed.

  (* test named selection of which na_own to use *)
  Lemma test_iInv_5 t N E1 E2 P:
    ↑N ⊆ E2 →
    na_inv t N (<pers> P) ∗ na_own t E1 ∗ na_own t E2
      ={⊤}=∗ na_own t E1 ∗ na_own t E2  ∗ ▷ P.
  Proof.
    iIntros (?) "(#?&Hown1&Hown2)".
    iInv N with "Hown2" as "(#HP&Hown2)".
    iModIntro. iSplitL "Hown2"; auto with iFrame.
  Qed.

  Lemma test_iInv_6 t N E1 E2 P:
    ↑N ⊆ E1 →
    na_inv t N (<pers> P) ∗ na_own t E1 ∗ na_own t E2
      ={⊤}=∗ na_own t E1 ∗ na_own t E2  ∗ ▷ P.
  Proof.
    iIntros (?) "(#?&Hown1&Hown2)".
    iInv N with "Hown1" as "(#HP&Hown1)".
    iModIntro. iSplitL "Hown1"; auto with iFrame.
  Qed.

  (* test robustness in presence of other invariants *)
  Lemma test_iInv_7 t N1 N2 N3 E1 E2 P:
    ↑N3 ⊆ E1 →
    inv N1 P ∗ na_inv t N3 (<pers> P) ∗ inv N2 P  ∗ na_own t E1 ∗ na_own t E2
      ={⊤}=∗ na_own t E1 ∗ na_own t E2  ∗ ▷ P.
  Proof.
    iIntros (?) "(#?&#?&#?&Hown1&Hown2)".
    iInv N3 with "Hown1" as "(#HP&Hown1)".
    iModIntro. iSplitL "Hown1"; auto with iFrame.
  Qed.

  (* iInv should work even where we have "inv N P" in which P contains an evar *)
  Lemma test_iInv_8 N : ∃ P, inv N P ={⊤}=∗ P ≡ True ∧ inv N P.
  Proof.
    eexists. iIntros "#H".
    iInv N as "HP". iFrame "HP". auto.
  Qed.

  (* test selection by hypothesis name instead of namespace *)
  Lemma test_iInv_9 t N1 N2 N3 E1 E2 P:
    ↑N3 ⊆ E1 →
    inv N1 P ∗ na_inv t N3 (<pers> P) ∗ inv N2 P  ∗ na_own t E1 ∗ na_own t E2
      ={⊤}=∗ na_own t E1 ∗ na_own t E2  ∗ ▷ P.
  Proof.
    iIntros (?) "(#?&#HInv&#?&Hown1&Hown2)".
    iInv "HInv" with "Hown1" as "(#HP&Hown1)".
    iModIntro. iSplitL "Hown1"; auto with iFrame.
  Qed.

  (* test selection by hypothesis name instead of namespace *)
  Lemma test_iInv_10 t N1 N2 N3 E1 E2 P:
    ↑N3 ⊆ E1 →
    inv N1 P ∗ na_inv t N3 (<pers> P) ∗ inv N2 P  ∗ na_own t E1 ∗ na_own t E2
      ={⊤}=∗ na_own t E1 ∗ na_own t E2  ∗ ▷ P.
  Proof.
    iIntros (?) "(#?&#HInv&#?&Hown1&Hown2)".
    iInv "HInv" as "(#HP&Hown1)".
    iModIntro. iSplitL "Hown1"; auto with iFrame.
  Qed.

  (* test selection by ident name *)
  Lemma test_iInv_11 N P: inv N (<pers> P) ={⊤}=∗ ▷ P.
  Proof.
    let H := iFresh in
    (iIntros H; iInv H as "#H2"). auto.
  Qed.

  (* error messages *)
  Check "test_iInv_12".
  Lemma test_iInv_12 N P: inv N (<pers> P) ={⊤}=∗ True.
  Proof.
    iIntros "H".
    Fail iInv 34 as "#H2".
    Fail iInv nroot as "#H2".
    Fail iInv "H2" as "#H2".
    done.
  Qed.

  (* test destruction of existentials when opening an invariant *)
  Lemma test_iInv_13 N:
    inv N (∃ (v1 v2 v3 : nat), emp ∗ emp ∗ emp) ={⊤}=∗ ▷ emp.
  Proof.
    iIntros "H"; iInv "H" as (v1 v2 v3) "(?&?&_)".
    eauto.
  Qed.

  (* Test [iInv] with accessor variables. *)
  Section iInv_accessor_variables.
    (** We consider a kind of invariant that does not take a proposition, but
    a predicate. The invariant accessor gives the predicate existentially. *)
    Context (INV : (bool → iProp Σ) → iProp Σ).
    Context `{!∀ Φ,
      IntoAcc (INV Φ) True True (fupd ⊤ ∅) (fupd ∅ ⊤) Φ Φ (λ b, Some (INV Φ))}.

    Check "test_iInv_accessor_variable".
    Lemma test_iInv_accessor_variable Φ : INV Φ ={⊤}=∗ INV Φ.
    Proof.
      iIntros "HINV".
      (* There are 4 variants of [iInv] that we have to test *)
      (* No selection pattern, no closing view shift *)
      Fail iInv "HINV" as "HINVinner".
      iInv "HINV" as (b) "HINVinner"; rename b into b_exists. Undo.
      (* Both sel.pattern and closing view shift *)
      Fail iInv "HINV" with "[//]" as "HINVinner" "Hclose".
      iInv "HINV" with "[//]" as (b) "HINVinner" "Hclose";
        rename b into b_exists. Undo.
      (* Sel.pattern but no closing view shift *)
      Fail iInv "HINV" with "[//]" as "HINVinner".
      iInv "HINV" with "[//]" as (b) "HINVinner"; rename b into b_exists. Undo.
      (* Closing view shift, no selection pattern *)
      Fail iInv "HINV" as "HINVinner" "Hclose".
      iInv "HINV" as (b) "HINVinner" "Hclose"; rename b into b_exists.
      by iApply "Hclose".
    Qed.
  End iInv_accessor_variables.

  Theorem test_iApply_inG `{!inG Σ A} γ (x x' : A) :
    x' ≼ x →
    own γ x -∗ own γ x'.
  Proof. intros. by iApply own_mono. Qed.

  Check "test_frac_split_combine".
  Lemma test_frac_split_combine `{!inG Σ fracR} γ :
    own γ 1%Qp -∗ own γ 1%Qp.
  Proof.
    iIntros "[H1 H2]". Show.
    iCombine "H1 H2" as "H". Show.
    iExact "H".
  Qed.

  Check "test_iDestruct_mod_not_fresh".
  Lemma test_iDestruct_mod_not_fresh P Q :
    P -∗ (|={⊤}=> Q) -∗ (|={⊤}=> False).
  Proof.
    iIntros "H H'". Fail iDestruct "H'" as ">H".
  Abort.

  (** Make sure that the splitting rule for [+] gets preferred over the one for
  [S]. See issue #470. *)
  Check "test_iIntros_lc".
  Lemma test_iIntros_lc n m : £ (S n + m) -∗ £ (S n).
  Proof. iIntros "[Hlc1 Hlc2]". Show. iExact "Hlc1". Qed.

  Check "lc_iSplit_lc".
  Lemma lc_iSplit_lc n m : £ (S n) -∗ £ m -∗ £ (S n + m).
  Proof. iIntros "Hlc1 Hlc2". iSplitL "Hlc1". Show. all: done. Qed.

  (** Make sure [iCombine] doesn't leave behind beta redexes. *)
  Check "test_iCombine_mapsto_no_beta".
  Lemma test_iCombine_ghost_var_no_beta `{!ghost_varG Σ nat} l (v : nat) q1 q2 :
    ghost_var l q1 v -∗ ghost_var l q2 v -∗ ghost_var l (q1+q2) v.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H". Show. done.
  Qed.
End iris_tests.

Section monpred_tests.
  Context `{!invGS_gen hlc Σ}.
  Context {I : biIndex}.
  Local Notation monPred := (monPred I (iPropI Σ)).
  Local Notation monPredI := (monPredI I (iPropI Σ)).
  Implicit Types P Q R : monPred.
  Implicit Types 𝓟 𝓠 𝓡 : iProp Σ.

  Check "test_iInv".
  Lemma test_iInv N E 𝓟 :
    ↑N ⊆ E →
    ⎡inv N 𝓟⎤ ⊢@{monPredI} |={E}=> emp.
  Proof.
    iIntros (?) "Hinv".
    iInv N as "HP". Show.
    iFrame "HP". auto.
  Qed.

  Check "test_iInv_with_close".
  Lemma test_iInv_with_close N E 𝓟 :
    ↑N ⊆ E →
    ⎡inv N 𝓟⎤ ⊢@{monPredI} |={E}=> emp.
  Proof.
    iIntros (?) "Hinv".
    iInv N as "HP" "Hclose". Show.
    iMod ("Hclose" with "HP"). auto.
  Qed.

End monpred_tests.
