Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qround.
Require Import Coq.QArith.Qcanon.
Require Import Coq.ZArith.Int.

From iris.base_logic.lib Require Import invariants.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Import reduction.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import class_instances.
From iris.program_logic Require Import ectx_lifting.
From iris Require Import options.

Require Import guarding.guard.
Require Import guarding.storage_protocol.protocol.
Require Import guarding.tactics.
From iris.algebra Require Import auth.

Require Import examples.misc_tactics.

Definition frac := option Qp.

Definition is_int (q: Qp) :=
    inject_Z (Qceiling (Qp_to_Qc q)) == Qp_to_Qc q.

Global Instance frac_inv : SPInv frac := λ t , match t with
  | None => True
  | Some q => is_int q
end.

Lemma ceil_ge_1 (q: Qp) : (Qceiling (Qp_to_Qc q) >= 1)%Z.
Proof.
  have h := Qle_ceiling (Qp_to_Qc q).
  have h2 := Qp_prf q.
  assert (¬((Qceiling (Qp_to_Qc q)) <= 0)%Z) as X. {
    intro R.
    rewrite Zle_Qle in R.
    unfold Qclt in h2.
    replace (Q2Qc 0 : Q) with (inject_Z 0) in h2 by trivial.
    have k := Qle_trans _ _ _ h R.
    have j := Qlt_not_le _ _ h2.
    apply j. trivial.
  }
  lia.
Qed.

Instance option_unit {T}  : Unit (option T) := None.
Instance option_pcore {T} `{p: PCore T} : PCore (option T) := λ t , None.
Instance option_op {T} `{Op T} : Op (option T) := λ a b ,
  match (a, b) with
    | (None, y) => y
    | (Some x, None) => Some x
    | (Some x, Some y) => Some (x ⋅ y)
  end.
Instance option_valid {T} `{Valid T} : Valid (option T) := λ a ,
  match a with
    | None => True
    | Some x => ✓ x
  end.
  
Instance option_equiv {T} `{p: Equiv T} : Equiv (option T) := λ a b ,
  match (a, b) with
    | (Some x, Some y) => x ≡ y
    | (None, None) => True
    | _ => False
  end. 
  
Definition option_ra_mixin {T} `{Equiv T, PCore T, Op T, Valid T} {equ: @Equivalence T (≡)} (m: RAMixin T)
    : RAMixin (option T).
Proof.
  split.
  - intro x. unfold Proper, "==>". intros x0 y Heq. destruct x, x0, y; trivial.
      + unfold "⋅", option_op. unfold "≡", option_equiv.
          unfold "≡", option_equiv in Heq.
          apply (ra_op_proper _ m). trivial.
      + unfold "≡", option_equiv in Heq. contradiction.
      + unfold "≡", option_equiv in Heq. contradiction.
      + unfold "≡", "⋅", option_equiv, option_op. trivial.
  - intros x y cx h j. unfold pcore, option_pcore in j. discriminate.
  - unfold Proper, "==>", impl. intros x y J. destruct x, y; trivial.
      + unfold "✓", option_valid. apply (ra_validN_proper _ m).
          unfold "≡", option_equiv in J. trivial.
      + intro. unfold "✓", option_valid. trivial.
      + unfold "≡", option_equiv in J. contradiction.
  - destruct m. unfold Assoc. intros x y z. destruct x, y, z; unfold "⋅", option_op, "≡", option_equiv; trivial.
  - destruct m. unfold Comm. intros x y. destruct x, y; unfold "⋅", option_op, "≡", option_equiv; trivial.
  - intros x cx X. unfold pcore, option_pcore in X. discriminate.
  - intros x cx X. unfold pcore, option_pcore in X. discriminate.
  - intros x y cx r X. unfold pcore, option_pcore in X. discriminate.
  - unfold "✓", option_valid, "⋅", option_op. intros x y X. destruct x, y; trivial.
      apply (ra_valid_op_l _ m _ _ X). 
Qed.
  
Local Instance frac_valid_instance : Valid Qp := λ x, True.
Local Instance frac_pcore_instance : PCore Qp := λ _, None.
Local Instance frac_op_instance : Op Qp := λ x y, (x + y)%Qp. 
Local Instance frac_equiv_instance : Equiv Qp := λ x y, x = y.

Local Instance frac_equivalence_instance : @Equivalence Qp (≡).
Proof. split.
  - unfold Reflexive, equiv, frac_equiv_instance. intro x. trivial.
  - unfold Symmetric, equiv, frac_equiv_instance. intros x y a. symmetry. trivial.
  - unfold Transitive, equiv, frac_equiv_instance. intros x y z a b. subst x. trivial.
Qed.

Local Instance option_equivalence_instance {T} `{Equiv T} {equ: @Equivalence T (≡)} : @Equivalence (option T) (≡).
Proof. split.
  - unfold Reflexive, equiv, option_equiv. intro x. destruct x; trivial.
  - unfold Symmetric, equiv, option_equiv. intros x y a. destruct x, y; trivial.
  - unfold Transitive, equiv, option_equiv. intros x y z a b. destruct x, y, z; trivial.
    + setoid_rewrite a. trivial.
    + contradiction.
Qed.
  
Definition frac_ra_mixin : RAMixin Qp.
Proof.
  split; try apply _; try done.
Qed.

Local Instance nat_valid_instance : Valid nat := λ x, True.
Local Instance nat_pcore_instance : PCore nat := λ _, None.
Local Instance nat_op_instance : Op nat := λ x y, (x + y)%nat. 
Local Instance nat_equiv_instance : Equiv nat := λ x y, x = y.
Local Instance nat_unit_instance : Unit nat := 0%nat.

Definition nat_ra_mixin : RAMixin nat.
Proof.
  split; try apply _; try done.
  (*- unfold Assoc. intros; unfold "⋅", nat_op_instance, "≡", nat_equiv_instance. lia.
  - unfold Comm. intros; unfold "⋅", nat_op_instance, "≡", nat_equiv_instance. lia.*)
Qed.
  
Local Instance frac_interp_instance : SPInterp (option Qp) nat := λ qopt , 
  match qopt with
  | None => 0%nat
  | Some q => Z.to_nat (Qceiling (Qp_to_Qc q))
  end.

Global Instance frac_storage_mixin_ii : @StorageMixinII (option Qp) nat
    option_equiv option_pcore option_op option_valid _ _ _ _ _ _ _ _ _ _.
Proof. split.
  - exact (option_ra_mixin frac_ra_mixin).
  - exact nat_ra_mixin.
  - unfold LeftId. intros x. unfold ε, option_unit, "⋅", option_op, "≡", option_equiv.
      destruct x; trivial.
  - unfold LeftId. intros x. unfold ε, nat_unit_instance, "⋅", nat_op_instance. trivial.
  - intros p X eq. destruct p; trivial.
      + unfold sp_inv, frac_inv. destruct X as [X|].
        * inversion eq. trivial.
        * inversion eq.
      + destruct X. * inversion eq. * trivial.
  - unfold Proper, "==>". intros x y Heq. unfold "≡", option_equiv in Heq. destruct x, y; trivial; try contradiction. unfold "≡", frac_equiv_instance in Heq. rewrite Heq. trivial.
  - intros. unfold "✓", nat_valid_instance. trivial.
Qed.

Fixpoint sep_pow {Σ} (n: nat) (P: iProp Σ) : iProp Σ :=
  match n with
    | 0%nat => (True)%I
    | S k => (bi_sep P (sep_pow k P))%I
  end. 

Lemma sep_pow_additive {Σ} (a b : nat) (Q: iProp Σ)
    : sep_pow (a + b) Q ≡ (sep_pow a Q ∗ sep_pow b Q)%I.
Proof.
  induction b as [|b IHb].
  - simpl. replace (a + 0) with a by lia.
    iIntros. iSplit. { iIntros "a".  iFrame. } iIntros "[a b]". iFrame.
  - simpl. replace (a + S b) with (S (a + b)) by lia. simpl.
    rewrite IHb. iIntros. iSplit.
    { iIntros "[a [b c]]". iFrame. }
    { iIntros "[a [b c]]". iFrame. }
Qed.

Definition family {Σ} (Q: iProp Σ) (n: nat) : iProp Σ := sep_pow n Q.
  
Lemma wf_prop_map_family {Σ} (Q: iProp Σ) : wf_prop_map (family Q).
Proof.  split.
  { unfold Proper, "==>", nat_equiv_instance. intros x y e. unfold "≡" in e.
    subst x. trivial.
  }
  split.
  { unfold ε, nat_unit_instance. unfold family, sep_pow. trivial. }
  intros a b x. unfold "⋅", nat_op_instance. unfold family. apply sep_pow_additive.
Qed.

Lemma q_le_add_1 (a b: Q) (is_le: Qle a b) : Qle (a + 1) (b + 1).
  Proof. rewrite Qplus_le_l. trivial. Qed.
Lemma q_lt_add_1 (a b: Q) (is_le: Qlt a b) : Qlt (a + 1) (b + 1).
  Proof. rewrite Qplus_lt_l. trivial. Qed.
Lemma injz_p1 (z: Z) : inject_Z z + 1 == inject_Z (z + 1). Proof.
  rewrite inject_Z_plus.
  replace (inject_Z 1) with (1%Q). - apply Qeq_refl. - simpl. trivial. Qed.
  
Lemma Qceiling_plus_1 q : (Qceiling (q + 1))%Z = (Qceiling q + 1)%Z. 
Proof.
  have h1 := Qle_ceiling q. have h2 := Qle_ceiling (q + 1).
  have h3 := Qceiling_lt q. have h4 := Qceiling_lt (q + 1).
  have h1' := q_le_add_1 _ _ h1. have h3' := q_lt_add_1 _ _ h3.
  clear h1. clear h3.
  have j1 := Qlt_le_trans _ _ _ h4 h1'. have j2 := Qlt_le_trans _ _ _ h3' h2.
  clear h1'. clear h2. clear h3'. clear h4. generalize j1. generalize j2.
  rewrite injz_p1. rewrite injz_p1. rewrite <- Zlt_Qlt. rewrite <- Zlt_Qlt.
  clear j1. clear j2. intro j1. intro j2.
  lia.
Qed.

Lemma is_int_plus_1 (q: Qp)
  (q_is_int : is_int q) : is_int (1%Qp + q).
Proof.
  unfold is_int in *.
  assert ((Qceiling (Qp_to_Qc (1 + q))) = Z.add 1 (Qceiling (Qp_to_Qc q))) as Y.
  2: {
    rewrite Y. 
    rewrite inject_Z_plus.
    rewrite q_is_int.
    destruct q. simpl.
    symmetry.
    apply Qreduction.Qred_correct.
  }
  replace (1 + q)%Qp with (q + 1)%Qp.
  - replace (1 + Qceiling (Qp_to_Qc q))%Z with (Qceiling (Qp_to_Qc q) + 1)%Z.
    + rewrite Qp.to_Qc_inj_add.
      rewrite <- Qceiling_plus_1.
      assert ((Qcplus (Qp_to_Qc q) (Qp_to_Qc (pos_to_Qp 1)))
          == ((Qplus (Qp_to_Qc q) 1))) as X.
        { simpl. rewrite Qreduction.Qred_correct. destruct q. simpl.
          assert (inject_Z 1 == 1) as XX.
          { unfold inject_Z. apply Qeq_refl. }
          rewrite XX. apply Qeq_refl.
        }
        rewrite X.
        trivial.
    + apply Z.add_comm.
  - apply Qp.add_comm.
Qed.
 
Lemma is_int_minus_1 (q: Qp)
  (q_p1_is_int : is_int (1 + q)) : is_int q.
Proof.
  unfold is_int in *.
  assert ((Qceiling (Qp_to_Qc (1 + q))) = Z.add 1 (Qceiling (Qp_to_Qc q))) as Y.
  2: {
    rewrite Y in q_p1_is_int. 
    rewrite inject_Z_plus in q_p1_is_int.
    assert ((inject_Z 1) == 1) as XX.
    + unfold inject_Z. apply Qeq_refl.
    + rewrite XX in q_p1_is_int.
      assert ((inject_Z (Qceiling (Qp_to_Qc q))) == 
          (-1) + (1 + inject_Z (Qceiling (Qp_to_Qc q)))) as T1.
      { rewrite Qplus_assoc. 
        assert (-1 + 1 == 0) as JJ. { rewrite Qplus_comm. apply Qplus_opp_r. }
        rewrite JJ. rewrite Qplus_0_l. apply Qeq_refl.
      }
      assert ((-1) + Qp_to_Qc (1 + q) == Qp_to_Qc q) as T2.
      {
        rewrite Qp.to_Qc_inj_add.
        simpl. unfold inject_Z. rewrite Qreduction.Qred_correct.
        rewrite Qplus_assoc.
        assert (-1 + 1 == 0) as JJ. { rewrite Qplus_comm. apply Qplus_opp_r. }
        rewrite JJ. rewrite Qplus_0_l. apply Qeq_refl.
      }
      rewrite T1.
      rewrite q_p1_is_int.
      apply T2.
   }
  replace (1 + q)%Qp with (q + 1)%Qp.
  - replace (1 + Qceiling (Qp_to_Qc q))%Z with (Qceiling (Qp_to_Qc q) + 1)%Z.
    + rewrite Qp.to_Qc_inj_add.
      rewrite <- Qceiling_plus_1.
      assert ((Qcplus (Qp_to_Qc q) (Qp_to_Qc (pos_to_Qp 1)))
          == ((Qplus (Qp_to_Qc q) 1))) as X.
        { simpl. rewrite Qreduction.Qred_correct. destruct q. simpl.
          assert (inject_Z 1 == 1) as XX.
          { unfold inject_Z. apply Qeq_refl. }
          rewrite XX. apply Qeq_refl.
        }
        rewrite X.
        trivial.
    + apply Z.add_comm.
  - apply Qp.add_comm.
Qed.

  
Lemma is_int_1 : is_int (1%Qp).
Proof.
  unfold is_int.
  assert ((Qp_to_Qc 1 : Q) == inject_Z 1) as X.
  - simpl. trivial. apply Qeq_refl.
  - (*rewrite X.*)
      rewrite Qceiling_Z. apply Qeq_refl.
Qed.

Lemma Z_to_nat_plus_1 (x: Z) (x_ge_0 : Z.ge x 0) : Z.to_nat (x + 1) = Z.to_nat x + 1.
Proof. lia. Qed.

Lemma Qceiling_qp_ge_0 q : (Z.ge (Qceiling (Qp_to_Qc q)) 0).
Proof. have t := ceil_ge_1 q. lia. Qed.


Lemma nat_ge_to_exists (x a : nat) : x ≥ a -> (∃ z : nat, x = a + z).
Proof. intros. exists (x - a). lia. Qed.

Lemma nat_ceil_ge_1 (q: Qp) : Z.to_nat (Qceiling (Qp_to_Qc q))%Z >= 1.
Proof. have h := ceil_ge_1 q. lia. Qed.

Lemma to_nat_add_1 (q: Qp) :
  Z.to_nat (Qceiling (Qp_to_Qc q)) + 1 = Z.to_nat (Qceiling (Qp_to_Qc (1 + q))).
Proof.
  rewrite <- Z_to_nat_plus_1 by apply Qceiling_qp_ge_0.
  f_equal.
  rewrite <- Qceiling_plus_1.
  assert ((Qp_to_Qc q + 1) == (Qp_to_Qc (1 + q)))%Q as X.
  2: { rewrite X. trivial. }
  rewrite Qp.to_Qc_inj_add.
  rewrite Qcplus_comm.
  assert (({| Qnum := Zpos xH; Qden := xH |}) == (Qp_to_Qc (pos_to_Qp xH))) as Y.
  { simpl. unfold inject_Z. f_equal. }
  rewrite Y.
  rewrite <- Q2Qc_eq_iff.
  unfold Qcplus.
  unfold Q2Qc, this. 
  apply Qc_decomp. unfold this.
  rewrite Qred_involutive. trivial.
Qed.

Class frac_logicG Σ :=
    {
      #[local] frac_sp_inG ::
        sp_logicG (storage_mixin_from_ii frac_storage_mixin_ii) Σ
    }.

Definition frac_logicΣ : gFunctors := #[
  sp_logicΣ (storage_mixin_from_ii frac_storage_mixin_ii)
].

Global Instance subG_frac_logicΣ {Σ} : subG frac_logicΣ Σ → frac_logicG Σ.
Proof. solve_inG. Qed.

Section Frac.
  Context {Σ: gFunctors}.
  Context `{!frac_logicG Σ}.
  Context `{!invGS_gen hlc Σ}.

  Definition sto_frac (γ: gname) (Q: iProp Σ) := sp_sto (sp_i := frac_sp_inG) γ (family Q).
  Definition own_frac (γ: gname) (qp: Qp) := sp_own (sp_i := frac_sp_inG) γ (Some qp).


  Lemma frac_alloc (N: namespace) E (Q: iProp Σ)
    : ⊢ |={E}=> ∃ (γ: gname) , sto_frac γ Q ∗ ⌜ γ ∈ (↑N : coPset) ⌝.
  Proof.
    iIntros.
    iDestruct (sp_alloc_ns (sp_i := frac_sp_inG)
        (None : option Qp)
        ε
        (family Q)
        E
        N
        with "[]") as "x".
    { unfold sp_rel, sp_inv, frac_inv. split; trivial. unfold sp_inv. trivial. }
    { apply wf_prop_map_family. }
    { done. }
    iMod "x". iModIntro.
    iDestruct "x" as (γ) "[%inn [a b]]".
    iExists γ.
    iFrame "a". iPureIntro. trivial.
  Qed.

  Lemma frac_deposit (R: iProp Σ) γ
    : sto_frac γ R ⊢ R ={{[γ]}}=∗ own_frac γ 1.
  Proof.
    iIntros "#m q".
    iDestruct (sp_deposit None (Some (1%Qp)) 1 _ _ with "m [q]") as "x".
    { rewrite eq_storage_protocol_deposit_ii. intros q Y. split.
      { unfold sp_inv, frac_inv in *. destruct q.
        { unfold "⋅", option_op, "⋅", frac_op_instance in *. apply is_int_plus_1. trivial. }
        { unfold "⋅", option_op, "⋅", frac_op_instance in *. apply is_int_1. }
      }
      split.
      { unfold "✓", nat_valid_instance. trivial. }
      { unfold sp_interp, frac_interp_instance, "⋅", option_op, nat_op_instance in *.
          destruct q.
          { unfold "⋅", frac_op_instance, "≡", nat_equiv_instance.
              apply to_nat_add_1. }
          simpl. trivial. } 
    }
    { iSplitR. { iDestruct (sp_own_unit with "m") as "u". unfold ε, option_unit. iFrame "u". }
        { iModIntro. unfold family, sep_pow, sep_pow. iFrame "q". }
    }
    iMod "x". iModIntro. iFrame "x".
  Qed.

  Lemma frac_join q1 q2 γ :
    (own_frac γ q1) ∗ (own_frac γ q2) ⊣⊢ own_frac γ (q1 + q2).
  Proof.
    setoid_rewrite <- sp_own_op.
    unfold own_frac.
    trivial.
  Qed.

  Lemma frac_withdraw (R: iProp Σ) γ :
    sto_frac γ R ⊢ own_frac γ 1 ={{[γ]}}=∗ ▷ R.
  Proof.
    iIntros "#m q".
    iDestruct (sp_withdraw (Some (1%Qp)) None 1 _ _ with "m [q]") as "x".
    { rewrite eq_storage_protocol_withdraw_ii. intros q Y. split.
      { unfold sp_inv, frac_inv in *. destruct q.
        { unfold "⋅", option_op, "⋅", frac_op_instance in *. apply is_int_minus_1. trivial. }
        { unfold "⋅", option_op, "⋅", frac_op_instance in *. trivial. }
      }
      unfold sp_interp, frac_interp_instance, "⋅", option_op, nat_op_instance. destruct q.
      - symmetry. apply to_nat_add_1.
      - simpl. trivial. }
    { iFrame "q". }
    iMod "x" as "[x y]".
    iModIntro. iModIntro. unfold family, sep_pow. iDestruct "y" as "[y z]". iFrame "y".
  Qed.

  Lemma frac_guard (R: iProp Σ) γ q :
    sto_frac γ R ⊢ own_frac γ q &&{ {[γ]} }&&> ▷ R.
  Proof.
    unfold sto_frac.
    unfold own_frac.
    assert (R ⊣⊢ (family R 1)) as X.
    {
      unfold family, sep_pow. iIntros. iSplit. { iIntros. iFrame. } iIntros "[x y]". iFrame.
    }
    setoid_rewrite X at 2.
    apply sp_guard.
    2: { set_solver. }
    rewrite eq_storage_protocol_guards_ii. intro q0. unfold "≼", sp_inv, frac_inv.
    intro.
    apply nat_ge_to_exists. unfold sp_interp, frac_interp_instance, "⋅", option_op.
    destruct q0.
    - apply nat_ceil_ge_1.
    - apply nat_ceil_ge_1.
  Qed.
  
  Lemma frac_alloc2 (N: namespace) (P: iProp Σ) (E: coPset) :
    (↑N ⊆ E) →
    P ⊢ |={E}=> ∃ (γ: gname) , own_frac γ 1%Qp
          ∗ □ (own_frac γ 1%Qp ={↑N}=∗ ▷ P)
          ∗ (∀ q , own_frac γ q &&{↑N}&&> ▷ P).
  Proof.
    intros HE. iIntros "P".
    iMod (frac_alloc N E P) as (γ) "[#sto %Hns]".
    iMod (fupd_mask_subseteq {[γ]}) as "Hb". { set_solver. }
    iMod (frac_deposit with "sto P") as "H1".
    iMod "Hb". iModIntro.
    iExists γ. iFrame "H1". iSplit.
    - iModIntro. iIntros "Ho1". iApply (fupd_mask_mono {[γ]}). { set_solver. }
      iApply frac_withdraw; iFrame. iFrame "sto".
    - iIntros (q). leaf_goal mask to ({[γ]}). { set_solver. }
      iApply frac_guard. iFrame "sto".
  Qed.

End Frac.
