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
From iris.algebra Require Import auth.

Require Import guarding.guard.
Require Import guarding.storage_protocol.protocol.

Require Import examples.misc_tactics.

Definition COUNT_NAMESPACE := nroot .@ "count".

Inductive Co :=
  | Refs : nat -> Co
  | Counters : Z -> nat -> Co   (* sum of all counters, # of counters - 1 *)
.

Local Instance co_valid : Valid Co := λ x, True.

Local Instance co_pcore : PCore Co := λ _, None.

Local Instance co_op : Op Co := λ x y,
  match (x, y) with
    | (Refs a, Refs b) => Refs (a + b)
    | (Refs a, Counters z c) => Counters (z - Z.of_nat a) c
    | (Counters z c, Refs a) => Counters (z - Z.of_nat a) c
    | (Counters z c, Counters z' c') => Counters (z + z')%Z (c + c' + 1)
  end.
    
Local Instance co_equiv : Equiv Co := λ x y, x = y.

Local Instance co_unit : Unit Co := Refs 0.

Local Instance co_equivalence : @Equivalence Co (≡).
Proof. split.
  - unfold Reflexive, equiv, co_equiv. intro x. trivial.
  - unfold Symmetric, equiv, co_equiv. intros x y a. symmetry. trivial.
  - unfold Transitive, equiv, co_equiv. intros x y z a b. subst x. trivial.
Qed.

Global Instance co_inv : SPInv Co := λ t , match t with
  | Refs n => n = 0
  | Counters count counters => count = 0
end.

Definition count_ra_mixin : RAMixin Co.
Proof.
  split; try apply _; try done.
  - unfold Assoc. intros x y z. unfold "⋅", co_op, "≡", co_equiv. destruct x, y, z; trivial; f_equal; lia.
  - unfold Comm. intros x y. unfold "⋅", co_op, "≡", co_equiv. destruct x, y; trivial; f_equal; lia.
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

Local Instance co_interp_instance : SPInterp Co nat := λ co , 
  match co with
  | Refs _ => 0%nat
  | Counters _ c => c + 1
  end.

Local Instance count_storage_mixin_ii : StorageMixinII Co nat.
Proof. split.
  - exact count_ra_mixin.
  - exact nat_ra_mixin.
  - unfold LeftId. intros x. unfold ε, co_unit, "⋅", co_op, "≡", co_equiv. destruct x; trivial.
      f_equal. lia.
  - unfold LeftId. intros x. unfold ε, nat_unit_instance, "⋅", nat_op_instance. trivial.
  - unfold Proper, "==>". intros x y Heq. unfold sp_inv, co_inv. destruct x, y; trivial;
      try contradiction; try discriminate; inversion Heq; trivial.
  - unfold Proper, "==>". intros x y Heq. unfold "≡", co_equiv in Heq. destruct x, y; trivial; try contradiction; try discriminate; inversion Heq; trivial.
  - intros. unfold "✓", nat_valid_instance. trivial.
Qed.

Class co_logicG Σ :=
    {
      #[local] count_sp_inG ::
        sp_logicG (storage_mixin_from_ii count_storage_mixin_ii) Σ
    }.

Definition co_logicΣ : gFunctors := #[
  sp_logicΣ (storage_mixin_from_ii count_storage_mixin_ii)
].

Global Instance subG_co_logicΣ {Σ} : subG co_logicΣ Σ → co_logicG Σ.
Proof. solve_inG. Qed.

Section Counting.

Context {Σ: gFunctors}.
Context `{co_in_Σ: !@co_logicG Σ}.
Context `{!invGS_gen hlc Σ}.

Fixpoint sep_pow (n: nat) (P: iProp Σ) : iProp Σ :=
  match n with
    | 0%nat => (True)%I
    | S k => (bi_sep P (sep_pow k P))%I
  end. 

Lemma sep_pow_additive (a b : nat) (Q: iProp Σ)
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

Definition family (Q: iProp Σ) (n: nat) : iProp Σ := sep_pow n Q.
  
Lemma wf_prop_map_family (Q: iProp Σ) : wf_prop_map (family Q).
Proof.  split.
  { unfold Proper, "==>", nat_equiv_instance. intros x y e. unfold "≡" in e.
    subst x. trivial.
  }
  split.
  { unfold ε, nat_unit_instance. unfold family, sep_pow. trivial. }
  intros a b x. unfold "⋅", nat_op_instance. unfold family. apply sep_pow_additive.
Qed.

Definition m (γ: gname) (Q: iProp Σ) := sp_sto (sp_i := count_sp_inG) γ (family Q).

Definition own_counter (γ: gname) (z: Z) := sp_own (sp_i := count_sp_inG) γ (Counters z 0).
    
Definition own_ref (γ: gname) := sp_own (sp_i := count_sp_inG) γ (Refs 1).

Lemma count_init E (Q: iProp Σ)
  : ⊢ True ={E}=∗ ∃ (γ: gname) , m γ Q.
Proof.
  iIntros "t".
  iDestruct (sp_alloc_ns (sp_i := count_sp_inG) (Refs 0) ε
      (family Q)
      E
      COUNT_NAMESPACE
      with "[t]") as "x".
  { unfold sp_inv, co_inv. split; trivial. unfold sp_inv. trivial. }
  { apply wf_prop_map_family. }
  { unfold family. unfold sp_interp, co_interp_instance. unfold sep_pow. iFrame. }
  iMod "x". iModIntro.
  iDestruct "x" as (γ) "[%inn [a b]]".
  iExists γ.
  iFrame "a".
Qed.

Lemma co_deposit (R: iProp Σ) γ
  : m γ R ⊢ R ={{[γ]}}=∗ own_counter γ 0.
Proof.
  iIntros "#m q".
  iDestruct (sp_deposit (Refs 0) (Counters 0 0) 1 _ _ with "m [q]") as "x".
  { rewrite eq_storage_protocol_deposit_ii. intros q Y. split.
    { unfold sp_inv, co_inv in *. destruct q.
      { unfold "⋅", co_op, "⋅", co_op in *. lia. }
      { unfold "⋅", co_op, "⋅", co_op in *. lia. }
    }
    split.
    { unfold "✓", nat_valid_instance. trivial. }
    { unfold sp_interp, co_interp_instance, "⋅", co_op in *.
        destruct q.
        { unfold "⋅", co_op, "≡", nat_equiv_instance, nat_op_instance. lia. }
        unfold nat_op_instance. f_equiv. simpl. trivial.
    }
  }
  { iSplitR. { iDestruct (sp_own_unit with "m") as "u". unfold ε, co_unit. iFrame "u". }
      { iModIntro. unfold family, sep_pow, sep_pow. iFrame "q". }
  }
  iMod "x". iModIntro. iFrame "x".
Qed.

Lemma co_join z γ :
  (own_counter γ z) ∗ (own_ref γ) ⊣⊢ own_counter γ (z - 1).
Proof.
  setoid_rewrite <- sp_own_op.
  unfold own_counter.
  trivial.
Qed.

Lemma co_withdraw (R: iProp Σ) γ :
  m γ R ⊢ own_counter γ 0 ={{[γ]}}=∗ ▷ R.
Proof.
  iIntros "#m q".
  iDestruct (sp_withdraw (Counters 0 0) (Refs 0) 1 _ _ with "m [q]") as "x".
  { rewrite eq_storage_protocol_withdraw_ii. intros q Y. split.
    { unfold sp_inv, co_inv in *. destruct q.
      { unfold "⋅", co_op in *. lia. }
      { unfold "⋅", co_op in *. lia. }
    }
    unfold sp_interp, co_interp_instance, "⋅", co_op, nat_op_instance. destruct q.
      - f_equal.
      - f_equal.
  } 
  { iFrame "q". }
  iMod "x" as "[x y]".
  iModIntro. iModIntro. unfold family, sep_pow. iDestruct "y" as "[y z]". iFrame "y".
Qed.

Lemma nat_ge_to_exists (x a : nat) : x ≥ a -> (∃ z : nat, x = a + z).
Proof. intros. exists (x - a). lia. Qed.

Lemma co_guard (R: iProp Σ) γ :
  m γ R ⊢ own_ref γ &&{ {[γ]} }&&> ▷ R.
Proof.
  unfold m.
  unfold own_ref.
  assert (R ⊣⊢ (family R 1)) as X.
  {
    unfold family, sep_pow. iIntros. iSplit. { iIntros. iFrame. } iIntros "[x y]". iFrame.
  }
  setoid_rewrite X at 2.
  apply sp_guard.
  2: { set_solver. }
  rewrite eq_storage_protocol_guards_ii. intro co. unfold "≼", sp_inv, co_inv.
  intro Y. apply nat_ge_to_exists.
  unfold "⋅" in *.
  unfold co_op in *. destruct co.
  - lia.
  - unfold sp_interp, co_interp_instance. lia.
Qed.

End Counting.
