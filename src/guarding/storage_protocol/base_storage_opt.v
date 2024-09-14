Require Import guarding.storage_protocol.protocol.
From iris.proofmode Require Import base ltac_tactics tactics coq_tactics reduction.

Inductive BaseOpt (S: Type) :=
  | Empty : BaseOpt S
  | Full : S -> BaseOpt S
  | Fail : BaseOpt S
.
Global Arguments Empty {_}.
Global Arguments Full {_} _.
Global Arguments Fail {_}.

Global Instance base_opt_equiv {S} : Equiv (BaseOpt S) | 0 :=
    λ x y , x = y.

Global Instance base_opt_pcore {S} : PCore (BaseOpt S) | 0 :=
    λ x , None. (* pcore doesn't matter *)

Global Instance base_opt_valid {S} : Valid (BaseOpt S) | 0 :=
    λ x , match x with
        | Empty => True
        | Full _ => True
        | Fail => False
    end.

Global Instance base_opt_op {S} : Op (BaseOpt S) | 0 :=
    λ x y ,
      match x with
        | Empty => y
        | Full x => match y with
          | Empty => Full x
          | Full _ => Fail
          | Fail => Fail
        end
        | Fail => Fail
      end.
      
Global Instance base_opt_unit {S} : Unit (BaseOpt S) | 0 := Empty.

Lemma base_opt_op_comm {S} (a b : BaseOpt S) : a ⋅ b = b ⋅ a.
Proof.
  destruct a, b; trivial.
Qed.

Lemma base_opt_op_assoc {S} (a b c : BaseOpt S) : a ⋅ (b ⋅ c) = (a ⋅ b) ⋅ c.
Proof.
  destruct a, b, c; trivial.
Qed.

Lemma base_opt_valid_op_l {S} (a b : BaseOpt S) : ✓ (a ⋅ b) → ✓ a.
Proof.
  unfold "✓", base_opt_valid. destruct a, b; trivial.
Qed.

Lemma base_opt_unit_left_id {S} (a : BaseOpt S) : ε ⋅ a = a.
Proof.
  destruct a; trivial.
Qed.

Lemma base_opt_unit_right_id {S} (a : BaseOpt S) : a ⋅ ε = a.
Proof.
  destruct a; trivial.
Qed.

Definition base_opt_ra_mixin S : RAMixin (BaseOpt S).
Proof. split.
  - typeclasses eauto.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - typeclasses eauto.
  - unfold Assoc. intros. apply base_opt_op_assoc.
  - unfold Comm. intros. apply base_opt_op_comm.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - apply base_opt_valid_op_l.
Qed.

Section BaseOptMap.
  Definition base_opt_prop_map {Σ: gFunctors} {S} (s_map : S -> iProp Σ) :=
      λ (a: BaseOpt S) ,
        match a with
        | Empty => (True)%I
        | Full s => s_map s
        | Fail => (False)%I (* doesn't actually matter *)
        end.

  Lemma wf_prop_base_base_opt {Σ: gFunctors} {S} (s_map : S -> iProp Σ)
      : wf_prop_map (base_opt_prop_map s_map).
  Proof.
    split.
    { typeclasses eauto. }
    split.
    { trivial. }
    { 
      intros a b val.
      
      assert (∀ a , (a : iProp Σ)%I ≡ (a ∗ True)%I) as true_r.
      { intro. iIntros. iSplit; iIntros "x"; iFrame. iDestruct "x" as "[x _]". iFrame. }
      
      assert (∀ a , (a : iProp Σ)%I ≡ (True ∗ a)%I) as true_l.
      { intro. iIntros. iSplit; iIntros "x"; iFrame. iDestruct "x" as "[_ x]". iFrame. }
      
      destruct a, b; unfold "✓", base_opt_valid, "⋅", base_opt_op, base_opt_prop_map in *;
          try (setoid_rewrite <- true_r; trivial);
          try (setoid_rewrite <- true_l; trivial);
          try contradiction.
    } 
  Qed.

End BaseOptMap.
