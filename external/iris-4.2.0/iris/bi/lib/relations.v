(** This file provides constructions to lift
a PROP-level binary relation to various closures. *)
From iris.bi.lib Require Export fixpoint.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

(* The sections add extra BI assumptions, which is only picked up with "Type"*. *)
Set Default Proof Using "Type*".

(** * Definitions *)
Section definitions.
  Context {PROP : bi} `{!BiInternalEq PROP}.
  Context {A : ofe}.

  Local Definition bi_rtc_pre (R : A → A → PROP)
      (x2 : A) (rec : A → PROP) (x1 : A) : PROP :=
    <affine> (x1 ≡ x2) ∨ ∃ x', R x1 x' ∗ rec x'.

  (** The reflexive transitive closure. *)
  Definition bi_rtc (R : A → A → PROP) (x1 x2 : A) : PROP :=
    bi_least_fixpoint (bi_rtc_pre R x2) x1.

  Global Instance: Params (@bi_rtc) 4 := {}.

  Local Definition bi_tc_pre (R : A → A → PROP)
      (x2 : A) (rec : A → PROP) (x1 : A) : PROP :=
    R x1 x2 ∨ ∃ x', R x1 x' ∗ rec x'.

  (** The transitive closure. *)
  Definition bi_tc (R : A → A → PROP) (x1 x2 : A) : PROP :=
    bi_least_fixpoint (bi_tc_pre R x2) x1.

  Global Instance: Params (@bi_tc) 4 := {}.

  (** Reductions of exactly [n] steps. *)
  Fixpoint bi_nsteps (R : A → A → PROP) (n : nat) (x1 x2 : A) : PROP :=
    match n with
    | 0    => <affine> (x1 ≡ x2)
    | S n' => ∃ x', R x1 x' ∗ bi_nsteps R n' x' x2
    end.

  Global Instance: Params (@bi_nsteps) 5 := {}.
End definitions.

Local Instance bi_rtc_pre_mono {PROP : bi} `{!BiInternalEq PROP}
    {A : ofe} (R : A → A → PROP) `{!NonExpansive2 R} (x : A) :
  BiMonoPred (bi_rtc_pre R x).
Proof.
  constructor; [|solve_proper].
  iIntros (rec1 rec2 ??) "#H". iIntros (x1) "[Hrec | Hrec]".
  { by iLeft. }
  iRight.
  iDestruct "Hrec" as (x') "[HP Hrec]".
  iDestruct ("H" with "Hrec") as "Hrec". eauto with iFrame.
Qed.

Global Instance bi_rtc_ne {PROP : bi} `{!BiInternalEq PROP} {A : ofe} (R : A → A → PROP) :
  NonExpansive2 (bi_rtc R).
Proof.
  intros n x1 x2 Hx y1 y2 Hy. rewrite /bi_rtc Hx. f_equiv=> rec z.
  solve_proper.
Qed.

Global Instance bi_rtc_proper {PROP : bi} `{!BiInternalEq PROP} {A : ofe} (R : A → A → PROP)
  : Proper ((≡) ==> (≡) ==> (⊣⊢)) (bi_rtc R).
Proof. apply ne_proper_2. apply _. Qed.

Local Instance bi_tc_pre_mono `{!BiInternalEq PROP}
    {A : ofe} (R : A → A → PROP) `{NonExpansive2 R} (x : A) :
  BiMonoPred (bi_tc_pre R x).
Proof.
  constructor; [|solve_proper].
  iIntros (rec1 rec2 ??) "#H". iIntros (x1) "Hrec".
  iDestruct "Hrec" as "[Hrec | Hrec]".
  { by iLeft. }
  iDestruct "Hrec" as (x') "[HR Hrec]".
  iRight. iExists x'. iFrame "HR". by iApply "H".
Qed.

Global Instance bi_tc_ne `{!BiInternalEq PROP} {A : ofe}
    (R : A → A → PROP) `{NonExpansive2 R} :
  NonExpansive2 (bi_tc R).
Proof.
  intros n x1 x2 Hx y1 y2 Hy. rewrite /bi_tc Hx. f_equiv=> rec z.
  solve_proper.
Qed.

Global Instance bi_tc_proper `{!BiInternalEq PROP} {A : ofe}
    (R : A → A → PROP) `{NonExpansive2 R}
  : Proper ((≡) ==> (≡) ==> (⊣⊢)) (bi_tc R).
Proof. apply ne_proper_2. apply _. Qed.

Global Instance bi_nsteps_ne {PROP : bi} `{!BiInternalEq PROP}
    {A : ofe} (R : A → A → PROP) `{NonExpansive2 R} (n : nat) :
  NonExpansive2 (bi_nsteps R n).
Proof. induction n; solve_proper. Qed.

Global Instance bi_nsteps_proper {PROP : bi} `{!BiInternalEq PROP}
    {A : ofe} (R : A → A → PROP) `{NonExpansive2 R} (n : nat)
  : Proper ((≡) ==> (≡) ==> (⊣⊢)) (bi_nsteps R n).
Proof. apply ne_proper_2. apply _. Qed.

(** * General theorems *)
Section general.
  Context {PROP : bi} `{!BiInternalEq PROP}.
  Context {A : ofe}.
  Context (R : A → A → PROP) `{!NonExpansive2 R}.

  (** ** Results about the reflexive-transitive closure [bi_rtc] *)
  Local Lemma bi_rtc_unfold (x1 x2 : A) :
    bi_rtc R x1 x2 ≡ bi_rtc_pre R x2 (λ x1, bi_rtc R x1 x2) x1.
  Proof. by rewrite /bi_rtc; rewrite -least_fixpoint_unfold. Qed.

  Lemma bi_rtc_strong_ind_l x2 Φ :
    NonExpansive Φ →
    □ (∀ x1, <affine> (x1 ≡ x2) ∨ (∃ x', R x1 x' ∗ (Φ x' ∧ bi_rtc R x' x2)) -∗ Φ x1) -∗
    ∀ x1, bi_rtc R x1 x2 -∗ Φ x1.
 Proof.
    iIntros (?) "#IH". rewrite /bi_rtc.
    by iApply (least_fixpoint_ind (bi_rtc_pre R x2) with "IH").
  Qed.

  Lemma bi_rtc_ind_l x2 Φ :
    NonExpansive Φ →
    □ (∀ x1, <affine> (x1 ≡ x2) ∨ (∃ x', R x1 x' ∗ Φ x') -∗ Φ x1) -∗
    ∀ x1, bi_rtc R x1 x2 -∗ Φ x1.
  Proof.
    iIntros (?) "#IH". rewrite /bi_rtc.
    by iApply (least_fixpoint_iter (bi_rtc_pre R x2) with "IH").
  Qed.

  Lemma bi_rtc_refl x : ⊢ bi_rtc R x x.
  Proof. rewrite bi_rtc_unfold. by iLeft. Qed.

  Lemma bi_rtc_l x1 x2 x3 : R x1 x2 -∗ bi_rtc R x2 x3 -∗ bi_rtc R x1 x3.
  Proof.
    iIntros "H1 H2".
    iEval (rewrite bi_rtc_unfold /bi_rtc_pre). iRight.
    iExists x2. iFrame.
  Qed.

  Lemma bi_rtc_once x1 x2 : R x1 x2 -∗ bi_rtc R x1 x2.
  Proof. iIntros "H". iApply (bi_rtc_l with "H"). iApply bi_rtc_refl. Qed.

  Lemma bi_rtc_trans x1 x2 x3 : bi_rtc R x1 x2 -∗ bi_rtc R x2 x3 -∗ bi_rtc R x1 x3.
  Proof.
    iRevert (x1).
    iApply bi_rtc_ind_l.
    { solve_proper. }
    iIntros "!>" (x1) "[H | H] H2".
    { by iRewrite "H". }
    iDestruct "H" as (x') "[H IH]".
    iApply (bi_rtc_l with "H").
    by iApply "IH".
  Qed.

  Lemma bi_rtc_r x y z : bi_rtc R x y -∗ R y z -∗ bi_rtc R x z.
  Proof.
    iIntros "H H'".
    iApply (bi_rtc_trans with "H").
    by iApply bi_rtc_once.
  Qed.

  Lemma bi_rtc_inv x z :
    bi_rtc R x z -∗ <affine> (x ≡ z) ∨ ∃ y, R x y ∗ bi_rtc R y z.
  Proof. rewrite bi_rtc_unfold. iIntros "[H | H]"; eauto. Qed.

  Global Instance bi_rtc_affine :
    (∀ x y, Affine (R x y)) →
    ∀ x y, Affine (bi_rtc R x y).
  Proof. intros. apply least_fixpoint_affine; apply _. Qed.

  (* FIXME: It would be nicer to use the least_fixpoint_persistent lemmas,
            but they seem to weak. *)
  Global Instance bi_rtc_persistent :
    (∀ x y, Persistent (R x y)) →
    ∀ x y, Persistent (bi_rtc R x y).
  Proof.
    intros ? x y. rewrite /Persistent.
    iRevert (x). iApply bi_rtc_ind_l; first solve_proper.
    iIntros "!>" (x) "[#Heq | (%x' & #Hxx' & #Hx'y)]".
    { iRewrite "Heq". iApply bi_rtc_refl. }
    iApply (bi_rtc_l with "Hxx' Hx'y").
  Qed.

  (** ** Results about the transitive closure [bi_tc] *)
  Local Lemma bi_tc_unfold (x1 x2 : A) :
    bi_tc R x1 x2 ≡ bi_tc_pre R x2 (λ x1, bi_tc R x1 x2) x1.
  Proof. by rewrite /bi_tc; rewrite -least_fixpoint_unfold. Qed.

  Lemma bi_tc_strong_ind_l x2 Φ :
    NonExpansive Φ →
    □ (∀ x1, (R x1 x2 ∨ (∃ x', R x1 x' ∗ (Φ x' ∧ bi_tc R x' x2))) -∗ Φ x1) -∗
    ∀ x1, bi_tc R x1 x2 -∗ Φ x1.
  Proof.
    iIntros (?) "#IH". rewrite /bi_tc.
    iApply (least_fixpoint_ind (bi_tc_pre R x2) with "IH").
  Qed.

  Lemma bi_tc_ind_l x2 Φ :
    NonExpansive Φ →
    □ (∀ x1, (R x1 x2 ∨ (∃ x', R x1 x' ∗ Φ x')) -∗ Φ x1) -∗
    ∀ x1, bi_tc R x1 x2 -∗ Φ x1.
  Proof.
    iIntros (?) "#IH". rewrite /bi_tc.
    iApply (least_fixpoint_iter (bi_tc_pre R x2) with "IH").
  Qed.

  Lemma bi_tc_l x1 x2 x3 : R x1 x2 -∗ bi_tc R x2 x3 -∗ bi_tc R x1 x3.
  Proof.
    iIntros "H1 H2".
    iEval (rewrite bi_tc_unfold /bi_tc_pre).
    iRight. iExists x2. iFrame.
  Qed.

  Lemma bi_tc_once x1 x2 : R x1 x2 -∗ bi_tc R x1 x2.
  Proof.
    iIntros "H".
    iEval (rewrite bi_tc_unfold /bi_tc_pre).
    by iLeft.
  Qed.

  Lemma bi_tc_trans x1 x2 x3 : bi_tc R x1 x2 -∗ bi_tc R x2 x3 -∗ bi_tc R x1 x3.
  Proof.
    iRevert (x1).
    iApply bi_tc_ind_l.
    { solve_proper. }
    iIntros "!>" (x1) "H H2".
    iDestruct "H" as "[H | H]".
    { iApply (bi_tc_l with "H H2"). }
    iDestruct "H" as (x') "[H IH]".
    iApply (bi_tc_l with "H").
    by iApply "IH".
  Qed.

  Lemma bi_tc_r x y z : bi_tc R x y -∗ R y z -∗ bi_tc R x z.
  Proof.
    iIntros "H H'".
    iApply (bi_tc_trans with "H").
    by iApply bi_tc_once.
  Qed.

  Lemma bi_tc_rtc_l x y z : bi_rtc R x y -∗ bi_tc R y z -∗ bi_tc R x z.
  Proof.
    iRevert (x).
    iApply bi_rtc_ind_l. { solve_proper. }
    iIntros "!>" (x) "[Heq | H] Hyz".
    { by iRewrite "Heq". }
    iDestruct "H" as (x') "[H IH]".
    iApply (bi_tc_l with "H").
    by iApply "IH".
  Qed.

  Lemma bi_tc_rtc_r x y z : bi_tc R x y -∗ bi_rtc R y z -∗ bi_tc R x z.
  Proof.
    iIntros "Hxy Hyz".
    iRevert (x) "Hxy". iRevert (y) "Hyz".
    iApply bi_rtc_ind_l. { solve_proper. }
    iIntros "!>" (y) "[Heq | H] %x Hxy".
    { by iRewrite -"Heq". }
    iDestruct "H" as (y') "[H IH]".
    iApply "IH". iApply (bi_tc_r with "Hxy H").
  Qed.

  Lemma bi_tc_rtc x y : bi_tc R x y -∗ bi_rtc R x y.
  Proof.
    iRevert (x). iApply bi_tc_ind_l. { solve_proper. }
    iIntros "!>" (x) "[Hxy | H]".
    { by iApply bi_rtc_once. }
    iDestruct "H" as (x') "[H H']".
    iApply (bi_rtc_l with "H H'").
  Qed.

  Global Instance bi_tc_affine :
    (∀ x y, Affine (R x y)) →
    ∀ x y, Affine (bi_tc R x y).
  Proof. intros. apply least_fixpoint_affine; apply _. Qed.

  Global Instance bi_tc_absorbing :
    (∀ x y, Absorbing (R x y)) →
    ∀ x y, Absorbing (bi_tc R x y).
  Proof. intros. apply least_fixpoint_absorbing; apply _. Qed.

  (* FIXME: It would be nicer to use the least_fixpoint_persistent lemmas,
            but they seem to weak. *)
  Global Instance bi_tc_persistent :
    (∀ x y, Persistent (R x y)) →
    ∀ x y, Persistent (bi_tc R x y).
  Proof.
    intros ? x y. rewrite /Persistent.
    iRevert (x). iApply bi_tc_ind_l; first solve_proper.
    iIntros "!# %x [#H|(%x'&#?&#?)] !>"; first by iApply bi_tc_once.
    by iApply bi_tc_l.
  Qed.

  (** ** Results about [bi_nsteps] *)
  Lemma bi_nsteps_O x : ⊢ bi_nsteps R 0 x x.
  Proof. auto. Qed.
  Lemma bi_nsteps_once x y : R x y -∗ bi_nsteps R 1 x y.
  Proof. simpl. eauto. Qed.
  Lemma bi_nsteps_once_inv x y : bi_nsteps R 1 x y -∗ R x y.
  Proof. iDestruct 1 as (x') "[Hxx' Heq]". by iRewrite -"Heq". Qed.
  Lemma bi_nsteps_l n x y z : R x y -∗ bi_nsteps R n y z -∗ bi_nsteps R (S n) x z.
  Proof. iIntros "? ?". iExists y. iFrame. Qed.

  Lemma bi_nsteps_trans n m x y z :
    bi_nsteps R n x y -∗ bi_nsteps R m y z -∗ bi_nsteps R (n + m) x z.
  Proof.
    iInduction n as [|n] "IH" forall (x); simpl.
    - iIntros "Heq". iRewrite "Heq". auto.
    - iDestruct 1 as (x') "[Hxx' Hx'y]". iIntros "Hyz".
      iExists x'. iFrame "Hxx'". iApply ("IH" with "Hx'y Hyz").
  Qed.

  Lemma bi_nsteps_r n x y z :
    bi_nsteps R n x y -∗ R y z -∗ bi_nsteps R (S n) x z.
  Proof.
    iIntros "Hxy Hyx". rewrite -Nat.add_1_r.
    iApply (bi_nsteps_trans with "Hxy").
    by iApply bi_nsteps_once.
  Qed.

  Lemma bi_nsteps_add_inv n m x z :
    bi_nsteps R (n + m) x z ⊢ ∃ y, bi_nsteps R n x y ∗ bi_nsteps R m y z.
  Proof.
    iInduction n as [|n] "IH" forall (x).
    - iIntros "Hxz". iExists x. auto.
    - iDestruct 1 as (y) "[Hxy Hyz]".
      iDestruct ("IH" with "Hyz") as (y') "[Hyy' Hy'z]".
      iExists y'. iFrame "Hy'z".
      iApply (bi_nsteps_l with "Hxy Hyy'").
  Qed.

  Lemma bi_nsteps_inv_r n x z :
    bi_nsteps R (S n) x z ⊢ ∃ y, bi_nsteps R n x y ∗ R y z.
  Proof.
    rewrite -Nat.add_1_r bi_nsteps_add_inv /=.
    iDestruct 1 as (y) "[Hxy (%x' & Hxx' & Heq)]".
    iExists y. iRewrite -"Heq". iFrame.
  Qed.

  (** ** Equivalences between closure operators *)
  Lemma bi_rtc_tc x y : bi_rtc R x y ⊣⊢ <affine> (x ≡ y) ∨ bi_tc R x y.
  Proof.
    iSplit.
    - iRevert (x). iApply bi_rtc_ind_l. { solve_proper. }
      iIntros "!>" (x) "[Heq | H]".
      { by iLeft. }
      iRight.
      iDestruct "H" as (x') "[H [Heq | IH]]".
      { iRewrite -"Heq". by iApply bi_tc_once. }
      iApply (bi_tc_l with "H IH").
    - iIntros "[Heq | Hxy]".
      { iRewrite "Heq". iApply bi_rtc_refl. }
      by iApply bi_tc_rtc.
  Qed.

  Lemma bi_tc_nsteps x y :
    bi_tc R x y ⊣⊢ ∃ n, <affine> ⌜0 < n⌝ ∗ bi_nsteps R n x y.
  Proof.
    iSplit.
    - iRevert (x). iApply bi_tc_ind_l. { solve_proper. }
      iIntros "!>" (x) "[Hxy | H]".
      { iExists 1. iSplitR; first auto with lia.
        iApply (bi_nsteps_l with "Hxy"). iApply bi_nsteps_O. }
      iDestruct "H" as (x') "[Hxx' IH]".
      iDestruct "IH" as (n ?) "Hx'y".
      iExists (S n). iSplitR; first auto with lia.
      iApply (bi_nsteps_l with "Hxx' Hx'y").
    - iDestruct 1 as (n ?) "Hxy".
      iInduction n as [|n] "IH" forall (y). { lia. }
      rewrite bi_nsteps_inv_r.
      iDestruct "Hxy" as (x') "[Hxx' Hx'y]".
      destruct n.
      { simpl. iRewrite "Hxx'". by iApply bi_tc_once. }
      iApply (bi_tc_r with "[Hxx'] Hx'y").
      iApply ("IH" with "[%] Hxx'"). lia.
  Qed.

  Lemma bi_rtc_nsteps x y : bi_rtc R x y ⊣⊢ ∃ n, bi_nsteps R n x y.
  Proof.
    iSplit.
    - iRevert (x). iApply bi_rtc_ind_l. { solve_proper. }
      iIntros "!>" (x) "[Heq | H]".
      { iExists 0. iRewrite "Heq". iApply bi_nsteps_O. }
      iDestruct "H" as (x') "[Hxx' IH]".
      iDestruct "IH" as (n) "Hx'y".
      iExists (S n). iApply (bi_nsteps_l with "Hxx' Hx'y").
    - iDestruct 1 as (n) "Hxy".
      iInduction n as [|n] "IH" forall (y).
      { simpl. iRewrite "Hxy". iApply bi_rtc_refl. }
      iDestruct (bi_nsteps_inv_r with "Hxy") as (x') "[Hxx' Hx'y]".
      iApply (bi_rtc_r with "[Hxx'] Hx'y").
      by iApply "IH".
  Qed.
End general.

Section timeless.
  Context {PROP : bi} `{!BiInternalEq PROP, !BiAffine PROP}.
  Context `{!OfeDiscrete A}.
  Context (R : A → A → PROP) `{!NonExpansive2 R}.

  Global Instance bi_nsteps_timeless n :
    (∀ x y, Timeless (R x y)) →
    ∀ x y, Timeless (bi_nsteps R n x y).
  Proof. induction n; apply _. Qed.

  Global Instance bi_rtc_timeless :
    (∀ x y, Timeless (R x y)) →
    ∀ x y, Timeless (bi_rtc R x y).
  Proof. intros ? x y. rewrite bi_rtc_nsteps. apply _. Qed.

  Global Instance bi_tc_timeless :
    (∀ x y, Timeless (R x y)) →
    ∀ x y, Timeless (bi_tc R x y).
  Proof. intros ? x y. rewrite bi_tc_nsteps. apply _. Qed.
End timeless.

Global Typeclasses Opaque bi_rtc.
Global Typeclasses Opaque bi_tc.
Global Typeclasses Opaque bi_nsteps.
