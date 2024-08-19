(** This file collects definitions and theorems on abstract rewriting systems.
These are particularly useful as we define the operational semantics as a
small step semantics. *)
From stdpp Require Export sets well_founded.
From stdpp Require Import options.

(** * Definitions *)
Section definitions.
  Context `(R : relation A).

  (** An element is reducible if a step is possible. *)
  Definition red (x : A) := ∃ y, R x y.

  (** An element is in normal form if no further steps are possible. *)
  Definition nf (x : A) := ¬red x.

  (** The symmetric closure. *)
  Definition sc : relation A := λ x y, R x y ∨ R y x.

  (** The reflexive transitive closure. *)
  Inductive rtc : relation A :=
    | rtc_refl x : rtc x x
    | rtc_l x y z : R x y → rtc y z → rtc x z.

  (** The reflexive transitive closure for setoids. *)
  Inductive rtcS `{Equiv A} : relation A :=
    | rtcS_refl x y : x ≡ y → rtcS x y
    | rtcS_l x y z : R x y → rtcS y z → rtcS x z.

  (** Reductions of exactly [n] steps. *)
  Inductive nsteps : nat → relation A :=
    | nsteps_O x : nsteps 0 x x
    | nsteps_l n x y z : R x y → nsteps n y z → nsteps (S n) x z.

  (** Reductions of at most [n] steps. *)
  Inductive bsteps : nat → relation A :=
    | bsteps_refl n x : bsteps n x x
    | bsteps_l n x y z : R x y → bsteps n y z → bsteps (S n) x z.

  (** The transitive closure. *)
  Inductive tc : relation A :=
    | tc_once x y : R x y → tc x y
    | tc_l x y z : R x y → tc y z → tc x z.

  (** An element [x] is universally looping if all paths starting at [x]
  are infinite. *)
  CoInductive all_loop : A → Prop :=
    | all_loop_do_step x : red x → (∀ y, R x y → all_loop y) → all_loop x.

  (** An element [x] is existentally looping if some path starting at [x]
  is infinite. *)
  CoInductive ex_loop : A → Prop :=
    | ex_loop_do_step x y : R x y → ex_loop y → ex_loop x.
End definitions.

(** The reflexive transitive symmetric closure. *)
Definition rtsc {A} (R : relation A) := rtc (sc R).

(** Weakly and strongly normalizing elements. *)
Definition wn {A} (R : relation A) (x : A) := ∃ y, rtc R x y ∧ nf R y.

Notation sn R := (Acc (flip R)).

(** The various kinds of "confluence" properties. Any relation that has the
diamond property is confluent, and any confluent relation is locally confluent.
The naming convention are taken from "Term Rewriting and All That" by Baader and
Nipkow. *)
Definition diamond {A} (R : relation A) :=
  ∀ x y1 y2, R x y1 → R x y2 → ∃ z, R y1 z ∧ R y2 z.

Definition confluent {A} (R : relation A) :=
  diamond (rtc R).

Definition locally_confluent {A} (R : relation A) :=
  ∀ x y1 y2, R x y1 → R x y2 → ∃ z, rtc R y1 z ∧ rtc R y2 z.

Global Hint Unfold nf red : core.

(** * General theorems *)
Section general.
  Context `{R : relation A}.

  Local Hint Constructors rtc nsteps bsteps tc : core.

  (** ** Results about the reflexive-transitive closure [rtc] *)
  Lemma rtc_transitive x y z : rtc R x y → rtc R y z → rtc R x z.
  Proof. induction 1; eauto. Qed.

  (* We give this instance a lower-than-usual priority because [setoid_rewrite]
     queries for [@Reflexive Prop ?r] in the hope of [iff_reflexive] getting
     picked as the instance.  [rtc_reflexive] overlaps with that, leading to
     backtracking.  We cannot set [Hint Mode] because that query must not fail,
     but we can at least avoid picking [rtc_reflexive].

     See Coq bug https://github.com/coq/coq/issues/7916 and the test
     [tests.typeclasses.test_setoid_rewrite]. *)
  Global Instance rtc_po : PreOrder (rtc R) | 10.
  Proof. split; [exact (@rtc_refl A R) | exact rtc_transitive]. Qed.

  (* Not an instance, related to the issue described above, this sometimes makes
  [setoid_rewrite] queries loop. *)
  Lemma rtc_equivalence : Symmetric R → Equivalence (rtc R).
  Proof.
    split; try apply _.
    intros x y. induction 1 as [|x1 x2 x3]; [done|trans x2; eauto].
  Qed.

  Lemma rtc_once x y : R x y → rtc R x y.
  Proof. eauto. Qed.
  Lemma rtc_r x y z : rtc R x y → R y z → rtc R x z.
  Proof. intros. etrans; eauto. Qed.
  Lemma rtc_inv x z : rtc R x z → x = z ∨ ∃ y, R x y ∧ rtc R y z.
  Proof. inv 1; eauto. Qed.
  Lemma rtc_ind_l (P : A → Prop) (z : A)
    (Prefl : P z) (Pstep : ∀ x y, R x y → rtc R y z → P y → P x) :
    ∀ x, rtc R x z → P x.
  Proof. induction 1; eauto. Qed.
  Lemma rtc_ind_r_weak (P : A → A → Prop)
    (Prefl : ∀ x, P x x) (Pstep : ∀ x y z, rtc R x y → R y z → P x y → P x z) :
    ∀ x z, rtc R x z → P x z.
  Proof.
    cut (∀ y z, rtc R y z → ∀ x, rtc R x y → P x y → P x z).
    { eauto using rtc_refl. }
    induction 1; eauto using rtc_r.
  Qed.
  Lemma rtc_ind_r (P : A → Prop) (x : A)
    (Prefl : P x) (Pstep : ∀ y z, rtc R x y → R y z → P y → P z) :
    ∀ z, rtc R x z → P z.
  Proof.
    intros z p. revert x z p Prefl Pstep. refine (rtc_ind_r_weak _ _ _); eauto.
  Qed.
  Lemma rtc_inv_r x z : rtc R x z → x = z ∨ ∃ y, rtc R x y ∧ R y z.
  Proof. revert z. apply rtc_ind_r; eauto. Qed.

  Lemma rtc_nf x y : rtc R x y → nf R x → x = y.
  Proof. destruct 1 as [x|x y1 y2]; [done|]. intros []; eauto. Qed.

  Lemma rtc_congruence {B} (f : A → B) (R' : relation B) x y :
    (∀ x y, R x y → R' (f x) (f y)) → rtc R x y → rtc R' (f x) (f y).
  Proof. induction 2; econstructor; eauto. Qed.

  (** ** Results about [nsteps] *)
  Lemma nsteps_once x y : R x y → nsteps R 1 x y.
  Proof. eauto. Qed.
  Lemma nsteps_once_inv x y : nsteps R 1 x y → R x y.
  Proof. inv 1 as [|???? Hhead Htail]; by inv Htail. Qed.
  Lemma nsteps_trans n m x y z :
    nsteps R n x y → nsteps R m y z → nsteps R (n + m) x z.
  Proof. induction 1; simpl; eauto. Qed.
  Lemma nsteps_r n x y z : nsteps R n x y → R y z → nsteps R (S n) x z.
  Proof. induction 1; eauto. Qed.

  Lemma nsteps_add_inv n m x z :
    nsteps R (n + m) x z → ∃ y, nsteps R n x y ∧ nsteps R m y z.
  Proof.
    revert x.
    induction n as [|n IH]; intros x Hx; simpl; [by eauto|].
    inv Hx; naive_solver.
  Qed.

  Lemma nsteps_inv_r n x z : nsteps R (S n) x z → ∃ y, nsteps R n x y ∧ R y z.
  Proof.
    rewrite <- PeanoNat.Nat.add_1_r.
    intros (?&?&?%nsteps_once_inv)%nsteps_add_inv; eauto.
  Qed.

  Lemma nsteps_congruence {B} (f : A → B) (R' : relation B) n x y :
    (∀ x y, R x y → R' (f x) (f y)) → nsteps R n x y → nsteps R' n (f x) (f y).
  Proof. induction 2; econstructor; eauto. Qed.

  (** ** Results about [bsteps] *)
  Lemma bsteps_once n x y : R x y → bsteps R (S n) x y.
  Proof. eauto. Qed.
  Lemma bsteps_add_r n m x y :
    bsteps R n x y → bsteps R (n + m) x y.
  Proof. induction 1; simpl; eauto. Qed.
  Lemma bsteps_weaken n m x y :
    n ≤ m → bsteps R n x y → bsteps R m x y.
  Proof.
    intros. rewrite (Nat.le_add_sub n m); auto using bsteps_add_r.
  Qed.
  Lemma bsteps_add_l n m x y :
    bsteps R n x y → bsteps R (m + n) x y.
  Proof. apply bsteps_weaken. auto with arith. Qed.
  Lemma bsteps_S n x y :  bsteps R n x y → bsteps R (S n) x y.
  Proof. apply bsteps_weaken. lia. Qed.
  Lemma bsteps_trans n m x y z :
    bsteps R n x y → bsteps R m y z → bsteps R (n + m) x z.
  Proof. induction 1; simpl; eauto using bsteps_add_l. Qed.
  Lemma bsteps_r n x y z : bsteps R n x y → R y z → bsteps R (S n) x z.
  Proof. induction 1; eauto. Qed.
  Lemma bsteps_ind_r (P : nat → A → Prop) (x : A)
    (Prefl : ∀ n, P n x)
    (Pstep : ∀ n y z, bsteps R n x y → R y z → P n y → P (S n) z) :
    ∀ n z, bsteps R n x z → P n z.
  Proof.
    cut (∀ m y z, bsteps R m y z → ∀ n,
      bsteps R n x y → (∀ m', n ≤ m' ∧ m' ≤ n + m → P m' y) → P (n + m) z).
    { intros help n. change n with (0 + n). eauto. }
    induction 1 as [|m x' y z p2 p3 IH]; [by eauto with arith|].
    intros n p1 H. rewrite <-plus_n_Sm.
    apply (IH (S n)); [by eauto using bsteps_r |].
    intros [|m'] [??]; [lia |]. apply Pstep with x'.
    - apply bsteps_weaken with n; intuition lia.
    - done.
    - apply H; intuition lia.
  Qed.

  Lemma bsteps_congruence {B} (f : A → B) (R' : relation B) n x y :
    (∀ x y, R x y → R' (f x) (f y)) → bsteps R n x y → bsteps R' n (f x) (f y).
  Proof. induction 2; econstructor; eauto. Qed.

  (** ** Results about the transitive closure [tc] *)
  Lemma tc_transitive x y z : tc R x y → tc R y z → tc R x z.
  Proof. induction 1; eauto. Qed.
  Global Instance tc_transitive' : Transitive (tc R).
  Proof. exact tc_transitive. Qed.
  Lemma tc_r x y z : tc R x y → R y z → tc R x z.
  Proof. intros. etrans; eauto. Qed.
  Lemma tc_rtc_l x y z : rtc R x y → tc R y z → tc R x z.
  Proof. induction 1; eauto. Qed.
  Lemma tc_rtc_r x y z : tc R x y → rtc R y z → tc R x z.
  Proof. intros Hxy Hyz. revert x Hxy. induction Hyz; eauto using tc_r. Qed.
  Lemma tc_rtc x y : tc R x y → rtc R x y.
  Proof. induction 1; eauto. Qed.

  Lemma red_tc x : red (tc R) x ↔ red R x.
  Proof.
    split.
    - intros [y []]; eexists; eauto.
    - intros [y HR]. exists y. by apply tc_once.
  Qed.

  Lemma tc_congruence {B} (f : A → B) (R' : relation B) x y :
    (∀ x y, R x y → R' (f x) (f y)) → tc R x y → tc R' (f x) (f y).
  Proof. induction 2; econstructor; by eauto. Qed.

  (** ** Results about the symmetric closure [sc] *)
  Global Instance sc_symmetric : Symmetric (sc R).
  Proof. unfold Symmetric, sc. naive_solver. Qed.

  Lemma sc_lr x y : R x y → sc R x y.
  Proof. by left. Qed.
  Lemma sc_rl x y : R y x → sc R x y.
  Proof. by right. Qed.

  Lemma sc_congruence {B} (f : A → B) (R' : relation B) x y :
    (∀ x y, R x y → R' (f x) (f y)) → sc R x y → sc R' (f x) (f y).
  Proof. induction 2; econstructor; by eauto. Qed.

  (** ** Equivalences between closure operators *)
  Lemma bsteps_nsteps n x y : bsteps R n x y ↔ ∃ n', n' ≤ n ∧ nsteps R n' x y.
  Proof.
    split.
    - induction 1 as [|n x1 x2 y ?? (n'&?&?)].
      + exists 0; naive_solver eauto with lia.
      + exists (S n'); naive_solver eauto with lia.
    - intros (n'&Hn'&Hsteps). apply bsteps_weaken with n'; [done|].
      clear Hn'. induction Hsteps; eauto.
  Qed.

  Lemma tc_nsteps x y : tc R x y ↔ ∃ n, 0 < n ∧ nsteps R n x y.
  Proof.
    split.
    - induction 1 as [|x1 x2 y ?? (n&?&?)].
      { exists 1. eauto using nsteps_once with lia. }
      exists (S n); eauto using nsteps_l.
    - intros (n & ? & Hstep). induction Hstep as [|n x1 x2 y ? Hstep]; [lia|].
      destruct Hstep; eauto with lia.
  Qed.

  Lemma rtc_tc x y : rtc R x y ↔ x = y ∨ tc R x y.
  Proof.
    split; [|naive_solver eauto using tc_rtc].
    induction 1; naive_solver.
  Qed.

  Lemma rtc_nsteps x y : rtc R x y ↔ ∃ n, nsteps R n x y.
  Proof.
    split.
    - induction 1; naive_solver.
    - intros [n Hsteps]. induction Hsteps; naive_solver.
  Qed.
  Lemma rtc_nsteps_1 x y : rtc R x y → ∃ n, nsteps R n x y.
  Proof. rewrite rtc_nsteps. naive_solver. Qed.
  Lemma rtc_nsteps_2 n x y : nsteps R n x y → rtc R x y.
  Proof. rewrite rtc_nsteps. naive_solver. Qed.

  Lemma rtc_bsteps x y : rtc R x y ↔ ∃ n, bsteps R n x y.
  Proof. rewrite rtc_nsteps. setoid_rewrite bsteps_nsteps. naive_solver. Qed.
  Lemma rtc_bsteps_1 x y : rtc R x y → ∃ n, bsteps R n x y.
  Proof. rewrite rtc_bsteps. naive_solver. Qed.
  Lemma rtc_bsteps_2 n x y : bsteps R n x y → rtc R x y.
  Proof. rewrite rtc_bsteps. naive_solver. Qed.

  Lemma nsteps_list n x y :
    nsteps R n x y ↔ ∃ l,
      length l = S n ∧
      head l = Some x ∧
      last l = Some y ∧
      ∀ i a b, l !! i = Some a → l !! S i = Some b → R a b.
  Proof.
    setoid_rewrite head_lookup. split.
    - induction 1 as [x|n' x x' y ?? IH].
      { exists [x]; naive_solver. }
      destruct IH as (l & Hlen & Hfirst & Hlast & Hcons).
      exists (x :: l). simpl. rewrite Hlen, last_cons, Hlast.
      split_and!; [done..|]. intros [|i]; naive_solver.
    - intros ([|x' l]&?&Hfirst&Hlast&Hcons); simplify_eq/=.
      revert x Hlast Hcons.
      induction l as [|x1 l IH]; intros x2 Hlast Hcons; simplify_eq/=; [constructor|].
      econstructor; [by apply (Hcons 0)|].
      apply IH; [done|]. intros i. apply (Hcons (S i)).
  Qed.

  Lemma bsteps_list n x y :
    bsteps R n x y ↔ ∃ l,
      length l ≤ S n ∧
      head l = Some x ∧
      last l = Some y ∧
      ∀ i a b, l !! i = Some a → l !! S i = Some b → R a b.
  Proof.
    rewrite bsteps_nsteps. split.
    - intros (n'&?&(l&?&?&?&?)%nsteps_list). exists l; eauto with lia.
    - intros (l&?&?&?&?). exists (pred (length l)). split; [lia|].
      apply nsteps_list. exists l. split; [|by eauto]. by destruct l.
  Qed.

  Lemma rtc_list x y :
    rtc R x y ↔ ∃ l,
      head l = Some x ∧
      last l = Some y ∧
      ∀ i a b, l !! i = Some a → l !! S i = Some b → R a b.
  Proof.
    rewrite rtc_bsteps. split.
    - intros (n'&(l&?&?&?&?)%bsteps_list). exists l; eauto with lia.
    - intros (l&?&?&?). exists (pred (length l)).
      apply bsteps_list. exists l. eauto with lia.
  Qed.

  Lemma tc_list x y :
    tc R x y ↔ ∃ l,
      1 < length l ∧
      head l = Some x ∧
      last l = Some y ∧
      ∀ i a b, l !! i = Some a → l !! S i = Some b → R a b.
  Proof.
    rewrite tc_nsteps. split.
    - intros (n'&?&(l&?&?&?&?)%nsteps_list). exists l; eauto with lia.
    - intros (l&?&?&?&?). exists (pred (length l)).
      split; [lia|]. apply nsteps_list. exists l. eauto with lia.
  Qed.

  Lemma ex_loop_inv x :
    ex_loop R x →
    ∃ x', R x x' ∧ ex_loop R x'.
  Proof. inv 1; eauto. Qed.

End general.

Section more_general.
  Context `{R : relation A}.

  (** ** Results about the reflexive-transitive-symmetric closure [rtsc] *)
  Global Instance rtsc_equivalence : Equivalence (rtsc R) | 10.
  Proof. apply rtc_equivalence, _. Qed.

  Lemma rtsc_lr x y : R x y → rtsc R x y.
  Proof. unfold rtsc. eauto using sc_lr, rtc_once. Qed.
  Lemma rtsc_rl x y : R y x → rtsc R x y.
  Proof. unfold rtsc. eauto using sc_rl, rtc_once. Qed.
  Lemma rtc_rtsc_rl x y : rtc R x y → rtsc R x y.
  Proof. induction 1; econstructor; eauto using sc_lr. Qed.
  Lemma rtc_rtsc_lr x y : rtc R y x → rtsc R x y.
  Proof. intros. symmetry. eauto using rtc_rtsc_rl. Qed.

  Lemma rtsc_congruence {B} (f : A → B) (R' : relation B) x y :
    (∀ x y, R x y → R' (f x) (f y)) → rtsc R x y → rtsc R' (f x) (f y).
  Proof. unfold rtsc; eauto using rtc_congruence, sc_congruence. Qed.

  Lemma ex_loop_tc x :
    ex_loop (tc R) x ↔ ex_loop R x.
  Proof.
    split.
    - revert x; cofix IH.
      intros x (y & Hstep & Hloop')%ex_loop_inv.
      destruct Hstep as [x y Hstep|x y z Hstep Hsteps].
      + econstructor; eauto.
      + econstructor; [by eauto|].
        eapply IH. econstructor; eauto.
    - revert x; cofix IH.
      intros x (y & Hstep & Hloop')%ex_loop_inv.
      econstructor; eauto using tc_once.
  Qed.

End more_general.

Section properties.
  Context `{R : relation A}.

  Local Hint Constructors rtc nsteps bsteps tc : core.

  Lemma nf_wn x : nf R x → wn R x.
  Proof. intros. exists x; eauto. Qed.
  Lemma wn_step x y : wn R y → R x y → wn R x.
  Proof. intros (z & ? & ?) ?. exists z; eauto. Qed.
  Lemma wn_step_rtc x y : wn R y → rtc R x y → wn R x.
  Proof. induction 2; eauto using wn_step. Qed.

  Lemma nf_sn x : nf R x → sn R x.
  Proof. intros Hnf. constructor; intros y Hxy. destruct Hnf; eauto. Qed.
  Lemma sn_step x y : sn R x → R x y → sn R y.
  Proof. induction 1; eauto. Qed.
  Lemma sn_step_rtc x y : sn R x → rtc R x y → sn R y.
  Proof. induction 2; eauto using sn_step. Qed.

  (** An acyclic relation that can only take finitely many steps (sometimes
  called "globally finite") is strongly normalizing *)
  Lemma tc_finite_sn x : Irreflexive (tc R) → pred_finite (tc R x) → sn R x.
  Proof.
    intros Hirr [xs Hfin]. remember (length xs) as n eqn:Hn.
    revert x xs Hn Hfin.
    induction (lt_wf n) as [n _ IH]; intros x xs -> Hfin.
    constructor; simpl; intros x' Hxx'.
    assert (x' ∈ xs) as (xs1&xs2&->)%elem_of_list_split by eauto using tc_once.
    refine (IH (length xs1 + length xs2) _ _ (xs1 ++ xs2) _ _);
      [rewrite app_length; simpl; lia..|].
    intros x'' Hx'x''. opose proof* (Hfin x'') as Hx''; [by econstructor|].
    cut (x' ≠ x''); [set_solver|].
    intros ->. by apply (Hirr x'').
  Qed.

  (** The following theorem requires that [red R] is decidable. The intuition
  for this requirement is that [wn R] is a very "positive" statement as it
  points out a particular trace. In contrast, [sn R] just says "this also holds
  for all successors", there is no "data"/"trace" there. *)
  Lemma sn_wn `{!∀ y, Decision (red R y)} x : sn R x → wn R x.
  Proof.
    induction 1 as [x _ IH]. destruct (decide (red R x)) as [[x' ?]|?].
    - destruct (IH x') as (y&?&?); eauto using wn_step.
    - by apply nf_wn.
  Qed.

  Lemma all_loop_red x : all_loop R x → red R x.
  Proof. destruct 1; auto. Qed.
  Lemma all_loop_step x y : all_loop R x → R x y → all_loop R y.
  Proof. destruct 1; auto. Qed.
  Lemma all_loop_rtc x y : all_loop R x → rtc R x y → all_loop R y.
  Proof. induction 2; eauto using all_loop_step. Qed.
  Lemma all_loop_alt x :
    all_loop R x ↔ ∀ y, rtc R x y → red R y.
  Proof.
    split; [eauto using all_loop_red, all_loop_rtc|].
    intros H. cut (∀ z, rtc R x z → all_loop R z); [eauto|].
    cofix FIX. constructor; eauto using rtc_r.
  Qed.

  Lemma wn_not_all_loop x : wn R x → ¬all_loop R x.
  Proof. intros (z&?&?). rewrite all_loop_alt. eauto. Qed.
  Lemma sn_not_ex_loop x : sn R x → ¬ex_loop R x.
  Proof. unfold not. induction 1; destruct 1; eauto. Qed.

  (** An alternative definition of confluence; also known as the Church-Rosser
  property. *)
  Lemma confluent_alt :
    confluent R ↔ (∀ x y, rtsc R x y → ∃ z, rtc R x z ∧ rtc R y z).
  Proof.
    split.
    - intros Hcr. induction 1 as [x|x y1 y1' [Hy1|Hy1] Hy1' (z&IH1&IH2)]; eauto.
      destruct (Hcr y1 x z) as (z'&?&?); eauto using rtc_transitive.
    - intros Hcr x y1 y2 Hy1 Hy2.
      apply Hcr; trans x; eauto using rtc_rtsc_rl, rtc_rtsc_lr.
  Qed.

  Lemma confluent_nf_r x y :
    confluent R → rtsc R x y → nf R y → rtc R x y.
  Proof.
    rewrite confluent_alt. intros Hcr ??. destruct (Hcr x y) as (z&Hx&Hy); auto.
    by apply rtc_nf in Hy as ->.
  Qed.
  Lemma confluent_nf_l x y :
    confluent R → rtsc R x y → nf R x → rtc R y x.
  Proof. intros. by apply (confluent_nf_r y x). Qed.

  Lemma diamond_confluent :
    diamond R → confluent R.
  Proof.
    intros Hdiam. assert (∀ x y1 y2,
      rtc R x y1 → R x y2 → ∃ z, rtc R y1 z ∧ rtc R y2 z) as Hstrip.
    { intros x y1 y2 Hy1; revert y2.
      induction Hy1 as [x|x y1 y1' Hy1 Hy1' IH]; [by eauto|]; intros y2 Hy2.
      destruct (Hdiam x y1 y2) as (z&Hy1z&Hy2z); auto.
      destruct (IH z) as (z'&?&?); eauto. }
    intros x y1 y2 Hy1; revert y2.
    induction Hy1 as [x|x y1 y1' Hy1 Hy1' IH]; [by eauto|]; intros y2 Hy2.
    destruct (Hstrip x y2 y1) as (z&?&?); eauto.
    destruct (IH z) as (z'&?&?); eauto using rtc_transitive.
  Qed.

  Lemma confluent_locally_confluent :
    confluent R → locally_confluent R.
  Proof. unfold confluent, locally_confluent; eauto. Qed.

  (** The following is also known as Newman's lemma *)
  Lemma locally_confluent_confluent :
    (∀ x, sn R x) → locally_confluent R → confluent R.
  Proof.
    intros Hsn Hcr x. induction (Hsn x) as [x _ IH].
    intros y1 y2 Hy1 Hy2. destruct Hy1 as [x|x y1 y1' Hy1 Hy1']; [by eauto|].
    destruct Hy2 as [x|x y2 y2' Hy2 Hy2']; [by eauto|].
    destruct (Hcr x y1 y2) as (z&Hy1z&Hy2z); auto.
    destruct (IH _ Hy1 y1' z) as (z1&?&?); auto.
    destruct (IH _ Hy2 y2' z1) as (z2&?&?); eauto using rtc_transitive.
  Qed.
End properties.

(** * Theorems on sub relations *)
Section subrel.
  Context {A} (R1 R2 : relation A).
  Notation subrel := (∀ x y, R1 x y → R2 x y).
  Lemma red_subrel x : subrel → red R1 x → red R2 x.
  Proof. intros ? [y ?]; eauto. Qed.
  Lemma nf_subrel x : subrel → nf R2 x → nf R1 x.
  Proof. intros ? H1 H2; destruct H1; by apply red_subrel. Qed.
  Lemma rtc_subrel x y : subrel → rtc R1 x y → rtc R2 x y.
  Proof. induction 2; [by apply rtc_refl|]. eapply rtc_l; eauto. Qed.
End subrel.
