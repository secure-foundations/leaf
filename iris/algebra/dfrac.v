(** Camera of discardable fractions.

    This is a generalisation of the fractional camera where elements can
    represent both ownership of a fraction (as in the fractional camera) and the
    knowledge that a fraction has been discarded.

    Ownership of a fraction is denoted [DfracOwn q] and behaves identically to
    [q] of the fractional camera.

    Knowledge that a fraction has been discarded is denoted [DfracDiscarded].
    This elements is its own core, making ownership persistent.

    One can make a frame preserving update from _owning_ a fraction to _knowing_
    that the fraction has been discarded.

    Crucially, ownership over 1 is an exclusive element just as it is in the
    fractional camera. Hence owning 1 implies that no fraction has been
    discarded. Conversely, knowing that a fraction has been discarded implies
    that no one can own 1. And, since discarding is an irreversible operation,
    it also implies that no one can own 1 in the future *)
From stdpp Require Import countable.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates frac.
From iris.prelude Require Import options.

(** An element of dfrac denotes ownership of a fraction, knowledge that a
    fraction has been discarded, or both. Note that [DfracBoth] can be written
    as [DfracOwn q ⋅ DfracDiscarded]. This should be used instead
    of [DfracBoth] which is for internal use only. *)
Inductive dfrac :=
  | DfracOwn : Qp → dfrac
  | DfracDiscarded : dfrac
  | DfracBoth : Qp → dfrac.

Section dfrac.
  Canonical Structure dfracO := leibnizO dfrac.

  Implicit Types p q : Qp.
  Implicit Types dp dq : dfrac.

  Global Instance dfrac_inhabited : Inhabited dfrac := populate DfracDiscarded.
  Global Instance dfrac_eq_dec : EqDecision dfrac.
  Proof. solve_decision. Defined.
  Global Instance dfrac_countable : Countable dfrac.
  Proof.
    set (enc dq := match dq with
      | DfracOwn q => inl q
      | DfracDiscarded => inr (inl ())
      | DfracBoth q => inr (inr q)
      end).
    set (dec y := Some match y with
      | inl q => DfracOwn q
      | inr (inl ()) => DfracDiscarded
      | inr (inr q) => DfracBoth q
      end).
    refine (inj_countable enc dec _). by intros [].
  Qed.

  Global Instance DfracOwn_inj : Inj (=) (=) DfracOwn.
  Proof. by injection 1. Qed.
  Global Instance DfracBoth_inj : Inj (=) (=) DfracBoth.
  Proof. by injection 1. Qed.

  (** An element is valid as long as the sum of its content is less than one. *)
  Local Instance dfrac_valid_instance : Valid dfrac := λ dq,
    match dq with
    | DfracOwn q => q ≤ 1
    | DfracDiscarded => True
    | DfracBoth q => q < 1
    end%Qp.

  (** As in the fractional camera the core is undefined for elements denoting
     ownership of a fraction. For elements denoting the knowledge that a fraction has
     been discarded the core is the identity function. *)
  Local Instance dfrac_pcore_instance : PCore dfrac := λ dq,
    match dq with
    | DfracOwn q => None
    | DfracDiscarded => Some DfracDiscarded
    | DfracBoth q => Some DfracDiscarded
    end.

  (** When elements are combined, ownership is added together and knowledge of
     discarded fractions is combined with the max operation. *)
  Local Instance dfrac_op_instance : Op dfrac := λ dq dp,
    match dq, dp with
    | DfracOwn q, DfracOwn q' => DfracOwn (q + q')
    | DfracOwn q, DfracDiscarded => DfracBoth q
    | DfracOwn q, DfracBoth q' => DfracBoth (q + q')
    | DfracDiscarded, DfracOwn q' => DfracBoth q'
    | DfracDiscarded, DfracDiscarded => DfracDiscarded
    | DfracDiscarded, DfracBoth q' => DfracBoth q'
    | DfracBoth q, DfracOwn q' => DfracBoth (q + q')
    | DfracBoth q, DfracDiscarded => DfracBoth q
    | DfracBoth q, DfracBoth q' => DfracBoth (q + q')
    end.

  Lemma dfrac_op_own q p : DfracOwn p ⋅ DfracOwn q = DfracOwn (p + q).
  Proof. done. Qed.

  Lemma dfrac_op_discarded :
    DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_own_included q p : DfracOwn q ≼ DfracOwn p ↔ (q < p)%Qp.
  Proof.
    rewrite Qp_lt_sum. split.
    - rewrite /included /op /dfrac_op_instance. intros [[o| |?] [= ->]]. by exists o.
    - intros [o ->]. exists (DfracOwn o). by rewrite dfrac_op_own.
  Qed.

  (* [dfrac] does not have a unit so reflexivity is not for granted! *)
  Lemma dfrac_discarded_included :
    DfracDiscarded ≼ DfracDiscarded.
  Proof. exists DfracDiscarded. done. Qed.

  Definition dfrac_ra_mixin : RAMixin dfrac.
  Proof.
    split; try apply _.
    - intros [?| |?] ? dq <-; intros [= <-]; eexists _; done.
    - intros [?| |?] [?| |?] [?| |?];
        rewrite /op /dfrac_op_instance 1?assoc_L 1?assoc_L; done.
    - intros [?| |?] [?| |?];
        rewrite /op /dfrac_op_instance 1?(comm_L Qp_add); done.
    - intros [?| |?] dq; rewrite /pcore /dfrac_pcore_instance; intros [= <-];
        rewrite /op /dfrac_op_instance; done.
    - intros [?| |?] ? [= <-]; done.
    - intros [?| |?] [?| |?] ? [[?| |?] [=]] [= <-]; eexists _; split; try done;
        apply dfrac_discarded_included.
    - intros [q| |q] [q'| |q']; rewrite /op /dfrac_op_instance /valid /dfrac_valid_instance //.
      + intros. trans (q + q')%Qp; [|done]. apply Qp_le_add_l.
      + apply Qp_lt_le_incl.
      + intros. trans (q + q')%Qp; [|by apply Qp_lt_le_incl]. apply Qp_le_add_l.
      + intros. trans (q + q')%Qp; [|done]. apply Qp_lt_add_l.
      + intros. trans (q + q')%Qp; [|done]. apply Qp_lt_add_l.
  Qed.
  Canonical Structure dfracR := discreteR dfrac dfrac_ra_mixin.

  Global Instance dfrac_cmra_discrete : CmraDiscrete dfracR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance dfrac_full_exclusive : Exclusive (DfracOwn 1).
  Proof.
    intros [q| |q];
      rewrite /op /cmra_op -cmra_discrete_valid_iff /valid /cmra_valid //=.
    - apply Qp_not_add_le_l.
    - move=> /Qp_lt_le_incl. apply Qp_not_add_le_l.
  Qed.

  Global Instance dfrac_cancelable q : Cancelable (DfracOwn q).
  Proof.
    apply: discrete_cancelable.
    intros [q1| |q1][q2| |q2] _ [=]; simplify_eq/=; try done.
    - by destruct (Qp_add_id_free q q2).
    - by destruct (Qp_add_id_free q q1).
  Qed.
  Global Instance dfrac_own_id_free q : IdFree (DfracOwn q).
  Proof. intros [q'| |q'] _ [=]. by apply (Qp_add_id_free q q'). Qed.
  Global Instance dfrac_discarded_core_id : CoreId DfracDiscarded.
  Proof. by constructor. Qed.

  Lemma dfrac_valid_own p : ✓ DfracOwn p ↔ (p ≤ 1)%Qp.
  Proof. done. Qed.

  Lemma dfrac_valid_own_r dq q : ✓ (dq ⋅ DfracOwn q) → (q < 1)%Qp.
  Proof.
    destruct dq as [q'| |q']; [|done|].
    - apply Qp_lt_le_trans, Qp_lt_add_r.
    - intro Hlt. etrans; last apply Hlt. apply Qp_lt_add_r.
  Qed.

  Lemma dfrac_valid_own_l dq q : ✓ (DfracOwn q ⋅ dq) → (q < 1)%Qp.
  Proof. rewrite comm. apply dfrac_valid_own_r. Qed.

  Lemma dfrac_valid_discarded p : ✓ DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_valid_own_discarded q :
    ✓ (DfracOwn q ⋅ DfracDiscarded) ↔ (q < 1)%Qp.
  Proof. done. Qed.

  Global Instance dfrac_is_op q q1 q2 :
    IsOp q q1 q2 →
    IsOp' (DfracOwn q) (DfracOwn q1) (DfracOwn q2).
  Proof. rewrite /IsOp' /IsOp dfrac_op_own=>-> //. Qed.

  (** Discarding a fraction is a frame preserving update. *)
  Lemma dfrac_discard_update dq : dq ~~> DfracDiscarded.
  Proof.
    intros n [[q'| |q']|]; rewrite -!cmra_discrete_valid_iff //=.
    - apply dfrac_valid_own_r.
    - apply cmra_valid_op_r.
  Qed.

End dfrac.
