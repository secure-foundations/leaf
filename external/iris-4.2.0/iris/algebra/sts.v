(**
This file formalizes the STS construction from the original Iris paper (POPL15).

DISCLAIMER: The definition of STSs is included in the Iris development for
historical purposes. If you plan to mechanize an Iris proof in Coq, it is
usually better to use a more direct encoding of the ghost state you need as a
resource algebra (camera). STSs are very painful to use in Coq, and they are
therefore barely used in practice.

The type [stsT] describes state-transition systems: a type of states, a type of
tokens, a step relation between states, and a token assignment function. Then
[sts_resR sts], for [sts: stsT], is the resource algebra of "STS resources",
which can be fragments ("we are in one of these states", where the set of states
needs to be closed under transitions performed without the locally owned
tokens), or authoritative ("we are exactly in this state").

The construction is performed via an intermediate internal type, [sts.car]. The
reason for this intermediate step is that composition of two STS resources is
defined only if their token sets are disjoint and the state sets are not
disjoint (i.e., they have at least one element in common). This condition is not
decidable, so we cannot use the usual approach (used e.g. in [gset_disj]) of
just composing those pairs to a dedicated "invalid" element. Instead, [sts_res]
consists of an [sts.car] element (fragment or authoritative), together with a
[Prop] defining whether this element is valid. That way we can "defer" the
validity check from composition to RA validity.
*)

From stdpp Require Export propset.
From iris.algebra Require Export cmra updates.
From iris.prelude Require Import options.
Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments core _ _ !_ /.

(** * Definition of STSs *)
Module sts.
Structure stsT := Sts {
  state : Type;
  token : Type;
  prim_step : relation state;
  tok : state → propset token;
}.
Global Arguments Sts {_ _} _ _.
Global Arguments prim_step {_} _ _.
Global Arguments tok {_} _.
Notation states sts := (propset (state sts)).
Notation tokens sts := (propset (token sts)).

(** * Theory and definitions *)
Section sts.
Context {sts : stsT}.

(** ** Step relations *)
Inductive step : relation (state sts * tokens sts) :=
  | Step s1 s2 T1 T2 :
     prim_step s1 s2 → tok s1 ## T1 → tok s2 ## T2 →
     tok s1 ∪ T1 ≡ tok s2 ∪ T2 → step (s1,T1) (s2,T2).
Notation steps := (rtc step).
Inductive frame_step (T : tokens sts) (s1 s2 : state sts) : Prop :=
  (* Possible alternative definition: (tok s2) ## T) ∧ s \rightarrow s'.
     This is not equivalent, but it might be good enough? *)
  | Frame_step T1 T2 :
     T1 ## tok s1 ∪ T → step (s1,T1) (s2,T2) → frame_step T s1 s2.
Notation frame_steps T := (rtc (frame_step T)).

(** ** Closure under frame steps *)
Record closed (S : states sts) (T : tokens sts) : Prop := Closed {
  closed_disjoint s : s ∈ S → tok s ## T;
  closed_step s1 s2 : s1 ∈ S → frame_step T s1 s2 → s2 ∈ S
}.
Definition up (s : state sts) (T : tokens sts) : states sts :=
  {[ s' | frame_steps T s s' ]}.
Definition up_set (S : states sts) (T : tokens sts) : states sts :=
  S ≫= λ s, up s T.

(** Tactic setup *)
Local Hint Resolve Step : core.
Local Hint Extern 50 (equiv (A:=propset _) _ _) => set_solver : sts.
Local Hint Extern 50 (¬equiv (A:=propset _) _ _) => set_solver : sts.
Local Hint Extern 50 (_ ∈ _) => set_solver : sts.
Local Hint Extern 50 (_ ⊆ _) => set_solver : sts.
Local Hint Extern 50 (_ ## _) => set_solver : sts.

(** ** Setoids *)
Local Instance frame_step_mono : Proper (flip (⊆) ==> (=) ==> (=) ==> impl) frame_step.
Proof.
  intros ?? HT ?? <- ?? <-; destruct 1; econstructor;
    eauto with sts; set_solver.
Qed.
Global Instance frame_step_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) frame_step.
Proof. move=> ?? /set_equiv_subseteq [??]; split; by apply frame_step_mono. Qed.
Local Instance closed_proper' : Proper ((≡) ==> (≡) ==> impl) closed.
Proof. destruct 3; constructor; intros; setoid_subst; eauto. Qed.
Global Instance closed_proper : Proper ((≡) ==> (≡) ==> iff) closed.
Proof. by split; apply closed_proper'. Qed.
Global Instance up_preserving : Proper ((=) ==> flip (⊆) ==> (⊆)) up.
Proof.
  intros s ? <- T T' HT ; apply elem_of_subseteq.
  induction 1 as [|s1 s2 s3 [T1 T2]]; [constructor|].
  eapply elem_of_PropSet, rtc_l; [eapply Frame_step with T1 T2|]; eauto with sts.
Qed.
Global Instance up_proper : Proper ((=) ==> (≡) ==> (≡)) up.
Proof.
  by move=> ??? ?? /set_equiv_subseteq [??]; split; apply up_preserving.
Qed.
Global Instance up_set_preserving : Proper ((⊆) ==> flip (⊆) ==> (⊆)) up_set.
Proof.
  intros S1 S2 HS T1 T2 HT. rewrite /up_set.
  f_equiv=> // s1 s2. by apply up_preserving.
Qed.
Global Instance up_set_proper : Proper ((≡) ==> (≡) ==> (≡)) up_set.
Proof.
  move=> S1 S2 /set_equiv_subseteq [??] T1 T2 /set_equiv_subseteq [??];
    split; by apply up_set_preserving.
Qed.

(** ** Properties of closure under frame steps *)
Lemma closed_steps S T s1 s2 :
  closed S T → s1 ∈ S → frame_steps T s1 s2 → s2 ∈ S.
Proof. induction 3; eauto using closed_step. Qed.
Lemma closed_op T1 T2 S1 S2 :
  closed S1 T1 → closed S2 T2 → closed (S1 ∩ S2) (T1 ∪ T2).
Proof.
  intros [? Hstep1] [? Hstep2]; split; [set_solver|].
  intros s3 s4; rewrite !elem_of_intersection; intros [??] [T3 T4 ?]; split.
  - apply Hstep1 with s3, Frame_step with T3 T4; auto with sts.
  - apply Hstep2 with s3, Frame_step with T3 T4; auto with sts.
Qed.
Lemma step_closed s1 s2 T1 T2 S Tf :
  step (s1,T1) (s2,T2) → closed S Tf → s1 ∈ S → T1 ## Tf →
  s2 ∈ S ∧ T2 ## Tf ∧ tok s2 ## T2.
Proof.
  inversion_clear 1 as [???? HR Hs1 Hs2]; intros [? Hstep]??; split_and?; auto.
  - eapply Hstep with s1, Frame_step with T1 T2; auto with sts.
  - set_solver -Hstep Hs1 Hs2.
Qed.
Lemma steps_closed s1 s2 T1 T2 S Tf :
  steps (s1,T1) (s2,T2) → closed S Tf → s1 ∈ S → T1 ## Tf →
  tok s1 ## T1 → s2 ∈ S ∧ T2 ## Tf ∧ tok s2 ## T2.
Proof.
  remember (s1,T1) as sT1 eqn:HsT1; remember (s2,T2) as sT2 eqn:HsT2.
  intros Hsteps; revert s1 T1 HsT1 s2 T2 HsT2.
  induction Hsteps as [?|? [s2 T2] ? Hstep Hsteps IH];
     intros s1 T1 HsT1 s2' T2' ?????; simplify_eq; first done.
  destruct (step_closed s1 s2 T1 T2 S Tf) as (?&?&?); eauto.
Qed.

(** ** Properties of the closure operators *)
Lemma elem_of_up s T : s ∈ up s T.
Proof. constructor. Qed.
Lemma subseteq_up_set S T : S ⊆ up_set S T.
Proof. intros s ?; apply elem_of_bind; eauto using elem_of_up. Qed.
Lemma elem_of_up_set S T s : s ∈ S → s ∈ up_set S T.
Proof. apply subseteq_up_set. Qed.
Lemma up_up_set s T : up s T ≡ up_set {[ s ]} T.
Proof. by rewrite /up_set set_bind_singleton. Qed.
Lemma closed_up_set S T : (∀ s, s ∈ S → tok s ## T) → closed (up_set S T) T.
Proof.
  intros HS; unfold up_set; split.
  - intros s; rewrite !elem_of_bind; intros (s'&Hstep&Hs').
    specialize (HS s' Hs'); clear Hs' S.
    induction Hstep as [s|s1 s2 s3 [T1 T2 ? Hstep] ? IH]; first done.
    inversion_clear Hstep; apply IH; clear IH; auto with sts.
  - intros s1 s2; rewrite /up; set_unfold; intros (s&?&?) ?; exists s.
    split; [eapply rtc_r|]; eauto.
Qed.
Lemma closed_up s T : tok s ## T → closed (up s T) T.
Proof.
  intros; rewrite -(set_bind_singleton (λ s, up s T) s).
  apply closed_up_set; set_solver.
Qed.
Lemma closed_up_set_empty S : closed (up_set S ∅) ∅.
Proof. eauto using closed_up_set with sts. Qed.
Lemma closed_up_empty s : closed (up s ∅) ∅.
Proof. eauto using closed_up with sts. Qed.
Lemma up_closed S T : closed S T → up_set S T ≡ S.
Proof.
  intros ?; apply set_equiv_subseteq; split; auto using subseteq_up_set.
  intros s; unfold up_set; rewrite elem_of_bind; intros (s'&Hstep&?).
  induction Hstep; eauto using closed_step.
Qed.
Lemma up_subseteq s T S : closed S T → s ∈ S → sts.up s T ⊆ S.
Proof. move=> ?? s' ?. eauto using closed_steps. Qed.
Lemma up_set_subseteq S1 T S2 : closed S2 T → S1 ⊆ S2 → sts.up_set S1 T ⊆ S2.
Proof. move=> ?? s [s' [? ?]]. eauto using closed_steps. Qed.
Lemma up_op s T1 T2 : up s (T1 ∪ T2) ⊆ up s T1 ∩ up s T2.
Proof. (* Notice that the other direction does not hold. *)
  intros x Hx. split; eapply elem_of_PropSet, rtc_subrel; try exact Hx.
  - intros; eapply frame_step_mono; last first; try done. set_solver+.
  - intros; eapply frame_step_mono; last first; try done. set_solver+.
Qed.
End sts.

Notation steps := (rtc step).
Notation frame_steps T := (rtc (frame_step T)).

(* The type of bounds we can give to the state of an STS. On paper, this is the
   type that we equip with an RA structure. In Coq we have to do some work to
   model composition only being defined under some non-computable conditions. *)
Inductive car (sts : stsT) :=
  | auth : state sts → propset (token sts) → car sts
  | frag : propset (state sts) → propset (token sts) → car sts.
Global Arguments auth {_} _ _.
Global Arguments frag {_} _ _.
End sts.

Notation stsT := sts.stsT.
Notation Sts := sts.Sts.

(** * STSs form an RA *)
Section sts_res.
Context {sts : stsT}.
Import sts.
Implicit Types S : states sts.
Implicit Types T : tokens sts.

Inductive sts_car_equiv : Equiv (car sts) :=
  | auth_equiv s T1 T2 : T1 ≡ T2 → auth s T1 ≡ auth s T2
  | frag_equiv S1 S2 T1 T2 : T1 ≡ T2 → S1 ≡ S2 → frag S1 T1 ≡ frag S2 T2.
Local Existing Instance sts_car_equiv.
Local Instance sts_car_valid_instance : Valid (car sts) := λ x,
  match x with
  | auth s T => tok s ## T
  | frag S' T => closed S' T ∧ ∃ s, s ∈ S'
  end.
Local Instance sts_car_core_instance : PCore (car sts) := λ x,
  Some match x with
  | frag S' _ => frag (up_set S' ∅ ) ∅
  | auth s _  => frag (up s ∅) ∅
  end.
Inductive sts_car_disjoint_instance : Disjoint (car sts) :=
  | frag_frag_disjoint S1 S2 T1 T2 :
     (∃ s, s ∈ S1 ∩ S2) → T1 ## T2 → frag S1 T1 ## frag S2 T2
  | auth_frag_disjoint s S T1 T2 : s ∈ S → T1 ## T2 → auth s T1 ## frag S T2
  | frag_auth_disjoint s S T1 T2 : s ∈ S → T1 ## T2 → frag S T1 ## auth s T2.
Local Existing Instance sts_car_disjoint_instance.
Local Instance sts_op_instance : Op (car sts) := λ x1 x2,
  match x1, x2 with
  | frag S1 T1, frag S2 T2 => frag (S1 ∩ S2) (T1 ∪ T2)
  | auth s T1, frag _ T2 => auth s (T1 ∪ T2)
  | frag _ T1, auth s T2 => auth s (T1 ∪ T2)
  | auth s T1, auth _ T2 => auth s (T1 ∪ T2) (* never happens *)
  end.

Local Hint Extern 50 (equiv (A:=propset _) _ _) => set_solver : sts.
Local Hint Extern 50 (∃ s : state sts, _) => set_solver : sts.
Local Hint Extern 50 (_ ∈ _) => set_solver : sts.
Local Hint Extern 50 (_ ⊆ _) => set_solver : sts.
Local Hint Extern 50 (_ ## _) => set_solver : sts.

Global Instance auth_proper s : Proper ((≡) ==> (≡)) (@auth sts s).
Proof. by constructor. Qed.
Global Instance frag_proper : Proper ((≡) ==> (≡) ==> (≡)) (@frag sts).
Proof. by constructor. Qed.

Local Instance sts_car_equivalence: Equivalence ((≡) : relation (car sts)).
Proof.
  split.
  - by intros []; constructor.
  - by destruct 1; constructor.
  - destruct 1; inversion_clear 1; constructor; etrans; eauto.
Qed.
Local Instance sts_car_op_proper : Proper ((≡@{car sts}) ==> (≡) ==> (≡)) (⋅).
Proof. by do 2 destruct 1; constructor; setoid_subst. Qed.
Local Instance sts_car_core_proper : Proper ((≡@{car sts}) ==> (≡)) core.
Proof. by destruct 1; constructor; setoid_subst. Qed.
Local Instance sts_car_valid_proper : Proper ((≡@{car sts}) ==> impl) valid.
Proof. by destruct 1; simpl; intros ?; setoid_subst. Qed.
Local Instance sts_car_valid_proper' : Proper ((≡@{car sts}) ==> iff) valid.
Proof. by split; apply: sts_car_valid_proper. Qed.
Local Instance sts_car_disjoint_proper (x : car sts) :
  Proper ((≡) ==> impl) (disjoint x).
Proof.
  by intros ? [|]; destruct 1; inversion_clear 1; econstructor; setoid_subst.
Qed.

Local Instance sts_car_disjoint_symmetric : Symmetric (@disjoint (car sts) _).
Proof. destruct 1; constructor; auto with sts. Qed.
Local Instance sts_car_disjoint_proper' :
  Proper ((≡@{car sts}) ==> (≡) ==> iff) disjoint.
Proof.
  intros x1 x2 Hx y1 y2 Hy; split.
  - by rewrite Hy (symmetry_iff (##) x1) (symmetry_iff (##) x2) Hx.
  - by rewrite -Hy (symmetry_iff (##) x2) (symmetry_iff (##) x1) -Hx.
Qed.

Local Lemma sts_car_core_valid (x : car sts) :
  ✓ x → ✓ core x.
Proof.
  destruct x; naive_solver eauto using closed_up, closed_up_set,
      elem_of_up, elem_of_up_set with sts.
Qed.
Local Lemma sts_car_op_valid (x y : car sts) :
  ✓ x → ✓ y → x ## y → ✓ (x ⋅ y).
Proof.
  destruct 3; simpl in *; destruct_and?; eauto using closed_op;
      select (closed _ _) (fun H => destruct H); set_solver.
Qed.
Local Lemma sts_car_op_assoc (x y z : car sts) :
  ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ⋅ (y ⋅ z) ≡ (x ⋅ y) ⋅ z.
Proof.
  destruct x, y, z; intros _ _ _ _ _; constructor; rewrite ?assoc; auto with sts.
Qed.
Local Lemma sts_car_op_comm (x y : car sts) :
  ✓ x → ✓ y → x ## y → x ⋅ y ≡ y ⋅ x.
Proof. destruct 3; constructor; auto with sts. Qed.

Local Lemma sts_car_disjoint_ll (x y z : car sts) :
  ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ## z.
Proof.
  destruct 4; inversion_clear 1; constructor; auto with sts.
Qed.
Local Lemma sts_car_disjoint_rl (x y z : car sts) :
  ✓ x → ✓ y → ✓ z → y ## z → x ## y ⋅ z → x ## y.
Proof. intros ???. rewrite !(symmetry_iff _ x). by apply sts_car_disjoint_ll. Qed.
Local Lemma sts_car_disjoint_lr (x y z : car sts) :
  ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → y ## z.
Proof. intros ????. rewrite sts_car_op_comm //. by apply sts_car_disjoint_ll. Qed.
Local Lemma sts_car_disjoint_move_l (x y z : car sts) :
    ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ## y ⋅ z.
Proof. destruct 4; inversion_clear 1; constructor; auto with sts. Qed.
Local Lemma sts_car_disjoint_move_r (a b c : car sts) :
  ✓ a → ✓ b → ✓ c → b ## c → a ## b ⋅ c → a ⋅ b ## c.
Proof.
  intros; symmetry; rewrite sts_car_op_comm; eauto using sts_car_disjoint_rl.
  apply sts_car_disjoint_move_l; auto; by rewrite sts_car_op_comm.
Qed.
Local Hint Immediate sts_car_disjoint_move_l sts_car_disjoint_move_r : core.

Local Lemma sts_car_core_disjoint_l (x : car sts) : ✓ x → core x ## x.
Proof. destruct x; constructor; eauto with sts. Qed. 
Local Lemma sts_car_core_l (x : car sts) : ✓ x → core x ⋅ x ≡ x.
Proof. destruct x; constructor; eauto with sts. Qed.
Local Lemma sts_car_core_idemp (x : car sts) : ✓ x → core (core x) ≡ core x.
Proof.
  destruct x as [s T|S T]; constructor; auto with sts.
  + rewrite (up_closed (up _ _)); auto using closed_up with sts.
  + rewrite (up_closed (up_set _ _)); eauto using closed_up_set with sts.
Qed.
Local Lemma sts_car_core_mono (x y : car sts) :
  ∃ z, ✓ x → ✓ y → x ## y → core (x ⋅ y) ≡ core x ⋅ z ∧ ✓ z ∧ core x ## z.
Proof.
  exists (core (x ⋅ y))=> ?? Hxy; split_and?.
  + destruct Hxy; constructor; unfold up_set; set_solver.
  + destruct Hxy; simpl;
      eauto using closed_up_set_empty, closed_up_empty with sts.
  + destruct Hxy; econstructor;
      repeat match goal with
      | |- context [ up_set ?S ?T ] =>
         unless (S ⊆ up_set S T) by done; pose proof (subseteq_up_set S T)
      | |- context [ up ?s ?T ] =>
         unless (s ∈ up s T) by done; pose proof (elem_of_up s T)
      end; auto with sts.
Qed.

(** The resource type for [sts]. *)
Record sts_res := StsRes {
  (** The underlying STS carrier element, storing the actual data. *)
  sts_car : car sts;
  (** Defines whether this element is valid. *)
  sts_valid : Prop;
  (** Valid elements must have a valid carrier element. *)
  sts_valid_prf : sts_valid → ✓ sts_car
}.
Add Printing Constructor sts_res.
Global Arguments StsRes _ _ {_}.

(** Setoid and OFE for [sts_res]. *)
Local Instance sts_equiv : Equiv sts_res := λ x y,
  (sts_valid x ↔ sts_valid y) ∧ (sts_valid x → sts_car x ≡ sts_car y).
Local Instance sts_equivalence : Equivalence (@equiv sts_res _).
Proof.
  split; unfold equiv, sts_equiv.
  - by intros [x px ?]; simpl.
  - intros [x px ?] [y py ?]; naive_solver.
  - intros [x px ?] [y py ?] [z pz ?] [? Hxy] [? Hyz]; simpl in *.
    split; [|intros; trans y]; tauto.
Qed.
Canonical Structure sts_resO : ofe := discreteO sts_res.

(** RA for [sts_res]. *)
Local Instance sts_res_valid_instance : Valid sts_res := sts_valid.
Local Program Instance sts_res_pcore_instance : PCore sts_res := λ x,
  Some (StsRes (core (sts_car x)) (✓ x)).
Next Obligation.
  intros []; naive_solver eauto using sts_car_core_valid.
Qed.
Local Program Instance sts_res_op_instance : Op sts_res := λ x y,
  StsRes (sts_car x ⋅ sts_car y)
           (✓ x ∧ ✓ y ∧ sts_car x ## sts_car y).
Next Obligation.
  intros [] []; naive_solver eauto using sts_car_op_valid.
Qed.

Definition sts_res_ra_mixin : RAMixin sts_res.
Proof.
  apply ra_total_mixin; first eauto.
  - intros ??? [? Heq]; split; simpl; [|intros (?&?&?); by rewrite Heq].
    split; intros (?&?&?); split_and!;
      first [rewrite ?Heq; tauto|rewrite -?Heq; tauto|tauto].
  - by intros ?? [? Heq]; split; [done|]; simpl; intros ?; rewrite Heq.
  - intros ?? [??]; naive_solver.
  - intros [x px ?] [y py ?] [z pz ?]; split; simpl;
      [intuition eauto 2 using sts_car_disjoint_lr, sts_car_disjoint_rl
      |intuition eauto using sts_car_op_assoc, sts_car_disjoint_rl].
  - intros [x px ?] [y py ?]; split; naive_solver eauto using sts_car_op_comm.
  - intros [x px ?]; split;
      naive_solver eauto using sts_car_core_l, sts_car_core_disjoint_l.
  - intros [x px ?]; split; naive_solver eauto using sts_car_core_idemp.
  - intros [x px ?] [y py ?] [[z pz ?] [? Hy]]; simpl in *.
    destruct (sts_car_core_mono x z) as (z'&Hz').
    unshelve eexists (StsRes z' (px ∧ py ∧ pz)).
    { intros (?&?&?); apply Hz'; tauto. }
    split; simpl; first tauto.
    intros. rewrite Hy //. tauto.
  - by intros [x px ?] [y py ?] (?&?&?).
Qed.
Canonical Structure sts_resR : cmra :=
  discreteR sts_res sts_res_ra_mixin.

Global Instance sts_res_disrete_cmra : CmraDiscrete sts_resR.
Proof. apply discrete_cmra_discrete. Qed.
Global Instance sts_res_cmra_total : CmraTotal sts_resR.
Proof. rewrite /CmraTotal; eauto. Qed.

Local Definition to_sts_res (x : car sts) : sts_res :=
  @StsRes x (valid x) id.
Global Instance to_sts_res_proper : Proper ((≡) ==> (≡)) to_sts_res.
Proof. by intros x1 x2 Hx; split; rewrite /= Hx. Qed.

Lemma to_sts_res_op a b :
  (✓ (a ⋅ b) → ✓ a ∧ ✓ b ∧ a ## b) →
  to_sts_res (a ⋅ b) ≡ to_sts_res a ⋅ to_sts_res b.
Proof. split; naive_solver eauto using sts_car_op_valid. Qed.

End sts_res.

Global Arguments sts_resR : clear implicits.

(** Finally, the general theory of STS that should be used by users *)

Section sts_definitions.
  Context {sts : stsT}.
  Definition sts_auth (s : sts.state sts) (T : sts.tokens sts) : sts_resR sts :=
    to_sts_res (sts.auth s T).
  Definition sts_frag (S : sts.states sts) (T : sts.tokens sts) : sts_resR sts :=
    to_sts_res (sts.frag S T).
  Definition sts_frag_up (s : sts.state sts) (T : sts.tokens sts) : sts_resR sts :=
    sts_frag (sts.up s T) T.
End sts_definitions.
Global Instance: Params (@sts_auth) 2 := {}.
Global Instance: Params (@sts_frag) 1 := {}.
Global Instance: Params (@sts_frag_up) 2 := {}.

Section stsRA.
Import sts.
Context {sts : stsT}.
Implicit Types s : state sts.
Implicit Types S : states sts.
Implicit Types T : tokens sts.
Local Arguments cmra_valid _ !_/.

(** Setoids *)
Global Instance sts_auth_proper s : Proper ((≡) ==> (≡)) (sts_auth s).
Proof. solve_proper. Qed.
Global Instance sts_frag_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sts_frag sts).
Proof. solve_proper. Qed.
Global Instance sts_frag_up_proper s : Proper ((≡) ==> (≡)) (sts_frag_up s).
Proof. solve_proper. Qed.

(** Validity *)
Lemma sts_auth_valid s T : ✓ sts_auth s T ↔ tok s ## T.
Proof. done. Qed.
Lemma sts_frag_valid S T : ✓ sts_frag S T ↔ closed S T ∧ ∃ s, s ∈ S.
Proof. done. Qed.
Lemma sts_frag_up_valid s T : ✓ sts_frag_up s T ↔ tok s ## T.
Proof.
  split.
  - move=>/sts_frag_valid [H _]. apply H, elem_of_up.
  - intros. apply sts_frag_valid; split.
    + by apply closed_up.
    + set_solver+.
Qed.

Lemma sts_auth_frag_valid_inv s S T1 T2 :
  ✓ (sts_auth s T1 ⋅ sts_frag S T2) → s ∈ S.
Proof. by intros (?&?&Hdisj); inversion Hdisj. Qed.

(** Op *)
Lemma sts_auth_frag_op s S T :
  s ∈ S → closed S T → sts_auth s ∅ ⋅ sts_frag S T ≡ sts_auth s T.
Proof.
  intros; split; [split|constructor; set_solver]; simpl.
  - intros (?&?&?); by apply closed_disjoint with S.
  - intros; split_and?; last constructor; set_solver.
Qed.
Lemma sts_auth_frag_up_op s T :
  sts_auth s ∅ ⋅ sts_frag_up s T ≡ sts_auth s T.
Proof.
  intros; split; [split|constructor; set_solver]; simpl.
  - intros (?&[??]&?). by apply closed_disjoint with (up s T), elem_of_up.
  - intros; split_and?.
    + set_solver+.
    + by apply closed_up.
    + exists s. set_solver.
    + constructor; last set_solver. apply elem_of_up.
Qed.

Lemma sts_frag_op S1 S2 T1 T2 :
  T1 ## T2 → sts.closed S1 T1 → sts.closed S2 T2 →
  sts_frag (S1 ∩ S2) (T1 ∪ T2) ≡ sts_frag S1 T1 ⋅ sts_frag S2 T2.
Proof.
  intros HT HS1 HS2. rewrite /sts_frag -to_sts_res_op //.
  move=>/=[?[? ?]]. split_and!; [set_solver..|constructor; set_solver].
Qed.

(* Notice that the following does *not* hold -- the composition of the
   two closures is weaker than the closure with the itnersected token
   set.  Also see up_op.
Lemma sts_frag_up_op s T1 T2 :
  T1 ## T2 → sts_frag_up s (T1 ∪ T2) ≡ sts_frag_up s T1 ⋅ sts_frag_up s T2.
*)

(** Frame preserving updates *)
Lemma sts_update_auth s1 s2 T1 T2 :
  steps (s1,T1) (s2,T2) → sts_auth s1 T1 ~~> sts_auth s2 T2.
Proof.
  intros ?. apply cmra_discrete_total_update.
  intros [x x_val Hx_val]; simpl. intros (Htok & Hval & Hdisj).
  specialize (Hx_val Hval).
  inversion Hdisj as [|? S ? Tf|]; simplify_eq/=; destruct_and?.
  destruct (steps_closed s1 s2 T1 T2 S Tf) as (?&?&?); auto; [].
  repeat (done || constructor).
Qed.

Lemma sts_update_frag S1 S2 T1 T2 :
  (closed S1 T1 → closed S2 T2 ∧ S1 ⊆ S2 ∧ T2 ⊆ T1) → sts_frag S1 T1 ~~> sts_frag S2 T2.
Proof.
  rewrite /sts_frag=> HC HS HT. apply cmra_discrete_total_update.
  intros [x x_val Hx_val]; simpl. intros (Htok & Hval & Hdisj).
  specialize (Hx_val Hval).
  inversion Hdisj as [|? S ? Tf|]; simplify_eq/=;
    (destruct HC as (? & ? & ?); first by destruct_and?).
  - split_and!; first done.
    + set_solver.
    + done.
    + constructor; set_solver.
  - split_and!; first done.
    + set_solver.
    + done.
    + constructor; set_solver.
Qed.

Lemma sts_update_frag_up s1 S2 T1 T2 :
  (tok s1 ## T1 → closed S2 T2) → s1 ∈ S2 → T2 ⊆ T1 → sts_frag_up s1 T1 ~~> sts_frag S2 T2.
Proof.
  intros HC ? HT; apply sts_update_frag. intros HC1; split; last split; eauto using closed_steps.
  - eapply HC, HC1, elem_of_up.
  - rewrite <-HT. eapply up_subseteq; last done. apply HC, HC1, elem_of_up.
Qed.

Lemma sts_up_set_intersection S1 Sf Tf :
  closed Sf Tf → S1 ∩ Sf ≡ S1 ∩ up_set (S1 ∩ Sf) Tf.
Proof.
  intros Hclf. apply (anti_symm (⊆)).
  - move=>s [HS1 HSf]. split.
    + by apply HS1.
    + by apply subseteq_up_set.
  - move=>s [HS1 [s' [/elem_of_PropSet Hsup Hs']]]. split; first done.
    eapply closed_steps, Hsup; first done. set_solver +Hs'.
Qed.

Global Instance sts_frag_core_id S : CoreId (sts_frag S ∅).
Proof.
  constructor; split=> //= [[??]].
  (* FIXME: rewriting with [sts.up_closed] for some reason fails here. *)
  f_equiv. by rewrite sts.up_closed.
Qed.

(** Inclusion *)
(* This is surprisingly different from to_validity_included. I am not sure
   whether this is because to_validity_included is non-canonical, or this
   one here is non-canonical - but I suspect both. *)
(* TODO: These have to be proven again. *)
(*
Lemma sts_frag_included S1 S2 T1 T2 :
  closed S2 T2 → S2 ≢ ∅ →
  (sts_frag S1 T1 ≼ sts_frag S2 T2) ↔
  (closed S1 T1 ∧ S1 ≢ ∅ ∧ ∃ Tf, T2 ≡ T1 ∪ Tf ∧ T1 ## Tf ∧
                                 S2 ≡ S1 ∩ up_set S2 Tf).
Proof.
  intros ??; split.
  - intros [[???] ?].
  destruct (to_validity_included (sts_dra.car sts) (sts_dra.frag S1 T1) (sts_dra.frag S2 T2)) as [Hfincl Htoincl].
  intros Hcl2 HS2ne. split.
  - intros Hincl. destruct Hfincl as ((Hcl1 & ?) & (z & EQ & Hval & Hdisj)).
    { split; last done. split; done. }
    clear Htoincl. split_and!; try done; [].
    destruct z as [sf Tf|Sf Tf].
    { exfalso. inversion_clear EQ. }
    exists Tf. inversion_clear EQ as [|? ? ? ? HT2 HS2].
    inversion_clear Hdisj as [? ? ? ? _ HTdisj | |]. split_and!; [done..|].
    rewrite HS2. apply up_set_intersection. apply Hval.
  - intros (Hcl & Hne & (Tf & HT & HTdisj & HS)). destruct Htoincl as ((Hcl' & ?) & (z & EQ)); last first.
    { exists z. exact EQ. } clear Hfincl.
    split; first (split; done). exists (sts_dra.frag (up_set S2 Tf) Tf). split_and!.
    + constructor; done.
    + simpl. split.
      * apply closed_up_set. move=>s Hs2. move:(closed_disjoint _ _ Hcl2 _ Hs2).
        set_solver +HT.
      * by apply up_set_non_empty.
    + constructor; last done. by rewrite -HS.
Qed.

Lemma sts_frag_included' S1 S2 T :
  closed S2 T → closed S1 T → S2 ≢ ∅ → S1 ≢ ∅ → S2 ≡ S1 ∩ up_set S2 ∅ →
  sts_frag S1 T ≼ sts_frag S2 T.
Proof.
  intros. apply sts_frag_included; split_and?; auto.
  exists ∅; split_and?; done || set_solver+.
Qed. *)
End stsRA.

(** STSs without tokens: Some stuff is simpler *)
Module sts_notok.
Structure stsT := Sts {
  state : Type;
  prim_step : relation state;
}.
Global Arguments Sts {_} _.
Global Arguments prim_step {_} _ _.
Notation states sts := (propset (state sts)).

Definition stsT_token := Empty_set.
Definition stsT_tok {sts : stsT} (_ : state sts) : propset stsT_token := ∅.

Canonical Structure sts_notok (sts : stsT) : sts.stsT :=
  sts.Sts (@prim_step sts) stsT_tok.
Coercion sts_notok.sts_notok : sts_notok.stsT >-> sts.stsT.

Section sts.
  Context {sts : stsT}.
  Implicit Types s : state sts.
  Implicit Types S : states sts.

  Notation prim_steps := (rtc prim_step).

  Lemma sts_step s1 s2 : prim_step s1 s2 → sts.step (s1, ∅) (s2, ∅).
  Proof. intros. split; set_solver. Qed.

  Lemma sts_steps s1 s2 : prim_steps s1 s2 → sts.steps (s1, ∅) (s2, ∅).
  Proof. induction 1; eauto using sts_step, rtc_refl, rtc_l. Qed.

  Lemma frame_prim_step T s1 s2 : sts.frame_step T s1 s2 → prim_step s1 s2.
  Proof. inversion 1 as [??? Hstep]. by inversion_clear Hstep. Qed.

  Lemma prim_frame_step T s1 s2 : prim_step s1 s2 → sts.frame_step T s1 s2.
  Proof.
    intros Hstep. apply sts.Frame_step with ∅ ∅; first set_solver.
    by apply sts_step.
  Qed.

  Lemma mk_closed S :
    (∀ s1 s2, s1 ∈ S → prim_step s1 s2 → s2 ∈ S) → sts.closed S ∅.
  Proof. intros ?. constructor; [by set_solver|eauto using frame_prim_step]. Qed.
End sts.
End sts_notok.

Notation sts_notokT := sts_notok.stsT.
Notation Sts_NoTok := sts_notok.Sts.

Section sts_notokRA.
  Context {sts : sts_notokT}.
  Import sts_notok.
  Implicit Types s : state sts.
  Implicit Types S : states sts.

  Lemma sts_notok_update_auth s1 s2 :
    rtc prim_step s1 s2 → sts_auth s1 ∅ ~~> sts_auth s2 ∅.
  Proof. intros. by apply sts_update_auth, sts_steps. Qed.
End sts_notokRA.
