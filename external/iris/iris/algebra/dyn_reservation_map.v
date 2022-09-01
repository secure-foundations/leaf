From iris.algebra Require Export gmap coPset local_updates.
From iris.algebra Require Import reservation_map updates proofmode_classes.
From iris.prelude Require Import options.

(** The camera [dyn_reservation_map A] over a camera [A] extends [gmap positive
A] with a notion of "reservation tokens" for a (potentially infinite) set [E :
coPset] which represent the right to allocate a map entry at any position [k ∈
E].  Unlike [reservation_map], [dyn_reservation_map] supports dynamically
allocating these tokens, including infinite sets of them.  This is useful when
syncing the keys of this map with another API that dynamically allocates names:
we can first reserve a fresh infinite set [E] of tokens here, then allocate a
new name *in [E]* with the other API (assuming it offers the usual "allocate a
fresh name in an infinite set" API), and then use our tokens to allocate the
same name here.  In effect, we have performed synchronized allocation of the
same name across two maps, without the other API having to have dedicated
support for this.

The key connectives are [dyn_reservation_map_data k a] (the "points-to"
assertion of this map), which associates data [a : A] with a key [k : positive],
and [dyn_reservation_map_token E] (the reservation token), which says
that no data has been associated with the indices in the mask [E]. The important
properties of this camera are:

- The lemma [dyn_reservation_map_reserve] provides a frame-preserving update to
  obtain ownership of [dyn_reservation_map_token E] for some fresh infinite [E].
- The lemma [dyn_reservation_map_alloc] provides a frame preserving update to
  associate data to a key: [dyn_reservation_map_token E ~~> dyn_reservation_map_data k a]
  provided [k ∈ E] and [✓ a].

In the future, it could be interesting to generalize this map to arbitrary key
types instead of hard-coding [positive]. *)

Record dyn_reservation_map (A : Type) := DynReservationMap {
  dyn_reservation_map_data_proj : gmap positive A;
  dyn_reservation_map_token_proj : coPset_disj
}.
Add Printing Constructor dyn_reservation_map.
Global Arguments DynReservationMap {_} _ _.
Global Arguments dyn_reservation_map_data_proj {_} _.
Global Arguments dyn_reservation_map_token_proj {_} _.
Global Instance: Params (@DynReservationMap) 1 := {}.
Global Instance: Params (@dyn_reservation_map_data_proj) 1 := {}.
Global Instance: Params (@dyn_reservation_map_token_proj) 1 := {}.

Definition dyn_reservation_map_data {A : cmra} (k : positive) (a : A) : dyn_reservation_map A :=
  DynReservationMap {[ k := a ]} ε.
Definition dyn_reservation_map_token {A : cmra} (E : coPset) : dyn_reservation_map A :=
  DynReservationMap ∅ (CoPset E).
Global Instance: Params (@dyn_reservation_map_data) 2 := {}.

(** We consruct the OFE and CMRA structure via an isomorphism with
[reservation_map]. *)

Section ofe.
  Context {A : ofe}.
  Implicit Types x y : dyn_reservation_map A.

  Local Definition to_reservation_map x : reservation_map A :=
    ReservationMap (dyn_reservation_map_data_proj x) (dyn_reservation_map_token_proj x).
  Local Definition from_reservation_map (x : reservation_map A) : dyn_reservation_map A :=
    DynReservationMap (reservation_map_data_proj x) (reservation_map_token_proj x).

  Local Instance dyn_reservation_map_equiv : Equiv (dyn_reservation_map A) := λ x y,
    dyn_reservation_map_data_proj x ≡ dyn_reservation_map_data_proj y ∧
    dyn_reservation_map_token_proj x = dyn_reservation_map_token_proj y.
  Local Instance dyn_reservation_map_dist : Dist (dyn_reservation_map A) := λ n x y,
    dyn_reservation_map_data_proj x ≡{n}≡ dyn_reservation_map_data_proj y ∧
    dyn_reservation_map_token_proj x = dyn_reservation_map_token_proj y.

  Global Instance DynReservationMap_ne :
    NonExpansive2 (@DynReservationMap A).
  Proof. by split. Qed.
  Global Instance DynReservationMap_proper :
    Proper ((≡) ==> (=) ==> (≡)) (@DynReservationMap A).
  Proof. by split. Qed.
  Global Instance dyn_reservation_map_data_proj_ne :
    NonExpansive (@dyn_reservation_map_data_proj A).
  Proof. by destruct 1. Qed.
  Global Instance dyn_reservation_map_data_proj_proper :
    Proper ((≡) ==> (≡)) (@dyn_reservation_map_data_proj A).
  Proof. by destruct 1. Qed.

  Definition dyn_reservation_map_ofe_mixin : OfeMixin (dyn_reservation_map A).
  Proof.
    by apply (iso_ofe_mixin to_reservation_map).
  Qed.
  Canonical Structure dyn_reservation_mapO :=
    Ofe (dyn_reservation_map A) dyn_reservation_map_ofe_mixin.

  Global Instance DynReservationMap_discrete a b :
    Discrete a → Discrete b → Discrete (DynReservationMap a b).
  Proof. intros ?? [??] [??]; split; unfold_leibniz; by eapply discrete. Qed.
  Global Instance dyn_reservation_map_ofe_discrete :
    OfeDiscrete A → OfeDiscrete dyn_reservation_mapO.
  Proof. intros ? [??]; apply _. Qed.
End ofe.

Global Arguments dyn_reservation_mapO : clear implicits.

Section cmra.
  Context {A : cmra}.
  Implicit Types a b : A.
  Implicit Types x y : dyn_reservation_map A.
  Implicit Types k : positive.

  Global Instance dyn_reservation_map_data_ne i : NonExpansive (@dyn_reservation_map_data A i).
  Proof. intros ? ???. rewrite /dyn_reservation_map_data. solve_proper. Qed.
  Global Instance dyn_reservation_map_data_proper N :
    Proper ((≡) ==> (≡)) (@dyn_reservation_map_data A N).
  Proof. solve_proper. Qed.
  Global Instance dyn_reservation_map_data_discrete N a :
    Discrete a → Discrete (dyn_reservation_map_data N a).
  Proof. intros. apply DynReservationMap_discrete; apply _. Qed.
  Global Instance dyn_reservation_map_token_discrete E : Discrete (@dyn_reservation_map_token A E).
  Proof. intros. apply DynReservationMap_discrete; apply _. Qed.

  Local Instance dyn_reservation_map_valid_instance : Valid (dyn_reservation_map A) := λ x,
    match dyn_reservation_map_token_proj x with
    | CoPset E =>
      ✓ (dyn_reservation_map_data_proj x) ∧ set_infinite (⊤ ∖ E) ∧
      (* dom (dyn_reservation_map_data_proj x) ⊥ E *)
      (∀ i, dyn_reservation_map_data_proj x !! i = None ∨ i ∉ E)
    | CoPsetBot => False
    end.
  Global Arguments dyn_reservation_map_valid_instance !_ /.
  Local Instance dyn_reservation_map_validN_instance : ValidN (dyn_reservation_map A) := λ n x,
    match dyn_reservation_map_token_proj x with
    | CoPset E =>
      ✓{n} (dyn_reservation_map_data_proj x) ∧ set_infinite (⊤ ∖ E) ∧
      (* dom (dyn_reservation_map_data_proj x) ⊥ E *)
      (∀ i, dyn_reservation_map_data_proj x !! i = None ∨ i ∉ E)
    | CoPsetBot => False
    end.
  Global Arguments dyn_reservation_map_validN_instance !_ /.
  Local Instance dyn_reservation_map_pcore_instance : PCore (dyn_reservation_map A) := λ x,
    Some (DynReservationMap (core (dyn_reservation_map_data_proj x)) ε).
  Local Instance dyn_reservation_map_op_instance : Op (dyn_reservation_map A) := λ x y,
    DynReservationMap (dyn_reservation_map_data_proj x ⋅ dyn_reservation_map_data_proj y)
                   (dyn_reservation_map_token_proj x ⋅ dyn_reservation_map_token_proj y).

  Definition dyn_reservation_map_valid_eq :
    valid = λ x, match dyn_reservation_map_token_proj x with
                 | CoPset E =>
                   ✓ (dyn_reservation_map_data_proj x) ∧ set_infinite (⊤ ∖ E) ∧
                   (* dom (dyn_reservation_map_data_proj x) ⊥ E *)
                   ∀ i, dyn_reservation_map_data_proj x !! i = None ∨ i ∉ E
                 | CoPsetBot => False
                 end := eq_refl _.
  Definition dyn_reservation_map_validN_eq :
    validN = λ n x, match dyn_reservation_map_token_proj x with
                    | CoPset E =>
                      ✓{n} (dyn_reservation_map_data_proj x) ∧ set_infinite (⊤ ∖ E) ∧
                      (* dom (dyn_reservation_map_data_proj x) ⊥ E *)
                      ∀ i, dyn_reservation_map_data_proj x !! i = None ∨ i ∉ E
                    | CoPsetBot => False
                    end := eq_refl _.

  Lemma dyn_reservation_map_included x y :
    x ≼ y ↔
      dyn_reservation_map_data_proj x ≼ dyn_reservation_map_data_proj y ∧
      dyn_reservation_map_token_proj x ≼ dyn_reservation_map_token_proj y.
  Proof.
    split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (DynReservationMap z1 z2); split; auto.
  Qed.

  Lemma dyn_reservation_map_data_proj_validN n x : ✓{n} x → ✓{n} dyn_reservation_map_data_proj x.
  Proof. by destruct x as [? [?|]]=> // -[??]. Qed.
  Lemma dyn_reservation_map_token_proj_validN n x : ✓{n} x → ✓{n} dyn_reservation_map_token_proj x.
  Proof. by destruct x as [? [?|]]=> // -[??]. Qed.

  Lemma dyn_reservation_map_cmra_mixin : CmraMixin (dyn_reservation_map A).
  Proof.
    apply (iso_cmra_mixin_restrict from_reservation_map to_reservation_map); try done.
    - intros n [m [E|]];
        rewrite dyn_reservation_map_validN_eq reservation_map_validN_eq /=;
        naive_solver.
    - intros n [m1 [E1|]] [m2 [E2|]] [Hm ?]=> // -[?[??]]; split; simplify_eq/=.
      + by rewrite -Hm.
      + split; first done. intros i. by rewrite -(dist_None n) -Hm dist_None.
    - intros [m [E|]]; rewrite dyn_reservation_map_valid_eq dyn_reservation_map_validN_eq /=
        ?cmra_valid_validN; naive_solver eauto using O.
    - intros n [m [E|]]; rewrite dyn_reservation_map_validN_eq /=;
        naive_solver eauto using cmra_validN_S.
    - intros n [m1 [E1|]] [m2 [E2|]]=> //=; rewrite dyn_reservation_map_validN_eq /=.
      rewrite {1}/op /cmra_op /=. case_decide; last done.
      intros [Hm [Hinf Hdisj]]; split; first by eauto using cmra_validN_op_l.
      split.
      + rewrite ->difference_union_distr_r_L in Hinf.
        eapply set_infinite_subseteq, Hinf. set_solver.
      + intros i. move: (Hdisj i). rewrite lookup_op.
        case: (m1 !! i); case: (m2 !! i); set_solver.
  Qed.

  Canonical Structure dyn_reservation_mapR :=
    Cmra (dyn_reservation_map A) dyn_reservation_map_cmra_mixin.

  Global Instance dyn_reservation_map_cmra_discrete :
    CmraDiscrete A → CmraDiscrete dyn_reservation_mapR.
  Proof.
    split; first apply _.
    intros [m [E|]]; rewrite dyn_reservation_map_validN_eq dyn_reservation_map_valid_eq //=.
      by intros [?%cmra_discrete_valid ?].
  Qed.

  Local Instance dyn_reservation_map_empty_instance : Unit (dyn_reservation_map A) :=
    DynReservationMap ε ε.
  Lemma dyn_reservation_map_ucmra_mixin : UcmraMixin (dyn_reservation_map A).
  Proof.
    split; simpl.
    - rewrite dyn_reservation_map_valid_eq /=. split; [apply ucmra_unit_valid|]. split.
      + rewrite difference_empty_L. apply top_infinite.
      + set_solver.
    - split; simpl; [by rewrite left_id|by rewrite left_id_L].
    - do 2 constructor; [apply (core_id_core _)|done].
  Qed.
  Canonical Structure dyn_reservation_mapUR :=
    Ucmra (dyn_reservation_map A) dyn_reservation_map_ucmra_mixin.

  Global Instance dyn_reservation_map_data_core_id k a :
    CoreId a → CoreId (dyn_reservation_map_data k a).
  Proof. do 2 constructor; simpl; auto. apply core_id_core, _. Qed.

  Lemma dyn_reservation_map_data_valid k a :
    ✓ (dyn_reservation_map_data k a) ↔ ✓ a.
  Proof.
    rewrite dyn_reservation_map_valid_eq /= singleton_valid.
    split; first naive_solver. intros Ha.
    split; first done. split; last set_solver.
    rewrite difference_empty_L. apply top_infinite.
  Qed.
  Lemma dyn_reservation_map_token_valid E :
    ✓ (dyn_reservation_map_token E) ↔ set_infinite (⊤ ∖ E).
  Proof.
    rewrite dyn_reservation_map_valid_eq /=. split; first naive_solver.
    intros Hinf. do 2 (split; first done). by left.
  Qed.
  Lemma dyn_reservation_map_data_op k a b :
    dyn_reservation_map_data k (a ⋅ b) = dyn_reservation_map_data k a ⋅ dyn_reservation_map_data k b.
  Proof.
      by rewrite {2}/op /dyn_reservation_map_op_instance /dyn_reservation_map_data /= singleton_op left_id_L.
  Qed.
  Lemma dyn_reservation_map_data_mono k a b :
    a ≼ b → dyn_reservation_map_data k a ≼ dyn_reservation_map_data k b.
  Proof. intros [c ->]. rewrite dyn_reservation_map_data_op. apply cmra_included_l. Qed.
  Global Instance dyn_reservation_map_data_is_op k a b1 b2 :
    IsOp a b1 b2 →
    IsOp' (dyn_reservation_map_data k a) (dyn_reservation_map_data k b1) (dyn_reservation_map_data k b2).
  Proof. rewrite /IsOp' /IsOp=> ->. by rewrite dyn_reservation_map_data_op. Qed.

  Lemma dyn_reservation_map_token_union E1 E2 :
    E1 ## E2 →
    dyn_reservation_map_token (E1 ∪ E2) = dyn_reservation_map_token E1 ⋅ dyn_reservation_map_token E2.
  Proof.
    intros. by rewrite /op /dyn_reservation_map_op_instance
      /dyn_reservation_map_token /= coPset_disj_union // left_id_L.
  Qed.
  Lemma dyn_reservation_map_token_difference E1 E2 :
    E1 ⊆ E2 →
    dyn_reservation_map_token E2 = dyn_reservation_map_token E1 ⋅ dyn_reservation_map_token (E2 ∖ E1).
  Proof.
    intros. rewrite -dyn_reservation_map_token_union; last set_solver.
    by rewrite -union_difference_L.
  Qed.
  Lemma dyn_reservation_map_token_valid_op E1 E2 :
    ✓ (dyn_reservation_map_token E1 ⋅ dyn_reservation_map_token E2) ↔
      E1 ## E2 ∧ set_infinite (⊤ ∖ (E1 ∪ E2)).
  Proof.
    split.
    - rewrite dyn_reservation_map_valid_eq /= {1}/op /cmra_op /=. case_decide; last done.
      naive_solver.
    - intros [Hdisj Hinf]. rewrite -dyn_reservation_map_token_union //.
      apply dyn_reservation_map_token_valid. done.
  Qed.

  Lemma dyn_reservation_map_reserve (Q : dyn_reservation_map A → Prop) :
    (∀ E, set_infinite E → Q (dyn_reservation_map_token E)) →
    ε ~~>: Q.
  Proof.
    intros HQ. apply cmra_total_updateP=> n [mf [Ef|]];
      rewrite left_id {1}dyn_reservation_map_validN_eq /=; last done.
    intros [Hmap [Hinf Hdisj]].
    (* Pick a fresh set disjoint from the existing tokens [Ef] and map [mf],
       such that both that set [E1] and the remainder [E2] are infinite. *)
    edestruct (coPset_split_infinite (⊤ ∖ (Ef ∪ dom coPset mf))) as
        (E1 & E2 & HEunion & HEdisj & HE1inf & HE2inf).
    { rewrite -difference_difference_L.
        by apply difference_infinite, dom_finite. }
    exists (dyn_reservation_map_token E1).
    split; first by apply HQ. clear HQ.
    rewrite dyn_reservation_map_validN_eq /=.
    rewrite coPset_disj_union; last set_solver.
    split; first by rewrite left_id_L. split.
    - eapply set_infinite_subseteq, HE2inf. set_solver.
    - intros i. rewrite left_id_L. destruct (Hdisj i) as [?|Hi]; first by left.
      destruct (mf !! i) as [p|] eqn:Hp; last by left.
      apply (elem_of_dom_2 (D:=coPset)) in Hp. right. set_solver.
  Qed.
  Lemma dyn_reservation_map_reserve' :
    ε ~~>: (λ x, ∃ E, set_infinite E ∧ x = dyn_reservation_map_token E).
  Proof. eauto using dyn_reservation_map_reserve. Qed.

  Lemma dyn_reservation_map_alloc E k a :
    k ∈ E → ✓ a → dyn_reservation_map_token E ~~> dyn_reservation_map_data k a.
  Proof.
    intros ??. apply cmra_total_update=> n [mf [Ef|]] //.
    rewrite dyn_reservation_map_validN_eq /= {1}/op /cmra_op /=. case_decide; last done.
    rewrite left_id_L {1}left_id. intros [Hmf [Hinf Hdisj]]; split; last split.
    - destruct (Hdisj k) as [Hmfi|]; last set_solver.
      move: Hmfi. rewrite lookup_op lookup_empty left_id_L=> Hmfi.
      intros j. rewrite lookup_op.
      destruct (decide (k = j)) as [<-|].
      + rewrite Hmfi lookup_singleton right_id_L. by apply cmra_valid_validN.
      + by rewrite lookup_singleton_ne // left_id_L.
    - eapply set_infinite_subseteq, Hinf. set_solver.
    - intros j. destruct (decide (k = j)); first set_solver.
      rewrite lookup_op lookup_singleton_ne //.
      destruct (Hdisj j) as [Hmfi|?]; last set_solver.
      move: Hmfi. rewrite lookup_op lookup_empty; auto.
  Qed.
  Lemma dyn_reservation_map_updateP P (Q : dyn_reservation_map A → Prop) k a :
    a ~~>: P →
    (∀ a', P a' → Q (dyn_reservation_map_data k a')) →
    dyn_reservation_map_data k a ~~>: Q.
  Proof.
    intros Hup HP. apply cmra_total_updateP=> n [mf [Ef|]] //.
    rewrite dyn_reservation_map_validN_eq /= left_id_L. intros [Hmf [Hinf Hdisj]].
    destruct (Hup n (mf !! k)) as (a'&?&?).
    { move: (Hmf (k)).
      by rewrite lookup_op lookup_singleton Some_op_opM. }
    exists (dyn_reservation_map_data k a'); split; first by eauto.
    rewrite /= left_id_L. split; last split.
    - intros j. destruct (decide (k = j)) as [<-|].
      + by rewrite lookup_op lookup_singleton Some_op_opM.
      + rewrite lookup_op lookup_singleton_ne // left_id_L.
        move: (Hmf j). rewrite lookup_op. eauto using cmra_validN_op_r.
    - done.
    - intros j. move: (Hdisj j).
      rewrite !lookup_op !op_None !lookup_singleton_None. naive_solver.
  Qed.
  Lemma dyn_reservation_map_update k a b :
    a ~~> b →
    dyn_reservation_map_data k a ~~> dyn_reservation_map_data k b.
  Proof.
    rewrite !cmra_update_updateP. eauto using dyn_reservation_map_updateP with subst.
  Qed.
End cmra.

Global Arguments dyn_reservation_mapR : clear implicits.
Global Arguments dyn_reservation_mapUR : clear implicits.
