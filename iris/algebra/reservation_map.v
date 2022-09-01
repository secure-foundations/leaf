From iris.algebra Require Export gmap coPset local_updates.
From iris.algebra Require Import updates proofmode_classes.
From iris.prelude Require Import options.

(** The camera [reservation_map A] over a camera [A] extends [gmap positive A]
with a notion of "reservation tokens" for a (potentially infinite) set
[E : coPset] which represent the right to allocate a map entry at any position
[k ∈ E].  The key connectives are [reservation_map_data k a] (the "points-to"
assertion of this map), which associates data [a : A] with a key [k : positive],
and [reservation_map_token E] (the reservation token), which says
that no data has been associated with the indices in the mask [E]. The important
properties of this camera are:

- The lemma [reservation_map_token_union] enables one to split [reservation_map_token]
  w.r.t. disjoint union. That is, if we have [E1 ## E2], then we get
  [reservation_map_token (E1 ∪ E2) = reservation_map_token E1 ⋅ reservation_map_token E2].
- The lemma [reservation_map_alloc] provides a frame preserving update to
  associate data to a key: [reservation_map_token E ~~> reservation_map_data k a]
  provided [k ∈ E] and [✓ a].

In the future, it could be interesting to generalize this map to arbitrary key
types instead of hard-coding [positive]. *)

Record reservation_map (A : Type) := ReservationMap {
  reservation_map_data_proj : gmap positive A;
  reservation_map_token_proj : coPset_disj
}.
Add Printing Constructor reservation_map.
Global Arguments ReservationMap {_} _ _.
Global Arguments reservation_map_data_proj {_} _.
Global Arguments reservation_map_token_proj {_} _.
Global Instance: Params (@ReservationMap) 1 := {}.
Global Instance: Params (@reservation_map_data_proj) 1 := {}.
Global Instance: Params (@reservation_map_token_proj) 1 := {}.

Definition reservation_map_data {A : cmra} (k : positive) (a : A) : reservation_map A :=
  ReservationMap {[ k := a ]} ε.
Definition reservation_map_token {A : cmra} (E : coPset) : reservation_map A :=
  ReservationMap ∅ (CoPset E).
Global Instance: Params (@reservation_map_data) 2 := {}.

(* Ofe *)
Section ofe.
  Context {A : ofe}.
  Implicit Types x y : reservation_map A.

  Local Instance reservation_map_equiv : Equiv (reservation_map A) := λ x y,
    reservation_map_data_proj x ≡ reservation_map_data_proj y ∧
    reservation_map_token_proj x = reservation_map_token_proj y.
  Local Instance reservation_map_dist : Dist (reservation_map A) := λ n x y,
    reservation_map_data_proj x ≡{n}≡ reservation_map_data_proj y ∧
    reservation_map_token_proj x = reservation_map_token_proj y.

  Global Instance ReservationMap_ne :
    NonExpansive2 (@ReservationMap A).
  Proof. by split. Qed.
  Global Instance ReservationMap_proper :
    Proper ((≡) ==> (=) ==> (≡)) (@ReservationMap A).
  Proof. by split. Qed.
  Global Instance reservation_map_data_proj_ne :
    NonExpansive (@reservation_map_data_proj A).
  Proof. by destruct 1. Qed.
  Global Instance reservation_map_data_proj_proper :
    Proper ((≡) ==> (≡)) (@reservation_map_data_proj A).
  Proof. by destruct 1. Qed.

  Definition reservation_map_ofe_mixin : OfeMixin (reservation_map A).
  Proof.
    by apply (iso_ofe_mixin
      (λ x, (reservation_map_data_proj x, reservation_map_token_proj x))).
  Qed.
  Canonical Structure reservation_mapO :=
    Ofe (reservation_map A) reservation_map_ofe_mixin.

  Global Instance ReservationMap_discrete a b :
    Discrete a → Discrete b → Discrete (ReservationMap a b).
  Proof. intros ?? [??] [??]; split; unfold_leibniz; by eapply discrete. Qed.
  Global Instance reservation_map_ofe_discrete :
    OfeDiscrete A → OfeDiscrete reservation_mapO.
  Proof. intros ? [??]; apply _. Qed.
End ofe.

Global Arguments reservation_mapO : clear implicits.

(* Camera *)
Section cmra.
  Context {A : cmra}.
  Implicit Types a b : A.
  Implicit Types x y : reservation_map A.
  Implicit Types k : positive.

  Global Instance reservation_map_data_ne i : NonExpansive (@reservation_map_data A i).
  Proof. solve_proper. Qed.
  Global Instance reservation_map_data_proper k :
    Proper ((≡) ==> (≡)) (@reservation_map_data A k).
  Proof. solve_proper. Qed.
  Global Instance reservation_map_data_discrete k a :
    Discrete a → Discrete (reservation_map_data k a).
  Proof. intros. apply ReservationMap_discrete; apply _. Qed.
  Global Instance reservation_map_token_discrete E : Discrete (@reservation_map_token A E).
  Proof. intros. apply ReservationMap_discrete; apply _. Qed.

  Local Instance reservation_map_valid_instance : Valid (reservation_map A) := λ x,
    match reservation_map_token_proj x with
    | CoPset E =>
      ✓ (reservation_map_data_proj x) ∧
      (* dom (reservation_map_data_proj x) ⊥ E *)
      ∀ i, reservation_map_data_proj x !! i = None ∨ i ∉ E
    | CoPsetBot => False
    end.
  Global Arguments reservation_map_valid_instance !_ /.
  Local Instance reservation_map_validN_instance : ValidN (reservation_map A) := λ n x,
    match reservation_map_token_proj x with
    | CoPset E =>
      ✓{n} (reservation_map_data_proj x) ∧
      (* dom (reservation_map_data_proj x) ⊥ E *)
      ∀ i, reservation_map_data_proj x !! i = None ∨ i ∉ E
    | CoPsetBot => False
    end.
  Global Arguments reservation_map_validN_instance !_ /.
  Local Instance reservation_map_pcore_instance : PCore (reservation_map A) := λ x,
    Some (ReservationMap (core (reservation_map_data_proj x)) ε).
  Local Instance reservation_map_op_instance : Op (reservation_map A) := λ x y,
    ReservationMap (reservation_map_data_proj x ⋅ reservation_map_data_proj y)
                   (reservation_map_token_proj x ⋅ reservation_map_token_proj y).

  Definition reservation_map_valid_eq :
    valid = λ x, match reservation_map_token_proj x with
                 | CoPset E =>
                   ✓ (reservation_map_data_proj x) ∧
                   (* dom (reservation_map_data_proj x) ⊥ E *)
                   ∀ i, reservation_map_data_proj x !! i = None ∨ i ∉ E
                 | CoPsetBot => False
                 end := eq_refl _.
  Definition reservation_map_validN_eq :
    validN = λ n x, match reservation_map_token_proj x with
                    | CoPset E =>
                      ✓{n} (reservation_map_data_proj x) ∧
                      (* dom (reservation_map_data_proj x) ⊥ E *)
                      ∀ i, reservation_map_data_proj x !! i = None ∨ i ∉ E
                    | CoPsetBot => False
                    end := eq_refl _.

  Lemma reservation_map_included x y :
    x ≼ y ↔
      reservation_map_data_proj x ≼ reservation_map_data_proj y ∧
      reservation_map_token_proj x ≼ reservation_map_token_proj y.
  Proof.
    split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (ReservationMap z1 z2); split; auto.
  Qed.
  
  Lemma reservation_map_data_proj_validN n x : ✓{n} x → ✓{n} reservation_map_data_proj x.
  Proof. by destruct x as [? [?|]]=> // -[??]. Qed.
  Lemma reservation_map_token_proj_validN n x : ✓{n} x → ✓{n} reservation_map_token_proj x.
  Proof. by destruct x as [? [?|]]=> // -[??]. Qed.
  
  Lemma reservation_map_cmra_mixin : CmraMixin (reservation_map A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
    - solve_proper.
    - intros n [m1 [E1|]] [m2 [E2|]] [Hm ?]=> // -[??]; split; simplify_eq/=.
      + by rewrite -Hm.
      + intros i. by rewrite -(dist_None n) -Hm dist_None.
    - intros [m [E|]]; rewrite reservation_map_valid_eq reservation_map_validN_eq /=
        ?cmra_valid_validN; naive_solver eauto using O.
    - intros n [m [E|]]; rewrite reservation_map_validN_eq /=;
        naive_solver eauto using cmra_validN_S.
    - split; simpl; [by rewrite assoc|by rewrite assoc_L].
    - split; simpl; [by rewrite comm|by rewrite comm_L].
    - split; simpl; [by rewrite cmra_core_l|by rewrite left_id_L].
    - split; simpl; [by rewrite cmra_core_idemp|done].
    - intros ??; rewrite! reservation_map_included; intros [??].
      by split; simpl; apply: cmra_core_mono. (* FIXME: FIXME(Coq #6294): needs new unification *)
    - intros n [m1 [E1|]] [m2 [E2|]]=> //=; rewrite reservation_map_validN_eq /=.
      rewrite {1}/op /cmra_op /=. case_decide; last done.
      intros [Hm Hdisj]; split; first by eauto using cmra_validN_op_l.
      intros i. move: (Hdisj i). rewrite lookup_op.
      case: (m1 !! i); case: (m2 !! i); set_solver.
    - intros n x y1 y2 ? [??]; simpl in *.
      destruct (cmra_extend n (reservation_map_data_proj x)
          (reservation_map_data_proj y1) (reservation_map_data_proj y2))
        as (m1&m2&?&?&?); auto using reservation_map_data_proj_validN.
      destruct (cmra_extend n (reservation_map_token_proj x)
          (reservation_map_token_proj y1) (reservation_map_token_proj y2))
        as (E1&E2&?&?&?); auto using reservation_map_token_proj_validN.
      by exists (ReservationMap m1 E1), (ReservationMap m2 E2).
  Qed.
  Canonical Structure reservation_mapR :=
    Cmra (reservation_map A) reservation_map_cmra_mixin.

  Global Instance reservation_map_cmra_discrete :
    CmraDiscrete A → CmraDiscrete reservation_mapR.
  Proof.
    split; first apply _.
    intros [m [E|]]; rewrite reservation_map_validN_eq reservation_map_valid_eq //=.
      by intros [?%cmra_discrete_valid ?].
  Qed.

  Local Instance reservation_map_empty_instance : Unit (reservation_map A) := ReservationMap ε ε.
  Lemma reservation_map_ucmra_mixin : UcmraMixin (reservation_map A).
  Proof.
    split; simpl.
    - rewrite reservation_map_valid_eq /=. split; [apply ucmra_unit_valid|]. set_solver.
    - split; simpl; [by rewrite left_id|by rewrite left_id_L].
    - do 2 constructor; [apply (core_id_core _)|done].
  Qed.
  Canonical Structure reservation_mapUR :=
    Ucmra (reservation_map A) reservation_map_ucmra_mixin.

  Global Instance reservation_map_data_core_id k a :
    CoreId a → CoreId (reservation_map_data k a).
  Proof. do 2 constructor; simpl; auto. apply core_id_core, _. Qed.

  Lemma reservation_map_data_valid k a : ✓ (reservation_map_data k a) ↔ ✓ a.
  Proof. rewrite reservation_map_valid_eq /= singleton_valid. set_solver. Qed.
  Lemma reservation_map_token_valid E : ✓ (reservation_map_token E).
  Proof. rewrite reservation_map_valid_eq /=. split; first done. by left. Qed.
  Lemma reservation_map_data_op k a b :
    reservation_map_data k (a ⋅ b) = reservation_map_data k a ⋅ reservation_map_data k b.
  Proof.
      by rewrite {2}/op /reservation_map_op_instance /reservation_map_data /= singleton_op left_id_L.
  Qed.
  Lemma reservation_map_data_mono k a b :
    a ≼ b → reservation_map_data k a ≼ reservation_map_data k b.
  Proof. intros [c ->]. rewrite reservation_map_data_op. apply cmra_included_l. Qed.
  Global Instance reservation_map_data_is_op k a b1 b2 :
    IsOp a b1 b2 →
    IsOp' (reservation_map_data k a) (reservation_map_data k b1) (reservation_map_data k b2).
  Proof. rewrite /IsOp' /IsOp=> ->. by rewrite reservation_map_data_op. Qed.

  Lemma reservation_map_token_union E1 E2 :
    E1 ## E2 →
    reservation_map_token (E1 ∪ E2) = reservation_map_token E1 ⋅ reservation_map_token E2.
  Proof.
    intros. by rewrite /op /reservation_map_op_instance
      /reservation_map_token /= coPset_disj_union // left_id_L.
  Qed.
  Lemma reservation_map_token_difference E1 E2 :
    E1 ⊆ E2 →
    reservation_map_token E2 = reservation_map_token E1 ⋅ reservation_map_token (E2 ∖ E1).
  Proof.
    intros. rewrite -reservation_map_token_union; last set_solver.
      by rewrite -union_difference_L.
  Qed.
  Lemma reservation_map_token_valid_op E1 E2 :
    ✓ (reservation_map_token E1 ⋅ reservation_map_token E2) ↔ E1 ## E2.
  Proof.
    rewrite reservation_map_valid_eq /= {1}/op /cmra_op /=. case_decide; last done.
    split; [done|]; intros _. split.
    - by rewrite left_id.
    - intros i. rewrite lookup_op lookup_empty. auto.
  Qed.

  Lemma reservation_map_alloc E k a :
    k ∈ E → ✓ a → reservation_map_token E ~~> reservation_map_data k a.
  Proof.
    intros ??. apply cmra_total_update=> n [mf [Ef|]] //.
    rewrite reservation_map_validN_eq /= {1}/op /cmra_op /=. case_decide; last done.
    rewrite left_id_L {1}left_id. intros [Hmf Hdisj]; split.
    - destruct (Hdisj k) as [Hmfi|]; last set_solver.
      move: Hmfi. rewrite lookup_op lookup_empty left_id_L=> Hmfi.
      intros j. rewrite lookup_op.
      destruct (decide (k = j)) as [<-|].
      + rewrite Hmfi lookup_singleton right_id_L. by apply cmra_valid_validN.
      + by rewrite lookup_singleton_ne // left_id_L.
    - intros j. destruct (decide (k = j)); first set_solver.
      rewrite lookup_op lookup_singleton_ne //.
      destruct (Hdisj j) as [Hmfi|?]; last set_solver.
      move: Hmfi. rewrite lookup_op lookup_empty; auto.
  Qed.
  Lemma reservation_map_updateP P (Q : reservation_map A → Prop) k a :
    a ~~>: P →
    (∀ a', P a' → Q (reservation_map_data k a')) →
    reservation_map_data k a ~~>: Q.
  Proof.
    intros Hup HP. apply cmra_total_updateP=> n [mf [Ef|]] //.
    rewrite reservation_map_validN_eq /= left_id_L. intros [Hmf Hdisj].
    destruct (Hup n (mf !! k)) as (a'&?&?).
    { move: (Hmf (k)).
      by rewrite lookup_op lookup_singleton Some_op_opM. }
    exists (reservation_map_data k a'); split; first by eauto.
    rewrite /= left_id_L. split.
    - intros j. destruct (decide (k = j)) as [<-|].
      + by rewrite lookup_op lookup_singleton Some_op_opM.
      + rewrite lookup_op lookup_singleton_ne // left_id_L.
        move: (Hmf j). rewrite lookup_op. eauto using cmra_validN_op_r.
    - intros j. move: (Hdisj j).
      rewrite !lookup_op !op_None !lookup_singleton_None. naive_solver.
  Qed.
  Lemma reservation_map_update k a b :
    a ~~> b →
    reservation_map_data k a ~~> reservation_map_data k b.
  Proof.
    rewrite !cmra_update_updateP. eauto using reservation_map_updateP with subst.
  Qed.
End cmra.

Global Arguments reservation_mapR : clear implicits.
Global Arguments reservation_mapUR : clear implicits.
