(* This file is still experimental. See its tracking issue
https://gitlab.mpi-sws.org/iris/iris/-/issues/407 for details on remaining
issues before stabilization. *)
From stdpp Require Export list.
From iris.algebra Require Export cmra list.
From iris.algebra Require Import updates local_updates big_op.
From iris.prelude Require Import options.

(* CMRA. Only works if [A] has a unit! *)
Section cmra.
  Context {A : ucmra}.
  Implicit Types l : list A.
  Local Arguments op _ _ !_ !_ / : simpl nomatch.

  Local Instance list_op_instance : Op (list A) :=
    fix go l1 l2 := let _ : Op _ := @go in
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: l1, y :: l2 => x ⋅ y :: l1 ⋅ l2
    end.
  Local Instance list_pcore_instance : PCore (list A) := λ l, Some (core <$> l).

  Local Instance list_valid_instance : Valid (list A) := Forall (λ x, ✓ x).
  Local Instance list_validN_instance : ValidN (list A) := λ n, Forall (λ x, ✓{n} x).

  Lemma cons_valid l x : ✓ (x :: l) ↔ ✓ x ∧ ✓ l.
  Proof. apply Forall_cons. Qed.
  Lemma cons_validN n l x : ✓{n} (x :: l) ↔ ✓{n} x ∧ ✓{n} l.
  Proof. apply Forall_cons. Qed.
  Lemma app_valid l1 l2 : ✓ (l1 ++ l2) ↔ ✓ l1 ∧ ✓ l2.
  Proof. apply Forall_app. Qed.
  Lemma app_validN n l1 l2 : ✓{n} (l1 ++ l2) ↔ ✓{n} l1 ∧ ✓{n} l2.
  Proof. apply Forall_app. Qed.

  Lemma list_lookup_valid l : ✓ l ↔ ∀ i, ✓ (l !! i).
  Proof.
    rewrite {1}/valid /list_valid_instance Forall_lookup; split.
    - intros Hl i. by destruct (l !! i) as [x|] eqn:?; [apply (Hl i)|].
    - intros Hl i x Hi. move: (Hl i); by rewrite Hi.
  Qed.
  Lemma list_lookup_validN n l : ✓{n} l ↔ ∀ i, ✓{n} (l !! i).
  Proof.
    rewrite {1}/validN /list_validN_instance Forall_lookup; split.
    - intros Hl i. by destruct (l !! i) as [x|] eqn:?; [apply (Hl i)|].
    - intros Hl i x Hi. move: (Hl i); by rewrite Hi.
  Qed.
  Lemma list_lookup_op l1 l2 i : (l1 ⋅ l2) !! i = l1 !! i ⋅ l2 !! i.
  Proof.
    revert i l2. induction l1 as [|x l1]; intros [|i] [|y l2];
      by rewrite /= ?left_id_L ?right_id_L.
  Qed.
  Lemma list_lookup_core l i : core l !! i = core (l !! i).
  Proof.
    rewrite /core /= list_lookup_fmap.
    destruct (l !! i); by rewrite /= ?Some_core.
  Qed.

  Lemma list_lookup_included l1 l2 : l1 ≼ l2 ↔ ∀ i, l1 !! i ≼ l2 !! i.
  Proof.
    split.
    { intros [l Hl] i. exists (l !! i). by rewrite Hl list_lookup_op. }
    revert l1. induction l2 as [|y l2 IH]=>-[|x l1] Hl.
    - by exists [].
    - destruct (Hl 0) as [[z|] Hz]; inversion Hz.
    - by exists (y :: l2).
    - destruct (IH l1) as [l3 ?]; first (intros i; apply (Hl (S i))).
      destruct (Hl 0) as [[z|] Hz]; inversion_clear Hz; simplify_eq/=.
      + exists (z :: l3); by constructor.
      + exists (core x :: l3); constructor; by rewrite ?cmra_core_r.
  Qed.

  Definition list_cmra_mixin : CmraMixin (list A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - intros n l l1 l2; rewrite !list_dist_lookup=> Hl i.
      by rewrite !list_lookup_op Hl.
    - intros n l1 l2 Hl; by rewrite /core /= Hl.
    - intros n l1 l2; rewrite !list_dist_lookup !list_lookup_validN=> Hl ? i.
      by rewrite -Hl.
    - intros l. rewrite list_lookup_valid. setoid_rewrite list_lookup_validN.
      setoid_rewrite cmra_valid_validN. naive_solver.
    - intros n x. rewrite !list_lookup_validN. auto using cmra_validN_S.
    - intros l1 l2 l3; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_op assoc.
    - intros l1 l2; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_op comm.
    - intros l; rewrite list_equiv_lookup=> i.
      by rewrite list_lookup_op list_lookup_core cmra_core_l.
    - intros l; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_core cmra_core_idemp.
    - intros l1 l2; rewrite !list_lookup_included=> Hl i.
      rewrite !list_lookup_core. by apply cmra_core_mono.
    - intros n l1 l2. rewrite !list_lookup_validN.
      setoid_rewrite list_lookup_op. eauto using cmra_validN_op_l.
    - intros n l.
      induction l as [|x l IH]=> -[|y1 l1] [|y2 l2] Hl Heq;
        (try by exfalso; inversion Heq).
      + by exists [], [].
      + exists [], (x :: l); inversion Heq; by repeat constructor.
      + exists (x :: l), []; inversion Heq; by repeat constructor.
      + destruct (IH l1 l2) as (l1'&l2'&?&?&?),
          (cmra_extend n x y1 y2) as (y1'&y2'&?&?&?);
          [by inversion_clear Heq; inversion_clear Hl..|].
        exists (y1' :: l1'), (y2' :: l2'); repeat constructor; auto.
  Qed.
  Canonical Structure listR := Cmra (list A) list_cmra_mixin.

  Global Instance list_unit_instance : Unit (list A) := [].
  Definition list_ucmra_mixin : UcmraMixin (list A).
  Proof.
    split.
    - constructor.
    - by intros l.
    - by constructor.
  Qed.
  Canonical Structure listUR := Ucmra (list A) list_ucmra_mixin.

  Global Instance list_cmra_discrete : CmraDiscrete A → CmraDiscrete listR.
  Proof.
    split; [apply _|]=> l; rewrite list_lookup_valid list_lookup_validN=> Hl i.
    by apply cmra_discrete_valid.
  Qed.

  Lemma list_core_id' l : (∀ x, x ∈ l → CoreId x) → CoreId l.
  Proof.
    intros Hyp. constructor. apply list_equiv_lookup=> i.
    rewrite list_lookup_core.
    destruct (l !! i) eqn:E; last done.
    by eapply Hyp, elem_of_list_lookup_2.
  Qed.

  Global Instance list_core_id l : (∀ x : A, CoreId x) → CoreId l.
  Proof. intros Hyp; by apply list_core_id'. Qed.

End cmra.

Global Arguments listR : clear implicits.
Global Arguments listUR : clear implicits.

Global Instance list_singletonM {A : ucmra} : SingletonM nat A (list A) := λ n x,
  replicate n ε ++ [x].

Section properties.
  Context {A : ucmra}.
  Implicit Types l : list A.
  Implicit Types x y z : A.
  Local Arguments op _ _ !_ !_ / : simpl nomatch.
  Local Arguments cmra_op _ !_ !_ / : simpl nomatch.
  Local Arguments ucmra_op _ !_ !_ / : simpl nomatch.

  Lemma list_lookup_opM l mk i : (l ⋅? mk) !! i = l !! i ⋅ (mk ≫= (.!! i)).
  Proof. destruct mk; by rewrite /= ?list_lookup_op ?right_id_L. Qed.

  Global Instance list_op_nil_l : LeftId (=) (@nil A) op.
  Proof. done. Qed.
  Global Instance list_op_nil_r : RightId (=) (@nil A) op.
  Proof. by intros []. Qed.

  Lemma list_op_app l1 l2 l3 :
    (l1 ++ l3) ⋅ l2 = (l1 ⋅ take (length l1) l2) ++ (l3 ⋅ drop (length l1) l2).
  Proof.
    revert l2 l3.
    induction l1 as [|x1 l1]=> -[|x2 l2] [|x3 l3]; f_equal/=; auto.
  Qed.
  Lemma list_op_app_le l1 l2 l3 :
    length l2 ≤ length l1 → (l1 ++ l3) ⋅ l2 = (l1 ⋅ l2) ++ l3.
  Proof. intros ?. by rewrite list_op_app take_ge // drop_ge // right_id_L. Qed.

  Lemma list_drop_op l1 l2 i:
    drop i l1 ⋅ drop i l2 = drop i (l1 ⋅ l2).
  Proof.
    apply list_eq. intros j.
    rewrite list_lookup_op !lookup_drop -list_lookup_op.
    done.
  Qed.

  Lemma list_take_op l1 l2 i:
    take i l1 ⋅ take i l2 = take i (l1 ⋅ l2).
  Proof.
    apply list_eq. intros j.
    rewrite list_lookup_op.
    destruct (decide (j < i)%nat).
    - by rewrite !lookup_take // -list_lookup_op.
    - by rewrite !lookup_take_ge //; lia.
  Qed.

  Lemma list_lookup_validN_Some n l i x : ✓{n} l → l !! i ≡{n}≡ Some x → ✓{n} x.
  Proof. move=> /list_lookup_validN /(_ i)=> Hl Hi; move: Hl. by rewrite Hi. Qed.
  Lemma list_lookup_valid_Some l i x : ✓ l → l !! i ≡ Some x → ✓ x.
  Proof. move=> /list_lookup_valid /(_ i)=> Hl Hi; move: Hl. by rewrite Hi. Qed.

  Lemma list_length_op l1 l2 : length (l1 ⋅ l2) = max (length l1) (length l2).
  Proof. revert l2. induction l1; intros [|??]; f_equal/=; auto. Qed.

  Lemma replicate_valid n (x : A) : ✓ x → ✓ replicate n x.
  Proof. apply Forall_replicate. Qed.
  Global Instance list_singletonM_ne i :
    NonExpansive (@list_singletonM A i).
  Proof. intros n l1 l2 ?. apply Forall2_app; by repeat constructor. Qed.
  Global Instance list_singletonM_proper i :
    Proper ((≡) ==> (≡)) (list_singletonM i) := ne_proper _.

  Lemma elem_of_list_singletonM i z x : z ∈ ({[i := x]} : list A) → z = ε ∨ z = x.
  Proof.
    rewrite elem_of_app elem_of_list_singleton elem_of_replicate. naive_solver.
  Qed.
  Lemma list_lookup_singletonM i x : ({[ i := x ]} : list A) !! i = Some x.
  Proof. induction i; by f_equal/=. Qed.
  Lemma list_lookup_singletonM_lt i i' x:
    (i' < i)%nat → ({[ i := x ]} : list A) !! i' = Some ε.
  Proof. move: i'. induction i; intros [|i']; naive_solver auto with lia. Qed.
  Lemma list_lookup_singletonM_gt i i' x:
    (i < i')%nat → ({[ i := x ]} : list A) !! i' = None.
  Proof. move: i'. induction i; intros [|i']; naive_solver auto with lia. Qed.
  Lemma list_lookup_singletonM_ne i j x :
    i ≠ j →
    ({[ i := x ]} : list A) !! j = None ∨ ({[ i := x ]} : list A) !! j = Some ε.
  Proof. revert j; induction i; intros [|j]; naive_solver auto with lia. Qed.
  Lemma list_singletonM_validN n i x : ✓{n} ({[ i := x ]} : list A) ↔ ✓{n} x.
  Proof.
    rewrite list_lookup_validN. split.
    { move=> /(_ i). by rewrite list_lookup_singletonM. }
    intros Hx j; destruct (decide (i = j)); subst.
    - by rewrite list_lookup_singletonM.
    - destruct (list_lookup_singletonM_ne i j x) as [Hi|Hi]; first done;
        rewrite Hi; by try apply (ucmra_unit_validN (A:=A)).
  Qed.
  Lemma list_singletonM_valid  i x : ✓ ({[ i := x ]} : list A) ↔ ✓ x.
  Proof.
    rewrite !cmra_valid_validN. by setoid_rewrite list_singletonM_validN.
  Qed.
  Lemma list_singletonM_length i x : length {[ i := x ]} = S i.
  Proof.
    rewrite /singletonM /list_singletonM app_length replicate_length /=; lia.
  Qed.

  Lemma list_singletonM_core i (x : A) : core {[ i := x ]} ≡@{list A} {[ i := core x ]}.
  Proof.
    rewrite /singletonM /list_singletonM.
    by rewrite {1}/core /= fmap_app fmap_replicate (core_id_core ∅).
  Qed.
  Lemma list_singletonM_op i (x y : A) :
    {[ i := x ]} ⋅ {[ i := y ]} ≡@{list A} {[ i := x ⋅ y ]}.
  Proof.
    rewrite /singletonM /list_singletonM /=.
    induction i; constructor; rewrite ?left_id; auto.
  Qed.
  Lemma list_alter_singletonM f i x :
    alter f i ({[i := x]} : list A) = {[i := f x]}.
  Proof.
    rewrite /singletonM /list_singletonM /=. induction i; f_equal/=; auto.
  Qed.
  Global Instance list_singletonM_core_id i (x : A) :
    CoreId x → CoreId {[ i := x ]}.
  Proof. by rewrite !core_id_total list_singletonM_core=> ->. Qed.
  Lemma list_singletonM_snoc l x:
    {[length l := x]} ⋅ l ≡ l ++ [x].
  Proof. elim: l => //= ?? <-. by rewrite left_id. Qed.
  Lemma list_singletonM_included i x l:
    {[i := x]} ≼ l ↔ (∃ x', l !! i = Some x' ∧ x ≼ x').
  Proof.
    rewrite list_lookup_included. split.
    { move /(_ i). rewrite list_lookup_singletonM option_included_total.
      naive_solver. }
    intros (y&Hi&?) j. destruct (Nat.lt_total j i) as [?|[->|?]].
    - rewrite list_lookup_singletonM_lt //.
      destruct (lookup_lt_is_Some_2 l j) as [z Hz].
      { trans i; eauto using lookup_lt_Some. }
      rewrite Hz. by apply Some_included_2, ucmra_unit_least.
    - rewrite list_lookup_singletonM Hi. by apply Some_included_2.
    - rewrite list_lookup_singletonM_gt //. apply: ucmra_unit_least.
  Qed.

  (* Update *)
  Lemma list_singletonM_updateP (P : A → Prop) (Q : list A → Prop) x :
    x ~~>: P → (∀ y, P y → Q [y]) → [x] ~~>: Q.
  Proof.
    rewrite !cmra_total_updateP=> Hup HQ n lf /list_lookup_validN Hv.
    destruct (Hup n (default ε (lf !! 0))) as (y&?&Hv').
    { move: (Hv 0). by destruct lf; rewrite /= ?right_id. }
    exists [y]; split; first by auto.
    apply list_lookup_validN=> i.
    move: (Hv i) Hv'. by destruct i, lf; rewrite /= ?right_id.
  Qed.
  Lemma list_singletonM_updateP' (P : A → Prop) x :
    x ~~>: P → [x] ~~>: λ k, ∃ y, k = [y] ∧ P y.
  Proof. eauto using list_singletonM_updateP. Qed.
  Lemma list_singletonM_update x y : x ~~> y → [x] ~~> [y].
  Proof.
    rewrite !cmra_update_updateP; eauto using list_singletonM_updateP with subst.
  Qed.

  Lemma app_updateP (P1 P2 Q : list A → Prop) l1 l2 :
    l1 ~~>: P1 → l2 ~~>: P2 →
    (∀ k1 k2, P1 k1 → P2 k2 → length l1 = length k1 ∧ Q (k1 ++ k2)) →
    l1 ++ l2 ~~>: Q.
  Proof.
    rewrite !cmra_total_updateP=> Hup1 Hup2 HQ n lf.
    rewrite list_op_app app_validN=> -[??].
    destruct (Hup1 n (take (length l1) lf)) as (k1&?&?); auto.
    destruct (Hup2 n (drop (length l1) lf)) as (k2&?&?); auto.
    exists (k1 ++ k2). rewrite list_op_app app_validN.
    by destruct (HQ k1 k2) as [<- ?].
  Qed.
  Lemma app_update l1 l2 k1 k2 :
    length l1 = length k1 →
    l1 ~~> k1 → l2 ~~> k2 → l1 ++ l2 ~~> k1 ++ k2.
  Proof. rewrite !cmra_update_updateP; eauto using app_updateP with subst. Qed.

  Lemma cons_updateP (P1 : A → Prop) (P2 Q : list A → Prop) x l :
    x ~~>: P1 → l ~~>: P2 → (∀ y k, P1 y → P2 k → Q (y :: k)) → x :: l ~~>: Q.
  Proof.
    intros. eapply (app_updateP _ _ _ [x]);
      naive_solver eauto using list_singletonM_updateP'.
  Qed.
  Lemma cons_updateP' (P1 : A → Prop) (P2 : list A → Prop) x l :
    x ~~>: P1 → l ~~>: P2 → x :: l ~~>: λ k, ∃ y k', k = y :: k' ∧ P1 y ∧ P2 k'.
  Proof. eauto 10 using cons_updateP. Qed.
  Lemma cons_update x y l k : x ~~> y → l ~~> k → x :: l ~~> y :: k.
  Proof. rewrite !cmra_update_updateP; eauto using cons_updateP with subst. Qed.

  Lemma list_middle_updateP (P : A → Prop) (Q : list A → Prop) l1 x l2 :
    x ~~>: P → (∀ y, P y → Q (l1 ++ y :: l2)) → l1 ++ x :: l2 ~~>: Q.
  Proof.
    intros. eapply app_updateP.
    - by apply cmra_update_updateP.
    - by eapply cons_updateP', cmra_update_updateP.
    - naive_solver.
  Qed.
  Lemma list_middle_update l1 l2 x y : x ~~> y → l1 ++ x :: l2 ~~> l1 ++ y :: l2.
  Proof.
    rewrite !cmra_update_updateP=> ?; eauto using list_middle_updateP with subst.
  Qed.

(* FIXME
  Lemma list_middle_local_update l1 l2 x y ml :
    x ~l~> y @ ml ≫= (.!! length l1) →
    l1 ++ x :: l2 ~l~> l1 ++ y :: l2 @ ml.
  Proof.
    intros [Hxy Hxy']; split.
    - intros n; rewrite !list_lookup_validN=> Hl i; move: (Hl i).
      destruct (lt_eq_lt_dec i (length l1)) as [[?|?]|?]; subst.
      + by rewrite !list_lookup_opM !lookup_app_l.
      + rewrite !list_lookup_opM !list_lookup_middle // !Some_op_opM; apply (Hxy n).
      + rewrite !(cons_middle _ l1 l2) !assoc.
        rewrite !list_lookup_opM !lookup_app_r !app_length //=; lia.
    - intros n mk; rewrite !list_lookup_validN !list_dist_lookup => Hl Hl' i.
      move: (Hl i) (Hl' i).
      destruct (lt_eq_lt_dec i (length l1)) as [[?|?]|?]; subst.
      + by rewrite !list_lookup_opM !lookup_app_l.
      + rewrite !list_lookup_opM !list_lookup_middle // !Some_op_opM !inj_iff.
        apply (Hxy' n).
      + rewrite !(cons_middle _ l1 l2) !assoc.
        rewrite !list_lookup_opM !lookup_app_r !app_length //=; lia.
  Qed.
  Lemma list_singleton_local_update i x y ml :
    x ~l~> y @ ml ≫= (.!! i) → {[ i := x ]} ~l~> {[ i := y ]} @ ml.
  Proof. intros; apply list_middle_local_update. by rewrite replicate_length. Qed.
*)

  Lemma list_alloc_singletonM_local_update x l :
    ✓ x → (l, ε) ~l~> (l ++ [x], {[length l := x]}).
  Proof.
    move => ?.
    have -> : ({[length l := x]} ≡@{list A} {[length l := x]} ⋅ ε) by rewrite right_id.
    rewrite -list_singletonM_snoc. apply op_local_update => ??.
    rewrite list_singletonM_snoc app_validN cons_validN. split_and? => //; [| constructor].
    by apply cmra_valid_validN.
  Qed.

  Lemma list_lookup_local_update l k l' k':
    (∀ i, (l !! i, k !! i) ~l~> (l' !! i, k' !! i)) →
    (l, k) ~l~> (l', k').
  Proof.
    intros Hup.
    apply local_update_unital=> n z Hlv Hl.
    assert (∀ i, ✓{n} (l' !! i) /\ l' !! i ≡{n}≡ (k' ⋅ z) !! i) as Hup'.
    { intros i. destruct (Hup i n (Some (z !! i))); simpl in *.
      - by apply list_lookup_validN.
      - rewrite -list_lookup_op.
        by apply list_dist_lookup.
      - by rewrite list_lookup_op.
    }
    split; [apply list_lookup_validN | apply list_dist_lookup].
    all: intros i; by destruct (Hup' i).
  Qed.

  Lemma list_alter_local_update i f g l k:
    (l !! i, k !! i) ~l~> (f <$> (l !! i), g <$> (k !! i)) →
    (l, k) ~l~> (alter f i l, alter g i k).
  Proof.
    intros Hup.
    apply list_lookup_local_update.
    intros i'.
    destruct (decide (i = i')) as [->|].
    - rewrite !list_lookup_alter //.
    - rewrite !list_lookup_alter_ne //.
  Qed.

  (* The "⋅ (replicate ... ++ ...)" part is needed because `m` could be
     shorter than `l`. *)
  Lemma app_l_local_update l k k' m m':
    (k, drop (length l) m) ~l~> (k', m') →
    (l ++ k, m) ~l~> (l ++ k', take (length l) m ⋅ (replicate (length l) ε ++ m')).
  Proof.
    move /(local_update_unital _) => HUp.
    apply local_update_unital => n mm /(app_validN _) [Hlv Hkv] Heq.
    move: (HUp n (drop (length l) mm) Hkv).
    intros [Hk'v Hk'eq];
      first by rewrite list_drop_op -Heq drop_app_le // drop_ge //.
    split; first by apply app_validN.
    rewrite Hk'eq.
    apply list_dist_lookup. intros i. rewrite !list_lookup_op.
    destruct (decide (i < length l)%nat) as [HLt|HGe].
    - rewrite !lookup_app_l //; last by rewrite replicate_length.
      rewrite lookup_take; last done.
      rewrite lookup_replicate_2; last done.
      rewrite comm assoc -list_lookup_op.
      rewrite (mixin_cmra_comm _ list_cmra_mixin) -Heq.
      rewrite lookup_app_l; last done.
      apply lookup_lt_is_Some in HLt as [? HEl].
      by rewrite HEl -Some_op ucmra_unit_right_id.
    - assert (length l ≤ i)%nat as HLe by lia.
      rewrite !lookup_app_r //; last by rewrite replicate_length.
      rewrite replicate_length.
      rewrite lookup_take_ge; last done.
      replace (mm !! _) with (drop (length l) mm !! (i - length l)%nat);
        last by rewrite lookup_drop; congr (mm !! _); lia.
      rewrite -assoc -list_lookup_op. symmetry.
      clear. move: n. apply equiv_dist. apply: ucmra_unit_left_id.
  Qed.

  Lemma app_l_local_update' l k k' m:
    (k, ε) ~l~> (k', m) →
    (l ++ k, ε) ~l~> (l ++ k', replicate (length l) ε ++ m).
  Proof.
    remember (app_l_local_update l k k' ε m) as HH eqn:HeqHH.
    clear HeqHH. move: HH.
    by rewrite take_nil drop_nil ucmra_unit_left_id.
  Qed.

  Lemma app_local_update l m:
    ✓ m → (l, ε) ~l~> (l ++ m, replicate (length l) ε ++ m).
  Proof.
    move: (app_l_local_update' l [] m m).
    rewrite app_nil_r.
    move=> H Hvm. apply H.
    apply local_update_unital=> n z _. rewrite ucmra_unit_left_id.
    move=><-. rewrite ucmra_unit_right_id. split; last done.
    by apply cmra_valid_validN.
  Qed.

  (* The "replicate ..." part is needed because `m'` could be
     shorter than `l`. *)
  Lemma app_r_local_update l l' k m m':
    length l = length l' →
    (l, take (length l) m) ~l~> (l', m') →
    (l ++ k, m) ~l~> (l' ++ k, replicate (length l) ε ⋅ m' ++ drop (length l) m).
  Proof.
    move=> HLen /(local_update_unital _) HUp.
    apply local_update_unital=> n mm /(app_validN _) [Hlv Hkv] Heq.
    move: (HUp n (take (length l) mm) Hlv).
    intros [Hl'v Hl'eq];
      first by rewrite list_take_op -Heq take_app_le // take_ge //.
    split; first by apply app_validN.
    assert (k ≡{n}≡ (drop (length l) (m ⋅ mm))) as ->
      by rewrite -Heq drop_app_le // drop_ge //.
    move: HLen. rewrite Hl'eq. clear. move=> HLen.
    assert (length m' ≤ length l)%nat as HLen'.
    { by rewrite list_length_op in HLen; lia. }
    rewrite list_op_app list_length_op replicate_length max_l;
      last lia.
    rewrite list_drop_op -assoc. rewrite HLen. move: HLen'.
    remember (length l) as o. clear.
    rewrite list_length_op.
    remember (length _ `max` length _)%nat as o'.
    assert (m' ⋅ take o' mm ≡{n}≡ replicate o' ε ⋅ (m' ⋅ take o' mm))
      as <-; last done.
    subst. remember (m' ⋅ take _ _) as m''.
    remember (length m' `max` length (take o mm))%nat as o''.
    assert (o'' ≤ length m'')%nat as HLen.
    { by subst; rewrite list_length_op !take_length; lia. }
    move: HLen. clear.
    intros HLen. move: n. apply equiv_dist, list_equiv_lookup.
    intros i. rewrite list_lookup_op.
    remember length as L eqn:HeqL.
    destruct (decide (i < L m''))%nat as [E|E].
    - subst. apply lookup_lt_is_Some in E as [? HEl].
      rewrite HEl.
      destruct (replicate _ _ !! _) eqn:Z; last done.
      apply lookup_replicate in Z as [-> _].
      by rewrite -Some_op ucmra_unit_left_id.
    - rewrite lookup_ge_None_2.
      { rewrite lookup_ge_None_2 //.
        by rewrite replicate_length; lia. }
      rewrite -HeqL. lia.
  Qed.

  Lemma app_r_local_update' l l' k k':
    length l = length l' →
    (l, ε) ~l~> (l', k') →
    (l ++ k, ε) ~l~> (l' ++ k, k').
  Proof.
    move=> HLen /(local_update_unital _) HUp.
    apply local_update_unital=> n mz /(app_validN _) [Hlv Hkv].
    move: (HUp n l). rewrite !ucmra_unit_left_id.
    intros [Hk'v Hk'eq] <-; [done|done|].
    split; first by apply app_validN.
    move: HLen. rewrite Hk'eq. clear. move=> HLen.
    assert (length k' ≤ length l)%nat as Hk'Len
        by (rewrite HLen list_length_op; lia).
    rewrite (mixin_cmra_comm _ list_cmra_mixin k' (l ++ k)).
    rewrite list_op_app_le; last done.
    by rewrite (mixin_cmra_comm _ list_cmra_mixin l k').
  Qed.

End properties.

(** Functor *)
Global Instance list_fmap_cmra_morphism {A B : ucmra} (f : A → B)
  `{!CmraMorphism f} : CmraMorphism (fmap f : list A → list B).
Proof.
  split; try apply _.
  - intros n l. rewrite !list_lookup_validN=> Hl i. rewrite list_lookup_fmap.
    by apply (cmra_morphism_validN (fmap f : option A → option B)).
  - intros l. apply Some_proper. rewrite -!list_fmap_compose.
    apply list_fmap_equiv_ext, cmra_morphism_core, _.
  - intros l1 l2. apply list_equiv_lookup=>i.
    by rewrite list_lookup_op !list_lookup_fmap list_lookup_op cmra_morphism_op.
Qed.

Program Definition listURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := listUR (urFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg := listO_map (urFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, urFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_equiv_ext=>y. apply urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_equiv_ext=>y; apply urFunctor_map_compose.
Qed.

Global Instance listURF_contractive F :
  urFunctorContractive F → urFunctorContractive (listURF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, urFunctor_map_contractive.
Qed.

Program Definition listRF (F : urFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := listR (urFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := listO_map (urFunctor_map F fg)
|}.
Solve Obligations with apply listURF.

Global Instance listRF_contractive F :
  urFunctorContractive F → rFunctorContractive (listRF F).
Proof. apply listURF_contractive. Qed.
