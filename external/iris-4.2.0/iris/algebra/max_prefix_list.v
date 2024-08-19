(** Defines an RA on lists whose composition is only defined when one operand is
a prefix of the other. The result is the longer list.
In particular, the core is the identity function for all elements. *)
From iris.algebra Require Export agree list gmap updates.
From iris.algebra Require Import local_updates proofmode_classes.
From iris.prelude Require Import options.

Definition max_prefix_list (A : Type) := gmap nat (agree A).
Definition max_prefix_listR (A : ofe) := gmapUR nat (agreeR A).
Definition max_prefix_listUR (A : ofe) := gmapUR nat (agreeR A).

Definition to_max_prefix_list {A} (l : list A) : gmap nat (agree A) :=
  to_agree <$> map_seq 0 l.
Global Instance: Params (@to_max_prefix_list) 1 := {}.
Global Typeclasses Opaque to_max_prefix_list.

Section max_prefix_list.
  Context {A : ofe}.
  Implicit Types l : list A.

  Global Instance to_max_prefix_list_ne : NonExpansive (@to_max_prefix_list A).
  Proof. solve_proper. Qed.
  Global Instance to_max_prefix_list_proper :
    Proper ((≡) ==> (≡)) (@to_max_prefix_list A).
  Proof. solve_proper. Qed.
  Global Instance to_max_prefix_list_dist_inj n :
    Inj (dist n) (dist n) (@to_max_prefix_list A).
  Proof.
    rewrite /to_max_prefix_list. intros l1 l2 Hl. apply list_dist_lookup=> i.
    move: (Hl i). rewrite !lookup_fmap !lookup_map_seq Nat.sub_0_r.
    rewrite !option_guard_True; [|lia..].
    destruct (l1 !! i), (l2 !! i); inversion_clear 1;
      constructor; by apply (inj to_agree).
  Qed.
  Global Instance to_max_prefix_list_inj : Inj (≡) (≡) (@to_max_prefix_list A).
  Proof.
    intros l1 l2. rewrite !equiv_dist=> ? n. by apply (inj to_max_prefix_list).
  Qed.

  Global Instance mono_list_lb_core_id (m : max_prefix_list A) : CoreId m := _.

  Lemma to_max_prefix_list_valid l : ✓ to_max_prefix_list l.
  Proof.
    intros i. rewrite /to_max_prefix_list lookup_fmap.
    by destruct (map_seq 0 l !! i).
  Qed.
  Lemma to_max_prefix_list_validN n l : ✓{n} to_max_prefix_list l.
  Proof. apply cmra_valid_validN, to_max_prefix_list_valid. Qed.

  Local Lemma to_max_prefix_list_app l1 l2 :
    to_max_prefix_list (l1 ++ l2) ≡
    to_max_prefix_list l1 ⋅ (to_agree <$> map_seq (length l1) l2).
  Proof.
    rewrite /to_max_prefix_list map_seq_app=> i /=. rewrite lookup_op !lookup_fmap.
    destruct (map_seq 0 l1 !! i) as [x|] eqn:Hl1; simpl; last first.
    { by rewrite lookup_union_r // left_id. }
    rewrite (lookup_union_Some_l _ _ _ x) //=.
    assert (map_seq (M:=gmap nat A) (length l1) l2 !! i = None) as ->.
    { apply lookup_map_seq_None.
      apply lookup_map_seq_Some in Hl1 as [_ ?%lookup_lt_Some]. lia. }
    by rewrite /= right_id.
  Qed.

  Lemma to_max_prefix_list_op_l l1 l2 :
    l1 `prefix_of` l2 →
    to_max_prefix_list l1 ⋅ to_max_prefix_list l2 ≡ to_max_prefix_list l2.
  Proof. intros [l ->]. by rewrite to_max_prefix_list_app assoc -core_id_dup. Qed.
  Lemma to_max_prefix_list_op_r l1 l2 :
    l1 `prefix_of` l2 →
    to_max_prefix_list l2 ⋅ to_max_prefix_list l1 ≡ to_max_prefix_list l2.
  Proof. intros. by rewrite comm to_max_prefix_list_op_l. Qed.

  Lemma max_prefix_list_included_includedN (ml1 ml2 : max_prefix_list A) :
    ml1 ≼ ml2 ↔ ∀ n, ml1 ≼{n} ml2.
  Proof.
    split; [intros; by apply: cmra_included_includedN|].
    intros Hincl. exists ml2. apply equiv_dist=> n. destruct (Hincl n) as [l ->].
    by rewrite assoc -core_id_dup.
  Qed.

  Local Lemma to_max_prefix_list_includedN_aux n l1 l2 :
    to_max_prefix_list l1 ≼{n} to_max_prefix_list l2 →
    l2 ≡{n}≡ l1 ++ drop (length l1) l2.
  Proof.
    rewrite lookup_includedN=> Hincl. apply list_dist_lookup=> i.
    rewrite lookup_app. move: (Hincl i).
    rewrite /to_max_prefix_list !lookup_fmap !lookup_map_seq Nat.sub_0_r.
    rewrite !option_guard_True; [|lia..].
    rewrite option_includedN_total fmap_None.
    intros [Hi|(?&?&(a2&->&->)%fmap_Some&(a1&->&->)%fmap_Some&Ha)].
    - rewrite lookup_drop Hi. apply lookup_ge_None in Hi. f_equiv; lia.
    - f_equiv. symmetry. by apply to_agree_includedN.
  Qed.
  Lemma to_max_prefix_list_includedN n l1 l2 :
    to_max_prefix_list l1 ≼{n} to_max_prefix_list l2 ↔ ∃ l, l2 ≡{n}≡ l1 ++ l.
  Proof.
    split.
    - intros. eexists. by apply to_max_prefix_list_includedN_aux.
    - intros [l ->]. rewrite to_max_prefix_list_app. apply: cmra_includedN_l.
  Qed.
  Lemma to_max_prefix_list_included l1 l2 :
    to_max_prefix_list l1 ≼ to_max_prefix_list l2 ↔ ∃ l, l2 ≡ l1 ++ l.
  Proof.
    split.
    - intros. eexists. apply equiv_dist=> n.
      apply to_max_prefix_list_includedN_aux. by apply: cmra_included_includedN.
    - intros [l ->]. rewrite to_max_prefix_list_app. eauto.
  Qed.
  Lemma to_max_prefix_list_included_L `{!LeibnizEquiv A} l1 l2 :
    to_max_prefix_list l1 ≼ to_max_prefix_list l2 ↔ l1 `prefix_of` l2.
  Proof. rewrite to_max_prefix_list_included /prefix. naive_solver. Qed.

  Local Lemma to_max_prefix_list_op_validN_aux n l1 l2 :
    length l1 ≤ length l2 →
    ✓{n} (to_max_prefix_list l1 ⋅ to_max_prefix_list l2) →
    l2 ≡{n}≡ l1 ++ drop (length l1) l2.
  Proof.
    intros Hlen Hvalid. apply list_dist_lookup=> i. move: (Hvalid i).
    rewrite /to_max_prefix_list lookup_op !lookup_fmap !lookup_map_seq Nat.sub_0_r.
    rewrite !option_guard_True; [|lia..].
    intros ?. rewrite lookup_app.
    destruct (l1 !! i) as [x1|] eqn:Hi1, (l2 !! i) as [x2|] eqn:Hi2; simpl in *.
    - f_equiv. symmetry. by apply to_agree_op_validN.
    - apply lookup_lt_Some in Hi1; apply lookup_ge_None in Hi2. lia.
    - apply lookup_ge_None in Hi1. rewrite lookup_drop -Hi2. f_equiv; lia.
    - apply lookup_ge_None in Hi1. rewrite lookup_drop -Hi2. f_equiv; lia.
  Qed.
  Lemma to_max_prefix_list_op_validN n l1 l2 :
    ✓{n} (to_max_prefix_list l1 ⋅ to_max_prefix_list l2) ↔
    (∃ l, l2 ≡{n}≡ l1 ++ l) ∨ (∃ l, l1 ≡{n}≡ l2 ++ l).
  Proof.
    split.
    - destruct (decide (length l1 ≤ length l2)).
      + left. eexists. by eapply to_max_prefix_list_op_validN_aux.
      + right. eexists. eapply to_max_prefix_list_op_validN_aux; [lia|by rewrite comm].
    - intros [[l ->]|[l ->]].
      + rewrite to_max_prefix_list_op_l; last by apply prefix_app_r.
        apply to_max_prefix_list_validN.
      + rewrite to_max_prefix_list_op_r; last by apply prefix_app_r.
        apply to_max_prefix_list_validN.
  Qed.
  Lemma to_max_prefix_list_op_valid l1 l2 :
    ✓ (to_max_prefix_list l1 ⋅ to_max_prefix_list l2) ↔
    (∃ l, l2 ≡ l1 ++ l) ∨ (∃ l, l1 ≡ l2 ++ l).
  Proof.
    split.
    - destruct (decide (length l1 ≤ length l2)).
      + left. eexists. apply equiv_dist=> n'.
        by eapply to_max_prefix_list_op_validN_aux, cmra_valid_validN.
      + right. eexists. apply equiv_dist=> n'.
        by eapply to_max_prefix_list_op_validN_aux,
          cmra_valid_validN; [lia|by rewrite comm].
    - intros [[l ->]|[l ->]].
      + rewrite to_max_prefix_list_op_l; last by apply prefix_app_r.
        apply to_max_prefix_list_valid.
      + rewrite to_max_prefix_list_op_r; last by apply prefix_app_r.
        apply to_max_prefix_list_valid.
  Qed.
  Lemma to_max_prefix_list_op_valid_L `{!LeibnizEquiv A} l1 l2 :
    ✓ (to_max_prefix_list l1 ⋅ to_max_prefix_list l2) ↔
    l1 `prefix_of` l2 ∨ l2 `prefix_of` l1.
  Proof. rewrite to_max_prefix_list_op_valid /prefix. naive_solver. Qed.

  Lemma max_prefix_list_local_update l1 l2 :
    l1 `prefix_of` l2 →
    (to_max_prefix_list l1, to_max_prefix_list l1) ~l~>
      (to_max_prefix_list l2, to_max_prefix_list l2).
  Proof.
    intros [l ->]. rewrite to_max_prefix_list_app (comm _ (to_max_prefix_list l1)).
    apply op_local_update=> n _. rewrite comm -to_max_prefix_list_app.
    apply to_max_prefix_list_validN.
  Qed.
End max_prefix_list.

Definition max_prefix_listURF (F : oFunctor) : urFunctor :=
  gmapURF nat (agreeRF F).

Global Instance max_prefix_listURF_contractive F :
  oFunctorContractive F → urFunctorContractive (max_prefix_listURF F).
Proof. apply _. Qed.

Definition max_prefix_listRF (F : oFunctor) : rFunctor :=
  gmapRF nat (agreeRF F).

Global Instance max_prefix_listRF_contractive F :
  oFunctorContractive F → rFunctorContractive (max_prefix_listRF F).
Proof. apply _. Qed.
