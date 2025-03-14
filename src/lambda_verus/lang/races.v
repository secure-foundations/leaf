From stdpp Require Import gmap.
From iris.program_logic Require Import adequacy.
From lrust.lang Require Import tactics.
Set Default Proof Using "Type".

Inductive access_kind : Type := ReadAcc | WriteAcc | FreeAcc.

(* This is a crucial definition; if we forget to sync it with head_step,
   the results proven here are worthless. *)
Inductive next_access_head : expr → state → access_kind * order → loc → Prop :=
| Access_read ord l σ :
    next_access_head (Read ord (Lit $ LitLoc l)) σ (ReadAcc, ord) l
| Access_write ord l e σ :
    is_Some (to_val e) →
    next_access_head (Write ord (Lit $ LitLoc l) e) σ (WriteAcc, ord) l
| Access_cas_fail l st e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some (LitV lit1) → to_val e2 = Some (LitV lit2) →
    lit_neq lit1 litl → σ !! l = Some (st, LitV litl) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (ReadAcc, ScOrd) l
| Access_cas_suc l st e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some (LitV lit1) → to_val e2 = Some (LitV lit2) →
    lit_eq σ lit1 litl → σ !! l = Some (st, LitV litl) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (WriteAcc, ScOrd) l
| Access_free n l σ i :
    0 ≤ i < n →
    next_access_head (Free (Lit $ LitInt n) (Lit $ LitLoc l))
                     σ (FreeAcc, Na2Ord) (l +ₗ i).

(* Some sanity checks to make sure the definition above is not entirely insensible. *)
Goal ∀ e1 e2 e3 σ, head_reducible (CAS e1 e2 e3) σ →
                   ∃ a l, next_access_head (CAS e1 e2 e3) σ a l.
Proof.
  intros ??? σ (?&?&?&?&?). inversion H; do 2 eexists;
    (eapply Access_cas_fail; done) || eapply Access_cas_suc; done.
Qed.
Goal ∀ o e σ, head_reducible (Read o e) σ →
              ∃ a l, next_access_head (Read o e) σ a l.
Proof.
  intros ?? σ (?&?&?&?&?). inversion H; do 2 eexists; eapply Access_read; done.
Qed.
Goal ∀ o e1 e2 σ, head_reducible (Write o e1 e2) σ →
              ∃ a l, next_access_head (Write o e1 e2) σ a l.
Proof.
  intros ??? σ (?&?&?&?&?). inversion H; do 2 eexists;
    eapply Access_write; try done; eexists; done.
Qed.
Goal ∀ e1 e2 σ, head_reducible (Free e1 e2) σ →
              ∃ a l, next_access_head (Free e1 e2) σ a l.
Proof.
  intros ?? σ (?&?&?&?&?). inversion H; do 2 eexists; eapply Access_free; done.
Qed.

Definition next_access_thread (e: expr) (σ : state)
           (a : access_kind * order) (l : loc) : Prop :=
  ∃ K e', next_access_head e' σ a l ∧ e = fill K e'.

Definition next_accesses_threadpool (el: list expr) (σ : state)
           (a1 a2 : access_kind * order) (l : loc): Prop :=
  ∃ t1 e1 t2 e2 t3, el = t1 ++ e1 :: t2 ++ e2 :: t3 ∧
                    next_access_thread e1 σ a1 l ∧ next_access_thread e2 σ a2 l.

Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.

Definition nonracing_threadpool (el : list expr) (σ : state) : Prop :=
  ∀ l a1 a2, next_accesses_threadpool el σ a1 a2 l →
             nonracing_accesses a1 a2.

Lemma next_access_head_reductible_ctx e σ σ' a l K :
  next_access_head e σ' a l → reducible (fill K e) σ → head_reducible e σ.
Proof.
  intros Hhead Hred. apply prim_head_reducible.
  - eapply (reducible_fill_inv (K:=ectx_language.fill K)), Hred. destruct Hhead; eauto.
  - apply ectxi_language_sub_redexes_are_values. intros [] ? ->; inversion Hhead; eauto.
Qed.

Definition head_reduce_not_to_stuck (e : expr) (σ : state) :=
  ∀ κ e' σ' efs, ectx_language.head_step e σ κ e' σ' efs → e' ≠ App (Lit $ LitInt 0) [].

Lemma next_access_head_reducible_state e σ a l :
  next_access_head e σ a l → head_reducible e σ →
  head_reduce_not_to_stuck e σ →
  match a with
  | (ReadAcc, (ScOrd | Na1Ord)) => ∃ v n, σ !! l = Some (RSt n, v)
  | (ReadAcc, Na2Ord) => ∃ v n, σ !! l = Some (RSt (S n), v)
  | (WriteAcc, (ScOrd | Na1Ord)) => ∃ v, σ !! l = Some (RSt 0, v)
  | (WriteAcc, Na2Ord) => ∃ v, σ !! l = Some (WSt, v)
  | (FreeAcc, _) => ∃ v ls, σ !! l = Some (ls, v)
  end.
Proof.
  intros Ha (κ&e'&σ'&ef&Hstep) Hrednonstuck. destruct Ha; inv_head_step; eauto.
  - destruct n; first by eexists. exfalso. eapply Hrednonstuck; last done.
    by eapply CasStuckS.
  - exfalso. eapply Hrednonstuck; last done.
    eapply CasStuckS; done.
  - match goal with H : ∀ m, _ |- _ => destruct (H i) as [_ [[]?]] end; eauto.
Qed.

Lemma next_access_head_Na1Ord_step e1 e2 ef σ1 σ2 κ a l :
  next_access_head e1 σ1 (a, Na1Ord) l →
  head_step e1 σ1 κ e2 σ2 ef →
  next_access_head e2 σ2 (a, Na2Ord) l.
Proof.
  intros Ha Hstep. inversion Ha; subst; clear Ha; inv_head_step; constructor; by rewrite to_of_val.
Qed.

Lemma next_access_head_Na1Ord_concurent_step e1 e1' e2 e'f σ σ' κ a1 a2 l :
  next_access_head e1 σ (a1, Na1Ord) l →
  head_step e1 σ κ e1' σ' e'f →
  next_access_head e2 σ a2 l →
  next_access_head e2 σ' a2 l.
Proof.
  intros Ha1 Hstep Ha2. inversion Ha1; subst; clear Ha1; inv_head_step;
  destruct Ha2; simplify_eq; econstructor; eauto; try apply lookup_insert.
  (* Oh my. FIXME. *)
  - eapply lit_eq_state; last done.
    setoid_rewrite <-(not_elem_of_dom (D:=gset loc)). rewrite dom_insert_L.
    cut (is_Some (σ !! l)); last by eexists. rewrite -(elem_of_dom (D:=gset loc)). set_solver+.
  - eapply lit_eq_state; last done.
    setoid_rewrite <-(not_elem_of_dom (D:=gset loc)). rewrite dom_insert_L.
    cut (is_Some (σ !! l)); last by eexists. rewrite -(elem_of_dom (D:=gset loc)). set_solver+.
Qed.

Lemma next_access_head_Free_concurent_step e1 e1' e2 e'f σ σ' κ o1 a2 l :
  next_access_head e1 σ (FreeAcc, o1) l → head_step e1 σ κ e1' σ' e'f →
  next_access_head e2 σ a2 l → head_reducible e2 σ' →
  False.
Proof.
  intros Ha1 Hstep Ha2 Hred2.
  assert (FREE : ∀ l n i, 0 ≤ i ∧ i < n → free_mem l (Z.to_nat n) σ !! (l +ₗ i) = None).
  { clear. intros l n i Hi.
    replace n with (Z.of_nat (Z.to_nat n)) in Hi by (apply Z2Nat.id; lia).
    revert l i Hi. induction (Z.to_nat n) as [|? IH]=>/=l i Hi. lia.
    destruct (decide (i = 0)).
    - subst. by rewrite /shift_loc Z.add_0_r -surjective_pairing lookup_delete.
    - replace i with (1+(i-1)) by lia.
      rewrite lookup_delete_ne -shift_loc_assoc ?IH //. lia.
      destruct l; intros [=?]. lia. }
  assert (FREE' : σ' !! l = None).
  { inversion Ha1; clear Ha1; inv_head_step. auto. }
  destruct Hred2 as (κ'&e2'&σ''&ef&?).
  inversion Ha2; clear Ha2; inv_head_step.
  eapply (@is_Some_None (lock_state * val)). rewrite -FREE'. naive_solver.
Qed.

Lemma safe_step_not_reduce_to_stuck el σ K e e' σ' ef κ :
  (∀ el' σ' e', rtc erased_step (el, σ) (el', σ') →
                e' ∈ el' → to_val e' = None → reducible e' σ') →
  fill K e ∈ el → head_step e σ κ e' σ' ef → head_reduce_not_to_stuck e' σ'.
Proof.
  intros Hsafe Hi Hstep κ1 e1 σ1 ? Hstep1 Hstuck.
  cut (reducible (fill K e1) σ1).
  { subst. intros (?&?&?&?&?). by eapply stuck_irreducible. }
  destruct (elem_of_list_split _ _ Hi) as (?&?&->).
  eapply Hsafe; last by (apply: fill_not_val; subst).
  - eapply rtc_l, rtc_l, rtc_refl.
    + eexists. econstructor. done. done. econstructor; done.
    + eexists. econstructor. done. done. econstructor; done.
  - subst. set_solver+.
Qed.

(* TODO: Unify this and the above. *)
Lemma safe_not_reduce_to_stuck el σ K e :
  (∀ el' σ' e', rtc erased_step (el, σ) (el', σ') →
                e' ∈ el' → to_val e' = None → reducible e' σ') →
  fill K e ∈ el → head_reduce_not_to_stuck e σ.
Proof.
  intros Hsafe Hi κ e1 σ1 ? Hstep1 Hstuck.
  cut (reducible (fill K e1) σ1).
  { subst. intros (?&?&?&?&?). by eapply stuck_irreducible. }
  destruct (elem_of_list_split _ _ Hi) as (?&?&->).
  eapply Hsafe; last by (apply: fill_not_val; subst).
  - eapply rtc_l, rtc_refl.
    + eexists. econstructor. done. done. econstructor; done.
  - subst. set_solver+.
Qed.

Theorem safe_nonracing el σ :
  (∀ el' σ' e', rtc erased_step (el, σ) (el', σ') →
                e' ∈ el' → to_val e' = None → reducible e' σ') →
  nonracing_threadpool el σ.
Proof.
  intros Hsafe l a1 a2 (t1&?&t2&?&t3&->&(K1&e1&Ha1&->)&(K2&e2&Ha2&->)).

  assert (to_val e1 = None). by destruct Ha1.
  assert (Hrede1:head_reducible e1 σ).
  { eapply (next_access_head_reductible_ctx e1 σ σ a1 l K1), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse1:head_reduce_not_to_stuck e1 σ).
  { eapply safe_not_reduce_to_stuck with (K:=K1); first done. set_solver+. }
  assert (Hσe1:=next_access_head_reducible_state _ _ _ _ Ha1 Hrede1 Hnse1).
  destruct Hrede1 as (κ1'&e1'&σ1'&ef1&Hstep1). clear Hnse1.
  assert (Ha1' : a1.2 = Na1Ord → next_access_head e1' σ1' (a1.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep1.
    by destruct a1; simpl in *; subst. }
  assert (Hrtc_step1:
    rtc erased_step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        (t1 ++ fill K1 e1' :: t2 ++ fill K2 e2 :: t3 ++ ef1, σ1')).
  { eapply rtc_l, rtc_refl. eexists. eapply step_atomic, Ectx_step, Hstep1; try  done.
    by rewrite -assoc. }
  assert (Hrede1: a1.2 = Na1Ord → head_reducible e1' σ1').
  { destruct a1 as [a1 []]=>// _.
    eapply (next_access_head_reductible_ctx e1' σ1' σ1' (a1, Na2Ord) l K1), Hsafe,
           fill_not_val=>//.
    by auto. abstract set_solver. by destruct Hstep1; inversion Ha1. }
  assert (Hnse1: head_reduce_not_to_stuck e1' σ1').
  { eapply safe_step_not_reduce_to_stuck with (K:=K1); first done; last done. set_solver+. }

  assert (to_val e2 = None). by destruct Ha2.
  assert (Hrede2:head_reducible e2 σ).
  { eapply (next_access_head_reductible_ctx e2 σ σ a2 l K2), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse2:head_reduce_not_to_stuck e2 σ).
  { eapply safe_not_reduce_to_stuck with (K:=K2); first done. set_solver+. }
  assert (Hσe2:=next_access_head_reducible_state _ _ _ _ Ha2 Hrede2 Hnse2).
  destruct Hrede2 as (κ2'&e2'&σ2'&ef2&Hstep2).
  assert (Ha2' : a2.2 = Na1Ord → next_access_head e2' σ2' (a2.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep2.
    by destruct a2; simpl in *; subst. }
  assert (Hrtc_step2:
    rtc erased_step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2' :: t3 ++ ef2, σ2')).
  { eapply rtc_l, rtc_refl. rewrite app_comm_cons assoc. eexists.
    eapply step_atomic, Ectx_step, Hstep2; try done. by rewrite -assoc. }
  assert (Hrede2: a2.2 = Na1Ord → head_reducible e2' σ2').
  { destruct a2 as [a2 []]=>// _.
    eapply (next_access_head_reductible_ctx e2' σ2' σ2' (a2, Na2Ord) l K2), Hsafe,
           fill_not_val=>//.
    by auto. abstract set_solver. by destruct Hstep2; inversion Ha2. }
  assert (Hnse2':head_reduce_not_to_stuck e2' σ2').
  { eapply safe_step_not_reduce_to_stuck with (K:=K2); first done; last done. set_solver+. }

  assert (Ha1'2 : a1.2 = Na1Ord → next_access_head e2 σ1' a2 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede1_2: head_reducible e2 σ1').
  { intros. eapply (next_access_head_reductible_ctx e2 σ1' σ  a2 l K2), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse1_2:head_reduce_not_to_stuck e2 σ1').
  { eapply safe_not_reduce_to_stuck with (K:=K2).
    - intros. eapply Hsafe. etrans; last done. done. done. done.
    - set_solver+. }
  assert (Hσe1'1:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha1' Hord) (Hrede1 Hord) Hnse1).
  assert (Hσe1'2:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha1'2 Hord) Hrede1_2 Hnse1_2).

  assert (Ha2'1 : a2.2 = Na1Ord → next_access_head e1 σ2' a1 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede2_1: head_reducible e1 σ2').
  { intros. eapply (next_access_head_reductible_ctx e1 σ2' σ a1 l K1), Hsafe, fill_not_val=>//.
    abstract set_solver. }
  assert (Hnse2_1:head_reduce_not_to_stuck e1 σ2').
  { eapply safe_not_reduce_to_stuck with (K:=K1).
    - intros. eapply Hsafe. etrans; last done. done. done. done.
    - set_solver+. }
  assert (Hσe2'1:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha2'1 Hord) Hrede2_1 Hnse2_1).
  assert (Hσe2'2:=
    λ Hord, next_access_head_reducible_state _ _ _ _ (Ha2' Hord) (Hrede2 Hord) Hnse2').

  assert (a1.1 = FreeAcc → False).
  { destruct a1 as [[]?]; inversion 1.
    eauto using next_access_head_Free_concurent_step. }
  assert (a2.1 = FreeAcc → False).
  { destruct a2 as [[]?]; inversion 1.
    eauto using next_access_head_Free_concurent_step. }

  destruct Ha1 as [[]|[]| | |], Ha2 as [[]|[]| | |]=>//=; simpl in *;
    repeat match goal with
    | H : _ = Na1Ord → _ |- _ => specialize (H (eq_refl Na1Ord)) || clear H
    | H : False |- _ => destruct H
    | H : ∃ _, _ |- _ => destruct H
    end;
    try congruence.

  clear κ2' e2' Hnse2' Hnse2_1 Hstep2 σ2' Hrtc_step2 Hrede2_1.
  destruct Hrede1_2 as (κ2'&e2'&σ'&ef&?).
  inv_head_step.
  match goal with
  | H : <[l:=_]> σ !! l = _ |- _ => by rewrite lookup_insert in H
  end.
Qed.

Corollary adequate_nonracing e1 t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  nonracing_threadpool t2 σ2.
Proof.
  intros [_ Had] Hrtc. apply safe_nonracing. intros el' σ' e' ?? He'.
  edestruct (Had el' σ' e') as [He''|]; try done. etrans; eassumption.
  rewrite /language.to_val /= He' in He''. by edestruct @is_Some_None.
Qed.
