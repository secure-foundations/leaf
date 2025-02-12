From iris.prelude Require Import options.
Require Import guarding.guard.
Require Import guarding.storage_protocol.base_storage_opt.
Require Import guarding.storage_protocol.protocol.
Require Import stdpp.base.
From iris.algebra Require Import cmra updates proofmode_classes auth.
From iris.base_logic.lib Require Export own iprop invariants.
From iris.proofmode Require Import base ltac_tactics tactics coq_tactics.

(** Resource logic for implementing a RwLock **)

(* begin hide *)
Inductive AgN (S: Type) `{!EqDecision S} :=
  | Empty : AgN S
  | Have : S -> nat -> AgN S
  | Conflict : AgN S
.
Arguments Empty {_}%type_scope {EqDecision0}.
Arguments Have {_}%type_scope {EqDecision0} _ _%nat_scope.
Arguments Conflict {_}%type_scope {EqDecision0}.

Instance free_op {S} `{!EqDecision S} : Op (AgN S) := λ a b , match a, b with
  | Empty, y => y
  | Conflict, y => Conflict
  | Have m x, Empty => Have m x
  | Have m x, Have n y => if decide (m = n) then Have m (x + y + 1) else Conflict
  | Have _ _, Conflict => Conflict
  end
.

Instance free_op_comm {S} `{!EqDecision S} : Comm (=) (@free_op S EqDecision0).
Proof. unfold Comm. intros. unfold free_op. destruct x, y; trivial.
  repeat case_decide; trivial.
  - f_equal. + symmetry. trivial. + lia.
  - subst s. contradiction.
  - subst s. contradiction.
Qed.

Instance free_op_assoc {S} `{!EqDecision S} : Assoc (=) (@free_op S EqDecision0).
Proof. unfold Assoc. intros. unfold free_op. destruct x, y, z; try case_decide; intuition.
  - case_decide; trivial. case_decide.
    + f_equal. lia.
    + subst s. contradiction.
  - case_decide; trivial. case_decide; trivial. subst s. intuition.
Qed.

Inductive Exc (S: Type) :=
  | Unknown : Exc S
  | Yes : S -> Exc S
  | Fail : Exc S
.
Arguments Unknown {_}%type_scope.
Arguments Yes {_}%type_scope _.
Arguments Fail {_}%type_scope.

Instance exc_op {S} : Op (Exc S) := λ a b , match a, b with
  | Unknown, y => y
  | Fail, y => Fail
  | Yes m, Unknown => Yes m
  | Yes _, _ => Fail
  end
.

Instance exc_op_comm {S} `{!EqDecision S} : Comm (=) (@exc_op S).
Proof. unfold Comm. intros. unfold exc_op. destruct x, y; trivial.
Qed.

Instance exc_op_assoc {S} `{!EqDecision S} : Assoc (=) (@exc_op S).
Proof. unfold Assoc. intros. unfold exc_op. destruct x, y, z; trivial.
Qed.

Inductive RwLock (S: Type) `{!EqDecision S} :=
  | Rwl : (Exc (bool * Z * S)) -> Exc () -> Exc () -> nat -> AgN S -> RwLock S
.
Arguments Rwl {_}%type_scope {EqDecision0} _ _ _ _%nat_scope _.

Instance rw_op {S} `{!EqDecision S} : Op (RwLock S) := λ a b , match a, b with
  | Rwl c ep eg sp sg, Rwl c' ep' eg' sp' sg' =>
      Rwl (c ⋅ c') (ep ⋅ ep') (eg ⋅ eg') (sp + sp') (sg ⋅ sg')
  end
.

Instance rw_op_comm {S} `{!EqDecision S} : Comm (=) (@rw_op S EqDecision0).
Proof. unfold Comm. intros. unfold rw_op. destruct x, y.
  f_equal.
  - apply exc_op_comm.
  - apply exc_op_comm.
  - apply exc_op_comm.
  - lia.
  - apply free_op_comm.
Qed.

Instance rw_op_assoc {S} `{!EqDecision S} : Assoc (=) (@rw_op S EqDecision0).
Proof. unfold Assoc. intros. unfold rw_op. destruct x, y, z.
  f_equal.
  - apply exc_op_assoc.
  - apply exc_op_assoc.
  - apply exc_op_assoc.
  - lia.
  - apply free_op_assoc.
Qed.

Definition Central {S: Type} `{!EqDecision S} (e: bool) (r: Z) (x: S) : RwLock S :=
  Rwl (Yes (e, r, x)) Unknown Unknown 0 (Empty).
  
Definition ExcPending {S: Type} `{!EqDecision S}: RwLock S :=
  Rwl Unknown (Yes ()) Unknown 0 (Empty).
  
Definition ExcGuard {S: Type} `{!EqDecision S}: RwLock S :=
  Rwl Unknown Unknown (Yes ()) 0 (Empty).
  
Definition ShPending {S: Type} `{!EqDecision S}: RwLock S :=
  Rwl Unknown Unknown Unknown 1 (Empty).
  
Definition ShGuard {S: Type} `{!EqDecision S} (m: S) : RwLock S :=
  Rwl Unknown Unknown Unknown 0 (Have m 0).
  
Definition free_count {S} `{!EqDecision S} (m: AgN S) : nat :=
  match m with
  | Empty => 0
  | Have _ n => n + 1
  | Conflict => 0
  end.
  
Instance rwlock_sp_inv {S} `{!EqDecision S} : SPInv (RwLock S) :=
  λ rw ,
  match rw with
  | Rwl _ Fail _ _ _ => False
  | Rwl _ _ Fail _ _ => False
  | Rwl _ _ _ _ Conflict => False
  | Rwl (Yes (e, r, x)) ep eg sp sg =>
         r = sp + (free_count sg)
      /\ (e = false -> ep = Unknown /\ eg = Unknown)
      /\ (e = true -> (ep = Yes () \/ eg = Yes ()) /\ ¬(ep = Yes() /\ eg = Yes()))
      /\ (eg = Yes () -> sg = Empty)
      /\ (match sg with Have m _ => x = m | _ => True end)
  | _ => False
  end.

Instance rwlock_unit (S: Type) `{!EqDecision S} : Unit (RwLock S) :=
  Rwl Unknown Unknown Unknown 0 Empty.

Global Instance rwlock_interp (S: Type) `{!EqDecision S} : SPInterp (RwLock S) (BaseOpt S) :=
  λ rw , match rw with
    | Rwl (Yes (_,_,x)) _ Unknown _ _ => Full x
    | _ => base_storage_opt.Empty
  end.

Lemma rw_unit_dot (S: Type) `{!EqDecision S} (a : RwLock S) :
  rw_op a ε = a.
Proof.
  unfold ε, rwlock_unit. destruct a. unfold "⋅", rw_op. unfold "⋅", exc_op, free_op.
  f_equal; trivial.
  - destruct e; trivial.
  - destruct e0; trivial.
  - destruct e1; trivial.
  - lia.
  - destruct a; trivial.
Qed.

Lemma rw_unit_dot_left (S: Type) `{!EqDecision S} (a : RwLock S) :
  rw_op ε a = a.
Proof.
  destruct a; trivial.
Qed.

Lemma rw_init_valid {S} `{!EqDecision S} (x: S)
  : sp_inv (Central false 0 x).
Proof.
  unfold sp_inv, rwlock_sp_inv, Central, free_count. split; trivial.
  - intuition; discriminate.
Qed.

Lemma rw_mov_exc_begin {S} `{!EqDecision S} rc x
  : storage_protocol_update_ii (B := BaseOpt S) (Central false rc x) (Central true rc x ⋅ ExcPending).
Proof.
  unfold storage_protocol_update_ii.
  unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp in *. intros p H.
  split.
    + unfold Central, ExcPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
    + unfold Central, ExcPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_exc_acquire {S} `{!EqDecision S} (exc: bool) (x: S)
  : storage_protocol_withdraw_ii
    (Central exc 0 x ⋅ ExcPending)
    (Central exc 0 x ⋅ ExcGuard)
    (base_storage_opt.Full x).
Proof.
  unfold storage_protocol_withdraw_ii.
  intro p. intro H. split.
  - unfold sp_inv, rwlock_sp_inv, "⋅", rw_op, Central, ExcGuard, ExcPending in *. destruct p.
      unfold "⋅", exc_op, free_op in *.
      + destruct e, e0, e1, a; unfold sp_inv, rwlock_sp_inv in *; intuition; try destruct exc; try destruct u; intuition; unfold free_count in *; try lia; intuition; try discriminate.
  - unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold sp_inv, rwlock_sp_inv in H; destruct a; try (destruct u); try (destruct exc); unfold ε, rwlock_unit in *; intuition; try (inversion H).
Qed.

Lemma rw_mov_exc_release {S} `{!EqDecision S} (exc: bool) (rc: Z) (x y: S)
  : storage_protocol_deposit_ii
    (Central exc rc y ⋅ ExcGuard)
    (Central false rc x)
    (Full x).
Proof.
  unfold storage_protocol_deposit_ii. intro p. intro H. split.
  - unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp, "⋅", rw_op, Central, ExcGuard, ExcPending in *. destruct p.
      unfold "⋅", exc_op, free_op in *. 
      destruct e, e0, e1, a; unfold sp_inv, rwlock_sp_inv; intuition; try destruct exc; try destruct u; try discriminate; intuition.
  - unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold sp_inv, rwlock_sp_inv in H; destruct a; try (destruct u); try (destruct exc); unfold ε, rwlock_unit in *; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_begin {S} `{!EqDecision S} (exc: bool) (rc: Z) (x: S)
  : storage_protocol_update_ii (B := BaseOpt S)
    (Central exc rc x)
    (Central exc (rc + 1) x ⋅ ShPending).
Proof.
  unfold storage_protocol_update. intros p H. unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp in *.
  split.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a; try contradiction; try destruct exc; intuition; try lia.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_acquire {S} `{!EqDecision S} (rc: Z) (x: S)
  : storage_protocol_update_ii (B := BaseOpt S)
    (Central false rc x ⋅ ShPending)
    (Central false rc x ⋅ ShGuard x).
Proof.
  unfold storage_protocol_update_ii. intros p H. unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp in *.
  split.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a; try contradiction; intuition; try lia; try discriminate.
        case_decide; intuition; try lia; try discriminate.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_release {S} `{!EqDecision S} (exc: bool) (rc: Z) (x y: S)
  : storage_protocol_update_ii (B := BaseOpt S)
    (Central exc rc x ⋅ ShGuard y)
    (Central exc (rc - 1) x).
Proof.
  unfold storage_protocol_update. intros p H. unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp in *.
  split.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a, exc; try contradiction; try case_decide; intuition; try lia; try discriminate; try subst x; trivial.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_retry {S} `{!EqDecision S} (exc: bool) (rc: Z) (x: S)
  : storage_protocol_update_ii (B := BaseOpt S)
    (Central exc rc x ⋅ ShPending)
    (Central exc (rc - 1) x).
Proof.
  unfold storage_protocol_update_ii. intros p H. unfold sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp in *.
  split.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a, exc; try contradiction; try case_decide; intuition; try lia.
    + unfold sp_inv, rwlock_sp_inv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_borrow {S} `{!EqDecision S} (x: S)
  : storage_protocol_guards_ii (ShGuard x) (Full x).
Proof.
  unfold storage_protocol_guards_ii. intros p H. unfold "≼". exists ε. rewrite base_opt_unit_right_id.
  unfold ShGuard, "⋅", rw_op, sp_inv, rwlock_sp_inv, sp_interp, rwlock_interp  in *. destruct p.
  unfold "⋅", exc_op, free_op in *. unfold sp_inv, rwlock_sp_inv in H. destruct e, e0, e1, a; try contradiction;
      try (case_decide); try contradiction; try (destruct p); try (destruct p);
      try intuition; try (destruct u); try contradiction; unfold free_count in *; try lia;
      intuition; try discriminate; destruct b; intuition; intuition;
      try discriminate; try (subst x; trivial); try (subst s; trivial).
      - destruct u0. intuition.
      - destruct u0. intuition.
Qed.

Global Instance free_eqdec {S} `{!EqDecision S} : EqDecision (AgN S).
Proof. solve_decision. Qed.

Global Instance exc_eqdec {S} `{!EqDecision S} : EqDecision (Exc S).
Proof. solve_decision. Qed.

Global Instance rwlock_eqdec {S} `{!EqDecision S} : EqDecision (RwLock S).
Proof. solve_decision. Qed.

Global Instance rwlock_equiv {S} `{EqDecision S} : Equiv (RwLock S) := λ a b , a = b.

Global Instance rwlock_pcore {S} `{EqDecision S} : PCore (RwLock S) := λ a , None.
Global Instance rwlock_valid {S} `{EqDecision S} : Valid (RwLock S) := λ a , True.

Lemma rwlock_valid_interp {S} `{EqDecision S} (p: RwLock S) : ✓ sp_interp p.
Proof. destruct p. unfold "✓", base_opt_valid. unfold sp_interp, rwlock_interp.
    destruct e; trivial. destruct p; trivial. destruct e1; trivial;
    destruct p; trivial.
Qed.

Definition rwlock_ra_mixin S {eqdec: EqDecision S} : RAMixin (@RwLock S eqdec).
Proof. split.
  - typeclasses eauto.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - typeclasses eauto.
  - unfold Assoc. intros. apply rw_op_assoc.
  - unfold Comm. intros. apply rw_op_comm.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - unfold pcore, base_opt_pcore. intros. discriminate.
  - trivial.
Qed.

Global Instance rwlock_storage_mixin_ii S {eqdec: EqDecision S} :
    StorageMixinII (RwLock S) (BaseOpt S).
Proof. split.
  - apply rwlock_ra_mixin.
  - apply base_opt_ra_mixin.
  - unfold LeftId. unfold "⋅". apply rw_unit_dot_left.
  - unfold LeftId. apply base_opt_unit_left_id.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros. apply rwlock_valid_interp.
Qed.

Class rwlock_logicG {S: Type} {eqdec: EqDecision S} Σ :=
    {
      #[local] rwlock_sp_inG ::
        sp_logicG (storage_mixin_from_ii (rwlock_storage_mixin_ii S)) Σ
    }.

Definition rwlock_logicΣ {S: Type} {eqdec: EqDecision S} : gFunctors := #[
  sp_logicΣ (storage_mixin_from_ii (rwlock_storage_mixin_ii S))
].

Global Instance subG_rwlock_logicΣ {S: Type} {eqdec: EqDecision S} {Σ} :
    subG (@rwlock_logicΣ S eqdec) Σ → @rwlock_logicG S eqdec Σ.
Proof. solve_inG. Qed.
(* end hide *)

Section RwlockLogic.

Context {S: Type}.
Context {eqdec: EqDecision S}.

Context {Σ: gFunctors}.
Context `{@rwlock_logicG S _ Σ}.
Context `{!invGS_gen hlc Σ}.

Definition fields γ (e: bool) (r: Z) (x: S) : iProp Σ
    := sp_own (sp_i := rwlock_sp_inG) γ (Central e r x).
Definition exc_pending γ : iProp Σ := sp_own (sp_i := rwlock_sp_inG) γ ExcPending.
Definition exc_guard γ : iProp Σ := sp_own (sp_i := rwlock_sp_inG) γ ExcGuard.
Definition sh_pending γ : iProp Σ := sp_own (sp_i := rwlock_sp_inG) γ ShPending.
Definition sh_guard γ m : iProp Σ := sp_own (sp_i := rwlock_sp_inG) γ (ShGuard m).

Definition rw_lock_inst (γ: gname) (f: S -> iProp Σ) : iProp Σ :=
  sp_sto (sp_i := rwlock_sp_inG) γ (base_opt_prop_map f).

(* Rw-Init *)

Lemma rw_new (x: S) (f: S -> iProp Σ) E
  : f x ={E}=∗ ∃ γ , rw_lock_inst γ f ∗ fields γ false 0 x.
Proof. 
  iIntros "fx".
  iMod (sp_alloc (Central false 0 x) (Full x) (base_opt_prop_map f) E with "[fx]") as "x".
  { split; trivial. apply rw_init_valid. }
  { apply wf_prop_base_base_opt. }
  {
    unfold sp_interp, rwlock_interp, Central, base_opt_prop_map. iFrame.
  }
  iDestruct "x" as (γ) "x". iModIntro. iExists γ.
  unfold rw_lock_inst, fields. iFrame.
Qed.

Lemma rw_new_ns (x: S) (f: S -> iProp Σ) E (N: namespace)
  : f x ={E}=∗ ∃ γ , ⌜ γ ∈ (↑N : coPset) ⌝ ∗ rw_lock_inst γ f ∗ fields γ false 0 x.
Proof. 
  iIntros "fx".
  iMod (sp_alloc_ns (Central false 0 x) (Full x) (base_opt_prop_map f) E N with "[fx]") as "x".
  { split; trivial. apply rw_init_valid. }
  { apply wf_prop_base_base_opt. }
  {
    unfold sp_interp, rwlock_interp, Central, base_opt_prop_map. iFrame.
  }
  iDestruct "x" as (γ) "[%gn x]". iModIntro. iExists γ.
  iSplitL "". { iPureIntro. trivial. }
  unfold rw_lock_inst, fields. iFrame.
Qed.

(* Rw-Exc-Begin *)

Lemma rw_exc_begin γ f rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    fields γ false rc x ={ E }=∗ fields γ true rc x ∗ exc_pending γ.
Proof.
  unfold fields, exc_pending.
  rewrite <- sp_own_op.
  apply sp_update'; trivial. rewrite eq_storage_protocol_update_ii.
  apply rw_mov_exc_begin.
Qed.

(* Rw-Exc-Acquire *)

Lemma rw_exc_acquire γ f exc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    fields γ exc 0 x ∗ exc_pending γ
      ={ E }=∗ 
    fields γ exc 0 x ∗ exc_guard γ ∗ ▷ f x.
Proof.
  unfold fields, exc_pending, exc_guard, rw_lock_inst.
  rewrite <- sp_own_op.
  rewrite <- bi.sep_assoc'.
  rewrite <- sp_own_op.
  replace (f x) with (base_opt_prop_map f (Full x)) by trivial.
  apply sp_withdraw'; trivial. rewrite eq_storage_protocol_withdraw_ii.
  apply rw_mov_exc_acquire.
Qed.

(* Rw-Exc-Release *)
  
Lemma rw_exc_release γ f exc rc (x y: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    (fields γ exc rc y ∗ exc_guard γ ∗ (▷ f x))
      ={ E }=∗
    fields γ false rc x.
Proof.
  unfold fields, exc_pending, exc_guard, rw_lock_inst.
  rewrite bi.sep_assoc.
  rewrite <- sp_own_op.
  replace (f x) with (base_opt_prop_map f (Full x)) by trivial.
  apply sp_deposit'; trivial. rewrite eq_storage_protocol_deposit_ii.
  apply rw_mov_exc_release.
Qed.

(* Rw-Shared-Begin *)

Lemma rw_shared_begin γ f exc rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
      fields γ exc rc x
      ={ E }=∗
      fields γ exc (rc+1) x ∗ sh_pending γ.
Proof.
  unfold fields, sh_pending.
  rewrite <- sp_own_op.
  apply sp_update'; trivial. rewrite eq_storage_protocol_update_ii.
  apply rw_mov_shared_begin.
Qed.

(* Rw-Shared-Acquire *)
  
Lemma rw_shared_acquire γ f rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
      fields γ false rc x ∗ sh_pending γ
      ={ E }=∗
      fields γ false rc x ∗ sh_guard γ x.
Proof.
  unfold fields, sh_guard, sh_pending.
  rewrite <- sp_own_op.
  rewrite <- sp_own_op.
  apply sp_update'; trivial. rewrite eq_storage_protocol_update_ii.
  apply rw_mov_shared_acquire.
Qed.

(* Rw-Shared-Release *)
  
Lemma rw_shared_release γ f exc rc (x y: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    fields γ exc rc x ∗ sh_guard γ y ={ E }=∗ fields γ exc (rc-1) x.
Proof.
  unfold fields, sh_guard, sh_pending.
  rewrite <- sp_own_op.
  apply sp_update'; trivial. rewrite eq_storage_protocol_update_ii.
  apply rw_mov_shared_release.
Qed.

(* Rw-Shared-Retry *)

Lemma rw_shared_retry γ f exc rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    fields γ exc rc x ∗ sh_pending γ ={ E }=∗ fields γ exc (rc-1) x.
Proof.
  unfold fields, sh_guard, sh_pending.
  rewrite <- sp_own_op.
  apply sp_update'; trivial. rewrite eq_storage_protocol_update_ii.
  apply rw_mov_shared_retry.
Qed.

(* Rw-Shared-Guard *)

Lemma rw_borrow_back γ f (x: S)
  : rw_lock_inst γ f ⊢
    sh_guard γ x &&{ {[ γ ]} }&&> ▷ f x.
Proof.
  unfold sh_guard.
  replace (f x) with (base_opt_prop_map f (Full x)) by trivial.
  apply sp_guard.
  - rewrite eq_storage_protocol_guards_ii. apply rw_mov_shared_borrow.
  - set_solver.
Qed.

End RwlockLogic.
