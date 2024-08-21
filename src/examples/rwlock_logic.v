Require Import guarding.guard.
Require Import guarding.storage_protocol.base_storage_opt.
Require Import guarding.storage_protocol.protocol.
Require Import guarding.storage_protocol.inved.

Require Import stdpp.base.
From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.
From iris.base_logic.lib Require Export invariants.

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
  
Instance rwlock_pinv {S} `{!EqDecision S} : PInv (RwLock S) :=
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

Global Instance rwlock_interp (S: Type) `{!EqDecision S} : Interp (RwLock S) (BaseOpt S) :=
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
  : pinv (Central false 0 x).
Proof.
  unfold pinv, rwlock_pinv, Central, free_count. split; trivial.
  - intuition; discriminate.
Qed.

Arguments storage_protocol_update B%type_scope {H} {P}%type_scope {H6 H7 H10} _ _.

Lemma rw_mov_exc_begin {S} `{!EqDecision S} rc x
  : storage_protocol_update (BaseOpt S) (Central false rc x) (Central true rc x ⋅ ExcPending).
Proof.
  unfold storage_protocol_update. unfold pinv, rwlock_pinv, interp, rwlock_interp in *. intros p H.
  split.
    + unfold Central, ExcPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
    + unfold Central, ExcPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_exc_acquire {S} `{!EqDecision S} (exc: bool) (x: S)
  : storage_protocol_withdraw
    (Central exc 0 x ⋅ ExcPending)
    (Central exc 0 x ⋅ ExcGuard)
    (base_storage_opt.Full x).
Proof.
  unfold storage_protocol_withdraw. intro p. intro H. split.
  - unfold pinv, rwlock_pinv, "⋅", rw_op, Central, ExcGuard, ExcPending in *. destruct p.
      unfold "⋅", exc_op, free_op in *.
      + destruct e, e0, e1, a; unfold pinv, rwlock_pinv in *; intuition; try destruct exc; try destruct u; intuition; unfold free_count in *; try lia; intuition; try discriminate.
  - unfold pinv, rwlock_pinv, interp, rwlock_interp in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold pinv, rwlock_pinv in H; destruct a; try (destruct u); try (destruct exc); unfold ε, rwlock_unit in *; intuition; try (inversion H).
Qed.

Lemma rw_mov_exc_release {S} `{!EqDecision S} (exc: bool) (rc: Z) (x y: S)
  : storage_protocol_deposit
    (Central exc rc y ⋅ ExcGuard)
    (Central false rc x)
    (Full x).
Proof.
  unfold storage_protocol_deposit. intro p. intro H. split.
  - unfold pinv, rwlock_pinv, interp, rwlock_interp, "⋅", rw_op, Central, ExcGuard, ExcPending in *. destruct p.
      unfold "⋅", exc_op, free_op in *. 
      destruct e, e0, e1, a; unfold pinv, rwlock_pinv; intuition; try destruct exc; try destruct u; try discriminate; intuition.
  - unfold pinv, rwlock_pinv, interp, rwlock_interp in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold pinv, rwlock_pinv in H; destruct a; try (destruct u); try (destruct exc); unfold ε, rwlock_unit in *; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_begin {S} `{!EqDecision S} (exc: bool) (rc: Z) (x: S)
  : storage_protocol_update (BaseOpt S)
    (Central exc rc x)
    (Central exc (rc + 1) x ⋅ ShPending).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a; try contradiction; try destruct exc; intuition; try lia.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_acquire {S} `{!EqDecision S} (rc: Z) (x: S)
  : storage_protocol_update (BaseOpt S)
    (Central false rc x ⋅ ShPending)
    (Central false rc x ⋅ ShGuard x).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a; try contradiction; intuition; try lia; try discriminate.
        case_decide; intuition; try lia; try discriminate.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_release {S} `{!EqDecision S} (exc: bool) (rc: Z) (x y: S)
  : storage_protocol_update (BaseOpt S)
    (Central exc rc x ⋅ ShGuard y)
    (Central exc (rc - 1) x).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a, exc; try contradiction; try case_decide; intuition; try lia; try discriminate; try subst x; trivial.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_retry {S} `{!EqDecision S} (exc: bool) (rc: Z) (x: S)
  : storage_protocol_update (BaseOpt S)
    (Central exc rc x ⋅ ShPending)
    (Central exc (rc - 1) x).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, a, exc; try contradiction; try case_decide; intuition; try lia.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, a; try contradiction; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_borrow {S} `{!EqDecision S} (x: S)
  : storage_protocol_guards (ShGuard x) (Full x).
Proof.
  unfold storage_protocol_guards. intros p H. unfold "≼". exists ε. rewrite base_opt_unit_right_id.
  unfold ShGuard, "⋅", rw_op, pinv, rwlock_pinv, interp, rwlock_interp  in *. destruct p.
  unfold "⋅", exc_op, free_op in *. unfold pinv, rwlock_pinv in H. destruct e, e0, e1, a; try contradiction;
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

Lemma rwlock_valid_interp {S} `{EqDecision S} (p: RwLock S) : ✓ interp p.
Proof. destruct p. unfold "✓", base_opt_valid. unfold interp, rwlock_interp.
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

Definition rwlock_protocol_mixin S {eqdec: EqDecision S} : ProtocolMixin (RwLock S).
Proof. split.
  - apply rwlock_ra_mixin.
  - unfold LeftId. unfold "⋅". apply rw_unit_dot_left.
  - intros. unfold "✓", rwlock_valid. trivial.
  - typeclasses eauto.
Qed.

Definition rwlock_storage_mixin S {eqdec: EqDecision S} : StorageMixin (RwLock S) (BaseOpt S).
Proof. split.
  - apply rwlock_protocol_mixin.
  - apply base_opt_ra_mixin.
  - unfold LeftId. apply base_opt_unit_left_id.
  - typeclasses eauto.
  - intros. apply rwlock_valid_interp.
Qed.

Class rwlock_logicG {S: Type} {eqdec: EqDecision S} Σ :=
    {
      #[global] rwlock_logic_inG :: inG Σ 
        (authUR (inved_protocolUR (protocol_mixin (RwLock S) (BaseOpt S) (rwlock_storage_mixin S))))
    }.

Definition rwlock_logicΣ {S: Type} {eqdec: EqDecision S} : gFunctors := #[
  GFunctor
        (authUR (inved_protocolUR (protocol_mixin (RwLock S) (BaseOpt S) (rwlock_storage_mixin S))))
].

Global Instance subG_rwlock_logicΣ {S: Type} {eqdec: EqDecision S} {Σ} :
    subG (@rwlock_logicΣ S eqdec) Σ → @rwlock_logicG S eqdec Σ.
Proof. solve_inG. Qed.

Section RwlockLogic.

Context {S: Type}.
Context {eqdec: EqDecision S}.

Context {Σ: gFunctors}.
Context `{@rwlock_logicG S _ Σ}.
Context `{!invGS Σ}.

Definition central γ (e: bool) (r: Z) (x: S) : iProp Σ := p_own γ (Central e r x).
Definition exc_pending γ : iProp Σ := p_own γ ExcPending.
Definition exc_guard γ : iProp Σ := p_own γ ExcGuard.
Definition sh_pending γ : iProp Σ := p_own γ ShPending.
Definition sh_guard γ m : iProp Σ := p_own γ (ShGuard m).

Definition rw_lock_inst (γ: gname) (f: S -> iProp Σ) : iProp Σ :=
    @maps
      (BaseOpt S) _ _ _ _ _ (RwLock S) _ _ _ _ _ _ _ _ _ Σ _ _
    γ (base_opt_prop_map f).

(* Rw-Init *)

Lemma rw_new (x: S) (f: S -> iProp Σ) E
  : f x ={E}=∗ ∃ γ , rw_lock_inst γ f ∗ central γ false 0 x.
Proof. 
  iIntros "fx".
  iMod (logic_init (Central false 0 x) (base_opt_prop_map f) E with "[fx]") as "x".
  { apply rw_init_valid. }
  { apply wf_prop_base_base_opt. }
  {
    unfold interp, rwlock_interp, Central, base_opt_prop_map. iFrame.
  }
  iDestruct "x" as (γ) "x". iModIntro. iExists γ.
  unfold rw_lock_inst, central. iFrame.
Qed.

Lemma rw_new_ns (x: S) (f: S -> iProp Σ) E (N: namespace)
  : f x ={E}=∗ ∃ γ , ⌜ γ ∈ (↑N : coPset) ⌝ ∗ rw_lock_inst γ f ∗ central γ false 0 x.
Proof. 
  iIntros "fx".
  iMod (logic_init_ns (Central false 0 x) (base_opt_prop_map f) E N with "[fx]") as "x".
  { apply rw_init_valid. }
  { apply wf_prop_base_base_opt. }
  {
    unfold interp, rwlock_interp, Central, base_opt_prop_map. iFrame.
  }
  iDestruct "x" as (γ) "[%gn x]". iModIntro. iExists γ.
  iSplitL "". { iPureIntro. trivial. }
  unfold rw_lock_inst, central. iFrame.
Qed.

(* Rw-Exc-Begin *)

Lemma rw_exc_begin γ f rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    central γ false rc x ={ E }=∗ central γ true rc x ∗ exc_pending γ.
Proof.
  unfold central, exc_pending.
  rewrite <- p_own_op.
  apply logic_update'; trivial.
  apply rw_mov_exc_begin.
Qed.

(* Rw-Exc-Acquire *)

Lemma rw_exc_acquire γ f exc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    central γ exc 0 x ∗ exc_pending γ
      ={ E }=∗ 
    central γ exc 0 x ∗ exc_guard γ ∗ ▷ f x.
Proof.
  unfold central, exc_pending, exc_guard, rw_lock_inst.
  rewrite <- p_own_op.
  rewrite <- bi.sep_assoc'.
  rewrite <- p_own_op.
  replace (f x) with (base_opt_prop_map f (Full x)) by trivial.
  apply logic_withdraw'; trivial.
  apply rw_mov_exc_acquire.
Qed.

(* Rw-Exc-Release *)
  
Lemma rw_exc_release γ f exc rc (x y: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    (central γ exc rc y ∗ exc_guard γ ∗ (▷ f x))
      ={ E }=∗
    central γ false rc x.
Proof.
  unfold central, exc_pending, exc_guard, rw_lock_inst.
  rewrite bi.sep_assoc.
  rewrite <- p_own_op.
  replace (f x) with (base_opt_prop_map f (Full x)) by trivial.
  apply logic_deposit'; trivial.
  apply rw_mov_exc_release.
Qed.

(* Rw-Shared-Begin *)

Lemma rw_shared_begin γ f exc rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
      central γ exc rc x
      ={ E }=∗
      central γ exc (rc+1) x ∗ sh_pending γ.
Proof.
  unfold central, sh_pending.
  rewrite <- p_own_op.
  apply logic_update'; trivial.
  apply rw_mov_shared_begin.
Qed.

(* Rw-Shared-Acquire *)
  
Lemma rw_shared_acquire γ f rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
      central γ false rc x ∗ sh_pending γ
      ={ E }=∗
      central γ false rc x ∗ sh_guard γ x.
Proof.
  unfold central, sh_guard, sh_pending.
  rewrite <- p_own_op.
  rewrite <- p_own_op.
  apply logic_update'; trivial.
  apply rw_mov_shared_acquire.
Qed.

(* Rw-Shared-Release *)
  
Lemma rw_shared_release γ f exc rc (x y: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    central γ exc rc x ∗ sh_guard γ y ={ E }=∗ central γ exc (rc-1) x.
Proof.
  unfold central, sh_guard, sh_pending.
  rewrite <- p_own_op.
  apply logic_update'; trivial.
  apply rw_mov_shared_release.
Qed.

(* Rw-Shared-Retry *)

Lemma rw_shared_retry γ f exc rc (x: S) E
  (in_e: γ ∈ E)
  : rw_lock_inst γ f ⊢
    central γ exc rc x ∗ sh_pending γ ={ E }=∗ central γ exc (rc-1) x.
Proof.
  unfold central, sh_guard, sh_pending.
  rewrite <- p_own_op.
  apply logic_update'; trivial.
  apply rw_mov_shared_retry.
Qed.

(* Rw-Shared-Guard *)

Lemma rw_borrow_back γ f (x: S)
  : rw_lock_inst γ f ⊢
    sh_guard γ x &&{ {[ γ ]} }&&> ▷ f x.
Proof.
  unfold sh_guard.
  replace (f x) with (base_opt_prop_map f (Full x)) by trivial.
  apply logic_guard.
  - apply rw_mov_shared_borrow.
  - set_solver.
Qed.

End RwlockLogic.


