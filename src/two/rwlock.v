Require Import Two.base_storage_opt.
Require Import Two.protocol.
Require Import Two.inved.

Require Import cpdt.CpdtTactics.
Require Import coq_tricks.Deex.

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

Inductive Free (S: Type) `{!EqDecision S} :=
  | Empty : Free S
  | Have : S -> nat -> Free S
  | Conflict : Free S
.
Arguments Empty {_}%type_scope {EqDecision0}.
Arguments Have {_}%type_scope {EqDecision0} _ _%nat_scope.
Arguments Conflict {_}%type_scope {EqDecision0}.

Instance free_op {S} `{!EqDecision S} : Op (Free S) := λ a b , match a, b with
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
  - crush.
  - crush.
Qed.

Instance free_op_assoc {S} `{!EqDecision S} : Assoc (=) (@free_op S EqDecision0).
Proof. unfold Assoc. intros. unfold free_op. destruct x, y, z; try case_decide; intuition.
  - case_decide; trivial. case_decide.
    + f_equal. lia.
    + crush.
  - case_decide; trivial. case_decide; trivial. crush.
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
  | Rwl : (Exc (bool * Z * S)) -> Exc () -> Exc () -> nat -> Free S -> RwLock S
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
  
Definition free_count {S} `{!EqDecision S} (m: Free S) : nat :=
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

(*
Definition rw_mov {S} `{!EqDecision S} `{!TPCM S} (a b : RwLock S) :=
  ∀ p, I_defined (a ⋅ p) -> I_defined (b ⋅ p) /\ I (a ⋅ p) = I (b ⋅ p).
  *)

Lemma rw_unit_dot (S: Type) `{!EqDecision S} (a : RwLock S) :
  rw_op a ε = a.
Proof.
  unfold ε, rwlock_unit. destruct a. unfold "⋅", rw_op. unfold "⋅", exc_op, free_op.
  f_equal; trivial.
  - destruct e; trivial.
  - destruct e0; trivial.
  - destruct e1; trivial.
  - lia.
  - destruct f; trivial.
Qed.

Lemma rw_unit_dot_left (S: Type) `{!EqDecision S} (a : RwLock S) :
  rw_op ε a = a.
Proof.
  destruct a; trivial.
Qed.

Lemma rw_init_valid {S} `{!EqDecision S} `{!TPCM S} (x: S)
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
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
    + unfold Central, ExcPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
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
      + destruct e, e0, e1, f; unfold pinv, rwlock_pinv in *; intuition; try destruct exc; try destruct u; intuition; unfold free_count in *; try lia; intuition; try discriminate.
  - unfold pinv, rwlock_pinv, interp, rwlock_interp in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold pinv, rwlock_pinv in H; destruct f; try (destruct u); try (destruct exc); unfold ε, rwlock_unit in *; intuition; try (inversion H).
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
      destruct e, e0, e1, f; unfold pinv, rwlock_pinv; intuition; try destruct exc; try destruct u; crush.
  - unfold pinv, rwlock_pinv, interp, rwlock_interp in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold pinv, rwlock_pinv in H; destruct f; try (destruct u); try (destruct exc); unfold ε, rwlock_unit in *; intuition; try discriminate.
Qed.

Lemma rw_mov_shared_begin {S} `{!EqDecision S} (exc: bool) (rc: Z) (x: S)
  : storage_protocol_update (BaseOpt S)
    (Central exc rc x)
    (Central exc (rc + 1) x ⋅ ShPending).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f; try contradiction; try destruct exc; intuition; try lia.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Lemma rw_mov_shared_acquire {S} `{!EqDecision S} (rc: Z) (x: S)
  : storage_protocol_update (BaseOpt S)
    (Central false rc x ⋅ ShPending)
    (Central false rc x ⋅ ShGuard x).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f; try contradiction; intuition; try lia; try discriminate.
        case_decide; intuition; try lia; try discriminate.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Lemma rw_mov_shared_release {S} `{!EqDecision S} (exc: bool) (rc: Z) (x y: S)
  : storage_protocol_update (BaseOpt S)
    (Central exc rc x ⋅ ShGuard y)
    (Central exc (rc - 1) x).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f, exc; try contradiction; try case_decide; intuition; try lia; try discriminate; try subst x; trivial.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Lemma rw_mov_shared_retry {S} `{!EqDecision S} (exc: bool) (rc: Z) (x: S)
  : storage_protocol_update (BaseOpt S)
    (Central exc rc x ⋅ ShPending)
    (Central exc (rc - 1) x).
Proof.
  unfold storage_protocol_update. intros p H. unfold pinv, rwlock_pinv, interp, rwlock_interp in *.
  split.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f, exc; try contradiction; try case_decide; intuition; try lia.
    + unfold pinv, rwlock_pinv in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Lemma rw_mov_shared_borrow {S} `{!EqDecision S} (x: S)
  : storage_protocol_guards (ShGuard x) (Full x).
Proof.
  unfold storage_protocol_guards. intros p H. unfold "≼". exists ε. rewrite base_opt_unit_right_id.
  unfold ShGuard, "⋅", rw_op, pinv, rwlock_pinv, interp, rwlock_interp  in *. destruct p.
  unfold "⋅", exc_op, free_op in *. unfold pinv, rwlock_pinv in H. destruct e, e0, e1, f; try contradiction;
      try (case_decide); try contradiction; try (destruct p); try (destruct p);
      try intuition; try (destruct u); try contradiction; unfold free_count in *; try lia;
      intuition; try discriminate; destruct b; intuition; intuition;
      try discriminate; try (subst x; trivial); try (subst s; trivial).
      - destruct u0. intuition.
      - destruct u0. intuition.
Qed.

Global Instance free_eqdec {S} `{!EqDecision S} : EqDecision (Free S).
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

Section RwlockLogic.

Context {𝜇: BurrowCtx}.
Context `{hG : @gen_burrowGS 𝜇 Σ}.

Context {S} `{!EqDecision S} `{!TPCM S}.
Context `{m_hastpcm: !HasTPCM 𝜇 S}.
Context `{rw_hastpcm: !HasTPCM 𝜇 (RwLock S)}.
Context `{!HasRef 𝜇 rw_hastpcm m_hastpcm (rwlock_ref S)}.

Definition rwloc 𝛼 𝛾 := extend_loc 𝛼 (rwlock_ref S) 𝛾.

Lemma rw_new 𝛾 (x: S)
  : L 𝛾 x ==∗ ∃ 𝛼 , L (rwloc 𝛼 𝛾) (Central false 0 x).
Proof. 
  apply InitializeExt.
  - unfold rel_defined, rwlock_ref.
    unfold I_defined. right. apply rw_init_valid.
  - trivial.
Qed.

Lemma rw_exc_begin 𝛾 rc (x: S)
  : L 𝛾 (Central false rc x) ==∗ L 𝛾 (Central true rc x) ∗ L 𝛾 ExcPending.
Proof.
  rewrite <- L_op.
  apply FrameUpdate.
  apply rw_mov_exc_begin.
Qed.

Lemma rw_exc_acquire 𝛼 𝛾 exc (x: S)
   : L (rwloc 𝛼 𝛾) (Central exc 0 x)
  -∗ L (rwloc 𝛼 𝛾) ExcPending
 ==∗ L (rwloc 𝛼 𝛾) (Central exc 0 x)
   ∗ L (rwloc 𝛼 𝛾) ExcGuard
   ∗ L 𝛾 x.
Proof.
  iIntros "A B".
  iDestruct (L_join with "A B") as "T".
  iMod (L_unit S 𝛾) as "U".
  iMod (FrameExchange _ _ _ _ x _ (dot (Central exc 0 x) ExcGuard) with "T U") as "T".
  - apply rw_mov_exc_acquire.
  - rewrite L_op.
    iModIntro.
    iDestruct "T" as "[[S R] U]".
    iFrame.
Qed.
  
Lemma rw_exc_release 𝛼 𝛾 exc rc (x y: S)
   : L (rwloc 𝛼 𝛾) (Central exc rc y)
  -∗ L (rwloc 𝛼 𝛾) ExcGuard
  -∗ L 𝛾 x
 ==∗ L (rwloc 𝛼 𝛾) (Central false rc x).
Proof.
  iIntros "a b c".
  iDestruct (L_join with "a b") as "a".
  iMod (FrameExchange _ _ _ _ (unit: S) _ (Central false rc x) with "a c") as "[a b]".
  - apply rw_mov_exc_release.
  - iModIntro. iFrame.
Qed.

Lemma rw_shared_begin 𝛾 exc rc (x: S)
  : L 𝛾 (Central exc rc x) ==∗ L 𝛾 (Central exc (rc+1) x) ∗ L 𝛾 ShPending.
Proof.
  rewrite <- L_op.
  apply FrameUpdate.
  apply rw_mov_shared_begin.
Qed.
  
Lemma rw_shared_acquire 𝛾 rc (x: S)
  : L 𝛾 (Central false rc x) -∗ L 𝛾 ShPending ==∗ L 𝛾 (Central false rc x) ∗ L 𝛾 (ShGuard x).
Proof.
  iIntros "A B".
  iDestruct (L_join with "A B") as "A".
  iMod (FrameUpdate _ _ (dot (Central false rc x) (ShGuard x)) with "A") as "A".
  - apply rw_mov_shared_acquire.
  - rewrite L_op. iModIntro. iFrame.
Qed.
  
Lemma rw_shared_release 𝛾 exc rc (x y: S)
  : L 𝛾 (Central exc rc x) -∗ L 𝛾 (ShGuard y) ==∗ L 𝛾 (Central exc (rc-1) x).
Proof.
  iIntros "A B".
  iDestruct (L_join with "A B") as "A".
  iMod (FrameUpdate _ _ ((Central exc (rc-1) x)) with "A") as "A".
  - apply rw_mov_shared_release.
  - iModIntro. iFrame.
Qed.
  
Lemma rw_shared_retry 𝛾 exc rc (x: S)
  : L 𝛾 (Central exc rc x) -∗ L 𝛾 ShPending ==∗ L 𝛾 (Central exc (rc-1) x).
Proof.
  iIntros "A B".
  iDestruct (L_join with "A B") as "A".
  iMod (FrameUpdate _ _ ((Central exc (rc-1) x)) with "A") as "A".
  - apply rw_mov_shared_retry.
  - iModIntro. iFrame.
Qed.
  
Lemma rw_borrow_back 𝛼 𝛾 (x: S) 𝜅
  : B 𝜅 (rwloc 𝛼 𝛾) (ShGuard x) ⊢ B 𝜅 𝛾 x.
Proof.
  apply BorrowBack. apply rw_mov_shared_borrow. Qed.

End RwlockLogic.


