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

Lemma rw_init_valid {S} `{!EqDecision S} `{!TPCM S} (x: S)
  : pinv (Central false 0 x).
Proof.
  unfold pinv, rwlock_pinv, Central, free_count. split; trivial.
  - intuition; discriminate.
Qed.

Lemma rw_mov_exc_begin {S} `{!EqDecision S} `{!TPCM S} rc x
  : storage_protocol_update (Central false rc x) (Central true rc x ⋅ ExcPending).
Proof.
  unfold rw_mov. intros. unfold I_defined, I in *.
  destruct H.
  - exfalso. unfold "⋅", rw_op, rw_unit, Central in H. destruct p. inversion H.
      unfold "⋅", exc_op in H1. destruct e; discriminate.
  - split.
    + right. unfold P in *. unfold Central, ExcPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
    + unfold P in *. unfold Central, ExcPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Definition rw_exchange_cond {S} `{!EqDecision S} `{!TPCM S}
    (f: RwLock S) (m: S) (f': RwLock S) (m': S) :=
  ∀ p ,
    I_defined (f ⋅ p) -> I_defined (f' ⋅ p) /\ mov (dot m (I (f ⋅ p))) (dot m' (I (f' ⋅ p))).

Lemma rw_mov_exc_acquire {S} `{!EqDecision S} `{!TPCM S} (exc: bool) (x: S)
  : rw_exchange_cond
    (Central exc 0 x ⋅ ExcPending)
    (unit: S)
    (Central exc 0 x ⋅ ExcGuard)
    x.
Proof.
  unfold rw_exchange_cond. intro. intro. split.
  - unfold I_defined, "⋅", rw_op, Central, ExcGuard, ExcPending in *. destruct p.
      unfold "⋅", exc_op, free_op in *.  right. destruct H.
      + exfalso. unfold rw_unit in H. destruct e, e0, e1, f; inversion H.
      + destruct e, e0, e1, f; unfold P in *; intuition; try destruct exc; try destruct u; intuition; unfold free_count in *; try lia; intuition; try discriminate.
  - rewrite unit_dot_left. unfold I, I_defined in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold P in H; destruct f; try (destruct u); try (destruct exc); unfold rw_unit in *; intuition; try (inversion H0).
Qed.

Lemma rw_mov_exc_release {S} `{!EqDecision S} `{!TPCM S} (exc: bool) (rc: Z) (x y: S)
  : rw_exchange_cond
    (Central exc rc y ⋅ ExcGuard)
    x
    (Central false rc x)
    (unit: S).
Proof.
  unfold rw_exchange_cond. intro. intro. split.
  - unfold I_defined, "⋅", rw_op, Central, ExcGuard, ExcPending in *. destruct p.
      unfold "⋅", exc_op, free_op in *.  right. destruct H.
      + exfalso. unfold rw_unit in H. destruct e, e0, e1, f; inversion H.
      + destruct e, e0, e1, f; unfold P; intuition; try destruct exc; try destruct u; crush.
  - rewrite unit_dot_left. unfold I, I_defined in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold P in H; destruct f; try (destruct u); try (destruct exc); unfold rw_unit in *; intuition; try (inversion H0).
Qed.

Lemma rw_mov_shared_begin {S} `{!EqDecision S} `{!TPCM S} (exc: bool) (rc: Z) (x: S)
  : rw_mov
    (Central exc rc x)
    (Central exc (rc + 1) x ⋅ ShPending).
Proof.
  unfold rw_mov. intros. unfold I_defined, I in *.
  destruct H.
  - exfalso. unfold "⋅", rw_op, rw_unit, Central in H. destruct p. inversion H.
      unfold "⋅", exc_op in H1. destruct e; discriminate.
  - split.
    + right. unfold P in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f; try contradiction; try destruct exc; intuition; try lia.
    + unfold P in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Lemma rw_mov_shared_acquire {S} `{!EqDecision S} `{!TPCM S} (rc: Z) (x: S)
  : rw_mov
    (Central false rc x ⋅ ShPending)
    (Central false rc x ⋅ ShGuard x).
Proof.
  unfold rw_mov. intros. unfold I_defined, I in *.
  destruct H.
  - exfalso. unfold "⋅", rw_op, rw_unit, Central in H. destruct p. inversion H.
  - split.
    + right. unfold P in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f; try contradiction; intuition; try lia; try discriminate.
        case_decide; intuition; try lia; try discriminate.
    + unfold P in *. unfold Central, ShPending, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Lemma rw_mov_shared_release {S} `{!EqDecision S} `{!TPCM S} (exc: bool) (rc: Z) (x y: S)
  : rw_mov
    (Central exc rc x ⋅ ShGuard y)
    (Central exc (rc - 1) x).
Proof.
  unfold rw_mov. intros. unfold I_defined, I in *.
  destruct H.
  - exfalso. unfold "⋅", rw_op, rw_unit, Central in H. destruct p. inversion H.
      unfold "⋅", exc_op in H1. destruct e; discriminate.
  - split.
    + right. unfold P in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f, exc; try contradiction; try case_decide; intuition; try lia; try discriminate; try subst x; trivial.
    + unfold P in *. unfold Central, ShGuard in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Lemma rw_mov_shared_retry {S} `{!EqDecision S} `{!TPCM S} (exc: bool) (rc: Z) (x: S)
  : rw_mov
    (Central exc rc x ⋅ ShPending)
    (Central exc (rc - 1) x).
Proof.
  unfold rw_mov. intros. unfold I_defined, I in *.
  destruct H.
  - exfalso. unfold "⋅", rw_op, rw_unit, Central in H. destruct p. inversion H.
  - split.
    + right. unfold P in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op, free_count in *. destruct e, e0, e1, f, exc; try contradiction; try case_decide; intuition; try lia.
    + unfold P in *. unfold Central, ShPending in *. destruct p.
      unfold "⋅", rw_op in *. unfold "⋅", exc_op, free_op in *. destruct e, e0, e1, f; try contradiction; crush.
Qed.

Definition rw_borrow_back_cond {S} `{!EqDecision S} `{!TPCM S} (f: RwLock S) (m: S)
  := ∀ p ,
    I_defined (f ⋅ p) -> ∃ z , (dot m z) = I (f ⋅ p).

Lemma rw_mov_shared_borrow {S} `{!EqDecision S} `{!TPCM S} (x: S)
  : rw_borrow_back_cond (ShGuard x) x.
Proof.
  unfold rw_borrow_back_cond. intros. exists unit. rewrite unit_dot.
  unfold ShGuard, "⋅", rw_op, I, I_defined in *. destruct p. destruct H.
  - exfalso. unfold rw_unit in H. inversion H. unfold "⋅" in H5. unfold free_op in H5.
      destruct f; try discriminate. case_decide; try discriminate.
  - unfold "⋅", exc_op, free_op in *. unfold P in H. destruct e, e0, e1, f; try contradiction;
      try (case_decide); try contradiction; try (destruct p); try (destruct p);
      try intuition; try (destruct u); try contradiction; unfold free_count in *; try lia;
      intuition; try discriminate; destruct b; intuition; destruct u0; intuition;
      try discriminate.
Qed.

Global Instance free_eqdec {S} `{!EqDecision S} : EqDecision (Free S).
Proof. solve_decision. Qed.

Global Instance exc_eqdec {S} `{!EqDecision S} : EqDecision (Exc S).
Proof. solve_decision. Qed.

Global Instance rwlock_eqdec {S} `{!EqDecision S} : EqDecision (RwLock S).
Proof. solve_decision. Qed.

Lemma rw_valid_monotonic {S} `{!EqDecision S} `{!TPCM S}
  (f: RwLock S) (g: RwLock S) : V (f ⋅ g) -> V f.
Proof.
  unfold V. intro. deex. exists (g ⋅ z). unfold "⋅" in *. rewrite rw_op_assoc. trivial. Qed.
  
Lemma rw_unit_valid {S} `{!EqDecision S} `{!TPCM S}
  : V (rw_unit S).
Proof.
  unfold V. exists (Central false 0 (unit: S)).
    unfold "⋅".
    rewrite rw_op_comm.
    rewrite rw_unit_dot. unfold P, rw_unit, Central. unfold free_count. crush.
Qed.
  
Lemma rw_mov_reflex {S} `{!EqDecision S} `{!TPCM S}
  (f: RwLock S) : rw_mov f f.
Proof.
  unfold rw_mov. intros. split; trivial. Qed.
  
Lemma rw_mov_trans {S} `{!EqDecision S} `{!TPCM S}
  (f g h: RwLock S) : rw_mov f g -> rw_mov g h -> rw_mov f h.
Proof. unfold rw_mov. intuition.
  - have q := H p. have q0 := H0 p. intuition.
  - have q := H p. have q0 := H0 p. intuition.
    rewrite H4. trivial.
Qed.

Lemma left_is_unit {S} `{!EqDecision S} (a b: RwLock S)
  : rw_op a b = rw_unit S -> a = rw_unit S.
Proof.
  intros. unfold rw_op, rw_unit in *. destruct a, b. inversion H. f_equal.
  - unfold "⋅" in *. unfold exc_op in H1. destruct e; unfold exc_op in *; intuition.
      destruct e2; intuition; try discriminate.
  - unfold "⋅" in *. unfold exc_op in H2. destruct e; unfold exc_op in *; intuition;
      destruct e2; intuition; try discriminate; destruct e1; intuition; destruct e0; intuition;
      try discriminate; try subst e4; try subst e3; trivial; try destruct e3; trivial;
      try discriminate; try destruct e4; try discriminate.
  - unfold "⋅" in *. unfold exc_op in H3. destruct e1, e4; intuition; try discriminate.
  - lia.
  - unfold "⋅" in *. unfold free_op in *. destruct f; try (symmetry; trivial); destruct f0;
      trivial; try case_decide; try discriminate.
Qed.
  
Lemma rw_mov_monotonic {S} `{!EqDecision S} `{!TPCM S} : forall x y z ,
      rw_mov x y -> V (rw_op x z) -> V (rw_op y z) /\ rw_mov (rw_op x z) (rw_op y z).
Proof.
  intros. assert (V (rw_op y z)) as Vrw.
  - have h : Decision (rw_op y z = rw_unit S) by solve_decision. destruct h.
    + rewrite e. apply rw_unit_valid.
    + unfold V in *.
      deex. unfold rw_mov in H. have h := H (rw_op z z0).
      unfold I_defined in h. unfold "⋅" in *.  intuition.
      rewrite rw_op_assoc in H2.
      have h := H2 H0. destruct_ands. destruct H3.
      * rewrite rw_op_assoc in H3.
        have liu := left_is_unit _ _ H3. contradiction.
      * exists z0. rewrite rw_op_assoc in H3. trivial.
  - split; trivial. unfold rw_mov. intros. unfold rw_mov in H.
    unfold "⋅" in *. rewrite <- rw_op_assoc. rewrite <- rw_op_assoc.
      apply H.
      rewrite <- rw_op_assoc in H1. trivial.
Qed.

Global Instance rwlock_tpcm {S} `{!EqDecision S} `{!TPCM S} : TPCM (RwLock S) := {
  m_valid := V ;
  dot := rw_op ;
  mov := rw_mov ;
  unit := rw_unit S ;
  valid_monotonic := rw_valid_monotonic ;
  unit_valid := rw_unit_valid ;
  unit_dot := rw_unit_dot S ;
  tpcm_comm := rw_op_comm ;
  tpcm_assoc := rw_op_assoc ;
  reflex := rw_mov_reflex ;
  trans := rw_mov_trans ;
  mov_monotonic := rw_mov_monotonic ;
}.

Lemma rwlock_I_valid_left
    {S} `{!EqDecision S} `{!TPCM S}
  : ∀ r : RwLock S, I_defined r → m_valid r.
Proof. intro.
  unfold m_valid, rwlock_tpcm.
  unfold I_defined. intro. destruct H.
  - rewrite H. apply rw_unit_valid.
  - unfold V. exists (rw_unit S). unfold "⋅". rewrite rw_unit_dot. trivial.
Qed.

Lemma rwlock_I_defined_unit
    {S} `{!EqDecision S} `{!TPCM S}
   : I_defined (unit: RwLock S).
Proof.
  unfold I_defined. left. trivial.
Qed.
   
Lemma rwlock_I_unit
    {S} `{!EqDecision S} `{!TPCM S}
  : I unit = unit.
Proof.
  trivial.
Qed.

Lemma rwlock_I_mov_refines
    {S} `{!EqDecision S} `{!TPCM S}
  : ∀ b b' : RwLock S, mov b b' → I_defined b → I_defined b' ∧ mov (I b) (I b').
Proof.
  intros.
  unfold mov, rwlock_tpcm, rw_mov in H.
  have h := H (rw_unit S). unfold "⋅" in h.
  repeat (rewrite rw_unit_dot in h). intuition. rewrite H3. apply reflex.
Qed.

Definition rwlock_ref
    S `{!EqDecision S} `{!TPCM S}
    : Refinement (RwLock S) S :=
({|
  rel_defined := I_defined ;
  rel := I ;
  rel_valid_left := rwlock_I_valid_left ;
  rel_defined_unit := rwlock_I_defined_unit ;
  rel_unit := rwlock_I_unit ;
  mov_refines := rwlock_I_mov_refines ;
|}).

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


