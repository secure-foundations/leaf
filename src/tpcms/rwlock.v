Require Import Burrow.rollup.
Require Import Burrow.ra.
From iris.prelude Require Import options.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export base_logic.

Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.
Require Import Burrow.tpcms.

Inductive Free (M: Type) `{!EqDecision M} :=
  | Empty : Free M
  | Have : M -> nat -> Free M
  | Conflict : Free M
.
Arguments Empty {_}%type_scope {EqDecision0}.
Arguments Have {_}%type_scope {EqDecision0} _ _%nat_scope.
Arguments Conflict {_}%type_scope {EqDecision0}.

Instance free_op {M} `{!EqDecision M} : Op (Free M) := λ a b , match a, b with
  | Empty, y => y
  | Conflict, y => Conflict
  | Have m x, Empty => Have m x
  | Have m x, Have n y => if decide (m = n) then Have m (x + y + 1) else Conflict
  | Have _ _, Conflict => Conflict
  end
.

Instance free_op_comm {M} `{!EqDecision M} : Comm (=) (@free_op M EqDecision0).
Proof. unfold Comm. intros. unfold free_op. destruct x, y; trivial.
  repeat case_decide; trivial.
  - f_equal. + symmetry. trivial. + lia.
  - crush.
  - crush.
Qed.

Instance free_op_assoc {M} `{!EqDecision M} : Assoc (=) (@free_op M EqDecision0).
Proof. unfold Assoc. intros. unfold free_op. destruct x, y, z; try case_decide; intuition.
  - case_decide; trivial. case_decide.
    + f_equal. lia.
    + crush.
  - case_decide; trivial. case_decide; trivial. crush.
Qed.

Inductive Exc (M: Type) :=
  | Unknown : Exc M
  | Yes : M -> Exc M
  | Fail : Exc M
.
Arguments Unknown {_}%type_scope.
Arguments Yes {_}%type_scope _.
Arguments Fail {_}%type_scope.

Instance exc_op {M} : Op (Exc M) := λ a b , match a, b with
  | Unknown, y => y
  | Fail, y => Fail
  | Yes m, Unknown => Yes m
  | Yes _, _ => Fail
  end
.

Instance exc_op_comm {M} `{!EqDecision M} : Comm (=) (@exc_op M).
Proof. unfold Comm. intros. unfold exc_op. destruct x, y; trivial.
Qed.

Instance exc_op_assoc {M} `{!EqDecision M} : Assoc (=) (@exc_op M).
Proof. unfold Assoc. intros. unfold exc_op. destruct x, y, z; trivial.
Qed.

Inductive RwLock (M: Type) `{!EqDecision M} :=
  | Rwl : (Exc (bool * Z * M)) -> Exc () -> Exc () -> nat -> Free M -> RwLock M
.
Arguments Rwl {_}%type_scope {EqDecision0} _ _ _ _%nat_scope _.

Instance rw_op {M} `{!EqDecision M} : Op (RwLock M) := λ a b , match a, b with
  | Rwl c ep eg sp sg, Rwl c' ep' eg' sp' sg' =>
      Rwl (c ⋅ c') (ep ⋅ ep') (eg ⋅ eg') (sp + sp') (sg ⋅ sg')
  end
.

Instance rw_op_comm {M} `{!EqDecision M} : Comm (=) (@rw_op M EqDecision0).
Proof. unfold Comm. intros. unfold rw_op. destruct x, y.
  f_equal.
  - apply exc_op_comm.
  - apply exc_op_comm.
  - apply exc_op_comm.
  - lia.
  - apply free_op_comm.
Qed.

Instance rw_op_assoc {M} `{!EqDecision M} : Assoc (=) (@rw_op M EqDecision0).
Proof. unfold Assoc. intros. unfold rw_op. destruct x, y, z.
  f_equal.
  - apply exc_op_assoc.
  - apply exc_op_assoc.
  - apply exc_op_assoc.
  - lia.
  - apply free_op_assoc.
Qed.

Definition Central {M: Type} `{!EqDecision M} (e: bool) (r: Z) (x: M) : RwLock M :=
  Rwl (Yes (e, r, x)) Unknown Unknown 0 (Empty).
  
Definition ExcPending {M: Type} `{!EqDecision M}: RwLock M :=
  Rwl Unknown (Yes ()) Unknown 0 (Empty).
  
Definition ExcGuard {M: Type} `{!EqDecision M}: RwLock M :=
  Rwl Unknown Unknown (Yes ()) 0 (Empty).
  
Definition ShPending {M: Type} `{!EqDecision M}: RwLock M :=
  Rwl Unknown Unknown Unknown 1 (Empty).
  
Definition ShGuard {M: Type} `{!EqDecision M} (m: M) : RwLock M :=
  Rwl Unknown Unknown Unknown 0 (Have m 0).
  
Definition free_count {M} `{!EqDecision M} (m: Free M) : nat :=
  match m with
  | Empty => 0
  | Have _ n => n + 1
  | Conflict => 0
  end.
  
Definition P {M} `{!EqDecision M} (rw: RwLock M) :=
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

Definition V {M} `{!EqDecision M} (rw: RwLock M) :=
  ∃ z , P (rw ⋅ z).

Definition rw_unit (M: Type) `{!EqDecision M} : RwLock M :=
  Rwl Unknown Unknown Unknown 0 Empty.

Definition I_defined {M} `{!EqDecision M} (rw: RwLock M) :=
  rw = rw_unit M \/ P rw.

Definition I {M} `{!EqDecision M} `{!TPCM M} (rw: RwLock M) :=
  match rw with
  | Rwl (Yes (_,_,x)) _ Unknown _ _ => x
  | _ => unit
  end.

Definition rw_mov {M} `{!EqDecision M} `{!TPCM M} (a b : RwLock M) :=
  ∀ p, I_defined (a ⋅ p) -> I_defined (b ⋅ p) /\ I (a ⋅ p) = I (b ⋅ p).

Lemma rw_unit_dot (M: Type) `{!EqDecision M} (a : RwLock M) :
  rw_op a (rw_unit M) = a.
Proof.
  unfold rw_unit. destruct a. unfold "⋅", rw_op. unfold "⋅", exc_op, free_op.
  f_equal; trivial.
  - destruct e; trivial.
  - destruct e0; trivial.
  - destruct e1; trivial.
  - lia.
  - destruct f; trivial.
Qed.

Lemma rw_init_valid {M} `{!EqDecision M} `{!TPCM M} (x: M)
  : P (Central false 0 x).
Proof.
  unfold P, Central, free_count. split; trivial.
  - intuition; discriminate.
Qed.

Lemma rw_mov_exc_begin {M} `{!EqDecision M} `{!TPCM M} rc x
  : rw_mov (Central false rc x) (Central true rc x ⋅ ExcPending).
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

Definition rw_exchange_cond {M} `{!EqDecision M} `{!TPCM M}
    (f: RwLock M) (m: M) (f': RwLock M) (m': M) :=
  ∀ p ,
    I_defined (f ⋅ p) -> I_defined (f' ⋅ p) /\ mov (dot m (I (f ⋅ p))) (dot m' (I (f' ⋅ p))).

Lemma rw_mov_exc_acquire {M} `{!EqDecision M} `{!TPCM M} (exc: bool) (x: M)
  : rw_exchange_cond
    (Central exc 0 x ⋅ ExcPending)
    (unit: M)
    (Central exc 0 x ⋅ ExcGuard)
    x.
Proof.
  unfold rw_exchange_cond. intro. intro. split.
  - unfold I_defined, "⋅", rw_op, Central, ExcGuard, ExcPending in *. destruct p.
      unfold "⋅", exc_op, free_op in *.  right. destruct H.
      + exfalso. unfold rw_unit in H. destruct e, e0, e1, f; inversion H.
      + destruct e, e0, e1, f; unfold P; intuition; try destruct exc; try destruct u; intuition; crush.
  - rewrite unit_dot_left. unfold I, I_defined in *. unfold "⋅", Central, ExcPending, ExcGuard, rw_op in *.
      destruct p. unfold "⋅", free_op, exc_op in *. destruct e, e1, e0; trivial;
        try (rewrite unit_dot);
        try (rewrite unit_dot_left);
        try (apply reflex);
        unfold P in H; destruct f; try (destruct u); try (destruct exc); unfold rw_unit in *; intuition; try (inversion H0).
Qed.

Lemma rw_mov_exc_release {M} `{!EqDecision M} `{!TPCM M} (exc: bool) (rc: Z) (x y: M)
  : rw_exchange_cond
    (Central exc rc x ⋅ ExcGuard)
    x
    (Central false rc x)
    (unit: M).
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

Lemma rw_mov_shared_begin {M} `{!EqDecision M} `{!TPCM M} (exc: bool) (rc: Z) (x: M)
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

Lemma rw_mov_shared_acquire {M} `{!EqDecision M} `{!TPCM M} (exc: bool) (rc: Z) (x: M)
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

Lemma rw_mov_shared_release {M} `{!EqDecision M} `{!TPCM M} (exc: bool) (rc: Z) (x y: M)
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

Lemma rw_mov_shared_retry {M} `{!EqDecision M} `{!TPCM M} (exc: bool) (rc: Z) (x: M)
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

Definition rw_borrow_back_cond {M} `{!EqDecision M} `{!TPCM M} (f: RwLock M) (m: M)
  := ∀ p ,
    I_defined (f ⋅ p) -> ∃ z , (dot m z) = I (f ⋅ p).

Lemma rw_mov_shared_borrow {M} `{!EqDecision M} `{!TPCM M} (x: M)
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

Global Instance free_eqdec {M} `{!EqDecision M} : EqDecision (Free M).
Proof. solve_decision. Qed.

Global Instance exc_eqdec {M} `{!EqDecision M} : EqDecision (Exc M).
Proof. solve_decision. Qed.

Global Instance rwlock_eqdec {M} `{!EqDecision M} : EqDecision (RwLock M).
Proof. solve_decision. Qed.

Lemma rw_valid_monotonic {M} `{!EqDecision M} `{!TPCM M}
  (f: RwLock M) (g: RwLock M) : V (f ⋅ g) -> V f.
Proof.
  unfold V. intro. deex. exists (g ⋅ z). unfold "⋅" in *. rewrite rw_op_assoc. trivial. Qed.
  
Lemma rw_unit_valid {M} `{!EqDecision M} `{!TPCM M}
  : V (rw_unit M).
Proof.
  unfold V. exists (Central false 0 (unit: M)).
    unfold "⋅".
    rewrite rw_op_comm.
    rewrite rw_unit_dot. unfold P, rw_unit, Central. unfold free_count. crush.
Qed.
  
Lemma rw_mov_reflex {M} `{!EqDecision M} `{!TPCM M}
  (f: RwLock M) : rw_mov f f.
Proof.
  unfold rw_mov. intros. split; trivial. Qed.
  
Lemma rw_mov_trans {M} `{!EqDecision M} `{!TPCM M}
  (f g h: RwLock M) : rw_mov f g -> rw_mov g h -> rw_mov f h.
Proof. unfold rw_mov. intuition.
  - have q := H p. have q0 := H0 p. intuition.
  - have q := H p. have q0 := H0 p. intuition.
    rewrite H4. trivial.
Qed.

Lemma left_is_unit {M} `{!EqDecision M} (a b: RwLock M)
  : rw_op a b = rw_unit M -> a = rw_unit M.
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
  
Lemma rw_mov_monotonic {M} `{!EqDecision M} `{!TPCM M} : forall x y z ,
      rw_mov x y -> V (rw_op x z) -> V (rw_op y z) /\ rw_mov (rw_op x z) (rw_op y z).
Proof.
  intros. assert (V (rw_op y z)) as Vrw.
  - have h : Decision (rw_op y z = rw_unit M) by solve_decision. destruct h.
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

Global Instance rwlock_tpcm {M} `{!EqDecision M} `{!TPCM M} : TPCM (RwLock M) := {
  m_valid := V ;
  dot := rw_op ;
  mov := rw_mov ;
  unit := rw_unit M ;
  valid_monotonic := rw_valid_monotonic ;
  unit_valid := rw_unit_valid ;
  unit_dot := rw_unit_dot M ;
  tpcm_comm := rw_op_comm ;
  tpcm_assoc := rw_op_assoc ;
  reflex := rw_mov_reflex ;
  trans := rw_mov_trans ;
  mov_monotonic := rw_mov_monotonic ;
}.

Lemma rwlock_I_valid_left
    {M} `{!EqDecision M} `{!TPCM M}
  : ∀ r : RwLock M, I_defined r → m_valid r.
Proof. intro.
  unfold m_valid, rwlock_tpcm.
  unfold I_defined. intro. destruct H.
  - rewrite H. apply rw_unit_valid.
  - unfold V. exists (rw_unit M). unfold "⋅". rewrite rw_unit_dot. trivial.
Qed.

Lemma rwlock_I_defined_unit
    {M} `{!EqDecision M} `{!TPCM M}
   : I_defined (unit: RwLock M).
Proof.
  unfold I_defined. left. trivial.
Qed.
   
Lemma rwlock_I_unit
    {M} `{!EqDecision M} `{!TPCM M}
  : I unit = unit.
Proof.
  trivial.
Qed.

Lemma rwlock_I_mov_refines
    {M} `{!EqDecision M} `{!TPCM M}
  : ∀ b b' : RwLock M, mov b b' → I_defined b → I_defined b' ∧ mov (I b) (I b').
Proof.
  intros.
  unfold mov, rwlock_tpcm, rw_mov in H.
  have h := H (rw_unit M). unfold "⋅" in h.
  repeat (rewrite rw_unit_dot in h). intuition. rewrite H3. apply reflex.
Qed.

Definition rwlock_ref
    M `{!EqDecision M} `{!TPCM M}
    : Refinement (RwLock M) M :=
({|
  rel_defined := I_defined ;
  rel := I ;
  rel_valid_left := rwlock_I_valid_left ;
  rel_defined_unit := rwlock_I_defined_unit ;
  rel_unit := rwlock_I_unit ;
  mov_refines := rwlock_I_mov_refines ;
|}).

Context {𝜇: BurrowCtx}.
Context `{hG : @gen_burrowGS 𝜇 Σ}.

Context {M} `{!EqDecision M} `{!TPCM M} (x: M).
Context `{!HasTPCM 𝜇 M}.
Context `{!HasTPCM 𝜇 (RwLock M)}.
Context `{!HasRef 𝜇 (rwlock_ref M)}.

Lemma rw_new 𝛾 (x: M)
  : L 𝛾 x ==∗ ∃ 𝛼 , L (extend_loc 𝛼 (rwlock_ref M) 𝛾) (Central false 0 x).
Proof. 
  apply InitializeExt.
  - unfold rel_defined, rwlock_ref.
    unfold I_defined. right. apply rw_init_valid.
  - trivial.
Qed.

Lemma rw_exc_begin 𝛾 rc (x: M)
  : L 𝛾 (Central false rc x) ==∗ L 𝛾 (Central true rc x) ∗ L 𝛾 ExcPending.
Proof.
  rewrite <- L_op.
  apply FrameUpdate.
  apply rw_mov_exc_begin.
Qed.

Lemma sep (a b : iProp Σ) :
  a -∗ b -∗ a ∗ b. Admitted.

Lemma rw_exc_acquire 𝛼 𝛾 exc (x: M)
   : L (extend_loc 𝛼 (rwlock_ref M) 𝛾) (Central exc 0 x)
  -∗ L (extend_loc 𝛼 (rwlock_ref M) 𝛾) ExcPending
 ==∗ L (extend_loc 𝛼 (rwlock_ref M) 𝛾) (Central exc 0 x)
   ∗ L (extend_loc 𝛼 (rwlock_ref M) 𝛾) ExcGuard
   ∗ L 𝛾 x.
Proof.
  iIntros "A B".
  iDestruct (L_join with "A B") as "T".
  iMod (L_unit M 𝛾) as "U".
  iMod (FrameExchange _ _ _ _ x _ (dot (Central exc 0 x) ExcGuard) with "T U") as "T".
  - apply rw_mov_exc_acquire.
  - rewrite L_op.
    iModIntro.
    iDestruct "T" as "[[S R] U]".
    iFrame.
Qed.
  
