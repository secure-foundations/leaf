Require Import Burrow.rollup.
From iris.prelude Require Import options.

Require Import Burrow.CpdtTactics.

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
  
