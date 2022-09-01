(* This file is still experimental. See its tracking issue
https://gitlab.mpi-sws.org/iris/iris/-/issues/405 for details on remaining
issues before stabilization. *)

(** A verified interpreter for HeapLang.

    This file defines a function [exec (fuel:nat) (e:expr) : val + Error] which
    runs a HeapLang expression to [inl v] if [e] terminates in a value [v], or
    returns [inr msg] with a structured error message [msg] if [e] gets stuck at
    some point. Use [pretty msg] to turn the message into a readable string.

    The point of this interpreter is to allow you to test your code or small
    snippets of HeapLang code and see what the semantics does. We prove it
    correct so that you can trust that the interpreter actually reflects the
    semantics, particularly when it says the program is stuck. The interpreter
    also goes through some pain to report specific error messages on failure,
    although these explanations are of course not verified.

    We prove a correctness theorem [exec_spec] about [exec] summarizing its
    guarantees. It distinguishes two cases:
    1. If [exec] returns [inl v], then [e] can execute to [v] according to [rtc
    erased_step] (following the semantics of HeapLang).
    2. If [exec] returns [inr (Stuck msg)], then [e] can execute to some [e']
    that is stuck according to the HeapLang semantics, so [e] really does "go
    wrong". [msg] is a human-readable string describing how [e] got stuck.
    3. Finally, [exec] can also fail due to running out of fuel or encountering
    an unsupported prophecy variable operation, in which case it returns a
    distinct error case and the correctness theorem provides no guarantees.

    The interpreter is _sequential_ and _deterministic_, which means it has some
    limitations. It will ignore forked threads and continue to execute the main
    thread, which may cause some programs to live-lock that would otherwise make
    progress under a fair scheduler.

    Determinism creates a subtle difference between the interpreter and the
    semantics. The interpreter only guarantees properties of one execution while
    the semantics and any safety property proven using Iris conceptually regard
    all executions. Concretely, consider this program: [let: "x" := ref #0 in
    !(LitLoc 1)]. There is one execution where this program terminates in [#0],
    and many where the allocation results in some other location and it is
    stuck. The interpeter happens to allocate starting at [LitLoc 1] and will
    say it produces [#0]. This is technically correct but not useful - there is
    a stuck execution the interpreter didn't find. The only non-determinism in
    sequential HeapLang is allocation, so we believe only strange programs like
    this that correctly "guess" the interpreter's allocations are affected.

    The interpreter is heavily based on Sydney Gibson's MEng thesis:
    https://pdos.csail.mit.edu/papers/gibsons-meng.pdf. That thesis includes an
    interpreter for sequential GooseLang, a fork of HeapLang.

*)

From stdpp Require Import gmap.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics pretty.
From iris.prelude Require Import options.

Local Ltac invc H := inversion H; subst; clear H.

(** Errors are tagged to give [exec] a stronger specification. [Stuck s] is
    distinguished from the other cases because it comes with a proof that the
    expression is eventually stuck. *)
Inductive Error :=
| Stuck (s:string)
| Unsupported (s:string)
| OutOfFuel.

Global Instance error_pretty : Pretty Error :=
  λ err, match err with
         | Stuck s => "stuck: " +:+ s
         | Unsupported s => "unsupported operation: " +:+ s
         | OutOfFuel => "out of fuel"
         end.

Module interp_monad.
  Record interp_state :=
    InterpState { lang_state : state; next_loc : Z; forked_threads : list expr; }.

  Add Printing Constructor interp_state.

  Definition modify_lang_state (f: state → state): interp_state → interp_state :=
    λ s, InterpState (f s.(lang_state)) s.(next_loc) (s.(forked_threads)).
  Definition add_forked_thread (e: expr) : interp_state → interp_state :=
    λ s, InterpState s.(lang_state) s.(next_loc) (s.(forked_threads) ++ [e]).
  Definition interp_state_alloc (n: Z) : interp_state → interp_state :=
    λ s, InterpState s.(lang_state) (n + s.(next_loc)) s.(forked_threads).

  Inductive state_wf (s: interp_state): Prop :=
    { state_wf_holds (l: loc) : (s.(next_loc) ≤ l.(loc_car))%Z →
                                s.(lang_state).(heap) !! l = None; }.

  Definition InterpretM (A:Type) : Type :=
    interp_state → (A+Error) * interp_state.

  Definition init_state : state := {| heap := ∅; used_proph_id := ∅ |}.
  Definition init_interp_state : interp_state :=
    InterpState init_state 1 [].

  (** [run] runs an interpreter monad value starting from an empty initial
      state. *)
  Local Definition run {A} (f: InterpretM A) : A + Error :=
    (f init_interp_state).1.

  Lemma init_interp_state_wf : state_wf init_interp_state.
  Proof. constructor; rewrite /init_interp_state //=. Qed.

  (* basic monad *)
  Global Instance interp_ret : MRet InterpretM := λ A (x:A), λ s, (inl x, s).
  Global Instance interp_bind : MBind InterpretM :=
    λ A B (f: A → InterpretM B) (x: InterpretM A),
    λ s, let (r, s') := x s in
        match r with
        | inl x' => f x' s'
        | inr e => (inr e, s')
        end.
  Global Instance interp_fmap : FMap InterpretM :=
    λ A B (f: A → B) (x: InterpretM A),
    λ s, let (r, s') := x s in
        match r with
        | inl x' => (inl (f x'), s')
        | inr e => (inr e, s')
        end.

  (* state+error-specific monadic constants *)
  Definition interp_modify (f: interp_state → interp_state): InterpretM () :=
    λ s, (inl (), f s).
  Definition interp_modify_state (f: state → state): InterpretM () :=
    interp_modify (modify_lang_state f).
  Definition interp_read {A} (f: state → A): InterpretM A :=
    λ s, (inl (f s.(lang_state)), s).
  Definition interp_error {A} (msg: string) : InterpretM A := λ s, (inr (Stuck msg), s).
  Definition interp_alloc (n:Z): InterpretM loc :=
    λ s, (inl {| loc_car := s.(next_loc)|}, interp_state_alloc n s).

  Definition read_loc (method: string) (vl: val) : InterpretM (loc*val) :=
      match vl with
      | LitV (LitLoc l) =>
        mv ← interp_read (λ σ, σ.(heap) !! l);
        match mv with
        | Some (Some v) => mret (l, v)
        | Some None =>
          interp_error $ method +:+ ": use after free at location: " +:+ pretty l
        | None =>
          interp_error $ method +:+ ": unallocated location: " +:+ pretty l
        end
      | _ => interp_error $ method +:+ ": applied to non-loc " +:+ pretty vl
      end.

  Lemma error_not_inl {A} {msg s} {v: A} {s'} :
    interp_error msg s = (inl v, s') → False.
  Proof. by inversion 1. Qed.

  Lemma mret_inv {A} (v: A) s v' s' :
    mret (M:=InterpretM) v s = (inl v', s') → v = v' ∧ s = s'.
  Proof. by inversion 1. Qed.

  Lemma interp_bind_inv A B (x: InterpretM A) (f: A → InterpretM B) r s s' :
    (x ≫= f) s = (r, s') →
    (∃ e, x s = (inr e, s') ∧ r = inr e) ∨
    (∃ s0 x', x s = (inl x', s0) ∧
              f x' s0 = (r, s')).
  Proof.
    rewrite /mbind /interp_bind.
    repeat case_match; inversion 1; subst; eauto.
  Qed.

  Lemma interp_bind_inl_inv A B (x: InterpretM A) (f: A → InterpretM B) (r: B) s s' :
    (x ≫= f) s = (inl r, s') →
    ∃ s0 x', x s = (inl x', s0) ∧
             f x' s0 = (inl r, s').
  Proof.
    intros [(e & ? & ?) | (s0 & x' & H1 & H2)]%interp_bind_inv.
    - congruence.
    - rewrite H1.
      eexists _, _; eauto.
  Qed.

  Lemma interp_fmap_inv {A B} (f: A → B) x s v s' :
    (fmap (M:=InterpretM) f x) s = (inl v, s') →
    ∃ v0, v = f v0 ∧ x s = (inl v0, s').
  Proof.
    rewrite /fmap /interp_fmap.
    repeat case_match; inversion 1; subst; eauto.
  Qed.

  Lemma read_loc_inv method vl s l v s' :
    read_loc method vl s = (inl (l, v), s') →
    vl = LitV (LitLoc l) ∧
    s' = s ∧
    s.(lang_state).(heap) !! l = Some (Some v).
  Proof.
    rewrite /read_loc.
    destruct vl as [l' | | | | ]; try by inversion 1.
    destruct l' as [| | | | l' |]; intro H; try by inversion H.
    apply interp_bind_inl_inv in H as (s0 & mv & Heq1 & Heq2).
    destruct mv as [mv|]; try by inversion Heq2.
    destruct mv; inversion Heq2; subst; clear Heq2.
    inversion Heq1; subst; clear Heq1.
    eauto.
  Qed.

  Ltac errored :=
    lazymatch goal with
    | H: interp_error _ _ = (inl _, _) |- _ => solve [ exfalso; apply (error_not_inl H) ]
    | H: (inr _, _) = (inl _, _) |- _ => solve [ exfalso; inversion H ]
    end.

  Ltac success :=
    repeat
      lazymatch goal with
      | H: mret _ _ = (inl _, _) |- _ =>
        let Heqv := fresh "Heqv" in
        let Heqs := fresh "Heqs" in
        apply mret_inv in H as [Heqv Heqs]; subst
      | H: (_ ≫= (λ x, _)) _ = (inl _, _) |- _ =>
        let s := fresh "s" in
        let x := fresh x in
        let Heq1 := fresh "Heq" in
        let Heq2 := fresh "Heq" in
        apply interp_bind_inl_inv in H as (s & x & Heq1 & Heq2); subst
      | H: (_ <$> _) _ = (inl ?v, _) |- _ =>
        let s := fresh "s" in
        let v_tmp := fresh "v" in
        rename v into v_tmp;
        apply interp_fmap_inv in H as (v & -> & H)
      | H: interp_modify _ _ = (inl _, _) |- _ => invc H
      | H: interp_modify_state _ _ = (inl _, _) |- _ => invc H
      | H: interp_read _ _ = (inl _, _) |- _ => invc H
      | H: read_loc _ _ _ = (inl _, _) |- _ =>
        apply read_loc_inv in H as (-> & -> & H)
      end; subst.

  Lemma interp_bind_inr_inv {A B} (x: InterpretM A) (f: A → InterpretM B) r s s' :
    (x ≫= f) s = (inr r, s') →
    (x s = (inr r, s')) ∨
    (∃ s0 x', x s = (inl x', s0) ∧ f x' s0 = (inr r, s')).
  Proof.
    rewrite /mbind /interp_bind.
    repeat case_match; intros; simplify_eq/=; eauto.
  Qed.

  Lemma interp_fmap_inr_inv {A B} (f: A → B) (x: InterpretM A) s e s' :
    (f <$> x) s = (inr e, s') →
    x s = (inr e, s').
  Proof.
    rewrite /fmap /interp_fmap.
    repeat case_match; intros; simplify_eq/=; auto.
  Qed.

  Lemma read_loc_inr_inv method vl s err s' :
    read_loc method vl s = (inr err, s') →
    s = s' ∧ match vl with
             | LitV (LitLoc l) => ∀ v, s.(lang_state).(heap) !! l ≠ Some (Some v)
             | _ => True
             end.
  Proof.
    rewrite /read_loc.
    repeat case_match; subst; try solve [ inversion 1; subst; auto ].
    intros H.
    apply interp_bind_inr_inv in H as [H|(s0&x& Hexec1 & Hexec2)]; success.
    - invc H.
    - repeat case_match; invc Hexec2.
      + intuition congruence.
      + intuition congruence.
  Qed.

  Ltac failure :=
    repeat
      match goal with
      | H: (_ ≫= _) _ = (inr _, _) |- _ =>
        let s := fresh "s" in
        let x := fresh "x" in
        let Heq := fresh "Heq" in
        apply interp_bind_inr_inv in H as [H | (s & x & Heq & H)]
      | H: interp_error _ _ = (inr _, _) |- _ => invc H
      | H: mret _ _ = (inr _, _) |- _ => solve [ inversion H ]
      | H: interp_modify _ _ = (inr _, _) |- _ => solve [ inversion H ]
      | H: interp_modify_state _ _ = (inr _, _) |- _ => solve [ inversion H ]
      | H: (_ <$> _) _ = (inr _, _) |- _ =>
        apply interp_fmap_inr_inv in H
      | H: read_loc _ _ _ = (inr _, _) |- _ =>
        apply read_loc_inr_inv in H as [-> H]
      end; subst.

End interp_monad.

Import interp_monad.

Section interpreter.

  (* to make the below definition work with strings as well we add an
  instance of [Pretty string] *)
  Local Instance pretty_string : Pretty string := λ s, s.
  Local Definition pretty_app (s: string) {A} `{Pretty A} (x:A) : string :=
    s +:+ pretty x.

  Infix "+" := pretty_app.

  (* We explain errors which in the semantics are represented by a pure function
     returning None; to sanity-check these definitions, we prove they cover
     exactly the cases where the underlying operation returns None. *)

  Definition option_opposites {A B} (m1 : option A) (m2 : option B) :=
    is_Some m1 ↔ m2 = None.

  Lemma option_opposites_alt {A B} (m1 : option A) (m2 : option B) :
    option_opposites m1 m2 ↔ match m1, m2 with
                             | Some _, None   => True
                             | None  , Some _ => True
                             | _     , _      => False
                             end.
  Proof.
    rewrite /option_opposites is_Some_alt.
    repeat case_match; intuition congruence.
  Qed.

  (** produce an error message for [un_op_eval] *)
  Definition explain_un_op_fail op v : option string :=
    match op with
    | NegOp => match v with
               | LitV (LitInt _) => None
               | LitV (LitBool _) => None
               | _ => Some $ "~ (NegOp) can only be applied to integers and booleans, got " + v
               end
    | MinusUnOp =>
      match v with
      | LitV (LitInt _) => None
      | _ => Some $ "unary - (MinusUnOp) can only be applied to integers, got " + v
      end
    end.

  Lemma explain_un_op_fail_wf op v :
    option_opposites (explain_un_op_fail op v) (un_op_eval op v).
  Proof.
    apply option_opposites_alt.
    rewrite /explain_un_op_fail /un_op_eval.
    repeat case_match; simplify_eq/=; auto.
  Qed.

  Definition explain_unboxed v : option string :=
    match v with
    | LitV l | InjLV (LitV l) | InjRV (LitV l) =>
      match l with
      | LitPoison => Some "poison values (from erasing prophecies) cannot be compared"
      | LitProphecy _ => Some "prophecies cannot be compared"
      | _ => None
      end
    | InjLV _ | InjRV _ => Some "sum values can only be compared if they contain literals"
    | PairV _ _ => Some "pairs are large and considered boxed, must compare by field"
    | RecV _ _ _ => Some "closures are large and cannot be compared"
    end.

  Lemma explain_unboxed_wf v :
    match explain_unboxed v with
    | Some _ => ~val_is_unboxed v
    | None   => val_is_unboxed v
    end.
  Proof.
    rewrite /explain_unboxed /val_is_unboxed /lit_is_unboxed.
    repeat case_match; intuition congruence.
  Qed.

  Definition explain_vals_compare_safe_fail v1 v2 : option string :=
    match explain_unboxed v1, explain_unboxed v2 with
    | Some msg1, Some msg2 =>
      Some $ "one of " + v1 + " and " + v2 + " must be unboxed to compare: "
      + v1 + ": " + msg1 + ", "
      + v2 + ": " + msg2
    | _, _ => None
    end.

  (** [explain_vals_compare_safe_fail] gives an explanation when
  [vals_compare_safe] would be false (that is, when v1 and v2 cannot be
  compared) *)
  Lemma explain_vals_compare_safe_fail_wf v1 v2 :
    is_Some (explain_vals_compare_safe_fail v1 v2) ↔ ~vals_compare_safe v1 v2.
  Proof.
    cut (explain_vals_compare_safe_fail v1 v2 = None ↔ vals_compare_safe v1 v2).
    { rewrite is_Some_alt.
      destruct (explain_vals_compare_safe_fail _ _); intuition congruence. }
    rewrite /explain_vals_compare_safe_fail /vals_compare_safe.
    pose proof (explain_unboxed_wf v1).
    pose proof (explain_unboxed_wf v2).
    destruct (explain_unboxed v1), (explain_unboxed v2); intuition congruence.
  Qed.

  (** produce an error message for [bin_op_eval] *)
  Definition explain_bin_op_fail op v1 v2 : option string :=
    if decide (op = EqOp)
    then (explain_vals_compare_safe_fail v1 v2)
    else match v1, v2 with
         | LitV (LitInt _), LitV (LitInt _) =>
           match op with
           | OffsetOp => Some $ "cannot add to integer " + v1 + " with +ₗ (only locations)"
           | _ => None
           end
         | LitV (LitBool b1), LitV (LitBool b2) =>
           match bin_op_eval_bool op b1 b2 with
           | Some _ => None
           | None => Some $ "non-boolean operator applied to booleans " + op
           end
         | LitV (LitLoc _), _ =>
           match op, v2 with
           | OffsetOp, LitV (LitInt _) => None
           | OffsetOp, _ => Some $ "can only call +ₗ on integers, got " + v2
           | _, _ => Some $ "the only supported operation on locations is +ₗ #i, got "
                            + op + " " + v2
           end
         | _, _ => Some $ "mismatched types of values " + v1 + " and " + v2
         end.

  Lemma explain_bin_op_fail_wf op v1 v2 :
    option_opposites (explain_bin_op_fail op v1 v2) (bin_op_eval op v1 v2).
  Proof.
    apply option_opposites_alt.
    rewrite /explain_bin_op_fail /bin_op_eval
            /bin_op_eval_int /bin_op_eval_bool /bin_op_eval_loc.
    repeat (case_match; simplify_eq/=; auto).
    - pose proof (explain_vals_compare_safe_fail_wf v1 v2).
      intuition eauto.
    - pose proof (explain_vals_compare_safe_fail_wf v1 v2) as H.
      replace (explain_vals_compare_safe_fail v1 v2) in H.
      rewrite -> is_Some_alt in H.
      intuition eauto.
  Qed.

  (* define a shorthand for readability below *)
  Local Notation error := interp_error.

  Fixpoint interpret (fuel:nat) (e: expr) {struct fuel} : InterpretM val :=
    match fuel with
    | 0 => λ s, (inr OutOfFuel, s)
    | S fuel' => let interp := interpret fuel' in
    match e with

      (* lambda calculus *)
    | Val v => mret v
    | Var x => error $ "free var: " + x
    | Rec f x e => mret (RecV f x e)
    | App f e =>
      v2 ← interp e;
      f ← interp f;
      match f with
      | RecV f x e1 =>
        interp (subst' x v2 (subst' f (RecV f x e1) e1))
      | _ => error $ "attempt to call non-function " +:+ pretty f
      end

    (* mostly boring pure operations (sums, products, unary/binary ops) *)
    | Pair e1 e2 =>
      v2 ← interp e2;
      v1 ← interp e1;
      mret (PairV v1 v2)
    | InjL e => InjLV <$> interp e
    | InjR e => InjRV <$> interp e
    | UnOp op e =>
      v ← interp e;
      match un_op_eval op v with
      | Some v => mret v
      | None => error $ "un-op failed: " + match explain_un_op_fail op v with
                                           | Some msg => msg
                                           | None => "" (* impossible *)
                                           end
      end
    | BinOp op e1 e2 =>
      v2 ← interp e2;
      v1 ← interp e1;
      match bin_op_eval op v1 v2 with
      | Some v => mret v
      | None => error $ "bin-op failed: " + match explain_bin_op_fail op v1 v2 with
                                            | Some msg => msg
                                            | None => "" (* impossible *)
                                            end
      end
    | If e e1 e2 =>
      cond ← interp e;
      match cond with
      | LitV (LitBool b) => interp (if b then e1 else e2)
      | _ => error $ "if: non-bool condition " + cond
      end
    | Fst e =>
      v ← interp e;
      match v with
      | PairV v1 _ => mret v1
      | _ => error $ "fst: called on non-pair " + v
      end
    | Snd e =>
      v ← interp e;
      match v with
      | PairV _ v2 => mret v2
      | _ => error $ "snd: called on non-pair " + v
      end
    | Case e e1 e2 =>
      v ← interp e;
      match v with
      | InjLV v => interp (App e1 (Val v))
      | InjRV v => interp (App e2 (Val v))
      | _ => error $ "case: called on non-sum " + v
      end

    | Fork e =>
      _ ← interp_modify (add_forked_thread e);
      mret (LitV LitUnit)

    (* heap manipulation *)
    | AllocN ne e =>
      v ← interp e;
      nv ← interp ne;
      match nv with
      | LitV (LitInt n) =>
        if decide (0 < n)%Z then
          l ← interp_alloc n;
          _ ← interp_modify_state (state_init_heap l n v);
          mret (LitV (LitLoc l))
        else (error $ if decide (n = 0)
                      then "alloc: cannot allocate 0 elements"
                      else "alloc: negative number of elements (first argument) " + n)
      | _ => error $ "alloc: number of elements (first argument) " + nv
      end
    | Load e =>
      vl ← interp e;
      l_v0 ← read_loc "load" vl;
      let '(_, v0) := l_v0 in
      mret v0
    | Free e =>
      vl ← interp e;
      l_v0 ← read_loc "free" vl;
      let '(l, _) := l_v0 in
      _ ← interp_modify_state (state_upd_heap <[l:=None]>);
      mret (LitV LitUnit)
    | Store el e =>
      w ← interp e;
      vl ← interp el;
      l_v0 ← read_loc "store" vl;
      let '(l, _) := l_v0 in
      _ ← interp_modify_state (state_upd_heap <[l:=Some w]>);
      mret (LitV LitUnit)
    | Xchg el e =>
      w ← interp e;
      vl ← interp el;
      l_v0 ← read_loc "xchg" vl;
      let '(l, v0) := l_v0 in
      _ ← interp_modify_state (state_upd_heap <[l:=Some w]>);
      mret v0
    | CmpXchg e e1 e2 =>
      v2 ← interp e2;
      v1 ← interp e1;
      vl ← interp e;
      l_v0 ← read_loc "cmpxchg" vl;
      let '(l, vl) := l_v0 in
      let b := bool_decide (vl = v1) in
      if decide (vals_compare_safe vl v1) then
        _ ← interp_modify_state (λ σ, if b
                                      then state_upd_heap <[l:=Some v2]> σ
                                      else σ);
        mret (PairV vl (LitV (LitBool b)))
      else
        error $ "cmpxchg: failed comparison: " + default "" (explain_vals_compare_safe_fail vl v1)
    | FAA el e =>
      v ← interp e;
      vl ← interp el;
      l_v0 ← read_loc "faa" vl;
      let '(l, v0) := l_v0 in
      match v0, v with
      | LitV (LitInt i1), LitV (LitInt i2) =>
        _ ← interp_modify_state (state_upd_heap <[l:=Some (LitV (LitInt (i1 + i2)))]>);
        mret (LitV (LitInt i1))
      (* check constant passed to FAA only if heap value is an integer *)
      | LitV (LitInt _), _ => error $ "faa: increment " + v + " is not an integer"
      | _, _ => error $ "faa: called on non-integer heap value: " + v0
      end

    (* unsupported prophecy variable operations *)
    | NewProph => λ s, (inr (Unsupported "NewProph"), s)
    | Resolve _ _ _ => λ s, (inr (Unsupported "Resolve"), s)
    end
    end.
End interpreter.

(** * Theory for proving steps are sound. *)

Lemma atomic_step e σ e' σ' :
  head_step e σ [] e' σ' [] →
  ∀ tp, rtc erased_step (e :: tp, σ) (e' :: tp, σ').
Proof.
  intros ? tp.
  apply rtc_once.
  exists [].
  eapply (step_atomic e σ e' σ' [] [] tp); simpl; auto.
  - rewrite app_nil_r //.
  - eapply (Ectx_step []); eauto.
Qed.

Lemma step_inv ts1 σ1 κ ts2 σ2 :
  step (Λ:=heap_lang) (ts1, σ1) κ (ts2, σ2) →
  ∃ (t1 : list expr) (e1 : expr) (t2 : list expr) (e2 : expr) (efs: list expr),
    ts1 = t1 ++ e1 :: t2 ∧
    ts2 = t1 ++ e2 :: t2 ++ efs ∧
    prim_step e1 σ1 κ e2 σ2 efs.
Proof.
  inversion 1.
  simplify_eq.
  eauto 10.
Qed.

Lemma fill_step K (e: expr) σ tp κ e' σ' tp' :
  step (e :: tp, σ) κ (e' :: tp', σ') →
  step (fill K e :: tp, σ) κ (fill K e' :: tp', σ').
Proof.
  intros Hstep.
  apply step_inv in Hstep as (t1 & e1 & t2 & e2 & efs & Heq1 & Heq2 & Hprim_step).
  pose proof Hprim_step as H.
  apply (fill_prim_step K) in H.
  simpl in H.
  destruct t1 as [|e0 t1].
  - simplify_eq/=.
    eapply (step_atomic _ _ _ _ efs [] t2); eauto.
  - simplify_eq/=.
    eapply (step_atomic _ _ _ _ efs (fill K e0 :: t1) t2); eauto.
Qed.

Lemma fill_erased_step (e: expr) σ tp e' σ' tp' K :
  erased_step (e :: tp, σ) (e' :: tp', σ') →
  erased_step (fill K e :: tp, σ) (fill K e' :: tp', σ').
Proof.
  rewrite /erased_step.
  intros [κ Hstep].
  exists κ.
  apply fill_step; auto.
Qed.

Lemma step_cons_no_destroy (e: expr) tp σ κ ρ2 :
  step (e :: tp, σ) κ ρ2 →
  ∃ e' tp' σ', ρ2 = (e' :: tp', σ').
Proof.
  destruct ρ2 as [ts' σ'].
  intros (t1&?&?&?&?&?&?&?)%step_inv; subst.
  destruct t1; simplify_eq/=; eauto.
Qed.

Lemma language_nsteps_inv_r (Λ: language) n ρ1 κs ρ2 :
  language.nsteps (Λ:=Λ) (S n) ρ1 κs ρ2 →
  ∃ ρ' κ κs', step ρ1 κ ρ' ∧ κs = κ ++ κs' ∧
              language.nsteps n ρ' κs' ρ2.
Proof. inversion 1; subst; eauto 10. Qed.

Lemma fill_erased_steps (e: expr) σ tp e' σ' tp' K :
  rtc erased_step (e :: tp, σ) (e' :: tp', σ') →
  rtc erased_step (fill K e :: tp, σ) (fill K e' :: tp', σ').
Proof.
  rewrite !erased_steps_nsteps.
  destruct 1 as (n & κs & Hsteps).
  generalize dependent e.
  generalize dependent tp.
  generalize dependent σ.
  generalize dependent e'.
  generalize dependent tp'.
  generalize dependent σ'.
  generalize dependent κs.
  induction n as [|n IHn]; intros ??????? Hsteps.
  - invc Hsteps.
    exists 0, [].
    constructor.
  - apply language_nsteps_inv_r in Hsteps as (ρ2 & κ & κs' & (Hstep & -> & Hsteps)).
    (* here is the crucial step: to apply [fill_step] need to know that [ρ2] has
    the right structure, which comes from threads not getting destroyed *)
    edestruct step_cons_no_destroy as (e''&tp''&σ''&Heq); eauto; subst.
    apply (fill_step K) in Hstep.
    apply IHn in Hsteps as (n'&κs&?).
    exists (S n'), (κ ++ κs).
    econstructor; eauto.
Qed.

Section interpret_ok.
  Tactic Notation "step" "by" tactic1(t) :=
    etrans; [ solve [ t ] | simpl ].

  Ltac change_to_fill e :=
    reshape_expr e ltac:(fun K e' =>
                           (* find a non-trivial context *)
                           lazymatch K with
                           | [_] => change e with (fill K e')
                           end).

  Ltac step_ctx :=
    lazymatch goal with
    | |- rtc erased_step (?e :: _, _) _ =>
      change_to_fill e;
      step by (apply fill_erased_steps; eauto)
    end.

  Ltac step_atomic :=
    step by (apply atomic_step; eauto using head_step);
    try reflexivity.

  Lemma state_wf_init_alloc (v0 : val) (s : interp_state) (n : Z) :
    (0 ≤ n)%Z →
    state_wf s →
    state_wf
      (modify_lang_state
          (λ σ : state, state_init_heap {| loc_car := next_loc s |} n v0 σ)
          (interp_state_alloc n s)).
  Proof.
    intros Hn.
    constructor; rewrite /modify_lang_state /interp_state_alloc /=; intros l ?.
    apply fin_maps.lookup_union_None; split.
    - destruct (heap_array _ _ !! l) eqn:Hlookup; auto.
      apply heap_array_lookup in Hlookup as (j & w & Hle & ? & ? & Hlookup); subst.
      apply lookup_replicate in Hlookup as [? ?]; subst.
      simpl in *.
      lia.
    - apply state_wf_holds; auto.
      lia.
  Qed.

  Lemma state_wf_same_dom s f :
    (dom (gset loc) (f s.(lang_state)).(heap) = dom _ s.(lang_state).(heap)) →
    state_wf s →
    state_wf (modify_lang_state f s).
  Proof.
    intros Hdom_eq Hwf.
    constructor; rewrite /modify_lang_state /= => l ?.
    apply (fin_map_dom.not_elem_of_dom (D:=gset loc)).
    rewrite Hdom_eq.
    apply fin_map_dom.not_elem_of_dom.
    apply state_wf_holds; auto.
  Qed.

  Lemma state_wf_upd s l mv0 v' :
    state_wf s →
    heap (lang_state s) !! l = Some mv0 →
    state_wf (modify_lang_state (λ σ : state, state_upd_heap <[l:=v']> σ) s).
  Proof.
    intros Hwf Heq.
    apply state_wf_same_dom; auto.
    rewrite fin_map_dom.dom_insert_L.
    apply (fin_map_dom.elem_of_dom_2 (D:=gset loc)) in Heq.
    set_solver.
  Qed.

  Lemma interpret_wf fuel (e: expr) s v s' :
    state_wf s →
    interpret fuel e s = (inl v, s') →
    state_wf s'.
  Proof.
    revert e s v s'.
    induction fuel as [|fuel]; simpl; intros e s v s' **; [ errored | ].
    destruct e; try errored; success; eauto;
      (repeat case_match; subst; try errored;
       success;
       eauto using state_wf_upd).
    - constructor; intros.
      simpl.
      apply state_wf_holds; auto.
    - match goal with
      | H: interp_alloc _ _ = (_, _) |- _ => invc H
      end.
      apply state_wf_init_alloc; eauto.
      lia.
    - apply state_wf_same_dom; eauto.
  Qed.

  Local Hint Resolve interpret_wf : core.

  Lemma interpret_sound fuel e s v s' :
    state_wf s →
    interpret fuel e s = (inl v, s') →
    rtc erased_step (e :: s.(forked_threads), s.(lang_state)) (Val v :: s'.(forked_threads), s'.(lang_state)).
  Proof.
    revert e s v s'.
    induction fuel as [|fuel]; simpl; intros e s v s' **; [ errored | ].
    destruct e; try errored; success; cbn [forked_threads lang_state];
      repeat match goal with
             | H: (match ?x with
                   | _ => _
                   end _ = (inl _, _)) |- _ =>
               let Heqn := fresh "Heqn" in
               destruct x eqn:Heqn; try errored; [idtac]
             | _ => progress success
             | _ => step_ctx
             | _ => step_atomic
             end.
    - (* Val *)
      reflexivity.
    - (* App *)
      eauto.
    - (* If *)
      lazymatch goal with
      | |- context[LitBool ?b] => destruct b; step_atomic; eauto
      end.
    - (* Case *)
      lazymatch goal with
      | |- context[Case (Val ?v)] => destruct v; try errored; step_atomic; eauto
      end.
    - (* Fork *)
      eapply rtc_once. exists [].
      lazymatch goal with
      | |- context[Fork ?e] => eapply (step_atomic _ _ _ _ [e] []); simpl; eauto
      end.
      apply head_prim_step; simpl.
      eauto using head_step.
    - (* AllocN *)
      lazymatch goal with
      | H: interp_alloc _ _ = _ |- _ => invc H
      end.
      eapply atomic_step. constructor; auto; intros.
      simpl. apply state_wf_holds; eauto.
      simpl; lia.
  Qed.

  (** * Theory for expressions that are stuck after some execution steps. *)

  Definition eventually_stuck (e: expr) tp σ tp' σ' :=
    ∃ e'', rtc erased_step (e :: tp, σ) (e'':: tp', σ') ∧ stuck e'' σ'.

  (** a stuck expression is eventually stuck *)
  Lemma eventually_stuck_now (e: expr) tp σ :
    stuck e σ →
    eventually_stuck e tp σ tp σ.
  Proof.
    intros.
    exists e.
    split; [ reflexivity | auto ].
  Qed.

  (** we can "peel off" some number of execution steps before proving that an
  expression is stuck *)
  Lemma eventually_stuck_steps e tp σ tp0 σ0 e' tp' σ' :
    rtc erased_step (e :: tp, σ) (e' :: tp0, σ0) →
    eventually_stuck e' tp0 σ0 tp' σ' →
    eventually_stuck e tp σ tp' σ'.
  Proof.
    intros Hsteps (e'' & Hsteps' & Hstuck).
    eexists. split; [ etrans; eauto | eauto ].
  Qed.

  (** [eventually_stuck] respects evaluation contexts *)
  Lemma eventually_stuck_fill K e tp σ tp' σ' :
    eventually_stuck e tp σ tp' σ' →
    eventually_stuck (fill K e) tp σ tp' σ'.
  Proof.
    intros (e' & Hsteps & Hstuck).
    eexists (fill K e'). split.
    - apply fill_erased_steps; auto.
    - apply stuck_fill; auto.
  Qed.

  Local Hint Resolve interpret_sound : core.

  (* peel off execution steps and use above automation to prove the [rtc
  erased_steps] premise *)
  Ltac stuck_steps :=
    eapply eventually_stuck_steps;
    [ repeat step_ctx; (step_atomic || reflexivity)
    |].

  (* automate using hypotheses about stuckness inside an evaluation context *)
  Ltac stuck_fill :=
    lazymatch goal with
    | |- eventually_stuck ?e _ _ _ _ =>
      change_to_fill e; apply eventually_stuck_fill; solve [ eauto ]
    end.

  (** We need more complicated theory to handle expressions that are stuck now,
  because there is no [head_step] they can take. *)

  (* [terminal_expr e] holds when e cannot be the result of taking a context
  step. Slightly more formally, e doesn't have the shape [fill K e'] where e' is
  reducible. *)
  Definition terminal_expr e :=
    ∀ K e', to_val e' = None →
            e = fill K e' →
            K = [] ∧ e' = e.

  Lemma stuck_not_val e σ :
    to_val e = None →
    (∀ (κs: list observation) (e': expr) (σ': state) (efs: list expr),
        prim_step e σ κs e' σ' efs → False) →
    stuck e σ.
  Proof.
    rewrite /stuck /irreducible.
    intuition.
  Qed.

  Local Hint Resolve val_head_stuck : core.

  (* This theorem expresses the point of [terminal_expr e]: a terminal_expr is
  stuck if it can't take a head step, because there's *)
  Lemma terminal_expr_stuck e σ :
    to_val e = None →
    terminal_expr e →
    (∀ κ e' σ' efs, head_step e σ κ e' σ' efs → False) →
    stuck e σ.
  Proof.
    intros Hnot_val Hterminal Hno_head_step.
    apply stuck_not_val; first done; intros * Hstep.
    invc Hstep; simpl in *.
    lazymatch type of Hnot_val with
    | to_val (fill ?K ?e1') = None => edestruct (Hterminal K e1') as [-> ?]; eauto
    end.
  Qed.

  Lemma fill_not_val' K e v :
    to_val e = None →
    Val v = fill K e →
    False.
  Proof.
    intros H Hfill.
    apply (fill_not_val K) in H; simpl in *.
    rewrite -Hfill /= in H.
    congruence.
  Qed.

  (* to prove [terminal_expr], we work by contradiction in the case where [K] is
  non-empty; to deal with [fill], which is a fold left, we express a non-empty
  list as [l ++ [x]] rather than the usual [x::l]. *)
  Lemma list_rev_case {A} (l: list A) :
    l = [] ∨ ∃ x l', l = l' ++ [x].
  Proof.
    induction l using rev_ind; eauto.
  Qed.

  Ltac ctx_case K Ki :=
    let K' := fresh "K" in
    destruct (list_rev_case K) as [->| (Ki & K' & ->)]; [by auto|];
    rewrite ?fill_app /=.

  Ltac prove_terminal :=
    lazymatch goal with
    | |- terminal_expr _ =>
      let K := fresh "K" in
      let e := fresh "e" in
      let Ki := fresh "Ki" in
      intros K e; ctx_case K Ki;
      destruct Ki;
      let H := fresh in
      intros ? H; invc H;
      solve [ exfalso; eauto using fill_not_val' ]
    | _ => fail "not a terminal_expr goal"
    end.

  (* demo the [prove_terminal] tactic *)
  Lemma fill_app_inv v1 v2 :
    terminal_expr (App (Val v1) (Val v2)).
  Proof. prove_terminal. Qed.

  Ltac stuck_now :=
    apply eventually_stuck_now, terminal_expr_stuck;
    [done
    |prove_terminal
    |let H := fresh "Hstep" in
     intros * H;
     try (inversion H; congruence) ].

  Lemma interpret_complete fuel : ∀ e s msg s',
    ∀ (Hwf: state_wf s),
      interpret fuel e s = (inr (Stuck msg), s') →
      eventually_stuck e s.(forked_threads) s.(lang_state) s'.(forked_threads) s'.(lang_state).
  Proof.
    induction fuel as [|fuel]; simpl; intros e s msg s' **; [congruence|].
    destruct e; failure; stuck_steps; try stuck_fill;
      try (repeat case_match; failure; try stuck_now;
           let n := numgoals in guard n <= 1);
      simplify_eq.
    - (* App *)
      stuck_steps.
      eauto.
    - (* If *)
      repeat case_match; failure; try stuck_now.
      + stuck_steps; eauto.
      + stuck_steps; eauto.
    - (* Case *)
      repeat case_match; failure; try stuck_now.
      + stuck_steps; eauto.
      + stuck_steps; eauto.
    - (* CmpXchg *)
      success. stuck_now.
    - (* FAA *)
      lazymatch goal with
      | H: read_loc _ _ _ = (inl ?p, _) |- _ => destruct p as [l v]
      end.
      success.
      repeat case_match; failure; stuck_now.
  Qed.

End interpret_ok.

Definition exec (fuel:nat) (e: expr) : val + Error :=
  interp_monad.run (interpret fuel e).

Theorem exec_spec fuel e :
  match exec fuel e with
  | inl v =>
    (* if the interpreter runs to completion, it produces a valid execution of
    [e] *)
    ∃ tp' σ', rtc erased_step ([e], init_state) ([Val v] ++ tp', σ')
  | inr (Stuck _) =>
    (* if the interpreter produces a "stuck" error message, [e] can get stuck *)
    ∃ e' tp' σ', rtc erased_step ([e], init_state) ([e'] ++ tp', σ') ∧ stuck e' σ'
  | inr _ =>
    (* If the interpreter fails otherwise (due to running out of fuel or an
    unsupported prophecy variable operation), then it provides no guarantees. *)
    True
  end.
Proof.
  rewrite /exec /interp_monad.run.
  destruct (interpret fuel e init_interp_state) as [r s] eqn:Hinterpret.
  destruct r as [v | [msg|msg|] ]; simpl; auto.
  - apply interpret_sound in Hinterpret;
      eauto using init_interp_state_wf.
  - apply interpret_complete in Hinterpret;
      auto using init_interp_state_wf.
    destruct Hinterpret as (e' & Hexec & Hstuck); eauto.
Qed.
