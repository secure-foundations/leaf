(** This file collects general purpose tactics that are used throughout
the development. *)
From Coq Require Export Lia.
From stdpp Require Export decidable.
From stdpp Require Import options.

Lemma f_equal_dep {A B} (f g : ∀ x : A, B x) x : f = g → f x = g x.
Proof. intros ->; reflexivity. Qed.
Lemma f_equal_help {A B} (f g : A → B) x y : f = g → x = y → f x = g y.
Proof. intros -> ->; reflexivity. Qed.
Ltac f_equal :=
  let rec go :=
    match goal with
    | _ => reflexivity
    | _ => apply f_equal_help; [go|try reflexivity]
    | |- ?f ?x = ?g ?x => apply (f_equal_dep f g); go
    end in
  try go.

(** We declare hint databases [f_equal], [congruence] and [lia] and containing
solely the tactic corresponding to its name. These hint database are useful in
to be combined in combination with other hint database. *)
Global Hint Extern 998 (_ = _) => f_equal : f_equal.
Global Hint Extern 999 => congruence : congruence.
Global Hint Extern 1000 => lia : lia.
Global Hint Extern 1001 => progress subst : subst. (** backtracking on this one will
be very bad, so use with care! *)

(** The tactic [intuition] expands to [intuition auto with *] by default. This
is rather inefficient when having big hint databases, or expensive [Hint Extern]
declarations as the ones above. *)
Ltac intuition_solver ::= auto.

(** The [fast_reflexivity] tactic only works on syntactically equal terms. It
can be used to avoid expensive failing unification. *)
Ltac fast_reflexivity :=
  match goal with
  | |- _ ?x ?x => solve [simple apply reflexivity]
  end.

(** [done] can get slow as it calls "trivial". [fast_done] can solve way less
goals, but it will also always finish quickly.  We do 'reflexivity' last because
for goals of the form ?x = y, if we have x = y in the context, we will typically
want to use the assumption and not reflexivity *)
Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | apply not_symmetry; eassumption
    | reflexivity ].
Tactic Notation "fast_by" tactic(tac) :=
  tac; fast_done.

Class TCFastDone (P : Prop) : Prop := tc_fast_done : P.
Global Hint Extern 1 (TCFastDone ?P) => (change P; fast_done) : typeclass_instances.

(** A slightly modified version of Ssreflect's finishing tactic [done]. It
also performs [reflexivity] and uses symmetry of negated equalities. Compared
to Ssreflect's [done], it does not compute the goal's [hnf] so as to avoid
unfolding setoid equalities. Note that this tactic performs much better than
Coq's [easy] tactic as it does not perform [inversion]. *)
Ltac done :=
  solve
  [ repeat first
    [ fast_done
    | solve [trivial]
    (* All the tactics below will introduce themselves anyway, or make no sense
       for goals of product type. So this is a good place for us to do it. *)
    | progress intros
    | solve [symmetry; trivial]
    | solve [apply not_symmetry; trivial]
    | discriminate
    | contradiction
    | split
    | match goal with H : ¬_ |- _ => case H; clear H; fast_done end ]
  ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

Ltac done_if b :=
  match b with
  | true => done
  | false => idtac
  end.

(** Aliases for transitivity and etransitivity that are easier to type *)
Tactic Notation "trans" constr(A) := transitivity A.
Tactic Notation "etrans" := etransitivity.

(** Tactics for splitting conjunctions:

- [split_and] : split the goal if is syntactically of the shape [_ ∧ _]
- [split_and?] : split the goal repeatedly (perhaps zero times) while it is
  of the shape [_ ∧ _].
- [split_and!] : works similarly, but at least one split should succeed. In
  order to do so, it will head normalize the goal first to possibly expose a
  conjunction.

Note that [split_and] differs from [split] by only splitting conjunctions. The
[split] tactic splits any inductive with one constructor.


- [destruct_and? H] : destruct assumption [H] repeatedly (perhaps zero times)
  while it is of the shape [_ ∧ _].
- [destruct_and! H] : works similarly, but at least one destruct should succeed.
  In order to do so, it will head normalize the goal first to possibly expose a
  conjunction.
- [destruct_and?] iterates [destruct_or? H] on every matching assumption [H].
- [destruct_and!] works similarly, but at least one destruct should succeed.
*)
Tactic Notation "split_and" :=
  match goal with
  | |- _ ∧ _ => split
  | |- Is_true (_ && _) => apply andb_True; split
  end.
Tactic Notation "split_and" "?" := repeat split_and.
Tactic Notation "split_and" "!" := hnf; split_and; split_and?.

Ltac destruct_and_go H :=
  try lazymatch type of H with
  | True => clear H
  | _ ∧ _ =>
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [ H1 H2 ];
    destruct_and_go H1; destruct_and_go H2
  | Is_true (bool_decide _) =>
    apply (bool_decide_unpack _) in H;
    destruct_and_go H
  | Is_true (_ && _) =>
    apply andb_True in H;
    destruct_and_go H
  end.

Tactic Notation "destruct_and" "?" ident(H) :=
  destruct_and_go H.
Tactic Notation "destruct_and" "!" ident(H) :=
  hnf in H; progress (destruct_and? H).

Tactic Notation "destruct_and" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_and? H) end.
Tactic Notation "destruct_and" "!" :=
  progress destruct_and?.

(** Tactics for splitting disjunctions in an assumption:

- [destruct_or? H] : destruct the assumption [H] repeatedly (perhaps zero times)
  while it is of the shape [_ ∨ _].
- [destruct_or! H] : works similarly, but at least one destruct should succeed.
  In order to do so, it will head normalize the goal first to possibly
  expose a disjunction.
- [destruct_or?] iterates [destruct_or? H] on every matching assumption [H].
- [destruct_or!] works similarly, but at least one destruct should succeed.
*)
Tactic Notation "destruct_or" "?" ident(H) :=
  repeat match type of H with
  | False => destruct H
  | _ ∨ _ => destruct H as [H|H]
  | Is_true (bool_decide _) => apply (bool_decide_unpack _) in H
  | Is_true (_ || _) => apply orb_True in H; destruct H as [H|H]
  end.
Tactic Notation "destruct_or" "!" ident(H) := hnf in H; progress (destruct_or? H).

Tactic Notation "destruct_or" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_or? H) end.
Tactic Notation "destruct_or" "!" :=
  progress destruct_or?.


(** The tactic [case_match] destructs an arbitrary match in the conclusion or
assumptions, and generates a corresponding equality. This tactic is best used
together with the [repeat] tactical. *)
Tactic Notation "case_match" "eqn" ":" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.
Ltac case_match :=
  let H := fresh in case_match eqn:H.

Tactic Notation "case_guard" "as" ident(Hx) :=
  match goal with
  | H : context C [@guard_or ?E ?e ?M ?T ?R ?P ?dec] |- _ =>
      change (@guard_or E e M T R P dec) with (
        match @decide P dec with left H' => @mret M R P H' | _ => @mthrow E M T P e end) in *;
      destruct_decide (@decide P dec) as Hx
  | |- context C [@guard_or ?E ?e ?M ?T ?R ?P ?dec] =>
      change (@guard_or E e M T R P dec) with (
        match @decide P dec with left H' => @mret M R P H' | _ => @mthrow E M T P e end) in *;
      destruct_decide (@decide P dec) as Hx
  end.
Tactic Notation "case_guard" :=
  let H := fresh in case_guard as H.

(** The tactic [unless T by tac_fail] succeeds if [T] is not provable by
the tactic [tac_fail]. *)
Tactic Notation "unless" constr(T) "by" tactic3(tac_fail) :=
  first [assert T by tac_fail; fail 1 | idtac].

(** The tactic [repeat_on_hyps tac] repeatedly applies [tac] in unspecified
order on all hypotheses until it cannot be applied to any hypothesis anymore. *)
Tactic Notation "repeat_on_hyps" tactic3(tac) :=
  repeat match goal with H : _ |- _ => progress tac H end.

(** The tactic [clear dependent H1 ... Hn] clears the hypotheses [Hi] and
their dependencies. This provides an n-ary variant of Coq's standard
[clear dependent]. *)
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) :=
  clear dependent H1; clear dependent H2.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) :=
  clear dependent H1 H2; clear dependent H3.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) :=
  clear dependent H1 H2 H3; clear dependent H4.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  hyp(H5) := clear dependent H1 H2 H3 H4; clear dependent H5.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  hyp (H6) := clear dependent H1 H2 H3 H4 H5; clear dependent H6.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  hyp (H6) hyp(H7) := clear dependent H1 H2 H3 H4 H5 H6; clear dependent H7.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  hyp (H6) hyp(H7) hyp(H8) :=
  clear dependent H1 H2 H3 H4 H5 H6 H7; clear dependent H8.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  hyp (H6) hyp(H7) hyp(H8) hyp(H9) :=
  clear dependent H1 H2 H3 H4 H5 H6 H7 H8; clear dependent H9.
Tactic Notation "clear" "dependent" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  hyp (H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10) :=
  clear dependent H1 H2 H3 H4 H5 H6 H7 H8 H9; clear dependent H10.

(** The tactic [is_non_dependent H] determines whether the goal's conclusion or
hypotheses depend on [H]. *)
Tactic Notation "is_non_dependent" constr(H) :=
  match goal with
  | _ : context [ H ] |- _ => fail 1
  | |- context [ H ] => fail 1
  | _ => idtac
  end.

(** The tactic [var_eq x y] fails if [x] and [y] are unequal, and [var_neq]
does the converse. *)
Ltac var_eq x1 x2 := match x1 with x2 => idtac | _ => fail 1 end.
Ltac var_neq x1 x2 := match x1 with x2 => fail 1 | _ => idtac end.

(** The tactic [mk_evar T] returns a new evar of type [T], without affecting the
current context.

This is usually a more useful behavior than Coq's [evar], which is a
side-effecting tactic (not returning anything) that introduces a local
definition into the context that holds the evar.
Note that the obvious alternative [open_constr (_:T)] has subtly different
behavior, see std++ issue 115.

Usually, Ltacs cannot return a value and have a side-effect, but we use the
trick described at
<https://stackoverflow.com/questions/45949064/check-for-evars-in-a-tactic-that-returns-a-value/46178884#46178884>
to work around that: wrap the side-effect in a [match goal]. *)
Ltac mk_evar T :=
  let T := constr:(T : Type) in
  let e := fresh in
  let _ := match goal with _ => evar (e:T) end in
  let e' := eval unfold e in e in
  let _ := match goal with _ => clear e end in
  e'.

(** The tactic [get_head t] returns the head function [f] when [t] is of the
shape [f a1 ... aN]. This is purely syntactic, no unification is performed. *)
Ltac get_head e :=
  lazymatch e with
  | ?h _ => get_head h
  | _    => e
  end.

(** The tactic [eunify x y] succeeds if [x] and [y] can be unified, and fails
otherwise. If it succeeds, it will instantiate necessary evars in [x] and [y].

Contrary to Coq's standard [unify] tactic, which uses [constr] for the arguments
[x] and [y], [eunify] uses [open_constr] so that one can use holes (i.e., [_]s).
For example, it allows one to write [eunify x (S _)], which will test if [x]
unifies a successor. *)
Tactic Notation "eunify" open_constr(x) open_constr(y) :=
  unify x y.

(** The tactic [no_new_unsolved_evars tac] executes [tac] and fails if it
creates any new evars or leaves behind any subgoals. *)
Ltac no_new_unsolved_evars tac := solve [unshelve tac].

(** Operational type class projections in recursive calls are not folded back
appropriately by [simpl]. The tactic [csimpl] uses the [fold_classes] tactics
to refold recursive calls of [fmap], [mbind], [omap] and [alter]. A
self-contained example explaining the problem can be found in the following
Coq-club message:

https://sympa.inria.fr/sympa/arc/coq-club/2012-10/msg00147.html *)
Ltac fold_classes :=
  repeat match goal with
  | |- context [ ?F ] =>
    progress match type of F with
    | FMap _ =>
       change F with (@fmap _ F);
       repeat change (@fmap _ (@fmap _ F)) with (@fmap _ F)
    | MBind _ =>
       change F with (@mbind _ F);
       repeat change (@mbind _ (@mbind _ F)) with (@mbind _ F)
    | OMap _ =>
       change F with (@omap _ F);
       repeat change (@omap _ (@omap _ F)) with (@omap _ F)
    | Alter _ _ _ =>
       change F with (@alter _ _ _ F);
       repeat change (@alter _ _ _ (@alter _ _ _ F)) with (@alter _ _ _ F)
    end
  end.
Ltac fold_classes_hyps H :=
  repeat match type of H with
  | context [ ?F ] =>
    progress match type of F with
    | FMap _ =>
       change F with (@fmap _ F) in H;
       repeat change (@fmap _ (@fmap _ F)) with (@fmap _ F) in H
    | MBind _ =>
       change F with (@mbind _ F) in H;
       repeat change (@mbind _ (@mbind _ F)) with (@mbind _ F) in H
    | OMap _ =>
       change F with (@omap _ F) in H;
       repeat change (@omap _ (@omap _ F)) with (@omap _ F) in H
    | Alter _ _ _ =>
       change F with (@alter _ _ _ F) in H;
       repeat change (@alter _ _ _ (@alter _ _ _ F)) with (@alter _ _ _ F) in H
    end
  end.
Tactic Notation "csimpl" "in" hyp(H) :=
  try (progress simpl in H; fold_classes_hyps H).
Tactic Notation "csimpl" := try (progress simpl; fold_classes).
Tactic Notation "csimpl" "in" "*" :=
  repeat_on_hyps (fun H => csimpl in H); csimpl.

(** The tactic [simplify_eq] repeatedly substitutes, discriminates,
and injects equalities, and tries to contradict impossible inequalities. *)
Tactic Notation "simplify_eq" := repeat
  match goal with
  | H : _ ≠ _ |- _ => by case H; try clear H
  | H : _ = _ → False |- _ => by case H; try clear H
  | H : ?x = _ |- _ => subst x
  | H : _ = ?x |- _ => subst x
  | H : _ = _ |- _ => discriminate H
  | H : _ ≡ _ |- _ => apply leibniz_equiv in H
  | H : ?f _ = ?f _ |- _ => apply (inj f) in H
  | H : ?f _ _ = ?f _ _ |- _ => apply (inj2 f) in H; destruct H
    (* before [injection] to circumvent bug #2939 in some situations *)
  | H : ?f _ = ?f _ |- _ => progress injection H as H
    (* first hyp will be named [H], subsequent hyps will be given fresh names *)
  | H : ?f _ _ = ?f _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ = ?f _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ => progress injection H as H
  | H : ?x = ?x |- _ => clear H
    (* unclear how to generalize the below *)
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2
  | H1 : ?o = Some ?x, H2 : ?o = None |- _ => congruence
  | H : @existT ?A _ _ _ = existT _ _ |- _ =>
     apply (Eqdep_dec.inj_pair2_eq_dec _ (decide_rel (=@{A}))) in H
  end.
Tactic Notation "simplify_eq" "/=" :=
  repeat (progress csimpl in * || simplify_eq).
Tactic Notation "f_equal" "/=" := csimpl in *; f_equal.

Ltac setoid_subst_aux R x :=
  match goal with
  | H : R x ?y |- _ =>
     is_var x;
     try match y with x _ => fail 2 end;
     repeat match goal with
     | |- context [ x ] => setoid_rewrite H
     | H' : context [ x ] |- _ =>
        try match H' with H => fail 2 end;
        setoid_rewrite H in H'
     end;
     clear x H
  end.
Ltac setoid_subst :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : @equiv ?A ?e ?x _ |- _ => setoid_subst_aux (@equiv A e) x
  | H : @equiv ?A ?e _ ?x |- _ => symmetry in H; setoid_subst_aux (@equiv A e) x
  end.

(** A little helper for [f_equiv] and [solve_proper] that simplifies away [flip]
relations. *)
Ltac clean_flip :=
  repeat match goal with
  | |- (flip ?R) ?x ?y => change (R y x)
  | H : (flip ?R) ?x ?y |- _ => change (R y x) in H
  end.

(** f_equiv works on goals of the form [f _ = f _], for any relation and any
number of arguments. It looks for an appropriate [Proper] instance, and applies
it. The tactic is somewhat limited, since it cannot be used to backtrack on
the Proper instances that has been found. To that end, we try to avoid the
trivial instance in which the resulting goals have an [eq]. More generally,
we try to "maintain" the relation of the current goal. For example,
when having [Proper (equiv ==> dist) f] and [Proper (dist ==> dist) f], it will
favor the second because the relation (dist) stays the same. *)
Ltac f_equiv :=
  (* Simplify away [flip], they would get in the way later. *)
  clean_flip;
  (* Find out what kind of goal we have, and try to make progress. *)
  match goal with
  (* Similar to [f_equal] also handle the reflexivity case. *)
  | |- _ ?x ?x => fast_reflexivity
  (* Making progress on [pointwise_relation] is as simple as introducing the variable. *)
  | |- pointwise_relation _ _ _ _ => intros ?
  (* We support matches on both sides, *if* they concern the same variable, or
     terms in some relation. *)
  | |- ?R (match ?x with _ => _ end) (match ?x with _ => _ end) =>
    destruct x
  | H : ?R ?x ?y |- ?R2 (match ?x with _ => _ end) (match ?y with _ => _ end) =>
     destruct H
  (* First assume that the arguments need the same relation as the result. We
  check the most restrictive pattern first: [(?f _) (?f _)] requires all but the
  last argument to be syntactically equal. *)
  | |- ?R (?f _) (?f _) => simple apply (_ : Proper (R ==> R) f)
  | |- ?R (?f _ _) (?f _ _) => simple apply (_ : Proper (R ==> R ==> R) f)
  | |- ?R (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R ==> R) f)
  (* For the case in which R is polymorphic, or an operational type class,
  like equiv. *)
  | |- (?R _) (?f _) (?f _) => simple apply (_ : Proper (R _ ==> R _) f)
  | |- (?R _ _) (?f _) (?f _) => simple apply (_ : Proper (R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _) (?f _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _) (?f _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _) (?f _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _) (?f _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)
  (* In case the function symbol differs, but the arguments are the same, maybe
     we have a relation about those functions in our context that we can simply
     apply. (The case where the arguments differ is a lot more complicated; with
     the way we typically define the relations on function spaces it further
     requires [Proper]ness of [f] or [g]). *)
  | H : _ ?f ?g |- ?R (?f ?x) (?g ?x) => solve [simple apply H]
  | H : _ ?f ?g |- ?R (?f ?x ?y) (?g ?x ?y) => solve [simple apply H]

  (* Fallback case: try to infer the relation, and allow the function to not be
     syntactically the same on both sides. Unfortunately, very often, it will
     turn the goal into a Leibniz equality so we get stuck. Furthermore, looking
     for instances in this order will mean that Coq will try to unify the
     remaining arguments that we have not explicitly generalized, which can be
     very slow -- but if we go for the opposite order, we will hit the Leibniz
     equality fallback instance even more often. *)
  (* TODO: Can we exclude that Leibniz equality instance? *)
  | |- ?R (?f _) _ => simple apply (_ : Proper (_ ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  end;
  (* Similar to [f_equal] immediately solve trivial goals *)
  try fast_reflexivity.
Tactic Notation "f_equiv" "/=" := csimpl in *; f_equiv.

(** The typeclass [SolveProperSubrelation] is used by the [solve_proper] tactic
when the goal is of the form [R1 x y] and there are assumptions of the form [R2
x y]. We cannot use Coq's [subrelation] class here as adding the [subrelation]
instances causes lots of backtracking in the [Proper] hint search, resulting in
very slow/diverging [rewrite]s due to exponential instance search. *)
Class SolveProperSubrelation {A} (R R' : relation A) :=
  is_solve_proper_subrelation x y : R x y → R' x y.
(** We use [!] to handle indexed relations such as [dist], where we
can have an [R n] assumption and a [R ?m] goal. *)
Global Hint Mode SolveProperSubrelation + ! ! : typeclass_instances.
Global Arguments is_solve_proper_subrelation {A R R' _ x y}.

Global Instance subrelation_solve_proper_subrelation {A} (R R' : relation A) :
  subrelation R R' →
  SolveProperSubrelation R R'.
Proof. intros ???. apply is_subrelation. Qed.

(** The tactic [solve_proper_unfold] unfolds the first head symbol, so that
we proceed by repeatedly using [f_equiv]. *)
Ltac solve_proper_unfold :=
  (* Try unfolding the head symbol, which is the one we are proving a new property about *)
  try lazymatch goal with
  | |- ?R ?t1 ?t2 =>
    let h1 := get_head t1 in
    let h2 := get_head t2 in
    unify h1 h2;
    unfold h1
  end.
(** [solve_proper_prepare] does some preparation work before the main
[solve_proper] loop.  Having this as a separate tactic is useful for debugging
[solve_proper] failure. *)
Ltac solve_proper_prepare :=
  (* Introduce everything *)
  intros;
  repeat lazymatch goal with
  | |- Proper _ _ => intros ???
  | |- (_ ==> _)%signature _ _ => intros ???
  | |- pointwise_relation _ _ _ _ => intros ?
  | |- ?R ?f _ =>
     (* Deal with other cases where we have an equivalence relation on functions
     (e.g. a [pointwise_relation] that is hidden in some form in [R]). We do
     this by checking if the arguments of the relation are actually functions,
     and then forcefully introduce one ∀ and introduce the remaining ∀s that
     show up in the goal. To check that we actually have an equivalence relation
     on functions, we try to eta expand [f], which will only succeed if [f] is
     actually a function. *)
     let f' := constr:(λ x, f x) in
     (* Now forcefully introduce the first ∀ and other ∀s that show up in the
     goal afterwards. *)
     intros ?; intros
  end;
  (* Simplify things, if we can. *)
  simplify_eq;
  (* We try with and without unfolding. We have to backtrack on
     that because unfolding may succeed, but then the proof may fail. *)
  (solve_proper_unfold + idtac); simpl.
(** [solve_proper_finish] is basically a version of [eassumption]
that can also take into account [subrelation]. *)
Ltac solve_proper_finish :=
  (* We always try this first, since the syntactic match below is not always
  able to find the assumptions we are looking for (e.g. when [Some x ⊑ Some y]
  is convertible to [x ⊑ y]). *)
  eassumption ||
  match goal with
  | H : ?R1 ?x ?y |- ?R2 ?x ?y =>
    no_new_unsolved_evars ltac:(eapply (is_solve_proper_subrelation H))
  end.
(** The tactic [solve_proper_core tac] solves goals of the form "Proper (R1 ==> R2)", for
any number of relations. The actual work is done by repeatedly applying
[tac]. *)
Ltac solve_proper_core tac :=
  solve_proper_prepare;
  (* Now do the job. The inner tactics can rely on [flip] having been cleaned. *)
  solve [repeat (clean_flip; first [solve_proper_finish | tac ()]) ].

(** Finally, [solve_proper] tries to apply [f_equiv] in a loop. *)
Ltac solve_proper := solve_proper_core ltac:(fun _ => f_equiv).

(** The tactic [intros_revert tac] introduces all foralls/arrows, performs tac,
and then reverts them. *)
Ltac intros_revert tac :=
  lazymatch goal with
  | |- ∀ _, _ => let H := fresh in intro H; intros_revert tac; revert H
  | |- _ => tac
  end.

(** The tactic [iter tac l] runs [tac x] for each element [x ∈ l] until [tac x]
succeeds. If it does not suceed for any element of the generated list, the whole
tactic wil fail. *)
Tactic Notation "iter" tactic(tac) tactic(l) :=
  let rec go l :=
  match l with ?x :: ?l => tac x || go l end in go l.

(** Runs [tac] on the n-th hypothesis that can be introduced from the goal. *)
Ltac num_tac n tac :=
  intros until n;
  lazymatch goal with
  (* matches the last hypothesis, which is what we want *)
  | H : _ |- _ => tac H
  end.

(** The tactic [inv] is a fixed version of [inversion_clear] from the standard
library that works around <https://github.com/coq/coq/issues/2465>. It also
has a shorter name since clearing is the default for [destruct], why wouldn't
it also be the default for inversion?
This is inspired by CompCert's [inv] tactic
<https://github.com/AbsInt/CompCert/blob/5f761eb8456609d102acd8bc780b6fd3481131ef/lib/Coqlib.v#L30>. *)
Tactic Notation "inv" ident(H) "as" simple_intropattern(ipat) :=
  inversion H as ipat; clear H; simplify_eq.
Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

(* We overload the notation with [integer] and [ident] to support
[inv H] and [inv 1], like the regular [inversion] tactic. *)
Tactic Notation "inv" integer(n) "as" simple_intropattern(ipat) :=
  num_tac n ltac:(fun H => inv H as ipat).
Tactic Notation "inv" integer(n) :=
  num_tac n ltac:(fun H => inv H).

(** * The "o" family of tactics equips [pose proof], [destruct], [inversion],
[generalize] and [specialize] with support for "o"pen terms. You can leave
underscores that become evars or subgoals, similar to [refine]. You can suffix
the tactic with [*] (e.g., [opose proof*]) to eliminate all remaining ∀ and →
(i.e., add underscores for the remaining arguments). For [odestruct] and
[oinversion], eliminating all remaining ∀ and → is the default (hence there is
no [*] version). *)

(** The helper [opose_core p tac] takes a uconstr [p] and turns it into a constr
that is passed to [tac]. All underscores inside [p] become evars, and the ones
that are unifiable (i.e, appear in the type of other evars) are shelved.

This is similar to creating a [open_constr], except that we have control over
what does and does not get shelved. Creating a [open_constr] would shelve every
created evar, which is not what we want, and it is hard to avoid since it
happens very early (before we can easily wrap things in [unshelve]). *)
Ltac opose_core p tac :=
  (* The "opose_internal" here is useful for debugging but not helpful for name
  collisions since it gets ignored with name mangling. The [clear] below is what
  ensures we don't get name collisions. *)
  let i := fresh "opose_internal" in
  unshelve (epose _ as i);
    [shelve (*type of [p]*)
    |refine p (* will create the subgoals, and shelve some of them *)
    |(* Now we have [i := t] in the context, let's get the [t] and remove [i]. *)
     let t := eval unfold i in i in
     (* We want to leave the context exactly as we found it, to avoid
     any issues with fresh name generation. So clear [i] before calling
     the user-visible tactic. *)
     clear i;
     tac t];
  (* [tac] might have added more subgoals, making some existing ones
  unifiable, so we need to shelve again. *)
  shelve_unifiable.

(** Turn all leading ∀ and → of [p] into evars (∀-evars will be shelved), and
call [tac] with the term applied with those evars. This fill unfold definitions
to find leading ∀/→.

[_name_guard] is an unused argument where you can pass anything you want. If the
argument is an intro pattern, those will be taken into account by the [fresh]
that is inside this tactic, avoiding name collisions that can otherwise arise.
This is a work-around for https://github.com/coq/coq/issues/18109. *)
Ltac ospecialize_foralls p _name_guard tac :=
  let T := type of p in
  lazymatch eval hnf in T with
  | ?T1 → ?T2 =>
    (* This is the [fresh] where the presence of [_name_guard] matters.
    Note that the "opose_internal" is nice but not sufficient because
    it gets ignored when name mangling is enabled. *)
    let pT1 := fresh "opose_internal" in
    assert T1 as pT1; [| ospecialize_foralls (p pT1) _name_guard tac; clear pT1]
  | ∀ x : ?T1, _ =>
    let e := mk_evar T1 in
    ospecialize_foralls (p e) _name_guard tac
  | ?T1 => tac p
  end.

Ltac opose_specialize_foralls_core p _name_guard tac :=
  opose_core p ltac:(fun p => ospecialize_foralls p _name_guard tac).

Tactic Notation "opose" "proof" uconstr(p) "as" simple_intropattern(pat) :=
  opose_core p ltac:(fun p => pose proof p as pat).
Tactic Notation "opose" "proof" "*" uconstr(p) "as" simple_intropattern(pat) :=
  opose_specialize_foralls_core p pat ltac:(fun p => pose proof p as pat).

Tactic Notation "opose" "proof" uconstr(p) := opose proof p as ?.
Tactic Notation "opose" "proof" "*" uconstr(p) := opose proof* p as ?.

Tactic Notation "ogeneralize" uconstr(p) :=
  opose_core p ltac:(fun p => generalize p).
Tactic Notation "ogeneralize" "*" uconstr(p) :=
  opose_specialize_foralls_core p () ltac:(fun p => generalize p).

(** Similar to [edestruct], [odestruct] will never clear the destructed
variable. *)
(** No [*] versions for [odestruct] and [oinversion]: we always specialize all
foralls and implications; otherwise it does not make sense to destruct/invert.
We also do not support [eqn:EQ]; this would not make sense for most users of
this tactic since the term being destructed is [some_lemma ?evar ?proofterm]. *)
Tactic Notation "odestruct" uconstr(p) :=
  opose_specialize_foralls_core p () ltac:(fun p => destruct p).
Tactic Notation "odestruct" uconstr(p) "as" simple_intropattern(pat) :=
  opose_specialize_foralls_core p pat ltac:(fun p => destruct p as pat).

Tactic Notation "oinversion" uconstr(p) "as" simple_intropattern(pat) :=
  opose_specialize_foralls_core p pat ltac:(fun p =>
    (* We have to create a temporary as [inversion] does not support
    general terms; then we clear the temporary. *)
    let Hp := fresh in pose proof p as Hp; inversion Hp as pat; clear Hp).
Tactic Notation "oinversion" uconstr(p) :=
  opose_specialize_foralls_core p () ltac:(fun p =>
    let Hp := fresh in pose proof p as Hp; inversion Hp; clear Hp).

Tactic Notation "oinv" uconstr(p) "as" simple_intropattern(pat) :=
  opose_specialize_foralls_core p pat ltac:(fun p =>
    (* If it is a variable we want to call [inv] on it directly
    so that it gets cleared. *)
    tryif is_var p then
      inv p as pat
    else
      (* No need to [clear Hp]; [inv] does that. *)
      let Hp := fresh in pose proof p as Hp; inv Hp as pat).
Tactic Notation "oinv" uconstr(p) :=
  opose_specialize_foralls_core p () ltac:(fun p =>
    tryif is_var p then
      inv p
    else
      let Hp := fresh in pose proof p as Hp; inv Hp).

(* As above, we overload the notation with [integer] and [ident] to support
[oinv 1], like the regular [inversion] tactic. *)
Tactic Notation "oinv" integer(n) "as" simple_intropattern(ipat) :=
  num_tac n ltac:(fun H => oinv H as ipat).
Tactic Notation "oinv" integer(n) :=
  num_tac n ltac:(fun H => oinv H).

(** Helper for [ospecialize]: call [tac] with the name of the head term *if*
that term is a variable.

Written in CPS to get around weird thunking limitations. *)
Ltac ospecialize_ident_head_of t tac :=
  let h := get_head t in
  tryif is_var h then tac h else
    fail "ospecialize can only specialize a local hypothesis;"
         "use opose proof instead".

Tactic Notation "ospecialize" uconstr(p) :=
  (* Unfortunately there does not seem to be a way to reuse [specialize] here,
  so we need to re-implement the logic for reusing the name. *)
  opose_core p ltac:(fun p =>
    ospecialize_ident_head_of p ltac:(fun H =>
      (* The term of [p] (but not its type) can refer to [H], so we need to use
      a temporary [H'] here to hold the type of [p] before we can clear [H]. *)
      let H' := fresh in
      pose proof p as H'; clear H; rename H' into H
  )).
Tactic Notation "ospecialize" "*" uconstr(p) :=
  opose_specialize_foralls_core p () ltac:(fun p =>
    ospecialize_ident_head_of p ltac:(fun H =>
      (* The term of [p] (but not its type) can refer to [H], so we need to use
      a temporary [H'] here to hold the type of [p] before we can clear [H]. *)
      let H' := fresh in
      pose proof p as H'; clear H; rename H' into H
  )).

(** The block definitions are taken from [Coq.Program.Equality] and can be used
by tactics to separate their goal from hypotheses they generalize over. *)
Definition block {A : Type} (a : A) := a.

Ltac block_goal := match goal with [ |- ?T ] => change (block T) end.
Ltac unblock_goal := unfold block in *.

(** [learn_hyp p as H] and [learn_hyp p], where [p] is a proof of [P],
add [P] to the context and fail if [P] already exists in the context.
This is a simple form of the learning pattern. These tactics are
inspired by [Program.Tactics.add_hypothesis]. *)
Tactic Notation "learn_hyp" constr(p) "as" ident(H') :=
  let P := type of p in
  match goal with
  | H : P |- _ => fail 1
  | _ => pose proof p as H'
  end.
Tactic Notation "learn_hyp" constr(p) :=
  let H := fresh in learn_hyp p as H.

(** The tactic [select pat tac] finds the last (i.e., bottommost) hypothesis
matching [pat] and passes it to the continuation [tac]. Its main advantage over
using [match goal with ] directly is that it is shorter. If [pat] matches
multiple hypotheses and [tac] fails, then [select tac] will not backtrack on
subsequent matching hypotheses.

The tactic [select] is written in CPS and does not return the name of the
hypothesis due to limitations in the Ltac1 tactic runtime (see
https://gitter.im/coq/coq?at=5e96c82f85b01628f04bbb89). *)
Tactic Notation "select" open_constr(pat) tactic3(tac) :=
  lazymatch goal with
  (** Before running [tac] on the hypothesis [H] we must first unify the
      pattern [pat] with the term it matched against. This forces every evar
      coming from [pat] (and in particular from the holes [_] it contains and
      from the implicit arguments it uses) to be instantiated. If we do not do
      so then shelved goals are produced for every such evar. *)
  | H : pat |- _ => let T := (type of H) in unify T pat; tac H
  end.

(** We provide [select] variants of some widely used tactics. *)

(** [select_revert] reverts the first hypothesis matching [pat]. *)
Tactic Notation "revert" "select" open_constr(pat) := select pat (fun H => revert H).

Tactic Notation "rename" "select" open_constr(pat) "into" ident(name) :=
  select pat (fun H => rename H into name).

Tactic Notation "destruct" "select" open_constr(pat) :=
  select pat (fun H => destruct H).
Tactic Notation "destruct" "select" open_constr(pat) "as" simple_intropattern(ipat) :=
  select pat (fun H => destruct H as ipat).

Tactic Notation "inversion" "select" open_constr(pat) :=
  select pat (fun H => inversion H).
Tactic Notation "inversion" "select" open_constr(pat) "as" simple_intropattern(ipat) :=
  select pat (fun H => inversion H as ipat).
Tactic Notation "inv" "select" open_constr(pat) :=
  select pat (fun H => inv H).
Tactic Notation "inv" "select" open_constr(pat) "as" simple_intropattern(ipat) :=
  select pat (fun H => inv H as ipat).

(** The tactic [is_closed_term t] succeeds if [t] is a closed term and fails otherwise.
By closed we mean that [t] does not depend on any variable bound in the context.
axioms are considered closed terms by this tactic (but Section
variables are not). A function application is considered closed if the
function and the argument are closed, without considering the body of
the function (or whether it is opaque or not). This tactic is useful
for example to decide whether to call [vm_compute] on [t].

This trick was originally suggested by Jason Gross:
https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Check.20that.20a.20term.20is.20closed.20in.20Ltac/near/240885618
*)
Ltac is_closed_term t :=
  first [
      (** We use the [assert_succeeds] sandbox to be able to freely
      change the context. *)
      assert_succeeds (
          (** Make sure that the goal only contains [t]. (We use
          [const False t] instead of [let x := t in False] as the
          let-binding in the latter would be unfolded by the [unfold]
          later.) *)
          exfalso; change_no_check (const False t);
          (** Clear all hypotheses. *)
          repeat match goal with H : _ |- _ => try unfold H in *; clear H end;
          (** If there are still hypotheses left, [t] is not closed. *)
          lazymatch goal with H : _ |- _ => fail | _ => idtac end
        ) |
      fail 1 "The term" t "is not closed"
    ].

(** Coq's [firstorder] tactic fails or loops on rather small goals already. In
particular, on those generated by the tactic [unfold_elem_ofs] which is used
to solve propositions on sets. The [naive_solver] tactic implements an
ad-hoc and incomplete [firstorder]-like solver using Ltac's backtracking
mechanism. The tactic suffers from the following limitations:
- It might leave unresolved evars as Ltac provides no way to detect that.
- To avoid the tactic becoming too slow, we allow a universally quantified
  hypothesis to be instantiated only once during each search path.
- It does not perform backtracking on instantiation of universally quantified
  assumptions.

We use a counter to make the search breath first. Breath first search ensures
that a minimal number of hypotheses is instantiated, and thus reduced the
posibility that an evar remains unresolved.

Despite these limitations, it works much better than Coq's [firstorder] tactic
for the purposes of this development. This tactic either fails or proves the
goal. *)
Lemma forall_and_distr (A : Type) (P Q : A → Prop) :
  (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x).
Proof. firstorder. Qed.

Tactic Notation "naive_solver" tactic(tac) :=
  unfold iff, not in *;
  repeat match goal with
  | H : context [∀ _, _ ∧ _ ] |- _ =>
    repeat setoid_rewrite forall_and_distr in H; revert H
  end;
  let rec go n :=
  repeat match goal with
  (**i solve the goal *)
  | |- _ => fast_done
  (**i intros *)
  | |- ∀ _, _ => intro
  (**i simplification of assumptions *)
  | H : False |- _ => destruct H
  | H : _ ∧ _ |- _ =>
     (* Work around bug https://coq.inria.fr/bugs/show_bug.cgi?id=2901 *)
     let H1 := fresh in let H2 := fresh in
     destruct H as [H1 H2]; try clear H
  | H : ∃ _, _  |- _ =>
     let x := fresh in let Hx := fresh in
     destruct H as [x Hx]; try clear H
  | H : ?P → ?Q, H2 : ?P |- _ => specialize (H H2)
  | H : Is_true (bool_decide _) |- _ => apply (bool_decide_unpack _) in H
  | H : Is_true (_ && _) |- _ => apply andb_True in H; destruct H
  (**i simplify and solve equalities *)
  | |- _ => progress simplify_eq/=
  (**i operations that generate more subgoals *)
  | |- _ ∧ _ => split
  | |- Is_true (bool_decide _) => apply (bool_decide_pack _)
  | |- Is_true (_ && _) => apply andb_True; split
  | H : _ ∨ _ |- _ =>
     let H1 := fresh in destruct H as [H1|H1]; try clear H
  | H : Is_true (_ || _) |- _ =>
     apply orb_True in H; let H1 := fresh in destruct H as [H1|H1]; try clear H
  (**i solve the goal using the user supplied tactic *)
  | |- _ => no_new_unsolved_evars (tac)
  end;
  (**i use recursion to enable backtracking on the following clauses. *)
  match goal with
  (**i instantiation of the conclusion *)
  | |- ∃ x, _ => no_new_unsolved_evars ltac:(eexists; go n)
  | |- _ ∨ _ => first [left; go n | right; go n]
  | |- Is_true (_ || _) => apply orb_True; first [left; go n | right; go n]
  | _ =>
    (**i instantiations of assumptions. *)
    lazymatch n with
    | S ?n' =>
      (**i we give priority to assumptions that fit on the conclusion. *)
      match goal with
      | H : _ → _ |- _ =>
        is_non_dependent H;
        no_new_unsolved_evars
          ltac:(first [eapply H | opose proof* H]; clear H; go n')
      end
    end
  end
  in iter (fun n' => go n') (eval compute in (seq 1 6)).
Tactic Notation "naive_solver" := naive_solver eauto.
