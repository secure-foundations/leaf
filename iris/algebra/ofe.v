From iris.prelude Require Export prelude.
From iris.prelude Require Import options.
Set Primitive Projections.

(** This files defines (a shallow embedding of) the category of OFEs:
    Complete ordered families of equivalences. This is a cartesian closed
    category, and mathematically speaking, the entire development lives
    in this category. However, we will generally prefer to work with raw
    Coq functions plus some registered Proper instances for non-expansiveness.
    This makes writing such functions much easier. It turns out that it many
    cases, we do not even need non-expansiveness.
*)

(** Unbundled version *)
Class Dist A := dist : nat → relation A.
Global Hint Mode Dist ! : typeclass_instances.
Global Instance: Params (@dist) 3 := {}.
Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation "x ≡{ n }@{ A }≡ y" := (dist (A:=A) n x y)
  (at level 70, n at next level, only parsing).
Notation "(≡{ n }≡)" := (dist n) (only parsing).
Notation "(≡{ n }@{ A }≡)" := (dist (A:=A) n) (only parsing).
Notation "( x ≡{ n }≡.)" := (dist n x) (only parsing).
Notation "(.≡{ n }≡ y )" := (λ x, x ≡{n}≡ y) (only parsing).

Global Hint Extern 0 (_ ≡{_}≡ _) => reflexivity : core.
Global Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption : core.
Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).
Notation NonExpansive2 f := (∀ n, Proper (dist n ==> dist n ==> dist n) f).

Tactic Notation "ofe_subst" ident(x) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?A ?d ?n x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.
Tactic Notation "ofe_subst" :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?A ?d ?n ?x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ ?x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.

Record OfeMixin A `{Equiv A, Dist A} := {
  mixin_equiv_dist (x y : A) : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
  mixin_dist_equivalence n : Equivalence (@dist A _ n);
  mixin_dist_S n (x y : A) : x ≡{S n}≡ y → x ≡{n}≡ y
}.

(** Bundled version *)
Structure ofe := Ofe {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist ofe_car;
  ofe_mixin : OfeMixin ofe_car
}.
Global Arguments Ofe _ {_ _} _.
Add Printing Constructor ofe.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Equiv _) => refine (ofe_equiv _); shelve : typeclass_instances.
Global Hint Extern 0 (Dist _) => refine (ofe_dist _); shelve : typeclass_instances.
Global Arguments ofe_car : simpl never.
Global Arguments ofe_equiv : simpl never.
Global Arguments ofe_dist : simpl never.
Global Arguments ofe_mixin : simpl never.

(** When declaring instances of subclasses of OFE (like CMRAs and unital CMRAs)
we need Coq to *infer* the canonical OFE instance of a given type and take the
mixin out of it. This makes sure we do not use two different OFE instances in
different places (see for example the constructors [Cmra] and [Ucmra] in the
file [cmra.v].)

In order to infer the OFE instance, we use the definition [ofe_mixin_of'] which
is inspired by the [clone] trick in ssreflect. It works as follows, when type
checking [@ofe_mixin_of' A ?Ac id] Coq faces a unification problem:

  ofe_car ?Ac  ~  A

which will resolve [?Ac] to the canonical OFE instance corresponding to [A]. The
definition [@ofe_mixin_of' A ?Ac id] will then provide the corresponding mixin.
Note that type checking of [ofe_mixin_of' A id] will fail when [A] does not have
a canonical OFE instance.

The notation [ofe_mixin_of A] that we define on top of [ofe_mixin_of' A id]
hides the [id] and normalizes the mixin to head normal form. The latter is to
ensure that we do not end up with redundant canonical projections to the mixin,
i.e. them all being of the shape [ofe_mixin_of' A id]. *)
Definition ofe_mixin_of' A {Ac : ofe} (f : Ac → A) : OfeMixin Ac := ofe_mixin Ac.
Notation ofe_mixin_of A :=
  ltac:(let H := eval hnf in (ofe_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section ofe_mixin.
  Context {A : ofe}.
  Implicit Types x y : A.
  Lemma equiv_dist x y : x ≡ y ↔ ∀ n, x ≡{n}≡ y.
  Proof. apply (mixin_equiv_dist _ (ofe_mixin A)). Qed.
  Global Instance dist_equivalence n : Equivalence (@dist A _ n).
  Proof. apply (mixin_dist_equivalence _ (ofe_mixin A)). Qed.
  Lemma dist_S n x y : x ≡{S n}≡ y → x ≡{n}≡ y.
  Proof. apply (mixin_dist_S _ (ofe_mixin A)). Qed.
End ofe_mixin.

Global Hint Extern 1 (_ ≡{_}≡ _) => apply equiv_dist; assumption : core.

(** Discrete OFEs and discrete OFE elements *)
Class Discrete {A : ofe} (x : A) := discrete y : x ≡{0}≡ y → x ≡ y.
Global Arguments discrete {_} _ {_} _ _.
Global Hint Mode Discrete + ! : typeclass_instances.
Global Instance: Params (@Discrete) 1 := {}.

Class OfeDiscrete (A : ofe) := ofe_discrete_discrete (x : A) :> Discrete x.
Global Hint Mode OfeDiscrete ! : typeclass_instances.

(** OFEs with a completion *)
Record chain (A : ofe) := {
  chain_car :> nat → A;
  chain_cauchy n i : n ≤ i → chain_car i ≡{n}≡ chain_car n
}.
Global Arguments chain_car {_} _ _.
Global Arguments chain_cauchy {_} _ _ _ _.

Program Definition chain_map {A B : ofe} (f : A → B)
    `{!NonExpansive f} (c : chain A) : chain B :=
  {| chain_car n := f (c n) |}.
Next Obligation. by intros A B f Hf c n i ?; apply Hf, chain_cauchy. Qed.

Notation Compl A := (chain A%type → A).
Class Cofe (A : ofe) := {
  compl : Compl A;
  conv_compl n c : compl c ≡{n}≡ c n;
}.
Global Arguments compl : simpl never.
Global Hint Mode Cofe ! : typeclass_instances.

Lemma compl_chain_map `{Cofe A, Cofe B} (f : A → B) c `(NonExpansive f) :
  compl (chain_map f c) ≡ f (compl c).
Proof. apply equiv_dist=>n. by rewrite !conv_compl. Qed.

Program Definition chain_const {A : ofe} (a : A) : chain A :=
  {| chain_car n := a |}.
Next Obligation. by intros A a n i _. Qed.

Lemma compl_chain_const {A : ofe} `{!Cofe A} (a : A) :
  compl (chain_const a) ≡ a.
Proof. apply equiv_dist=>n. by rewrite conv_compl. Qed.

(** General properties *)
Section ofe.
  Context {A : ofe}.
  Implicit Types x y : A.
  Global Instance ofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    - by intros x; rewrite equiv_dist.
    - by intros x y; rewrite !equiv_dist.
    - by intros x y z; rewrite !equiv_dist; intros; trans y.
  Qed.
  Global Instance dist_ne n : Proper (dist n ==> dist n ==> iff) (@dist A _ n).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    - by trans x1; [|trans y1].
    - by trans x2; [|trans y2].
  Qed.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (@dist A _ n).
  Proof.
    by move => x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx n) (Hy n).
  Qed.
  Global Instance dist_proper_2 n x : Proper ((≡) ==> iff) (dist n x).
  Proof. by apply dist_proper. Qed.
  Global Instance Discrete_proper : Proper ((≡) ==> iff) (@Discrete A).
  Proof. intros x y Hxy. rewrite /Discrete. by setoid_rewrite Hxy. Qed.

  Lemma dist_le n n' x y : x ≡{n}≡ y → n' ≤ n → x ≡{n'}≡ y.
  Proof. induction 2; eauto using dist_S. Qed.
  Lemma dist_le' n n' x y : n' ≤ n → x ≡{n}≡ y → x ≡{n'}≡ y.
  Proof. intros; eauto using dist_le. Qed.
  (** [ne_proper] and [ne_proper_2] are not instances to improve efficiency of
  type class search during setoid rewriting.
  Local Instances of [NonExpansive{,2}] are hence accompanied by instances of
  [Proper] built using these lemmas. *)
  Lemma ne_proper {B : ofe} (f : A → B) `{!NonExpansive f} :
    Proper ((≡) ==> (≡)) f.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Lemma ne_proper_2 {B C : ofe} (f : A → B → C) `{!NonExpansive2 f} :
    Proper ((≡) ==> (≡) ==> (≡)) f.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
  Qed.

  Lemma conv_compl' `{Cofe A} n (c : chain A) : compl c ≡{n}≡ c (S n).
  Proof.
    transitivity (c n); first by apply conv_compl. symmetry.
    apply chain_cauchy. lia.
  Qed.

  Lemma discrete_iff n (x : A) `{!Discrete x} y : x ≡ y ↔ x ≡{n}≡ y.
  Proof.
    split; intros; auto. apply (discrete _), dist_le with n; auto with lia.
  Qed.
  Lemma discrete_iff_0 n (x : A) `{!Discrete x} y : x ≡{0}≡ y ↔ x ≡{n}≡ y.
  Proof. by rewrite -!discrete_iff. Qed.
End ofe.

(** Contractive functions *)
Definition dist_later `{Dist A} (n : nat) (x y : A) : Prop :=
  match n with 0 => True | S n => x ≡{n}≡ y end.
Global Arguments dist_later _ _ !_ _ _ /.

Global Instance dist_later_equivalence (A : ofe) n : Equivalence (@dist_later A _ n).
Proof. destruct n as [|n]; [by split|]. apply dist_equivalence. Qed.

Lemma dist_dist_later {A : ofe} n (x y : A) : dist n x y → dist_later n x y.
Proof. intros Heq. destruct n; first done. exact: dist_S. Qed.

Lemma dist_later_dist {A : ofe} n (x y : A) : dist_later (S n) x y → dist n x y.
Proof. done. Qed.

(* We don't actually need this lemma (as our tactics deal with this through
   other means), but technically speaking, this is the reason why
   pre-composing a non-expansive function to a contractive function
   preserves contractivity. *)
Lemma ne_dist_later {A B : ofe} (f : A → B) :
  NonExpansive f → ∀ n, Proper (dist_later n ==> dist_later n) f.
Proof. intros Hf [|n]; last exact: Hf. hnf. by intros. Qed.

Notation Contractive f := (∀ n, Proper (dist_later n ==> dist n) f).

Global Instance const_contractive {A B : ofe} (x : A) : Contractive (@const A B x).
Proof. by intros n y1 y2. Qed.

Section contractive.
  Local Set Default Proof Using "Type*".
  Context {A B : ofe} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{0}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.
  Lemma contractive_S n x y : x ≡{n}≡ y → f x ≡{S n}≡ f y.
  Proof. intros. by apply (_ : Contractive f). Qed.

  Global Instance contractive_ne : NonExpansive f | 100.
  Proof. by intros n x y ?; apply dist_S, contractive_S. Qed.
  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. apply (ne_proper _). Qed.
End contractive.

Ltac f_contractive :=
  match goal with
  | |- ?f _ ≡{_}≡ ?f _ => simple apply (_ : Proper (dist_later _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (dist_later _ ==> _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (_ ==> dist_later _ ==> _) f)
  end;
  try match goal with
  | |- @dist_later ?A _ ?n ?x ?y =>
         destruct n as [|n]; [exact I|change (@dist A _ n x y)]
  end;
  try simple apply reflexivity.

Ltac solve_contractive :=
  solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv]).

(** Limit preserving predicates *)
Class LimitPreserving `{!Cofe A} (P : A → Prop) : Prop :=
  limit_preserving (c : chain A) : (∀ n, P (c n)) → P (compl c).
Global Hint Mode LimitPreserving + + ! : typeclass_instances.

Section limit_preserving.
  Context `{Cofe A}.
  (* These are not instances as they will never fire automatically...
     but they can still be helpful in proving things to be limit preserving. *)

  Lemma limit_preserving_ext (P Q : A → Prop) :
    (∀ x, P x ↔ Q x) → LimitPreserving P → LimitPreserving Q.
  Proof. intros HP Hlimit c ?. apply HP, Hlimit=> n; by apply HP. Qed.

  Global Instance limit_preserving_const (P : Prop) : LimitPreserving (λ _ : A, P).
  Proof. intros c HP. apply (HP 0). Qed.

  Lemma limit_preserving_discrete (P : A → Prop) :
    Proper (dist 0 ==> impl) P → LimitPreserving P.
  Proof. intros PH c Hc. by rewrite (conv_compl 0). Qed.

  Lemma limit_preserving_and (P1 P2 : A → Prop) :
    LimitPreserving P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x ∧ P2 x).
  Proof.
    intros Hlim1 Hlim2 c Hc.
    split.
    - apply Hlim1, Hc.
    - apply Hlim2, Hc.
  Qed.

  Lemma limit_preserving_impl (P1 P2 : A → Prop) :
    Proper (dist 0 ==> impl) P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x → P2 x).
  Proof.
    intros Hlim1 Hlim2 c Hc HP1. apply Hlim2=> n; apply Hc.
    eapply Hlim1, HP1. apply dist_le with n; last lia. apply (conv_compl n).
  Qed.

  Lemma limit_preserving_forall {B} (P : B → A → Prop) :
    (∀ y, LimitPreserving (P y)) →
    LimitPreserving (λ x, ∀ y, P y x).
  Proof. intros Hlim c Hc y. by apply Hlim. Qed.

  Lemma limit_preserving_equiv `{!Cofe B} (f g : A → B) :
    NonExpansive f → NonExpansive g → LimitPreserving (λ x, f x ≡ g x).
  Proof.
    intros Hf Hg c Hc. apply equiv_dist=> n.
    by rewrite -!compl_chain_map !conv_compl /= Hc.
  Qed.
End limit_preserving.

(** Fixpoint *)
Program Definition fixpoint_chain {A : ofe} `{Inhabited A} (f : A → A)
  `{!Contractive f} : chain A := {| chain_car i := Nat.iter (S i) f inhabitant |}.
Next Obligation.
  intros A ? f ? n.
  induction n as [|n IH]=> -[|i] //= ?; try lia.
  - apply (contractive_0 f).
  - apply (contractive_S f), IH; auto with lia.
Qed.

Program Definition fixpoint_def `{Cofe A, Inhabited A} (f : A → A)
  `{!Contractive f} : A := compl (fixpoint_chain f).
Definition fixpoint_aux : seal (@fixpoint_def). Proof. by eexists. Qed.
Definition fixpoint := fixpoint_aux.(unseal).
Global Arguments fixpoint {A _ _} f {_}.
Definition fixpoint_eq : @fixpoint = @fixpoint_def := fixpoint_aux.(seal_eq).

Section fixpoint.
  Context `{Cofe A, Inhabited A} (f : A → A) `{!Contractive f}.

  Lemma fixpoint_unfold : fixpoint f ≡ f (fixpoint f).
  Proof.
    apply equiv_dist=>n.
    rewrite fixpoint_eq /fixpoint_def (conv_compl n (fixpoint_chain f)) //.
    induction n as [|n IH]; simpl; eauto using contractive_0, contractive_S.
  Qed.

  Lemma fixpoint_unique (x : A) : x ≡ f x → x ≡ fixpoint f.
  Proof.
    rewrite !equiv_dist=> Hx n. induction n as [|n IH]; simpl in *.
    - rewrite Hx fixpoint_unfold; eauto using contractive_0.
    - rewrite Hx fixpoint_unfold. apply (contractive_S _), IH.
  Qed.

  Lemma fixpoint_ne (g : A → A) `{!Contractive g} n :
    (∀ z, f z ≡{n}≡ g z) → fixpoint f ≡{n}≡ fixpoint g.
  Proof.
    intros Hfg. rewrite fixpoint_eq /fixpoint_def
      (conv_compl n (fixpoint_chain f)) (conv_compl n (fixpoint_chain g)) /=.
    induction n as [|n IH]; simpl in *; [by rewrite !Hfg|].
    rewrite Hfg; apply contractive_S, IH; auto using dist_S.
  Qed.
  Lemma fixpoint_proper (g : A → A) `{!Contractive g} :
    (∀ x, f x ≡ g x) → fixpoint f ≡ fixpoint g.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.

  Lemma fixpoint_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) → (∀ x, P x → P (f x)) →
    LimitPreserving P →
    P (fixpoint f).
  Proof.
    intros ? [x Hx] Hincr Hlim. set (chcar i := Nat.iter (S i) f x).
    assert (Hcauch : ∀ n i : nat, n ≤ i → chcar i ≡{n}≡ chcar n).
    { intros n. rewrite /chcar. induction n as [|n IH]=> -[|i] //=;
        eauto using contractive_0, contractive_S with lia. }
    set (fp2 := compl {| chain_cauchy := Hcauch |}).
    assert (f fp2 ≡ fp2).
    { apply equiv_dist=>n. rewrite /fp2 (conv_compl n) /= /chcar.
      induction n as [|n IH]; simpl; eauto using contractive_0, contractive_S. }
    rewrite -(fixpoint_unique fp2) //.
    apply Hlim=> n /=. by apply Nat_iter_ind.
  Qed.
End fixpoint.


(** Fixpoint of f when f^k is contractive. **)
Definition fixpointK `{Cofe A, Inhabited A} k (f : A → A)
  `{!Contractive (Nat.iter k f)} := fixpoint (Nat.iter k f).

Section fixpointK.
  Local Set Default Proof Using "Type*".
  Context `{Cofe A, Inhabited A} (f : A → A) (k : nat).
  Context {f_contractive : Contractive (Nat.iter k f)} {f_ne : NonExpansive f}.
  (* Note than f_ne is crucial here:  there are functions f such that f^2 is contractive,
     but f is not non-expansive.
     Consider for example f: SPred → SPred (where SPred is "downclosed sets of natural numbers").
     Define f (using informative excluded middle) as follows:
     f(N) = N  (where N is the set of all natural numbers)
     f({0, ..., n}) = {0, ... n-1}  if n is even (so n-1 is at least -1, in which case we return the empty set)
     f({0, ..., n}) = {0, ..., n+2} if n is odd
     In other words, if we consider elements of SPred as ordinals, then we decreaste odd finite
     ordinals by 1 and increase even finite ordinals by 2.
     f is not non-expansive:  Consider f({0}) = ∅ and f({0,1}) = f({0,1,2,3}).
     The arguments are clearly 0-equal, but the results are not.

     Now consider g := f^2. We have
     g(N) = N
     g({0, ..., n}) = {0, ... n+1}  if n is even
     g({0, ..., n}) = {0, ..., n+4} if n is odd
     g is contractive.  All outputs contain 0, so they are all 0-equal.
     Now consider two n-equal inputs. We have to show that the outputs are n+1-equal.
     Either they both do not contain n in which case they have to be fully equal and
     hence so are the results.  Or else they both contain n, so the results will
     both contain n+1, so the results are n+1-equal.
   *)

  Let f_proper : Proper ((≡) ==> (≡)) f := ne_proper f.
  Local Existing Instance f_proper.

  Lemma fixpointK_unfold : fixpointK k f ≡ f (fixpointK k f).
  Proof.
    symmetry. rewrite /fixpointK. apply fixpoint_unique.
    by rewrite -Nat_iter_S_r Nat_iter_S -fixpoint_unfold.
  Qed.

  Lemma fixpointK_unique (x : A) : x ≡ f x → x ≡ fixpointK k f.
  Proof.
    intros Hf. apply fixpoint_unique. clear f_contractive.
    induction k as [|k' IH]=> //=. by rewrite -IH.
  Qed.

  Section fixpointK_ne.
    Context (g : A → A) `{g_contractive : !Contractive (Nat.iter k g)}.
    Context {g_ne : NonExpansive g}.

    Lemma fixpointK_ne n : (∀ z, f z ≡{n}≡ g z) → fixpointK k f ≡{n}≡ fixpointK k g.
    Proof.
      rewrite /fixpointK=> Hfg /=. apply fixpoint_ne=> z.
      clear f_contractive g_contractive.
      induction k as [|k' IH]=> //=. by rewrite IH Hfg.
    Qed.

    Lemma fixpointK_proper : (∀ z, f z ≡ g z) → fixpointK k f ≡ fixpointK k g.
    Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpointK_ne. Qed.
  End fixpointK_ne.

  Lemma fixpointK_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) → (∀ x, P x → P (f x)) →
    LimitPreserving P →
    P (fixpointK k f).
  Proof.
    intros. rewrite /fixpointK. apply fixpoint_ind; eauto.
    intros; apply Nat_iter_ind; auto.
  Qed.
End fixpointK.

(** Mutual fixpoints *)
Section fixpointAB.
  Context `{Cofe A, Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA : A → B → A).
  Context (fB : A → B → B).
  Context {fA_contractive : ∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context {fB_contractive : ∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.

  Local Definition fixpoint_AB (x : A) : B := fixpoint (fB x).
  Local Instance fixpoint_AB_contractive : Contractive fixpoint_AB.
  Proof.
    intros n x x' Hx; rewrite /fixpoint_AB.
    apply fixpoint_ne=> y. by f_contractive.
  Qed.

  Local Definition fixpoint_AA (x : A) : A := fA x (fixpoint_AB x).
  Local Instance fixpoint_AA_contractive : Contractive fixpoint_AA.
  Proof using fA_contractive. solve_contractive. Qed.

  Definition fixpoint_A : A := fixpoint fixpoint_AA.
  Definition fixpoint_B : B := fixpoint_AB fixpoint_A.

  Lemma fixpoint_A_unfold : fA fixpoint_A fixpoint_B ≡ fixpoint_A.
  Proof. by rewrite {2}/fixpoint_A (fixpoint_unfold _). Qed.
  Lemma fixpoint_B_unfold : fB fixpoint_A fixpoint_B ≡ fixpoint_B.
  Proof. by rewrite {2}/fixpoint_B /fixpoint_AB (fixpoint_unfold _). Qed.

  Local Instance: Proper ((≡) ==> (≡) ==> (≡)) fA.
  Proof using fA_contractive.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_S.
  Qed.
  Local Instance: Proper ((≡) ==> (≡) ==> (≡)) fB.
  Proof using fB_contractive.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_S.
  Qed.

  Lemma fixpoint_A_unique p q : fA p q ≡ p → fB p q ≡ q → p ≡ fixpoint_A.
  Proof.
    intros HfA HfB. rewrite -HfA. apply fixpoint_unique. rewrite /fixpoint_AA.
    f_equiv=> //. apply fixpoint_unique. by rewrite HfA HfB.
  Qed.
  Lemma fixpoint_B_unique p q : fA p q ≡ p → fB p q ≡ q → q ≡ fixpoint_B.
  Proof. intros. apply fixpoint_unique. by rewrite -fixpoint_A_unique. Qed.
End fixpointAB.

Section fixpointAB_ne.
  Context `{Cofe A, Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA fA' : A → B → A).
  Context (fB fB' : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA'}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB'}.

  Lemma fixpoint_A_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_A fA fB ≡{n}≡ fixpoint_A fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z.
    rewrite /fixpoint_AA /fixpoint_AB HfA. f_equiv. by apply fixpoint_ne.
  Qed.
  Lemma fixpoint_B_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_B fA fB ≡{n}≡ fixpoint_B fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z. rewrite HfB. f_contractive.
    apply fixpoint_A_ne; auto using dist_S.
  Qed.

  Lemma fixpoint_A_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_A fA fB ≡ fixpoint_A fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_A_ne. Qed.
  Lemma fixpoint_B_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_B fA fB ≡ fixpoint_B fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_B_ne. Qed.
End fixpointAB_ne.

(** Non-expansive function space *)
Record ofe_mor (A B : ofe) : Type := OfeMor {
  ofe_mor_car :> A → B;
  ofe_mor_ne : NonExpansive ofe_mor_car
}.
Global Arguments OfeMor {_ _} _ {_}.
Add Printing Constructor ofe_mor.
Global Existing Instance ofe_mor_ne.

Notation "'λne' x .. y , t" :=
  (@OfeMor _ _ (λ x, .. (@OfeMor _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).

Section ofe_mor.
  Context {A B : ofe}.
  Global Instance ofe_mor_proper (f : ofe_mor A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, ofe_mor_ne. Qed.
  Local Instance ofe_mor_equiv : Equiv (ofe_mor A B) := λ f g, ∀ x, f x ≡ g x.
  Local Instance ofe_mor_dist : Dist (ofe_mor A B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition ofe_mor_ofe_mixin : OfeMixin (ofe_mor A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure ofe_morO := Ofe (ofe_mor A B) ofe_mor_ofe_mixin.

  Program Definition ofe_mor_chain (c : chain ofe_morO)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition ofe_mor_compl `{Cofe B} : Compl ofe_morO := λ c,
    {| ofe_mor_car x := compl (ofe_mor_chain c x) |}.
  Next Obligation.
    intros ? c n x y Hx. by rewrite (conv_compl n (ofe_mor_chain c x))
      (conv_compl n (ofe_mor_chain c y)) /= Hx.
  Qed.
  Global Program Instance ofe_mor_cofe `{Cofe B} : Cofe ofe_morO :=
    {| compl := ofe_mor_compl |}.
  Next Obligation.
    intros ? n c x; simpl.
    by rewrite (conv_compl n (ofe_mor_chain c x)) /=.
  Qed.

  Global Instance ofe_mor_car_ne :
    NonExpansive2 (@ofe_mor_car A B).
  Proof. intros n f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance ofe_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@ofe_mor_car A B) := ne_proper_2 _.
  Lemma ofe_mor_ext (f g : ofe_mor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End ofe_mor.

Global Arguments ofe_morO : clear implicits.
Notation "A -n> B" :=
  (ofe_morO A B) (at level 99, B at level 200, right associativity).
Global Instance ofe_mor_inhabited {A B : ofe} `{Inhabited B} :
  Inhabited (A -n> B) := populate (λne _, inhabitant).

(** Identity and composition and constant function *)
Definition cid {A} : A -n> A := OfeMor id.
Global Instance: Params (@cid) 1 := {}.
Definition cconst {A B : ofe} (x : B) : A -n> B := OfeMor (const x).
Global Instance: Params (@cconst) 2 := {}.

Definition ccompose {A B C}
  (f : B -n> C) (g : A -n> B) : A -n> C := OfeMor (f ∘ g).
Global Instance: Params (@ccompose) 3 := {}.
Infix "◎" := ccompose (at level 40, left associativity).
Global Instance ccompose_ne {A B C} :
  NonExpansive2 (@ccompose A B C).
Proof. intros n ?? Hf g1 g2 Hg x. rewrite /= (Hg x) (Hf (g2 x)) //. Qed.
Global Instance ccompose_proper {A B C} :
  Proper ((≡) ==> (≡) ==> (≡)) (@ccompose A B C).
Proof. apply ne_proper_2; apply _. Qed.

(* Function space maps *)
Definition ofe_mor_map {A A' B B'} (f : A' -n> A) (g : B -n> B')
  (h : A -n> B) : A' -n> B' := g ◎ h ◎ f.
Global Instance ofe_mor_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n ==> dist n) (@ofe_mor_map A A' B B').
Proof. intros ??? ??? ???. by repeat apply ccompose_ne. Qed.

Definition ofe_morO_map {A A' B B'} (f : A' -n> A) (g : B -n> B') :
  (A -n> B) -n> (A' -n>  B') := OfeMor (ofe_mor_map f g).
Global Instance ofe_morO_map_ne {A A' B B'} :
  NonExpansive2 (@ofe_morO_map A A' B B').
Proof.
  intros n f f' Hf g g' Hg ?. rewrite /= /ofe_mor_map.
  by repeat apply ccompose_ne.
Qed.

(** * Unit type *)
Section unit.
  Local Instance unit_dist : Dist unit := λ _ _ _, True.
  Definition unit_ofe_mixin : OfeMixin unit.
  Proof. by repeat split; try exists 0. Qed.
  Canonical Structure unitO : ofe := Ofe unit unit_ofe_mixin.

  Global Program Instance unit_cofe : Cofe unitO := { compl x := () }.
  Next Obligation. by repeat split; try exists 0. Qed.

  Global Instance unit_ofe_discrete : OfeDiscrete unitO.
  Proof. done. Qed.
End unit.

(** * Empty type *)
Section empty.
  Local Instance Empty_set_dist : Dist Empty_set := λ _ _ _, True.
  Definition Empty_set_ofe_mixin : OfeMixin Empty_set.
  Proof. by repeat split; try exists 0. Qed.
  Canonical Structure Empty_setO : ofe := Ofe Empty_set Empty_set_ofe_mixin.

  Global Program Instance Empty_set_cofe : Cofe Empty_setO := { compl x := x 0 }.
  Next Obligation. by repeat split; try exists 0. Qed.

  Global Instance Empty_set_ofe_discrete : OfeDiscrete Empty_setO.
  Proof. done. Qed.
End empty.

(** * Product type *)
Section product.
  Context {A B : ofe}.

  Local Instance prod_dist : Dist (A * B) := λ n, prod_relation (dist n) (dist n).
  Global Instance pair_ne :
    NonExpansive2 (@pair A B) := _.
  Global Instance fst_ne : NonExpansive (@fst A B) := _.
  Global Instance snd_ne : NonExpansive (@snd A B) := _.
  Definition prod_ofe_mixin : OfeMixin (A * B).
  Proof.
    split.
    - intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
      rewrite !equiv_dist; naive_solver.
    - apply _.
    - by intros n [x1 y1] [x2 y2] [??]; split; apply dist_S.
  Qed.
  Canonical Structure prodO : ofe := Ofe (A * B) prod_ofe_mixin.

  Global Program Instance prod_cofe `{Cofe A, Cofe B} : Cofe prodO :=
    { compl c := (compl (chain_map fst c), compl (chain_map snd c)) }.
  Next Obligation.
    intros ?? n c; split.
    - apply (conv_compl n (chain_map fst c)).
    - apply (conv_compl n (chain_map snd c)).
  Qed.

  Global Instance prod_discrete (x : A * B) :
    Discrete (x.1) → Discrete (x.2) → Discrete x.
  Proof. by intros ???[??]; split; apply (discrete _). Qed.
  Global Instance prod_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete prodO.
  Proof. intros ?? [??]; apply _. Qed.
End product.

Global Arguments prodO : clear implicits.
Typeclasses Opaque prod_dist.

Global Instance prod_map_ne {A A' B B' : ofe} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodO_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  prodO A B -n> prodO A' B' := OfeMor (prod_map f g).
Global Instance prodO_map_ne {A A' B B'} :
  NonExpansive2 (@prodO_map A A' B B').
Proof. intros n f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

(** * COFE → OFE Functors *)
Record oFunctor := OFunctor {
  oFunctor_car : ∀ A `{!Cofe A} B `{!Cofe B}, ofe;
  oFunctor_map `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → oFunctor_car A1 B1 -n> oFunctor_car A2 B2;
  oFunctor_map_ne `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    NonExpansive (@oFunctor_map A1 _ A2 _ B1 _ B2 _);
  oFunctor_map_id `{!Cofe A, !Cofe B} (x : oFunctor_car A B) :
    oFunctor_map (cid,cid) x ≡ x;
  oFunctor_map_compose `{!Cofe A1, !Cofe A2, !Cofe A3, !Cofe B1, !Cofe B2, !Cofe B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    oFunctor_map (f◎g, g'◎f') x ≡ oFunctor_map (g,g') (oFunctor_map (f,f') x)
}.
Global Existing Instance oFunctor_map_ne.
Global Instance: Params (@oFunctor_map) 9 := {}.

Declare Scope oFunctor_scope.
Delimit Scope oFunctor_scope with OF.
Bind Scope oFunctor_scope with oFunctor.

Class oFunctorContractive (F : oFunctor) :=
  oFunctor_map_contractive `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :>
    Contractive (@oFunctor_map F A1 _ A2 _ B1 _ B2 _).
Global Hint Mode oFunctorContractive ! : typeclass_instances.

(** Not a coercion due to the [Cofe] type class argument, and to avoid
ambiguous coercion paths, see https://gitlab.mpi-sws.org/iris/iris/issues/240. *)
Definition oFunctor_apply (F: oFunctor) (A: ofe) `{!Cofe A} : ofe :=
  oFunctor_car F A A.

Program Definition oFunctor_oFunctor_compose (F1 F2 : oFunctor)
  `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} : oFunctor := {|
  oFunctor_car A _ B _ := oFunctor_car F1 (oFunctor_car F2 B A) (oFunctor_car F2 A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ 'fg :=
    oFunctor_map F1 (oFunctor_map F2 (fg.2,fg.1),oFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] [??]; simpl in *.
  apply oFunctor_map_ne; split; apply oFunctor_map_ne; by split.
Qed.
Next Obligation.
  intros F1 F2 ? A ? B ? x; simpl in *. rewrite -{2}(oFunctor_map_id F1 x).
  apply equiv_dist=> n. apply oFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_id.
Qed.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -oFunctor_map_compose. apply equiv_dist=> n. apply oFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_compose.
Qed.
Global Instance oFunctor_oFunctor_compose_contractive_1 (F1 F2 : oFunctor)
    `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} :
  oFunctorContractive F1 → oFunctorContractive (oFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_contractive; destruct Hfg; split; simpl in *; apply oFunctor_map_ne; by split.
Qed.
Global Instance oFunctor_oFunctor_compose_contractive_2 (F1 F2 : oFunctor)
    `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} :
  oFunctorContractive F2 → oFunctorContractive (oFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_equiv; split; simpl in *; f_contractive; destruct Hfg; by split.
Qed.

Program Definition constOF (B : ofe) : oFunctor :=
  {| oFunctor_car A1 A2 _ _ := B; oFunctor_map A1 _ A2 _ B1 _ B2 _ f := cid |}.
Solve Obligations with done.
Coercion constOF : ofe >-> oFunctor.

Global Instance constOF_contractive B : oFunctorContractive (constOF B).
Proof. rewrite /oFunctorContractive; apply _. Qed.

Program Definition idOF : oFunctor :=
  {| oFunctor_car A1 _ A2 _ := A2; oFunctor_map A1 _ A2 _ B1 _ B2 _ f := f.2 |}.
Solve Obligations with done.
Notation "∙" := idOF : oFunctor_scope.

Program Definition prodOF (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := prodO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    prodO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???; by apply prodO_map_ne; apply oFunctor_map_ne.
Qed.
Next Obligation. by intros F1 F2 A ? B ? [??]; rewrite /= !oFunctor_map_id. Qed.
Next Obligation.
  intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [??]; simpl.
  by rewrite !oFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodOF F1%OF F2%OF) : oFunctor_scope.

Global Instance prodOF_contractive F1 F2 :
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (prodOF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply prodO_map_ne; apply oFunctor_map_contractive.
Qed.

Program Definition ofe_morOF (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := oFunctor_car F1 B A -n> oFunctor_car F2 A B;
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    ofe_morO_map (oFunctor_map F1 (fg.2, fg.1)) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 ? A2 ? B1 ? B2 ? n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_map_ne; split; by apply Hfg.
Qed.
Next Obligation.
  intros F1 F2 A ? B ? [f ?] ?; simpl. rewrite /= !oFunctor_map_id.
  apply (ne_proper f). apply oFunctor_map_id.
Qed.
Next Obligation.
  intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [h ?] ?; simpl in *.
  rewrite -!oFunctor_map_compose. do 2 apply (ne_proper _). apply oFunctor_map_compose.
Qed.
Notation "F1 -n> F2" := (ofe_morOF F1%OF F2%OF) : oFunctor_scope.

Global Instance ofe_morOF_contractive F1 F2 :
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (ofe_morOF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morO_map_ne; apply oFunctor_map_contractive; destruct n, Hfg; by split.
Qed.

(** * Sum type *)
Section sum.
  Context {A B : ofe}.

  Local Instance sum_dist : Dist (A + B) := λ n, sum_relation (dist n) (dist n).
  Global Instance inl_ne : NonExpansive (@inl A B) := _.
  Global Instance inr_ne : NonExpansive (@inr A B) := _.
  Global Instance inl_ne_inj n : Inj (dist n) (dist n) (@inl A B) := _.
  Global Instance inr_ne_inj n : Inj (dist n) (dist n) (@inr A B) := _.

  Definition sum_ofe_mixin : OfeMixin (A + B).
  Proof.
    split.
    - intros x y; split=> Hx.
      + destruct Hx=> n; constructor; by apply equiv_dist.
      + destruct (Hx 0); constructor; apply equiv_dist=> n; by apply (inj _).
    - apply _.
    - destruct 1; constructor; by apply dist_S.
  Qed.
  Canonical Structure sumO : ofe := Ofe (A + B) sum_ofe_mixin.

  Program Definition inl_chain (c : chain sumO) (a : A) : chain A :=
    {| chain_car n := match c n return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Program Definition inr_chain (c : chain sumO) (b : B) : chain B :=
    {| chain_car n := match c n return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros c b n i ?; simpl. by destruct (chain_cauchy c n i). Qed.

  Definition sum_compl `{Cofe A, Cofe B} : Compl sumO := λ c,
    match c 0 with
    | inl a => inl (compl (inl_chain c a))
    | inr b => inr (compl (inr_chain c b))
    end.
  Global Program Instance sum_cofe `{Cofe A, Cofe B} : Cofe sumO :=
    { compl := sum_compl }.
  Next Obligation.
    intros ?? n c; rewrite /compl /sum_compl.
    feed inversion (chain_cauchy c 0 n); first by auto with lia; constructor.
    - rewrite (conv_compl n (inl_chain c _)) /=. destruct (c n); naive_solver.
    - rewrite (conv_compl n (inr_chain c _)) /=. destruct (c n); naive_solver.
  Qed.

  Global Instance inl_discrete (x : A) : Discrete x → Discrete (inl x).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance inr_discrete (y : B) : Discrete y → Discrete (inr y).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance sum_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete sumO.
  Proof. intros ?? [?|?]; apply _. Qed.
End sum.

Global Arguments sumO : clear implicits.
Typeclasses Opaque sum_dist.

Global Instance sum_map_ne {A A' B B' : ofe} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@sum_map A A' B B').
Proof.
  intros f f' Hf g g' Hg ??; destruct 1; constructor; [by apply Hf|by apply Hg].
Qed.
Definition sumO_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  sumO A B -n> sumO A' B' := OfeMor (sum_map f g).
Global Instance sumO_map_ne {A A' B B'} :
  NonExpansive2 (@sumO_map A A' B B').
Proof. intros n f f' Hf g g' Hg [?|?]; constructor; [apply Hf|apply Hg]. Qed.

Program Definition sumOF (F1 F2 : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := sumO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    sumO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg)
|}.
Next Obligation.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???; by apply sumO_map_ne; apply oFunctor_map_ne.
Qed.
Next Obligation. by intros F1 F2 A ? B ? [?|?]; rewrite /= !oFunctor_map_id. Qed.
Next Obligation.
  intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [?|?]; simpl;
    by rewrite !oFunctor_map_compose.
Qed.
Notation "F1 + F2" := (sumOF F1%OF F2%OF) : oFunctor_scope.

Global Instance sumOF_contractive F1 F2 :
  oFunctorContractive F1 → oFunctorContractive F2 →
  oFunctorContractive (sumOF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply sumO_map_ne; apply oFunctor_map_contractive.
Qed.

(** * Discrete OFEs *)
Section discrete_ofe.
  Context `{Equiv A} (Heq : @Equivalence A (≡)).

  Local Instance discrete_dist : Dist A := λ n x y, x ≡ y.
  Definition discrete_ofe_mixin : OfeMixin A.
  Proof using Type*.
    split.
    - intros x y; split; [done|intros Hn; apply (Hn 0)].
    - done.
    - done.
  Qed.

  Global Instance discrete_ofe_discrete : OfeDiscrete (Ofe A discrete_ofe_mixin).
  Proof. by intros x y. Qed.

  Global Program Instance discrete_cofe : Cofe (Ofe A discrete_ofe_mixin) :=
    { compl c := c 0 }.
  Next Obligation.
    intros n c. rewrite /compl /=;
    symmetry; apply (chain_cauchy c 0 n). lia.
  Qed.
End discrete_ofe.

Notation discreteO A := (Ofe A (discrete_ofe_mixin _)).
(** Force the [Equivalence] proof to be [eq_equivalence] so that it does not
find another one, like [ofe_equivalence], in the case of aliases. See also
https://gitlab.mpi-sws.org/iris/iris/issues/299 *)
Notation leibnizO A := (Ofe A (@discrete_ofe_mixin _ equivL eq_equivalence)).

(** In order to define a discrete CMRA with carrier [A] (in the file [cmra.v])
we need to determine the [Equivalence A] proof that was used to construct the
OFE instance of [A] (note that this proof is not the same as the one we obtain
via [ofe_equivalence]).

We obtain the proof of [Equivalence A] by inferring the canonical OFE mixin
using [ofe_mixin_of A], and then check whether it is indeed a discrete OFE. This
will fail if no OFE, or an OFE other than the discrete OFE, was registered. *)
Notation discrete_ofe_equivalence_of A := ltac:(
  match constr:(ofe_mixin_of A) with
  | discrete_ofe_mixin ?H => exact H
  end) (only parsing).

Global Instance leibnizO_leibniz A : LeibnizEquiv (leibnizO A).
Proof. by intros x y. Qed.

(** * Basic Coq types *)
Canonical Structure boolO := leibnizO bool.
Canonical Structure natO := leibnizO nat.
Canonical Structure positiveO := leibnizO positive.
Canonical Structure NO := leibnizO N.
Canonical Structure ZO := leibnizO Z.

Section prop.
  Local Instance Prop_equiv : Equiv Prop := iff.
  Local Instance Prop_equivalence : Equivalence (≡@{Prop}) := _.
  Canonical Structure PropO := discreteO Prop.
End prop.

(** * Option type *)
Section option.
  Context {A : ofe}.

  Local Instance option_dist : Dist (option A) := λ n, option_Forall2 (dist n).
  Lemma dist_option_Forall2 n mx my : mx ≡{n}≡ my ↔ option_Forall2 (dist n) mx my.
  Proof. done. Qed.

  Definition option_ofe_mixin : OfeMixin (option A).
  Proof.
    split.
    - intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
      intros Hxy; destruct (Hxy 0); constructor; apply equiv_dist.
      by intros n; feed inversion (Hxy n).
    - apply _.
    - destruct 1; constructor; by apply dist_S.
  Qed.
  Canonical Structure optionO := Ofe (option A) option_ofe_mixin.

  Program Definition option_chain (c : chain optionO) (x : A) : chain A :=
    {| chain_car n := default x (c n) |}.
  Next Obligation. intros c x n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Definition option_compl `{Cofe A} : Compl optionO := λ c,
    match c 0 with Some x => Some (compl (option_chain c x)) | None => None end.
  Global Program Instance option_cofe `{Cofe A} : Cofe optionO :=
    { compl := option_compl }.
  Next Obligation.
    intros ? n c; rewrite /compl /option_compl.
    feed inversion (chain_cauchy c 0 n); auto with lia; [].
    constructor. rewrite (conv_compl n (option_chain c _)) /=.
    destruct (c n); naive_solver.
  Qed.

  Global Instance option_ofe_discrete : OfeDiscrete A → OfeDiscrete optionO.
  Proof. destruct 2; constructor; by apply (discrete _). Qed.

  Global Instance Some_ne : NonExpansive (@Some A).
  Proof. by constructor. Qed.
  Global Instance is_Some_ne n : Proper (dist n ==> iff) (@is_Some A).
  Proof. destruct 1; split; eauto. Qed.
  Global Instance Some_dist_inj n : Inj (dist n) (dist n) (@Some A).
  Proof. by inversion_clear 1. Qed.
  Global Instance from_option_ne {B} (R : relation B) n :
    Proper ((dist (A:=A) n ==> R) ==> R ==> dist n ==> R) from_option.
  Proof. destruct 3; simpl; auto. Qed.

  Global Instance None_discrete : Discrete (@None A).
  Proof. inversion_clear 1; constructor. Qed.
  Global Instance Some_discrete x : Discrete x → Discrete (Some x).
  Proof. by intros ?; inversion_clear 1; constructor; apply discrete. Qed.

  Lemma dist_None n mx : mx ≡{n}≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|by intros ->]. Qed.
  Lemma dist_Some_inv_l n mx my x :
    mx ≡{n}≡ my → mx = Some x → ∃ y, my = Some y ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_r n mx my y :
    mx ≡{n}≡ my → my = Some y → ∃ x, mx = Some x ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_l' n my x : Some x ≡{n}≡ my → ∃ x', Some x' = my ∧ x ≡{n}≡ x'.
  Proof. intros ?%(dist_Some_inv_l _ _ _ x); naive_solver. Qed.
  Lemma dist_Some_inv_r' n mx y : mx ≡{n}≡ Some y → ∃ y', mx = Some y' ∧ y ≡{n}≡ y'.
  Proof. intros ?%(dist_Some_inv_r _ _ _ y); naive_solver. Qed.
End option.

Typeclasses Opaque option_dist.
Global Arguments optionO : clear implicits.

Global Instance option_fmap_ne {A B : ofe} n:
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@fmap option _ A B).
Proof. intros f f' Hf ?? []; constructor; auto. Qed.
Global Instance option_mbind_ne {A B : ofe} n:
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@mbind option _ A B).
Proof. destruct 2; simpl; auto. Qed.
Global Instance option_mjoin_ne {A : ofe} n:
  Proper (dist n ==> dist n) (@mjoin option _ A).
Proof. destruct 1 as [?? []|]; simpl; by constructor. Qed.

Lemma fmap_Some_dist {A B : ofe} (f : A → B) (mx : option A) (y : B) n :
  f <$> mx ≡{n}≡ Some y ↔ ∃ x : A, mx = Some x ∧ y ≡{n}≡ f x.
Proof.
  split; [|by intros (x&->&->)].
  intros (?&?%fmap_Some&?)%dist_Some_inv_r'; naive_solver.
Qed.

Definition optionO_map {A B} (f : A -n> B) : optionO A -n> optionO B :=
  OfeMor (fmap f : optionO A → optionO B).
Global Instance optionO_map_ne A B : NonExpansive (@optionO_map A B).
Proof. by intros n f f' Hf []; constructor; apply Hf. Qed.

Program Definition optionOF (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := optionO (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := optionO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply oFunctor_map_compose.
Qed.

Global Instance optionOF_contractive F :
  oFunctorContractive F → oFunctorContractive (optionOF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
    apply optionO_map_ne, oFunctor_map_contractive.
Qed.

(** * Later type *)
(** Note that the projection [later_car] is not non-expansive (see also the
lemma [later_car_anti_contractive] below), so it cannot be used in the logic.
If you need to get a witness out, you should use the lemma [Next_uninj]
instead. *)
Record later (A : Type) : Type := Next { later_car : A }.
Add Printing Constructor later.
Global Arguments Next {_} _.
Global Arguments later_car {_} _.
Global Instance: Params (@Next) 1 := {}.

Section later.
  Context {A : ofe}.
  Local Instance later_equiv : Equiv (later A) := λ x y, later_car x ≡ later_car y.
  Local Instance later_dist : Dist (later A) := λ n x y,
    dist_later n (later_car x) (later_car y).
  Definition later_ofe_mixin : OfeMixin (later A).
  Proof.
    split.
    - intros x y; unfold equiv, later_equiv; rewrite !equiv_dist.
      split.
      + intros Hxy [|n]; [done|apply Hxy].
      + intros Hxy n; apply (Hxy (S n)).
    - split; rewrite /dist /later_dist.
      + by intros [x].
      + by intros [x] [y].
      + by intros [x] [y] [z] ??; trans y.
    - intros [|n] [x] [y] ?; [done|]; rewrite /dist /later_dist; by apply dist_S.
  Qed.
  Canonical Structure laterO : ofe := Ofe (later A) later_ofe_mixin.

  Program Definition later_chain (c : chain laterO) : chain A :=
    {| chain_car n := later_car (c (S n)) |}.
  Next Obligation. intros c n i ?; apply (chain_cauchy c (S n)); lia. Qed.
  Global Program Instance later_cofe `{Cofe A} : Cofe laterO :=
    { compl c := Next (compl (later_chain c)) }.
  Next Obligation.
    intros ? [|n] c; [done|by apply (conv_compl n (later_chain c))].
  Qed.

  Global Instance Next_contractive : Contractive (@Next A).
  Proof. by intros [|n] x y. Qed.
  Global Instance Later_inj n : Inj (dist n) (dist (S n)) (@Next A).
  Proof. by intros x y. Qed.

  Lemma Next_uninj x : ∃ a, x ≡ Next a.
  Proof. by exists (later_car x). Qed.
  Local Instance later_car_anti_contractive n :
    Proper (dist n ==> dist_later n) later_car.
  Proof. move=> [x] [y] /= Hxy. done. Qed.

  (** [f] is contractive iff it can factor into [Next] and a non-expansive
  function. *)
  Lemma contractive_alt {B : ofe} (f : A → B) :
    Contractive f ↔ ∃ g : later A → B, NonExpansive g ∧ ∀ x, f x ≡ g (Next x).
  Proof.
    split.
    - intros Hf. exists (f ∘ later_car); split=> // n x y ?. by f_equiv.
    - intros (g&Hg&Hf) n x y Hxy. rewrite !Hf. by apply Hg.
  Qed.
End later.

Global Arguments laterO : clear implicits.

Definition later_map {A B} (f : A → B) (x : later A) : later B :=
  Next (f (later_car x)).
Global Instance later_map_ne {A B : ofe} (f : A → B) n :
  Proper (dist (pred n) ==> dist (pred n)) f →
  Proper (dist n ==> dist n) (later_map f) | 0.
Proof. destruct n as [|n]; intros Hf [x] [y] ?; do 2 red; simpl; auto. Qed.
Global Instance later_map_proper {A B : ofe} (f : A → B) :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (later_map f).
Proof. solve_proper. Qed.
Lemma later_map_id {A} (x : later A) : later_map id x = x.
Proof. by destruct x. Qed.
Lemma later_map_compose {A B C} (f : A → B) (g : B → C) (x : later A) :
  later_map (g ∘ f) x = later_map g (later_map f x).
Proof. by destruct x. Qed.
Lemma later_map_ext {A B : ofe} (f g : A → B) x :
  (∀ x, f x ≡ g x) → later_map f x ≡ later_map g x.
Proof. destruct x; intros Hf; apply Hf. Qed.
Definition laterO_map {A B} (f : A -n> B) : laterO A -n> laterO B :=
  OfeMor (later_map f).
Global Instance laterO_map_contractive (A B : ofe) : Contractive (@laterO_map A B).
Proof. intros [|n] f g Hf n'; [done|]; apply Hf; lia. Qed.

Program Definition laterOF (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := laterO (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := laterO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n fg fg' ?.
  by apply (contractive_ne laterO_map), oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x; simpl. rewrite -{2}(later_map_id x).
  apply later_map_ext=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl. rewrite -later_map_compose.
  apply later_map_ext=>y; apply oFunctor_map_compose.
Qed.
Notation "▶ F"  := (laterOF F%OF) (at level 20, right associativity) : oFunctor_scope.

Global Instance laterOF_contractive F : oFunctorContractive (laterOF F).
Proof.
  intros A1 ? A2 ? B1 ? B2 ? n fg fg' Hfg. apply laterO_map_contractive.
  destruct n as [|n]; simpl in *; first done. apply oFunctor_map_ne, Hfg.
Qed.

(** * Dependently-typed functions over a discrete domain *)
(** This separate notion is useful whenever we need dependent functions, and
whenever we want to avoid the hassle of the bundled non-expansive function type.

Note that non-dependent functions over a discrete domain, [A -d> B] (following
the notation we introduce below) are non-expansive if they are
[Proper ((≡) ==> (≡))]. In other words, since the domain is discrete,
non-expansiveness and respecting [(≡)] are the same. If the domain is moreover
Leibniz ([LeibnizEquiv A]), we get both for free.

We make [discrete_fun] a definition so that we can register it as a canonical
structure.  We do not bundle the [Proper] proof to keep [discrete_fun] easier to
use. It turns out all the desired OFE and functorial properties do not rely on
this [Proper] instance. *)
Definition discrete_fun {A} (B : A → ofe) := ∀ x : A, B x.

Section discrete_fun.
  Context {A : Type} {B : A → ofe}.
  Implicit Types f g : discrete_fun B.

  Local Instance discrete_fun_equiv : Equiv (discrete_fun B) := λ f g, ∀ x, f x ≡ g x.
  Local Instance discrete_fun_dist : Dist (discrete_fun B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition discrete_fun_ofe_mixin : OfeMixin (discrete_fun B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure discrete_funO := Ofe (discrete_fun B) discrete_fun_ofe_mixin.

  Program Definition discrete_fun_chain `(c : chain discrete_funO)
    (x : A) : chain (B x) := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Global Program Instance discrete_fun_cofe `{∀ x, Cofe (B x)} : Cofe discrete_funO :=
    { compl c x := compl (discrete_fun_chain c x) }.
  Next Obligation. intros ? n c x. apply (conv_compl n (discrete_fun_chain c x)). Qed.

  Global Instance discrete_fun_inhabited `{∀ x, Inhabited (B x)} : Inhabited discrete_funO :=
    populate (λ _, inhabitant).
  Global Instance discrete_fun_lookup_discrete `{EqDecision A} f x :
    Discrete f → Discrete (f x).
  Proof.
    intros Hf y ?.
    set (g x' := if decide (x = x') is left H then eq_rect _ B y _ H else f x').
    trans (g x).
    { apply Hf=> x'. unfold g. by destruct (decide _) as [[]|]. }
    unfold g. destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
End discrete_fun.

Global Arguments discrete_funO {_} _.
Notation "A -d> B" :=
  (@discrete_funO A (λ _, B)) (at level 99, B at level 200, right associativity).

Definition discrete_fun_map {A} {B1 B2 : A → ofe} (f : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) : discrete_fun B2 := λ x, f _ (g x).

Lemma discrete_fun_map_ext {A} {B1 B2 : A → ofe} (f1 f2 : ∀ x, B1 x → B2 x)
  (g : discrete_fun B1) :
  (∀ x, f1 x (g x) ≡ f2 x (g x)) → discrete_fun_map f1 g ≡ discrete_fun_map f2 g.
Proof. done. Qed.
Lemma discrete_fun_map_id {A} {B : A → ofe} (g : discrete_fun B) :
  discrete_fun_map (λ _, id) g = g.
Proof. done. Qed.
Lemma discrete_fun_map_compose {A} {B1 B2 B3 : A → ofe}
    (f1 : ∀ x, B1 x → B2 x) (f2 : ∀ x, B2 x → B3 x) (g : discrete_fun B1) :
  discrete_fun_map (λ x, f2 x ∘ f1 x) g = discrete_fun_map f2 (discrete_fun_map f1 g).
Proof. done. Qed.

Global Instance discrete_fun_map_ne {A} {B1 B2 : A → ofe} (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (discrete_fun_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /discrete_fun_map (Hy x). Qed.

Definition discrete_funO_map {A} {B1 B2 : A → ofe} (f : discrete_fun (λ x, B1 x -n> B2 x)) :
  discrete_funO B1 -n> discrete_funO B2 := OfeMor (discrete_fun_map f).
Global Instance discrete_funO_map_ne {A} {B1 B2 : A → ofe} :
  NonExpansive (@discrete_funO_map A B1 B2).
Proof. intros n f1 f2 Hf g x; apply Hf. Qed.

Program Definition discrete_funOF {C} (F : C → oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := discrete_funO (λ c, oFunctor_car (F c) A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := discrete_funO_map (λ c, oFunctor_map (F c) fg)
|}.
Next Obligation.
  intros C F A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=>?; apply oFunctor_map_ne.
Qed.
Next Obligation.
  intros C F A ? B ? g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros C F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f1 f2 f1' f2' g.
  rewrite /= -discrete_fun_map_compose.
  apply discrete_fun_map_ext=>y; apply oFunctor_map_compose.
Qed.

Notation "T -d> F" := (@discrete_funOF T%type (λ _, F%OF)) : oFunctor_scope.

Global Instance discrete_funOF_contractive {C} (F : C → oFunctor) :
  (∀ c, oFunctorContractive (F c)) → oFunctorContractive (discrete_funOF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=>c; apply oFunctor_map_contractive.
Qed.

(** * Constructing isomorphic OFEs *)
Lemma iso_ofe_mixin {A : ofe} {B : Type} `{!Equiv B, !Dist B} (g : B → A)
  (g_equiv : ∀ y1 y2, y1 ≡ y2 ↔ g y1 ≡ g y2)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2) : OfeMixin B.
Proof.
  split.
  - intros y1 y2. rewrite g_equiv. setoid_rewrite g_dist. apply equiv_dist.
  - split.
    + intros y. by apply g_dist.
    + intros y1 y2. by rewrite !g_dist.
    + intros y1 y2 y3. rewrite !g_dist. intros ??; etrans; eauto.
  - intros n y1 y2. rewrite !g_dist. apply dist_S.
Qed.

Section iso_cofe_subtype.
  Context {A B : ofe} `{Cofe A} (P : A → Prop) (f : ∀ x, P x → B) (g : B → A).
  Context (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2).
  Let Hgne : NonExpansive g.
  Proof. intros n y1 y2. apply g_dist. Qed.
  Local Existing Instance Hgne.
  Context (gf : ∀ x Hx, g (f x Hx) ≡ x).
  Context (Hlimit : ∀ c : chain B, P (compl (chain_map g c))).
  Program Definition iso_cofe_subtype : Cofe B :=
    {| compl c := f (compl (chain_map g c)) _ |}.
  Next Obligation. apply Hlimit. Qed.
  Next Obligation.
    intros n c; simpl. apply g_dist. by rewrite gf conv_compl.
  Qed.
End iso_cofe_subtype.

Lemma iso_cofe_subtype' {A B : ofe} `{Cofe A}
  (P : A → Prop) (f : ∀ x, P x → B) (g : B → A)
  (Pg : ∀ y, P (g y))
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x Hx, g (f x Hx) ≡ x)
  (Hlimit : LimitPreserving P) : Cofe B.
Proof. apply: (iso_cofe_subtype P f g)=> // c. apply Hlimit=> ?; apply Pg. Qed.

Definition iso_cofe {A B : ofe} `{Cofe A} (f : A → B) (g : B → A)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x, g (f x) ≡ x) : Cofe B.
Proof. by apply (iso_cofe_subtype (λ _, True) (λ x _, f x) g). Qed.

(** * Sigma type *)
Section sigma.
  Context {A : ofe} {P : A → Prop}.
  Implicit Types x : sig P.

  (* TODO: Find a better place for this Equiv instance. It also
     should not depend on A being an OFE. *)
  Local Instance sig_equiv : Equiv (sig P) := λ x1 x2, `x1 ≡ `x2.
  Local Instance sig_dist : Dist (sig P) := λ n x1 x2, `x1 ≡{n}≡ `x2.

  Definition sig_equiv_alt x y : x ≡ y ↔ `x ≡ `y := reflexivity _.
  Definition sig_dist_alt n x y : x ≡{n}≡ y ↔ `x ≡{n}≡ `y := reflexivity _.

  Lemma exist_ne n a1 a2 (H1 : P a1) (H2 : P a2) :
    a1 ≡{n}≡ a2 → a1 ↾ H1 ≡{n}≡ a2 ↾ H2.
  Proof. done. Qed.

  Global Instance proj1_sig_ne : NonExpansive (@proj1_sig _ P).
  Proof. by intros n [a Ha] [b Hb] ?. Qed.
  Definition sig_ofe_mixin : OfeMixin (sig P).
  Proof. by apply (iso_ofe_mixin proj1_sig). Qed.
  Canonical Structure sigO : ofe := Ofe (sig P) sig_ofe_mixin.

  Global Instance sig_cofe `{Cofe A, !LimitPreserving P} : Cofe sigO.
  Proof. apply (iso_cofe_subtype' P (exist P) proj1_sig)=> //. by intros []. Qed.

  Global Instance sig_discrete (x : sig P) :  Discrete (`x) → Discrete x.
  Proof. intros ? y. rewrite sig_dist_alt sig_equiv_alt. apply (discrete _). Qed.
  Global Instance sig_ofe_discrete : OfeDiscrete A → OfeDiscrete sigO.
  Proof. intros ??. apply _. Qed.
End sigma.

Global Arguments sigO {_} _.

(** * SigmaT type *)
(** Ofe for [sigT]. The first component must be discrete and use Leibniz
equality, while the second component might be any OFE. *)
Section sigT.
  Import EqNotations.

  Context {A : Type} {P : A → ofe}.
  Implicit Types x : sigT P.

  (**
    The distance for [{ a : A & P }] uses Leibniz equality on [A] to
    transport the second components to the same type,
    and then step-indexed distance on the second component.
    Unlike in the topos of trees, with (C)OFEs we cannot use step-indexed equality
    on the first component.
  *)
  Local Instance sigT_dist : Dist (sigT P) := λ n x1 x2,
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡{n}≡ projT2 x2.

  (**
    Usually we'd give a direct definition, and show it equivalent to
    [∀ n, x1 ≡{n}≡ x2] when proving the [equiv_dist] OFE axiom.
    But here the equivalence requires UIP — see [sigT_equiv_eq_alt].
    By defining [equiv] in terms of [dist], we can define an OFE
    without assuming UIP, at the cost of complex reasoning on [equiv].
  *)
  Local Instance sigT_equiv : Equiv (sigT P) := λ x1 x2,
    ∀ n, x1 ≡{n}≡ x2.

  (** Unfolding lemmas.
      Written with [↔] not [=] to avoid https://github.com/coq/coq/issues/3814. *)
  Definition sigT_equiv_eq x1 x2 : (x1 ≡ x2) ↔ ∀ n, x1 ≡{n}≡ x2 :=
      reflexivity _.

  Definition sigT_dist_eq x1 x2 n : (x1 ≡{n}≡ x2) ↔
    ∃ Heq : projT1 x1 = projT1 x2, (rew Heq in projT2 x1) ≡{n}≡ projT2 x2 :=
      reflexivity _.

  Definition sigT_dist_proj1 n {x y} : x ≡{n}≡ y → projT1 x = projT1 y := proj1_ex.
  Definition sigT_equiv_proj1 {x y} : x ≡ y → projT1 x = projT1 y := λ H, proj1_ex (H 0).

  Definition sigT_ofe_mixin : OfeMixin (sigT P).
  Proof.
    split => // n.
    - split; hnf; setoid_rewrite sigT_dist_eq.
      + intros. by exists eq_refl.
      + move => [xa x] [ya y] /=. destruct 1 as [-> Heq].
        by exists eq_refl.
      + move => [xa x] [ya y] [za z] /=.
        destruct 1 as [-> Heq1].
        destruct 1 as [-> Heq2]. exists eq_refl => /=. by trans y.
    - setoid_rewrite sigT_dist_eq.
      move => [xa x] [ya y] /=. destruct 1 as [-> Heq].
      exists eq_refl. exact: dist_S.
  Qed.

  Canonical Structure sigTO : ofe := Ofe (sigT P) sigT_ofe_mixin.

  Lemma sigT_equiv_eq_alt `{!∀ a b : A, ProofIrrel (a = b)} x1 x2 :
    x1 ≡ x2 ↔
    ∃ Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 ≡ projT2 x2.
  Proof.
    setoid_rewrite equiv_dist; setoid_rewrite sigT_dist_eq; split => Heq.
    - move: (Heq 0) => [H0eq1 _].
      exists H0eq1 => n. move: (Heq n) => [] Hneq1.
      by rewrite (proof_irrel H0eq1 Hneq1).
    - move: Heq => [Heq1 Heqn2] n. by exists Heq1.
  Qed.

  (** [projT1] is non-expansive and proper. *)
  Global Instance projT1_ne : NonExpansive (projT1 : sigTO → leibnizO A).
  Proof. solve_proper. Qed.

  Global Instance projT1_proper : Proper ((≡) ==> (≡)) (projT1 : sigTO → leibnizO A).
  Proof. apply ne_proper, projT1_ne. Qed.

  (** [projT2] is "non-expansive"; the properness lemma [projT2_ne] requires UIP. *)
  Lemma projT2_ne n (x1 x2 : sigTO) (Heq : x1 ≡{n}≡ x2) :
    rew (sigT_dist_proj1 n Heq) in projT2 x1 ≡{n}≡ projT2 x2.
  Proof. by destruct Heq. Qed.

  Lemma projT2_proper `{!∀ a b : A, ProofIrrel (a = b)} (x1 x2 : sigTO) (Heqs : x1 ≡ x2):
    rew (sigT_equiv_proj1 Heqs) in projT2 x1 ≡ projT2 x2.
  Proof.
    move: x1 x2 Heqs => [a1 x1] [a2 x2] Heqs.
    case: (proj1 (sigT_equiv_eq_alt _ _) Heqs) => /=. intros ->.
    rewrite (proof_irrel (sigT_equiv_proj1 Heqs) eq_refl) /=. done.
  Qed.

  (** [existT] is "non-expansive" — general, dependently-typed statement. *)
  Lemma existT_ne n {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡{n}≡ v2) →
      existT i1 v1 ≡{n}≡ existT i2 v2.
  Proof. intros ->; simpl. exists eq_refl => /=. done. Qed.

  Lemma existT_proper {i1 i2} {v1 : P i1} {v2 : P i2} :
    ∀ (Heq : i1 = i2), (rew f_equal P Heq in v1 ≡ v2) →
      existT i1 v1 ≡ existT i2 v2.
  Proof. intros Heq Heqv n. apply (existT_ne n Heq), equiv_dist, Heqv. Qed.

  (** [existT] is "non-expansive" — non-dependently-typed version. *)
  Global Instance existT_ne_2 a : NonExpansive (@existT A P a).
  Proof. move => ??? Heq. apply (existT_ne _ eq_refl Heq). Qed.

  Global Instance existT_proper_2 a : Proper ((≡) ==> (≡)) (@existT A P a).
  Proof. apply ne_proper, _. Qed.

  Implicit Types (c : chain sigTO).

  Global Instance sigT_discrete x : Discrete (projT2 x) → Discrete x.
  Proof.
    move: x => [xa x] ? [ya y] [] /=; intros -> => /= Hxy n.
    exists eq_refl => /=. apply equiv_dist, (discrete _), Hxy.
  Qed.

  Global Instance sigT_ofe_discrete : (∀ a, OfeDiscrete (P a)) → OfeDiscrete sigTO.
  Proof. intros ??. apply _. Qed.

  Lemma sigT_chain_const_proj1 c n : projT1 (c n) = projT1 (c 0).
  Proof. refine (sigT_dist_proj1 _ (chain_cauchy c 0 n _)). lia. Qed.

  (* For this COFE construction we need UIP (Uniqueness of Identity Proofs)
    on [A] (i.e. [∀ x y : A, ProofIrrel (x = y)]. UIP is most commonly obtained
    from decidable equality (by Hedberg’s theorem, see
    [stdpp.proof_irrel.eq_pi]). *)
  Section cofe.
    Context `{!∀ a b : A, ProofIrrel (a = b)} `{!∀ a, Cofe (P a)}.

    Program Definition chain_map_snd c : chain (P (projT1 (c 0))) :=
      {| chain_car n := rew (sigT_chain_const_proj1 c n) in projT2 (c n) |}.
    Next Obligation.
      move => c n i Hle /=.
      (* [Hgoal] is our thesis, up to casts: *)
      case: (chain_cauchy c n i Hle) => [Heqin Hgoal] /=.
      (* Pretty delicate. We have two casts to [projT1 (c 0)].
        We replace those by one cast. *)
      move: (sigT_chain_const_proj1 c i) (sigT_chain_const_proj1 c n)
        => Heqi0 Heqn0.
      (* Rewrite [projT1 (c 0)] to [projT1 (c n)] in goal and [Heqi0]: *)
      destruct Heqn0.
      by rewrite /= (proof_irrel Heqi0 Heqin).
    Qed.

    Definition sigT_compl : Compl sigTO :=
      λ c, existT (projT1 (chain_car c 0)) (compl (chain_map_snd c)).

    Global Program Instance sigT_cofe : Cofe sigTO := { compl := sigT_compl }.
    Next Obligation.
      intros n c. rewrite /sigT_compl sigT_dist_eq /=.
      exists (symmetry (sigT_chain_const_proj1 c n)).
      (* Our thesis, up to casts: *)
      pose proof (conv_compl n (chain_map_snd c)) as Hgoal.
      move: (compl (chain_map_snd c)) Hgoal => pc0 /=.
      destruct (sigT_chain_const_proj1 c n); simpl. done.
    Qed.
  End cofe.
End sigT.

Global Arguments sigTO {_} _.

Section sigTOF.
  Context {A : Type}.

  Program Definition sigT_map {P1 P2 : A → ofe} :
    discrete_funO (λ a, P1 a -n> P2 a) -n>
    sigTO P1 -n> sigTO P2 :=
    λne f xpx, existT _ (f _ (projT2 xpx)).
  Next Obligation.
    move => ?? f n [x px] [y py] [/= Heq]. destruct Heq; simpl.
    exists eq_refl => /=. by f_equiv.
  Qed.
  Next Obligation.
    move => ?? n f g Heq [x px] /=. exists eq_refl => /=. apply Heq.
  Qed.

  Program Definition sigTOF (F : A → oFunctor) : oFunctor := {|
    oFunctor_car A CA B CB := sigTO (λ a, oFunctor_car (F a) A B);
    oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := sigT_map (λ a, oFunctor_map (F a) fg)
  |}.
  Next Obligation.
    repeat intro. exists eq_refl => /=. solve_proper.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_map_id.
  Qed.
  Next Obligation.
    simpl; intros. apply (existT_proper eq_refl), oFunctor_map_compose.
  Qed.

  Global Instance sigTOF_contractive {F} :
    (∀ a, oFunctorContractive (F a)) → oFunctorContractive (sigTOF F).
  Proof.
    repeat intro. apply sigT_map => a. exact: oFunctor_map_contractive.
  Qed.
End sigTOF.
Global Arguments sigTOF {_} _%OF.

Notation "{ x  &  P }" := (sigTOF (λ x, P%OF)) : oFunctor_scope.
Notation "{ x : A &  P }" := (@sigTOF A%type (λ x, P%OF)) : oFunctor_scope.

(** * Isomorphisms between OFEs *)
Record ofe_iso (A B : ofe) := OfeIso {
  ofe_iso_1 : A -n> B;
  ofe_iso_2 : B -n> A;
  ofe_iso_12 y : ofe_iso_1 (ofe_iso_2 y) ≡ y;
  ofe_iso_21 x : ofe_iso_2 (ofe_iso_1 x) ≡ x;
}.
Global Arguments OfeIso {_ _} _ _ _ _.
Global Arguments ofe_iso_1 {_ _} _.
Global Arguments ofe_iso_2 {_ _} _.
Global Arguments ofe_iso_12 {_ _} _ _.
Global Arguments ofe_iso_21 {_ _} _ _.

Section ofe_iso.
  Context {A B : ofe}.

  Local Instance ofe_iso_equiv : Equiv (ofe_iso A B) := λ I1 I2,
    ofe_iso_1 I1 ≡ ofe_iso_1 I2 ∧ ofe_iso_2 I1 ≡ ofe_iso_2 I2.

  Local Instance ofe_iso_dist : Dist (ofe_iso A B) := λ n I1 I2,
    ofe_iso_1 I1 ≡{n}≡ ofe_iso_1 I2 ∧ ofe_iso_2 I1 ≡{n}≡ ofe_iso_2 I2.

  Global Instance ofe_iso_1_ne : NonExpansive (ofe_iso_1 (A:=A) (B:=B)).
  Proof. by destruct 1. Qed.
  Global Instance ofe_iso_2_ne : NonExpansive (ofe_iso_2 (A:=A) (B:=B)).
  Proof. by destruct 1. Qed.

  Lemma ofe_iso_ofe_mixin : OfeMixin (ofe_iso A B).
  Proof. by apply (iso_ofe_mixin (λ I, (ofe_iso_1 I, ofe_iso_2 I))). Qed.
  Canonical Structure ofe_isoO : ofe := Ofe (ofe_iso A B) ofe_iso_ofe_mixin.

  Global Instance ofe_iso_cofe `{!Cofe A, !Cofe B} : Cofe ofe_isoO.
  Proof.
    apply (iso_cofe_subtype'
      (λ I : prodO (A -n> B) (B -n> A),
        (∀ y, I.1 (I.2 y) ≡ y) ∧ (∀ x, I.2 (I.1 x) ≡ x))
      (λ I HI, OfeIso (I.1) (I.2) (proj1 HI) (proj2 HI))
      (λ I, (ofe_iso_1 I, ofe_iso_2 I))); [by intros []|done|done|].
    apply limit_preserving_and; apply limit_preserving_forall=> ?;
      apply limit_preserving_equiv; first [intros ???; done|solve_proper].
  Qed.
End ofe_iso.

Global Arguments ofe_isoO : clear implicits.

Program Definition iso_ofe_refl {A} : ofe_iso A A := OfeIso cid cid _ _.
Solve Obligations with done.

Definition iso_ofe_sym {A B : ofe} (I : ofe_iso A B) : ofe_iso B A :=
  OfeIso (ofe_iso_2 I) (ofe_iso_1 I) (ofe_iso_21 I) (ofe_iso_12 I).
Global Instance iso_ofe_sym_ne {A B} : NonExpansive (iso_ofe_sym (A:=A) (B:=B)).
Proof. intros n I1 I2 []; split; simpl; by f_equiv. Qed.

Program Definition iso_ofe_trans {A B C}
    (I : ofe_iso A B) (J : ofe_iso B C) : ofe_iso A C :=
  OfeIso (ofe_iso_1 J ◎ ofe_iso_1 I) (ofe_iso_2 I ◎ ofe_iso_2 J) _ _.
Next Obligation. intros A B C I J z; simpl. by rewrite !ofe_iso_12. Qed.
Next Obligation. intros A B C I J z; simpl. by rewrite !ofe_iso_21. Qed.
Global Instance iso_ofe_trans_ne {A B C} : NonExpansive2 (iso_ofe_trans (A:=A) (B:=B) (C:=C)).
Proof. intros n I1 I2 [] J1 J2 []; split; simpl; by f_equiv. Qed.

Program Definition iso_ofe_cong (F : oFunctor) `{!Cofe A, !Cofe B}
    (I : ofe_iso A B) : ofe_iso (oFunctor_apply F A) (oFunctor_apply F B) :=
  OfeIso (oFunctor_map F (ofe_iso_2 I, ofe_iso_1 I))
    (oFunctor_map F (ofe_iso_1 I, ofe_iso_2 I)) _ _.
Next Obligation.
  intros F A ? B ? I x. rewrite -oFunctor_map_compose -{2}(oFunctor_map_id F x).
  apply equiv_dist=> n.
  apply oFunctor_map_ne; split=> ? /=; by rewrite ?ofe_iso_12 ?ofe_iso_21.
Qed.
Next Obligation.
  intros F A ? B ? I y. rewrite -oFunctor_map_compose -{2}(oFunctor_map_id F y).
  apply equiv_dist=> n.
  apply oFunctor_map_ne; split=> ? /=; by rewrite ?ofe_iso_12 ?ofe_iso_21.
Qed.
Global Instance iso_ofe_cong_ne (F : oFunctor) `{!Cofe A, !Cofe B} :
  NonExpansive (iso_ofe_cong F (A:=A) (B:=B)).
Proof. intros n I1 I2 []; split; simpl; by f_equiv. Qed.
Global Instance iso_ofe_cong_contractive (F : oFunctor) `{!Cofe A, !Cofe B} :
  oFunctorContractive F → Contractive (iso_ofe_cong F (A:=A) (B:=B)).
Proof. intros ? n I1 I2 HI; split; simpl; f_contractive; by destruct HI. Qed.
