From stdpp Require Import finite.
From iris.algebra Require Export ofe monoid.
From iris.prelude Require Import options.
Local Set Primitive Projections.

Class PCore (A : Type) := pcore : A → option A.
Global Hint Mode PCore ! : typeclass_instances.
Global Instance: Params (@pcore) 2 := {}.

Class Op (A : Type) := op : A → A → A.
Global Hint Mode Op ! : typeclass_instances.
Global Instance: Params (@op) 2 := {}.
Infix "⋅" := op (at level 50, left associativity) : stdpp_scope.
Notation "(⋅)" := op (only parsing) : stdpp_scope.

(* The inclusion quantifies over [A], not [option A].  This means we do not get
   reflexivity.  However, if we used [option A], the following would no longer
   hold:
     x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2
   If you need the reflexive closure of the inclusion relation, you can use
   [Some a ≼ Some b]. There are various [Some_included] lemmas that help
   deal with propositions of this shape.
*)
Definition included {A} `{!Equiv A, !Op A} (x y : A) := ∃ z, y ≡ x ⋅ z.
Infix "≼" := included (at level 70) : stdpp_scope.
Notation "(≼)" := included (only parsing) : stdpp_scope.
Global Hint Extern 0 (_ ≼ _) => reflexivity : core.
Global Instance: Params (@included) 3 := {}.

(** [opM] is used in some lemma statements where [A] has not yet been shown to
be a CMRA, so we define it directly in terms of [Op]. *)
Definition opM `{!Op A} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := opM (at level 50, left associativity) : stdpp_scope.

Class ValidN (A : Type) := validN : nat → A → Prop.
Global Hint Mode ValidN ! : typeclass_instances.
Global Instance: Params (@validN) 3 := {}.
Notation "✓{ n } x" := (validN n x)
  (at level 20, n at next level, format "✓{ n }  x").

Class Valid (A : Type) := valid : A → Prop.
Global Hint Mode Valid ! : typeclass_instances.
Global Instance: Params (@valid) 2 := {}.
Notation "✓ x" := (valid x) (at level 20) : stdpp_scope.

Definition includedN `{!Dist A, !Op A} (n : nat) (x y : A) := ∃ z, y ≡{n}≡ x ⋅ z.
Notation "x ≼{ n } y" := (includedN n x y)
  (at level 70, n at next level, format "x  ≼{ n }  y") : stdpp_scope.
Global Instance: Params (@includedN) 4 := {}.
Global Hint Extern 0 (_ ≼{_} _) => reflexivity : core.

Section mixin.
  Record CmraMixin A `{!Dist A, !Equiv A, !PCore A, !Op A, !Valid A, !ValidN A} := {
    (* setoids *)
    mixin_cmra_op_ne (x : A) : NonExpansive (op x);
    mixin_cmra_pcore_ne n (x y : A) cx :
      x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy;
    mixin_cmra_validN_ne n : Proper (dist (A := A) n ==> impl) (validN n);
    (* valid *)
    mixin_cmra_valid_validN (x : A) : ✓ x ↔ ∀ n, ✓{n} x;
    mixin_cmra_validN_S n (x : A) : ✓{S n} x → ✓{n} x;
    (* monoid *)
    mixin_cmra_assoc : Assoc (≡@{A}) (⋅);
    mixin_cmra_comm : Comm (≡@{A}) (⋅);
    mixin_cmra_pcore_l (x : A) cx : pcore x = Some cx → cx ⋅ x ≡ x;
    mixin_cmra_pcore_idemp (x : A) cx : pcore x = Some cx → pcore cx ≡ Some cx;
    mixin_cmra_pcore_mono (x y : A) cx :
      x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
    mixin_cmra_validN_op_l n (x y : A) : ✓{n} (x ⋅ y) → ✓{n} x;
    mixin_cmra_extend n (x y1 y2 : A) :
      ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
      { z1 : A & { z2 | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 } }
  }.
End mixin.

(** Bundled version *)
#[projections(primitive=no)] (* FIXME: making this primitive leads to strange
TC resolution failures in view.v *)
Structure cmra := Cmra' {
  cmra_car :> Type;
  cmra_equiv : Equiv cmra_car;
  cmra_dist : Dist cmra_car;
  cmra_pcore : PCore cmra_car;
  cmra_op : Op cmra_car;
  cmra_valid : Valid cmra_car;
  cmra_validN : ValidN cmra_car;
  cmra_ofe_mixin : OfeMixin cmra_car;
  cmra_mixin : CmraMixin cmra_car;
}.
Global Arguments Cmra' _ {_ _ _ _ _ _} _ _.
(* Given [m : CmraMixin A], the notation [Cmra A m] provides a smart
constructor, which uses [ofe_mixin_of A] to infer the canonical OFE mixin of
the type [A], so that it does not have to be given manually. *)
Notation Cmra A m := (Cmra' A (ofe_mixin_of A%type) m) (only parsing).

Global Arguments cmra_car : simpl never.
Global Arguments cmra_equiv : simpl never.
Global Arguments cmra_dist : simpl never.
Global Arguments cmra_pcore : simpl never.
Global Arguments cmra_op : simpl never.
Global Arguments cmra_valid : simpl never.
Global Arguments cmra_validN : simpl never.
Global Arguments cmra_ofe_mixin : simpl never.
Global Arguments cmra_mixin : simpl never.
Add Printing Constructor cmra.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (PCore _) => refine (cmra_pcore _); shelve : typeclass_instances.
Global Hint Extern 0 (Op _) => refine (cmra_op _); shelve : typeclass_instances.
Global Hint Extern 0 (Valid _) => refine (cmra_valid _); shelve : typeclass_instances.
Global Hint Extern 0 (ValidN _) => refine (cmra_validN _); shelve : typeclass_instances.
Coercion cmra_ofeO (A : cmra) : ofe := Ofe A (cmra_ofe_mixin A).
Canonical Structure cmra_ofeO.

(** As explained more thoroughly in iris#539, Coq can run into trouble when
  [cmra] combinators (such as [optionUR]) are stacked and combined with
  coercions like [cmra_ofeO]. To partially address this, we give Coq's
  type-checker some directions for unfolding, with the Strategy command.

  For these structures, we instruct Coq to eagerly _expand_ all projections,
  except for the coercion to type (in this case, [cmra_car]), since that causes
  problem with canonical structure inference. Additionally, we make Coq 
  eagerly expand the coercions that go from one structure to another, like
  [cmra_ofeO] in this case. *)
Global Strategy expand [cmra_ofeO cmra_equiv cmra_dist cmra_pcore cmra_op
                        cmra_valid cmra_validN cmra_ofe_mixin cmra_mixin].

Definition cmra_mixin_of' A {Ac : cmra} (f : Ac → A) : CmraMixin Ac := cmra_mixin Ac.
Notation cmra_mixin_of A :=
  ltac:(let H := eval hnf in (cmra_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section cmra_mixin.
  Context {A : cmra}.
  Implicit Types x y : A.
  Global Instance cmra_op_ne (x : A) : NonExpansive (op x).
  Proof. apply (mixin_cmra_op_ne _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_ne n x y cx :
    x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy.
  Proof. apply (mixin_cmra_pcore_ne _ (cmra_mixin A)). Qed.
  Global Instance cmra_validN_ne n : Proper (dist n ==> impl) (@validN A _ n).
  Proof. apply (mixin_cmra_validN_ne _ (cmra_mixin A)). Qed.
  Lemma cmra_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x.
  Proof. apply (mixin_cmra_valid_validN _ (cmra_mixin A)). Qed.
  Lemma cmra_validN_S n x : ✓{S n} x → ✓{n} x.
  Proof. apply (mixin_cmra_validN_S _ (cmra_mixin A)). Qed.
  Global Instance cmra_assoc : Assoc (≡) (@op A _).
  Proof. apply (mixin_cmra_assoc _ (cmra_mixin A)). Qed.
  Global Instance cmra_comm : Comm (≡) (@op A _).
  Proof. apply (mixin_cmra_comm _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x.
  Proof. apply (mixin_cmra_pcore_l _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx.
  Proof. apply (mixin_cmra_pcore_idemp _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_mono x y cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
  Proof. apply (mixin_cmra_pcore_mono _ (cmra_mixin A)). Qed.
  Lemma cmra_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x.
  Proof. apply (mixin_cmra_validN_op_l _ (cmra_mixin A)). Qed.
  Lemma cmra_extend n x y1 y2 :
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    { z1 : A & { z2 | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 } }.
  Proof. apply (mixin_cmra_extend _ (cmra_mixin A)). Qed.
End cmra_mixin.

(** * CoreId elements *)
Class CoreId {A : cmra} (x : A) := core_id : pcore x ≡ Some x.
Global Arguments core_id {_} _ {_}.
Global Hint Mode CoreId + ! : typeclass_instances.
Global Instance: Params (@CoreId) 1 := {}.

(** * Exclusive elements (i.e., elements that cannot have a frame). *)
Class Exclusive {A : cmra} (x : A) := exclusive0_l y : ✓{0} (x ⋅ y) → False.
Global Arguments exclusive0_l {_} _ {_} _ _.
Global Hint Mode Exclusive + ! : typeclass_instances.
Global Instance: Params (@Exclusive) 1 := {}.

(** * Cancelable elements. *)
Class Cancelable {A : cmra} (x : A) :=
  cancelableN n y z : ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ≡{n}≡ z.
Global Arguments cancelableN {_} _ {_} _ _ _ _.
Global Hint Mode Cancelable + ! : typeclass_instances.
Global Instance: Params (@Cancelable) 1 := {}.

(** * Identity-free elements. *)
Class IdFree {A : cmra} (x : A) :=
  id_free0_r y : ✓{0}x → x ⋅ y ≡{0}≡ x → False.
Global Arguments id_free0_r {_} _ {_} _ _.
Global Hint Mode IdFree + ! : typeclass_instances.
Global Instance: Params (@IdFree) 1 := {}.

(** * CMRAs whose core is total *)
Class CmraTotal (A : cmra) := cmra_total (x : A) : is_Some (pcore x).
Global Hint Mode CmraTotal ! : typeclass_instances.

(** The function [core] returns a dummy when used on CMRAs without total
core. We only ever use this for [CmraTotal] CMRAs, but it is more convenient
to not require that proof to be able to call this function. *)
Definition core {A} `{!PCore A} (x : A) : A := default x (pcore x).
Global Instance: Params (@core) 2 := {}.

(** * CMRAs with a unit element *)
Class Unit (A : Type) := ε : A.
Global Hint Mode Unit ! : typeclass_instances.
Global Arguments ε {_ _}.

Record UcmraMixin A `{!Dist A, !Equiv A, !PCore A, !Op A, !Valid A, !Unit A} := {
  mixin_ucmra_unit_valid : ✓ (ε : A);
  mixin_ucmra_unit_left_id : LeftId (≡@{A}) ε (⋅);
  mixin_ucmra_pcore_unit : pcore ε ≡@{option A} Some ε
}.

#[projections(primitive=no)] (* FIXME: making this primitive leads to strange
TC resolution failures in view.v *)
Structure ucmra := Ucmra' {
  ucmra_car :> Type;
  ucmra_equiv : Equiv ucmra_car;
  ucmra_dist : Dist ucmra_car;
  ucmra_pcore : PCore ucmra_car;
  ucmra_op : Op ucmra_car;
  ucmra_valid : Valid ucmra_car;
  ucmra_validN : ValidN ucmra_car;
  ucmra_unit : Unit ucmra_car;
  ucmra_ofe_mixin : OfeMixin ucmra_car;
  ucmra_cmra_mixin : CmraMixin ucmra_car;
  ucmra_mixin : UcmraMixin ucmra_car;
}.
Global Arguments Ucmra' _ {_ _ _ _ _ _ _} _ _ _.
Notation Ucmra A m :=
  (Ucmra' A (ofe_mixin_of A%type) (cmra_mixin_of A%type) m) (only parsing).
Global Arguments ucmra_car : simpl never.
Global Arguments ucmra_equiv : simpl never.
Global Arguments ucmra_dist : simpl never.
Global Arguments ucmra_pcore : simpl never.
Global Arguments ucmra_op : simpl never.
Global Arguments ucmra_valid : simpl never.
Global Arguments ucmra_validN : simpl never.
Global Arguments ucmra_ofe_mixin : simpl never.
Global Arguments ucmra_cmra_mixin : simpl never.
Global Arguments ucmra_mixin : simpl never.
Add Printing Constructor ucmra.
(* FIXME(Coq #6294) : we need the new unification algorithm here. *)
Global Hint Extern 0 (Unit _) => refine (ucmra_unit _); shelve : typeclass_instances.
Coercion ucmra_ofeO (A : ucmra) : ofe := Ofe A (ucmra_ofe_mixin A).
Canonical Structure ucmra_ofeO.
Coercion ucmra_cmraR (A : ucmra) : cmra :=
  Cmra' A (ucmra_ofe_mixin A) (ucmra_cmra_mixin A).
Canonical Structure ucmra_cmraR.

(** As for CMRAs above, we instruct Coq to eagerly _expand_ all projections,
  except for the coercion to type (in this case, [ucmra_car]), since that causes
  problem with canonical structure inference.  Additionally, we make Coq 
  eagerly expand the coercions that go from one structure to another, like
  [ucmra_cmraR] and [ucmra_ofeO] in this case. *)
Global Strategy expand [ucmra_cmraR ucmra_ofeO ucmra_equiv ucmra_dist ucmra_pcore
                        ucmra_op ucmra_valid ucmra_validN ucmra_unit
                        ucmra_ofe_mixin ucmra_cmra_mixin].

(** Lifting properties from the mixin *)
Section ucmra_mixin.
  Context {A : ucmra}.
  Implicit Types x y : A.
  Lemma ucmra_unit_valid : ✓ (ε : A).
  Proof. apply (mixin_ucmra_unit_valid _ (ucmra_mixin A)). Qed.
  Global Instance ucmra_unit_left_id : LeftId (≡) ε (@op A _).
  Proof. apply (mixin_ucmra_unit_left_id _ (ucmra_mixin A)). Qed.
  Lemma ucmra_pcore_unit : pcore (ε:A) ≡ Some ε.
  Proof. apply (mixin_ucmra_pcore_unit _ (ucmra_mixin A)). Qed.
End ucmra_mixin.

(** * Discrete CMRAs *)
#[projections(primitive=no)] (* FIXME: making this primitive means we cannot use
the projections with eauto any more (see https://github.com/coq/coq/issues/17561) *)
Class CmraDiscrete (A : cmra) := {
  #[global] cmra_discrete_ofe_discrete :: OfeDiscrete A;
  cmra_discrete_valid (x : A) : ✓{0} x → ✓ x
}.
Global Hint Mode CmraDiscrete ! : typeclass_instances.

(** * Morphisms *)
Class CmraMorphism {A B : cmra} (f : A → B) := {
  #[global] cmra_morphism_ne :: NonExpansive f;
  cmra_morphism_validN n x : ✓{n} x → ✓{n} f x;
  cmra_morphism_pcore x : f <$> pcore x ≡ pcore (f x);
  cmra_morphism_op x y : f (x ⋅ y) ≡ f x ⋅ f y
}.
Global Hint Mode CmraMorphism - - ! : typeclass_instances.
Global Arguments cmra_morphism_validN {_ _} _ {_} _ _ _.
Global Arguments cmra_morphism_pcore {_ _} _ {_} _.
Global Arguments cmra_morphism_op {_ _} _ {_} _ _.

(** * Properties **)
Section cmra.
Context {A : cmra}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Setoids *)
Global Instance cmra_pcore_ne' : NonExpansive (@pcore A _).
Proof.
  intros n x y Hxy. destruct (pcore x) as [cx|] eqn:?.
  { destruct (cmra_pcore_ne n x y cx) as (cy&->&->); auto. }
  destruct (pcore y) as [cy|] eqn:?; auto.
  destruct (cmra_pcore_ne n y x cy) as (cx&?&->); simplify_eq/=; auto.
Qed.
Lemma cmra_pcore_proper x y cx :
  x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy.
Proof.
  intros. destruct (cmra_pcore_ne 0 x y cx) as (cy&?&?); auto.
  exists cy; split; [done|apply equiv_dist=> n].
  destruct (cmra_pcore_ne n x y cx) as (cy'&?&?); naive_solver.
Qed.
Global Instance cmra_pcore_proper' : Proper ((≡) ==> (≡)) (@pcore A _).
Proof. apply (ne_proper _). Qed.
Global Instance cmra_op_ne' : NonExpansive2 (@op A _).
Proof. intros n x1 x2 Hx y1 y2 Hy. by rewrite Hy (comm _ x1) Hx (comm _ y2). Qed.
Global Instance cmra_op_proper' : Proper ((≡) ==> (≡) ==> (≡)) (@op A _).
Proof. apply (ne_proper_2 _). Qed.
Global Instance cmra_validN_ne' n : Proper (dist n ==> iff) (@validN A _ n) | 1.
Proof. by split; apply cmra_validN_ne. Qed.
Global Instance cmra_validN_proper n : Proper ((≡) ==> iff) (@validN A _ n) | 1.
Proof. by intros x1 x2 Hx; apply cmra_validN_ne', equiv_dist. Qed.

Global Instance cmra_valid_proper : Proper ((≡) ==> iff) (@valid A _).
Proof.
  intros x y Hxy; rewrite !cmra_valid_validN.
  by split=> ? n; [rewrite -Hxy|rewrite Hxy].
Qed.
Global Instance cmra_includedN_ne n :
  Proper (dist n ==> dist n ==> iff) (@includedN A _ _ n) | 1.
Proof.
  intros x x' Hx y y' Hy.
  by split; intros [z ?]; exists z; [rewrite -Hx -Hy|rewrite Hx Hy].
Qed.
Global Instance cmra_includedN_proper n :
  Proper ((≡) ==> (≡) ==> iff) (@includedN A _ _ n) | 1.
Proof.
  intros x x' Hx y y' Hy; revert Hx Hy; rewrite !equiv_dist=> Hx Hy.
  by rewrite (Hx n) (Hy n).
Qed.
Global Instance cmra_included_proper :
  Proper ((≡) ==> (≡) ==> iff) (@included A _ _) | 1.
Proof.
  intros x x' Hx y y' Hy.
  by split; intros [z ?]; exists z; [rewrite -Hx -Hy|rewrite Hx Hy].
Qed.
Global Instance cmra_opM_ne : NonExpansive2 (@opM A _).
Proof. destruct 2; by ofe_subst. Qed.
Global Instance cmra_opM_proper : Proper ((≡) ==> (≡) ==> (≡)) (@opM A _).
Proof. destruct 2; by setoid_subst. Qed.

Global Instance CoreId_proper : Proper ((≡) ==> iff) (@CoreId A).
Proof. solve_proper. Qed.
Global Instance Exclusive_proper : Proper ((≡) ==> iff) (@Exclusive A).
Proof. intros x y Hxy. rewrite /Exclusive. by setoid_rewrite Hxy. Qed.
Global Instance Cancelable_proper : Proper ((≡) ==> iff) (@Cancelable A).
Proof. intros x y Hxy. rewrite /Cancelable. by setoid_rewrite Hxy. Qed.
Global Instance IdFree_proper : Proper ((≡) ==> iff) (@IdFree A).
Proof. intros x y Hxy. rewrite /IdFree. by setoid_rewrite Hxy. Qed.

(** ** Op *)
Lemma cmra_op_opM_assoc x y mz : (x ⋅ y) ⋅? mz ≡ x ⋅ (y ⋅? mz).
Proof. destruct mz; by rewrite /= -?assoc. Qed.

(** ** Validity *)
Lemma cmra_validN_le n n' x : ✓{n} x → n' ≤ n → ✓{n'} x.
Proof. induction 2; eauto using cmra_validN_S. Qed.
Lemma cmra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x.
Proof. rewrite !cmra_valid_validN; eauto using cmra_validN_op_l. Qed.
Lemma cmra_validN_op_r n x y : ✓{n} (x ⋅ y) → ✓{n} y.
Proof. rewrite (comm _ x); apply cmra_validN_op_l. Qed.
Lemma cmra_valid_op_r x y : ✓ (x ⋅ y) → ✓ y.
Proof. rewrite !cmra_valid_validN; eauto using cmra_validN_op_r. Qed.

(** ** Core *)
Lemma cmra_pcore_l' x cx : pcore x ≡ Some cx → cx ⋅ x ≡ x.
Proof. intros (cx'&?&<-)%Some_equiv_eq. by apply cmra_pcore_l. Qed.
Lemma cmra_pcore_r x cx : pcore x = Some cx → x ⋅ cx ≡ x.
Proof. intros. rewrite comm. by apply cmra_pcore_l. Qed.
Lemma cmra_pcore_r' x cx : pcore x ≡ Some cx → x ⋅ cx ≡ x.
Proof. intros (cx'&?&<-)%Some_equiv_eq. by apply cmra_pcore_r. Qed.
Lemma cmra_pcore_idemp' x cx : pcore x ≡ Some cx → pcore cx ≡ Some cx.
Proof. intros (cx'&?&<-)%Some_equiv_eq. eauto using cmra_pcore_idemp. Qed.
Lemma cmra_pcore_dup x cx : pcore x = Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp. Qed.
Lemma cmra_pcore_dup' x cx : pcore x ≡ Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp'. Qed.
Lemma cmra_pcore_validN n x cx : ✓{n} x → pcore x = Some cx → ✓{n} cx.
Proof.
  intros Hvx Hx%cmra_pcore_l. move: Hvx; rewrite -Hx. apply cmra_validN_op_l.
Qed.
Lemma cmra_pcore_valid x cx : ✓ x → pcore x = Some cx → ✓ cx.
Proof.
  intros Hv Hx%cmra_pcore_l. move: Hv; rewrite -Hx. apply cmra_valid_op_l.
Qed.

(** ** Exclusive elements *)
Lemma exclusiveN_l n x `{!Exclusive x} y : ✓{n} (x ⋅ y) → False.
Proof. intros. eapply (exclusive0_l x y), cmra_validN_le; eauto with lia. Qed.
Lemma exclusiveN_r n x `{!Exclusive x} y : ✓{n} (y ⋅ x) → False.
Proof. rewrite comm. by apply exclusiveN_l. Qed.
Lemma exclusive_l x `{!Exclusive x} y : ✓ (x ⋅ y) → False.
Proof. by move /cmra_valid_validN /(_ 0) /exclusive0_l. Qed.
Lemma exclusive_r x `{!Exclusive x} y : ✓ (y ⋅ x) → False.
Proof. rewrite comm. by apply exclusive_l. Qed.
Lemma exclusiveN_opM n x `{!Exclusive x} my : ✓{n} (x ⋅? my) → my = None.
Proof. destruct my as [y|]; last done. move=> /(exclusiveN_l _ x) []. Qed.
Lemma exclusive_includedN n x `{!Exclusive x} y : x ≼{n} y → ✓{n} y → False.
Proof. intros [? ->]. by apply exclusiveN_l. Qed.
Lemma exclusive_included x `{!Exclusive x} y : x ≼ y → ✓ y → False.
Proof. intros [? ->]. by apply exclusive_l. Qed.

(** ** Order *)
Lemma cmra_included_includedN n x y : x ≼ y → x ≼{n} y.
Proof. intros [z ->]. by exists z. Qed.
Global Instance cmra_includedN_trans n : Transitive (@includedN A _ _ n).
Proof.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2). by rewrite assoc -Hy -Hz.
Qed.
Global Instance cmra_included_trans: Transitive (@included A _ _).
Proof.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2). by rewrite assoc -Hy -Hz.
Qed.
Lemma cmra_valid_included x y : ✓ y → x ≼ y → ✓ x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using cmra_valid_op_l. Qed.
Lemma cmra_validN_includedN n x y : ✓{n} y → x ≼{n} y → ✓{n} x.
Proof. intros Hyv [z ?]; ofe_subst y; eauto using cmra_validN_op_l. Qed.
Lemma cmra_validN_included n x y : ✓{n} y → x ≼ y → ✓{n} x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using cmra_validN_op_l. Qed.

Lemma cmra_includedN_le n n' x y : x ≼{n} y → n' ≤ n → x ≼{n'} y.
Proof. by intros [z Hz] ?; exists z; eapply dist_le. Qed.
Lemma cmra_includedN_S n x y : x ≼{S n} y → x ≼{n} y.
Proof. intros ?. eapply cmra_includedN_le; [done|lia]. Qed.

Lemma cmra_includedN_l n x y : x ≼{n} x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_included_l x y : x ≼ x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_includedN_r n x y : y ≼{n} x ⋅ y.
Proof. rewrite (comm op); apply cmra_includedN_l. Qed.
Lemma cmra_included_r x y : y ≼ x ⋅ y.
Proof. rewrite (comm op); apply cmra_included_l. Qed.

Lemma cmra_pcore_mono' x y cx :
  x ≼ y → pcore x ≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
Proof.
  intros ? (cx'&?&Hcx)%Some_equiv_eq.
  destruct (cmra_pcore_mono x y cx') as (cy&->&?); auto.
  exists cy; by rewrite -Hcx.
Qed.
Lemma cmra_pcore_monoN' n x y cx :
  x ≼{n} y → pcore x ≡{n}≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼{n} cy.
Proof.
  intros [z Hy] (cx'&?&Hcx)%dist_Some_inv_r'.
  destruct (cmra_pcore_mono x (x ⋅ z) cx')
    as (cy&Hxy&?); auto using cmra_included_l.
  assert (pcore y ≡{n}≡ Some cy) as (cy'&?&Hcy')%dist_Some_inv_r'.
  { by rewrite Hy Hxy. }
  exists cy'; split; first done.
  rewrite Hcx -Hcy'; auto using cmra_included_includedN.
Qed.
Lemma cmra_included_pcore x cx : pcore x = Some cx → cx ≼ x.
Proof. exists x. by rewrite cmra_pcore_l. Qed.

Lemma cmra_monoN_l n x y z : x ≼{n} y → z ⋅ x ≼{n} z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_mono_l x y z : x ≼ y → z ⋅ x ≼ z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_monoN_r n x y z : x ≼{n} y → x ⋅ z ≼{n} y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_monoN_l. Qed.
Lemma cmra_mono_r x y z : x ≼ y → x ⋅ z ≼ y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_mono_l. Qed.
Lemma cmra_monoN n x1 x2 y1 y2 : x1 ≼{n} y1 → x2 ≼{n} y2 → x1 ⋅ x2 ≼{n} y1 ⋅ y2.
Proof. intros; etrans; eauto using cmra_monoN_l, cmra_monoN_r. Qed.
Lemma cmra_mono x1 x2 y1 y2 : x1 ≼ y1 → x2 ≼ y2 → x1 ⋅ x2 ≼ y1 ⋅ y2.
Proof. intros; etrans; eauto using cmra_mono_l, cmra_mono_r. Qed.

Global Instance cmra_monoN' n :
  Proper (includedN n ==> includedN n ==> includedN n) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_monoN. Qed.
Global Instance cmra_mono' :
  Proper (included ==> included ==> included) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_mono. Qed.

Lemma cmra_included_dist_l n x1 x2 x1' :
  x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2.
Proof.
  intros [z Hx2] Hx1; exists (x1' ⋅ z); split; auto using cmra_included_l.
  by rewrite Hx1 Hx2.
Qed.

(** ** CoreId elements *)
Lemma core_id_dup x `{!CoreId x} : x ≡ x ⋅ x.
Proof. by apply cmra_pcore_dup' with x. Qed.

Lemma core_id_extract x y `{!CoreId x} :
  x ≼ y → y ≡ y ⋅ x.
Proof.
  intros ?.
  destruct (cmra_pcore_mono' x y x) as (cy & Hcy & [x' Hx']); [done|exact: core_id|].
  rewrite -(cmra_pcore_r y) //. rewrite Hx' -!assoc. f_equiv.
  rewrite [x' ⋅ x]comm assoc -core_id_dup. done.
Qed.

(** ** Total core *)
Section total_core.
  Local Set Default Proof Using "Type*".
  Context `{!CmraTotal A}.

  Lemma cmra_pcore_core x : pcore x = Some (core x).
  Proof.
    rewrite /core. destruct (cmra_total x) as [cx ->]. done.
  Qed.
  Lemma cmra_core_l x : core x ⋅ x ≡ x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_l.
  Qed.
  Lemma cmra_core_idemp x : core (core x) ≡ core x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_idemp.
  Qed.
  Lemma cmra_core_mono x y : x ≼ y → core x ≼ core y.
  Proof.
    intros; destruct (cmra_total x) as [cx Hcx].
    destruct (cmra_pcore_mono x y cx) as (cy&Hcy&?); auto.
    by rewrite /core /= Hcx Hcy.
  Qed.

  Global Instance cmra_core_ne : NonExpansive (@core A _).
  Proof.
    intros n x y Hxy. destruct (cmra_total x) as [cx Hcx].
    by rewrite /core /= -Hxy Hcx.
  Qed.
  Global Instance cmra_core_proper : Proper ((≡) ==> (≡)) (@core A _).
  Proof. apply (ne_proper _). Qed.

  Lemma cmra_core_r x : x ⋅ core x ≡ x.
  Proof. by rewrite (comm _ x) cmra_core_l. Qed.
  Lemma cmra_core_dup x : core x ≡ core x ⋅ core x.
  Proof. by rewrite -{3}(cmra_core_idemp x) cmra_core_r. Qed.
  Lemma cmra_core_validN n x : ✓{n} x → ✓{n} core x.
  Proof. rewrite -{1}(cmra_core_l x); apply cmra_validN_op_l. Qed.
  Lemma cmra_core_valid x : ✓ x → ✓ core x.
  Proof. rewrite -{1}(cmra_core_l x); apply cmra_valid_op_l. Qed.

  Lemma core_id_total x : CoreId x ↔ core x ≡ x.
  Proof.
    split; [intros; by rewrite /core /= (core_id x)|].
    rewrite /CoreId /core /=.
    destruct (cmra_total x) as [? ->]. by constructor.
  Qed.
  Lemma core_id_core x `{!CoreId x} : core x ≡ x.
  Proof. by apply core_id_total. Qed.

  (** Not an instance since TC search cannot solve the premise. *)
  Lemma cmra_pcore_core_id x y : pcore x = Some y → CoreId y.
  Proof. rewrite /CoreId. eauto using cmra_pcore_idemp. Qed.

  Global Instance cmra_core_core_id x : CoreId (core x).
  Proof. eapply cmra_pcore_core_id. rewrite cmra_pcore_core. done. Qed.

  Lemma cmra_included_core x : core x ≼ x.
  Proof. by exists x; rewrite cmra_core_l. Qed.
  Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
  Proof.
    split; [|apply _]. by intros x; exists (core x); rewrite cmra_core_r.
  Qed.
  Global Instance cmra_included_preorder : PreOrder (@included A _ _).
  Proof.
    split; [|apply _]. by intros x; exists (core x); rewrite cmra_core_r.
  Qed.
  Lemma cmra_core_monoN n x y : x ≼{n} y → core x ≼{n} core y.
  Proof.
    intros [z ->].
    apply cmra_included_includedN, cmra_core_mono, cmra_included_l.
  Qed.
End total_core.

(** ** Discrete *)
Lemma cmra_discrete_included_l x y : Discrete x → ✓{0} y → x ≼{0} y → x ≼ y.
Proof.
  intros ?? [x' ?].
  destruct (cmra_extend 0 y x x') as (z&z'&Hy&Hz&Hz'); auto; simpl in *.
  by exists z'; rewrite Hy (discrete_0 x z).
Qed.
Lemma cmra_discrete_included_r x y : Discrete y → x ≼{0} y → x ≼ y.
Proof. intros ? [x' ?]. exists x'. by apply (discrete_0 y). Qed.
Lemma cmra_op_discrete x1 x2 :
  ✓{0} (x1 ⋅ x2) → Discrete x1 → Discrete x2 → Discrete (x1 ⋅ x2).
Proof.
  intros ??? z Hz.
  destruct (cmra_extend 0 z x1 x2) as (y1&y2&Hz'&?&?); auto; simpl in *.
  { rewrite -?Hz. done. }
  by rewrite Hz' (discrete_0 x1 y1) // (discrete_0 x2 y2).
Qed.

(** ** Discrete *)
Lemma cmra_discrete_valid_iff `{!CmraDiscrete A} n x : ✓ x ↔ ✓{n} x.
Proof.
  split; first by rewrite cmra_valid_validN.
  eauto using cmra_discrete_valid, cmra_validN_le with lia.
Qed.
Lemma cmra_discrete_valid_iff_0 `{!CmraDiscrete A} n x : ✓{0} x ↔ ✓{n} x.
Proof. by rewrite -!cmra_discrete_valid_iff. Qed.
Lemma cmra_discrete_included_iff `{!OfeDiscrete A} n x y : x ≼ y ↔ x ≼{n} y.
Proof.
  split; first by apply cmra_included_includedN.
  intros [z ->%(discrete_iff _ _)]; eauto using cmra_included_l.
Qed.
Lemma cmra_discrete_included_iff_0 `{!OfeDiscrete A} n x y : x ≼{0} y ↔ x ≼{n} y.
Proof. by rewrite -!cmra_discrete_included_iff. Qed.

(** Cancelable elements  *)
Global Instance cancelable_proper : Proper (equiv ==> iff) (@Cancelable A).
Proof. unfold Cancelable. intros x x' EQ. by setoid_rewrite EQ. Qed.
Lemma cancelable x `{!Cancelable x} y z : ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z.
Proof. rewrite !equiv_dist cmra_valid_validN. intros. by apply (cancelableN x). Qed.
Lemma discrete_cancelable x `{!CmraDiscrete A}:
  (∀ y z, ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z) → Cancelable x.
Proof. intros ????. rewrite -!discrete_iff -cmra_discrete_valid_iff. auto. Qed.
Global Instance cancelable_op x y :
  Cancelable x → Cancelable y → Cancelable (x ⋅ y).
Proof.
  intros ?? n z z' ??. apply (cancelableN y), (cancelableN x).
  - eapply cmra_validN_op_r. by rewrite assoc.
  - by rewrite assoc.
  - by rewrite !assoc.
Qed.
Global Instance exclusive_cancelable (x : A) : Exclusive x → Cancelable x.
Proof. intros ? n z z' []%(exclusiveN_l _ x). Qed.

(** Id-free elements  *)
Global Instance id_free_ne n : Proper (dist n ==> iff) (@IdFree A).
Proof.
  intros x x' EQ%(dist_le _ 0); last lia. rewrite /IdFree.
  split=> y ?; (rewrite -EQ || rewrite EQ); eauto.
Qed.
Global Instance id_free_proper : Proper (equiv ==> iff) (@IdFree A).
Proof. by move=> P Q /equiv_dist /(_ 0)=> ->. Qed.
Lemma id_freeN_r n n' x `{!IdFree x} y : ✓{n}x → x ⋅ y ≡{n'}≡ x → False.
Proof. eauto using cmra_validN_le, dist_le with lia. Qed.
Lemma id_freeN_l n n' x `{!IdFree x} y : ✓{n}x → y ⋅ x ≡{n'}≡ x → False.
Proof. rewrite comm. eauto using id_freeN_r. Qed.
Lemma id_free_r x `{!IdFree x} y : ✓x → x ⋅ y ≡ x → False.
Proof. move=> /cmra_valid_validN ? /equiv_dist. eauto. Qed.
Lemma id_free_l x `{!IdFree x} y : ✓x → y ⋅ x ≡ x → False.
Proof. rewrite comm. eauto using id_free_r. Qed.
Lemma discrete_id_free x `{!CmraDiscrete A}:
  (∀ y, ✓ x → x ⋅ y ≡ x → False) → IdFree x.
Proof.
  intros Hx y ??. apply (Hx y), (discrete_0 _); eauto using cmra_discrete_valid.
Qed.
Global Instance id_free_op_r x y : IdFree y → Cancelable x → IdFree (x ⋅ y).
Proof.
  intros ?? z ? Hid%symmetry. revert Hid. rewrite -assoc=>/(cancelableN x) ?.
  eapply (id_free0_r y); [by eapply cmra_validN_op_r |symmetry; eauto].
Qed.
Global Instance id_free_op_l x y : IdFree x → Cancelable y → IdFree (x ⋅ y).
Proof. intros. rewrite comm. apply _. Qed.
Global Instance exclusive_id_free x : Exclusive x → IdFree x.
Proof. intros ? z ? Hid. apply (exclusiveN_l 0 x z). by rewrite Hid. Qed.
End cmra.

(* We use a [Hint Extern] with [apply:], instead of [Hint Immediate], to invoke
  the new unification algorithm. The old unification algorithm sometimes gets
  confused by going from [ucmra]'s to [cmra]'s and back. *)
Global Hint Extern 0 (?a ≼ ?a ⋅ _) => apply: cmra_included_l : core.
Global Hint Extern 0 (?a ≼ _ ⋅ ?a) => apply: cmra_included_r : core.

(** * Properties about CMRAs with a unit element **)
Section ucmra.
  Context {A : ucmra}.
  Implicit Types x y z : A.

  Lemma ucmra_unit_validN n : ✓{n} (ε:A).
  Proof. apply cmra_valid_validN, ucmra_unit_valid. Qed.
  Lemma ucmra_unit_leastN n x : ε ≼{n} x.
  Proof. by exists x; rewrite left_id. Qed.
  Lemma ucmra_unit_least x : ε ≼ x.
  Proof. by exists x; rewrite left_id. Qed.
  Global Instance ucmra_unit_right_id : RightId (≡) ε (@op A _).
  Proof. by intros x; rewrite (comm op) left_id. Qed.
  Global Instance ucmra_unit_core_id : CoreId (ε:A).
  Proof. apply ucmra_pcore_unit. Qed.

  Global Instance cmra_unit_cmra_total : CmraTotal A.
  Proof.
    intros x. destruct (cmra_pcore_mono' ε x ε) as (cx&->&?); [..|by eauto].
    - apply ucmra_unit_least.
    - apply (core_id _).
  Qed.
  Global Instance empty_cancelable : Cancelable (ε:A).
  Proof. intros ???. by rewrite !left_id. Qed.

  (* For big ops *)
  Global Instance cmra_monoid : Monoid (@op A _) := {| monoid_unit := ε |}.
End ucmra.

Global Hint Immediate cmra_unit_cmra_total : core.
Global Hint Extern 0 (ε ≼ _) => apply: ucmra_unit_least : core.

(** * Properties about CMRAs with Leibniz equality *)
Section cmra_leibniz.
  Local Set Default Proof Using "Type*".
  Context {A : cmra} `{!LeibnizEquiv A}.
  Implicit Types x y : A.

  Global Instance cmra_assoc_L : Assoc (=) (@op A _).
  Proof. intros x y z. unfold_leibniz. by rewrite assoc. Qed.
  Global Instance cmra_comm_L : Comm (=) (@op A _).
  Proof. intros x y. unfold_leibniz. by rewrite comm. Qed.

  Lemma cmra_pcore_l_L x cx : pcore x = Some cx → cx ⋅ x = x.
  Proof. unfold_leibniz. apply cmra_pcore_l'. Qed.
  Lemma cmra_pcore_idemp_L x cx : pcore x = Some cx → pcore cx = Some cx.
  Proof. unfold_leibniz. apply cmra_pcore_idemp'. Qed.

  Lemma cmra_op_opM_assoc_L x y mz : (x ⋅ y) ⋅? mz = x ⋅ (y ⋅? mz).
  Proof. unfold_leibniz. apply cmra_op_opM_assoc. Qed.

  (** ** Core *)
  Lemma cmra_pcore_r_L x cx : pcore x = Some cx → x ⋅ cx = x.
  Proof. unfold_leibniz. apply cmra_pcore_r'. Qed.
  Lemma cmra_pcore_dup_L x cx : pcore x = Some cx → cx = cx ⋅ cx.
  Proof. unfold_leibniz. apply cmra_pcore_dup'. Qed.

  (** ** CoreId elements *)
  Lemma core_id_dup_L x `{!CoreId x} : x = x ⋅ x.
  Proof. unfold_leibniz. by apply core_id_dup. Qed.

  (** ** Total core *)
  Section total_core.
    Context `{!CmraTotal A}.

    Lemma cmra_core_r_L x : x ⋅ core x = x.
    Proof. unfold_leibniz. apply cmra_core_r. Qed.
    Lemma cmra_core_l_L x : core x ⋅ x = x.
    Proof. unfold_leibniz. apply cmra_core_l. Qed.
    Lemma cmra_core_idemp_L x : core (core x) = core x.
    Proof. unfold_leibniz. apply cmra_core_idemp. Qed.
    Lemma cmra_core_dup_L x : core x = core x ⋅ core x.
    Proof. unfold_leibniz. apply cmra_core_dup. Qed.
    Lemma core_id_total_L x : CoreId x ↔ core x = x.
    Proof. unfold_leibniz. apply core_id_total. Qed.
    Lemma core_id_core_L x `{!CoreId x} : core x = x.
    Proof. by apply core_id_total_L. Qed.
  End total_core.
End cmra_leibniz.

Section ucmra_leibniz.
  Local Set Default Proof Using "Type*".
  Context {A : ucmra} `{!LeibnizEquiv A}.
  Implicit Types x y z : A.

  Global Instance ucmra_unit_left_id_L : LeftId (=) ε (@op A _).
  Proof. intros x. unfold_leibniz. by rewrite left_id. Qed.
  Global Instance ucmra_unit_right_id_L : RightId (=) ε (@op A _).
  Proof. intros x. unfold_leibniz. by rewrite right_id. Qed.
End ucmra_leibniz.

(** * Constructing a CMRA with total core *)
Section cmra_total.
  Context A `{!Dist A, !Equiv A, !PCore A, !Op A, !Valid A, !ValidN A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_ne : ∀ x : A, NonExpansive (op x)).
  Context (core_ne : NonExpansive (@core A _)).
  Context (validN_ne : ∀ n, Proper (dist n ==> impl) (@validN A _ n)).
  Context (valid_validN : ∀ (x : A), ✓ x ↔ ∀ n, ✓{n} x).
  Context (validN_S : ∀ n (x : A), ✓{S n} x → ✓{n} x).
  Context (op_assoc : Assoc (≡) (@op A _)).
  Context (op_comm : Comm (≡) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x ≡ x).
  Context (core_idemp : ∀ x : A, core (core x) ≡ core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (validN_op_l : ∀ n (x y : A), ✓{n} (x ⋅ y) → ✓{n} x).
  Context (extend : ∀ n (x y1 y2 : A),
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    { z1 : A & { z2 | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 } }).
  Lemma cmra_total_mixin : CmraMixin A.
  Proof using Type*.
    split; auto.
    - intros n x y ? Hcx%core_ne Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]; by constructor.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End cmra_total.

(** * Properties about morphisms *)
Global Instance cmra_morphism_id {A : cmra} : CmraMorphism (@id A).
Proof.
  split => /=.
  - apply _.
  - done.
  - intros. by rewrite option_fmap_id.
  - done.
Qed.
Global Instance cmra_morphism_proper {A B : cmra} (f : A → B) `{!CmraMorphism f} :
  Proper ((≡) ==> (≡)) f := ne_proper _.
Global Instance cmra_morphism_compose {A B C : cmra} (f : A → B) (g : B → C) :
  CmraMorphism f → CmraMorphism g → CmraMorphism (g ∘ f).
Proof.
  split.
  - apply _.
  - move=> n x Hx /=. by apply cmra_morphism_validN, cmra_morphism_validN.
  - move=> x /=. by rewrite option_fmap_compose !cmra_morphism_pcore.
  - move=> x y /=. by rewrite !cmra_morphism_op.
Qed.

Section cmra_morphism.
  Local Set Default Proof Using "Type*".
  Context {A B : cmra} (f : A → B) `{!CmraMorphism f}.
  Lemma cmra_morphism_core x : f (core x) ≡ core (f x).
  Proof. unfold core. rewrite -cmra_morphism_pcore. by destruct (pcore x). Qed.
  Lemma cmra_morphism_monotone x y : x ≼ y → f x ≼ f y.
  Proof. intros [z ->]. exists (f z). by rewrite cmra_morphism_op. Qed.
  Lemma cmra_morphism_monotoneN n x y : x ≼{n} y → f x ≼{n} f y.
  Proof. intros [z ->]. exists (f z). by rewrite cmra_morphism_op. Qed.
  Lemma cmra_morphism_valid x : ✓ x → ✓ f x.
  Proof. rewrite !cmra_valid_validN; eauto using cmra_morphism_validN. Qed.
End cmra_morphism.

(** COFE → CMRA Functors *)
Record rFunctor := RFunctor {
  rFunctor_car : ∀ A `{!Cofe A} B `{!Cofe B}, cmra;
  rFunctor_map `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → rFunctor_car A1 B1 -n> rFunctor_car A2 B2;
  rFunctor_map_ne `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    NonExpansive (@rFunctor_map A1 _ A2 _ B1 _ B2 _);
  rFunctor_map_id `{!Cofe A, !Cofe B} (x : rFunctor_car A B) :
    rFunctor_map (cid,cid) x ≡ x;
  rFunctor_map_compose `{!Cofe A1, !Cofe A2, !Cofe A3, !Cofe B1, !Cofe B2, !Cofe B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    rFunctor_map (f◎g, g'◎f') x ≡ rFunctor_map (g,g') (rFunctor_map (f,f') x);
  rFunctor_mor `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2}
      (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CmraMorphism (rFunctor_map fg)
}.
Global Existing Instances rFunctor_map_ne rFunctor_mor.
Global Instance: Params (@rFunctor_map) 9 := {}.

Declare Scope rFunctor_scope.
Delimit Scope rFunctor_scope with RF.
Bind Scope rFunctor_scope with rFunctor.

Class rFunctorContractive (F : rFunctor) :=
  #[global] rFunctor_map_contractive `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} ::
    Contractive (@rFunctor_map F A1 _ A2 _ B1 _ B2 _).
Global Hint Mode rFunctorContractive ! : typeclass_instances.

Definition rFunctor_apply (F: rFunctor) (A: ofe) `{!Cofe A} : cmra :=
  rFunctor_car F A A.

Program Definition rFunctor_to_oFunctor (F: rFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := rFunctor_car F A B;
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := rFunctor_map F fg
|}.
Next Obligation.
  intros F A ? B ? x. simpl in *. apply rFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. simpl in *.
  apply rFunctor_map_compose.
Qed.

Global Instance rFunctor_to_oFunctor_contractive F :
  rFunctorContractive F → oFunctorContractive (rFunctor_to_oFunctor F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg. apply rFunctor_map_contractive. done.
Qed.

Program Definition rFunctor_oFunctor_compose (F1 : rFunctor) (F2 : oFunctor)
  `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} : rFunctor := {|
  rFunctor_car A _ B _ := rFunctor_car F1 (oFunctor_car F2 B A) (oFunctor_car F2 A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ 'fg :=
    rFunctor_map F1 (oFunctor_map F2 (fg.2,fg.1),oFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] [??]; simpl in *.
  apply rFunctor_map_ne; split; apply oFunctor_map_ne; by split.
Qed.
Next Obligation.
  intros F1 F2 ? A ? B ? x; simpl in *. rewrite -{2}(rFunctor_map_id F1 x).
  apply equiv_dist=> n. apply rFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_id.
Qed.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -rFunctor_map_compose. apply equiv_dist=> n. apply rFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_compose.
Qed.
Global Instance rFunctor_oFunctor_compose_contractive_1
    (F1 : rFunctor) (F2 : oFunctor)
    `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} :
  rFunctorContractive F1 → rFunctorContractive (rFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_contractive; destruct Hfg; split; simpl in *; apply oFunctor_map_ne; by split.
Qed.
Global Instance rFunctor_oFunctor_compose_contractive_2
    (F1 : rFunctor) (F2 : oFunctor)
    `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} :
  oFunctorContractive F2 → rFunctorContractive (rFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_equiv; split; simpl in *; f_contractive; destruct Hfg; by split.
Qed.

Program Definition constRF (B : cmra) : rFunctor :=
  {| rFunctor_car A1 _ A2 _ := B; rFunctor_map A1 _ A2 _ B1 _ B2 _ f := cid |}.
Solve Obligations with done.
Coercion constRF : cmra >-> rFunctor.

Global Instance constRF_contractive B : rFunctorContractive (constRF B).
Proof. rewrite /rFunctorContractive; apply _. Qed.

(** COFE → UCMRA Functors *)
Record urFunctor := URFunctor {
  urFunctor_car : ∀ A `{!Cofe A} B `{!Cofe B}, ucmra;
  urFunctor_map `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → urFunctor_car A1 B1 -n> urFunctor_car A2 B2;
  urFunctor_map_ne `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} :
    NonExpansive (@urFunctor_map A1 _ A2 _ B1 _ B2 _);
  urFunctor_map_id `{!Cofe A, !Cofe B} (x : urFunctor_car A B) :
    urFunctor_map (cid,cid) x ≡ x;
  urFunctor_map_compose `{!Cofe A1, !Cofe A2, !Cofe A3, !Cofe B1, !Cofe B2, !Cofe B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    urFunctor_map (f◎g, g'◎f') x ≡ urFunctor_map (g,g') (urFunctor_map (f,f') x);
  urFunctor_mor `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2}
      (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CmraMorphism (urFunctor_map fg)
}.
Global Existing Instances urFunctor_map_ne urFunctor_mor.
Global Instance: Params (@urFunctor_map) 9 := {}.

Declare Scope urFunctor_scope.
Delimit Scope urFunctor_scope with URF.
Bind Scope urFunctor_scope with urFunctor.

Class urFunctorContractive (F : urFunctor) :=
  #[global] urFunctor_map_contractive `{!Cofe A1, !Cofe A2, !Cofe B1, !Cofe B2} ::
    Contractive (@urFunctor_map F A1 _ A2 _ B1 _ B2 _).
Global Hint Mode urFunctorContractive ! : typeclass_instances.

Definition urFunctor_apply (F: urFunctor) (A: ofe) `{!Cofe A} : ucmra :=
  urFunctor_car F A A.

Program Definition urFunctor_to_rFunctor (F: urFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := urFunctor_car F A B;
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := urFunctor_map F fg
|}.
Next Obligation.
  intros F A ? B ? x. simpl in *. apply urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. simpl in *.
  apply urFunctor_map_compose.
Qed.

Global Instance urFunctor_to_rFunctor_contractive F :
  urFunctorContractive F → rFunctorContractive (urFunctor_to_rFunctor F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg. apply urFunctor_map_contractive. done.
Qed.

Program Definition urFunctor_oFunctor_compose (F1 : urFunctor) (F2 : oFunctor)
  `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} : urFunctor := {|
  urFunctor_car A _ B _ := urFunctor_car F1 (oFunctor_car F2 B A) (oFunctor_car F2 A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ 'fg :=
    urFunctor_map F1 (oFunctor_map F2 (fg.2,fg.1),oFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] [??]; simpl in *.
  apply urFunctor_map_ne; split; apply oFunctor_map_ne; by split.
Qed.
Next Obligation.
  intros F1 F2 ? A ? B ? x; simpl in *. rewrite -{2}(urFunctor_map_id F1 x).
  apply equiv_dist=> n. apply urFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_id.
Qed.
Next Obligation.
  intros F1 F2 ? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -urFunctor_map_compose. apply equiv_dist=> n. apply urFunctor_map_ne.
  split=> y /=; by rewrite !oFunctor_map_compose.
Qed.
Global Instance urFunctor_oFunctor_compose_contractive_1
    (F1 : urFunctor) (F2 : oFunctor)
    `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} :
  urFunctorContractive F1 → urFunctorContractive (urFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_contractive; destruct Hfg; split; simpl in *; apply oFunctor_map_ne; by split.
Qed.
Global Instance urFunctor_oFunctor_compose_contractive_2
    (F1 : urFunctor) (F2 : oFunctor)
    `{!∀ `{Cofe A, Cofe B}, Cofe (oFunctor_car F2 A B)} :
  oFunctorContractive F2 → urFunctorContractive (urFunctor_oFunctor_compose F1 F2).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n [f1 g1] [f2 g2] Hfg; simpl in *.
  f_equiv; split; simpl in *; f_contractive; destruct Hfg; by split.
Qed.

Program Definition constURF (B : ucmra) : urFunctor :=
  {| urFunctor_car A1 _ A2 _ := B; urFunctor_map A1 _ A2 _ B1 _ B2 _ f := cid |}.
Solve Obligations with done.
Coercion constURF : ucmra >-> urFunctor.

Global Instance constURF_contractive B : urFunctorContractive (constURF B).
Proof. rewrite /urFunctorContractive; apply _. Qed.

(** * Transporting a CMRA equality *)
Definition cmra_transport {A B : cmra} (H : A = B) (x : A) : B :=
  eq_rect A id x _ H.

Lemma cmra_transport_trans {A B C : cmra} (H1 : A = B) (H2 : B = C) x :
  cmra_transport H2 (cmra_transport H1 x) = cmra_transport (eq_trans H1 H2) x.
Proof. by destruct H2. Qed.

Section cmra_transport.
  Context {A B : cmra} (H : A = B).
  Notation T := (cmra_transport H).
  Global Instance cmra_transport_ne : NonExpansive T.
  Proof. by intros ???; destruct H. Qed.
  Global Instance cmra_transport_proper : Proper ((≡) ==> (≡)) T.
  Proof. by intros ???; destruct H. Qed.
  Lemma cmra_transport_op x y : T (x ⋅ y) = T x ⋅ T y.
  Proof. by destruct H. Qed.
  Lemma cmra_transport_core x : T (core x) = core (T x).
  Proof. by destruct H. Qed.
  Lemma cmra_transport_validN n x : ✓{n} T x ↔ ✓{n} x.
  Proof. by destruct H. Qed.
  Lemma cmra_transport_valid x : ✓ T x ↔ ✓ x.
  Proof. by destruct H. Qed.
  Global Instance cmra_transport_discrete x : Discrete x → Discrete (T x).
  Proof. by destruct H. Qed.
  Global Instance cmra_transport_core_id x : CoreId x → CoreId (T x).
  Proof. by destruct H. Qed.
End cmra_transport.

(** * Instances *)
(** ** Discrete CMRA *)
Record RAMixin A `{Equiv A, PCore A, Op A, Valid A} := {
  (* setoids *)
  ra_op_proper (x : A) : Proper ((≡) ==> (≡)) (op x);
  ra_core_proper (x y : A) cx :
    x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy;
  ra_validN_proper : Proper ((≡@{A}) ==> impl) valid;
  (* monoid *)
  ra_assoc : Assoc (≡@{A}) (⋅);
  ra_comm : Comm (≡@{A}) (⋅);
  ra_pcore_l (x : A) cx : pcore x = Some cx → cx ⋅ x ≡ x;
  ra_pcore_idemp (x : A) cx : pcore x = Some cx → pcore cx ≡ Some cx;
  ra_pcore_mono (x y : A) cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
  ra_valid_op_l (x y : A) : ✓ (x ⋅ y) → ✓ x
}.

Section discrete.
  Local Set Default Proof Using "Type*".
  Context `{!Equiv A, !PCore A, !Op A, !Valid A} (Heq : @Equivalence A (≡)).
  Context (ra_mix : RAMixin A).
  Existing Instances discrete_dist.

  Local Instance discrete_validN_instance : ValidN A := λ n x, ✓ x.
  Definition discrete_cmra_mixin : CmraMixin A.
  Proof.
    destruct ra_mix; split; try done.
    - intros x; split; first done. by move=> /(_ 0).
    - intros n x y1 y2 ??; by exists y1, y2.
  Qed.

  Local Instance discrete_cmra_discrete :
    CmraDiscrete (Cmra' A (discrete_ofe_mixin Heq) discrete_cmra_mixin).
  Proof. split; first apply _. done. Qed.
End discrete.

(** A smart constructor for the discrete RA over a carrier [A]. It uses
[ofe_discrete_equivalence_of A] to make sure the same [Equivalence] proof is
used as when constructing the OFE. *)
Notation discreteR A ra_mix :=
  (Cmra A (discrete_cmra_mixin (discrete_ofe_equivalence_of A%type) ra_mix))
  (only parsing).

Section ra_total.
  Local Set Default Proof Using "Type*".
  Context A `{Equiv A, PCore A, Op A, Valid A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_proper : ∀ x : A, Proper ((≡) ==> (≡)) (op x)).
  Context (core_proper: Proper ((≡) ==> (≡)) (@core A _)).
  Context (valid_proper : Proper ((≡) ==> impl) (@valid A _)).
  Context (op_assoc : Assoc (≡) (@op A _)).
  Context (op_comm : Comm (≡) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x ≡ x).
  Context (core_idemp : ∀ x : A, core (core x) ≡ core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (valid_op_l : ∀ x y : A, ✓ (x ⋅ y) → ✓ x).
  Lemma ra_total_mixin : RAMixin A.
  Proof.
    split; auto.
    - intros x y ? Hcx%core_proper Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]; by constructor.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End ra_total.

(** ** CMRA for the unit type *)
Section unit.
  Local Instance unit_valid_instance : Valid () := λ x, True.
  Local Instance unit_validN_instance : ValidN () := λ n x, True.
  Local Instance unit_pcore_instance : PCore () := λ x, Some x.
  Local Instance unit_op_instance : Op () := λ x y, ().
  Lemma unit_cmra_mixin : CmraMixin ().
  Proof. apply discrete_cmra_mixin, ra_total_mixin; by eauto. Qed.
  Canonical Structure unitR : cmra := Cmra unit unit_cmra_mixin.

  Local Instance unit_unit_instance : Unit () := ().
  Lemma unit_ucmra_mixin : UcmraMixin ().
  Proof. done. Qed.
  Canonical Structure unitUR : ucmra := Ucmra unit unit_ucmra_mixin.

  Global Instance unit_cmra_discrete : CmraDiscrete unitR.
  Proof. done. Qed.
  Global Instance unit_core_id (x : ()) : CoreId x.
  Proof. by constructor. Qed.
  Global Instance unit_cancelable (x : ()) : Cancelable x.
  Proof. by constructor. Qed.
End unit.

(** ** CMRA for the empty type *)
Section empty.
  Local Instance Empty_set_valid_instance : Valid Empty_set := λ x, False.
  Local Instance Empty_set_validN_instance : ValidN Empty_set := λ n x, False.
  Local Instance Empty_set_pcore_instance : PCore Empty_set := λ x, Some x.
  Local Instance Empty_set_op_instance : Op Empty_set := λ x y, x.
  Lemma Empty_set_cmra_mixin : CmraMixin Empty_set.
  Proof. apply discrete_cmra_mixin, ra_total_mixin; by (intros [] || done). Qed.
  Canonical Structure Empty_setR : cmra := Cmra Empty_set Empty_set_cmra_mixin.

  Global Instance Empty_set_cmra_discrete : CmraDiscrete Empty_setR.
  Proof. done. Qed.
  Global Instance Empty_set_core_id (x : Empty_set) : CoreId x.
  Proof. by constructor. Qed.
  Global Instance Empty_set_cancelable (x : Empty_set) : Cancelable x.
  Proof. by constructor. Qed.
End empty.

(** ** Product *)
Section prod.
  Context {A B : cmra}.
  Local Arguments pcore _ _ !_ /.
  Local Arguments cmra_pcore _ !_/.

  Local Instance prod_op_instance : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).
  Local Instance prod_pcore_instance : PCore (A * B) := λ x,
    c1 ← pcore (x.1); c2 ← pcore (x.2); Some (c1, c2).
  Local Arguments prod_pcore_instance !_ /.
  Local Instance prod_valid_instance : Valid (A * B) := λ x, ✓ x.1 ∧ ✓ x.2.
  Local Instance prod_validN_instance : ValidN (A * B) := λ n x, ✓{n} x.1 ∧ ✓{n} x.2.

  Lemma prod_pcore_Some (x cx : A * B) :
    pcore x = Some cx ↔ pcore (x.1) = Some (cx.1) ∧ pcore (x.2) = Some (cx.2).
  Proof. destruct x, cx; by intuition simplify_option_eq. Qed.
  Lemma prod_pcore_Some' (x cx : A * B) :
    pcore x ≡ Some cx ↔ pcore (x.1) ≡ Some (cx.1) ∧ pcore (x.2) ≡ Some (cx.2).
  Proof.
    split; [by intros (cx'&[-> ->]%prod_pcore_Some&<-)%Some_equiv_eq|].
    rewrite {3}/pcore /prod_pcore_instance. (* TODO: use setoid rewrite *)
    intros [Hx1 Hx2]; inversion_clear Hx1; simpl; inversion_clear Hx2.
    by constructor.
  Qed.

  Lemma prod_included (x y : A * B) : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2.
  Proof.
    split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
  Qed.
  Lemma prod_includedN (x y : A * B) n : x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2.
  Proof.
    split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
  Qed.

  Definition prod_cmra_mixin : CmraMixin (A * B).
  Proof.
    split; try apply _.
    - by intros n x y1 y2 [Hy1 Hy2]; split; rewrite /= ?Hy1 ?Hy2.
    - intros n x y cx; setoid_rewrite prod_pcore_Some=> -[??] [??].
      destruct (cmra_pcore_ne n (x.1) (y.1) (cx.1)) as (z1&->&?); auto.
      destruct (cmra_pcore_ne n (x.2) (y.2) (cx.2)) as (z2&->&?); auto.
      exists (z1,z2); repeat constructor; auto.
    - by intros n y1 y2 [Hy1 Hy2] [??]; split; rewrite /= -?Hy1 -?Hy2.
    - intros x; split.
      + intros [??] n; split; by apply cmra_valid_validN.
      + intros Hxy; split; apply cmra_valid_validN=> n; apply Hxy.
    - by intros n x [??]; split; apply cmra_validN_S.
    - by split; rewrite /= assoc.
    - by split; rewrite /= comm.
    - intros x y [??]%prod_pcore_Some;
        constructor; simpl; eauto using cmra_pcore_l.
    - intros x y; rewrite prod_pcore_Some prod_pcore_Some'.
      naive_solver eauto using cmra_pcore_idemp.
    - intros x y cx; rewrite prod_included prod_pcore_Some=> -[??] [??].
      destruct (cmra_pcore_mono (x.1) (y.1) (cx.1)) as (z1&?&?); auto.
      destruct (cmra_pcore_mono (x.2) (y.2) (cx.2)) as (z2&?&?); auto.
      exists (z1,z2). by rewrite prod_included prod_pcore_Some.
    - intros n x y [??]; split; simpl in *; eauto using cmra_validN_op_l.
    - intros n x y1 y2 [??] [??]; simpl in *.
      destruct (cmra_extend n (x.1) (y1.1) (y2.1)) as (z11&z12&?&?&?); auto.
      destruct (cmra_extend n (x.2) (y1.2) (y2.2)) as (z21&z22&?&?&?); auto.
      by exists (z11,z21), (z12,z22).
  Qed.
  Canonical Structure prodR := Cmra (prod A B) prod_cmra_mixin.

  Lemma pair_op (a a' : A) (b b' : B) : (a ⋅ a', b ⋅ b') = (a, b) ⋅ (a', b').
  Proof. done. Qed.
  Lemma pair_valid (a : A) (b : B) : ✓ (a, b) ↔ ✓ a ∧ ✓ b.
  Proof. done. Qed.
  Lemma pair_validN (a : A) (b : B) n : ✓{n} (a, b) ↔ ✓{n} a ∧ ✓{n} b.
  Proof. done. Qed.
  Lemma pair_included (a a' : A) (b b' : B) :
    (a, b) ≼ (a', b') ↔ a ≼ a' ∧ b ≼ b'.
  Proof. apply prod_included. Qed.
  Lemma pair_includedN (a a' : A) (b b' : B) n :
    (a, b) ≼{n} (a', b') ↔ a ≼{n} a' ∧ b ≼{n} b'.
  Proof. apply prod_includedN. Qed.
  Lemma pair_pcore (a : A) (b : B) :
    pcore (a, b) = c1 ← pcore a; c2 ← pcore b; Some (c1, c2).
  Proof. done. Qed.
  Lemma pair_core `{!CmraTotal A, !CmraTotal B} (a : A) (b : B) :
    core (a, b) = (core a, core b).
  Proof.
    rewrite /core {1}/pcore /=.
    rewrite (cmra_pcore_core a) /= (cmra_pcore_core b). done.
  Qed.

  Global Instance prod_cmra_total : CmraTotal A → CmraTotal B → CmraTotal prodR.
  Proof.
    intros H1 H2 [a b]. destruct (H1 a) as [ca ?], (H2 b) as [cb ?].
    exists (ca,cb); by simplify_option_eq.
  Qed.

  Global Instance prod_cmra_discrete :
    CmraDiscrete A → CmraDiscrete B → CmraDiscrete prodR.
  Proof. split; [apply _|]. by intros ? []; split; apply cmra_discrete_valid. Qed.

  (* FIXME(Coq #6294): This is not an instance because we need it to use the new
  unification. *)
  Lemma pair_core_id x y :
    CoreId x → CoreId y → CoreId (x,y).
  Proof. by rewrite /CoreId prod_pcore_Some'. Qed.

  Global Instance pair_exclusive_l x y : Exclusive x → Exclusive (x,y).
  Proof. by intros ?[][?%exclusive0_l]. Qed.
  Global Instance pair_exclusive_r x y : Exclusive y → Exclusive (x,y).
  Proof. by intros ?[][??%exclusive0_l]. Qed.

  Global Instance pair_cancelable x y :
    Cancelable x → Cancelable y → Cancelable (x,y).
  Proof. intros ???[][][][]. constructor; simpl in *; by eapply cancelableN. Qed.

  Global Instance pair_id_free_l x y : IdFree x → IdFree (x,y).
  Proof. move=> Hx [a b] [? _] [/=? _]. apply (Hx a); eauto. Qed.
  Global Instance pair_id_free_r x y : IdFree y → IdFree (x,y).
  Proof. move=> Hy [a b] [_ ?] [_ /=?]. apply (Hy b); eauto. Qed.
End prod.

(* Registering as [Hint Extern] with new unification. *)
Global Hint Extern 4 (CoreId _) =>
  notypeclasses refine (pair_core_id _ _ _ _) : typeclass_instances.

Global Arguments prodR : clear implicits.

Section prod_unit.
  Context {A B : ucmra}.

  Local Instance prod_unit_instance `{Unit A, Unit B} : Unit (A * B) := (ε, ε).
  Lemma prod_ucmra_mixin : UcmraMixin (A * B).
  Proof.
    split.
    - split; apply ucmra_unit_valid.
    - by split; rewrite /=left_id.
    - rewrite prod_pcore_Some'; split; apply (core_id _).
  Qed.
  Canonical Structure prodUR := Ucmra (prod A B) prod_ucmra_mixin.

  Lemma pair_split (a : A) (b : B) : (a, b) ≡ (a, ε) ⋅ (ε, b).
  Proof. by rewrite -pair_op left_id right_id. Qed.

  Lemma pair_split_L `{!LeibnizEquiv A, !LeibnizEquiv B} (x : A) (y : B) :
    (x, y) = (x, ε) ⋅ (ε, y).
  Proof. unfold_leibniz. apply pair_split. Qed.

  Lemma pair_op_1 (a a': A) : (a ⋅ a', ε) ≡@{A*B} (a, ε) ⋅ (a', ε).
  Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

  Lemma pair_op_1_L `{!LeibnizEquiv A, !LeibnizEquiv B} (a a': A) :
    (a ⋅ a', ε) =@{A*B} (a, ε) ⋅ (a', ε).
  Proof. unfold_leibniz. apply pair_op_1. Qed.

  Lemma pair_op_2 (b b': B) : (ε, b ⋅ b') ≡@{A*B} (ε, b) ⋅ (ε, b').
  Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

  Lemma pair_op_2_L `{!LeibnizEquiv A, !LeibnizEquiv B} (b b': B) :
    (ε, b ⋅ b') =@{A*B} (ε, b) ⋅ (ε, b').
  Proof. unfold_leibniz. apply pair_op_2. Qed.
End prod_unit.

Global Arguments prodUR : clear implicits.

Global Instance prod_map_cmra_morphism {A A' B B' : cmra} (f : A → A') (g : B → B') :
  CmraMorphism f → CmraMorphism g → CmraMorphism (prod_map f g).
Proof.
  split; first apply _.
  - by intros n x [??]; split; simpl; apply cmra_morphism_validN.
  - intros x. etrans; last apply (reflexivity (mbind _ _)).
    etrans; first apply (reflexivity (_ <$> mbind _ _)). simpl.
    assert (Hf := cmra_morphism_pcore f (x.1)).
    destruct (pcore (f (x.1))), (pcore (x.1)); inversion_clear Hf=>//=.
    assert (Hg := cmra_morphism_pcore g (x.2)).
    destruct (pcore (g (x.2))), (pcore (x.2)); inversion_clear Hg=>//=.
    by setoid_subst.
  - intros. by rewrite /prod_map /= !cmra_morphism_op.
Qed.

Program Definition prodRF (F1 F2 : rFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := prodR (rFunctor_car F1 A B) (rFunctor_car F2 A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    prodO_map (rFunctor_map F1 fg) (rFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 ? A2 ? B1 ? B2 ? n ???.
  by apply prodO_map_ne; apply rFunctor_map_ne.
Qed.
Next Obligation. by intros F1 F2 A ? B ? [??]; rewrite /= !rFunctor_map_id. Qed.
Next Obligation.
  intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [??]; simpl.
  by rewrite !rFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodRF F1%RF F2%RF) : rFunctor_scope.

Global Instance prodRF_contractive F1 F2 :
  rFunctorContractive F1 → rFunctorContractive F2 →
  rFunctorContractive (prodRF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply prodO_map_ne; apply rFunctor_map_contractive.
Qed.

Program Definition prodURF (F1 F2 : urFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := prodUR (urFunctor_car F1 A B) (urFunctor_car F2 A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    prodO_map (urFunctor_map F1 fg) (urFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 ? A2 ? B1 ? B2 ? n ???.
  by apply prodO_map_ne; apply urFunctor_map_ne.
Qed.
Next Obligation. by intros F1 F2 A ? B ? [??]; rewrite /= !urFunctor_map_id. Qed.
Next Obligation.
  intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [??]; simpl.
  by rewrite !urFunctor_map_compose.
Qed.
Notation "F1 * F2" := (prodURF F1%URF F2%URF) : urFunctor_scope.

Global Instance prodURF_contractive F1 F2 :
  urFunctorContractive F1 → urFunctorContractive F2 →
  urFunctorContractive (prodURF F1 F2).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n ???;
    by apply prodO_map_ne; apply urFunctor_map_contractive.
Qed.

(** ** CMRA for the option type *)
Section option.
  Context {A : cmra}.
  Implicit Types a b : A.
  Implicit Types ma mb : option A.
  Local Arguments core _ _ !_ /.
  Local Arguments pcore _ _ !_ /.

  Local Instance option_valid_instance : Valid (option A) := λ ma,
    match ma with Some a => ✓ a | None => True end.
  Local Instance option_validN_instance : ValidN (option A) := λ n ma,
    match ma with Some a => ✓{n} a | None => True end.
  Local Instance option_pcore_instance : PCore (option A) := λ ma,
    Some (ma ≫= pcore).
  Local Arguments option_pcore_instance !_ /.
  Local Instance option_op_instance : Op (option A) :=
    union_with (λ a b, Some (a ⋅ b)).

  Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.
  Definition Some_validN a n : ✓{n} Some a ↔ ✓{n} a := reflexivity _.
  Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.
  Lemma Some_core `{!CmraTotal A} a : Some (core a) = core (Some a).
  Proof. rewrite /core /=. by destruct (cmra_total a) as [? ->]. Qed.
  Lemma pcore_Some a : pcore (Some a) = Some (pcore a).
  Proof. done. Qed.
  Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma).
  Proof. by destruct ma. Qed.

  Lemma option_included ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a ≡ b ∨ a ≼ b).
  Proof.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto;
        setoid_subst; eauto.
    - intros [->|(a&b&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None; by constructor.
      + exists (Some c); by constructor.
  Qed.
  Lemma option_included_total `{!CmraTotal A} ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ a ≼ b.
  Proof.
    rewrite option_included. split; last naive_solver.
    intros [->|(a&b&->&->&[Hab|?])]; [by eauto| |by eauto 10].
    right. exists a, b. by rewrite {3}Hab.
  Qed.

  Lemma option_includedN n ma mb :
    ma ≼{n} mb ↔ ma = None ∨
                 ∃ x y, ma = Some x ∧ mb = Some y ∧ (x ≡{n}≡ y ∨ x ≼{n} y).
  Proof.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto;
        ofe_subst; eauto using cmra_includedN_l.
    - intros [->|(a&y&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None; by constructor.
      + exists (Some c); by constructor.
  Qed.
  Lemma option_includedN_total `{!CmraTotal A} n ma mb :
    ma ≼{n} mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ a ≼{n} b.
  Proof.
    rewrite option_includedN. split; last naive_solver.
    intros [->|(a&b&->&->&[Hab|?])]; [by eauto| |by eauto 10].
    right. exists a, b. by rewrite {3}Hab.
  Qed.

  (* See below for more [included] lemmas. *)

  Lemma option_cmra_mixin : CmraMixin (option A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - by intros [a|] n; destruct 1; constructor; ofe_subst.
    - destruct 1; by ofe_subst.
    - by destruct 1; rewrite /validN /option_validN_instance //=; ofe_subst.
    - intros [a|]; [apply cmra_valid_validN|done].
    - intros n [a|];
        unfold validN, option_validN_instance; eauto using cmra_validN_S.
    - intros [a|] [b|] [c|]; constructor; rewrite ?assoc; auto.
    - intros [a|] [b|]; constructor; rewrite 1?comm; auto.
    - intros [a|]; simpl; auto.
      destruct (pcore a) as [ca|] eqn:?; constructor; eauto using cmra_pcore_l.
    - intros [a|]; simpl; auto.
      destruct (pcore a) as [ca|] eqn:?; simpl; eauto using cmra_pcore_idemp.
    - intros ma mb; setoid_rewrite option_included.
      intros [->|(a&b&->&->&[?|?])]; simpl; eauto.
      + destruct (pcore a) as [ca|] eqn:?; eauto.
        destruct (cmra_pcore_proper a b ca) as (?&?&?); eauto 10.
      + destruct (pcore a) as [ca|] eqn:?; eauto.
        destruct (cmra_pcore_mono a b ca) as (?&?&?); eauto 10.
    - intros n [a|] [b|]; rewrite /validN /option_validN_instance /=;
        eauto using cmra_validN_op_l.
    - intros n ma mb1 mb2.
      destruct ma as [a|], mb1 as [b1|], mb2 as [b2|]; intros Hx Hx';
        (try by exfalso; inversion Hx'); (try (apply (inj Some) in Hx')).
      + destruct (cmra_extend n a b1 b2) as (c1&c2&?&?&?); auto.
        by exists (Some c1), (Some c2); repeat constructor.
      + by exists (Some a), None; repeat constructor.
      + by exists None, (Some a); repeat constructor.
      + exists None, None; repeat constructor.
  Qed.
  Canonical Structure optionR := Cmra (option A) option_cmra_mixin.

  Global Instance option_cmra_discrete : CmraDiscrete A → CmraDiscrete optionR.
  Proof. split; [apply _|]. by intros [a|]; [apply (cmra_discrete_valid a)|]. Qed.

  Local Instance option_unit_instance : Unit (option A) := None.
  Lemma option_ucmra_mixin : UcmraMixin optionR.
  Proof. split; [done|  |done]. by intros []. Qed.
  Canonical Structure optionUR := Ucmra (option A) option_ucmra_mixin.

  (** Misc *)
  Lemma op_None ma mb : ma ⋅ mb = None ↔ ma = None ∧ mb = None.
  Proof. destruct ma, mb; naive_solver. Qed.
  Lemma op_is_Some ma mb : is_Some (ma ⋅ mb) ↔ is_Some ma ∨ is_Some mb.
  Proof. rewrite -!not_eq_None_Some op_None. destruct ma, mb; naive_solver. Qed.
  (* When the goal is already of the form [None ⋅ x], the [LeftId] instance for
     [ε] does not fire. *)
  Global Instance op_None_left_id : LeftId (=) None (@op (option A) _).
  Proof. intros [a|]; done. Qed.
  Global Instance op_None_right_id : RightId (=) None (@op (option A) _).
  Proof. intros [a|]; done. Qed.

  Lemma cmra_opM_opM_assoc a mb mc : a ⋅? mb ⋅? mc ≡ a ⋅? (mb ⋅ mc).
  Proof. destruct mb, mc; by rewrite /= -?assoc. Qed.
  Lemma cmra_opM_opM_assoc_L `{!LeibnizEquiv A} a mb mc :
    a ⋅? mb ⋅? mc = a ⋅? (mb ⋅ mc).
  Proof. unfold_leibniz. apply cmra_opM_opM_assoc. Qed.
  Lemma cmra_opM_opM_swap a mb mc : a ⋅? mb ⋅? mc ≡ a ⋅? mc ⋅? mb.
  Proof. by rewrite !cmra_opM_opM_assoc (comm _ mb). Qed.
  Lemma cmra_opM_opM_swap_L `{!LeibnizEquiv A} a mb mc :
    a ⋅? mb ⋅? mc = a ⋅? mc ⋅? mb.
  Proof. by rewrite !cmra_opM_opM_assoc_L (comm_L _ mb). Qed.
  Lemma cmra_opM_fmap_Some ma1 ma2 : ma1 ⋅? (Some <$> ma2) = ma1 ⋅ ma2.
  Proof. by destruct ma1, ma2. Qed.

  Global Instance Some_core_id a : CoreId a → CoreId (Some a).
  Proof. by constructor. Qed.
  Global Instance option_core_id ma : (∀ x : A, CoreId x) → CoreId ma.
  Proof. intros. destruct ma; apply _. Qed.

  Lemma exclusiveN_Some_l n a `{!Exclusive a} mb :
    ✓{n} (Some a ⋅ mb) → mb = None.
  Proof. destruct mb; last done. move=> /(exclusiveN_l _ a) []. Qed.
  Lemma exclusiveN_Some_r n a `{!Exclusive a} mb :
    ✓{n} (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply exclusiveN_Some_l. Qed.

  Lemma exclusive_Some_l a `{!Exclusive a} mb : ✓ (Some a ⋅ mb) → mb = None.
  Proof. destruct mb; last done. move=> /(exclusive_l a) []. Qed.
  Lemma exclusive_Some_r a `{!Exclusive a} mb : ✓ (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply exclusive_Some_l. Qed.

  Lemma Some_includedN n a b : Some a ≼{n} Some b ↔ a ≡{n}≡ b ∨ a ≼{n} b.
  Proof. rewrite option_includedN; naive_solver. Qed.
  Lemma Some_includedN_1 n a b : Some a ≼{n} Some b → a ≡{n}≡ b ∨ a ≼{n} b.
  Proof. rewrite Some_includedN. auto. Qed.
  Lemma Some_includedN_2 n a b : a ≡{n}≡ b ∨ a ≼{n} b → Some a ≼{n} Some b.
  Proof. rewrite Some_includedN. auto. Qed.
  Lemma Some_includedN_mono n a b : a ≼{n} b → Some a ≼{n} Some b.
  Proof. rewrite Some_includedN. auto. Qed.
  Lemma Some_includedN_refl n a b : a ≡{n}≡ b → Some a ≼{n} Some b.
  Proof. rewrite Some_includedN. auto. Qed.
  Lemma Some_includedN_is_Some n x mb : Some x ≼{n} mb → is_Some mb.
  Proof. rewrite option_includedN. naive_solver. Qed.

  Lemma Some_included a b : Some a ≼ Some b ↔ a ≡ b ∨ a ≼ b.
  Proof. rewrite option_included; naive_solver. Qed.
  Lemma Some_included_1 a b : Some a ≼ Some b → a ≡ b ∨ a ≼ b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_2 a b : a ≡ b ∨ a ≼ b → Some a ≼ Some b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_mono a b : a ≼ b → Some a ≼ Some b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_refl a b : a ≡ b → Some a ≼ Some b.
  Proof. rewrite Some_included. auto. Qed.
  Lemma Some_included_is_Some x mb : Some x ≼ mb → is_Some mb.
  Proof. rewrite option_included. naive_solver. Qed.

  Lemma Some_includedN_opM n a b : Some a ≼{n} Some b ↔ ∃ mc, b ≡{n}≡ a ⋅? mc.
  Proof.
    rewrite /includedN. f_equiv=> mc. by rewrite -(inj_iff Some b) Some_op_opM.
  Qed.
  Lemma Some_included_opM a b : Some a ≼ Some b ↔ ∃ mc, b ≡ a ⋅? mc.
  Proof.
    rewrite /included. f_equiv=> mc. by rewrite -(inj_iff Some b) Some_op_opM.
  Qed.

  Lemma cmra_validN_Some_includedN n a b : ✓{n} a → Some b ≼{n} Some a → ✓{n} b.
  Proof. apply: (cmra_validN_includedN _ (Some _) (Some _)). Qed.
  Lemma cmra_valid_Some_included a b : ✓ a → Some b ≼ Some a → ✓ b.
  Proof. apply: (cmra_valid_included (Some _) (Some _)). Qed.

  Lemma Some_includedN_total `{!CmraTotal A} n a b : Some a ≼{n} Some b ↔ a ≼{n} b.
  Proof. rewrite Some_includedN. split; [|by eauto]. by intros [->|?]. Qed.
  Lemma Some_included_total `{!CmraTotal A} a b : Some a ≼ Some b ↔ a ≼ b.
  Proof. rewrite Some_included. split; [|by eauto]. by intros [->|?]. Qed.

  Lemma Some_includedN_exclusive n a `{!Exclusive a} b :
    Some a ≼{n} Some b → ✓{n} b → a ≡{n}≡ b.
  Proof. move=> /Some_includedN [//|/exclusive_includedN]; tauto. Qed.
  Lemma Some_included_exclusive a `{!Exclusive a} b :
    Some a ≼ Some b → ✓ b → a ≡ b.
  Proof. move=> /Some_included [//|/exclusive_included]; tauto. Qed.

  Lemma is_Some_includedN n ma mb : ma ≼{n} mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_includedN. naive_solver. Qed.
  Lemma is_Some_included ma mb : ma ≼ mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_included. naive_solver. Qed.

  Global Instance cancelable_Some a :
    IdFree a → Cancelable a → Cancelable (Some a).
  Proof.
    intros Hirr ? n [b|] [c|] ? EQ; inversion_clear EQ.
    - constructor. by apply (cancelableN a).
    - destruct (Hirr b); [|eauto using dist_le with lia].
      by eapply (cmra_validN_op_l 0 a b), (cmra_validN_le n); last lia.
    - destruct (Hirr c); [|symmetry; eauto using dist_le with lia].
      by eapply (cmra_validN_le n); last lia.
    - done.
  Qed.

  Global Instance option_cancelable (ma : option A) :
    (∀ a : A, IdFree a) → (∀ a : A, Cancelable a) → Cancelable ma.
  Proof. destruct ma; apply _. Qed.
End option.

Global Arguments optionR : clear implicits.
Global Arguments optionUR : clear implicits.

Section option_prod.
  Context {A B : cmra}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma Some_pair_includedN n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ Some b1 ≼{n} Some b2.
  Proof. rewrite !Some_includedN. intros [[??]|[??]%prod_includedN]; eauto. Qed.
  Lemma Some_pair_includedN_l n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2.
  Proof. intros. eapply Some_pair_includedN. done. Qed.
  Lemma Some_pair_includedN_r n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → Some b1 ≼{n} Some b2.
  Proof. intros. eapply Some_pair_includedN. done. Qed.
  Lemma Some_pair_includedN_total_1 `{CmraTotal A} n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → a1 ≼{n} a2 ∧ Some b1 ≼{n} Some b2.
  Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ a1). Qed.
  Lemma Some_pair_includedN_total_2 `{CmraTotal B} n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ b1 ≼{n} b2.
  Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ b1). Qed.

  Lemma Some_pair_included a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ Some b1 ≼ Some b2.
  Proof. rewrite !Some_included. intros [[??]|[??]%prod_included]; eauto. Qed.
  Lemma Some_pair_included_l a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2.
  Proof. intros. eapply Some_pair_included. done. Qed.
  Lemma Some_pair_included_r a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some b1 ≼ Some b2.
  Proof. intros. eapply Some_pair_included. done. Qed.
  Lemma Some_pair_included_total_1 `{CmraTotal A} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → a1 ≼ a2 ∧ Some b1 ≼ Some b2.
  Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total a1). Qed.
  Lemma Some_pair_included_total_2 `{CmraTotal B} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ b1 ≼ b2.
  Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total b1). Qed.
End option_prod.

Lemma option_fmap_mono {A B : cmra} (f : A → B) (ma mb : option A) :
  Proper ((≡) ==> (≡)) f →
  (∀ a b, a ≼ b → f a ≼ f b) →
  ma ≼ mb → f <$> ma ≼ f <$> mb.
Proof.
  intros ??. rewrite !option_included; intros [->|(a&b&->&->&?)]; naive_solver.
Qed.

Global Instance option_fmap_cmra_morphism {A B : cmra} (f: A → B) `{!CmraMorphism f} :
  CmraMorphism (fmap f : option A → option B).
Proof.
  split; first apply _.
  - intros n [a|] ?; rewrite /cmra_validN //=. by apply (cmra_morphism_validN f).
  - move=> [a|] //. by apply Some_proper, cmra_morphism_pcore.
  - move=> [a|] [b|] //=. by rewrite (cmra_morphism_op f).
Qed.

Program Definition optionURF (F : rFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := optionUR (rFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg := optionO_map (rFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  by apply optionO_map_ne, rFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply rFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x.
  rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply rFunctor_map_compose.
Qed.

Global Instance optionURF_contractive F :
  rFunctorContractive F → urFunctorContractive (optionURF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  by apply optionO_map_ne, rFunctor_map_contractive.
Qed.

Program Definition optionRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := optionR (rFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := optionO_map (rFunctor_map F fg)
|}.
Solve Obligations with apply optionURF.

Global Instance optionRF_contractive F :
  rFunctorContractive F → rFunctorContractive (optionRF F).
Proof. apply optionURF_contractive. Qed.

(* Dependently-typed functions over a discrete domain *)
Section discrete_fun_cmra.
  Context {A : Type} {B : A → ucmra}.
  Implicit Types f g : discrete_fun B.

  Local Instance discrete_fun_op_instance : Op (discrete_fun B) := λ f g x,
    f x ⋅ g x.
  Local Instance discrete_fun_pcore_instance : PCore (discrete_fun B) := λ f,
    Some (λ x, core (f x)).
  Local Instance discrete_fun_valid_instance : Valid (discrete_fun B) := λ f,
    ∀ x, ✓ f x.
  Local Instance discrete_fun_validN_instance : ValidN (discrete_fun B) := λ n f,
    ∀ x, ✓{n} f x.

  Definition discrete_fun_lookup_op f g x : (f ⋅ g) x = f x ⋅ g x := eq_refl.
  Definition discrete_fun_lookup_core f x : (core f) x = core (f x) := eq_refl.

  Lemma discrete_fun_included_spec_1 (f g : discrete_fun B) x : f ≼ g → f x ≼ g x.
  Proof.
    by intros [h Hh]; exists (h x); rewrite /op /discrete_fun_op_instance (Hh x).
  Qed.

  Lemma discrete_fun_included_spec `{Hfin : Finite A} (f g : discrete_fun B) :
    f ≼ g ↔ ∀ x, f x ≼ g x.
  Proof.
    split; [by intros; apply discrete_fun_included_spec_1|].
    intros [h ?]%finite_choice; by exists h.
  Qed.

  Lemma discrete_fun_cmra_mixin : CmraMixin (discrete_fun B).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - intros n f1 f2 f3 Hf x. by rewrite discrete_fun_lookup_op (Hf x).
    - intros n f1 f2 Hf x. by rewrite discrete_fun_lookup_core (Hf x).
    - intros n f1 f2 Hf ? x. by rewrite -(Hf x).
    - intros g; split.
      + intros Hg n i; apply cmra_valid_validN, Hg.
      + intros Hg i; apply cmra_valid_validN=> n; apply Hg.
    - intros n f Hf x; apply cmra_validN_S, Hf.
    - intros f1 f2 f3 x. by rewrite discrete_fun_lookup_op assoc.
    - intros f1 f2 x. by rewrite discrete_fun_lookup_op comm.
    - intros f x.
      by rewrite discrete_fun_lookup_op discrete_fun_lookup_core cmra_core_l.
    - intros f x. by rewrite discrete_fun_lookup_core cmra_core_idemp.
    - intros f1 f2 Hf12. exists (core f2)=>x. rewrite discrete_fun_lookup_op.
      apply (discrete_fun_included_spec_1 _ _ x), (cmra_core_mono (f1 x)) in Hf12.
      rewrite !discrete_fun_lookup_core. destruct Hf12 as [? ->].
      rewrite assoc -cmra_core_dup //.
    - intros n f1 f2 Hf x. apply cmra_validN_op_l with (f2 x), Hf.
    - intros n f f1 f2 Hf Hf12.
      assert (FUN := λ x, cmra_extend n (f x) (f1 x) (f2 x) (Hf x) (Hf12 x)).
      exists (λ x, projT1 (FUN x)), (λ x, proj1_sig (projT2 (FUN x))).
      split; [|split]=>x; [rewrite discrete_fun_lookup_op| |];
        by destruct (FUN x) as (?&?&?&?&?).
  Qed.
  Canonical Structure discrete_funR :=
    Cmra (discrete_fun B) discrete_fun_cmra_mixin.

  Local Instance discrete_fun_unit_instance : Unit (discrete_fun B) := λ x, ε.
  Definition discrete_fun_lookup_empty x : ε x = ε := eq_refl.

  Lemma discrete_fun_ucmra_mixin : UcmraMixin (discrete_fun B).
  Proof.
    split.
    - intros x. apply ucmra_unit_valid.
    - intros f x. by rewrite discrete_fun_lookup_op left_id.
    - constructor=> x. apply core_id_core, _.
  Qed.
  Canonical Structure discrete_funUR :=
    Ucmra (discrete_fun B) discrete_fun_ucmra_mixin.

  Global Instance discrete_fun_unit_discrete :
    (∀ i, Discrete (ε : B i)) → Discrete (ε : discrete_fun B).
  Proof. intros ? f Hf x. by apply: discrete. Qed.
End discrete_fun_cmra.

Global Arguments discrete_funR {_} _.
Global Arguments discrete_funUR {_} _.

Global Instance discrete_fun_map_cmra_morphism {A} {B1 B2 : A → ucmra}
    (f : ∀ x, B1 x → B2 x) :
  (∀ x, CmraMorphism (f x)) → CmraMorphism (discrete_fun_map f).
Proof.
  split; first apply _.
  - intros n g Hg x. rewrite /discrete_fun_map.
    apply (cmra_morphism_validN (f _)), Hg.
  - intros. apply Some_proper=>i. apply (cmra_morphism_core (f i)).
  - intros g1 g2 i.
    by rewrite /discrete_fun_map discrete_fun_lookup_op cmra_morphism_op.
Qed.

Program Definition discrete_funURF {C} (F : C → urFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := discrete_funUR (λ c, urFunctor_car (F c) A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    discrete_funO_map (λ c, urFunctor_map (F c) fg)
|}.
Next Obligation.
  intros C F A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=>?; apply urFunctor_map_ne.
Qed.
Next Obligation.
  intros C F A ? B ? g; simpl. rewrite -{2}(discrete_fun_map_id g).
  apply discrete_fun_map_ext=> y; apply urFunctor_map_id.
Qed.
Next Obligation.
  intros C F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f1 f2 f1' f2' g.
  rewrite /=-discrete_fun_map_compose.
  apply discrete_fun_map_ext=> y; apply urFunctor_map_compose.
Qed.
Global Instance discrete_funURF_contractive {C} (F : C → urFunctor) :
  (∀ c, urFunctorContractive (F c)) → urFunctorContractive (discrete_funURF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n ?? g.
  by apply discrete_funO_map_ne=> c; apply urFunctor_map_contractive.
Qed.

(** * Constructing a camera [B] through a mapping into [A]

The mapping may restrict the domain (i.e., we have an injection from [B] to [A],
not a bijection) and validity. These two restrictions work on opposite "ends" of
[A] according to [≼]: domain restriction must prove that when an element is in
the domain, so is its composition with other elements; validity restriction must
prove that if the composition of two elements is valid, then so are both of the
elements. The "domain" is the image of [g] in [A], or equivalently the part of
[A] where [f] returns [Some]. *)
Lemma inj_cmra_mixin_restrict_validity {A : cmra} {B : ofe}
  `{!PCore B, !Op B, !Valid B, !ValidN B}
  (f : A → option B) (g : B → A)
  (* [g] is proper/non-expansive and injective w.r.t. OFE equality *)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (* [g] is surjective into the part of [A] where [is_Some ∘ f] holds
  (and [f] its inverse) *)
  (gf_dist : ∀ (x : A) (y : B) n, f x ≡{n}≡ Some y ↔ g y ≡{n}≡ x)
  (* [g] commutes with [pcore] (on the part where it is defined) and [op] *)
  (g_pcore_dist : ∀ (y cy : B) n,
    pcore y ≡{n}≡ Some cy ↔ pcore (g y) ≡{n}≡ Some (g cy))
  (g_op : ∀ (y1 y2 : B), g (y1 ⋅ y2) ≡ g y1 ⋅ g y2)
  (* [g] also commutes with [opM] when the right-hand side is produced by [f],
  and cancels the [f]. In particular this axiom implies that when taking an
  element in the domain ([g y]), its composition with *any* [x : A] is still in
  the domain, and [f] computes the preimage properly.
  Note that just requiring "the composition of two elements from the domain
  is in the domain" is insufficient for this lemma to hold. [g_op] already shows
  that this is the case, but the issue is that in [pcore_mono] we obtain a
  [g y1 ≼ g y2], and the existentially quantified "remainder" in the [≼] has no
  reason to be in the domain, so [g_op] is too weak to turn this into some
  relation between [y1] and [y2] in [B]. At the same time, [g_opM_f] does not
  impl [g_op] since we need [g_op] to prove that [⋅] in [B] respects [≡].
  Therefore both [g_op] and [g_opM_f] are required for this lemma to work. *)
  (g_opM_f : ∀ (x : A) (y : B), g (y ⋅? f x) ≡ g y ⋅ x)
  (* The validity predicate on [B] restricts the one on [A] *)
  (g_validN : ∀ n y, ✓{n} y → ✓{n} (g y))
  (* The validity predicate on [B] satisfies the laws of validity *)
  (valid_validN_ne : ∀ n, Proper (dist n ==> impl) (validN (A:=B) n))
  (valid_rvalidN : ∀ y : B, ✓ y ↔ ∀ n, ✓{n} y)
  (validN_S : ∀ n (y : B), ✓{S n} y → ✓{n} y)
  (validN_op_l : ∀ n (y1 y2 : B), ✓{n} (y1 ⋅ y2) → ✓{n} y1) :
  CmraMixin B.
Proof.
  (* Some general derived facts that will be useful later. *)
  assert (g_equiv : ∀ y1 y2, y1 ≡ y2 ↔ g y1 ≡ g y2).
  { intros ??. rewrite !equiv_dist. naive_solver. }
  assert (g_pcore : ∀ (y cy : B),
    pcore y ≡ Some cy ↔ pcore (g y) ≡ Some (g cy)).
  { intros. rewrite !equiv_dist. naive_solver. }
  assert (gf : ∀ x y, f x ≡ Some y ↔ g y ≡ x).
  { intros. rewrite !equiv_dist. naive_solver. }
  assert (fg : ∀ y, f (g y) ≡ Some y).
  { intros. apply gf. done. }
  assert (g_ne : NonExpansive g).
  { intros n ???. apply g_dist. done. }
  (* Some of the CMRA properties are useful in proving the others. *)
  assert (b_pcore_l' : ∀ y cy : B, pcore y ≡ Some cy → cy ⋅ y ≡ y).
  { intros y cy Hy. apply g_equiv. rewrite g_op. apply cmra_pcore_l'.
    apply g_pcore. done. }
  assert (b_pcore_idemp : ∀ y cy : B, pcore y ≡ Some cy → pcore cy ≡ Some cy).
  { intros y cy Hy. eapply g_pcore, cmra_pcore_idemp', g_pcore. done. }
  (* Now prove all the mixin laws. *)
  split.
  - intros y n z1 z2 Hz%g_dist. apply g_dist. by rewrite !g_op Hz.
  - intros n y1 y2 cy Hy%g_dist Hy1.
    assert (g <$> pcore y2 ≡{n}≡ Some (g cy))
      as (cx & (cy'&->&->)%fmap_Some_1 & ?%g_dist)%dist_Some_inv_r'; [|by eauto].
    assert (Hgcy : pcore (g y1) ≡ Some (g cy)).
    { apply g_pcore. rewrite Hy1. done. }
    rewrite equiv_dist in Hgcy. specialize (Hgcy n).
    rewrite Hy in Hgcy. apply g_pcore_dist in Hgcy. rewrite Hgcy. done.
  - done.
  - done.
  - done.
  - intros y1 y2 y3. apply g_equiv. by rewrite !g_op assoc.
  - intros y1 y2. apply g_equiv. by rewrite !g_op comm.
  - intros y cy Hcy. apply b_pcore_l'. by rewrite Hcy.
  - intros y cy Hcy. eapply b_pcore_idemp. by rewrite -Hcy.
  - intros y1 y2 cy [z Hy2] Hy1.
    destruct (cmra_pcore_mono' (g y1) (g y2) (g cy)) as (cx&Hcgy2&[x Hcx]).
    { exists (g z). rewrite -g_op. by apply g_equiv. }
    { apply g_pcore. rewrite Hy1 //. }
    apply (reflexive_eq (R:=equiv)) in Hcgy2.
    rewrite -g_opM_f in Hcx. rewrite Hcx in Hcgy2.
    apply g_pcore in Hcgy2.
    apply Some_equiv_eq in Hcgy2 as [cy' [-> Hcy']].
    eexists. split; first done.
    destruct (f x) as [y|].
    + exists y. done.
    + exists cy. apply (reflexive_eq (R:=equiv)), b_pcore_idemp, b_pcore_l' in Hy1.
      rewrite Hy1 //.
  - done.
  - intros n y z1 z2 ?%g_validN ?.
    destruct (cmra_extend n (g y) (g z1) (g z2)) as (x1&x2&Hgy&Hx1&Hx2).
    { done. }
    { rewrite -g_op. by apply g_dist. }
    symmetry in Hx1, Hx2.
    apply gf_dist in Hx1, Hx2.
    destruct (f x1) as [y1|] eqn:Hy1; last first.
    { exfalso. inversion Hx1. }
    destruct (f x2) as [y2|] eqn:Hy2; last first.
    { exfalso. inversion Hx2. }
    exists y1, y2. split_and!.
    + apply g_equiv. rewrite Hgy g_op.
      f_equiv; symmetry; apply gf; rewrite ?Hy1 ?Hy2 //.
    + apply g_dist. apply (inj Some) in Hx1. rewrite Hx1 //.
    + apply g_dist. apply (inj Some) in Hx2. rewrite Hx2 //.
Qed.

(** Constructing a CMRA through an isomorphism that may restrict validity. *)
Lemma iso_cmra_mixin_restrict_validity {A : cmra} {B : ofe}
  `{!PCore B, !Op B, !Valid B, !ValidN B}
  (f : A → B) (g : B → A)
  (* [g] is proper/non-expansive and injective w.r.t. setoid and OFE equality *)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (* [g] is surjective (and [f] its inverse) *)
  (gf : ∀ x : A, g (f x) ≡ x)
  (* [g] commutes with [pcore] and [op] *)
  (g_pcore : ∀ y : B, pcore (g y) ≡ g <$> pcore y)
  (g_op : ∀ y1 y2, g (y1 ⋅ y2) ≡ g y1 ⋅ g y2)
  (* The validity predicate on [B] restricts the one on [A] *)
  (g_validN : ∀ n y, ✓{n} y → ✓{n} (g y))
  (* The validity predicate on [B] satisfies the laws of validity *)
  (valid_validN_ne : ∀ n, Proper (dist n ==> impl) (validN (A:=B) n))
  (valid_rvalidN : ∀ y : B, ✓ y ↔ ∀ n, ✓{n} y)
  (validN_S : ∀ n (y : B), ✓{S n} y → ✓{n} y)
  (validN_op_l : ∀ n (y1 y2 : B), ✓{n} (y1 ⋅ y2) → ✓{n} y1) :
  CmraMixin B.
Proof.
  assert (g_ne : NonExpansive g).
  { intros n ???. apply g_dist. done. }
  assert (g_equiv : ∀ y1 y2, y1 ≡ y2 ↔ g y1 ≡ g y2).
  { intros ??.
    split; intros ?; apply equiv_dist; intros; apply g_dist, equiv_dist; done. }
  apply (inj_cmra_mixin_restrict_validity (λ x, Some (f x)) g); try done.
  - intros. split.
    + intros Hy%(inj Some). rewrite -Hy gf //.
    + intros ?. f_equiv. apply g_dist. rewrite gf. done.
  - intros. rewrite g_pcore. split.
    + intros ->. done.
    + intros (? & -> & ->%g_dist)%fmap_Some_dist. done.
  - intros ??. simpl. rewrite g_op gf //.
Qed.

(** * Constructing a camera through an isomorphism *)
Lemma iso_cmra_mixin {A : cmra} {B : ofe}
  `{!PCore B, !Op B, !Valid B, !ValidN B}
  (f : A → B) (g : B → A)
  (* [g] is proper/non-expansive and injective w.r.t. OFE equality *)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (* [g] is surjective (and [f] its inverse) *)
  (gf : ∀ x : A, g (f x) ≡ x)
  (* [g] commutes with [pcore], [op], [valid], and [validN] *)
  (g_pcore : ∀ y : B, pcore (g y) ≡ g <$> pcore y)
  (g_op : ∀ y1 y2, g (y1 ⋅ y2) ≡ g y1 ⋅ g y2)
  (g_valid : ∀ y, ✓ (g y) ↔ ✓ y)
  (g_validN : ∀ n y, ✓{n} (g y) ↔ ✓{n} y) :
  CmraMixin B.
Proof.
  apply (iso_cmra_mixin_restrict_validity f g); auto.
  - by intros n y ?%g_validN.
  - intros n y1 y2 Hy%g_dist Hy1. by rewrite -g_validN -Hy g_validN.
  - intros y. rewrite -g_valid cmra_valid_validN. naive_solver.
  - intros n y. rewrite -!g_validN. apply cmra_validN_S.
  - intros n y1 y2. rewrite -!g_validN g_op. apply cmra_validN_op_l.
Qed.
