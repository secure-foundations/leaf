(** This file collects general purpose definitions and theorems on the option
data type that are not in the Coq standard library. *)
From stdpp Require Export tactics.
From stdpp Require Import options.

Inductive option_reflect {A} (P : A → Prop) (Q : Prop) : option A → Type :=
  | ReflectSome x : P x → option_reflect P Q (Some x)
  | ReflectNone : Q → option_reflect P Q None.

(** * General definitions and theorems *)
(** Basic properties about equality. *)
Lemma None_ne_Some {A} (x : A) : None ≠ Some x.
Proof. congruence. Qed.
Lemma Some_ne_None {A} (x : A) : Some x ≠ None.
Proof. congruence. Qed.
Lemma eq_None_ne_Some {A} (mx : option A) : (∀ x, mx ≠ Some x) ↔ mx = None.
Proof. destruct mx; split; congruence. Qed.
Lemma eq_None_ne_Some_1 {A} (mx : option A) x : mx = None → mx ≠ Some x.
Proof. intros ?. by apply eq_None_ne_Some. Qed.
Lemma eq_None_ne_Some_2 {A} (mx : option A) : (∀ x, mx ≠ Some x) → mx = None.
Proof. intros ?. by apply eq_None_ne_Some. Qed.
Global Instance Some_inj {A} : Inj (=) (=) (@Some A).
Proof. congruence. Qed.

(** The [from_option] is the eliminator for option. *)
Definition from_option {A B} (f : A → B) (y : B) (mx : option A) : B :=
  match mx with None => y | Some x => f x end.
Global Instance: Params (@from_option) 2 := {}.
Global Arguments from_option {_ _} _ _ !_ / : assert.

(** The eliminator with the identity function. *)
Notation default := (from_option id).

(** An alternative, but equivalent, definition of equality on the option
data type. This theorem is useful to prove that two options are the same. *)
Lemma option_eq {A} (mx my: option A): mx = my ↔ ∀ x, mx = Some x ↔ my = Some x.
Proof. split; [by intros; by subst |]. destruct mx, my; naive_solver. Qed.
Lemma option_eq_1 {A} (mx my: option A) x : mx = my → mx = Some x → my = Some x.
Proof. congruence. Qed.
Lemma option_eq_1_alt {A} (mx my : option A) x :
  mx = my → my = Some x → mx = Some x.
Proof. congruence. Qed.

Definition is_Some {A} (mx : option A) := ∃ x, mx = Some x.
Global Instance: Params (@is_Some) 1 := {}.

(** We avoid calling [done] recursively as that can lead to an unresolved evar. *)
Global Hint Extern 0 (is_Some _) => eexists; fast_done : core.

Lemma is_Some_alt {A} (mx : option A) :
  is_Some mx ↔ match mx with Some _ => True | None => False end.
Proof. unfold is_Some. destruct mx; naive_solver. Qed.

Lemma mk_is_Some {A} (mx : option A) x : mx = Some x → is_Some mx.
Proof. by intros ->. Qed.
Global Hint Resolve mk_is_Some : core.
Lemma is_Some_None {A} : ¬is_Some (@None A).
Proof. by destruct 1. Qed.
Global Hint Resolve is_Some_None : core.

Lemma eq_None_not_Some {A} (mx : option A) : mx = None ↔ ¬is_Some mx.
Proof. rewrite is_Some_alt; destruct mx; naive_solver. Qed.
Lemma not_eq_None_Some {A} (mx : option A) : mx ≠ None ↔ is_Some mx.
Proof. rewrite is_Some_alt; destruct mx; naive_solver. Qed.

Global Instance is_Some_pi {A} (mx : option A) : ProofIrrel (is_Some mx).
Proof.
  set (P (mx : option A) := match mx with Some _ => True | _ => False end).
  set (f mx := match mx return P mx → is_Some mx with
    Some _ => λ _, ex_intro _ _ eq_refl | None => False_rect _ end).
  set (g mx (H : is_Some mx) :=
    match H return P mx with ex_intro _ _ p => eq_rect _ _ I _ (eq_sym p) end).
  assert (∀ mx H, f mx (g mx H) = H) as f_g by (by intros ? [??]; subst).
  intros p1 p2. rewrite <-(f_g _ p1), <-(f_g _ p2). by destruct mx, p1.
Qed.

Global Instance is_Some_dec {A} (mx : option A) : Decision (is_Some mx) :=
  match mx with
  | Some x => left (ex_intro _ x eq_refl)
  | None => right is_Some_None
  end.

Definition is_Some_proj {A} {mx : option A} : is_Some mx → A :=
  match mx with Some x => λ _, x | None => False_rect _ ∘ is_Some_None end.

Definition Some_dec {A} (mx : option A) : { x | mx = Some x } + { mx = None } :=
  match mx return { x | mx = Some x } + { mx = None } with
  | Some x => inleft (x ↾ eq_refl _)
  | None => inright eq_refl
  end.

(** Lifting a relation point-wise to option *)
Inductive option_Forall2 {A B} (R: A → B → Prop) : option A → option B → Prop :=
  | Some_Forall2 x y : R x y → option_Forall2 R (Some x) (Some y)
  | None_Forall2 : option_Forall2 R None None.
Definition option_relation {A B} (R: A → B → Prop) (P: A → Prop) (Q: B → Prop)
    (mx : option A) (my : option B) : Prop :=
  match mx, my with
  | Some x, Some y => R x y
  | Some x, None => P x
  | None, Some y => Q y
  | None, None => True
  end.

Section Forall2.
  Context {A} (R : relation A).

  Global Instance option_Forall2_refl : Reflexive R → Reflexive (option_Forall2 R).
  Proof. intros ? [?|]; by constructor. Qed.
  Global Instance option_Forall2_sym : Symmetric R → Symmetric (option_Forall2 R).
  Proof. destruct 2; by constructor. Qed.
  Global Instance option_Forall2_trans : Transitive R → Transitive (option_Forall2 R).
  Proof. destruct 2; inversion_clear 1; constructor; etrans; eauto. Qed.
  Global Instance option_Forall2_equiv : Equivalence R → Equivalence (option_Forall2 R).
  Proof. destruct 1; split; apply _. Qed.

  Lemma option_eq_Forall2 (mx my : option A) :
    mx = my ↔ option_Forall2 eq mx my.
  Proof.
    split.
    - intros ->. destruct my; constructor; done.
    - intros [|]; naive_solver.
  Qed.
End Forall2.

(** Setoids *)
Global Instance option_equiv `{Equiv A} : Equiv (option A) := option_Forall2 (≡).

Section setoids.
  Context `{Equiv A}.
  Implicit Types mx my : option A.

  Lemma option_equiv_Forall2 mx my : mx ≡ my ↔ option_Forall2 (≡) mx my.
  Proof. done. Qed.

  Global Instance option_equivalence :
    Equivalence (≡@{A}) → Equivalence (≡@{option A}).
  Proof. apply _. Qed.
  Global Instance option_leibniz `{!LeibnizEquiv A} : LeibnizEquiv (option A).
  Proof. intros x y; destruct 1; f_equal; by apply leibniz_equiv. Qed.

  Global Instance Some_proper : Proper ((≡) ==> (≡@{option A})) Some.
  Proof. by constructor. Qed.
  Global Instance Some_equiv_inj : Inj (≡) (≡@{option A}) Some.
  Proof. by inversion_clear 1. Qed.

  Lemma None_equiv_eq mx : mx ≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|intros ->; constructor]. Qed.
  Lemma Some_equiv_eq mx y : mx ≡ Some y ↔ ∃ y', mx = Some y' ∧ y' ≡ y.
  Proof. split; [inversion 1; naive_solver|naive_solver (by constructor)]. Qed.

  Global Instance is_Some_proper : Proper ((≡@{option A}) ==> iff) is_Some.
  Proof. by inversion_clear 1. Qed.
  Global Instance from_option_proper {B} (R : relation B) :
    Proper (((≡@{A}) ==> R) ==> R ==> (≡) ==> R) from_option.
  Proof. destruct 3; simpl; auto. Qed.
End setoids.

Global Typeclasses Opaque option_equiv.

(** Equality on [option] is decidable. *)
Global Instance option_eq_None_dec {A} (mx : option A) : Decision (mx = None) :=
  match mx with Some _ => right (Some_ne_None _) | None => left eq_refl end.
Global Instance option_None_eq_dec {A} (mx : option A) : Decision (None = mx) :=
  match mx with Some _ => right (None_ne_Some _) | None => left eq_refl end.
Global Instance option_eq_dec `{dec : EqDecision A} : EqDecision (option A).
Proof.
 refine (λ mx my,
  match mx, my with
  | Some x, Some y => cast_if (decide (x = y))
  | None, None => left _ | _, _ => right _
  end); clear dec; abstract congruence.
Defined.

(** * Monadic operations *)
Global Instance option_ret: MRet option := @Some.
Global Instance option_bind: MBind option := λ A B f mx,
  match mx with Some x => f x | None => None end.
Global Instance option_join: MJoin option := λ A mmx,
  match mmx with Some mx => mx | None => None end.
Global Instance option_fmap: FMap option := @option_map.
Global Instance option_guard: MGuard option := λ P dec A f,
  match dec with left H => f H | _ => None end.

Lemma option_fmap_inj {A B} (R1 : A → A → Prop) (R2 : B → B → Prop) (f : A → B) :
  Inj R1 R2 f → Inj (option_Forall2 R1) (option_Forall2 R2) (fmap f).
Proof. intros ? [?|] [?|]; inversion 1; constructor; auto. Qed.
Global Instance option_fmap_eq_inj {A B} (f : A → B) :
  Inj (=) (=) f → Inj (=@{option A}) (=@{option B}) (fmap f).
Proof.
  intros ?%option_fmap_inj ?? ?%option_eq_Forall2%(inj _).
  by apply option_eq_Forall2.
Qed.
Global Instance option_fmap_equiv_inj `{Equiv A, Equiv B} (f : A → B) :
  Inj (≡) (≡) f → Inj (≡@{option A}) (≡@{option B}) (fmap f).
Proof. apply option_fmap_inj. Qed.

Lemma fmap_is_Some {A B} (f : A → B) mx : is_Some (f <$> mx) ↔ is_Some mx.
Proof. unfold is_Some; destruct mx; naive_solver. Qed.
Lemma fmap_Some {A B} (f : A → B) mx y :
  f <$> mx = Some y ↔ ∃ x, mx = Some x ∧ y = f x.
Proof. destruct mx; naive_solver. Qed.
Lemma fmap_Some_1 {A B} (f : A → B) mx y :
  f <$> mx = Some y → ∃ x, mx = Some x ∧ y = f x.
Proof. apply fmap_Some. Qed.
Lemma fmap_Some_2 {A B} (f : A → B) mx x : mx = Some x → f <$> mx = Some (f x).
Proof. intros. apply fmap_Some; eauto. Qed.
Lemma fmap_Some_equiv {A B} `{Equiv B} `{!Equivalence (≡@{B})} (f : A → B) mx y :
  f <$> mx ≡ Some y ↔ ∃ x, mx = Some x ∧ y ≡ f x.
Proof.
  destruct mx; simpl; split.
  - intros ?%(inj Some). eauto.
  - intros (? & ->%(inj Some) & ?). constructor. done.
  - intros [=]%symmetry%None_equiv_eq.
  - intros (? & [=] & ?).
Qed.
Lemma fmap_Some_equiv_1 {A B} `{Equiv B} `{!Equivalence (≡@{B})} (f : A → B) mx y :
  f <$> mx ≡ Some y → ∃ x, mx = Some x ∧ y ≡ f x.
Proof. by rewrite fmap_Some_equiv. Qed.
Lemma fmap_None {A B} (f : A → B) mx : f <$> mx = None ↔ mx = None.
Proof. by destruct mx. Qed.
Lemma option_fmap_id {A} (mx : option A) : id <$> mx = mx.
Proof. by destruct mx. Qed.
Lemma option_fmap_compose {A B} (f : A → B) {C} (g : B → C) (mx : option A) :
  g ∘ f <$> mx = g <$> (f <$> mx).
Proof. by destruct mx. Qed.
Lemma option_fmap_ext {A B} (f g : A → B) (mx : option A) :
  (∀ x, f x = g x) → f <$> mx = g <$> mx.
Proof. intros; destruct mx; f_equal/=; auto. Qed.
Lemma option_fmap_equiv_ext {A} `{Equiv B} (f g : A → B) (mx : option A) :
  (∀ x, f x ≡ g x) → f <$> mx ≡ g <$> mx.
Proof. destruct mx; constructor; auto. Qed.

Lemma option_fmap_bind {A B C} (f : A → B) (g : B → option C) mx :
  (f <$> mx) ≫= g = mx ≫= g ∘ f.
Proof. by destruct mx. Qed.
Lemma option_bind_assoc {A B C} (f : A → option B)
  (g : B → option C) (mx : option A) : (mx ≫= f) ≫= g = mx ≫= (mbind g ∘ f).
Proof. by destruct mx; simpl. Qed.
Lemma option_bind_ext {A B} (f g : A → option B) mx my :
  (∀ x, f x = g x) → mx = my → mx ≫= f = my ≫= g.
Proof. destruct mx, my; naive_solver. Qed.
Lemma option_bind_ext_fun {A B} (f g : A → option B) mx :
  (∀ x, f x = g x) → mx ≫= f = mx ≫= g.
Proof. intros. by apply option_bind_ext. Qed.
Lemma bind_Some {A B} (f : A → option B) (mx : option A) y :
  mx ≫= f = Some y ↔ ∃ x, mx = Some x ∧ f x = Some y.
Proof. destruct mx; naive_solver. Qed.
Lemma bind_Some_equiv {A} `{Equiv B} (f : A → option B) (mx : option A) y :
  mx ≫= f ≡ Some y ↔ ∃ x, mx = Some x ∧ f x ≡ Some y.
Proof. destruct mx; (split; [inversion 1|]); naive_solver. Qed.
Lemma bind_None {A B} (f : A → option B) (mx : option A) :
  mx ≫= f = None ↔ mx = None ∨ ∃ x, mx = Some x ∧ f x = None.
Proof. destruct mx; naive_solver. Qed.
Lemma bind_with_Some {A} (mx : option A) : mx ≫= Some = mx.
Proof. by destruct mx. Qed.

Global Instance option_fmap_proper `{Equiv A, Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{option A}) ==> (≡@{option B})) fmap.
Proof. destruct 2; constructor; auto. Qed.
Global Instance option_bind_proper `{Equiv A, Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡@{option A}) ==> (≡@{option B})) mbind.
Proof. destruct 2; simpl; try constructor; auto. Qed.
Global Instance option_join_proper `{Equiv A} :
  Proper ((≡) ==> (≡@{option (option A)})) mjoin.
Proof. destruct 1 as [?? []|]; simpl; by constructor. Qed.

(** ** Inverses of constructors *)
(** We can do this in a fancy way using dependent types, but rewrite does
not particularly like type level reductions. *)
Class Maybe {A B : Type} (c : A → B) :=
  maybe : B → option A.
Global Arguments maybe {_ _} _ {_} !_ / : assert.
Class Maybe2 {A1 A2 B : Type} (c : A1 → A2 → B) :=
  maybe2 : B → option (A1 * A2).
Global Arguments maybe2 {_ _ _} _ {_} !_ / : assert.
Class Maybe3 {A1 A2 A3 B : Type} (c : A1 → A2 → A3 → B) :=
  maybe3 : B → option (A1 * A2 * A3).
Global Arguments maybe3 {_ _ _ _} _ {_} !_ / : assert.
Class Maybe4 {A1 A2 A3 A4 B : Type} (c : A1 → A2 → A3 → A4 → B) :=
  maybe4 : B → option (A1 * A2 * A3 * A4).
Global Arguments maybe4 {_ _ _ _ _} _ {_} !_ / : assert.

Global Instance maybe_comp `{Maybe B C c1, Maybe A B c2} : Maybe (c1 ∘ c2) := λ x,
  maybe c1 x ≫= maybe c2.
Global Arguments maybe_comp _ _ _ _ _ _ _ !_ / : assert.

Global Instance maybe_inl {A B} : Maybe (@inl A B) := λ xy,
  match xy with inl x => Some x | _ => None end.
Global Instance maybe_inr {A B} : Maybe (@inr A B) := λ xy,
  match xy with inr y => Some y | _ => None end.
Global Instance maybe_Some {A} : Maybe (@Some A) := id.
Global Arguments maybe_Some _ !_ / : assert.

(** * Union, intersection and difference *)
Global Instance option_union_with {A} : UnionWith A (option A) := λ f mx my,
  match mx, my with
  | Some x, Some y => f x y
  | Some x, None => Some x
  | None, Some y => Some y
  | None, None => None
  end.
Global Instance option_intersection_with {A} : IntersectionWith A (option A) :=
  λ f mx my, match mx, my with Some x, Some y => f x y | _, _ => None end.
Global Instance option_difference_with {A} : DifferenceWith A (option A) := λ f mx my,
  match mx, my with
  | Some x, Some y => f x y
  | Some x, None => Some x
  | None, _ => None
  end.
Global Instance option_union {A} : Union (option A) := union_with (λ x _, Some x).

Lemma union_Some {A} (mx my : option A) z :
  mx ∪ my = Some z ↔ mx = Some z ∨ (mx = None ∧ my = Some z).
Proof. destruct mx, my; naive_solver. Qed.
Lemma union_Some_l {A} x (my : option A) :
  Some x ∪ my = Some x.
Proof. destruct my; done. Qed.
Lemma union_Some_r {A} (mx : option A) y :
  mx ∪ Some y = Some (default y mx).
Proof. destruct mx; done. Qed.
Lemma union_None {A} (mx my : option A) :
  mx ∪ my = None ↔ mx = None ∧ my = None.
Proof. destruct mx, my; naive_solver. Qed.
Lemma union_is_Some {A} (mx my : option A) :
  is_Some (mx ∪ my) ↔ is_Some mx ∨ is_Some my.
Proof. destruct mx, my; naive_solver. Qed.

Global Instance option_union_left_id {A} : LeftId (=@{option A}) None union.
Proof. by intros [?|]. Qed.
Global Instance option_union_right_id {A} : RightId (=@{option A}) None union.
Proof. by intros [?|]. Qed.

Global Instance option_intersection {A} : Intersection (option A) :=
  intersection_with (λ x _, Some x).

Lemma intersection_Some {A} (mx my : option A) x :
  mx ∩ my = Some x ↔ mx = Some x ∧ is_Some my.
Proof. destruct mx, my; unfold is_Some; naive_solver. Qed.
Lemma intersection_is_Some {A} (mx my : option A) :
  is_Some (mx ∩ my) ↔ is_Some mx ∧ is_Some my.
Proof. destruct mx, my; unfold is_Some; naive_solver. Qed.
Lemma intersection_Some_r {A} (mx : option A) (y : A) :
  mx ∩ Some y = mx.
Proof. by destruct mx. Qed.
Lemma intersection_None {A} (mx my : option A) :
  mx ∩ my = None ↔ mx = None ∨ my = None.
Proof. destruct mx, my; naive_solver. Qed.
Lemma intersection_None_l {A} (my : option A) :
  None ∩ my = None.
Proof. destruct my; done. Qed.
Lemma intersection_None_r {A} (mx : option A) :
  mx ∩ None = None.
Proof. destruct mx; done. Qed.

Global Instance option_intersection_right_absorb {A} :
  RightAbsorb (=@{option A}) None intersection.
Proof. by intros [?|]. Qed.

Global Instance option_intersection_left_absorb {A} :
  LeftAbsorb (=@{option A}) None intersection.
Proof. by intros [?|]. Qed.

Section union_intersection_difference.
  Context {A} (f : A → A → option A).

  Global Instance union_with_left_id : LeftId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance union_with_right_id : RightId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance union_with_comm :
    Comm (=) f → Comm (=@{option A}) (union_with f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(comm f). Qed.
  (** These are duplicates of the above [LeftId]/[RightId] instances, but easier to
  find with [SearchAbout]. *)
  Lemma union_with_None_l my : union_with f None my = my.
  Proof. destruct my; done. Qed.
  Lemma union_with_None_r mx : union_with f mx None = mx.
  Proof. destruct mx; done. Qed.

  Global Instance intersection_with_left_ab : LeftAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance intersection_with_right_ab : RightAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance intersection_with_comm :
    Comm (=) f → Comm (=@{option A}) (intersection_with f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(comm f). Qed.
  (** These are duplicates of the above [LeftAbsorb]/[RightAbsorb] instances, but
  easier to find with [SearchAbout]. *)
  Lemma intersection_with_None_l my : intersection_with f None my = None.
  Proof. destruct my; done. Qed.
  Lemma intersection_with_None_r mx : intersection_with f mx None = None.
  Proof. destruct mx; done. Qed.

  Global Instance difference_with_comm :
    Comm (=) f → Comm (=@{option A}) (intersection_with f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(comm f). Qed.
  Global Instance difference_with_right_id : RightId (=) None (difference_with f).
  Proof. by intros [?|]. Qed.

  Global Instance union_with_proper `{Equiv A} :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡@{option A}) ==> (≡) ==> (≡)) union_with.
  Proof. intros ?? Hf; do 2 destruct 1; try constructor; by try apply Hf. Qed.
  Global Instance intersection_with_proper `{Equiv A} :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡@{option A}) ==> (≡) ==> (≡)) intersection_with.
  Proof. intros ?? Hf; do 2 destruct 1; try constructor; by try apply Hf. Qed.
  Global Instance difference_with_proper `{Equiv A} :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡@{option A}) ==> (≡) ==> (≡)) difference_with.
  Proof. intros ?? Hf; do 2 destruct 1; try constructor; by try apply Hf. Qed.
  Global Instance union_proper `{Equiv A} :
    Proper ((≡@{option A}) ==> (≡) ==> (≡)) union.
  Proof. apply union_with_proper. by constructor. Qed.
End union_intersection_difference.

(** * Tactics *)
Tactic Notation "case_option_guard" "as" ident(Hx) :=
  match goal with
  | H : context C [@mguard option _ ?P ?dec] |- _ =>
    change (@mguard option _ P dec) with (λ A (f : P → option A),
      match @decide P dec with left H' => f H' | _ => None end) in *;
    destruct_decide (@decide P dec) as Hx
  | |- context C [@mguard option _ ?P ?dec] =>
    change (@mguard option _ P dec) with (λ A (f : P → option A),
      match @decide P dec with left H' => f H' | _ => None end) in *;
    destruct_decide (@decide P dec) as Hx
  end.
Tactic Notation "case_option_guard" :=
  let H := fresh in case_option_guard as H.

Lemma option_guard_True {A} P `{Decision P} (mx : option A) :
  P → mguard P (λ _, mx) = mx.
Proof. intros. by case_option_guard. Qed.
Lemma option_guard_True_pi {A} P `{Decision P, ProofIrrel P} (f : P → option A)
    (HP : P) :
  mguard P f = f HP.
Proof. intros. case_option_guard; [|done]. f_equal; apply proof_irrel. Qed.
Lemma option_guard_False {A} P `{Decision P} (f : P → option A) :
  ¬P → mguard P f = None.
Proof. intros. by case_option_guard. Qed.
Lemma option_guard_iff {A} P Q `{Decision P, Decision Q} (mx : option A) :
  (P ↔ Q) → (guard P; mx) = guard Q; mx.
Proof. intros [??]. repeat case_option_guard; intuition. Qed.
Lemma option_guard_decide {A} P `{Decision P} (mx : option A) :
  (guard P; mx) = if decide P then mx else None.
Proof. done. Qed.
Lemma option_guard_bool_decide {A} P `{Decision P} (mx : option A) :
  (guard P; mx) = if bool_decide P then mx else None.
Proof. by rewrite option_guard_decide, decide_bool_decide. Qed.

Tactic Notation "simpl_option" "by" tactic3(tac) :=
  let assert_Some_None A mx H := first
    [ let x := mk_evar A in
      assert (mx = Some x) as H by tac
    | assert (mx = None) as H by tac ]
  in repeat match goal with
  | H : context [@mret _ _ ?A] |- _ =>
     change (@mret _ _ A) with (@Some A) in H
  | |- context [@mret _ _ ?A] => change (@mret _ _ A) with (@Some A)
  | H : context [mbind (M:=option) (A:=?A) ?f ?mx] |- _ =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
  | H : context [fmap (M:=option) (A:=?A) ?f ?mx] |- _ =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
  | H : context [from_option (A:=?A) _ _ ?mx] |- _ =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
  | H : context [ match ?mx with _ => _ end ] |- _ =>
    match type of mx with
    | option ?A =>
      let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
    end
  | |- context [mbind (M:=option) (A:=?A) ?f ?mx] =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
  | |- context [fmap (M:=option) (A:=?A) ?f ?mx] =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
  | |- context [from_option (A:=?A) _ _ ?mx] =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
  | |- context [ match ?mx with _ => _ end ] =>
    match type of mx with
    | option ?A =>
      let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
    end
  | H : context [decide _] |- _ => rewrite decide_True in H by tac
  | H : context [decide _] |- _ => rewrite decide_False in H by tac
  | H : context [mguard _ _] |- _ => rewrite option_guard_False in H by tac
  | H : context [mguard _ _] |- _ => rewrite option_guard_True in H by tac
  | _ => rewrite decide_True by tac
  | _ => rewrite decide_False by tac
  | _ => rewrite option_guard_True by tac
  | _ => rewrite option_guard_False by tac
  | H : context [None ∪ _] |- _ => rewrite (left_id_L None (∪)) in H
  | H : context [_ ∪ None] |- _ => rewrite (right_id_L None (∪)) in H
  | |- context [None ∪ _] => rewrite (left_id_L None (∪))
  | |- context [_ ∪ None] => rewrite (right_id_L None (∪))
  end.
Tactic Notation "simplify_option_eq" "by" tactic3(tac) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | _ : maybe _ ?x = Some _ |- _ => is_var x; destruct x
  | _ : maybe2 _ ?x = Some _ |- _ => is_var x; destruct x
  | _ : maybe3 _ ?x = Some _ |- _ => is_var x; destruct x
  | _ : maybe4 _ ?x = Some _ |- _ => is_var x; destruct x
  | H : _ ∪ _ = Some _ |- _ => apply union_Some in H; destruct H
  | H : mbind (M:=option) ?f ?mx = ?my |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (f x = my) in H|change (None = my) in H]
  | H : ?my = mbind (M:=option) ?f ?mx |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (my = f x) in H|change (my = None) in H]
  | H : fmap (M:=option) ?f ?mx = ?my |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (Some (f x) = my) in H|change (None = my) in H]
  | H : ?my = fmap (M:=option) ?f ?mx |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (my = Some (f x)) in H|change (my = None) in H]
  | _ => progress case_decide
  | _ => progress case_option_guard
  end.
Tactic Notation "simplify_option_eq" := simplify_option_eq by eauto.
