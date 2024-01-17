From stdpp Require Import prelude fin_maps propset.

(** Some tests for f_equiv. *)
(* Similar to [f_equal], it should solve goals by [reflexivity]. *)
Lemma test_f_equiv_refl {A} (R : relation A) `{!Equivalence R} x :
  R x x.
Proof. f_equiv. Qed.

(* And immediately solve sub-goals by reflexivity *)
Lemma test_f_equiv_refl_nested {A} (R : relation A) `{!Equivalence R} g x y z :
  Proper (R ==> R ==> R) g →
  R y z →
  R (g x y) (g x z).
Proof. intros ? Hyz. f_equiv. apply Hyz. Qed.

Section f_equiv.
  Context `{!Equiv A, !Equiv B, !SubsetEq A}.

  Lemma f_equiv1 (fn : A → B) (x1 x2 : A) :
    Proper ((≡) ==> (≡)) fn →
    x1 ≡ x2 →
    fn x1 ≡ fn x2.
  Proof. intros. f_equiv. assumption. Qed.

  Lemma f_equiv2 (fn : A → B) (x1 x2 : A) :
    Proper ((⊆) ==> (≡)) fn →
    x1 ⊆ x2 →
    fn x1 ≡ fn x2.
  Proof. intros. f_equiv. assumption. Qed.

  (* Ensure that we prefer the ≡. *)
  Lemma f_equiv3 (fn : A → B) (x1 x2 : A) :
    Proper ((≡) ==> (≡)) fn →
    Proper ((⊆) ==> (≡)) fn →
    x1 ≡ x2 →
    fn x1 ≡ fn x2.
  Proof.
    (* The Coq tactic prefers the ⊆. *)
    intros. Morphisms.f_equiv. Fail assumption.
  Restart.
    intros. f_equiv. assumption.
  Qed.
End f_equiv.

(** Some tests for solve_proper (also testing f_equiv indirectly). *)

(** Test case for #161 *)
Lemma test_solve_proper_const {A} (R : relation A) `{!Equivalence R} x :
  Proper (R ==> R) (λ _, x).
Proof. solve_proper. Qed.

Section tests.
  Context {A B : Type} `{!Equiv A, !Equiv B}.
  Context (foo : A → A) (bar : A → B) (baz : B → A → A).
  Context `{!Proper ((≡) ==> (≡)) foo,
            !Proper ((≡) ==> (≡)) bar,
            !Proper ((≡) ==> (≡) ==> (≡)) baz}.

  Definition test1 (x : A) := baz (bar (foo x)) x.
  Goal Proper ((≡) ==> (≡)) test1.
  Proof. solve_proper. Qed.

  Definition test2 (b : bool) (x : A) :=
    if b then bar (foo x) else bar x.
  Goal ∀ b, Proper ((≡) ==> (≡)) (test2 b).
  Proof. solve_proper. Qed.

  Definition test3 (f : nat → A) :=
    baz (bar (f 0)) (f 2).
  Goal Proper (pointwise_relation nat (≡) ==> (≡)) test3.
  Proof. solve_proper. Qed.

  (* We mirror [discrete_fun] from Iris to have an equivalence on a function
  space. *)
  Definition discrete_fun {A} (B : A → Type) `{!∀ x, Equiv (B x)} := ∀ x : A, B x.
  Local Instance discrete_fun_equiv  {A} {B : A → Type} `{!∀ x, Equiv (B x)} :
      Equiv (discrete_fun B) :=
    λ f g, ∀ x, f x ≡ g x.
  Notation "A -d> B" :=
    (@discrete_fun A (λ _, B) _) (at level 99, B at level 200, right associativity).
  Definition test4 x (f : A -d> A) := f x.
  Goal ∀ x, Proper ((≡) ==> (≡)) (test4 x).
  Proof. solve_proper. Qed.
End tests.

Global Instance from_option_proper_test1 `{Equiv A} {B} (R : relation B) (f : A → B) :
  Proper ((≡) ==> R) f → Proper (R ==> (≡) ==> R) (from_option f).
Proof. apply _. Qed.
Global Instance from_option_proper_test2 `{Equiv A} {B} (R : relation B) (f : A → B) :
  Proper ((≡) ==> R) f → Proper (R ==> (≡) ==> R) (from_option f).
Proof. solve_proper. Qed.

(** The following tests are inspired by Iris's [ofe] structure (here, simplified
to just a type an arbitrary relation), and the discrete function space [A -d> B]
on a Type [A] and OFE [B]. The tests occur when proving [Proper]s for
higher-order functions, which typically occurs while defining functions using
Iris's [fixpoint] operator. *)
Record setoid :=
  Setoid { setoid_car :> Type; setoid_equiv : relation setoid_car }.
Arguments setoid_equiv {_} _ _.

Definition myfun (A : Type) (B : setoid) := A → B.
Definition myfun_equiv {A B} : relation (myfun A B) :=
  pointwise_relation _ setoid_equiv.
Definition myfunS (A : Type) (B : setoid) := Setoid (myfun A B) myfun_equiv.

Section setoid_tests.
  Context {A : setoid} (f : A → A) (h : A → A → A).
  Context `{!Proper (setoid_equiv ==> setoid_equiv) f,
            !Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) h}.

  Definition setoid_test1 (rec : myfunS nat A) : myfunS nat A :=
    λ n, h (f (rec n)) (rec n).
  Goal Proper (setoid_equiv ==> setoid_equiv) setoid_test1.
  Proof. solve_proper. Qed.

  Definition setoid_test2 (rec : myfunS nat (myfunS nat A)) : myfunS nat A :=
    λ n, h (f (rec n n)) (rec n n).
  Goal Proper (setoid_equiv ==> setoid_equiv) setoid_test2.
  Proof. solve_proper. Qed.

  Definition setoid_test3 (rec : myfunS nat A) : myfunS nat (myfunS nat A) :=
    λ n m, h (f (rec n)) (rec m).
  Goal Proper (setoid_equiv ==> setoid_equiv) setoid_test3.
  Proof. solve_proper. Qed.
End setoid_tests.

Section map_tests.
  Context `{FinMap K M} `{Equiv A}.

  (** For higher-order functions on maps (like [map_with_with], [fmap], etc)
  we use "higher-order [Proper] instances" [Proper ((≡) ==> (≡)) ==> ...)]
  that also allow the function to differ. We test that we can derive simpler
  [Proper]s for a fixed function using both type class inference ([apply _])
  and std++'s [solve_proper] tactic. *)
  Global Instance map_alter_proper_test (f : A → A) i :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡)) (alter (M:=M A) f i).
  Proof. apply _. Restart. solve_proper. Abort.
  Global Instance map_zip_proper_test `{Equiv B} :
    Proper ((≡@{M A}) ==> (≡@{M B}) ==> (≡@{M (A * B)})) map_zip.
  Proof. apply _. Restart. solve_proper. Abort.
  Global Instance map_zip_with_proper_test `{Equiv B, Equiv C} (f : A → B → C) :
    Proper ((≡) ==> (≡) ==> (≡)) f →
    Proper ((≡) ==> (≡) ==> (≡)) (map_zip_with (M:=M) f).
  Proof. apply _. Restart. solve_proper. Abort.
  Global Instance map_fmap_proper_test `{Equiv B} (f : A → B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (fmap f).
  Proof. apply _. Restart. solve_proper. Abort.
  Global Instance map_omap_proper_test `{Equiv B} (f : A → option B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (omap f).
  Proof. apply _. Restart. solve_proper. Abort.
End map_tests.

(** And similarly for lists *)
Global Instance list_alter_proper_test `{!Equiv A} (f : A → A) i :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (alter (M:=list A) f i).
Proof. apply _. Restart. solve_proper. Abort.
Global Instance list_fmap_proper_test `{!Equiv A, !Equiv B} (f : A → B) :
  Proper ((≡) ==> (≡)) f → Proper ((≡@{list A}) ==> (≡)) (fmap f).
Proof. apply _. Restart. solve_proper. Abort.
Global Instance list_bind_proper_test `{!Equiv A, !Equiv B} (f : A → list B) :
  Proper ((≡) ==> (≡)) f → Proper ((≡) ==> (≡)) (mbind f).
Proof. apply _. Restart. solve_proper. Abort.
Global Instance mapM_proper_test `{!Equiv A, !Equiv B} (f : A → option B) :
  Proper ((≡) ==> (≡)) f → Proper ((≡) ==> (≡)) (mapM f).
Proof. apply _. Restart. solve_proper. Abort.

Lemma test_prod_equivalence (X1 X2 X3 Y : propset nat * propset nat) :
  X3 ≡ X2 → X2 ≡ X1 → (X1,Y) ≡ (X3,Y).
Proof. intros H1 H2. by rewrite H1, <-H2. Qed.
