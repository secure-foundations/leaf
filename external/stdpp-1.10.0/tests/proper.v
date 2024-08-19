From stdpp Require Import prelude fin_maps propset.

Global Instance from_option_proper_test1 `{Equiv A} {B} (R : relation B) (f : A → B) :
  Proper ((≡) ==> R) f → Proper (R ==> (≡) ==> R) (from_option f).
Proof. apply _. Qed.
Global Instance from_option_proper_test2 `{Equiv A} {B} (R : relation B) (f : A → B) :
  Proper ((≡) ==> R) f → Proper (R ==> (≡) ==> R) (from_option f).
Proof. solve_proper. Qed.

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
  Proof.
    apply _.
  Restart. Proof.
    solve_proper.
  Abort.
  Global Instance map_zip_proper_test `{Equiv B} :
    Proper ((≡@{M A}) ==> (≡@{M B}) ==> (≡@{M (A * B)})) map_zip.
  Proof.
    apply _.
  Restart. Proof.
    solve_proper.
  Abort.
  Global Instance map_zip_with_proper_test `{Equiv B, Equiv C} (f : A → B → C) :
    Proper ((≡) ==> (≡) ==> (≡)) f →
    Proper ((≡) ==> (≡) ==> (≡)) (map_zip_with (M:=M) f).
  Proof.
    apply _.
  Restart. Proof.
    solve_proper.
  Abort.
  Global Instance map_fmap_proper_test `{Equiv B} (f : A → B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (fmap f).
  Proof.
    apply _.
  Restart. Proof.
    solve_proper.
  Abort.
  Global Instance map_omap_proper_test `{Equiv B} (f : A → option B) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡@{M _})) (omap f).
  Proof.
    apply _.
  Restart. Proof.
    solve_proper.
  Abort.
End map_tests.

(** And similarly for lists *)
Global Instance list_alter_proper_test `{!Equiv A} (f : A → A) i :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (alter (M:=list A) f i).
Proof.
  apply _.
Restart. Proof.
  solve_proper.
Abort.
Global Instance list_fmap_proper_test `{!Equiv A, !Equiv B} (f : A → B) :
  Proper ((≡) ==> (≡)) f → Proper ((≡@{list A}) ==> (≡)) (fmap f).
Proof.
  apply _.
Restart. Proof.
  solve_proper.
Abort.
Global Instance list_bind_proper_test `{!Equiv A, !Equiv B} (f : A → list B) :
  Proper ((≡) ==> (≡)) f → Proper ((≡) ==> (≡)) (mbind f).
Proof.
  apply _.
Restart. Proof.
  solve_proper.
Abort.
Global Instance mapM_proper_test `{!Equiv A, !Equiv B} (f : A → option B) :
  Proper ((≡) ==> (≡)) f → Proper ((≡) ==> (≡)) (mapM f).
Proof.
  apply _.
Restart. Proof.
  solve_proper.
Abort.

Lemma test_prod_equivalence (X1 X2 X3 Y : propset nat * propset nat) :
  X3 ≡ X2 → X2 ≡ X1 → (X1,Y) ≡ (X3,Y).
Proof. intros H1 H2. by rewrite H1, <-H2. Qed.
