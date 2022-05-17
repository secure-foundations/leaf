From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth.
From iris.algebra Require Import functions.
From iris.algebra Require Import gmap.
From iris.prelude Require Import options.

Lemma list_equiv_weaken {T} (eq1 eq2: Equiv T)
  (w: ∀ (a b : T) , @equiv T eq1 a b -> @equiv T eq2 a b)
  (x y: list T)
  : @equiv (list T) (@list_equiv T eq1) x y -> @equiv (list T) (@list_equiv T eq2) x y.
Proof.
  intros H.
  induction H.
  - apply nil_equiv.
  - apply cons_equiv. + intuition. + intuition.
Qed.

Definition perm_equiv {T} (eq: Equiv T) (a: list T) (b: list T) :=
  ∃ q , a ≡ₚ q ∧ q ≡ b.

Lemma perm_equiv_refl {T} (eq: Equiv T) {eqv: Equivalence eq} (a: list T) : perm_equiv eq a a.
Proof. unfold perm_equiv. exists a. split; trivial. Qed.

Lemma perm_equiv_symm {T} (eq: Equiv T) {eqv: Equivalence eq} (a: list T) (b: list T) :
    perm_equiv eq a b -> perm_equiv eq b a.
Proof. unfold perm_equiv. intro h. destruct h as [q [h r]].
  have u := Permutation_equiv a q b h r.
  have u1 := u eqv.
  destruct u1 as [l2' [y z]].
  exists l2'. split; symmetry; trivial.
Qed.

Lemma perm_equiv_weaken {T} (eq1 eq2: Equiv T)
  (w: ∀ (a b : T) , @equiv T eq1 a b -> @equiv T eq2 a b)
  (x y: list T)
  : perm_equiv eq1 x y -> perm_equiv eq2 x y.
Proof.
  unfold perm_equiv.
  intros H. destruct H as [q [h r]].
  exists q. split; trivial.
  apply list_equiv_weaken with (eq3 := eq1); trivial.
Qed.

Lemma perm_equiv_trans {T} (eq: Equiv T) {eqv: Equivalence eq} (a: list T) (b: list T) (c: list T):
    perm_equiv eq a b -> perm_equiv eq b c -> perm_equiv eq a c.
Proof.
  unfold perm_equiv. intros g h.
  destruct g as [q1 [g1 g2]].
  destruct h as [q2 [h1 h2]].
  have z := equiv_Permutation q1 b q2 g2 h1.
  destruct z as [l2' [j1 j2]].
  exists l2'. split.
  - eapply Equivalence_Transitive. + apply g1. + apply j1.
  - eapply Equivalence_Transitive. + apply j2. + apply h2.
Qed.

Lemma perm_equiv_app_comm {T} (eq: Equiv T) {eqv: Equivalence eq} (a: list T) (b: list T)
    : perm_equiv eq (a ++ b) (b ++ a).
Proof.
  unfold perm_equiv. exists (b ++ a). split; trivial.
  apply Permutation_app_comm.
Qed.

Lemma perm_equiv_app {T} (eq: Equiv T) {eqv: Equivalence eq} (a b b': list T)
    : perm_equiv eq b b' -> perm_equiv eq (a ++ b) (a ++ b').
Proof.
  unfold perm_equiv. intros H.
  destruct H as [q [u v]].
  exists (a ++ q). split.
  - apply Permutation_app_head. trivial.
  - setoid_rewrite v. trivial.
Qed.

Lemma perm_equiv_front {T} (eq: Equiv T) {eqv: Equivalence eq} (a b: list T) (x: T)
  : perm_equiv eq a (x :: b) -> ∃ (x': T) (b': list T) ,
      a ≡ₚ x' :: b' ∧ eq x' x ∧ perm_equiv eq b' b.
Proof.
  intros H. unfold perm_equiv in H. destruct H as [q [w v]].
  destruct q.
  - inversion v.
  - inversion v. subst. exists t. exists q. split; trivial. split; trivial.
      unfold perm_equiv. exists q. split; trivial.
Qed.

Lemma perm_equiv_skip {T} (eq: Equiv T) {eqv: Equivalence eq} (a b: list T) (x x': T)
  : eq x x' -> perm_equiv eq a b -> perm_equiv eq (x :: a) (x' :: b). Admitted.
  
Lemma perm_equiv_extens {T} (eq: Equiv T) {eqv: Equivalence eq} (a b b': list T)
    (pe: perm_equiv eq a (b ++ b'))
    : ∃ z z' , a ≡ₚ z ++ z' ∧ perm_equiv eq z b ∧ perm_equiv eq z' b'.
Proof.
  generalize pe. generalize a. clear pe. clear a.
  induction b.
  - intros. simpl in pe. exists []. exists a. split.
    { simpl. trivial. }
    split; trivial. apply perm_equiv_refl; trivial.
  - rename a into x.
      intros a pe.
      simpl in pe.
      have j := @perm_equiv_front _ eq eqv _ _ _ pe.
      destruct j as [x' [a' [v [w u]]]].
      have ind := IHb a' u.
      destruct ind as [z [z' [f [e g]]]].
      exists (x' :: z). exists z'.
      split.
      { simpl. apply perm_trans with (l' := x' :: a'); trivial.
          apply perm_skip. trivial. }
      split.
      { apply perm_equiv_skip; trivial. }
      { trivial. }
Qed.
 
(*  simpl in pe.
  have j := @perm_equiv_front _ eq eqv _ _ _ pe.


  destruct pe as [l [j k]].
  generalize k. generalize b. generalize b'. clear k. clear b. clear b'.
  induction j.
  - intros.
      destruct b; destruct b'.
      + exists []. exists []. split; trivial. split; apply perm_equiv_refl; typeclasses eauto.
      + simpl in k. inversion k.
      + simpl in k. inversion k.
      + simpl in k. inversion k.
  - intros. destruct b; destruct b'.
      + simpl in k. inversion k.
      + simpl in k. inversion k. subst. exists []. exists (t :: l). split.
          * simpl. setoid_rewrite H2. trivial.
          * split. { apply perm_equiv_refl. typeclasses eauto. }  *)


Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

Record free (A : Type) : Type := {
  free_car : list A;
}.
Global Arguments free_car {_} _.
Local Coercion free_car : free >-> list.

Definition to_free {A} (a : A) : free A :=
  {| free_car := [a] |}.

Lemma free_eq {A} (x y : free A) : free_car x = free_car y → x = y.
Proof.
  destruct x as [a ?], y as [b ?]; simpl.
  intros ->; f_equal.
Qed.

Section free.
Context {A : ofe}.
Implicit Types a b : A.
Implicit Types x y : free A.
 
(* OFE *)
Local Instance free_dist : Dist (free A) := λ n x y,
  perm_equiv (≡{n}≡) x y.
Local Instance free_equiv : Equiv (free A) := λ x y, ∀ n, x ≡{n}≡ y.

Definition free_ofe_mixin : OfeMixin (free A).
Proof.
  split.
  - done.
  - intros n; split; rewrite /dist /free_dist.
    + intros x. apply perm_equiv_refl. typeclasses eauto.
    + intros x y. apply perm_equiv_symm. typeclasses eauto.
    + intros x y z. apply perm_equiv_trans. typeclasses eauto.
  - intros. apply perm_equiv_weaken with (eq1 := (≡{S n}≡)); trivial.
    intros. apply dist_le with (n0 := S n); trivial. lia.
Qed.
Canonical Structure freeO := Ofe (free A) free_ofe_mixin.

(* CMRA *)
Local Instance free_validN_instance : ValidN (free A) := λ n x, True.
Local Instance free_valid_instance : Valid (free A) := λ x, ∀ n, ✓{n} x.

Local Program Instance free_op_instance : Op (free A) := λ x y,
  {| free_car := free_car x ++ free_car y |}.
  
Local Instance free_pcore_instance : PCore (free A) := λ x ,
    Some {| free_car := [] |}.

Local Instance free_comm : Comm (≡) (@op (free A) _).
Proof. intros x y n. apply perm_equiv_app_comm. typeclasses eauto. Qed.

Local Instance free_assoc : Assoc (≡) (@op (free A) _).
Proof.
  intros x y z n.
  unfold dist. unfold free_dist.
  unfold op. unfold free_op_instance.
  unfold free_car.
  rewrite app_ass.
  apply perm_equiv_refl.
  typeclasses eauto.
Qed.
  
Local Instance free_validN_ne n : Proper (dist n ==> impl) (@validN (free A) _ n).
Proof.
  unfold validN. unfold free_validN_instance.
  unfold Proper, "==>", impl. intros. trivial.
Qed.

Local Instance free_validN_proper n : Proper (equiv ==> iff) (@validN (free A) _ n).
Proof. move=> x y /equiv_dist H. by split; rewrite (H n). Qed.

Local Instance free_op_ne' x : NonExpansive (op x).
Proof.
  intros n y1 y2 k.
  apply perm_equiv_app; trivial. typeclasses eauto.
Qed.

Local Instance free_op_ne : NonExpansive2 (@op (free A) _).
Proof. by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx. Qed.
Local Instance free_op_proper : Proper ((≡) ==> (≡) ==> (≡)) (op (A := free A)) := ne_proper_2 _.

Definition free_cmra_mixin : CmraMixin (free A).
Proof.
  apply cmra_total_mixin; try apply _ || by eauto.
  - intros n x. unfold core. unfold pcore. unfold free_pcore_instance.
      unfold default. intros. trivial.
  - intros x. unfold core. unfold pcore. unfold free_pcore_instance. unfold default.
      unfold op. unfold free_op_instance. unfold free_car. unfold id.
      unfold "++". destruct x. trivial.
  - intros n x y. 
      unfold core. unfold pcore. unfold free_pcore_instance. unfold default.
      unfold "≼". exists {| free_car := [] |}. trivial.
  - intros.
    
  - intros n x y1 y2 Hval Hx; exists x, x; simpl; split.
    + by rewrite free_idemp.
    + by move: Hval; rewrite Hx; move=> /free_op_invN->; rewrite free_idemp.
Qed.
Canonical Structure freeR : cmra := Cmra (free A) free_cmra_mixin.

Global Instance free_cmra_total : CmraTotal freeR.
Proof. rewrite /CmraTotal; eauto. Qed.
Global Instance free_core_id x : CoreId x.
Proof. by constructor. Qed.

Global Instance free_cmra_discrete : OfeDiscrete A → CmraDiscrete freeR.
Proof.
  intros HD. split.
  - intros x y [H H'] n; split=> a; setoid_rewrite <-(discrete_iff_0 _ _); auto.
  - intros x; rewrite free_validN_def=> Hv n. apply free_validN_def=> a b ??.
    apply discrete_iff_0; auto.
Qed.

Global Instance to_free_ne : NonExpansive to_free.
Proof.
  intros n a1 a2 Hx; split=> b /=;
    setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.
Global Instance to_free_proper : Proper ((≡) ==> (≡)) to_free := ne_proper _.

Global Instance to_free_discrete a : Discrete a → Discrete (to_free a).
Proof.
  intros ? y [H H'] n; split.
  - intros a' ->%elem_of_list_singleton. destruct (H a) as [b ?]; first by left.
    exists b. by rewrite -discrete_iff_0.
  - intros b Hb. destruct (H' b) as (b'&->%elem_of_list_singleton&?); auto.
    exists a. by rewrite elem_of_list_singleton -discrete_iff_0.
Qed.

Global Instance to_free_injN n : Inj (dist n) (dist n) (to_free).
Proof.
  move=> a b [_] /=. setoid_rewrite elem_of_list_singleton. naive_solver.
Qed.
Global Instance to_free_inj : Inj (≡) (≡) (to_free).
Proof. intros a b ?. apply equiv_dist=>n. by apply (inj to_free), equiv_dist. Qed.

Lemma to_free_uninjN n x : ✓{n} x → ∃ a, to_free a ≡{n}≡ x.
Proof.
  rewrite free_validN_def=> Hv.
  destruct (elem_of_free x) as [a ?].
  exists a; split=> b /=; setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.

Lemma to_free_uninj x : ✓ x → ∃ a, to_free a ≡ x.
Proof.
  rewrite /valid /free_valid_instance; setoid_rewrite free_validN_def.
  destruct (elem_of_free x) as [a ?].
  exists a; split=> b /=; setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.

Lemma free_valid_includedN n x y : ✓{n} y → x ≼{n} y → x ≡{n}≡ y.
Proof.
  move=> Hval [z Hy]; move: Hval; rewrite Hy.
  by move=> /free_op_invN->; rewrite free_idemp.
Qed.

Lemma to_free_includedN n a b : to_free a ≼{n} to_free b ↔ a ≡{n}≡ b.
Proof.
  split; last by intros ->. intros [x [_ Hincl]].
  by destruct (Hincl a) as (? & ->%elem_of_list_singleton & ?); first set_solver+.
Qed.

Lemma to_free_included a b : to_free a ≼ to_free b ↔ a ≡ b.
Proof.
  split; last by intros ->.
  intros (x & Heq). apply equiv_dist=>n. destruct (Heq n) as [_ Hincl].
  by destruct (Hincl a) as (? & ->%elem_of_list_singleton & ?); first set_solver+.
Qed.

Global Instance free_cancelable x : Cancelable x.
Proof.
  intros n y z Hv Heq.
  destruct (to_free_uninjN n x) as [x' EQx]; first by eapply cmra_validN_op_l.
  destruct (to_free_uninjN n y) as [y' EQy]; first by eapply cmra_validN_op_r.
  destruct (to_free_uninjN n z) as [z' EQz].
  { eapply (cmra_validN_op_r n x z). by rewrite -Heq. }
  assert (Hx'y' : x' ≡{n}≡ y').
  { apply (inj to_free), free_op_invN. by rewrite EQx EQy. }
  assert (Hx'z' : x' ≡{n}≡ z').
  { apply (inj to_free), free_op_invN. by rewrite EQx EQz -Heq. }
  by rewrite -EQy -EQz -Hx'y' -Hx'z'.
Qed.

Lemma free_op_inv x y : ✓ (x ⋅ y) → x ≡ y.
Proof.
  intros ?. apply equiv_dist=>n. by apply free_op_invN, cmra_valid_validN.
Qed.
Lemma to_free_op_invN a b n : ✓{n} (to_free a ⋅ to_free b) → a ≡{n}≡ b.
Proof. by intros ?%free_op_invN%(inj to_free). Qed.
Lemma to_free_op_inv a b : ✓ (to_free a ⋅ to_free b) → a ≡ b.
Proof. by intros ?%free_op_inv%(inj to_free). Qed.
Lemma to_free_op_inv_L `{!LeibnizEquiv A} a b : ✓ (to_free a ⋅ to_free b) → a = b.
Proof. by intros ?%to_free_op_inv%leibniz_equiv. Qed.

Lemma to_free_op_validN a b n : ✓{n} (to_free a ⋅ to_free b) ↔ a ≡{n}≡ b.
Proof.
  split; first by apply to_free_op_invN.
  intros ->. rewrite free_idemp //.
Qed.
Lemma to_free_op_valid a b : ✓ (to_free a ⋅ to_free b) ↔ a ≡ b.
Proof.
  split; first by apply to_free_op_inv.
  intros ->. rewrite free_idemp //.
Qed.
Lemma to_free_op_valid_L `{!LeibnizEquiv A} a b : ✓ (to_free a ⋅ to_free b) ↔ a = b.
Proof. rewrite to_free_op_valid. by fold_leibniz. Qed.

End free.

Global Instance: Params (@to_free) 1 := {}.
Global Arguments freeO : clear implicits.
Global Arguments freeR : clear implicits.

Program Definition free_map {A B} (f : A → B) (x : free A) : free B :=
  {| free_car := f <$> free_car x |}.
Next Obligation. by intros A B f [[|??] ?]. Qed.
Lemma free_map_id {A} (x : free A) : free_map id x = x.
Proof. apply free_eq. by rewrite /= list_fmap_id. Qed.
Lemma free_map_compose {A B C} (f : A → B) (g : B → C) (x : free A) :
  free_map (g ∘ f) x = free_map g (free_map f x).
Proof. apply free_eq. by rewrite /= list_fmap_compose. Qed.
Lemma free_map_to_free {A B} (f : A → B) (x : A) :
  free_map f (to_free x) = to_free (f x).
Proof. by apply free_eq. Qed.

Section free_map.
  Context {A B : ofe} (f : A → B) {Hf: NonExpansive f}.

  Local Instance free_map_ne : NonExpansive (free_map f).
  Proof using Type*.
    intros n x y [H H']; split=> b /=; setoid_rewrite elem_of_list_fmap.
    - intros (a&->&?). destruct (H a) as (a'&?&?); auto. naive_solver.
    - intros (a&->&?). destruct (H' a) as (a'&?&?); auto. naive_solver.
  Qed.
  Local Instance free_map_proper : Proper ((≡) ==> (≡)) (free_map f) := ne_proper _.

  Lemma free_map_ext (g : A → B) x :
    (∀ a, f a ≡ g a) → free_map f x ≡ free_map g x.
  Proof using Hf.
    intros Hfg n; split=> b /=; setoid_rewrite elem_of_list_fmap.
    - intros (a&->&?). exists (g a). rewrite Hfg; eauto.
    - intros (a&->&?). exists (f a). rewrite -Hfg; eauto.
  Qed.

  Global Instance free_map_morphism : CmraMorphism (free_map f).
  Proof using Hf.
    split; first apply _.
    - intros n x. rewrite !free_validN_def=> Hv b b' /=.
      intros (a&->&?)%elem_of_list_fmap (a'&->&?)%elem_of_list_fmap.
      apply Hf; eauto.
    - done.
    - intros x y n; split=> b /=;
        rewrite !fmap_app; setoid_rewrite elem_of_app; eauto.
  Qed.
End free_map.

Definition freeO_map {A B} (f : A -n> B) : freeO A -n> freeO B :=
  OfeMor (free_map f : freeO A → freeO B).
Global Instance freeO_map_ne A B : NonExpansive (@freeO_map A B).
Proof.
  intros n f g Hfg x; split=> b /=;
    setoid_rewrite elem_of_list_fmap; naive_solver.
Qed.

Program Definition freeRF (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := freeR (oFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := freeO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros ? A1 ? A2 ? B1 ? B2 ? n ???; simpl. by apply freeO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x; simpl. rewrite -{2}(free_map_id x).
  apply (free_map_ext _)=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl. rewrite -free_map_compose.
  apply (free_map_ext _)=>y; apply oFunctor_map_compose.
Qed.

Global Instance freeRF_contractive F :
  oFunctorContractive F → rFunctorContractive (freeRF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n ???; simpl.
  by apply freeO_map_ne, oFunctor_map_contractive.
Qed.

