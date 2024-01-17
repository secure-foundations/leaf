From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

(** Define an agreement construction such that Agree A is discrete when A is discrete.
    Notice that this construction is NOT complete.  The following is due to Aleš:

Proposition: Ag(T) is not necessarily complete.
Proof.
  Let T be the set of binary streams (infinite sequences) with the usual
  ultrametric, measuring how far they agree.

  Let Aₙ be the set of all binary strings of length n. Thus for Aₙ to be a
  subset of T we have them continue as a stream of zeroes.

  Now Aₙ is a finite non-empty subset of T. Moreover {Aₙ} is a Cauchy sequence
  in the defined (Hausdorff) metric.

  However the limit (if it were to exist as an element of Ag(T)) would have to
  be the set of all binary streams, which is not exactly finite.

  Thus Ag(T) is not necessarily complete.
*)

(** Note that the projection [agree_car] is not non-expansive, so it cannot be
used in the logic. If you need to get a witness out, you should use the
lemma [to_agree_uninjN] instead. In general, [agree_car] should ONLY be used
internally in this file.  *)
Record agree (A : Type) : Type := {
  agree_car : list A;
  agree_not_nil : bool_decide (agree_car = []) = false
}.
Global Arguments agree_car {_} _.
Global Arguments agree_not_nil {_} _.
Local Coercion agree_car : agree >-> list.

Definition to_agree {A} (a : A) : agree A :=
  {| agree_car := [a]; agree_not_nil := eq_refl |}.

Lemma elem_of_agree {A} (x : agree A) : ∃ a, a ∈ agree_car x.
Proof. destruct x as [[|a ?] ?]; set_solver+. Qed.
Lemma agree_eq {A} (x y : agree A) : agree_car x = agree_car y → x = y.
Proof.
  destruct x as [a ?], y as [b ?]; simpl.
  intros ->; f_equal. apply (proof_irrel _).
Qed.

Section agree.
Context {A : ofe}.
Implicit Types a b : A.
Implicit Types x y : agree A.

(* OFE *)
Local Instance agree_dist : Dist (agree A) := λ n x y,
  (∀ a, a ∈ agree_car x → ∃ b, b ∈ agree_car y ∧ a ≡{n}≡ b) ∧
  (∀ b, b ∈ agree_car y → ∃ a, a ∈ agree_car x ∧ a ≡{n}≡ b).
Local Instance agree_equiv : Equiv (agree A) := λ x y, ∀ n, x ≡{n}≡ y.

Definition agree_ofe_mixin : OfeMixin (agree A).
Proof.
  split.
  - done.
  - intros n; split; rewrite /dist /agree_dist.
    + intros x; split; eauto.
    + intros x y [??]. naive_solver eauto.
    + intros x y z [H1 H1'] [H2 H2']; split.
      * intros a ?. destruct (H1 a) as (b&?&?); auto.
        destruct (H2 b) as (c&?&?); eauto. by exists c; split; last etrans.
      * intros a ?. destruct (H2' a) as (b&?&?); auto.
        destruct (H1' b) as (c&?&?); eauto. by exists c; split; last etrans.
  - intros n m x y [??] ?; split; naive_solver eauto using dist_le with si_solver.
Qed.
Canonical Structure agreeO := Ofe (agree A) agree_ofe_mixin.

(* CMRA *)
(* agree_validN is carefully written such that, when applied to a singleton, it
is convertible to True. This makes working with agreement much more pleasant. *)
Local Instance agree_validN_instance : ValidN (agree A) := λ n x,
  match agree_car x with
  | [a] => True
  | _ => ∀ a b, a ∈ agree_car x → b ∈ agree_car x → a ≡{n}≡ b
  end.
Local Instance agree_valid_instance : Valid (agree A) := λ x, ∀ n, ✓{n} x.

Local Program Instance agree_op_instance : Op (agree A) := λ x y,
  {| agree_car := agree_car x ++ agree_car y |}.
Next Obligation. by intros [[|??]] y. Qed.
Local Instance agree_pcore_instance : PCore (agree A) := Some.

Lemma agree_validN_def n x :
  ✓{n} x ↔ ∀ a b, a ∈ agree_car x → b ∈ agree_car x → a ≡{n}≡ b.
Proof.
  rewrite /validN /agree_validN_instance. destruct (agree_car _) as [|? [|??]]; auto.
  setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.

Local Instance agree_comm : Comm (≡) (@op (agree A) _).
Proof. intros x y n; split=> a /=; setoid_rewrite elem_of_app; naive_solver. Qed.
Local Instance agree_assoc : Assoc (≡) (@op (agree A) _).
Proof.
  intros x y z n; split=> a /=; repeat setoid_rewrite elem_of_app; naive_solver.
Qed.
Lemma agree_idemp x : x ⋅ x ≡ x.
Proof. intros n; split=> a /=; setoid_rewrite elem_of_app; naive_solver. Qed.

Local Instance agree_validN_ne n : Proper (dist n ==> impl) (@validN (agree A) _ n).
Proof.
  intros x y [H H']; rewrite /impl !agree_validN_def; intros Hv a b Ha Hb.
  destruct (H' a) as (a'&?&<-); auto. destruct (H' b) as (b'&?&<-); auto.
Qed.
Local Instance agree_validN_proper n : Proper (equiv ==> iff) (@validN (agree A) _ n).
Proof. move=> x y /equiv_dist H. by split; rewrite (H n). Qed.

Local Instance agree_op_ne' x : NonExpansive (op x).
Proof.
  intros n y1 y2 [H H']; split=> a /=; setoid_rewrite elem_of_app; naive_solver.
Qed.
Local Instance agree_op_ne : NonExpansive2 (@op (agree A) _).
Proof. by intros n x1 x2 Hx y1 y2 Hy; rewrite Hy !(comm _ _ y2) Hx. Qed.
Local Instance agree_op_proper : Proper ((≡) ==> (≡) ==> (≡)) (op (A := agree A)) := ne_proper_2 _.

Lemma agree_included x y : x ≼ y ↔ y ≡ x ⋅ y.
Proof.
  split; [|by intros ?; exists y].
  by intros [z Hz]; rewrite Hz assoc agree_idemp.
Qed.

Lemma agree_op_invN n x1 x2 : ✓{n} (x1 ⋅ x2) → x1 ≡{n}≡ x2.
Proof.
  rewrite agree_validN_def /=. setoid_rewrite elem_of_app=> Hv; split=> a Ha.
  - destruct (elem_of_agree x2); naive_solver.
  - destruct (elem_of_agree x1); naive_solver.
Qed.

Definition agree_cmra_mixin : CmraMixin (agree A).
Proof.
  apply cmra_total_mixin; try apply _ || by eauto.
  - intros n x; rewrite !agree_validN_def; eauto using dist_le.
  - intros x. apply agree_idemp.
  - intros n x y; rewrite !agree_validN_def /=.
    setoid_rewrite elem_of_app; naive_solver.
  - intros n x y1 y2 Hval Hx; exists x, x; simpl; split.
    + by rewrite agree_idemp.
    + by move: Hval; rewrite Hx; move=> /agree_op_invN->; rewrite agree_idemp.
Qed.
Canonical Structure agreeR : cmra := Cmra (agree A) agree_cmra_mixin.

Global Instance agree_cmra_total : CmraTotal agreeR.
Proof. rewrite /CmraTotal; eauto. Qed.
Global Instance agree_core_id x : CoreId x.
Proof. by constructor. Qed.

Global Instance agree_cmra_discrete : OfeDiscrete A → CmraDiscrete agreeR.
Proof.
  intros HD. split.
  - intros x y [H H'] n; split=> a; setoid_rewrite <-(discrete_iff_0 _ _); auto.
  - intros x; rewrite agree_validN_def=> Hv n. apply agree_validN_def=> a b ??.
    apply discrete_iff_0; auto.
Qed.

Global Instance to_agree_ne : NonExpansive to_agree.
Proof.
  intros n a1 a2 Hx; split=> b /=;
    setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.
Global Instance to_agree_proper : Proper ((≡) ==> (≡)) to_agree := ne_proper _.

Global Instance to_agree_discrete a : Discrete a → Discrete (to_agree a).
Proof.
  intros ? y [H H'] n; split.
  - intros a' ->%elem_of_list_singleton. destruct (H a) as [b ?]; first by left.
    exists b. by rewrite -discrete_iff_0.
  - intros b Hb. destruct (H' b) as (b'&->%elem_of_list_singleton&?); auto.
    exists a. by rewrite elem_of_list_singleton -discrete_iff_0.
Qed.

Lemma agree_op_inv x y : ✓ (x ⋅ y) → x ≡ y.
Proof.
  intros ?. apply equiv_dist=> n. by apply agree_op_invN, cmra_valid_validN.
Qed.

Global Instance to_agree_injN n : Inj (dist n) (dist n) (to_agree).
Proof.
  move=> a b [_] /=. setoid_rewrite elem_of_list_singleton. naive_solver.
Qed.
Global Instance to_agree_inj : Inj (≡) (≡) (to_agree).
Proof. intros a b ?. apply equiv_dist=>n. by apply (inj to_agree), equiv_dist. Qed.

Lemma to_agree_uninjN n x : ✓{n} x → ∃ a, to_agree a ≡{n}≡ x.
Proof.
  rewrite agree_validN_def=> Hv.
  destruct (elem_of_agree x) as [a ?].
  exists a; split=> b /=; setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.
Lemma to_agree_uninj x : ✓ x → ∃ a, to_agree a ≡ x.
Proof.
  rewrite /valid /agree_valid_instance; setoid_rewrite agree_validN_def.
  destruct (elem_of_agree x) as [a ?].
  exists a; split=> b /=; setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.

Lemma agree_valid_includedN n x y : ✓{n} y → x ≼{n} y → x ≡{n}≡ y.
Proof.
  move=> Hval [z Hy]; move: Hval; rewrite Hy.
  by move=> /agree_op_invN->; rewrite agree_idemp.
Qed.
Lemma agree_valid_included x y : ✓ y → x ≼ y → x ≡ y.
Proof.
  move=> Hval [z Hy]; move: Hval; rewrite Hy.
  by move=> /agree_op_inv->; rewrite agree_idemp.
Qed.

Lemma to_agree_includedN n a b : to_agree a ≼{n} to_agree b ↔ a ≡{n}≡ b.
Proof.
  split; last by intros ->.
  intros. by apply (inj to_agree), agree_valid_includedN.
Qed.
Lemma to_agree_included a b : to_agree a ≼ to_agree b ↔ a ≡ b.
Proof.
  split; last by intros ->.
  intros. by apply (inj to_agree), agree_valid_included.
Qed.

Global Instance agree_cancelable x : Cancelable x.
Proof.
  intros n y z Hv Heq.
  destruct (to_agree_uninjN n x) as [x' EQx]; first by eapply cmra_validN_op_l.
  destruct (to_agree_uninjN n y) as [y' EQy]; first by eapply cmra_validN_op_r.
  destruct (to_agree_uninjN n z) as [z' EQz].
  { eapply (cmra_validN_op_r n x z). by rewrite -Heq. }
  assert (Hx'y' : x' ≡{n}≡ y').
  { apply (inj to_agree), agree_op_invN. by rewrite EQx EQy. }
  assert (Hx'z' : x' ≡{n}≡ z').
  { apply (inj to_agree), agree_op_invN. by rewrite EQx EQz -Heq. }
  by rewrite -EQy -EQz -Hx'y' -Hx'z'.
Qed.

Lemma to_agree_op_invN a b n : ✓{n} (to_agree a ⋅ to_agree b) → a ≡{n}≡ b.
Proof. by intros ?%agree_op_invN%(inj to_agree). Qed.
Lemma to_agree_op_inv a b : ✓ (to_agree a ⋅ to_agree b) → a ≡ b.
Proof. by intros ?%agree_op_inv%(inj to_agree). Qed.
Lemma to_agree_op_inv_L `{!LeibnizEquiv A} a b : ✓ (to_agree a ⋅ to_agree b) → a = b.
Proof. by intros ?%to_agree_op_inv%leibniz_equiv. Qed.

Lemma to_agree_op_validN a b n : ✓{n} (to_agree a ⋅ to_agree b) ↔ a ≡{n}≡ b.
Proof.
  split; first by apply to_agree_op_invN.
  intros ->. rewrite agree_idemp //.
Qed.
Lemma to_agree_op_valid a b : ✓ (to_agree a ⋅ to_agree b) ↔ a ≡ b.
Proof.
  split; first by apply to_agree_op_inv.
  intros ->. rewrite agree_idemp //.
Qed.
Lemma to_agree_op_valid_L `{!LeibnizEquiv A} a b : ✓ (to_agree a ⋅ to_agree b) ↔ a = b.
Proof. rewrite to_agree_op_valid. by fold_leibniz. Qed.

End agree.

Global Instance: Params (@to_agree) 1 := {}.
Global Arguments agreeO : clear implicits.
Global Arguments agreeR : clear implicits.

Program Definition agree_map {A B} (f : A → B) (x : agree A) : agree B :=
  {| agree_car := f <$> agree_car x |}.
Next Obligation. by intros A B f [[|??] ?]. Qed.
Lemma agree_map_id {A} (x : agree A) : agree_map id x = x.
Proof. apply agree_eq. by rewrite /= list_fmap_id. Qed.
Lemma agree_map_compose {A B C} (f : A → B) (g : B → C) (x : agree A) :
  agree_map (g ∘ f) x = agree_map g (agree_map f x).
Proof. apply agree_eq. by rewrite /= list_fmap_compose. Qed.
Lemma agree_map_to_agree {A B} (f : A → B) (x : A) :
  agree_map f (to_agree x) = to_agree (f x).
Proof. by apply agree_eq. Qed.

Section agree_map.
  Context {A B : ofe} (f : A → B) {Hf: NonExpansive f}.

  Local Instance agree_map_ne : NonExpansive (agree_map f).
  Proof using Type*.
    intros n x y [H H']; split=> b /=; setoid_rewrite elem_of_list_fmap.
    - intros (a&->&?). destruct (H a) as (a'&?&?); auto. naive_solver.
    - intros (a&->&?). destruct (H' a) as (a'&?&?); auto. naive_solver.
  Qed.
  Local Instance agree_map_proper : Proper ((≡) ==> (≡)) (agree_map f) := ne_proper _.

  Lemma agree_map_ext (g : A → B) x :
    (∀ a, f a ≡ g a) → agree_map f x ≡ agree_map g x.
  Proof using Hf.
    intros Hfg n; split=> b /=; setoid_rewrite elem_of_list_fmap.
    - intros (a&->&?). exists (g a). rewrite Hfg; eauto.
    - intros (a&->&?). exists (f a). rewrite -Hfg; eauto.
  Qed.

  Global Instance agree_map_morphism : CmraMorphism (agree_map f).
  Proof using Hf.
    split; first apply _.
    - intros n x. rewrite !agree_validN_def=> Hv b b' /=.
      intros (a&->&?)%elem_of_list_fmap (a'&->&?)%elem_of_list_fmap.
      apply Hf; eauto.
    - done.
    - intros x y n; split=> b /=;
        rewrite !fmap_app; setoid_rewrite elem_of_app; eauto.
  Qed.
End agree_map.

Definition agreeO_map {A B} (f : A -n> B) : agreeO A -n> agreeO B :=
  OfeMor (agree_map f : agreeO A → agreeO B).
Global Instance agreeO_map_ne A B : NonExpansive (@agreeO_map A B).
Proof.
  intros n f g Hfg x; split=> b /=;
    setoid_rewrite elem_of_list_fmap; naive_solver.
Qed.

Program Definition agreeRF (F : oFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := agreeR (oFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := agreeO_map (oFunctor_map F fg)
|}.
Next Obligation.
  intros ? A1 ? A2 ? B1 ? B2 ? n ???; simpl. by apply agreeO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x; simpl. rewrite -{2}(agree_map_id x).
  apply (agree_map_ext _)=>y. by rewrite oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl. rewrite -agree_map_compose.
  apply (agree_map_ext _)=>y; apply oFunctor_map_compose.
Qed.

Global Instance agreeRF_contractive F :
  oFunctorContractive F → rFunctorContractive (agreeRF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n ???; simpl.
  by apply agreeO_map_ne, oFunctor_map_contractive.
Qed.
