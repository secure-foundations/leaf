From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

(** * Local updates *)
Definition local_update {A : cmra} (x y : A * A) := ∀ n mz,
  ✓{n} x.1 → x.1 ≡{n}≡ x.2 ⋅? mz → ✓{n} y.1 ∧ y.1 ≡{n}≡ y.2 ⋅? mz.
Global Instance: Params (@local_update) 1 := {}.
Infix "~l~>" := local_update (at level 70).

Section updates.
  Context {A : cmra}.
  Implicit Types x y : A.

  Global Instance local_update_proper :
    Proper ((≡) ==> (≡) ==> iff) (@local_update A).
  Proof. unfold local_update. by repeat intro; setoid_subst. Qed.

  Global Instance local_update_preorder : PreOrder (@local_update A).
  Proof. split; unfold local_update; red; naive_solver. Qed.

  Lemma exclusive_local_update `{!Exclusive y} x x' : ✓ x' → (x,y) ~l~> (x',x').
  Proof.
    intros ? n mz Hxv Hx; simpl in *.
    move: Hxv; rewrite Hx; move=> /exclusiveN_opM=> ->; split; auto.
    by apply cmra_valid_validN.
  Qed.

  Lemma op_local_update x y z :
    (∀ n, ✓{n} x → ✓{n} (z ⋅ x)) → (x,y) ~l~> (z ⋅ x, z ⋅ y).
  Proof.
    intros Hv n mz Hxv Hx; simpl in *; split; [by auto|].
    by rewrite Hx -cmra_op_opM_assoc.
  Qed.
  Lemma op_local_update_discrete `{!CmraDiscrete A} x y z :
    (✓ x → ✓ (z ⋅ x)) → (x,y) ~l~> (z ⋅ x, z ⋅ y).
  Proof.
    intros; apply op_local_update=> n. by rewrite -!(cmra_discrete_valid_iff n).
  Qed.

  Lemma op_local_update_frame x y x' y' yf :
    (x,y) ~l~> (x',y') → (x,y ⋅ yf) ~l~> (x', y' ⋅ yf).
  Proof.
    intros Hup n mz Hxv Hx; simpl in *.
    destruct (Hup n (Some (yf ⋅? mz))); [done|by rewrite /= -cmra_op_opM_assoc|].
    by rewrite cmra_op_opM_assoc.
  Qed.

  Lemma cancel_local_update x y z `{!Cancelable x} :
    (x ⋅ y, x ⋅ z) ~l~> (y, z).
  Proof.
    intros n f ? Heq. split; first by eapply cmra_validN_op_r.
    apply (cancelableN x); first done. by rewrite -cmra_op_opM_assoc.
  Qed.

  Lemma replace_local_update x y `{!IdFree x} :
    ✓ y → (x, x) ~l~> (y, y).
  Proof.
    intros ? n mz ? Heq; simpl in *; split; first by apply cmra_valid_validN.
    destruct mz as [z|]; [|done]. by destruct (id_freeN_r n n x z).
  Qed.

  Lemma core_id_local_update x y z `{!CoreId y} :
    y ≼ x → (x, z) ~l~> (x, z ⋅ y).
  Proof.
    intros Hincl n mf ? Heq; simpl in *; split; first done.
    rewrite [x]core_id_extract // Heq. destruct mf as [f|]; last done.
    simpl. rewrite -assoc [f ⋅ y]comm assoc //.
  Qed.

  Lemma local_update_discrete `{!CmraDiscrete A} (x y x' y' : A) :
    (x,y) ~l~> (x',y') ↔ ∀ mz, ✓ x → x ≡ y ⋅? mz → ✓ x' ∧ x' ≡ y' ⋅? mz.
  Proof.
    rewrite /local_update /=. setoid_rewrite <-cmra_discrete_valid_iff.
    setoid_rewrite <-(λ n, discrete_iff n x).
    setoid_rewrite <-(λ n, discrete_iff n x'). naive_solver eauto using O.
  Qed.

  Lemma local_update_valid0 x y x' y' :
    (✓{0} x → ✓{0} y → Some y ≼{0} Some x → (x,y) ~l~> (x',y')) →
    (x,y) ~l~> (x',y').
  Proof.
    intros Hup n mz Hmz Hz; simpl in *. apply Hup; auto.
    - by apply (cmra_validN_le n); last lia.
    - apply (cmra_validN_le n); last lia.
      move: Hmz; rewrite Hz. destruct mz; simpl; eauto using cmra_validN_op_l.
    - eapply (cmra_includedN_le n); last lia.
      apply Some_includedN_opM. eauto.
  Qed.
  Lemma local_update_valid `{!CmraDiscrete A} x y x' y' :
    (✓ x → ✓ y → Some y ≼ Some x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof.
    rewrite !(cmra_discrete_valid_iff 0) (cmra_discrete_included_iff 0).
    apply local_update_valid0.
  Qed.

  Lemma local_update_total_valid0 `{!CmraTotal A} x y x' y' :
    (✓{0} x → ✓{0} y → y ≼{0} x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof.
    intros Hup. apply local_update_valid0=> ?? Hincl. apply Hup; auto.
    by apply Some_includedN_total.
  Qed.
  Lemma local_update_total_valid `{!CmraTotal A, !CmraDiscrete A} x y x' y' :
    (✓ x → ✓ y → y ≼ x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof.
    rewrite !(cmra_discrete_valid_iff 0) (cmra_discrete_included_iff 0).
    apply local_update_total_valid0.
  Qed.
End updates.

Section updates_unital.
  Context {A : ucmra}.
  Implicit Types x y : A.

  Lemma local_update_unital x y x' y' :
    (x,y) ~l~> (x',y') ↔ ∀ n z,
      ✓{n} x → x ≡{n}≡ y ⋅ z → ✓{n} x' ∧ x' ≡{n}≡ y' ⋅ z.
  Proof.
    split.
    - intros Hup n z. apply (Hup _ (Some z)).
    - intros Hup n [z|]; simpl; [by auto|].
      rewrite -(right_id ε op y) -(right_id ε op y'). auto.
  Qed.

  Lemma local_update_unital_discrete `{!CmraDiscrete A} (x y x' y' : A) :
    (x,y) ~l~> (x',y') ↔ ∀ z, ✓ x → x ≡ y ⋅ z → ✓ x' ∧ x' ≡ y' ⋅ z.
  Proof.
    rewrite local_update_discrete. split.
    - intros Hup z. apply (Hup (Some z)).
    - intros Hup [z|]; simpl; [by auto|].
      rewrite -(right_id ε op y) -(right_id ε op y'). auto.
  Qed.

  Lemma cancel_local_update_unit x y `{!Cancelable x} :
    (x ⋅ y, x) ~l~> (y, ε).
  Proof. rewrite -{2}(right_id ε op x). by apply cancel_local_update. Qed.
End updates_unital.

(** * Unit *)
Lemma unit_local_update (x y x' y' : unit) : (x, y) ~l~> (x', y').
Proof. destruct x,y,x',y'; reflexivity. Qed.

(** * Dependently-typed functions over a discrete domain *)
Lemma discrete_fun_local_update {A} {B : A → ucmra} (f g f' g' : discrete_fun B) :
  (∀ x : A, (f x, g x) ~l~> (f' x, g' x)) →
  (f, g) ~l~> (f', g').
Proof.
  setoid_rewrite local_update_unital. intros Hupd n h Hf Hg.
  split=> x; eapply Hupd, Hg; eauto.
Qed.

(** * Product *)
Lemma prod_local_update {A B : cmra} (x y x' y' : A * B) :
  (x.1,y.1) ~l~> (x'.1,y'.1) → (x.2,y.2) ~l~> (x'.2,y'.2) →
  (x,y) ~l~> (x',y').
Proof.
  intros Hup1 Hup2 n mz [??] [??]; simpl in *.
  destruct (Hup1 n (fst <$> mz)); [done|by destruct mz|].
  destruct (Hup2 n (snd <$> mz)); [done|by destruct mz|].
  by destruct mz.
Qed.

Lemma prod_local_update' {A B : cmra} (x1 y1 x1' y1' : A) (x2 y2 x2' y2' : B) :
  (x1,y1) ~l~> (x1',y1') → (x2,y2) ~l~> (x2',y2') →
  ((x1,x2),(y1,y2)) ~l~> ((x1',x2'),(y1',y2')).
Proof. intros. by apply prod_local_update. Qed.
Lemma prod_local_update_1 {A B : cmra} (x1 y1 x1' y1' : A) (x2 y2 : B) :
  (x1,y1) ~l~> (x1',y1') → ((x1,x2),(y1,y2)) ~l~> ((x1',x2),(y1',y2)).
Proof. intros. by apply prod_local_update. Qed.
Lemma prod_local_update_2 {A B : cmra} (x1 y1 : A) (x2 y2 x2' y2' : B) :
  (x2,y2) ~l~> (x2',y2') → ((x1,x2),(y1,y2)) ~l~> ((x1,x2'),(y1,y2')).
Proof. intros. by apply prod_local_update. Qed.

(** * Option *)
Lemma option_local_update {A : cmra} (x y x' y' : A) :
  (x, y) ~l~> (x',y') →
  (Some x, Some y) ~l~> (Some x', Some y').
Proof.
  intros Hup. apply local_update_unital=>n mz Hxv Hx; simpl in *.
  destruct (Hup n mz); first done.
  { destruct mz as [?|]; inversion_clear Hx; auto. }
  split; first done. destruct mz as [?|]; constructor; auto.
Qed.

Lemma option_local_update_None {A: ucmra} (x x' y': A):
  (x, ε) ~l~> (x', y') ->
  (Some x, None) ~l~> (Some x', Some y').
Proof.
  intros Hup. apply local_update_unital=> n mz.
  rewrite left_id=> ? <-.
  destruct (Hup n (Some x)); simpl in *; first done.
  - by rewrite left_id.
  - split; first done. rewrite -Some_op. by constructor.
Qed.

Lemma alloc_option_local_update {A : cmra} (x : A) y :
  ✓ x →
  (None, y) ~l~> (Some x, Some x).
Proof.
  move=>Hx. apply local_update_unital=> n z _ /= Heq. split.
  { rewrite Some_validN. apply cmra_valid_validN. done. }
  destruct z as [z|]; last done. destruct y; inversion Heq.
Qed.

Lemma delete_option_local_update {A : cmra} (x : option A) (y : A) :
  Exclusive y → (x, Some y) ~l~> (None, None).
Proof.
  move=>Hex. apply local_update_unital=>n z /= Hy Heq. split; first done.
  destruct z as [z|]; last done. exfalso.
  move: Hy. rewrite Heq /= -Some_op=>Hy. eapply Hex.
  eapply cmra_validN_le; [|lia]. eapply Hy.
Qed.

Lemma delete_option_local_update_cancelable {A : cmra} (mx : option A) :
  Cancelable mx → (mx, mx) ~l~> (None, None).
Proof.
  intros ?. apply local_update_unital=>n mf /= Hmx Heq. split; first done.
  rewrite left_id. eapply (cancelableN mx); by rewrite right_id_L.
Qed.
