From iris.bi Require Import derived_laws_later big_op.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.

(** This file defines a type class for BIs with a notion of internal equality.
Internal equality is not part of the [bi] canonical structure as [internal_eq]
can only be given a definition that satisfies [NonExpansive2 internal_eq] _and_
[▷ (x ≡ y) ⊢ Next x ≡ Next y] if the BI is step-indexed. *)
Class InternalEq (PROP : bi) :=
  internal_eq : ∀ {A : ofe}, A → A → PROP.
Global Arguments internal_eq {_ _ _} _ _ : simpl never.
Global Hint Mode InternalEq ! : typeclass_instances.
Global Instance: Params (@internal_eq) 3 := {}.
Infix "≡" := internal_eq : bi_scope.
Infix "≡@{ A }" := (internal_eq (A := A)) (only parsing) : bi_scope.

Notation "( X ≡.)" := (internal_eq X) (only parsing) : bi_scope.
Notation "(.≡ X )" := (λ Y, Y ≡ X)%I (only parsing) : bi_scope.
Notation "(≡@{ A } )" := (internal_eq (A:=A)) (only parsing) : bi_scope.

(* Mixins allow us to create instances easily without having to use Program *)
Record BiInternalEqMixin (PROP : bi) `(InternalEq PROP) := {
  bi_internal_eq_mixin_internal_eq_ne (A : ofe) : NonExpansive2 (@internal_eq PROP _ A);
  bi_internal_eq_mixin_internal_eq_refl {A : ofe} (P : PROP) (a : A) : P ⊢ a ≡ a;
  bi_internal_eq_mixin_internal_eq_rewrite {A : ofe} a b (Ψ : A → PROP) :
    NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b;
  bi_internal_eq_mixin_fun_extI {A} {B : A → ofe} (f g : discrete_fun B) :
    (∀ x, f x ≡ g x) ⊢@{PROP} f ≡ g;
  bi_internal_eq_mixin_sig_equivI_1 {A : ofe} (P : A → Prop) (x y : sig P) :
    `x ≡ `y ⊢@{PROP} x ≡ y;
  bi_internal_eq_mixin_discrete_eq_1 {A : ofe} (a b : A) :
    Discrete a → a ≡ b ⊢@{PROP} ⌜a ≡ b⌝;
  bi_internal_eq_mixin_later_equivI_1 {A : ofe} (x y : A) :
    Next x ≡ Next y ⊢@{PROP} ▷ (x ≡ y);
  bi_internal_eq_mixin_later_equivI_2 {A : ofe} (x y : A) :
    ▷ (x ≡ y) ⊢@{PROP} Next x ≡ Next y;
}.

Class BiInternalEq (PROP : bi) := {
  bi_internal_eq_internal_eq :> InternalEq PROP;
  bi_internal_eq_mixin : BiInternalEqMixin PROP bi_internal_eq_internal_eq;
}.
Global Hint Mode BiInternalEq ! : typeclass_instances.
Global Arguments bi_internal_eq_internal_eq : simpl never.

Section internal_eq_laws.
  Context `{BiInternalEq PROP}.
  Implicit Types P Q : PROP.

  Global Instance internal_eq_ne (A : ofe) : NonExpansive2 (@internal_eq PROP _ A).
  Proof. eapply bi_internal_eq_mixin_internal_eq_ne, (bi_internal_eq_mixin). Qed.

  Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ a ≡ a.
  Proof. eapply bi_internal_eq_mixin_internal_eq_refl, bi_internal_eq_mixin. Qed.
  Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → PROP) :
    NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
  Proof. eapply bi_internal_eq_mixin_internal_eq_rewrite, bi_internal_eq_mixin. Qed.

  Lemma fun_extI {A} {B : A → ofe} (f g : discrete_fun B) :
    (∀ x, f x ≡ g x) ⊢@{PROP} f ≡ g.
  Proof. eapply bi_internal_eq_mixin_fun_extI, bi_internal_eq_mixin. Qed.
  Lemma sig_equivI_1 {A : ofe} (P : A → Prop) (x y : sig P) :
    `x ≡ `y ⊢@{PROP} x ≡ y.
  Proof. eapply bi_internal_eq_mixin_sig_equivI_1, bi_internal_eq_mixin. Qed.
  Lemma discrete_eq_1 {A : ofe} (a b : A) :
    Discrete a → a ≡ b ⊢@{PROP} ⌜a ≡ b⌝.
  Proof. eapply bi_internal_eq_mixin_discrete_eq_1, bi_internal_eq_mixin. Qed.

  Lemma later_equivI_1 {A : ofe} (x y : A) : Next x ≡ Next y ⊢@{PROP} ▷ (x ≡ y).
  Proof. eapply bi_internal_eq_mixin_later_equivI_1, bi_internal_eq_mixin. Qed.
  Lemma later_equivI_2 {A : ofe} (x y : A) : ▷ (x ≡ y) ⊢@{PROP} Next x ≡ Next y.
  Proof. eapply bi_internal_eq_mixin_later_equivI_2, bi_internal_eq_mixin. Qed.
End internal_eq_laws.

(* Derived laws *)
Section internal_eq_derived.
Context `{BiInternalEq PROP}.
Implicit Types P : PROP.

(* Force implicit argument PROP *)
Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

Global Instance internal_eq_proper (A : ofe) :
  Proper ((≡) ==> (≡) ==> (⊣⊢)) (@internal_eq PROP _ A) := ne_proper_2 _.

(* Equality *)
Local Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim : core.
Local Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro : core.
Local Hint Resolve internal_eq_refl : core.
Local Hint Extern 100 (NonExpansive _) => solve_proper : core.

Lemma equiv_internal_eq {A : ofe} P (a b : A) : a ≡ b → P ⊢ a ≡ b.
Proof. intros ->. auto. Qed.
Lemma internal_eq_rewrite' {A : ofe} a b (Ψ : A → PROP) P
  {HΨ : NonExpansive Ψ} : (P ⊢ a ≡ b) → (P ⊢ Ψ a) → P ⊢ Ψ b.
Proof.
  intros Heq HΨa. rewrite -(idemp bi_and P) {1}Heq HΨa.
  apply impl_elim_l'. by apply internal_eq_rewrite.
Qed.

Lemma internal_eq_sym {A : ofe} (a b : A) : a ≡ b ⊢ b ≡ a.
Proof. apply (internal_eq_rewrite' a b (λ b, b ≡ a)%I); auto. Qed.
Lemma internal_eq_iff P Q : P ≡ Q ⊢ P ↔ Q.
Proof. apply (internal_eq_rewrite' P Q (λ Q, P ↔ Q))%I; auto using iff_refl. Qed.

Lemma f_equivI {A B : ofe} (f : A → B) `{!NonExpansive f} x y :
  x ≡ y ⊢ f x ≡ f y.
Proof. apply (internal_eq_rewrite' x y (λ y, f x ≡ f y)%I); auto. Qed.
Lemma f_equivI_contractive {A B : ofe} (f : A → B) `{Hf : !Contractive f} x y :
  ▷ (x ≡ y) ⊢ f x ≡ f y.
Proof.
  rewrite later_equivI_2. move: Hf=>/contractive_alt [g [? Hfg]]. rewrite !Hfg.
  by apply f_equivI.
Qed.

Lemma prod_equivI {A B : ofe} (x y : A * B) : x ≡ y ⊣⊢ x.1 ≡ y.1 ∧ x.2 ≡ y.2.
Proof.
  apply (anti_symm _).
  - apply and_intro; apply f_equivI; apply _.
  - rewrite {3}(surjective_pairing x) {3}(surjective_pairing y).
    apply (internal_eq_rewrite' (x.1) (y.1) (λ a, (x.1,x.2) ≡ (a,y.2))%I); auto.
    apply (internal_eq_rewrite' (x.2) (y.2) (λ b, (x.1,x.2) ≡ (x.1,b))%I); auto.
Qed.
Lemma sum_equivI {A B : ofe} (x y : A + B) :
  x ≡ y ⊣⊢
    match x, y with
    | inl a, inl a' => a ≡ a' | inr b, inr b' => b ≡ b' | _, _ => False
    end.
Proof.
  apply (anti_symm _).
  - apply (internal_eq_rewrite' x y (λ y,
             match x, y with
             | inl a, inl a' => a ≡ a' | inr b, inr b' => b ≡ b' | _, _ => False
             end)%I); auto.
    destruct x; auto.
  - destruct x as [a|b], y as [a'|b']; auto; apply f_equivI, _.
Qed.
Lemma option_equivI {A : ofe} (x y : option A) :
  x ≡ y ⊣⊢ match x, y with
           | Some a, Some a' => a ≡ a' | None, None => True | _, _ => False
           end.
Proof.
  apply (anti_symm _).
  - apply (internal_eq_rewrite' x y (λ y,
             match x, y with
             | Some a, Some a' => a ≡ a' | None, None => True | _, _ => False
             end)%I); auto.
    destruct x; auto.
  - destruct x as [a|], y as [a'|]; auto. apply f_equivI, _.
Qed.

Lemma sig_equivI {A : ofe} (P : A → Prop) (x y : sig P) : `x ≡ `y ⊣⊢ x ≡ y.
Proof.
  apply (anti_symm _).
  - apply sig_equivI_1.
  - apply f_equivI, _.
Qed.

Section sigT_equivI.
Import EqNotations.

Lemma sigT_equivI {A : Type} {P : A → ofe} (x y : sigT P) :
  x ≡ y ⊣⊢
  ∃ eq : projT1 x = projT1 y, rew eq in projT2 x ≡ projT2 y.
Proof.
  apply (anti_symm _).
  - apply (internal_eq_rewrite' x y (λ y,
             ∃ eq : projT1 x = projT1 y,
               rew eq in projT2 x ≡ projT2 y))%I;
        [| done | exact: (exist_intro' _ _ eq_refl) ].
    move => n [a pa] [b pb] [/=]; intros -> => /= Hab.
    apply exist_ne => ?. by rewrite Hab.
  - apply exist_elim. move: x y => [a pa] [b pb] /=. intros ->; simpl.
    apply f_equivI, _.
Qed.
End sigT_equivI.

Lemma discrete_fun_equivI {A} {B : A → ofe} (f g : discrete_fun B) : f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
Proof.
  apply (anti_symm _); auto using fun_extI.
  apply (internal_eq_rewrite' f g (λ g, ∀ x : A, f x ≡ g x)%I); auto.
  intros n h h' Hh; apply forall_ne=> x; apply internal_eq_ne; auto.
Qed.
Lemma ofe_morO_equivI {A B : ofe} (f g : A -n> B) : f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
Proof.
  apply (anti_symm _).
  - apply (internal_eq_rewrite' f g (λ g, ∀ x : A, f x ≡ g x)%I); auto.
  - rewrite -(discrete_fun_equivI (ofe_mor_car _ _ f) (ofe_mor_car _ _ g)).
    set (h1 (f : A -n> B) :=
      exist (λ f : A -d> B, NonExpansive (f : A → B)) f (ofe_mor_ne A B f)).
    set (h2 (f : sigO (λ f : A -d> B, NonExpansive (f : A → B))) :=
      @OfeMor A B (`f) (proj2_sig f)).
    assert (∀ f, h2 (h1 f) = f) as Hh by (by intros []).
    assert (NonExpansive h2) by (intros ??? EQ; apply EQ).
    by rewrite -{2}[f]Hh -{2}[g]Hh -f_equivI -sig_equivI.
Qed.

Lemma pure_internal_eq {A : ofe} (x y : A) : ⌜x ≡ y⌝ ⊢ x ≡ y.
Proof. apply pure_elim'=> ->. apply internal_eq_refl. Qed.
Lemma discrete_eq {A : ofe} (a b : A) : Discrete a → a ≡ b ⊣⊢ ⌜a ≡ b⌝.
Proof.
  intros. apply (anti_symm _); auto using discrete_eq_1, pure_internal_eq.
Qed.

Lemma absorbingly_internal_eq {A : ofe} (x y : A) : <absorb> (x ≡ y) ⊣⊢ x ≡ y.
Proof.
  apply (anti_symm _), absorbingly_intro.
  apply wand_elim_r', (internal_eq_rewrite' x y (λ y, True -∗ x ≡ y)%I); auto.
  apply wand_intro_l, internal_eq_refl.
Qed.
Lemma persistently_internal_eq {A : ofe} (a b : A) : <pers> (a ≡ b) ⊣⊢ a ≡ b.
Proof.
  apply (anti_symm (⊢)).
  { by rewrite persistently_into_absorbingly absorbingly_internal_eq. }
  apply (internal_eq_rewrite' a b (λ b, <pers> (a ≡ b))%I); auto.
  rewrite -(internal_eq_refl emp%I a). apply persistently_emp_intro.
Qed.

Global Instance internal_eq_absorbing {A : ofe} (x y : A) :
  Absorbing (PROP:=PROP) (x ≡ y).
Proof. by rewrite /Absorbing absorbingly_internal_eq. Qed.
Global Instance internal_eq_persistent {A : ofe} (a b : A) :
  Persistent (PROP:=PROP) (a ≡ b).
Proof. by intros; rewrite /Persistent persistently_internal_eq. Qed.

(* Equality under a later. *)
Lemma internal_eq_rewrite_contractive {A : ofe} a b (Ψ : A → PROP)
  {HΨ : Contractive Ψ} : ▷ (a ≡ b) ⊢ Ψ a → Ψ b.
Proof.
  rewrite f_equivI_contractive. apply (internal_eq_rewrite (Ψ a) (Ψ b) id _).
Qed.
Lemma internal_eq_rewrite_contractive' {A : ofe} a b (Ψ : A → PROP) P
  {HΨ : Contractive Ψ} : (P ⊢ ▷ (a ≡ b)) → (P ⊢ Ψ a) → P ⊢ Ψ b.
Proof.
  rewrite later_equivI_2. move: HΨ=>/contractive_alt [g [? HΨ]]. rewrite !HΨ.
  by apply internal_eq_rewrite'.
Qed.

Lemma later_equivI {A : ofe} (x y : A) : Next x ≡ Next y ⊣⊢ ▷ (x ≡ y).
Proof. apply (anti_symm _); auto using later_equivI_1, later_equivI_2. Qed.
Lemma later_equivI_prop_2 `{!Contractive (bi_later (PROP:=PROP))} P Q :
  ▷ (P ≡ Q) ⊢ (▷ P) ≡ (▷ Q).
Proof. apply (f_equivI_contractive _). Qed.

Global Instance eq_timeless {A : ofe} (a b : A) :
  Discrete a → Timeless (PROP:=PROP) (a ≡ b).
Proof. intros. rewrite /Discrete !discrete_eq. apply (timeless _). Qed.
End internal_eq_derived.
