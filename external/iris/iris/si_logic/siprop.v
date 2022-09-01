From iris.algebra Require Export ofe.
From iris.bi Require Import notation.
From iris.prelude Require Import options.

(** The type [siProp] defines "plain" step-indexed propositions, on which we
define the usual connectives of higher-order logic, and prove that these satisfy
the usual laws of higher-order logic. *)
Record siProp := SiProp {
  siProp_holds : nat → Prop;
  siProp_closed n1 n2 : siProp_holds n1 → n2 ≤ n1 → siProp_holds n2
}.
Local Coercion siProp_holds : siProp >-> Funclass.
Global Arguments siProp_holds : simpl never.
Add Printing Constructor siProp.

Declare Scope siProp_scope.
Delimit Scope siProp_scope with SI.
Bind Scope siProp_scope with siProp.

Section cofe.
  Inductive siProp_equiv' (P Q : siProp) : Prop :=
    { siProp_in_equiv : ∀ n, P n ↔ Q n }.
  Local Instance siProp_equiv : Equiv siProp := siProp_equiv'.
  Inductive siProp_dist' (n : nat) (P Q : siProp) : Prop :=
    { siProp_in_dist : ∀ n', n' ≤ n → P n' ↔ Q n' }.
  Local Instance siProp_dist : Dist siProp := siProp_dist'.
  Definition siProp_ofe_mixin : OfeMixin siProp.
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i ?; apply HPQ.
      + intros HPQ; split=> n; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> i.
      + by intros P Q HPQ; split=> i ?; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i ?.
        by trans (Q i);[apply HP|apply HQ].
    - intros n P Q HPQ; split=> i ?; apply HPQ; auto.
  Qed.
  Canonical Structure siPropO : ofe := Ofe siProp siProp_ofe_mixin.

  Program Definition siProp_compl : Compl siPropO := λ c,
    {| siProp_holds n := c n n |}.
  Next Obligation.
    intros c n1 n2 ??; simpl in *.
    apply (chain_cauchy c n2 n1); eauto using siProp_closed.
  Qed.
  Global Program Instance siProp_cofe : Cofe siPropO := {| compl := siProp_compl |}.
  Next Obligation.
    intros n c; split=>i ?; symmetry; apply (chain_cauchy c i n); auto.
  Qed.
End cofe.

(** logical entailement *)
Inductive siProp_entails (P Q : siProp) : Prop :=
  { siProp_in_entails : ∀ n, P n → Q n }.
Global Hint Resolve siProp_closed : siProp_def.

(** logical connectives *)
Program Definition siProp_pure_def (φ : Prop) : siProp :=
  {| siProp_holds n := φ |}.
Solve Obligations with done.
Definition siProp_pure_aux : seal (@siProp_pure_def). Proof. by eexists. Qed.
Definition siProp_pure := unseal siProp_pure_aux.
Definition siProp_pure_eq :
  @siProp_pure = @siProp_pure_def := seal_eq siProp_pure_aux.

Program Definition siProp_and_def (P Q : siProp) : siProp :=
  {| siProp_holds n := P n ∧ Q n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Definition siProp_and_aux : seal (@siProp_and_def). Proof. by eexists. Qed.
Definition siProp_and := unseal siProp_and_aux.
Definition siProp_and_eq: @siProp_and = @siProp_and_def := seal_eq siProp_and_aux.

Program Definition siProp_or_def (P Q : siProp) : siProp :=
  {| siProp_holds n := P n ∨ Q n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Definition siProp_or_aux : seal (@siProp_or_def). Proof. by eexists. Qed.
Definition siProp_or := unseal siProp_or_aux.
Definition siProp_or_eq: @siProp_or = @siProp_or_def := seal_eq siProp_or_aux.

Program Definition siProp_impl_def (P Q : siProp) : siProp :=
  {| siProp_holds n := ∀ n', n' ≤ n → P n' → Q n' |}.
Next Obligation. intros P Q [|n1] [|n2]; auto with lia. Qed.
Definition siProp_impl_aux : seal (@siProp_impl_def). Proof. by eexists. Qed.
Definition siProp_impl := unseal siProp_impl_aux.
Definition siProp_impl_eq :
  @siProp_impl = @siProp_impl_def := seal_eq siProp_impl_aux.

Program Definition siProp_forall_def {A} (Ψ : A → siProp) : siProp :=
  {| siProp_holds n := ∀ a, Ψ a n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Definition siProp_forall_aux : seal (@siProp_forall_def). Proof. by eexists. Qed.
Definition siProp_forall {A} := unseal siProp_forall_aux A.
Definition siProp_forall_eq :
  @siProp_forall = @siProp_forall_def := seal_eq siProp_forall_aux.

Program Definition siProp_exist_def {A} (Ψ : A → siProp) : siProp :=
  {| siProp_holds n := ∃ a, Ψ a n |}.
Solve Obligations with naive_solver eauto 2 with siProp_def.
Definition siProp_exist_aux : seal (@siProp_exist_def). Proof. by eexists. Qed.
Definition siProp_exist {A} := unseal siProp_exist_aux A.
Definition siProp_exist_eq: @siProp_exist = @siProp_exist_def := seal_eq siProp_exist_aux.

Program Definition siProp_internal_eq_def {A : ofe} (a1 a2 : A) : siProp :=
  {| siProp_holds n := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using dist_le.
Definition siProp_internal_eq_aux : seal (@siProp_internal_eq_def). Proof. by eexists. Qed.
Definition siProp_internal_eq {A} := unseal siProp_internal_eq_aux A.
Definition siProp_internal_eq_eq:
  @siProp_internal_eq = @siProp_internal_eq_def := seal_eq siProp_internal_eq_aux.

Program Definition siProp_later_def (P : siProp) : siProp :=
  {| siProp_holds n := match n return _ with 0 => True | S n' => P n' end |}.
Next Obligation. intros P [|n1] [|n2]; eauto using siProp_closed with lia. Qed.
Definition siProp_later_aux : seal (@siProp_later_def). Proof. by eexists. Qed.
Definition siProp_later := unseal siProp_later_aux.
Definition siProp_later_eq :
  @siProp_later = @siProp_later_def := seal_eq siProp_later_aux.

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module siProp_primitive.
Definition unseal_eqs :=
  (siProp_pure_eq, siProp_and_eq, siProp_or_eq, siProp_impl_eq, siProp_forall_eq,
  siProp_exist_eq, siProp_internal_eq_eq, siProp_later_eq).
Ltac unseal := rewrite !unseal_eqs /=.

Section primitive.
Local Arguments siProp_holds !_ _ /.

Notation "P ⊢ Q" := (siProp_entails P Q)
  (at level 99, Q at level 200, right associativity).
Notation "'True'" := (siProp_pure True) : siProp_scope.
Notation "'False'" := (siProp_pure False) : siProp_scope.
Notation "'⌜' φ '⌝'" := (siProp_pure φ%type%stdpp) : siProp_scope.
Infix "∧" := siProp_and : siProp_scope.
Infix "∨" := siProp_or : siProp_scope.
Infix "→" := siProp_impl : siProp_scope.
Notation "∀ x .. y , P" := (siProp_forall (λ x, .. (siProp_forall (λ y, P%SI)) ..)) : siProp_scope.
Notation "∃ x .. y , P" := (siProp_exist (λ x, .. (siProp_exist (λ y, P%SI)) ..)) : siProp_scope.
Notation "x ≡ y" := (siProp_internal_eq x y) : siProp_scope.
Notation "▷ P" := (siProp_later P) (at level 20, right associativity) : siProp_scope.

(** Below there follow the primitive laws for [siProp]. There are no derived laws
in this file. *)

(** Entailment *)
Lemma entails_po : PreOrder siProp_entails.
Proof.
  split.
  - intros P; by split=> i.
  - intros P Q Q' HP HQ; split=> i ?; by apply HQ, HP.
Qed.
Lemma entails_anti_symm : AntiSymm (≡) siProp_entails.
Proof. intros P Q HPQ HQP; split=> n; by split; [apply HPQ|apply HQP]. Qed.
Lemma equiv_entails P Q : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split.
  - intros HPQ; split; split=> i; apply HPQ.
  - intros [??]. by apply entails_anti_symm.
Qed.

(** Non-expansiveness and setoid morphisms *)
Lemma pure_ne n : Proper (iff ==> dist n) siProp_pure.
Proof. intros φ1 φ2 Hφ. by unseal. Qed.
Lemma and_ne : NonExpansive2 siProp_and.
Proof.
  intros n P P' HP Q Q' HQ; unseal; split=> n' ?.
  split; (intros [??]; split; [by apply HP|by apply HQ]).
Qed.
Lemma or_ne : NonExpansive2 siProp_or.
Proof.
  intros n P P' HP Q Q' HQ; split=> n' ?.
  unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
Qed.
Lemma impl_ne : NonExpansive2 siProp_impl.
Proof.
  intros n P P' HP Q Q' HQ; split=> n' ?.
  unseal; split; intros HPQ n'' ??; apply HQ, HPQ, HP; auto with lia.
Qed.
Lemma forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@siProp_forall A).
Proof.
   by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
Qed.
Lemma exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@siProp_exist A).
Proof.
  intros Ψ1 Ψ2 HΨ.
  unseal; split=> n' ?; split; intros [a ?]; exists a; by apply HΨ.
Qed.
Lemma later_contractive : Contractive siProp_later.
Proof.
  unseal; intros [|n] P Q HPQ; split=> -[|n'] ? //=; try lia.
  apply HPQ; lia.
Qed.
Lemma internal_eq_ne (A : ofe) : NonExpansive2 (@siProp_internal_eq A).
Proof.
  intros n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
  - by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
  - by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
Qed.

(** Introduction and elimination rules *)
Lemma pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝.
Proof. intros ?. unseal; by split. Qed.
Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
Proof. unseal=> HP; split=> n ?. by apply HP. Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ a, ⌜ φ a ⌝) ⊢ ⌜ ∀ a, φ a ⌝.
Proof. by unseal. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. unseal; by split=> n [??]. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. unseal; by split=> n [??]. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof.
  intros HQ HR; unseal; split=> n ?.
  split.
  - by apply HQ.
  - by apply HR.
Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. unseal; split=> n ?; left; auto. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. unseal; split=> n ?; right; auto. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof.
  intros HP HQ. unseal; split=> n [?|?].
  - by apply HP.
  - by apply HQ.
Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof.
  unseal=> HQ; split=> n ? n' ??.
  apply HQ; naive_solver eauto using siProp_closed.
Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. unseal=> HP; split=> n [??]. apply HP with n; auto. Qed.

Lemma forall_intro {A} P (Ψ : A → siProp) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. unseal; intros HPΨ; split=> n ? a; by apply HPΨ. Qed.
Lemma forall_elim {A} {Ψ : A → siProp} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. unseal; split=> n HP; apply HP. Qed.

Lemma exist_intro {A} {Ψ : A → siProp} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. unseal; split=> n ?; by exists a. Qed.
Lemma exist_elim {A} (Φ : A → siProp) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. unseal; intros HΨ; split=> n [a ?]; by apply HΨ with a. Qed.

(** Equality *)
Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ (a ≡ a).
Proof. unseal; by split=> n ? /=. Qed.
Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → siProp) :
  NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
Proof.
  intros Hnonexp. unseal; split=> n Hab n' ? HΨ. eapply Hnonexp with n a; auto.
Qed.

Lemma fun_ext {A} {B : A → ofe} (f g : discrete_fun B) : (∀ x, f x ≡ g x) ⊢ f ≡ g.
Proof. by unseal. Qed.
Lemma sig_eq {A : ofe} (P : A → Prop) (x y : sig P) : `x ≡ `y ⊢ x ≡ y.
Proof. by unseal. Qed.
Lemma discrete_eq_1 {A : ofe} (a b : A) : Discrete a → a ≡ b ⊢ ⌜a ≡ b⌝.
Proof. unseal=> ?. split=> n. by apply (discrete_iff n). Qed.

Lemma prop_ext_2 P Q : ((P → Q) ∧ (Q → P)) ⊢ P ≡ Q.
Proof.
  unseal; split=> n /= HPQ. split=> n' ?.
  move: HPQ=> [] /(_ n') ? /(_ n'). naive_solver.
Qed.

(** Later *)
Lemma later_eq_1 {A : ofe} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y).
Proof. by unseal. Qed.
Lemma later_eq_2 {A : ofe} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y.
Proof. by unseal. Qed.

Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
Proof. unseal=> HP; split=>-[|n]; [done|apply HP; eauto using cmra_validN_S]. Qed.
Lemma later_intro P : P ⊢ ▷ P.
Proof. unseal; split=> -[|n] /= HP; eauto using siProp_closed. Qed.

Lemma later_forall_2 {A} (Φ : A → siProp) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
Proof. unseal; by split=> -[|n]. Qed.
Lemma later_exist_false {A} (Φ : A → siProp) :
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof. unseal; split=> -[|[|n]] /=; eauto. Qed.
Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
Proof.
  unseal; split=> -[|n] /= HP; [by left|right].
  intros [|n'] ?; eauto using siProp_closed with lia.
Qed.

(** Consistency/soundness statement *)
Lemma pure_soundness φ : (True ⊢ ⌜ φ ⌝) → φ.
Proof. unseal=> -[H]. by apply (H 0). Qed.

Lemma internal_eq_soundness {A : ofe} (x y : A) : (True ⊢ x ≡ y) → x ≡ y.
Proof. unseal=> -[H]. apply equiv_dist=> n. by apply (H n). Qed.

Lemma later_soundness P : (True ⊢ ▷ P) → (True ⊢ P).
Proof.
  unseal=> -[HP]; split=> n _. apply siProp_closed with n; last done.
  by apply (HP (S n)).
Qed.
End primitive.
End siProp_primitive.
