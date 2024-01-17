From iris.algebra Require Export ofe.
From iris.bi Require Export notation.
From iris.prelude Require Import options.

(* We enable primitive projections in this file to improve the performance of the Iris proofmode:
    primitive projections for the bi-records makes the proofmode faster.
*)
Local Set Primitive Projections.

Section bi_mixin.
  Context {PROP : Type} `{!Dist PROP, !Equiv PROP}.
  Context (bi_entails : PROP → PROP → Prop).
  Context (bi_emp : PROP).
  Context (bi_pure : Prop → PROP).
  Context (bi_and : PROP → PROP → PROP).
  Context (bi_or : PROP → PROP → PROP).
  Context (bi_impl : PROP → PROP → PROP).
  Context (bi_forall : ∀ A, (A → PROP) → PROP).
  Context (bi_exist : ∀ A, (A → PROP) → PROP).
  Context (bi_sep : PROP → PROP → PROP).
  Context (bi_wand : PROP → PROP → PROP).

  Bind Scope bi_scope with PROP.
  Local Infix "⊢" := bi_entails.
  Local Notation "'emp'" := bi_emp : bi_scope.
  Local Notation "'True'" := (bi_pure True) : bi_scope.
  Local Notation "'False'" := (bi_pure False) : bi_scope.
  Local Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp) : bi_scope.
  Local Infix "∧" := bi_and : bi_scope.
  Local Infix "∨" := bi_or : bi_scope.
  Local Infix "→" := bi_impl : bi_scope.
  Local Notation "∀ x .. y , P" :=
    (bi_forall _ (λ x, .. (bi_forall _ (λ y, P%I)) ..)) : bi_scope.
  Local Notation "∃ x .. y , P" :=
    (bi_exist _ (λ x, .. (bi_exist _ (λ y, P%I)) ..)) : bi_scope.
  Local Infix "∗" := bi_sep : bi_scope.
  Local Infix "-∗" := bi_wand : bi_scope.

  (** * Axioms for a general BI (logic of bunched implications) *)

  (** The following axioms are satisifed by both affine and linear BIs, and BIs
  that combine both kinds of resources. In particular, we have an "ordered RA"
  model satisfying all these axioms. For this model, we extend RAs with an
  arbitrary partial order, and up-close resources wrt. that order (instead of
  extension order).  We demand composition to be monotone wrt. the order: [x1 ≼
  x2 → x1 ⋅ y ≼ x2 ⋅ y].  We define [emp := λ r, ε ≼ r]; persistently is still
  defined with the core: [persistently P := λ r, P (core r)].  This is uplcosed
  because the core is monotone.  *)

  Record BiMixin := {
    bi_mixin_entails_po : PreOrder bi_entails;
    bi_mixin_equiv_entails P Q : (P ≡ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P);

    (** Non-expansiveness *)
    bi_mixin_pure_ne n : Proper (iff ==> dist n) bi_pure;
    bi_mixin_and_ne : NonExpansive2 bi_and;
    bi_mixin_or_ne : NonExpansive2 bi_or;
    bi_mixin_impl_ne : NonExpansive2 bi_impl;
    bi_mixin_forall_ne A n :
      Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A);
    bi_mixin_exist_ne A n :
      Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A);
    bi_mixin_sep_ne : NonExpansive2 bi_sep;
    bi_mixin_wand_ne : NonExpansive2 bi_wand;

    (** Higher-order logic *)
    bi_mixin_pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝;
    bi_mixin_pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P;

    bi_mixin_and_elim_l P Q : P ∧ Q ⊢ P;
    bi_mixin_and_elim_r P Q : P ∧ Q ⊢ Q;
    bi_mixin_and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R;

    bi_mixin_or_intro_l P Q : P ⊢ P ∨ Q;
    bi_mixin_or_intro_r P Q : Q ⊢ P ∨ Q;
    bi_mixin_or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R;

    bi_mixin_impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R;
    bi_mixin_impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R;

    bi_mixin_forall_intro {A} P (Ψ : A → PROP) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a;
    bi_mixin_forall_elim {A} {Ψ : A → PROP} a : (∀ a, Ψ a) ⊢ Ψ a;

    bi_mixin_exist_intro {A} {Ψ : A → PROP} a : Ψ a ⊢ ∃ a, Ψ a;
    bi_mixin_exist_elim {A} (Φ : A → PROP) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q;

    (** BI connectives *)
    bi_mixin_sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q';
    bi_mixin_emp_sep_1 P : P ⊢ emp ∗ P;
    bi_mixin_emp_sep_2 P : emp ∗ P ⊢ P;
    bi_mixin_sep_comm' P Q : P ∗ Q ⊢ Q ∗ P;
    bi_mixin_sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R);
    bi_mixin_wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R;
    bi_mixin_wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R;
  }.

  (** We require any BI to have a persistence modality that carves out the
  intuitionistic fragment of the separation logic. For logics such as Iris,
  the persistence modality has a non-trivial definition (involving the [core] of
  the camera). It is not clear whether a trivial definition exists: while
  [<pers> P := False] comes close, it does not satisfy [later_persistently_1].
  
  However, for some simpler discrete BIs the persistence modality
  can be defined as:

    <pers> P := ⌜ emp ⊢ P ⌝

  That is, [P] holds persistently if it holds without resources.

  The nesting of the entailment below the pure embedding ⌜ ⌝ only works for
  discrete BIs: Non-expansiveness of [<pers>] relies on [dist] ignoring the
  step-index.

  To prove the rule [<pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> Ψ a] the BI furthermore
  needs to satisfy the "existential property": [emp ⊢ ∃ x, Φ x] implies
  [∃ x, emp ⊢ Φ x].

  This construction is formalized by the smart constructor
  [bi_persistently_mixin_discrete] for [BiPersistentlyMixin]. See
  [tests/heapprop] and [tests/heapprop_affine] for examples of how to use this
  smart constructor. *)

  Context (bi_persistently : PROP → PROP).
  Local Notation "'<pers>' P" := (bi_persistently P) : bi_scope.

  Record BiPersistentlyMixin := {
    bi_mixin_persistently_ne : NonExpansive bi_persistently;

    (* In the ordered RA model: Holds without further assumptions. *)
    bi_mixin_persistently_mono P Q : (P ⊢ Q) → <pers> P ⊢ <pers> Q;
    (* In the ordered RA model: `core` is idempotent *)
    bi_mixin_persistently_idemp_2 P : <pers> P ⊢ <pers> <pers> P;

    (* In the ordered RA model: [ε ≼ core x]. *)
    bi_mixin_persistently_emp_2 : emp ⊢ <pers> emp;

    (* The laws of a "frame" (https://ncatlab.org/nlab/show/frame, not to be
    confused with separation logic terminology): commuting with finite
    conjunction and infinite disjunction.
    The null-ary case, [persistently_True : True ⊢ <pers> True], is derivable from the
    other laws. *)
    bi_mixin_persistently_and_2 (P Q : PROP) :
      (<pers> P) ∧ (<pers> Q) ⊢ <pers> (P ∧ Q);
    bi_mixin_persistently_exist_1 {A} (Ψ : A → PROP) :
      <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a);

    (* In the ordered RA model: [core x ≼ core (x ⋅ y)]. *)
    bi_mixin_persistently_absorbing P Q : <pers> P ∗ Q ⊢ <pers> P;
    (* In the ordered RA model: [x ⋅ core x = x]. *)
    bi_mixin_persistently_and_sep_elim P Q : <pers> P ∧ Q ⊢ P ∗ Q;
  }.

  Lemma bi_persistently_mixin_discrete :
    (∀ n (P Q : PROP), P ≡{n}≡ Q → P ≡ Q) →
    (∀ {A} (Φ : A → PROP), (emp ⊢ ∃ x, Φ x) → ∃ x, emp ⊢ Φ x) →
    (∀ P : PROP, (<pers> P)%I = ⌜ emp ⊢ P ⌝%I) →
    BiMixin →
    BiPersistentlyMixin.
  Proof.
    intros Hdiscrete Hex Hpers Hbi. pose proof (bi_mixin_entails_po Hbi).
    split.
    - (* [NonExpansive bi_persistently] *)
      intros n P Q [HPQ HQP]%Hdiscrete%(bi_mixin_equiv_entails Hbi).
      rewrite !Hpers. apply (bi_mixin_pure_ne Hbi). split=> ?; by etrans.
    - (*[(P ⊢ Q) → <pers> P ⊢ <pers> Q] *)
      intros P Q HPQ. rewrite !Hpers. apply (bi_mixin_pure_elim' Hbi)=> ?.
      apply (bi_mixin_pure_intro Hbi). by trans P.
    - (* [<pers> P ⊢ <pers> <pers> P] *)
      intros P. rewrite !Hpers. apply (bi_mixin_pure_elim' Hbi)=> ?.
      by do 2 apply (bi_mixin_pure_intro Hbi).
    - (* [emp ⊢ <pers> emp] *)
      rewrite Hpers. by apply (bi_mixin_pure_intro Hbi).
    - (* [<pers> P ∧ <pers> Q ⊢ <pers> (P ∧ Q)] *)
      intros P Q. rewrite !Hpers.
      apply (bi_mixin_impl_elim_l' Hbi). apply (bi_mixin_pure_elim' Hbi)=> ?.
      apply (bi_mixin_impl_intro_r Hbi).
      etrans; [apply (bi_mixin_and_elim_r Hbi)|].
      apply (bi_mixin_pure_elim' Hbi)=> ?.
      apply (bi_mixin_pure_intro Hbi). by apply (bi_mixin_and_intro Hbi).
    - (* [<pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> Ψ a] *)
      intros A Φ. rewrite !Hpers. apply (bi_mixin_pure_elim' Hbi)=> /Hex [x ?].
      etrans; [|apply (bi_mixin_exist_intro Hbi x)]; simpl.
      rewrite Hpers. by apply (bi_mixin_pure_intro Hbi).
    - (* [<pers> P ∗ Q ⊢ <pers> P] *)
      intros P Q. rewrite !Hpers.
      apply (bi_mixin_wand_elim_l' Hbi). apply (bi_mixin_pure_elim' Hbi)=> ?.
      apply (bi_mixin_wand_intro_r Hbi). by apply (bi_mixin_pure_intro Hbi).
    - (* [<pers> P ∧ Q ⊢ P ∗ Q] *)
      intros P Q. rewrite !Hpers.
      apply (bi_mixin_impl_elim_l' Hbi). apply (bi_mixin_pure_elim' Hbi)=> ?.
      apply (bi_mixin_impl_intro_r Hbi).
      etrans; [apply (bi_mixin_and_elim_r Hbi)|].
      etrans; [apply (bi_mixin_emp_sep_1 Hbi)|].
      by apply (bi_mixin_sep_mono Hbi).
  Qed.

  (** We equip any BI with a later modality. This avoids an additional layer in
  the BI hierachy and improves performance significantly (see Iris issue #303).

  For non step-indexed BIs the later modality can simply be defined as the
  identity function, as the Löb axiom or contractiveness of later is not part of
  [BiLaterMixin]. For step-indexed BIs one should separately prove an instance
  of the class [BiLaterContractive PROP] or [BiLöb PROP]. (Note that there is an
  instance [BiLaterContractive PROP → BiLöb PROP] in [derived_laws_later].)

  For non step-indexed BIs one can get a "free" instance of [BiLaterMixin] using
  the smart constructor [bi_later_mixin_id] below. *)
  Context (bi_later : PROP → PROP).
  Local Notation "▷ P" := (bi_later P) : bi_scope.

  Record BiLaterMixin := {
    bi_mixin_later_ne : NonExpansive bi_later;

    bi_mixin_later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q;
    bi_mixin_later_intro P : P ⊢ ▷ P;

    bi_mixin_later_forall_2 {A} (Φ : A → PROP) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a;
    bi_mixin_later_exist_false {A} (Φ : A → PROP) :
      (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a);
    bi_mixin_later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q;
    bi_mixin_later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q);
    bi_mixin_later_persistently_1 P : ▷ <pers> P ⊢ <pers> ▷ P;
    bi_mixin_later_persistently_2 P : <pers> ▷ P ⊢ ▷ <pers> P;

    bi_mixin_later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P);
  }.

  Lemma bi_later_mixin_id :
    (∀ (P : PROP), (▷ P)%I = P) →
    BiMixin → BiLaterMixin.
  Proof.
    intros Hlater Hbi. pose proof (bi_mixin_entails_po Hbi).
    split; repeat intro; rewrite ?Hlater //.
    - apply (bi_mixin_forall_intro Hbi)=> a.
      etrans; [apply (bi_mixin_forall_elim Hbi a)|]. by rewrite Hlater.
    - etrans; [|apply (bi_mixin_or_intro_r Hbi)].
      apply (bi_mixin_exist_elim Hbi)=> a.
      etrans; [|apply (bi_mixin_exist_intro Hbi a)]. by rewrite /= Hlater.
    - etrans; [|apply (bi_mixin_or_intro_r Hbi)].
      apply (bi_mixin_impl_intro_r Hbi), (bi_mixin_and_elim_l Hbi).
  Qed.
End bi_mixin.

Module Import universes.
  (** The universe of the logic (PROP). *)
  Universe Logic.
  (** The universe of quantifiers in the logic. *)
  Universe Quant.
End universes.

Structure bi := Bi {
  bi_car :> Type@{Logic};
  bi_dist : Dist bi_car;
  bi_equiv : Equiv bi_car;
  bi_entails : bi_car → bi_car → Prop;
  bi_emp : bi_car;
  bi_pure : Prop → bi_car;
  bi_and : bi_car → bi_car → bi_car;
  bi_or : bi_car → bi_car → bi_car;
  bi_impl : bi_car → bi_car → bi_car;
  bi_forall : ∀ A : Type@{Quant}, (A → bi_car) → bi_car;
  bi_exist : ∀ A : Type@{Quant}, (A → bi_car) → bi_car;
  bi_sep : bi_car → bi_car → bi_car;
  bi_wand : bi_car → bi_car → bi_car;
  bi_persistently : bi_car → bi_car;
  bi_later : bi_car → bi_car;
  bi_ofe_mixin : OfeMixin bi_car;
  bi_cofe_aux : Cofe (Ofe bi_car bi_ofe_mixin);
  bi_bi_mixin : BiMixin bi_entails bi_emp bi_pure bi_and bi_or bi_impl bi_forall
                        bi_exist bi_sep bi_wand;
  bi_bi_persistently_mixin :
    BiPersistentlyMixin bi_entails bi_emp bi_and bi_exist bi_sep bi_persistently;
  bi_bi_later_mixin : BiLaterMixin bi_entails bi_pure bi_or bi_impl
                                   bi_forall bi_exist bi_sep bi_persistently bi_later;
}.
Bind Scope bi_scope with bi_car.

Coercion bi_ofeO (PROP : bi) : ofe := Ofe PROP (bi_ofe_mixin PROP).
Canonical Structure bi_ofeO.

(** The projection [bi_cofe_aux] is not registered as an instance because it has
the wrong type. Its result type is unfolded, i.e., [Cofe (Ofe PROP ...)], and
thus should never be used. The instance [bi_cofe] has the proper result type
[Cofe (bi_ofeO PROP)]. *)
Global Instance bi_cofe (PROP : bi) : Cofe PROP := bi_cofe_aux PROP.

Global Instance: Params (@bi_entails) 1 := {}.
Global Instance: Params (@bi_emp) 1 := {}.
Global Instance: Params (@bi_pure) 1 := {}.
Global Instance: Params (@bi_and) 1 := {}.
Global Instance: Params (@bi_or) 1 := {}.
Global Instance: Params (@bi_impl) 1 := {}.
Global Instance: Params (@bi_forall) 2 := {}.
Global Instance: Params (@bi_exist) 2 := {}.
Global Instance: Params (@bi_sep) 1 := {}.
Global Instance: Params (@bi_wand) 1 := {}.
Global Instance: Params (@bi_persistently) 1 := {}.
Global Instance: Params (@bi_later) 1  := {}.

Global Arguments bi_car : simpl never.
Global Arguments bi_dist : simpl never.
Global Arguments bi_equiv : simpl never.
Global Arguments bi_entails {PROP} _ _ : simpl never, rename.
Global Arguments bi_emp {PROP} : simpl never, rename.
Global Arguments bi_pure {PROP} _%stdpp : simpl never, rename.
Global Arguments bi_and {PROP} _ _ : simpl never, rename.
Global Arguments bi_or {PROP} _ _ : simpl never, rename.
Global Arguments bi_impl {PROP} _ _ : simpl never, rename.
Global Arguments bi_forall {PROP _} _%I : simpl never, rename.
Global Arguments bi_exist {PROP _} _%I : simpl never, rename.
Global Arguments bi_sep {PROP} _ _ : simpl never, rename.
Global Arguments bi_wand {PROP} _ _ : simpl never, rename.
Global Arguments bi_persistently {PROP} _ : simpl never, rename.
Global Arguments bi_later {PROP} _ : simpl never, rename.

Global Hint Extern 0 (bi_entails _ _) => reflexivity : core.
(** We set this rewrite relation's cost above the stdlib's
  ([impl], [iff], [eq], ...) and [≡] but below [⊑].
  [eq] (at 100) < [≡] (at 150) < [bi_entails _] (at 170) < [⊑] (at 200)
*)
Global Instance bi_rewrite_relation (PROP : bi) : RewriteRelation (@bi_entails PROP) | 170 := {}.
Global Instance bi_inhabited {PROP : bi} : Inhabited PROP := populate (bi_pure True).

Notation "'emp'" := (bi_emp) : bi_scope.
Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp) : bi_scope.
Notation "'True'" := (bi_pure True) : bi_scope.
Notation "'False'" := (bi_pure False) : bi_scope.
Infix "∧" := bi_and : bi_scope.
Notation "(∧)" := bi_and (only parsing) : bi_scope.
Infix "∨" := bi_or : bi_scope.
Notation "(∨)" := bi_or (only parsing) : bi_scope.
Infix "→" := bi_impl : bi_scope.
Notation "¬ P" := (P → False)%I : bi_scope.
Infix "∗" := bi_sep : bi_scope.
Notation "(∗)" := bi_sep (only parsing) : bi_scope.
Notation "P -∗ Q" := (bi_wand P Q) : bi_scope.
Notation "∀ x .. y , P" :=
  (bi_forall (λ x, .. (bi_forall (λ y, P%I)) ..)) : bi_scope.
Notation "∃ x .. y , P" :=
  (bi_exist (λ x, .. (bi_exist (λ y, P%I)) ..)) : bi_scope.
Notation "'<pers>' P" := (bi_persistently P) : bi_scope.

Notation "▷ P" := (bi_later P) : bi_scope.

Notation "P ⊢ Q" := (bi_entails P%I Q%I) : stdpp_scope.
Notation "P '⊢@{' PROP } Q" := (bi_entails (PROP:=PROP) P%I Q%I) (only parsing) : stdpp_scope.
Notation "(⊢)" := bi_entails (only parsing) : stdpp_scope.
Notation "'(⊢@{' PROP } )" := (bi_entails (PROP:=PROP)) (only parsing) : stdpp_scope.

Notation "P ⊣⊢ Q" := (equiv (A:=bi_car _) P%I Q%I) : stdpp_scope.
Notation "P '⊣⊢@{' PROP } Q" := (equiv (A:=bi_car PROP) P%I Q%I) (only parsing) : stdpp_scope.
Notation "(⊣⊢)" := (equiv (A:=bi_car _)) (only parsing) : stdpp_scope.
Notation "'(⊣⊢@{' PROP } )" := (equiv (A:=bi_car PROP)) (only parsing) : stdpp_scope.
Notation "( P ⊣⊢.)" := (equiv (A:=bi_car _) P) (only parsing) : stdpp_scope.
Notation "(.⊣⊢ Q )" := (λ P, P ≡@{bi_car _} Q) (only parsing) : stdpp_scope.

Definition bi_emp_valid {PROP : bi} (P : PROP) : Prop := emp ⊢ P.

Global Arguments bi_emp_valid {_} _%I : simpl never.
Global Typeclasses Opaque bi_emp_valid.

Notation "⊢ Q" := (bi_emp_valid Q%I) : stdpp_scope.
Notation "'⊢@{' PROP } Q" := (bi_emp_valid (PROP:=PROP) Q%I) (only parsing) : stdpp_scope.
(** Work around parsing issues: see [notation.v] for details. *)
Notation "'(⊢@{' PROP } Q )" := (bi_emp_valid (PROP:=PROP) Q%I) (only parsing) : stdpp_scope.
Notation "(.⊢ Q )" := (λ P, P ⊢ Q) (only parsing) : stdpp_scope.
Notation "( P ⊢.)" := (bi_entails P) (only parsing) : stdpp_scope.

Notation "P -∗ Q" := (⊢ P -∗ Q) : stdpp_scope.

Module bi.
Section bi_laws.
Context {PROP : bi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types A : Type.

(* About the entailment *)
Global Instance entails_po : PreOrder (@bi_entails PROP).
Proof. eapply bi_mixin_entails_po, bi_bi_mixin. Qed.
Lemma equiv_entails P Q : P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof. eapply bi_mixin_equiv_entails, bi_bi_mixin. Qed.

(* Non-expansiveness *)
Global Instance pure_ne n : Proper (iff ==> dist n) (@bi_pure PROP).
Proof. eapply bi_mixin_pure_ne, bi_bi_mixin. Qed.
Global Instance and_ne : NonExpansive2 (@bi_and PROP).
Proof. eapply bi_mixin_and_ne, bi_bi_mixin. Qed.
Global Instance or_ne : NonExpansive2 (@bi_or PROP).
Proof. eapply bi_mixin_or_ne, bi_bi_mixin. Qed.
Global Instance impl_ne : NonExpansive2 (@bi_impl PROP).
Proof. eapply bi_mixin_impl_ne, bi_bi_mixin. Qed.
Global Instance forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_forall PROP A).
Proof. eapply bi_mixin_forall_ne, bi_bi_mixin. Qed.
Global Instance exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_exist PROP A).
Proof. eapply bi_mixin_exist_ne, bi_bi_mixin. Qed.
Global Instance sep_ne : NonExpansive2 (@bi_sep PROP).
Proof. eapply bi_mixin_sep_ne, bi_bi_mixin. Qed.
Global Instance wand_ne : NonExpansive2 (@bi_wand PROP).
Proof. eapply bi_mixin_wand_ne, bi_bi_mixin. Qed.
Global Instance persistently_ne : NonExpansive (@bi_persistently PROP).
Proof. eapply bi_mixin_persistently_ne, bi_bi_persistently_mixin. Qed.

(* Higher-order logic *)
Lemma pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝.
Proof. eapply bi_mixin_pure_intro, bi_bi_mixin. Qed.
Lemma pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P.
Proof. eapply bi_mixin_pure_elim', bi_bi_mixin. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. eapply bi_mixin_and_elim_l, bi_bi_mixin. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. eapply bi_mixin_and_elim_r, bi_bi_mixin. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. eapply bi_mixin_and_intro, bi_bi_mixin. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. eapply bi_mixin_or_intro_l, bi_bi_mixin. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. eapply bi_mixin_or_intro_r, bi_bi_mixin. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof. eapply bi_mixin_or_elim, bi_bi_mixin. Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof. eapply bi_mixin_impl_intro_r, bi_bi_mixin. Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. eapply bi_mixin_impl_elim_l', bi_bi_mixin. Qed.

Lemma forall_intro {A} P (Ψ : A → PROP) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. eapply bi_mixin_forall_intro, bi_bi_mixin. Qed.
Lemma forall_elim {A} {Ψ : A → PROP} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. eapply (bi_mixin_forall_elim bi_entails), bi_bi_mixin. Qed.

Lemma exist_intro {A} {Ψ : A → PROP} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. eapply bi_mixin_exist_intro, bi_bi_mixin. Qed.
Lemma exist_elim {A} (Φ : A → PROP) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. eapply bi_mixin_exist_elim, bi_bi_mixin. Qed.

(* BI connectives *)
Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
Proof. eapply bi_mixin_sep_mono, bi_bi_mixin. Qed.
Lemma emp_sep_1 P : P ⊢ emp ∗ P.
Proof. eapply bi_mixin_emp_sep_1, bi_bi_mixin. Qed.
Lemma emp_sep_2 P : emp ∗ P ⊢ P.
Proof. eapply bi_mixin_emp_sep_2, bi_bi_mixin. Qed.
Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
Proof. eapply (bi_mixin_sep_comm' bi_entails), bi_bi_mixin. Qed.
Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
Proof. eapply bi_mixin_sep_assoc', bi_bi_mixin. Qed.
Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
Proof. eapply bi_mixin_wand_intro_r, bi_bi_mixin. Qed.
Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
Proof. eapply bi_mixin_wand_elim_l', bi_bi_mixin. Qed.

(* Persistently *)
Lemma persistently_mono P Q : (P ⊢ Q) → <pers> P ⊢ <pers> Q.
Proof. eapply bi_mixin_persistently_mono, bi_bi_persistently_mixin. Qed.
Lemma persistently_idemp_2 P : <pers> P ⊢ <pers> <pers> P.
Proof. eapply bi_mixin_persistently_idemp_2, bi_bi_persistently_mixin. Qed.

Lemma persistently_emp_2 : emp ⊢@{PROP} <pers> emp.
Proof. eapply bi_mixin_persistently_emp_2, bi_bi_persistently_mixin. Qed.

Lemma persistently_and_2 (P Q : PROP) :
  ((<pers> P) ∧ (<pers> Q)) ⊢ <pers> (P ∧ Q).
Proof. eapply bi_mixin_persistently_and_2, bi_bi_persistently_mixin. Qed.
Lemma persistently_exist_1 {A} (Ψ : A → PROP) :
  <pers> (∃ a, Ψ a) ⊢ ∃ a, <pers> (Ψ a).
Proof. eapply bi_mixin_persistently_exist_1, bi_bi_persistently_mixin. Qed.

Lemma persistently_absorbing P Q : <pers> P ∗ Q ⊢ <pers> P.
Proof.
  eapply (bi_mixin_persistently_absorbing bi_entails), bi_bi_persistently_mixin.
Qed.
Lemma persistently_and_sep_elim P Q : <pers> P ∧ Q ⊢ P ∗ Q.
Proof.
  eapply (bi_mixin_persistently_and_sep_elim bi_entails), bi_bi_persistently_mixin.
Qed.

(* Later *)
Global Instance later_ne : NonExpansive (@bi_later PROP).
Proof. eapply bi_mixin_later_ne, bi_bi_later_mixin. Qed.

Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
Proof. eapply bi_mixin_later_mono, bi_bi_later_mixin. Qed.
Lemma later_intro P : P ⊢ ▷ P.
Proof. eapply bi_mixin_later_intro, bi_bi_later_mixin. Qed.

Lemma later_forall_2 {A} (Φ : A → PROP) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
Proof. eapply bi_mixin_later_forall_2, bi_bi_later_mixin. Qed.
Lemma later_exist_false {A} (Φ : A → PROP) :
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof. eapply bi_mixin_later_exist_false, bi_bi_later_mixin. Qed.
Lemma later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
Proof. eapply bi_mixin_later_sep_1, bi_bi_later_mixin. Qed.
Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
Proof. eapply bi_mixin_later_sep_2, bi_bi_later_mixin. Qed.
Lemma later_persistently_1 P : ▷ <pers> P ⊢ <pers> ▷ P.
Proof. eapply (bi_mixin_later_persistently_1 bi_entails), bi_bi_later_mixin. Qed.
Lemma later_persistently_2 P : <pers> ▷ P ⊢ ▷ <pers> P.
Proof. eapply (bi_mixin_later_persistently_2 bi_entails), bi_bi_later_mixin. Qed.

Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
Proof. eapply bi_mixin_later_false_em, bi_bi_later_mixin. Qed.
End bi_laws.
End bi.
