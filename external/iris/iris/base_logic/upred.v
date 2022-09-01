From stdpp Require Import finite.
From iris.algebra Require Export cmra updates.
From iris.bi Require Import notation.
From iris.prelude Require Import options.

Local Hint Extern 1 (_ ≼ _) => etrans; [eassumption|] : core.
Local Hint Extern 1 (_ ≼ _) => etrans; [|eassumption] : core.
Local Hint Extern 10 (_ ≤ _) => lia : core.

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(** A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the sProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *sProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in sProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   sProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

(** Note that, somewhat curiously, [uPred M] is *not* in general a Camera,
   at least not if all propositions are considered "valid" Camera elements.
   It fails to satisfy the extension axiom. Here is the counterexample:

We use [M := (option Ex {A,B})^2] -- so we have pairs
whose components are ε, A or B.

Let
[[
  P r n := (ownM (A,A) ∧ ▷ False) ∨ ownM (A,B) ∨ ownM (B,A) ∨ ownM (B,B)
         ↔ r = (A,A) ∧ n = 0 ∨
           r = (A,B) ∨
           r = (B,A) ∨
           r = (B,B)
 Q1 r n := ownM (A, ε) ∨ ownM (B, ε)
         ↔ (A, ε) ≼ r ∨ (B, ε) ≼ r
           ("Left component is not ε")
 Q2 r n := ownM (ε, A) ∨ ownM (ε, B)
         ↔ (ε, A) ≼ r ∨ (ε, B) ≼ r
           ("Right component is not ε")
]]
These are all sufficiently closed and non-expansive and whatnot.
We have [P ≡{0}≡ Q1 * Q2]. So assume extension holds, then we get Q1', Q2'
such that
[[
  P ≡ Q1' ∗ Q2'
 Q1 ≡{0}≡ Q1'
 Q2 ≡{0}≡ Q2'
]]
Now comes the contradiction:
We know that [P (A,A) 1] does *not* hold, but I am going to show that
[(Q1' ∗ Q2') (A,A) 1] holds, which would be a contraction.
To this end, I will show (a) [Q1' (A,ε) 1] and (b) [Q2' (ε,A) 1].
The result [(Q1' ∗ Q2') (A,A)] follows from [(A,ε) ⋅ (ε,A) = (A,A)].

(a) Proof of [Q1' (A,ε) 1].
    We have [P (A,B) 1], and thus [Q1' r1 1] and [Q2' r2 1] for some
    [r1 ⋅ r2 = (A,B)]. There are four possible decompositions [r1 ⋅ r2]:
    - [(ε,ε) ⋅ (A,B)]: This would give us [Q1' (ε,ε) 1], from which we
      obtain (through down-closure and the equality [Q1 ≡{0}≡ Q1'] above) that
      [Q1 (ε,ε) 0]. However, we know that's false.
    - [(A,B) ⋅ (ε,ε)]: Can be excluded for similar reasons
      (the second resource must not be ε in the 2nd component).
    - [(ε,B) ⋅ (A,ε)]: Can be excluded for similar reasons
      (the first resource must not be ε in the 1st component).
    - [(A,ε) ⋅ (ε,B)]: This gives us the desired [Q1' (A,ε) 1].

(b) Proof of [Q2' (ε,A) 1].
    We have [P (B,A) 1], and thus [Q1' r1 1] and [Q2' r2 1] for some
    [r1 ⋅ r2 = (B,A)]. There are again four possible decompositions,
    and like above we can exclude three of them. This leaves us with
    [(B,ε) ⋅ (ε,A)] and thus [Q2' (ε,A) 1].

This completes the proof.

*)

Record uPred (M : ucmra) : Type := UPred {
  uPred_holds : nat → M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≼{n2} x2 → n2 ≤ n1 → uPred_holds n2 x2
}.
(** When working in the model, it is convenient to be able to treat [uPred] as
[nat → M → Prop].  But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.
Bind Scope bi_scope with uPred.
Global Arguments uPred_holds {_} _ _ _ : simpl never.
Add Printing Constructor uPred.
Global Instance: Params (@uPred_holds) 3 := {}.

Section cofe.
  Context {M : ucmra}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Local Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.
  Inductive uPred_dist' (n : nat) (P Q : uPred M) : Prop :=
    { uPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Local Instance uPred_dist : Dist (uPred M) := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros n P Q HPQ; split=> i x ??; apply HPQ; auto.
  Qed.
  Canonical Structure uPredO : ofe := Ofe (uPred M) uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c,
    {| uPred_holds n x := ∀ n', n' ≤ n → ✓{n'} x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply uPred_mono.
    - eapply HP, cmra_validN_includedN, cmra_includedN_le=>//; lia.
    - eapply cmra_includedN_le=>//; lia.
    - done.
  Qed.
  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    intros n c; split=>i x Hin Hv.
    etrans; [|by symmetry; apply (chain_cauchy c i n)]. split=>H; [by apply H|].
    repeat intro. apply (chain_cauchy c _ i)=>//. by eapply uPred_mono.
  Qed.
End cofe.
Global Arguments uPredO : clear implicits.

Global Instance uPred_ne {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto; by rewrite Hx.
Qed.
Global Instance uPred_proper {M} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply uPred_ne, equiv_dist. Qed.

Lemma uPred_holds_ne {M} (P Q : uPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using uPred_mono, cmra_validN_le.
Qed.

(* Equivalence to the definition of uPred in the appendix. *)
Lemma uPred_alt {M : ucmra} (P: nat → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ≤ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ≤ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼{n} x2 → ∀ m, m ≤ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ≤ n1 → x1 ≡{n1}≡ x2 → x1 ≼{n2} x2).
  { intros ????? H. eapply cmra_includedN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using cmra_includedN_le.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed.

(** functor *)
Program Definition uPred_map {M1 M2 : ucmra} (f : M2 -n> M1)
  `{!CmraMorphism f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, cmra_morphism_monotoneN. Qed.

Global Instance uPred_map_ne {M1 M2 : ucmra} (f : M2 -n> M1)
  `{!CmraMorphism f} n : Proper (dist n ==> dist n) (uPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using cmra_morphism_validN.
Qed.
Lemma uPred_map_id {M : ucmra} (P : uPred M): uPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma uPred_map_compose {M1 M2 M3 : ucmra} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CmraMorphism f, !CmraMorphism g} (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma uPred_map_ext {M1 M2 : ucmra} (f g : M1 -n> M2)
      `{!CmraMorphism f} `{!CmraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, uPred_map f x ≡ uPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /uPred_holds /= Hf. Qed.
Definition uPredO_map {M1 M2 : ucmra} (f : M2 -n> M1) `{!CmraMorphism f} :
  uPredO M1 -n> uPredO M2 := OfeMor (uPred_map f : uPredO M1 → uPredO M2).
Lemma uPredO_map_ne {M1 M2 : ucmra} (f g : M2 -n> M1)
    `{!CmraMorphism f, !CmraMorphism g} n :
  f ≡{n}≡ g → uPredO_map f ≡{n}≡ uPredO_map g.
Proof.
  by intros Hfg P; split=> n' y ??;
    rewrite /uPred_holds /= (dist_le _ _ _ _(Hfg y)); last lia.
Qed.

Program Definition uPredOF (F : urFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := uPredO (urFunctor_car F B A);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := uPredO_map (urFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply uPredO_map_ne, urFunctor_map_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A ? B ? P; simpl. rewrite -{2}(uPred_map_id P).
  apply uPred_map_ext=>y. by rewrite urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' P; simpl. rewrite -uPred_map_compose.
  apply uPred_map_ext=>y; apply urFunctor_map_compose.
Qed.

Global Instance uPredOF_contractive F :
  urFunctorContractive F → oFunctorContractive (uPredOF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n P Q HPQ.
  apply uPredO_map_ne, urFunctor_map_contractive. destruct n; split; by apply HPQ.
Qed.

(** logical entailement *)
Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Global Hint Resolve uPred_mono : uPred_def.

(** logical connectives *)
Program Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds n x := φ |}.
Solve Obligations with done.
Definition uPred_pure_aux : seal (@uPred_pure_def). Proof. by eexists. Qed.
Definition uPred_pure := uPred_pure_aux.(unseal).
Global Arguments uPred_pure {M}.
Definition uPred_pure_eq :
  @uPred_pure = @uPred_pure_def := uPred_pure_aux.(seal_eq).

Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_and_aux : seal (@uPred_and_def). Proof. by eexists. Qed.
Definition uPred_and := uPred_and_aux.(unseal).
Global Arguments uPred_and {M}.
Definition uPred_and_eq: @uPred_and = @uPred_and_def := uPred_and_aux.(seal_eq).

Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_or_aux : seal (@uPred_or_def). Proof. by eexists. Qed.
Definition uPred_or := uPred_or_aux.(unseal).
Global Arguments uPred_or {M}.
Definition uPred_or_eq: @uPred_or = @uPred_or_def := uPred_or_aux.(seal_eq).

Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ [x2 Hx1'] Hn1 n2 x3 [x4 Hx3] ?; simpl in *.
  rewrite Hx3 (dist_le _ _ _ _ Hx1'); auto. intros ??.
  eapply HPQ; auto. exists (x2 ⋅ x4); by rewrite assoc.
Qed.
Definition uPred_impl_aux : seal (@uPred_impl_def). Proof. by eexists. Qed.
Definition uPred_impl := uPred_impl_aux.(unseal).
Global Arguments uPred_impl {M}.
Definition uPred_impl_eq :
  @uPred_impl = @uPred_impl_def := uPred_impl_aux.(seal_eq).

Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_forall_aux : seal (@uPred_forall_def). Proof. by eexists. Qed.
Definition uPred_forall := uPred_forall_aux.(unseal).
Global Arguments uPred_forall {M A}.
Definition uPred_forall_eq :
  @uPred_forall = @uPred_forall_def := uPred_forall_aux.(seal_eq).

Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_exist_aux : seal (@uPred_exist_def). Proof. by eexists. Qed.
Definition uPred_exist := uPred_exist_aux.(unseal).
Global Arguments uPred_exist {M A}.
Definition uPred_exist_eq: @uPred_exist = @uPred_exist_def := uPred_exist_aux.(seal_eq).

Program Definition uPred_internal_eq_def {M} {A : ofe} (a1 a2 : A) : uPred M :=
  {| uPred_holds n x := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using dist_le.
Definition uPred_internal_eq_aux : seal (@uPred_internal_eq_def). Proof. by eexists. Qed.
Definition uPred_internal_eq := uPred_internal_eq_aux.(unseal).
Global Arguments uPred_internal_eq {M A}.
Definition uPred_internal_eq_eq:
  @uPred_internal_eq = @uPred_internal_eq_def := uPred_internal_eq_aux.(seal_eq).

Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros M P Q n1 n2 x y (x1&x2&Hx&?&?) [z Hy] Hn.
  exists x1, (x2 ⋅ z); split_and?; eauto using uPred_mono, cmra_includedN_l.
  rewrite Hy. eapply dist_le, Hn. by rewrite Hx assoc.
Qed.
Definition uPred_sep_aux : seal (@uPred_sep_def). Proof. by eexists. Qed.
Definition uPred_sep := uPred_sep_aux.(unseal).
Global Arguments uPred_sep {M}.
Definition uPred_sep_eq: @uPred_sep = @uPred_sep_def := uPred_sep_aux.(seal_eq).

Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ???; simpl in *.
  eapply uPred_mono with n3 (x1 ⋅ x3);
    eauto using cmra_validN_includedN, cmra_monoN_r, cmra_includedN_le.
Qed.
Definition uPred_wand_aux : seal (@uPred_wand_def). Proof. by eexists. Qed.
Definition uPred_wand := uPred_wand_aux.(unseal).
Global Arguments uPred_wand {M}.
Definition uPred_wand_eq :
  @uPred_wand = @uPred_wand_def := uPred_wand_aux.(seal_eq).

(* Equivalently, this could be `∀ y, P n y`.  That's closer to the intuition
   of "embedding the step-indexed logic in Iris", but the two are equivalent
   because Iris is afine.  The following is easier to work with. *)
Program Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.
Definition uPred_plainly_aux : seal (@uPred_plainly_def). Proof. by eexists. Qed.
Definition uPred_plainly := uPred_plainly_aux.(unseal).
Global Arguments uPred_plainly {M}.
Definition uPred_plainly_eq :
  @uPred_plainly = @uPred_plainly_def := uPred_plainly_aux.(seal_eq).

Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (core x) |}.
Solve Obligations with naive_solver eauto using uPred_mono, cmra_core_monoN.
Definition uPred_persistently_aux : seal (@uPred_persistently_def). Proof. by eexists. Qed.
Definition uPred_persistently := uPred_persistently_aux.(unseal).
Global Arguments uPred_persistently {M}.
Definition uPred_persistently_eq :
  @uPred_persistently = @uPred_persistently_def := uPred_persistently_aux.(seal_eq).

Program Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation.
  intros M P [|n1] [|n2] x1 x2; eauto using uPred_mono, cmra_includedN_S with lia.
Qed.
Definition uPred_later_aux : seal (@uPred_later_def). Proof. by eexists. Qed.
Definition uPred_later := uPred_later_aux.(unseal).
Global Arguments uPred_later {M}.
Definition uPred_later_eq :
  @uPred_later = @uPred_later_def := uPred_later_aux.(seal_eq).

Program Definition uPred_ownM_def {M : ucmra} (a : M) : uPred M :=
  {| uPred_holds n x := a ≼{n} x |}.
Next Obligation.
  intros M a n1 n2 x1 x [a' Hx1] [x2 Hx] Hn.
  exists (a' ⋅ x2). rewrite Hx. eapply dist_le, Hn. rewrite (assoc op) -Hx1 //.
Qed.
Definition uPred_ownM_aux : seal (@uPred_ownM_def). Proof. by eexists. Qed.
Definition uPred_ownM := uPred_ownM_aux.(unseal).
Global Arguments uPred_ownM {M}.
Definition uPred_ownM_eq :
  @uPred_ownM = @uPred_ownM_def := uPred_ownM_aux.(seal_eq).

Program Definition uPred_cmra_valid_def {M} {A : cmra} (a : A) : uPred M :=
  {| uPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using cmra_validN_le.
Definition uPred_cmra_valid_aux : seal (@uPred_cmra_valid_def). Proof. by eexists. Qed.
Definition uPred_cmra_valid := uPred_cmra_valid_aux.(unseal).
Global Arguments uPred_cmra_valid {M A}.
Definition uPred_cmra_valid_eq :
  @uPred_cmra_valid = @uPred_cmra_valid_def := uPred_cmra_valid_aux.(seal_eq).

Program Definition uPred_bupd_def {M} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros M Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk.
  rewrite (dist_le _ _ _ _ Hx); last lia. intros Hxy.
  destruct (HQ k (x3 ⋅ yf)) as (x'&?&?); [auto|by rewrite assoc|].
  exists (x' ⋅ x3); split; first by rewrite -assoc.
  eauto using uPred_mono, cmra_includedN_l.
Qed.
Definition uPred_bupd_aux : seal (@uPred_bupd_def). Proof. by eexists. Qed.
Definition uPred_bupd := uPred_bupd_aux.(unseal).
Global Arguments uPred_bupd {M}.
Definition uPred_bupd_eq :
  @uPred_bupd = @uPred_bupd_def := uPred_bupd_aux.(seal_eq).

(** Global uPred-specific Notation *)
Notation "✓ x" := (uPred_cmra_valid x) (at level 20) : bi_scope.

(** Primitive logical rules.
    These are not directly usable later because they do not refer to the BI
    connectives. *)
Module uPred_primitive.
Definition unseal_eqs :=
  (uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_internal_eq_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_plainly_eq, uPred_persistently_eq, uPred_later_eq, uPred_ownM_eq,
  uPred_cmra_valid_eq, @uPred_bupd_eq).
Ltac unseal :=
  rewrite !unseal_eqs /=.

Section primitive.
Context {M : ucmra}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Local Arguments uPred_holds {_} !_ _ _ /.
Local Hint Immediate uPred_in_entails : core.

Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.
Notation "P ⊣⊢ Q" := (@uPred_equiv M P%I Q%I) : stdpp_scope.
Notation "(⊣⊢)" := (@uPred_equiv M) (only parsing) : stdpp_scope.

Notation "'True'" := (uPred_pure True) : bi_scope.
Notation "'False'" := (uPred_pure False) : bi_scope.
Notation "'⌜' φ '⌝'" := (uPred_pure φ%type%stdpp) : bi_scope.
Infix "∧" := uPred_and : bi_scope.
Infix "∨" := uPred_or : bi_scope.
Infix "→" := uPred_impl : bi_scope.
Notation "∀ x .. y , P" :=
  (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)) : bi_scope.
Notation "∃ x .. y , P" :=
  (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)) : bi_scope.
Infix "∗" := uPred_sep : bi_scope.
Infix "-∗" := uPred_wand : bi_scope.
Notation "□ P" := (uPred_persistently P) : bi_scope.
Notation "■ P" := (uPred_plainly P) : bi_scope.
Notation "x ≡ y" := (uPred_internal_eq x y) : bi_scope.
Notation "▷ P" := (uPred_later P) : bi_scope.
Notation "|==> P" := (uPred_bupd P) : bi_scope.

(** Entailment *)
Lemma entails_po : PreOrder (⊢).
Proof.
  split.
  - by intros P; split=> x i.
  - by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
Qed.
Lemma entails_anti_sym : AntiSymm (⊣⊢) (⊢).
Proof. intros P Q HPQ HQP; split=> x n; by split; [apply HPQ|apply HQP]. Qed.
Lemma equiv_entails P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split.
  - intros HPQ; split; split=> x i; apply HPQ.
  - intros [??]. exact: entails_anti_sym.
Qed.
Lemma entails_lim (cP cQ : chain (uPredO M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
  eapply uPred_holds_ne, Hlim, HP; rewrite ?conv_compl; eauto.
Qed.

(** Non-expansiveness and setoid morphisms *)
Lemma pure_ne n : Proper (iff ==> dist n) (@uPred_pure M).
Proof. intros φ1 φ2 Hφ. by unseal; split=> -[|m] ?; try apply Hφ. Qed.

Lemma and_ne : NonExpansive2 (@uPred_and M).
Proof.
  intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
  split; (intros [??]; split; [by apply HP|by apply HQ]).
Qed.

Lemma or_ne : NonExpansive2 (@uPred_or M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x n' ??.
  unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
Qed.

Lemma impl_ne :
  NonExpansive2 (@uPred_impl M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x n' ??.
  unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP; auto.
Qed.

Lemma sep_ne : NonExpansive2 (@uPred_sep M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??.
  unseal; split; intros (x1&x2&?&?&?); ofe_subst x;
    exists x1, x2; split_and!; try (apply HP || apply HQ);
    eauto using cmra_validN_op_l, cmra_validN_op_r.
Qed.

Lemma wand_ne :
  NonExpansive2 (@uPred_wand M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??; unseal; split; intros HPQ x' n'' ???;
    apply HQ, HPQ, HP; eauto using cmra_validN_op_r.
Qed.

Lemma internal_eq_ne (A : ofe) :
  NonExpansive2 (@uPred_internal_eq M A).
Proof.
  intros n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
  - by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
  - by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
Qed.

Lemma forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall M A).
Proof.
  by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
Qed.

Lemma exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist M A).
Proof.
  intros Ψ1 Ψ2 HΨ.
  unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
Qed.

Lemma later_contractive : Contractive (@uPred_later M).
Proof.
  unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try lia.
  apply HPQ; eauto using cmra_validN_S.
Qed.

Lemma plainly_ne : NonExpansive (@uPred_plainly M).
Proof.
  intros n P1 P2 HP.
  unseal; split=> n' x; split; apply HP; eauto using ucmra_unit_validN.
Qed.

Lemma persistently_ne : NonExpansive (@uPred_persistently M).
Proof.
  intros n P1 P2 HP.
  unseal; split=> n' x; split; apply HP; eauto using cmra_core_validN.
Qed.

Lemma ownM_ne : NonExpansive (@uPred_ownM M).
Proof.
  intros n a b Ha.
  unseal; split=> n' x ? /=. by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.

Lemma cmra_valid_ne {A : cmra} :
  NonExpansive (@uPred_cmra_valid M A).
Proof.
  intros n a b Ha; unseal; split=> n' x ? /=.
  by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.

Lemma bupd_ne : NonExpansive (@uPred_bupd M).
Proof.
  intros n P Q HPQ.
  unseal; split=> n' x; split; intros HP k yf ??;
    destruct (HP k yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto using cmra_validN_op_l.
Qed.

(** Introduction and elimination rules *)
Lemma pure_intro φ P : φ → P ⊢ ⌜φ⌝.
Proof. by intros ?; unseal; split. Qed.
Lemma pure_elim' φ P : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P.
Proof. unseal; intros HP; split=> n x ??. by apply HP. Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝.
Proof. by unseal. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. intros HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR]. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; left; auto. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; right; auto. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof.
  intros HP HQ; unseal; split=> n x ? [?|?].
  - by apply HP.
  - by apply HQ.
Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof.
  unseal; intros HQ; split=> n x ?? n' x' ????. apply HQ;
    naive_solver eauto using uPred_mono, cmra_included_includedN.
Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. unseal; intros HP ; split=> n x ? [??]; apply HP with n x; auto. Qed.

Lemma forall_intro {A} P (Ψ : A → uPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ. Qed.
Lemma forall_elim {A} {Ψ : A → uPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. unseal; split=> n x ? HP; apply HP. Qed.

Lemma exist_intro {A} {Ψ : A → uPred M} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. unseal; split=> n x ??; by exists a. Qed.
Lemma exist_elim {A} (Φ : A → uPred M) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. unseal; intros HΦΨ; split=> n x ? [a ?]; by apply HΦΨ with a. Qed.

(** BI connectives *)
Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
Proof.
  intros HQ HQ'; unseal.
  split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x;
    eauto 7 using cmra_validN_op_l, cmra_validN_op_r, uPred_in_entails.
Qed.
Lemma True_sep_1 P : P ⊢ True ∗ P.
Proof.
  unseal; split; intros n x ??. exists (core x), x. by rewrite cmra_core_l.
Qed.
Lemma True_sep_2 P : True ∗ P ⊢ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&_&?); ofe_subst;
    eauto using uPred_mono, cmra_includedN_r.
Qed.
Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&?&?); exists x2, x1; by rewrite (comm op).
Qed.
Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
  exists y1, (y2 ⋅ x2); split_and?; auto.
  + by rewrite (assoc op) -Hy -Hx.
  + by exists y2, x2.
Qed.
Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
Proof.
  unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
  exists x, x'; split_and?; auto.
  eapply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
Proof.
  unseal =>HPQR. split; intros n x ? (?&?&?&?&?). ofe_subst.
  eapply HPQR; eauto using cmra_validN_op_l.
Qed.

(** Persistently *)
Lemma persistently_mono P Q : (P ⊢ Q) → □ P ⊢ □ Q.
Proof. intros HP; unseal; split=> n x ? /=. by apply HP, cmra_core_validN. Qed.
Lemma persistently_elim P : □ P ⊢ P.
Proof.
  unseal; split=> n x ? /=.
  eauto using uPred_mono, cmra_included_core, cmra_included_includedN.
Qed.
Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
Proof. unseal; split=> n x ?? /=. by rewrite cmra_core_idemp. Qed.

Lemma persistently_forall_2 {A} (Ψ : A → uPred M) : (∀ a, □ Ψ a) ⊢ (□ ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma persistently_exist_1 {A} (Ψ : A → uPred M) : (□ ∃ a, Ψ a) ⊢ (∃ a, □ Ψ a).
Proof. by unseal. Qed.

Lemma persistently_and_sep_l_1 P Q : □ P ∧ Q ⊢ P ∗ Q.
Proof.
  unseal; split=> n x ? [??]; exists (core x), x; simpl in *.
  by rewrite cmra_core_l.
Qed.

(** Plainly *)
Lemma plainly_mono P Q : (P ⊢ Q) → ■ P ⊢ ■ Q.
Proof. intros HP; unseal; split=> n x ? /=. apply HP, ucmra_unit_validN. Qed.
Lemma plainly_elim_persistently P : ■ P ⊢ □ P.
Proof. unseal; split; simpl; eauto using uPred_mono, ucmra_unit_leastN. Qed.
Lemma plainly_idemp_2 P : ■ P ⊢ ■ ■ P.
Proof. unseal; split=> n x ?? //. Qed.

Lemma plainly_forall_2 {A} (Ψ : A → uPred M) : (∀ a, ■ Ψ a) ⊢ (■ ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma plainly_exist_1 {A} (Ψ : A → uPred M) : (■ ∃ a, Ψ a) ⊢ (∃ a, ■ Ψ a).
Proof. by unseal. Qed.

Lemma prop_ext_2 P Q : ■ ((P -∗ Q) ∧ (Q -∗ P)) ⊢ P ≡ Q.
Proof.
  unseal; split=> n x ? /=. setoid_rewrite (left_id ε op). split; naive_solver.
Qed.

(* The following two laws are very similar, and indeed they hold not just for □
   and ■, but for any modality defined as `M P n x := ∀ y, R x y → P n y`. *)
Lemma persistently_impl_plainly P Q : (■ P → □ Q) ⊢ □ (■ P → Q).
Proof.
  unseal; split=> /= n x ? HPQ n' x' ????.
  eapply uPred_mono with n' (core x)=>//; [|by apply cmra_included_includedN].
  apply (HPQ n' x); eauto using cmra_validN_le.
Qed.

Lemma plainly_impl_plainly P Q : (■ P → ■ Q) ⊢ ■ (■ P → Q).
Proof.
  unseal; split=> /= n x ? HPQ n' x' ????.
  eapply uPred_mono with n' ε=>//; [|by apply cmra_included_includedN].
  apply (HPQ n' x); eauto using cmra_validN_le.
Qed.

(** Later *)
Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
Proof.
  unseal=> HP; split=>-[|n] x ??; [done|apply HP; eauto using cmra_validN_S].
Qed.
Lemma later_intro P : P ⊢ ▷ P.
Proof.
  unseal; split=> -[|n] /= x ? HP; first done.
  apply uPred_mono with (S n) x; eauto using cmra_validN_S.
Qed.
Lemma later_forall_2 {A} (Φ : A → uPred M) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
Proof. unseal; by split=> -[|n] x. Qed.
Lemma later_exist_false {A} (Φ : A → uPred M) :
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof. unseal; split=> -[|[|n]] x /=; eauto. Qed.
Lemma later_sep_1 P Q : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q.
Proof.
  unseal; split=> n x ?.
  destruct n as [|n]; simpl.
  { by exists x, (core x); rewrite cmra_core_r. }
  intros (x1&x2&Hx&?&?); destruct (cmra_extend n x x1 x2)
    as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_S; simpl in *.
  exists y1, y2; split; [by rewrite Hx'|by rewrite Hy1 Hy2].
Qed.
Lemma later_sep_2 P Q : ▷ P ∗ ▷ Q ⊢ ▷ (P ∗ Q).
Proof.
  unseal; split=> n x ?.
  destruct n as [|n]; simpl; [done|intros (x1&x2&Hx&?&?)].
  exists x1, x2; eauto using dist_S.
Qed.

Lemma later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
Proof.
  unseal; split=> -[|n] x ? /= HP; [by left|right].
  intros [|n'] x' ????; eauto using uPred_mono, cmra_included_includedN.
Qed.

Lemma later_persistently_1 P : ▷ □ P ⊢ □ ▷ P.
Proof. by unseal. Qed.
Lemma later_persistently_2 P : □ ▷ P ⊢ ▷ □ P.
Proof. by unseal. Qed.
Lemma later_plainly_1 P : ▷ ■ P ⊢ ■ ▷ P.
Proof. by unseal. Qed.
Lemma later_plainly_2 P : ■ ▷ P ⊢ ▷ ■ P.
Proof. by unseal. Qed.

(** Internal equality *)
Lemma internal_eq_refl {A : ofe} P (a : A) : P ⊢ (a ≡ a).
Proof. unseal; by split=> n x ??; simpl. Qed.
Lemma internal_eq_rewrite {A : ofe} a b (Ψ : A → uPred M) :
  NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
Proof. intros HΨ. unseal; split=> n x ?? n' x' ??? Ha. by apply HΨ with n a. Qed.

Lemma fun_ext {A} {B : A → ofe} (g1 g2 : discrete_fun B) :
  (∀ i, g1 i ≡ g2 i) ⊢ g1 ≡ g2.
Proof. by unseal. Qed.
Lemma sig_eq {A : ofe} (P : A → Prop) (x y : sigO P) :
  proj1_sig x ≡ proj1_sig y ⊢ x ≡ y.
Proof. by unseal. Qed.

Lemma later_eq_1 {A : ofe} (x y : A) : Next x ≡ Next y ⊢ ▷ (x ≡ y).
Proof. by unseal. Qed.
Lemma later_eq_2 {A : ofe} (x y : A) : ▷ (x ≡ y) ⊢ Next x ≡ Next y.
Proof. by unseal. Qed.

Lemma discrete_eq_1 {A : ofe} (a b : A) : Discrete a → a ≡ b ⊢ ⌜a ≡ b⌝.
Proof.
  unseal=> ?. split=> n x ?. by apply (discrete_iff n).
Qed.

(** This is really just a special case of an entailment
between two [siProp], but we do not have the infrastructure
to express the more general case. This temporary proof rule will
be replaced by the proper one eventually. *)
Lemma internal_eq_entails {A B : ofe} (a1 a2 : A) (b1 b2 : B) :
  (∀ n, a1 ≡{n}≡ a2 → b1 ≡{n}≡ b2) → a1 ≡ a2 ⊢ b1 ≡ b2.
Proof. unseal=>Hsi. split=>n x ?. apply Hsi. Qed.

(** Basic update modality *)
Lemma bupd_intro P : P ⊢ |==> P.
Proof.
  unseal. split=> n x ? HP k yf ?; exists x; split; first done.
  apply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ⊢ |==> Q.
Proof.
  unseal. intros HPQ; split=> n x ? HP k yf ??.
  destruct (HP k yf) as (x'&?&?); eauto.
  exists x'; split; eauto using uPred_in_entails, cmra_validN_op_l.
Qed.
Lemma bupd_trans P : (|==> |==> P) ⊢ |==> P.
Proof. unseal; split; naive_solver. Qed.
Lemma bupd_frame_r P R : (|==> P) ∗ R ⊢ |==> P ∗ R.
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
  destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
  { by rewrite assoc -(dist_le _ _ _ _ Hx); last lia. }
  exists (x' ⋅ x2); split; first by rewrite -assoc.
  exists x', x2. eauto using uPred_mono, cmra_validN_op_l, cmra_validN_op_r.
Qed.
Lemma bupd_plainly P : (|==> ■ P) ⊢ P.
Proof.
  unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  eapply uPred_mono; eauto using ucmra_unit_leastN.
Qed.

(** Own *)
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof.
  unseal; split=> n x ?; split.
  - intros [z ?]; exists a1, (a2 ⋅ z); split; [by rewrite (assoc op)|].
    split.
    + by exists (core a1); rewrite cmra_core_r.
    + by exists z.
  - intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
    by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1)
      -(assoc op _ a2) (comm op z1) -Hy1 -Hy2.
Qed.
Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ □ uPred_ownM (core a).
Proof.
  split=> n x /=; unseal; intros Hx. simpl. by apply cmra_core_monoN.
Qed.
Lemma ownM_unit P : P ⊢ (uPred_ownM ε).
Proof. unseal; split=> n x ??; by  exists x; rewrite left_id. Qed.
Lemma later_ownM a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  unseal; split=> -[|n] x /= ? Hax; first by eauto using ucmra_unit_leastN.
  destruct Hax as [y ?].
  destruct (cmra_extend n x a y) as (a'&y'&Hx&?&?); auto using cmra_validN_S.
  exists a'. rewrite Hx. eauto using cmra_includedN_l.
Qed.

Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x ⊢ |==> ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
Proof.
  unseal=> Hup; split=> n x2 ? [x3 Hx] k yf ??.
  destruct (Hup k (Some (x3 ⋅ yf))) as (y&?&?); simpl in *.
  { rewrite /= assoc -(dist_le _ _ _ _ Hx); auto. }
  exists (y ⋅ x3); split; first by rewrite -assoc.
  exists y; eauto using cmra_includedN_l.
Qed.

(** Valid *)
Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
Proof.
  unseal; split=> n x Hv [a' ?]; ofe_subst; eauto using cmra_validN_op_l.
Qed.
Lemma cmra_valid_intro {A : cmra} P (a : A) : ✓ a → P ⊢ (✓ a).
Proof. unseal=> ?; split=> n x ? _ /=; by apply cmra_valid_validN. Qed.
Lemma cmra_valid_elim {A : cmra} (a : A) : ¬ ✓{0} a → ✓ a ⊢ False.
Proof. unseal=> Ha; split=> n x ??; apply Ha, cmra_validN_le with n; auto. Qed.
Lemma plainly_cmra_valid_1 {A : cmra} (a : A) : ✓ a ⊢ ■ ✓ a.
Proof. by unseal. Qed.
Lemma cmra_valid_weaken {A : cmra} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
Proof. unseal; split=> n x _; apply cmra_validN_op_l. Qed.

Lemma discrete_valid {A : cmra} `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
Proof. unseal; split=> n x _. by rewrite /= -cmra_discrete_valid_iff. Qed.

(** This is really just a special case of an entailment
between two [siProp], but we do not have the infrastructure
to express the more general case. This temporary proof rule will
be replaced by the proper one eventually. *)
Lemma valid_entails {A B : cmra} (a : A) (b : B) :
  (∀ n, ✓{n} a → ✓{n} b) → ✓ a ⊢ ✓ b.
Proof. unseal=> Hval. split=>n x ?. apply Hval. Qed.

(** Consistency/soundness statement *)
(** The lemmas [pure_soundness] and [internal_eq_soundness] should become an
instance of [siProp] soundness in the future. *)
Lemma pure_soundness φ : (True ⊢ ⌜ φ ⌝) → φ.
Proof. unseal=> -[H]. by apply (H 0 ε); eauto using ucmra_unit_validN. Qed.

Lemma internal_eq_soundness {A : ofe} (x y : A) : (True ⊢ x ≡ y) → x ≡ y.
Proof.
  unseal=> -[H]. apply equiv_dist=> n.
  by apply (H n ε); eauto using ucmra_unit_validN.
Qed.

Lemma later_soundness P : (True ⊢ ▷ P) → (True ⊢ P).
Proof.
  unseal=> -[HP]; split=> n x Hx _.
  apply uPred_mono with n ε; eauto using ucmra_unit_leastN.
  by apply (HP (S n)); eauto using ucmra_unit_validN.
Qed.
End primitive.
End uPred_primitive.
