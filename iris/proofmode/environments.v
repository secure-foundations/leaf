From iris.prelude Require Export prelude.
From iris.bi Require Export bi.
From iris.proofmode Require Import base.
From iris.prelude Require Import options.
Import bi.

Inductive env (A : Type) : Type :=
  | Enil : env A
  | Esnoc : env A → ident → A → env A.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _ _ _.
Global Instance: Params (@Enil) 1 := {}.
Global Instance: Params (@Esnoc) 1 := {}.

Fixpoint env_lookup {A} (i : ident) (Γ : env A) : option A :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x => if ident_beq i j then Some x else env_lookup i Γ
  end.

Module env_notations.
  Notation "y ≫= f" := (pm_option_bind f y).
  Notation "x ← y ; z" := (y ≫= λ x, z).
  Notation "' x1 ← y ; z" := (y ≫= (λ x1, z)).
  Notation "Γ !! j" := (env_lookup j Γ).
End env_notations.
Import env_notations.

Local Open Scope lazy_bool_scope.

Inductive env_wf {A} : env A → Prop :=
  | Enil_wf : env_wf Enil
  | Esnoc_wf Γ i x : Γ !! i = None → env_wf Γ → env_wf (Esnoc Γ i x).

Fixpoint env_to_list {A} (E : env A) : list A :=
  match E with Enil => [] | Esnoc Γ _ x => x :: env_to_list Γ end.
Coercion env_to_list : env >-> list.
Global Instance: Params (@env_to_list) 1 := {}.

Fixpoint env_dom {A} (Γ : env A) : list ident :=
  match Γ with Enil => [] | Esnoc Γ i _ => i :: env_dom Γ end.

Fixpoint env_app {A} (Γapp : env A) (Γ : env A) : option (env A) :=
  match Γapp with
  | Enil => Some Γ
  | Esnoc Γapp i x =>
     Γ' ← env_app Γapp Γ;
     match Γ' !! i with None => Some (Esnoc Γ' i x) | Some _ => None end
  end.

Fixpoint env_replace {A} (i: ident) (Γi: env A) (Γ: env A) : option (env A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x =>
     if ident_beq i j then env_app Γi Γ else
     match Γi !! j with
     | None => Γ' ← env_replace i Γi Γ; Some (Esnoc Γ' j x)
     | Some _ => None
     end
  end.

Fixpoint env_delete {A} (i : ident) (Γ : env A) : env A :=
  match Γ with
  | Enil => Enil
  | Esnoc Γ j x => if ident_beq i j then Γ else Esnoc (env_delete i Γ) j x
  end.

Fixpoint env_lookup_delete {A} (i : ident) (Γ : env A) : option (A * env A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x =>
     if ident_beq i j then Some (x,Γ)
     else '(y,Γ') ← env_lookup_delete i Γ; Some (y, Esnoc Γ' j x)
  end.

Inductive env_Forall2 {A B} (P : A → B → Prop) : env A → env B → Prop :=
  | env_Forall2_nil : env_Forall2 P Enil Enil
  | env_Forall2_snoc Γ1 Γ2 i x y :
     env_Forall2 P Γ1 Γ2 → P x y → env_Forall2 P (Esnoc Γ1 i x) (Esnoc Γ2 i y).

Inductive env_subenv {A} : relation (env A) :=
  | env_subenv_nil : env_subenv Enil Enil
  | env_subenv_snoc Γ1 Γ2 i x :
     env_subenv Γ1 Γ2 → env_subenv (Esnoc Γ1 i x) (Esnoc Γ2 i x)
  | env_subenv_skip Γ1 Γ2 i y :
     env_subenv Γ1 Γ2 → env_subenv Γ1 (Esnoc Γ2 i y).

Section env.
Context {A : Type}.
Implicit Types Γ : env A.
Implicit Types i : ident.
Implicit Types x : A.
Local Hint Resolve Esnoc_wf Enil_wf : core.

Ltac simplify :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : context [ident_beq ?s1 ?s2] |- _ => destruct (ident_beq_reflect s1 s2)
  | |- context [ident_beq ?s1 ?s2] => destruct (ident_beq_reflect s1 s2)
  | H : context [pm_option_bind _ ?x] |- _ => destruct x eqn:?
  | |- context [pm_option_bind _ ?x] => destruct x eqn:?
  | _ => case_match
  end.

Lemma env_lookup_perm Γ i x : Γ !! i = Some x → Γ ≡ₚ x :: env_delete i Γ.
Proof.
  induction Γ; intros; simplify; rewrite 1?Permutation_swap; f_equiv; eauto.
Qed.

Lemma env_lookup_snoc Γ i P : env_lookup i (Esnoc Γ i P) = Some P.
Proof. induction Γ; simplify; auto. Qed.
Lemma env_lookup_snoc_ne Γ i j P :
  i ≠ j → env_lookup i (Esnoc Γ j P) = env_lookup i Γ.
Proof. induction Γ=> ?; simplify; auto. Qed.

Lemma env_app_perm Γ Γapp Γ' :
  env_app Γapp Γ = Some Γ' → env_to_list Γ' ≡ₚ Γapp ++ Γ.
Proof. revert Γ'; induction Γapp; intros; simplify; f_equal; auto. Qed.
Lemma env_app_fresh Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None → Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_fresh_1 Γ Γapp Γ' i x :
  env_app Γapp Γ = Some Γ' → Γ' !! i = None → Γ !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_disjoint Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None ∨ Γ !! i = None.
Proof.
  revert Γ'.
  induction Γapp; intros; simplify; naive_solver eauto using env_app_fresh_1.
Qed.
Lemma env_app_wf Γ Γapp Γ' : env_app Γapp Γ = Some Γ' → env_wf Γ → env_wf Γ'.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.

Lemma env_replace_fresh Γ Γj Γ' i j :
  env_replace j Γj Γ = Some Γ' →
  Γj !! i = None → env_delete j Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γ; intros; simplify; eauto using env_app_fresh. Qed.
Lemma env_replace_wf Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → env_wf (env_delete i Γ) → env_wf Γ'.
Proof.
  revert Γ'. induction Γ; intros ??; simplify; [|inversion_clear 1];
    eauto using env_app_wf, env_replace_fresh.
Qed.
Lemma env_replace_lookup Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → is_Some (Γ !! i).
Proof. revert Γ'. induction Γ; intros; simplify; eauto. Qed.
Lemma env_replace_perm Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → Γ' ≡ₚ Γi ++ env_delete i Γ.
Proof.
  revert Γ'. induction Γ as [|Γ IH j y]=>Γ' ?; simplify; auto using env_app_perm.
  rewrite -Permutation_middle -IH //.
Qed.

Lemma env_lookup_delete_correct Γ i :
  env_lookup_delete i Γ = (x ← Γ !! i; Some (x,env_delete i Γ)).
Proof. induction Γ; intros; simplify; eauto. Qed.
Lemma env_lookup_delete_Some Γ Γ' i x :
  env_lookup_delete i Γ = Some (x,Γ') ↔ Γ !! i = Some x ∧ Γ' = env_delete i Γ.
Proof. rewrite env_lookup_delete_correct; simplify; naive_solver. Qed.

Lemma env_lookup_env_delete Γ j : env_wf Γ → env_delete j Γ !! j = None.
Proof. induction 1; intros; simplify; eauto. Qed.
Lemma env_lookup_env_delete_ne Γ i j : i ≠ j → env_delete j Γ !! i = Γ !! i.
Proof. induction Γ; intros; simplify; eauto. Qed.
Lemma env_delete_fresh Γ i j : Γ !! i = None → env_delete j Γ !! i = None.
Proof. induction Γ; intros; simplify; eauto. Qed.

Lemma env_delete_wf Γ j : env_wf Γ → env_wf (env_delete j Γ).
Proof. induction 1; simplify; eauto using env_delete_fresh. Qed.

Global Instance env_Forall2_refl (P : relation A) :
  Reflexive P → Reflexive (env_Forall2 P).
Proof. intros ? Γ. induction Γ; constructor; auto. Qed.
Global Instance env_Forall2_sym (P : relation A) :
  Symmetric P → Symmetric (env_Forall2 P).
Proof. induction 2; constructor; auto. Qed.
Global Instance env_Forall2_trans (P : relation A) :
  Transitive P → Transitive (env_Forall2 P).
Proof.
  intros ? Γ1 Γ2 Γ3 HΓ; revert Γ3.
  induction HΓ; inversion_clear 1; constructor; eauto.
Qed.
Global Instance env_Forall2_antisymm (P Q : relation A) :
  AntiSymm P Q → AntiSymm (env_Forall2 P) (env_Forall2 Q).
Proof. induction 2; inversion_clear 1; constructor; auto. Qed.
Lemma env_Forall2_impl {B} (P Q : A → B → Prop) Γ Σ :
  env_Forall2 P Γ Σ → (∀ x y, P x y → Q x y) → env_Forall2 Q Γ Σ.
Proof. induction 1; constructor; eauto. Qed.

Global Instance Esnoc_proper (P : relation A) :
  Proper (env_Forall2 P ==> (=) ==> P ==> env_Forall2 P) Esnoc.
Proof. intros Γ1 Γ2 HΓ i ? <-; by constructor. Qed.
Global Instance env_to_list_proper (P : relation A) :
  Proper (env_Forall2 P ==> Forall2 P) env_to_list.
Proof. induction 1; constructor; auto. Qed.

Lemma env_Forall2_fresh {B} (P : A → B → Prop) Γ Σ i :
  env_Forall2 P Γ Σ → Γ !! i = None → Σ !! i = None.
Proof. by induction 1; simplify. Qed.
Lemma env_Forall2_wf {B} (P : A → B → Prop) Γ Σ :
  env_Forall2 P Γ Σ → env_wf Γ → env_wf Σ.
Proof. induction 1; inversion_clear 1; eauto using env_Forall2_fresh. Qed.

Lemma env_subenv_fresh Γ Σ i : env_subenv Γ Σ → Σ !! i = None → Γ !! i = None.
Proof. by induction 1; simplify. Qed.
Lemma env_subenv_wf Γ Σ : env_subenv Γ Σ → env_wf Σ → env_wf Γ.
Proof. induction 1; inversion_clear 1; eauto using env_subenv_fresh. Qed.
Global Instance env_to_list_subenv_proper :
  Proper (env_subenv ==> sublist) (@env_to_list A).
Proof. induction 1; simpl; constructor; auto. Qed.
End env.

Record envs (PROP : bi) := Envs {
  env_intuitionistic : env PROP;
  env_spatial : env PROP;
  env_counter : positive (** A counter to generate fresh hypothesis names *)
}.
Add Printing Constructor envs.
Global Arguments Envs {_} _ _ _.
Global Arguments env_intuitionistic {_} _.
Global Arguments env_spatial {_} _.
Global Arguments env_counter {_} _.

(** We now define the judgment [envs_entails Δ Q] for proof mode entailments.
This judgment expresses that [Q] can be proved under the proof mode environment
[Δ]. To improve performance and to encapsulate the internals of the proof mode
(i.e. to ensure that tactics like [intro] cannot accidentally unfold the
entailment), we seal off [envs_entails].

The way the the definitions below are setup involves some trickery so we can
implement the [iFresh] tactic, which increases the counter [env_counter], in
an efficient way. Concretely, we made sure that [envs_entails (Envs Γp Γs c) Q]
and [envs_entails (Envs Γp Γs c') Q] are convertible for any [c] and [c']. This
way, [iFresh] can simply be implemented by changing the goal from
[envs_entails (Envs Γp Γs c) Q] into [envs_entails (Envs Γp Γs (Pos_succ c)) Q]
using the tactic [change_no_check]. This way, the generated proof term
contains no additional steps for changing the counter.

We first define a version [pre_envs_entails] that takes the two contexts
[env_intuitionistic] and [env_spatial] as its arguments. We seal this definition
and then lift it to take the whole proof mode context [Δ : envs PROP]. This is
crucial to make sure that the counter [env_counter] is not part of the seal. *)
Record envs_wf' {PROP : bi} (Γp Γs : env PROP) := {
  env_intuitionistic_valid : env_wf Γp;
  env_spatial_valid : env_wf Γs;
  envs_disjoint i : Γp !! i = None ∨ Γs !! i = None
}.
Definition envs_wf {PROP : bi} (Δ : envs PROP) :=
  envs_wf' (env_intuitionistic Δ) (env_spatial Δ).

Definition of_envs' {PROP : bi} (Γp Γs : env PROP) : PROP :=
  (⌜envs_wf' Γp Γs⌝ ∧ □ [∧] Γp ∗ [∗] Γs)%I.
Global Instance: Params (@of_envs') 1 := {}.
Definition of_envs {PROP : bi} (Δ : envs PROP) : PROP :=
  of_envs' (env_intuitionistic Δ) (env_spatial Δ).
Global Instance: Params (@of_envs) 1 := {}.
Global Arguments of_envs : simpl never.

Definition pre_envs_entails_def {PROP : bi} (Γp Γs : env PROP) (Q : PROP) :=
  of_envs' Γp Γs ⊢ Q.
Definition pre_envs_entails_aux : seal (@pre_envs_entails_def). Proof. by eexists. Qed.
Definition pre_envs_entails := pre_envs_entails_aux.(unseal).
Definition pre_envs_entails_eq : @pre_envs_entails = @pre_envs_entails_def :=
  pre_envs_entails_aux.(seal_eq).

Definition envs_entails {PROP : bi} (Δ : envs PROP) (Q : PROP) : Prop :=
  pre_envs_entails  PROP (env_intuitionistic Δ) (env_spatial Δ) Q.
Definition envs_entails_eq :
  @envs_entails = λ PROP (Δ : envs PROP) Q, (of_envs Δ ⊢ Q).
Proof. by rewrite /envs_entails pre_envs_entails_eq. Qed.
Global Arguments envs_entails {PROP} Δ Q%I.
Global Instance: Params (@envs_entails) 1 := {}.

Record envs_Forall2 {PROP : bi} (R : relation PROP) (Δ1 Δ2 : envs PROP) := {
  env_intuitionistic_Forall2 : env_Forall2 R (env_intuitionistic Δ1) (env_intuitionistic Δ2);
  env_spatial_Forall2 : env_Forall2 R (env_spatial Δ1) (env_spatial Δ2)
}.

Definition envs_dom {PROP} (Δ : envs PROP) : list ident :=
  env_dom (env_intuitionistic Δ) ++ env_dom (env_spatial Δ).

Definition envs_lookup {PROP} (i : ident) (Δ : envs PROP) : option (bool * PROP) :=
  let (Γp,Γs,n) := Δ in
  match env_lookup i Γp with
  | Some P => Some (true, P)
  | None => P ← env_lookup i Γs; Some (false, P)
  end.

Definition envs_delete {PROP} (remove_intuitionistic : bool)
    (i : ident) (p : bool) (Δ : envs PROP) : envs PROP :=
  let (Γp,Γs,n) := Δ in
  match p with
  | true => Envs (if remove_intuitionistic then env_delete i Γp else Γp) Γs n
  | false => Envs Γp (env_delete i Γs) n
  end.

Definition envs_lookup_delete {PROP} (remove_intuitionistic : bool)
    (i : ident) (Δ : envs PROP) : option (bool * PROP * envs PROP) :=
  let (Γp,Γs,n) := Δ in
  match env_lookup_delete i Γp with
  | Some (P,Γp') => Some (true, P, Envs (if remove_intuitionistic then Γp' else Γp) Γs n)
  | None => '(P,Γs') ← env_lookup_delete i Γs; Some (false, P, Envs Γp Γs' n)
  end.

Fixpoint envs_lookup_delete_list {PROP} (remove_intuitionistic : bool)
    (js : list ident) (Δ : envs PROP) : option (bool * list PROP * envs PROP) :=
  match js with
  | [] => Some (true, [], Δ)
  | j :: js =>
     '(p,P,Δ') ← envs_lookup_delete remove_intuitionistic j Δ;
     '(q,Ps,Δ'') ← envs_lookup_delete_list remove_intuitionistic js Δ';
     Some ((p:bool) &&& q, P :: Ps, Δ'')
  end.

Definition envs_snoc {PROP} (Δ : envs PROP)
    (p : bool) (j : ident) (P : PROP) : envs PROP :=
  let (Γp,Γs,n) := Δ in
  if p then Envs (Esnoc Γp j P) Γs n else Envs Γp (Esnoc Γs j P) n.

Definition envs_app {PROP : bi} (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs,n) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_app Γ Γp; Some (Envs Γp' Γs n)
  | false => _ ← env_app Γ Γp; Γs' ← env_app Γ Γs; Some (Envs Γp Γs' n)
  end.

Definition envs_simple_replace {PROP : bi} (i : ident) (p : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  let (Γp,Γs,n) := Δ in
  match p with
  | true => _ ← env_app Γ Γs; Γp' ← env_replace i Γ Γp; Some (Envs Γp' Γs n)
  | false => _ ← env_app Γ Γp; Γs' ← env_replace i Γ Γs; Some (Envs Γp Γs' n)
  end.

Definition envs_replace {PROP : bi} (i : ident) (p q : bool)
    (Γ : env PROP) (Δ : envs PROP) : option (envs PROP) :=
  if beq p q then envs_simple_replace i p Γ Δ
  else envs_app q Γ (envs_delete true i p Δ).

Definition env_spatial_is_nil {PROP} (Δ : envs PROP) : bool :=
  if env_spatial Δ is Enil then true else false.

Definition envs_clear_spatial {PROP} (Δ : envs PROP) : envs PROP :=
  Envs (env_intuitionistic Δ) Enil (env_counter Δ).

Definition envs_clear_intuitionistic {PROP} (Δ : envs PROP) : envs PROP :=
  Envs Enil (env_spatial Δ) (env_counter Δ).

Definition envs_incr_counter {PROP} (Δ : envs PROP) : envs PROP :=
  Envs (env_intuitionistic Δ) (env_spatial Δ) (Pos_succ (env_counter Δ)).

Fixpoint envs_split_go {PROP}
    (js : list ident) (Δ1 Δ2 : envs PROP) : option (envs PROP * envs PROP) :=
  match js with
  | [] => Some (Δ1, Δ2)
  | j :: js =>
     '(p,P,Δ1') ← envs_lookup_delete true j Δ1;
     if p : bool then envs_split_go js Δ1 Δ2 else
     envs_split_go js Δ1' (envs_snoc Δ2 false j P)
  end.
(* if [d = Right] then [result = (remaining hyps, hyps named js)] and
   if [d = Left] then [result = (hyps named js, remaining hyps)] *)
Definition envs_split {PROP} (d : direction)
    (js : list ident) (Δ : envs PROP) : option (envs PROP * envs PROP) :=
  '(Δ1,Δ2) ← envs_split_go js Δ (envs_clear_spatial Δ);
  if d is Right then Some (Δ1,Δ2) else Some (Δ2,Δ1).

Fixpoint env_to_prop_go {PROP : bi} (acc : PROP) (Γ : env PROP) : PROP :=
  match Γ with Enil => acc | Esnoc Γ _ P => env_to_prop_go (P ∗ acc)%I Γ end.
Definition env_to_prop {PROP : bi} (Γ : env PROP) : PROP :=
  match Γ with Enil => emp%I | Esnoc Γ _ P => env_to_prop_go P Γ end.

Fixpoint env_to_prop_and_go {PROP : bi} (acc : PROP) (Γ : env PROP) : PROP :=
  match Γ with Enil => acc | Esnoc Γ _ P => env_to_prop_and_go (P ∧ acc)%I Γ end.
Definition env_to_prop_and {PROP : bi} (Γ : env PROP) : PROP :=
  match Γ with Enil => True%I | Esnoc Γ _ P => env_to_prop_and_go P Γ end.

Section envs.
Context {PROP : bi}.
Implicit Types Γ Γp Γs : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

Lemma of_envs_eq Δ :
  of_envs Δ = (⌜envs_wf Δ⌝ ∧ □ [∧] env_intuitionistic Δ ∗ [∗] env_spatial Δ)%I.
Proof. done. Qed.
(** An environment is a ∗ of something intuitionistic and the spatial environment.
TODO: Can we define it as such? *)
Lemma of_envs_eq' Δ :
  of_envs Δ ⊣⊢ (⌜envs_wf Δ⌝ ∧ □ [∧] env_intuitionistic Δ) ∗ [∗] env_spatial Δ.
Proof. rewrite of_envs_eq persistent_and_sep_assoc //. Qed.

Global Instance envs_Forall2_refl (R : relation PROP) :
  Reflexive R → Reflexive (envs_Forall2 R).
Proof. by constructor. Qed.
Global Instance envs_Forall2_sym (R : relation PROP) :
  Symmetric R → Symmetric (envs_Forall2 R).
Proof. intros ??? [??]; by constructor. Qed.
Global Instance envs_Forall2_trans (R : relation PROP) :
  Transitive R → Transitive (envs_Forall2 R).
Proof. intros ??? [??] [??] [??]; constructor; etrans; eauto. Qed.
Global Instance envs_Forall2_antisymm (R R' : relation PROP) :
  AntiSymm R R' → AntiSymm (envs_Forall2 R) (envs_Forall2 R').
Proof. intros ??? [??] [??]; constructor; by eapply (anti_symm _). Qed.
Lemma envs_Forall2_impl (R R' : relation PROP) Δ1 Δ2 :
  envs_Forall2 R Δ1 Δ2 → (∀ P Q, R P Q → R' P Q) → envs_Forall2 R' Δ1 Δ2.
Proof. intros [??] ?; constructor; eauto using env_Forall2_impl. Qed.

Global Instance env_intuitionistic_mono :
  Proper (envs_Forall2 (⊢) ==> env_Forall2 (⊢)) (@env_intuitionistic PROP).
Proof. solve_proper. Qed.
Global Instance env_intuitionistic_flip_mono :
  Proper (flip (envs_Forall2 (⊢)) ==> flip (env_Forall2 (⊢))) (@env_intuitionistic PROP).
Proof. solve_proper. Qed.
Global Instance env_intuitionistic_proper :
  Proper (envs_Forall2 (⊣⊢) ==> env_Forall2 (⊣⊢)) (@env_intuitionistic PROP).
Proof. solve_proper. Qed.

Global Instance env_spatial_mono :
  Proper (envs_Forall2 (⊢) ==> env_Forall2 (⊢)) (@env_spatial PROP).
Proof. solve_proper. Qed.
Global Instance env_spatial_flip_mono :
  Proper (flip (envs_Forall2 (⊢)) ==> flip (env_Forall2 (⊢))) (@env_spatial PROP).
Proof. solve_proper. Qed.
Global Instance env_spatial_proper :
  Proper (envs_Forall2 (⊣⊢) ==> env_Forall2 (⊣⊢)) (@env_spatial PROP).
Proof. solve_proper. Qed.

Global Instance of_envs_mono' :
  Proper (env_Forall2 (⊢) ==> env_Forall2 (⊢) ==> (⊢)) (@of_envs' PROP).
Proof.
  intros Γp1 Γp2 Hp Γs1 Γs2 Hs; apply and_mono; simpl in *.
  - apply pure_mono=> -[???]. constructor;
      naive_solver eauto using env_Forall2_wf, env_Forall2_fresh.
  - by repeat f_equiv.
Qed.
Global Instance of_envs_proper' :
  Proper (env_Forall2 (⊣⊢) ==> env_Forall2 (⊣⊢) ==> (⊣⊢)) (@of_envs' PROP).
Proof.
  intros Γp1 Γp2 Hp Γs1 Γs2 Hs; apply (anti_symm (⊢)); apply of_envs_mono';
    eapply (env_Forall2_impl (⊣⊢)); by eauto using equiv_entails_1_1.
Qed.

Global Instance of_envs_mono : Proper (envs_Forall2 (⊢) ==> (⊢)) (@of_envs PROP).
Proof. solve_proper. Qed.
Global Instance of_envs_proper : Proper (envs_Forall2 (⊣⊢) ==> (⊣⊢)) (@of_envs PROP).
Proof. solve_proper. Qed.

Global Instance Envs_proper (R : relation PROP) :
  Proper (env_Forall2 R ==> env_Forall2 R ==> eq ==> envs_Forall2 R) (@Envs PROP).
Proof. by constructor. Qed.

Global Instance envs_entails_proper :
  Proper (envs_Forall2 (⊣⊢) ==> (⊣⊢) ==> iff) (@envs_entails PROP).
Proof. rewrite envs_entails_eq. solve_proper. Qed.
Global Instance envs_entails_mono :
  Proper (flip (envs_Forall2 (⊢)) ==> (⊢) ==> impl) (@envs_entails PROP).
Proof. rewrite envs_entails_eq=> Δ1 Δ2 ? P1 P2 <- <-. by f_equiv. Qed.
Global Instance envs_entails_flip_mono :
  Proper (envs_Forall2 (⊢) ==> flip (⊢) ==> flip impl) (@envs_entails PROP).
Proof. rewrite envs_entails_eq=> Δ1 Δ2 ? P1 P2 <- <-. by f_equiv. Qed.

Lemma envs_delete_intuitionistic Δ i : envs_delete false i true Δ = Δ.
Proof. by destruct Δ. Qed.
Lemma envs_delete_spatial Δ i :
  envs_delete false i false Δ = envs_delete true i false Δ.
Proof. by destruct Δ. Qed.

Lemma envs_lookup_delete_Some Δ Δ' rp i p P :
  envs_lookup_delete rp i Δ = Some (p,P,Δ')
  ↔ envs_lookup i Δ = Some (p,P) ∧ Δ' = envs_delete rp i p Δ.
Proof.
  rewrite /envs_lookup /envs_delete /envs_lookup_delete.
  destruct Δ as [Γp Γs]; rewrite /= !env_lookup_delete_correct.
  destruct (Γp !! i), (Γs !! i); naive_solver.
Qed.

Lemma envs_lookup_sound' Δ rp i p P :
  envs_lookup i Δ = Some (p,P) →
  of_envs Δ ⊢ □?p P ∗ of_envs (envs_delete rp i p Δ).
Proof.
  rewrite /envs_lookup /envs_delete !of_envs_eq=>?.
  apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - rewrite pure_True ?left_id; last (destruct Hwf, rp; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh).
    destruct rp.
    + rewrite (env_lookup_perm Γp) //= intuitionistically_and.
      by rewrite and_sep_intuitionistically -assoc.
    + rewrite {1}intuitionistically_sep_dup {1}(env_lookup_perm Γp) //=.
      by rewrite intuitionistically_and and_elim_l -assoc.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    rewrite pure_True ?left_id; last (destruct Hwf; constructor;
      naive_solver eauto using env_delete_wf, env_delete_fresh).
    rewrite (env_lookup_perm Γs) //=. by rewrite !assoc -(comm _ P).
Qed.
Lemma envs_lookup_sound Δ i p P :
  envs_lookup i Δ = Some (p,P) →
  of_envs Δ ⊢ □?p P ∗ of_envs (envs_delete true i p Δ).
Proof. apply envs_lookup_sound'. Qed.
Lemma envs_lookup_intuitionistic_sound Δ i P :
  envs_lookup i Δ = Some (true,P) → of_envs Δ ⊢ □ P ∗ of_envs Δ.
Proof. intros ?%(envs_lookup_sound' _ false). by destruct Δ. Qed.
Lemma envs_lookup_sound_2 Δ i p P :
  envs_wf Δ → envs_lookup i Δ = Some (p,P) →
  □?p P ∗ of_envs (envs_delete true i p Δ) ⊢ of_envs Δ.
Proof.
  rewrite /envs_lookup !of_envs_eq=>Hwf ?.
  rewrite [⌜envs_wf Δ⌝%I]pure_True // left_id.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?; simplify_eq/=.
  - by rewrite (env_lookup_perm Γp) //= intuitionistically_and
      and_sep_intuitionistically and_elim_r assoc.
  - destruct (Γs !! i) eqn:?; simplify_eq/=.
    by rewrite (env_lookup_perm Γs) //= and_elim_r !assoc (comm _ P).
Qed.

Lemma envs_lookup_split Δ i p P :
  envs_lookup i Δ = Some (p,P) → of_envs Δ ⊢ □?p P ∗ (□?p P -∗ of_envs Δ).
Proof.
  intros. apply pure_elim with (envs_wf Δ).
  { rewrite of_envs_eq. apply and_elim_l. }
  intros. rewrite {1}envs_lookup_sound//.
  apply sep_mono_r. apply wand_intro_l, envs_lookup_sound_2; done.
Qed.

Lemma envs_lookup_delete_sound Δ Δ' rp i p P :
  envs_lookup_delete rp i Δ = Some (p,P,Δ') → of_envs Δ ⊢ □?p P ∗ of_envs Δ'.
Proof. intros [? ->]%envs_lookup_delete_Some. by apply envs_lookup_sound'. Qed.

Lemma envs_lookup_delete_list_sound Δ Δ' rp js p Ps :
  envs_lookup_delete_list rp js Δ = Some (p,Ps,Δ') →
  of_envs Δ ⊢ □?p [∗] Ps ∗ of_envs Δ'.
Proof.
  revert Δ Δ' p Ps. induction js as [|j js IH]=> Δ Δ'' p Ps ?; simplify_eq/=.
  { by rewrite intuitionistically_emp left_id. }
  destruct (envs_lookup_delete rp j Δ) as [[[q1 P] Δ']|] eqn:Hj; simplify_eq/=.
  apply envs_lookup_delete_Some in Hj as [Hj ->].
  destruct (envs_lookup_delete_list _ js _) as [[[q2 Ps'] ?]|] eqn:?; simplify_eq/=.
  rewrite -intuitionistically_if_sep_2 -assoc.
  rewrite envs_lookup_sound' //; rewrite IH //.
  repeat apply sep_mono=>//; apply intuitionistically_if_flag_mono; by destruct q1.
Qed.

Lemma envs_lookup_delete_list_cons Δ Δ' Δ'' rp j js p1 p2 P Ps :
  envs_lookup_delete rp j Δ = Some (p1, P, Δ') →
  envs_lookup_delete_list rp js Δ' = Some (p2, Ps, Δ'') →
  envs_lookup_delete_list rp (j :: js) Δ = Some (p1 &&& p2, (P :: Ps), Δ'').
Proof. rewrite //= => -> //= -> //=. Qed.

Lemma envs_lookup_delete_list_nil Δ rp :
  envs_lookup_delete_list rp [] Δ = Some (true, [], Δ).
Proof. done. Qed.

Lemma envs_lookup_snoc Δ i p P :
  envs_lookup i Δ = None → envs_lookup i (envs_snoc Δ p i P) = Some (p, P).
Proof.
  rewrite /envs_lookup /envs_snoc=> ?.
  destruct Δ as [Γp Γs], p, (Γp !! i); simplify_eq; by rewrite env_lookup_snoc.
Qed.
Lemma envs_lookup_snoc_ne Δ i j p P :
  i ≠ j → envs_lookup i (envs_snoc Δ p j P) = envs_lookup i Δ.
Proof.
  rewrite /envs_lookup /envs_snoc=> ?.
  destruct Δ as [Γp Γs], p; simplify_eq; by rewrite env_lookup_snoc_ne.
Qed.

Lemma envs_snoc_sound Δ p i P :
  envs_lookup i Δ = None → of_envs Δ ⊢ □?p P -∗ of_envs (envs_snoc Δ p i P).
Proof.
  rewrite /envs_lookup /envs_snoc !of_envs_eq=> ?; apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], (Γp !! i) eqn:?, (Γs !! i) eqn:?; simplify_eq/=.
  apply wand_intro_l; destruct p; simpl.
  - apply and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (ident_beq_reflect j i); naive_solver.
    + by rewrite intuitionistically_and and_sep_intuitionistically assoc.
  - apply and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using Esnoc_wf.
      intros j; destruct (ident_beq_reflect j i); naive_solver.
    + by rewrite !assoc (comm _ P).
Qed.

Lemma envs_app_sound Δ Δ' p Γ :
  envs_app p Γ Δ = Some Δ' →
  of_envs Δ ⊢ (if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
Proof.
  rewrite !of_envs_eq /envs_app=> ?; apply pure_elim_l=> Hwf.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_app Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + rewrite (env_app_perm _ _ Γp') //.
      rewrite big_opL_app intuitionistically_and and_sep_intuitionistically.
      by rewrite assoc.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_app Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_app_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      naive_solver eauto using env_app_fresh.
    + by rewrite (env_app_perm _ _ Γs') // big_opL_app !assoc (comm _ ([∗] Γ)%I).
Qed.

Lemma envs_app_singleton_sound Δ Δ' p j Q :
  envs_app p (Esnoc Enil j Q) Δ = Some Δ' → of_envs Δ ⊢ □?p Q -∗ of_envs Δ'.
Proof. move=> /envs_app_sound. destruct p; by rewrite /= right_id. Qed.

Lemma envs_simple_replace_sound' Δ Δ' i p Γ :
  envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs (envs_delete true i p Δ) ⊢ (if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
Proof.
  rewrite /envs_simple_replace /envs_delete !of_envs_eq=> ?.
  apply pure_elim_l=> Hwf. destruct Δ as [Γp Γs], p; simplify_eq/=.
  - destruct (env_app Γ Γs) eqn:Happ,
      (env_replace i Γ Γp) as [Γp'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γp') //.
      rewrite big_opL_app intuitionistically_and and_sep_intuitionistically.
      by rewrite assoc.
  - destruct (env_app Γ Γp) eqn:Happ,
      (env_replace i Γ Γs) as [Γs'|] eqn:?; simplify_eq/=.
    apply wand_intro_l, and_intro; [apply pure_intro|].
    + destruct Hwf; constructor; simpl; eauto using env_replace_wf.
      intros j. apply (env_app_disjoint _ _ _ j) in Happ.
      destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh.
    + rewrite (env_replace_perm _ _ Γs') // big_opL_app.
      by rewrite !assoc (comm _ ([∗] Γ)%I).
Qed.

Lemma envs_simple_replace_singleton_sound' Δ Δ' i p j Q :
  envs_simple_replace i p (Esnoc Enil j Q) Δ = Some Δ' →
  of_envs (envs_delete true i p Δ) ⊢ □?p Q -∗ of_envs Δ'.
Proof. move=> /envs_simple_replace_sound'. destruct p; by rewrite /= right_id. Qed.

Lemma envs_simple_replace_sound Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ ((if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_simple_replace_sound'//. Qed.

Lemma envs_simple_replace_maybe_sound Δ Δ' i p P Γ :
  envs_lookup i Δ = Some (p,P) → envs_simple_replace i p Γ Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ (((if p then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ') ∧ (□?p P -∗ of_envs Δ)).
Proof.
  intros. apply pure_elim with (envs_wf Δ).
  { rewrite of_envs_eq. apply and_elim_l. }
  intros. rewrite {1}envs_lookup_sound//. apply sep_mono_r, and_intro.
  - rewrite envs_simple_replace_sound'//.
  - apply wand_intro_l, envs_lookup_sound_2; done.
Qed.

Lemma envs_simple_replace_singleton_sound Δ Δ' i p P j Q :
  envs_lookup i Δ = Some (p,P) →
  envs_simple_replace i p (Esnoc Enil j Q) Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ (□?p Q -∗ of_envs Δ').
Proof.
  intros. by rewrite envs_lookup_sound// envs_simple_replace_singleton_sound'//.
Qed.

Lemma envs_replace_sound' Δ Δ' i p q Γ :
  envs_replace i p q Γ Δ = Some Δ' →
  of_envs (envs_delete true i p Δ) ⊢ (if q then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ'.
Proof.
  rewrite /envs_replace; destruct (beq _ _) eqn:Hpq.
  - apply eqb_prop in Hpq as ->. apply envs_simple_replace_sound'.
  - apply envs_app_sound.
Qed.

Lemma envs_replace_singleton_sound' Δ Δ' i p q j Q :
  envs_replace i p q (Esnoc Enil j Q) Δ = Some Δ' →
  of_envs (envs_delete true i p Δ) ⊢ □?q Q -∗ of_envs Δ'.
Proof. move=> /envs_replace_sound'. destruct q; by rewrite /= ?right_id. Qed.

Lemma envs_replace_sound Δ Δ' i p q P Γ :
  envs_lookup i Δ = Some (p,P) → envs_replace i p q Γ Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ ((if q then □ [∧] Γ else [∗] Γ) -∗ of_envs Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_sound'//. Qed.

Lemma envs_replace_singleton_sound Δ Δ' i p q P j Q :
  envs_lookup i Δ = Some (p,P) →
  envs_replace i p q (Esnoc Enil j Q) Δ = Some Δ' →
  of_envs Δ ⊢ □?p P ∗ (□?q Q -∗ of_envs Δ').
Proof. intros. by rewrite envs_lookup_sound// envs_replace_singleton_sound'//. Qed.

Lemma envs_lookup_envs_clear_spatial Δ j :
  envs_lookup j (envs_clear_spatial Δ)
  = '(p,P) ← envs_lookup j Δ; if p : bool then Some (p,P) else None.
Proof.
  rewrite /envs_lookup /envs_clear_spatial.
  destruct Δ as [Γp Γs]; simpl; destruct (Γp !! j) eqn:?; simplify_eq/=; auto.
  by destruct (Γs !! j).
Qed.

Lemma envs_clear_spatial_sound Δ :
  of_envs Δ ⊢ of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ.
Proof.
  rewrite !of_envs_eq /envs_clear_spatial /=. apply pure_elim_l=> Hwf.
  rewrite right_id -persistent_and_sep_assoc. apply and_intro; [|done].
  apply pure_intro. destruct Hwf; constructor; simpl; auto using Enil_wf.
Qed.

Lemma env_spatial_is_nil_intuitionistically Δ :
  env_spatial_is_nil Δ = true → of_envs Δ ⊢ □ of_envs Δ.
Proof.
  intros. rewrite !of_envs_eq; destruct Δ as [? []]; simplify_eq/=.
  rewrite !right_id /bi_intuitionistically {1}affinely_and_r persistently_and.
  by rewrite persistently_affinely_elim persistently_idemp persistently_pure.
Qed.

Lemma envs_lookup_envs_delete Δ i p P :
  envs_wf Δ →
  envs_lookup i Δ = Some (p,P) → envs_lookup i (envs_delete true i p Δ) = None.
Proof.
  rewrite /envs_lookup /envs_delete=> -[?? Hdisj] Hlookup.
  destruct Δ as [Γp Γs], p; simplify_eq/=.
  - rewrite env_lookup_env_delete //. revert Hlookup.
    destruct (Hdisj i) as [->| ->]; [|done]. by destruct (Γs !! _).
  - rewrite env_lookup_env_delete //. by destruct (Γp !! _).
Qed.
Lemma envs_lookup_envs_delete_ne Δ rp i j p :
  i ≠ j → envs_lookup i (envs_delete rp j p Δ) = envs_lookup i Δ.
Proof.
  rewrite /envs_lookup /envs_delete=> ?. destruct Δ as [Γp Γs],p; simplify_eq/=.
  - destruct rp=> //. by rewrite env_lookup_env_delete_ne.
  - destruct (Γp !! i); simplify_eq/=; by rewrite ?env_lookup_env_delete_ne.
Qed.

Lemma envs_incr_counter_equiv Δ : envs_Forall2 (⊣⊢) Δ (envs_incr_counter Δ).
Proof. done. Qed.
Lemma envs_incr_counter_sound Δ : of_envs (envs_incr_counter Δ) ⊣⊢ of_envs Δ.
Proof. by f_equiv. Qed.

Lemma envs_split_go_sound js Δ1 Δ2 Δ1' Δ2' :
  (∀ j P, envs_lookup j Δ1 = Some (false, P) → envs_lookup j Δ2 = None) →
  envs_split_go js Δ1 Δ2 = Some (Δ1',Δ2') →
  of_envs Δ1 ∗ of_envs Δ2 ⊢ of_envs Δ1' ∗ of_envs Δ2'.
Proof.
  revert Δ1 Δ2.
  induction js as [|j js IH]=> Δ1 Δ2 Hlookup HΔ; simplify_eq/=; [done|].
  apply pure_elim with (envs_wf Δ1)=> [|Hwf].
  { by rewrite !of_envs_eq !and_elim_l sep_elim_l. }
  destruct (envs_lookup_delete _ j Δ1)
    as [[[[] P] Δ1'']|] eqn:Hdel; simplify_eq/=; auto.
  apply envs_lookup_delete_Some in Hdel as [??]; subst.
  rewrite envs_lookup_sound //; rewrite /= (comm _ P) -assoc.
  rewrite -(IH _ _ _ HΔ); last first.
   { intros j' P'; destruct (decide (j = j')) as [->|].
     - by rewrite (envs_lookup_envs_delete _ _ _ P).
     - rewrite envs_lookup_envs_delete_ne // envs_lookup_snoc_ne //. eauto. }
  rewrite (envs_snoc_sound Δ2 false j P) /= ?wand_elim_r; eauto.
Qed.
Lemma envs_split_sound Δ d js Δ1 Δ2 :
  envs_split d js Δ = Some (Δ1,Δ2) → of_envs Δ ⊢ of_envs Δ1 ∗ of_envs Δ2.
Proof.
  rewrite /envs_split=> ?. rewrite -(idemp bi_and (of_envs Δ)).
  rewrite {2}envs_clear_spatial_sound.
  rewrite (env_spatial_is_nil_intuitionistically (envs_clear_spatial _)) //.
  rewrite -persistently_and_intuitionistically_sep_l.
  rewrite (and_elim_l (<pers> _)%I)
          persistently_and_intuitionistically_sep_r intuitionistically_elim.
  destruct (envs_split_go _ _) as [[Δ1' Δ2']|] eqn:HΔ; [|done].
  apply envs_split_go_sound in HΔ as ->; last first.
  { intros j P. by rewrite envs_lookup_envs_clear_spatial=> ->. }
  destruct d; simplify_eq/=; [|done]. by rewrite comm.
Qed.

Lemma env_to_prop_sound Γ : env_to_prop Γ ⊣⊢ [∗] Γ.
Proof.
  destruct Γ as [|Γ i P]; simpl; first done.
  revert P. induction Γ as [|Γ IH ? Q]=>P; simpl.
  - by rewrite right_id.
  - rewrite /= IH (comm _ Q _) assoc. done.
Qed.

Lemma env_to_prop_and_sound Γ : env_to_prop_and Γ ⊣⊢ [∧] Γ.
Proof.
  destruct Γ as [|Γ i P]; simpl; first done.
  revert P. induction Γ as [|Γ IH ? Q]=>P; simpl.
  - by rewrite right_id.
  - rewrite /= IH (comm _ Q _) assoc. done.
Qed.
End envs.
