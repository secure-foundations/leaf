From iris.algebra Require Import functions gmap proofmode_classes.
From iris.proofmode Require Import classes.
From iris.base_logic.lib Require Export iprop.
From iris.prelude Require Import options.
Import uPred.

(** The class [inG Σ A] expresses that the CMRA [A] is in the list of functors
[Σ]. This class is similar to the [subG] class, but written down in terms of
individual CMRAs instead of (lists of) CMRA *functors*. This additional class is
needed because Coq is otherwise unable to solve type class constraints due to
higher-order unification problems. *)
Class inG (Σ : gFunctors) (A : cmra) := InG {
  inG_id : gid Σ;
  inG_apply := rFunctor_apply (gFunctors_lookup Σ inG_id);
  inG_prf : A = inG_apply (iPropO Σ) _;
}.
Global Arguments inG_id {_ _} _.
Global Arguments inG_apply {_ _} _ _ {_}.

(** We use the mode [-] for [Σ] since there is always a unique [Σ]. We use the
mode [!] for [A] since we can have multiple [inG]s for different [A]s, so we do
not want Coq to pick one arbitrarily. *)
Global Hint Mode inG - ! : typeclass_instances.

Lemma subG_inG Σ (F : gFunctor) : subG F Σ → inG Σ (rFunctor_apply F (iPropO Σ)).
Proof. move=> /(_ 0%fin) /= [j ->]. by exists j. Qed.

(** This tactic solves the usual obligations "subG ? Σ → {in,?}G ? Σ" *)
Ltac solve_inG :=
  (* Get all assumptions *)
  intros;
  (* Unfold the top-level xΣ. We need to support this to be a function. *)
  lazymatch goal with
  | H : subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _) _ |- _ => try unfold xΣ in H
  | H : subG ?xΣ _ |- _ => try unfold xΣ in H
  end;
  (* Take apart subG for non-"atomic" lists *)
  repeat match goal with
         | H : subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
         end;
  (* Try to turn singleton subG into inG; but also keep the subG for typeclass
     resolution -- to keep them, we put them onto the goal. *)
  repeat match goal with
         | H : subG _ _ |- _ => move:(H); (apply subG_inG in H || clear H)
         end;
  (* Again get all assumptions and simplify the functors *)
  intros; simpl in *;
  (* We support two kinds of goals: Things convertible to inG;
     and records with inG and typeclass fields. Try to solve the
     first case. *)
  try assumption;
  (* That didn't work, now we're in for the second case. *)
  split; (assumption || by apply _).

(** * Definition of the connective [own] *)
Local Definition inG_unfold {Σ A} {i : inG Σ A} :
    inG_apply i (iPropO Σ) -n> inG_apply i (iPrePropO Σ) :=
  rFunctor_map _ (iProp_fold, iProp_unfold).
Local Definition inG_fold {Σ A} {i : inG Σ A} :
    inG_apply i (iPrePropO Σ) -n> inG_apply i (iPropO Σ) :=
  rFunctor_map _ (iProp_unfold, iProp_fold).

Local Definition iRes_singleton {Σ A} {i : inG Σ A} (γ : gname) (a : A) : iResUR Σ :=
  discrete_fun_singleton (inG_id i)
    {[ γ := inG_unfold (cmra_transport inG_prf a) ]}.
Global Instance: Params (@iRes_singleton) 4 := {}.

Local Definition own_def `{!inG Σ A} (γ : gname) (a : A) : iProp Σ :=
  uPred_ownM (iRes_singleton γ a).
Local Definition own_aux : seal (@own_def). Proof. by eexists. Qed.
Definition own := own_aux.(unseal).
Global Arguments own {Σ A _} γ a.
Local Definition own_eq : @own = @own_def := own_aux.(seal_eq).
Local Instance: Params (@own) 4 := {}.

(** * Properties about ghost ownership *)
Section global.
Context `{i : !inG Σ A}.
Implicit Types a : A.

(** ** Properties of [iRes_singleton] *)
Local Lemma inG_unfold_fold (x : inG_apply i (iPrePropO Σ)) :
  inG_unfold (inG_fold x) ≡ x.
Proof.
  rewrite /inG_unfold /inG_fold -rFunctor_map_compose -{2}[x]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_unfold_fold.
Qed.
Local Lemma inG_fold_unfold (x : inG_apply i (iPropO Σ)) :
  inG_fold (inG_unfold x) ≡ x.
Proof.
  rewrite /inG_unfold /inG_fold -rFunctor_map_compose -{2}[x]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_fold_unfold.
Qed.
Local Lemma inG_unfold_validN n (x : inG_apply i (iPropO Σ)) :
  ✓{n} (inG_unfold x) ↔ ✓{n} x.
Proof.
  split; [|apply (cmra_morphism_validN _)].
  move=> /(cmra_morphism_validN inG_fold). by rewrite inG_fold_unfold.
Qed.

Local Instance iRes_singleton_ne γ : NonExpansive (@iRes_singleton Σ A _ γ).
Proof. by intros n a a' Ha; apply discrete_fun_singleton_ne; rewrite Ha. Qed.
Local Lemma iRes_singleton_validI γ a : ✓ (iRes_singleton γ a) ⊢@{iPropI Σ} ✓ a.
Proof.
  rewrite /iRes_singleton.
  rewrite discrete_fun_validI (forall_elim (inG_id i)) discrete_fun_lookup_singleton.
  rewrite singleton_validI.
  trans (✓ cmra_transport inG_prf a : iProp Σ)%I; last by destruct inG_prf.
  apply valid_entails=> n. apply inG_unfold_validN.
Qed.
Local Lemma iRes_singleton_op γ a1 a2 :
  iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2.
Proof.
  rewrite /iRes_singleton discrete_fun_singleton_op singleton_op cmra_transport_op.
  f_equiv. apply: singletonM_proper. apply (cmra_morphism_op _).
Qed.

Local Instance iRes_singleton_discrete γ a :
  Discrete a → Discrete (iRes_singleton γ a).
Proof.
  intros ?. rewrite /iRes_singleton.
  apply discrete_fun_singleton_discrete, gmap_singleton_discrete; [apply _|].
  intros x Hx. assert (cmra_transport inG_prf a ≡ inG_fold x) as Ha.
  { apply (discrete _). by rewrite -Hx inG_fold_unfold. }
  by rewrite Ha inG_unfold_fold.
Qed.
Local Instance iRes_singleton_core_id γ a :
  CoreId a → CoreId (iRes_singleton γ a).
Proof.
  intros. apply discrete_fun_singleton_core_id, gmap_singleton_core_id.
  by rewrite /CoreId -cmra_morphism_pcore core_id.
Qed.

Local Lemma later_internal_eq_iRes_singleton γ a r :
  ▷ (r ≡ iRes_singleton γ a) ⊢@{iPropI Σ}
  ◇ ∃ b r', r ≡ iRes_singleton γ b ⋅ r' ∧ ▷ (a ≡ b).
Proof.
  assert (NonExpansive (λ r : iResUR Σ, r (inG_id i) !! γ)).
  { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id i)). }
  rewrite (f_equivI (λ r : iResUR Σ, r (inG_id i) !! γ) r).
  rewrite {1}/iRes_singleton discrete_fun_lookup_singleton lookup_singleton.
  rewrite option_equivI. case Hb: (r (inG_id _) !! γ)=> [b|]; last first.
  { by rewrite /bi_except_0 -or_intro_l. }
  rewrite -except_0_intro.
  rewrite -(exist_intro (cmra_transport (eq_sym inG_prf) (inG_fold b))).
  rewrite -(exist_intro (discrete_fun_insert (inG_id _) (delete γ (r (inG_id i))) r)).
  apply and_intro.
  - apply equiv_internal_eq. rewrite /iRes_singleton.
    rewrite cmra_transport_trans eq_trans_sym_inv_l /=.
    intros i'. rewrite discrete_fun_lookup_op.
    destruct (decide (i' = inG_id i)) as [->|?].
    + rewrite discrete_fun_lookup_insert discrete_fun_lookup_singleton.
      intros γ'. rewrite lookup_op. destruct (decide (γ' = γ)) as [->|?].
      * by rewrite lookup_singleton lookup_delete Hb inG_unfold_fold.
      * by rewrite lookup_singleton_ne // lookup_delete_ne // left_id.
    + rewrite discrete_fun_lookup_insert_ne //.
      by rewrite discrete_fun_lookup_singleton_ne // left_id.
  - apply later_mono. rewrite (f_equivI inG_fold) inG_fold_unfold.
    apply: (internal_eq_rewrite' _ _ (λ b, a ≡ cmra_transport (eq_sym inG_prf) b)%I);
      [solve_proper|apply internal_eq_sym|].
    rewrite cmra_transport_trans eq_trans_sym_inv_r /=. apply internal_eq_refl.
Qed.

(** ** Properties of [own] *)
Global Instance own_ne γ : NonExpansive (@own Σ A _ γ).
Proof. rewrite !own_eq. solve_proper. Qed.
Global Instance own_proper γ :
  Proper ((≡) ==> (⊣⊢)) (@own Σ A _ γ) := ne_proper _.

Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
Proof. by rewrite !own_eq /own_def -ownM_op iRes_singleton_op. Qed.
Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
Proof. move=> [c ->]. by rewrite own_op sep_elim_l. Qed.

Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@own Σ A _ γ).
Proof. intros a1 a2. apply own_mono. Qed.

Lemma own_valid γ a : own γ a ⊢ ✓ a.
Proof. by rewrite !own_eq /own_def ownM_valid iRes_singleton_validI. Qed.
Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
Proof. apply wand_intro_r. by rewrite -own_op own_valid. Qed.
Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
Proof. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
Proof. by rewrite comm -own_valid_r. Qed.

Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
Proof. rewrite !own_eq /own_def. apply _. Qed.
Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
Proof. rewrite !own_eq /own_def; apply _. Qed.

Lemma later_own γ a : ▷ own γ a -∗ ◇ ∃ b, own γ b ∧ ▷ (a ≡ b).
Proof.
  rewrite own_eq /own_def later_ownM. apply exist_elim=> r.
  assert (NonExpansive (λ r : iResUR Σ, r (inG_id i) !! γ)).
  { intros n r1 r2 Hr. f_equiv. by specialize (Hr (inG_id i)). }
  rewrite internal_eq_sym later_internal_eq_iRes_singleton.
  rewrite (except_0_intro (uPred_ownM r)) -except_0_and. f_equiv.
  rewrite and_exist_l. f_equiv=> b. rewrite and_exist_l. apply exist_elim=> r'.
  rewrite assoc. apply and_mono_l.
  etrans; [|apply ownM_mono, (cmra_included_l _ r')].
  eapply (internal_eq_rewrite' _ _ uPred_ownM _); [apply and_elim_r|].
  apply and_elim_l.
Qed.

(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
  pred_infinite P →
  (∀ γ, P γ → ✓ (f γ)) →
  ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ (f γ).
Proof.
  intros HPinf Hf.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, P γ ∧ m = iRes_singleton γ (f γ)⌝ ∧ uPred_ownM m)%I).
  - rewrite /bi_emp_valid (ownM_unit emp).
    apply bupd_ownM_updateP, (discrete_fun_singleton_updateP_empty _ (λ m, ∃ γ,
      m = {[ γ := inG_unfold (cmra_transport inG_prf (f γ)) ]} ∧ P γ));
      [|naive_solver].
    apply (alloc_updateP_strong_dep _ P _ (λ γ,
      inG_unfold (cmra_transport inG_prf (f γ)))); [done| |naive_solver].
    intros γ _ ?.
    by apply (cmra_morphism_valid inG_unfold), cmra_transport_valid, Hf.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id.
Qed.
Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
  (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ (f γ).
Proof.
  intros Ha.
  apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
  apply (pred_infinite_set (C:=gset gname)).
  intros E. set (γ := fresh (G ∪ E)).
  exists γ. apply not_elem_of_union, is_fresh.
Qed.
Lemma own_alloc_dep (f : gname → A) :
  (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
Proof.
  intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
  apply bupd_mono, exist_mono=>?. apply: sep_elim_r.
Qed.

Lemma own_alloc_strong a (P : gname → Prop) :
  pred_infinite P →
  ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ own γ a.
Proof. intros HP Ha. eapply (own_alloc_strong_dep (λ _, a)); eauto. Qed.
Lemma own_alloc_cofinite a (G : gset gname) :
  ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ own γ a.
Proof. intros Ha. eapply (own_alloc_cofinite_dep (λ _, a)); eauto. Qed.
Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
Proof. intros Ha. eapply (own_alloc_dep (λ _, a)); eauto. Qed.

(** ** Frame preserving updates *)
Lemma own_updateP P γ a : a ~~>: P → own γ a ==∗ ∃ a', ⌜P a'⌝ ∗ own γ a'.
Proof.
  intros Hupd. rewrite !own_eq.
  rewrite -(bupd_mono (∃ m,
    ⌜ ∃ a', m = iRes_singleton γ a' ∧ P a' ⌝ ∧ uPred_ownM m)%I).
  - apply bupd_ownM_updateP, (discrete_fun_singleton_updateP _ (λ m, ∃ x,
      m = {[ γ := x ]} ∧ ∃ x',
      x = inG_unfold x' ∧ ∃ a',
      x' = cmra_transport inG_prf a' ∧ P a')); [|naive_solver].
    apply singleton_updateP', (iso_cmra_updateP' inG_fold).
    { apply inG_unfold_fold. }
    { apply (cmra_morphism_op _). }
    { apply inG_unfold_validN. }
    by apply cmra_transport_updateP'.
  - apply exist_elim=> m; apply pure_elim_l=> -[a' [-> HP]].
    rewrite -(exist_intro a'). rewrite -persistent_and_sep.
    by apply and_intro; [apply pure_intro|].
Qed.

Lemma own_update γ a a' : a ~~> a' → own γ a ==∗ own γ a'.
Proof.
  intros; rewrite (own_updateP (a' =.)); last by apply cmra_update_updateP.
  apply bupd_mono, exist_elim=> a''. rewrite sep_and. apply pure_elim_l=> -> //.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
Proof. intros. apply wand_intro_r. rewrite -own_op. by apply own_update. Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
Proof. intros. do 2 apply wand_intro_r. rewrite -!own_op. by apply own_update. Qed.
End global.

Global Arguments own_valid {_ _} [_] _ _.
Global Arguments own_valid_2 {_ _} [_] _ _ _.
Global Arguments own_valid_3 {_ _} [_] _ _ _ _.
Global Arguments own_valid_l {_ _} [_] _ _.
Global Arguments own_valid_r {_ _} [_] _ _.
Global Arguments own_updateP {_ _} [_] _ _ _ _.
Global Arguments own_update {_ _} [_] _ _ _ _.
Global Arguments own_update_2 {_ _} [_] _ _ _ _ _.
Global Arguments own_update_3 {_ _} [_] _ _ _ _ _ _.

Lemma own_unit A `{i : !inG Σ (A:ucmra)} γ : ⊢ |==> own γ (ε:A).
Proof.
  rewrite /bi_emp_valid (ownM_unit emp) !own_eq /own_def.
  apply bupd_ownM_update, discrete_fun_singleton_update_empty.
  apply (alloc_unit_singleton_update (inG_unfold (cmra_transport inG_prf ε))).
  - apply (cmra_morphism_valid _), cmra_transport_valid, ucmra_unit_valid.
  - intros x. rewrite -(inG_unfold_fold x) -(cmra_morphism_op inG_unfold).
    f_equiv. generalize (inG_fold x)=> x'.
    destruct inG_prf=> /=. by rewrite left_id.
  - done.
Qed.

(** Big op class instances *)
Section big_op_instances.
  Context `{!inG Σ (A:ucmra)}.

  Global Instance own_cmra_sep_homomorphism γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (own γ).
  Proof. split; try apply _. apply own_op. Qed.

  Lemma big_opL_own {B} γ (f : nat → B → A) (l : list B) :
    l ≠ [] →
    own γ ([^op list] k↦x ∈ l, f k x) ⊣⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (own γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_own_1 {B} γ (f : nat → B → A) (l : list B) :
    own γ ([^op list] k↦x ∈ l, f k x) ⊢ [∗ list] k↦x ∈ l, own γ (f k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_own_1 `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, own γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, own γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_own_1 `{Countable B} γ (g : B → A) (X : gmultiset B) :
    own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, own γ (g x).
  Proof. apply (big_opMS_commute _). Qed.
End big_op_instances.

(** Proofmode class instances *)
Section proofmode_instances.
  Context `{!inG Σ A}.
  Implicit Types a b : A.

  Global Instance into_sep_own γ a b1 b2 :
    IsOp a b1 b2 → IntoSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoSep (is_op a) own_op. Qed.
  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /IntoAnd (is_op a) own_op sep_and. Qed.

  Global Instance from_sep_own γ a b1 b2 :
    IsOp a b1 b2 → FromSep (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromSep -own_op -is_op. Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → TCOr (CoreId b1) (CoreId b2) →
    FromAnd (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hb. rewrite /FromAnd (is_op a) own_op.
    destruct Hb; by rewrite persistent_and_sep.
  Qed.
End proofmode_instances.
