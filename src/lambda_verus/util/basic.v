Require Export Equality FunctionalExtensionality.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import proofmode.

(** * Utility for Point-Free Style *)

Ltac fun_ext := apply functional_extensionality.
Ltac fun_ext_dep := apply functional_extensionality_dep.

Class SemiIso {A B} (f: A → B) (g: B → A) := semi_iso: g ∘ f = id.

Lemma semi_iso' {A B} f g `{!@SemiIso A B f g} x : g (f x) = x.
Proof. have ->: g (f x) = (g ∘ f) x by done. by rewrite semi_iso. Qed.

Class Iso {A B} (f: A → B) (g: B → A) :=
  { iso_semi_iso_l :> SemiIso f g; iso_semi_iso_r :> SemiIso g f }.

Global Instance iso_id {A} : Iso (@id A) id.
Proof. done. Qed.

Global Instance semi_iso_inj `{!@SemiIso A B f g} : Inj (=) (=) f | 100.
Proof. move=> ?? /(f_equal g). by rewrite !semi_iso'. Qed.

Lemma compose_assoc {A B C D} (f: A → B) g (h: C → D) : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. done. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).
Global Arguments s_comb {_ _ _} _ _ _ / : assert.
Global Typeclasses Transparent s_comb.

Class Inj3 {A B C D} (R1: relation A) (R2: relation B) (R3: relation C)
    (S: relation D) (f: A → B → C → D) : Prop :=
  inj3 x1 x2 x3 y1 y2 y3 :
    S (f x1 x2 x3) (f y1 y2 y3) → R1 x1 y1 ∧ R2 x2 y2 ∧ R3 x3 y3.

Global Arguments inj3 {_ _ _ _ _ _ _ _} _ {_} _ _ _ _ _ _ _ : assert.

(** * Utility for voidness *)

Global Instance Empty_set_empty: Empty Set := Empty_set.
Global Instance Empty_set_empty': Empty Type := Empty_set.

Class Void A := absurd: ∀{B}, A → B.

Global Instance Empty_set_void: Void ∅.
Proof. by move. Qed.
Global Instance False_void: Void False.
Proof. by move. Qed.

Global Instance fun_void `{!Inhabited A, !Void B} : Void (A → B).
Proof. move=> ? /(.$ inhabitant) ?. by apply absurd. Qed.

Global Instance void_iso `{!Void A, !Void B} : Iso absurd absurd.
Proof. split; fun_ext=> ?; by apply absurd. Qed.

(** * Utility for Iris *)

Notation big_sepL := (big_opL bi_sep) (only parsing).

(** * Utility for Natural Numbers *)

Lemma succ_le m n : S m ≤ n ↔ ∃n', n = S n' ∧ m ≤ n'.
Proof. split; [|case; lia]. move: n=> [|n']; [|exists n']; lia. Qed.

Global Instance eq_nat_sym : Symmetric eq_nat.
Proof. move=> ??. by rewrite !eq_nat_is_eq. Qed.

(** * Utility for Booleans *)

Lemma negb_andb b c : negb (b && c) = negb b || negb c.
Proof. by case b; case c. Qed.
Lemma negb_orb b c : negb (b || c) = negb b && negb c.
Proof. by case b; case c. Qed.
Lemma negb_negb_orb b c : negb (negb b || c) = b && negb c.
Proof. by case b; case c. Qed.

(** * Utility for Pairs *)

Lemma surjective_pairing_fun {A B C} (f: A → B * C) : f = pair ∘ (fst ∘ f) ⊛ (snd ∘ f).
Proof. fun_ext=> ?/=. by rewrite -surjective_pairing. Qed.

Definition prod_assoc {A B C} '(x, (y, z)) : (A * B) * C := ((x, y), z).
Definition prod_assoc' {A B C} '((x, y), z) : A * (B * C) := (x, (y, z)).
Global Instance prod_assoc_iso {A B C} : Iso (@prod_assoc A B C) prod_assoc'.
Proof. split; fun_ext; by [case=> [?[??]]|case=> [[??]?]]. Qed.

Definition prod_left_id {A} '((), x) : A := x.
Definition prod_left_id' {A} (x: A) := ((), x).
Global Instance prod_left_id_iso {A} : Iso (@prod_left_id A) prod_left_id'.
Proof. split; fun_ext; by [case=> [[]?]|]. Qed.

Definition prod_right_id {A} '(x, ()) : A := x.
Definition prod_right_id' {A} (x: A) := (x, ()).
Global Instance prod_right_id_iso {A} : Iso (@prod_right_id A) prod_right_id'.
Proof. split; fun_ext; by [case=> [?[]]|]. Qed.

(** * Utility for Lists *)

Lemma app_length_ex {A} (xl: list A) m n :
  length xl = m + n → ∃yl zl, xl = yl ++ zl ∧ length yl = m ∧ length zl = n.
Proof.
  move=> ?. exists (take m xl), (drop m xl).
  rewrite take_length drop_length take_drop. split; [done|lia].
Qed.

Lemma zip_fst_snd_fun {A B C} (f: C → list (A * B)) :
  zip ∘ (map fst ∘ f) ⊛ (map snd ∘ f) = f.
Proof. fun_ext=>/= ?. apply zip_fst_snd. Qed.

Definition llookup {A} (xl: list A) (i: fin (length xl)) : A :=
  list_to_vec xl !!! i.
Infix "!!ₗ" := llookup (at level 20, right associativity).

Definition lapply {A B} (fl: list (B → A)) (x: B) : list A := (.$ x) <$> fl.

Lemma lapply_app {A B} (fl gl: list (B → A)) x :
  lapply (fl ++ gl) x = lapply fl x ++ lapply gl x.
Proof. by elim fl; [done|]=>/= ??->. Qed.

(** Fixpoint version of [List.Forall: *)
Fixpoint lforall {A} (Φ: A → Prop) (xl: list A) : Prop :=
  match xl with [] => True | x :: xl' => Φ x ∧ lforall Φ xl' end.

Section forall2b. Context {A B} (f: A → B → bool).
Fixpoint forall2b (xl: list A) (yl: list B) :=
  match xl, yl with
  | [], [] => true
  | x :: xl', y :: yl' => f x y && forall2b xl' yl'
  | _, _ => false
  end.
End forall2b.

(** Option-returning version of [last] *)
Fixpoint last_error {A} (xl: list A) : option A :=
  match xl with [] => None | [x] => Some x | _ :: xl' => last_error xl' end.

(** * Utility for [fin] *)

Class IntoFin {n} (k: nat) (i: fin n) := into_fin: k = i.

Global Instance into_fin_0 {n} : @IntoFin (S n) 0 0%fin.
Proof. done. Qed.

Global Instance into_fin_S {n} k i : IntoFin k i → @IntoFin (S n) (S k) (FS i).
Proof. by move=> ->. Qed.

Fixpoint fin_renew {m n} : eq_nat m n → fin m → fin n :=
  match m, n with
  | 0, _ => λ _, fin_0_inv _
  | S _, 0 => absurd
  | S m', S n' => λ eq, fin_S_inv _ 0%fin (FS ∘ @fin_renew m' n' eq)
  end.

Lemma fin_to_nat_fin_renew {m n} (eq: eq_nat m n) i :
  fin_to_nat (fin_renew eq i) = i.
Proof.
  move: m n eq i. fix FIX 1. case=> [|?]; case=> [|?] ? i //=; inv_fin i=>//= ?.
  f_equal. apply FIX.
Qed.

Fixpoint big_sepN {PROP: bi} (n: nat) : (fin n → PROP) → PROP :=
  match n with
  | 0 => λ _, True
  | S m => λ Φ, Φ 0%fin ∗ big_sepN m (λ j, Φ (FS j))
  end%I.

Notation "[∗ nat] i < n , P" := (big_sepN n (λ i, P%I))
  (at level 200, n at level 10, i at level 1, right associativity,
    format "[∗  nat]  i  <  n ,  P") : bi_scope.

Lemma big_sepN_impl `{!BiAffine PROP} n (Φ Ψ: _ → PROP) :
  ([∗ nat] i < n, Φ i) -∗ □ (∀i, Φ i -∗ Ψ i) -∗ [∗ nat] i < n, Ψ i.
Proof.
  iIntros "All #In". iInduction n as [|] "IH"; [done|]=>/=.
  iDestruct "All" as "[Φ All]". iSplitL "Φ"; [by iApply "In"|].
  iApply "IH"; [|done]. iIntros "!>%". iApply "In".
Qed.
