From iris.algebra Require Import monoid.
From iris.bi Require Export derived_laws.
From iris.prelude Require Import options.

Module bi.
Import interface.bi.
Import derived_laws.bi.

Section later_derived.
Context {PROP : bi}.
Implicit Types φ : Prop.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.

(* Force implicit argument PROP *)
Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

Local Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim : core.
Local Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro : core.

Global Instance later_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_later PROP) := ne_proper _.

(* Later derived *)
Local Hint Resolve later_mono : core.
Global Instance later_mono' : Proper ((⊢) ==> (⊢)) (@bi_later PROP).
Proof. intros P Q; apply later_mono. Qed.
Global Instance later_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_later PROP).
Proof. intros P Q; apply later_mono. Qed.

Lemma later_True : ▷ True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using later_intro. Qed.
Lemma later_emp `{!BiAffine PROP} : ▷ emp ⊣⊢ emp.
Proof. by rewrite -True_emp later_True. Qed.
Lemma later_forall {A} (Φ : A → PROP) : (▷ ∀ a, Φ a) ⊣⊢ (∀ a, ▷ Φ a).
Proof.
  apply (anti_symm _); auto using later_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma later_exist_2 {A} (Φ : A → PROP) : (∃ a, ▷ Φ a) ⊢ ▷ (∃ a, Φ a).
Proof. apply exist_elim; eauto using exist_intro. Qed.
Lemma later_exist_except_0 {A} (Φ : A → PROP) : ▷ (∃ a, Φ a) ⊢ ◇ (∃ a, ▷ Φ a).
Proof. apply later_exist_false. Qed.
Lemma later_exist `{Inhabited A} (Φ : A → PROP) : ▷ (∃ a, Φ a) ⊣⊢ (∃ a, ▷ Φ a).
Proof.
  apply: anti_symm; [|apply later_exist_2].
  rewrite later_exist_false. apply or_elim; last done.
  rewrite -(exist_intro inhabitant); auto.
Qed.
Lemma later_and P Q : ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q.
Proof. rewrite !and_alt later_forall. by apply forall_proper=> -[]. Qed.
Lemma later_or P Q : ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
Proof. rewrite !or_alt later_exist. by apply exist_proper=> -[]. Qed.
Lemma later_impl P Q : ▷ (P → Q) ⊢ ▷ P → ▷ Q.
Proof. apply impl_intro_l. by rewrite -later_and impl_elim_r. Qed.
Lemma later_sep P Q : ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q.
Proof. apply (anti_symm _); auto using later_sep_1, later_sep_2. Qed.
Lemma later_wand P Q : ▷ (P -∗ Q) ⊢ ▷ P -∗ ▷ Q.
Proof. apply wand_intro_l. by rewrite -later_sep wand_elim_r. Qed.
Lemma later_iff P Q : ▷ (P ↔ Q) ⊢ ▷ P ↔ ▷ Q.
Proof. by rewrite /bi_iff later_and !later_impl. Qed.
Lemma later_persistently P : ▷ <pers> P ⊣⊢ <pers> ▷ P.
Proof. apply (anti_symm _); auto using later_persistently_1, later_persistently_2. Qed.
Lemma later_affinely_2 P : <affine> ▷ P ⊢ ▷ <affine> P.
Proof. rewrite /bi_affinely later_and. auto using later_intro. Qed.
Lemma later_intuitionistically_2 P : □ ▷ P ⊢ ▷ □ P.
Proof. by rewrite /bi_intuitionistically -later_persistently later_affinely_2. Qed.
Lemma later_intuitionistically_if_2 p P : □?p ▷ P ⊢ ▷ □?p P.
Proof. destruct p; simpl; auto using later_intuitionistically_2. Qed.
Lemma later_absorbingly P : ▷ <absorb> P ⊣⊢ <absorb> ▷ P.
Proof. by rewrite /bi_absorbingly later_sep later_True. Qed.

Lemma later_affinely `{!BiAffine PROP} P : ▷ <affine> P ⊣⊢ <affine> ▷ P.
Proof. by rewrite !affine_affinely. Qed.
Lemma later_intuitionistically `{!BiAffine PROP} P : ▷ □ P ⊣⊢ □ ▷ P.
Proof. by rewrite !intuitionistically_into_persistently later_persistently. Qed.
Lemma later_intuitionistically_if `{!BiAffine PROP} p P : ▷ □?p P ⊣⊢ □?p ▷ P.
Proof. destruct p; simpl; auto using later_intuitionistically. Qed.

Global Instance later_persistent P : Persistent P → Persistent (▷ P).
Proof. intros. by rewrite /Persistent -later_persistently {1}(persistent P). Qed.
Global Instance later_absorbing P : Absorbing P → Absorbing (▷ P).
Proof. intros ?. by rewrite /Absorbing -later_absorbingly absorbing. Qed.

(** * Alternatives to Löb induction *)
(** We prove relations between the following statements:

1. [Contractive (▷)], later is contractive as expressed by [BiLaterContractive].
2. [(▷ P ⊢ P) → (True ⊢ P)], the external/"weak" of Löb as expressed by [BiLöb].
3. [(▷ P → P) ⊢ P], the internal version/"strong" of Löb.
4. [□ (□ ▷ P -∗ P) ⊢ P], an internal version of Löb with magic wand instead of
   implication.
5. [□ (▷ P -∗ P) ⊢ P], a weaker version of the former statement, which does not
   make the induction hypothesis intuitionistic.

We prove that:

- (1) implies (2) in all BI logics (lemma [later_contractive_bi_löb]).
- (2) and (3) are logically equivalent in all BI logics (lemma [löb_alt_strong]).
- (2) implies (4) and (5) in all BI logics (lemmas [löb_wand_intuitionistically]
  and [löb_wand]).
- (5) and (2) are logically equivalent in affine BI logics (lemma [löb_alt_wand]).

In particular, this gives that (2), (3), (4) and (5) are logically equivalent in
affine BI logics such as Iris. *)

Lemma löb `{!BiLöb PROP} P : (▷ P → P) ⊢ P.
Proof.
  apply entails_impl_True, löb_weak. apply impl_intro_r.
  rewrite -{2}(idemp (∧) (▷ P → P))%I.
  rewrite {2}(later_intro (▷ P → P)).
  rewrite later_impl.
  rewrite assoc impl_elim_l.
  rewrite impl_elim_r. done.
Qed.

Lemma löb_alt_strong : BiLöb PROP ↔ ∀ P, (▷ P → P) ⊢ P.
Proof. split; intros HLöb P; [by apply löb|]. by intros ->%entails_impl_True. Qed.

(** Proof following https://en.wikipedia.org/wiki/L%C3%B6b's_theorem#Proof_of_L%C3%B6b's_theorem.
Their [Ψ] is called [Q] in our proof. *)
Global Instance later_contractive_bi_löb : BiLaterContractive PROP → BiLöb PROP.
Proof.
  intros=> P.
  pose (flöb_pre (P Q : PROP) := (▷ Q → P)%I).
  assert (∀ P, Contractive (flöb_pre P)) by solve_contractive.
  set (Q := fixpoint (flöb_pre P)).
  assert (Q ⊣⊢ (▷ Q → P)) as HQ by (exact: fixpoint_unfold).
  intros HP. rewrite -HP.
  assert (▷ Q ⊢ P) as HQP.
  { rewrite -HP. rewrite -(idemp (∧) (▷ Q))%I {2}(later_intro (▷ Q)).
    by rewrite {1}HQ {1}later_impl impl_elim_l. }
  rewrite -HQP HQ -2!later_intro.
  apply (entails_impl_True _ P). done.
Qed.

Lemma löb_wand_intuitionistically `{!BiLöb PROP} P : □ (□ ▷ P -∗ P) ⊢ P.
Proof.
  rewrite -{3}(intuitionistically_elim P) -(löb (□ P)). apply impl_intro_l.
  rewrite {1}intuitionistically_into_persistently_1 later_persistently.
  rewrite persistently_and_intuitionistically_sep_l.
  rewrite -{1}(intuitionistically_idemp (▷ P)) intuitionistically_sep_2.
  by rewrite wand_elim_r.
Qed.
Lemma löb_wand `{!BiLöb PROP} P : □ (▷ P -∗ P) ⊢ P.
Proof.
  by rewrite -(intuitionistically_elim (▷ P)) löb_wand_intuitionistically.
Qed.

(** The proof of the right-to-left direction relies on the BI being affine. It
is unclear how to generalize the lemma or proof to support non-affine BIs. *)
Lemma löb_alt_wand `{!BiAffine PROP} : BiLöb PROP ↔ ∀ P, □ (▷ P -∗ P) ⊢ P.
Proof.
  split; intros Hlöb; [by apply löb_wand|].
  apply löb_alt_strong=> P.
  rewrite bi.impl_alt. apply bi.exist_elim=> R. apply impl_elim_r'.
  rewrite -(Hlöb (R → P)%I) -intuitionistically_into_persistently.
  apply intuitionistically_intro', wand_intro_l, impl_intro_l.
  rewrite -persistently_and_intuitionistically_sep_r assoc
    persistently_and_intuitionistically_sep_r intuitionistically_elim.
  rewrite -{1}(idemp bi_and R) -(assoc _ R) {2}(later_intro R).
  by rewrite -later_and impl_elim_r (comm _ R) wand_elim_r.
Qed.

(** A funny consequence of Löb induction.
This shows that Löb induction is incompatible with classical logic.
See [lib/counterexamples.v] for a fully worked-out proof of that fact. *)
Lemma not_not_later_False `{!BiLöb PROP} : ⊢@{PROP} ¬ ¬ ▷ False.
Proof. apply entails_impl, löb. Qed.

(* Iterated later modality *)
Global Instance laterN_ne m : NonExpansive (@bi_laterN PROP m).
Proof. induction m; simpl; [by intros ???|]. solve_proper. Qed.
Global Instance laterN_proper m :
  Proper ((⊣⊢) ==> (⊣⊢)) (@bi_laterN PROP m) := ne_proper _.

Lemma laterN_0 P : ▷^0 P ⊣⊢ P.
Proof. done. Qed.
Lemma later_laterN n P : ▷^(S n) P ⊣⊢ ▷ ▷^n P.
Proof. done. Qed.
Lemma laterN_later n P : ▷^(S n) P ⊣⊢ ▷^n ▷ P.
Proof. induction n; f_equiv/=; auto. Qed.
Lemma laterN_plus n1 n2 P : ▷^(n1 + n2) P ⊣⊢ ▷^n1 ▷^n2 P.
Proof. induction n1; f_equiv/=; auto. Qed.
Lemma laterN_le n1 n2 P : n1 ≤ n2 → ▷^n1 P ⊢ ▷^n2 P.
Proof. induction 1; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_iter n P : (▷^n P)%I = Nat.iter n bi_later P.
Proof. induction n; f_equal/=; auto. Qed.

Lemma laterN_mono n P Q : (P ⊢ Q) → ▷^n P ⊢ ▷^n Q.
Proof. induction n; simpl; auto. Qed.
Global Instance laterN_mono' n : Proper ((⊢) ==> (⊢)) (@bi_laterN PROP n).
Proof. intros P Q; apply laterN_mono. Qed.
Global Instance laterN_flip_mono' n :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_laterN PROP n).
Proof. intros P Q; apply laterN_mono. Qed.

Lemma laterN_intro n P : P ⊢ ▷^n P.
Proof. induction n as [|n IH]; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_True n : ▷^n True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using laterN_intro, True_intro. Qed.
Lemma laterN_emp `{!BiAffine PROP} n : ▷^n emp ⊣⊢ emp.
Proof. by rewrite -True_emp laterN_True. Qed.
Lemma laterN_forall {A} n (Φ : A → PROP) : (▷^n ∀ a, Φ a) ⊣⊢ (∀ a, ▷^n Φ a).
Proof. induction n as [|n IH]; simpl; rewrite -?later_forall ?IH; auto. Qed.
Lemma laterN_exist_2 {A} n (Φ : A → PROP) : (∃ a, ▷^n Φ a) ⊢ ▷^n (∃ a, Φ a).
Proof. apply exist_elim; eauto using exist_intro, laterN_mono. Qed.
Lemma laterN_exist `{Inhabited A} n (Φ : A → PROP) :
  (▷^n ∃ a, Φ a) ⊣⊢ ∃ a, ▷^n Φ a.
Proof. induction n as [|n IH]; simpl; rewrite -?later_exist ?IH; auto. Qed.
Lemma laterN_and n P Q : ▷^n (P ∧ Q) ⊣⊢ ▷^n P ∧ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_and ?IH; auto. Qed.
Lemma laterN_or n P Q : ▷^n (P ∨ Q) ⊣⊢ ▷^n P ∨ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_or ?IH; auto. Qed.
Lemma laterN_impl n P Q : ▷^n (P → Q) ⊢ ▷^n P → ▷^n Q.
Proof. apply impl_intro_l. by rewrite -laterN_and impl_elim_r. Qed.
Lemma laterN_sep n P Q : ▷^n (P ∗ Q) ⊣⊢ ▷^n P ∗ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_sep ?IH; auto. Qed.
Lemma laterN_wand n P Q : ▷^n (P -∗ Q) ⊢ ▷^n P -∗ ▷^n Q.
Proof. apply wand_intro_l. by rewrite -laterN_sep wand_elim_r. Qed.
Lemma laterN_iff n P Q : ▷^n (P ↔ Q) ⊢ ▷^n P ↔ ▷^n Q.
Proof. by rewrite /bi_iff laterN_and !laterN_impl. Qed.
Lemma laterN_persistently n P : ▷^n <pers> P ⊣⊢ <pers> ▷^n P.
Proof. induction n as [|n IH]; simpl; auto. by rewrite IH later_persistently. Qed.
Lemma laterN_affinely_2 n P : <affine> ▷^n P ⊢ ▷^n <affine> P.
Proof. rewrite /bi_affinely laterN_and. auto using laterN_intro. Qed.
Lemma laterN_intuitionistically_2 n P : □ ▷^n P ⊢ ▷^n □ P.
Proof. by rewrite /bi_intuitionistically -laterN_persistently laterN_affinely_2. Qed.
Lemma laterN_intuitionistically_if_2 n p P : □?p ▷^n P ⊢ ▷^n □?p P.
Proof. destruct p; simpl; auto using laterN_intuitionistically_2. Qed.
Lemma laterN_absorbingly n P : ▷^n <absorb> P ⊣⊢ <absorb> ▷^n P.
Proof. by rewrite /bi_absorbingly laterN_sep laterN_True. Qed.

Global Instance laterN_persistent n P : Persistent P → Persistent (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance laterN_absorbing n P : Absorbing P → Absorbing (▷^n P).
Proof. induction n; apply _. Qed.

(* Except-0 *)
Global Instance except_0_ne : NonExpansive (@bi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@bi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_mono' : Proper ((⊢) ==> (⊢)) (@bi_except_0 PROP).
Proof. solve_proper. Qed.
Global Instance except_0_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@bi_except_0 PROP).
Proof. solve_proper. Qed.

Lemma except_0_intro P : P ⊢ ◇ P.
Proof. rewrite /bi_except_0; auto. Qed.
Lemma except_0_mono P Q : (P ⊢ Q) → ◇ P ⊢ ◇ Q.
Proof. by intros ->. Qed.
Lemma except_0_idemp P : ◇ ◇ P ⊣⊢ ◇ P.
Proof. apply (anti_symm _); rewrite /bi_except_0; auto. Qed.

Lemma except_0_True : ◇ True ⊣⊢ True.
Proof. rewrite /bi_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_emp `{!BiAffine PROP} : ◇ emp ⊣⊢ emp.
Proof. by rewrite -True_emp except_0_True. Qed.
Lemma except_0_or P Q : ◇ (P ∨ Q) ⊣⊢ ◇ P ∨ ◇ Q.
Proof. rewrite /bi_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_and P Q : ◇ (P ∧ Q) ⊣⊢ ◇ P ∧ ◇ Q.
Proof. by rewrite /bi_except_0 or_and_l. Qed.
Lemma except_0_sep P Q : ◇ (P ∗ Q) ⊣⊢ ◇ P ∗ ◇ Q.
Proof.
  rewrite /bi_except_0. apply (anti_symm _).
  - apply or_elim; last by auto using sep_mono.
    by rewrite -!or_intro_l -persistently_pure -later_sep -persistently_sep_dup.
  - rewrite sep_or_r !sep_or_l {1}(later_intro P) {1}(later_intro Q).
    rewrite -!later_sep !left_absorb right_absorb. auto.
Qed.
Lemma except_0_forall {A} (Φ : A → PROP) : ◇ (∀ a, Φ a) ⊣⊢ ∀ a, ◇ Φ a.
Proof.
  apply (anti_symm _).
  { apply forall_intro=> a. by rewrite (forall_elim a). }
  trans (▷ (∀ a : A, Φ a) ∧ (∀ a : A, ◇ Φ a))%I.
  { apply and_intro, reflexivity. rewrite later_forall. apply forall_mono=> a.
    apply or_elim; auto using later_intro. }
  rewrite later_false_em and_or_r. apply or_elim.
  { rewrite and_elim_l. apply or_intro_l. }
  apply or_intro_r', forall_intro=> a. rewrite !(forall_elim a).
  by rewrite and_or_l impl_elim_l and_elim_r idemp.
Qed.
Lemma except_0_exist_2 {A} (Φ : A → PROP) : (∃ a, ◇ Φ a) ⊢ ◇ ∃ a, Φ a.
Proof. apply exist_elim=> a. by rewrite (exist_intro a). Qed.
Lemma except_0_exist `{Inhabited A} (Φ : A → PROP) :
  ◇ (∃ a, Φ a) ⊣⊢ (∃ a, ◇ Φ a).
Proof.
  apply (anti_symm _); [|by apply except_0_exist_2]. apply or_elim.
  - rewrite -(exist_intro inhabitant). by apply or_intro_l.
  - apply exist_mono=> a. apply except_0_intro.
Qed.
Lemma except_0_later P : ◇ ▷ P ⊢ ▷ P.
Proof. by rewrite /bi_except_0 -later_or False_or. Qed.
Lemma except_0_laterN n P : ◇ ▷^n P ⊢ ▷^n ◇ P.
Proof. by destruct n as [|n]; rewrite //= ?except_0_later -except_0_intro. Qed.
Lemma except_0_into_later P : ◇ P ⊢ ▷ P.
Proof. by rewrite -except_0_later -later_intro. Qed.
Lemma except_0_persistently P : ◇ <pers> P ⊣⊢ <pers> ◇ P.
Proof.
  by rewrite /bi_except_0 persistently_or -later_persistently persistently_pure.
Qed.
Lemma except_0_affinely_2 P : <affine> ◇ P ⊢ ◇ <affine> P.
Proof. rewrite /bi_affinely except_0_and. auto using except_0_intro. Qed.
Lemma except_0_intuitionistically_2 P : □ ◇ P ⊢ ◇ □ P.
Proof. by rewrite /bi_intuitionistically -except_0_persistently except_0_affinely_2. Qed.
Lemma except_0_intuitionistically_if_2 p P : □?p ◇ P ⊢ ◇ □?p P.
Proof. destruct p; simpl; auto using except_0_intuitionistically_2. Qed.
Lemma except_0_absorbingly P : ◇ <absorb> P ⊣⊢ <absorb> ◇ P.
Proof. by rewrite /bi_absorbingly except_0_sep except_0_True. Qed.

Lemma except_0_frame_l P Q : P ∗ ◇ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro P) except_0_sep. Qed.
Lemma except_0_frame_r P Q : ◇ P ∗ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro Q) except_0_sep. Qed.

Lemma later_affinely_1 `{!Timeless (PROP:=PROP) emp} P : ▷ <affine> P ⊢ ◇ <affine> ▷ P.
Proof.
  rewrite /bi_affinely later_and (timeless emp) except_0_and.
  by apply and_mono, except_0_intro.
Qed.

Global Instance except_0_persistent P : Persistent P → Persistent (◇ P).
Proof. rewrite /bi_except_0; apply _. Qed.
Global Instance except_0_absorbing P : Absorbing P → Absorbing (◇ P).
Proof. rewrite /bi_except_0; apply _. Qed.

(* Timeless instances *)
Global Instance Timeless_proper : Proper ((≡) ==> iff) (@Timeless PROP).
Proof. solve_proper. Qed.

Global Instance pure_timeless φ : Timeless (PROP:=PROP) ⌜φ⌝.
Proof.
  rewrite /Timeless /bi_except_0 pure_alt later_exist_false.
  apply or_elim, exist_elim; [auto|]=> Hφ. rewrite -(exist_intro Hφ). auto.
Qed.
Global Instance emp_timeless `{BiAffine PROP} : Timeless (PROP:=PROP) emp.
Proof. rewrite -True_emp. apply _. Qed.

Global Instance and_timeless P Q : Timeless P → Timeless Q → Timeless (P ∧ Q).
Proof. intros; rewrite /Timeless except_0_and later_and; auto. Qed.
Global Instance or_timeless P Q : Timeless P → Timeless Q → Timeless (P ∨ Q).
Proof. intros; rewrite /Timeless except_0_or later_or; auto. Qed.

Global Instance impl_timeless `{!BiLöb PROP} P Q : Timeless Q → Timeless (P → Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_em.
  apply or_mono, impl_intro_l; first done.
  rewrite -{2}(löb Q). apply impl_intro_l.
  rewrite HQ /bi_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite assoc (comm _ _ P) -assoc !impl_elim_r.
Qed.
Global Instance sep_timeless P Q: Timeless P → Timeless Q → Timeless (P ∗ Q).
Proof.
  intros; rewrite /Timeless except_0_sep later_sep; auto using sep_mono.
Qed.

Global Instance wand_timeless `{!BiLöb PROP} P Q : Timeless Q → Timeless (P -∗ Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_em.
  apply or_mono, wand_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /bi_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite (comm _ P) persistent_and_sep_assoc impl_elim_r wand_elim_l.
Qed.
Global Instance forall_timeless {A} (Ψ : A → PROP) :
  (∀ x, Timeless (Ψ x)) → Timeless (∀ x, Ψ x).
Proof.
  rewrite /Timeless=> HQ. rewrite except_0_forall later_forall.
  apply forall_mono; auto.
Qed.
Global Instance exist_timeless {A} (Ψ : A → PROP) :
  (∀ x, Timeless (Ψ x)) → Timeless (∃ x, Ψ x).
Proof.
  rewrite /Timeless=> ?. rewrite later_exist_false. apply or_elim.
  - rewrite /bi_except_0; auto.
  - apply exist_elim=> x. rewrite -(exist_intro x); auto.
Qed.
Global Instance persistently_timeless P : Timeless P → Timeless (<pers> P).
Proof.
  intros. rewrite /Timeless /bi_except_0 later_persistently_1.
  by rewrite (timeless P) /bi_except_0 persistently_or {1}persistently_elim.
Qed.

Global Instance affinely_timeless P :
  Timeless (PROP:=PROP) emp → Timeless P → Timeless (<affine> P).
Proof. rewrite /bi_affinely; apply _. Qed.
Global Instance absorbingly_timeless P : Timeless P → Timeless (<absorb> P).
Proof. rewrite /bi_absorbingly; apply _. Qed.

Global Instance intuitionistically_timeless P :
  Timeless (PROP:=PROP) emp → Timeless P → Timeless (□ P).
Proof. rewrite /bi_intuitionistically; apply _. Qed.

Global Instance from_option_timeless {A} P (Ψ : A → PROP) (mx : option A) :
  (∀ x, Timeless (Ψ x)) → Timeless P → Timeless (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Big op stuff *)
Global Instance bi_later_monoid_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_later PROP).
Proof.
  split; [split|]; try apply _.
  - apply later_and.
  - apply later_True.
Qed.
Global Instance bi_laterN_and_homomorphism n :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_laterN PROP n).
Proof.
  split; [split|]; try apply _.
  - apply laterN_and.
  - apply laterN_True.
Qed.
Global Instance bi_except_0_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@bi_except_0 PROP).
Proof.
  split; [split|]; try apply _.
  - apply except_0_and.
  - apply except_0_True.
Qed.

Global Instance bi_later_monoid_or_homomorphism :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@bi_later PROP).
Proof. split; try apply _. apply later_or. Qed.
Global Instance bi_laterN_or_homomorphism n :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_or. Qed.
Global Instance bi_except_0_or_homomorphism :
  WeakMonoidHomomorphism bi_or bi_or (≡) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_or. Qed.

Global Instance bi_later_monoid_sep_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_later PROP).
Proof. split; try apply _. apply later_sep. Qed.
Global Instance bi_laterN_sep_weak_homomorphism n :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_sep. Qed.
Global Instance bi_except_0_sep_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (≡) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_sep. Qed.

Global Instance bi_later_monoid_sep_homomorphism `{!BiAffine PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_later PROP).
Proof. split; try apply _. apply later_emp. Qed.
Global Instance bi_laterN_sep_homomorphism `{!BiAffine PROP} n :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_emp. Qed.
Global Instance bi_except_0_sep_homomorphism `{!BiAffine PROP} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_emp. Qed.

Global Instance bi_later_monoid_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_later PROP).
Proof. split; try apply _. intros P Q. by rewrite later_sep. Qed.
Global Instance bi_laterN_sep_entails_weak_homomorphism n :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_laterN PROP n).
Proof. split; try apply _. intros P Q. by rewrite laterN_sep. Qed.
Global Instance bi_except_0_sep_entails_weak_homomorphism :
  WeakMonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_except_0 PROP).
Proof. split; try apply _. intros P Q. by rewrite except_0_sep. Qed.

Global Instance bi_later_monoid_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_later PROP).
Proof. split; try apply _. apply later_intro. Qed.
Global Instance bi_laterN_sep_entails_homomorphism n :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_laterN PROP n).
Proof. split; try apply _. apply laterN_intro. Qed.
Global Instance bi_except_0_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@bi_except_0 PROP).
Proof. split; try apply _. apply except_0_intro. Qed.
End later_derived.
End bi.
