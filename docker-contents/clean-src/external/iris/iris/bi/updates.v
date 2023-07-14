From stdpp Require Import coPset.
From iris.bi Require Import interface derived_laws_later big_op plainly.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.

(* The sections add extra BI assumptions, which is only picked up with "Type"*. *)
Set Default Proof Using "Type*".

(* We first define operational type classes for the notations, and then later
bundle these operational type classes with the laws. *)
Class BUpd (PROP : Type) : Type := bupd : PROP → PROP.
Global Instance : Params (@bupd) 2 := {}.
Global Hint Mode BUpd ! : typeclass_instances.
Global Arguments bupd {_}%type_scope {_} _%bi_scope.

Notation "|==> Q" := (bupd Q) : bi_scope.
Notation "P ==∗ Q" := (P ⊢ |==> Q) (only parsing) : stdpp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I : bi_scope.

Class FUpd (PROP : Type) : Type := fupd : coPset → coPset → PROP → PROP.
Global Instance: Params (@fupd) 4 := {}.
Global Hint Mode FUpd ! : typeclass_instances.
Global Arguments fupd {_}%type_scope {_} _ _ _%bi_scope.

Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q) : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)%I : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q) : stdpp_scope.

Notation "|={ E }=> Q" := (fupd E E Q) : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%I : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q) : stdpp_scope.

(** * Step-taking fancy updates. *)
(** These have two masks, but they are different than the two masks of a
    mask-changing update: in [|={Eo}[Ei]▷=> Q], the first mask [Eo] ("outer
    mask") holds at the beginning and the end; the second mask [Ei] ("inner
    mask") holds around each ▷. This is also why we use a different notation
    than for the two masks of a mask-changing updates. *)
Notation "|={ Eo } [ Ei ]▷=> Q" := (|={Eo,Ei}=> ▷ |={Ei,Eo}=> Q)%I : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗ Q" := (P -∗ |={Eo}[Ei]▷=> Q)%I : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗ Q" := (P -∗ |={Eo}[Ei]▷=> Q) (only parsing) : stdpp_scope.

Notation "|={ E }▷=> Q" := (|={E}[E]▷=> Q)%I : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E}[E]▷=∗ Q)%I : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E}[E]▷=∗ Q) : stdpp_scope.

(** For the iterated version, in principle there are 4 masks: "outer" and
    "inner" of [|={Eo}[Ei]▷=>], as well as "begin" and "end" masks [E1] and [E2]
    that could potentially differ from [Eo]. The latter can be obtained from
    this notation by adding normal mask-changing update modalities: [
    |={E1,Eo}=> |={Eo}[Ei]▷=>^n |={Eo,E2}=> Q] *)
Notation "|={ Eo } [ Ei ]▷=>^ n Q" := (Nat.iter n (λ P, |={Eo}[Ei]▷=> P) Q)%I : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗^ n Q" := (P -∗ |={Eo}[Ei]▷=>^n Q)%I : bi_scope.
Notation "P ={ Eo } [ Ei ]▷=∗^ n Q" := (P -∗ |={Eo}[Ei]▷=>^n Q) (only parsing) : stdpp_scope.

Notation "|={ E }▷=>^ n Q" := (|={E}[E]▷=>^n Q)%I : bi_scope.
Notation "P ={ E }▷=∗^ n Q" := (P ={E}[E]▷=∗^n Q)%I : bi_scope.
Notation "P ={ E }▷=∗^ n Q" := (P ={E}[E]▷=∗^n Q) (only parsing) : stdpp_scope.

(** Bundled versions  *)
(* Mixins allow us to create instances easily without having to use Program *)
Record BiBUpdMixin (PROP : bi) `(BUpd PROP) := {
  bi_bupd_mixin_bupd_ne : NonExpansive (bupd (PROP:=PROP));
  bi_bupd_mixin_bupd_intro (P : PROP) : P ==∗ P;
  bi_bupd_mixin_bupd_mono (P Q : PROP) : (P ⊢ Q) → (|==> P) ==∗ Q;
  bi_bupd_mixin_bupd_trans (P : PROP) : (|==> |==> P) ==∗ P;
  bi_bupd_mixin_bupd_frame_r (P R : PROP) : (|==> P) ∗ R ==∗ P ∗ R;
}.

Record BiFUpdMixin (PROP : bi) `(FUpd PROP) := {
  bi_fupd_mixin_fupd_ne E1 E2 :
    NonExpansive (fupd (PROP:=PROP) E1 E2);
  bi_fupd_mixin_fupd_mask_subseteq E1 E2 :
    E2 ⊆ E1 → ⊢@{PROP} |={E1,E2}=> |={E2,E1}=> emp;
  bi_fupd_mixin_except_0_fupd E1 E2 (P : PROP) :
    ◇ (|={E1,E2}=> P) ={E1,E2}=∗ P;
  bi_fupd_mixin_fupd_mono E1 E2 (P Q : PROP) :
    (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q;
  bi_fupd_mixin_fupd_trans E1 E2 E3 (P : PROP) :
    (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P;
  bi_fupd_mixin_fupd_mask_frame_r' E1 E2 Ef (P : PROP) :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P;
  bi_fupd_mixin_fupd_frame_r E1 E2 (P R : PROP) :
    (|={E1,E2}=> P) ∗ R ={E1,E2}=∗ P ∗ R;
}.

Class BiBUpd (PROP : bi) := {
  bi_bupd_bupd :> BUpd PROP;
  bi_bupd_mixin : BiBUpdMixin PROP bi_bupd_bupd;
}.
Global Hint Mode BiBUpd ! : typeclass_instances.
Global Arguments bi_bupd_bupd : simpl never.

Class BiFUpd (PROP : bi) := {
  bi_fupd_fupd :> FUpd PROP;
  bi_fupd_mixin : BiFUpdMixin PROP bi_fupd_fupd;
}.
Global Hint Mode BiFUpd ! : typeclass_instances.
Global Arguments bi_fupd_fupd : simpl never.

Class BiBUpdFUpd (PROP : bi) `{BiBUpd PROP, BiFUpd PROP} :=
  bupd_fupd E (P : PROP) : (|==> P) ={E}=∗ P.
Global Hint Mode BiBUpdFUpd ! - - : typeclass_instances.

Class BiBUpdPlainly (PROP : bi) `{!BiBUpd PROP, !BiPlainly PROP} :=
  bupd_plainly (P : PROP) : (|==> ■ P) -∗ P.
Global Hint Mode BiBUpdPlainly ! - - : typeclass_instances.

(** These rules for the interaction between the [■] and [|={E1,E2=>] modalities
only make sense for affine logics. From the axioms below, one could derive
[■ P ={E}=∗ P] (see the lemma [fupd_plainly_elim]), which in turn gives
[True ={E}=∗ emp]. *)
Class BiFUpdPlainly (PROP : bi) `{!BiFUpd PROP, !BiPlainly PROP} := {
  (** When proving a fancy update of a plain proposition, you can also prove it
  while being allowed to open all invariants. *)
  fupd_plainly_mask_empty E (P : PROP) :
    (|={E,∅}=> ■ P) ⊢ |={E}=> P;
  (** A strong eliminator (a la modus ponens) for the wand-fancy-update with a
  plain conclusion: We eliminate [R ={E}=∗ ■ P] by supplying an [R], but we get
  to keep the [R]. *)
  fupd_plainly_keep_l E (P R : PROP) :
    (R ={E}=∗ ■ P) ∗ R ⊢ |={E}=> P ∗ R;
  (** Later "almost" commutes with fancy updates over plain propositions. It
  commutes "almost" because of the ◇ modality, which is needed in the definition
  of fancy updates so one can remove laters of timeless propositions. *)
  fupd_plainly_later E (P : PROP) :
    (▷ |={E}=> ■ P) ⊢ |={E}=> ▷ ◇ P;
  (** Forall quantifiers commute with fancy updates over plain propositions. *)
  fupd_plainly_forall_2 E {A} (Φ : A → PROP) :
    (∀ x, |={E}=> ■ Φ x) ⊢ |={E}=> ∀ x, Φ x
}.
Global Hint Mode BiBUpdFUpd ! - - : typeclass_instances.

Section bupd_laws.
  Context `{BiBUpd PROP}.
  Implicit Types P : PROP.

  Global Instance bupd_ne : NonExpansive (@bupd PROP _).
  Proof. eapply bi_bupd_mixin_bupd_ne, bi_bupd_mixin. Qed.
  Lemma bupd_intro P : P ==∗ P.
  Proof. eapply bi_bupd_mixin_bupd_intro, bi_bupd_mixin. Qed.
  Lemma bupd_mono (P Q : PROP) : (P ⊢ Q) → (|==> P) ==∗ Q.
  Proof. eapply bi_bupd_mixin_bupd_mono, bi_bupd_mixin. Qed.
  Lemma bupd_trans (P : PROP) : (|==> |==> P) ==∗ P.
  Proof. eapply bi_bupd_mixin_bupd_trans, bi_bupd_mixin. Qed.
  Lemma bupd_frame_r (P R : PROP) : (|==> P) ∗ R ==∗ P ∗ R.
  Proof. eapply bi_bupd_mixin_bupd_frame_r, bi_bupd_mixin. Qed.
End bupd_laws.

Section fupd_laws.
  Context `{BiFUpd PROP}.
  Implicit Types P : PROP.

  Global Instance fupd_ne E1 E2 : NonExpansive (@fupd PROP _ E1 E2).
  Proof. eapply bi_fupd_mixin_fupd_ne, bi_fupd_mixin. Qed.
  (** [iMod] with this lemma is useful to change the current mask to a subset,
  and obtain a fupd for changing it back. For the case where you want to get rid
  of a mask-changing fupd in the goal, [iApply fupd_mask_intro] avoids having to
  specify the mask. *)
  Lemma fupd_mask_subseteq {E1} E2 : E2 ⊆ E1 → ⊢@{PROP} |={E1,E2}=> |={E2,E1}=> emp.
  Proof. eapply bi_fupd_mixin_fupd_mask_subseteq, bi_fupd_mixin. Qed.
  Lemma except_0_fupd E1 E2 (P : PROP) : ◇ (|={E1,E2}=> P) ={E1,E2}=∗ P.
  Proof. eapply bi_fupd_mixin_except_0_fupd, bi_fupd_mixin. Qed.
  Lemma fupd_mono E1 E2 (P Q : PROP) : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q.
  Proof. eapply bi_fupd_mixin_fupd_mono, bi_fupd_mixin. Qed.
  Lemma fupd_trans E1 E2 E3 (P : PROP) : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P.
  Proof. eapply bi_fupd_mixin_fupd_trans, bi_fupd_mixin. Qed.
  Lemma fupd_mask_frame_r' E1 E2 Ef (P : PROP) :
    E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
  Proof. eapply bi_fupd_mixin_fupd_mask_frame_r', bi_fupd_mixin. Qed.
  Lemma fupd_frame_r E1 E2 (P R : PROP) : (|={E1,E2}=> P) ∗ R ={E1,E2}=∗ P ∗ R.
  Proof. eapply bi_fupd_mixin_fupd_frame_r, bi_fupd_mixin. Qed.
End fupd_laws.

Section bupd_derived.
  Context `{BiBUpd PROP}.
  Implicit Types P Q R : PROP.

  (* FIXME: Removing the `PROP:=` diverges. *)
  Global Instance bupd_proper :
    Proper ((≡) ==> (≡)) (bupd (PROP:=PROP)) := ne_proper _.

  (** BUpd derived rules *)
  Global Instance bupd_mono' : Proper ((⊢) ==> (⊢)) (bupd (PROP:=PROP)).
  Proof. intros P Q; apply bupd_mono. Qed.
  Global Instance bupd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) (bupd (PROP:=PROP)).
  Proof. intros P Q; apply bupd_mono. Qed.

  Lemma bupd_frame_l R Q : (R ∗ |==> Q) ==∗ R ∗ Q.
  Proof. rewrite !(comm _ R); apply bupd_frame_r. Qed.
  Lemma bupd_wand_l P Q : (P -∗ Q) ∗ (|==> P) ==∗ Q.
  Proof. by rewrite bupd_frame_l wand_elim_l. Qed.
  Lemma bupd_wand_r P Q : (|==> P) ∗ (P -∗ Q) ==∗ Q.
  Proof. by rewrite bupd_frame_r wand_elim_r. Qed.
  Lemma bupd_sep P Q : (|==> P) ∗ (|==> Q) ==∗ P ∗ Q.
  Proof. by rewrite bupd_frame_r bupd_frame_l bupd_trans. Qed.
  Lemma bupd_idemp P : (|==> |==> P) ⊣⊢ |==> P.
  Proof.
    apply: anti_symm.
    - apply bupd_trans.
    - apply bupd_intro.
  Qed.

  Global Instance bupd_sep_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (bupd (PROP:=PROP)).
  Proof. split; [split|]; try apply _; [apply bupd_sep | apply bupd_intro]. Qed.

  Lemma bupd_or P Q : (|==> P) ∨ (|==> Q) ⊢ |==> (P ∨ Q).
  Proof. apply or_elim; apply bupd_mono; [ apply or_intro_l | apply or_intro_r ]. Qed.

  Global Instance bupd_or_homomorphism :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) (bupd (PROP:=PROP)).
  Proof. split; [split|]; try apply _; [apply bupd_or | apply bupd_intro]. Qed.

  Lemma bupd_and P Q : (|==> (P ∧ Q)) ⊢ (|==> P) ∧ (|==> Q).
  Proof. apply and_intro; apply bupd_mono; [apply and_elim_l | apply and_elim_r]. Qed.

  Lemma bupd_exist A (Φ : A → PROP) : (∃ x : A, |==> Φ x) ⊢ |==> ∃ x : A, Φ x.
  Proof. apply exist_elim=> a. by rewrite -(exist_intro a). Qed.

  Lemma bupd_forall A (Φ : A → PROP) : (|==> ∀ x : A, Φ x) ⊢ ∀ x : A, |==> Φ x.
  Proof. apply forall_intro=> a. by rewrite -(forall_elim a). Qed.

  Lemma big_sepL_bupd {A} (Φ : nat → A → PROP) l :
    ([∗ list] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepM_bupd {A} `{Countable K} (Φ : K → A → PROP) l :
    ([∗ map] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ map] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_bupd `{Countable A} (Φ : A → PROP) l :
    ([∗ set]  x ∈ l, |==> Φ x) ⊢ |==> [∗ set] x ∈ l, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_bupd `{Countable A} (Φ : A → PROP) l :
    ([∗ mset] x ∈ l, |==> Φ x) ⊢ |==> [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  Lemma except_0_bupd P : ◇ (|==> P) ⊢ (|==> ◇ P).
  Proof.
    rewrite /bi_except_0. apply or_elim; eauto using bupd_mono, or_intro_r.
    by rewrite -bupd_intro -or_intro_l.
  Qed.

  Section bupd_plainly.
    Context `{!BiPlainly PROP, !BiBUpdPlainly PROP}.

    Lemma bupd_plain P `{!Plain P} : (|==> P) ⊢ P.
    Proof. by rewrite {1}(plain P) bupd_plainly. Qed.

    Lemma bupd_plain_forall {A} (Φ : A → PROP) `{∀ x, Plain (Φ x)} :
      (|==> ∀ x, Φ x) ⊣⊢ (∀ x, |==> Φ x).
    Proof.
      apply (anti_symm _).
      - apply bupd_forall.
      - rewrite -bupd_intro. apply forall_intro=> x.
        by rewrite (forall_elim x) bupd_plain.
    Qed.
  End bupd_plainly.
End bupd_derived.

Section fupd_derived.
  Context `{BiFUpd PROP}.
  Implicit Types P Q R : PROP.

  Global Instance fupd_proper E1 E2 :
    Proper ((≡) ==> (≡)) (fupd (PROP:=PROP) E1 E2) := ne_proper _.

  (** FUpd derived rules *)
  Global Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (fupd (PROP:=PROP) E1 E2).
  Proof. intros P Q; apply fupd_mono. Qed.
  Global Instance fupd_flip_mono' E1 E2 :
    Proper (flip (⊢) ==> flip (⊢)) (fupd (PROP:=PROP) E1 E2).
  Proof. intros P Q; apply fupd_mono. Qed.

  Lemma fupd_mask_intro_subseteq E1 E2 P :
    E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P.
  Proof.
    intros HE.
    apply wand_entails', wand_intro_r.
    rewrite fupd_mask_subseteq; last exact: HE.
    rewrite !fupd_frame_r. rewrite left_id. done.
  Qed.
  Lemma fupd_intro E P : P ={E}=∗ P.
  Proof. by rewrite {1}(fupd_mask_intro_subseteq E E P) // fupd_trans. Qed.
  Lemma fupd_except_0 E1 E2 P : (|={E1,E2}=> ◇ P) ={E1,E2}=∗ P.
  Proof. by rewrite {1}(fupd_intro E2 P) except_0_fupd fupd_trans. Qed.
  Lemma fupd_idemp E P : (|={E}=> |={E}=> P) ⊣⊢ |={E}=> P.
  Proof.
    apply: anti_symm.
    - apply fupd_trans.
    - apply fupd_intro.
  Qed.

  (** Weaken the first mask of the goal from [E1] to [E2].
      This lemma is intended to be [iApply]ed.
      However, usually you can [iMod (fupd_mask_subseteq E2)] instead and that
      will be slightly more convenient. *)
  Lemma fupd_mask_weaken {E1} E2 {E3 P} :
    E2 ⊆ E1 →
    ((|={E2,E1}=> emp) ={E2,E3}=∗ P) -∗ |={E1,E3}=> P.
  Proof.
    intros HE.
    apply wand_entails', wand_intro_r.
    rewrite {1}(fupd_mask_subseteq E2) //.
    rewrite fupd_frame_r. by rewrite wand_elim_r fupd_trans.
  Qed.

  (** Introduction lemma for a mask-changing fupd.
      This lemma is intended to be [iApply]ed. *)
  Lemma fupd_mask_intro E1 E2 P :
    E2 ⊆ E1 →
    ((|={E2,E1}=> emp) -∗ P) -∗ |={E1,E2}=> P.
  Proof.
    intros. etrans; [|by apply fupd_mask_weaken]. by rewrite -fupd_intro.
  Qed.

  Lemma fupd_mask_intro_discard E1 E2 P `{!Absorbing P} : E2 ⊆ E1 → P ={E1,E2}=∗ P.
  Proof.
    intros. etrans; [|by apply fupd_mask_intro].
    apply wand_intro_r. rewrite sep_elim_l. done.
  Qed.

  Lemma fupd_frame_l E1 E2 R Q : (R ∗ |={E1,E2}=> Q) ={E1,E2}=∗ R ∗ Q.
  Proof. rewrite !(comm _ R); apply fupd_frame_r. Qed.
  Lemma fupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=> P) ={E1,E2}=∗ Q.
  Proof. by rewrite fupd_frame_l wand_elim_l. Qed.
  Lemma fupd_wand_r E1 E2 P Q : (|={E1,E2}=> P) ∗ (P -∗ Q) ={E1,E2}=∗ Q.
  Proof. by rewrite fupd_frame_r wand_elim_r. Qed.

  Lemma fupd_trans_frame E1 E2 E3 P Q :
    ((Q ={E2,E3}=∗ emp) ∗ |={E1,E2}=> (Q ∗ P)) ={E1,E3}=∗ P.
  Proof.
    rewrite fupd_frame_l assoc -(comm _ Q) wand_elim_r.
    by rewrite fupd_frame_r left_id fupd_trans.
  Qed.

  Lemma fupd_elim E1 E2 E3 P Q :
    (Q -∗ (|={E2,E3}=> P)) → (|={E1,E2}=> Q) -∗ (|={E1,E3}=> P).
  Proof. intros ->. rewrite fupd_trans //. Qed.

  Lemma fupd_mask_frame_r E1 E2 Ef P :
    E1 ## Ef → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
  Proof.
    intros ?. rewrite -fupd_mask_frame_r' //. f_equiv.
    apply impl_intro_l, and_elim_r.
  Qed.
  Lemma fupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=∗ P.
  Proof.
    intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_mask_frame_r.
  Qed.
  (** How to apply an arbitrary mask-changing view shift when having
      an arbitrary mask. *)
  Lemma fupd_mask_frame E E' E1 E2 P :
    E1 ⊆ E →
    (|={E1,E2}=> |={E2 ∪ (E ∖ E1),E'}=> P) -∗ (|={E,E'}=> P).
  Proof.
    intros ?. rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver.
    rewrite fupd_trans.
    by replace (E1 ∪ E ∖ E1) with E by (by apply union_difference_L).
  Qed.
  (* A variant of [fupd_mask_frame] that works well for accessors: Tailored to
     elliminate updates of the form [|={E1,E1∖E2}=> Q] and provides a way to
     transform the closing view shift instead of letting you prove the same
     side-conditions twice. *)
  Lemma fupd_mask_frame_acc E E' E1(*Eo*) E2(*Em*) P Q :
    E1 ⊆ E →
    (|={E1,E1∖E2}=> Q) -∗
    (Q -∗ |={E∖E2,E'}=> (∀ R, (|={E1∖E2,E1}=> R) -∗ |={E∖E2,E}=> R) -∗  P) -∗
    (|={E,E'}=> P).
  Proof.
    intros HE. apply wand_intro_r. rewrite fupd_frame_r.
    rewrite wand_elim_r. clear Q.
    rewrite -(fupd_mask_frame E E'); first apply fupd_mono; last done.
    (* The most horrible way to apply fupd_intro_mask *)
    rewrite -[X in (X -∗ _)](right_id emp%I).
    rewrite (fupd_mask_intro_subseteq (E1 ∖ E2 ∪ E ∖ E1) (E ∖ E2) emp); last first.
    { rewrite {1}(union_difference_L _ _ HE). set_solver. }
    rewrite fupd_frame_l fupd_frame_r. apply fupd_elim.
    apply fupd_mono.
    eapply wand_apply;
      last (apply sep_mono; first reflexivity); first reflexivity.
    apply forall_intro=>R. apply wand_intro_r.
    rewrite fupd_frame_r. apply fupd_elim. rewrite left_id.
    rewrite (fupd_mask_frame_r _ _ (E ∖ E1)); last set_solver+.
    rewrite {4}(union_difference_L _ _ HE). done.
  Qed.

  Lemma fupd_mask_subseteq_emptyset_difference E1 E2 :
    E2 ⊆ E1 →
    ⊢@{PROP} |={E1, E2}=> |={∅, E1∖E2}=> emp.
  Proof.
    intros ?. rewrite [in fupd E1](union_difference_L E2 E1); [|done].
    rewrite (comm_L (∪))
      -[X in fupd _ X](left_id_L ∅ (∪) E2) -fupd_mask_frame_r; [|set_solver+].
    apply fupd_mask_intro_subseteq; set_solver.
  Qed.

  Lemma fupd_or E1 E2 P Q :
    (|={E1,E2}=> P) ∨ (|={E1,E2}=> Q) ⊢@{PROP}
    (|={E1,E2}=> (P ∨ Q)).
  Proof. apply or_elim; apply fupd_mono; [ apply or_intro_l | apply or_intro_r ]. Qed.

  Global Instance fupd_or_homomorphism E :
    MonoidHomomorphism bi_or bi_or (flip (⊢)) (fupd (PROP:=PROP) E E).
  Proof. split; [split|]; try apply _; [apply fupd_or | apply fupd_intro]. Qed.

  Lemma fupd_and E1 E2 P Q :
    (|={E1,E2}=> (P ∧ Q)) ⊢@{PROP} (|={E1,E2}=> P) ∧ (|={E1,E2}=> Q).
  Proof. apply and_intro; apply fupd_mono; [apply and_elim_l | apply and_elim_r]. Qed.

  Lemma fupd_exist E1 E2 A (Φ : A → PROP) : (∃ x : A, |={E1, E2}=> Φ x) ⊢ |={E1, E2}=> ∃ x : A, Φ x.
  Proof. apply exist_elim=> a. by rewrite -(exist_intro a). Qed.

  Lemma fupd_forall E1 E2 A (Φ : A → PROP) : (|={E1, E2}=> ∀ x : A, Φ x) ⊢ ∀ x : A, |={E1, E2}=> Φ x.
  Proof. apply forall_intro=> a. by rewrite -(forall_elim a). Qed.

  Lemma fupd_sep E P Q : (|={E}=> P) ∗ (|={E}=> Q) ={E}=∗ P ∗ Q.
  Proof. by rewrite fupd_frame_r fupd_frame_l fupd_trans. Qed.

  Global Instance fupd_sep_homomorphism E :
    MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (fupd (PROP:=PROP) E E).
  Proof. split; [split|]; try apply _; [apply fupd_sep | apply fupd_intro]. Qed.

  Lemma big_sepL_fupd {A} E (Φ : nat → A → PROP) l :
    ([∗ list] k↦x ∈ l, |={E}=> Φ k x) ={E}=∗ [∗ list] k↦x ∈ l, Φ k x.
  Proof. by rewrite (big_opL_commute _). Qed.
  Lemma big_sepL2_fupd {A B} E (Φ : nat → A → B → PROP) l1 l2 :
    ([∗ list] k↦x;y ∈ l1;l2, |={E}=> Φ k x y) ={E}=∗ [∗ list] k↦x;y ∈ l1;l2, Φ k x y.
  Proof.
    rewrite !big_sepL2_alt !persistent_and_affinely_sep_l.
    etrans; [| by apply fupd_frame_l]. apply sep_mono_r. apply big_sepL_fupd.
  Qed.

  Lemma big_sepM_fupd `{Countable K} {A} E (Φ : K → A → PROP) m :
    ([∗ map] k↦x ∈ m, |={E}=> Φ k x) ={E}=∗ [∗ map] k↦x ∈ m, Φ k x.
  Proof. by rewrite (big_opM_commute _). Qed.
  Lemma big_sepS_fupd `{Countable A} E (Φ : A → PROP) X :
    ([∗ set] x ∈ X, |={E}=> Φ x) ={E}=∗ [∗ set] x ∈ X, Φ x.
  Proof. by rewrite (big_opS_commute _). Qed.
  Lemma big_sepMS_fupd `{Countable A} E (Φ : A → PROP) l :
    ([∗ mset] x ∈ l, |={E}=> Φ x) ⊢ |={E}=> [∗ mset] x ∈ l, Φ x.
  Proof. by rewrite (big_opMS_commute _). Qed.

  (** Fancy updates that take a step derived rules. *)
  Lemma step_fupd_wand Eo Ei P Q : (|={Eo}[Ei]▷=> P) -∗ (P -∗ Q) -∗ |={Eo}[Ei]▷=> Q.
  Proof.
    apply wand_intro_l.
    by rewrite (later_intro (P -∗ Q)) fupd_frame_l -later_sep fupd_frame_l
               wand_elim_l.
  Qed.

  Lemma step_fupd_mask_frame_r Eo Ei Ef P :
    Eo ## Ef → Ei ## Ef → (|={Eo}[Ei]▷=> P) ⊢ |={Eo ∪ Ef}[Ei ∪ Ef]▷=> P.
  Proof.
    intros. rewrite -fupd_mask_frame_r //. do 2 f_equiv. by apply fupd_mask_frame_r.
  Qed.

  Lemma step_fupd_mask_mono Eo1 Eo2 Ei1 Ei2 P :
    Ei2 ⊆ Ei1 → Eo1 ⊆ Eo2 → (|={Eo1}[Ei1]▷=> P) ⊢ |={Eo2}[Ei2]▷=> P.
  Proof.
    intros ??. rewrite -(emp_sep (|={Eo1}[Ei1]▷=> P)%I).
    rewrite (fupd_mask_intro_subseteq Eo2 Eo1 emp) //.
    rewrite fupd_frame_r -(fupd_trans Eo2 Eo1 Ei2). f_equiv.
    rewrite fupd_frame_l -(fupd_trans Eo1 Ei1 Ei2). f_equiv.
    rewrite (fupd_mask_intro_subseteq Ei1 Ei2 (|={_,_}=> emp)) //.
    rewrite fupd_frame_r. f_equiv.
    rewrite [X in (X ∗ _)%I]later_intro -later_sep. f_equiv.
    rewrite fupd_frame_r -(fupd_trans Ei2 Ei1 Eo2). f_equiv.
    rewrite fupd_frame_l -(fupd_trans Ei1 Eo1 Eo2). f_equiv.
    by rewrite fupd_frame_r left_id.
  Qed.

  Lemma step_fupd_intro Ei Eo P : Ei ⊆ Eo → ▷ P -∗ |={Eo}[Ei]▷=> P.
  Proof. intros. by rewrite -(step_fupd_mask_mono Ei _ Ei _) // -!fupd_intro. Qed.

  Lemma step_fupd_frame_l Eo Ei R Q :
    (R ∗ |={Eo}[Ei]▷=> Q) -∗ |={Eo}[Ei]▷=> (R ∗ Q).
  Proof.
    rewrite fupd_frame_l.
    apply fupd_mono.
    rewrite [P in P ∗ _ ⊢ _](later_intro R) -later_sep fupd_frame_l.
    by apply later_mono, fupd_mono.
  Qed.

  Lemma step_fupd_fupd Eo Ei P : (|={Eo}[Ei]▷=> P) ⊣⊢ (|={Eo}[Ei]▷=> |={Eo}=> P).
  Proof.
    apply (anti_symm (⊢)).
    - by rewrite -fupd_intro.
    - by rewrite fupd_trans.
  Qed.

  Lemma step_fupdN_mono Eo Ei n P Q :
    (P ⊢ Q) → (|={Eo}[Ei]▷=>^n P) ⊢ (|={Eo}[Ei]▷=>^n Q).
  Proof.
    intros HPQ. induction n as [|n IH]=> //=. rewrite IH //.
  Qed.

  Lemma step_fupdN_wand Eo Ei n P Q :
    (|={Eo}[Ei]▷=>^n P) -∗ (P -∗ Q) -∗ (|={Eo}[Ei]▷=>^n Q).
  Proof.
    apply wand_intro_l. induction n as [|n IH]=> /=.
    { by rewrite wand_elim_l. }
    rewrite -IH -fupd_frame_l later_sep -fupd_frame_l.
    by apply sep_mono; first apply later_intro.
  Qed.

  Lemma step_fupdN_intro Ei Eo n P : Ei ⊆ Eo → ▷^n P -∗ |={Eo}[Ei]▷=>^n P.
  Proof.
    induction n as [|n IH]=> ?; [done|].
    rewrite /= -step_fupd_intro; [|done]. by rewrite IH.
  Qed.

  Lemma step_fupdN_S_fupd n E P :
    (|={E}[∅]▷=>^(S n) P) ⊣⊢ (|={E}[∅]▷=>^(S n) |={E}=> P).
  Proof.
    apply (anti_symm (⊢)); rewrite !Nat_iter_S_r; apply step_fupdN_mono;
      rewrite -step_fupd_fupd //.
  Qed.

  Lemma step_fupdN_frame_l Eo Ei n R Q :
    (R ∗ |={Eo}[Ei]▷=>^n Q) -∗ |={Eo}[Ei]▷=>^n (R ∗ Q).
  Proof.
    induction n as [|n IH]; simpl; [done|].
    rewrite step_fupd_frame_l IH //=.
  Qed.

  Section fupd_plainly_derived.
    Context `{!BiPlainly PROP, !BiFUpdPlainly PROP}.

    Lemma fupd_plainly_mask E E' P : (|={E,E'}=> ■ P) ⊢ |={E}=> P.
    Proof.
      rewrite -(fupd_plainly_mask_empty).
      apply fupd_elim, (fupd_mask_intro_discard _ _ _). set_solver.
    Qed.

    Lemma fupd_plainly_elim E P : ■ P ={E}=∗ P.
    Proof. by rewrite (fupd_intro E (■ P)) fupd_plainly_mask. Qed.

    Lemma fupd_plainly_keep_r E P R : R ∗ (R ={E}=∗ ■ P) ⊢ |={E}=> R ∗ P.
    Proof. by rewrite !(comm _ R) fupd_plainly_keep_l. Qed.

    Lemma fupd_plain_mask_empty E P `{!Plain P} : (|={E,∅}=> P) ⊢ |={E}=> P.
    Proof. by rewrite {1}(plain P) fupd_plainly_mask_empty. Qed.
    Lemma fupd_plain_mask E E' P `{!Plain P} : (|={E,E'}=> P) ⊢ |={E}=> P.
    Proof. by rewrite {1}(plain P) fupd_plainly_mask. Qed.

    Lemma fupd_plain_keep_l E P R `{!Plain P} : (R ={E}=∗ P) ∗ R ⊢ |={E}=> P ∗ R.
    Proof. by rewrite {1}(plain P) fupd_plainly_keep_l. Qed.
    Lemma fupd_plain_keep_r E P R `{!Plain P} : R ∗ (R ={E}=∗ P) ⊢ |={E}=> R ∗ P.
    Proof. by rewrite {1}(plain P) fupd_plainly_keep_r. Qed.

    Lemma fupd_plainly_laterN E n P : (▷^n |={E}=> ■ P) ⊢ |={E}=> ▷^n ◇ P.
    Proof.
      revert P. induction n as [|n IH]=> P /=.
      { by rewrite -except_0_intro (fupd_plainly_elim E) fupd_trans. }
      rewrite -!later_laterN !laterN_later.
      rewrite -plainly_idemp fupd_plainly_later.
      by rewrite except_0_plainly_1 later_plainly_1 IH except_0_later.
    Qed.
    Lemma fupd_plain_later E P `{!Plain P} : (▷ |={E}=> P) ⊢ |={E}=> ▷ ◇ P.
    Proof. by rewrite {1}(plain P) fupd_plainly_later. Qed.
    Lemma fupd_plain_laterN E n P `{!Plain P} : (▷^n |={E}=> P) ⊢ |={E}=> ▷^n ◇ P.
    Proof. by rewrite {1}(plain P) fupd_plainly_laterN. Qed.

    Lemma fupd_plain_forall_2 E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      (∀ x, |={E}=> Φ x) ⊢ |={E}=> ∀ x, Φ x.
    Proof.
      rewrite -fupd_plainly_forall_2. apply forall_mono=> x.
      by rewrite {1}(plain (Φ _)).
    Qed.
    Lemma fupd_plain_forall E1 E2 {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      E2 ⊆ E1 →
      (|={E1,E2}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E1,E2}=> Φ x).
    Proof.
      intros. apply (anti_symm _); first apply fupd_forall.
      trans (∀ x, |={E1}=> Φ x)%I.
      { apply forall_mono=> x. by rewrite fupd_plain_mask. }
      rewrite fupd_plain_forall_2. apply fupd_elim.
      rewrite {1}(plain (∀ x, Φ x)) (fupd_mask_intro_discard E1 E2 (■ _)) //.
      apply fupd_elim. by rewrite fupd_plainly_elim.
    Qed.
    Lemma fupd_plain_forall' E {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      (|={E}=> ∀ x, Φ x) ⊣⊢ (∀ x, |={E}=> Φ x).
    Proof. by apply fupd_plain_forall. Qed.

    Lemma step_fupd_plain Eo Ei P `{!Plain P} : (|={Eo}[Ei]▷=> P) ={Eo}=∗ ▷ ◇ P.
    Proof.
      rewrite -(fupd_plain_mask _ Ei (▷ ◇ P)).
      apply fupd_elim. by rewrite fupd_plain_mask -fupd_plain_later.
    Qed.

    Lemma step_fupdN_plain Eo Ei n P `{!Plain P} : (|={Eo}[Ei]▷=>^n P) ={Eo}=∗ ▷^n ◇ P.
    Proof.
      induction n as [|n IH].
      - by rewrite -fupd_intro -except_0_intro.
      - rewrite Nat_iter_S step_fupd_fupd IH !fupd_trans step_fupd_plain.
        apply fupd_mono. destruct n as [|n]; simpl.
        * by rewrite except_0_idemp.
        * by rewrite except_0_later.
    Qed.

    Lemma step_fupd_plain_forall Eo Ei {A} (Φ : A → PROP) `{!∀ x, Plain (Φ x)} :
      Ei ⊆ Eo →
      (|={Eo}[Ei]▷=> ∀ x, Φ x) ⊣⊢ (∀ x, |={Eo}[Ei]▷=> Φ x).
    Proof.
      intros. apply (anti_symm _).
      { apply forall_intro=> x. by rewrite (forall_elim x). }
      trans (∀ x, |={Eo}=> ▷ ◇ Φ x)%I.
      { apply forall_mono=> x. by rewrite step_fupd_plain. }
      rewrite -fupd_plain_forall'. apply fupd_elim.
      rewrite -(fupd_except_0 Ei Eo) -step_fupd_intro //.
      by rewrite -later_forall -except_0_forall.
    Qed.
  End fupd_plainly_derived.
End fupd_derived.
