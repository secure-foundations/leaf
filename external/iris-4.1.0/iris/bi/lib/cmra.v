From iris.proofmode Require Import proofmode.
From iris.bi Require Import internal_eq.
From iris.algebra Require Import cmra csum excl agree.
From iris.prelude Require Import options.

(** Derived [≼] connective on [cmra] elements. This can be defined on
    any [bi] that has internal equality [≡]. It corresponds to the
    step-indexed [≼{n}] connective in the [uPred] model. *)
Definition internal_included `{!BiInternalEq PROP} {A : cmra} (a b : A) : PROP :=
  ∃ c, b ≡ a ⋅ c.
Global Arguments internal_included {_ _ _} _ _ : simpl never.
Global Instance: Params (@internal_included) 3 := {}.
Global Typeclasses Opaque internal_included.

Infix "≼" := internal_included : bi_scope.

Section internal_included_laws.
  Context `{!BiInternalEq PROP}.
  Implicit Type A B : cmra.

  (* Force implicit argument PROP *)
  Notation "P ⊢ Q" := (P ⊢@{PROP} Q).
  Notation "P ⊣⊢ Q" := (P ⊣⊢@{PROP} Q).

  (** Propers *)
  Global Instance internal_included_nonexpansive A :
    NonExpansive2 (internal_included (PROP := PROP) (A := A)).
  Proof. solve_proper. Qed.
  Global Instance internal_included_proper A :
    Proper ((≡) ==> (≡) ==> (⊣⊢)) (internal_included (PROP := PROP) (A := A)).
  Proof. solve_proper. Qed.

  (** Proofmode support *)
  Global Instance into_pure_internal_included {A} (a b : A) `{!Discrete b} :
    @IntoPure PROP (a ≼ b) (a ≼ b).
  Proof. rewrite /IntoPure /internal_included. eauto. Qed.

  Global Instance from_pure_internal_included {A} (a b : A) :
    @FromPure PROP false (a ≼ b) (a ≼ b).
  Proof. rewrite /FromPure /= /internal_included. eauto. Qed.

  Global Instance into_exist_internal_included {A} (a b : A) :
    IntoExist (PROP := PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I (λ x, x).
  Proof. by rewrite /IntoExist. Qed.

  Global Instance from_exist_internal_included {A} (a b : A) :
    FromExist (PROP := PROP) (a ≼ b) (λ c, b ≡ a ⋅ c)%I.
  Proof. by rewrite /FromExist. Qed.

  Global Instance internal_included_persistent {A} (a b : A) :
    Persistent (PROP := PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.

  Global Instance internal_included_absorbing {A} (a b : A) :
    Absorbing (PROP := PROP) (a ≼ b).
  Proof. rewrite /internal_included. apply _. Qed.

  Lemma internal_included_refl `{!CmraTotal A} (x : A) : ⊢@{PROP} x ≼ x.
  Proof. iExists (core x). by rewrite cmra_core_r. Qed.
  Lemma internal_included_trans {A} (x y z : A) :
    ⊢@{PROP} x ≼ y -∗ y ≼ z -∗ x ≼ z.
  Proof.
    iIntros "#[%x' Hx'] #[%y' Hy']". iExists (x' ⋅ y').
    rewrite assoc. by iRewrite -"Hx'".
  Qed.

  (** Simplification lemmas *)
  Lemma f_homom_includedI {A B} (x y : A) (f : A → B) `{!NonExpansive f} :
    (* This is a slightly weaker condition than being a [CmraMorphism] *)
    (∀ c, f x ⋅ f c ≡ f (x ⋅ c)) →
    (x ≼ y ⊢ f x ≼ f y).
  Proof.
    intros f_homom. iDestruct 1 as (z) "Hz".
    iExists (f z). rewrite f_homom.
    by iApply f_equivI.
  Qed.

  Lemma prod_includedI {A B} (x y : A * B) :
    x ≼ y ⊣⊢ (x.1 ≼ y.1) ∧ (x.2 ≼ y.2).
  Proof.
    destruct x as [x1 x2], y as [y1 y2]; simpl; iSplit.
    - iIntros "#[%z H]". rewrite prod_equivI /=. iDestruct "H" as "[??]".
      iSplit; by iExists _.
    - iIntros "#[[%z1 Hz1] [%z2 Hz2]]". iExists (z1, z2).
      rewrite prod_equivI /=; auto.
  Qed.

  Lemma option_includedI {A} (mx my : option A) :
    mx ≼ my ⊣⊢ match mx, my with
               | Some x, Some y => (x ≼ y) ∨ (x ≡ y)
               | None, _ => True
               | Some x, None => False
               end.
  Proof.
    iSplit.
    - iIntros "[%mz H]". rewrite option_equivI.
      destruct mx as [x|], my as [y|], mz as [z|]; simpl; auto; [|].
      + iLeft. by iExists z.
      + iRight. by iRewrite "H".
    - destruct mx as [x|], my as [y|]; simpl; auto; [|].
      + iDestruct 1 as "[[%z H]|H]"; iRewrite "H".
        * by iExists (Some z).
        * by iExists None.
      + iIntros "_". by iExists (Some y).
  Qed.

  Lemma option_included_totalI `{!CmraTotal A} (mx my : option A) :
    mx ≼ my ⊣⊢ match mx, my with
               | Some x, Some y => x ≼ y
               | None, _ => True
               | Some x, None => False
               end.
  Proof.
    rewrite option_includedI. destruct mx as [x|], my as [y|]; [|done..].
    iSplit; [|by auto].
    iIntros "[Hx|Hx] //". iRewrite "Hx". iApply (internal_included_refl y).
  Qed.

  Lemma csum_includedI {A B} (sx sy : csum A B) :
    sx ≼ sy ⊣⊢ match sx, sy with
               | Cinl x, Cinl y => x ≼ y
               | Cinr x, Cinr y => x ≼ y
               | _, CsumBot => True
               | _, _ => False
               end.
  Proof.
    iSplit.
    - iDestruct 1 as (sz) "H". rewrite csum_equivI.
      destruct sx, sy, sz; rewrite /internal_included /=; auto.
    - destruct sx as [x|x|], sy as [y|y|]; eauto; [|].
      + iIntros "#[%z H]". iExists (Cinl z). by rewrite csum_equivI.
      + iIntros "#[%z H]". iExists (Cinr z). by rewrite csum_equivI.
  Qed.

  Lemma excl_includedI {O : ofe} (x y : excl O) :
    x ≼ y ⊣⊢ match y with
             | ExclBot => True
             |  _ => False
             end.
  Proof.
    iSplit.
    - iIntros "[%z Hz]". rewrite excl_equivI. destruct y, x, z; auto.
    - destruct y; [done|]. iIntros "_". by iExists ExclBot.
  Qed.

  Lemma agree_includedI {O : ofe} (x y : agree O) : x ≼ y ⊣⊢ y ≡ x ⋅ y.
  Proof.
    iSplit.
    + iIntros "[%z Hz]". iRewrite "Hz". by rewrite assoc agree_idemp.
    + iIntros "H". by iExists _.
  Qed.
End internal_included_laws.