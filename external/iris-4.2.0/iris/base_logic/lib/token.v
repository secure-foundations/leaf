(** This library provides assertions that represent "unique tokens".
The [token γ] assertion provides ownership of the token named [γ],
and the key lemma [token_exclusive] proves only one token exists. *)
From iris.algebra Require Import excl.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(** The CMRA we need. *)
Class tokenG Σ := TokenG {
  token_inG : inG Σ (exclR unitO);
}.
Local Existing Instance token_inG.
Global Hint Mode tokenG - : typeclass_instances.

Definition tokenΣ : gFunctors :=
  #[ GFunctor (exclR unitO) ].

Global Instance subG_tokenΣ Σ : subG tokenΣ Σ → tokenG Σ.
Proof. solve_inG. Qed.

Local Definition token_def `{!tokenG Σ} (γ : gname) : iProp Σ :=
  own γ (Excl ()).
Local Definition token_aux : seal (@token_def). Proof. by eexists. Qed.
Definition token := token_aux.(unseal).
Local Definition token_unseal :
  @token = @token_def := token_aux.(seal_eq).
Global Arguments token {Σ _} γ.

Local Ltac unseal := rewrite ?token_unseal /token_def.

Section lemmas.
  Context `{!tokenG Σ}.

  Global Instance token_timeless γ : Timeless (token γ).
  Proof. unseal. apply _. Qed.

  Lemma token_alloc_strong (P : gname → Prop) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ token γ.
  Proof. unseal. intros. iApply own_alloc_strong; done. Qed.
  Lemma token_alloc :
    ⊢ |==> ∃ γ, token γ.
  Proof. unseal. iApply own_alloc. done. Qed.

  Lemma token_exclusive γ :
    token γ -∗ token γ -∗ False.
  Proof.
    unseal. iIntros "Htok1 Htok2".
    iCombine "Htok1 Htok2" gives %[].
  Qed.
  Global Instance token_combine_gives γ :
    CombineSepGives (token γ) (token γ) ⌜False⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (token_exclusive with "H1 H2") as %[].
  Qed.

End lemmas.

