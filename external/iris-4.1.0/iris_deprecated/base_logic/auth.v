(** This logic-level wrapper on top of the [auth] RA turns out to be much harder
to use than just directly using the RA, hence it is deprecated and will be
removed entirely after some grace period. *)

From iris.algebra Require Export auth.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export invariants.
From iris.prelude Require Import options.
Import uPred.

(* The CMRA we need. *)
Class authG Σ (A : ucmra) := AuthG {
  auth_inG : inG Σ (authR A);
  auth_cmra_discrete :> CmraDiscrete A;
}.
Local Existing Instance auth_inG.

Definition authΣ (A : ucmra) : gFunctors := #[ GFunctor (authR A) ].

Global Instance subG_authΣ Σ A : subG (authΣ A) Σ → CmraDiscrete A → authG Σ A.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!invGS Σ, !authG Σ A} {T : Type} (γ : gname).

  Definition auth_own (a : A) : iProp Σ :=
    own γ (◯ a).
  Definition auth_inv (f : T → A) (φ : T → iProp Σ) : iProp Σ :=
    ∃ t, own γ (● f t) ∗ φ t.
  Definition auth_ctx (N : namespace) (f : T → A) (φ : T → iProp Σ) : iProp Σ :=
    inv N (auth_inv f φ).

  Global Instance auth_own_ne : NonExpansive auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_proper : Proper ((≡) ==> (⊣⊢)) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_timeless a : Timeless (auth_own a).
  Proof. apply _. Qed.
  Global Instance auth_own_core_id a : CoreId a → Persistent (auth_own a).
  Proof. apply _. Qed.

  Global Instance auth_inv_ne n :
    Proper (pointwise_relation T (dist n) ==>
            pointwise_relation T (dist n) ==> dist n) auth_inv.
  Proof. solve_proper. Qed.
  Global Instance auth_inv_proper :
    Proper (pointwise_relation T (≡) ==>
            pointwise_relation T (⊣⊢) ==> (⊣⊢)) auth_inv.
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_ne N n :
    Proper (pointwise_relation T (dist n) ==>
            pointwise_relation T (dist n) ==> dist n) (auth_ctx N).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_proper N :
    Proper (pointwise_relation T (≡) ==>
            pointwise_relation T (⊣⊢) ==> (⊣⊢)) (auth_ctx N).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_persistent N f φ : Persistent (auth_ctx N f φ).
  Proof. apply _. Qed.
End definitions.

Global Typeclasses Opaque auth_own auth_inv auth_ctx.
Global Instance: Params (@auth_own) 4 := {}.
Global Instance: Params (@auth_inv) 5 := {}.
Global Instance: Params (@auth_ctx) 7 := {}.

Section auth.
  Context `{!invGS Σ, !authG Σ A}.
  Context {T : Type} `{!Inhabited T}.
  Context (f : T → A) (φ : T → iProp Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iProp Σ.
  Implicit Types a b : A.
  Implicit Types t u : T.
  Implicit Types γ : gname.

  Lemma auth_own_op γ a b : auth_own γ (a ⋅ b) ⊣⊢ auth_own γ a ∗ auth_own γ b.
  Proof. by rewrite /auth_own -own_op auth_frag_op. Qed.

(*
  Global Instance from_and_auth_own γ a b1 b2 :
    IsOp a b1 b2 →
    FromAnd false (auth_own γ a) (auth_own γ b1) (auth_own γ b2) | 90.
  Proof. rewrite /IsOp /FromAnd=> ->. by rewrite auth_own_op. Qed.
  Global Instance from_and_auth_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → Or (CoreId b1) (CoreId b2) →
    FromAnd true (auth_own γ a) (auth_own γ b1) (auth_own γ b2) | 91.
  Proof.
    intros ? Hper; apply mk_from_and_persistent; [destruct Hper; apply _|].
    by rewrite -auth_own_op -is_op.
  Qed.

  Global Instance into_and_auth_own p γ a b1 b2 :
    IsOp a b1 b2 →
    IntoAnd p (auth_own γ a) (auth_own γ b1) (auth_own γ b2) | 90.
  Proof. intros. apply mk_into_and_sep. by rewrite (is_op a) auth_own_op. Qed.
*)

  Lemma auth_own_mono γ a b : a ≼ b → auth_own γ b ⊢ auth_own γ a.
  Proof. intros [? ->]. by rewrite auth_own_op sep_elim_l. Qed.
  Lemma auth_own_valid γ a : auth_own γ a ⊢ ✓ a.
  Proof. by rewrite /auth_own own_valid auth_frag_validI. Qed.
  Global Instance auth_own_sep_homomorphism γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (auth_own γ).
  Proof. split; try apply _. apply auth_own_op. Qed.

  Lemma big_opL_auth_own {B} γ (g : nat → B → A) (l : list B) :
    l ≠ [] →
    auth_own γ ([^op list] k↦x ∈ l, g k x) ⊣⊢
             [∗ list] k↦x ∈ l, auth_own γ (g k x).
  Proof. apply (big_opL_commute1 _). Qed.
  Lemma big_opM_auth_own `{Countable K} {B} γ (g : K → B → A) (m : gmap K B) :
    m ≠ ∅ →
    auth_own γ ([^op map] k↦x ∈ m, g k x) ⊣⊢
             [∗ map] k↦x ∈ m, auth_own γ (g k x).
  Proof. apply (big_opM_commute1 _). Qed.
  Lemma big_opS_auth_own `{Countable B} γ (g : B → A) (X : gset B) :
    X ≠ ∅ →
    auth_own γ ([^op set] x ∈ X, g x) ⊣⊢ [∗ set] x ∈ X, auth_own γ (g x).
  Proof. apply (big_opS_commute1 _). Qed.
  Lemma big_opMS_auth_own `{Countable B} γ (g : B → A) (X : gmultiset B) :
    X ≠ ∅ →
    auth_own γ ([^op mset] x ∈ X, g x) ⊣⊢ [∗ mset] x ∈ X, auth_own γ (g x).
  Proof. apply (big_opMS_commute1 _). Qed.

  Global Instance auth_own_cmra_sep_entails_homomorphism γ :
    MonoidHomomorphism op uPred_sep (⊢) (auth_own γ).
  Proof.
    split; [split|]; try apply _.
    - intros. by rewrite auth_own_op.
    - apply (affine _).
  Qed.

  Lemma big_opL_auth_own_1 {B} γ (g : nat → B → A) (l : list B) :
    auth_own γ ([^op list] k↦x ∈ l, g k x) ⊢
             [∗ list] k↦x ∈ l, auth_own γ (g k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_auth_own_1 `{Countable K} {B} γ (g : K → B → A)
        (m : gmap K B) :
    auth_own γ ([^op map] k↦x ∈ m, g k x) ⊢ [∗ map] k↦x ∈ m, auth_own γ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_auth_own_1 `{Countable B} γ (g : B → A) (X : gset B) :
    auth_own γ ([^op set] x ∈ X, g x) ⊢ [∗ set] x ∈ X, auth_own γ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_auth_own_1 `{Countable B} γ (g : B → A)
        (X : gmultiset B) :
    auth_own γ ([^op mset] x ∈ X, g x) ⊢ [∗ mset] x ∈ X, auth_own γ (g x).
  Proof. apply (big_opMS_commute _). Qed.

  Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (auth_own γ).
  Proof. intros a1 a2. apply auth_own_mono. Qed.

  Lemma auth_alloc_strong N E t (I : gname → Prop) :
    pred_infinite I →
    ✓ (f t) → ▷ φ t ={E}=∗ ∃ γ, ⌜I γ⌝ ∗ auth_ctx γ N f φ ∗ auth_own γ (f t).
  Proof.
    iIntros (??) "Hφ". rewrite /auth_own /auth_ctx.
    iMod (own_alloc_strong (● f t ⋅ ◯ f t) I) as (γ) "[% [Hγ Hγ']]";
      [done|by apply auth_both_valid_discrete|].
    iMod (inv_alloc N _ (auth_inv γ f φ) with "[-Hγ']") as "#?".
    { iNext. rewrite /auth_inv. iExists t. by iFrame. }
    eauto.
  Qed.

  Lemma auth_alloc_cofinite N E t (G : gset gname) :
    ✓ (f t) → ▷ φ t ={E}=∗ ∃ γ, ⌜γ ∉ G⌝ ∗ auth_ctx γ N f φ ∗ auth_own γ (f t).
  Proof.
    intros ?. apply auth_alloc_strong=>//.
    apply (pred_infinite_set (C:=gset gname)) => E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma auth_alloc N E t :
    ✓ (f t) → ▷ φ t ={E}=∗ ∃ γ, auth_ctx γ N f φ ∗ auth_own γ (f t).
  Proof.
    iIntros (?) "Hφ".
    iMod (auth_alloc_cofinite N E t ∅ with "Hφ") as (γ) "[_ ?]"; eauto.
  Qed.

  Lemma auth_empty γ : ⊢ |==> auth_own γ ε.
  Proof. by rewrite /auth_own -own_unit. Qed.

  Lemma auth_inv_acc E γ a :
    ▷ auth_inv γ f φ ∗ auth_own γ a ={E}=∗ ∃ t,
      ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E}=∗ ▷ auth_inv γ f φ ∗ auth_own γ b.
  Proof using Type*.
    iIntros "[Hinv Hγf]". rewrite /auth_inv /auth_own.
    iDestruct "Hinv" as (t) "[>Hγa Hφ]".
    iModIntro. iExists t.
    iDestruct (own_valid_2 with "Hγa Hγf") as % [? ?]%auth_both_valid_discrete.
    iSplit; first done. iFrame. iIntros (u b) "[% Hφ]".
    iMod (own_update_2 with "Hγa Hγf") as "[Hγa Hγf]".
    { eapply auth_update; eassumption. }
    iModIntro. iFrame. iExists u. iFrame.
  Qed.

  Lemma auth_acc E N γ a :
    ↑N ⊆ E →
    auth_ctx γ N f φ ∗ auth_own γ a ={E,E∖↑N}=∗ ∃ t,
      ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E∖↑N,E}=∗ auth_own γ b.
  Proof using Type*.
    iIntros (?) "[#? Hγf]". rewrite /auth_ctx. iInv N as "Hinv" "Hclose".
    (* The following is essentially a very trivial composition of the accessors
       [auth_inv_acc] and [inv_acc] -- but since we don't have any good support
       for that currently, this gets more tedious than it should, with us having
       to unpack and repack various proofs.
       TODO: Make this mostly automatic, by supporting "opening accessors
       around accessors". *)
    iMod (auth_inv_acc with "[$Hinv $Hγf]") as (t) "(?&?&HclAuth)".
    iModIntro. iExists t. iFrame. iIntros (u b) "H".
    iMod ("HclAuth" $! u b with "H") as "(Hinv & ?)". by iMod ("Hclose" with "Hinv").
  Qed.
End auth.

Global Arguments auth_acc {_ _ _} [_] {_} [_] _ _ _ _ _ _ _.
