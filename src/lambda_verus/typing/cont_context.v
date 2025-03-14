From iris.proofmode Require Import proofmode.
From lrust.lang Require Import notation.
From lrust.typing Require Import type lft_contexts type_context.
Set Default Proof Using "Type".

Implicit Type 𝔄: syn_type.

Section cont_context.
  Context `{!typeG Σ}.

  Definition cont_postcondition: iProp Σ := True%I.

  Record cctx_elt 𝔄 := CCtxe {
    cctxe_k: val;  cctxe_L: llctx;  cctxe_Al: syn_typel;  cctxe_n: nat;
    cctxe_T: vec val cctxe_n → tctx cctxe_Al;  cctxe_tr: predl_trans' cctxe_Al 𝔄;
  }.
  Global Arguments CCtxe {_} _ _ {_ _} _ _.

  Definition cctx_elt_interp {𝔄} (tid: thread_id)
    (postπ: proph (pred' 𝔄)) (c: cctx_elt 𝔄) : iProp Σ :=
    let 'CCtxe k L T tr := c in ∀vl vπl,
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ tctx_interp tid (T vl) vπl -∗
        ⟨π, tr (postπ π) (vπl -$ π)⟩ -∗ WP k (map of_val vl) {{ _, cont_postcondition }}.

  Definition cctx_interp {𝔄} (tid: thread_id)
    (postπ: proph (pred' 𝔄)) (C: list (cctx_elt 𝔄)) : iProp Σ :=
    ∀c, ⌜c ∈ C⌝ -∗ cctx_elt_interp tid postπ c.
End cont_context.
Add Printing Constructor cctx_elt.

Notation cctx 𝔄 := (list (cctx_elt 𝔄)).

Notation "k ◁cont{ L , T } tr" := (CCtxe k L T tr)
  (at level 55, format "k  ◁cont{ L ,  T }  tr").

Section cont_context.
  Context `{!typeG Σ}.

  Global Instance cctx_interp_permut {𝔄} tid (postπ: proph (pred' 𝔄)) :
    Proper ((≡ₚ) ==> (⊣⊢)) (cctx_interp tid postπ).
  Proof. solve_proper. Qed.

  Lemma cctx_interp_cons {𝔄} tid postπ (c: cctx_elt 𝔄) C :
    cctx_interp tid postπ (c :: C) ⊣⊢
    cctx_elt_interp tid postπ c ∧ cctx_interp tid postπ C.
  Proof.
    iSplit; iIntros "cC".
    - iSplit; [|iIntros (??)]; iApply "cC"; iPureIntro; by constructor.
    - iIntros (? In). move: In. rewrite elem_of_cons. case=> [->|?].
      + by iDestruct "cC" as "[? _]".
      + iDestruct "cC" as "[_ C]". by iApply "C".
  Qed.

  Lemma cctx_interp_nil {𝔄} tid (postπ: proph (pred' 𝔄)) :
    cctx_interp tid postπ [] ⊣⊢ True.
  Proof. iSplit; [by iIntros|]. iIntros "_ % %In". inversion In. Qed.

  Lemma cctx_interp_app {𝔄} tid postπ (C: cctx 𝔄) C' :
    cctx_interp tid postπ (C ++ C') ⊣⊢
    cctx_interp tid postπ C ∧ cctx_interp tid postπ C'.
  Proof.
    elim C. { by rewrite/= cctx_interp_nil left_id. }
    move=>/= ?? IH. by rewrite !cctx_interp_cons IH assoc.
  Qed.

  Lemma cctx_interp_singleton {𝔄} tid postπ (c: cctx_elt 𝔄) :
    cctx_interp tid postπ [c] ⊣⊢ cctx_elt_interp tid postπ c.
  Proof. by rewrite cctx_interp_cons cctx_interp_nil right_id. Qed.

  Definition cctx_incl {𝔄} (E: elctx) (C C': cctx 𝔄) : Prop :=
    ∀tid postπ, lft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ cctx_interp tid postπ C -∗ cctx_interp tid postπ C'.

  Global Instance cctx_incl_preorder {𝔄} E : PreOrder (@cctx_incl 𝔄 E).
  Proof.
    split; [iIntros (???) "_ _ _ _ $"|].
    iIntros (??? In In' ??) "#LFT #PROPH #UNIQ #E ?".
    iApply (In' with "LFT PROPH UNIQ E"). by iApply (In with "LFT PROPH UNIQ E").
  Qed.

  Lemma incl_cctx_incl {𝔄} E (C1 C2: cctx 𝔄) : C1 ⊆ C2 → cctx_incl E C2 C1.
  Proof.
    iIntros (Sub ??) "_ _ _ _ C". iIntros (? In). move/Sub in In. by iApply "C".
  Qed.

  Lemma cctx_incl_nil {𝔄} E (C: cctx 𝔄) : cctx_incl E C [].
  Proof. iIntros "%% _ _ _ _ _ % %In". inversion In. Qed.

  Lemma cctx_incl_cons {𝔄 𝔄l} k L n (T T': vec val n → tctx 𝔄l) tr tr' (C C': cctx 𝔄) E :
    cctx_incl E C C' → (∀vl, tctx_incl E L (T' vl) (T vl) tr') →
    cctx_incl E (k ◁cont{L, T} tr :: C) (k ◁cont{L, T'} (tr' ∘ tr) :: C').
  Proof.
    iIntros (InC InT ??) "LFT PROPH UNIQ E kC". rewrite !cctx_interp_cons. iSplit.
    - iDestruct "kC" as "[k _]". iIntros (??) "Na L T' Obs".
      iMod (proj2 (InT _) with "LFT PROPH UNIQ E L T' Obs") as (?) "(L & T & Obs)".
      iApply ("k" with "Na L T Obs").
    - iDestruct "kC" as "[_ ?]". by iApply (InC with "LFT PROPH UNIQ E").
  Qed.
End cont_context.

Global Hint Resolve cctx_incl_nil cctx_incl_cons : lrust_typing.
