From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Class IntoVecVal {n} (el: list expr) (vl: vec val n) :=
  into_vec_val: el = map of_val vl.

Global Instance into_vec_val_nil: IntoVecVal [] [#].
Proof. done. Qed.

Global Instance into_vec_val_cons {n} e v el (vl: _ n) :
  IntoVal e v → IntoVecVal el vl → IntoVecVal (e :: el) (v ::: vl).
Proof. by move=>/= <-->. Qed.

Section typing.
  Context `{!typeG Σ}.

  (** Jumping to and defining a continuation. *)

  Lemma type_jump {𝔄l 𝔅l ℭl 𝔇 n} (T': vec val n → tctx 𝔅l) k el
      (vl: vec val n) tr trx Φ E L (T: tctx 𝔄l) (Tx: tctx ℭl) (C: cctx 𝔇) :
    IntoVecVal el vl → k ◁cont{L, T'} tr ∈ C →
    tctx_extract_ctx E L (T' vl) T Tx trx → resolve_tctx E L Tx Φ →
    ⊢ typed_body E L C T (jump: k el)
        (trx ∘ (λ post bcl, let '(bl, cl) := psep bcl in Φ cl (tr post bl)))%type.
  Proof.
    move=> -> ? TT' Rslv. iApply typed_body_tctx_incl; [done|]. iIntros (? bcπl ?).
    move: (papp_ex bcπl)=> [?[?->]]. iIntros "LFT TIME PROPH _ E Na L C /=[T' Tx] Obs".
    iMod (Rslv with "LFT PROPH E L Tx") as (?) "[⧖ ToObs]"; [done|]. wp_bind Skip.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [ToObs]")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L. }
    wp_seq. iIntros "[Obs' L] !>". iCombine "Obs Obs'" as "#?". wp_seq.
    iApply ("C" with "[%//] Na L T' []"). iApply proph_obs_impl; [|done]=>/= ?.
    rewrite papply_app papp_sepl papp_sepr. case=> ? Imp. by apply Imp.
  Qed.

  Lemma type_cont {𝔄l 𝔅l ℭ} bl (T': vec val (length bl) → tctx 𝔅l) trk L'
        (T: tctx 𝔄l) kb ec e tr E L (C: cctx ℭ) :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k: val, typed_body E L (k ◁cont{L', T'} trk :: C) T (subst' kb k e) tr) -∗
    □(∀(k: val) (vl: vec val (length bl)), typed_body E L'
      (k ◁cont{L', T'} trk :: C) (T' vl) (subst' kb k $ subst_v bl vl ec) trk) -∗
    typed_body E L C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (??) "e #ec %%% #LFT #TIME #PROPH #UNIQ #E Na L C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME PROPH UNIQ E Na L [C] T Obs").
    iLöb as "IH". iIntros (?). rewrite elem_of_cons.
    iIntros ([->|?]); [|by iApply "C"]. iIntros (??) "Na L' T' Obs". wp_rec.
    iApply ("ec" with "LFT TIME PROPH UNIQ E Na L' [C] T' Obs"). by iApply "IH".
  Qed.

  Lemma type_cont_norec {𝔄l 𝔅l ℭ} bl (T': vec val (length bl) → tctx 𝔅l) trk
        L' (T: tctx 𝔄l) kb ec e tr E L (C: cctx ℭ) :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k: val, typed_body E L (k ◁cont{L', T'} trk :: C) T (subst' kb k e) tr) -∗
    (∀(k: val) (vl: vec val (length bl)),
      typed_body E L' C (T' vl) (subst' kb k $ subst_v bl vl ec) trk) -∗
    typed_body E L C T (letcont: kb bl := ec in e) tr.
  Proof.
    iIntros (??) "e ec %%% #LFT #TIME #PROPH #UNIQ #E Na L C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME PROPH UNIQ E Na L [ec C] T Obs").
    iIntros (?). rewrite elem_of_cons. iIntros ([->|?]); [|by iApply "C"].
    iIntros (??) "Na L' T' Obs". wp_rec.
    iApply ("ec" with "LFT TIME PROPH UNIQ E Na L' C T' Obs").
  Qed.
End typing.
