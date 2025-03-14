From iris.proofmode Require Import proofmode.
From lrust.lang Require Import spawn.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Definition spawnN := lrustN .@ "spawn".

Section spawn.
  Context `{!typeG Σ, !spawnG Σ}.

  Definition join_future {𝔄} (ty: type 𝔄) (Φ: pred' 𝔄) (v: val) : iProp Σ :=
    ∀tid, ∃vπ d, ⟨π, Φ (vπ π)⟩ ∗ ⧖d ∗ (box ty).(ty_own) vπ d tid [v].

  (* Rust's thread::JoinHandle<T> *)
  Program Definition join_handle {𝔄} (ty: type 𝔄) : type (predₛ 𝔄) := {|
    ty_size := 1;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own Φπ _ _ vl := [loc[l] := vl] ∃Φ, ⌜Φπ = const Φ⌝ ∗
      join_handle spawnN l (join_future ty Φ);
    ty_shr Φπ _ _ _ _ := ∃Φ, ⌜Φπ = const Φ⌝;
  |}%I.
  Next Obligation. iIntros (?????[|[[]|][]]) "* ? //". Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation.
    iIntros "*% LFT _ Bor κ !>". iApply step_fupdN_full_intro.
    setoid_rewrite by_just_loc_ex.
    iMod (bor_acc with "LFT Bor κ") as "[(%& ↦ &%&>->&%&>->& join) ToBor]"; [done|].
    iMod ("ToBor" with "[↦ join]") as "[_ $]"; [|by iExists _]. iNext.
    iExists _. iFrame "↦". iExists _. iSplitR; [done|]. iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (??????[|[[]|][]]) "*% _ _ join //". iIntros "$".
    iDestruct "join" as (?->) "join". iApply step_fupdN_full_intro.
    iIntros "!>!>". iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros "_!>".
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros "* _ _ _ _ (%&->) $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). by iIntros.
  Qed.

  Global Instance join_handle_ne {𝔄} : NonExpansive (@join_handle 𝔄).
  Proof. rewrite /join_handle /join_future. solve_ne_type. Qed.

  Global Instance join_handle_type_contractive {𝔄} : TypeContractive (@join_handle 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |done]=>/= *.
    rewrite /join_future. do 15 f_equiv. by apply box_type_contractive.
  Qed.

  Global Instance join_handle_send {𝔄} (ty: type 𝔄) : Send (join_handle ty).
  Proof. done. Qed.
  Global Instance join_handle_sync {𝔄} (ty: type 𝔄) : Sync (join_handle ty).
  Proof. done. Qed.

  Lemma join_handle_resolve {𝔄} (ty: type 𝔄) E L :
    resolve E L (join_handle ty) (const True).
  Proof. apply resolve_just. Qed.

  Lemma join_handle_real {𝔄} (ty: type 𝔄) E L : real E L (join_handle ty) id.
  Proof.
    split.
    - iIntros (?????[|[[]|][]]) "_ _ _ L join //". iFrame "L".
      iDestruct "join" as (?->) "join". iApply step_fupdN_full_intro.
      iIntros "!>!>". iSplitR; [by iExists _|]. iExists _. by iFrame.
    - iIntros "*% _ _ $ % !>!>!>". by iApply step_fupdN_full_intro.
  Qed.

  Definition forward_pred {A B} (f: A → B) (Φ: pred' A) (b: B) : Prop :=
    ∃a, b = f a ∧ Φ a.

  Lemma join_handle_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f →
    subtype E L (join_handle ty) (join_handle ty') (forward_pred f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "#Incl". iPoseProof "Incl" as "#(%&?&_)".
    do 2 (iSplit; [done|]). iSplit; iModIntro; last first.
    { iIntros "* (%&->)". iExists _. iPureIntro. by fun_ext=>/=. }
    iIntros (?? tid' [|[[]|][]]) "join //". iDestruct "join" as (?->) "join".
    iExists _. iSplit. { iPureIntro. by fun_ext=>/=. }
    iApply (join_handle_impl with "[] join"). iIntros "!>% fut %tid".
    iDestruct ("fut" $! tid) as (??) "(Obs & ⧖ & box)". iExists _, _.
    iFrame "⧖". iSplitL "Obs".
    { iApply proph_obs_impl; [|done]=>/= ??. by eexists _. }
    iDestruct (box_type_incl with "Incl") as "(_&_& InO &_)". by iApply "InO".
  Qed.

  Lemma join_handle_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g →
    eqtype E L (join_handle ty) (join_handle ty') (forward_pred f) (forward_pred g).
  Proof. move=> [??]. split; by apply join_handle_subtype. Qed.

  Definition spawn (call_once: val) : val :=
    fn: ["f"] :=
      let: "call_once" := call_once in
      let: "j" := spawn
        [λ: ["c"], letcall: "r" := "call_once" ["f"] in finish ["c"; "r"]] in
      letalloc: "r" <- "j" in
      return: ["r"].

  (* Rust's thread::spawn *)
  Lemma spawn_type {𝔄 𝔅} (Φ: pred' 𝔅) tr (fty: type 𝔄) (retty: type 𝔅)
      call_once `{!Send fty, !Send retty} :
    typed_val call_once (fn(∅; fty) → retty) tr →
    let E ϝ := ty_outlives_E fty static ++ ty_outlives_E retty static in
    typed_val (spawn call_once) (fn(E; fty) → join_handle retty)
      (λ post f, tr Φ f ∧ post Φ).
  Proof.
    move=> ??. eapply type_fn; [solve_typing|]=>/= _ ??[f[]]. simpl_subst.
    via_tr_impl.
    { iApply type_val; [done|]. intro_subst_as (c).
      iApply (type_let' +[c ◁ fn(_;_)→_; f ◁ _] (λ j, +[j ◁ join_handle retty])
        (λ post '-[tr'; f], tr' Φ -[f] ∧ post -[Φ])).
      { iIntros (??(?&?&[])) "LFT TIME PROPH UNIQ E Na L (c & f &_) #Obs".
        iMod persistent_time_receipt_0 as "⧖".
        iApply (spawn_spec _ (join_future retty Φ) with "[- ⧖ Na L]"); last first.
        { iIntros "!> % join". iExists -[const Φ]. iFrame "Na L".
          iSplit; [|by iApply proph_obs_impl; [|done]=>/= ?[_ ?]]. iSplitL; [|done].
          rewrite tctx_hasty_val. iExists _. iFrame "⧖". iExists _. by iFrame. }
        iIntros (?) "/= fin". do 2 wp_let. iMod na_alloc as (tid') "Na".
        iApply (type_call_iris (𝔄l:=[_]) () -[_] [] 1%Qp (const _) with
          "LFT TIME PROPH UNIQ E Na [] c [f] [Obs]"); [solve_typing|..].
        { iApply lft_tok_static. }
        { rewrite/= right_id !tctx_hasty_val. iDestruct "f" as (?) "[??]".
          rewrite send_change_tid. iExists _. iFrame. }
        { by iApply proph_obs_impl; [|done]=>/= [?[? _]]. }
        iClear "Obs". iIntros (??) "Na _ ret Obs". wp_rec.
        iApply (finish_spec with "[$fin ret Obs]"); [|done].
        rewrite tctx_hasty_val. iDestruct "ret" as (?) "[⧖ ?]".
        iIntros (?). iExists _, _. iFrame "Obs ⧖". by rewrite send_change_tid. }
      intro_subst. iApply type_letalloc_1; [solve_extract|done|]. intro_subst.
      iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=>/= ?[?[]].
  Qed.

  Definition join: val :=
    fn: ["bj"] :=
      let: "j" := !"bj" in delete [ #1; "bj"];;
      let: "r" := spawn.join ["j"] in
      return: ["r"].

  (* Rust's JoinHandle::join *)
  Lemma join_type {𝔄} (retty: type 𝔄) :
    typed_val join (fn(∅; join_handle retty) → retty)
      (λ post '-[Φ], ∀a: 𝔄, Φ a → post a).
  Proof.
    eapply type_fn; [solve_typing|]=> _ ??[?[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing..|]. intro_subst_as (j).
      iApply type_delete; [solve_extract|done..|].
      iApply (type_let' +[_ ◁ join_handle _] (λ r, +[r ◁ box retty])
        (λ post '-[Φ], ∀a: 𝔄, Φ a → post -[a])).
      { iIntros (??[?[]]) "_ _ _ _ _ $$ /=[j _] Obs". rewrite tctx_hasty_val.
        iDestruct "j" as (?) "[_ join]". case j as [[|j|]|]=>//.
        iDestruct "join" as (?->) "join". iApply (join_spec with "join"). iNext.
        iIntros (?) "fut". iDestruct ("fut" $! _) as (??) "(Obs' &?&?)".
        iCombine "Obs Obs'" as "?". iExists -[_].
        rewrite right_id tctx_hasty_val. iSplit; [iExists _; by iFrame|].
        iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp. }
      intro_subst. iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=>/= ?[?[]].
  Qed.
End spawn.

Global Hint Resolve join_handle_resolve join_handle_real
  join_handle_subtype join_handle_eqtype : lrust_typing.
