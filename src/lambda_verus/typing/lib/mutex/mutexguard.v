From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing option mutex.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(* This type is an experiment in defining a Rust type on top of a non-typesysten-specific
   interface, like the one provided by lang.lib.lock.
   It turns out that we need an accessor-based spec for this purpose, so that
   we can put the protocol into shared borrows.  Cancellable invariants
   don't work because their cancelling view shift has a non-empty mask,
   and it would have to be executed in the consequence view shift of
   a borrow.
*)

Section mutexguard.
  Context `{!typeG Σ}.

  (*
    pub struct MutexGuard<'a, T: ?Sized + 'a> {
      // funny underscores due to how Deref/DerefMut currently work (they
      // disregard field privacy).
      __lock: &'a Mutex<T>,
      __poison: poison::Guard,
    }
  *)

  Lemma split_mt_mutexguard {A B} φ (Φπ: proph A) Ψ l' :
    (l' ↦∗: λ vl, ⌜φ⌝ ∗ [loc[l] := vl] ∃(Φ: A) (κ': B), ⌜Φπ = const Φ⌝ ∗ Ψ l Φ κ') ⊣⊢
    ⌜φ⌝ ∗ ∃(l: loc) Φ κ', ⌜Φπ = const Φ⌝ ∗ l' ↦ #l ∗ Ψ l Φ κ'.
  Proof.
    iSplit.
    - iIntros "(%vl & ↦ &$& big)". case vl as [|[[]|][]]=>//.
      rewrite heap_mapsto_vec_singleton. iDestruct "big" as (??->) "?".
      iExists _, _, _. by iFrame.
    - iIntros "($&%&%&%&->& ↦ &?)". iExists [_].
      rewrite heap_mapsto_vec_singleton. iFrame "↦". iExists _, _. by iFrame.
  Qed.

  (* Rust's sync::MutexGuard<'a, T> *)
  Program Definition mutexguard {𝔄} (κ: lft) (ty: type 𝔄) : type (predₛ 𝔄) := {|
    ty_size := 1;  ty_lfts := κ :: ty.(ty_lfts);  ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    (* One logical step is required for [ty_share] *)
    ty_own Φπ d tid vl := ⌜d > 0⌝ ∗ [loc[l] := vl] ∃Φ κ',
      ⌜Φπ = const Φ⌝ ∗ κ ⊑ κ' ∗ κ' ⊑ ty_lft ty ∗
      &at{κ, mutexN} (lock_proto l (mutex_body ty Φ κ' l tid)) ∗
      mutex_body ty Φ κ' l tid;
    ty_shr Φπ _ κ' tid l := ∃Φ (l': loc) κᵢ (vπ: proph 𝔄) d,
      ⌜Φπ = const Φ⌝ ∗ κ' ⊑ κᵢ ∗ κᵢ ⊑ ty_lft ty ∗
      &frac{κ'}(λ q', l ↦{q'} #l') ∗ ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗
      □ ∀E q, ⌜↑lftN ∪ ↑shrN ⊆ E⌝ -∗ q.[κᵢ]
        ={E,E∖↑shrN}=∗ |={E∖↑shrN}▷=>^(S d) |={E∖↑shrN,E}=>
          ty.(ty_shr) vπ d κᵢ tid (l' +ₗ 1) ∗ q.[κᵢ];
  |}%I.
  Next Obligation. iIntros (??????[|[[]|][]]) "[%?] //". Qed.
  Next Obligation. iIntros "*% [%$] !%". lia. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros "%%* #Inκ' (%&%&%&%&%&->& ⊑κᵢ & κᵢ⊑ & Bor & big)".
    iExists _, _, _, _, _. iFrame "κᵢ⊑ big". iSplit; [done|].
    iSplit; [|by iApply frac_bor_shorten]. by iApply lft_incl_trans.
  Qed.
  Next Obligation.
    iIntros (????? d κ') "*% #LFT #In Bor κ' //". rewrite split_mt_mutexguard.
    iMod (bor_sep_persistent with "LFT Bor κ'") as "(>% & Bor & κ')"; [done|].
    do 3 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κ'") as "(>-> & Bor & κ')"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT Bor↦") as "#Bor↦"; [done|].
    do 2 (iMod (bor_sep_persistent with "LFT Bor κ'") as "(#? & Bor & κ')"; [done|]).
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|].
    case d as [|]; [done|]. iIntros "/=!>!>!>!>".
    iApply step_fupdN_full_intro. iMod "Bor". set κᵢ := _ ⊓ κ'.
    iAssert (κ' ⊑ κᵢ)%I as "κ'⊑κᵢ".
    { iApply lft_incl_glb; [|iApply lft_incl_refl]. iApply lft_incl_trans; [|done].
      iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    iMod (lft_incl_acc with "κ'⊑κᵢ κ'") as (?) "[κᵢ Toκ']"; [done|].
    do 2 (iMod (bor_exists_tok with "LFT Bor κᵢ") as (?) "[Bor κᵢ]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κᵢ") as "(>Obs & Bor & κᵢ)"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κᵢ") as "(>⧖ & Bor & κᵢ)"; [done|].
    iMod ("Toκ'" with "κᵢ") as "κ'".
    iMod (inv_alloc shrN _ (_ ∨ ty.(ty_shr) _ _ _ _ _)%I with "[Bor]") as "#inv".
    { iLeft. iNext. iExact "Bor". }
    iModIntro. iFrame "κ'". iExists _, _, κᵢ, _, _. iSplit; [done|].
    iFrame "Bor↦ Obs ⧖ κ'⊑κᵢ". iAssert (κᵢ ⊑ ty_lft ty)%I as "#?".
    { iApply lft_incl_trans; [iApply lft_intersect_incl_l|done]. }
    iSplit; [done|]. iIntros "!>" (???) "κᵢ".
    iInv shrN as "[Bor|#ty]" "Close"; iIntros "/=!>!>!>"; last first.
    { iApply step_fupdN_full_intro. iModIntro. iFrame "κᵢ".
      iMod ("Close" with "[]"); by [iRight|]. }
    iMod (ty_share with "LFT [] Bor κᵢ") as "Upd"; [solve_ndisj|done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[#ty $]".
    iMod ("Close" with "[]"); by [iRight|].
  Qed.
  Next Obligation.
    iIntros (???????[|[[]|][]]) "*% _ _ [% big] //". iDestruct "big" as (??->) "?".
    iIntros "$ !>". iApply step_fupdN_full_intro. iModIntro. iExists [], 1%Qp.
    do 2 (iSplit; [done|]). iIntros "_!>". iSplit; [done|]. iExists _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros "*% _ _ _ (%&%&%&%&%&->&?) $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplit; [done|]). by iIntros.
  Qed.

  Global Instance mutexguard_ne {𝔄} κ : NonExpansive (mutexguard (𝔄:=𝔄) κ).
  Proof. rewrite /mutexguard /mutex_body. solve_ne_type. Qed.

  Global Instance mutexguard_type_contractive {𝔄} κ :
    TypeContractive (mutexguard (𝔄:=𝔄) κ).
  Proof.
    split; [by eapply type_lft_morphism_add_one|done| |].
    - move=>/= *. do 10 f_equiv. { by apply equiv_dist, lft_incl_equiv_proper_r. }
      rewrite /mutex_body.
      f_equiv; [do 2 f_equiv|]; f_contractive; do 9 f_equiv; by simpl in *.
    - move=>/= *. do 13 f_equiv. { by apply equiv_dist, lft_incl_equiv_proper_r. }
      do 17 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance mutexguard_sync {𝔄} κ (ty: type 𝔄) :
    Sync ty → Sync (mutexguard κ ty).
  Proof. move=> ?>/=. by do 30 f_equiv. Qed.

  (* POSIX requires the unlock to occur from the thread that acquired
     the lock, so Rust does not implement Send for MutexGuard. We can
     prove this for our spinlock implementation, however. *)
  Global Instance mutexguard_send {𝔄} κ (ty: type 𝔄) :
    Send ty → Send (mutexguard κ ty).
  Proof.
    move=> ?>/=. rewrite /mutex_body. do 21 (f_equiv || move=>?); [|done].
    by do 2 f_equiv.
  Qed.

  (* In order to prove [mutexguard_resolve] with a non-trivial postcondition,
    we need to modify the model of [resolve] to use [⧖d] inside [ty_own] *)
  Lemma mutexguard_resolve {𝔄} κ (ty: type 𝔄) E L :
    resolve E L (mutexguard κ ty) (const True).
  Proof. apply resolve_just. Qed.

  Lemma mutexguard_real {𝔄} κ (ty: type 𝔄) E L : real E L (mutexguard κ ty) id.
  Proof.
    split.
    - iIntros (????? vl) "*% _ _ $ (%& big) !>". case vl as [|[[]|][]]=>//.
      iDestruct "big" as (??->) "?". iApply step_fupdN_full_intro. iModIntro.
      iSplit; [by iExists _|]. iSplit; [done|]. iExists _, _. by iFrame.
    - iIntros "*% _ _ $ (%&%&%&%&%&->&?) !>!>!>". iApply step_fupdN_full_intro.
      iModIntro. iSplit; [by iExists _|]. iExists _, _, _, _, _. by iFrame.
  Qed.

  Lemma mutexguard_subtype {𝔄 𝔅} κ κ' f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' f g →
    subtype E L (mutexguard κ ty) (mutexguard κ' ty') (.∘ g).
  Proof.
    move=> Lft /eqtype_unfold Eq ?. iIntros "L".
    iDestruct (Lft with "L") as "#Toκ'⊑κ". iDestruct (Eq with "L") as "#ToEq".
    iIntros "!> E". iDestruct ("Toκ'⊑κ" with "E") as "#κ'⊑κ".
    iDestruct ("ToEq" with "E") as "(%&[#?#?]& #InOwn & #InShr)". iSplit; [done|].
    iSplit; [by iApply lft_intersect_mono|]. iSplit; iModIntro.
    - iIntros (???[|[[]|][]]) "[% big] //".
      iDestruct "big" as (? κ''->) "(#?&#?& At & Mut)". iSplit; [done|]. iExists _, κ''.
      iSplit; [done|]. do 2 (iSplit; [by iApply lft_incl_trans|]).
      iDestruct (mutex_body_iff with "InOwn") as "Iff". iSplit; [|by iApply "Iff"].
      iApply at_bor_shorten; [done|]. iApply (at_bor_iff with "[] At"). iNext.
      by iApply lock_proto_iff_proper.
    - iIntros "* (%&%& %κᵢ &%&%&->&#?&#?&#?&#?&#?& #big)".
      iExists _, _, κᵢ, (f ∘ _), _. do 2 (iSplit; [done|]).
      iSplit; [by iApply lft_incl_trans|]. iSplit; [done|].
      iSplit. { iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'. }
      iSplit; [done|]. iIntros "!>" (???) "κᵢ". iMod ("big" with "[//] κᵢ") as "Upd".
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >[?$] !>". by iApply "InShr".
  Qed.
  Lemma mutexguard_eqtype {𝔄 𝔅} κ κ' f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    lctx_lft_eq E L κ' κ → eqtype E L ty ty' f g →
    eqtype E L (mutexguard κ ty) (mutexguard κ' ty') (.∘ g) (.∘ f).
  Proof.
    move=> [??][??]. split; by (eapply mutexguard_subtype; [split; apply _|..]).
  Qed.

  Lemma mutex_acc E l q κ (R: iProp Σ) :
    ↑lftN ∪ ↑mutexN ⊆ E → lft_ctx -∗ &at{κ, mutexN} (lock_proto l R) -∗
    □ (q.[κ] ={E,∅}=∗ ▷ lock_proto l R ∗ (▷ lock_proto l R ={∅,E}=∗ q.[κ])).
  Proof.
    iIntros (?) "#LFT #At !> κ".
    iMod (at_bor_acc_tok with "LFT At κ") as "[Prt Toκ]"; [solve_ndisj..|].
    iApply fupd_mask_intro; [set_solver|]. iIntros "End". iFrame "Prt". by iMod "End".
  Qed.

  Definition mutex_lock : val :=
    fn: ["bm"] :=
      let: "m" := !"bm" in acquire ["m"];;
      letalloc: "g" <- "m" in
      delete [ #1; "bm"];; return: ["g"].

  (* Rust's Mutex::lock *)
  Lemma mutex_lock_type {𝔄} (ty: type 𝔄) :
    typed_val mutex_lock (fn<α>(∅; &shr{α} (mutex ty)) → mutexguard α ty)
      (λ post '-[Φ], post Φ).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[bm[]]. simpl_subst.
    iIntros (?[?[]]?) "#LFT TIME _ _ E Na L C /=[bm _] #Obs". rewrite tctx_hasty_val.
    iDestruct "bm" as ([|d]) "[⧖ box]"=>//. case bm as [[|bm|]|]=>//=.
    rewrite split_mt_ptr. iDestruct "box" as "[↦mtx †m]".
    case d as [|]; [by iDestruct "↦mtx" as ">[]"|].
    iDestruct "↦mtx" as (?) "(↦m &%&%&>->& ? & ? & #At)". wp_read. wp_let.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    wp_apply (acquire_spec with "[] α"). { by iApply (mutex_acc with "LFT At"). }
    iIntros "[Bor α]". wp_seq. wp_apply wp_new; [done..|]. iIntros (?) "[†g ↦g]".
    wp_let. rewrite heap_mapsto_vec_singleton. wp_write.
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    wp_apply (wp_delete with "[$↦m $†m]"); [done|]. iIntros "_". do 3 wp_seq.
    iMod ("ToL" with "α L") as "L". rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[_] with "Na L [-] Obs").
    rewrite/= right_id (tctx_hasty_val #_). iExists _. iSplit; [done|].
    rewrite -freeable_sz_full. iFrame "†g". iNext. rewrite split_mt_mutexguard.
    iSplit; [done|]. iExists _, _, _. iFrame "At". by iFrame.
  Qed.

  Definition mutexguard_deref: val :=
    fn: ["g"] :=
      let: "g'" := !"g" in let: "m" := !"g'" in
      letalloc: "r" <- "m" +ₗ #1 in
      delete [ #1; "g"];; return: ["r"].

  (* Rust's MutexGuard::deref_mut *)
  Lemma mutexguard_deref_uniq_type {𝔄} Ψ (ty: type 𝔄) :
    typed_val mutexguard_deref
      (fn<(α, β)>(∅; &uniq{α} (mutexguard β ty)) → &uniq{α} (!{Ψ} ty))
      (λ post '-[(Φ, Φ')], Φ ≡ Ψ ∧ ∀a a': 𝔄, Φ a → Φ' = Φ → post (a, a')).
  Proof.
    eapply type_fn; [apply _|]=>/= αβ ??[g[]]. case αβ=> α β. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ E Na L C /=[g _] Obs".
    rewrite tctx_hasty_val. iDestruct "g" as ([|d]) "[_ box]"=>//.
    case g as [[|g|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#α⊑βty &%&%& %ξi &>[% %Eq]& ↦g & Vo & Bor) †g]".
    wp_read. move: Eq. set ξ := PrVar _ ξi=> Eq.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "([α α₊] & L & ToL)";
      [solve_typing..|].
    do 2 (iMod (bor_exists_tok with "LFT Bor α") as (?) "[Bor α]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor α") as "(_& Bor & α)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorPc Bor]"; [done|].
    iMod (bor_acc with "LFT BorPc α₊") as "[Pc Toα₊]"; [done|]. wp_let.
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_mutexguard.
    iMod (bor_sep_persistent with "LFT Bor α") as "(>% & Bor & α)"; [done|].
    iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_exists with "LFT Bor") as (Φ) "Bor"; [done|].
    iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_sep_persistent with "LFT Bor α") as "(>%Eq' & Bor & α)"; [done|].
    have ->: vπ = λ π, (Φ, π ξ). { by rewrite [vπ]surjective_pairing_fun Eq Eq'. }
    iMod (uniq_resolve ξ [] 1%Qp (const Φ) with "PROPH Vo Pc [//]")
      as "(Obs' & Pc &_)"; [done|done|]. iCombine "Obs' Obs" as "Obs".
    iMod ("Toα₊" with "Pc") as "[_ α₊]". iCombine "α α₊" as "α".
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_acc with "LFT Bor↦ α") as "[>↦l Toα]"; [done|]. wp_read.
    iMod ("Toα" with "↦l") as "[_ α]".
    iMod (bor_sep_persistent with "LFT Bor α") as "(#β⊑κ & Bor & α)"; [done|].
    do 2 (iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|]).
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|]. wp_let. iMod "Bor".
    wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]".
    set κ' := _ ⊓ α. iAssert (α ⊑ κ')%I as "#α⊑κ'".
    { iApply lft_incl_glb; [|iApply lft_incl_refl]. iApply lft_incl_trans; [|done].
      iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    iMod (lft_incl_acc with "α⊑κ' α") as (?) "[κ' Toα]"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ'") as "[big ToBor]"; [done|]. wp_let.
    iDestruct "big" as (aπ dᵢ) "(Obs' & #⧖ &%& ↦ & ty)".
    iCombine "Obs Obs'" as "#Obs". wp_op. rewrite heap_mapsto_vec_singleton.
    wp_write. wp_bind (delete _).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_delete with "[$↦g $†g]"); [done|]. iIntros "!>_ #⧖S". do 3 wp_seq.
    iMod (uniq_intro aπ with "PROPH UNIQ") as (ζj) "[Vo' Pc']"; [done|].
    set ζ := PrVar _ ζj. iMod ("ToBor" with "[] [Pc' ↦ ty]") as "[Bor κ']"; last first.
    - iMod ("Toα" with "κ'") as "α". iMod ("ToL" with "α L") as "L".
      rewrite cctx_interp_singleton.
      iApply ("C" $! [# #_] -[λ π, (aπ π, π ζ)] with "Na L [-] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= ?[[->[? Imp]]?]. by apply Imp. }
      rewrite/= right_id (tctx_hasty_val #_) -freeable_sz_full. iExists _.
      iFrame "⧖S †r". iNext. rewrite split_mt_uniq_bor. iSplit.
      { iApply lft_incl_trans; [iApply "α⊑βty"|]. iApply lft_intersect_incl_r. }
      iExists _, dᵢ, ζj. iSplit; [done|]. iFrame "↦r Vo'". by iApply bor_shorten.
    - iNext. iExists _, _. iFrame "⧖ Pc'". iExists _. iFrame "↦ ty".
      iApply proph_obs_impl; [|done]=>/= ?[[_[Eqv _]]?]. by apply Eqv.
    - iIntros "!> big !>!>". iDestruct "big" as (??) "(⧖' & Pc' &%& ↦ & Obs' & ty)".
      iCombine "Obs Obs'" as "#?". iExists _, _. iFrame "⧖'".
      iSplit; [|iExists _; by iFrame].
      iApply proph_obs_impl; [|done]=>/= ?[[[_[Eqv _]]_]?]. by apply Eqv.
  Qed.

  (* Rust's MutexGuard::deref *)
  Lemma mutexguard_deref_shr_type {𝔄} (ty: type 𝔄) :
    typed_val mutexguard_deref
      (fn<(α, β)>(∅; &shr{α} (mutexguard β ty)) → &shr{α} ty)
      (λ post '-[Φ], ∀a: 𝔄, Φ a → post a).
  Proof.
    eapply type_fn; [apply _|]=>/= αβ ??[g[]]. case αβ=> α β. simpl_subst.
    iIntros (?[?[]]?) "LFT #TIME _ _ #E Na L C /=[g _] Obs". rewrite tctx_hasty_val.
    iDestruct "g" as ([|d]) "[_ box]"=>//. case g as [[|g|]|]=>//=.
    rewrite split_mt_ptr. iDestruct "box" as "[↦guard †g]".
    case d as [|]; [by iDestruct "↦guard" as ">[]"|].
    iDestruct "↦guard" as (?) "(↦g & guard)". wp_read. wp_let.
    iDestruct "guard" as (?????->) "(#⊑κᵢ &?& Bor↦ & Obs' & #⧖ & #Upd)".
    iCombine "Obs Obs'" as "#?".
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)";
      [solve_typing..|].
    iMod (frac_bor_acc with "LFT Bor↦ α") as (?) "[>↦l Toα]"; [done|].
    wp_read. wp_let. iMod ("Toα" with "↦l") as "α".
    iMod (lft_incl_acc with "⊑κᵢ α") as (?) "[κᵢ Toα]"; [done|].
    wp_bind (new _). iSpecialize ("Upd" $! ⊤ with "[//] κᵢ").
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]");
      [done|done| |].
    { iApply step_fupdN_with_emp. rewrite difference_empty_L.
      iApply (step_fupdN_nmono (S _)); [|done]. lia. }
    iApply wp_new; [done..|]. iIntros "!>% [†r ↦r] [ty κᵢ] !>". wp_let.
    iMod ("Toα" with "κᵢ") as "α". iMod ("ToL" with "α L") as "L".
    rewrite heap_mapsto_vec_singleton. wp_op. wp_write. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iClear "⧖".
    iApply (wp_delete with "[$↦g $†g]"); [done|]. iIntros "!>_ #⧖".
    do 3 wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[_] with "Na L [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp. }
    rewrite/= right_id (tctx_hasty_val #_). iExists _. iSplit; [done|].
    rewrite/= freeable_sz_full. iFrame "†r". iNext. iExists [_].
    rewrite heap_mapsto_vec_singleton. iFrame "↦r". by iApply ty_shr_lft_mono.
  Qed.

  Definition mutexguard_drop: val :=
    fn: ["g"] :=
      release [!"g"];; delete [ #1; "g"];;
      return: [new [ #0]].

  (* Rust's MutexGuard::drop *)
  Lemma mutexguard_drop_type {𝔄} (ty: type 𝔄) :
    typed_val mutexguard_drop (fn<α>(∅; mutexguard α ty) → ())
      (λ post '-[_], post ()).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[g[]]. simpl_subst.
    iIntros (?[?[]]?) "#LFT _ _ _ E Na L C /=[g _] #Obs". rewrite tctx_hasty_val.
    iDestruct "g" as ([|d]) "[⧖ box]"=>//. case g as [[|g|]|]=>//=.
    rewrite split_mt_mutexguard. iDestruct "box" as "((>%&%&%&%&>->& ↦g & big) & †g)".
    wp_read. iDestruct "big" as "(_&_& #At & Bor)".
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    wp_apply (release_spec with "[] [α Bor]");
      [by iApply (mutex_acc with "LFT At")|by iFrame|].
    iIntros "α". wp_seq. iMod ("ToL" with "α L") as "L". wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_delete with "[$↦g $†g]"); [done|]. iIntros "!>_". do 3 wp_seq.
    wp_apply wp_new; [done..|]. iIntros (?) "[†r ↦r]".
    rewrite cctx_interp_singleton. iApply ("C" $! [# #_] -[_] with "Na L [-] Obs").
    rewrite/= right_id (tctx_hasty_val #_). iExists _. iSplit; [done|].
    rewrite -freeable_sz_full. iFrame "†r". iNext. iExists _. iFrame "↦r".
    by rewrite unit_ty_own.
  Qed.

  (* TODO: Should we do try_lock? *)
End mutexguard.

Global Hint Resolve mutexguard_resolve mutexguard_real
  mutexguard_subtype mutexguard_eqtype : lrust_typing.
