From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From lrust.lang.lib Require Import memcpy lock.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Definition mutexN := lrustN .@ "mutex".

Section mutex.
  Context `{!typeG Σ}.

  (*
    pub struct Mutex<T: ?Sized> {
      // Note that this mutex is in a *box*, not inlined into the struct itself.
      // Once a native mutex has been used once, its address can never change (it
      // can't be moved). This mutex type can be safely moved at any time, so to
      // ensure that the native mutex is used correctly we box the inner lock to
      // give it a constant address.
      inner: Box<sys::Mutex>,
      poison: poison::Flag,
      data: UnsafeCell<T>,
    }
  *)

  Definition mutex_body {𝔄} (ty: type 𝔄) (Φ: pred' 𝔄) (κ: lft)
      (l: loc) (tid: thread_id) : iProp Σ :=
    &{κ} (∃vπ d, ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗ (l +ₗ 1) ↦∗: ty.(ty_own) vπ d tid).

  Lemma mutex_body_iff {𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty ty' Φ κ l tid :
    □ (∀vπ d tid vl, ty_own ty vπ d tid vl ↔ ty_own ty' (f ∘ vπ) d tid vl) -∗
    □ (mutex_body ty Φ κ l tid ↔ mutex_body ty' (Φ ∘ g) κ l tid).
  Proof.
    iIntros "#EqOwn". iApply bor_iff_proper. iIntros "!>!>".
    iSplit; iIntros "(%&% & Obs & ⧖ &%& ↦ & ty)".
    - iExists (f ∘ _), _. iFrame "⧖". iSplitL "Obs".
      { iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'. }
      iExists _. iFrame "↦". by iApply "EqOwn".
    - iExists (g ∘ _), _. iFrame "⧖ Obs". iExists _. iFrame "↦".
      iApply "EqOwn". by rewrite compose_assoc semi_iso.
  Qed.

  Lemma split_mt_mutex {𝔄} Ψ l (Φπ: proph (pred' 𝔄)) :
    (l ↦∗: λ vl, ∃Φ (b: bool) vl' vπ d,
      ⌜vl = #b :: vl' ∧ Φπ = const Φ⌝ ∗ ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗ Ψ vπ d vl') ⊣⊢
    (∃Φ (b: bool) vπ d, ⌜Φπ = const Φ⌝ ∗
      l ↦ #b ∗ ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗ (l +ₗ 1) ↦∗: Ψ vπ d).
  Proof.
    iSplit.
    - iIntros "(%& ↦ &%&%&%&%&%&[->%]& Obs & ⧖ &?)". iExists _, _, _, _.
      rewrite heap_mapsto_vec_cons. iDestruct "↦" as "[$ ?]". iFrame "Obs ⧖".
      iSplit; [done|]. iExists _. iFrame.
    - iIntros "(%&%&%&%&%& ↦b & Obs & ⧖ &%& ↦ &?)". iExists (_::_).
      rewrite heap_mapsto_vec_cons. iFrame "↦b ↦". iExists _, _, _, _, _. by iFrame.
  Qed.

  (* Rust's sync::Mutex<T> *)
  Program Definition mutex {𝔄} (ty: type 𝔄) : type (predₛ 𝔄) := {|
      ty_size := 1 + ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
      ty_own Φπ _ tid vl := ∃Φ (b: bool) vl' (vπ: proph 𝔄) d,
        ⌜vl = #b :: vl' ∧ Φπ = const Φ⌝ ∗
        ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗ ty.(ty_own) vπ d tid vl';
      ty_shr Φπ _ κ tid l := ∃Φ κ', ⌜Φπ = const Φ⌝ ∗ κ ⊑ κ' ∗ κ' ⊑ ty_lft ty ∗
        &at{κ, mutexN} (lock_proto l (mutex_body ty Φ κ' l tid));
    |}%I.
  Next Obligation.
    iIntros "* (%&%&%&%&%&[->_]&_&_& ty) /=". rewrite ty_size_eq.
    by iDestruct "ty" as %->.
  Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    iIntros "* #? (%&%&%&#?&?&?)". iExists _, _. iSplit; [done|].
    iSplit; [|iSplit; [done|]]; by [iApply lft_incl_trans|iApply at_bor_shorten].
  Qed.
  Next Obligation.
    iIntros "*% #LFT #In Bor κ !>". iApply step_fupdN_full_intro. rewrite split_mt_mutex.
    iMod (bor_acc_cons with "LFT Bor κ") as "[(%&%& big) ToBor]"; [done|].
    iMod (bi.later_exist_except_0 with "big") as (??) "(>->& ↦b & >Obs & >⧖ & ↦ty)".
    iMod ("ToBor" $! ((∃b: bool, l ↦ #b) ∗
      ∃vπ d, ⟨π, Φ (vπ π)⟩ ∗ ⧖(S d) ∗ (l +ₗ 1) ↦∗: ty.(ty_own) vπ d tid)%I
      with "[] [↦b Obs ⧖ ↦ty]") as "[Bor κ]".
    { iIntros "!> big !>!>". iDestruct "big" as "[[% ↦b] (%&%& Obs & ⧖ &%& ↦ &?)]".
      iExists _, _, _, _. iFrame "↦b Obs ⧖". iSplit; [done|]. iExists _. iFrame. }
    { iNext. iSplitL "↦b"; [by iExists _|]. iExists _, _. iFrame. }
    iMod (bor_sep with "LFT Bor") as "[Borb Borty]"; [done|]. clear b.
    iMod (bor_acc_cons with "LFT Borb κ") as "[>(%b & ↦b) ToBorb]"; [done|].
    iMod (lock_proto_create with "↦b [Borty]") as "Proto".
    { case b; [done|]. by iExact "Borty". }
    iMod ("ToBorb" with "[] Proto") as "[Bor $]".
    { iIntros "!> Proto !>!>".
      iDestruct (lock_proto_destroy with "Proto") as (?) "[? _]". by iExists _. }
    iExists _, _. iMod (bor_share with "Bor") as "$"; [solve_ndisj|].
    iFrame "In". iSplitR; [done|]. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros "*% _ _ (%&%&%&%&%&[->->]&?) $ !>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). iIntros "_!>".
    iExists _, _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros "*% _ _ _ (%&%&->&?) $ !>!>!>". iApply step_fupdN_full_intro.
    iModIntro. iExists [], 1%Qp. do 2 (iSplitR; [done|]). by iIntros.
  Qed.

  Global Instance mutex_ne {𝔄} : NonExpansive (@mutex 𝔄).
  Proof. rewrite /mutex /mutex_body. solve_ne_type. Qed.

  Global Instance mutex_type_ne {𝔄} : TypeNonExpansive (@mutex 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|by move=>/= ??->|..].
    - move=>/= *. by do 13 f_equiv.
    - move=>/= *. do 7 f_equiv. { by apply equiv_dist, lft_incl_equiv_proper_r. }
      rewrite /mutex_body. do 12 (f_contractive || f_equiv). simpl in *. by apply dist_S.
  Qed.

  Global Instance mutex_send {𝔄} (ty: type 𝔄) : Send ty → Send (mutex ty).
  Proof. move=> ?>/=. by do 13 f_equiv. Qed.

  Global Instance mutex_sync {𝔄} (ty: type 𝔄) : Send ty → Sync (mutex ty).
  Proof. move=> ?>/=. rewrite /mutex_body. by do 19 f_equiv. Qed.

  (* In order to prove [mutex_resolve] with a non-trivial postcondition,
    we need to modify the model of [resolve] to use [⧖d] inside [ty_own] *)
  Lemma mutex_resolve {𝔄} (ty: type 𝔄) E L : resolve E L (mutex ty) (const True).
  Proof. apply resolve_just. Qed.

  Lemma mutex_real {𝔄} (ty: type 𝔄) E L : real E L (mutex ty) id.
  Proof.
    split.
    - iIntros "*% _ _ $ (%&%&%&%&%&[->->]&?)". iApply step_fupdN_full_intro.
      iSplitR; [by iExists _|]. iExists _, _, _, _, _. by iFrame.
    - iIntros "*% _ _ $ (%&%&->&?)!>!>!>". iApply step_fupdN_full_intro.
      iSplitR; [by iExists _|]. iExists _, _. by iFrame.
  Qed.

  Lemma mutex_subtype {𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    eqtype E L ty ty' f g → subtype E L (mutex ty) (mutex ty') (.∘ g).
  Proof.
    move=> /eqtype_unfold Eq ?. iIntros "L". iDestruct (Eq with "L") as "#Eq".
    iIntros "!> E". iDestruct ("Eq" with "E") as "(%EqSz & [#? #?] & #EqOwn &_)".
    iSplit; [by rewrite/= EqSz|]. iSplit; [done|]. iSplit; iIntros "!> *".
    - iDestruct 1 as (?????[->->]) "(?& ⧖ & ty)". iExists _, _, _, (f ∘ _), _.
      iSplit; [done|]. iFrame "⧖". iSplitR "ty"; [|by iApply "EqOwn"].
      iApply proph_obs_eq; [|done]=>/= ?. by rewrite semi_iso'.
    - iDestruct 1 as (??->) "(In & #In' & At)". iExists _, _. iSplit; [done|].
      iFrame "In". iSplit; [by iApply lft_incl_trans|].
      iApply (at_bor_iff with "[] At"). iNext. iApply lock_proto_iff_proper.
      by iApply mutex_body_iff.
  Qed.
  Lemma mutex_eqtype {𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (mutex ty) (mutex ty') (.∘ g) (.∘ f).
  Proof. move=> [??]. split; by (eapply mutex_subtype; [split; apply _|]). Qed.

  (* Rust's Mutex::new *)
  Definition mutex_new {𝔄} (ty: type 𝔄) : val :=
    fn: ["x"] :=
      let: "m" := new [ #(mutex ty).(ty_size)] in
      "m" +ₗ #1 <-{ty.(ty_size)} !"x";;
      mklock_unlocked ["m" +ₗ #0];;
      delete [ #ty.(ty_size); "x"];; return: ["m"].

  Lemma mutex_new_type {𝔄} Φ (ty: type 𝔄) :
    typed_val (mutex_new ty) (fn(∅; ty) → mutex ty)
      (λ post '-[a], Φ a ∧ post Φ).
  Proof.
    eapply type_fn; [apply _|]=> _ ??[x[]]. simpl_subst.
    iIntros (?[?[]]?) "_ _ _ _ _ Na L C /=[x _] #Obs".
    rewrite tctx_hasty_val. iDestruct "x" as ([|]) "[#⧖ box]"=>//.
    case x as [[|x|]|]=>//=. iDestruct "box" as "[(%& >↦x & ty) †x]".
    wp_apply wp_new; [done..|]. iIntros (?) "[†m ↦m]".
    iDestruct (ty_size_eq with "ty") as %Szvl.
    rewrite Nat2Z.id /= heap_mapsto_vec_cons. iDestruct "↦m" as "[↦b ↦m]". wp_let.
    wp_op. wp_apply (wp_memcpy with "[$↦m $↦x]"); [by rewrite repeat_length|lia|].
    iIntros "[↦m ↦x]". wp_seq. wp_op. rewrite shift_loc_0. wp_rec. wp_write.
    wp_apply (wp_delete with "[$↦x †x]"); [lia| |]. { by rewrite freeable_sz_full Szvl. }
    iIntros "_". do 3 wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const Φ] with "Na L [-] []"); last first.
    { by iApply proph_obs_impl; [|done]=>/= ?[_ ?]. }
    rewrite/= right_id (tctx_hasty_val #_). iExists _. iFrame "⧖".
    rewrite/= freeable_sz_full. iFrame "†m". iNext. rewrite split_mt_mutex.
    iExists _, _, _, _. iSplit; [done|]. iFrame "↦b ⧖".
    iSplit; last first. { iExists _. iFrame. }
    by iApply proph_obs_impl; [|done]=>/= ?[? _].
  Qed.

  (* Rust's Mutex::into_inner *)
  Definition mutex_into_inner {𝔄} (ty: type 𝔄) : val :=
    fn: ["m"] :=
      let: "x" := new [ #ty.(ty_size)] in
      "x" <-{ty.(ty_size)} !("m" +ₗ #1);;
      delete [ #(mutex ty).(ty_size); "m"];; return: ["x"].

  Lemma mutex_into_inner_type {𝔄} (ty: type 𝔄) :
    typed_val (mutex_into_inner ty) (fn(∅; mutex ty) → ty)
      (λ post '-[Φ], ∀a: 𝔄, Φ a → post a).
  Proof.
    eapply type_fn; [apply _|]=>/= _ ??[m[]]. simpl_subst.
    iIntros (?[?[]]?) "_ _ _ _ _ Na L C /=[m _] Obs". rewrite tctx_hasty_val.
    iDestruct "m" as ([|]) "[_ box]"=>//. case m as [[|m|]|]=>//=.
    rewrite split_mt_mutex. iDestruct "box" as "[↦mtx †m]".
    wp_apply wp_new; [lia|done|]. rewrite Nat2Z.id. iIntros (?) "[†x ↦x]".
    wp_let. iDestruct "↦mtx" as (????->) "(↦b & Obs' & ⧖ &%& ↦m & ty)".
    iCombine "Obs Obs'" as "#?". iDestruct (ty_size_eq with "ty") as %Szvl. wp_op.
    wp_apply (wp_memcpy with "[$↦x $↦m]"); [|lia|]. { by rewrite repeat_length. }
    iIntros "[↦x ↦m]". wp_seq. wp_apply (wp_delete (_::_) with "[↦b ↦m †m]"); swap 1 2.
    { rewrite heap_mapsto_vec_cons freeable_sz_full -Szvl. iFrame. } { simpl. lia. }
    iIntros "_". do 3 wp_seq. rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[_] with "Na L [-]"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp. }
    rewrite/= right_id (tctx_hasty_val #_). iExists _. iFrame "⧖".
    rewrite/= freeable_sz_full. iFrame "†x". iNext. iExists _. iFrame.
  Qed.

  (* Rust's Mutex::get_mut *)
  Definition mutex_get_uniq: val :=
    fn: ["m"] :=
      let: "m'" := !"m" in
      "m" <- ("m'" +ₗ #1);;
      return: ["m"].

  (* The final invariant of [&uniq{α} (mutex ty)] should be trivial,
    because [&uniq{α} ty] does not restrict the target value *)
  Lemma mutex_get_uniq_type {𝔄} (ty: type 𝔄) :
    typed_val mutex_get_uniq (fn<α>(∅; &uniq{α} (mutex ty)) → &uniq{α} ty)
      (λ post '-[(Φ, Φ')], ∀a a': 𝔄, Φ a → Φ' = const True → post (a, a')).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[m[]]. simpl_subst.
    iIntros (?[vπ[]]?) "LFT TIME #PROPH UNIQ E Na L C /=[m _] Obs".
    rewrite tctx_hasty_val. iDestruct "m" as ([|]) "[_ box]"=>//.
    case m as [[|m|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In &%&%& %ξi &>[% %Eq1]& ↦ & Vo & Bor) †m]".
    move: Eq. set ξ := PrVar _ ξi=> Eq. wp_read. setoid_rewrite split_mt_mutex.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Bor α") as "[big ToBor]"; [done|]. wp_let.
    iDestruct "big" as (??) "(_& Pc &%&%& %aπ &%&->& ↦b & Obs' & #⧖ & ↦ty)".
    iCombine "Obs Obs'" as "Obs". iDestruct (uniq_agree with "Vo Pc") as %[Eq2 _].
    wp_op. wp_bind (_ <- _)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    wp_write. iIntros "#⧖S". do 3 wp_seq.
    iMod (uniq_preresolve ξ [] (const (const True)) 1%Qp with "PROPH Vo Pc []")
      as "(Obs' &_& ToPc)"; [done..|]. iCombine "Obs' Obs" as "#Obs"=>/=.
    iMod (uniq_intro aπ with "PROPH UNIQ") as (ζj) "[Vo' Pc']"; [done|].
    set ζ := PrVar _ ζj.
    iMod ("ToBor" with "[↦b ToPc] [↦ty Pc']") as "[Bor α]"; last first.
    - rewrite cctx_interp_singleton. iMod ("ToL" with "α L") as "L".
      iApply ("C" $! [# #_] -[λ π, (aπ π, π ζ)] with "Na L [-] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= π.
        move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=.
        case (vπ π)=>/= ??->->[->[Imp ?]]. by apply Imp. }
      rewrite/= right_id (tctx_hasty_val #_). iExists _. iFrame "⧖S".
      rewrite/= freeable_sz_full. iFrame "†m". iNext. rewrite split_mt_uniq_bor.
      iFrame "In". iExists _, _, _. by iFrame.
    - iNext. iExists _, _. by iFrame.
    - iIntros "!> big !>!>". iDestruct "big" as (??) "(⧖' &_& ↦ty)".
      iExists _, _. iFrame "⧖".
      iSplitL "ToPc". { iApply "ToPc". iApply proph_eqz_refl. }
      iExists _, _, _, _. iSplit; [done|]. iFrame "↦b ⧖' ↦ty".
      by iApply proph_obs_true.
  Qed.
End mutex.

Global Hint Resolve mutex_resolve mutex_real mutex_subtype mutex_eqtype
  : lrust_typing.
