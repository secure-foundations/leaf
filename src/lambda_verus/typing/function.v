Import EqNotations.
From lrust.typing Require Export type.
From lrust.typing Require Import own programs cont.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Fixpoint subst_plv {𝔄l} (bl: plistc binder 𝔄l) (vl: plistc val 𝔄l) (e: expr) : expr :=
  match 𝔄l, bl, vl with
  | [], _, _ => e
  | _::_, b -:: bl', v -:: vl' => subst' b v (subst_plv bl' vl' e)
  end.

Global Instance do_subst_plv {𝔄l} (bl vl: plistc _ 𝔄l) e :
  DoSubstL bl (map of_val vl) e (subst_plv bl vl e).
Proof.
  rewrite /DoSubstL. induction 𝔄l, bl, vl; [done|]=>/=. by rewrite IH𝔄l.
Qed.

Lemma subst_plv_renew {𝔄l 𝔅l} (bl: plistc binder 𝔄l) (vl': plistc val 𝔅l) eq eq' e :
  subst_plv (plistc_renew eq bl) vl' e =
    subst_plv bl (plistc_renew eq' vl') e.
Proof.
  move: 𝔄l 𝔅l bl vl' eq eq'. fix FIX 1.
  case=> [|??]; case=>//= ??[??][??]??. f_equal. apply FIX.
Qed.

Section fn.
  Context `{!typeG Σ} {A: Type} {𝔄l 𝔅}.

  Record fn_params :=
    FP { fp_E_ex: lft → elctx;  fp_ityl: typel 𝔄l;  fp_oty: type 𝔅 }.

  Definition fn_params_dist n fp fp' : Prop :=
    (∀ϝ, fp.(fp_E_ex) ϝ = fp'.(fp_E_ex) ϝ) ∧
    fp.(fp_ityl) ≡{n}≡ fp'.(fp_ityl) ∧ fp.(fp_oty) ≡{n}≡ fp'.(fp_oty).

  Definition fp_E (fp: fn_params) ϝ : elctx :=
    fp.(fp_E_ex) ϝ ++ tyl_E fp.(fp_ityl) ++ tyl_outlives_E fp.(fp_ityl) ϝ ++
    fp.(fp_oty).(ty_E) ++ ty_outlives_E fp.(fp_oty) ϝ.

  Global Instance fp_E_ne n : Proper (fn_params_dist n ==> (=) ==> (=)) fp_E.
  Proof.
    rewrite /fp_E. move=> ?? Eq ??->. move: Eq=> [->[Eqi Eqo]].
    f_equiv. do 2 (f_equiv; [by rewrite Eqi|]). by rewrite Eqo.
  Qed.

  Lemma elctx_sat_fp_E (fp: fn_params) ϝ ϝ' L :
    fp_E_ex fp = const [] →
    elctx_sat (ϝ' ⊑ₑ ϝ :: fp_E fp ϝ) L (fp_E fp ϝ').
  Proof.
    move=> Eq. rewrite /fp_E Eq /=. apply elctx_sat_app; [solve_typing|].
    apply elctx_sat_app. { apply (tyl_outlives_E_elctx_sat_mono ϝ'); solve_typing. }
    apply elctx_sat_app; [solve_typing|].
    apply (ty_outlives_E_elctx_sat_mono ϝ'); solve_typing.
  Qed.

  Definition tr_ret {𝔄} : predl_trans' [𝔄] 𝔄 := λ post '-[a], post a.

  Program Definition fn (fp: A → fn_params) : type (predl_trans'ₛ 𝔄l 𝔅) :=
    {| (* FIXME : The definition of ty_lfts is less restrictive than the one
          used in Rust. In Rust, the type of parameters are taken into account
          for well-formedness, and all the liftime constrains relating a
          generalized liftime are ignored. For simplicity, we ignore all of
          them, but this is not very faithful. *)
      pt_size := 1;
      pt_own (tr: predl_trans'ₛ _ _) tid vl := tc_opaque
        (∃fb kb (bl: plistc _ _) e H, ⌜vl = [@RecV fb (kb :: bl) e H]⌝ ∗
          ▷ □ ∀x ϝ k (wl: plistc _ _),
            typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
              [k ◁cont{[ϝ ⊑ₗ []], λ v: vec _ 1, +[vhd v ◁ box (fp x).(fp_oty)] } tr_ret]
              (hzip_with (λ _ ty (w: val), w ◁ box ty) (fp x).(fp_ityl) wl)
              (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
              tr)
    |}%I.
  Next Obligation. rewrite /tc_opaque. apply _. Qed.
  Next Obligation. move=> *. by iDestruct 1 as (?????->) "?". Qed.

  Global Instance fn_ne n :
    Proper (pointwise_relation A (fn_params_dist n) ==> dist n) fn.
  Proof.
    move=> fp fp' Eq. apply ty_of_st_ne, st_of_pt_ne. split; [done|]=>/= ???.
    do 5 apply bi.exist_ne=> ?. do 3 f_equiv. f_equiv=> x. (do 5 f_equiv)=> wl.
    rewrite /typed_body. (do 3 f_equiv)=> vπl.
    do 8 f_equiv; [by eapply fp_E_ne|]. do 2 f_equiv; [|f_equiv].
    - rewrite !cctx_interp_singleton /cctx_elt_interp. do 3 f_equiv.
      case=>/= [??]. rewrite /tctx_elt_interp. do 12 f_equiv. apply Eq.
    - move: (Eq x)=> [_[+ _]]. rewrite {1}/dist.
      move: (fp x).(fp_ityl) (fp' x).(fp_ityl)=> ??. clear=> Eq.
      induction Eq; [done|]. case wl=> ??. case vπl=> ??/=.
      f_equiv; [|by apply IHEq]. rewrite /tctx_elt_interp. by do 8 f_equiv.
  Qed.
End fn.

Arguments fn_params {_ _} _ _.

Global Instance elctx_empty : Empty (lft → elctx) := λ _, [].

Notation "fn< p > ( E ; ity , .. , ity' ) → oty" :=
  (fn (λ p, FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn< p > ( E ) → oty" := (fn (λ p, FP E%EL +[] oty%T))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E )  →  oty") : lrust_type_scope.
Notation "fn( E ; ity , .. , ity' ) → oty" :=
  (fn (λ _: (), FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T))
  (at level 99, oty at level 200, format
    "fn( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn( E ) → oty" := (fn (λ _: (), FP E%EL +[] oty%T))
  (at level 99, oty at level 200, format "fn( E )  →  oty") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance fn_type_contractive {A 𝔄l 𝔅 ℭ} E
         (IT: A → type ℭ → typel 𝔄l) (OT: A → type ℭ → type 𝔅) :
    (∀x, ListTypeNonExpansive (IT x)) → (∀x, TypeNonExpansive (OT x)) →
    TypeContractive (λ ty, fn (λ x, FP (E x) (IT x ty) (OT x ty))).
  Proof.
    move=> NeIT NeOT.
    have Eq: (∀n ty ty', ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
      elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
      (∀vπ d tid vl, dist_later n (ty.(ty_own) vπ d tid vl) (ty'.(ty_own) vπ d tid vl)) →
      (∀vπ d κ tid l, (ty.(ty_shr) vπ d κ tid l) ≡{n}≡ (ty'.(ty_shr) vπ d κ tid l)) →
      ∀vπ vl,
        (fn (λ x, FP (E x) (IT x ty) (OT x ty))).(ty_own) vπ 0 xH vl ≡{n}≡
        (fn (λ x, FP (E x) (IT x ty') (OT x ty'))).(ty_own) vπ 0 xH vl); last first.
    { split; [|done| |].
      - apply (type_lft_morphism_const _ static [])=>//= ?. apply lft_equiv_refl.
      - move=> *. by apply Eq.
      - move=>/= n *. apply bi.exist_ne=> ?. apply bi.sep_ne; [done|].
        apply uPred_primitive.later_contractive. destruct n=>/=; [done|by apply Eq]. }
    move=>/= n ty ty' *. apply bi.exist_ne=> ?. apply bi.sep_ne; [done|].
    do 5 apply bi.exist_ne=> ?. f_equiv. f_contractive. (do 2 f_equiv)=> x.
    (do 5 f_equiv)=> wl. rewrite /typed_body. (do 3 f_equiv)=> aπl. do 2 f_equiv.
    have EqBox: ∀𝔄 (T: type ℭ → type 𝔄), TypeNonExpansive T → ∀vπ d tid vl,
      (box (T ty)).(ty_own) vπ d tid vl ≡{n}≡ (box (T ty')).(ty_own) vπ d tid vl.
    { move=> ?? Ne. apply box_type_contractive=> *.
      - by apply Ne.
      - by iApply type_lft_morphism_lft_equiv_proper.
      - apply type_lft_morphism_elctx_interp_proper=>//. apply _.
      - apply dist_dist_later. by apply Ne.
      - apply dist_S. by apply Ne. }
    move: (NeIT x)=> [?[->NeITl]]. do 5 f_equiv; [|do 3 f_equiv; [|f_equiv]].
    - apply equiv_dist. rewrite /fp_E /= !elctx_interp_app.
      do 2 f_equiv; [|f_equiv; [|f_equiv]].
      + elim: NeITl; [done|]=> ????? _ ?. rewrite /tyl_E /= !elctx_interp_app.
        f_equiv; [|done]. apply type_lft_morphism_elctx_interp_proper=>//. apply _.
      + elim: NeITl; [done|]=> ????? _ ?. rewrite /tyl_outlives_E /= !elctx_interp_app.
        f_equiv; [|done]. rewrite !elctx_interp_ty_outlives_E.
        apply lft_incl_equiv_proper_r. by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
      + rewrite !elctx_interp_ty_outlives_E. apply lft_incl_equiv_proper_r.
        by iApply type_lft_morphism_lft_equiv_proper.
    - rewrite !cctx_interp_singleton /cctx_elt_interp. do 3 f_equiv. case=>/= ??.
      do 4 f_equiv. rewrite /tctx_elt_interp. do 6 f_equiv. by apply EqBox.
    - clear -NeITl EqBox. induction NeITl, wl, aπl; [done|]=>/=.
      f_equiv; [|done]. rewrite /tctx_elt_interp. do 6 f_equiv. by apply EqBox.
  Qed.

  Global Instance fn_send {A 𝔄l 𝔅} (fp: A → fn_params 𝔄l 𝔅) : Send (fn fp).
  Proof. done. Qed.

  Lemma fn_resolve {A 𝔄l 𝔅} (fp: A → fn_params 𝔄l 𝔅) E L : resolve E L (fn fp) (const True).
  Proof. apply resolve_just. Qed.

  Local Lemma subtypel_llctx_big_sep_box {𝔄l 𝔅l}
        (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl q E L :
    subtypel E L tyl tyl' fl →
    llctx_interp L q -∗ □ (elctx_interp E -∗
      [∗ hlist] ty; ty';- f ∈ tyl; tyl';- fl, type_incl (box ty) (box ty') f).
  Proof.
    elim=> [|>/box_subtype Sub _ IH]; [by iIntros "_!>_"|]. iIntros "L".
    iDestruct (Sub with "L") as "#Sub". iDestruct (IH with "L") as "#IH".
    iIntros "!> #E /=". iDestruct ("Sub" with "E") as "$".
    iDestruct ("IH" with "E") as "$".
  Qed.

  Lemma fn_subtype {A 𝔄l 𝔄l' 𝔅 𝔅'}
        (fp: A → fn_params 𝔄l 𝔅) (fp': A → fn_params 𝔄l' 𝔅') fl g E L :
    (∀x ϝ, let E' := E ++ fp_E (fp' x) ϝ in elctx_sat E' L (fp_E (fp x) ϝ) ∧
      subtypel E' L (fp' x).(fp_ityl) (fp x).(fp_ityl) fl ∧
      subtype E' L (fp x).(fp_oty) (fp' x).(fp_oty) g) →
    subtype E L (fn fp) (fn fp')
     (λ tr (post: predₛ 𝔅') (al': Π!%ST 𝔄l'), tr (post ∘ g) (plist_map fl al')).
  Proof.
    move=> Big. apply subtype_plain_type=>/= ?. iIntros "L".
    iAssert (∀x ϝ, □ (elctx_interp (E ++ fp_E (fp' x) ϝ) -∗
      elctx_interp (fp_E (fp x) ϝ) ∗
      ([∗ hlist] ty'; ty;- f ∈ (fp' x).(fp_ityl); (fp x).(fp_ityl);- fl,
        type_incl (box ty') (box ty) f) ∗
      type_incl (box (fp x).(fp_oty)) (box (fp' x).(fp_oty)) g))%I as "#Big".
    { iIntros (x ϝ). case (Big x ϝ)=> Efp
        [/subtypel_llctx_big_sep_box Il /box_subtype O].
      iDestruct (Efp with "L") as "#Efp". iDestruct (Il with "L") as "#Il".
      iDestruct (O with "L") as "#O". iIntros "!> E'".
      iSplit; last iSplit; by [iApply "Efp"|iApply "Il"|iApply "O"]. }
    iIntros "!> #E". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iIntros (tr _ vl). iDestruct 1 as (fb kb bl e H ->) "#fn".
    set eq := plist2_eq_nat_len fl. set bl' := plistc_renew (symmetry eq) bl.
    have Eq: (bl: list _) = bl' by rewrite vec_to_list_plistc_renew.
    iExists fb, kb, bl', e, (rew [λ bl₀, _ (_:b:_:b: bl₀ +b+_) _] Eq in H).
    simpl_eq. iSplit; [done|]. iNext. rewrite /typed_body.
    iIntros (x ϝ ? wl' ? aπl' postπ') "!> LFT TIME PROPH UNIQ #Efp' Na L C T Obs".
    rewrite subst_plv_renew. set wl := plistc_renew _ wl'.
    iDestruct ("Big" with "[$E $Efp']") as "(Efp & InIl & InO)".
    iApply ("fn" $! _ _ _ _ _
      (plist_map_with (λ _ _, (∘)) fl aπl') (λ π b, postπ' π (g b))
      with "LFT TIME PROPH UNIQ Efp Na L [C] [T] [Obs]").
    - rewrite !cctx_interp_singleton. iRevert "InO C". iClear "#".
      iIntros "#(_&_& InO &_) C". iIntros (?[??]) "Na L /=[(%&%&%& ⧖ & oty) _] Obs".
      iApply ("C" $! _ -[_] with "Na L [⧖ oty] Obs"). iSplitL; [|done].
      iExists _, _. iSplitR; [done|]. iFrame "⧖". by iApply "InO".
    - iRevert "InIl T". iClear "#". iIntros "?". iStopProof. rewrite /wl.
      move: (fp x).(fp_ityl) (fp' x).(fp_ityl)=> tyl tyl'. clear.
      move: 𝔄l 𝔄l' tyl tyl' fl eq wl' aπl'. fix FIX 1. case=> [|??]; case=> [|??]//=
      tyl tyl'; inv_hlist tyl; inv_hlist tyl'; [by iIntros|].
      iIntros (????[]?[][]) "/= #[(_&_& In &_) ?] [t ?]".
      iSplitL "t"; [|by iApply FIX]. iDestruct "t" as (???) "[⧖ ?]".
      iExists _, _. iSplit; [done|]. iFrame "⧖". by iApply "In".
    - iApply proph_obs_eq; [|done]=>/= ?. f_equal. clear. move: 𝔄l 𝔄l' fl aπl'.
      fix FIX 1. case=> [|??]; case=>//= ??[??][??]. f_equal. apply FIX.
  Qed.

  Lemma fn_subtype_specialize {A B 𝔄l 𝔅} (σ: A → B) (fp: B → fn_params 𝔄l 𝔅) E L :
    subtype E L (fn fp) (fn (fp ∘ σ)) id.
  Proof.
    apply subtype_plain_type. iIntros (?) "_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. iIntros "* ?". iStopProof. do 13 f_equiv.
    iIntros "Big" (?). iApply "Big".
  Qed.

  Local Lemma wp_app_hasty_box {𝔄l} vl r (f: val)
    (pl: plistc _ 𝔄l) tyl vπl tid (Φ: val → iProp Σ) :
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ box ty) tyl pl) vπl -∗
    (∀wl: plistc _ _,
      tctx_interp tid (hzip_with (λ _ ty (w: val), w ◁ box ty) tyl wl) vπl -∗
      WP f (of_val r :: map of_val (vl ++ wl)) {{ Φ }}) -∗
    WP f (of_val r :: map of_val vl ++ pl) {{ Φ }}.
  Proof.
    move: tyl pl vπl vl. elim=> [|???? IH].
    { iIntros "* _ Wp". iSpecialize ("Wp" $! -[] with "[//]"). by rewrite !right_id. }
    iIntros ([p pl'][??]vl) "/= [p pl'] ToWp".
    have ->: App f (of_val r :: map of_val vl ++ p :: pl') =
      fill_item (AppRCtx f (r :: vl) pl') p by done.
    iApply wp_bind. iApply (wp_hasty with "p"). iIntros (w ? _) "⧖ p".
    have ->: fill_item (AppRCtx f (r :: vl) pl') w =
      App f (of_val r :: map of_val (vl ++ [w]) ++ pl') by rewrite map_app -assoc.
    iApply (IH with "pl'"). iIntros (?) "pl'". rewrite -assoc.
    iApply ("ToWp" $! (_-::_)). iFrame "pl'". iExists w, _. iFrame "⧖ p".
    by rewrite eval_path_of_val.
  Qed.

  Lemma type_call_iris' {A 𝔄l 𝔅} qL L κl x (fp: A → fn_params 𝔄l 𝔅)
      p ql ql' (k: expr) E qκl vπl trπ tid postπ :
    AsVal k → IntoPlistc ql ql' →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) L (fp_E (fp x) ϝ)) →
    lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    na_own tid ⊤ -∗ llctx_interp L qL -∗ qκl.[lft_intersect_list κl] -∗
    tctx_elt_interp tid (p ◁ fn fp) trπ -∗
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ box ty) (fp x).(fp_ityl) ql') vπl -∗
    ⟨π, trπ π (postπ π) (vπl -$ π)⟩ -∗
    (∀(ret: val) wπ, na_own tid ⊤ -∗ llctx_interp L qL -∗ qκl.[lft_intersect_list κl] -∗
      tctx_elt_interp tid (ret ◁ box (fp x).(fp_oty)) wπ -∗ ⟨π, postπ π (wπ π)⟩ -∗
      WP k [of_val ret] {{ _, cont_postcondition }}) -∗
    WP (call: p ql → k) {{ _, cont_postcondition }}.
  Proof.
    move=> [k' <-]-> ToEfp. iIntros "#LFT TIME PROPH UNIQ E Na L κl p ql Obs k".
    iMod (lft_create with "LFT") as (ϝ) "[ϝ #To†ϝ]"; [done|].
    iMod (bor_create _ ϝ with "LFT κl") as "[Borκl Toκl]"; [done|].
    iDestruct (frac_bor_lft_incl with "LFT [>Borκl]") as "#?".
    { iApply (bor_fracture with "LFT"); [done|]. by rewrite Qp_mul_1_r. }
    iDestruct (ToEfp ϝ with "L [$E]") as "#Efp".
    { clear ToEfp. iInduction κl as [|κ κl] "IH"; [done|]=>/=.
      iSplit. { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
      iApply "IH". iModIntro. iApply lft_incl_trans; [done|].
      iApply lft_intersect_incl_r. }
    wp_apply (wp_hasty with "p"). iIntros "*% _". iDestruct 1 as (tr ->?????[=->]) "e".
    have ->: (λ: ["_r"], Skip;; k' ["_r"])%E = (λ: ["_r"], Skip;; k' ["_r"])%V by unlock.
    iApply (wp_app_hasty_box [] with "ql")=>/=. iIntros (?) "ityl". wp_rec.
    iApply ("e" with "LFT TIME PROPH UNIQ Efp Na [ϝ] [Toκl L k] ityl Obs"); first 2 last.
    { iSplitL; [|done]. iExists _. iSplit; [by rewrite/= left_id|]. by iFrame "ϝ". }
    rewrite cctx_interp_singleton. iIntros (v[??]). inv_vec v=> v.
    iIntros "Na [(%& %Eq & ϝ &_) _] [oty ?] Obs". rewrite/= left_id in Eq.
    rewrite -Eq. wp_rec. wp_bind Skip. iSpecialize ("To†ϝ" with "ϝ").
    iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); [done|].
    iApply (wp_step_fupd with "To†ϝ"); [set_solver|]. wp_seq. iIntros "†ϝ !>".
    wp_seq. iMod ("Toκl" with "†ϝ") as "> κl". iApply ("k" with "Na L κl oty Obs").
  Qed.

  Lemma type_call_iris {A 𝔄l 𝔅} x vπl κl qκl postπ (fp: A → fn_params 𝔄l 𝔅)
      p ql ql' (k: expr) E trπ tid :
    AsVal k → IntoPlistc ql ql' →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) κl ++ E) [] (fp_E (fp x) ϝ)) →
    lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
    qκl.[lft_intersect_list κl] -∗ tctx_elt_interp tid (p ◁ fn fp) trπ -∗
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ box ty) (fp x).(fp_ityl) ql') vπl -∗
    ⟨π, trπ π (postπ π) (vπl -$ π)⟩ -∗
    (∀(ret: val) wπ, na_own tid ⊤ -∗ qκl.[lft_intersect_list κl] -∗
      tctx_elt_interp tid (ret ◁ box (fp x).(fp_oty)) wπ -∗ ⟨π, postπ π (wπ π)⟩ -∗
      WP k [of_val ret] {{ _, cont_postcondition }}) -∗
    WP (call: p ql → k) {{ _, cont_postcondition }}.
  Proof.
    iIntros (???) "LFT TIME PROPH UNIQ E Na κl p ql Obs k".
    iApply (type_call_iris' 1%Qp with "LFT TIME PROPH UNIQ E Na [] κl p ql Obs");
      [done|by rewrite /llctx_interp|].
    iIntros (??) "Na _ κl ret Obs". iApply ("k" with "Na κl ret Obs").
  Qed.

  Lemma type_call {A 𝔄l 𝔅 ℭl 𝔇l 𝔈l 𝔉} x (fp: A → fn_params 𝔄l 𝔅) p ql ql' k trx
      trk tri E L (C: cctx 𝔉) (T: tctx ℭl) (T': tctx 𝔇l) (Tk: vec val 1 → tctx 𝔈l) :
    IntoPlistc ql ql' → Forall (lctx_lft_alive E L) L.*1 →
    tctx_extract_ctx E L (p ◁ fn fp +::
      hzip_with (λ _ ty q, q ◁ box ty) (fp x).(fp_ityl) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    k ◁cont{L, Tk} trk ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ box (fp x).(fp_oty) +:: T') (Tk [#ret]) tri) →
    ⊢ typed_body E L C T (call: p ql → k) (trx ∘ (λ post '(trp -:: adl),
      let '(al, dl) := psep adl in trp (λ b: 𝔅, tri (trk post) (b -:: dl)) al)).
  Proof.
    move=> ? Alv ??? InTk. iApply typed_body_tctx_incl; [done|].
    iIntros (?[? adπl]postπ). move: (papp_ex adπl)=> [aπl[dπl->]].
    iIntros "#LFT TIME #PROPH #UNIQ #E Na L C /=(p & ql & T') Obs".
    iMod (lctx_lft_alive_tok_list with "E L") as (?) "(κL & L & ToL)"; [done|done|].
    iApply (type_call_iris' with "LFT TIME PROPH UNIQ E Na L κL p ql [Obs]"); [done|..].
    { iApply proph_obs_eq; [|done]=>/= ?. by rewrite papply_app papp_sepl papp_sepr. }
    iIntros (ret ?) "Na L κL ret Obs". iMod ("ToL" with "κL L") as "L".
    iMod (proj2 (InTk _) _ _ (_-::_) with "LFT PROPH UNIQ E L [$ret $T'] Obs")
      as (?) "(L & Tk & Obs)".
    have ->: [ret: expr] = map of_val ([#ret]) by done.
    iApply ("C" with "[%//] Na L Tk Obs").
  Qed.

  Lemma type_letcall {A 𝔄l 𝔅 ℭl 𝔇l 𝔈} x (fp: A → fn_params 𝔄l 𝔅) p ql ql'
                     (T: tctx ℭl) (T': tctx 𝔇l) b e trx tr E L (C: cctx 𝔈)
                     `{!IntoPlistc ql ql', !Closed (b :b: []) e, !Closed [] p} :
    TCForall (Closed []) ql → Forall (lctx_lft_alive E L) L.*1 →
    tctx_extract_ctx E L (p ◁ fn fp +::
      hzip_with (λ _ ty q, q ◁ box ty) (fp x).(fp_ityl) ql') T T' trx →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    (∀ret: val, typed_body E L C
      (ret ◁ box (fp x).(fp_oty) +:: T') (subst' b ret e) tr) -∗
    typed_body E L C T (letcall: b := p ql in e) (trx ∘ (λ post '(trp -:: adl),
      let '(al, dl) := psep adl in trp (λ b, tr post (b -:: dl)) al)).
  Proof.
    move=> Clql ???. iIntros "e". iApply type_cont_norec.
    - (* TODO : make [solve_closed] work here. *)
      eapply is_closed_weaken; [done|]. set_solver+.
    - (* TODO : make [solve_closed] work here. *)
      rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl;
        [by apply TCForall_Forall|]=> ??.
        eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - iIntros (k).
      (* TODO : make [simpl_subst] work here. *)
      have ->: subst' "_k" k (call: p ql → "_k")%E = subst "_k" k p $
        (λ: ["_r"], Skip;; k ["_r"])%E :: map (subst "_k" k) ql by done.
      rewrite is_closed_nil_subst; [|done].
      have ->: map (subst "_k" k) ql = ql.
      { clear -Clql. elim Clql; [done|]=>/= ????->. by rewrite is_closed_nil_subst. }
      iApply typed_body_proper; last first.
      { iApply type_call=>//; [constructor|]=> v.
        have {1}->: v = vhd [#v] by done. move: [#v]=> ?. apply tctx_incl_refl. }
      done.
    - iIntros (? ret). inv_vec ret=> ret. rewrite /subst_v /=.
      rewrite (is_closed_subst []); [| |set_solver+]; last first.
      { apply subst'_is_closed; [|done]. apply is_closed_of_val. }
      iApply "e".
  Qed.

  Lemma type_fnrec {A 𝔄l 𝔅} tr (fp: A → fn_params 𝔄l 𝔅) fb e bl bl'
      `{Into: !IntoPlistc bl bl', Cl: !Closed (fb :b: ("return" :: bl)%binder +b+ []) e} :
    (∀x ϝ (f: val) k (wl: plistc _ 𝔄l),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
            [k ◁cont{[ϝ ⊑ₗ []], λ v: vec _ 1, +[vhd v ◁ box (fp x).(fp_oty)] } tr_ret]
            (f ◁ fn fp +:: hzip_with (λ _ ty (v: val), v ◁ box ty) (fp x).(fp_ityl) wl)
            (subst' fb f $ subst "return" k $ subst_plv bl' wl e)
            (λ post '(tr' -:: al), tr' = tr ∧ tr post al)%type) →
    typed_val (fnrec: fb bl := e)%V (fn fp) tr.
  Proof.
    move: Cl. rewrite Into. iIntros (? Body ?????) "_ _ _ _ _ $$ _ Obs".
    iMod persistent_time_receipt_0 as "#⧖". iApply wp_value. iExists -[const tr].
    iFrame "Obs". iSplit; [|done]. iLöb as "IH". iExists _, 0%nat.
    iSplit; [by rewrite/= decide_True_pi|]. iFrame "⧖". iExists tr.
    iSplit; [done|]. iExists fb, "return", bl', e, _. iSplit; [done|].
    iIntros "!>!> *%%% LFT TIME PROPH UNIQ Efp Na L C T ?".
    iApply (Body _ _ (RecV _ _ _) $! _ (_-::_) with
      "LFT TIME PROPH UNIQ Efp Na L C [$T $IH]").
    by iApply proph_obs_impl; [|done]=>/= ??.
  Qed.

  Lemma type_fn {A 𝔄l 𝔅} tr (fp: A → fn_params 𝔄l 𝔅) e bl bl'
      `{!IntoPlistc bl bl', !Closed ("return" :: bl +b+ []) e} :
    (∀x ϝ k (wl: plistc _ 𝔄l),
        ⊢ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
            [k ◁cont{[ϝ ⊑ₗ []], λ v: vec _ 1, +[vhd v ◁ box (fp x).(fp_oty)] } tr_ret]
            (hzip_with (λ _ ty (v: val), v ◁ box ty) (fp x).(fp_ityl) wl)
            (subst "return" k $ subst_plv bl' wl e) tr) →
    typed_val (fn: bl := e)%V (fn fp) tr.
  Proof.
    move=> Body. eapply type_fnrec; [apply _|]=> *.
    iApply typed_body_impl; last first.
    { iApply typed_body_tctx_incl; [|iApply Body]. apply tctx_incl_resolve_head. }
    by move=>/= ?[??][_ ?].
  Qed.
End typing.

Ltac simpl_fp_E := rewrite /fp_E /ty_outlives_E /=.

Global Hint Resolve elctx_sat_fp_E : lrust_typing.
Global Hint Resolve fn_resolve fn_subtype : lrust_typing.
