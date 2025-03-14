From iris.proofmode Require Import environments.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Section typing.
  Context `{!typeG Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body {𝔄l 𝔅} (E: elctx) (L: llctx) (C: cctx 𝔅) (T: tctx 𝔄l)
    (e: expr) (tr: predl_trans' 𝔄l 𝔅) : iProp Σ := ∀tid vπl postπ,
    lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
    llctx_interp L 1 -∗ cctx_interp tid postπ C -∗ tctx_interp tid T vπl -∗
      ⟨π, tr (postπ π) (vπl -$ π)⟩ -∗ WP e {{ _, cont_postcondition }}.
  Global Arguments typed_body {_ _} _ _ _ _ _%E _%type.

  Global Instance typed_body_proper 𝔄l 𝔅 E L C T e :
    Proper ((≡) ==> (≡)) (@typed_body 𝔄l 𝔅 E L C T e).
  Proof. intros ?? EQ. unfold typed_body. do 18 f_equiv. apply EQ. Qed.

  Lemma typed_body_impl {𝔄l 𝔅} (tr tr': predl_trans' 𝔄l 𝔅) E L
      (C: cctx 𝔅) (T: tctx 𝔄l) e :
    (∀post vl, tr post vl → tr' post vl) →
    typed_body E L C T e tr' -∗ typed_body E L C T e tr.
  Proof.
    move=> Imp. rewrite /typed_body. do 16 f_equiv=>/=. do 2 f_equiv. move=> ?.
    by apply Imp.
  Qed.

  Lemma typed_body_tctx_incl {𝔄l 𝔅l ℭ} tr' tr (T: tctx 𝔄l) (T': tctx 𝔅l) E L
      (C: cctx ℭ) e :
    tctx_incl E L T T' tr' →
    typed_body E L C T' e tr -∗ typed_body E L C T e (tr' ∘ tr).
  Proof.
    iIntros ([? In]) "e". iIntros (???) "#LFT TIME #PROPH #UNIQ #E Na L C T Obs".
    iMod (In with "LFT PROPH UNIQ E L T Obs") as (?) "(L & T' & Obs)".
    iApply ("e" with "LFT TIME PROPH UNIQ E Na L C T' Obs").
  Qed.

  (** Instruction *)
  Definition typed_instr {𝔄l 𝔅l} (E: elctx) (L: llctx)
    (T: tctx 𝔄l) (e: expr) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀tid postπ vπl, lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ tctx_interp tid T vπl -∗
      ⟨π, tr (postπ π) (vπl -$ π)⟩ -∗ WP e {{ v, ∃vπl', na_own tid ⊤ ∗
        llctx_interp L 1 ∗ tctx_interp tid (T' v) vπl' ∗ ⟨π, postπ π (vπl' -$ π)⟩ }}.
  Global Arguments typed_instr {_ _} _ _ _ _%E _ _%type.

  (** Writing and Reading *)

  Definition typed_write {𝔄 𝔅 𝔄' 𝔅'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (tyb': type 𝔅') (gt: 𝔄 → 𝔅) (st: 𝔄 → 𝔅' → 𝔄') : Prop :=
    tyb.(ty_size) = tyb'.(ty_size) ∧ ∀vπ d v tid qL,
    lft_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    llctx_interp L qL -∗ ty.(ty_own) vπ d tid [v] ={⊤}=∗ ∃l: loc,
      ⌜v = #l⌝ ∗ ▷ l ↦∗: tyb.(ty_own) (gt ∘ vπ) d tid ∗
      ∀wπ db', ▷ l ↦∗: tyb'.(ty_own) wπ db' tid -∗ ⧖(S db') ={⊤}=∗
        llctx_interp L qL ∗ ty'.(ty_own) (st ∘ vπ ⊛ wπ) (S db') tid [v].
  Global Arguments typed_write {_ _ _ _} _ _ _%T _%T _%T _%T _%type _%type.

  (* Technically speaking, we could remvoe the vl quantifiaction here and use
     mapsto_pred instead (i.e., l ↦∗: ty.(ty_own) tid). However, that would
     make work for some of the provers way harder, since they'd have to show
     that nobody could possibly have changed the vl (because only half the
     fraction was given). So we go with the definition that is easier to prove. *)
  Definition typed_read {𝔄 𝔅 𝔄'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (gt: 𝔄 → 𝔅) (st: 𝔄 → 𝔄') : Prop := ∀vπ d v tid qL,
    lft_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗ llctx_interp L qL -∗
    ty.(ty_own) vπ d tid [v] ={⊤}=∗ ∃(l: loc) vl q, ⌜v = #l⌝ ∗
      l ↦∗{q} vl ∗ ▷ tyb.(ty_own) (gt ∘ vπ) d tid vl ∗ (l ↦∗{q} vl ={⊤}=∗
        na_own tid ⊤ ∗ llctx_interp L qL ∗ ty'.(ty_own) (st ∘ vπ) d tid [v]).
  Global Arguments typed_read {_ _ _} _ _ _%T _%T _%T _ _%type.

  Definition typed_instr_ty {𝔄l 𝔅} (E: elctx) (L: llctx)
    (T: tctx 𝔄l) (e: expr) (ty: type 𝔅) (tr: pred' 𝔅 → predl 𝔄l) : Prop :=
    typed_instr E L T e (λ v, +[v ◁ ty]) (λ post al, tr (λ b, post -[b]) al).
  Global Arguments typed_instr_ty {_ _} _ _ _ _%E _%T _%type.

  Definition typed_val {𝔄} (v: val) (ty: type 𝔄) (a: 𝔄) : Prop :=
    ∀E L, typed_instr_ty E L +[] (of_val v) ty (λ post _, post a).
  Global Arguments typed_val {_} _%V _%T _%type.

  (* This lemma is helpful for specifying the predicate transformer. *)
  Lemma type_with_tr 𝔄l 𝔅 tr E L (C: cctx 𝔅) (T: tctx 𝔄l) e :
    typed_body E L C T e tr -∗ typed_body E L C T e tr.
  Proof. done. Qed.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type {𝔄l 𝔅} (T: tctx 𝔄l) vπl tr E L (C: cctx 𝔅) e tid postπ :
    typed_body E L C T e tr -∗
    lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
    llctx_interp L 1 -∗ cctx_interp tid postπ C -∗ tctx_interp tid T vπl -∗
    ⟨π, tr (postπ π) (vπl -$ π)⟩ -∗ WP e {{ _, cont_postcondition }}.
  Proof.
    iIntros "Bd LFT TIME PROPH UNIQ E Na L C T Obs".
    iApply ("Bd" with "LFT TIME PROPH UNIQ E Na L C T Obs").
  Qed.

  (* TODO: Proof a version of this that substitutes into a compatible context...
     if we really want to do that. *)
  Lemma type_equivalize_lft {𝔄l 𝔅} E L (C: cctx 𝔅) (T: tctx 𝔄l) κ κ' e tr :
    typed_body (κ ⊑ₑ κ' :: κ' ⊑ₑ κ :: E) L C T e tr -∗
    typed_body E (κ ⊑ₗ [κ'] :: L) C T e tr.
  Proof.
    iIntros "e" (???) "#LFT TIME PROPH UNIQ E Na [Eq L] C T".
    iMod (lctx_equalize_lft with "LFT Eq") as "[In In']".
    iApply ("e" with "LFT TIME PROPH UNIQ [$E $In $In'] Na L C T").
  Qed.

  (* [type_dep_cond] lets typing deduction depend on dynamic values,
    requiring some precondition on them *)
  Lemma type_dep_cond {𝔄l A 𝔅l ℭl 𝔇} (Φ: pred' A) (Tx: tctx 𝔄l) (f: _ → A)
      E L (T: tctx 𝔅l) (T': tctx ℭl) (C: cctx 𝔇) e trx tr :
    Closed [] e → tctx_extract_ctx E L Tx T T' trx → real_tctx E L Tx f →
    (∀a: A, ⌜Φ a⌝ -∗ typed_body E L C (Tx h++ T') e (tr a)) -∗
    typed_body E L C T (Skip;; e) (trx ∘ (λ post acl,
      let a := f (psepl acl) in Φ a ∧ tr a post acl))%type.
  Proof.
    iIntros (?? Rl) "e". iApply (typed_body_tctx_incl trx); [done|].
    iIntros (? acπl ?) "#LFT #TIME #PROPH UNIQ #E Na L C".
    move: (papp_ex acπl)=> [aπl[cπl->]]. iIntros "[Tx T'] #Obs".
    iMod (Rl with "LFT E L Tx") as (?) "[⧖ Upd]". wp_bind Skip.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L /=. }
    wp_seq. iIntros "(%Eq & L & Tx) !>". move: Eq=> [a Eq]. wp_seq.
    iMod (proph_obs_sat with "PROPH Obs") as %[π₀ Obs]; [done|].
    move: (equal_f Eq π₀) Obs=>/= + [+_]. rewrite papply_app papp_sepl=>/= -> Φa.
    iApply ("e" $! a Φa _ (_-++_)  with "LFT TIME PROPH UNIQ E Na L C [$Tx $T'] []").
    iApply proph_obs_impl; [|done]=>/= π[_ +]. move: (equal_f Eq π)=>/= <-.
    by rewrite papply_app papp_sepl.
  Qed.

  (* [type_dep] lets typing deduction depend on dynamic values;
    it is derived from [type_dep_cond] *)
  Lemma type_dep {𝔄l A 𝔅l ℭl 𝔇} (Tx: tctx 𝔄l) (f: _ → A)
      E L (T: tctx 𝔅l) (T': tctx ℭl) (C: cctx 𝔇) e trx tr :
    Closed [] e → tctx_extract_ctx E L Tx T T' trx → real_tctx E L Tx f →
    (∀a: A, typed_body E L C (Tx h++ T') e (tr a)) -∗
    typed_body E L C T (Skip;; e) (trx ∘ (λ post acl,
      let a := f (psepl acl) in tr a post acl))%type.
  Proof.
    iIntros (???) "e". iApply (typed_body_tctx_incl trx); [done|].
    iApply typed_body_impl; last first.
    { iApply (type_dep_cond (const True)); [apply tctx_incl_refl|done|].
      iIntros (a ?). iApply ("e" $! a). }
    move=>/= ???. by split.
  Qed.

  Lemma type_let' {𝔄l 𝔅l ℭl 𝔇} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr'
      (T: tctx ℭl) (C: cctx 𝔇) xb e e' E L :
    Closed (xb :b: []) e' → typed_instr E L T1 e T2 tr →
    (∀v: val, typed_body E L C (T2 v h++ T) (subst' xb v e') tr') -∗
    typed_body E L C (T1 h++ T) (let: xb := e in e') (λ post acl,
      let '(al, cl) := psep acl in tr (λ bl, tr' post (bl -++ cl)) al).
  Proof.
    iIntros "% %Inst e'" (? vπl2 ?). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #PROPH #UNIQ #E Na L C [T1 T] Obs". wp_bind e.
    iApply (wp_wand with "[Na L T1 Obs]").
    { iApply (Inst with "LFT TIME PROPH UNIQ E Na L T1").
      iApply proph_obs_eq; [|done]=> ?. by rewrite /trans_upper papply_app papp_sepl. }
    iIntros "% (%& Na & L & T2 &?)". wp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" with "LFT TIME PROPH UNIQ E Na L C T2T").
    iApply proph_obs_eq; [|done]=>/= ?. by rewrite papply_app papp_sepr.
  Qed.

  Lemma type_let {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr' trx
    (T: tctx ℭl) (T': tctx 𝔇l) E L (C: cctx 𝔈) xb e e' tr_res :
    Closed (xb :b: []) e' → typed_instr E L T1 e T2 tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    (∀v: val, typed_body E L C (T2 v h++ T') (subst' xb v e') tr') -∗
    typed_body E L C T (let: xb := e in e') tr_res.
  Proof.
    iIntros (???->) "?". iApply (typed_body_tctx_incl trx); [done|].
    by iApply type_let'.
  Qed.

  Lemma type_val {𝔄 𝔅l ℭ} v (a: 𝔄) ty (T: tctx 𝔅l) E L (C: cctx ℭ) xb e tr :
    Closed (xb :b: []) e → typed_val v ty a →
    (∀v': val, typed_body E L C (v' ◁ ty +:: T) (subst' xb v' e) tr) -∗
    typed_body E L C T (let: xb := v in e) (λ post bl, tr post (a -:: bl)).
  Proof.
    iIntros (? Val) "?". iApply type_let; [apply Val|solve_typing|done..].
  Qed.

  (* [type_val_dep] lets the obtained value depend on dynamic values;
    it is derived from [type_dep] and [type_val] *)
  Lemma type_val_dep {𝔄 𝔅l B ℭl 𝔇l 𝔈} (a: B → 𝔄) ty (Tx: tctx 𝔅l)
      E L (C: cctx 𝔈) (T: tctx ℭl) (T': tctx 𝔇l) v xb e trx tr f :
    Closed (xb :b: []) e → (∀b, typed_val v ty (a b)) →
    tctx_extract_ctx E L Tx T T' trx → real_tctx E L Tx f →
    (∀v': val, typed_body E L C (v' ◁ ty +:: Tx h++ T') (subst' xb v' e) tr) -∗
    typed_body E L C T (Skip;; let: xb := v in e) (trx ∘
      (λ post bdl, let '(bl, dl) := psep bdl in tr post (a (f bl) -:: bdl))).
  Proof.
    iIntros (? Val ??) "e". iApply typed_body_impl; last first.
    { iApply type_dep; [ |done|done|].
      (* TODO: make [solve_closed] work here *)
      { rewrite /Closed /= !andb_True. split; [done|]. split; [|done].
        apply is_closed_of_val. }
      iIntros (b). iApply type_val; by [exact (Val b)|]. }
    by move=>/= ??.
  Qed.

  Lemma type_seq {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: tctx 𝔅l)
    (T: tctx ℭl) (T': tctx 𝔇l) E L (C: cctx 𝔈) e e' tr tr' trx tr_res :
    Closed [] e' → typed_instr E L T1 e (const T2) tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    typed_body E L C (T2 h++ T') e' tr' -∗ typed_body E L C T (e;; e') tr_res.
  Proof. iIntros. iApply (type_let _ (const T2))=>//. by iIntros. Qed.

  Lemma type_newlft {𝔄l 𝔅} κl E L (C: cctx 𝔅) (T: tctx 𝔄l) e tr :
    Closed [] e → (∀κ, typed_body E (κ ⊑ₗ κl :: L) C T e tr) -∗
    typed_body E L C T (Newlft;; e) tr.
  Proof.
    iIntros (?) "e %%% #LFT TIME PROPH UNIQ E Na L C T Obs".
    iMod (lft_create with "LFT") as (Λ) "[Λ #Hinh]"; [done|].
    set κ' := lft_intersect_list κl. wp_seq.
    iApply ("e" $! κ' ⊓ Λ with "LFT TIME PROPH UNIQ E Na [Λ $L] C T Obs").
    rewrite /llctx_interp. iExists Λ. iFrame "Λ". by iSplit.
  Qed.

  Lemma type_endlft {𝔄l 𝔅l ℭ} (T: tctx 𝔄l) (T' T'': tctx 𝔅l)
      κ κl tru tr e E L (C: cctx ℭ) :
    Closed [] e →
    resolve_unblock_tctx E (κ ⊑ₗ κl :: L) κ T T' tru → unblock_tctx E L κ T' T'' →
    typed_body E L C T'' e tr -∗
    typed_body E (κ ⊑ₗ κl :: L) C T (Endlft;; e) (tru ∘ tr).
  Proof.
    iIntros (? RslvU Un) "e %%% #LFT #TIME #PROPH UNIQ #E Na L' C T Obs".
    wp_bind Skip. iMod (RslvU with "LFT PROPH E L' T Obs") as (??) "[⧖ ToT']".
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [ToT']")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L. }
    wp_seq. iIntros "([(%&%& κ' & To†) L] & T' & Obs) !>".
    iSpecialize ("To†" with "κ'"). wp_seq. wp_bind Skip.
    iApply wp_mask_mono; [|iApply (wp_step_fupd with "To†")]; [set_solver..|].
    wp_seq. iIntros "† !>". wp_seq. wp_bind Skip.
    iMod (Un with "LFT E L [†] T'") as (??) "[⧖ ToT']".
    { simpl in *. subst. rewrite -lft_dead_or. by iRight. }
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [ToT']")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L. }
    wp_seq. iIntros "(L & T'' & Obs') !>". wp_seq. iCombine "Obs Obs'" as "Obs".
    iApply ("e" with "LFT TIME PROPH UNIQ E Na L C T'' [Obs]").
    by iApply proph_obs_impl; [|done]=>/= ?[?<-].
  Qed.

  (** Explicit resolution of a path *)
  Lemma type_resolve_instr {𝔄} p (ty: type 𝔄) Φ E L :
    resolve E L ty Φ →
    typed_instr E L +[p ◁ ty] Skip (λ _, +[]) (λ post '-[a], Φ a → post -[]).
  Proof.
    iIntros (Rslv ??[?[]]) "LFT TIME PROPH _ E $ L /=[(%&%&%& ⧖ & ty) _] Obs".
    iDestruct (Rslv ⊤ with "LFT PROPH E L ty") as "Upd"; [done|].
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L. }
    wp_seq. iIntros "[Obs' $] !>". iExists -[]. iCombine "Obs Obs'" as "?".
    rewrite left_id. iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp.
  Qed.

  Lemma type_resolve {𝔄 𝔅l ℭl 𝔇} p (ty: type 𝔄) Φ E L trx e tr
      (T: tctx 𝔅l) (T': tctx ℭl) (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ ty] T T' trx → resolve E L ty Φ →
    typed_body E L C T' e tr -∗
    typed_body E L C T (Skip;; e)
      (trx ∘ (λ post '(a -:: cl), Φ a → tr post cl))%type.
  Proof.
    iIntros (? Extr ?) "?". iApply type_seq; [by eapply type_resolve_instr|done| |done].
    move: Extr=> [Htrx _]??/=. apply Htrx. by case.
  Qed.

  Lemma type_path_instr {𝔄} p (ty: type 𝔄) E L :
    typed_instr_ty E L +[p ◁ ty] p ty (λ post '-[v], post v).
  Proof.
    iIntros (??[vπ[]]) "_ _ _ _ _ $$ [T _] Obs". iApply (wp_hasty with "T").
    iIntros (v d _) "??". iExists -[vπ]. do 2 (iSplit; [|done]). iExists v, d.
    rewrite eval_path_of_val. by iFrame.
  Qed.

  Lemma type_letpath {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) (T: tctx 𝔅l) (T': tctx ℭl)
    (C: cctx 𝔇) x p e trx tr E L :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    (∀v: val, typed_body E L C (v ◁ ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by eapply type_path_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.

  Lemma type_assign_instr {𝔄 𝔅 𝔄' 𝔅'} (ty: type 𝔄) (tyb: type 𝔅)
                          (ty': type 𝔄') (tyb': type 𝔅') gt st Φ p pb E L :
    typed_write E L ty tyb ty' tyb' gt st → resolve' E L tyb Φ →
    typed_instr E L +[p ◁ ty; pb ◁ tyb'] (p <- pb) (λ _, +[p ◁ ty'])
      (λ post '-[a; b], Φ (gt a) (post -[st a b])).
  Proof.
    iIntros ([Eq Wrt] Rslv ?? (vπ & wπ &[]))
      "#LFT #TIME PROPH UNIQ #E $ [L L'] (p & pb & _) Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (???) "⧖ ty".
    iMod (Wrt with "LFT UNIQ E L ty") as (? ->) "[(%vl & ↦ & tyb) Toty']".
    iDestruct (ty_size_eq with "tyb") as "#>%Sz".
    iDestruct (Rslv (⊤ ∖ (⊤ ∖ ↑lftN ∖ ↑prophN)) with "LFT PROPH E L' tyb") as "ToObs";
    [set_solver|]. iApply (wp_step_fupdN_persistent_time_receipt _ _ (⊤ ∖ ↑lftN ∖ ↑prophN)
    with "TIME ⧖ [ToObs]")=>//. { by iApply step_fupdN_with_emp. }
    wp_bind pb. iApply (wp_hasty with "pb"). iIntros (vb db ?) "#⧖' tyb'".
    iDestruct (ty_size_eq with "tyb'") as %Sz'. move: Sz. rewrite Eq -Sz' /=.
    case vl=> [|?[|]]=>// ?.
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [solve_ndisj|].
    rewrite heap_mapsto_vec_singleton.
    wp_write. iIntros "#⧖S [Obs' $]". iCombine "Obs Obs'" as "Obs".
    iMod ("Toty'" with "[↦ tyb'] ⧖S") as "[$ ty']".
    { iExists [vb]. rewrite -heap_mapsto_vec_singleton. iFrame. }
    iExists -[st ∘ vπ ⊛ wπ]. iSplitR "Obs".
    - rewrite right_id tctx_hasty_val'; [|done]. iExists (S db). by iFrame.
    - iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp.
  Qed.

  Lemma type_assign {𝔄 𝔅 𝔄' 𝔅' 𝔄l 𝔅l ℭ} (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
                    (tyb': type 𝔅') gt st Φ p pb E L
                    (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) trx tr e :
    Closed [] e → tctx_extract_ctx E L +[p ◁ ty; pb ◁ tyb'] T T' trx →
    typed_write E L ty tyb ty' tyb' gt st → resolve' E L tyb Φ →
    typed_body E L C (p ◁ ty' +:: T') e tr -∗
    typed_body E L C T (p <- pb;; e)
      (trx ∘ (λ post '(a -:: b -:: bl), Φ (gt a) (tr post (st a b -:: bl)))).
  Proof.
    iIntros (? Extr ??) "?". iApply type_seq; [by eapply type_assign_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_deref_instr {𝔄 𝔅 𝔄'} (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
                                    gt st p E L :
    tyb.(ty_size) = 1%nat → typed_read E L ty tyb ty' gt st →
    typed_instr E L +[p ◁ ty] (!p) (λ v, +[v ◁ tyb; p ◁ ty'])
      (λ post '-[a], post -[gt a; st a]).
  Proof.
    move=> Sz Rd. iIntros (??[vπ[]]) "LFT _ _ _ E Na L [p _] ?".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (???) "#? ty".
    iMod (Rd with "LFT E Na L ty") as (l vl q ->) "(↦ & tyb & Toty')".
    iDestruct (ty_size_eq with "tyb") as "#>%Len". rewrite Sz in Len.
    case vl as [|v[|]]=>//. rewrite heap_mapsto_vec_singleton. iApply wp_fupd.
    wp_read. iMod ("Toty'" with "↦") as "($&$& ty')". iModIntro.
    iExists -[gt ∘ vπ; st ∘ vπ]. iSplit; [|done]. rewrite right_id
    tctx_hasty_val tctx_hasty_val'; [|done]. iSplitL "tyb"; iExists d; by iSplit.
  Qed.

  Lemma type_deref {𝔄 𝔅 𝔄' 𝔄l 𝔅l ℭ} (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') gt st
                   (T: tctx 𝔄l) (T': tctx 𝔅l) p x e trx tr E L (C: cctx ℭ) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    typed_read E L ty tyb ty' gt st → tyb.(ty_size) = 1%nat →
    (∀v: val, typed_body E L C (v ◁ tyb +:: p ◁ ty' +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e)
      (trx ∘ (λ post '(a -:: al), tr post (gt a -:: st a -:: al))).
  Proof.
    iIntros (? Extr ??) "?". iApply type_let; [by eapply type_deref_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.

  Lemma type_memcpy_instr {𝔄 𝔄' 𝔅 𝔅' ℭ ℭ'} (tyw: type 𝔄) (tyw': type 𝔄')
        (tyr: type 𝔅) (tyr': type 𝔅') (tyb: type ℭ) (tyb': type ℭ')
        gtw stw gtr str Φ (n: Z) pw pr E L :
    typed_write E L tyw tyb tyw' tyb' gtw stw → resolve' E L tyb Φ →
    typed_read E L tyr tyb' tyr' gtr str → n = tyb'.(ty_size) →
    typed_instr E L +[pw ◁ tyw; pr ◁ tyr] (pw <-{n} !pr)
      (λ _, +[pw ◁ tyw'; pr ◁ tyr'])
      (λ post '-[a; b], Φ (gtw a) (post -[stw a (gtr b); str b])).
  Proof.
    iIntros ([Eq Wrt] Rslv Rd ->??(?&?&[]))
      "/= #LFT #TIME PROPH UNIQ #E Na [[L L'] L''] (pw & pr &_) Obs".
    wp_bind pw. iApply (wp_hasty with "pw"). iIntros (???) "⧖ tyw".
    iMod (Wrt with "LFT UNIQ E L tyw") as (?->) "[(% & >↦ & tyb) Totyw]".
    wp_bind pr. iApply (wp_hasty with "pr"). iIntros (???) "#⧖' tyr".
    iMod (Rd with "LFT E Na L' tyr") as (? vlb ?->) "(↦' & tyb' & Totyr')".
    iDestruct (ty_size_eq with "tyb") as "#>%".
    iDestruct (ty_size_eq with "tyb'") as "#>%".
    iDestruct (Rslv (⊤ ∖ (⊤ ∖ ↑lftN ∖ ↑prophN)) with "LFT PROPH E L'' tyb") as "ToObs";
      [set_solver|].
    iApply (wp_step_fupdN_persistent_time_receipt _ _ (⊤ ∖ ↑lftN ∖ ↑prophN)
      with "TIME ⧖ [ToObs]")=>//; [by iApply step_fupdN_with_emp|].
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [solve_ndisj|].
    iApply (wp_memcpy with "[$↦ $↦']"); [congruence|congruence|].
    iIntros "!> [↦ ↦'] #⧖'S [Obs' $]". iCombine "Obs Obs'" as "Obs".
    iMod ("Totyw" with "[↦ tyb'] ⧖'S") as "[$ tyw']". { iExists vlb. iFrame. }
    iMod ("Totyr'" with "↦'") as "($&$& tyr')". iModIntro. iExists -[_; _].
    iSplit; [rewrite right_id|].
    - iSplitL "tyw'"; (rewrite tctx_hasty_val'; [|done]); iExists _; by iFrame.
    - iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp.
  Qed.

  Lemma type_memcpy {𝔄 𝔄' 𝔅 𝔅' ℭ ℭ' 𝔄l 𝔅l 𝔇} (tyw: type 𝔄) (tyw': type 𝔄')
      (tyr: type 𝔅) (tyr': type 𝔅') (tyb: type ℭ) (tyb': type ℭ') gtw stw gtr
      str Φ (n: Z) pw pr E L (C: cctx 𝔇) (T: tctx 𝔄l) (T': tctx 𝔅l) e trx tr :
    Closed [] e → tctx_extract_ctx E L +[pw ◁ tyw; pr ◁ tyr] T T' trx →
    typed_write E L tyw tyb tyw' tyb' gtw stw → resolve' E L tyb Φ →
    typed_read E L tyr tyb' tyr' gtr str → n = tyb'.(ty_size) →
    typed_body E L C (pw ◁ tyw' +:: pr ◁ tyr' +:: T') e tr -∗
    typed_body E L C T (pw <-{n} !pr;; e)
      (trx ∘ (λ post '(a -:: b -:: bl),
                Φ (gtw a) (tr post (stw a (gtr b) -:: str b -:: bl)))).
  Proof.
    iIntros (? Extr ????) "?". iApply type_seq; [by eapply type_memcpy_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.
End typing.

Ltac via_tr_impl :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅)); last first
    end
  end.

Ltac via_tr_impl_with tr :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      evar (tr: predl_trans' 𝔄l 𝔅);
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅) tr); last first
    end
  end.

Ltac intro_subst := iIntros (?); simpl_subst.
Ltac intro_subst_as x := iIntros (x); simpl_subst.

Global Hint Opaque typed_instr typed_write typed_read : lrust_typing.
