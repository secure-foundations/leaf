From lrust.lang.lib Require Import memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import uninit type_context programs.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section own.
  Context `{!typeG Σ}.

  Definition freeable_sz (n sz: nat) (l: loc) : iProp Σ :=
    match sz, n with 0%nat, _ => True | _, 0%nat => False |
      sz, n => †{pos_to_Qp (Pos.of_nat sz) / pos_to_Qp (Pos.of_nat n)}l…sz end.
  Arguments freeable_sz: simpl never.

  Global Instance freeable_sz_timeless n sz l : Timeless (freeable_sz n sz l).
  Proof. case sz, n; apply _. Qed.

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ †{1}l…n ∨ ⌜Z.of_nat n = 0⌝.
  Proof.
    case n=> [|n']. { iSplit; iIntros; by [iRight|]. }
    have ->: Z.of_nat (S n') = 0 ↔ False by done.
    by rewrite right_id /freeable_sz Qp_div_diag.
  Qed.

  Lemma freeable_sz_full_S n l : freeable_sz (S n) (S n) l ⊣⊢ †{1}l…(S n).
  Proof.
    rewrite freeable_sz_full. iSplit; [|iIntros; by iLeft]. by iIntros "[$|%]".
  Qed.

  Lemma freeable_sz_split n sz sz' l :
    freeable_sz n sz l ∗ freeable_sz n sz' (l +ₗ sz) ⊣⊢
    freeable_sz n (sz + sz') l.
  Proof.
    case sz; [|case sz'; [|rewrite /freeable_sz; case n]]=>/= *.
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit; by [iIntros "[??]"|iIntros].
    - rewrite heap_freeable_op_eq. f_equiv; [|done].
      by rewrite -Qp_div_add_distr pos_to_Qp_add -Nat2Pos.inj_add.
  Qed.

  Lemma freeable_sz_eq n sz sz' l :
    sz = sz' → freeable_sz n sz l -∗ freeable_sz n sz' l.
  Proof. iIntros (->) "$". Qed.

  (* Make sure 'simpl' doesn't unfold. *)
  Global Opaque freeable_sz.

  Program Definition own_ptr {𝔄} (n: nat) (ty: type 𝔄) : type 𝔄 := {|
    ty_size := 1;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl := [S(d') := d] [loc[l] := vl]
      ▷ l ↦∗: ty.(ty_own) vπ d' tid ∗ freeable_sz n ty.(ty_size) l;
    ty_shr vπ d κ tid l := [S(d') := d]
      ∃l': loc, &frac{κ}(λ q', l ↦{q'} #l') ∗ ▷ ty.(ty_shr) vπ d' κ tid l';
  |}%I.
  Next Obligation.
    move=> ????[|?]*; [by iIntros|]. rewrite/= by_just_loc_ex. by iIntros "[%[->?]]".
  Qed.
  Next Obligation.
    move=> ???[|?][|?] */=; try (by iIntros); [lia|]. do 7 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ???[|?][|?] */=; try (by iIntros); [lia|]. do 4 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??????[|?]*; [by iIntros|]. iIntros "#? [%l[??]]". iExists l.
    iSplit; by [iApply frac_bor_shorten|iApply ty_shr_lft_mono].
  Qed.
  Next Obligation.
    move=> ????? d *. iIntros "#LFT #In Bor κ". rewrite split_mt_ptr.
    move: d=> [|d]; [by iMod (bor_persistent with "LFT Bor κ") as "[>[]_]"|]=>/=.
    iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_later_tok with "LFT Bor κ") as "Bor"; [done|].
    iIntros "!>!>!>". iMod "Bor" as "[Bor κ]".
    iMod (ty_share with "LFT In Bor κ") as "Upd"; [done|]. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iIntros ">[?$] !>". iExists _. iFrame.
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|]. rewrite/= {1}by_just_loc_ex.
    iIntros "#LFT #In (%&->& [%[↦ ty]] & †) κ !>!>!>".
    iDestruct (ty_own_proph with "LFT In ty κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros ">(%ξl & %q &%& ξl & Toty) !>".
    iExists ξl, q. iSplit; [done|]. iIntros "{$† $ξl}ξl".
    iMod ("Toty" with "ξl") as "[?$]". iExists vl. by iFrame.
  Qed.
  Next Obligation.
    move=> ?????[|?]*/=; [by iIntros|]. iIntros "#LFT #In #In' [%l[↦ ty]] κ !>!>".
    iDestruct (ty_shr_proph with "LFT In In' ty κ") as "> Upd"; [done|].
    iIntros "!>!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%ξl & %q &%& ξl & Toκ) !>". iExists ξl, q. iSplit; [done|].
    iIntros "{$ξl}ξl". by iMod ("Toκ" with "ξl").
  Qed.

  Global Instance own_ne {𝔄} n : NonExpansive (@own_ptr 𝔄 n).
  Proof. solve_ne_type. Qed.

  Global Instance own_type_contractive 𝔄 n : TypeContractive (@own_ptr 𝔄 n).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |].
    - move=>/= > ->*. do 9 (f_contractive || f_equiv). by simpl in *.
    - move=>/= > *. do 6 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance own_send {𝔄} n (ty: type 𝔄) : Send ty → Send (own_ptr n ty).
  Proof. move=> >/=. by do 9 (f_equiv || move=>?). Qed.

  Global Instance own_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync (own_ptr n ty).
  Proof. move=> >/=. by do 6 (f_equiv || move=>?). Qed.

  Global Instance own_just_loc {𝔄} n (ty: type 𝔄) : JustLoc (own_ptr n ty).
  Proof. iIntros (?[|]?[|[[]|][]]) "? //". by iExists _. Qed.

  Lemma own_resolve {𝔄} E L n (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (own_ptr n ty) Φ.
  Proof.
    iIntros (Rslv ???[|]?[|[[]|][]]?) "LFT PROPH E L own //".
    iIntros "/=!>!>!>". iDestruct "own" as "[(%& _ & ty) _]".
    by iApply (Rslv with "LFT PROPH E L").
  Qed.

  Lemma own_real {𝔄 𝔅} E L n ty (f: 𝔄 → 𝔅) :
    real E L ty f → real E L (own_ptr n ty) f.
  Proof.
    move=> [Rlo Rls]. split.
    - iIntros (???[|]?[|[[]|][]]?) "LFT E L own //". iIntros "/=!>!>!>".
      iDestruct "own" as "[(%& ↦ & ty) $]".
      iMod (Rlo with "LFT E L ty") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >($&$&?) !>!>".
      iExists _. iFrame.
    - iIntros (???[|]????) "LFT E L own //". iDestruct "own" as (?) "[Bor ty]".
      iIntros "!>!>". iMod (Rls with "LFT E L ty") as "Upd"; [done|].
      iIntros "/=!>!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">($&$& ?) !>". iExists _. iFrame.
  Qed.

  Lemma own_type_incl {𝔄 𝔅} n (f: 𝔄 → 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗ type_incl (own_ptr n ty1) (own_ptr n ty2) f.
  Proof.
    iIntros "#(%Eq &?& InOwn & InShr)". do 2 (iSplit; [done|]). iSplit; iModIntro.
    - iIntros (?[|?]??); [done|]. rewrite/= {1}by_just_loc_ex Eq.
      iIntros "(%&->& ↦ &$)". iApply (heap_mapsto_pred_wand with "↦"). iApply "InOwn".
    - iIntros (?[|?]???); [done|]. iIntros "#[%l'[??]]". iExists l'.
      iSplit; [done|]. by iApply "InShr".
  Qed.

  Lemma own_subtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (own_ptr n ty) (own_ptr n ty') f.
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply own_type_incl; by [|iApply "Incl"].
  Qed.

  Lemma own_eqtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (own_ptr n ty) (own_ptr n ty') f g.
  Proof. move=> [??]. split; by apply own_subtype. Qed.
End own.

Section box.
  Context `{!typeG Σ}.

  Definition box {𝔄} (ty: type 𝔄) : type 𝔄 := own_ptr ty.(ty_size) ty.

  Global Instance box_ne 𝔄 : NonExpansive (@box 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance box_type_contractive 𝔄 : TypeContractive (@box 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |].
    - move=>/= > ->*. do 9 (f_contractive || f_equiv). by simpl in *.
    - move=>/= *. do 6 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Lemma box_type_incl {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty':
    type_incl ty ty' f -∗ type_incl (box ty) (box ty') f.
  Proof.
    iIntros "[%Eq ?]". rewrite /box Eq. iApply own_type_incl. by iSplit.
  Qed.

  Lemma box_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (box ty) (box ty') f.
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #?". iApply box_type_incl. by iApply "Incl".
  Qed.

  Lemma box_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (box ty) (box ty') f g.
  Proof. move=> [??]. split; by apply box_subtype. Qed.
End box.

Section typing.
  Context `{!typeG Σ}.

  Lemma write_own {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) n E L :
    ty.(ty_size) = ty'.(ty_size) →
    typed_write E L (own_ptr n ty') ty' (own_ptr n ty) ty id (λ _ a, a).
  Proof.
    move=> Sz. split; [done|]. iIntros (?[|][[]|]??) "_ _ _ $ own //".
    iDestruct "own" as "[(%vl & >↦ & ty) †]". iModIntro. iExists _.
    iSplit; [done|]. iSplitL "↦ ty".
    - iNext. iExists _. iFrame "↦". iApply ty_own_depth_mono; [|done]. lia.
    - iIntros (??) "$ ? !>". by rewrite Sz.
  Qed.

  Lemma read_own_copy {𝔄} (ty: type 𝔄) n E L :
    Copy ty → typed_read E L (own_ptr n ty) ty (own_ptr n ty) id id.
  Proof.
    move=> ??[|?]???; iIntros "_ _ $$ own"=>//=. setoid_rewrite by_just_loc_ex at 1.
    iDestruct "own" as (l[=->]) "[(%vl & >↦ & ty) †]". iModIntro.
    iExists l, vl, 1%Qp. iSplit; [done|]. iFrame "↦ †". iSplit.
    - iApply ty_own_depth_mono; [|done]. lia.
    - iIntros "? !>!>". iExists vl. iFrame.
  Qed.

  Lemma read_own_move {𝔄} (ty: type 𝔄) n E L :
    typed_read E L (own_ptr n ty) ty (own_ptr n (↯ ty.(ty_size))) id (const tt).
  Proof.
    move=> ?[|?]???; iIntros "_ _ $$ own"=>//. setoid_rewrite by_just_loc_ex at 1.
    iDestruct "own" as (l[=->]) "[(%vl & >↦ & ty) †]".
    iDestruct (ty_size_eq with "ty") as "#>%". iModIntro.
    iExists l, vl, 1%Qp. iSplit; [done|]. iFrame "↦ †". iSplitL "ty".
    - iApply ty_own_depth_mono; [|done]. lia.
    - iIntros "?!>!>". iExists vl. simpl. auto with iFrame.
  Qed.

  Lemma type_new_instr n E L :
    0 ≤ n → let n' := Z.to_nat n in
    typed_instr_ty E L +[] (new [ #n])%E (own_ptr n' (↯ n')) (λ post _, post ()).
  Proof.
    iIntros (?????) "_ TIME _ _ _ $$ _ ?". iMod persistent_time_receipt_0 as "⧖".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new=>//. iIntros "!>" (l) "(† & ↦) #⧖". iExists -[const ()].
    iSplit; [|done]. rewrite/= right_id (tctx_hasty_val #l).
    iExists 1%nat. iFrame "⧖". rewrite/= freeable_sz_full Z2Nat.id; [|done].
    iFrame "†". iNext. iExists _. iFrame "↦". rewrite repeat_length. auto.
  Qed.

  Lemma type_new {𝔄l 𝔅} n x e tr E L (C: cctx 𝔅) (T: tctx 𝔄l) :
    Closed (x :b: []) e → 0 ≤ n → let n' := Z.to_nat n in
    (∀v: val, typed_body E L C (v ◁ own_ptr n' (↯ n') +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := new [ #n] in e) (λ post al, tr post (() -:: al)).
  Proof.
    iIntros. iApply type_let; [by apply type_new_instr|solve_typing|done..].
  Qed.

  Lemma type_new_subtype {𝔄 𝔅l ℭ} (ty: type 𝔄) n (T: tctx 𝔅l) f e tr x E L (C: cctx ℭ) :
    Closed (x :b: []) e → 0 ≤ n → let n' := Z.to_nat n in
    subtype E L (↯ n') ty f →
    (∀v: val, typed_body E L C (v ◁ own_ptr n' ty +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := new [ #n] in e) (λ post al, tr post (f () -:: al)).
  Proof.
    iIntros (??? Sub) "?".
    iApply type_let; [by apply type_new_instr|solve_typing| |]; last first.
    { iIntros (?).
      iApply typed_body_tctx_incl;
        [eapply subtype_tctx_incl, own_subtype, Sub|done]. }
    done.
  Qed.

  Lemma type_delete_instr {𝔄} (ty: type 𝔄) (n: Z) p E L :
    let n' := ty.(ty_size) in n = Z.of_nat n' →
    typed_instr E L +[p ◁ own_ptr n' ty] (delete [ #n; p])%E (λ _, +[])
      (λ post _, post -[]).
  Proof.
    iIntros (?->??[?[]]) "_ _ _ _ _ $$ [p _] #Obs". wp_bind p.
    iApply (wp_hasty with "p"). iIntros (?[|?] _) "? own"; [done|].
    setoid_rewrite by_just_loc_ex. iDestruct "own" as (?[=->]) "[(%& >↦ & ty)?]".
    iDestruct (ty_size_eq with "ty") as "#>%Sz". iApply (wp_delete with "[-]").
    - by rewrite /n' -Sz.
    - iFrame "↦". rewrite Sz. by iApply freeable_sz_full.
    - iIntros "!>_". iExists -[]. by iSplit.
  Qed.

  Lemma type_delete {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) n' (n: Z) p e
    E L (C: cctx 𝔇) (T: tctx 𝔅l) (T': tctx ℭl) trx tr :
    Closed [] e → tctx_extract_ctx E L +[p ◁ own_ptr n' ty] T T' trx →
    n' = ty.(ty_size) → n = n' → typed_body E L C T' e tr -∗
    typed_body E L C T (delete [ #n; p ];; e) (trx ∘ (λ post '(_ -:: al), tr post al)).
  Proof.
    iIntros (? Extr -> ?) "?". iApply type_seq; [by eapply type_delete_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.

  Lemma type_letalloc_1 {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) (x: string) p e
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed [] p → Closed [x] e →
    tctx_extract_ctx E L +[p ◁ ty] T T' trx → ty.(ty_size) = 1%nat →
    (∀v: val, typed_body E L C (v ◁ box ty +:: T') (subst x v e) tr) -∗
    typed_body E L C T (letalloc: x <- p in e) (trx ∘ tr).
  Proof.
    iIntros (??? Sz) "?". iApply typed_body_tctx_incl; [done|].
    iApply typed_body_impl; last first.
    { iApply type_new; [|done|].
      - rewrite /Closed /= !andb_True. split; [done|]. split; [|done].
        split; [apply bool_decide_spec|eapply is_closed_weaken=>//]; set_solver.
      - iIntros (xv) "/=".
        have ->: (subst x xv (x <- p;; e))%E = (xv <- p;; subst x xv e)%E.
        { rewrite /subst /=.
          repeat f_equal;
            [by rewrite bool_decide_true|eapply is_closed_subst=>//; set_solver]. }
        iApply type_assign;
          [|solve_typing|by eapply write_own|solve_typing|by rewrite /box Sz].
        apply subst_is_closed; [apply is_closed_of_val|done]. }
    by move=>/= ?[??]?.
  Qed.

  Lemma type_letalloc_n {𝔄 𝔅 𝔅' ℭl 𝔇l 𝔈} (ty: type 𝔄) (tyr: type 𝔅)
        (tyr': type 𝔅') gt st (T: tctx ℭl) (T': tctx 𝔇l) trx tr (x: string)
        p e E L (C: cctx 𝔈) :
    Closed [] p → Closed [x] e → tctx_extract_ctx E L +[p ◁ tyr] T T' trx →
    typed_read E L tyr ty tyr' gt st →
    (∀v: val, typed_body E L C (v ◁ box ty +:: p ◁ tyr' +:: T') (subst x v e) tr) -∗
    typed_body E L C T (letalloc: x <-{ty.(ty_size)} !p in e) (trx ∘
      (λ post '(b -:: bl), tr post (gt b -:: st b -:: bl))).
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    iApply typed_body_impl; last first.
    { iApply type_new; [|lia|]=>/=.
      - rewrite /Closed /=. rewrite !andb_True.
        eauto 10 using is_closed_of_val, is_closed_weaken with set_solver.
    - iIntros (xv).
      have ->: subst x xv (x <-{ty.(ty_size)} !p;; e)%E =
               (xv <-{ty.(ty_size)} !p;; subst x xv e)%E.
      { rewrite /subst /=. repeat f_equal.
        - eapply (is_closed_subst []); [apply is_closed_of_val|set_solver].
        - by rewrite bool_decide_true.
        - eapply is_closed_subst; [done|set_solver]. }
      rewrite Nat2Z.id. iApply type_memcpy.
      + apply subst_is_closed; [apply is_closed_of_val|done].
      + solve_typing.
      + by apply (write_own ty (uninit _)).
      + solve_typing.
      + done.
      + done.
      + done. }
      by move=>/= ?[??]?.
  Qed.
End typing.

Global Hint Resolve own_resolve own_real own_subtype own_eqtype
  box_subtype box_eqtype write_own read_own_copy : lrust_typing.
(* By setting the priority high, we make sure copying is tried before
   moving. *)
Global Hint Resolve read_own_move | 100 : lrust_typing.
