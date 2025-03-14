From iris.proofmode Require Import proofmode.
From lrust.typing Require Import type lft_contexts.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅 ℭ: syn_type) (𝔄l 𝔅l ℭl 𝔇l: syn_typel).

Definition path := expr.
Bind Scope expr_scope with path.

Inductive tctx_elt `{!typeG Σ} 𝔄 : Type :=
| TCtx_hasty (p: path) (ty: type 𝔄)
| TCtx_blocked (p: path) (κ: lft) (ty: type 𝔄).

Notation tctx := (hlist tctx_elt).

Notation "p ◁ ty" := (TCtx_hasty _ p ty%T) (at level 55).
Notation "p ◁{ κ } ty" := (TCtx_blocked _ p κ ty%T)
   (at level 55, format "p  ◁{ κ }  ty").

(* [pred] is used by [Nat] *)
Notation pred' A := (A → Prop) (only parsing).
Notation predl 𝔄l := (pred' (plist of_syn_type 𝔄l)).
Notation predl_trans 𝔄l 𝔅l := (predl 𝔅l → predl 𝔄l).
Notation predl_trans' 𝔄l 𝔅 := (pred' 𝔅 → predl 𝔄l).

Global Instance pred'_equiv A : Equiv (pred' A) := pointwise_relation _ (↔).
Global Instance predl_trans_equiv 𝔄l 𝔅l : Equiv (predl_trans 𝔄l 𝔅l) :=
  pointwise_relation _ (pointwise_relation _ (↔)).
Global Instance predl_trans'_equiv 𝔄l 𝔅 : Equiv (predl_trans' 𝔄l 𝔅) :=
  pointwise_relation _ (pointwise_relation _ (↔)).

Notation predₛ 𝔄 := (𝔄 → Propₛ)%ST.
Notation predlₛ 𝔄l := (predₛ (Π! 𝔄l))%ST.
Notation predl_trans'ₛ 𝔄l 𝔅 := (predₛ 𝔅 → predlₛ 𝔄l)%ST.

Definition trans_app {𝔄l 𝔅l ℭl 𝔇l} (tr: predl_trans 𝔄l 𝔅l) (tr': predl_trans ℭl 𝔇l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ 𝔇l) := λ post acl,
  let '(al, cl) := psep acl in tr (λ bl, tr' (λ dl, post (bl -++ dl)) cl) al.

Global Instance trans_app_proper {𝔄l 𝔅l ℭl 𝔇l} tr tr' :
  Proper ((≡) ==> (≡)) tr →
  Proper ((≡) ==> (≡)) tr' →
  Proper ((≡) ==> (≡)) (@trans_app 𝔄l 𝔅l ℭl 𝔇l tr tr').
Proof. intros Htr Htr' ????. unfold trans_app. apply Htr=>?. apply Htr'=>? //. Qed.

Definition trans_lower {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (ℭl ++ 𝔄l) (ℭl ++ 𝔅l) := λ post cal,
  let '(cl, al) := psep cal in tr (λ bl, post (cl -++ bl)) al.

Definition trans_upper {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ ℭl) := λ post acl,
  let '(al, cl) := psep acl in tr (λ bl, post (bl -++ cl)) al.

Definition trans_tail {ℭ 𝔄l 𝔅l} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (ℭ :: 𝔄l) (ℭ :: 𝔅l) :=
  λ post '(c -:: al), tr (λ bl, post (c -:: bl)) al.

Section type_context.
  Context `{!typeG Σ}.

  Fixpoint eval_path (p: path) : option val := match p with
    | BinOp OffsetOp e (#(LitInt n))%E => match eval_path e with
        Some #(LitLoc l) => Some #(l +ₗ n) | _ => None end
    | e => to_val e end.

  Lemma eval_path_of_val (v: val) : eval_path v = Some v.
  Proof. case v; [done|]=>/= *. by rewrite (decide_True_pi _). Qed.

  Lemma wp_eval_path E p v :
    eval_path p = Some v → ⊢ WP p @ E {{ v', ⌜v' = v⌝ }}.
  Proof.
    move: v. elim: p=>//.
    - move=> > [=?]. by iApply wp_value.
    - move=> > ?? /of_to_val ?. by iApply wp_value.
    - case=>// e Wp. case=>//. case=>//= ?. move: Wp.
      case (eval_path e)=>//. case=>//. case=>// ? Wp _ ?[=<-].
      wp_bind e. iApply wp_wand; [by iApply Wp|]. iIntros. subst. by wp_op.
  Qed.

  Lemma eval_path_closed p v : eval_path p = Some v → Closed [] p.
  Proof.
    move: v. elim p=>//.
    - move=> >. rewrite /eval_path=> /of_to_val <-. apply is_closed_of_val.
    - case=>// e IH. case=>//. case=>//= ? _. move: IH. case (eval_path e)=>//.
      case=>//. case=>// ? IH ? _. move: (IH _ eq_refl). apply _.
  Qed.

  (** Type Context Element Interpretation *)
  Definition tctx_elt_interp {𝔄} (tid: thread_id) (t: tctx_elt 𝔄) (vπ: proph 𝔄)
    : iProp Σ := match t with
    | p ◁ ty => ∃v d, ⌜eval_path p = Some v⌝ ∗ ⧖d ∗ ty.(ty_own) vπ d tid [v]
    | p ◁{κ} ty => ∃v, ⌜eval_path p = Some v⌝ ∗
        ([†κ] ={⊤}=∗ ∃vπ' d, ▷(vπ :== vπ') ∗ ⧖d ∗ ty.(ty_own) vπ' d tid [v]) end%I.

  (* Block tctx_elt_interp from reducing with simpl when t is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.
End type_context.

(** Type Context Interpretation *)
Notation tctx_interp tid :=
  (big_sepHL_1 (λ 𝔄 t vπ, tctx_elt_interp (𝔄:=𝔄) tid t vπ)).

Section lemmas.
  Context `{!typeG Σ}.

  Lemma tctx_hasty_val {𝔄} (v: val) (ty: type 𝔄) vπ tid :
    tctx_elt_interp tid (v ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty.(ty_own) vπ d tid [v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (??[=->]) "[??]". iExists _. iFrame.
    - iDestruct 1 as (d) "[??]". iExists _, _. by iFrame.
  Qed.

  Lemma tctx_elt_interp_hasty_path {𝔄} p1 p2 (ty: type 𝔄) tid vπ :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (p1 ◁ ty) vπ ⊣⊢ tctx_elt_interp tid (p2 ◁ ty) vπ.
  Proof. move=> Hp. rewrite /tctx_elt_interp. by setoid_rewrite Hp. Qed.

  Lemma tctx_hasty_val' {𝔄} tid p v (ty: type 𝔄) vπ:
    Some v = eval_path p →
    tctx_elt_interp tid (p ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty.(ty_own) vπ d tid [v].
  Proof.
    move=> ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    by rewrite eval_path_of_val.
  Qed.

  Lemma wp_hasty {𝔄} E tid p (ty: type 𝔄) vπ Φ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗
    (∀v d, ⌜Some v = eval_path p⌝ -∗ ⧖d -∗ ty.(ty_own) vπ d tid [v] -∗ Φ v) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iIntros "(%&%&%&#?&?) ToΦ". iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (?->). by iApply "ToΦ".
  Qed.

  Lemma closed_hasty {𝔄} tid p (ty: type 𝔄) vπ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗ ⌜Closed [] p⌝.
  Proof. iIntros "(%&%&%&_)!%". by eapply eval_path_closed. Qed.

  (** resolveing a Type Context *)

  Definition resolve_tctx {𝔄l} (E: elctx) (L: llctx) (T: tctx 𝔄l)
    (Φ: plist of_syn_type 𝔄l → Prop → Prop) : Prop :=
    ∀F q tid vπl, ↑lftN ∪ ↑prophN ⊆ F → lft_ctx -∗ proph_ctx -∗
      elctx_interp E -∗ llctx_interp L q -∗ tctx_interp tid T vπl ={F}=∗
        ∃d, ⧖d ∗ |={F}▷=>^d |={F}=>
          ⟨π, ∀φ, Φ (vπl -$ π) φ → φ⟩ ∗ llctx_interp L q.

  Lemma resolve_tctx_just {𝔄l} E L (T: tctx 𝔄l) : resolve_tctx E L T (const id).
  Proof.
    move=> *. iMod persistent_time_receipt_0 as "⧖". iIntros "_ _ _ $ _!>". iExists _.
    iFrame "⧖". iApply step_fupdN_full_intro. by iApply proph_obs_true=>/= ?.
  Qed.

  Lemma resolve_tctx_nil E L : resolve_tctx E L +[] (const id).
  Proof. apply resolve_tctx_just. Qed.

  Lemma resolve_tctx_cons_hasty {𝔄 𝔅l} E L p (ty: type 𝔄) Φ (T: tctx 𝔅l) Ψ :
    resolve E L ty Φ → resolve_tctx E L T Ψ →
    resolve_tctx E L (p ◁ ty +:: T) (λ '(a -:: bl) φ, Φ a → Ψ bl φ).
  Proof.
    iIntros (Rslv Rslv' ???[??]?) "#LFT #PROPH #E [L L₊] /=[(%&%&_& ⧖ & ty) T]".
    iMod (Rslv with "LFT PROPH E L ty") as "ToObs"; [done|].
    iMod (Rslv' with "LFT PROPH E L₊ T") as (?) "[⧖' ToObs']"; [done|].
    iCombine "⧖ ⧖'" as "⧖". iCombine "ToObs ToObs'" as "ToObs".
    iExists _. iFrame "⧖". iApply (step_fupdN_wand with "ToObs").
    iIntros "!> [>[Obs $] >[Obs' $]] !>". iCombine "Obs Obs'" as "?".
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]? Imp'. by apply Imp, Imp'.
  Qed.

  Lemma resolve_tctx_cons_just {𝔄 𝔅l} E L (t: tctx_elt 𝔄) (T: tctx 𝔅l) Φ :
    resolve_tctx E L T Φ → resolve_tctx E L (t +:: T) (λ '(_ -:: bl), Φ bl).
  Proof.
    iIntros (Rslv ???[??]?) "LFT PROPH E L /=[_ T]".
    by iApply (Rslv with "LFT PROPH E L T").
  Qed.

  Lemma resolve_tctx_cons_just_hasty {𝔄 𝔅l} E L p (ty: type 𝔄) (T: tctx 𝔅l) Φ :
    resolve E L ty (const True) → resolve_tctx E L T Φ →
    resolve_tctx E L (p ◁ ty +:: T) (λ '(_ -:: bl), Φ bl).
  Proof. move=> ?. apply resolve_tctx_cons_just. Qed.

  Lemma resolve_tctx_cons_just_blocked {𝔄 𝔅l} E L p κ (ty: type 𝔄) (T: tctx 𝔅l) Φ :
    resolve_tctx E L T Φ → resolve_tctx E L (p ◁{κ} ty +:: T) (λ '(_ -:: bl), Φ bl).
  Proof. apply resolve_tctx_cons_just. Qed.

  (** Taking Out the Real Part of a Type Context *)

  Definition real_tctx {𝔄l B} (E: elctx) (L: llctx) (T: tctx 𝔄l)
      (f: plist of_syn_type 𝔄l → B) : Prop :=
    ∀q tid vπl, lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
      tctx_interp tid T vπl ={⊤}=∗ ∃d, ⧖d ∗ |={⊤}▷=>^d |={⊤}=>
        ⌜∃vl, f ∘ papply vπl = const vl⌝ ∗ llctx_interp L q ∗ tctx_interp tid T vπl.

  Lemma real_tctx_nil E L : real_tctx E L +[] id.
  Proof.
    iIntros (???) "_ _ $ _". iMod persistent_time_receipt_0 as "⧖".
    iExists 0%nat. iFrame "⧖". iPureIntro. by exists -[].
  Qed.

  Lemma real_tctx_cons {𝔄 𝔅l ℭ D} E L p ty (f: 𝔄 → ℭ) T (g: plist _ 𝔅l → D) :
    real E L ty f → real_tctx E L T g →
    real_tctx E L (p ◁ ty +:: T) (λ '(a -:: bl), f a -:: g bl).
  Proof.
    iIntros ([Rl _] Rl' ??[??]) "#LFT #E [L L₊] /=[(%&%&%& ⧖ & ty) T]".
    iMod (Rl with "LFT E L ty") as "Upd"; [done|].
    iMod (Rl' with "LFT E L₊ T") as (?) "[⧖' Upd']". iCombine "⧖ ⧖'" as "#⧖".
    iCombine "Upd Upd'" as "Upd". iExists _. iFrame "⧖".
    iApply (step_fupdN_wand with "Upd").
    iIntros "!> [>(%Eq &$& ty) >(%Eq' &$&$)] !>". iSplit; last first.
    { iExists _, _. iFrame "ty". iSplit; [done|].
      iApply persistent_time_receipt_mono; [|done]. lia. }
    iPureIntro. move: Eq=> [b Eq]. move: Eq'=> [bl Eq']. exists (b -:: bl).
    fun_ext=> π. by move: (equal_f Eq π) (equal_f Eq' π)=>/= <-<-.
  Qed.

  Lemma real_tctx_cons_blocked {𝔄 𝔅l C} E L p (ty: type 𝔄) T (g: plist _ 𝔅l → C) κ :
    real_tctx E L T g → real_tctx E L (p ◁{κ} ty +:: T) (λ '(_ -:: bl), g bl).
  Proof.
    iIntros (Rl ??[??]) "LFT E L /=[$ T]".
    iMod (Rl with "LFT E L T") as (?) "[⧖ Upd]". iExists _. iFrame "⧖".
    iApply (step_fupdN_wand with "Upd"). by iIntros "!> >($&$&$)".
  Qed.

  (** Type Context Inclusion *)

  Definition tctx_incl {𝔄l 𝔅l} (E: elctx) (L: llctx) (T: tctx 𝔄l) (T': tctx 𝔅l)
    (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    Proper ((≡) ==> (≡)) tr ∧
    ∀q tid vπl postπ,
      lft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
      tctx_interp tid T vπl -∗ ⟨π, tr (postπ π) (vπl -$ π)⟩
      ={⊤}=∗
      ∃vπl', llctx_interp L q ∗ tctx_interp tid T' vπl' ∗ ⟨π, postπ π (vπl' -$ π)⟩.

  Lemma tctx_incl_impl {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l)
                       (tr tr': predl_trans 𝔄l 𝔅l) E L :
    tctx_incl E L T T' tr' → (∀post vl, tr post vl → tr' post vl) →
    Proper ((≡) ==> (≡)) tr →
    tctx_incl E L T T' tr.
  Proof.
    move=> [? In] Imp. split; [done|].
    iIntros (????) "LFT PROPH UNIQ E L T #Obs".
    iMod (In with "LFT PROPH UNIQ E L T []") as "$"; [|done].
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma tctx_incl_ext {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l) tr tr' E L :
    tctx_incl E L T T' tr' → (∀post vl, tr post vl ↔ tr' post vl) →
    tctx_incl E L T T' tr.
  Proof.
    move=> In Eq. eapply tctx_incl_impl; [done| |].
    - move=> ??. by rewrite Eq.
    - move=> ????. rewrite !Eq. by apply In.
 Qed.

  Lemma tctx_incl_refl {𝔄l} (T: tctx 𝔄l) E L : tctx_incl E L T T id.
  Proof. split; [by apply _|]. move=> ?? vπl ?. iIntros. iExists vπl. by iFrame. Qed.

  Lemma tctx_incl_trans {𝔄l 𝔅l ℭl} tr tr' (T1: tctx 𝔄l) (T2: tctx 𝔅l) (T3: tctx ℭl) E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L T2 T3 tr' → tctx_incl E L T1 T3 (tr ∘ tr').
  Proof.
    move=> In In'. split.
    { eapply compose_proper; [apply In|apply In']. }
    iIntros "* #LFT #PROPH #UNIQ #E L T Obs".
    destruct In as [? In]. destruct In' as [? In'].
    iMod (In with "LFT PROPH UNIQ E L T Obs") as (?) "(L & T & Obs)".
    iMod (In' with "LFT PROPH UNIQ E L T Obs") as (vπl'') "(?&?&?)".
    iExists vπl''. by iFrame.
  Qed.

  Lemma tctx_incl_app {𝔄l 𝔅l ℭl 𝔇l}
    (T1: tctx 𝔄l) (T1': tctx 𝔅l) (T2: tctx ℭl) (T2': tctx 𝔇l) tr tr' E L :
    tctx_incl E L T1 T1' tr → tctx_incl E L T2 T2' tr' →
    tctx_incl E L (T1 h++ T2) (T1' h++ T2') (trans_app tr tr').
  Proof.
    move=> [? In1] [? In2]. split; [apply _|].
    move=>?? vπl ?. move: (papp_ex vπl)=> [?[?->]].
    iIntros "#LFT #PROPH #UNIQ #E L [T1 T2] Obs".
    iMod (In1 with "LFT PROPH UNIQ E L T1 [Obs]") as (wπl) "(L & T1' & Obs)".
    { iApply proph_obs_eq; [|done]=> ?.
      by rewrite /trans_app papply_app papp_sepl papp_sepr. }
    iMod (In2 with "LFT PROPH UNIQ E L T2 Obs") as (wπl') "(L & T2' &?)".
    iExists (wπl -++ wπl'). iFrame "L T1' T2'".
    iApply proph_obs_eq; [|done]=>/= ?. by rewrite papply_app.
  Qed.

  Lemma tctx_incl_frame_l {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tf: tctx ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (Tf h++ T) (Tf h++ T') (trans_lower tr).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { apply tctx_incl_app; [|done]. apply tctx_incl_refl. }
    done.
  Qed.
  Lemma tctx_incl_frame_r {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tf: tctx ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (T h++ Tf) (T' h++ Tf) (trans_upper tr).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { apply tctx_incl_app; [done|]. apply tctx_incl_refl. }
    done.
  Qed.
  Lemma tctx_incl_tail {𝔄 𝔄l 𝔅l} (t: tctx_elt 𝔄) (T1: tctx 𝔄l) (T2: tctx 𝔅l) tr E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L (t +:: T1) (t +:: T2) (trans_tail tr).
  Proof.
    move=> ?. eapply tctx_incl_ext. { by apply (tctx_incl_frame_l _ _ +[_]). }
    by move=> ?[??].
  Qed.

  Lemma tctx_incl_swap {𝔄 𝔅 𝔄l} (t: tctx_elt 𝔄) (t': tctx_elt 𝔅) (T: tctx 𝔄l) E L :
    tctx_incl E L (t +:: t' +:: T) (t' +:: t +:: T)
      (λ post '(a -:: b -:: al), post (b -:: a -:: al)).
  Proof.
    split; [by intros ??? [? [? ?]]|].
    iIntros (??(vπ & vπ' & wπl)?) "_ _ _ _ $ (?&?&?) ?!>".
    iExists (vπ' -:: vπ -:: wπl). iFrame.
  Qed.

  Lemma tctx_incl_resolve_head {𝔄 𝔅l} (t: tctx_elt 𝔄) (T: tctx 𝔅l) E L :
    tctx_incl E L (t +:: T) T (λ post '(_ -:: bl), post bl).
  Proof.
    split; [by intros ??? [? ?]|].
    iIntros (??[??]?) "_ _ _ _ $ [_ T] ? !>". iExists _. by iFrame "T".
  Qed.

  Lemma tctx_incl_resolve_lower {𝔄l 𝔅l} (T: tctx 𝔄l) (T': tctx 𝔅l) E L :
    tctx_incl E L (T h++ T') T (λ post abl, post (psepl abl)).
  Proof.
    split; [by intros ????|].
    move=> ?? abπl ?. move: (papp_ex abπl)=> [aπl[?->]].
    iIntros "_ _ _ _ $ [T _] ? !>". iExists aπl. iFrame "T".
    iApply proph_obs_eq; [|done]=> ?. by rewrite/= papply_app papp_sepl.
  Qed.

  Definition tctx_equiv {𝔄l} (T T': tctx 𝔄l) : Prop :=
    ∀E L, tctx_incl E L T T' id ∧ tctx_incl E L T' T id.

  Lemma get_tctx_equiv {𝔄l} (T T': tctx 𝔄l) :
    (∀tid vπl, tctx_interp tid T vπl ⊣⊢ tctx_interp tid T' vπl) → tctx_equiv T T'.
  Proof.
    move=> Eq ??; split; (split; [apply _|]);
      iIntros (????) "_ _ _ _ $ T Obs !>"; iExists _; rewrite Eq; iFrame.
  Qed.

  Lemma copy_tctx_incl {𝔄 𝔄l} (ty: type 𝔄) `{!Copy ty} (T: tctx 𝔄l) p E L :
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty +:: p ◁ ty +:: T)
      (λ post '(a -:: al), post (a -:: a -:: al)).
  Proof.
    split; [by intros ??? [??]|].
    iIntros (??[vπ wπl]?) "_ _ _ _ $ /=[#? T] Obs !>".
    iExists (vπ -:: vπ -:: wπl). iFrame "Obs T". by iSplit.
  Qed.

  Lemma tctx_to_shift_loc_0 {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) E L :
    JustLoc ty → tctx_incl E L (p ◁ ty +:: T) (p +ₗ #0 ◁ ty +:: T) id.
  Proof.
    intros JLoc. split; [apply _|].
    - iIntros (??[??]?) "_ _ _ _ $ /=[(%&%& %Ev & ⧖ & ty) T] Obs !>".
      iExists (_-::_). iDestruct (JLoc with "ty") as %[?[=->]]. iFrame "T Obs".
      iExists _, _. iFrame "⧖ ty". by rewrite/= Ev shift_loc_0.
  Qed.

  Lemma tctx_of_shift_loc_0 {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) E L :
    tctx_incl E L (p +ₗ #0 ◁ ty +:: T) (p ◁ ty +:: T) id.
  Proof.
    split; [apply _|]. iIntros (??[??]?) "_ _ _ _ $ /=[(%&%& %Ev & ⧖ty) T] Obs !>".
    iExists (_-::_). iFrame "T Obs". iExists _, _. iFrame "⧖ty". iPureIntro.
    move: Ev=>/=. case (eval_path p)=>//. (do 2 case=>//)=> ?. by rewrite shift_loc_0.
  Qed.

  Lemma tctx_shift_loc_assoc {𝔄 𝔅l} (ty: type 𝔄) p (T: tctx 𝔅l) (z z': Z) :
    tctx_equiv (p +ₗ #z +ₗ #z' ◁ ty +:: T) (p +ₗ #(z + z') ◁ ty +:: T).
  Proof.
    apply get_tctx_equiv=>/= ?[??]. f_equiv.
    rewrite tctx_elt_interp_hasty_path; [done|]=>/=. case (eval_path p)=>//.
    (do 2 case=>//)=> ?. by rewrite shift_loc_assoc.
  Qed.

  Lemma subtype_tctx_incl {𝔄 𝔅 𝔄l} ty ty' (f: 𝔄 → 𝔅) (T: tctx 𝔄l) p E L :
    subtype E L ty ty' f →
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty' +:: T)
      (λ post '(a -:: al), post (f a -:: al)).
  Proof.
    intros Sub. split; [by intros ??? [??]|].
    iIntros (??[vπ wπl]?) "#LFT _ _ E L /=[(%v & %d &%&?& ty) T] Obs /=".
    iDestruct (Sub with "L E") as "#(_ & _ & #InOwn & _)". iModIntro.
    iExists (f ∘ vπ -:: wπl). iFrame "L T Obs". iExists v, d.
    do 2 (iSplit; [done|]). by iApply "InOwn".
  Qed.

  Lemma subtype_tctx_incl_blocked {𝔄 𝔅 𝔄l} (ty : type 𝔄) (ty' : type 𝔅)
                                  `{!Inj (=) (=) f}  κ κ' (T: tctx 𝔄l) p E L :
    subtype E L ty ty' f → lctx_lft_incl E L κ κ' →
    tctx_incl E L (p ◁{κ} ty +:: T) (p ◁{κ'} ty' +:: T)
      (λ post '(a -:: al), post (f a -:: al)).
  Proof.
    intros Sub InLft. split; [by intros ??? [??]|].
    iIntros (??[vπ wπl]?) "#LFT _ _ E L /=[(%v &%& Toty) T] Obs".
    iDestruct (Sub with "L E") as "#(_&_& #InOwn &_)".
    iDestruct (InLft with "L E") as "#κ⊑κ'". iModIntro. iExists (f ∘ vπ -:: wπl).
    iFrame "L Obs T". iExists v. iSplit; [done|]. iIntros "†κ'".
    iMod (lft_incl_dead with "κ⊑κ' †κ'") as "†κ"; [done|].
    iMod ("Toty" with "†κ") as (vπ' d) "(?& ⧖ & ty)". iModIntro.
    iExists (f ∘ vπ'), d. iFrame "⧖".
    iSplitR "ty"; by [iApply proph_eqz_constr|iApply "InOwn"].
  Qed.

  (* Extracting from a type context. *)

  Definition tctx_extract_elt {𝔄 𝔄l 𝔅l} E L (t: tctx_elt 𝔄)
    (T: tctx 𝔄l) (T': tctx 𝔅l) (tr: predl_trans 𝔄l (𝔄 :: 𝔅l)) : Prop :=
    tctx_incl E L T (t +:: T') tr.

  Lemma tctx_extract_elt_further {𝔄 𝔅 𝔄l 𝔅l}
    (t: tctx_elt 𝔄) (t': tctx_elt 𝔅) (T: tctx 𝔄l) (T': tctx 𝔅l) tr E L :
    tctx_extract_elt E L t T T' tr →
    tctx_extract_elt E L t (t' +:: T) (t' +:: T')
      (λ post '(b -:: al), tr (λ '(a -:: bl), post (a -:: b -:: bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; by [eapply tctx_incl_tail|apply tctx_incl_swap]. }
    move=> ?[??]/=. f_equal.
  Qed.

  Lemma tctx_extract_elt_here_copy {𝔄 𝔅 𝔄l} ty ty' (f: 𝔅 → 𝔄) (T: tctx 𝔄l) p p' E L :
    p = p' → Copy ty' → subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p' ◁ ty' +:: T) (p' ◁ ty' +:: T)
      (λ post '(b -:: al), post (f b -:: b -:: al)).
  Proof.
    move=> ->??. eapply tctx_incl_ext.
    { by eapply tctx_incl_trans; [apply copy_tctx_incl|apply subtype_tctx_incl]. }
    by move=> ?[??].
  Qed.

  Lemma tctx_extract_elt_here_exact {𝔄 𝔄l} (t: tctx_elt 𝔄) (T: tctx 𝔄l) E L :
    tctx_extract_elt E L t (t +:: T) T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_elt_here {𝔄 𝔅 𝔄l} ty ty' (f: 𝔅 → 𝔄) (T: tctx 𝔄l) p E L :
    subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p ◁ ty' +:: T) T
      (λ post '(b -:: al), post (f b -:: al)).
  Proof.
    move=> ?. eapply tctx_incl_ext; [by apply subtype_tctx_incl|]. by move=> ?[??].
  Qed.

  Definition tctx_extract_ctx {𝔄l 𝔅l ℭl} E L (T: tctx 𝔄l)
    (T1: tctx 𝔅l) (T2: tctx ℭl) (tr: predl_trans 𝔅l (𝔄l ++ ℭl)) : Prop :=
    tctx_incl E L T1 (T h++ T2) tr.

  Lemma tctx_extract_ctx_eq {𝔄l 𝔅l ℭl} tr tr' E L
                            (T: tctx 𝔄l) (T1: tctx 𝔅l) (T2: tctx ℭl) :
    tctx_extract_ctx E L T T1 T2 tr' → tr = tr' → tctx_extract_ctx E L T T1 T2 tr.
  Proof. by move=> ?->. Qed.

  Lemma tctx_extract_ctx_nil {𝔄l} (T: tctx 𝔄l) E L :
    tctx_extract_ctx E L +[] T T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_ctx_elt {𝔄 𝔄l 𝔅l ℭl 𝔇l}
      (t: tctx_elt 𝔄) (T: tctx 𝔄l) (T1: tctx 𝔅l) (T2: tctx ℭl) (T3: tctx 𝔇l)
      tr tr' E L :
    tctx_extract_elt E L t T1 T2 tr → tctx_extract_ctx E L T T2 T3 tr' →
    tctx_extract_ctx E L (t +:: T) T1 T3 (tr ∘ trans_tail tr').
  Proof. move=> ??. eapply tctx_incl_trans; by [|apply tctx_incl_tail]. Qed.

  Lemma tctx_extract_ctx_incl {𝔄l 𝔅l ℭl} (T: tctx 𝔄l) (T': tctx 𝔅l) (Tx: tctx ℭl) tr E L :
    tctx_extract_ctx E L T' T Tx tr →
    tctx_incl E L T T' (λ post, tr (λ bcl, post (psepl bcl))).
  Proof.
    move=> Ex. eapply tctx_incl_ext.
    { eapply tctx_incl_trans; [apply Ex|apply tctx_incl_resolve_lower]. }
    done.
  Qed.

  (** resolveing for Unblocking *)

  (* [κ] is a dummy parameter for automation *)
  Definition resolve_unblock_tctx {𝔄l 𝔅l} (E: elctx) (L: llctx) (κ: lft)
      (T: tctx 𝔄l) (T': tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀q tid vπl postπ, lft_ctx -∗ proph_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
      tctx_interp tid T vπl -∗ ⟨π, tr (postπ π) (vπl -$ π)⟩ ={⊤}=∗
        ∃d vπl', ⧖d ∗ |={⊤}▷=>^d |={⊤}=>
          llctx_interp L q ∗ tctx_interp tid T' vπl' ∗ ⟨π, postπ π (vπl' -$ π)⟩.

  Lemma resolve_unblock_tctx_impl {𝔄l 𝔅l} (tr tr': predl_trans 𝔄l 𝔅l) T T' E L κ :
    resolve_unblock_tctx E L κ T T' tr' → (∀post al, tr post al → tr' post al) →
    resolve_unblock_tctx E L κ T T' tr.
  Proof.
    iIntros (RslvU Imp ????) "LFT PROPH E L T Obs".
    iApply (RslvU with "LFT PROPH E L T [Obs]").
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma resolve_unblock_tctx_nil κ E L : resolve_unblock_tctx E L κ +[] +[] id.
  Proof.
    iIntros (??[]?) "/= _ _ _ $ _ $". iMod persistent_time_receipt_0 as "⧖".
    iExists 0%nat, -[]. by iFrame "⧖".
  Qed.

  Lemma resolve_unblock_tctx_cons_resolve {𝔄 𝔅l ℭl} (ty: type 𝔄) p Φ
      (T: tctx 𝔅l) (T': tctx ℭl) tr κ E L :
    κ ∈ ty_lfts ty → resolve' E L ty Φ → resolve_unblock_tctx E L κ T T' tr →
    resolve_unblock_tctx E L κ (p ◁ ty +:: T) T'
      (λ post '(a -:: bl), tr (λ cl, Φ a (post cl)) bl).
  Proof.
    iIntros (_ Rslv RslvU ??[vπ ?]?)
      "#LFT #PROPH #E [L L₊] /=[(%& %d &_& ⧖ & ty) T] Obs".
    iMod (Rslv with "LFT PROPH E L₊ ty") as "Upd"; [done|].
    iMod (RslvU with "LFT PROPH E L T Obs") as (? vπl') "[⧖' Upd']".
    iCombine "Upd Upd'" as "Upd". iCombine "⧖ ⧖'" as "⧖".
    iExists _, vπl'. iFrame "⧖". iApply (step_fupdN_wand with "Upd").
    iIntros "!> [>[Obs $] >($&$& Obs')]". iCombine "Obs Obs'" as "?".
    iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp.
  Qed.

  Lemma resolve_unblock_tctx_cons_keep {𝔄 𝔅l ℭl} (t: tctx_elt 𝔄)
      (T: tctx 𝔅l) (T': tctx ℭl) tr κ E L :
    resolve_unblock_tctx E L κ T T' tr →
    resolve_unblock_tctx E L κ (t +:: T) (t +:: T') (trans_tail tr).
  Proof.
    iIntros (RslvU ??[vπ ?]?) "LFT PROPH E L /=[t T] Obs".
    iMod (RslvU with "LFT PROPH E L T Obs") as (d vπl') "[⧖ Upd]". iModIntro.
    iExists d, (vπ -:: vπl'). iFrame "⧖". iApply (step_fupdN_wand with "Upd").
    iIntros ">($&$&?) !>". iFrame.
  Qed.

  (** Unblocking a Type Context *)

  Definition unblock_tctx {𝔄l} (E: elctx) (L: llctx) (κ: lft) (T T': tctx 𝔄l) : Prop :=
    ∀q tid vπl, lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗ [†κ] -∗
      tctx_interp tid T vπl ={⊤}=∗ ∃d vπl', ⧖d ∗ |={⊤}▷=> |={⊤}▷=>^d |={⊤}=>
        llctx_interp L q ∗ tctx_interp tid T' vπl' ∗ ⟨π, vπl -$ π = vπl' -$ π⟩.

  Lemma unblock_tctx_nil κ E L : unblock_tctx E L κ +[] +[].
  Proof.
    iIntros (??[]) "_ _ $ _ _". iMod persistent_time_receipt_0 as "⧖". iExists 0%nat, -[].
    iIntros "{$⧖}!>!>!>!>!>". iSplit; [done|]. by iApply proph_obs_true.
  Qed.

  Lemma unblock_tctx_cons_unblock {𝔄 𝔄l} p (ty: type 𝔄) (T T': tctx 𝔄l) κ E L :
    lctx_lft_alive E L (ty_lft ty) → unblock_tctx E L κ T T' →
    unblock_tctx E L κ (p ◁{κ} ty +:: T) (p ◁ ty +:: T').
  Proof.
    iIntros (Alv Un ??[??]) "#LFT #E [L L'] #†κ /=[(%v &%& Upd) T]".
    iMod ("Upd" with "†κ") as (vπ' dp) "(Eqz & #⧖dp & ty)".
    iMod (Un with "LFT E L †κ T") as (dT vπl') "[⧖dT >ToT']".
    iMod (Alv with "E L'") as (?) "[lft ToL']"; [done|].
    iMod (ty_own_proph with "LFT [] ty lft") as "Toty";
      [done|by iApply lft_incl_refl|].
    iExists _, (vπ' -:: vπl'). iCombine "⧖dp ⧖dT" as "$". iIntros "!>!>!>". iMod "ToT'".
    iModIntro. iCombine "Toty ToT'" as "Big". iApply (step_fupdN_wand with "Big").
    iIntros "[>(%&%&%& ξl & Toty) >($&$& Obs')]".
    iMod ("Eqz" with "[] ξl") as "[Obs ξl]"; [done|]. iCombine "Obs Obs'" as "?".
    iMod ("Toty" with "ξl") as "[ty lft]". iMod ("ToL'" with "lft") as "$".
    iModIntro. iSplit.
    - iExists v, dp. iSplit; [done|]. by iFrame.
    - by iApply proph_obs_impl; [|done]=> ?[->->].
  Qed.

  Lemma unblock_tctx_cons_just {𝔄 𝔄l} (t: tctx_elt 𝔄) (T T': tctx 𝔄l) κ E L :
    unblock_tctx E L κ T T' → unblock_tctx E L κ (t +:: T) (t +:: T').
  Proof.
    iIntros (Un ??[vπ ?]) "LFT E L †κ /=[t T]".
    iMod (Un with "LFT E L †κ T") as (d vπl') "[⧖ Upd]". iModIntro.
    iExists d, (vπ -:: vπl'). iFrame "⧖". iApply (step_fupdN_wand with "Upd").
    iIntros "!> >($&$&?) !>". iFrame "t". by iApply proph_obs_impl; [|done]=>/= ?->.
  Qed.

  Lemma unblock_tctx_cons_just_hasty {𝔄 𝔄l} p (ty: type 𝔄) (T T': tctx 𝔄l) κ E L :
    unblock_tctx E L κ T T' → unblock_tctx E L κ (p ◁ ty +:: T) (p ◁ ty +:: T').
  Proof. apply unblock_tctx_cons_just. Qed.

  Lemma unblock_tctx_cons_just_blocked {𝔄 𝔄l} p (ty: type 𝔄) (T T': tctx 𝔄l) κ κ' E L :
    κ ≠ κ' → unblock_tctx E L κ T T' →
    unblock_tctx E L κ (p ◁{κ'} ty +:: T) (p ◁{κ'} ty +:: T').
  Proof. move=> ?. apply unblock_tctx_cons_just. Qed.
End lemmas.

Ltac solve_extract :=
  eapply tctx_extract_ctx_eq; [solve_typing|];
  rewrite /trans_tail /compose /=; by reflexivity.

Ltac solve_resolve_unblock :=
  eapply resolve_unblock_tctx_impl; [solve_typing|]=> ??;
  rewrite /trans_tail /=; by exact id.

Global Hint Resolve resolve_tctx_nil : lrust_typing.
(* Mysteriously, registering [resolve_tctx_cons_*] with [Global Hint Resolve]
  does not help automation in some situations,
  but the following hints let automation work *)
Global Hint Extern 10 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_hasty : lrust_typing.
Global Hint Extern 0 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_just_hasty : lrust_typing.
Global Hint Extern 0 (resolve_tctx _ _ _ _) =>
  simple apply resolve_tctx_cons_just_blocked : lrust_typing.

Global Hint Resolve real_tctx_nil real_tctx_cons_blocked
  : lrust_typing.
(* We need [eapply] to use [real_tctx_cons] *)
Global Hint Extern 0 (real_tctx _ _ _ _) =>
    eapply real_tctx_cons : lrust_typing.

Global Hint Resolve tctx_extract_elt_here_copy | 1 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here_exact | 2 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here | 20 : lrust_typing.
(* We need [eapply] to use [tctx_extract_elt_further] *)
Global Hint Extern 50 (tctx_extract_elt _ _ _ _ _ _) =>
  eapply tctx_extract_elt_further : lrust_typing.

Global Hint Resolve tctx_extract_ctx_nil tctx_extract_ctx_elt
  tctx_extract_ctx_incl : lrust_typing.

Global Hint Resolve resolve_unblock_tctx_nil resolve_unblock_tctx_cons_resolve
  : lrust_typing.
Global Hint Resolve resolve_unblock_tctx_cons_keep | 20 : lrust_typing.

Global Hint Resolve unblock_tctx_nil unblock_tctx_cons_unblock
  unblock_tctx_cons_just_hasty unblock_tctx_cons_just_blocked : lrust_typing.

Global Hint Opaque resolve_tctx tctx_incl tctx_extract_elt tctx_extract_ctx
  resolve_unblock_tctx unblock_tctx : lrust_typing.
