From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.rwlock Require Import rwlock.
Set Default Proof Using "Type".

Section rwlockreadguard.
  Context `{!typeG Σ, !rwlockG Σ}.

  (* Original Rust type:
    pub struct RwLockReadGuard<'a, T: ?Sized + 'a> {
        __lock: &'a RwLock<T>,
    }
  *)

  Program Definition rwlockreadguard (α : lft) (ty : type) :=
    {| ty_size := 1;
       ty_lfts := α :: ty.(ty_lfts); ty_E := ty.(ty_E) ++ ty_outlives_E ty α;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           ∃ ν q γ β tid_own, ty.(ty_shr) (α ⊓ ν) tid (l +ₗ 1) ∗
             α ⊑ β ∗ &at{β,rwlockN}(rwlock_inv tid_own tid l γ β ty) ∗
             q.[ν] ∗ own γ (◯ reading_st q ν) ∗
             (1.[ν] ={↑lftN ∪ ↑lft_userN}[↑lft_userN]▷=∗ [†ν])
         | _ => False
         end;
       ty_shr κ tid l :=
         ∃ (l' : loc),
           &frac{κ} (λ q, l↦∗{q} [ #l']) ∗
           ▷ ty.(ty_shr) (α ⊓ κ) tid (l' +ₗ 1) |}%I.
  Next Obligation. intros α ty tid [|[[]|] []]; auto. Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q ?) "#LFT #Hl Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]". done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦". done.
    destruct vl as [|[[|l'|]|][]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (ν) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (q') "Hb". done.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (tid_own) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[Hshr Hb]". done.
    iMod (bor_persistent with "LFT Hshr Htok") as "[#Hshr Htok]". done.
    iMod (bor_sep with "LFT Hb") as "[Hαβ Hb]". done.
    iMod (bor_persistent with "LFT Hαβ Htok") as "[#Hαβ Htok]". done.
    iMod (bor_sep with "LFT Hb") as "[Hinv Hb]". done.
    iMod (bor_persistent with "LFT Hinv Htok") as "[#Hinv $]". done.
    iMod (bor_sep with "LFT Hb") as "[Hκν _]". done.
    iDestruct (frac_bor_lft_incl with "LFT [> Hκν]") as "#Hκν".
    { iApply bor_fracture; try done. by rewrite Qp_mul_1_r. }
    iExists _. iFrame "#". iApply ty_shr_mono; last done.
    iApply lft_intersect_mono; last done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (α ty κ κ' tid l) "#Hκ'κ H". iDestruct "H" as (l') "[#Hf #Hshr]".
    iExists l'. iSplit; first by iApply frac_bor_shorten.
    iApply ty_shr_mono; last done. iApply lft_intersect_mono; last done.
    iApply lft_incl_refl.
  Qed.

  Global Instance rwlockreadguard_type_contractive α : TypeContractive (rwlockreadguard α).
  Proof.
    split.
    - apply (type_lft_morphism_add _ α [α] []) => ?.
      + iApply lft_equiv_refl.
      + by rewrite elctx_interp_app elctx_interp_ty_outlives_E
                   /elctx_interp /= left_id right_id.
    - done.
    - intros n ty1 ty2 Hsz Hl HE Ho Hs tid [|[[]|][]]=>//=. unfold rwlock_inv.
      repeat (apply Hs || apply dist_S, Hs || apply dist_S, Ho ||
              f_contractive || f_equiv).
    - intros n ty1 ty2 Hsz Hl HE Ho Hs κ tid l. simpl. by setoid_rewrite Hs.
  Qed.

  Global Instance rwlockreadguard_ne α : NonExpansive (rwlockreadguard α).
  Proof.
    unfold rwlockreadguard, rwlock_inv. intros n ty1 ty2 Hty12.
    split=>//=; try by rewrite Hty12.
    - intros tid [|[[]|][]]=>//=. repeat (apply Hty12 || f_equiv).
    - intros κ tid l. repeat (apply Hty12 || f_equiv).
  Qed.

  (* The rust type is not covariant, although it probably could (cf. refcell).
     This would require changing the definition of the type, though. *)
  Global Instance rwlockreadguard_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) rwlockreadguard.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty q) "HL".
    iDestruct (proj1 Hty with "HL") as "#Hty". iDestruct (Hα with "HL") as "#Hα".
    iDestruct (rwlock_inv_proper with "HL") as "#Hty1ty2"; first done.
    iDestruct (rwlock_inv_proper with "HL") as "#Hty2ty1"; first by symmetry.
    iIntros "!> #HE". iDestruct ("Hα" with "HE") as "Hα1α2".
    iDestruct ("Hty" with "HE") as "(%&#?&#Ho&#Hs)".
    iSplit; [done|iSplit; [|iSplit; iModIntro]].
    - by iApply lft_intersect_mono.
    - iIntros (tid [|[[]|][]]) "H"; try done.
      iDestruct "H" as (ν q' γ β tid_own) "(#Hshr & #H⊑ & #Hinv & Htok & Hown)".
      iExists ν, q', γ, β, tid_own. iFrame "∗#". iSplit; last iSplit.
      + iApply ty_shr_mono; last by iApply "Hs".
        iApply lft_intersect_mono. done. iApply lft_incl_refl.
      + by iApply lft_incl_trans.
      + iApply (at_bor_iff with "[] Hinv").
        iIntros "!> !>"; iSplit; iIntros "H". by iApply "Hty1ty2". by iApply "Hty2ty1".
    - iIntros (κ tid l) "H". iDestruct "H" as (l') "[Hf Hshr]". iExists l'.
      iFrame. iApply ty_shr_mono; last by iApply "Hs".
      iApply lft_intersect_mono. done. iApply lft_incl_refl.
  Qed.
  Global Instance rwlockreadguard_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L))
           rwlockreadguard.
  Proof. intros ??????. by apply rwlockreadguard_mono. Qed.
  Lemma rwlockreadguard_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    subtype E L (rwlockreadguard α1 ty1) (rwlockreadguard α2 ty2).
  Proof. intros. by eapply rwlockreadguard_mono. Qed.
  Global Instance rwlockreadguard_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) rwlockreadguard.
  Proof. intros ??[]?? EQ. split; apply rwlockreadguard_mono'; try done; apply EQ. Qed.
  Lemma rwlockreadguard_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (rwlockreadguard α1 ty1) (rwlockreadguard α2 ty2).
  Proof. intros. by eapply rwlockreadguard_proper. Qed.

  (* Rust requires the type to also be Send.  Not sure why. *)
  Global Instance rwlockreadguard_sync α ty :
    Sync ty → Sync (rwlockreadguard α ty).
  Proof.
    move=>?????/=. apply bi.exist_mono=>?. by rewrite sync_change_tid.
  Qed.

  (* POSIX requires the unlock to occur from the thread that acquired
     the lock, so Rust does not implement Send for RwLockWriteGuard. We can
     prove this for our spinlock implementation, however. *)
  Global Instance rwlockreadguard_send α ty :
    Sync ty → Send (rwlockreadguard α ty).
  Proof.
    iIntros (??? [|[[]|][]]) "H"; try done. simpl. iRevert "H".
    iApply bi.exist_mono. iIntros (κ); simpl. apply bi.equiv_spec.
    repeat lazymatch goal with
           | |- (ty_shr _ _ _ _) ≡ (ty_shr _ _ _ _) => by apply sync_change_tid'
           | |- (rwlock_inv _ _ _ _ _ _) ≡ _ => by apply rwlock_inv_change_tid_shr
           | |- _ => f_equiv
           end.
  Qed.
End rwlockreadguard.

Global Hint Resolve rwlockreadguard_mono' rwlockreadguard_proper' : lrust_typing.
