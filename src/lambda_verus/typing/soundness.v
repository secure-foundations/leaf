From iris.algebra Require Import frac.
From iris.base_logic.lib Require Import na_invariants.
From iris.proofmode Require Import proofmode.
From lrust.lang Require Import races adequacy proofmode notation.
From lrust.lifetime Require Import lifetime frac_borrow.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Class typePreG Σ := PreTypeG {
  type_preG_lrustGS :> lrustGpreS Σ;
  type_preG_lftGS :> lftGpreS Σ;
  type_preG_na_invG :> na_invG Σ;
  type_preG_frac_borG :> frac_borG Σ;
  type_preG_prophG:> prophPreG Σ;
  type_preG_uniqG:> uniqPreG Σ;
}.

Definition typeΣ : gFunctors :=
  #[lrustΣ; lftΣ; na_invΣ;
    GFunctor (constRF fracR); uniqΣ; prophΣ].
Global Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Section type_soundness.
  Definition exit_cont : val := λ: [<>], #☠.

  Definition main_type `{!typeG Σ} := (fn(∅) → unit_ty)%T.

  Definition main_transformer : predl_trans'ₛ [] () := (λ post '-[], post ()).

  (* Intuitively, it says that execution of a closed, semantically well-typed
    program, without any special precondition, does not get stuck *)
  Theorem type_soundness `{!typePreG Σ} (main : val) σ t :
    (∀ `{!typeG Σ}, typed_val main main_type main_transformer) →
    rtc erased_step ([main [exit_cont]%E], ∅) (t, σ) →
    nonracing_threadpool t σ ∧
    (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
  Proof.
    intros Hmain Hrtc.
    cut (adequate NotStuck (main [exit_cont]%E) ∅ (λ _ _, True)).
    { split. by eapply adequate_nonracing.
      intros. by eapply (adequate_not_stuck _ (main [exit_cont]%E)). }
    apply: lrust_adequacy=>?. iIntros "#TIME".
    iMod lft_init as (?) "#LFT". done.
    iMod na_alloc as (tid) "Htl".
    iMod proph_init as (?) "#PROPH". done.
    iMod uniq_init as (?) "#UNIQ". done. set (Htype := TypeG _ _ _ _ _ _ _).
    wp_bind (of_val main). iApply (wp_wand with "[Htl]").
    iApply (Hmain Htype [] [] tid (λ _ '-[vπ], vπ (const True) -[]) -[]
      with "LFT TIME PROPH UNIQ [] Htl [] [$]").
    { by rewrite /elctx_interp. }
    { by rewrite /llctx_interp big_sepL_nil. }
    { by iApply proph_obs_true. }
    clear Hrtc Hmain main. iIntros (main) "Hmain".
    iDestruct "Hmain" as ([vπ []]) "/= (Htl & ? & [Hmain _] & ?)".
    iDestruct "Hmain" as (??) "(EQ & ? & Hmain)". rewrite eval_path_of_val.
    iDestruct "EQ" as %[= <-]. iDestruct "Hmain" as (?) "/= (-> & Hmain)".
    iDestruct "Hmain" as (f k _ e ?) "(EQ & Hmain)". iDestruct "EQ" as %[= ->].
    wp_rec.
    iMod (lft_create with "LFT") as (ϝ) "Hϝ"; first done.
    iApply ("Hmain" $! () ϝ exit_cont -[] tid -[] (λ π _, True) with "LFT TIME PROPH UNIQ [] Htl [Hϝ] [] [$] [$]").
    { by rewrite /elctx_interp /=. }
    { rewrite /llctx_interp /=. iSplit; last done. iExists ϝ. iFrame. by rewrite /= left_id. }
    rewrite cctx_interp_singleton. simpl. iIntros (args [? []]) "_ _".
    inv_vec args. iIntros (x) "_ /= ?". by wp_lam.
  Qed.
End type_soundness.

(* Soundness theorem when no other CMRA is needed. *)

Theorem type_soundness_closed (main : val) σ t :
  (∀ `{!typeG typeΣ}, typed_val main main_type main_transformer) →
  rtc erased_step ([main [exit_cont]%E], ∅) (t, σ) →
  nonracing_threadpool t σ ∧
  (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
Proof.
  intros. eapply @type_soundness; try done. apply _.
Qed.
