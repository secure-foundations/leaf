From iris.algebra Require Import frac agree csum.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.deprecated.program_logic Require Import hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import assert proofmode notation adequacy.
From iris.heap_lang.lib Require Import par.
Set Default Proof Using "Type".

(** This is the introductory example from Ralf's PhD thesis.
The difference to [one_shot] is that [set] asserts to be called only once. *)

Unset Mangle Names.

Definition one_shot_example : val := λ: <>,
  let: "x" := ref NONE in (
  (* set *) (λ: "n",
    assert: CAS "x" NONE (SOME "n")),
  (* check  *) (λ: <>,
    let: "y" := !"x" in λ: <>,
      let: "y'" := !"x" in
      match: "y" with
        NONE => #()
      | SOME <> => assert: "y" = "y'"
      end)).

Definition one_shotR := csumR fracR (agreeR ZO).
Definition Pending (q : Qp) : one_shotR := Cinl q.
Definition Shot (n : Z) : one_shotR := Cinr (to_agree n).

Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.
Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.

Section proof.
Local Set Default Proof Using "Type*".
Context `{!heapGS Σ, !one_shotG Σ}.

Definition one_shot_inv (γ : gname) (l : loc) : iProp Σ :=
  (l ↦ NONEV ∗ own γ (Pending (1/2)%Qp) ∨
   ∃ n : Z, l ↦ SOMEV #n ∗ own γ (Shot n))%I.

Local Hint Extern 0 (environments.envs_entails _ (one_shot_inv _ _)) =>
  unfold one_shot_inv : core.

Lemma pending_split γ q :
  own γ (Pending q) ⊣⊢ own γ (Pending (q/2)) ∗ own γ (Pending (q/2)).
Proof.
  rewrite /Pending. rewrite -own_op -Cinl_op. rewrite frac_op Qp_div_2 //.
Qed.

Lemma pending_shoot γ n :
  own γ (Pending 1%Qp) ==∗ own γ (Shot n).
Proof.
  iIntros "Hγ". iMod (own_update with "Hγ") as "$"; last done.
  by apply cmra_update_exclusive with (y:=Shot n).
Qed.

Lemma wp_one_shot (Φ : val → iProp Σ) :
  (∀ (f1 f2 : val) (T : iProp Σ), T ∗
    □ (∀ n : Z, T -∗ WP f1 #n {{ w, True }}) ∗
    □ WP f2 #() {{ g, □ WP (of_val g) #() {{ _, True }} }} -∗ Φ (f1,f2)%V)
      (* FIXME: Once we depend on Coq 8.13, make WP notation use [v closed binder]
         so that we can add a type annotation at the [g] binder here. *)
  ⊢ WP one_shot_example #() {{ Φ }}.
Proof.
  iIntros "Hf /=". pose proof (nroot .@ "N") as N.
  wp_lam. wp_alloc l as "Hl".
  iMod (own_alloc (Pending 1%Qp)) as (γ) "Hγ"; first done.
  iDestruct (pending_split with "Hγ") as "[Hγ1 Hγ2]".
  iMod (inv_alloc N _ (one_shot_inv γ l) with "[Hl Hγ2]") as "#HN".
  { iNext. iLeft. by iFrame. }
  wp_pures. iModIntro. iApply ("Hf" $! _ _ (own γ (Pending (1/2)%Qp))).
  iSplitL; first done. iSplit.
  - iIntros (n) "!> Hγ1". wp_pures.
    iApply wp_assert. wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">[[Hl Hγ2]|H]"; last iDestruct "H" as (m) "[Hl Hγ']".
    + iDestruct (pending_split with "[$Hγ1 $Hγ2]") as "Hγ".
      iMod (pending_shoot _ n with "Hγ") as "Hγ".
      wp_cmpxchg_suc. iModIntro. iSplitL; last (wp_pures; by eauto).
      iNext; iRight; iExists n; by iFrame.
    + by iDestruct (own_valid_2 with "Hγ1 Hγ'") as %?.
  - iIntros "!> /=". wp_lam. wp_bind (! _)%E.
    iInv N as ">Hγ".
    iAssert (∃ v, l ↦ v ∗ (⌜v = NONEV⌝ ∗ own γ (Pending (1/2)%Qp) ∨
       ∃ n : Z, ⌜v = SOMEV #n⌝ ∗ own γ (Shot n)))%I with "[Hγ]" as "Hv".
    { iDestruct "Hγ" as "[[Hl Hγ]|Hl]"; last iDestruct "Hl" as (m) "[Hl Hγ]".
      + iExists NONEV. iFrame. eauto.
      + iExists (SOMEV #m). iFrame. eauto. }
    iDestruct "Hv" as (v) "[Hl Hv]". wp_load.
    iAssert (one_shot_inv γ l ∗ (⌜v = NONEV⌝ ∨ ∃ n : Z,
      ⌜v = SOMEV #n⌝ ∗ own γ (Shot n)))%I with "[Hl Hv]" as "[Hinv #Hv]".
    { iDestruct "Hv" as "[[% ?]|Hv]"; last iDestruct "Hv" as (m) "[% ?]"; subst.
      + Show. iSplit. iLeft; by iSplitL "Hl". eauto.
      + iSplit. iRight; iExists m; by iSplitL "Hl". eauto. }
    iSplitL "Hinv"; first by eauto.
    iModIntro. wp_pures. iIntros "!> !>". wp_lam. wp_bind (! _)%E.
    iInv N as "Hinv".
    iDestruct "Hv" as "[%|Hv]"; last iDestruct "Hv" as (m) "[% Hγ']"; subst.
    + iDestruct "Hinv" as "[[Hl >Hγ]|H]"; last iDestruct "H" as (m') "[Hl Hγ]";
      wp_load; iModIntro; (iSplitL "Hl Hγ"; first by eauto with iFrame);
      wp_pures; done.
    + iDestruct "Hinv" as "[[Hl >Hγ]|H]"; last iDestruct "H" as (m') "[Hl Hγ]".
      { by iDestruct (own_valid_2 with "Hγ Hγ'") as %?. }
      wp_load. Show.
      iDestruct (own_valid_2 with "Hγ Hγ'") as %?%to_agree_op_inv_L; subst.
      iModIntro. iSplitL "Hl Hγ"; first by eauto with iFrame.
      wp_pures. iApply wp_assert. wp_op. by case_bool_decide.
Qed.

Lemma ht_one_shot (Φ : val → iProp Σ) :
  ⊢ {{ True }} one_shot_example #()
    {{ ff, ∃ T, T ∗
      (∀ n : Z, {{ T }} Fst ff #n {{ _, True }}) ∗
      {{ True }} Snd ff #() {{ g, {{ True }} g #() {{ _, True }} }}
    }}.
Proof.
  iIntros "!> _". iApply wp_one_shot. iIntros (f1 f2 T) "(HT & #Hf1 & #Hf2)".
  iExists T. iFrame "HT". iSplit.
  - iIntros (n) "!> HT". wp_smart_apply "Hf1". done.
  - iIntros "!> _". wp_smart_apply (wp_wand with "Hf2"). by iIntros (v) "#? !> _".
Qed.
End proof.

(* Have a client with a closed proof. *)
Definition client : expr :=
  let: "ff" := one_shot_example #() in
  (Fst "ff" #5 ||| let: "check" := Snd "ff" #() in "check" #()).

Section client.
  Context `{!heapGS Σ, !one_shotG Σ, !spawnG Σ}.

  Lemma client_safe : ⊢ WP client {{ _, True }}.
  Proof using Type*.
    rewrite /client. wp_apply wp_one_shot. iIntros (f1 f2 T) "(HT & #Hf1 & #Hf2)".
    wp_let. wp_smart_apply (wp_par with "[HT]").
    - wp_smart_apply "Hf1". done.
    - wp_proj. wp_bind (f2 _)%E. iApply wp_wand; first by iExact "Hf2".
      iIntros (check) "Hcheck". wp_pures. iApply "Hcheck".
    - auto.
  Qed.
End client.

(** Put together all library functors. *)
Definition clientΣ : gFunctors := #[ heapΣ; one_shotΣ; spawnΣ ].
(** This lemma implicitly shows that these functors are enough to meet
all library assumptions. *)
Lemma client_adequate σ : adequate NotStuck client σ (λ _ _, True).
Proof. apply (heap_adequacy clientΣ)=> ?. iIntros "_". iApply client_safe. Qed.
