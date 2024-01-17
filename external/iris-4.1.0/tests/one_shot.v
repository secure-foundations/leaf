From iris.algebra Require Import excl agree csum.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.deprecated.program_logic Require Import hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import assert proofmode notation adequacy.
From iris.heap_lang.lib Require Import par.
From iris.prelude Require Import options.

(** This is the introductory example from the "Iris from the Ground Up" journal
paper. *)

Unset Mangle Names.

Definition one_shot_example : val := λ: <>,
  let: "x" := ref NONE in (
  (* tryset *) (λ: "n",
    CAS "x" NONE (SOME "n")),
  (* check  *) (λ: <>,
    let: "y" := !"x" in λ: <>,
    match: "y" with
      NONE => #()
    | SOME "n" =>
       match: !"x" with
         NONE => assert: #false
       | SOME "m" => assert: "n" = "m"
       end
    end)).

Definition one_shotR := csumR (exclR unitO) (agreeR ZO).
Definition Pending : one_shotR := Cinl (Excl ()).
Definition Shot (n : Z) : one_shotR := Cinr (to_agree n).

Class one_shotG Σ := { one_shot_inG : inG Σ one_shotR }.
Local Existing Instance one_shot_inG.

Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.

Section proof.
Local Set Default Proof Using "Type*".
Context `{!heapGS Σ, !one_shotG Σ}.

Definition one_shot_inv (γ : gname) (l : loc) : iProp Σ :=
  (l ↦ NONEV ∗ own γ Pending ∨ ∃ n : Z, l ↦ SOMEV #n ∗ own γ (Shot n))%I.

Lemma wp_one_shot (Φ : val → iProp Σ) :
  (∀ f1 f2 : val,
    (∀ n : Z, □ WP f1 #n {{ w, ⌜w = #true⌝ ∨ ⌜w = #false⌝ }}) ∗
    □ WP f2 #() {{ g, □ WP (of_val g) #() {{ _, True }} }} -∗ Φ (f1,f2)%V)
      (* FIXME: Once we depend on Coq 8.13, make WP notation use [v closed binder]
         so that we can add a type annotation at the [g] binder here. *)
  ⊢ WP one_shot_example #() {{ Φ }}.
Proof.
  iIntros "Hf /=". pose proof (nroot .@ "N") as N.
  wp_lam. wp_alloc l as "Hl".
  iMod (own_alloc Pending) as (γ) "Hγ"; first done.
  iMod (inv_alloc N _ (one_shot_inv γ l) with "[Hl Hγ]") as "#HN".
  { iNext. iLeft. by iSplitL "Hl". }
  wp_pures. iModIntro. iApply "Hf"; iSplit.
  - iIntros (n) "!>". wp_lam. wp_pures. wp_bind (CmpXchg _ _ _).
    iInv N as ">[[Hl Hγ]|H]"; last iDestruct "H" as (m) "[Hl Hγ]".
    + iMod (own_update with "Hγ") as "Hγ".
      { by apply cmra_update_exclusive with (y:=Shot n). }
      wp_cmpxchg_suc. iModIntro. iSplitL; last (wp_pures; by eauto).
      iNext; iRight; iExists n; by iFrame.
    + wp_cmpxchg_fail. iModIntro. iSplitL; last (wp_pures; by eauto).
      rewrite /one_shot_inv; eauto 10.
  - iIntros "!> /=". wp_lam. wp_bind (! _)%E.
    iInv N as ">Hγ".
    iAssert (∃ v, l ↦ v ∗ ((⌜v = NONEV⌝ ∗ own γ Pending) ∨
       ∃ n : Z, ⌜v = SOMEV #n⌝ ∗ own γ (Shot n)))%I with "[Hγ]" as "Hv".
    { iDestruct "Hγ" as "[[Hl Hγ]|Hl]"; last iDestruct "Hl" as (m) "[Hl Hγ]".
      + iExists NONEV. iFrame. eauto.
      + iExists (SOMEV #m). iFrame. eauto. }
    iDestruct "Hv" as (v) "[Hl Hv]". wp_load.
    iAssert (one_shot_inv γ l ∗ (⌜v = NONEV⌝ ∨ ∃ n : Z,
      ⌜v = SOMEV #n⌝ ∗ own γ (Shot n)))%I with "[Hl Hv]" as "[Hinv #Hv]".
    { iDestruct "Hv" as "[[% ?]|Hv]"; last iDestruct "Hv" as (m) "[% ?]"; subst.
      + Show. iSplit.
        * iLeft; by iSplitL "Hl".
        * eauto.
      + iSplit.
        * iRight; iExists m; by iSplitL "Hl".
        * eauto. }
    iSplitL "Hinv"; first by eauto.
    iModIntro. wp_pures. iIntros "!> !>". wp_lam.
    iDestruct "Hv" as "[%|Hv]"; last iDestruct "Hv" as (m) "[% Hγ']";
      subst; wp_match; [done|].
    wp_bind (! _)%E.
    iInv N as "[[Hl >Hγ]|H]"; last iDestruct "H" as (m') "[Hl Hγ]".
    { by iCombine "Hγ Hγ'" gives %?. }
    wp_load. Show.
    iCombine "Hγ Hγ'" gives %?%to_agree_op_inv_L; subst.
    iModIntro. iSplitL "Hl".
    { iNext; iRight; by eauto. }
    wp_smart_apply wp_assert. wp_pures. by case_bool_decide.
Qed.

Lemma ht_one_shot (Φ : val → iProp Σ) :
  ⊢ {{ True }} one_shot_example #()
    {{ ff,
      (∀ n : Z, {{ True }} Fst ff #n {{ w, ⌜w = #true⌝ ∨ ⌜w = #false⌝ }}) ∗
      {{ True }} Snd ff #() {{ g, {{ True }} g #() {{ _, True }} }}
    }}.
Proof.
  iIntros "!> _". iApply wp_one_shot. iIntros (f1 f2) "[#Hf1 #Hf2]"; iSplit.
  - iIntros (n) "!> _". wp_smart_apply "Hf1".
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
    rewrite /client. wp_apply wp_one_shot. iIntros (f1 f2) "[#Hf1 #Hf2]".
    wp_let. wp_smart_apply wp_par.
    - wp_smart_apply "Hf1".
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

(* Since we check the output of the test files, this means
our test suite will fail if we ever accidentally add an axiom
to anything used by this proof. *)
Print Assumptions client_adequate.
