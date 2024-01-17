From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants ghost_var.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** * This file showcases the basic usage of later credits. *)
(** The examples are taken from the later credits paper at ICFP'22,
      "Later Credits: Resourceful Reasoning for the Later Modality",
   available at <https://plv.mpi-sws.org/later-credits/>. *)

(** Overview of important connectives, tactics, and lemmas for later credits:
  - the resource [£ n] denotes ownership of n later credits, i.e., the right to
    eliminate [n] laters at a fancy update,

  - the lemma [lc_fupd_elim_later] allows to strip a later off a hypothesis ["H"]
    using a credit ["Hcred" : £ 1], assuming that the goal is a fancy update.
    Example usage: [iMod (lc_fupd_elim_later with "Hcred H") as "H".]

  - the lemma [lc_fupd_add_later] allows to add a later in front of the goal,
    if the current goal is a fancy update, using one credit ["Hcred" : £ 1].
    The later can subsequently be introduced with [iNext] to strip laters off
    multiple hypotheses.
    Example usage: [iApply (lc_fupd_add_later with "Hcred").]

  - the lemma [lc_split] shows that [£ (n + m) ⊣⊢ £ n ∗ £ m], i.e., later credits
    compose via addition. This is also automatically applied by [iSplit] and
    [iDestruct].

  - the HeapLang-specific [wp_pure cred:"Hcred"] tactic takes a single pure step
    (just like [wp_pure]) and generates a new hypothesis ["Hcred" : £ 1]
    asserting ownership of a single later credit that can subsequently be used
    with the lemmas described above. *)

(** This is the small example from the end of Section 2 (page 9) of the paper.
  Using later credits in this example is not strictly necessary, but it
  demonstrates how they can be used. *)
Lemma mini_later_credits_example `{!heapGS Σ} N (f : val) l :
  (** Assume we have some specification for f... *)
  (∀ v, ⊢ {{{ ∃ n: nat, ⌜v = LitV n⌝}}} f v {{{ (n' : nat), RET #n'; True }}}) →
  (** ... and an invariant managing [l] *)
  inv N (∃ n : nat, l ↦ LitV n) -∗
  (** Our program stores the result of calling [f] to [l]. *)
  {{{ True }}} #l <- f (#41 + #1) {{{ v, RET v; True }}}.
Proof.
  (** We will use a later credit to strip the later we get over the
     contents of the invariant when opening it. This is not strictly
     necessary (timelessness would also work here), but it is
     nevertheless instructive. *)

  iIntros (Hs) "#Hpre". iIntros (Φ) "!> _ Hpost".
  wp_bind (_ + _)%E.
  (** We generate a later credit ["Hcred" : £ 1] from executing a pure step.
     [wp_pure credit:"Hcred"] behaves like [wp_pure] in executing a pure step,
     but additionally provides a new hypothesis ["Hcred" : £ 1].
     [£ 1] denotes ownership of the right to eliminate one later. *)
  wp_pure credit:"Hcred".

  (** We now use the specification for [f]. *)
  wp_bind (f _). iApply Hs.
  { iExists 42. done. }
  iNext. iIntros (n') "_".
  (** Now we open the invariant... *)
  iInv "Hpre" as "Hl".
  (** and get [Hl : ▷ (∃ n : nat, l ↦ #n)]. *)

  (** We can use the later credit we just obtained to eliminate the later.
     Later credits can be used to eliminate laters at fancy updates, in general
     away from a weakest precondition.
     [lc_fupd_elim_later] can be used to transform a hypothesis [▷ P] to [P]
     using one credit [£1]. *)
  iMod (lc_fupd_elim_later with "Hcred Hl") as "Hl".
  iDestruct "Hl" as "(%n & Hl)".
  (** now we can execute the store using the [l ↦ _]. *)
  wp_store. iModIntro.
  iSplitL "Hl". { eauto with iFrame. }
  by iApply "Hpost".
Qed.

(** Now for a slightly more complicated example involving nested invariants.
  This is an instance of the example outlined in the introduction (page 4) of the paper.

  Of course, we again consider a very simple proof that might appear toyish, but with
  challenges that might well appear as part of much more complicated proof setups. *)
Lemma nested_invariants_example `{!heapGS Σ} `{!ghost_varG Σ loc} γ (l : loc) :
  (** Assume that the location [l] is managed through another indirection with a ghost variable [γ],
     a situation you might well encounter as part of more complicated proof setups.
     The ownership of the location [l] itself is kept inside a nested invariant. *)
  inv (nroot .@ "1") (∃ l : loc, inv (nroot .@ "2") (∃ n : nat, l ↦ #n) ∗ ghost_var γ (1/2) l) -∗
  (** One half of [γ] is kept outside the invariant to keep knowledge about the location [l].
     We also assume to get one later credit, perhaps from a preceding pure step or from a
     totally different part of the program. *)
  {{{ ghost_var γ (1/2) l ∗ £ 1 }}} #l <- #42 {{{ v, RET v; True }}}.
Proof.
  iIntros "#Hinv". iIntros (Φ) "!> (Hv & Hcred) Hpost".
  (** We open the outer invariant... *)
  iInv "Hinv" as "(%l' & #Hinv' & >Hv')".
  (** and use timelessness to strip the later over ["Hv'"].
     But we cannot do the same for ["Hinv'"], the knowledge about the nested invariant, because
     it is not timeless. And we also cannot take any program step to strip the later here! *)
  iCombine "Hv Hv'" gives %[_ <-].
  (** Instead, we use the later credit to strip the later in front of the invariant.
    Here we make use of [lc_fupd_add_later], which adds a later to the goal using one credit,
    if the current goal is a fancy update. *)
  iApply fupd_wp. iApply (lc_fupd_add_later with "Hcred").
  (** We can use this to strip laters off multiple hypotheses now. *)
  iIntros "!>!>".
  (** Now we are ready to open the nested invariant! *)
  iInv "Hinv'" as "(%n & >Hl)".
  (** And finally we can take a program step. *)
  wp_store. iModIntro.
  iSplitL "Hl". { iNext. iExists 42. done. }
  iModIntro. iSplitL "Hv'". { iNext. eauto with iFrame. }
  by iApply "Hpost".
Qed.
