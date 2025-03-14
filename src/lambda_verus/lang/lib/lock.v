From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From lrust.lang Require Import lang proofmode notation.
Set Default Proof Using "Type".

Definition mklock_unlocked : val := λ: ["l"], "l" <- #false.
Definition mklock_locked : val := λ: ["l"], "l" <- #true.
Definition try_acquire : val := λ: ["l"], CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" ["l"] := if: try_acquire ["l"] then #☠ else "acquire" ["l"].
Definition release : val := λ: ["l"], "l" <-ˢᶜ #false.

(* It turns out that we need an accessor-based spec so that we can put the
   protocol into shared borrows.  Cancellable invariants don't work because
   their cancelling view shift has a non-empty mask, and it would have to be
   executed in the consequence view shift of a borrow. *)
Section proof.
  Context `{!lrustGS Σ}.

  Definition lock_proto (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else R)%I.

  Global Instance lock_proto_ne l : NonExpansive (lock_proto l).
  Proof. solve_proper. Qed.
  Global Instance lock_proto_proper l : Proper ((≡) ==> (≡)) (lock_proto l).
  Proof. apply ne_proper, _. Qed.

  Lemma lock_proto_iff l R R' :
    □ (R ↔ R') -∗ lock_proto l R -∗ lock_proto l R'.
  Proof.
    iIntros "#HRR' Hlck". iDestruct "Hlck" as (b) "[Hl HR]". iExists b.
    iFrame "Hl". destruct b; first done. by iApply "HRR'".
  Qed.

  Lemma lock_proto_iff_proper l R R' :
    □ (R ↔ R') -∗ □ (lock_proto l R ↔ lock_proto l R').
  Proof.
    iIntros "#HR !>". iSplit; iIntros "Hlck"; iApply (lock_proto_iff with "[HR] Hlck").
    - done.
    - iModIntro; iSplit; iIntros; by iApply "HR".
  Qed.

  (** The main proofs. *)
  Lemma lock_proto_create (R : iProp Σ) l (b : bool) :
    l ↦ #b -∗ (if b then True else ▷ R) ==∗ ▷ lock_proto l R.
  Proof.
    iIntros "Hl HR". iExists _. iFrame "Hl". destruct b; first done. by iFrame.
  Qed.

  Lemma lock_proto_destroy l R :
    lock_proto l R -∗ ∃ (b : bool), l ↦ #b ∗ if b then True else R.
  Proof.
    iIntros "Hlck". iDestruct "Hlck" as (b) "[Hl HR]". auto with iFrame.
  Qed.

  Lemma mklock_unlocked_spec (R : iProp Σ) (l : loc) v :
    {{{ l ↦ v ∗ ▷ R }}} mklock_unlocked [ #l ] {{{ RET #☠; ▷ lock_proto l R }}}.
  Proof.
    iIntros (Φ) "[Hl HR] HΦ". wp_lam. rewrite -wp_fupd. wp_write.
    iMod (lock_proto_create with "Hl HR") as "Hproto".
    iApply "HΦ". by iFrame.
  Qed.

  Lemma mklock_locked_spec (R : iProp Σ) (l : loc) v :
    {{{ l ↦ v }}} mklock_locked [ #l ] {{{ RET #☠; ▷ lock_proto l R }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_lam. rewrite -wp_fupd. wp_write.
    iMod (lock_proto_create with "Hl [//]") as "Hproto".
    iApply "HΦ". by iFrame.
  Qed.

  (* At this point, it'd be really nice to have some sugar for symmetric
     accessors. *)
  Lemma try_acquire_spec E l R P :
    □ (P ={E,∅}=∗ ▷ lock_proto l R ∗ (▷ lock_proto l R ={∅,E}=∗ P)) -∗
    {{{ P }}} try_acquire [ #l ] @ E
    {{{ b, RET #b; (if b is true then R else True) ∗ P }}}.
  Proof.
    iIntros "#Hproto !> * HP HΦ".
    wp_rec. iMod ("Hproto" with "HP") as "(Hinv & Hclose)".
    iDestruct "Hinv" as ([]) "[Hl HR]".
    - wp_apply (wp_cas_int_fail with "Hl"); [done..|]. iIntros "Hl".
      iMod ("Hclose" with "[Hl]"); first (iExists true; by eauto).
      iModIntro. iApply ("HΦ" $! false). auto.
    - wp_apply (wp_cas_int_suc with "Hl"); [done..|]. iIntros "Hl".
      iMod ("Hclose" with "[Hl]") as "HP"; first (iExists true; by eauto).
      iModIntro. iApply ("HΦ" $! true); iFrame.
  Qed.

  Lemma acquire_spec E l R P :
    □ (P ={E,∅}=∗ ▷ lock_proto l R ∗ (▷ lock_proto l R ={∅,E}=∗ P)) -∗
    {{{ P }}} acquire [ #l ] @ E {{{ RET #☠; R ∗ P }}}.
  Proof.
    iIntros "#Hproto !> * HP HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hproto HP"). iIntros ([]).
    - iIntros "[HR Hown]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "[_ Hown]". wp_if. iApply ("IH" with "Hown HΦ").
  Qed.

  Lemma release_spec E l R P :
    □ (P ={E,∅}=∗ ▷ lock_proto l R ∗ (▷ lock_proto l R ={∅,E}=∗ P)) -∗
    {{{ R ∗ P }}} release [ #l ] @ E {{{ RET #☠; P }}}.
  Proof.
    iIntros "#Hproto !> * (HR & HP) HΦ". wp_let.
    iMod ("Hproto" with "HP") as "(Hinv & Hclose)".
    iDestruct "Hinv" as (b) "[? _]". wp_write. iApply "HΦ".
    iApply "Hclose". iExists false. by iFrame.
  Qed.
End proof.

Global Typeclasses Opaque lock_proto.
