From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From iris.bi Require Import fractional.
From iris.algebra Require Import excl csum frac auth numbers.
From lrust.lang Require Import lang proofmode notation new_delete.
From iris.prelude Require Import options.

(* JH: while working on Arc, I think figured that the "weak count
locking" mechanism that Rust is using and that is verified below may
not be necessary.

Instead, what can be done in get_mut is the following:
  - First, do a CAS on the strong count to put it to 0 from the expected
value 1. This has the effect, at the same time, of ensuring that no one
else has a strong reference, and of forbidding other weak references to
be upgraded (since the strong count is now at 0). If the CAS fail,
simply return None.
  - Second, check the weak count. If it is at 1, then we are sure that
we are the only owner.
  - Third, in any case write 1 in the strong count to cancel the CAS.

What's wrong with this protocol? The "only" problem I can see is that if
someone tries to upgrade a weak after we did the CAS, then this will
fail even though this could be possible.

RJ: Upgrade failing spuriously sounds like a problem severe enough to
justify the locking protocol.
*)

Definition strong_count : val :=
  λ: ["l"], !ˢᶜ"l".

Definition weak_count : val :=
  λ: ["l"], !ˢᶜ("l" +ₗ #1).

Definition clone_arc : val :=
  rec: "clone" ["l"] :=
    let: "strong" := !ˢᶜ"l" in
    if: CAS "l" "strong" ("strong" + #1) then #☠ else "clone" ["l"].

Definition clone_weak : val :=
  rec: "clone" ["l"] :=
    let: "weak" := !ˢᶜ("l" +ₗ #1) in
    if: CAS ("l" +ₗ #1) "weak" ("weak" + #1) then #☠ else "clone" ["l"].

Definition downgrade : val :=
  rec: "downgrade" ["l"] :=
    let: "weak" := !ˢᶜ("l" +ₗ #1) in
    if: "weak" = #(-1) then
      (* -1 in weak indicates that somebody locked the counts; let's spin. *)
      "downgrade" ["l"]
    else
      if: CAS ("l" +ₗ #1) "weak" ("weak" + #1) then #☠
      else "downgrade" ["l"].

Definition upgrade : val :=
  rec: "upgrade" ["l"] :=
    let: "strong" := !ˢᶜ"l" in
    if: "strong" = #0 then #false
    else
      if: CAS "l" "strong" ("strong" + #1) then #true
      else "upgrade" ["l"].

Definition drop_weak : val :=
  rec: "drop" ["l"] :=
    (* This can ignore the lock because the lock is only held when there
       are no other weak refs in existence, so this code will never be called
       with the lock held. *)
    let: "weak" := !ˢᶜ("l" +ₗ #1) in
    if: CAS ("l" +ₗ #1) "weak" ("weak" - #1) then "weak" = #1
    else "drop" ["l"].

Definition drop_arc : val :=
  rec: "drop" ["l"] :=
    let: "strong" := !ˢᶜ"l" in
    if: CAS "l" "strong" ("strong" - #1) then "strong" = #1
    else "drop" ["l"].

Definition try_unwrap : val :=
  λ: ["l"], CAS "l" #1 #0.

Definition is_unique : val :=
  λ: ["l"],
    (* Try to acquire the lock for the last ref by CASing weak count from 1 to -1. *)
    if: CAS ("l" +ₗ #1) #1 #(-1) then
      let: "strong" := !ˢᶜ"l" in
      let: "unique" := "strong" = #1 in
      "l" +ₗ #1 <-ˢᶜ #1;;
      "unique"
    else
      #false.

Definition try_unwrap_full : val :=
  λ: ["l"],
    if: CAS "l" #1 #0 then
      if: !ˢᶜ("l" +ₗ #1) = #1 then "l" <- #1;; #0
      else #1
    else #2.

(** The CMRA we need. *)
(* Not bundling heapGS, as it may be shared with other users. *)

(* See rc.v for understanding the structure of this CMRA.
   The only additional thing is the [optionR (exclR unitO))], used to handle
   properly the locking mechanisme for the weak count. *)
Definition arc_stR :=
  prodUR (optionUR (csumR (prodR (prodR fracR positiveR) (optionR (exclR unitO)))
                          (exclR unitO))) natUR.
Class arcG Σ :=
  RcG :> inG Σ (authR arc_stR).
Definition arcΣ : gFunctors := #[GFunctor (authR arc_stR)].
Global Instance subG_arcΣ {Σ} : subG arcΣ Σ → arcG Σ.
Proof. solve_inG. Qed.

Section def.
  Context `{!lrustGS Σ, !arcG Σ} (P1 : Qp → iProp Σ) (P2 : iProp Σ) (N : namespace).

  Definition arc_tok γ q : iProp Σ :=
    own γ (◯ (Some $ Cinl (q, 1%positive, None), 0%nat)).
  Definition weak_tok γ : iProp Σ :=
    own γ (◯ (None, 1%nat)).

  Global Instance arc_tok_timeless γ q : Timeless (arc_tok γ q) := _.
  Global Instance weak_tok_timeless γ : Timeless (weak_tok γ) := _.

  Definition arc_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ st : arc_stR, own γ (● st) ∗
      match st with
      | (Some (Cinl (q, strong, wlock)), weak) =>
         ∃ q', ⌜(q + q')%Qp = 1%Qp⌝ ∗ P1 q' ∗ l ↦ #(Zpos strong) ∗
           if wlock then (l +ₗ 1) ↦ #(-1) ∗ ⌜weak = 0%nat⌝
           else (l +ₗ 1) ↦ #(S weak)
      | (Some (Cinr _), weak) =>
        l ↦ #0 ∗ (l +ₗ 1) ↦ #(S weak)
      | (None, (S _) as weak) =>
        l ↦ #0 ∗ (l +ₗ 1) ↦ #weak ∗ P2
      | _ => True
      end)%I.

  Definition is_arc (γ : gname) (l : loc) : iProp Σ :=
    inv N (arc_inv γ l).

  Global Instance is_arc_persistent γ l : Persistent (is_arc γ l) := _.

  Definition arc_tok_acc (γ : gname) P E : iProp Σ :=
    (□ (P ={E,∅}=∗ ∃ q, arc_tok γ q ∗ (arc_tok γ q ={∅,E}=∗ P)))%I.

  Definition weak_tok_acc (γ : gname) P E : iProp Σ :=
    (□ (P ={E,∅}=∗ weak_tok γ ∗ (weak_tok γ ={∅,E}=∗ P)))%I.

  Definition drop_spec (drop : val) P : iProp Σ :=
    ({{{ P ∗ P1 1 }}} drop [] {{{ RET #☠; P ∗ P2 }}})%I.
End def.

Section arc.
  (* P1 is the thing that is shared by strong reference owners (in practice,
     this is the lifetime token), and P2 is the thing that is owned by the
     protocol when only weak references are left (in practice, P2 is the
     ownership of the underlying memory incl. deallocation). *)
  Context `{!lrustGS Σ, !arcG Σ} (P1 : Qp → iProp Σ) {HP1:Fractional P1}
          (P2 : iProp Σ) (N : namespace).

  Local Instance P1_AsFractional q : AsFractional (P1 q) P1 q.
  Proof using HP1. done. Qed.

  Global Instance arc_inv_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n ==> eq ==> eq ==> dist n)
           arc_inv.
  Proof. solve_proper. Qed.
  Global Instance arc_inv_proper :
    Proper (pointwise_relation _ (≡) ==> (≡) ==> eq ==> eq ==> (≡))
           arc_inv.
  Proof. solve_proper. Qed.

  Global Instance is_arc_contractive n :
    Proper (pointwise_relation _ (dist_later n) ==> dist_later n ==> eq ==> eq ==> eq ==> dist n)
           is_arc.
  Proof. solve_contractive. Qed.
  Global Instance is_arc_proper :
    Proper (pointwise_relation _ (≡) ==> (≡) ==> eq ==> eq ==> eq ==> (≡)) is_arc.
  Proof. solve_proper. Qed.

  Lemma create_arc E l :
    l ↦ #1 -∗ (l +ₗ 1) ↦ #1 -∗ P1 1%Qp ={E}=∗
      ∃ γ q, is_arc P1 P2 N γ l ∗ P1 q ∗ arc_tok γ q.
  Proof using HP1.
    iIntros "Hl1 Hl2 [HP1 HP1']".
    iMod (own_alloc ((● (Some $ Cinl ((1/2)%Qp, xH, None), O) ⋅
                      ◯ (Some $ Cinl ((1/2)%Qp, xH, None), O))))
      as (γ) "[H● H◯]"; first by apply auth_both_valid_discrete.
    iExists _, _. iFrame. iApply inv_alloc. iExists _. iFrame. iExists _. iFrame.
    rewrite Qp_div_2. auto.
  Qed.

  Lemma create_weak E l :
    l ↦ #0 -∗ (l +ₗ 1) ↦ #1 -∗ P2 ={E}=∗ ∃ γ, is_arc P1 P2 N γ l ∗ weak_tok γ.
  Proof.
    iIntros "Hl1 Hl2 HP2".
    iMod (own_alloc ((● (None, 1%nat) ⋅ ◯ (None, 1%nat)))) as (γ) "[H● H◯]";
      first by apply auth_both_valid_discrete.
    iExists _. iFrame. iApply inv_alloc. iExists _. iFrame.
  Qed.

  Lemma arc_tok_auth_val st γ q :
    own γ (● st) -∗ arc_tok γ q -∗
    ⌜∃ q' strong wlock weak, st = (Some $ Cinl (q', strong, wlock), weak) ∧
                             if decide (strong = xH) then q = q' ∧ wlock = None
                             else ∃ q'', q' = (q + q'')%Qp⌝.
  Proof.
    iIntros "H● Htok". iDestruct (own_valid_2 with "H● Htok") as
        %[[Hincl%option_included _]%prod_included [Hval _]]%auth_both_valid_discrete.
    destruct st, Hincl as [[=]|(?&?&[= <-]&?&[Hincl|Hincl%csum_included])];
      simpl in *; subst.
    - setoid_subst. iExists _, _, _, _. by iSplit.
    - destruct Hincl as [->|[(?&[[??]?]&[=<-]&->&[[[??]%frac_included%Qp_lt_sum
        ?%pos_included]%prod_included _]%prod_included)|(?&?&[=]&?)]]; first done.
      iExists _, _, _, _. iSplit=>//. simpl in *. destruct decide; [subst;lia|eauto].
  Qed.

  Lemma strong_count_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc P1 P2 N γ l -∗ arc_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} strong_count [ #l] {{{ (c : nat), RET #c; P ∗ ⌜(c > 0)%nat⌝ }}}.
  Proof using HP1.
    iIntros "#INV #Hacc !> * HP HΦ". iLöb as "IH". wp_rec.
    iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(?& strong &?&?&[-> _]).
    iDestruct "H" as (?) "(Hq & HP1 & H↦ & Hw)". wp_read.
    iMod ("Hclose2" with "Hown") as "HP". iModIntro.
    iMod ("Hclose1" with "[-HP HΦ]") as "_"; [iExists _; auto with iFrame|].
    iModIntro. rewrite -positive_nat_Z. iApply "HΦ". auto with iFrame lia.
  Qed.

  (* FIXME : in the case the weak count is locked, we can possibly
     return -1. This problem already exists in Rust. *)
  Lemma weak_count_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc P1 P2 N γ l -∗ arc_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} weak_count [ #l] {{{ (c : Z), RET #c; P ∗ ⌜c >= -1⌝ }}}.
  Proof using HP1.
    iIntros "#INV #Hacc !> * HP HΦ". iLöb as "IH". wp_rec. wp_op.
    iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(?& strong &wl&?&[-> _]).
    iDestruct "H" as (?) "(Hq & HP1 & H↦ & Hw)". destruct wl.
    - iDestruct "Hw" as ">[Hw %]". wp_read.
      iMod ("Hclose2" with "Hown") as "HP". iModIntro.
      iMod ("Hclose1" with "[-HP HΦ]") as "_"; [iExists _; auto with iFrame|].
      iApply "HΦ". auto with iFrame lia.
    - wp_read. iMod ("Hclose2" with "Hown") as "HP". iModIntro.
      iMod ("Hclose1" with "[-HP HΦ]") as "_"; [iExists _; auto with iFrame|].
      iApply "HΦ". auto with iFrame lia.
  Qed.

  Lemma clone_arc_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc P1 P2 N γ l -∗ arc_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} clone_arc [ #l]
    {{{ q', RET #☠; P ∗ arc_tok γ q' ∗ P1 q' }}}.
  Proof using HP1.
    iIntros "#INV #Hacc !> * HP HΦ". iLöb as "IH". wp_rec. wp_bind (!ˢᶜ_)%E.
    iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(?& strong &?&?&[-> _]).
    iDestruct "H" as (?) "(Hq & HP1 & H↦ & Hw)". wp_read.
    iMod ("Hclose2" with "Hown") as "HP". iModIntro.
    iMod ("Hclose1" with "[-HP HΦ]") as "_"; [iExists _; auto with iFrame|].
    iModIntro. wp_let. wp_op. wp_bind (CAS _ _ _). iInv N as (st) "[>H● H]" "Hclose1".
    iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(?&strong'&?&?&[-> _]).
    iDestruct "H" as (qq) "(>#Hq & [HP1 HP1'] & Hl & Hw)". iDestruct "Hq" as %Hq.
    destruct (decide (strong = strong')) as [->|?].
    - wp_apply (wp_cas_int_suc with "Hl"). iIntros "Hl".
      iMod (own_update with "H●") as "[H● Hown']".
      { apply auth_update_alloc, prod_local_update_1,
         (op_local_update_discrete _ _ (Some (Cinl ((qq/2)%Qp, 1%positive, None))))
           =>-[/= Hqa ?]. split;[split|]=>//=; last by rewrite left_id.
        apply frac_valid. rewrite -Hq comm_L.
        by apply Qp_add_le_mono_l, Qp_div_le. }
      iMod ("Hclose2" with "Hown") as "HP". iModIntro.
      iMod ("Hclose1" with "[Hl Hw H● HP1']") as "_".
      { iExists _. iFrame. iExists _. rewrite /= [xH ⋅ _]comm_L. iFrame.
        rewrite [(qq / 2)%Qp ⋅ _]comm frac_op -[(_ + _)%Qp]assoc Qp_div_2 left_id_L. auto. }
      iModIntro. wp_case. iApply "HΦ". iFrame.
    - wp_apply (wp_cas_int_fail with "Hl"); [congruence|]. iIntros "Hl".
      iMod ("Hclose2" with "Hown") as "HP". iModIntro.
      iMod ("Hclose1" with "[-HP HΦ]") as "_".
      { iExists _. iFrame. iExists qq. iCombine "HP1 HP1'" as "$". auto with iFrame. }
      iModIntro. wp_case. iApply ("IH" with "HP HΦ").
  Qed.

  Lemma downgrade_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc P1 P2 N γ l -∗ arc_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} downgrade [ #l] {{{ RET #☠; P ∗ weak_tok γ }}}.
  Proof.
    iIntros "#INV #Hacc !> * HP HΦ". iLöb as "IH". wp_rec. wp_op. wp_bind (!ˢᶜ_)%E.
    iInv N as (st) "[>H● H]" "Hclose1".
    iApply fupd_wp. iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(?&?& wlock & weak &[-> _]).
    iMod ("Hclose2" with "Hown") as "HP". iModIntro.
    iDestruct "H" as (?) "(? & ? & ? & Hw)". destruct wlock.
    { iDestruct "Hw" as "(Hw & >%)". subst. wp_read.
      iMod ("Hclose1" with "[-HP HΦ]") as "_"; first by iExists _; auto with iFrame.
      iModIntro. wp_let. wp_op. wp_if. iApply ("IH" with "HP HΦ"). }
    wp_read. iMod ("Hclose1" with "[-HP HΦ]") as "_"; first by iExists _; auto with iFrame.
    iModIntro. wp_let. wp_op. wp_if. wp_op. wp_op. wp_bind (CAS _ _ _).
    iInv N as (st) "[>H● H]" "Hclose1".
    iApply fupd_wp. iMod ("Hacc" with "HP") as (?) "[Hown Hclose2]".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(?&?& wlock & weak' &[-> _]).
    iMod ("Hclose2" with "Hown") as "HP". iModIntro.
    iDestruct "H" as (qq) "(>Heq & HP1 & Hl & Hl1)". iDestruct "Heq" as %Heq.
    destruct (decide (weak = weak' ∧ wlock = None)) as [[<- ->]|Hw].
    - wp_apply (wp_cas_int_suc with "Hl1"). iIntros "Hl1".
      iMod (own_update with "H●") as "[H● Hown']".
      { by apply auth_update_alloc, prod_local_update_2,
              (op_local_update_discrete _ _ (1%nat)). }
      iMod ("Hclose1" with "[-Hown' HP HΦ]") as "_".
      { iExists _. iFrame. iExists _.
        rewrite Z.add_comm -(Nat2Z.inj_add 1) /=. auto with iFrame. }
      iModIntro. wp_case. iApply "HΦ". iFrame.
    - destruct wlock.
      + iDestruct "Hl1" as "[Hl1 >%]". subst.
        wp_apply (wp_cas_int_fail with "Hl1"); [done..|].
        iIntros "Hl1". iMod ("Hclose1" with "[-HP HΦ]") as "_".
        { iExists _. auto with iFrame. }
        iModIntro. wp_case. iApply ("IH" with "HP HΦ").
      + wp_apply (wp_cas_int_fail with "Hl1").
        { contradict Hw. split=>//. apply SuccNat2Pos.inj. lia. }
        iIntros "Hl1". iMod ("Hclose1" with "[-HP HΦ]") as "_".
        { iExists _. auto with iFrame. }
        iModIntro. wp_case. iApply ("IH" with "HP HΦ").
  Qed.

  Lemma weak_tok_auth_val γ st :
    own γ (● st) -∗ weak_tok γ -∗ ⌜∃ st' weak, st = (st', S weak) ∧ ✓ st'⌝.
  Proof.
    iIntros "H● Htok". iDestruct (own_valid_2 with "H● Htok") as
        %[[Hincl%option_included Hincl'%nat_included]%prod_included [Hval _]]
         %auth_both_valid_discrete.
    destruct st as [?[]], Hincl as [_|(?&?&[=]&?)]; simpl in *; try lia. eauto.
  Qed.

  Lemma clone_weak_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc P1 P2 N γ l -∗ weak_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} clone_weak [ #l] {{{ RET #☠; P ∗ weak_tok γ }}}.
  Proof.
    iIntros "#INV #Hacc !> * HP HΦ". iLöb as "IH". wp_rec. wp_op. wp_bind (!ˢᶜ_)%E.
    iAssert (□ (P ={⊤,⊤∖↑N}=∗ ∃ w : Z, (l +ₗ 1) ↦ #w ∗
              ((l +ₗ 1) ↦ #(w + 1) ={⊤∖↑N,⊤}=∗ P ∗ weak_tok γ) ∧
              ((l +ₗ 1) ↦ #w ={⊤∖↑N,⊤}=∗ P)))%I as "#Hproto".
    { iIntros "!> HP". iInv N as (st) "[>H● H]" "Hclose1".
      iMod ("Hacc" with "HP") as "[Hown Hclose2]".
      iDestruct (weak_tok_auth_val with "H● Hown") as %(st' & weak & -> & Hval).
      iMod ("Hclose2" with "Hown") as "HP".
      destruct st' as [[[[??][?|]]| |]|]; try done; [|iExists _..].
      - by iDestruct "H" as (?) "(_ & _ & _ & _ & >%)".
      - iDestruct "H" as (?) "(? & ? & ? & >$)". iIntros "!>"; iSplit; iIntros "?".
        + iMod (own_update with "H●") as "[H● $]".
          { by apply auth_update_alloc, prod_local_update_2,
                  (op_local_update_discrete _ _ (1%nat)). }
          rewrite Z.add_comm -(Nat2Z.inj_add 1). iFrame.
          iApply "Hclose1". iExists _. auto with iFrame.
        + iFrame. iApply ("Hclose1" with "[-]"). iExists _. auto with iFrame.
      - iDestruct "H" as "[? >$]". iIntros "!>"; iSplit; iIntros "?".
        + iMod (own_update with "H●") as "[H● $]".
          { by apply auth_update_alloc, prod_local_update_2,
                  (op_local_update_discrete _ _ (1%nat)). }
          rewrite Z.add_comm -(Nat2Z.inj_add 1). iFrame. iApply "Hclose1".
          iExists _. auto with iFrame.
        + iFrame. iApply ("Hclose1" with "[-]"). iExists _. auto with iFrame.
      - iDestruct "H" as "(? & >$ & ?)". iIntros "!>"; iSplit; iIntros "?".
        + iMod (own_update with "H●") as "[H● $]".
          { by apply auth_update_alloc, prod_local_update_2,
                  (op_local_update_discrete _ _ (1%nat)). }
          rewrite Z.add_comm -(Nat2Z.inj_add 1). iFrame. iApply "Hclose1".
          iExists _. auto with iFrame.
        + iFrame. iApply ("Hclose1" with "[-]"). iExists _. auto with iFrame. }
    iMod ("Hproto" with "HP") as (w) "[Hw [_ Hclose]]". wp_read.
    iMod ("Hclose" with "Hw") as "HP". iModIntro. wp_let. wp_op. wp_op.
    wp_bind (CAS _ _ _). iMod ("Hproto" with "HP") as (w') "[H↦ Hclose]".
    destruct (decide (w = w')) as [<-|].
    - wp_apply (wp_cas_int_suc with "H↦"). iIntros "H↦".
      iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "H↦"). iModIntro.
      wp_case. by iApply "HΦ".
    - wp_apply (wp_cas_int_fail with "H↦"); try done. iIntros "H↦".
      iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "H↦") as "Hown".
      iModIntro. wp_case. by iApply ("IH" with "Hown").
  Qed.

  Lemma upgrade_spec (γ : gname) (l : loc) (P : iProp Σ) :
    is_arc P1 P2 N γ l -∗ weak_tok_acc γ P (⊤ ∖ ↑N) -∗
    {{{ P }}} upgrade [ #l]
    {{{ (b : bool) q, RET #b; P ∗ if b then arc_tok γ q ∗ P1 q else True }}}.
  Proof using HP1.
    iIntros "#INV #Hacc !> * HP HΦ". iLöb as "IH". wp_rec. wp_bind (!ˢᶜ_)%E.
    iAssert (□ (P ={⊤,∅}=∗ ∃ s : Z, l ↦ #s ∗
              (⌜s ≠ 0⌝ -∗ l ↦ #(s + 1) ={∅,⊤}=∗ ∃ q, P ∗ arc_tok γ q ∗ ▷ P1 q) ∧
              (l ↦ #s ={∅,⊤}=∗ P)))%I as "#Hproto".
    { iIntros "!> HP". iInv N as (st) "[>H● H]" "Hclose1".
      iMod ("Hacc" with "HP") as "[Hown Hclose2]".
      iDestruct (weak_tok_auth_val with "H● Hown") as %(st' & weak & -> & Hval).
      destruct st' as [[[[q' c]?]| |]|]; try done; iExists _.
      - iDestruct "H" as (q) "(>Heq & [HP1 HP1'] & >$ & ?)". iDestruct "Heq" as %Heq.
        iIntros "!>"; iSplit; iMod ("Hclose2" with "Hown") as "HP".
        + iIntros "_ Hl". iExists (q/2)%Qp. iMod (own_update with "H●") as "[H● $]".
          { apply auth_update_alloc. rewrite -[(_,0%nat)]right_id.
            apply op_local_update_discrete=>Hv. constructor; last done.
            split; last by rewrite /= left_id; apply Hv. split=>[|//].
            apply frac_valid. rewrite /= -Heq comm_L.
            by apply Qp_add_le_mono_l, Qp_div_le. }
          iFrame. iApply "Hclose1". iExists _. iFrame. iExists _. iFrame.
          rewrite /= [xH ⋅ _]comm_L frac_op [(_ + q')%Qp]comm -[(_ + _)%Qp]assoc
                  Qp_div_2 left_id_L. auto with iFrame.
        + iIntros "Hl". iFrame. iApply ("Hclose1" with "[-]"). iExists _. iFrame.
          iExists q. iCombine "HP1 HP1'" as "$". auto with iFrame.
      - iDestruct "H" as "[>$ ?]". iIntros "!>"; iSplit; first by auto with congruence.
        iIntros "Hl". iMod ("Hclose2" with "Hown") as "$". iApply "Hclose1".
        iExists _. auto with iFrame.
      - iDestruct "H" as "[>$ ?]". iIntros "!>"; iSplit; first by auto with congruence.
        iIntros "Hl". iMod ("Hclose2" with "Hown") as "$". iApply "Hclose1".
        iExists _. auto with iFrame. }
    iMod ("Hproto" with "HP") as (s) "[Hs [_ Hclose]]". wp_read.
    iMod ("Hclose" with "Hs") as "HP". iModIntro. wp_let. wp_op; wp_if; case_bool_decide.
    - iApply wp_value. iApply ("HΦ" $! _ 1%Qp). auto.
    - wp_op. wp_bind (CAS _ _ _). iMod ("Hproto" with "HP") as (s') "[H↦ Hclose]".
      destruct (decide (s = s')) as [<-|].
      + wp_apply (wp_cas_int_suc with "H↦"). iIntros "H↦".
        iDestruct "Hclose" as "[Hclose _]".
        iMod ("Hclose" with "[//] H↦") as (q) "(?&?&?)". iModIntro.
        wp_case. iApply "HΦ". iFrame.
      + wp_apply (wp_cas_int_fail with "H↦"); try done. iIntros "H↦".
        iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "H↦") as "Hown".
        iModIntro. wp_case. by iApply ("IH" with "Hown").
  Qed.

  Lemma drop_weak_spec (γ : gname) (l : loc) :
    is_arc P1 P2 N γ l -∗
    {{{ weak_tok γ }}} drop_weak [ #l]
    {{{ (b : bool), RET #b ; if b then P2 ∗ l ↦ #0 ∗ (l +ₗ 1) ↦ #0 else True }}}.
  Proof.
    iIntros "#INV !> * Hown HΦ". iLöb as "IH". wp_rec. wp_op. wp_bind (!ˢᶜ_)%E.
    iAssert (□ (weak_tok γ ={⊤,⊤ ∖ ↑N}=∗ ∃ w : Z, (l +ₗ 1) ↦ #w ∗
              ((l +ₗ 1) ↦ #(w - 1) ={⊤ ∖ ↑N,⊤}=∗ ⌜w ≠ 1⌝ ∨
               ▷ P2 ∗ l ↦ #0 ∗ (l +ₗ 1) ↦ #0) ∧
              ((l +ₗ 1) ↦ #w ={⊤ ∖ ↑N,⊤}=∗ weak_tok γ)))%I as "#Hproto".
    { iIntros "!> Hown". iInv N as (st) "[>H● H]" "Hclose1".
      iDestruct (weak_tok_auth_val with "H● Hown") as %(st' & weak & -> & Hval).
      destruct st' as [[[[??][?|]]| |]|]; try done; [|iExists _..].
      - by iDestruct "H" as (?) "(_ & _ & _ & _ & >%)".
      - iDestruct "H" as (q) "(>Heq & HP1 & ? & >$)". iIntros "!>"; iSplit; iIntros "Hl1".
        + iMod ("Hclose1" with "[>-]") as "_"; last iLeft; auto with lia.
          iExists _. iMod (own_update_2 with "H● Hown") as "$".
          { apply auth_update_dealloc, prod_local_update_2,
                  (cancel_local_update_unit 1%nat), _. }
          iExists _. iFrame. by replace (S (S weak) - 1) with (S weak:Z) by lia.
        + iFrame. iApply "Hclose1". iExists _. auto with iFrame.
      - iDestruct "H" as "[? >$]". iIntros "!>"; iSplit; iIntros "Hl1".
        + iMod ("Hclose1" with "[>-]") as "_"; last iLeft; auto with lia.
          iExists _. iMod (own_update_2 with "H● Hown") as "$".
          { apply auth_update_dealloc, prod_local_update_2,
                  (cancel_local_update_unit 1%nat), _. }
          iFrame. by replace (S (S weak) - 1) with (S weak:Z) by lia.
        + iFrame. iApply "Hclose1". iExists _. auto with iFrame.
      - iDestruct "H" as "(>? & >$ & HP2)". iIntros "!>"; iSplit; iIntros "Hl1".
        + iMod (own_update_2 with "H● Hown") as "H●".
          { apply auth_update_dealloc, prod_local_update_2,
                  (cancel_local_update_unit 1%nat), _. }
          destruct weak as [|weak].
          * iMod ("Hclose1" with "[H●]") as "_"; last by auto with iFrame.
            iExists _. iFrame.
          * iMod ("Hclose1" with "[>-]") as "_"; last iLeft; auto with lia.
            iExists _. iFrame. by replace (S (S weak) - 1) with (S weak:Z) by lia.
        + iFrame. iApply "Hclose1". iExists _. auto with iFrame. }
    iMod ("Hproto" with "Hown") as (w) "[Hw [_ Hclose]]". wp_read.
    iMod ("Hclose" with "Hw") as "Hown". iModIntro. wp_let. wp_op. wp_op.
    wp_bind (CAS _ _ _).
    iMod ("Hproto" with "Hown") as (w') "[Hw Hclose]". destruct (decide (w = w')) as [<-|?].
    - wp_apply (wp_cas_int_suc with "Hw"). iIntros "Hw".
      iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "Hw") as "HP2". iModIntro.
      wp_case. wp_op; case_bool_decide; subst; iApply "HΦ"=>//.
      by iDestruct "HP2" as "[%|$]".
    - wp_apply (wp_cas_int_fail with "Hw"); try done. iIntros "Hw".
      iDestruct "Hclose" as "[_ Hclose]". iMod ("Hclose" with "Hw") as "Hown".
      iModIntro. wp_case. by iApply ("IH" with "Hown").
  Qed.

  Lemma close_last_strong γ l :
    is_arc P1 P2 N γ l -∗ own γ (◯ (Some (Cinr (Excl ())), 0%nat)) -∗ P2
    ={⊤}=∗ weak_tok γ.
  Proof.
    iIntros "INV H◯ HP2". iInv N as ([st ?]) "[>H● H]" "Hclose".
    iDestruct (own_valid_2 with "H● H◯")
      as %[[[[=]|Hincl]%option_included _]%prod_included [? _]]%auth_both_valid_discrete.
    simpl in Hincl. destruct Hincl as (?&?&[=<-]&->&[?|[]%exclusive_included]);
        try done; try apply _. setoid_subst.
    iMod (own_update_2 with "H● H◯") as "[H● $]".
    { apply auth_update, prod_local_update', (op_local_update _ _ 1%nat)=>//.
      apply delete_option_local_update, _. }
    iApply "Hclose". iExists _. by iFrame.
  Qed.

  Lemma drop_arc_spec (γ : gname) (q: Qp) (l : loc) :
    is_arc P1 P2 N γ l -∗
    {{{ arc_tok γ q ∗ P1 q }}} drop_arc  [ #l]
    {{{ (b : bool), RET #b ; if b then P1 1 ∗ (P2 ={⊤}=∗ weak_tok γ) else True }}}.
  Proof using HP1.
    iIntros "#INV !> * [Hown HP1] HΦ". iLöb as "IH".
    wp_rec. wp_bind (!ˢᶜ_)%E. iInv N as (st) "[>H● H]" "Hclose".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(?& s &?&?&[-> _]).
    iDestruct "H" as (x') "(? & ? & ? & ?)". wp_read.
    iMod ("Hclose" with "[-Hown HP1 HΦ]") as "_". { iExists _. auto with iFrame. }
    iModIntro. wp_let. wp_op. wp_bind (CAS _ _ _). iInv N as (st) "[>H● H]" "Hclose".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(q' & s' & wl & w &[-> Hqq']).
    iDestruct "H" as (q'') "(>Hq'' & HP1' & Hs & Hw)". iDestruct "Hq''" as %Hq''.
    destruct (decide (s = s')) as [<-|?].
    - wp_apply (wp_cas_int_suc with "Hs"). iIntros "Hs".
      destruct decide as [->|?].
      + destruct Hqq' as [<- ->].
        iMod (own_update_2 with "H● Hown") as "[H● H◯]".
        { apply auth_update, prod_local_update_1. rewrite -[x in (x, _)]right_id.
          etrans; first apply: cancel_local_update_unit.
          by apply (op_local_update _ _ (Some (Cinr (Excl ())))). }
        iMod ("Hclose" with "[H● Hs Hw]") as "_"; first by iExists _; do 2 iFrame.
        iModIntro. wp_case. iApply wp_fupd. wp_op.
        iApply ("HΦ"). rewrite -{2}Hq''. iCombine "HP1 HP1'" as "$".
        by iApply close_last_strong.
      + destruct Hqq' as [? ->].
        rewrite -[in (_, _)](Pos.succ_pred s) // -[wl in Cinl (_, wl)]left_id
                -Pos.add_1_l 2!pair_op Cinl_op Some_op.
        iMod (own_update_2 _ _ _ _ with "H● Hown") as "H●".
        { apply auth_update_dealloc, prod_local_update_1, @cancel_local_update_unit, _. }
        iMod ("Hclose" with "[- HΦ]") as "_".
        { iExists _. iFrame. iExists (q + q'')%Qp. iCombine "HP1 HP1'" as "$".
          iSplit; last by destruct s.
          iIntros "!> !%". rewrite assoc -Hq''. f_equal. apply comm, _. }
        iModIntro. wp_case. wp_op; case_bool_decide; simplify_eq. by iApply "HΦ".
    - wp_apply (wp_cas_int_fail with "Hs"); [congruence|]. iIntros "Hs".
      iSpecialize ("IH" with "Hown HP1 HΦ").
      iMod ("Hclose" with "[- IH]") as "_"; first by iExists _; auto with iFrame.
      iModIntro. by wp_case.
  Qed.

  Lemma try_unwrap_spec (γ : gname) (q: Qp) (l : loc) :
    is_arc P1 P2 N γ l -∗
    {{{ arc_tok γ q ∗ P1 q }}} try_unwrap [ #l]
    {{{ (b : bool), RET #b ;
        if b then P1 1 ∗ (P2 ={⊤}=∗ weak_tok γ) else arc_tok γ q ∗ P1 q }}}.
  Proof using HP1.
    iIntros "#INV !> * [Hown HP1] HΦ". wp_rec. iInv N as (st) "[>H● H]" "Hclose".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(q' & s & wl & w &[-> Hqq']).
    iDestruct "H" as (q'') "(>Hq'' & HP1' & Hs & Hw)". iDestruct "Hq''" as %Hq''.
    destruct (decide (s = xH)) as [->|?].
    - wp_apply (wp_cas_int_suc with "Hs"). iIntros "Hs".
      destruct Hqq' as [<- ->]. iMod (own_update_2 with "H● Hown") as "[H● H◯]".
      { apply auth_update, prod_local_update_1. rewrite -[x in (x, _)]right_id.
        etrans; first apply: cancel_local_update_unit.
        by apply (op_local_update _ _ (Some (Cinr (Excl ())))). }
      iMod ("Hclose" with "[H● Hs Hw]") as "_"; first by iExists _; do 2 iFrame.
      iApply ("HΦ" $! true). rewrite -{1}Hq''. iCombine "HP1 HP1'" as "$".
      by iApply close_last_strong.
    - wp_apply (wp_cas_int_fail with "Hs"); [congruence|]. iIntros "Hs".
      iMod ("Hclose" with "[-Hown HP1 HΦ]") as "_"; first by iExists _; auto with iFrame.
      iApply ("HΦ" $! false). by iFrame.
  Qed.

  Lemma is_unique_spec (γ : gname) (q: Qp) (l : loc) :
    is_arc P1 P2 N γ l -∗
    {{{ arc_tok γ q ∗ P1 q }}} is_unique [ #l]
    {{{ (b : bool), RET #b ;
        if b then l ↦ #1 ∗ (l +ₗ 1) ↦ #1 ∗ P1 1
        else arc_tok γ q ∗ P1 q }}}.
  Proof using HP1.
    iIntros "#INV !> * [Hown HP1] HΦ". wp_rec. wp_bind (CAS _ _ _). wp_op.
    iInv N as (st) "[>H● H]" "Hclose".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(? & ? & wl & w &[-> _]).
    iDestruct "H" as (?) "(>Hq'' & HP1' & >Hs & >Hw)".
    destruct wl; last (destruct w; last first).
    - iDestruct "Hw" as "[Hw %]". subst.
      iApply (wp_cas_int_fail with "Hw")=>//. iNext. iIntros "Hw".
      iMod ("Hclose" with "[-HΦ Hown HP1]") as "_"; first by iExists _; eauto with iFrame.
      iModIntro. wp_case. iApply "HΦ". iFrame.
    - iApply (wp_cas_int_fail with "Hw"); [lia|]. iNext. iIntros "Hw".
      iMod ("Hclose" with "[-HΦ Hown HP1]") as "_"; first by iExists _; eauto with iFrame.
      iModIntro. wp_case. iApply "HΦ". iFrame.
    - iApply (wp_cas_int_suc with "Hw")=>//. iNext. iIntros "Hw".
      iMod (own_update_2 with "H● Hown") as "[H● H◯]".
      { by apply auth_update, prod_local_update_1, option_local_update,
                 csum_local_update_l, prod_local_update_2,
                 (alloc_option_local_update (Excl ())). }
      iMod ("Hclose" with "[-HΦ HP1 H◯]") as "_"; first by iExists _; eauto with iFrame.
      iModIntro. wp_case. wp_bind (!ˢᶜ_)%E. iInv N as ([st ?]) "[>H● H]" "Hclose".
      iDestruct (own_valid_2 with "H● H◯") as
        %[[[[=]|Hincl]%option_included _]%prod_included [? _]]%auth_both_valid_discrete.
      simpl in Hincl. destruct Hincl as (? & ? & [=<-] & -> & [|Hincl]); last first.
      + apply csum_included in Hincl. destruct Hincl as [->|[Hincl|(?&?&[=]&?)]]=>//.
        destruct Hincl as (?&[[??]?]&[=<-]&->&[[_ Hlt]%prod_included _]%prod_included).
        simpl in Hlt. apply pos_included in Hlt.
        iDestruct "H" as (?) "(? & ? & ? & ?)". wp_read.
        iMod ("Hclose" with "[-HΦ H◯ HP1]") as "_"; first by iExists _; auto with iFrame.
        iModIntro. wp_let. wp_op; case_bool_decide; [lia|]. wp_let. wp_op. wp_bind (_ <-ˢᶜ _)%E.
        iInv N as ([st w]) "[>H● H]" "Hclose".
        iDestruct (own_valid_2 with "H● H◯") as
           %[[[[=]|Hincl]%option_included _]%prod_included [Hval _]]%auth_both_valid_discrete.
        simpl in Hincl. destruct Hincl as (x1 & x2 & [=<-] & -> & Hincl); last first.
        assert (∃ q p, x2 = Cinl (q, p, Excl' ())) as (? & ? & ->).
        { destruct Hincl as [|Hincl]; first by setoid_subst; eauto.
          apply csum_included in Hincl. destruct Hincl as [->|[Hincl|(?&?&[=]&?)]]=>//.
          destruct Hincl as (?&[[??]?]&[=<-]&->&[_ Hincl%option_included]%prod_included).
          simpl in Hincl. destruct Hincl as [[=]|(?&?&[=<-]&->&[?|[]%exclusive_included])];
            [|by apply _|by apply Hval]. setoid_subst. eauto. }
        iDestruct "H" as (?) "(? & ? & ? & >? & >%)". subst. wp_write.
        iMod (own_update_2 with "H● H◯") as "[H● H◯]".
        { apply auth_update, prod_local_update_1, option_local_update,
          csum_local_update_l, prod_local_update_2, delete_option_local_update, _. }
        iMod ("Hclose" with "[-HΦ H◯ HP1]") as "_"; first by iExists _; auto with iFrame.
        iModIntro. wp_seq. iApply "HΦ". iFrame.
      + setoid_subst. iDestruct "H" as (?) "(Hq & HP1' & ? & >? & >%)". subst. wp_read.
        iMod (own_update_2 with "H● H◯") as "H●".
        { apply auth_update_dealloc. rewrite -{1}[(_, 0%nat)]right_id.
          apply cancel_local_update_unit, _. }
        iMod ("Hclose" with "[H●]") as "_"; first by iExists _; iFrame.
        iModIntro. wp_seq. wp_op. wp_let. wp_op. wp_write. iApply "HΦ".
        iDestruct "Hq" as %<-. iCombine "HP1 HP1'" as "$". iFrame.
  Qed.

  Lemma try_unwrap_full_spec (γ : gname) (q: Qp) (l : loc) :
    is_arc P1 P2 N γ l -∗
    {{{ arc_tok γ q ∗ P1 q }}} try_unwrap_full [ #l]
    {{{ (x : fin 3), RET #x ;
        match x : nat with
        (* No other reference : we get everything. *)
        | 0%nat => l ↦ #1 ∗ (l +ₗ 1) ↦ #1 ∗ P1 1
        (* No other strong, but there are weaks : we get P1,
           plus the option to get a weak if we pay P2. *)
        | 1%nat => P1 1 ∗ (P2 ={⊤}=∗ weak_tok γ)
        (* There are other strong : we get back what we gave at the first place. *)
        | _ (* 2 *) => arc_tok γ q ∗ P1 q
        end }}}.
  Proof using HP1.
    iIntros "#INV !> * [Hown HP1] HΦ". wp_rec. wp_bind (CAS _ _ _).
    iInv N as (st) "[>H● H]" "Hclose".
    iDestruct (arc_tok_auth_val with "H● Hown") as %(q' & s & wl & w &[-> Hqq']).
    iDestruct "H" as (q'') "(>Hq'' & HP1' & Hs & Hw)". iDestruct "Hq''" as %Hq''.
    destruct (decide (s = xH)) as [->|?].
    - wp_apply (wp_cas_int_suc with "Hs")=>//. iIntros "Hs".
      destruct Hqq' as [<- ->]. iMod (own_update_2 with "H● Hown") as "[H● H◯]".
      { apply auth_update, prod_local_update_1. rewrite -[x in (x, _)]right_id.
        etrans; first apply: cancel_local_update_unit.
        by apply (op_local_update _ _ (Some (Cinr (Excl ())))). }
      iCombine "HP1" "HP1'" as "HP1". rewrite Hq''. clear Hq'' q''.
      iMod ("Hclose" with "[H● Hs Hw]") as "_"; first by iExists _; do 2 iFrame.
      clear w. iModIntro. wp_case. wp_op. wp_bind (!ˢᶜ_)%E.
      iInv N as ([st w']) "[>H● H]" "Hclose".
      iDestruct (own_valid_2 with "H● H◯")
        as %[[[[=]|Hincl]%option_included _]%prod_included [? _]]%auth_both_valid_discrete.
      simpl in Hincl. destruct Hincl as (?&?&[=<-]&->&[?|[]%exclusive_included]);
        [|by apply _|done]. setoid_subst. iDestruct "H" as "[Hl Hl1]".
      wp_read. destruct w'.
      + iMod (own_update_2 with "H● H◯") as "H●".
        { apply auth_update_dealloc, prod_local_update_1,
                delete_option_local_update, _. }
        iMod ("Hclose" with "[H●]") as "_"; first by iExists _; iFrame. iModIntro.
        wp_op. wp_if. wp_write. iApply ("HΦ" $! 0%fin). iFrame.
      + iMod ("Hclose" with "[H● Hl Hl1]") as "_"; first by iExists _; do 2 iFrame.
        iModIntro. wp_op; case_bool_decide; [lia|]. wp_if. iApply ("HΦ" $! 1%fin). iFrame.
        by iApply close_last_strong.
    - wp_apply (wp_cas_int_fail with "Hs"); [congruence|]. iIntros "Hs".
      iMod ("Hclose" with "[H● Hs Hw HP1']") as "_"; first by iExists _; auto with iFrame.
      iModIntro. wp_case. iApply ("HΦ" $! 2%fin). iFrame.
  Qed.
End arc.

Global Typeclasses Opaque is_arc arc_tok weak_tok.
