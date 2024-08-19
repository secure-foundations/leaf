(** This file contains the examples from the paper:

Interactive Proofs in Higher-Order Concurrent Separation Logic
Robbert Krebbers, Amin Timany and Lars Birkedal
POPL 2017 *)
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import base_logic.
From iris.deprecated.program_logic Require Import hoare.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Unset Mangle Names.

(** The proofs from Section 3.1 *)
Section demo.
  Context {M : ucmra}.
  Notation iProp := (uPred M).

  (* The version in Coq *)
  Lemma and_exist A (P R: Prop) (Ψ: A → Prop) :
    P ∧ (∃ a, Ψ a) ∧ R → ∃ a, P ∧ Ψ a.
  Proof.
    intros [HP [HΨ HR]].
    destruct HΨ as [x HΨ].
    exists x.
    split.
    -  assumption.
    -  assumption.
  Qed.

  (* The version in IPM *)
  Check "sep_exist".
  Lemma sep_exist A (P R: iProp) (Ψ: A → iProp) :
    P ∗ (∃ a, Ψ a) ∗ R ⊢ ∃ a, Ψ a ∗ P.
  Proof.
    iIntros "[HP [HΨ HR]]".
    iDestruct "HΨ" as (x) "HΨ".
    iExists x. Show.
    iSplitL "HΨ".
    - Show. iAssumption.
    - Show. iAssumption.
  Qed.

  (* The short version in IPM, as in the paper *)
  Check "sep_exist_short".
  Lemma sep_exist_short A (P R: iProp) (Ψ: A → iProp) :
    P ∗ (∃ a, Ψ a) ∗ R ⊢ ∃ a, Ψ a ∗ P.
  Proof. iIntros "[HP [HΨ HR]]". Show. iFrame "HP". iAssumption. Qed.

  (* An even shorter version in IPM, using the frame introduction pattern `$` *)
  Lemma sep_exist_shorter A (P R: iProp) (Ψ: A → iProp) :
    P ∗ (∃ a, Ψ a) ∗ R ⊢ ∃ a, Ψ a ∗ P.
  Proof. by iIntros "[$ [??]]". Qed.
End demo.

(** The proofs from Section 3.2 *)
(** In the Iris development we often write specifications directly using weakest
preconditions, in sort of `CPS` style, so that they can be applied easier when
proving client code. A version of [list_reverse] in that style can be found in
the file [theories/tests/list_reverse.v]. *)
Section list_reverse.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  Fixpoint is_list (hd : val) (xs : list val) : iProp :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_list hd' xs
    end%I.

  Definition rev : val :=
    rec: "rev" "hd" "acc" :=
      match: "hd" with
        NONE => "acc"
      | SOME "l" =>
         let: "tmp1" := Fst !"l" in
         let: "tmp2" := Snd !"l" in
         "l" <- ("tmp1", "acc");;
         "rev" "tmp2" "hd"
      end.

  Lemma rev_acc_ht hd acc xs ys :
    ⊢ {{ is_list hd xs ∗ is_list acc ys }} rev hd acc {{ w, is_list w (reverse xs ++ ys) }}.
  Proof.
    iIntros "!> [Hxs Hys]".
    iLöb as "IH" forall (hd acc xs ys). wp_rec; wp_let.
    destruct xs as [|x xs]; iSimplifyEq.
    - (* nil *) by wp_match.
    - (* cons *) iDestruct "Hxs" as (l hd') "(% & Hx & Hxs)"; iSimplifyEq.
      wp_match. wp_load. wp_load. wp_store.
      rewrite reverse_cons -assoc.
      iApply ("IH" $! hd' (InjRV #l) xs (x :: ys) with "Hxs [Hx Hys]").
      iExists l, acc; by iFrame.
  Qed.

  Lemma rev_ht hd xs :
    ⊢ {{ is_list hd xs }} rev hd NONEV {{ w, is_list w (reverse xs) }}.
  Proof.
    iIntros "!> Hxs". rewrite -(right_id_L [] (++) (reverse xs)).
    iApply (rev_acc_ht hd NONEV with "[Hxs]"); simpl; by iFrame.
  Qed.
End list_reverse.

(** The proofs from Section 5 *)
(** This part contains a formalization of the monotone counter, but with an
explicit contruction of the monoid, as we have also done in the proof mode
paper. This should simplify explaining and understanding what is happening.
A version that uses the authoritative monoid and natural number monoid
under max can be found in [theories/heap_lang/lib/counter.v]. *)

Definition newcounter : val := λ: <>, ref #0.
Definition incr : val :=
  rec: "incr" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "incr" "l".
Definition read : val := λ: "l", !"l".

(** The CMRA we need. *)
Inductive M := Auth : nat → M | Frag : nat → M | Bot.

Section M.
  Local Arguments cmra_op _ !_ !_/.
  Local Arguments op _ _ !_ !_/.
  Local Arguments core _ _ !_/.

  Canonical Structure M_O : ofe := leibnizO M.

  Local Instance M_valid : Valid M := λ x, x ≠ Bot.
  Local Instance M_op : Op M := λ x y,
    match x, y with
    | Auth n, Frag j | Frag j, Auth n => if decide (j ≤ n) then Auth n else Bot
    | Frag i, Frag j => Frag (max i j)
    | _, _ => Bot
    end.
  Local Instance M_pcore : PCore M := λ x,
    Some match x with Auth j | Frag j => Frag j | _ => Bot end.
  Local Instance M_unit : Unit M := Frag 0.

  Definition M_ra_mixin : RAMixin M.
  Proof.
    apply ra_total_mixin; try solve_proper || eauto.
    - intros [n1|i1|] [n2|i2|] [n3|i3|];
        repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n1|i1|] [n2|i2|]; repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n|i|]; repeat (simpl; case_decide); f_equal/=; lia.
    - by intros [n|i|].
    - intros [n1|i1|] y [[n2|i2|] ?]; exists (core y); simplify_eq/=;
        repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n1|i1|] [n2|i2|]; simpl; by try case_decide.
  Qed.
  Canonical Structure M_R : cmra := discreteR M M_ra_mixin.

  Global Instance M_discrete : CmraDiscrete M_R.
  Proof. apply discrete_cmra_discrete. Qed.

  Definition M_ucmra_mixin : UcmraMixin M.
  Proof.
    split; try (done || apply _).
    intros [?|?|]; simpl; try case_decide; f_equal/=; lia.
  Qed.
  Canonical Structure M_UR : ucmra := Ucmra M M_ucmra_mixin.

  Global Instance frag_core_id n : CoreId (Frag n).
  Proof. by constructor. Qed.
  Lemma auth_frag_valid j n : ✓ (Auth n ⋅ Frag j) → j ≤ n.
  Proof. simpl. case_decide; first done. by intros []. Qed.
  Lemma auth_frag_op (j n : nat) : j ≤ n → Auth n = Auth n ⋅ Frag j.
  Proof. intros. by rewrite /= decide_True. Qed.

  Lemma M_update n : Auth n ~~> Auth (S n).
  Proof.
    apply cmra_discrete_total_update=>-[m|j|] /= ?; repeat case_decide; done || lia.
  Qed.
End M.

Class counterG Σ := CounterG { counter_tokG : inG Σ M_UR }.
Local Existing Instance counter_tokG.

Definition counterΣ : gFunctors := #[GFunctor (constRF M_UR)].
Global Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section counter_proof.
  Context `{!heapGS Σ, !counterG Σ}.
  Implicit Types l : loc.

  Definition I (γ : gname) (l : loc) : iProp Σ :=
    (∃ c : nat, l ↦ #c ∗ own γ (Auth c))%I.

  Definition C (l : loc) (n : nat) : iProp Σ :=
    (∃ N γ, inv N (I γ l) ∧ own γ (Frag n))%I.

  (** The main proofs. *)
  Global Instance C_persistent l n : Persistent (C l n).
  Proof. apply _. Qed.

  Lemma newcounter_spec :
    ⊢ {{ True }} newcounter #() {{ v, ∃ l, ⌜v = #l⌝ ∧ C l 0 }}.
  Proof.
    iIntros "!> _ /=". rewrite /newcounter /=. wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Auth 0)) as (γ) "Hγ"; first done.
    rewrite (auth_frag_op 0 0) //; iDestruct "Hγ" as "[Hγ Hγf]".
    set (N:= nroot .@ "counter").
    iMod (inv_alloc N _ (I γ l) with "[Hl Hγ]") as "#?".
    { iIntros "!>". iExists 0. by iFrame. }
    iModIntro. rewrite /C; eauto 10.
  Qed.

  Lemma incr_spec l n :
    ⊢ {{ C l n }} incr #l {{ v, ⌜v = #()⌝ ∧ C l (S n) }}.
  Proof.
    iIntros "!> Hl /=". iLöb as "IH". wp_rec.
    iDestruct "Hl" as (N γ) "[#Hinv Hγf]".
    wp_bind (! _)%E. iInv "Hinv" as (c) "[Hl Hγ]".
    wp_load. iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    wp_let. wp_op.
    wp_bind (CmpXchg _ _ _). iInv "Hinv" as (c') ">[Hl Hγ]".
    destruct (decide (c' = c)) as [->|].
    - iCombine "Hγ" "Hγf" as "Hγ".
      iDestruct (own_valid with "Hγ") as %?%auth_frag_valid; rewrite -auth_frag_op //.
      iMod (own_update with "Hγ") as "Hγ"; first apply M_update.
      rewrite (auth_frag_op (S n) (S c)); last lia; iDestruct "Hγ" as "[Hγ Hγf]".
      wp_cmpxchg_suc. iModIntro. iSplitL "Hl Hγ".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      wp_pures. by iFrame "#∗".
    - wp_cmpxchg_fail; first (intros [=]; abstract lia).
      iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c'; by iFrame|].
      wp_pures. iApply "IH". iFrame "#∗".
  Qed.

  Check "read_spec".
  Lemma read_spec l n :
    ⊢ {{ C l n }} read #l {{ v, ∃ m : nat, ⌜v = #m ∧ n ≤ m⌝ ∧ C l m }}.
  Proof.
    iIntros "!> Hl /=". iDestruct "Hl" as (N γ) "[#Hinv Hγf]".
    rewrite /read /=. wp_lam. Show. iInv "Hinv" as (c) "[Hl Hγ]". wp_load. Show.
    iDestruct (own_valid γ (Auth c ⋅ Frag n) with "[-]") as %H%auth_frag_valid.
    { iApply own_op. by iFrame. }
    rewrite (auth_frag_op c c); last lia; iDestruct "Hγ" as "[Hγ Hγf']".
    iModIntro. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    rewrite /C; eauto 10 with lia.
  Qed.
End counter_proof.
