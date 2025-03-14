From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From lrust.util Require Import basic.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export base.
From guarding.lib Require Import lifetime_full.
From guarding Require Import guard.
Set Default Proof Using "Type".

Definition elctx_elt : Type := Lifetime * Lifetime.
Notation elctx := (list elctx_elt).

Declare Scope lrust_elctx_scope.
Delimit Scope lrust_elctx_scope with EL.
(* We need to define [elctx] and [llctx] as notations to make eauto
   work. But then, Coq is not able to bind them to their
   notations, so we have to use [Arguments] everywhere. *)
Bind Scope lrust_elctx_scope with elctx_elt.

Notation "κ1 ⊑ₑ κ2" := (@pair Lifetime Lifetime κ1 κ2) (at level 55).

Definition llctx_elt : Type := Lifetime * list Lifetime.
Notation llctx := (list llctx_elt).

Notation "κ ⊑ₗ κl" := (@pair Lifetime (list Lifetime) κ κl) (at level 55).

(* External lifetime context. *)
Definition elctx_elt_interp `{!invGS Σ, !lifetime_internals_ra.llft_logicGS Σ} (x : elctx_elt) : iProp Σ :=
  (x.1 ⊑ x.2)%I.
Notation elctx_interp := (big_sepL (λ _, elctx_elt_interp)).

Definition static := llft_empty.
Notation lft_intersect_list l := (foldr (⊓) static l).



Section lft_contexts.
  Context `{!invGS Σ, !lifetime_internals_ra.llft_logicGS Σ}.
  Implicit Type (κ: Lifetime).

  Global Instance elctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) elctx_interp.
  Proof. intros ???. by apply big_opL_permutation. Qed.
  Global Instance elctx_interp_persistent E :
    Persistent (elctx_interp E).
  Proof. apply _. Qed.
  Lemma elctx_interp_app (E1 E2 : elctx) :
    elctx_interp (E1 ++ E2) ⊣⊢ elctx_interp E1 ∗ elctx_interp E2.
  Proof. apply big_sepL_app. Qed.

  (* Local lifetime context. *)
  Definition llctx_elt_interp (x : llctx_elt) : iProp Σ :=
    let κ' := lft_intersect_list (x.2) in
    (∃ κ0, ⌜x.1 = κ' ⊓ κ0⌝ ∗ @[κ0] ∗ □ (@[κ0] ={↑Nllft}▷=∗ [†κ0]))%I.
    (*
  Global Instance llctx_elt_interp_fractional x :
    Fractional (llctx_elt_interp x).
  Proof.
    destruct x as [κ κs]. iIntros (q q'). iSplit; iIntros "H".
    - iDestruct "H" as (κ0) "(% & [Hq Hq'] & #?)".
      iSplitL "Hq"; iExists _; by iFrame "∗%".
    - iDestruct "H" as "[Hq Hq']".
      iDestruct "Hq" as (κ0) "(% & Hq & #?)".
      iDestruct "Hq'" as (κ0') "(% & Hq' & #?)". simpl in *.
      rewrite (inj ((lft_intersect_list κs) ⊓.) κ0' κ0); last congruence.
      iExists κ0. iFrame "∗%". done.
  Qed.
  *)

  Definition llctx_interp (L : llctx) : iProp Σ :=
    ([∗ list] x ∈ L, llctx_elt_interp x)%I.
  Global Arguments llctx_interp _.
  (*
  Global Instance llctx_interp_fractional L :
    Fractional (llctx_interp L).
  Proof. intros ??. rewrite -big_sepL_sep. by setoid_rewrite <-fractional. Qed.
  Global Instance llctx_interp_as_fractional L q :
    AsFractional (llctx_interp L q) (llctx_interp L) q.
  Proof. split. done. apply _. Qed.
  Global Instance frame_llctx_interp p L q1 q2 RES :
    FrameFractionalHyps p (llctx_interp L q1) (llctx_interp L) RES q1 q2 →
    Frame p (llctx_interp L q1) (llctx_interp L q2) RES | 5.
  Proof. apply: frame_fractional. Qed.
  *)

  Global Instance llctx_interp_permut :
    Proper ((≡ₚ) ==> (⊣⊢)) llctx_interp.
  Proof. intros x y Hequiv. apply big_opL_permutation. trivial. Qed.

(*
  Lemma lctx_equalize_lft κ1 κ2 `{!frac_borG Σ} :
    llft_ctx -∗ llctx_elt_interp (κ1 ⊑ₗ [κ2]%list) ={⊤}=∗
      elctx_elt_interp (κ1 ⊑ₑ κ2) ∗ elctx_elt_interp (κ2 ⊑ₑ κ1).
  Proof.
    iIntros "#LFT". iDestruct 1 as (κ) "(% & Hκ & _)"; simplify_eq/=.
    iMod (lft_eternalize with "Hκ") as "#Hincl".
    iModIntro. iSplit.
    - iApply lft_incl_trans; iApply lft_intersect_incl_l.
    - iApply (lft_incl_glb with "[]"); first iApply (lft_incl_glb with "[]").
      + iApply lft_incl_refl.
      + iApply lft_incl_static.
      + iApply lft_incl_trans; last done. iApply lft_incl_static.
  Qed.
  *)

  Context (E : elctx) (L : llctx).

  (* Lifetime inclusion *)
  Definition lctx_lft_incl κ κ' : Prop :=
    llctx_interp L -∗ □ (elctx_interp E -∗ κ ⊑ κ').

  Definition lctx_lft_eq κ κ' : Prop :=
    lctx_lft_incl κ κ' ∧ lctx_lft_incl κ' κ.

  Lemma lctx_lft_incl_incl κ κ' : lctx_lft_incl κ κ' → lctx_lft_incl κ κ'.
  Proof. done. Qed.

  Lemma lctx_lft_incl_refl κ : lctx_lft_incl κ κ.
  Proof. iIntros "A". iModIntro. iIntros "B". iApply guards_refl. Qed.

  Global Instance lctx_lft_incl_preorder : PreOrder lctx_lft_incl.
  Proof.
    split; first by intros ?; apply lctx_lft_incl_refl.
    - iIntros (??? H1 H2) "HL".
    iDestruct (H1 with "HL") as "#H1".
    iDestruct (H2 with "HL") as "#H2".
    iClear "∗". iIntros "!> #HE". iApply guards_transitive. iSplitL "H1".
    { by iApply "H1". } by iApply "H2".
  Qed.

  Global Instance lctx_lft_incl_proper :
    Proper (lctx_lft_eq ==> lctx_lft_eq ==> iff) lctx_lft_incl.
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance lctx_lft_eq_equivalence : Equivalence lctx_lft_eq.
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.
  
  Lemma lft_incl_static κ : ⊢ κ ⊑ static.
  Proof. Admitted.

  Lemma lctx_lft_incl_static κ : lctx_lft_incl κ static.
  Proof. iIntros "_ !> _". iApply lft_incl_static. Qed.
  
  Lemma lft_incl_trans κ1 κ2 κ3 : κ1 ⊑ κ2 -∗ κ2 ⊑ κ3 -∗ κ1 ⊑ κ3.
  Proof. iIntros "#A #B". iApply guards_transitive. iSplitL. { iFrame "A". } iFrame "B". Qed.
  
  Lemma lft_intersect_list_elem_of_incl κs κ : 
  κ ∈ κs → ⊢ lft_intersect_list κs ⊑ κ.
Proof. Admitted.

  Lemma lctx_lft_incl_local κ κ' κs :
    κ ⊑ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ κ'.
  Proof.
    iIntros (? Hκ'κs) "H".
    iDestruct (big_sepL_elem_of with "H") as "H"; first done.
    iDestruct "H" as (κ'') "[EQ _]". iDestruct "EQ" as %EQ.
    simpl in EQ; subst. iIntros "!> #HE".
    iApply lft_incl_trans; first by iApply llftl_incl_intersect.
    by iApply lft_intersect_list_elem_of_incl.
  Qed.

  Lemma lctx_lft_incl_local' κ κ' κ'' κs :
    κ ⊑ₗ κs ∈ L → κ' ∈ κs → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; last done. by eapply lctx_lft_incl_local. Qed.

  Lemma lctx_lft_incl_external κ κ' : κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ κ'.
  Proof.
    iIntros (?) "_!>?". by rewrite /elctx_elt_interp big_sepL_elem_of //.
  Qed.

  Lemma lctx_lft_incl_external' κ κ' κ'' :
    κ ⊑ₑ κ' ∈ E → lctx_lft_incl κ' κ'' → lctx_lft_incl κ κ''.
  Proof. intros. etrans; [|done]. by eapply lctx_lft_incl_external. Qed.

  Lemma lctx_lft_incl_intersect κ κ' κ'' :
    lctx_lft_incl κ κ' → lctx_lft_incl κ κ'' →
    lctx_lft_incl κ (κ' ⊓ κ'').
  Proof.
    iIntros (Hκ' Hκ'') "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iDestruct (Hκ'' with "HL") as "#Hκ''".
    iIntros "!> #HE". iApply llftl_incl_glb. iSplit. by iApply "Hκ'". by iApply "Hκ''".
  Qed.

  Lemma lctx_lft_incl_intersect_l κ κ' κ'' :
    lctx_lft_incl κ κ' →
    lctx_lft_incl (κ ⊓ κ'') κ'.
  Proof.
    iIntros (Hκ') "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iApply lft_incl_trans.
      by iApply llftl_incl_intersect. by iApply "Hκ'".
  Qed.

  Lemma lctx_lft_incl_intersect_r κ κ' κ'' :
    lctx_lft_incl κ κ' →
    lctx_lft_incl (κ'' ⊓ κ) κ'.
  Proof.
    iIntros (Hκ') "HL".
    iDestruct (Hκ' with "HL") as "#Hκ'".
    iIntros "!> #HE". iApply lft_incl_trans.
    Admitted. (*
      by iApply lft_intersect_incl_r. by iApply "Hκ'".
  Qed. *)

  (* Lifetime aliveness *)

  Definition lctx_lft_alive (κ : Lifetime) : Prop :=
    llctx_interp L ⊢ elctx_interp E -∗ (llctx_interp L &&{↑NllftG}&&> @[κ]).

  Lemma lctx_lft_alive_tok_list κs :
    Forall lctx_lft_alive κs →
      lctx_lft_alive ( lft_intersect_list κs ).
  Admitted.
    
  Lemma lctx_lft_alive_static : lctx_lft_alive static.
  Proof.
    iIntros "A". Admitted.

  Lemma lctx_lft_alive_intersect α β :
    lctx_lft_alive α →
    lctx_lft_alive β →
    lctx_lft_alive (α ⊓ β).
  Proof. Admitted.

  Lemma lctx_lft_alive_local κ κs:
    κ ⊑ₗ κs ∈ L → Forall lctx_lft_alive κs → lctx_lft_alive κ.
  Proof.
  Admitted.

  Lemma lctx_lft_alive_incl κ κ':
    lctx_lft_alive κ → lctx_lft_incl κ κ' → lctx_lft_alive κ'.
  Proof.
    unfold lctx_lft_alive, lctx_lft_incl.
    intros Ha Hb. iIntros "HL #HE".
    iDestruct (Hb with "HL HE") as "#Hb".
    iDestruct (Ha with "HL HE") as "Ha".
    iApply guards_transitive. iFrame "Ha". iFrame "Hb".
  Qed.

  Lemma lctx_lft_alive_external κ κ':
    κ ⊑ₑ κ' ∈ E → lctx_lft_alive κ → lctx_lft_alive κ'.
  Proof.
    intros. by eapply lctx_lft_alive_incl, lctx_lft_incl_external.
  Qed.

  (* External lifetime context satisfiability *)

  Definition elctx_sat E' : Prop :=
    llctx_interp L -∗ □ (elctx_interp E -∗ elctx_interp E').

  Lemma elctx_sat_nil : elctx_sat [].
  Proof. by iIntros "_!>_". Qed.

  Lemma elctx_sat_lft_incl E' κ κ' :
    lctx_lft_incl κ κ' → elctx_sat E' → elctx_sat (κ ⊑ₑ κ' :: E').
  Proof.
    iIntros (Hκκ' HE') "HL".
    iDestruct (Hκκ' with "HL") as "#Hincl".
    iDestruct (HE' with "HL") as "#HE'".
    iClear "∗". iIntros "!> #HE". iSplit; by [iApply "Hincl"|iApply "HE'"].
  Qed.

  Lemma elctx_sat_app E1 E2 :
    elctx_sat E1 → elctx_sat E2 → elctx_sat (E1 ++ E2).
  Proof.
    iIntros (HE1 HE2) "HL".
    iDestruct (HE1 with "HL") as "#HE1".
    iDestruct (HE2 with "HL") as "#HE2".
    iClear "∗". iIntros "!> #HE".
    iDestruct ("HE1" with "HE") as "#$".
    iApply ("HE2" with "HE").
  Qed.

  Lemma elctx_sat_refl : elctx_sat E.
  Proof. iIntros "_ !> ?". done. Qed.

  Lemma elctx_sat_head E' κ κ' :
    elctx_sat (κ ⊑ₑ κ' :: E') → lctx_lft_incl κ κ'.
  Proof.
    iIntros (InE') "L". iDestruct (InE' with "L") as "#InE'"=>/=.
    iIntros "!> #E". iDestruct ("InE'" with "E") as "[$ _]".
  Qed.
  Lemma elctx_sat_tail E' e :
    elctx_sat (e :: E') → elctx_sat E'.
  Proof.
    iIntros (eE') "L". iDestruct (eE' with "L") as "#eE'"=>/=.
    iIntros "!> #E". iDestruct ("eE'" with "E") as "[_ $]".
  Qed.

  Lemma elctx_sat_app_l E₀ E₁ :
    elctx_sat (E₀ ++ E₁) → elctx_sat E₀.
  Proof.
    iIntros (E₀E₁) "L". iDestruct (E₀E₁ with "L") as "#E₀E₁".
    iIntros "!> #E". rewrite elctx_interp_app.
    iDestruct ("E₀E₁" with "E") as "[$ _]".
  Qed.
  Lemma elctx_sat_app_r E₀ E₁ :
    elctx_sat (E₀ ++ E₁) → elctx_sat E₁.
  Proof.
    iIntros (E₀E₁) "L". iDestruct (E₀E₁ with "L") as "#E₀E₁".
    iIntros "!> #E". rewrite elctx_interp_app.
    iDestruct ("E₀E₁" with "E") as "[_ $]".
  Qed.
End lft_contexts.

Arguments lctx_lft_incl {_ _ _} _ _ _ _.
Arguments lctx_lft_eq {_ _ _} _ _ _ _.
Arguments lctx_lft_alive {_ _ _} _ _ _.
Arguments elctx_sat {_ _ _} _ _ _.
Arguments lctx_lft_incl_incl {_ _ _ _ _} _ _.
(*Arguments lctx_lft_alive_tok {_ _ _ _ _} _ _ _.*)

Lemma elctx_sat_submseteq `{!invGS Σ, !lifetime_internals_ra.llft_logicGS Σ} E E' L :
  E' ⊆+ E → elctx_sat E L E'.
Proof. iIntros (HE') "_ !> H". by iApply big_sepL_submseteq. Qed.

Global Hint Resolve
     lctx_lft_incl_refl lctx_lft_incl_static lctx_lft_alive_intersect lctx_lft_incl_local'
     lctx_lft_incl_external' lctx_lft_incl_intersect
     lctx_lft_incl_intersect_l lctx_lft_incl_intersect_r
     lctx_lft_alive_static lctx_lft_alive_local lctx_lft_alive_external
     elctx_sat_nil elctx_sat_lft_incl elctx_sat_app elctx_sat_refl
  : lrust_typing.

Global Hint Resolve elctx_sat_submseteq | 100 : lrust_typing.

Global Hint Opaque elctx_sat lctx_lft_alive lctx_lft_incl : lrust_typing.
