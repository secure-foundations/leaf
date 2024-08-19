From iris.algebra Require Import auth excl gmap.
From iris.base_logic.lib Require Import own invariants gen_heap.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.

(** An "invariant" location is a location that has some invariant about its
value attached to it, and that can never be deallocated explicitly by the
program.  It provides a persistent witness that will always allow reading the
location, guaranteeing that the value read will satisfy the invariant.

This is useful for data structures like RDCSS that need to read locations long
after their ownership has been passed back to the client, but do not care *what*
it is that they are reading in that case. In that extreme case, the invariant
may just be [True].

Since invariant locations cannot be deallocated, they only make sense when
modeling languages with garbage collection.  HeapLang can be used to model
either language by choosing whether or not to use the [Free] operation.  By
using a separate assertion [inv_pointsto_own] for "invariant" locations, we can
keep all the other proofs that do not need it conservative.  *)

Definition inv_heapN: namespace := nroot .@ "inv_heap".
Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

Definition inv_heap_mapUR (L V : Type) `{Countable L} : ucmra := gmapUR L $ prodR
  (optionR $ exclR $ leibnizO V)
  (agreeR (V -d> PropO)).

Definition to_inv_heap {L V : Type} `{Countable L}
    (h: gmap L (V * (V -d> PropO))) : inv_heap_mapUR L V :=
  prod_map (λ x, Excl' x) to_agree <$> h.

Class inv_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  inv_heapGpreS_inG : inG Σ (authR (inv_heap_mapUR L V))
}.
Local Existing Instance inv_heapGpreS_inG.

Class inv_heapGS (L V : Type) (Σ : gFunctors) `{Countable L} := Inv_HeapG {
  inv_heap_inG : inv_heapGpreS L V Σ;
  inv_heap_name : gname
}.
Local Existing Instance inv_heap_inG.
Global Arguments Inv_HeapG _ _ {_ _ _ _}.
Global Arguments inv_heap_name {_ _ _ _ _} _ : assert.

Definition inv_heapΣ (L V : Type) `{Countable L} : gFunctors :=
  #[ GFunctor (authR (inv_heap_mapUR L V)) ].

Global Instance subG_inv_heapGpreS (L V : Type) `{Countable L} {Σ} :
  subG (inv_heapΣ L V) Σ → inv_heapGpreS L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context {L V : Type} `{Countable L}.
  Context `{!invGS_gen hlc Σ, !gen_heapGS L V Σ, gG: !inv_heapGS L V Σ}.

  Definition inv_heap_inv_P : iProp Σ :=
    ∃ h : gmap L (V * (V -d> PropO)),
       own (inv_heap_name gG) (● to_inv_heap h) ∗
       [∗ map] l ↦ p ∈ h, ⌜p.2 p.1⌝ ∗ l ↦ p.1.

  Definition inv_heap_inv : iProp Σ := inv inv_heapN inv_heap_inv_P.

  Definition inv_pointsto_own (l : L) (v : V) (I : V → Prop) : iProp Σ :=
    own (inv_heap_name gG) (◯ {[l := (Excl' v, to_agree I) ]}).

  Definition inv_pointsto (l : L) (I : V → Prop) : iProp Σ :=
    own (inv_heap_name gG) (◯ {[l := (None, to_agree I)]}).

End definitions.

Local Notation "l '↦_' I v" := (inv_pointsto_own l v I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  v") : bi_scope.

Local Notation "l '↦_' I □" := (inv_pointsto l I%stdpp%type)
  (at level 20, I at level 9, format "l  '↦_' I  '□'") : bi_scope.

(* [inv_heap_inv] has no parameters to infer the types from, so we need to
   make them explicit. *)
Global Arguments inv_heap_inv _ _ {_ _ _ _ _ _ _}.

Global Instance: Params (@inv_pointsto_own) 8 := {}.
Global Instance: Params (@inv_pointsto) 7 := {}.

Section to_inv_heap.
  Context {L V : Type} `{Countable L}.
  Implicit Types (h : gmap L (V * (V -d> PropO))).

  Lemma to_inv_heap_valid h : ✓ to_inv_heap h.
  Proof. intros l. rewrite lookup_fmap. by case (h !! l). Qed.

  Lemma to_inv_heap_singleton l v I :
    to_inv_heap {[l := (v, I)]} =@{inv_heap_mapUR L V} {[l := (Excl' v, to_agree I)]}.
  Proof. by rewrite /to_inv_heap fmap_insert fmap_empty. Qed.

  Lemma to_inv_heap_insert l v I h :
    to_inv_heap (<[l := (v, I)]> h) = <[l := (Excl' v, to_agree I)]> (to_inv_heap h).
  Proof. by rewrite /to_inv_heap fmap_insert. Qed.

  Lemma lookup_to_inv_heap_None h l :
    h !! l = None → to_inv_heap h !! l = None.
  Proof. by rewrite /to_inv_heap lookup_fmap=> ->. Qed.

  Lemma lookup_to_inv_heap_Some h l v I :
    h !! l = Some (v, I) → to_inv_heap h !! l = Some (Excl' v, to_agree I).
  Proof. by rewrite /to_inv_heap lookup_fmap=> ->. Qed.

  Lemma lookup_to_inv_heap_Some_2 h l v' I' :
    to_inv_heap h !! l ≡ Some (v', I') →
    ∃ v I, v' = Excl' v ∧ I' ≡ to_agree I ∧ h !! l = Some (v, I).
  Proof.
    rewrite /to_inv_heap /prod_map lookup_fmap. rewrite fmap_Some_equiv.
    intros ([] & Hsome & [Heqv HeqI]); simplify_eq/=; eauto.
  Qed.
End to_inv_heap.

Lemma inv_heap_init (L V : Type) `{Countable L, !invGS_gen hlc Σ, !gen_heapGS L V Σ, !inv_heapGpreS L V Σ} E :
  ⊢ |==> ∃ _ : inv_heapGS L V Σ, |={E}=> inv_heap_inv L V.
Proof.
  iMod (own_alloc (● (to_inv_heap ∅))) as (γ) "H●".
  { rewrite auth_auth_valid. exact: to_inv_heap_valid. }
  iModIntro.
  iExists (Inv_HeapG L V γ).
  iAssert (inv_heap_inv_P (gG := Inv_HeapG L V γ)) with "[H●]" as "P".
  { iExists _. iFrame. done. }
  iApply (inv_alloc inv_heapN E inv_heap_inv_P with "P").
Qed.

Section inv_heap.
  Context {L V : Type} `{Countable L}.
  Context `{!invGS_gen hlc Σ, !gen_heapGS L V Σ, gG: !inv_heapGS L V Σ}.
  Implicit Types (l : L) (v : V) (I : V → Prop).
  Implicit Types (h : gmap L (V * (V -d> PropO))).

  (** * Helpers *)

  Lemma inv_pointsto_lookup_Some l h I :
    l ↦_I □ -∗ own (inv_heap_name gG) (● to_inv_heap h) -∗
    ⌜∃ v I', h !! l = Some (v, I') ∧ ∀ w, I w ↔ I' w ⌝.
  Proof.
    iIntros "Hl_inv H◯".
    iCombine "H◯ Hl_inv" gives %[Hincl Hvalid]%auth_both_valid_discrete.
    iPureIntro.
    move: Hincl; rewrite singleton_included_l; intros ([v' I'] & Hsome & Hincl).
    apply lookup_to_inv_heap_Some_2 in Hsome as (v'' & I'' & _ & HI & Hh).
    move: Hincl; rewrite HI Some_included_total pair_included
      to_agree_included; intros [??]; eauto.
  Qed.

  Lemma inv_pointsto_own_lookup_Some l v h I :
    l ↦_I v -∗ own (inv_heap_name gG) (● to_inv_heap h) -∗
    ⌜ ∃ I', h !! l = Some (v, I') ∧ ∀ w, I w ↔ I' w ⌝.
  Proof.
    iIntros "Hl_inv H●".
    iCombine "H● Hl_inv" gives %[Hincl Hvalid]%auth_both_valid_discrete.
    iPureIntro.
    move: Hincl; rewrite singleton_included_l; intros ([v' I'] & Hsome & Hincl).
    apply lookup_to_inv_heap_Some_2 in Hsome as (v'' & I'' & -> & HI & Hh).
    move: Hincl; rewrite HI Some_included_total pair_included
      Excl_included to_agree_included; intros [-> ?]; eauto.
  Qed.

  (** * Typeclass instances *)

  (* FIXME(Coq #6294): needs new unification
  The uses of [apply:] and [move: ..; rewrite ..] (by lack of [apply: .. in ..])
  in this file are needed because Coq's default unification algorithm fails. *)
  Global Instance inv_pointsto_own_proper l v :
    Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto_own l v).
  Proof.
    intros I1 I2 ?. rewrite /inv_pointsto_own. do 2 f_equiv.
    apply: singletonM_proper. f_equiv. by apply: to_agree_proper.
  Qed.
  Global Instance inv_pointsto_proper l :
    Proper (pointwise_relation _ iff ==> (≡)) (inv_pointsto l).
  Proof.
    intros I1 I2 ?. rewrite /inv_pointsto. do 2 f_equiv.
    apply: singletonM_proper. f_equiv. by apply: to_agree_proper.
  Qed.

  Global Instance inv_heap_inv_persistent : Persistent (inv_heap_inv L V).
  Proof. apply _. Qed.

  Global Instance inv_pointsto_persistent l I : Persistent (l ↦_I □).
  Proof. apply _. Qed.

  Global Instance inv_pointsto_timeless l I : Timeless (l ↦_I □).
  Proof. apply _. Qed.

  Global Instance inv_pointsto_own_timeless l v I : Timeless (l ↦_I v).
  Proof. apply _. Qed.

  (** * Public lemmas *)

  Lemma make_inv_pointsto l v I E :
    ↑inv_heapN ⊆ E →
    I v →
    inv_heap_inv L V -∗ l ↦ v ={E}=∗ l ↦_I v.
  Proof.
    iIntros (HN HI) "#Hinv Hl".
    iMod (inv_acc_timeless _ inv_heapN with "Hinv") as "[HP Hclose]"; first done.
    iDestruct "HP" as (h) "[H● HsepM]".
    destruct (h !! l) as [v'| ] eqn: Hlookup.
    - (* auth map contains l --> contradiction *)
      iDestruct (big_sepM_lookup with "HsepM") as "[_ Hl']"; first done.
      by iCombine "Hl Hl'" gives %[??].
    - iMod (own_update with "H●") as "[H● H◯]".
      { apply lookup_to_inv_heap_None in Hlookup.
        apply (auth_update_alloc _
          (to_inv_heap (<[l:=(v,I)]> h)) (to_inv_heap ({[l:=(v,I)]}))).
        rewrite to_inv_heap_insert to_inv_heap_singleton.
        by apply: alloc_singleton_local_update. }
      iMod ("Hclose" with "[H● HsepM Hl]").
      + iExists _.
        iDestruct (big_sepM_insert _ _ _ (_,_) with "[$HsepM $Hl]")
          as "HsepM"; auto with iFrame.
      + iModIntro. by rewrite /inv_pointsto_own to_inv_heap_singleton.
  Qed.

  Lemma inv_pointsto_own_inv l v I : l ↦_I v -∗ l ↦_I □.
  Proof.
    iApply own_mono. apply auth_frag_mono.
    rewrite singleton_included_total pair_included.
    split; [apply: ucmra_unit_least|done].
  Qed.

  (** An accessor to make use of [inv_pointsto_own].
    This opens the invariant *before* consuming [inv_pointsto_own] so that you can use
    this before opening an atomic update that provides [inv_pointsto_own]!. *)
  Lemma inv_pointsto_own_acc_strong E :
    ↑inv_heapN ⊆ E →
    inv_heap_inv L V ={E, E ∖ ↑inv_heapN}=∗ ∀ l v I, l ↦_I v -∗
      (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ==∗
        inv_pointsto_own l w I ∗ |={E ∖ ↑inv_heapN, E}=> True)).
  Proof.
    iIntros (HN) "#Hinv".
    iMod (inv_acc_timeless _ inv_heapN _ with "Hinv") as "[HP Hclose]"; first done.
    iIntros "!>" (l v I) "Hl_inv".
    iDestruct "HP" as (h) "[H● HsepM]".
    iDestruct (inv_pointsto_own_lookup_Some with "Hl_inv H●") as %(I'&?&HI').
    setoid_rewrite HI'.
    iDestruct (big_sepM_delete with "HsepM") as "[[HI Hl] HsepM]"; first done.
    iIntros "{$HI $Hl}" (w ?) "Hl".
    iMod (own_update_2 with "H● Hl_inv") as "[H● H◯]".
    { apply (auth_update _ _ (<[l := (Excl' w, to_agree I')]> (to_inv_heap h))
             {[l := (Excl' w, to_agree I)]}).
      apply: singleton_local_update.
      { by apply lookup_to_inv_heap_Some. }
      apply: prod_local_update_1. apply: option_local_update.
      apply: exclusive_local_update. done. }
    iDestruct (big_sepM_insert _ _ _ (w, I') with "[$HsepM $Hl //]") as "HsepM".
    { apply lookup_delete. }
    rewrite insert_delete_insert -to_inv_heap_insert. iIntros "!> {$H◯}".
    iApply ("Hclose" with "[H● HsepM]"). iExists _; by iFrame.
  Qed.

  (** Derive a more standard accessor. *)
  Lemma inv_pointsto_own_acc E l v I:
    ↑inv_heapN ⊆ E →
    inv_heap_inv L V -∗ l ↦_I v ={E, E ∖ ↑inv_heapN}=∗
      (⌜I v⌝ ∗ l ↦ v ∗ (∀ w, ⌜I w ⌝ -∗ l ↦ w ={E ∖ ↑inv_heapN, E}=∗ l ↦_I w)).
  Proof.
    iIntros (?) "#Hinv Hl".
    iMod (inv_pointsto_own_acc_strong with "Hinv") as "Hacc"; first done.
    iDestruct ("Hacc" with "Hl") as "(HI & Hl & Hclose)".
    iIntros "!> {$HI $Hl}" (w) "HI Hl".
    iMod ("Hclose" with "HI Hl") as "[$ $]".
  Qed.

  Lemma inv_pointsto_acc l I E :
    ↑inv_heapN ⊆ E →
    inv_heap_inv L V -∗ l ↦_I □ ={E, E ∖ ↑inv_heapN}=∗
    ∃ v, ⌜I v⌝ ∗ l ↦ v ∗ (l ↦ v ={E ∖ ↑inv_heapN, E}=∗ ⌜True⌝).
  Proof.
    iIntros (HN) "#Hinv Hl_inv".
    iMod (inv_acc_timeless _ inv_heapN _ with "Hinv") as "[HP Hclose]"; first done.
    iModIntro.
    iDestruct "HP" as (h) "[H● HsepM]".
    iDestruct (inv_pointsto_lookup_Some with "Hl_inv H●") as %(v&I'&?&HI').
    iDestruct (big_sepM_lookup_acc with "HsepM") as "[[#HI Hl] HsepM]"; first done.
    setoid_rewrite HI'.
    iExists _. iIntros "{$HI $Hl} Hl".
    iMod ("Hclose" with "[H● HsepM Hl]"); last done.
    iExists _. iFrame "H●". iApply ("HsepM" with "[$Hl //]").
  Qed.

End inv_heap.

Global Typeclasses Opaque inv_heap_inv inv_pointsto inv_pointsto_own.
