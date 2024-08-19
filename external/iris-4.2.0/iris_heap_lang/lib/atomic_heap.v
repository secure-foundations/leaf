From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.

(** A general logically atomic interface for a heap. All parameters are
implicit, since it is expected that there is only one [heapGS_gen] in scope that
could possibly apply. For example:
  
  Context `{!heapGS_gen hlc Σ, !atomic_heap}.

Or, for libraries that require later credits:

  Context `{!heapGS Σ, !atomic_heap}.

Only one instance of this class should ever be in scope. To write a library that
is generic over the lock, just add a [`{!atomic_heap}] implicit parameter around
the code and [`{!atomic_heapGS Σ}] around the proofs. To use a particular atomic
heap instance, use [Local Existing Instance <atomic_heap instance>].

When writing an instance of this class, please take care not to shadow the class
projections (e.g., either use [Local Definition alloc] or avoid the name [alloc]
altogether), and do not register an instance -- just make it a [Definition] that
others can register later.
*)
Class atomic_heap := AtomicHeap {
  (* -- operations -- *)
  alloc : val;
  free : val;
  load : val;
  store : val;
  cmpxchg : val;
  (** * Ghost state *)
  (** The assumptions about [Σ], and the singleton [gname]s (if needed) *)
  atomic_heapGS : gFunctors → Type;
  (* -- predicates -- *)
  pointsto `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (dq: dfrac) (v : val) : iProp Σ;
  (* -- pointsto properties -- *)
  #[global] pointsto_timeless `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l q v ::
    Timeless (pointsto (H:=H) l q v);
  #[global] pointsto_fractional `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l v ::
    Fractional (λ (q : Qp), pointsto (H:=H) l (DfracOwn q) v);
  #[global] pointsto_persistent `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l v ::
    Persistent (pointsto (H:=H) l DfracDiscarded v);
  #[global] pointsto_as_fractional `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l q v ::
    AsFractional (pointsto (H:=H) l (DfracOwn q) v) (λ q, pointsto (H:=H) l (DfracOwn q) v) q;
  pointsto_agree `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l dq1 dq2 v1 v2 :
    pointsto (H:=H) l dq1 v1 -∗ pointsto (H:=H) l dq2 v2 -∗ ⌜v1 = v2⌝;
  pointsto_persist `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} l dq v :
    pointsto (H:=H) l dq v ==∗ pointsto (H:=H) l DfracDiscarded v;
  (* -- operation specs -- *)
  alloc_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (v : val) :
    {{{ True }}} alloc v {{{ l, RET #l; pointsto (H:=H) l (DfracOwn 1) v }}};
  free_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (v : val) :
    {{{ pointsto (H:=H) l (DfracOwn 1) v }}} free #l {{{ l, RET #l; True }}};
  load_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) :
    ⊢ <<{ ∀∀ (v : val) q, pointsto (H:=H) l q v }>>
        load #l @ ∅
      <<{ pointsto (H:=H) l q v | RET v }>>;
  store_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (w : val) :
    ⊢ <<{ ∀∀ v, pointsto (H:=H) l (DfracOwn 1) v }>> store #l w @ ∅
      <<{ pointsto (H:=H) l (DfracOwn 1) w | RET #() }>>;
  (* This spec is slightly weaker than it could be: It is sufficient for [w1]
  *or* [v] to be unboxed.  However, by writing it this way the [val_is_unboxed]
  is outside the atomic triple, which makes it much easier to use -- and the
  spec is still good enough for all our applications.
  The postcondition deliberately does not use [bool_decide] so that users can
  [destruct (decide (a = b))] and it will simplify in both places. *)
  cmpxchg_spec `{!heapGS_gen hlc Σ} {H : atomic_heapGS Σ} (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    ⊢ <<{ ∀∀ v, pointsto (H:=H) l (DfracOwn 1) v }>> cmpxchg #l w1 w2 @ ∅
      <<{ if decide (v = w1)
          then pointsto (H:=H) l (DfracOwn 1) w2 else pointsto (H:=H) l (DfracOwn 1) v
        | RET (v, #if decide (v = w1) then true else false) }>>;
}.

Global Arguments alloc : simpl never.
Global Arguments free : simpl never.
Global Arguments load : simpl never.
Global Arguments store : simpl never.
Global Arguments cmpxchg : simpl never.
Global Arguments pointsto : simpl never.

Existing Class atomic_heapGS.
Global Hint Mode atomic_heapGS + + : typeclass_instances.
Global Hint Extern 0 (atomic_heapGS _) => progress simpl : typeclass_instances.

Local Notation CAS e1 e2 e3 := (Snd (cmpxchg e1 e2 e3)).

Definition faa_atomic `{!atomic_heap} : val :=
  rec: "faa" "l" "n" :=
    let: "m" := load "l" in
    if: CAS "l" "m" ("m" + "n") then "m" else "faa" "l" "n".

(** Notation for heap primitives, in a module so you can import it separately. *)
Module notation.
  Notation "l ↦ dq v" := (pointsto l dq v)
    (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

  Notation "'ref' e" := (alloc e) : expr_scope.
  Notation "! e" := (load e) : expr_scope.
  Notation "e1 <- e2" := (store e1 e2) : expr_scope.

  Notation CAS e1 e2 e3 := (Snd (cmpxchg e1 e2 e3)).
  Notation FAA e1 e2 := (faa_atomic e1 e2).
End notation.

Section derived.
  Context `{!heapGS_gen hlc Σ, !atomic_heap, !atomic_heapGS Σ}.

  Import notation.

  Lemma cas_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    ⊢ <<{ ∀∀ v, pointsto l (DfracOwn 1) v }>>
      CAS #l w1 w2 @ ∅
    <<{ if decide (v = w1)
        then pointsto l (DfracOwn 1) w2 else pointsto l (DfracOwn 1) v
      | RET #if decide (v = w1) then true else false }>>.
  Proof.
    iIntros (? Φ) "AU". awp_apply cmpxchg_spec; first done.
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (v) "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "$ !> HΦ !>". wp_pures. done.
  Qed.

  Lemma faa_spec (l : loc) (i2 : Z) :
    ⊢ <<{ ∀∀ i1 : Z, pointsto l (DfracOwn 1) #i1 }>>
      FAA #l #i2 @ ∅
    <<{ pointsto l (DfracOwn 1) #(i1 + i2) | RET #i1 }>>.
  Proof.
    iIntros (Φ) "AU". rewrite /faa_atomic. iLöb as "IH".
    wp_pures. awp_apply load_spec.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (i1) "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "$ !> AU !>". wp_pures.
    awp_apply cas_spec; first done.
    iApply (aacc_aupd with "AU"); first done.
    iIntros (m) "Hl".
    iAaccIntro with "Hl"; first by eauto with iFrame.
    iIntros "Hl"; destruct (decide (#m = #i1)); simplify_eq.
    - iModIntro. iRight. iFrame. iIntros "Hpost". iModIntro. by wp_pures.
    - iModIntro. iLeft. iFrame. iIntros "AU". iModIntro. wp_pure.
      by iApply "IH".
  Qed.

End derived.

(** Proof that the primitive physical operations of heap_lang satisfy said interface. *)
Definition primitive_alloc : val :=
  λ: "v", ref "v".
Definition primitive_free : val :=
  λ: "v", Free "v".
Definition primitive_load : val :=
  λ: "l", !"l".
Definition primitive_store : val :=
  λ: "l" "x", "l" <- "x".
Definition primitive_cmpxchg : val :=
  λ: "l" "e1" "e2", CmpXchg "l" "e1" "e2".

Section proof.
  Context `{!heapGS_gen hlc Σ}.

  Lemma primitive_alloc_spec (v : val) :
    {{{ True }}} primitive_alloc v {{{ l, RET #l; l ↦ v }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_alloc l. iApply "HΦ". done.
  Qed.

  Lemma primitive_free_spec (l : loc) (v : val) :
    {{{ l ↦ v }}} primitive_free #l {{{ l, RET #l; True }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_lam. wp_free. iApply "HΦ". done.
  Qed.

  Lemma primitive_load_spec (l : loc) :
    ⊢ <<{ ∀∀ (v : val) q, l ↦{q} v }>> primitive_load #l @ ∅
      <<{ l ↦{q} v | RET v }>>.
  Proof.
    iIntros (Φ) "AU". wp_lam.
    iMod "AU" as (v q) "[H↦ [_ Hclose]]".
    wp_load. iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  Lemma primitive_store_spec (l : loc) (w : val) :
    ⊢ <<{ ∀∀ v, l ↦ v }>> primitive_store #l w @ ∅
      <<{ l ↦ w | RET #() }>>.
  Proof.
    iIntros (Φ) "AU". wp_lam. wp_let.
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    wp_store. iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  Lemma primitive_cmpxchg_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    ⊢ <<{ ∀∀ (v : val), l ↦ v }>>
      primitive_cmpxchg #l w1 w2 @ ∅
    <<{ if decide (v = w1) then l ↦ w2 else l ↦ v
      | RET (v, #if decide (v = w1) then true else false) }>>.
  Proof.
    iIntros (? Φ) "AU". wp_lam. wp_pures.
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    destruct (decide (v = w1)) as [Heq|Hne];
      [wp_cmpxchg_suc|wp_cmpxchg_fail];
    iMod ("Hclose" with "H↦") as "HΦ"; done.
  Qed.
End proof.

(* NOT an instance because users should choose explicitly to use it
     (using [Explicit Instance]). *)
Definition primitive_atomic_heap : atomic_heap :=
  {| atomic_heapGS _ := TCTrue;
     alloc_spec _ _ _ _ := primitive_alloc_spec;
     free_spec _ _ _ _ := primitive_free_spec;
     load_spec _ _ _ _ := primitive_load_spec;
     store_spec _ _ _ _ := primitive_store_spec;
     cmpxchg_spec _ _ _ _ := primitive_cmpxchg_spec;
     pointsto_persist _ _ _ _ := primitive_laws.pointsto_persist;
     pointsto_agree _ _ _ _ := primitive_laws.pointsto_agree |}.
