From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export derived_laws.
From iris.heap_lang Require Import notation proofmode.
From iris.prelude Require Import options.

(** A general logically atomic interface for a heap. *)
Class atomic_heap {Σ} `{!heapGS Σ} := AtomicHeap {
  (* -- operations -- *)
  alloc : val;
  free : val;
  load : val;
  store : val;
  cmpxchg : val;
  (* -- predicates -- *)
  mapsto (l : loc) (dq: dfrac) (v : val) : iProp Σ;
  (* -- mapsto properties -- *)
  mapsto_timeless l q v :> Timeless (mapsto l q v);
  mapsto_fractional l v :> Fractional (λ (q : Qp), mapsto l (DfracOwn q) v);
  mapsto_persistent l v :> Persistent (mapsto l DfracDiscarded v);
  mapsto_as_fractional l q v :>
    AsFractional (mapsto l (DfracOwn q) v) (λ q, mapsto l (DfracOwn q) v) q;
  mapsto_agree l dq1 dq2 v1 v2 : mapsto l dq1 v1 -∗ mapsto l dq2 v2 -∗ ⌜v1 = v2⌝;
  mapsto_persist l dq v : mapsto l dq v ==∗ mapsto l DfracDiscarded v;
  (* -- operation specs -- *)
  alloc_spec (v : val) :
    {{{ True }}} alloc v {{{ l, RET #l; mapsto l (DfracOwn 1) v }}};
  free_spec (l : loc) (v : val) :
    {{{ mapsto l (DfracOwn 1) v }}} free #l {{{ l, RET #l; True }}};
  load_spec (l : loc) :
    ⊢ <<< ∀ (v : val) q, mapsto l q v >>> load #l @ ⊤ <<< mapsto l q v, RET v >>>;
  store_spec (l : loc) (w : val) :
    ⊢ <<< ∀ v, mapsto l (DfracOwn 1) v >>> store #l w @ ⊤
      <<< mapsto l (DfracOwn 1) w, RET #() >>>;
  (* This spec is slightly weaker than it could be: It is sufficient for [w1]
  *or* [v] to be unboxed.  However, by writing it this way the [val_is_unboxed]
  is outside the atomic triple, which makes it much easier to use -- and the
  spec is still good enough for all our applications.
  The postcondition deliberately does not use [bool_decide] so that users can
  [destruct (decide (a = b))] and it will simplify in both places. *)
  cmpxchg_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    ⊢ <<< ∀ v, mapsto l (DfracOwn 1) v >>> cmpxchg #l w1 w2 @ ⊤
      <<< if decide (v = w1) then mapsto l (DfracOwn 1) w2 else mapsto l (DfracOwn 1) v,
        RET (v, #if decide (v = w1) then true else false) >>>;
}.
Global Arguments atomic_heap _ {_}.

(** Notation for heap primitives, in a module so you can import it separately. *)
(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Module notation.
  Notation "l ↦{ dq } v" := (mapsto l dq v)
    (at level 20, format "l  ↦{ dq }  v") : bi_scope.
  Notation "l ↦□ v" := (mapsto l DfracDiscarded v)
    (at level 20, format "l  ↦□  v") : bi_scope.
  Notation "l ↦{# q } v" := (mapsto l (DfracOwn q) v)
    (at level 20, format "l  ↦{# q }  v") : bi_scope.
  Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
    (at level 20, format "l  ↦  v") : bi_scope.

  Notation "'ref' e" := (alloc e) : expr_scope.
  Notation "! e" := (load e) : expr_scope.
  Notation "e1 <- e2" := (store e1 e2) : expr_scope.

  Notation CAS e1 e2 e3 := (Snd (cmpxchg e1 e2 e3)).

End notation.

Section derived.
  Context `{!heapGS Σ, !atomic_heap Σ}.

  Import notation.

  Lemma cas_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    ⊢ <<< ∀ v, mapsto l (DfracOwn 1) v >>> CAS #l w1 w2 @ ⊤
    <<< if decide (v = w1) then mapsto l (DfracOwn 1) w2 else mapsto l (DfracOwn 1) v,
        RET #if decide (v = w1) then true else false >>>.
  Proof.
    iIntros (? Φ) "AU". awp_apply cmpxchg_spec; first done.
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (v) "H↦". iAaccIntro with "H↦"; first by eauto with iFrame.
    iIntros "$ !> HΦ !>". wp_pures. done.
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
  Context `{!heapGS Σ}.

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
    ⊢ <<< ∀ (v : val) q, l ↦{q} v >>> primitive_load #l @ ⊤
    <<< l ↦{q} v, RET v >>>.
  Proof.
    iIntros (Φ) "AU". wp_lam.
    iMod "AU" as (v q) "[H↦ [_ Hclose]]".
    wp_load. iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  Lemma primitive_store_spec (l : loc) (w : val) :
    ⊢ <<< ∀ v, l ↦ v >>> primitive_store #l w @ ⊤
    <<< l ↦ w, RET #() >>>.
  Proof.
    iIntros (Φ) "AU". wp_lam. wp_let.
    iMod "AU" as (v) "[H↦ [_ Hclose]]".
    wp_store. iMod ("Hclose" with "H↦") as "HΦ". done.
  Qed.

  Lemma primitive_cmpxchg_spec (l : loc) (w1 w2 : val) :
    val_is_unboxed w1 →
    ⊢ <<< ∀ (v : val), l ↦ v >>>
      primitive_cmpxchg #l w1 w2 @ ⊤
    <<< if decide (v = w1) then l ↦ w2 else l ↦ v,
        RET (v, #if decide (v = w1) then true else false) >>>.
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
Definition primitive_atomic_heap `{!heapGS Σ} : atomic_heap Σ :=
  {| alloc_spec := primitive_alloc_spec;
     free_spec := primitive_free_spec;
     load_spec := primitive_load_spec;
     store_spec := primitive_store_spec;
     cmpxchg_spec := primitive_cmpxchg_spec;
     mapsto_persist := primitive_laws.mapsto_persist;
     mapsto_agree := primitive_laws.mapsto_agree |}.
