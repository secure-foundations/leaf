From iris.base_logic.lib Require Export invariants.
From iris.bi.lib Require Export fractional.
From iris.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** A general interface for a reader-writer lock.

All parameters are implicit, since it is expected that there is only one
[heapGS_gen] in scope that could possibly apply.

Only one instance of this class should ever be in scope. To write a library that
is generic over the lock, just add a [`{!rwlock}] implicit parameter around the
code and [`{!rwlockG Σ}] around the proofs. To use a particular lock instance,
use [Local Existing Instance <rwlock instance>].

When writing an instance of this class, please take care not to shadow the class
projections (e.g., either use [Local Definition newlock] or avoid the name
[newlock] altogether), and do not register an instance -- just make it a
[Definition] that others can register later. *)
Class rwlock := RwLock {
  (** * Operations *)
  newlock : val;
  acquire_reader : val;
  release_reader : val;
  acquire_writer : val;
  release_writer : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  rwlockG : gFunctors → Type;
  (** [lock_name] is used to associate [reader_locked] and [writer_locked] with
  [is_rw_lock] *)
  lock_name : Type;
  (** * Predicates *)
  (** No namespace [N] parameter because we only expose program specs, which
  anyway have the full mask. *)
  is_rw_lock `{!heapGS_gen hlc Σ} {L : rwlockG Σ} (γ : lock_name) (lock : val) (Φ : Qp → iProp Σ) : iProp Σ;
  reader_locked `{!heapGS_gen hlc Σ} {L : rwlockG Σ} (γ : lock_name) (q : Qp) : iProp Σ;
  writer_locked `{!heapGS_gen hlc Σ} {L : rwlockG Σ} (γ : lock_name) : iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_rw_lock_persistent `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ lk Φ ::
    Persistent (is_rw_lock (L:=L) γ lk Φ);
  is_rw_lock_iff `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ lk Φ Ψ :
    is_rw_lock (L:=L) γ lk Φ -∗ ▷ □ (∀ q, Φ q ∗-∗ Ψ q) -∗ is_rw_lock (L:=L) γ lk Ψ;
  #[global] reader_locked_timeless `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ q ::
    Timeless (reader_locked (L:=L) γ q);
  #[global] writer_locked_timeless `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ ::
    Timeless (writer_locked (L:=L) γ);
  writer_locked_exclusive `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ :
    writer_locked (L:=L) γ -∗ writer_locked (L:=L) γ -∗ False;
  writer_locked_not_reader_locked `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ q :
    writer_locked (L:=L) γ -∗ reader_locked (L:=L) γ q -∗ False;
  (** * Program specs *)
  newlock_spec `{!heapGS_gen hlc Σ} {L : rwlockG Σ} (Φ : Qp → iProp Σ) `{!AsFractional P Φ 1} :
    {{{ P }}}
      newlock #()
    {{{ lk γ, RET lk; is_rw_lock (L:=L) γ lk Φ }}};
  acquire_reader_spec `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ lk Φ :
    {{{ is_rw_lock (L:=L) γ lk Φ }}}
      acquire_reader lk
    {{{ q, RET #(); reader_locked (L:=L) γ q ∗ Φ q }}};
  release_reader_spec `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ lk Φ q :
    {{{ is_rw_lock (L:=L) γ lk Φ ∗ reader_locked (L:=L) γ q ∗ Φ q }}}
      release_reader lk
    {{{ RET #(); True }}};
  acquire_writer_spec `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ lk Φ :
    {{{ is_rw_lock (L:=L) γ lk Φ }}}
      acquire_writer lk
    {{{ RET #(); writer_locked (L:=L) γ ∗ Φ 1%Qp }}};
  release_writer_spec `{!heapGS_gen hlc Σ} {L : rwlockG Σ} γ lk Φ :
    {{{ is_rw_lock (L:=L) γ lk Φ ∗ writer_locked (L:=L) γ ∗ Φ 1%Qp }}}
      release_writer lk
    {{{ RET #(); True }}};
}.

Global Arguments newlock : simpl never.
Global Arguments acquire_reader : simpl never.
Global Arguments release_reader : simpl never.
Global Arguments acquire_writer : simpl never.
Global Arguments release_writer : simpl never.
Global Arguments is_rw_lock : simpl never.
Global Arguments reader_locked : simpl never.
Global Arguments writer_locked : simpl never.

Existing Class rwlockG.
Global Hint Mode rwlockG + + : typeclass_instances.
Global Hint Extern 0 (rwlockG _) => progress simpl : typeclass_instances.

Global Instance is_rw_lock_contractive `{!heapGS_gen hlc Σ, !rwlock, !rwlockG Σ} γ lk n :
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (is_rw_lock γ lk).
Proof.
  assert (Contractive (is_rw_lock γ lk : (Qp -d> iPropO Σ) → _)) as Hcontr.
  { apply (uPred.contractive_internal_eq (M:=iResUR Σ)); iIntros (Φ1 Φ2) "#HΦ".
    rewrite discrete_fun_equivI.
    iApply plainly.prop_ext_2; iIntros "!>"; iSplit; iIntros "H";
      iApply (is_rw_lock_iff with "H");
      iIntros "!> !>" (q); iRewrite ("HΦ" $! q); auto. }
  intros Φ1 Φ2 HΦ. apply Hcontr. dist_later_intro. apply HΦ.
Qed.

Global Instance is_rw_lock_proper `{!heapGS_gen hlc Σ, !rwlock, !rwlockG Σ} γ lk :
  Proper (pointwise_relation _ (≡) ==> (≡)) (is_rw_lock γ lk).
Proof.
  intros Φ1 Φ2 HΦ. apply equiv_dist=> n. apply is_rw_lock_contractive=> q.
  dist_later_intro. apply equiv_dist, HΦ.
Qed.
