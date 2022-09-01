From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import primitive_laws notation.
From iris.prelude Require Import options.

Structure lock Σ `{!heapGS Σ} := Lock {
  (** * Operations *)
  newlock : val;
  acquire : val;
  release : val;
  (** * Predicates *)
  (** [name] is used to associate locked with [is_lock] *)
  name : Type;
  (** No namespace [N] parameter because we only expose program specs, which
  anyway have the full mask. *)
  is_lock (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (** * General properties of the predicates *)
  is_lock_ne γ lk : Contractive (is_lock γ lk);
  is_lock_persistent γ lk R : Persistent (is_lock γ lk R);
  is_lock_iff γ lk R1 R2 :
    is_lock γ lk R1 -∗ ▷ □ (R1 ↔ R2) -∗ is_lock γ lk R2;
  locked_timeless γ : Timeless (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (** * Program specs *)
  newlock_spec (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}};
  acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}};
  release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}
}.

Global Arguments newlock {_ _} _.
Global Arguments acquire {_ _} _.
Global Arguments release {_ _} _.
Global Arguments is_lock {_ _} _ _ _ _.
Global Arguments locked {_ _} _ _.

Global Existing Instances is_lock_ne is_lock_persistent locked_timeless.

Global Instance is_lock_proper Σ `{!heapGS Σ} (L: lock Σ) γ lk:
  Proper ((≡) ==> (≡)) (is_lock L γ lk) := ne_proper _.
