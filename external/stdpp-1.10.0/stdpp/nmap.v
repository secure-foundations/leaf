(** This files extends the implementation of finite over [positive] to finite
maps whose keys range over Coq's data type of binary naturals [N]. *)
From stdpp Require Import pmap mapset.
From stdpp Require Export prelude fin_maps.
From stdpp Require Import options.

Local Open Scope N_scope.

Record Nmap (A : Type) : Type := NMap { Nmap_0 : option A; Nmap_pos : Pmap A }.
Global Arguments Nmap_0 {_} _ : assert.
Global Arguments Nmap_pos {_} _ : assert.
Global Arguments NMap {_} _ _ : assert.

Global Instance Nmap_eq_dec `{EqDecision A} : EqDecision (Nmap A).
Proof.
 refine (λ t1 t2,
  match t1, t2 with
  | NMap x t1, NMap y t2 => cast_if_and (decide (x = y)) (decide (t1 = t2))
  end); abstract congruence.
Defined.
Global Instance Nmap_empty {A} : Empty (Nmap A) := NMap None ∅.
Global Opaque Nmap_empty.
Global Instance Nmap_lookup {A} : Lookup N A (Nmap A) := λ i t,
  match i with
  | 0 => Nmap_0 t
  | N.pos p => Nmap_pos t !! p
  end.
Global Instance Nmap_partial_alter {A} : PartialAlter N A (Nmap A) := λ f i t,
  match i, t with
  | 0, NMap o t => NMap (f o) t
  | N.pos p, NMap o t => NMap o (partial_alter f p t)
  end.
Global Instance Nmap_fmap: FMap Nmap := λ A B f t,
  match t with NMap o t => NMap (f <$> o) (f <$> t) end.
Global Instance Nmap_omap: OMap Nmap := λ A B f t,
  match t with NMap o t => NMap (o ≫= f) (omap f t) end.
Global Instance Nmap_merge: Merge Nmap := λ A B C f t1 t2,
  match t1, t2 with
  | NMap o1 t1, NMap o2 t2 => NMap (diag_None f o1 o2) (merge f t1 t2)
  end.
Global Instance Nmap_fold {A} : MapFold N A (Nmap A) := λ B f d t,
  match t with
  | NMap mx t =>
     map_fold (f ∘ N.pos) match mx with Some x => f 0 x d | None => d end t
  end.

Global Instance Nmap_map: FinMap N Nmap.
Proof.
  split.
  - intros ? [??] [??] H. f_equal; [apply (H 0)|].
    apply map_eq. intros i. apply (H (N.pos i)).
  - by intros ? [|?].
  - intros ? f [? t] [|i]; simpl; [done |]. apply lookup_partial_alter.
  - intros ? f [? t] [|i] [|j]; simpl; try intuition congruence.
    intros. apply lookup_partial_alter_ne. congruence.
  - intros ??? [??] []; simpl; [done|]. apply lookup_fmap.
  - intros ?? f [??] [|?]; simpl; [done|]; apply (lookup_omap f).
  - intros ??? f [??] [??] [|?]; simpl; [done|]; apply (lookup_merge f).
  - intros A B P f b Hemp Hinsert [mx t]. unfold map_fold; simpl.
    apply (map_fold_ind (λ r t, P r (NMap mx t))); clear t.
    { destruct mx as [x|]; [|done].
      replace (NMap (Some x) ∅) with (<[0:=x]> ∅ : Nmap _) by done.
      by apply Hinsert. }
    intros i x t r ??. by apply (Hinsert (N.pos i) x (NMap mx t)).
Qed.

(** * Finite sets *)
(** We construct sets of [N]s satisfying extensional equality. *)
Notation Nset := (mapset Nmap).
Global Instance Nmap_dom {A} : Dom (Nmap A) Nset := mapset_dom.
Global Instance: FinMapDom N Nmap Nset := mapset_dom_spec.
