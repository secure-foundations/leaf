From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import Burrow.CpdtTactics.

From stdpp Require Import gmap.
From stdpp Require Import mapset.
From stdpp Require Import sets.
From stdpp Require Import list.
Require Import Burrow.gmap_utils.
Require Import Burrow.rollup.
Require Import Burrow.indexing.
Require Import Burrow.tactics.
Require Import Burrow.locations.
Require Import Burrow.resource_proofs.
Require Import coq_tricks.Deex.

#[refine]
Global Instance pair_tpcm (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N} : TPCM (M * N) := {
  m_valid p := match p with (m, n) => m_valid m /\ m_valid n end ;
  dot p1 p2 := match p1 with (m1, n1) => match p2 with (m2, n2) => (dot m1 m2, dot n1 n2)
                end end ;
  mov p1 p2 := match p1 with (m1, n1) => match p2 with (m2, n2) => mov m1 m2 /\ mov n1 n2
                end end ;
  unit := (unit, unit) ; 
}.
Proof.
  - intros. destruct x, y. destruct_ands. split.
      + apply valid_monotonic with (y := m0). trivial.
      + apply valid_monotonic with (y := n0). trivial.
  - split; apply unit_valid; trivial.
  - intros. destruct x. repeat (rewrite unit_dot). trivial.
  - intros. destruct x, y. rewrite tpcm_comm. f_equal. rewrite tpcm_comm. trivial.
  - intros. destruct x, y, z. rewrite tpcm_assoc. f_equal. rewrite tpcm_assoc. trivial.
  - intros. destruct x. split; apply reflex.
  - intros. destruct x, y, z. destruct_ands. split.
      + apply trans with (y := m0); trivial.
      + apply trans with (y := n0); trivial.
  - intros. destruct x, y, z. destruct_ands.
      have j := mov_monotonic m m0 m1 H H0.
      have k := mov_monotonic n n0 n1 H2 H1.
      intuition.
Defined.

Inductive InternalProduct (M: Type) (N: Type) :=
  | InternalProductC : M -> N -> InternalProduct M N.
Arguments InternalProductC {_ _}%type_scope _ _.

Global Instance iprod_eqdec M `{EqDecision M} N `{EqDecision N}
    : EqDecision (InternalProduct M N).
  Proof. unfold EqDecision. intros. solve_decision. Defined.
  
#[refine]
Global Instance iprod_tpcm (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N} : TPCM (InternalProduct M N) := {
  m_valid p := match p with InternalProductC m n => m_valid m /\ m_valid n end ;
  dot p1 p2 := match p1 with InternalProductC m1 n1 => match p2 with InternalProductC m2 n2 => InternalProductC (dot m1 m2) (dot n1 n2)
                end end ;
  mov p1 p2 := match p1 with InternalProductC m1 n1 => match p2 with InternalProductC m2 n2 => mov m1 m2 /\ mov n1 n2
                end end ;
  unit := InternalProductC unit unit ;
}.
Proof.
  - intros. destruct x, y. destruct_ands. split.
      + apply valid_monotonic with (y := m0). trivial.
      + apply valid_monotonic with (y := n0). trivial.
  - split; apply unit_valid; trivial.
  - intros. destruct x. repeat (rewrite unit_dot). trivial.
  - intros. destruct x, y. rewrite tpcm_comm. f_equal. rewrite tpcm_comm. trivial.
  - intros. destruct x, y, z. rewrite tpcm_assoc. f_equal. rewrite tpcm_assoc. trivial.
  - intros. destruct x. split; apply reflex.
  - intros. destruct x, y, z. destruct_ands. split.
      + apply trans with (y := m0); trivial.
      + apply trans with (y := n0); trivial.
  - intros. destruct x, y, z. destruct_ands.
      have j := mov_monotonic m m0 m1 H H0.
      have k := mov_monotonic n n0 n1 H2 H1.
      intuition.
Defined.

Class TPCMEmbed (M: Type) (B: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B} := {
  embed: M -> B ;
  eproject: B -> M ;
  
  valid_embed: ∀ a , m_valid a -> m_valid (embed a) ;
  valid_eproject: ∀ a , m_valid a -> m_valid (eproject a) ;
  eproject_dot: ∀ a b , dot (eproject a) (eproject b) = eproject (dot a b) ;
  embed_dot: ∀ a b , dot (embed a) (embed b) = embed (dot a b) ;
  mov_embed: ∀ a b , mov a b -> mov (embed a) (embed b) ;
  mov_eproject: ∀ a b , mov a b -> mov (eproject a) (eproject b) ;
  unit_embed: embed unit = unit ;
  eproject_embed : ∀ a , eproject (embed a) = a ;
}.

#[refine]
Global Instance embed_transitive (M N P : Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
    `{!EqDecision P} `{!TPCM P}
    (m_embed: TPCMEmbed M N)
    (n_embed: TPCMEmbed N P)
    : TPCMEmbed M P := {
  embed := λ m , embed (embed m) ;
  eproject := λ p , eproject (eproject p) ;
}.
  - intros. apply valid_embed. apply valid_embed. trivial.
  - intros. apply valid_eproject. apply valid_eproject. trivial.
  - intros. rewrite eproject_dot. rewrite eproject_dot. trivial.
  - intros. rewrite embed_dot. rewrite embed_dot. trivial.
  - intros. apply mov_embed. apply mov_embed. trivial.
  - intros. apply mov_eproject. apply mov_eproject. trivial.
  - intros. rewrite unit_embed. apply unit_embed.
  - intros. rewrite eproject_embed. rewrite eproject_embed. trivial.
Qed.
    
Global Remove Hints embed_transitive : typeclass_instances.


Definition refinement_embed_src R M B
    `{!EqDecision R} `{!TPCM R}
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B}
    `{!TPCMEmbed R B} (ref: Refinement R M) : Refinement B M.
Proof. refine ({|
  rel_defined := λ b , m_valid b /\ rel_defined R M ref (eproject b) ;
  rel := λ b , (rel R M ref (eproject b)) ;
  rel_valid_left := _ ;
  rel_defined_unit := _ ;
  rel_unit := _ ;
  mov_refines := _ ;
|}).
 - intros. destruct_ands. trivial.
 - split.
    + apply unit_valid.
    + rewrite <- unit_embed. rewrite eproject_embed. apply rel_defined_unit.
 - rewrite <- unit_embed. rewrite eproject_embed. rewrite rel_unit. trivial.
 - intros. destruct_ands. repeat split.
    + rewrite <- unit_dot in H0.
      have h := mov_monotonic b b' unit H H0.
      destruct_ands. rewrite unit_dot in H2. trivial.
    + assert (mov (eproject b) (eproject b')) as me by (apply mov_eproject; trivial).
      apply (mov_refines _ _ _ (eproject b)); trivial.
    + assert (mov (eproject b) (eproject b')) as me by (apply mov_eproject; trivial).
      apply (mov_refines _ _ _ (eproject b)); trivial.
Defined.

Definition refinement_embed_dst R M B
    `{!EqDecision R} `{!TPCM R}
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B}
    `{!TPCMEmbed M B} (ref: Refinement R M) : Refinement R B.
Proof. refine ({|
  rel_defined := λ r , rel_defined R M ref r ;
  rel := λ r , embed (rel R M ref r) ;
  rel_valid_left := _ ;
  rel_defined_unit := _ ;
  rel_unit := _ ;
  mov_refines := _ ;
|}).
 - intros. apply (rel_valid_left R M ref r H).
 - apply rel_defined_unit.
 - rewrite rel_unit. apply unit_embed.
 - intros. split.
   + apply mov_refines with (b := b); trivial.
   + apply mov_embed. apply mov_refines with (b := b); trivial.
Qed.

#[refine]
Global Instance tpcm_embed_self (M: Type)
    `{!EqDecision M} `{!TPCM M}
  : TPCMEmbed M M := {
    embed := λ m , m ;
    eproject := λ m , m ;
}.
Proof.
  - intro. trivial.
  - intros. trivial.
  - intros. trivial.
  - intros. trivial.
  - intros. trivial.
  - intros. trivial.
  - intros. trivial.
  - intros. trivial.
Qed.

#[refine]
Global Instance iprod_tpcm_embed_left (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed M (InternalProduct M N) := {
    embed := λ m , InternalProductC m unit ;
    eproject := λ p , match p with InternalProductC m _ => m end ;
}.
Proof.
  - intros. split; trivial. apply unit_valid.
  - intros. destruct a.
    unfold m_valid in H. unfold iprod_tpcm in H. destruct_ands. trivial.
  - intros. destruct a, b. unfold dot. unfold iprod_tpcm. trivial.
  - intros. unfold dot. unfold iprod_tpcm. f_equal. apply unit_dot.
  - intros. unfold mov, iprod_tpcm. split; trivial. apply reflex.
  - intros. destruct a, b. unfold mov, iprod_tpcm in H. destruct_ands; trivial.
  - unfold unit at 3. unfold iprod_tpcm. trivial.
  - trivial.
Defined.

Global Remove Hints iprod_tpcm_embed_left : typeclass_instances.

#[refine]
Global Instance iprod_tpcm_embed_right (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed N (InternalProduct M N) := {
    embed := λ n , InternalProductC unit n ;
    eproject := λ p , match p with InternalProductC _ n => n end ;
}.
Proof.
  - intros. split; trivial. apply unit_valid.
  - intros. destruct a.
    unfold m_valid in H. unfold iprod_tpcm in H. destruct_ands. trivial.
  - intros. destruct a, b. unfold dot. unfold iprod_tpcm. trivial.
  - intros. unfold dot. unfold iprod_tpcm. f_equal. apply unit_dot.
  - intros. unfold mov, iprod_tpcm. split; trivial. apply reflex.
  - intros. destruct a, b. unfold mov, iprod_tpcm in H. destruct_ands; trivial.
  - unfold unit at 3. unfold iprod_tpcm. trivial.
  - trivial.
Defined.

Global Remove Hints iprod_tpcm_embed_right : typeclass_instances.

Definition ic_wf M `{!EqDecision M} `{!TPCM M} (ic_obj: gmap nat M) :=
  bool_decide (map_Forall (λ _ m, m ≠ unit) ic_obj).

Record InfiniteCopies M `{!EqDecision M} `{!TPCM M} := {
  ic_obj : gmap nat M ;
  ic_prf : ic_wf M ic_obj  ;
}.
Global Arguments ic_obj {M}%type_scope {EqDecision0 TPCM0} _.

Lemma ic_eq {M} `{!EqDecision M} `{!TPCM M} (ic1 ic2 : InfiniteCopies M)
    : ic1 = ic2 <-> ic_obj ic1 = ic_obj ic2.
Proof.
  split; [by intros ->|intros]. destruct ic1, ic2. simplify_eq/=.
  f_equal; apply proof_irrel.
Qed.

Global Instance ic_eq_dec {M} `{!EqDecision M} `{!TPCM M} : EqDecision (InfiniteCopies M). 
Proof.
 refine (λ m1 m2, cast_if (decide (ic_obj m1 = ic_obj m2)));
  abstract (by rewrite ic_eq).
Defined.

Lemma elem_ne_unit_of_ic_wf {M} `{!EqDecision M} `{!TPCM M} (ic_obj: gmap nat M) i
  (is_wf: ic_wf M ic_obj)
  : match ic_obj !! i with
    | Some x => x ≠ unit
    | None => True
  end.
Proof.
  unfold ic_wf in is_wf.
  generalize is_wf.
  rewrite bool_decide_spec.
  unfold map_Forall. intros.
  have h := H i.
  destruct (ic_obj !! i); trivial.
  apply h. trivial. Qed.

Definition ic_dot {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M) : InfiniteCopies M.
Proof.
refine ({|
  ic_obj := merge (λ x y , match x, y with
      | None, None => None
      | Some x, None => Some x
      | None, Some x => Some x
      | Some x, Some y => if decide (dot x y = unit) then None else Some (dot x y)
      end
  ) (ic_obj a) (ic_obj b) ;
  ic_prf := _ ;
|}).
 - unfold ic_wf.
    rewrite bool_decide_spec.
    unfold map_Forall. intros.
    rewrite lookup_merge in H.
    destruct a, b.
    unfold ic_obj in H.
    unfold diag_None in H. 
    
    have j1 := elem_ne_unit_of_ic_wf ic_obj0 i ic_prf0.
    have j2 := elem_ne_unit_of_ic_wf ic_obj1 i ic_prf1.
    
    destruct (ic_obj0 !! i), (ic_obj1 !! i); try case_decide; intuition; crush.
Defined.

Definition ic_get {M} `{!EqDecision M} `{!TPCM M} (a: InfiniteCopies M) (i: nat) : M :=
  match ic_obj a !! i with
  | None => unit
  | Some x => x
  end.

Definition ic_unit M `{!EqDecision M} `{!TPCM M} : InfiniteCopies M.
Proof.
refine ({|
  ic_obj := empty ;
  ic_prf := _ ;
|}).
 - unfold ic_wf. rewrite bool_decide_spec. unfold map_Forall. intros.
    rewrite lookup_empty in H. discriminate. Defined.

Definition ic_mov {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M) : Prop :=
  ∀ i , mov (ic_get a i) (ic_get b i).

Lemma ic_get_ic_dot {M} `{!EqDecision M} `{!TPCM M} (x y : InfiniteCopies M) (i : nat)
  : ic_get (ic_dot x y) i = dot (ic_get x i) (ic_get y i).
Proof.
  destruct x, y.
  unfold ic_get, ic_dot, ic_obj.
  rewrite lookup_merge.
  unfold diag_None.
  destruct (ic_obj0 !! i), (ic_obj1 !! i); try case_decide; intuition; crush.
  - rewrite unit_dot. trivial.
  - rewrite unit_dot_left. trivial.
  - rewrite unit_dot. trivial.
Qed.

Lemma ic_get_ic_unit {M} `{!EqDecision M} `{!TPCM M} (i : nat)
  : ic_get (ic_unit M) i = unit.
Proof.
  unfold ic_unit, ic_get, ic_obj. rewrite lookup_empty. trivial.
Qed.

Lemma ic_extens {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M)
  : (∀ i , ic_get a i = ic_get b i) -> a = b.
Proof.
  intros. rewrite ic_eq. destruct a, b. unfold ic_obj.
  apply map_eq. intros. have h := H i. unfold ic_get in h.
  unfold ic_obj in h.
  have j1 := elem_ne_unit_of_ic_wf ic_obj0 i ic_prf0.
  have j2 := elem_ne_unit_of_ic_wf ic_obj1 i ic_prf1.
  destruct (ic_obj0 !! i), (ic_obj1 !! i); crush.
Qed.

#[refine]
Global Instance ic_tpcm (M: Type)
    `{!EqDecision M} `{!TPCM M} : TPCM (InfiniteCopies M) := {
  m_valid p := ∀ i , m_valid (ic_get p i) ;
  dot p1 p2 := ic_dot p1 p2 ;
  mov p1 p2 := ic_mov p1 p2 ;
  unit := ic_unit M ;
}.
  - intros. have h := H i. rewrite ic_get_ic_dot in h.
      apply valid_monotonic with (y0 := ic_get y i). trivial.
  - intros. rewrite ic_get_ic_unit. apply unit_valid.
  - intros. apply ic_extens. intro. rewrite ic_get_ic_dot.
      rewrite ic_get_ic_unit. apply unit_dot.
  - intros. apply ic_extens. intro. repeat (rewrite ic_get_ic_dot).
      apply tpcm_comm.
  - intros. apply ic_extens. intro. repeat (rewrite ic_get_ic_dot).
      apply tpcm_assoc.
  - intros. unfold ic_mov. intros. apply reflex.
  - intros. unfold ic_mov in *. intros.
      have j1 := H i. have j2:= H0 i. apply trans with (y0 := ic_get y i); trivial.
  - intros. unfold ic_mov in H. split.
    + intro.
      have j1 := H i. have j2 := H0 i.
      rewrite ic_get_ic_dot.
      rewrite ic_get_ic_dot in j2.
      apply mov_monotonic with (x0 := ic_get x i); trivial.
    + unfold ic_mov. intro.
      have j1 := H i. have j2 := H0 i.
      rewrite ic_get_ic_dot.
      rewrite ic_get_ic_dot.
      rewrite ic_get_ic_dot in j2.
      apply mov_monotonic with (x0 := ic_get x i); trivial.
Defined.

(*Definition gmap_key_map `{!EqDecision K, !Countable K} `{!EqDecision L, !Countable L} {V}
    (fn: K -> L) (m: gmap K V) : gmap L V. Admitted.*)
    
Definition ic_key_opt_map `{!EqDecision M} `{!TPCM M}
    (fn: nat -> option nat) (m: InfiniteCopies M) : InfiniteCopies M. Admitted.

Definition ic_key_map `{!EqDecision M} `{!TPCM M}
    (fn: nat -> nat) (m: InfiniteCopies M) : InfiniteCopies M :=
  ic_key_opt_map (λ n , Some (fn n)) m.

Definition ic_pair {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M) :=
  dot (ic_key_map (λ n , 2*n) a) (ic_key_map (λ n, 2*n + 1) b).

Inductive Parity :=
| Even : nat -> Parity
| Odd : nat -> Parity.

Definition parity (n: nat) : Parity. Admitted.
Definition even_get (n: nat) : option nat :=
    match parity n with Even k => Some k | Odd _ => None end.
Definition odd_get (n: nat) : option nat :=
    match parity n with Odd k => Some k | Even _ => None end.
    
Lemma parity_2i (i: nat) : parity (2*i) = Even i. Admitted.
Lemma parity_2i_1 (i: nat) : parity (2*i + 1) = Odd i. Admitted.
Lemma even_or_odd (i: nat) : (∃ k , i = 2*k) \/ (∃ k , i = 2*k + 1). Admitted.
  
Definition ic_left {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M) :=
  (ic_key_opt_map even_get a).
  
Definition ic_right {M} `{!EqDecision M} `{!TPCM M} (b : InfiniteCopies M) :=
  (ic_key_opt_map odd_get b).

Lemma ic_get_ic_left {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M) (i: nat)
  : ic_get (ic_left a) i = ic_get a (2 * i). Admitted.
  
Lemma ic_get_ic_right {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M) (i: nat)
  : ic_get (ic_right a) i = ic_get a (2 * i + 1). Admitted.
  
Lemma ic_get_ic_pair {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M) (i: nat)
  : ic_get (ic_pair a b) i = match parity i with
    | Even k => ic_get a k
    | Odd k => ic_get b k
    end. Admitted.

Lemma ic_left_ic_pair {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M)
  : ic_left (ic_pair a b) = a.
Proof.
  apply ic_extens. intros.
  rewrite ic_get_ic_left.
  rewrite ic_get_ic_pair.
  rewrite parity_2i. trivial.
Qed.

Lemma ic_right_ic_pair {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M)
  : ic_right (ic_pair a b) = b.
Proof.
  apply ic_extens. intros.
  rewrite ic_get_ic_right.
  rewrite ic_get_ic_pair.
  rewrite parity_2i_1. trivial.
Qed.

Lemma ic_pair_ic_left_ic_right {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M)
  : ic_pair (ic_left a) (ic_right a) = a.
Proof.
  apply ic_extens. intros.
  rewrite ic_get_ic_pair.
  have j := even_or_odd i. destruct j.
  - deex. subst i. rewrite parity_2i. rewrite ic_get_ic_left. trivial.
  - deex. subst i. rewrite parity_2i_1. rewrite ic_get_ic_right. trivial.
Qed.

Lemma ic_left_unit {M} `{!EqDecision M} `{!TPCM M}
  : ic_left unit = unit.
Proof.
  apply ic_extens. intros. rewrite ic_get_ic_left.
  rewrite ic_get_ic_unit. rewrite ic_get_ic_unit. trivial.
Qed.

Lemma ic_right_unit {M} `{!EqDecision M} `{!TPCM M}
  : ic_right unit = unit.
Proof.
  apply ic_extens. intros. rewrite ic_get_ic_right.
  rewrite ic_get_ic_unit. rewrite ic_get_ic_unit. trivial.
Qed.

Definition refinement_left 
    `{!EqDecision M} `{!TPCM M}
    : Refinement (InfiniteCopies M) (InfiniteCopies M).
Proof. refine ({|
  rel_defined := m_valid ;
  rel := ic_left ;
  rel_valid_left := _ ;
  rel_defined_unit := _ ;
  rel_unit := _ ;
  mov_refines := _ ;
|}).
 - intros. trivial.
 - intros. apply unit_valid.
 - apply ic_left_unit.
 - intros. split.
    + rewrite <- unit_dot. apply mov_monotonic with (x := b); trivial.
        rewrite unit_dot. trivial.
    + unfold mov in *. unfold ic_tpcm in *. unfold ic_mov in *. intros.
        rewrite ic_get_ic_left. rewrite ic_get_ic_left.
        apply H.
Qed.

Definition refinement_right
    `{!EqDecision M} `{!TPCM M}
    : Refinement (InfiniteCopies M) (InfiniteCopies M).
Proof. refine ({|
  rel_defined := m_valid ;
  rel := ic_right ;
  rel_valid_left := _ ;
  rel_defined_unit := _ ;
  rel_unit := _ ;
  mov_refines := _ ;
|}).
 - intros. trivial.
 - intros. apply unit_valid.
 - apply ic_right_unit.
 - intros. split.
    + rewrite <- unit_dot. apply mov_monotonic with (x := b); trivial.
        rewrite unit_dot. trivial.
    + unfold mov in *. unfold ic_tpcm in *. unfold ic_mov in *. intros.
        rewrite ic_get_ic_right. rewrite ic_get_ic_right.
        apply H.
Qed.

Definition refinement_trivial
    `{!EqDecision M} `{!TPCM M}
    : Refinement M M.
    Proof. refine ({|
  rel_defined := m_valid ;
  rel := λ m, unit ;
  rel_valid_left := _ ;
  rel_defined_unit := _ ;
  rel_unit := _ ;
  mov_refines := _ ;
|}).
 - intros. trivial.
 - intros. apply unit_valid.
 - trivial.
 - intros. split.
    + rewrite <- unit_dot. apply mov_monotonic with (x := b); trivial.
        rewrite unit_dot. trivial.
    + apply reflex.
Qed.

Definition ic_singleton {M} `{!EqDecision M} `{!TPCM M} (m : M) : InfiniteCopies M.
Proof.
refine ({|
  ic_obj := if (decide (m = unit)) then empty else {[ 0 := m ]} ;
  ic_prf := _ ;
|}).
 - unfold ic_wf.
    rewrite bool_decide_spec.
    unfold map_Forall. intros.
    case_decide.
    + rewrite lookup_empty in H. discriminate.
    + have eq : Decision (i = 0) by solve_decision.
      destruct eq.
      * subst i. rewrite lookup_singleton in H. crush.
      * rewrite lookup_singleton_ne in H; crush.
Defined.

Lemma ic_get_ic_singleton {M} `{!EqDecision M} `{!TPCM M} (m : M)
  : ic_get (ic_singleton m) 0 = m.
Proof.
  unfold ic_singleton, ic_get, ic_obj. case_decide.
  - rewrite lookup_empty. symmetry. trivial.
  - rewrite lookup_singleton. trivial.
Qed.

Lemma ic_get_ic_singleton_ne {M} `{!EqDecision M} `{!TPCM M} (m : M) (i: nat)
  (ne_0: i ≠ 0) : ic_get (ic_singleton m) i = unit.
Proof.
  unfold ic_singleton, ic_get, ic_obj. case_decide.
  - rewrite lookup_empty. symmetry. trivial.
  - rewrite lookup_singleton_ne; trivial. lia.
Qed.

#[refine]
Global Instance ic_tpcm_embed (M: Type)
    `{!EqDecision M} `{!TPCM M}
  : TPCMEmbed M (InfiniteCopies M) := {
    embed := ic_singleton ;
    eproject := λ a, ic_get a 0 ;
}.
Proof.
  - intros. unfold m_valid, ic_tpcm. intro.
    have h : Decision (i = 0) by solve_decision. destruct h.
    + subst. rewrite ic_get_ic_singleton. trivial.
    + rewrite ic_get_ic_singleton_ne; trivial. apply unit_valid.
  - intros. unfold m_valid, ic_tpcm in H. have h := H 0. trivial.
  - intros. rewrite ic_get_ic_dot. trivial.
  - intros. apply ic_extens. intros. rewrite ic_get_ic_dot.
    have h : Decision (i = 0) by solve_decision. destruct h.
    + subst. repeat (rewrite ic_get_ic_singleton). trivial.
    + repeat (rewrite ic_get_ic_singleton_ne; trivial). apply unit_dot.
  - intros. unfold mov, ic_tpcm, ic_mov. intros.
    have h : Decision (i = 0) by solve_decision. destruct h.
    + subst. rewrite ic_get_ic_singleton. rewrite ic_get_ic_singleton. trivial.
    + rewrite ic_get_ic_singleton_ne; trivial.
      rewrite ic_get_ic_singleton_ne; trivial.
      apply reflex.
  - intros. unfold mov, ic_tpcm, ic_mov in H. have h := H 0. trivial.
  - apply ic_extens. intros.
    have h : Decision (i = 0) by solve_decision. destruct h.
    + subst. rewrite ic_get_ic_singleton. rewrite ic_get_ic_unit. trivial.
    + rewrite ic_get_ic_singleton_ne; trivial.
  - intros. rewrite ic_get_ic_singleton. trivial.
Qed.

Lemma m_valid_ic_pair `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M)
    : m_valid a -> m_valid b -> m_valid (ic_pair a b).
Proof. intros. unfold m_valid, ic_tpcm in *. intros.
    rewrite ic_get_ic_pair. have h := even_or_odd i. destruct h.
    + deex. subst. rewrite parity_2i. apply H.
    + deex. subst. rewrite parity_2i_1. apply H0.
Qed.

Lemma m_valid_ic_left `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M)
    : m_valid a -> m_valid (ic_left a).
Proof. intros. unfold m_valid, ic_tpcm in *. intros.
    rewrite ic_get_ic_left. apply H.
Qed.

Lemma m_valid_ic_right `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M)
    : m_valid a -> m_valid (ic_right a).
Proof. intros. unfold m_valid, ic_tpcm in *. intros.
    rewrite ic_get_ic_right. apply H.
Qed.

#[refine]
Global Instance ic_tpcm_embed_two (M N B: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
    `{!EqDecision B} `{!TPCM B}
    (m_embed: TPCMEmbed M (InfiniteCopies B))
    (n_embed: TPCMEmbed N (InfiniteCopies B))
    : TPCMEmbed (M * N) (InfiniteCopies B) := {
  embed := λ p , match p with (m, n) => ic_pair (embed m) (embed n) end ;
  eproject := λ b , (eproject (ic_left b), eproject (ic_right b)) ;
}.
Proof.
  - intros. destruct a. unfold m_valid, ic_tpcm. intros. apply m_valid_ic_pair.
     + apply valid_embed. unfold m_valid, pair_tpcm in H. destruct_ands. trivial.
     + apply valid_embed. unfold m_valid, pair_tpcm in H. destruct_ands. trivial.
  - intros. unfold m_valid, pair_tpcm. split.
     + apply valid_eproject. apply m_valid_ic_left. trivial.
     + apply valid_eproject. apply m_valid_ic_right. trivial.
  - intros. unfold dot, pair_tpcm, ic_tpcm. f_equal.
     (*+ rewrite ic_left_ic_dot. apply eproject_dot.*)
  Admitted.

Global Instance ic_tpcm_embed_extend (M: Type) (B: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B}
    (m_embed: TPCMEmbed M B) : TPCMEmbed M (InfiniteCopies B) :=
      embed_transitive M B (InfiniteCopies B) m_embed (ic_tpcm_embed B).

Record RefinementEmbedding (B: Type) `{!EqDecision B} `{TPCM B} := {
  re_R: Type;
  re_M: Type;
  re_R_eqdec: EqDecision re_R;
  re_R_tpcm: TPCM re_R;
  re_M_eqdec: EqDecision re_M;
  re_M_tpcm: TPCM re_M;
  re_ref: Refinement re_R re_M;
  re_R_embed: TPCMEmbed re_R B;
  re_M_embed: TPCMEmbed re_M B;
}.

Class BurrowCtx := {
  bc_small_M: Type ;
  bc_small_RI: Type ;
  
  bc_small_M_eqdec :> EqDecision bc_small_M ;
  bc_small_M_tpcm :> TPCM bc_small_M ;
  bc_small_RI_eqdec :> EqDecision bc_small_RI ;
  bc_small_RI_countable :> Countable bc_small_RI ;
  
  bc_refs: bc_small_RI -> RefinementEmbedding bc_small_M ;
}.

Definition bc_M (𝜇: BurrowCtx) : Type := InfiniteCopies bc_small_M.

Inductive FinalRI (small_RI: Type) :=
  | FinalRILeft : FinalRI small_RI
  | FinalRIRight : FinalRI small_RI
  | FinalRITriv : FinalRI small_RI
  | FinalRINormal : small_RI -> FinalRI small_RI
.

(*Definition bc_RI (𝜇: BurrowCtx) : Type := FinalRI bc_small_RI.*)

Global Instance bc_FinalRI_eqdec (small_RI: Type) `{!EqDecision small_RI}
    : EqDecision (FinalRI small_RI).
Proof. solve_decision. Qed.

Global Instance bc_FinalRI_countable (small_RI: Type) `{!EqDecision small_RI, !Countable small_RI}
    : Countable (FinalRI small_RI).
Admitted.

Global Instance bc_refinement_index (small_M small_RI: Type)
    `{!EqDecision small_M, TPCM small_M}
    `{!EqDecision small_RI, !Countable small_RI}
    : RefinementIndex (InfiniteCopies small_M) (FinalRI small_RI).
Admitted.

Definition BurrowState (𝜇: BurrowCtx)
    := State (InfiniteCopies bc_small_M) (FinalRI bc_small_RI).

Class HasTPCM (𝜇: BurrowCtx) (M: Type) `{!EqDecision M, TPCM M}
    := { inctx_embed :> TPCMEmbed M bc_small_M }.
  
Class HasRef (𝜇: BurrowCtx) {R M: Type}
      `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
      `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
      `{r_hastpcm: !HasTPCM 𝜇 R} `{m_hastpcm: !HasTPCM 𝜇 M}
      (ref: Refinement R M)
    := {
        hasref_ri: bc_small_RI ; 
        hasref_is: (bc_refs hasref_ri) = {|
          re_R := R;
          re_M := M;
          re_R_eqdec := r_eqdec;
          re_R_tpcm := r_tpcm;
          re_M_eqdec := m_eqdec;
          re_M_tpcm := m_tpcm;
          re_ref := ref;
          re_R_embed := inctx_embed;
          re_M_embed := inctx_embed;
        |}
       }.

Definition BurrowLoc (𝜇: BurrowCtx) := Loc (FinalRI bc_small_RI).

Definition extend_loc {𝜇: BurrowCtx}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_hastpcm: !HasTPCM 𝜇 R} `{m_hastpcm: !HasTPCM 𝜇 M}
    (𝛼: nat) (ref: Refinement R M) (𝛾: BurrowLoc 𝜇)
    `{hr: !HasRef 𝜇 ref} : BurrowLoc 𝜇
    := (ExtLoc 𝛼 (FinalRINormal bc_small_RI (@hasref_ri
        𝜇 R M r_eqdec r_tpcm m_eqdec m_tpcm r_hastpcm m_hastpcm ref hr
    )) 𝛾).

Definition cross_loc {𝜇: BurrowCtx} (𝛾1 𝛾2: BurrowLoc 𝜇) := CrossLoc 𝛾1 𝛾2.

Definition live' {𝜇: BurrowCtx} {M}
    `{!EqDecision M} `{!TPCM M}
    `{!HasTPCM 𝜇 M} (loc: BurrowLoc 𝜇) (m: M) : BurrowState 𝜇
    := live loc (embed m).

Lemma live_dot_live' {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (𝛾: BurrowLoc 𝜇) (m1 m2: M)
    : live' 𝛾 m1 ⋅ live' 𝛾 m2 ≡ live' 𝛾 (dot m1 m2).
Proof.
  unfold live'. setoid_rewrite live_dot_live. rewrite embed_dot. trivial.
Qed.
    
  
