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
Require Import coq_tricks.Deex.

Print Is_true.

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

Class TPCMEmbed (M: Type) (B: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B} := {
  embed: M -> B ;
  eproject: B -> M ;
  
  valid_embed: ∀ a , m_valid a -> m_valid (embed a) ;
  valid_eproject: ∀ a , m_valid a -> m_valid (eproject a) ;
  eproject_dot: ∀ a b , dot (eproject a) (eproject b) = eproject (dot a b) ;
  mov_embed: ∀ a b , mov a b -> mov (embed a) (embed b) ;
  mov_eproject: ∀ a b , mov a b -> mov (eproject a) (eproject b) ;
  unit_embed: embed unit = unit ;
  eproject_embed : ∀ a , eproject (embed a) = a ;
}.

#[refine]
Global Instance pair_tpcm_embed_self (M: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
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
Qed.

#[refine]
Global Instance pair_tpcm_embed_left (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed M (M * N) := {
    embed := λ m , (m, unit) ;
    eproject := λ p , match p with (m, _) => m end ;
}.
Proof.
  - intros. split; trivial. apply unit_valid.
  - intros. destruct a.
    unfold m_valid in H. unfold pair_tpcm in H. destruct_ands. trivial.
  - intros. destruct a, b. unfold dot. unfold pair_tpcm. trivial.
  - intros. unfold mov, pair_tpcm. split; trivial. apply reflex.
  - intros. destruct a, b. unfold mov, pair_tpcm in H. destruct_ands; trivial.
  - unfold unit at 3. unfold pair_tpcm. trivial.
  - trivial.
Defined.

#[refine]
Global Instance pair_tpcm_embed_right (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed N (M * N) := {
    embed := λ n , (unit, n) ;
    eproject := λ p , match p with (_, n) => n end ;
}.
Proof.
  - intros. split; trivial. apply unit_valid.
  - intros. destruct a.
    unfold m_valid in H. unfold pair_tpcm in H. destruct_ands. trivial.
  - intros. destruct a, b. unfold dot. unfold pair_tpcm. trivial.
  - intros. unfold mov, pair_tpcm. split; trivial. apply reflex.
  - intros. destruct a, b. unfold mov, pair_tpcm in H. destruct_ands; trivial.
  - unfold unit at 3. unfold pair_tpcm. trivial.
  - trivial.
Defined.

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

Global Instance ic_eq_eq {M} `{!EqDecision M} `{!TPCM M} : EqDecision (InfiniteCopies M). 
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
