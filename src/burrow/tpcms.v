From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes.
From iris.prelude Require Import options.
Require Import cpdt.CpdtTactics.

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
Require Import Burrow.exchanges.
Require Import Burrow.parity.
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

Local Instance iprod_eqdec M `{EqDecision M} N `{EqDecision N}
    : EqDecision (InternalProduct M N).
  Proof. unfold EqDecision. intros. solve_decision. Defined.
  
#[refine]
Local Instance iprod_tpcm (M: Type) (N: Type)
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
  erest: B -> B ;
  
  valid_embed: ∀ a , m_valid a -> m_valid (embed a) ;
  valid_eproject: ∀ a , m_valid a -> m_valid (eproject a) ;
  eproject_dot: ∀ a b , dot (eproject a) (eproject b) = eproject (dot a b) ;
  embed_dot: ∀ a b , dot (embed a) (embed b) = embed (dot a b) ;
  mov_embed: ∀ a b , mov a b -> mov (embed a) (embed b) ;
  mov_eproject: ∀ a b , mov a b -> mov (eproject a) (eproject b) ;
  unit_embed: embed unit = unit ;
  eproject_embed : ∀ a , eproject (embed a) = a ;
  embed_eproject : ∀ b , b = dot (embed (eproject b)) (erest b) ;
  valid_dot_rest : ∀ a b , m_valid a -> m_valid b -> m_valid (dot (embed a) (erest b)) ;
}.

Lemma m_valid_of_m_valid_embed (M B : Type)
    `{!EqDecision M} `{!TPCM M} `{!EqDecision B} `{!TPCM B} `{!TPCMEmbed M B}
    a : m_valid (embed a) -> m_valid a.
Proof.
  intro.
  assert (m_valid (eproject (@embed M B EqDecision0 TPCM0 EqDecision1 TPCM1 TPCMEmbed0 a))).
    - apply valid_eproject. trivial.
    - rewrite eproject_embed in H0. trivial.
Qed.

#[refine]
Local Instance embed_transitive (M N P : Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
    `{!EqDecision P} `{!TPCM P}
    (m_embed: TPCMEmbed M N)
    (n_embed: TPCMEmbed N P)
    : TPCMEmbed M P := {
  embed := λ m , embed (embed m) ;
  eproject := λ p , eproject (eproject p) ;
  erest := λ m , dot (embed (erest (eproject m))) (erest m) ;
}.
  - intros. apply valid_embed. apply valid_embed. trivial.
  - intros. apply valid_eproject. apply valid_eproject. trivial.
  - intros. rewrite eproject_dot. rewrite eproject_dot. trivial.
  - intros. rewrite embed_dot. rewrite embed_dot. trivial.
  - intros. apply mov_embed. apply mov_embed. trivial.
  - intros. apply mov_eproject. apply mov_eproject. trivial.
  - intros. rewrite unit_embed. apply unit_embed.
  - intros. rewrite eproject_embed. rewrite eproject_embed. trivial.
  - intros.
    have j := @embed_eproject N P EqDecision1 TPCM1 EqDecision2 TPCM2 n_embed b.
    have k := @embed_eproject M N EqDecision0 TPCM0 EqDecision1 TPCM1 m_embed
        (@eproject N P EqDecision1 TPCM1 EqDecision2 TPCM2 n_embed b).
    deex.
    rewrite tpcm_assoc.
    rewrite embed_dot.
    rewrite <- k. trivial.
  - intros.
    rewrite tpcm_assoc.
    rewrite embed_dot.
    apply valid_dot_rest; trivial.
    apply valid_dot_rest; trivial.
    apply valid_eproject. trivial.
Defined.
    
Local Remove Hints embed_transitive : typeclass_instances.


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
Defined.

#[refine]
Local Instance tpcm_embed_self (M: Type)
    `{!EqDecision M} `{!TPCM M}
  : TPCMEmbed M M := {
    embed := λ m , m ;
    eproject := λ m , m ;
    erest := λ m, unit ;
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
  - intros. rewrite unit_dot. trivial.
  - intros. rewrite unit_dot. trivial.
Qed.

Local Remove Hints tpcm_embed_self : typeclass_instances.

#[refine]
Local Instance iprod_tpcm_embed_left (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed M (InternalProduct M N) := {
    embed := λ m , InternalProductC m unit ;
    eproject := λ p , match p with InternalProductC m _ => m end ;
    erest := λ p , match p with InternalProductC _ m' => InternalProductC unit m' end ;
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
  - intros. destruct b. unfold dot, iprod_tpcm. rewrite unit_dot. rewrite unit_dot_left.
      trivial.
  - intros. destruct b. unfold m_valid, dot, iprod_tpcm. rewrite unit_dot. rewrite unit_dot_left. split; trivial. unfold m_valid, iprod_tpcm in H0. intuition.
Defined.

Local Remove Hints iprod_tpcm_embed_left : typeclass_instances.

#[refine]
Local Instance iprod_tpcm_embed_right (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed N (InternalProduct M N) := {
    embed := λ n , InternalProductC unit n ;
    eproject := λ p , match p with InternalProductC _ n => n end ;
    erest := λ p , match p with InternalProductC m' _ => InternalProductC m' unit end ;
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
  - intros. destruct b. unfold dot, iprod_tpcm. rewrite unit_dot. rewrite unit_dot_left.
      trivial.
  - intros. destruct b. unfold m_valid, dot, iprod_tpcm. rewrite unit_dot. rewrite unit_dot_left. split; trivial. unfold m_valid, iprod_tpcm in H0. intuition.
Defined.

Local Remove Hints iprod_tpcm_embed_right : typeclass_instances.

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

Local Instance ic_eq_dec {M} `{!EqDecision M} `{!TPCM M} : EqDecision (InfiniteCopies M). 
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
Local Instance ic_tpcm (M: Type)
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
    
Definition ic_key_opt_map `{!EqDecision M} `{!TPCM M}
    (fn: nat -> option nat) (m: InfiniteCopies M) : InfiniteCopies M.
Proof.
refine ({|
  ic_obj := gmap_key_opt_map fn (ic_obj m) ;
  ic_prf := _ ; 
|}).
  - unfold ic_wf. rewrite bool_decide_spec. unfold map_Forall. intros.
    have j := gmap_key_opt_map_rev_key_exists fn (ic_obj m) i.
    have j0 := j nat_eq_dec nat_countable.
    rewrite H in j0. deex. destruct_ands.
    destruct m. unfold ic_obj in H1.
    have t := elem_ne_unit_of_ic_wf (ic_obj0) k ic_prf0. rewrite H1 in t. trivial.
Defined.

Definition ic_key_map `{!EqDecision M} `{!TPCM M}
    (fn: nat -> nat) (m: InfiniteCopies M) : InfiniteCopies M :=
  ic_key_opt_map (λ n , Some (fn n)) m.

Definition ic_pair {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M) :=
  dot (ic_key_map (λ n , 2*n) a) (ic_key_map (λ n, 2*n + 1) b).
  
Definition ic_left {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M) :=
  (ic_key_opt_map even_get a).
  
Definition ic_right {M} `{!EqDecision M} `{!TPCM M} (b : InfiniteCopies M) :=
  (ic_key_opt_map odd_get b).
      
  
Lemma ic_get_ic_key_opt_map `{!EqDecision M} `{!TPCM M}
    (fn: nat -> option nat) (m: InfiniteCopies M) (x y: nat)
    (x_eq: fn y = Some x)
    (inj: ∀ x y , fn x = fn y -> fn x ≠ None -> x = y)
  : ic_get (ic_key_opt_map fn m) x = ic_get m y.
Proof.
  unfold ic_key_opt_map, ic_get, ic_obj. destruct m.
  have r := gmap_key_opt_map_rev_key_exists fn ic_obj0 x.
  have r1 := r nat_eq_dec nat_countable.
  destruct (gmap_key_opt_map fn ic_obj0 !! x) eqn:gkom.
  - deex. destruct_ands. assert (k = y).
    + apply inj; crush.
    + subst. rewrite H0. trivial.
  - destruct (ic_obj0 !! y) eqn:icom; trivial.
    exfalso.
    assert (ic_obj0 !! y ≠ None) by crush.
    have lg := lookup_gmap_key_opt_map_not_none fn ic_obj0 y x H x_eq.
    crush.
Qed.
  
Lemma ic_get_ic_key_opt_map_unit `{!EqDecision M} `{!TPCM M}
    (fn: nat -> option nat) (m: InfiniteCopies M) (x: nat)
    (inj: ∀ y , fn y ≠ Some x)
  : ic_get (ic_key_opt_map fn m) x = unit.
Proof.
  unfold ic_key_opt_map, ic_get, ic_obj. destruct m.
  destruct (gmap_key_opt_map fn ic_obj0 !! x) eqn:gkom; trivial. exfalso.
  have r := gmap_key_opt_map_rev_key_exists fn ic_obj0 x.
  have r1 := r nat_eq_dec nat_countable.
  rewrite gkom in r1. deex. destruct_ands. have inj0 := inj k.
  contradiction.
Qed.

Lemma ic_get_ic_left {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M) (i: nat)
  : ic_get (ic_left a) i = ic_get a (2 * i).
Proof.
  unfold ic_left. apply ic_get_ic_key_opt_map.
    - unfold even_get. rewrite parity_2i. trivial.
    - intros. apply eq_of_even_get_eq; trivial.
Qed.
  
Lemma ic_get_ic_right {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M) (i: nat)
  : ic_get (ic_right a) i = ic_get a (2 * i + 1).
Proof.
  unfold ic_right. apply ic_get_ic_key_opt_map.
    - unfold odd_get. rewrite parity_2i_1. trivial.
    - intros. apply eq_of_odd_get_eq; trivial.
Qed.
  
Lemma ic_get_ic_pair {M} `{!EqDecision M} `{!TPCM M} (a b : InfiniteCopies M) (i: nat)
  : ic_get (ic_pair a b) i = match parity i with
    | Even k => ic_get a k
    | Odd k => ic_get b k
    end.
Proof.
  have eoe := even_or_odd i. destruct eoe; deex; subst i.
  - rewrite parity_2i. unfold ic_pair. rewrite ic_get_ic_dot.
    replace (ic_get a k) with (dot (ic_get a k) unit) by (rewrite unit_dot; trivial).
    f_equal.
    + unfold ic_key_map. apply ic_get_ic_key_opt_map; trivial. intros. crush.
    + unfold ic_key_map. apply ic_get_ic_key_opt_map_unit. crush.
  - rewrite parity_2i_1. unfold ic_pair. rewrite ic_get_ic_dot.
    replace (ic_get b k) with (dot unit (ic_get b k)) by (rewrite unit_dot_left; trivial).
    f_equal.
    + unfold ic_key_map. apply ic_get_ic_key_opt_map_unit. crush.
    + unfold ic_key_map. apply ic_get_ic_key_opt_map; trivial. intros. crush.
Qed.

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
Defined.

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
Defined.

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
Defined.

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

Definition ic_cut {M} `{!EqDecision M} `{!TPCM M} (m : InfiniteCopies M) : InfiniteCopies M.
Proof.
refine ({|
  ic_obj := delete 0 (ic_obj m) ;
  ic_prf := _ ;
|}).
 - unfold ic_wf.
    rewrite bool_decide_spec.
    unfold map_Forall. intros.
    destruct m. unfold ic_obj in H.
    have h : Decision (i = 0) by solve_decision. destruct h.
    + subst. rewrite lookup_delete in H. discriminate.
    + rewrite lookup_delete_ne in H.
      * have j1 := elem_ne_unit_of_ic_wf ic_obj0 i ic_prf0.
        rewrite H in j1. trivial.
      * crush.
Defined.

Lemma ic_get_ic_cut {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M)
  : ic_get (ic_cut a) 0 = unit.
Proof. unfold ic_get, ic_cut, ic_obj. rewrite lookup_delete. trivial.
Qed.

Lemma ic_get_ic_cut_ne {M} `{!EqDecision M} `{!TPCM M} (a : InfiniteCopies M) (i: nat)
  : i ≠ 0 -> ic_get (ic_cut a) i = ic_get a i.
Proof. intro. unfold ic_get, ic_cut, ic_obj. destruct a. rewrite lookup_delete_ne. 
  - trivial. - crush.
Qed.

#[refine]
Local Instance ic_tpcm_embed (M: Type)
    `{!EqDecision M} `{!TPCM M}
  : TPCMEmbed M (InfiniteCopies M) := {
    embed := ic_singleton ;
    eproject := λ a, ic_get a 0 ;
    erest := ic_cut ;
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
  - intros. apply ic_extens. intros. rewrite ic_get_ic_dot.
    have h : Decision (i = 0) by solve_decision. destruct h.
    + subst i. rewrite ic_get_ic_singleton. rewrite ic_get_ic_cut.
        rewrite unit_dot. trivial.
    + rewrite ic_get_ic_singleton_ne; trivial. rewrite ic_get_ic_cut_ne; trivial.
        rewrite unit_dot_left. trivial.
  - intros. unfold m_valid, ic_tpcm. intro. rewrite ic_get_ic_dot.
    have h : Decision (i = 0) by solve_decision. destruct h.
    + subst i. rewrite ic_get_ic_singleton. rewrite ic_get_ic_cut.
        rewrite unit_dot. trivial.
    + rewrite ic_get_ic_singleton_ne; trivial. rewrite ic_get_ic_cut_ne; trivial.
        rewrite unit_dot_left. trivial.
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

Lemma ic_left_ic_dot `{!EqDecision M} `{!TPCM M} (a b: InfiniteCopies M)
    : ic_left (ic_dot a b) = ic_dot (ic_left a) (ic_left b).
Proof. apply ic_extens. intro. rewrite ic_get_ic_left. rewrite ic_get_ic_dot.
    rewrite ic_get_ic_dot. rewrite ic_get_ic_left. rewrite ic_get_ic_left.
    trivial. Qed.
    
Lemma ic_right_ic_dot `{!EqDecision M} `{!TPCM M} (a b: InfiniteCopies M)
    : ic_right (ic_dot a b) = ic_dot (ic_right a) (ic_right b).
Proof. apply ic_extens. intro. rewrite ic_get_ic_right. rewrite ic_get_ic_dot.
    rewrite ic_get_ic_dot. rewrite ic_get_ic_right. rewrite ic_get_ic_right.
    trivial. Qed.
    
Lemma ic_pair_ic_dot `{!EqDecision M} `{!TPCM M} (a b c d: InfiniteCopies M)
    : ic_pair (ic_dot a b) (ic_dot c d)
    = ic_dot (ic_pair a c) (ic_pair b d).
Proof. apply ic_extens. intro. rewrite ic_get_ic_pair. rewrite ic_get_ic_dot.
    rewrite ic_get_ic_pair. rewrite ic_get_ic_pair. destruct (parity i).
    - rewrite ic_get_ic_dot. trivial.
    - rewrite ic_get_ic_dot. trivial.
Qed.
    
Lemma mov_ic_get_of_mov `{!EqDecision M} `{!TPCM M} a b (k: nat)
  : mov a b -> mov (ic_get a k) (ic_get b k).
Proof. intro. unfold mov, ic_tpcm, ic_mov in H. apply H. Qed.

Lemma ic_pair_unit `{!EqDecision M} `{!TPCM M}
  : ic_pair unit unit = unit.
Proof.
  apply ic_extens. intro. rewrite ic_get_ic_pair.
  destruct (parity i); repeat (rewrite ic_get_ic_unit); trivial.
Qed.

#[refine]
Local Instance ic_tpcm_embed_two (M N B: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
    `{!EqDecision B} `{!TPCM B}
    (m_embed: TPCMEmbed M (InfiniteCopies B))
    (n_embed: TPCMEmbed N (InfiniteCopies B))
    : TPCMEmbed (M * N) (InfiniteCopies B) := {
  embed := λ p , match p with (m, n) => ic_pair (embed m) (embed n) end ;
  eproject := λ b , (eproject (ic_left b), eproject (ic_right b)) ;
  erest := λ b , ic_pair 
    (@erest M (InfiniteCopies B) _ _ _ _ m_embed (ic_left b))
    (@erest N (InfiniteCopies B) _ _ _ _ n_embed (ic_right b)) ;
}.
Proof.
  - intros. destruct a. unfold m_valid, ic_tpcm. intros. apply m_valid_ic_pair.
     + apply valid_embed. unfold m_valid, pair_tpcm in H. destruct_ands. trivial.
     + apply valid_embed. unfold m_valid, pair_tpcm in H. destruct_ands. trivial.
  - intros. unfold m_valid, pair_tpcm. split.
     + apply valid_eproject. apply m_valid_ic_left. trivial.
     + apply valid_eproject. apply m_valid_ic_right. trivial.
  - intros. unfold dot, pair_tpcm. f_equal.
    + unfold ic_tpcm. rewrite ic_left_ic_dot. rewrite eproject_dot.
        unfold dot. trivial.
    + unfold ic_tpcm. rewrite ic_right_ic_dot. rewrite eproject_dot.
        unfold dot. trivial.
  - intros. destruct a, b. unfold dot, ic_tpcm, pair_tpcm.
    rewrite <- embed_dot.
    rewrite <- embed_dot.
    rewrite <- ic_pair_ic_dot.
    unfold dot. trivial.
  - intros. destruct a, b. unfold mov,ic_tpcm. unfold ic_mov.
      intros. rewrite ic_get_ic_pair. rewrite ic_get_ic_pair.
      unfold mov, pair_tpcm in H. destruct_ands.
      have eoo := even_or_odd i. destruct eoo.
      + deex. rewrite H1. rewrite parity_2i.
          apply mov_ic_get_of_mov. apply mov_embed. trivial.
      + deex. rewrite H1. rewrite parity_2i_1.
          apply mov_ic_get_of_mov. apply mov_embed. trivial.
  - intros. unfold mov, pair_tpcm. split.
    + unfold mov, ic_tpcm, ic_mov in H.
      apply mov_eproject. unfold mov, ic_tpcm, ic_mov. intro.
        rewrite ic_get_ic_left.
        rewrite ic_get_ic_left. apply H.
    + unfold mov, ic_tpcm, ic_mov in H.
      apply mov_eproject. unfold mov, ic_tpcm, ic_mov. intro.
        rewrite ic_get_ic_right.
        rewrite ic_get_ic_right. apply H.
  - unfold unit, pair_tpcm, ic_tpcm.
    rewrite unit_embed. rewrite unit_embed.
    rewrite ic_pair_unit. trivial.
  - destruct a. f_equal.
      + rewrite ic_left_ic_pair. rewrite eproject_embed. trivial.
      + rewrite ic_right_ic_pair. rewrite eproject_embed. trivial.
  - intros. 
    have j := @embed_eproject M (InfiniteCopies B) _ _ _ _ m_embed (ic_left b).
    have k := @embed_eproject N (InfiniteCopies B) _ _ _ _ n_embed (ic_right b).
    deex.
    unfold dot, ic_tpcm.
    rewrite <- ic_pair_ic_dot.
    replace b with (ic_pair (ic_left b) (ic_right b)) by (apply ic_pair_ic_left_ic_right).
    f_equal;
      replace (ic_pair (ic_left b) (ic_right b)) with b by (symmetry; apply ic_pair_ic_left_ic_right).
     + rewrite j. f_equal.
        * rewrite <- j. trivial.
        * rewrite <- j. trivial.
     + rewrite k. f_equal.
        * rewrite <- k. trivial.
        * rewrite <- k. trivial.
  - intros. destruct a.
    unfold dot, ic_tpcm.
    rewrite <- ic_pair_ic_dot.
    unfold m_valid, pair_tpcm in H; destruct_ands.
    apply m_valid_ic_pair.
    + have j := @valid_dot_rest M (InfiniteCopies B) _ _ _ _ m_embed m (ic_left b).
        unfold dot, ic_tpcm in j.
        apply j; trivial. apply m_valid_ic_left. trivial.
    + have j := @valid_dot_rest N (InfiniteCopies B) _ _ _ _ n_embed n (ic_right b).
        unfold dot, ic_tpcm in j.
        apply j; trivial. apply m_valid_ic_right. trivial.
Defined.
     
Local Instance ic_tpcm_embed_extend (M: Type) (B: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B}
    (m_embed: TPCMEmbed M B) : TPCMEmbed M (InfiniteCopies B) :=
      embed_transitive M B (InfiniteCopies B) m_embed (ic_tpcm_embed B).

Record BurrowCtx := {
  bc_small_M: Type ;
  bc_small_RI: Type ;
  
  bc_small_M_eqdec : EqDecision bc_small_M ;
  bc_small_M_tpcm : TPCM bc_small_M ;
  bc_small_RI_eqdec : EqDecision bc_small_RI ;
  bc_small_RI_countable : Countable bc_small_RI ;
  
  bc_refs: bc_small_RI -> Refinement (InfiniteCopies bc_small_M) (InfiniteCopies bc_small_M) ;
}.

Instance bc_small_M_eqdec_inst (𝜇: BurrowCtx) : EqDecision (bc_small_M 𝜇).
  Proof. apply bc_small_M_eqdec. Defined.
Instance bc_small_M_tpcm_inst (𝜇: BurrowCtx) : TPCM (bc_small_M 𝜇).
  Proof. apply bc_small_M_tpcm. Defined.
Instance bc_small_RI_eqdec_inst (𝜇: BurrowCtx) : EqDecision (bc_small_RI 𝜇).
  Proof. apply bc_small_RI_eqdec. Defined.
Instance bc_small_RI_countable_inst (𝜇: BurrowCtx) : Countable (bc_small_RI 𝜇).
  Proof. apply bc_small_RI_countable. Defined.


Definition bc_M (𝜇: BurrowCtx) : Type := InfiniteCopies (bc_small_M 𝜇).

Inductive FinalRI (small_RI: Type) :=
  | FinalRILeft : FinalRI small_RI
  | FinalRIRight : FinalRI small_RI
  | FinalRITriv : FinalRI small_RI
  | FinalRINormal : small_RI -> FinalRI small_RI
.

(*Definition bc_RI (𝜇: BurrowCtx) : Type := FinalRI bc_small_RI.*)

Local Instance bc_FinalRI_eqdec (small_RI: Type) `{!EqDecision small_RI}
    : EqDecision (FinalRI small_RI).
Proof. solve_decision. Qed.

Global Instance bc_FinalRI_countable (small_RI: Type) `{!EqDecision small_RI, !Countable small_RI}
    : Countable (FinalRI small_RI).
Proof.
  set (enc :=
    fix go e :=
      match e with
      | FinalRILeft _ => inl ()
      | FinalRIRight _ => inr (inl ())
      | FinalRITriv _ => inr (inr (inl ()))
      | FinalRINormal _ ri => inr (inr (inr ri))
      end : (() + (() + (() + small_RI)))
    ).
  set (dec :=
    fix go (e : (() + (() + (() + small_RI)))) :=
      match e with
      | inl _ => FinalRILeft small_RI
      | inr (inl _) => FinalRIRight small_RI
      | inr (inr (inl _)) => FinalRITriv small_RI
      | inr (inr (inr ri)) => FinalRINormal small_RI ri
      end
    ).
 refine (inj_countable' enc dec _).
 intro.
 destruct x; simpl; f_equal.
Qed.

#[refine]
Global Instance bc_refinement_index (𝜇: BurrowCtx)
    : RefinementIndex (InfiniteCopies (bc_small_M 𝜇)) (FinalRI (bc_small_RI 𝜇)) := {
  refinement_of := λ ri , (match ri with
    | FinalRILeft _ => refinement_left
    | FinalRIRight _ => refinement_right
    | FinalRITriv _ => refinement_trivial
    | FinalRINormal _ sri => bc_refs 𝜇 sri
  end) ;    
  triv_ri := FinalRITriv (bc_small_RI 𝜇);
  left_ri := FinalRILeft (bc_small_RI 𝜇);
  right_ri := FinalRIRight (bc_small_RI 𝜇);
  pair_up := ic_pair ;
}.
 - intros. unfold refinement_left, refinement_right, rel. rewrite ic_pair_ic_left_ic_right.
    trivial.
 - intros. unfold refinement_left, rel. apply ic_left_ic_pair.
 - intros. unfold refinement_right, rel. apply ic_right_ic_pair.
 - intros. rewrite ic_pair_ic_dot. trivial.
 - intros. unfold refinement_trivial, rel_defined. trivial.
 - intros. unfold refinement_trivial, rel. trivial.
 - intros. unfold refinement_left, rel_defined. apply m_valid_ic_pair; trivial.
 - intros. unfold refinement_right, rel_defined. apply m_valid_ic_pair; trivial.
 - intros. rewrite <- ic_left_ic_pair with (b0 := b). apply m_valid_ic_left; trivial.
 - intros. rewrite <- ic_right_ic_pair with (a0 := a). apply m_valid_ic_right; trivial.
Defined.

(* BurrowState stuff *)

Definition BurrowState (𝜇: BurrowCtx)
    := State (InfiniteCopies (bc_small_M 𝜇)) (FinalRI (bc_small_RI 𝜇)).
    
Instance ref_equiv {M} `{!EqDecision M} `{!TPCM M} {R} `{!EqDecision R} `{!TPCM R}
  : Equiv (Refinement R M) := λ (ref1 ref2: Refinement R M) ,
      (∀ r , rel_defined R M ref1 r <-> rel_defined R M ref2 r)
      /\ (∀ r , rel R M ref1 r = rel R M ref2 r).
      
Instance ref_equiv_trans {M} `{!EqDecision M} `{!TPCM M} : Transitive ref_equiv.
  Proof. unfold Transitive, ref_equiv. intros. destruct_ands.
      crush. have h := H r. have h1 := H1 r. have h2 := H2 r. have h0 := H0 r.
      intuition. Qed.
Instance ref_equiv_symm {M} `{!EqDecision M} `{!TPCM M} : Symmetric ref_equiv.
  Proof. unfold Symmetric, ref_equiv. intros. destruct_ands. crush.
      have h := H r. have h0 := H0 r. intuition. Qed.
Instance ref_equiv_refl {M} `{!EqDecision M} `{!TPCM M} : Reflexive ref_equiv.
  Proof. unfold Reflexive, ref_equiv. intros. destruct_ands. crush. Qed.

Class HasTPCM (𝜇: BurrowCtx) (M: Type) `{!EqDecision M, !TPCM M}
    := { inctx_embed :> TPCMEmbed M (InfiniteCopies (bc_small_M 𝜇)) }.

Global Instance product_hastpcm (𝜇: BurrowCtx) (M: Type) (N: Type)
    `{!EqDecision M, TPCM M}
    `{!EqDecision N, TPCM N}
    `{m_ht: !HasTPCM 𝜇 M} `{n_ht: !HasTPCM 𝜇 N} : HasTPCM 𝜇 (M * N)
| 5 := { (* assign high priority so this is tried after the other HasTPCM instances *)
  inctx_embed := ic_tpcm_embed_two M N (bc_small_M 𝜇)
      (inctx_embed) (inctx_embed) ;
}.
  
Class HasRef (𝜇: BurrowCtx) {R M: Type}
      `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
      `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
      `{r_hastpcm: !HasTPCM 𝜇 R} `{m_hastpcm: !HasTPCM 𝜇 M}
      (ref: Refinement R M)
    := {
        hasref_ri: (bc_small_RI 𝜇) ; 
        hasref_is: (bc_refs 𝜇 hasref_ri) ≡ 
            refinement_embed_dst (InfiniteCopies (bc_small_M 𝜇)) M (InfiniteCopies (bc_small_M 𝜇))
            (refinement_embed_src R M (InfiniteCopies (bc_small_M 𝜇)) ref)
        }.
        
Definition SingleTPCMCtx M `{!EqDecision M} `{TPCM M} : BurrowCtx.
Proof.
refine ({|
  bc_small_M := M ;
  bc_small_RI := () ;
  bc_refs := λ l , refinement_trivial ;
|}).
Defined.

Global Instance SingleTPCMCtx_HasTPCM M `{!EqDecision M} `{TPCM M}
  : HasTPCM (SingleTPCMCtx M) M | 3.
Proof.
  split. typeclasses eauto. Qed.

Definition refinement_sqr M N
    `{!EqDecision M} `{TPCM M}
    `{!EqDecision N} `{TPCM N}
    `{!TPCMEmbed M N}
    (R: Refinement M M) : Refinement N N :=
      refinement_embed_dst N M N (refinement_embed_src M M N R).
      
Instance refinement_embed_dst_proper R M B
    `{!EqDecision R} `{!TPCM R}
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B}
    `{!TPCMEmbed M B}
    : Proper ((≡) ==> (≡)) (refinement_embed_dst R M B).
Proof.
  unfold Proper, "==>", refinement_embed_dst. unfold "≡", ref_equiv.
  cbn [rel]. cbn [rel_defined]. intros. crush. Qed.
  
Instance refinement_embed_src_proper R M B
    `{!EqDecision R} `{!TPCM R}
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B}
    `{!TPCMEmbed R B}
    : Proper ((≡) ==> (≡)) (refinement_embed_src R M B).
Proof.
  unfold Proper, "==>", refinement_embed_src. unfold "≡", ref_equiv.
  cbn [rel]. cbn [rel_defined]. intros. crush. 
  rewrite <- H0. trivial. Qed.

Instance refinement_sqr_proper M N
    `{!EqDecision M} `{TPCM M}
    `{!EqDecision N} `{TPCM N}
    `{!TPCMEmbed M N}
    : Proper ((≡) ==> (≡)) (refinement_sqr M N).
Proof.
  unfold Proper, "==>", refinement_sqr. intros.
    setoid_rewrite H1. trivial. Qed.

Lemma refinement_embed_src_dst
    `{!EqDecision A} `{TPCM A}
    `{!EqDecision B} `{TPCM B}
    `{!EqDecision X} `{TPCM X}
    `{!EqDecision Y} `{TPCM Y}
    `{!TPCMEmbed A X}
    `{!TPCMEmbed B Y}
    (ref: Refinement A B)
    : (refinement_embed_src A Y X (refinement_embed_dst A B Y ref))
    ≡ (refinement_embed_dst X B Y (refinement_embed_src A B X ref)).
Proof.
  unfold "≡", ref_equiv. crush. Qed.
    
Lemma refinement_swap_iden A B X Y S T
    `{!EqDecision A} `{TPCM A}
    `{!EqDecision B} `{TPCM B}
    `{!EqDecision X} `{TPCM X}
    `{!EqDecision Y} `{TPCM Y}
    `{!EqDecision S} `{TPCM S}
    `{!EqDecision T} `{TPCM T}
    (e_ax: TPCMEmbed A X)
    (e_by: TPCMEmbed B Y)
    (e_as: TPCMEmbed A S)
    (e_sx: TPCMEmbed S X)
    (e_bt: TPCMEmbed B T)
    (e_ty: TPCMEmbed T Y)
    (c1: e_ax = embed_transitive A S X e_as e_sx)
    (c2: e_by = embed_transitive B T Y e_bt e_ty)
    (ref : Refinement A B)
  :
  (refinement_embed_dst X T Y (refinement_embed_src S T X (
    (refinement_embed_dst S B T (refinement_embed_src A B S ref))
  ))) ≡
  (refinement_embed_dst X B Y (refinement_embed_src A B X ref)).
Proof.
  rewrite c1. clear c1.
  rewrite c2. clear c2.
  unfold "≡", ref_equiv. split.
  - intro. split.
    + unfold refinement_embed_dst, rel_defined, refinement_embed_src, rel_defined,
        refinement_embed_dst, rel_defined, refinement_embed_src, rel_defined.
      intros. intuition.
    + unfold refinement_embed_dst, rel_defined, refinement_embed_src, rel_defined,
        refinement_embed_dst, rel_defined, refinement_embed_src, rel_defined.
      intros. intuition.
      apply valid_eproject. trivial.
  - intro. 
    unfold refinement_embed_dst, rel, refinement_embed_src, rel,
        refinement_embed_dst, rel, refinement_embed_src, rel. trivial.
Qed.

Definition NewTPCMCtx (𝜇: BurrowCtx) M `{!EqDecision M} `{TPCM M} : BurrowCtx.
Proof.
refine ({|
  bc_small_M := InternalProduct (InfiniteCopies (bc_small_M 𝜇)) M ;
  bc_small_RI := bc_small_RI 𝜇 ;
  bc_refs := λ ri , refinement_sqr
      (InfiniteCopies (bc_small_M 𝜇))
      (InfiniteCopies (InternalProduct (InfiniteCopies (bc_small_M 𝜇)) M))
      (bc_refs 𝜇 ri)
|}).
 - typeclasses eauto.
 - 
    apply ic_tpcm_embed_extend.
    apply iprod_tpcm_embed_left.
Defined.

Global Instance NewTPCM_HasTPCM M `{!EqDecision M} `{TPCM M}
    (𝜇 : BurrowCtx)
  : HasTPCM (NewTPCMCtx 𝜇 M) M | 3.
Proof.
  split. unfold bc_small_M, NewTPCMCtx.
  apply ic_tpcm_embed_extend.
  apply iprod_tpcm_embed_right.
Qed.

Global Instance NewTPCM_KeepsTPCM
    M `{!EqDecision M} `{TPCM M}
    N `{!EqDecision N} `{TPCM N}
    (𝜇 : BurrowCtx) `{!HasTPCM 𝜇 N}
  : HasTPCM (NewTPCMCtx 𝜇 M) N | 3.
Proof.
  split. unfold bc_small_M, NewTPCMCtx.
  apply (embed_transitive N (InfiniteCopies (bc_small_M 𝜇))
          (InfiniteCopies (InternalProduct (InfiniteCopies (bc_small_M 𝜇)) M))).
   - typeclasses eauto.
   - apply ic_tpcm_embed_extend. apply iprod_tpcm_embed_left.
Defined.

Global Instance NewTPCM_KeepsRef
    M `{!EqDecision M} `{TPCM M}
    N `{!EqDecision N} `{TPCM N}
    T `{!EqDecision T} `{TPCM T}
    (𝜇 : BurrowCtx)
    (ref: Refinement M N)
    `{!HasTPCM 𝜇 M} `{!HasTPCM 𝜇 N}
    `{hr: !HasRef 𝜇 ref}
  : HasRef (NewTPCMCtx 𝜇 T) ref.
Proof.
  refine ({|
    hasref_ri := ((@hasref_ri 𝜇 M N _ _ _ _ _ _ ref hr) : bc_small_RI (NewTPCMCtx 𝜇 T));
  |}).
  - unfold bc_refs, NewTPCMCtx.
    cbn [bc_small_M].
    have jk := @hasref_is 𝜇 _ _ _ _ _ _ _ _ ref hr.
    setoid_rewrite jk.
    unfold refinement_sqr.
    apply refinement_swap_iden.
    + typeclasses eauto.
    + typeclasses eauto.
    + typeclasses eauto.
    + typeclasses eauto.
    + typeclasses eauto.
    + typeclasses eauto.
    + trivial.
    + trivial.
Qed.

Definition NewRefCtx (𝜇: BurrowCtx)
    R `{!EqDecision R} `{TPCM R}
    M `{!EqDecision M} `{TPCM M}
    `{!HasTPCM 𝜇 R} `{!HasTPCM 𝜇 M}
    (ref: Refinement R M)
    : BurrowCtx.
Proof.
refine ({|
  bc_small_M := bc_small_M 𝜇 ;
  bc_small_RI := (bc_small_RI 𝜇) + () ;
  bc_refs := λ ri , match ri with
    | inl ri => (bc_refs 𝜇 ri)
    | inr _ => refinement_embed_dst (InfiniteCopies (bc_small_M 𝜇)) M (InfiniteCopies (bc_small_M 𝜇))
            (refinement_embed_src R M (InfiniteCopies (bc_small_M 𝜇)) ref)
    end ;
|}).
Defined.

Global Instance NewRef_KeepsTPCM (𝜇: BurrowCtx)
    R `{!EqDecision R} `{TPCM R}
    M `{!EqDecision M} `{TPCM M}
    T `{!EqDecision T} `{TPCM T}
    `{!HasTPCM 𝜇 R} `{!HasTPCM 𝜇 M} `{!HasTPCM 𝜇 T}
    (ref: Refinement R M)
  : HasTPCM (NewRefCtx 𝜇 R M ref) T | 3.
Proof.
  split.  unfold NewRefCtx. cbn [bc_small_M].
  destruct HasTPCM2. trivial.
Defined.

Global Instance NewRef_HasRef (𝜇: BurrowCtx)
    R `{!EqDecision R} `{TPCM R}
    M `{!EqDecision M} `{TPCM M}
    `{!HasTPCM 𝜇 R} `{!HasTPCM 𝜇 M}
    (ref: Refinement R M)
  : HasRef (NewRefCtx 𝜇 R M ref) ref.
Proof.
  refine ({|
    hasref_ri := (inr () : bc_small_RI ((NewRefCtx 𝜇 R M ref))) ;
  |}).
  trivial.
Qed.

Global Instance NewRef_KeepsRef (𝜇: BurrowCtx)
    R `{!EqDecision R} `{TPCM R}
    M `{!EqDecision M} `{TPCM M}
    S `{!EqDecision S} `{TPCM S}
    T `{!EqDecision T} `{TPCM T}
    `{!HasTPCM 𝜇 R} `{!HasTPCM 𝜇 M}
    `{!HasTPCM 𝜇 S} `{!HasTPCM 𝜇 T}
    (ref: Refinement R M)
    (ref': Refinement S T)
    `{hr': !HasRef 𝜇 ref'}
  : HasRef (NewRefCtx 𝜇 R M ref) ref'.
Proof.
  refine ({|
    hasref_ri := ((inl (@hasref_ri 𝜇 S T _ _ _ _ _ _ ref' hr')) : bc_small_RI ((NewRefCtx 𝜇 R M ref))) ;
  |}).
  unfold bc_refs, NewRefCtx.
  apply (@hasref_is 𝜇 S T _ _ _ _ _ _ ref' hr').
Qed.

Definition BurrowLoc (𝜇: BurrowCtx) := Loc (FinalRI (bc_small_RI 𝜇)).

Definition extend_loc {𝜇: BurrowCtx}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_hastpcm: !HasTPCM 𝜇 R} `{m_hastpcm: !HasTPCM 𝜇 M}
    (𝛼: nat) (ref: Refinement R M) (𝛾: BurrowLoc 𝜇)
    `{hr: !HasRef 𝜇 ref} : BurrowLoc 𝜇
    := (ExtLoc 𝛼 (FinalRINormal (bc_small_RI 𝜇) (@hasref_ri
        𝜇 R M r_eqdec r_tpcm m_eqdec m_tpcm r_hastpcm m_hastpcm ref hr
    )) 𝛾).

Definition cross_loc {𝜇: BurrowCtx} (𝛾1 𝛾2: BurrowLoc 𝜇) := CrossLoc 𝛾1 𝛾2.

Definition mu_embed (M: Type) (𝜇: BurrowCtx) `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (m: M) : InfiniteCopies (bc_small_M 𝜇) := embed m.
  
Definition mu_eproject (M: Type) (𝜇: BurrowCtx) `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (b: InfiniteCopies (bc_small_M 𝜇)) : M := eproject b.
  
Definition mu_erest (M: Type) (𝜇: BurrowCtx) `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (b: InfiniteCopies (bc_small_M 𝜇)) : InfiniteCopies (bc_small_M 𝜇) := erest b.
  
Lemma m_valid_of_m_valid_mu_embed (M: Type) (𝜇: BurrowCtx) `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    m : m_valid (mu_embed M 𝜇 m) -> m_valid m.
Proof.
  unfold mu_embed. apply m_valid_of_m_valid_embed. Qed.

Definition live' {𝜇: BurrowCtx} {M}
    `{!EqDecision M} `{!TPCM M}
    `{!HasTPCM 𝜇 M} (loc: BurrowLoc 𝜇) (m: M) : BurrowState 𝜇
    := live loc (mu_embed M 𝜇 m).
    
Definition reserved' {𝜇: BurrowCtx} {M}
    `{!EqDecision M} `{!TPCM M}
    `{!HasTPCM 𝜇 M} (kappa: Lifetime) (loc: BurrowLoc 𝜇) (m: M) : BurrowState 𝜇
    := reserved kappa loc (mu_embed M 𝜇 m).
    
Definition is_borrow' {𝜇: BurrowCtx} {M}
    `{!EqDecision M} `{!TPCM M}
    `{!HasTPCM 𝜇 M} (kappa: Lifetime) (loc: BurrowLoc 𝜇) (m: M) (state: BurrowState 𝜇) : Prop
    := is_borrow kappa loc (mu_embed M 𝜇 m) state.

Lemma live_dot_live' {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (𝛾: BurrowLoc 𝜇) (m1 m2: M)
    : live' 𝛾 m1 ⋅ live' 𝛾 m2 ≡ live' 𝛾 (dot m1 m2).
Proof.
  unfold live'. setoid_rewrite live_dot_live. rewrite embed_dot. trivial.
Qed.

Lemma live_unit' {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (𝛾: BurrowLoc 𝜇) : live' 𝛾 (unit:M) ≡ state_unit.
Proof.
  unfold live'. unfold mu_embed. rewrite unit_embed. apply live_unit.
Qed.

Lemma live_and_borrow_implies_valid'
    {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (𝜅: Lifetime) (m k : M) (b : BurrowState 𝜇)
    (isb: is_borrow' 𝜅 𝛾 k b)
    (isv: ✓(active 𝜅 ⋅ live' 𝛾 m ⋅ b))
    : m_valid (dot m k).
Proof.
  unfold is_borrow' in isb.
  unfold live' in isv.
  apply m_valid_of_m_valid_mu_embed with (𝜇:=𝜇) (HasTPCM0:=HasTPCM0).
  unfold mu_embed in *.
  rewrite <- embed_dot.
  apply live_and_borrow_implies_valid with (gamma:=𝛾) (kappa:=𝜅) (b0:=b); trivial.
Qed.

Lemma live_implies_valid'
    {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (m : M)
    (isv: ✓(live' 𝛾 m))
    : m_valid m.
Proof.
  unfold live' in isv. 
  apply m_valid_of_m_valid_mu_embed with (𝜇:=𝜇) (HasTPCM0:=HasTPCM0).
  unfold mu_embed in *.
  apply live_implies_valid with (gamma:=𝛾); trivial.
Qed.

Lemma borrow_begin'
    {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (𝛾: BurrowLoc 𝜇) (m : M) (p : BurrowState 𝜇)
    (si: state_valid (live' 𝛾 m ⋅ p))
     : exists 𝜅 , state_valid (active 𝜅 ⋅ reserved' 𝜅 𝛾 m ⋅ p)
        /\ 𝜅 ≠ empty_lifetime.
Proof.
  unfold live' in si.
  unfold reserved' in si.
  apply borrow_begin_valid. trivial.
Qed.

Lemma borrow_lifetime_inclusion'
    {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    𝜅 𝜅' 𝛾 (m: M) (state: BurrowState 𝜇)
    (li: lifetime_included 𝜅' 𝜅)
    (ib: is_borrow' 𝜅 𝛾 m state)
       : is_borrow' 𝜅' 𝛾 m state.
Proof. unfold is_borrow' in *.
  apply borrow_lifetime_inclusion with (kappa := 𝜅); trivial.
Qed.


Lemma le_embed_r_of_le_c_eproject M B
  `{!EqDecision M} `{!TPCM M} 
  `{!EqDecision B} `{!TPCM B} `{!TPCMEmbed M B}
  (c:M) (r:B) : tpcm_le c (eproject r) -> tpcm_le (embed c) r.
Proof.
  unfold tpcm_le. intros. deex.
  have ee := @embed_eproject M B EqDecision0 TPCM0 EqDecision1 TPCM1 TPCMEmbed0 r.
  deex.
  exists (dot (embed c0) (erest r)).
  rewrite ee.
  rewrite tpcm_assoc. f_equal.
  - rewrite embed_dot. rewrite H. trivial.
  - f_equal. symmetry. trivial.
Qed.

Lemma le_embed_r_of_le_c_eproject_mu
  (𝜇: BurrowCtx) M `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
      c r : tpcm_le c (mu_eproject M 𝜇 r) -> tpcm_le (mu_embed M 𝜇 c) r.
Proof. unfold mu_eproject, mu_embed. apply le_embed_r_of_le_c_eproject.
Qed.

Lemma le_a_eproject_of_le_embed_r_mu
  (𝜇: BurrowCtx) M `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
      a r
  : tpcm_le (mu_embed M 𝜇 a) r -> tpcm_le a (mu_eproject M 𝜇 r).
Proof.
  unfold tpcm_le. intros. deex. exists (mu_eproject M 𝜇 c).
  replace a with (mu_eproject M 𝜇 (mu_embed M 𝜇 a)).
  * rewrite eproject_dot. rewrite H. unfold mu_eproject. trivial.
  * unfold mu_eproject, mu_embed. rewrite eproject_embed. trivial.
Qed.

Lemma le_embed_embed M B
  `{!EqDecision M} `{!TPCM M} 
  `{!EqDecision B} `{!TPCM B} `{!TPCMEmbed M B}
  (a b: M) : tpcm_le a b -> tpcm_le (embed a) (embed b).
Proof.
  unfold tpcm_le. intros. deex. exists (embed c).
    rewrite <- H. rewrite embed_dot. trivial.
Qed.

Lemma le_embed_embed_mu
  (𝜇: BurrowCtx) M `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (a b : M) : tpcm_le a b -> tpcm_le (mu_embed M 𝜇 a) (mu_embed M 𝜇 b).
Proof. unfold mu_embed. apply le_embed_embed. Qed.

Lemma borrow_nonseparating_conjunction'
  {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (a b c : M) 𝜅 𝛾 state1 state2
  (abcr: ∀ r , m_valid r -> tpcm_le a r -> tpcm_le b r -> tpcm_le c r)
    (b1: is_borrow' 𝜅 𝛾 a state1)
    (b2: is_borrow' 𝜅 𝛾 b state2)
    : is_borrow' 𝜅 𝛾 c (state1 ⋅ state2).
Proof.
  unfold is_borrow' in *.
  apply borrow_nonseparating_conjunction with (a0 := mu_embed M 𝜇 a) (b0 := mu_embed M 𝜇 b); trivial.
  intros.
  assert (m_valid (mu_eproject M 𝜇 r)) as ef1
    by (unfold mu_eproject; apply valid_eproject; trivial).
  have abcr' := abcr (mu_eproject M 𝜇 r) ef1
    (le_a_eproject_of_le_embed_r_mu 𝜇 M a r H0)
    (le_a_eproject_of_le_embed_r_mu 𝜇 M b r H1).
  apply le_embed_r_of_le_c_eproject_mu. trivial.
Qed.

Lemma rel_defined_mu
    {𝜇: BurrowCtx} {R M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_hastpcm: !HasTPCM 𝜇 M} `{r_hastpcm: !HasTPCM 𝜇 R}
    (ref : Refinement R M)
    `{hr: !HasRef 𝜇 ref} (r: InfiniteCopies (bc_small_M 𝜇))
 : rel_defined (InfiniteCopies (bc_small_M 𝜇)) (InfiniteCopies (bc_small_M 𝜇))
      (refinement_of (FinalRINormal (bc_small_RI 𝜇) hasref_ri)) r
   <-> m_valid r /\ rel_defined R M ref (mu_eproject R 𝜇 r).
Proof.
  unfold refinement_of, bc_refinement_index.
  unfold refinement_embed_dst, rel_defined.
  unfold refinement_embed_src, rel_defined.
  unfold mu_eproject.
  have j := @hasref_is 𝜇 R M r_eqdec r_tpcm m_eqdec m_tpcm r_hastpcm m_hastpcm ref hr.
  unfold "≡", ref_equiv in j. destruct_ands.
  unfold rel_defined in *.
  rewrite H.
  unfold refinement_embed_dst, rel_defined.
  unfold refinement_embed_src, rel_defined.
  trivial.
Qed.

Lemma rel_mu
    {𝜇: BurrowCtx} {R M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_hastpcm: !HasTPCM 𝜇 M} `{r_hastpcm: !HasTPCM 𝜇 R}
    (ref : Refinement R M)
    `{hr: !HasRef 𝜇 ref} (r: InfiniteCopies (bc_small_M 𝜇))
 : rel (InfiniteCopies (bc_small_M 𝜇)) (InfiniteCopies (bc_small_M 𝜇))
      (refinement_of (FinalRINormal (bc_small_RI 𝜇) hasref_ri)) r
   = mu_embed M 𝜇 (rel R M ref (mu_eproject R 𝜇 r)).
Proof.
  unfold refinement_of, bc_refinement_index.
  unfold refinement_embed_dst, rel.
  unfold refinement_embed_src, rel.
  unfold mu_embed, mu_eproject.
  have j := @hasref_is 𝜇 R M r_eqdec r_tpcm m_eqdec m_tpcm r_hastpcm m_hastpcm ref hr.
  unfold "≡", ref_equiv in j. destruct_ands.
  unfold rel in *.
  rewrite H0.
  unfold refinement_embed_dst, rel.
  unfold refinement_embed_src, rel.
  trivial.
Qed.

Lemma borrow_back'
  {𝜇: BurrowCtx} {R M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_hastpcm: !HasTPCM 𝜇 M} `{r_hastpcm: !HasTPCM 𝜇 R}
    (ref : Refinement R M)
    `{hr: !HasRef 𝜇 ref}
    𝛼 𝛾 f m 𝜅 state
  (bbcond : ∀ p: R, rel_defined R M ref (dot f p) ->
      tpcm_le m (rel R M ref (dot f p)))
  (ib: is_borrow' 𝜅 (extend_loc 𝛼 ref 𝛾) f state)
  : is_borrow' 𝜅 𝛾 m state.
Proof.
  unfold is_borrow' in *.
  unfold extend_loc in ib.
  apply borrow_back with (alpha:=𝛼) (f0 := mu_embed R 𝜇 f) (ri := FinalRINormal (bc_small_RI 𝜇) (
    (@hasref_ri 𝜇 R M r_eqdec r_tpcm m_eqdec m_tpcm r_hastpcm m_hastpcm ref hr))); trivial.
  intro. rewrite rel_defined_mu.
  intros. rewrite rel_mu.
  destruct_ands.
  apply le_embed_embed_mu.
  unfold mu_eproject, mu_embed. rewrite <- eproject_dot.
  rewrite eproject_embed.
  apply bbcond.
  unfold mu_eproject, mu_embed in H0. rewrite <- eproject_dot in H0.
  rewrite eproject_embed in H0.
  trivial.
Qed.

Lemma mu_embed_product
  {𝜇: BurrowCtx}
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {N} `{!EqDecision N} `{!TPCM N} `{!HasTPCM 𝜇 N}
  (m1: M) (m2: N)
  : (mu_embed (M * N) 𝜇 (m1, m2)) = (ic_pair (mu_embed M 𝜇 m1) (mu_embed N 𝜇 m2)).
Proof.
  unfold mu_embed. unfold embed. unfold inctx_embed, product_hastpcm.
  unfold ic_tpcm_embed_two. trivial.
Qed.

Lemma borrow_back_left'
  {𝜇: BurrowCtx}
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {N} `{!EqDecision N} `{!TPCM N} `{!HasTPCM 𝜇 N}
  (𝛾1 𝛾2 : BurrowLoc 𝜇) (m1 : M) (m2 : N) 𝜅 (state : BurrowState 𝜇)
  (ib: is_borrow' 𝜅 (cross_loc 𝛾1 𝛾2) (m1, m2) state)
  : is_borrow' 𝜅 𝛾1 m1 state.
Proof. unfold is_borrow' in *.
  apply (borrow_back_left 𝛾1 𝛾2 (mu_embed M 𝜇 m1) (mu_embed N 𝜇 m2) 𝜅 state).
  unfold cross_loc in ib.
  unfold pair_up, bc_refinement_index.
  unfold mu_embed in ib.
  unfold embed in ib.
  rewrite <- mu_embed_product. unfold mu_embed. trivial.
Qed.
  
Lemma borrow_back_right'
  {𝜇: BurrowCtx}
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {N} `{!EqDecision N} `{!TPCM N} `{!HasTPCM 𝜇 N}
  (𝛾1 𝛾2 : BurrowLoc 𝜇) (m1 : M) (m2 : N) 𝜅 (state : BurrowState 𝜇)
  (ib: is_borrow' 𝜅 (cross_loc 𝛾1 𝛾2) (m1, m2) state)
  : is_borrow' 𝜅 𝛾2 m2 state.
Proof. unfold is_borrow' in *.
  apply (borrow_back_right 𝛾1 𝛾2 (mu_embed M 𝜇 m1) (mu_embed N 𝜇 m2) 𝜅 state).
  unfold cross_loc in ib.
  unfold pair_up, bc_refinement_index.
  unfold mu_embed in ib.
  unfold embed in ib.
  rewrite <- mu_embed_product. unfold mu_embed. trivial.
Qed.
  
Lemma borrow_expire'
  {𝜇: BurrowCtx}
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  (m: M) 𝛾 𝜅 (p: BurrowState 𝜇)
  (kappa_nonempty : 𝜅 ≠ empty_lifetime)
  (si: ✓(active 𝜅 ⋅ reserved' 𝜅 𝛾 m ⋅ p))
     : ✓(live' 𝛾 m ⋅ p).
Proof.
  unfold live', reserved' in *.
  apply borrow_expire with (kappa:=𝜅); trivial.
Qed.

Lemma borrow_exchange_normal'
  {𝜇: BurrowCtx} {M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{m_hastpcm: !HasTPCM 𝜇 M}
      b 𝜅 𝛾 (m z m' : M) (p: BurrowState 𝜇)
  (isb: is_borrow' 𝜅 𝛾 z b)
  (exchange_cond: mov (dot m z) (dot m' z))
  (si: ✓(active 𝜅 ⋅ live' 𝛾 m ⋅ b ⋅ p))
     : ✓(active 𝜅 ⋅ live' 𝛾 m' ⋅ b ⋅ p).
Proof. unfold live' in *.
  apply borrow_exchange_normal_valid with (m0:=mu_embed M 𝜇 m) (z0:=mu_embed M 𝜇 z); trivial.
  unfold mu_embed. rewrite embed_dot. rewrite embed_dot.
  apply mov_embed. trivial.
Qed.

Lemma mu_embed_dot
  {𝜇: BurrowCtx} {M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{m_hastpcm: !HasTPCM 𝜇 M}
  (a b: M) : mu_embed M 𝜇 (dot a b) = dot (mu_embed M 𝜇 a) (mu_embed M 𝜇 b).
Proof.
  unfold mu_embed. rewrite embed_dot. trivial.
Qed.

Lemma mu_eproject_dot
  {𝜇: BurrowCtx} {M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{m_hastpcm: !HasTPCM 𝜇 M}
  a b : mu_eproject M 𝜇 (dot a b) = dot (mu_eproject M 𝜇 a) (mu_eproject M 𝜇 b).
Proof.
  unfold mu_eproject. rewrite eproject_dot. trivial.
Qed.

Lemma mu_eproject_mu_embed
  {𝜇: BurrowCtx} {M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{m_hastpcm: !HasTPCM 𝜇 M}
  a : mu_eproject M 𝜇 (mu_embed M 𝜇 a) = a.
Proof.
  unfold mu_eproject, mu_embed. rewrite eproject_embed. trivial.
Qed.

Lemma mu_embed_mu_eproject
  (𝜇: BurrowCtx) (M: Type)
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{m_hastpcm: !HasTPCM 𝜇 M}
  b : b = dot (mu_embed M 𝜇 (mu_eproject M 𝜇 b)) (mu_erest M 𝜇 b).
Proof. unfold mu_embed, mu_eproject. apply embed_eproject. Qed.

Lemma borrow_exchange_cond_mu_embed
  {𝜇: BurrowCtx} {R M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_hastpcm: !HasTPCM 𝜇 M} `{r_hastpcm: !HasTPCM 𝜇 R}
    (ref : Refinement R M) `{hr: !HasRef 𝜇 ref}
  (m m' : M) (f z f': R)
  (exchange_cond : borrow_exchange_cond ref z m f m' f')
  : borrow_exchange_cond (refinement_of (FinalRINormal (bc_small_RI 𝜇) hasref_ri))
    (mu_embed R 𝜇 z) (mu_embed M 𝜇 m) (mu_embed R 𝜇 f) (mu_embed M 𝜇 m') 
    (mu_embed R 𝜇 f').
Proof.
  unfold borrow_exchange_cond in *.
  intro.
  rewrite rel_defined_mu.
  rewrite rel_defined_mu.
  rewrite rel_mu.
  rewrite rel_mu.
  intros. destruct_ands.
  rewrite <- mu_embed_dot in H0.
  rewrite mu_eproject_dot in H0.
  rewrite mu_eproject_mu_embed in H0.
  have ec := exchange_cond (mu_eproject R 𝜇 p) H0.
  destruct_ands.
  have pq := @mu_embed_mu_eproject 𝜇 R r_eqdec r_tpcm r_hastpcm p.
  have mvf'z := rel_valid_left _ _ ref _ H1.
  repeat split.
  - rewrite pq.
    rewrite tpcm_assoc.
    rewrite <- mu_embed_dot.
    rewrite <- mu_embed_dot.
    unfold mu_embed, mu_eproject, mu_erest.
    apply valid_dot_rest.
    + unfold mu_eproject in mvf'z. trivial.
    + rewrite tpcm_comm in H.
      have j := valid_monotonic p _ H. trivial.
  -
    rewrite mu_eproject_dot.
    rewrite mu_eproject_dot.
    rewrite mu_eproject_mu_embed.
    rewrite mu_eproject_mu_embed. trivial.
  - 
    repeat (rewrite <- mu_embed_dot).
    apply mov_embed.
    repeat (rewrite mu_eproject_dot).
    rewrite mu_eproject_mu_embed.
    rewrite mu_eproject_mu_embed.
    trivial.
Qed.

Lemma borrow_exchange'
  {𝜇: BurrowCtx} {R M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_hastpcm: !HasTPCM 𝜇 M} `{r_hastpcm: !HasTPCM 𝜇 R}
    (ref : Refinement R M)
    `{hr: !HasRef 𝜇 ref}
      b 𝜅 𝛾 (m m' : M) (f z f': R) 𝛼 (p: BurrowState 𝜇)
  (isb: is_borrow' 𝜅 (extend_loc 𝛼 ref 𝛾) z b)
  (exchange_cond: borrow_exchange_cond ref z m f m' f')
  (si: ✓(active 𝜅 ⋅ live' (extend_loc 𝛼 ref 𝛾) f ⋅ b ⋅ live' 𝛾 m ⋅ p))
     : ✓(active 𝜅 ⋅ live' (extend_loc 𝛼 ref 𝛾) f' ⋅ b ⋅ live' 𝛾 m' ⋅ p).
Proof. unfold live', is_borrow' in *.
  apply borrow_exchange_valid with (m0 := mu_embed M 𝜇 m)
      (f0 := mu_embed R 𝜇 f)
      (z0 := mu_embed R 𝜇 z); trivial.
  unfold refinement_of, bc_refinement_index.
  apply borrow_exchange_cond_mu_embed. trivial.
Qed.

Lemma initialize_ext'
  {𝜇: BurrowCtx} {R M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{r_eqdec: !EqDecision R, r_tpcm: !TPCM R}
    `{m_hastpcm: !HasTPCM 𝜇 M} `{r_hastpcm: !HasTPCM 𝜇 R}
    (ref : Refinement R M)
    `{hr: !HasRef 𝜇 ref}
  𝛾 (m: M) (f: R) (p: BurrowState 𝜇)
  (is_rel_def: rel_defined R M ref f)
  (is_rel: rel R M ref f = m)
  (si: ✓(live' 𝛾 m ⋅ p))
  : ∃ 𝛼 , ✓(live' (extend_loc 𝛼 ref 𝛾) f ⋅ p).
Proof.
  unfold live' in *. unfold extend_loc.
  eapply initialize_ext_valid with (m0 := mu_embed M 𝜇 m); trivial.
  - rewrite rel_defined_mu. split; trivial.
    + apply valid_embed. exact (rel_valid_left _ _ _ _ is_rel_def).
    + rewrite mu_eproject_mu_embed. trivial.
  - rewrite rel_mu. f_equal. rewrite mu_eproject_mu_embed. trivial.
Qed.

Lemma initialize_normal'
  {𝜇: BurrowCtx} {M: Type}
    `{m_eqdec: !EqDecision M, m_tpcm: !TPCM M}
    `{m_hastpcm: !HasTPCM 𝜇 M}
  (m: M) p
  (is_val: m_valid m)
  (si: ✓ p)
  : ∃ 𝛾 , ✓ (live' 𝛾 m ⋅ p).
Proof.
  unfold live'.
  assert (m_valid (mu_embed M 𝜇 m)) as mvm
    by (apply valid_embed; trivial).
  have j := initialize_normal_valid (mu_embed M 𝜇 m) p mvm si.
  deex.
  exists (BaseLoc (FinalRI (bc_small_RI 𝜇)) alpha).
  trivial.
Qed.

Lemma swap_cross_left'
  {𝜇: BurrowCtx}
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {N} `{!EqDecision N} `{!TPCM N} `{!HasTPCM 𝜇 N}
  (𝛾1 𝛾2: BurrowLoc 𝜇) (m m1: M) (m2 : N) (p: BurrowState 𝜇)
  (si: ✓(live' 𝛾1 m ⋅ live' (cross_loc 𝛾1 𝛾2) (m1, m2) ⋅ p))
     : ✓(live' 𝛾1 m1 ⋅ live' (cross_loc 𝛾1 𝛾2) (m, m2) ⋅ p).
Proof.
  unfold live' in *.
  rewrite mu_embed_product.
  
  have j := @swap_cross_left_valid _ _ _ _ _ _ _ 𝛾1 𝛾2
      (mu_embed M 𝜇 m) (mu_embed M 𝜇 m1) (mu_embed N 𝜇 m2) p.
  have j0 := j EqDecision0 TPCM0 HasTPCM0 EqDecision0 TPCM0 HasTPCM0
      EqDecision1 TPCM1 HasTPCM1.
  unfold pair_up, bc_refinement_index in j0.
  apply j0.
  trivial.
Qed.

Lemma swap_cross_right'
  {𝜇: BurrowCtx}
    {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    {N} `{!EqDecision N} `{!TPCM N} `{!HasTPCM 𝜇 N}
  (𝛾1 𝛾2: BurrowLoc 𝜇) (m: N) (m1: M) (m2 : N) (p: BurrowState 𝜇)
  (si: ✓(live' 𝛾2 m ⋅ live' (cross_loc 𝛾1 𝛾2) (m1, m2) ⋅ p))
     : ✓(live' 𝛾2 m2 ⋅ live' (cross_loc 𝛾1 𝛾2) (m1, m) ⋅ p).
Proof.
  unfold live' in *.
  rewrite mu_embed_product.
  
  have j := @swap_cross_right_valid _ _ _ _ _ _ _ 𝛾1 𝛾2
      (mu_embed N 𝜇 m) (mu_embed M 𝜇 m1) (mu_embed N 𝜇 m2) p.
  have j0 := j EqDecision1 TPCM1 HasTPCM1 EqDecision0 TPCM0 HasTPCM0
      EqDecision1 TPCM1 HasTPCM1.
  unfold pair_up, bc_refinement_index in j0.
  apply j0.
  trivial.
Qed.

Lemma state_no_live_reserved'
  {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  𝜅 𝛾 m : state_no_live (reserved' 𝜅 𝛾 m).
Proof. unfold reserved'. apply state_no_live_reserved. Qed.

Lemma is_borrow_reserved'
  {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  𝜅 𝛾 m : is_borrow' 𝜅 𝛾 m (reserved' 𝜅 𝛾 m).
Proof. unfold reserved', is_borrow'. apply is_borrow_reserved. Qed.

Lemma is_borrow_unit'
  {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
    (lt: Lifetime) (loc: BurrowLoc 𝜇)
  : is_borrow' lt loc (unit: M) state_unit.
Proof. unfold is_borrow'. unfold mu_embed. rewrite unit_embed. apply is_borrow_unit.
Qed.

Lemma is_borrow_weaken'
  {𝜇: BurrowCtx} {M} `{!EqDecision M} `{!TPCM M} `{!HasTPCM 𝜇 M}
  𝜅 𝛾 (a b: M) state
  : is_borrow' 𝜅 𝛾 (dot a b) state -> is_borrow' 𝜅 𝛾 a state.
Proof.
  intros. unfold is_borrow' in *.
  rewrite mu_embed_dot in H.
  apply is_borrow_weaken with (b0 := mu_embed M 𝜇 b). trivial.
Qed.

