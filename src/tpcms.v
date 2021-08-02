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

#[refine]
Instance pair_tpcm (M: Type) (N: Type)
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
  
  valid_embed: ∀ a , m_valid (embed a) <-> m_valid a ;
  dot_embed: ∀ a b , dot (embed a) (embed b) = embed (dot a b) ;
  mov_embed: ∀ a b , mov (embed a) (embed b) <-> mov a b ;
  unit_embed: embed unit = unit ;
  eproject_embed : ∀ a , eproject (embed a) = a ;
}.

#[refine]
Instance pair_tpcm_embed_self (M: Type)
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
Qed.

#[refine]
Instance pair_tpcm_embed_left (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed M (M * N) := {
    embed := λ m , (m, unit) ;
    eproject := λ p , match p with (m, _) => m end ;
}.
Proof.
  - intros. split.
    + intro. unfold m_valid in H. unfold pair_tpcm in H. destruct_ands. trivial.
    + intro. unfold m_valid. unfold pair_tpcm. split; trivial. apply unit_valid.
  - intros.
    unfold dot. unfold pair_tpcm. f_equal. apply unit_dot.
  - intros. split.
    + intro. unfold mov, pair_tpcm in H. destruct_ands; trivial.
    + intro. unfold mov, pair_tpcm. split; trivial. apply reflex.
  - unfold unit at 3. unfold pair_tpcm. trivial.
  - trivial.
Defined.

#[refine]
Instance pair_tpcm_embed_right (M: Type) (N: Type)
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision N} `{!TPCM N}
  : TPCMEmbed N (M * N) := {
    embed := λ n , (unit, n) ;
    eproject := λ p , match p with (_, n) => n end ;
}.
Proof.
  - intros. split.
    + intro. unfold m_valid in H. unfold pair_tpcm in H. destruct_ands. trivial.
    + intro. unfold m_valid. unfold pair_tpcm. split; trivial. apply unit_valid.
  - intros.
    unfold dot. unfold pair_tpcm. f_equal. apply unit_dot.
  - intros. split.
    + intro. unfold mov, pair_tpcm in H. destruct_ands; trivial.
    + intro. unfold mov, pair_tpcm. split; trivial. apply reflex.
  - unfold unit at 3. unfold pair_tpcm. trivial.
  - trivial.
Defined.

Definition refinement_embed_src R M B
    `{!EqDecision R} `{!TPCM R}
    `{!EqDecision M} `{!TPCM M}
    `{!EqDecision B} `{!TPCM B}
    `{!TPCMEmbed R B} (ref: Refinement R M) : Refinement B M.
Proof. refine ({|
  rel_defined := λ b , ∃ r , embed r = b /\ rel_defined R M ref (eproject b) ;
  rel := λ b , (rel R M ref (eproject b)) ;
  rel_valid_left := _ ;
  rel_defined_unit := _ ;
  rel_unit := _ ;
  mov_refines := _ ;
|}).
 - intros. deex. destruct_ands.
    subst r. rewrite valid_embed.
      rewrite eproject_embed in H0.
      apply (rel_valid_left R M ref r0). trivial.
 - exists unit. split.
    + apply unit_embed.
    + rewrite <- unit_embed. rewrite eproject_embed. apply rel_defined_unit.
 - rewrite <- unit_embed. rewrite eproject_embed. rewrite rel_unit. trivial.
 - intros. deex. destruct_ands. split.
    + 
    
Defined.
