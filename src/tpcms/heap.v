Require Import Burrow.trees.
From stdpp Require Import gmap.

Require Import cpdt.CpdtTactics.
Require Import coq_tricks.Deex.

Require Import Tpcms.auth_frag.
Require Import Tpcms.gmap.

Definition HeapT P V `{!EqDecision V} `{!EqDecision P} `{!Countable P} :=
    AuthFrag (gmap P (option V)).
    
Definition map_somes {P} {V} `{Countable P} (σ : gmap P V) : gmap P (option V)
  := fmap Some σ.

Lemma lookup_map_somes {P} {V} `{Countable P} (σ : gmap P V) k
  : map_somes σ !! k = match σ !! k with Some x => Some (Some x) | None => None end.
Proof.
  unfold map_somes. rewrite lookup_fmap. unfold "<$>", option_fmap, option_map. trivial.
Qed.

Lemma map_somes_insert {P} {V} `{Countable P} (σ: gmap P V) l v
  : map_somes (<[ l := v ]> σ) = <[ l := Some v ]> (map_somes σ).
Proof.
  unfold map_somes. rewrite fmap_insert. trivial. Qed.

Section HeapT.

Context P V `{!EqDecision V} `{!EqDecision P} `{!Countable P}.
  
Lemma heapt_alloc (m : gmap P (option V)) (l: P) (v: V)
  : m !! l = None →
  mov (auth m) (dot (auth ((<[l:= Some v]> m))) (frag ({[l := Some v]} : gmap P (option V)))).
Proof. intro.
  unfold mov, auth, frag, af_tpcm, af_mov. intros. unfold af_dot.
  unfold dot, gmap_tpcm. destruct z.
  unfold af_valid in *.
  unfold auth_dot in *.
  unfold af_dot in *.
  unfold auth_dot in *.
  unfold m_valid, gmap_tpcm, gmap_valid in H0.
  destruct o.
  - trivial.
  - destruct_ands. deex. split.
    + unfold m_valid, gmap_valid. intro.
      have h : Decision (k = l) by solve_decision. destruct h.
      * subst k. rewrite lookup_insert. trivial.
      * rewrite lookup_insert_ne.
        -- have q := H0 k. destruct (m !! k); trivial.
        -- intuition.
    + exists c.
      rewrite unit_dot_left in H1.
      subst m.
      rewrite <- gmap_dot_assoc.
      unfold dot in *. unfold gmap_dot, unit in *.
      apply map_eq. intro.
      unfold gmerge in *.
      have q := H0 i. clear H0.
      have h : Decision (i = l) by solve_decision. destruct h.
      * subst i. rewrite lookup_insert.
          rewrite lookup_merge. unfold diag_None.
          rewrite lookup_merge. unfold diag_None.
          rewrite lookup_merge. unfold diag_None.
          rewrite lookup_merge in q. unfold diag_None in q.
          rewrite lookup_merge in H. unfold diag_None in H.
          rewrite lookup_singleton.
          rewrite lookup_empty.
          destruct (c !! l), (g !! l); intuition.
          -- discriminate.
          -- discriminate.
      * rewrite lookup_insert_ne.
        -- rewrite lookup_merge. unfold diag_None.
           rewrite lookup_merge. unfold diag_None.
           rewrite lookup_merge. unfold diag_None.
           rewrite lookup_merge. unfold diag_None.
           rewrite lookup_merge in q. unfold diag_None in q.
           rewrite lookup_merge in H. unfold diag_None in H.
           rewrite lookup_singleton_ne; trivial.
           rewrite lookup_empty.
           destruct (c !! i), (g !! i); intuition.
           crush.
        -- crush.
Qed.

Lemma auth_frag_agree' (l: P) (v: V) (m: gmap P (option V))
  (va : m_valid (dot (auth m) (frag ({[l := Some v]} : gmap P (option V)))))
  : m !! l = Some (Some v).
Proof.
  unfold m_valid, af_tpcm, af_valid, dot, gmap_tpcm, af_dot, auth, frag,
      auth_dot, gmap_dot in va. destruct_ands. deex.
  rewrite unit_dot_left in H0.
  subst m.
  rewrite lookup_merge. unfold diag_None. rewrite lookup_singleton.
  unfold m_valid, gmap_valid in H. have h := H l. clear H.
  rewrite lookup_merge in h. unfold diag_None in h. rewrite lookup_singleton in h.
  unfold gmerge in h. destruct (c !! l).
  - contradiction.
  - unfold gmerge. trivial.
Qed.

Lemma auth_frag_agree (l: P) (v: V) (m: gmap P V)
  (va : m_valid (dot (auth (map_somes m)) (frag ({[l := Some v]} : gmap P (option V)))))
  : m !! l = Some v.
Proof.
  have h := auth_frag_agree' l v (map_somes m) va.
  unfold map_somes. rewrite lookup_fmap in h. unfold "<$>" in h.
  unfold option_fmap, option_map in h. destruct (m !! l); crush.
Qed.

Lemma auth_frag_update' (l: P) (v1 v2: V) (m: gmap P (option V))
  (va : m !! l = Some (Some v1))
  : mov (dot (auth m) (frag {[l := Some v1]}))
    (dot (auth (<[l := Some v2]> m)) (frag {[l := Some v2]})).
Proof.
  unfold mov, af_tpcm, af_mov. intro. unfold af_valid, af_dot, dot, gmap_tpcm,
      auth, frag. destruct z. unfold auth_dot.
  unfold m_valid, gmap_valid, gmap_dot. destruct o.
  - intuition.
  - intros. destruct_ands. deex. split.
    + intro. have h := H k. clear H.
      have ed : Decision (k = l) by solve_decision. destruct ed.
      * subst l. rewrite lookup_insert. trivial.
      * rewrite lookup_insert_ne; trivial. crush.
    + exists c.
      subst m.
      apply map_eq. intro k. have h := H k. clear H.
      have ed : Decision (k = l) by solve_decision. destruct ed.
      * subst l. rewrite lookup_insert. unfold gmerge in *.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_singleton.
        unfold unit.
        rewrite lookup_empty.
        rewrite lookup_merge in h. unfold diag_None in h.
        rewrite lookup_merge in h. unfold diag_None in h.
        rewrite lookup_merge in h. unfold diag_None in h.
        rewrite lookup_singleton in h.
        unfold unit in h.
        rewrite lookup_empty in h.
        destruct (g !! k), (c !! k); trivial; contradiction.
      * assert (l ≠ k) by crush.
        unfold gmerge.
        rewrite lookup_insert_ne; trivial.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_merge. unfold diag_None.
        rewrite lookup_merge. unfold diag_None.
        unfold unit. rewrite lookup_empty.
        rewrite lookup_singleton_ne; trivial.
        rewrite lookup_singleton_ne; trivial.
Qed.

Lemma auth_frag_update (l: P) (v1 v2: V) (σ: gmap P V)
  (va : σ !! l = Some v1)
  : mov (dot (auth (map_somes σ)) (frag {[l := Some v1]}))
    (dot (auth (map_somes (<[l:=v2]> σ))) (frag {[l := Some v2]})).
Proof.
  rewrite map_somes_insert.
  have j := auth_frag_update' l v1 v2 (map_somes σ). apply j.
  unfold map_somes. rewrite lookup_fmap. unfold "<$>".
  unfold option_fmap, option_map. destruct (σ !! l); crush.
Qed.

Lemma auth_empty_valid
  : m_valid (auth (∅ : gmap P (option V))).
Proof. unfold m_valid, af_tpcm, af_valid, auth. split.
  - replace ((∅ : gmap P (option V))) with (unit : gmap P (option V)).
    apply unit_valid. trivial.
  - exists (unit : gmap P (option V)). rewrite unit_dot. trivial.
Qed.

Lemma auth_map_somes (σ : gmap P V)
  : m_valid (auth (map_somes σ)).
Proof. unfold m_valid, af_tpcm, af_valid, auth. split.
  - unfold m_valid, gmap_tpcm. unfold gmap_valid. intro. 
    rewrite lookup_map_somes. destruct (σ !! k); trivial.
  - exists (map_somes σ). rewrite unit_dot_left. trivial.
Qed.

End HeapT.
