From Coq Require Import Min.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree numbers.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export proofmode.
From lrust.lang Require Export lang.
From iris.prelude Require Import options.
Import uPred.

Definition lock_stateR : cmra :=
  csumR (exclR unitO) natR.

Definition heapUR : ucmra :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (agreeR valO)).

Definition heap_freeableUR : ucmra :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitO))).

Class heapGS Σ := HeapGS {
  heap_inG :> inG Σ (authR heapUR);
  heap_freeable_inG :> inG Σ (authR heap_freeableUR);
  heap_name : gname;
  heap_freeable_name : gname
}.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.
Definition to_heap : state → heapUR :=
  fmap (λ v, (1%Qp, to_lock_stateR (v.1), to_agree (v.2))).
Definition heap_freeable_rel (σ : state) (hF : heap_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs →
    qs.2 ≠ ∅ ∧ ∀ i, is_Some (σ !! (blk, i)) ↔ is_Some (qs.2 !! i).

Section definitions.
  Context `{!heapGS Σ}.

  Definition heap_mapsto_st (st : lock_state)
             (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own heap_name (◯ {[ l := (q, to_lock_stateR st, to_agree v) ]}).

  Definition heap_mapsto_def (l : loc) (q : Qp) (v: val) : iProp Σ :=
    heap_mapsto_st (RSt 0) l q v.
  Definition heap_mapsto_aux : seal (@heap_mapsto_def). Proof. by eexists. Qed.
  Definition heap_mapsto := unseal heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    seal_eq heap_mapsto_aux.

  Definition heap_mapsto_vec (l : loc) (q : Qp) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, heap_mapsto (l +ₗ i) q v)%I.

  Fixpoint inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
    match n with O => ∅ | S n => <[i0 := Excl ()]>(inter (i0+1) n) end.

  Definition heap_freeable_def (l : loc) (q : Qp) (n: nat) : iProp Σ :=
    own heap_freeable_name (◯ {[ l.1 := (q, inter (l.2) n) ]}).
  Definition heap_freeable_aux : seal (@heap_freeable_def). Proof. by eexists. Qed.
  Definition heap_freeable := unseal heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    seal_eq heap_freeable_aux.

  Definition heap_ctx (σ:state) : iProp Σ :=
    (∃ hF, own heap_name (● to_heap σ)
         ∗ own heap_freeable_name (● hF)
         ∗ ⌜heap_freeable_rel σ hF⌝)%I.
End definitions.

Global Typeclasses Opaque heap_mapsto heap_freeable heap_mapsto_vec.
Global Instance: Params (@heap_mapsto) 4 := {}.
Global Instance: Params (@heap_freeable) 5 := {}.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : bi_scope.

Notation "l ↦∗{ q } vl" := (heap_mapsto_vec l q vl)
  (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope.
Notation "l ↦∗ vl" := (heap_mapsto_vec l 1 vl) (at level 20) : bi_scope.

Notation "l ↦∗{ q }: P" := (∃ vl, l ↦∗{ q } vl ∗ P vl)%I
  (at level 20, q at level 50, format "l  ↦∗{ q }:  P") : bi_scope.
Notation "l ↦∗: P " := (∃ vl, l ↦∗ vl ∗ P vl)%I
  (at level 20, format "l  ↦∗:  P") : bi_scope.

Notation "†{ q } l … n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : bi_scope.

Section to_heap.
  Implicit Types σ : state.

  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. case (σ !! l)=> [[[|n] v]|] //=. Qed.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.

  Lemma to_heap_insert σ l x v :
    to_heap (<[l:=(x, v)]> σ)
    = <[l:=(1%Qp, to_lock_stateR x, to_agree v)]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma to_heap_delete σ l : to_heap (delete l σ) = delete l (to_heap σ).
  Proof. by rewrite /to_heap fmap_delete. Qed.
End to_heap.

Section heap.
  Context `{!heapGS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  (** General properties of mapsto and freeable *)
  Global Instance heap_mapsto_timeless l q v : Timeless (l↦{q}v).
  Proof. rewrite heap_mapsto_eq /heap_mapsto_def. apply _. Qed.

  Global Instance heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros p q.
    by rewrite heap_mapsto_eq -own_op -auth_frag_op singleton_op -pair_op agree_idemp.
  Qed.
  Global Instance heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split; first done. apply _. Qed.
  Global Instance frame_heap_mapsto p l v q1 q2 RES :
    FrameFractionalHyps p (l ↦{q1} v) (λ q, l ↦{q} v)%I RES q1 q2 →
    Frame p (l ↦{q1} v) (l ↦{q2} v) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance heap_mapsto_vec_timeless l q vl : Timeless (l ↦∗{q} vl).
  Proof. rewrite /heap_mapsto_vec. apply _. Qed.

  Global Instance heap_mapsto_vec_fractional l vl: Fractional (λ q, l ↦∗{q} vl)%I.
  Proof.
    intros p q. rewrite /heap_mapsto_vec -big_sepL_sep.
    by setoid_rewrite (fractional (Φ := λ q, _ ↦{q} _)%I).
  Qed.
  Global Instance heap_mapsto_vec_as_fractional l q vl:
    AsFractional (l ↦∗{q} vl) (λ q, l ↦∗{q} vl)%I q.
  Proof. split; first done. apply _. Qed.
  Global Instance frame_heap_mapsto_vec p l vl q1 q2 RES :
    FrameFractionalHyps p (l ↦∗{q1} vl) (λ q, l ↦∗{q} vl)%I RES q1 q2 →
    Frame p (l ↦∗{q1} vl) (l ↦∗{q2} vl) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance heap_freeable_timeless q l n : Timeless (†{q}l…n).
  Proof. rewrite heap_freeable_eq /heap_freeable_def. apply _. Qed.

  Lemma heap_mapsto_agree l q1 q2 v1 v2 : l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid=> -[? /to_agree_op_inv_L->]; eauto.
  Qed.

  Lemma heap_mapsto_vec_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. by rewrite /heap_mapsto_vec. Qed.

  Lemma heap_mapsto_vec_app l q vl1 vl2 :
    l ↦∗{q} (vl1 ++ vl2) ⊣⊢ l ↦∗{q} vl1 ∗ (l +ₗ length vl1) ↦∗{q} vl2.
  Proof.
    rewrite /heap_mapsto_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma heap_mapsto_vec_singleton l q v : l ↦∗{q} [v] ⊣⊢ l ↦{q} v.
  Proof. by rewrite /heap_mapsto_vec /= shift_loc_0 right_id. Qed.

  Lemma heap_mapsto_vec_cons l q v vl:
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vl.
  Proof.
    by rewrite (heap_mapsto_vec_app l q [v] vl) heap_mapsto_vec_singleton.
  Qed.

  Lemma heap_mapsto_vec_op l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗{q1} vl1 ∗ l ↦∗{q2} vl2 ⊣⊢ ⌜vl1 = vl2⌝ ∧ l ↦∗{q1+q2} vl1.
  Proof.
    intros Hlen%Forall2_same_length. apply (anti_symm (⊢)).
    - revert l. induction Hlen as [|v1 v2 vl1 vl2 _ _ IH]=> l.
      { rewrite !heap_mapsto_vec_nil. iIntros "_"; auto. }
      rewrite !heap_mapsto_vec_cons. iIntros "[[Hv1 Hvl1] [Hv2 Hvl2]]".
      iDestruct (IH (l +ₗ 1) with "[$Hvl1 $Hvl2]") as "[% $]"; subst.
      rewrite (inj_iff (.:: vl2)).
      iDestruct (heap_mapsto_agree with "[$Hv1 $Hv2]") as %<-.
      iSplit; first done. iFrame.
    - by iIntros "[% [$ Hl2]]"; subst.
  Qed.

  Lemma heap_mapsto_pred_op l q1 q2 n (Φ : list val → iProp Σ) :
    (∀ vl, Φ vl -∗ ⌜length vl = n⌝) →
    l ↦∗{q1}: Φ ∗ l ↦∗{q2}: (λ vl, ⌜length vl = n⌝) ⊣⊢ l ↦∗{q1+q2}: Φ.
  Proof.
    intros Hlen. iSplit.
    - iIntros "[Hmt1 Hmt2]".
      iDestruct "Hmt1" as (vl) "[Hmt1 Hown]". iDestruct "Hmt2" as (vl') "[Hmt2 %]".
      iDestruct (Hlen with "Hown") as %?.
      iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op; last congruence.
      iDestruct "Hmt" as "[_ Hmt]". iExists vl. by iFrame.
    - iIntros "Hmt". iDestruct "Hmt" as (vl) "[[Hmt1 Hmt2] Hown]".
      iDestruct (Hlen with "Hown") as %?.
      iSplitL "Hmt1 Hown"; iExists _; by iFrame.
  Qed.

  Lemma heap_mapsto_pred_wand l q Φ1 Φ2 :
    l ↦∗{q}: Φ1 -∗ (∀ vl, Φ1 vl -∗ Φ2 vl) -∗ l ↦∗{q}: Φ2.
  Proof.
    iIntros "Hm Hwand". iDestruct "Hm" as (vl) "[Hm HΦ]". iExists vl.
    iFrame "Hm". by iApply "Hwand".
  Qed.

  Lemma heap_mapsto_pred_iff_proper l q Φ1 Φ2 :
    □ (∀ vl, Φ1 vl ↔ Φ2 vl) -∗ □ (l ↦∗{q}: Φ1 ↔ l ↦∗{q}: Φ2).
  Proof.
    iIntros "#HΦ !>". iSplit; iIntros; iApply (heap_mapsto_pred_wand with "[-]"); try done; [|];
    iIntros; by iApply "HΦ".
  Qed.

  Lemma heap_mapsto_vec_combine l q vl :
    vl ≠ [] →
    l ↦∗{q} vl ⊣⊢ own heap_name (◯ [^op list] i ↦ v ∈ vl,
      {[l +ₗ i := (q, Cinr 0%nat, to_agree v)]}).
  Proof.
    rewrite /heap_mapsto_vec heap_mapsto_eq /heap_mapsto_def /heap_mapsto_st=>?.
    rewrite (big_opL_commute auth_frag) big_opL_commute1 //.
  Qed.

  Global Instance heap_mapsto_pred_fractional l (P : list val → iProp Σ):
    (∀ vl, Persistent (P vl)) → Fractional (λ q, l ↦∗{q}: P)%I.
  Proof.
    intros p q q'. iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[[Hown1 Hown2] #HP]".
      iSplitL "Hown1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (vl1) "[Hown1 #HP1]".
      iDestruct "H2" as (vl2) "[Hown2 #HP2]".
      set (ll := min (length vl1) (length vl2)).
      rewrite -[vl1](firstn_skipn ll) -[vl2](firstn_skipn ll) 2!heap_mapsto_vec_app.
      iDestruct "Hown1" as "[Hown1 _]". iDestruct "Hown2" as "[Hown2 _]".
      iCombine "Hown1" "Hown2" as "Hown". rewrite heap_mapsto_vec_op; last first.
      { rewrite !firstn_length. subst ll.
        rewrite -!min_assoc min_idempotent min_comm -min_assoc min_idempotent min_comm. done. }
      iDestruct "Hown" as "[H Hown]". iDestruct "H" as %Hl. iExists (take ll vl1). iFrame.
      destruct (min_spec (length vl1) (length vl2)) as [[Hne Heq]|[Hne Heq]].
      + iClear "HP2". rewrite take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
      + iClear "HP1". rewrite Hl take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
  Qed.
  Global Instance heap_mapsto_pred_as_fractional l q (P : list val → iProp Σ):
    (∀ vl, Persistent (P vl)) → AsFractional (l ↦∗{q}: P) (λ q, l ↦∗{q}: P)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma inter_lookup_Some i j (n : nat):
    i ≤ j < i+n → inter i n !! j = Excl' ().
  Proof.
    revert i. induction n as [|n IH]=>/= i; first lia.
    rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → inter i n !! j = None.
  Proof.
    revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma inter_op i n n' : inter i n ⋅ inter (i+n) n' ≡ inter i (n+n').
  Proof.
    intros j. rewrite lookup_op.
    destruct (decide (i ≤ j < i+n)); last destruct (decide (i+n ≤ j < i+n+n')).
    - by rewrite (inter_lookup_None (i+n) j n') ?inter_lookup_Some; try lia.
    - by rewrite (inter_lookup_None i j n) ?inter_lookup_Some; try lia.
    - by rewrite !inter_lookup_None; try lia.
  Qed.
  Lemma inter_valid i n : ✓ inter i n.
  Proof. revert i. induction n as [|n IH]=>i; first done. by apply insert_valid. Qed.

  Lemma heap_freeable_op_eq l q1 q2 n n' :
    †{q1}l…n ∗ †{q2}l+ₗn … n' ⊣⊢ †{q1+q2}l…(n+n').
  Proof.
    by rewrite heap_freeable_eq /heap_freeable_def -own_op -auth_frag_op
      singleton_op -pair_op inter_op.
  Qed.

  (** Properties about heap_freeable_rel and heap_freeable *)
  Lemma heap_freeable_rel_None σ l hF :
    (∀ m : Z, σ !! (l +ₗ m) = None) → heap_freeable_rel σ hF →
    hF !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
    destruct (map_choose s) as [i []%REL'%not_eq_None_Some]; first done.
    move: (FRESH (i - l.2)). by rewrite /shift_loc Zplus_minus.
  Qed.

  Lemma heap_freeable_is_Some σ hF l n i :
    heap_freeable_rel σ hF →
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    is_Some (σ !! (l +ₗ i)) ↔ 0 ≤ i ∧ i < n.
  Proof.
    destruct l as [b j]; rewrite /shift_loc /=. intros REL Hl.
    destruct (REL b (1%Qp, inter j n)) as [_ ->]; simpl in *; auto.
    destruct (decide (0 ≤ i ∧ i < n)).
    - rewrite is_Some_alt inter_lookup_Some; lia.
    - rewrite is_Some_alt inter_lookup_None; lia.
  Qed.

  Lemma heap_freeable_rel_init_mem l h n σ:
    n ≠ O →
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    heap_freeable_rel σ h →
    heap_freeable_rel (init_mem l n σ)
                      (<[l.1 := (1%Qp, inter (l.2) n)]> h).
  Proof.
    move=> Hvlnil FRESH REL blk qs /lookup_insert_Some [[<- <-]|[??]].
    - split.
      { destruct n as [|n]; simpl in *; [done|]. apply: insert_non_empty. }
      intros i. destruct (decide (l.2 ≤ i ∧ i < l.2 + n)).
      + rewrite inter_lookup_Some // lookup_init_mem; naive_solver.
      + rewrite inter_lookup_None; last lia. rewrite lookup_init_mem_ne /=; last lia.
        replace (l.1,i) with (l +ₗ (i - l.2)) by (rewrite /shift_loc; f_equal; lia).
        by rewrite FRESH !is_Some_alt.
    - destruct (REL blk qs) as [? Hs]; auto.
      split; [done|]=> i. by rewrite -Hs lookup_init_mem_ne; last auto.
  Qed.

  Lemma heap_freeable_rel_free_mem σ hF n l :
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    heap_freeable_rel σ hF →
    heap_freeable_rel (free_mem l n σ) (delete (l.1) hF).
  Proof.
    intros Hl REL b qs; rewrite lookup_delete_Some=> -[NEQ ?].
    destruct (REL b qs) as [? REL']; auto.
    split; [done|]=> i. by rewrite -REL' lookup_free_mem_ne.
  Qed.

  Lemma heap_freeable_rel_stable σ h l p :
    heap_freeable_rel σ h → is_Some (σ !! l) →
    heap_freeable_rel (<[l := p]>σ) h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
    split; [done|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (blk, i))); naive_solver.
  Qed.

  (** Weakest precondition *)
  Lemma heap_alloc_vs σ l n :
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    own heap_name (● to_heap σ)
    ==∗ own heap_name (● to_heap (init_mem l n σ))
       ∗ own heap_name (◯ [^op list] i ↦ v ∈ (repeat (LitV LitPoison) n),
           {[l +ₗ i := (1%Qp, Cinr 0%nat, to_agree v)]}).
  Proof.
    intros FREE. rewrite -own_op. apply own_update, auth_update_alloc.
    revert l FREE. induction n as [|n IH]=> l FRESH; [done|].
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /=.
    etrans; first apply (IH (l +ₗ 1)).
    { intros. by rewrite shift_loc_assoc. }
    rewrite shift_loc_0 -insert_singleton_op; last first.
    { rewrite -None_equiv_eq big_opL_commute None_equiv_eq big_opL_None=> l' v' ?.
      rewrite lookup_singleton_None -{2}(shift_loc_0 l). apply not_inj; lia. }
    rewrite to_heap_insert. setoid_rewrite shift_loc_assoc.
    apply alloc_local_update; last done. apply lookup_to_heap_None.
    rewrite lookup_init_mem_ne /=; last lia. by rewrite -(shift_loc_0 l) FRESH.
  Qed.

  Lemma heap_alloc σ l n :
    0 < n →
    (∀ m, σ !! (l +ₗ m) = None) →
    heap_ctx σ ==∗
      heap_ctx (init_mem l (Z.to_nat n) σ) ∗ †l…(Z.to_nat n) ∗
      l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    intros ??; iDestruct 1 as (hF) "(Hvalσ & HhF & %)".
    assert (Z.to_nat n ≠ O). { rewrite -(Nat2Z.id 0)=>/Z2Nat.inj. lia. }
    iMod (heap_alloc_vs _ _ (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hmapsto]"; first done.
    iMod (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, inter (l.2) (Z.to_nat n))).
      - eauto using heap_freeable_rel_None.
      - split; first done. apply inter_valid. }
    iModIntro. iSplitL "Hvalσ HhF".
    { iExists _. iFrame. iPureIntro.
      auto using heap_freeable_rel_init_mem. }
    rewrite heap_freeable_eq /heap_freeable_def heap_mapsto_vec_combine //; last first.
    { destruct (Z.to_nat n); done. }
    iFrame.
  Qed.

  Lemma heap_free_vs σ l vl :
    own heap_name (● to_heap σ) ∗ own heap_name (◯ [^op list] i ↦ v ∈ vl,
      {[l +ₗ i := (1%Qp, Cinr 0%nat, to_agree v)]})
    ==∗ own heap_name (● to_heap (free_mem l (length vl) σ)).
  Proof.
    rewrite -own_op. apply own_update, auth_update_dealloc.
    revert σ l. induction vl as [|v vl IH]=> σ l; [done|].
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= shift_loc_0.
    apply local_update_total_valid=> _ Hvalid _.
    assert (([^op list] k↦y ∈ vl,
      {[l +ₗ (1 + k) := (1%Qp, Cinr 0%nat, to_agree y)]} : heapUR) !! l = None).
    { move: (Hvalid l). rewrite lookup_op lookup_singleton.
      by move=> /(cmra_discrete_valid_iff 0) /exclusiveN_Some_l. }
    rewrite -insert_singleton_op //. etrans.
    { apply (delete_local_update _ _ l (1%Qp, Cinr 0%nat, to_agree v)).
      by rewrite lookup_insert. }
    rewrite delete_insert // -to_heap_delete delete_free_mem.
    setoid_rewrite <-shift_loc_assoc. apply IH.
  Qed.

  Lemma heap_free σ l vl (n : Z) :
    n = length vl →
    heap_ctx σ -∗ l ↦∗ vl -∗ †l…(length vl)
    ==∗ ⌜0 < n⌝ ∗ ⌜∀ m, is_Some (σ !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝ ∗
        heap_ctx (free_mem l (Z.to_nat n) σ).
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & REL)"; iDestruct "REL" as %REL.
    iIntros "Hmt Hf". rewrite heap_freeable_eq /heap_freeable_def.
    iDestruct (own_valid_2 with "HhF Hf") as % [Hl Hv]%auth_both_valid_discrete.
    move: Hl=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hl Hq]].
    apply (Some_included_exclusive _ _) in Hq as [=<-<-]%leibniz_equiv; last first.
    { move: (Hv (l.1)). rewrite Hl. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (REL (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iMod (heap_free_vs with "[Hmt Hvalσ]") as "Hvalσ".
    { rewrite heap_mapsto_vec_combine //. iFrame. }
    iMod (own_update_2 with "HhF Hf") as "HhF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst. repeat iSplit;  eauto using heap_freeable_is_Some.
    iExists _. subst. rewrite Nat2Z.id. iFrame.
    eauto using heap_freeable_rel_free_mem.
  Qed.

  Lemma heap_mapsto_lookup σ l ls q v :
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (q, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜∃ n' : nat,
        σ !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    - by exists O.
    - eauto.
    - exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_lookup_1 σ l ls v :
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (1%Qp, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜σ !! l = Some (ls, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma heap_read_vs σ n1 n2 nf l q v:
    σ !! l = Some (RSt (n1 + nf), v) →
    own heap_name (● to_heap σ) -∗ heap_mapsto_st (RSt n1) l q v
    ==∗ own heap_name (● to_heap (<[l:=(RSt (n2 + nf), v)]> σ))
        ∗ heap_mapsto_st (RSt n2) l q v.
  Proof.
    intros Hσv. apply wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma heap_read σ l q v :
    heap_ctx σ -∗ l ↦{q} v -∗ ∃ n, ⌜σ !! l = Some (RSt n, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
  Qed.

  Lemma heap_read_1 σ l v :
    heap_ctx σ -∗ l ↦ v -∗ ⌜σ !! l = Some (RSt 0, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; auto.
  Qed.

  Lemma heap_read_na σ l q v :
    heap_ctx σ -∗ l ↦{q} v ==∗ ∃ n,
      ⌜σ !! l = Some (RSt n, v)⌝ ∗
      heap_ctx (<[l:=(RSt (S n), v)]> σ) ∗
      ∀ σ2, heap_ctx σ2 ==∗ ∃ n2, ⌜σ2 !! l = Some (RSt (S n2), v)⌝ ∗
        heap_ctx (<[l:=(RSt n2, v)]> σ2) ∗ l ↦{q} v.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)"; iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_read_vs _ 0 1 with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iExists n; iSplit; [done|]. iSplitL "HhF Hσ".
    { iExists hF. iFrame. eauto using heap_freeable_rel_stable. }
    clear dependent n σ hF. iIntros (σ2). iDestruct 1 as (hF) "(Hσ & HhF & %)".
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_read_vs _ 1 0 with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iExists n; iModIntro; iSplit; [done|]. iFrame "Hmt".
    iExists hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma heap_write_vs σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own heap_name (● to_heap σ) -∗ heap_mapsto_st st1 l 1%Qp v
    ==∗ own heap_name (● to_heap (<[l:=(st2, v')]> σ))
        ∗ heap_mapsto_st st2 l 1%Qp v'.
  Proof.
    intros Hσv. apply wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write σ l v v' :
    heap_ctx σ -∗ l ↦ v ==∗ heap_ctx (<[l:=(RSt 0, v')]> σ) ∗ l ↦ v'.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; auto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. iExists _. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma heap_write_na σ l v v' :
    heap_ctx σ -∗ l ↦ v ==∗
      ⌜σ !! l = Some (RSt 0, v)⌝ ∗
      heap_ctx (<[l:=(WSt, v)]> σ) ∗
      ∀ σ2, heap_ctx σ2 ==∗ ⌜σ2 !! l = Some (WSt, v)⌝ ∗
        heap_ctx (<[l:=(RSt 0, v')]> σ2) ∗ l ↦ v'.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)"; iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; eauto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iSplit; [done|]. iSplitL "HhF Hσ".
    { iExists hF. iFrame. eauto using heap_freeable_rel_stable. }
    clear dependent σ hF. iIntros (σ2). iDestruct 1 as (hF) "(Hσ & HhF & %)".
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro; iSplit; [done|]. iFrame "Hmt".
    iExists hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.
End heap.
