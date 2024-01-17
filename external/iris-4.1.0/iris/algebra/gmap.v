From stdpp Require Export list gmap.
From iris.algebra Require Export list cmra.
From iris.algebra Require Import gset.
From iris.algebra Require Import updates local_updates proofmode_classes big_op.
From iris.prelude Require Import options.

Section ofe.
Context `{Countable K} {A : ofe}.
Implicit Types m : gmap K A.
Implicit Types i : K.

Local Instance gmap_dist : Dist (gmap K A) := λ n m1 m2,
  ∀ i, m1 !! i ≡{n}≡ m2 !! i.
Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Proof.
  split.
  - intros m1 m2; split.
    + by intros Hm n k; apply equiv_dist.
    + intros Hm k; apply equiv_dist; intros n; apply Hm.
  - intros n; split.
    + by intros m k.
    + by intros m1 m2 ? k.
    + by intros m1 m2 m3 ?? k; trans (m2 !! k).
  - intros n m m1 m2 ? ? k. eauto using dist_le with si_solver.
Qed.
Canonical Structure gmapO : ofe := Ofe (gmap K A) gmap_ofe_mixin.

Program Definition gmap_chain (c : chain gmapO)
  (k : K) : chain (optionO A) := {| chain_car n := c n !! k |}.
Next Obligation. by intros c k n i ?; apply (chain_cauchy c). Qed.
Definition gmap_compl `{Cofe A} : Compl gmapO := λ c,
  map_imap (λ i _, compl (gmap_chain c i)) (c 0).
Global Program Instance gmap_cofe `{Cofe A} : Cofe gmapO :=
  {| compl := gmap_compl |}.
Next Obligation.
  intros ? n c k. rewrite /compl /gmap_compl map_lookup_imap.
  oinversion (λ H, chain_cauchy c 0 n H k);simplify_option_eq;auto with lia.
  by rewrite conv_compl /=; apply reflexive_eq.
Qed.

Global Instance gmap_ofe_discrete : OfeDiscrete A → OfeDiscrete gmapO.
Proof. intros ? m m' ? i. by apply (discrete _). Qed.
(* why doesn't this go automatic? *)
Global Instance gmapO_leibniz: LeibnizEquiv A → LeibnizEquiv gmapO.
Proof. intros; change (LeibnizEquiv (gmap K A)); apply _. Qed.

Global Instance lookup_ne k : NonExpansive (lookup k : gmap K A → option A).
Proof. by intros n m1 m2. Qed.
Global Instance lookup_total_ne `{!Inhabited A} k :
  NonExpansive (lookup_total k : gmap K A → A).
Proof. intros n m1 m2. rewrite !lookup_total_alt. by intros ->. Qed.
Global Instance partial_alter_ne n :
  Proper ((dist n ==> dist n) ==> (=) ==> dist n ==> dist n)
         (partial_alter (M:=gmap K A)).
Proof.
  by intros f1 f2 Hf i ? <- m1 m2 Hm j; destruct (decide (i = j)) as [->|];
    rewrite ?lookup_partial_alter ?lookup_partial_alter_ne //;
    try apply Hf; apply lookup_ne.
Qed.
Global Instance insert_ne i : NonExpansive2 (insert (M:=gmap K A) i).
Proof. intros n x y ? m m' ? j; apply partial_alter_ne; by try constructor. Qed.
Global Instance singleton_ne i : NonExpansive (singletonM i : A → gmap K A).
Proof. by intros ????; apply insert_ne. Qed.
Global Instance delete_ne i : NonExpansive (delete (M:=gmap K A) i).
Proof.
  intros n m m' ? j; destruct (decide (i = j)); simplify_map_eq;
    [by constructor|by apply lookup_ne].
Qed.
Global Instance alter_ne (f : A → A) (k : K) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (alter (M := gmap K A) f k).
Proof. intros ? m m' Hm k'. by apply partial_alter_ne; [solve_proper|..]. Qed.

Global Instance gmap_empty_discrete : Discrete (∅ : gmap K A).
Proof.
  intros m Hm i; specialize (Hm i); rewrite lookup_empty in Hm |- *.
  inversion_clear Hm; constructor.
Qed.
Global Instance gmap_lookup_discrete m i : Discrete m → Discrete (m !! i).
Proof.
  intros ? [x|] Hx; [|by symmetry; apply: discrete].
  assert (m ≡{0}≡ <[i:=x]> m)
    by (by symmetry in Hx; inversion Hx; ofe_subst; rewrite insert_id).
  by rewrite (discrete m (<[i:=x]>m)) // lookup_insert.
Qed.
Global Instance gmap_insert_discrete m i x :
  Discrete x → Discrete m → Discrete (<[i:=x]>m).
Proof.
  intros ?? m' Hm j; destruct (decide (i = j)); simplify_map_eq.
  { by apply: discrete; rewrite -Hm lookup_insert. }
  by apply: discrete; rewrite -Hm lookup_insert_ne.
Qed.
Global Instance gmap_singleton_discrete i x :
  Discrete x → Discrete ({[ i := x ]} : gmap K A).
Proof. rewrite /singletonM /map_singleton. apply _. Qed.
Lemma insert_idN n m i x :
  m !! i ≡{n}≡ Some x → <[i:=x]>m ≡{n}≡ m.
Proof. intros (y'&?&->)%dist_Some_inv_r'. by rewrite insert_id. Qed.

Global Instance gmap_dom_ne n :
  Proper ((≡{n}@{gmap K A}≡) ==> (=)) dom.
Proof. intros m1 m2 Hm. apply set_eq=> k. by rewrite !elem_of_dom Hm. Qed.
End ofe.

Global Instance map_seq_ne {A : ofe} start :
  NonExpansive (map_seq (M:=gmap nat A) start).
Proof.
  intros n l1 l2 Hl. revert start.
  induction Hl; intros; simpl; repeat (done || f_equiv).
Qed.

Global Arguments gmapO _ {_ _} _.

(** Non-expansiveness of higher-order map functions and big-ops *)
Global Instance merge_ne `{Countable K} {A B C : ofe} n :
  Proper ((dist (A:=option A) n ==> dist (A:=option B) n ==> dist (A:=option C) n) ==>
          dist n ==> dist n ==> dist n) (merge (M:=gmap K)).
Proof.
  intros ?? Hf ?? Hm1 ?? Hm2 i. rewrite !lookup_merge.
  destruct (Hm1 i), (Hm2 i); try apply Hf; by constructor.
Qed.
Global Instance union_with_ne `{Countable K} {A : ofe} n :
  Proper ((dist n ==> dist n ==> dist n) ==>
          dist n ==> dist n ==> dist n) (union_with (M:=gmap K A)).
Proof.
  intros ?? Hf ?? Hm1 ?? Hm2 i; apply (merge_ne _ _); auto.
  by do 2 destruct 1; first [apply Hf | constructor].
Qed.
Global Instance map_fmap_ne `{Countable K} {A B : ofe} (f : A → B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (fmap (M:=gmap K) f).
Proof. intros ? m m' ? k; rewrite !lookup_fmap. by repeat f_equiv. Qed.
Global Instance map_zip_with_ne `{Countable K} {A B C : ofe} (f : A → B → C) n :
  Proper (dist n ==> dist n ==> dist n) f →
  Proper (dist n ==> dist n ==> dist n) (map_zip_with (M:=gmap K) f).
Proof.
  intros Hf m1 m1' Hm1 m2 m2' Hm2. apply merge_ne; try done.
  destruct 1; destruct 1; repeat f_equiv; constructor || done.
Qed.

Global Instance gmap_union_ne `{Countable K} {A : ofe} :
  NonExpansive2 (union (A:=gmap K A)).
Proof. intros n. apply union_with_ne. by constructor. Qed.
Global Instance gmap_disjoint_ne `{Countable K} {A : ofe} n :
  Proper (dist n ==> dist n ==> iff) (map_disjoint (M:=gmap K) (A:=A)).
Proof.
  intros m1 m1' Hm1 m2 m2' Hm2; split;
    intros Hm i; specialize (Hm i); by destruct (Hm1 i), (Hm2 i).
Qed.

Lemma gmap_union_dist_eq `{Countable K} {A : ofe} (m m1 m2 : gmap K A) n :
  m ≡{n}≡ m1 ∪ m2 ↔ ∃ m1' m2', m = m1' ∪ m2' ∧ m1' ≡{n}≡ m1 ∧ m2' ≡{n}≡ m2.
Proof.
  split; last first.
  { by intros (m1'&m2'&->&<-&<-). }
  intros Hm.
  exists (filter (λ '(l,_), is_Some (m1 !! l)) m),
    (m2 ∩ m1 ∪ filter (λ '(l,_), is_Some (m2 !! l)) m).
  split_and!; [apply map_eq|..]; intros k; move: (Hm k);
    rewrite ?lookup_union ?lookup_intersection !map_lookup_filter;
    case _ : (m !! k)=> [x|] /=; case _ : (m1 !! k)=> [x1|] /=;
      case _ : (m2 !! k)=> [x2|] /=; by inversion 1.
Qed.

Lemma big_opM_ne_2 `{Monoid M o} `{Countable K} {A : ofe} (f g : K → A → M) m1 m2 n :
  m1 ≡{n}≡ m2 →
  (∀ k y1 y2,
    m1 !! k = Some y1 → m2 !! k = Some y2 → y1 ≡{n}≡ y2 → f k y1 ≡{n}≡ g k y2) →
  ([^o map] k ↦ y ∈ m1, f k y) ≡{n}≡ ([^o map] k ↦ y ∈ m2, g k y).
Proof.
  intros Hl Hf. apply big_opM_gen_proper_2; try (apply _ || done).
  { by intros ?? ->. }
  { apply monoid_ne. }
  intros k. assert (m1 !! k ≡{n}≡ m2 !! k) as Hlk by (by f_equiv).
  destruct (m1 !! k) eqn:?, (m2 !! k) eqn:?; inversion Hlk; naive_solver.
Qed.

(* CMRA *)
Section cmra.
Context `{Countable K} {A : cmra}.
Implicit Types m : gmap K A.

Local Instance gmap_unit_instance : Unit (gmap K A) := (∅ : gmap K A).
Local Instance gmap_op_instance : Op (gmap K A) := merge op.
Local Instance gmap_pcore_instance : PCore (gmap K A) := λ m, Some (omap pcore m).
Local Instance gmap_valid_instance : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).
Local Instance gmap_validN_instance : ValidN (gmap K A) := λ n m, ∀ i, ✓{n} (m !! i).

Lemma gmap_op m1 m2 : m1 ⋅ m2 = merge op m1 m2.
Proof. done. Qed.
Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
Proof. rewrite lookup_merge. by destruct (m1 !! i), (m2 !! i). Qed.
Lemma lookup_core m i : core m !! i = core (m !! i).
Proof. by apply lookup_omap. Qed.

Lemma lookup_includedN n (m1 m2 : gmap K A) : m1 ≼{n} m2 ↔ ∀ i, m1 !! i ≼{n} m2 !! i.
Proof.
  split; [by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm|].
  revert m2. induction m1 as [|i x m Hi IH] using map_ind=> m2 Hm.
  { exists m2. by rewrite left_id. }
  destruct (IH (delete i m2)) as [m2' Hm2'].
  { intros j. move: (Hm j); destruct (decide (i = j)) as [->|].
    - intros _. rewrite Hi. apply: ucmra_unit_leastN.
    - rewrite lookup_insert_ne // lookup_delete_ne //. }
  destruct (Hm i) as [my Hi']; simplify_map_eq.
  exists (partial_alter (λ _, my) i m2')=>j; destruct (decide (i = j)) as [->|].
  - by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
  - move: (Hm2' j). by rewrite !lookup_op lookup_delete_ne //
      lookup_insert_ne // lookup_partial_alter_ne.
Qed.

(* [m1 ≼ m2] is not equivalent to [∀ n, m1 ≼{n} m2],
so there is no good way to reuse the above proof. *)
Lemma lookup_included (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
Proof.
  split; [by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm|].
  revert m2. induction m1 as [|i x m Hi IH] using map_ind=> m2 Hm.
  { exists m2. by rewrite left_id. }
  destruct (IH (delete i m2)) as [m2' Hm2'].
  { intros j. move: (Hm j); destruct (decide (i = j)) as [->|].
    - intros _. rewrite Hi. apply: ucmra_unit_least.
    - rewrite lookup_insert_ne // lookup_delete_ne //. }
  destruct (Hm i) as [my Hi']; simplify_map_eq.
  exists (partial_alter (λ _, my) i m2')=>j; destruct (decide (i = j)) as [->|].
  - by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
  - move: (Hm2' j). by rewrite !lookup_op lookup_delete_ne //
      lookup_insert_ne // lookup_partial_alter_ne.
Qed.

Lemma gmap_cmra_mixin : CmraMixin (gmap K A).
Proof.
  apply cmra_total_mixin.
  - eauto.
  - intros n m1 m2 m3 Hm i; by rewrite !lookup_op (Hm i).
  - intros n m1 m2 Hm i; by rewrite !lookup_core (Hm i).
  - intros n m1 m2 Hm ? i; by rewrite -(Hm i).
  - intros m; split.
    + by intros ? n i; apply cmra_valid_validN.
    + intros Hm i; apply cmra_valid_validN=> n; apply Hm.
  - intros n m Hm i; apply cmra_validN_S, Hm.
  - by intros m1 m2 m3 i; rewrite !lookup_op assoc.
  - by intros m1 m2 i; rewrite !lookup_op comm.
  - intros m i. by rewrite lookup_op lookup_core cmra_core_l.
  - intros m i. by rewrite !lookup_core cmra_core_idemp.
  - intros m1 m2; rewrite !lookup_included=> Hm i.
    rewrite !lookup_core. by apply cmra_core_mono.
  - intros n m1 m2 Hm i; apply cmra_validN_op_l with (m2 !! i).
    by rewrite -lookup_op.
  - intros n m y1 y2 Hm Heq.
    refine ((λ FUN, _) (λ i, cmra_extend n (m !! i) (y1 !! i) (y2 !! i) (Hm i) _));
      last by rewrite -lookup_op.
    exists (map_imap (λ i _, projT1 (FUN i)) y1).
    exists (map_imap (λ i _, proj1_sig (projT2 (FUN i))) y2).
    split; [|split]=>i; rewrite ?lookup_op !map_lookup_imap;
    destruct (FUN i) as (z1i&z2i&Hmi&Hz1i&Hz2i)=>/=.
    + destruct (y1 !! i), (y2 !! i); inversion Hz1i; inversion Hz2i; subst=>//.
    + revert Hz1i. case: (y1!!i)=>[?|] //.
    + revert Hz2i. case: (y2!!i)=>[?|] //.
Qed.
Canonical Structure gmapR := Cmra (gmap K A) gmap_cmra_mixin.

Global Instance gmap_cmra_discrete : CmraDiscrete A → CmraDiscrete gmapR.
Proof. split; [apply _|]. intros m ? i. by apply: cmra_discrete_valid. Qed.

Lemma gmap_ucmra_mixin : UcmraMixin (gmap K A).
Proof.
  split.
  - by intros i; rewrite lookup_empty.
  - by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
  - constructor=> i. by rewrite lookup_omap lookup_empty.
Qed.
Canonical Structure gmapUR := Ucmra (gmap K A) gmap_ucmra_mixin.

End cmra.

Global Arguments gmapR _ {_ _} _.
Global Arguments gmapUR _ {_ _} _.

Section properties.
Context `{Countable K} {A : cmra}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Global Instance lookup_op_homomorphism i :
  MonoidHomomorphism op op (≡) (lookup i : gmap K A → option A).
Proof.
  split; [split|]; try apply _.
  - intros m1 m2; by rewrite lookup_op.
  - done.
Qed.

Lemma lookup_opM m1 mm2 i : (m1 ⋅? mm2) !! i = m1 !! i ⋅ (mm2 ≫= (.!! i)).
Proof. destruct mm2; by rewrite /= ?lookup_op ?right_id_L. Qed.

Lemma lookup_validN_Some n m i x : ✓{n} m → m !! i ≡{n}≡ Some x → ✓{n} x.
Proof. by move=> /(_ i) Hm Hi; move:Hm; rewrite Hi. Qed.
Lemma lookup_valid_Some m i x : ✓ m → m !! i ≡ Some x → ✓ x.
Proof. move=> Hm Hi. move:(Hm i). by rewrite Hi. Qed.

Lemma insert_validN n m i x : ✓{n} x → ✓{n} m → ✓{n} <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.
Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
Lemma singleton_validN n i x : ✓{n} ({[ i := x ]} : gmap K A) ↔ ✓{n} x.
Proof.
  split.
  - move=>/(_ i); by simplify_map_eq.
  - intros. apply insert_validN; first done. apply: ucmra_unit_validN.
Qed.
Lemma singleton_valid i x : ✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.
Proof. rewrite !cmra_valid_validN. by setoid_rewrite singleton_validN. Qed.

Lemma delete_validN n m i : ✓{n} m → ✓{n} (delete i m).
Proof. intros Hm j; destruct (decide (i = j)); by simplify_map_eq. Qed.
Lemma delete_valid m i : ✓ m → ✓ (delete i m).
Proof. intros Hm j; destruct (decide (i = j)); by simplify_map_eq. Qed.

Lemma insert_singleton_op m i x : m !! i = None → <[i:=x]> m = {[ i := x ]} ⋅ m.
Proof.
  intros Hi; apply map_eq=> j; destruct (decide (i = j)) as [->|].
  - by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
  - by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
Qed.

Lemma singleton_core (i : K) (x : A) cx :
  pcore x = Some cx → core {[ i := x ]} =@{gmap K A} {[ i := cx ]}.
Proof. apply omap_singleton_Some. Qed.
Lemma singleton_core' (i : K) (x : A) cx :
  pcore x ≡ Some cx → core {[ i := x ]} ≡@{gmap K A} {[ i := cx ]}.
Proof.
  intros (cx'&?&<-)%Some_equiv_eq. by rewrite (singleton_core _ _ cx').
Qed.
Lemma singleton_core_total `{!CmraTotal A} (i : K) (x : A) :
  core {[ i := x ]} =@{gmap K A} {[ i := core x ]}.
Proof. apply singleton_core. rewrite cmra_pcore_core //. Qed.
Lemma singleton_op (i : K) (x y : A) :
  {[ i := x ]} ⋅ {[ i := y ]} =@{gmap K A} {[ i := x ⋅ y ]}.
Proof. by apply (merge_singleton _ _ _ x y). Qed.
Global Instance singleton_is_op i a a1 a2 :
  IsOp a a1 a2 → IsOp' ({[ i := a ]} : gmap K A) {[ i := a1 ]} {[ i := a2 ]}.
Proof. rewrite /IsOp' /IsOp=> ->. by rewrite -singleton_op. Qed.

Lemma gmap_core_id m : (∀ i x, m !! i = Some x → CoreId x) → CoreId m.
Proof.
  intros Hcore; apply core_id_total=> i.
  rewrite lookup_core. destruct (m !! i) as [x|] eqn:Hix; rewrite Hix; [|done].
  by eapply Hcore.
Qed.
Global Instance gmap_core_id' m : (∀ x : A, CoreId x) → CoreId m.
Proof. auto using gmap_core_id. Qed.

Global Instance gmap_singleton_core_id i (x : A) :
  CoreId x → CoreId {[ i := x ]}.
Proof. intros. by apply core_id_total, singleton_core'. Qed.

Lemma singleton_includedN_l n m i x :
  {[ i := x ]} ≼{n} m ↔ ∃ y, m !! i ≡{n}≡ Some y ∧ Some x ≼{n} Some y.
Proof.
  split.
  - move=> [m' /(_ i)]; rewrite lookup_op lookup_singleton=> Hi.
    exists (x ⋅? m' !! i). rewrite -Some_op_opM.
    split; first done. apply cmra_includedN_l.
  - intros (y&Hi&[mz Hy]). exists (partial_alter (λ _, mz) i m).
    intros j; destruct (decide (i = j)) as [->|].
    + by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
    + by rewrite lookup_op lookup_singleton_ne// lookup_partial_alter_ne// left_id.
Qed.
(* We do not have [x ≼ y ↔ ∀ n, x ≼{n} y], so we cannot use the previous lemma *)
Lemma singleton_included_l m i x :
  {[ i := x ]} ≼ m ↔ ∃ y, m !! i ≡ Some y ∧ Some x ≼ Some y.
Proof.
  split.
  - move=> [m' /(_ i)]; rewrite lookup_op lookup_singleton.
    exists (x ⋅? m' !! i). by rewrite -Some_op_opM.
  - intros (y&Hi&[mz Hy]). exists (partial_alter (λ _, mz) i m).
    intros j; destruct (decide (i = j)) as [->|].
    + by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
    + by rewrite lookup_op lookup_singleton_ne// lookup_partial_alter_ne// left_id.
Qed.
Lemma singleton_included_exclusive_l m i x :
  Exclusive x → ✓ m →
  {[ i := x ]} ≼ m ↔ m !! i ≡ Some x.
Proof.
  intros ? Hm. rewrite singleton_included_l. split; last by eauto.
  intros (y&?&->%(Some_included_exclusive _)); eauto using lookup_valid_Some.
Qed.
Lemma singleton_included i x y :
  {[ i := x ]} ≼ ({[ i := y ]} : gmap K A) ↔ Some x ≼ Some y.
Proof.
  rewrite singleton_included_l. split.
  - intros (y'&Hi&?). rewrite lookup_insert in Hi. by rewrite Hi.
  - intros ?. exists y. by rewrite lookup_insert.
Qed.
Lemma singleton_included_total `{!CmraTotal A}  i x y :
  {[ i := x ]} ≼ ({[ i := y ]} : gmap K A) ↔ x ≼ y.
Proof. rewrite singleton_included Some_included_total. done. Qed.
Lemma singleton_included_mono i x y :
  x ≼ y → {[ i := x ]} ≼ ({[ i := y ]} : gmap K A).
Proof. intros Hincl. apply singleton_included, Some_included_mono. done. Qed.

Global Instance singleton_cancelable i x :
  Cancelable (Some x) → Cancelable {[ i := x ]}.
Proof.
  intros ? n m1 m2 Hv EQ j. move: (Hv j) (EQ j). rewrite !lookup_op.
  destruct (decide (i = j)) as [->|].
  - rewrite lookup_singleton. by apply cancelableN.
  - by rewrite lookup_singleton_ne // !(left_id None _).
Qed.

Global Instance gmap_cancelable (m : gmap K A) :
  (∀ x : A, IdFree x) → (∀ x : A, Cancelable x) → Cancelable m.
Proof.
  intros ?? n m1 m2 ?? i. apply (cancelableN (m !! i)); by rewrite -!lookup_op.
Qed.

Lemma insert_op m1 m2 i x y :
  <[i:=x ⋅ y]>(m1 ⋅ m2) =  <[i:=x]>m1 ⋅ <[i:=y]>m2.
Proof. by rewrite (insert_merge (⋅) m1 m2 i (x ⋅ y) x y). Qed.

Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
  x ~~>: P →
  (∀ y, P y → Q (<[i:=y]>m)) →
  <[i:=x]>m ~~>: Q.
Proof.
  intros Hx%option_updateP' HP; apply cmra_total_updateP=> n mf Hm.
  destruct (Hx n (Some (mf !! i))) as ([y|]&?&?); try done.
  { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
  exists (<[i:=y]> m); split; first by auto.
  intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
  destruct (decide (i = j)); simplify_map_eq/=; auto.
Qed.
Lemma insert_updateP' (P : A → Prop) m i x :
  x ~~>: P → <[i:=x]>m ~~>: λ m', ∃ y, m' = <[i:=y]>m ∧ P y.
Proof. eauto using insert_updateP. Qed.
Lemma insert_update m i x y : x ~~> y → <[i:=x]>m ~~> <[i:=y]>m.
Proof. rewrite !cmra_update_updateP; eauto using insert_updateP with subst. Qed.

Lemma singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
  x ~~>: P → (∀ y, P y → Q {[ i := y ]}) → {[ i := x ]} ~~>: Q.
Proof. apply insert_updateP. Qed.
Lemma singleton_updateP' (P : A → Prop) i x :
  x ~~>: P → {[ i := x ]} ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. apply insert_updateP'. Qed.
Lemma singleton_update i (x y : A) : x ~~> y → {[ i := x ]} ~~> {[ i := y ]}.
Proof. apply insert_update. Qed.

Lemma delete_update m i : m ~~> delete i m.
Proof.
  apply cmra_total_update=> n mf Hm j; destruct (decide (i = j)); subst.
  - move: (Hm j). rewrite !lookup_op lookup_delete left_id.
    apply cmra_validN_op_r.
  - move: (Hm j). by rewrite !lookup_op lookup_delete_ne.
Qed.

Lemma gmap_op_union m1 m2 : m1 ##ₘ m2 → m1 ⋅ m2 = m1 ∪ m2.
Proof.
  intros Hm. apply map_eq=> k. specialize (Hm k).
  rewrite lookup_op lookup_union. by destruct (m1 !! k), (m2 !! k).
Qed.

Lemma gmap_op_valid0_disjoint m1 m2 :
  ✓{0} (m1 ⋅ m2) → (∀ k x, m1 !! k = Some x → Exclusive x) → m1 ##ₘ m2.
Proof.
  unfold Exclusive. intros Hvalid Hexcl k.
  specialize (Hvalid k). rewrite lookup_op in Hvalid. specialize (Hexcl k).
  destruct (m1 !! k), (m2 !! k); [|done..].
  rewrite -Some_op Some_validN in Hvalid. naive_solver.
Qed.
Lemma gmap_op_valid_disjoint m1 m2 :
  ✓ (m1 ⋅ m2) → (∀ k x, m1 !! k = Some x → Exclusive x) → m1 ##ₘ m2.
Proof. move=> /cmra_valid_validN /(_ 0). apply gmap_op_valid0_disjoint. Qed.

Lemma dom_op m1 m2 : dom (m1 ⋅ m2) = dom m1 ∪ dom m2.
Proof.
  apply set_eq=> i; rewrite elem_of_union !elem_of_dom.
  unfold is_Some; setoid_rewrite lookup_op.
  destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma dom_included m1 m2 : m1 ≼ m2 → dom m1 ⊆ dom m2.
Proof.
  rewrite lookup_included=>? i; rewrite !elem_of_dom. by apply is_Some_included.
Qed.

Section freshness.
  Local Set Default Proof Using "Type*".
  Context `{!Infinite K}.
  Lemma alloc_updateP_strong_dep (Q : gmap K A → Prop) (I : K → Prop) m (f : K → A) :
    pred_infinite I →
    (∀ i, m !! i = None → I i → ✓ (f i)) →
    (∀ i, m !! i = None → I i → Q (<[i:=f i]>m)) → m ~~>: Q.
  Proof.
    move=> /(pred_infinite_set I (C:=gset K)) HP ? HQ.
    apply cmra_total_updateP. intros n mf Hm.
    destruct (HP (dom (m ⋅ mf))) as [i [Hi1 Hi2]].
    assert (m !! i = None).
    { eapply not_elem_of_dom. revert Hi2.
      rewrite dom_op not_elem_of_union. naive_solver. }
    exists (<[i:=f i]>m); split.
    - by apply HQ.
    - rewrite insert_singleton_op //.
      rewrite -assoc -insert_singleton_op; last by eapply not_elem_of_dom.
    apply insert_validN; [apply cmra_valid_validN|]; auto.
  Qed.
  Lemma alloc_updateP_strong (Q : gmap K A → Prop) (I : K → Prop) m x :
    pred_infinite I →
    ✓ x → (∀ i, m !! i = None → I i → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=> HP ? HQ. eapply (alloc_updateP_strong_dep _ _ _ (λ _, x)); eauto.
  Qed.
  Lemma alloc_updateP (Q : gmap K A → Prop) m x :
    ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    move=>??.
    eapply (alloc_updateP_strong _ (λ _, True));
    eauto using pred_infinite_True.
  Qed.
  Lemma alloc_updateP_cofinite (Q : gmap K A → Prop) (J : gset K) m x :
    ✓ x → (∀ i, m !! i = None → i ∉ J → Q (<[i:=x]>m)) → m ~~>: Q.
  Proof.
    eapply alloc_updateP_strong.
    apply (pred_infinite_set (C:=gset K)).
    intros E. exists (fresh (J ∪ E)).
    apply not_elem_of_union, is_fresh.
  Qed.

  (* Variants without the universally quantified Q, for use in case that is an evar. *)
  Lemma alloc_updateP_strong_dep' m (f : K → A) (I : K → Prop) :
    pred_infinite I →
    (∀ i, m !! i = None → I i → ✓ (f i)) →
    m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=f i]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_strong_dep. Qed.
  Lemma alloc_updateP_strong' m x (I : K → Prop) :
    pred_infinite I →
    ✓ x → m ~~>: λ m', ∃ i, I i ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_strong. Qed.
  Lemma alloc_updateP' m x :
    ✓ x → m ~~>: λ m', ∃ i, m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP. Qed.
  Lemma alloc_updateP_cofinite' m x (J : gset K) :
    ✓ x → m ~~>: λ m', ∃ i, i ∉ J ∧ m' = <[i:=x]>m ∧ m !! i = None.
  Proof. eauto using alloc_updateP_cofinite. Qed.
End freshness.

Lemma alloc_unit_singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) u i :
  ✓ u → LeftId (≡) u (⋅) →
  u ~~>: P → (∀ y, P y → Q {[ i := y ]}) → ∅ ~~>: Q.
Proof.
  intros ?? Hx HQ. apply cmra_total_updateP=> n gf Hg.
  destruct (Hx n (gf !! i)) as (y&?&Hy).
  { move:(Hg i). rewrite !left_id.
    case: (gf !! i)=>[x|]; rewrite /= ?left_id //.
    intros; by apply cmra_valid_validN. }
  exists {[ i := y ]}; split; first by auto.
  intros i'; destruct (decide (i' = i)) as [->|].
  - rewrite lookup_op lookup_singleton.
    move:Hy; case: (gf !! i)=>[x|]; rewrite /= ?right_id //.
  - move:(Hg i'). by rewrite !lookup_op lookup_singleton_ne // !left_id.
Qed.
Lemma alloc_unit_singleton_updateP' (P: A → Prop) u i :
  ✓ u → LeftId (≡) u (⋅) →
  u ~~>: P → ∅ ~~>: λ m, ∃ y, m = {[ i := y ]} ∧ P y.
Proof. eauto using alloc_unit_singleton_updateP. Qed.
Lemma alloc_unit_singleton_update (u : A) i (y : A) :
  ✓ u → LeftId (≡) u (⋅) → u ~~> y → (∅:gmap K A) ~~> {[ i := y ]}.
Proof.
  rewrite !cmra_update_updateP;
    eauto using alloc_unit_singleton_updateP with subst.
Qed.

Lemma gmap_local_update m1 m2 m1' m2' :
  (∀ i, (m1 !! i, m2 !! i) ~l~> (m1' !! i, m2' !! i)) →
  (m1, m2) ~l~> (m1', m2').
Proof.
  intros Hupd. apply local_update_unital=> n mf Hmv Hm.
  apply forall_and_distr=> i. rewrite lookup_op -cmra_opM_fmap_Some.
  apply Hupd; simpl; first done. by rewrite Hm lookup_op cmra_opM_fmap_Some.
Qed.

Lemma alloc_local_update m1 m2 i x :
  m1 !! i = None → ✓ x → (m1,m2) ~l~> (<[i:=x]>m1, <[i:=x]>m2).
Proof.
  intros Hi ?. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
  rewrite !lookup_insert Hi. by apply alloc_option_local_update.
Qed.

Lemma alloc_singleton_local_update m i x :
  m !! i = None → ✓ x → (m,∅) ~l~> (<[i:=x]>m, {[ i:=x ]}).
Proof. apply alloc_local_update. Qed.

Lemma insert_local_update m1 m2 i x y x' y' :
  m1 !! i = Some x → m2 !! i = Some y →
  (x, y) ~l~> (x', y') →
  (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
Proof.
  intros Hi1 Hi2 Hup. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
  rewrite !lookup_insert Hi1 Hi2. by apply option_local_update.
Qed.

Lemma singleton_local_update_any m i y x' y' :
  (∀ x, m !! i = Some x → (x, y) ~l~> (x', y')) →
  (m, {[ i := y ]}) ~l~> (<[i:=x']>m, {[ i := y' ]}).
Proof.
  intros. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_insert_ne.
  rewrite !lookup_singleton lookup_insert.
  destruct (m !! j); first by eauto using option_local_update.
  apply local_update_total_valid0=> _ _ /option_includedN; naive_solver.
Qed.

Lemma singleton_local_update m i x y x' y' :
  m !! i = Some x →
  (x, y) ~l~> (x', y') →
  (m, {[ i := y ]}) ~l~> (<[i:=x']>m, {[ i := y' ]}).
Proof.
  intros Hmi ?. apply singleton_local_update_any.
  intros x2. rewrite Hmi=>[=<-]. done.
Qed.

Lemma delete_local_update m1 m2 i x `{!Exclusive x} :
  m2 !! i = Some x → (m1, m2) ~l~> (delete i m1, delete i m2).
Proof.
  intros Hi. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_delete_ne.
  rewrite !lookup_delete Hi. by apply delete_option_local_update.
Qed.

Lemma delete_singleton_local_update m i x `{!Exclusive x} :
  (m, {[ i := x ]}) ~l~> (delete i m, ∅).
Proof.
  rewrite -(delete_singleton i x).
  by eapply delete_local_update, lookup_singleton.
Qed.

Lemma delete_local_update_cancelable m1 m2 i mx `{!Cancelable mx} :
  m1 !! i ≡ mx → m2 !! i ≡ mx →
  (m1, m2) ~l~> (delete i m1, delete i m2).
Proof.
  intros Hi1 Hi2. apply gmap_local_update=> j.
  destruct (decide (i = j)) as [->|]; last by rewrite !lookup_delete_ne.
  rewrite !lookup_delete Hi1 Hi2. by apply delete_option_local_update_cancelable.
Qed.

Lemma delete_singleton_local_update_cancelable m i x `{!Cancelable (Some x)} :
  m !! i ≡ Some x → (m, {[ i := x ]}) ~l~> (delete i m, ∅).
Proof.
  intros. rewrite -(delete_singleton i x).
  apply (delete_local_update_cancelable m _ i (Some x));
    [done|by rewrite lookup_singleton].
Qed.

Lemma gmap_fmap_mono {B : cmra} (f : A → B) m1 m2 :
  Proper ((≡) ==> (≡)) f →
  (∀ x y, x ≼ y → f x ≼ f y) → m1 ≼ m2 → fmap f m1 ≼ fmap f m2.
Proof.
  intros ??. rewrite !lookup_included=> Hm i.
  rewrite !lookup_fmap. by apply option_fmap_mono.
Qed.

Lemma big_opM_singletons m :
  ([^op map] k ↦ x ∈ m, {[ k := x ]}) = m.
Proof.
  (* We are breaking the big_opM abstraction here. The reason is that [map_ind]
     is too weak: we need an induction principle that visits all the keys in the
     right order, namely the order in which they appear in map_to_list.  Here,
     we achieve this by unfolding [big_opM] and doing induction over that list
     instead. *)
  rewrite big_op.big_opM_unseal /big_op.big_opM_def -{2}(list_to_map_to_list m).
  assert (NoDup (map_to_list m).*1) as Hnodup by apply NoDup_fst_map_to_list.
  revert Hnodup. induction (map_to_list m) as [|[k x] l IH]; csimpl; first done.
  intros [??]%NoDup_cons. rewrite IH //.
  rewrite insert_singleton_op ?not_elem_of_list_to_map_1 //.
Qed.

End properties.

Section unital_properties.
Context `{Countable K} {A : ucmra}.
Implicit Types m : gmap K A.
Implicit Types i : K.
Implicit Types x y : A.

Lemma insert_alloc_local_update m1 m2 i x x' y' :
  m1 !! i = Some x → m2 !! i = None →
  (x, ε) ~l~> (x', y') →
  (m1, m2) ~l~> (<[i:=x']>m1, <[i:=y']>m2).
Proof.
  intros Hi1 Hi2 Hup. apply local_update_unital=> n mf Hm1v Hm.
  assert (mf !! i ≡{n}≡ Some x) as Hif.
  { move: (Hm i). by rewrite lookup_op Hi1 Hi2 left_id. }
  destruct (Hup n (mf !! i)) as [Hx'v Hx'eq].
  { move: (Hm1v i). by rewrite Hi1. }
  { by rewrite Hif -(inj_iff Some) -Some_op_opM -Some_op left_id. }
  split.
  - by apply insert_validN.
  - simpl in Hx'eq. by rewrite -(insert_idN n mf i x) // -insert_op -Hm Hx'eq Hif.
Qed.
End unital_properties.

(** Functor *)
Global Instance gmap_fmap_ne `{Countable K} {A B : ofe} (f : A → B) n :
  Proper (dist n ==> dist n) f → Proper (dist n ==>dist n) (fmap (M:=gmap K) f).
Proof. by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne. Qed.
Lemma gmap_fmap_ne_ext `{Countable K}
  {A : Type} {B : ofe} (f1 f2 : A → B) (m : gmap K A) n :
  (∀ i x, m !! i = Some x → f1 x ≡{n}≡ f2 x) →
  f1 <$> m ≡{n}≡ f2 <$> m.
Proof.
  move => Hf i.
  rewrite !lookup_fmap.
  destruct (m !! i) eqn:?; constructor; by eauto.
Qed.
Global Instance gmap_fmap_cmra_morphism `{Countable K} {A B : cmra} (f : A → B)
  `{!CmraMorphism f} : CmraMorphism (fmap f : gmap K A → gmap K B).
Proof.
  split; try apply _.
  - by intros n m ? i; rewrite lookup_fmap; apply (cmra_morphism_validN _).
  - intros m. apply Some_proper=>i. rewrite lookup_fmap !lookup_omap lookup_fmap.
    case: (m!!i)=>//= ?. apply cmra_morphism_pcore, _.
  - intros m1 m2 i. by rewrite lookup_op !lookup_fmap lookup_op cmra_morphism_op.
Qed.
Definition gmapO_map `{Countable K} {A B} (f: A -n> B) :
  gmapO K A -n> gmapO K B := OfeMor (fmap f : gmapO K A → gmapO K B).
Global Instance gmapO_map_ne `{Countable K} {A B} :
  NonExpansive (@gmapO_map K _ _ A B).
Proof.
  intros n f g Hf m k; rewrite /= !lookup_fmap.
  destruct (_ !! k) eqn:?; simpl; constructor; apply Hf.
Qed.

Program Definition gmapOF K `{Countable K} (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := gmapO K (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply oFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply oFunctor_map_compose.
Qed.
Global Instance gmapOF_contractive K `{Countable K} F :
  oFunctorContractive F → oFunctorContractive (gmapOF K F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, oFunctor_map_contractive.
Qed.

Program Definition gmapURF K `{Countable K} (F : rFunctor) : urFunctor := {|
  urFunctor_car A _ B _ := gmapUR K (rFunctor_car F A B);
  urFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros K ?? F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, rFunctor_map_ne.
Qed.
Next Obligation.
  intros K ?? F A ? B ? x. rewrite /= -{2}(map_fmap_id x).
  apply map_fmap_equiv_ext=>y ??; apply rFunctor_map_id.
Qed.
Next Obligation.
  intros K ?? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -map_fmap_compose.
  apply map_fmap_equiv_ext=>y ??; apply rFunctor_map_compose.
Qed.
Global Instance gmapURF_contractive K `{Countable K} F :
  rFunctorContractive F → urFunctorContractive (gmapURF K F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply gmapO_map_ne, rFunctor_map_contractive.
Qed.

Program Definition gmapRF K `{Countable K} (F : rFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := gmapR K (rFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg := gmapO_map (rFunctor_map F fg)
|}.
Solve Obligations with apply gmapURF.

Global Instance gmapRF_contractive K `{Countable K} F :
  rFunctorContractive F → rFunctorContractive (gmapRF K F).
Proof. apply gmapURF_contractive. Qed.
