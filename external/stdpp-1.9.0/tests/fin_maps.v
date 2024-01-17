From stdpp Require Import fin_maps fin_map_dom.
From stdpp Require Import strings pmap gmap.

(** * Tests involving the [FinMap] interfaces, i.e., tests that are not specific
to an implementation of finite maps. *)
Section map_disjoint.
  Context `{FinMap K M}.

  Lemma solve_map_disjoint_singleton_1 {A} (m1 m2 : M A) i x :
    m1 ##ₘ <[i:=x]> m2 → {[ i:= x ]} ∪ m2 ##ₘ m1 ∧ m2 ##ₘ ∅.
  Proof. intros. solve_map_disjoint. Qed.
  Lemma solve_map_disjoint_singleton_2 {A} (m1 m2 : M A) i x :
    m2 !! i = None → m1 ##ₘ {[ i := x ]} ∪ m2 → m2 ##ₘ <[i:=x]> m1 ∧ m1 !! i = None.
  Proof. intros. solve_map_disjoint. Qed.

  Lemma solve_map_disjoint_compose_l_singleton_1 {A} (n : M K) (m1 m2 : M A) i x :
    m1 ##ₘ <[i:=x]> m2 → ({[ i:= x ]} ∪ m2) ∘ₘ n ##ₘ m1 ∘ₘ n ∧ m2 ##ₘ ∅.
  Proof. intros. solve_map_disjoint. Qed.
  Lemma solve_map_disjoint_compose_l_singleton_2 {A} (n : M K) (m1 m2 : M A) i x :
    m2 !! i = None → m1 ##ₘ {[ i := x ]} ∪ m2 → m2 ∘ₘ n ##ₘ <[i:=x]> m1 ∘ₘ n ∧ m1 !! i = None.
  Proof. intros. solve_map_disjoint. Qed.

  Lemma solve_map_disjoint_compose_r_singleton_1 {A} (m1 m2 : M K) (n : M A) i x :
    m1 ##ₘ <[i:=x]> m2 → n ∘ₘ ({[ i:= x ]} ∪ m2) ##ₘ n ∘ₘ m1 ∧ m2 ##ₘ ∅.
  Proof. intros. solve_map_disjoint. Qed.
  Lemma solve_map_disjoint_compose_r_singleton_2 {A} (m1 m2 : M K) (n : M A) i x :
    m2 !! i = None → m1 ##ₘ {[ i := x ]} ∪ m2 → n ∘ₘ m2 ##ₘ n ∘ₘ <[i:=x]> m1 ∧ m1 !! i = None.
  Proof. intros. solve_map_disjoint. Qed.
End map_disjoint.

Section map_dom.
  Context `{FinMapDom K M D}.

  Lemma set_solver_dom_subseteq {A} (i j : K) (x y : A) :
    {[i; j]} ⊆ dom (<[i:=x]> (<[j:=y]> (∅ : M A))).
  Proof. set_solver. Qed.

  Lemma set_solver_dom_disjoint {A} (X : D) : dom (∅ : M A) ## X.
  Proof. set_solver. Qed.
End map_dom.

Section map_img.
  Context `{FinMap K M, Set_ A SA}.

  Lemma set_solver_map_img i x :
    map_img (∅ : M A) ⊆@{SA} map_img ({[ i := x ]} : M A).
  Proof. set_unfold. set_solver. Qed.
End map_img.

(** * Tests for the [Pmap] and [gmap] instances. *)

(** TODO: Fix [Pset] so that it satisfies the same [cbn]/[simpl] tests as
[gset] below. *)

Goal {[1; 2; 3]} =@{gset nat} ∅.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal elements (C := gset nat) {[1; 2; 3]} = [].
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal
  {[1; 2; 3]} ∖ {[ 1 ]} ∪ {[ 4 ]} ∩ {[ 10 ]} =@{gset nat} ∅ ∖ {[ 2 ]}.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal 1%positive ∈ dom (M := Pmap nat) (<[ 1%positive := 2 ]> ∅).
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal 1 ∈ dom (M := gmap nat nat) (<[ 1 := 2 ]> ∅).
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
Abort.

Goal bool_decide (∅ =@{gset nat} {[ 1; 2; 3 ]}) = false.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ≡@{gset nat} {[ 1; 2; 3 ]}) = false.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (1 ∈@{gset nat} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ##@{gset nat} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Goal bool_decide (∅ ⊆@{gset nat} {[ 1; 2; 3 ]}) = true.
Proof.
  Fail progress simpl.
  Fail progress cbn.
  Show.
  reflexivity.
Qed.

Lemma should_not_unfold (m1 m2 : gmap nat nat) k x :
  dom m1 = dom m2 →
  <[k:=x]> m1 = <[k:=x]> m2 →
  True.
Proof.
  (** Make sure that [injection]/[simplify_eq] does not unfold constructs on
  [gmap] and [gset]. *)
  intros Hdom Hinsert.
  Fail injection Hdom.
  Fail injection Hinsert.
  Fail progress simplify_eq.
  done.
Qed.

(** Test case for issue #139 *)

Lemma test_issue_139 (m : gmap nat nat) : ∃ x, x ∉ dom m.
Proof.
  destruct (exist_fresh (dom m)); eauto.
Qed.

(** Make sure that unification does not eagerly unfold [map_fold] *)

Definition only_evens (m : gmap nat nat) : gmap nat nat :=
  filter (λ '(_,x), (x | 2)) m.

Lemma only_evens_Some m i n : only_evens m !! i = Some n → (n | 2).
Proof.
  intros Hev.
  apply map_lookup_filter_Some in Hev as [??]. done.
Qed.

(** Make sure that [pmap] and [gmap] compute *)

Definition pmap_insert_positives (start step num : positive) : Pmap unit :=
  Pos.iter (λ rec p m,
    rec (p + step)%positive (<[p:=tt]> m)) (λ _ m, m) num start ∅.
Definition pmap_insert_positives_rev (start step num : positive) : Pmap unit :=
  Pos.iter (λ rec p m,
    rec (p - step)%positive (<[p:=tt]> m)) (λ _ m, m) num start ∅.

Definition pmap_insert_positives_test (num : positive) : bool :=
  bool_decide (pmap_insert_positives 1 1 num = pmap_insert_positives_rev num 1 num).

Definition pmap_insert_positives_union_test (num : positive) : bool :=
  bool_decide (pmap_insert_positives 1 1 num =
    pmap_insert_positives 2 2 (Pos.div2_up num) ∪
    pmap_insert_positives 1 2 (Pos.div2_up num)).

Definition pmap_insert_positives_filter_test (num : positive) : bool :=
  bool_decide (pmap_insert_positives 1 2 (Pos.div2_up num) =
    filter (λ '(p,_), Z.odd (Z.pos p)) (pmap_insert_positives 1 1 num)).

(* Test that the time is approximately n-log-n. We cannot test this on CI since
you get different timings all the time. Instead we just test for [128000], which
likely takes forever if the complexity is not n-log-n. *)
(*
Time Eval vm_compute in pmap_insert_positives_test 1000.
Time Eval vm_compute in pmap_insert_positives_test 2000.
Time Eval vm_compute in pmap_insert_positives_test 4000.
Time Eval vm_compute in pmap_insert_positives_test 8000.
Time Eval vm_compute in pmap_insert_positives_test 16000.
Time Eval vm_compute in pmap_insert_positives_test 32000.
Time Eval vm_compute in pmap_insert_positives_test 64000.
Time Eval vm_compute in pmap_insert_positives_test 128000.
Time Eval vm_compute in pmap_insert_positives_test 256000.
Time Eval vm_compute in pmap_insert_positives_test 512000.
Time Eval vm_compute in pmap_insert_positives_test 1000000.
*)
Check "pmap_insert_positives_test".
Eval vm_compute in pmap_insert_positives_test 128000.
Eval vm_compute in pmap_insert_positives_union_test 128000.
Eval vm_compute in pmap_insert_positives_filter_test 128000.

Definition gmap_insert_positives (start step num : positive) : gmap positive unit :=
  Pos.iter (λ rec p m,
    rec (p + step)%positive (<[p:=tt]> m)) (λ _ m, m) num start ∅.
Definition gmap_insert_positives_rev (start step num : positive) : gmap positive unit :=
  Pos.iter (λ rec p m,
    rec (p - step)%positive (<[p:=tt]> m)) (λ _ m, m) num start ∅.

(* Test that the time increases linearly *)
Definition gmap_insert_positives_test (num : positive) : bool :=
  bool_decide (gmap_insert_positives 1 1 num = gmap_insert_positives_rev num 1 num).

Definition gmap_insert_positives_union_test (num : positive) : bool :=
  bool_decide (gmap_insert_positives 1 1 num =
    gmap_insert_positives 2 2 (Pos.div2_up num) ∪
    gmap_insert_positives 1 2 (Pos.div2_up num)).

Definition gmap_insert_positives_filter_test (num : positive) : bool :=
  bool_decide (gmap_insert_positives 1 2 (Pos.div2_up num) =
    filter (λ '(p,_), Z.odd (Z.pos p)) (gmap_insert_positives 1 1 num)).

(* Test that the time is approximately n-log-n. We cannot test this on CI since
you get different timings all the time. Instead we just test for [128000], which
likely takes forever if the complexity is not n-log-n. *)
(*
Time Eval vm_compute in gmap_insert_positives_test 1000.
Time Eval vm_compute in gmap_insert_positives_test 2000.
Time Eval vm_compute in gmap_insert_positives_test 4000.
Time Eval vm_compute in gmap_insert_positives_test 8000.
Time Eval vm_compute in gmap_insert_positives_test 16000.
Time Eval vm_compute in gmap_insert_positives_test 32000.
Time Eval vm_compute in gmap_insert_positives_test 64000.
Time Eval vm_compute in gmap_insert_positives_test 128000.
Time Eval vm_compute in gmap_insert_positives_test 256000.
Time Eval vm_compute in gmap_insert_positives_test 512000.
Time Eval vm_compute in gmap_insert_positives_test 1000000.
*)
Check "gmap_insert_positives_test".
Eval vm_compute in gmap_insert_positives_test 128000.
Eval vm_compute in gmap_insert_positives_union_test 128000.
Eval vm_compute in gmap_insert_positives_filter_test 128000.

(** Make sure that [pmap] and [gmap] have canonical representations, and compute
reasonably efficiently even with [reflexivity]. *)

Check "pmap_insert_comm".
Theorem pmap_insert_comm :
  {[ 3:=false; 2:=true]}%positive =@{Pmap bool} {[ 2:=true; 3:=false ]}%positive.
Proof. simpl. Show. reflexivity. Qed.

Check "pmap_lookup_concrete".
Theorem pmap_lookup_concrete :
  lookup (M:=Pmap bool) 2%positive {[ 3:=false; 2:=true ]}%positive = Some true.
Proof. simpl. Show. reflexivity. Qed.

Theorem pmap_insert_positives_reflexivity_500 :
  pmap_insert_positives 1 1 500 = pmap_insert_positives_rev 500 1 500.
Proof. reflexivity. Qed.
Theorem pmap_insert_positives_reflexivity_1000 :
  pmap_insert_positives 1 1 1000 = pmap_insert_positives_rev 1000 1 1000.
Proof. (* this should take less than a second *) reflexivity. Qed.

Theorem pmap_insert_positives_union_reflexivity_500 :
  (pmap_insert_positives_rev 1 1 400) ∪
    (pmap_insert_positives 1 1 500 ∖ pmap_insert_positives_rev 1 1 400)
  = pmap_insert_positives 1 1 500.
Proof. reflexivity. Qed.
Theorem pmap_insert_positives_union_reflexivity_1000 :
  (pmap_insert_positives_rev 1 1 800) ∪
    (pmap_insert_positives 1 1 1000 ∖ pmap_insert_positives_rev 1 1 800)
  = pmap_insert_positives 1 1 1000.
Proof. (* this should less than a second *) reflexivity. Qed.

Check "gmap_insert_comm".
Theorem gmap_insert_comm :
  {[ 3:=false; 2:=true]} =@{gmap nat bool} {[ 2:=true; 3:=false ]}.
Proof. simpl. Show. reflexivity. Qed.

Check "gmap_lookup_concrete".
Theorem gmap_lookup_concrete :
  lookup (M:=gmap nat bool) 2 {[ 3:=false; 2:=true ]} = Some true.
Proof. simpl. Show. reflexivity. Qed.

Theorem gmap_insert_positives_reflexivity_500 :
  gmap_insert_positives 1 1 500 = gmap_insert_positives_rev 500 1 500.
Proof. reflexivity. Qed.
Theorem gmap_insert_positives_reflexivity_1000 :
  gmap_insert_positives 1 1 1000 = gmap_insert_positives_rev 1000 1 1000.
Proof. (* this should less than a second *) reflexivity. Qed.

Theorem gmap_insert_positives_union_reflexivity_500 :
  (gmap_insert_positives_rev 1 1 400) ∪
    (gmap_insert_positives 1 1 500 ∖ gmap_insert_positives_rev 1 1 400)
  = gmap_insert_positives 1 1 500.
Proof. reflexivity. Qed.
Theorem gmap_insert_positives_union_reflexivity_1000 :
  (gmap_insert_positives_rev 1 1 800) ∪
    (gmap_insert_positives 1 1 1000 ∖ gmap_insert_positives_rev 1 1 800)
  = gmap_insert_positives 1 1 1000.
Proof. (* this should less than a second *) reflexivity. Qed.

(** This should be immediate, see std++ issue #183 *)
Goal dom ((<[10%positive:=1]> ∅) : Pmap _) = dom ((<[10%positive:=2]> ∅) : Pmap _).
Proof. reflexivity. Qed.

Goal dom ((<["f":=1]> ∅) : gmap _ _) = dom ((<["f":=2]> ∅) : gmap _ _).
Proof. reflexivity. Qed.

(** Make sure that [pmap] and [gmap] can be used in nested inductive
definitions *)

Inductive test := Test : Pmap test → test.

Fixpoint test_size (t : test) : nat :=
  let 'Test ts := t in S (map_fold (λ _ t', plus (test_size t')) 0 ts).

Fixpoint test_merge (t1 t2 : test) : test :=
  match t1, t2 with
  | Test ts1, Test ts2 =>
     Test $ union_with (λ t1 t2, Some (test_merge t1 t2)) ts1 ts2
  end.

Lemma test_size_merge :
  test_size (test_merge
    (Test {[ 10%positive := Test ∅; 50%positive := Test ∅ ]})
    (Test {[ 10%positive := Test ∅; 32%positive := Test ∅ ]})) = 4.
Proof. reflexivity. Qed.

Global Instance test_eq_dec : EqDecision test.
Proof.
  refine (fix go t1 t2 :=
    let _ : EqDecision test := @go in
    match t1, t2 with
    | Test ts1, Test ts2 => cast_if (decide (ts1 = ts2))
    end); abstract congruence.
Defined.

Inductive gtest K `{Countable K} := GTest : gmap K (gtest K) → gtest K.
Arguments GTest {_ _ _} _.

Fixpoint gtest_size `{Countable K} (t : gtest K) : nat :=
  let 'GTest ts := t in S (map_fold (λ _ t', plus (gtest_size t')) 0 ts).

Fixpoint gtest_merge `{Countable K} (t1 t2 : gtest K) : gtest K :=
  match t1, t2 with
  | GTest ts1, GTest ts2 =>
     GTest $ union_with (λ t1 t2, Some (gtest_merge t1 t2)) ts1 ts2
  end.

Lemma gtest_size_merge :
  gtest_size (gtest_merge
    (GTest {[ 10 := GTest ∅; 50 := GTest ∅ ]})
    (GTest {[ 10 := GTest ∅; 32 := GTest ∅ ]})) = 4.
Proof. reflexivity. Qed.

Lemma gtest_size_merge_string :
  gtest_size (gtest_merge
    (GTest {[ "foo" := GTest ∅; "bar" := GTest ∅ ]})
    (GTest {[ "foo" := GTest ∅; "baz" := GTest ∅ ]})) = 4.
Proof. reflexivity. Qed.

Global Instance gtest_eq_dec `{Countable K} : EqDecision (gtest K).
Proof.
  refine (fix go t1 t2 :=
    let _ : EqDecision (gtest K) := @go in
    match t1, t2 with
    | GTest ts1, GTest ts2 => cast_if (decide (ts1 = ts2))
    end); abstract congruence.
Defined.

Lemma gtest_ind' `{Countable K} (P : gtest K → Prop) :
  (∀ ts, map_Forall (λ _, P) ts → P (GTest ts)) →
  ∀ t, P t.
Proof.
  intros Hnode t.
  remember (gtest_size t) as n eqn:Hn. revert t Hn.
  induction (lt_wf n) as [n _ IH]; intros [ts] ->; simpl in *.
  apply Hnode. revert ts IH.
  apply (map_fold_ind (λ r ts, (∀ n', n' < S r → _) → map_Forall (λ _, P) ts)).
  - intros IH. apply map_Forall_empty.
  - intros k t m r ? IHm IHt. apply map_Forall_insert; [done|]. split.
    + eapply IHt; [|done]; lia.
    + eapply IHm. intros; eapply IHt;[|done]; lia.
Qed.

(** We show that [gtest K] is countable itself. This means that we can use
[gtest K] (which involves nested uses of [gmap]) as keys in [gmap]/[gset], i.e.,
[gmap (gtest K) V] and [gset (gtest K)]. And even [gtest (gtest K)].

Showing that [gtest K] is countable is not trivial due to its nested-inductive
nature. We need to write [encode] and [decode] functions, and prove that they
are inverses. We do this by converting to/from [gen_tree]. This shows that Coq's
guardedness checker accepts non-trivial recursive definitions involving [gtest],
and we can do non-trivial induction proofs about [gtest]. *)
Global Program Instance gtest_countable `{Countable K} : Countable (gtest K) :=
  let enc :=
    fix go t :=
      let 'GTest ts := t return _ in
      GenNode 0 (map_fold (λ (k : K) t rec, GenLeaf k :: go t :: rec) [] ts) in
  let dec_list := λ dec : gen_tree K → gtest K,
    fix go ts :=
      match ts return gmap K (gtest K) with
      | GenLeaf k :: t :: ts => <[k:=dec t]> (go ts)
      | _ => ∅
      end in
  let dec :=
    fix go t :=
      match t return _ with
      | GenNode 0 ts => GTest (dec_list go ts)
      | _ => GTest ∅ (* dummy *)
      end in
  inj_countable' enc dec _.
Next Obligation.
  intros K ?? enc dec_list dec t.
  remember (gtest_size t) as n eqn:Hn. revert t Hn.
  induction (lt_wf n) as [n _ IH]; intros [ts] ->; simpl in *; f_equal.
  revert ts IH. apply (map_fold_ind (λ r ts, _ → dec_list dec r = ts)); [done|].
  intros i t ts r ? IHts IHt; simpl. f_equal.
  - eapply IHt; [|done]. rewrite map_fold_insert_L by auto with lia. lia.
  - apply IHts; intros n ? t' ->. eapply IHt; [|done].
    rewrite map_fold_insert_L by auto with lia. lia.
Qed.

Goal
  ({[ GTest {[ 1 := GTest ∅ ]} := "foo" ]} : gmap (gtest nat) string)
  !! GTest {[ 1 := GTest ∅ ]} = Some "foo".
Proof. reflexivity. Qed.

Goal {[ GTest {[ 1 := GTest ∅ ]} ]} ≠@{gset (gtest nat)} {[ GTest ∅ ]}.
Proof. discriminate. Qed.

Goal GTest {[ GTest {[ 1 := GTest ∅ ]} := GTest ∅ ]} ≠@{gtest (gtest nat)} GTest ∅.
Proof. discriminate. Qed.
