From iris.algebra Require Import cmra view auth agree csum list excl gmap.
From iris.algebra.lib Require Import excl_auth gmap_view.
From iris.base_logic Require Import bi derived.
From iris.prelude Require Import options.

(** Internalized properties of our CMRA constructions. *)
Local Coercion uPred_holds : uPred >-> Funclass.

Section upred.
Context {M : ucmra}.

(* Force implicit argument M *)
Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P Q).
Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).

Lemma prod_validI {A B : cmra} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
Proof. by uPred.unseal. Qed.
Lemma option_validI {A : cmra} (mx : option A) :
  ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : uPred M end.
Proof. uPred.unseal. by destruct mx. Qed.
Lemma discrete_fun_validI {A} {B : A → ucmra} (g : discrete_fun B) :
  ✓ g ⊣⊢ ∀ i, ✓ g i.
Proof. by uPred.unseal. Qed.

Lemma frac_validI (q : Qp) : ✓ q ⊣⊢ ⌜q ≤ 1⌝%Qp.
Proof. rewrite uPred.discrete_valid frac_valid //. Qed.

Section gmap_ofe.
  Context `{Countable K} {A : ofe}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.

  Lemma gmap_equivI m1 m2 : m1 ≡ m2 ⊣⊢ ∀ i, m1 !! i ≡ m2 !! i.
  Proof. by uPred.unseal. Qed.
End gmap_ofe.

Section gmap_cmra.
  Context `{Countable K} {A : cmra}.
  Implicit Types m : gmap K A.

  Lemma gmap_validI m : ✓ m ⊣⊢ ∀ i, ✓ (m !! i).
  Proof. by uPred.unseal. Qed.
  Lemma singleton_validI i x : ✓ ({[ i := x ]} : gmap K A) ⊣⊢ ✓ x.
  Proof.
    rewrite gmap_validI. apply: anti_symm.
    - rewrite (bi.forall_elim i) lookup_singleton option_validI. done.
    - apply bi.forall_intro=>j. destruct (decide (i = j)) as [<-|Hne].
      + rewrite lookup_singleton option_validI. done.
      + rewrite lookup_singleton_ne // option_validI.
        apply bi.True_intro.
  Qed.
End gmap_cmra.

Section list_ofe.
  Context {A : ofe}.
  Implicit Types l : list A.

  Lemma list_equivI l1 l2 : l1 ≡ l2 ⊣⊢ ∀ i, l1 !! i ≡ l2 !! i.
  Proof. uPred.unseal; constructor=> n x ?. apply list_dist_lookup. Qed.
End list_ofe.

Section excl.
  Context {A : ofe}.
  Implicit Types a b : A.
  Implicit Types x y : excl A.

  Lemma excl_equivI x y :
    x ≡ y ⊣⊢ match x, y with
                        | Excl a, Excl b => a ≡ b
                        | ExclBot, ExclBot => True
                        | _, _ => False
                        end.
  Proof.
    uPred.unseal. do 2 split.
    - by destruct 1.
    - by destruct x, y; try constructor.
  Qed.
  Lemma excl_validI x :
    ✓ x ⊣⊢ if x is ExclBot then False else True.
  Proof. uPred.unseal. by destruct x. Qed.
End excl.

Section agree.
  Context {A : ofe}.
  Implicit Types a b : A.
  Implicit Types x y : agree A.

  Lemma agree_equivI a b : to_agree a ≡ to_agree b ⊣⊢ (a ≡ b).
  Proof.
    uPred.unseal. do 2 split.
    - intros Hx. exact: (inj to_agree).
    - intros Hx. exact: to_agree_ne.
  Qed.
  Lemma agree_validI x y : ✓ (x ⋅ y) ⊢ x ≡ y.
  Proof. uPred.unseal; split=> r n _ ?; by apply: agree_op_invN. Qed.

  Lemma to_agree_uninjI x : ✓ x ⊢ ∃ a, to_agree a ≡ x.
  Proof. uPred.unseal. split=> n y _. exact: to_agree_uninjN. Qed.
End agree.

Section csum_ofe.
  Context {A B : ofe}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma csum_equivI (x y : csum A B) :
    x ≡ y ⊣⊢ match x, y with
                        | Cinl a, Cinl a' => a ≡ a'
                        | Cinr b, Cinr b' => b ≡ b'
                        | CsumBot, CsumBot => True
                        | _, _ => False
                        end.
  Proof.
    uPred.unseal; do 2 split; first by destruct 1.
      by destruct x, y; try destruct 1; try constructor.
  Qed.
End csum_ofe.

Section csum_cmra.
  Context {A B : cmra}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma csum_validI (x : csum A B) :
    ✓ x ⊣⊢ match x with
                      | Cinl a => ✓ a
                      | Cinr b => ✓ b
                      | CsumBot => False
                      end.
  Proof. uPred.unseal. by destruct x. Qed.
End csum_cmra.

Section view.
  Context {A B} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types ag : option (frac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.

  Lemma view_both_dfrac_validI_1 (relI : uPred M) dq a b :
    (∀ n (x : M), rel n a b → relI n x) →
    ✓ (●V{dq} a ⋅ ◯V b : view rel) ⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros Hrel. uPred.unseal. split=> n x _ /=.
    rewrite /uPred_holds /= view_both_dfrac_validN. by move=> [? /Hrel].
  Qed.
  Lemma view_both_dfrac_validI_2 (relI : uPred M) dq a b :
    (∀ n (x : M), relI n x → rel n a b) →
    ⌜✓dq⌝ ∧ relI ⊢ ✓ (●V{dq} a ⋅ ◯V b : view rel).
  Proof.
    intros Hrel. uPred.unseal. split=> n x _ /=.
    rewrite /uPred_holds /= view_both_dfrac_validN. by move=> [? /Hrel].
  Qed.
  Lemma view_both_dfrac_validI (relI : uPred M) dq a b :
    (∀ n (x : M), rel n a b ↔ relI n x) →
    ✓ (●V{dq} a ⋅ ◯V b : view rel) ⊣⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros. apply (anti_symm _);
      [apply view_both_dfrac_validI_1|apply view_both_dfrac_validI_2]; naive_solver.
  Qed.

  Lemma view_both_validI_1 (relI : uPred M) a b :
    (∀ n (x : M), rel n a b → relI n x) →
    ✓ (●V a ⋅ ◯V b : view rel) ⊢ relI.
  Proof. intros. by rewrite view_both_dfrac_validI_1 // bi.and_elim_r. Qed.
  Lemma view_both_validI_2 (relI : uPred M) a b :
    (∀ n (x : M), relI n x → rel n a b) →
    relI ⊢ ✓ (●V a ⋅ ◯V b : view rel).
  Proof.
    intros. rewrite -view_both_dfrac_validI_2 //.
    apply bi.and_intro; [|done]. by apply bi.pure_intro.
  Qed.
  Lemma view_both_validI (relI : uPred M) a b :
    (∀ n (x : M), rel n a b ↔ relI n x) →
    ✓ (●V a ⋅ ◯V b : view rel) ⊣⊢ relI.
  Proof.
    intros. apply (anti_symm _);
      [apply view_both_validI_1|apply view_both_validI_2]; naive_solver.
  Qed.

  Lemma view_auth_dfrac_validI (relI : uPred M) dq a :
    (∀ n (x : M), relI n x ↔ rel n a ε) →
    ✓ (●V{dq} a : view rel) ⊣⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros. rewrite -(right_id ε op (●V{dq} a)). by apply view_both_dfrac_validI.
  Qed.
  Lemma view_auth_validI (relI : uPred M) a :
    (∀ n (x : M), relI n x ↔ rel n a ε) →
    ✓ (●V a : view rel) ⊣⊢ relI.
  Proof. intros. rewrite -(right_id ε op (●V a)). by apply view_both_validI. Qed.

  Lemma view_frag_validI (relI : uPred M) b :
    (∀ n (x : M), relI n x ↔ ∃ a, rel n a b) →
    ✓ (◯V b : view rel) ⊣⊢ relI.
  Proof. uPred.unseal=> Hrel. split=> n x _. by rewrite Hrel. Qed.
End view.

Section auth.
  Context {A : ucmra}.
  Implicit Types a b : A.
  Implicit Types x y : auth A.

  Lemma auth_auth_dfrac_validI dq a : ✓ (●{dq} a) ⊣⊢ ⌜✓dq⌝ ∧ ✓ a.
  Proof.
    apply view_auth_dfrac_validI=> n. uPred.unseal; split; [|by intros [??]].
    split; [|done]. apply ucmra_unit_leastN.
  Qed.
  Lemma auth_auth_validI a : ✓ (● a) ⊣⊢ ✓ a.
  Proof.
    by rewrite auth_auth_dfrac_validI bi.pure_True // left_id.
  Qed.

  Lemma auth_frag_validI a : ✓ (◯ a) ⊣⊢ ✓ a.
  Proof.
    apply view_frag_validI=> n x.
    rewrite auth_view_rel_exists. by uPred.unseal.
  Qed.

  Lemma auth_both_dfrac_validI dq a b :
    ✓ (●{dq} a ⋅ ◯ b) ⊣⊢ ⌜✓dq⌝ ∧ (∃ c, a ≡ b ⋅ c) ∧ ✓ a.
  Proof. apply view_both_dfrac_validI=> n. by uPred.unseal. Qed.
  Lemma auth_both_validI a b :
    ✓ (● a ⋅ ◯ b) ⊣⊢ (∃ c, a ≡ b ⋅ c) ∧ ✓ a.
  Proof.
    by rewrite auth_both_dfrac_validI bi.pure_True // left_id.
  Qed.

End auth.

Section excl_auth.
  Context {A : ofe}.
  Implicit Types a b : A.

  Lemma excl_auth_agreeI a b : ✓ (●E a ⋅ ◯E b) ⊢ (a ≡ b).
  Proof.
    rewrite auth_both_validI bi.and_elim_l.
    apply bi.exist_elim=> -[[c|]|];
      by rewrite option_equivI /= excl_equivI //= bi.False_elim.
  Qed.
End excl_auth.

Section gmap_view.
  Context {K : Type} `{Countable K} {V : ofe}.
  Implicit Types (m : gmap K V) (k : K) (dq : dfrac) (v : V).

  Lemma gmap_view_both_validI m k dq v :
    ✓ (gmap_view_auth 1 m ⋅ gmap_view_frag k dq v) ⊢
    ✓ dq ∧ m !! k ≡ Some v.
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag. apply view_both_validI_1.
    intros n a. uPred.unseal. apply gmap_view.gmap_view_rel_lookup.
  Qed.

  Lemma gmap_view_frag_op_validI k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ⊣⊢
    ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite /gmap_view_frag -view_frag_op. apply view_frag_validI=> n x.
    rewrite gmap_view.gmap_view_rel_exists singleton_op singleton_validN.
    rewrite -pair_op pair_validN to_agree_op_validN. by uPred.unseal.
  Qed.

End gmap_view.

End upred.
