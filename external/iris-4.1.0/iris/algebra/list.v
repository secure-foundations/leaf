From stdpp Require Export list.
From iris.algebra Require Export ofe.
From iris.algebra Require Import big_op.
From iris.prelude Require Import options.

Section ofe.
Context {A : ofe}.
Implicit Types l : list A.

Local Instance list_dist : Dist (list A) := λ n, Forall2 (dist n).

Lemma list_dist_Forall2 n l k : l ≡{n}≡ k ↔ Forall2 (dist n) l k.
Proof. done. Qed.
Lemma list_dist_lookup n l1 l2 : l1 ≡{n}≡ l2 ↔ ∀ i, l1 !! i ≡{n}≡ l2 !! i.
Proof. setoid_rewrite option_dist_Forall2. apply Forall2_lookup. Qed.

Global Instance cons_ne : NonExpansive2 (@cons A) := _.
Global Instance app_ne : NonExpansive2 (@app A) := _.
Global Instance length_ne n : Proper (dist n ==> (=)) (@length A) := _.
Global Instance tail_ne : NonExpansive (@tail A) := _.
Global Instance take_ne n : NonExpansive (@take A n) := _.
Global Instance drop_ne n : NonExpansive (@drop A n) := _.
Global Instance head_ne : NonExpansive (head (A:=A)).
Proof. destruct 1; by constructor. Qed.
Global Instance list_lookup_ne i : NonExpansive (lookup (M:=list A) i).
Proof. intros ????. by apply option_dist_Forall2, Forall2_lookup. Qed.
Global Instance list_lookup_total_ne `{!Inhabited A} i :
  NonExpansive (lookup_total (M:=list A) i).
Proof. intros ???. rewrite !list_lookup_total_alt. by intros ->. Qed.
Global Instance list_alter_ne n :
  Proper ((dist n ==> dist n) ==> (=) ==> dist n ==> dist n) (alter (M:=list A)) := _.
Global Instance list_insert_ne i : NonExpansive2 (insert (M:=list A) i) := _.
Global Instance list_inserts_ne i : NonExpansive2 (@list_inserts A i) := _.
Global Instance list_delete_ne i : NonExpansive (delete (M:=list A) i) := _.
Global Instance option_list_ne : NonExpansive (@option_list A).
Proof. intros ????; by apply Forall2_option_list, option_dist_Forall2. Qed.
Global Instance list_filter_ne n P `{∀ x, Decision (P x)} :
  Proper (dist n ==> iff) P →
  Proper (dist n ==> dist n) (filter (B:=list A) P) := _.
Global Instance replicate_ne n : NonExpansive (@replicate A n) := _.
Global Instance reverse_ne : NonExpansive (@reverse A) := _.
Global Instance last_ne : NonExpansive (@last A).
Proof. intros ????; by apply option_dist_Forall2, Forall2_last. Qed.
Global Instance resize_ne n : NonExpansive2 (@resize A n) := _.

Global Instance cons_dist_inj n :
  Inj2 (dist n) (dist n) (dist n) (@cons A).
Proof. by inversion_clear 1. Qed.

Lemma nil_dist_eq n l : l ≡{n}≡ [] ↔ l = [].
Proof. split; by inversion 1. Qed.
Lemma cons_dist_eq n l k y :
  l ≡{n}≡ y :: k → ∃ x l', x ≡{n}≡ y ∧ l' ≡{n}≡ k ∧ l = x :: l'.
Proof. apply Forall2_cons_inv_r. Qed.
Lemma app_dist_eq n l k1 k2 :
  l ≡{n}≡ k1 ++ k2 ↔ ∃ k1' k2', l = k1' ++ k2' ∧ k1' ≡{n}≡ k1 ∧ k2' ≡{n}≡ k2.
Proof. rewrite list_dist_Forall2 Forall2_app_inv_r. naive_solver. Qed.
Lemma list_singleton_dist_eq n l x :
  l ≡{n}≡ [x] ↔ ∃ x', l = [x'] ∧ x' ≡{n}≡ x.
Proof.
  split; [|by intros (?&->&->)].
  intros (?&?&?&->%Forall2_nil_inv_r&->)%list_dist_Forall2%Forall2_cons_inv_r.
  eauto.
Qed.

Definition list_ofe_mixin : OfeMixin (list A).
Proof.
  split.
  - intros l k. rewrite list_equiv_Forall2 -Forall2_forall.
    split; induction 1; constructor; intros; try apply equiv_dist; auto.
  - apply _.
  - rewrite /dist /list_dist. eauto using Forall2_impl, dist_le with si_solver.
Qed.
Canonical Structure listO := Ofe (list A) list_ofe_mixin.

(** To define [compl : chain (list A) → list A] we make use of the fact that
given a given chain [c0, c1, c2, ...] of lists, the list [c0] completely
determines the shape (i.e. the length) of all lists in the chain. So, the
[compl] operation is defined by structural recursion on [c0], and takes the
completion of the elements of all lists in the chain point-wise. We use [head]
and [tail] as the inverse of [cons]. *)
Fixpoint list_compl_go `{!Cofe A} (c0 : list A) (c : chain listO) : listO :=
  match c0 with
  | [] => []
  | x :: c0 => compl (chain_map (default x ∘ head) c) :: list_compl_go c0 (chain_map tail c)
  end.

Global Program Instance list_cofe `{!Cofe A} : Cofe listO :=
  {| compl c := list_compl_go (c 0) c |}.
Next Obligation.
  intros ? n c; rewrite /compl.
  assert (c 0 ≡{0}≡ c n) as Hc0 by (symmetry; apply chain_cauchy; lia).
  revert Hc0. generalize (c 0)=> c0. revert c.
  induction c0 as [|x c0 IH]=> c Hc0 /=.
  { by inversion Hc0. }
  apply symmetry, cons_dist_eq in Hc0 as (x' & xs' & Hx & Hc0 & Hcn).
  rewrite Hcn. f_equiv.
  - by rewrite conv_compl /= Hcn /=.
  - rewrite IH /= ?Hcn //.
Qed.

Global Instance list_ofe_discrete : OfeDiscrete A → OfeDiscrete listO.
Proof. induction 2; constructor; try apply (discrete _); auto. Qed.

Global Instance nil_discrete : Discrete (@nil A).
Proof. inversion_clear 1; constructor. Qed.
Global Instance cons_discrete x l : Discrete x → Discrete l → Discrete (x :: l).
Proof. intros ??; inversion_clear 1; constructor; by apply discrete. Qed.

Lemma dist_Permutation n l1 l2 l3 :
  l1 ≡{n}≡ l2 → l2 ≡ₚ l3 → ∃ l2', l1 ≡ₚ l2' ∧ l2' ≡{n}≡ l3.
Proof.
  intros Hequiv Hperm. revert l1 Hequiv.
  induction Hperm as [|x l2 l3 _ IH|x y l2|l2 l3 l4 _ IH1 _ IH2]; intros l1.
  - intros ?. by exists l1.
  - intros (x'&l2'&?&(l2''&?&?)%IH&->)%cons_dist_eq.
    exists (x' :: l2''). by repeat constructor.
  - intros (y'&?&?&(x'&l2'&?&?&->)%cons_dist_eq&->)%cons_dist_eq.
    exists (x' :: y' :: l2'). by repeat constructor.
  - intros (l2'&?&(l3'&?&?)%IH2)%IH1. exists l3'. split; [by etrans|done].
Qed.
End ofe.

Global Arguments listO : clear implicits.

(** Non-expansiveness of higher-order list functions and big-ops *)
Global Instance list_fmap_ne {A B : ofe} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (fmap (M:=list) (A:=A) (B:=B)).
Proof. intros f1 f2 Hf l1 l2 Hl; by eapply Forall2_fmap, Forall2_impl; eauto. Qed.
Global Instance list_omap_ne {A B : ofe} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (omap (M:=list) (A:=A) (B:=B)).
Proof.
  intros f1 f2 Hf. induction 1 as [|x1 x2 l1 l2 Hx Hl]; csimpl; [constructor|].
  destruct (Hf _ _ Hx); [f_equiv|]; auto.
Qed.
Global Instance imap_ne {A B : ofe} n :
  Proper (pointwise_relation _ ((dist n ==> dist n)) ==> dist n ==> dist n)
         (imap (A:=A) (B:=B)).
Proof.
  intros f1 f2 Hf l1 l2 Hl. revert f1 f2 Hf.
  induction Hl as [|x1 x2 l1 l2 ?? IH]; intros f1 f2 Hf; simpl; [constructor|].
  f_equiv; [by apply Hf|]. apply IH. intros i y1 y2 Hy. by apply Hf.
Qed.
Global Instance list_bind_ne {A B : ofe} (f : A → list A) n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n)
         (mbind (M:=list) (A:=A) (B:=B)).
Proof. intros f1 f2 Hf. induction 1; csimpl; [constructor|f_equiv; auto]. Qed.
Global Instance list_join_ne {A : ofe} : NonExpansive (mjoin (M:=list) (A:=A)).
Proof. induction 1; simpl; [constructor|solve_proper]. Qed.
Global Instance zip_with_ne {A B C : ofe} n :
  Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n)
         (zip_with (A:=A) (B:=B) (C:=C)).
Proof.
  intros f1 f2 Hf.
  induction 1; destruct 1; simpl; [constructor..|f_equiv; try apply Hf; auto].
Qed.

Global Instance list_fmap_dist_inj {A B : ofe} (f : A → B) n :
  Inj (≡{n}≡) (≡{n}≡) f → Inj (≡{n}@{list A}≡) (≡{n}@{list B}≡) (fmap f).
Proof. apply list_fmap_inj. Qed.

Lemma big_opL_ne_2 {M : ofe} {o : M → M → M} `{!Monoid o} {A : ofe} (f g : nat → A → M) l1 l2 n :
  l1 ≡{n}≡ l2 →
  (∀ k y1 y2,
    l1 !! k = Some y1 → l2 !! k = Some y2 → y1 ≡{n}≡ y2 → f k y1 ≡{n}≡ g k y2) →
  ([^o list] k ↦ y ∈ l1, f k y) ≡{n}≡ ([^o list] k ↦ y ∈ l2, g k y).
Proof.
  intros Hl Hf. apply big_opL_gen_proper_2; try (apply _ || done).
  { apply monoid_ne. }
  intros k. assert (l1 !! k ≡{n}≡ l2 !! k) as Hlk by (by f_equiv).
  destruct (l1 !! k) eqn:?, (l2 !! k) eqn:?; inversion Hlk; naive_solver.
Qed.

(** Functor *)
Lemma list_fmap_ext_ne {A} {B : ofe} (f g : A → B) (l : list A) n :
  (∀ x, f x ≡{n}≡ g x) → f <$> l ≡{n}≡ g <$> l.
Proof. intros Hf. by apply Forall2_fmap, Forall_Forall2_diag, Forall_true. Qed.
Definition listO_map {A B} (f : A -n> B) : listO A -n> listO B :=
  OfeMor (fmap f : listO A → listO B).
Global Instance listO_map_ne A B : NonExpansive (@listO_map A B).
Proof. intros n f g ? l. by apply list_fmap_ext_ne. Qed.

Program Definition listOF (F : oFunctor) : oFunctor := {|
  oFunctor_car A _ B _ := listO (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := listO_map (oFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_equiv_ext=>???. apply oFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_equiv_ext=>???; apply oFunctor_map_compose.
Qed.

Global Instance listOF_contractive F :
  oFunctorContractive F → oFunctorContractive (listOF F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, oFunctor_map_contractive.
Qed.
