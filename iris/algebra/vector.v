From stdpp Require Export vector.
From iris.algebra Require Export ofe.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

Section ofe.
  Context {A : ofe}.

  Local Instance vec_equiv m : Equiv (vec A m) := equiv (A:=list A).
  Local Instance vec_dist m : Dist (vec A m) := dist (A:=list A).

  Definition vec_ofe_mixin m : OfeMixin (vec A m).
  Proof. by apply (iso_ofe_mixin vec_to_list). Qed.
  Canonical Structure vecO m : ofe := Ofe (vec A m) (vec_ofe_mixin m).

  Global Instance list_cofe `{Cofe A} m : Cofe (vecO m).
  Proof.
    apply: (iso_cofe_subtype (λ l : list A, length l = m)
      (λ l, eq_rect _ (vec A) (list_to_vec l) m) vec_to_list)=> //.
    - intros v []. by rewrite /= vec_to_list_to_vec.
    - intros c. by rewrite (conv_compl 0 (chain_map _ c)) /= vec_to_list_length.
  Qed.

  Global Instance vnil_discrete : Discrete (@vnil A).
  Proof. intros v _. by inv_vec v. Qed.
  Global Instance vcons_discrete n x (v : vec A n) :
    Discrete x → Discrete v → Discrete (x ::: v).
  Proof.
    intros ?? v' ?. inv_vec v'=>x' v'. inversion_clear 1.
    constructor.
    - by apply discrete.
    - change (v ≡ v'). by apply discrete.
  Qed.
  Global Instance vec_ofe_discrete m : OfeDiscrete A → OfeDiscrete (vecO m).
  Proof. intros ? v. induction v; apply _. Qed.
End ofe.

Global Arguments vecO : clear implicits.
Typeclasses Opaque vec_dist.

Section proper.
  Context {A : ofe}.

  Global Instance vcons_ne n :
    Proper (dist n ==> forall_relation (λ x, dist n ==> dist n)) (@vcons A).
  Proof. by constructor. Qed.
  Global Instance vcons_proper :
    Proper (equiv ==> forall_relation (λ x, equiv ==> equiv)) (@vcons A).
  Proof. by constructor. Qed.

  Global Instance vlookup_ne n m :
    Proper (dist n ==> eq ==> dist n) (@Vector.nth A m).
  Proof.
    intros v. induction v as [|x m v IH]; intros v'; inv_vec v'.
    - intros _ x. inv_fin x.
    - intros x' v' EQ i ? <-. inversion_clear EQ. inv_fin i=> // i. by apply IH.
  Qed.
  Global Instance vlookup_proper m :
    Proper (equiv ==> eq ==> equiv) (@Vector.nth A m).
  Proof.
    intros v v' ? x x' ->. apply equiv_dist=> n. f_equiv. by apply equiv_dist.
  Qed.

  Global Instance vec_to_list_ne m : NonExpansive (@vec_to_list A m).
  Proof. by intros v v'. Qed.
  Global Instance vec_to_list_proper m : Proper ((≡) ==> (≡)) (@vec_to_list A m).
  Proof. by intros v v'. Qed.
End proper.

(** Functor *)
Definition vec_map {A B : ofe} m (f : A → B) : vecO A m → vecO B m :=
  @vmap A B f m.
Lemma vec_map_ext_ne {A B : ofe} m (f g : A → B) (v : vec A m) n :
  (∀ x, f x ≡{n}≡ g x) → vec_map m f v ≡{n}≡ vec_map m g v.
Proof.
  intros Hf. eapply (list_fmap_ext_ne f g v) in Hf.
  by rewrite -!vec_to_list_map in Hf.
Qed.
Global Instance vec_map_ne {A B : ofe} m f n :
  Proper (dist n ==> dist n) f →
  Proper (dist n ==> dist n) (@vec_map A B m f).
Proof.
  intros ? v v' H. eapply list_fmap_ne in H; last done.
  by rewrite -!vec_to_list_map in H.
Qed.
Definition vecO_map {A B : ofe} m (f : A -n> B) : vecO A m -n> vecO B m :=
  OfeMor (vec_map m f).
Global Instance vecO_map_ne {A A'} m :
  NonExpansive (@vecO_map A A' m).
Proof. intros n f g ? v. by apply vec_map_ext_ne. Qed.

Program Definition vecOF (F : oFunctor) m : oFunctor := {|
  oFunctor_car A _ B _ := vecO (oFunctor_car F A B) m;
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := vecO_map m (oFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n m f g Hfg. by apply vecO_map_ne, oFunctor_map_ne.
Qed.
Next Obligation.
  intros F m A ? B ? l.
  change (vec_to_list (vec_map m (oFunctor_map F (cid, cid)) l) ≡ l).
  rewrite vec_to_list_map. apply listOF.
Qed.
Next Obligation.
  intros F m A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' l.
  change (vec_to_list (vec_map m (oFunctor_map F (f ◎ g, g' ◎ f')) l)
    ≡ vec_map m (oFunctor_map F (g, g')) (vec_map m (oFunctor_map F (f, f')) l)).
  rewrite !vec_to_list_map. by apply: (oFunctor_map_compose (listOF F) f g f' g').
Qed.

Global Instance vecOF_contractive F m :
  oFunctorContractive F → oFunctorContractive (vecOF F m).
Proof.
  by intros ?? A1 ? A2 ? B1 ? B2 ? n ???; apply vecO_map_ne; first apply oFunctor_map_contractive.
Qed.
