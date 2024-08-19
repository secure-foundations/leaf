From stdpp Require Import nat_cancel.
From iris.proofmode Require Import modality_instances classes.
From iris.prelude Require Import options.
Import bi.

Section class_instances_internal_eq.
Context `{!BiInternalEq PROP}.
Implicit Types P Q R : PROP.

(* When a user calls [iPureIntro] on [⊢ a ≡ b], the following instance turns
  turns this into the pure goal [a ≡ b : Prop].
  If [a, b : A] with [LeibnizEquiv A], another candidate would be [a = b]. While
  this does not lead to information loss, [=] is harder to prove than [≡]. We thus
  leave such simplifications to the user (e.g. they can call [fold_leibniz]). *)
Global Instance from_pure_internal_eq {A : ofe} (a b : A) :
  @FromPure PROP false (a ≡ b) (a ≡ b).
Proof. by rewrite /FromPure pure_internal_eq. Qed.

(* On the other hand, when a user calls [iIntros "%H"] on [⊢ (a ≡ b) -∗ P],
  it is most convenient if [H] is as strong as possible---meaning, the user would
  rather get [H : a = b] than [H : a ≡ b]. This is only possible if the
  equivalence on [A] implies Leibniz equality (i.e., we have [LeibnizEquiv A]).
  If the equivalence on [A] does not imply Leibniz equality, we cannot simplify
  [a ≡ b] any further.
  The following instance implements above logic, while avoiding a double search
  for [Discrete a]. *)
Global Instance into_pure_eq {A : ofe} (a b : A) (P : Prop) :
  Discrete a →
  TCOr (TCAnd (LeibnizEquiv A) (TCEq P (a = b)))
       (TCEq P (a ≡ b)) →
  @IntoPure PROP (a ≡ b) P.
Proof.
  move=> ? [[? ->]|->]; rewrite /IntoPure discrete_eq; last done.
  by rewrite leibniz_equiv_iff.
Qed.

Global Instance from_modal_Next {A : ofe} (x y : A) :
  FromModal (PROP1:=PROP) (PROP2:=PROP) True (modality_laterN 1)
    (▷^1 (x ≡ y) : PROP)%I (Next x ≡ Next y) (x ≡ y).
Proof. by rewrite /FromModal /= later_equivI. Qed.

Global Instance into_laterN_Next {A : ofe} only_head n n' (x y : A) :
  NatCancel n 1 n' 0 →
  IntoLaterN (PROP:=PROP) only_head n (Next x ≡ Next y) (x ≡ y) | 2.
Proof.
  rewrite /IntoLaterN /MaybeIntoLaterN /NatCancel Nat.add_0_r.
  move=> <-. rewrite later_equivI. by rewrite Nat.add_comm /= -laterN_intro.
Qed.

Global Instance into_internal_eq_internal_eq {A : ofe} (x y : A) :
  @IntoInternalEq PROP _ A (x ≡ y) x y.
Proof. by rewrite /IntoInternalEq. Qed.
Global Instance into_internal_eq_affinely {A : ofe} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (<affine> P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite affinely_elim. Qed.
Global Instance into_internal_eq_intuitionistically {A : ofe} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (□ P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite intuitionistically_elim. Qed.
Global Instance into_internal_eq_absorbingly {A : ofe} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (<absorb> P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite absorbingly_internal_eq. Qed.
Global Instance into_internal_eq_plainly `{!BiPlainly PROP} {A : ofe} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (■ P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite plainly_elim. Qed.
Global Instance into_internal_eq_persistently {A : ofe} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (<pers> P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite persistently_elim. Qed.
End class_instances_internal_eq.
