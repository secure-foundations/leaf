From stdpp Require Import nat_cancel.
From iris.bi Require Import bi.
From iris.proofmode Require Import modality_instances classes.
From iris.prelude Require Import options.
Import bi.

Section class_instances_internal_eq.
Context `{!BiInternalEq PROP}.
Implicit Types P Q R : PROP.

Global Instance from_pure_internal_eq {A : ofe} (a b : A) :
  @FromPure PROP false (a ≡ b) (a ≡ b).
Proof. by rewrite /FromPure pure_internal_eq. Qed.

Global Instance into_pure_eq {A : ofe} (a b : A) :
  Discrete a → @IntoPure PROP (a ≡ b) (a ≡ b).
Proof. intros. by rewrite /IntoPure discrete_eq. Qed.

Global Instance from_modal_Next {A : ofe} (x y : A) :
  FromModal (PROP1:=PROP) (PROP2:=PROP) True (modality_laterN 1)
    (▷^1 (x ≡ y) : PROP)%I (Next x ≡ Next y) (x ≡ y).
Proof. by rewrite /FromModal /= later_equivI. Qed.

Global Instance into_laterN_Next {A : ofe} only_head n n' (x y : A) :
  NatCancel n 1 n' 0 →
  IntoLaterN (PROP:=PROP) only_head n (Next x ≡ Next y) (x ≡ y) | 2.
Proof.
  rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel Nat.add_0_r.
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
Global Instance into_internal_eq_plainly `{BiPlainly PROP} {A : ofe} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (■ P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite plainly_elim. Qed.
Global Instance into_internal_eq_persistently {A : ofe} (x y : A) P :
  IntoInternalEq P x y → IntoInternalEq (<pers> P) x y.
Proof. rewrite /IntoInternalEq=> ->. by rewrite persistently_elim. Qed.
End class_instances_internal_eq.
