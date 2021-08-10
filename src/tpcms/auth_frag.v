Require Import Burrow.rollup.
From stdpp Require Import gmap.

Require Import Burrow.CpdtTactics.
Require Import coq_tricks.Deex.

Inductive AuthFrag (M: Type) :=
  | AF : option (option M) -> M -> AuthFrag M
.
Global Arguments AF {_}%type_scope _ _.

Definition af_valid {M} `{!EqDecision M} `{!TPCM M} a :=
  match a with
  | AF None frag => m_valid frag
  | AF (Some (Some auth)) frag => m_valid auth /\ ∃ c , dot frag c = auth
  | AF (Some None) _ => False
  end.
  
Definition auth_dot {M} (a b : option (option M)) : option (option M) :=
  match a, b with
  | None, None => None
  | Some x, None => Some x
  | None, Some y => Some y
  | Some x, Some y => Some None
  end.
  
Definition af_dot {M} `{!EqDecision M} `{!TPCM M} (a b : AuthFrag M) :=
  match a, b with
  | AF auth_a frag_a, AF auth_b frag_b => AF (auth_dot auth_a auth_b) (dot frag_a frag_b)
  end.

Definition af_mov {M} `{!EqDecision M} `{!TPCM M} (a b : AuthFrag M) :=
  ∀ z , af_valid (af_dot a z) -> af_valid (af_dot b z).
  
Lemma af_dot_comm {M} `{!EqDecision M} `{!TPCM M} (x y : AuthFrag M)
  : (af_dot x y) = (af_dot y x).
Proof. unfold af_dot. destruct x, y.
    rewrite tpcm_comm. f_equal.
    unfold auth_dot. destruct o, o0; trivial.
Qed.
  
Lemma af_dot_assoc {M} `{!EqDecision M} `{!TPCM M} (x y z : AuthFrag M)
  : af_dot x (af_dot y z) = af_dot (af_dot x y) z.
Proof. unfold af_dot. destruct x, y, z.
    rewrite tpcm_assoc. f_equal.
    unfold auth_dot. destruct o, o0, o1; trivial.
Qed.

Global Instance af_eqdec M `{!EqDecision M} : EqDecision (AuthFrag M).
Proof. solve_decision. Qed.

#[refine]
Global Instance af_tpcm M `{!EqDecision M} `{!TPCM M} : TPCM (AuthFrag M) := {
  m_valid p := af_valid p ;
  dot a b := af_dot a b ;
  mov a b := af_mov a b ;
  unit := AF None unit ;
}.
 - intros. unfold af_valid, af_dot in *. destruct x, y. unfold auth_dot in *.
    destruct o, o0; intuition.
    + destruct o; intuition. deex. exists (dot m0 c). rewrite tpcm_assoc. trivial.
    + destruct o; intuition. deex. subst m1. rewrite <- tpcm_assoc in H0.
        apply valid_monotonic with (y := dot m0 c). trivial.
    + apply valid_monotonic with (y := m0). trivial.
 - unfold af_valid. apply unit_valid.
 - intros. unfold af_dot. destruct x. rewrite unit_dot.
    unfold auth_dot. destruct o; trivial.
 - apply af_dot_comm.
 - apply af_dot_assoc.
 - intros. unfold af_mov. intro. trivial.
 - intros. unfold af_mov in *. intros. apply H0. apply H. trivial.
 - intros. split.
  * unfold af_mov in H. apply H. apply H0.
  * unfold af_mov in H. unfold af_mov. intro.
      rewrite <- af_dot_assoc.
      rewrite <- af_dot_assoc.
      apply H.
Defined.

Definition auth {M} `{!EqDecision M} `{!TPCM M} (m: M) :=
    AF (Some (Some m)) unit.
    
Definition frag {M} `{!EqDecision M} `{!TPCM M} (m: M) :=
    AF None m.
