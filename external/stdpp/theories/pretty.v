From stdpp Require Export strings.
From stdpp Require Import relations numbers.
From Coq Require Import Ascii.
From stdpp Require Import options.

Class Pretty A := pretty : A → string.
Global Hint Mode Pretty ! : typeclass_instances.

Definition pretty_N_char (x : N) : ascii :=
  match x with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end%char%N.
Lemma pretty_N_char_inj x y :
  (x < 10)%N → (y < 10)%N → pretty_N_char x = pretty_N_char y → x = y.
Proof. compute; intros. by repeat (discriminate || case_match). Qed.

Fixpoint pretty_N_go_help (x : N) (acc : Acc (<)%N x) (s : string) : string :=
  match decide (0 < x)%N with
  | left H => pretty_N_go_help (x `div` 10)%N
     (Acc_inv acc (N.div_lt x 10 H eq_refl))
     (String (pretty_N_char (x `mod` 10)) s)
  | right _ => s
  end.
(** The argument [S (N.size_nat x)] of [wf_guard] makes sure that computation
works if [x] is a closed term, but that it blocks if [x] is an open term. The
latter prevents unexpected stack overflows, see [tests/pretty.v]. *)
Definition pretty_N_go (x : N) : string → string :=
  pretty_N_go_help x (wf_guard (S (N.size_nat x)) N.lt_wf_0 x).
Global Instance pretty_N : Pretty N := λ x,
  if decide (x = 0)%N then "0" else pretty_N_go x "".

Lemma pretty_N_go_0 s : pretty_N_go 0 s = s.
Proof. done. Qed.
Lemma pretty_N_go_help_irrel x acc1 acc2 s :
  pretty_N_go_help x acc1 s = pretty_N_go_help x acc2 s.
Proof.
  revert x acc1 acc2 s; fix FIX 2; intros x [acc1] [acc2] s; simpl.
  destruct (decide (0 < x)%N); auto.
Qed.
Lemma pretty_N_go_step x s :
  (0 < x)%N → pretty_N_go x s
  = pretty_N_go (x `div` 10) (String (pretty_N_char (x `mod` 10)) s).
Proof.
  unfold pretty_N_go; intros; destruct (wf_guard 32 N.lt_wf_0 x).
  destruct (wf_guard _ _). (* this makes coqchk happy. *)
  unfold pretty_N_go_help at 1; fold pretty_N_go_help.
  by destruct (decide (0 < x)%N); auto using pretty_N_go_help_irrel.
Qed.

(** Helper lemma to prove [pretty_N_inj] and [pretty_Z_inj]. *)
Lemma pretty_N_go_ne_0 x s : s ≠ "0" → pretty_N_go x s ≠ "0".
Proof.
  revert s. induction (N.lt_wf_0 x) as [x _ IH]; intros s ?.
  assert (x = 0 ∨ 0 < x < 10 ∨ 10 ≤ x)%N as [->|[[??]|?]] by lia.
  - by rewrite pretty_N_go_0.
  - rewrite pretty_N_go_step by done. apply IH.
    { by apply N.div_lt. }
    assert (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6
          ∨ x = 7 ∨ x = 8 ∨ x = 9)%N by lia; naive_solver.
  - rewrite 2!pretty_N_go_step by (try apply N.div_str_pos_iff; lia).
    apply IH; [|done].
    trans (x `div` 10)%N; apply N.div_lt; auto using N.div_str_pos with lia.
Qed.
(** Helper lemma to prove [pretty_Z_inj]. *)
Lemma pretty_N_go_ne_dash x s s' : s ≠ "-" +:+ s' → pretty_N_go x s ≠ "-" +:+ s'.
Proof.
  revert s. induction (N.lt_wf_0 x) as [x _ IH]; intros s ?.
  assert (x = 0 ∨ 0 < x)%N as [->|?] by lia.
  - by rewrite pretty_N_go_0.
  - rewrite pretty_N_go_step by done. apply IH.
    { by apply N.div_lt. }
    unfold pretty_N_char. by repeat case_match.
Qed.

Global Instance pretty_N_inj : Inj (=@{N}) (=) pretty.
Proof.
  cut (∀ x y s s', pretty_N_go x s = pretty_N_go y s' →
    String.length s = String.length s' → x = y ∧ s = s').
  { intros help x y. unfold pretty, pretty_N. intros.
    repeat case_decide; simplify_eq/=; [done|..].
    - by destruct (pretty_N_go_ne_0 y "").
    - by destruct (pretty_N_go_ne_0 x "").
    - by apply (help x y "" ""). }
  assert (∀ x s, ¬String.length (pretty_N_go x s) < String.length s) as help.
  { setoid_rewrite <-Nat.le_ngt.
    intros x; induction (N.lt_wf_0 x) as [x _ IH]; intros s.
    assert (x = 0 ∨ 0 < x)%N as [->|?] by lia; [by rewrite pretty_N_go_0|].
    rewrite pretty_N_go_step by done.
    etrans; [|by eapply IH, N.div_lt]; simpl; lia. }
  intros x; induction (N.lt_wf_0 x) as [x _ IH]; intros y s s'.
  assert ((x = 0 ∨ 0 < x) ∧ (y = 0 ∨ 0 < y))%N as [[->|?] [->|?]] by lia;
    rewrite ?pretty_N_go_0, ?pretty_N_go_step, ?(pretty_N_go_step y) by done.
  { done. }
  { intros -> Hlen. edestruct help; rewrite Hlen; simpl; lia. }
  { intros <- Hlen. edestruct help; rewrite <-Hlen; simpl; lia. }
  intros Hs Hlen.
  apply IH in Hs as [? [= Hchar]];
    [|auto using N.div_lt_upper_bound with lia|simpl; lia].
  split; [|done].
  apply pretty_N_char_inj in Hchar; [|by auto using N.mod_lt..].
  rewrite (N.div_mod x 10), (N.div_mod y 10) by done. lia.
Qed.

Global Instance pretty_nat : Pretty nat := λ x, pretty (N.of_nat x).
Global Instance pretty_nat_inj : Inj (=@{nat}) (=) pretty.
Proof. apply _. Qed.

Global Instance pretty_positive : Pretty positive := λ x, pretty (Npos x).
Global Instance pretty_positive_inj : Inj (=@{positive}) (=) pretty.
Proof. apply _. Qed.

Global Instance pretty_Z : Pretty Z := λ x,
  match x with
  | Z0 => "0" | Zpos x => pretty x | Zneg x => "-" +:+ pretty x
  end%string.
Global Instance pretty_Z_inj : Inj (=@{Z}) (=) pretty.
Proof.
  unfold pretty, pretty_Z.
  intros [|x|x] [|y|y] Hpretty; simplify_eq/=; try done.
  - by destruct (pretty_N_go_ne_0 (N.pos y) "").
  - by destruct (pretty_N_go_ne_0 (N.pos x) "").
  - by edestruct (pretty_N_go_ne_dash (N.pos x) "").
  - by edestruct (pretty_N_go_ne_dash (N.pos y) "").
Qed.
