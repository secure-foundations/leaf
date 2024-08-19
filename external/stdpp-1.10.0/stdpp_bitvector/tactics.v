(** This file is maintained by Michael Sammler. *)
From stdpp.bitvector Require Export definitions.
From stdpp Require Import options.

(** * bitvector tactics *)
(** This file provides tactics for the bitvector library in
[bitvector.v]. In particular, it provides integration of bitvectors
with the [bitblast] tactic and tactics for simplifying and solving
bitvector expressions. The main tactic provided by this library is
[bv_simplify] which performs the following steps:

1. Simplify the goal by rewriting with the [bv_simplify] database.
2. If the goal is an (in)equality (= or ≠) between bitvectors, turn it into
an (in)equality between their unsigned values. (Using unsigned values here
rather than signed is somewhat arbitrary but works well enough in practice.)
3. Unfold [bv_unsigned] and [bv_signed] of operations on [bv n] to
operations on [Z].
4. Simplify the goal by rewriting with the [bv_unfolded_simplify]
database.

This file provides the following variants of the [bv_simplify] tactic:
- [bv_simplify] applies the simplification procedure to the goal.
- [bv_simplify H] applies the simplification procedure to the hypothesis [H].
- [bv_simplify select pat] applies the simplification procedure to the hypothesis
  matching [pat].

- [bv_simplify_arith] applies the simplification procedure to the goal and
  additionally rewrites with the [bv_unfolded_to_arith] database to turn the goal
  into a more suitable shape for calling [lia].
- [bv_simplify_arith H] same as [bv_simplify_arith], but in the hypothesis [H].
- [bv_simplify_arith select pat] same as [bv_simplify_arith], but in the
  hypothesis matching [pat].

- [bv_solve] simplifies the goal using [bv_simplify_arith], learns bounds facts
  about bitvector variables in the context and tries to solve the goal using [lia].

This automation assumes that [lia] can handle [`mod`] and [`div`] as can be enabled
via the one of the following flags:
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
or
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
or
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
See https://coq.github.io/doc/master/refman/addendum/micromega.html#coq:tacn.zify
for details.
*)

(** * Settings *)
Local Open Scope Z_scope.

(** * General tactics *)
Ltac unfold_lets_in_context :=
  repeat match goal with
         | H := _ |- _ => unfold H in *; clear H
         end.

Tactic Notation "reduce_closed" constr(x) :=
  is_closed_term x;
  let r := eval vm_compute in x in
  change_no_check x with r in *
.

(** * General lemmas *)
Lemma bv_extract_concat_later m n1 n2 s l (b1 : bv n1) (b2 : bv n2):
  (n2 ≤ s)%N →
  (m = n1 + n2)%N →
  bv_extract s l (bv_concat m b1 b2) = bv_extract (s - n2) l b1.
Proof.
  intros ? ->. apply bv_eq.
  rewrite !bv_extract_unsigned, bv_concat_unsigned, !bv_wrap_land by done.
  apply Z.bits_inj_iff' => ??.
  rewrite !Z.land_spec, !Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec, Z.ones_spec; [|lia..].
  case_bool_decide; rewrite ?andb_false_r, ?andb_true_r; [|done].
  rewrite <-(bv_wrap_bv_unsigned _ b2), bv_wrap_spec_high, ?orb_false_r; [|lia].
  f_equal. lia.
Qed.
Lemma bv_extract_concat_here m n1 n2 s (b1 : bv n1) (b2 : bv n2):
  s = 0%N →
  (m = n1 + n2)%N →
  bv_extract s n2 (bv_concat m b1 b2) = b2.
Proof.
  intros -> ->. apply bv_eq.
  rewrite !bv_extract_unsigned, bv_concat_unsigned, !bv_wrap_land by done.
  apply Z.bits_inj_iff' => ??.
  rewrite !Z.land_spec, !Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec, Z.ones_spec; [|lia..].
  case_bool_decide; rewrite ?andb_false_r, ?andb_true_r.
  - rewrite (Z.testbit_neg_r (bv_unsigned b1)); [|lia]. simpl. f_equal. lia.
  - rewrite <-(bv_wrap_bv_unsigned _ b2), bv_wrap_spec_high, ?orb_false_l; lia.
Qed.

(** * [bv_simplify] rewrite database *)
(** The [bv_simplify] database collects rewrite rules that rewrite
bitvectors into other bitvectors. *)
Create HintDb bv_simplify discriminated. (* Technically not necessary for rewrite db. *)
Global Hint Rewrite @bv_concat_0 using done : bv_simplify.
Global Hint Rewrite @bv_extract_concat_later
  @bv_extract_concat_here using lia : bv_simplify.
Global Hint Rewrite @bv_extract_bool_to_bv using lia : bv_simplify.
Global Hint Rewrite @bv_not_bool_to_bv : bv_simplify.
Global Hint Rewrite bool_decide_bool_to_bv_0 bool_decide_bool_to_bv_1 : bv_simplify.

(** * [bv_unfold] *)
Create HintDb bv_unfold_db discriminated.
Global Hint Constants Opaque : bv_unfold_db.
Global Hint Variables Opaque : bv_unfold_db.
Global Hint Extern 1 (TCFastDone ?P) => (change P; fast_done) : bv_unfold_db.
Global Hint Transparent BvWf andb Is_true Z.ltb Z.leb Z.compare Pos.compare
  Pos.compare_cont bv_modulus Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.of_N
  : bv_unfold_db.

Notation bv_suwrap signed := (if signed then bv_swrap else bv_wrap).

Class BvUnfold (n : N) (signed : bool) (wrapped : bool) (b : bv n) (z : Z) := {
    bv_unfold_proof : ((if signed then bv_signed else bv_unsigned) b) =
                        (if wrapped then bv_suwrap signed n z else z);
}.
Global Arguments bv_unfold_proof {_ _ _} _ _ {_}.
Global Hint Mode BvUnfold + + + + - : bv_unfold_db.

(** [BV_UNFOLD_BLOCK] is a marker that this occurence of [bv_signed]
or [bv_unsigned] has already been simplified. *)
Definition BV_UNFOLD_BLOCK {A} (x : A) : A := x.

Lemma bv_unfold_end s w n b :
  BvUnfold n s w b ((if s then BV_UNFOLD_BLOCK bv_signed else BV_UNFOLD_BLOCK bv_unsigned) b).
Proof.
  constructor. unfold BV_UNFOLD_BLOCK.
  destruct w, s; by rewrite ?bv_wrap_bv_unsigned, ?bv_swrap_bv_signed.
Qed.
Global Hint Resolve bv_unfold_end | 1000 : bv_unfold_db.
Lemma bv_unfold_BV s w n z Hwf :
  BvUnfold n s w (@BV _ z Hwf) (if w then z else if s then bv_swrap n z else z).
Proof.
  constructor. unfold bv_unsigned.
  destruct w, s; simpl; try done; by rewrite bv_wrap_small by by apply bv_wf_in_range.
Qed.
Global Hint Resolve bv_unfold_BV | 10 : bv_unfold_db.
Lemma bv_unfold_bv_0 s w n :
  BvUnfold n s w (bv_0 n) 0.
Proof. constructor. destruct w, s; rewrite ?bv_0_signed, ?bv_0_unsigned, ?bv_swrap_0; done. Qed.
Global Hint Resolve bv_unfold_bv_0 | 10 : bv_unfold_db.
Lemma bv_unfold_Z_to_bv s w n z :
  BvUnfold n s w (Z_to_bv _ z) (if w then z else bv_suwrap s n z).
Proof. constructor. destruct w, s; rewrite ?Z_to_bv_signed, ?Z_to_bv_unsigned; done. Qed.
Global Hint Resolve bv_unfold_Z_to_bv | 10 : bv_unfold_db.
Lemma bv_unfold_succ s w n b z :
  BvUnfold n s true b z →
  BvUnfold n s w (bv_succ b) (if w then Z.succ z else bv_suwrap s n (Z.succ z)).
Proof.
  intros [Hz]. constructor.
  destruct w, s; rewrite ?bv_succ_signed, ?bv_succ_unsigned, ?Hz; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_succ | 10 : bv_unfold_db.
Lemma bv_unfold_pred s w n b z :
  BvUnfold n s true b z →
  BvUnfold n s w (bv_pred b) (if w then Z.pred z else bv_suwrap s n (Z.pred z)).
Proof.
  intros [Hz]. constructor.
  destruct w, s; rewrite ?bv_pred_signed, ?bv_pred_unsigned, ?Hz; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_pred | 10 : bv_unfold_db.
Lemma bv_unfold_add s w n b1 b2 z1 z2 :
  BvUnfold n s true b1 z1 →
  BvUnfold n s true b2 z2 →
  BvUnfold n s w (bv_add b1 b2) (if w then z1 + z2 else bv_suwrap s n (z1 + z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_add_signed, ?bv_add_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_add | 10 : bv_unfold_db.
Lemma bv_unfold_sub s w n b1 b2 z1 z2 :
  BvUnfold n s true b1 z1 →
  BvUnfold n s true b2 z2 →
  BvUnfold n s w (bv_sub b1 b2) (if w then z1 - z2 else bv_suwrap s n (z1 - z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_sub_signed, ?bv_sub_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_sub | 10 : bv_unfold_db.
Lemma bv_unfold_opp s w n b z :
  BvUnfold n s true b z →
  BvUnfold n s w (bv_opp b) (if w then - z else bv_suwrap s n (- z)).
Proof.
  intros [Hz]. constructor.
  destruct w, s; rewrite ?bv_opp_signed, ?bv_opp_unsigned, ?Hz; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_opp | 10 : bv_unfold_db.
Lemma bv_unfold_mul s w n b1 b2 z1 z2 :
  BvUnfold n s true b1 z1 →
  BvUnfold n s true b2 z2 →
  BvUnfold n s w (bv_mul b1 b2) (if w then z1 * z2 else bv_suwrap s n (z1 * z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_mul_signed, ?bv_mul_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_mul | 10 : bv_unfold_db.
Lemma bv_unfold_divu s w n b1 b2 z1 z2 :
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_divu b1 b2) (if w then z1 `div` z2 else if s then bv_swrap n (z1 `div` z2) else z1 `div` z2).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_divu_signed, ?bv_divu_unsigned, ?Hz1, ?Hz2; try bv_wrap_simplify_solve.
  - pose proof (bv_unsigned_in_range _ (bv_divu b1 b2)) as Hr. rewrite bv_divu_unsigned in Hr. subst.
    by rewrite bv_wrap_small.
  - done.
Qed.
Global Hint Resolve bv_unfold_divu | 10 : bv_unfold_db.
Lemma bv_unfold_modu s w n b1 b2 z1 z2 :
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_modu b1 b2) (if w then z1 `mod` z2 else if s then bv_swrap n (z1 `mod` z2) else z1 `mod` z2).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_modu_signed, ?bv_modu_unsigned, ?Hz1, ?Hz2; try bv_wrap_simplify_solve.
  - pose proof (bv_unsigned_in_range _ (bv_modu b1 b2)) as Hr. rewrite bv_modu_unsigned in Hr. subst.
    by rewrite bv_wrap_small.
  - done.
Qed.
Global Hint Resolve bv_unfold_modu | 10 : bv_unfold_db.
Lemma bv_unfold_divs s w n b1 b2 z1 z2 :
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_divs b1 b2) (if w then z1 `div` z2 else bv_suwrap s n (z1 `div` z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_divs_signed, ?bv_divs_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_divs | 10 : bv_unfold_db.
Lemma bv_unfold_quots s w n b1 b2 z1 z2 :
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_quots b1 b2) (if w then z1 `quot` z2 else bv_suwrap s n (z1 `quot` z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_quots_signed, ?bv_quots_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_quots | 10 : bv_unfold_db.
Lemma bv_unfold_mods s w n b1 b2 z1 z2 :
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_mods b1 b2) (if w then z1 `mod` z2 else bv_suwrap s n (z1 `mod` z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_mods_signed, ?bv_mods_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_mods | 10 : bv_unfold_db.
Lemma bv_unfold_rems s w n b1 b2 z1 z2 :
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_rems b1 b2) (if w then z1 `rem` z2 else bv_suwrap s n (z1 `rem` z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_rems_signed, ?bv_rems_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_rems | 10 : bv_unfold_db.
Lemma bv_unfold_shiftl s w n b1 b2 z1 z2 :
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_shiftl b1 b2) (if w then z1 ≪ z2 else bv_suwrap s n (z1 ≪ z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_shiftl_signed, ?bv_shiftl_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_shiftl | 10 : bv_unfold_db.
Lemma bv_unfold_shiftr s w n b1 b2 z1 z2 :
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_shiftr b1 b2) (if w then z1 ≫ z2 else if s then bv_swrap n (z1 ≫ z2) else (z1 ≫ z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_shiftr_signed, ?bv_shiftr_unsigned, ?Hz1, ?Hz2; try bv_wrap_simplify_solve.
  - pose proof (bv_unsigned_in_range _ (bv_shiftr b1 b2)) as Hr. rewrite bv_shiftr_unsigned in Hr. subst.
    by rewrite bv_wrap_small.
  - done.
Qed.
Global Hint Resolve bv_unfold_shiftr | 10 : bv_unfold_db.
Lemma bv_unfold_ashiftr s w n b1 b2 z1 z2 :
  BvUnfold n true false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_ashiftr b1 b2) (if w then z1 ≫ z2 else bv_suwrap s n (z1 ≫ z2)).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_ashiftr_signed, ?bv_ashiftr_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_ashiftr | 10 : bv_unfold_db.
Lemma bv_unfold_or s w n b1 b2 z1 z2 :
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_or b1 b2) (if w then Z.lor z1 z2 else if s then bv_swrap n (Z.lor z1 z2) else Z.lor z1 z2).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_or_signed, ?bv_or_unsigned, ?Hz1, ?Hz2; try bv_wrap_simplify_solve.
  - pose proof (bv_unsigned_in_range _ (bv_or b1 b2)) as Hr. rewrite bv_or_unsigned in Hr. subst.
    by rewrite bv_wrap_small.
  - done.
Qed.
Global Hint Resolve bv_unfold_or | 10 : bv_unfold_db.
Lemma bv_unfold_and s w n b1 b2 z1 z2 :
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_and b1 b2) (if w then Z.land z1 z2 else if s then bv_swrap n (Z.land z1 z2) else Z.land z1 z2).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_and_signed, ?bv_and_unsigned, ?Hz1, ?Hz2; try bv_wrap_simplify_solve.
  - pose proof (bv_unsigned_in_range _ (bv_and b1 b2)) as Hr. rewrite bv_and_unsigned in Hr. subst.
    by rewrite bv_wrap_small.
  - done.
Qed.
Global Hint Resolve bv_unfold_and | 10 : bv_unfold_db.
Lemma bv_unfold_xor s w n b1 b2 z1 z2 :
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_xor b1 b2) (if w then Z.lxor z1 z2 else if s then bv_swrap n (Z.lxor z1 z2) else Z.lxor z1 z2).
Proof.
  intros [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_xor_signed, ?bv_xor_unsigned, ?Hz1, ?Hz2; try bv_wrap_simplify_solve.
  - pose proof (bv_unsigned_in_range _ (bv_xor b1 b2)) as Hr. rewrite bv_xor_unsigned in Hr. subst.
    by rewrite bv_wrap_small.
  - done.
Qed.
Global Hint Resolve bv_unfold_xor | 10 : bv_unfold_db.
Lemma bv_unfold_not s w n b z :
  BvUnfold n false false b z →
  BvUnfold n s w (bv_not b) (if w then Z.lnot z else bv_suwrap s n (Z.lnot z)).
Proof.
  intros [Hz]. constructor.
  destruct w, s; rewrite ?bv_not_signed, ?bv_not_unsigned, ?Hz; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_not | 10 : bv_unfold_db.
Lemma bv_unfold_zero_extend s w n n' b z `{!TCFastDone (n' <=? n = true)%N} :
  BvUnfold n' false false b z →
  BvUnfold n s w (bv_zero_extend n b) (if w then z else if s then bv_swrap n z else z).
Proof.
  intros [Hz]. constructor. unfold TCFastDone in *. rewrite ->?N.leb_le in *.
  destruct w, s; rewrite ?bv_zero_extend_signed, ?bv_zero_extend_unsigned, ?Hz by done;
    try bv_wrap_simplify_solve.
  - rewrite <-Hz, bv_wrap_small; [done|]. bv_saturate. pose proof (bv_modulus_le_mono n' n). lia.
  - done.
Qed.
Global Hint Resolve bv_unfold_zero_extend | 10 : bv_unfold_db.
Lemma bv_unfold_sign_extend s w n n' b z `{!TCFastDone (n' <=? n = true)%N} :
  BvUnfold n' true false b z →
  BvUnfold n s w (bv_sign_extend n b) (if w then z else if s then z else bv_wrap n z).
Proof.
  intros [Hz]. constructor. unfold TCFastDone in *. rewrite ->?N.leb_le in *.
  destruct w, s; rewrite ?bv_sign_extend_signed, ?bv_sign_extend_unsigned, ?Hz by done;
    try bv_wrap_simplify_solve.
  - subst. rewrite <-(bv_sign_extend_signed n) at 2 by done. by rewrite bv_swrap_bv_signed, bv_sign_extend_signed.
  - done.
Qed.
Global Hint Resolve bv_unfold_sign_extend | 10 : bv_unfold_db.
Lemma bv_unfold_extract s w n n' n1 b z :
  BvUnfold n' false false b z →
  BvUnfold n s w (bv_extract n1 n b) (if w then z ≫ Z.of_N n1 else bv_suwrap s n (z ≫ Z.of_N n1)).
Proof.
  intros [Hz]. constructor.
  destruct w, s; rewrite ?bv_extract_signed, ?bv_extract_unsigned, ?Hz; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_extract | 10 : bv_unfold_db.
Lemma bv_unfold_concat s w n n1 n2 b1 b2 z1 z2 `{!TCFastDone (n = n1 + n2)%N} :
  BvUnfold n1 false false b1 z1 →
  BvUnfold n2 false false b2 z2 →
  BvUnfold n s w (bv_concat n b1 b2) (if w then Z.lor (z1 ≪ Z.of_N n2) z2 else if s then  bv_swrap n (Z.lor (z1 ≪ Z.of_N n2) z2) else Z.lor (z1 ≪ Z.of_N n2) z2).
Proof.
  intros [Hz1] [Hz2]. constructor. unfold TCFastDone in *.
  destruct w, s; rewrite ?bv_concat_signed, ?bv_concat_unsigned, ?Hz1, ?Hz2 by done;
    try bv_wrap_simplify_solve.
  - subst. rewrite <-(bv_concat_unsigned (n1 + n2)) at 2 by done.
    by rewrite bv_wrap_bv_unsigned, bv_concat_unsigned.
  - done.
Qed.
Global Hint Resolve bv_unfold_concat | 10 : bv_unfold_db.
Lemma bv_unfold_add_Z s w n b1 z1 z2 :
  BvUnfold n s true b1 z1 →
  BvUnfold n s w (bv_add_Z b1 z2) (if w then z1 + z2 else bv_suwrap s n (z1 + z2)).
Proof.
  intros [Hz1]. constructor.
  destruct w, s; rewrite ?bv_add_Z_signed, ?bv_add_Z_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_add_Z | 10 : bv_unfold_db.
Lemma bv_unfold_sub_Z s w n b1 z1 z2 :
  BvUnfold n s true b1 z1 →
  BvUnfold n s w (bv_sub_Z b1 z2) (if w then z1 - z2 else bv_suwrap s n (z1 - z2)).
Proof.
  intros [Hz1]. constructor.
  destruct w, s; rewrite ?bv_sub_Z_signed, ?bv_sub_Z_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_sub_Z | 10 : bv_unfold_db.
Lemma bv_unfold_mul_Z s w n b1 z1 z2 :
  BvUnfold n s true b1 z1 →
  BvUnfold n s w (bv_mul_Z b1 z2) (if w then z1 * z2 else bv_suwrap s n (z1 * z2)).
Proof.
  intros [Hz1]. constructor.
  destruct w, s; rewrite ?bv_mul_Z_signed, ?bv_mul_Z_unsigned, ?Hz1, ?Hz2; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_mul_Z | 10 : bv_unfold_db.

Ltac bv_unfold_eq :=
  lazymatch goal with
  | |- @bv_unsigned ?n ?b = ?z =>
      simple notypeclasses refine (@bv_unfold_proof n false false b z _)
  | |- @bv_signed ?n ?b = ?z =>
      simple notypeclasses refine (@bv_unfold_proof n true false b z _)
  end;
  typeclasses eauto with bv_unfold_db.
Ltac bv_unfold :=
  repeat (match goal with
            (* TODO: Detect if there is a bv_wrap around the
            bv_unsigned (like after applying bv_eq_wrapped) *)
          | |- context [@bv_unsigned ?n ?b] =>
              pattern (@bv_unsigned n b);
              simple refine (eq_rec_r _ _ _); [shelve| |bv_unfold_eq]; cbn beta
          | |- context [@bv_signed ?n ?b] =>
              pattern (@bv_signed n b);
              simple refine (eq_rec_r _ _ _); [shelve| |bv_unfold_eq]; cbn beta
          end); unfold BV_UNFOLD_BLOCK.

(** * [bv_unfolded_simplify] rewrite database *)
(** The [bv_unfolded_simplify] database collects rewrite rules that
should be used to simplify the goal after Z is bv_unfolded. *)
Create HintDb bv_unfolded_simplify discriminated. (* Technically not necessary for rewrite db. *)
Global Hint Rewrite Z.shiftr_0_r Z.lor_0_r Z.lor_0_l : bv_unfolded_simplify.
Global Hint Rewrite Z.land_ones using lia : bv_unfolded_simplify.
Global Hint Rewrite bv_wrap_bv_wrap using lia : bv_unfolded_simplify.
Global Hint Rewrite
  Z_to_bv_small using unfold bv_modulus; lia : bv_unfolded_simplify.

(** * [bv_unfolded_to_arith] rewrite database *)
(** The [bv_unfolded_to_arith] database collects rewrite rules that
convert bitwise operations to arithmetic operations in preparation for lia. *)
Create HintDb bv_unfolded_to_arith discriminated. (* Technically not necessary for rewrite db. *)
Global Hint Rewrite <-Z.opp_lnot : bv_unfolded_to_arith.
Global Hint Rewrite Z.shiftl_mul_pow2 Z.shiftr_div_pow2 using lia : bv_unfolded_to_arith.

(** * Reduction of closed terms *)
Ltac reduce_closed_N_tac := idtac.
Ltac reduce_closed_N :=
  idtac;
  reduce_closed_N_tac;
  repeat match goal with
  | |- context [N.add ?a ?b] => progress reduce_closed (N.add a b)
  | H : context [N.add ?a ?b] |- _ => progress reduce_closed (N.add a b)
  end.

Ltac reduce_closed_bv_simplify_tac := idtac.
Ltac reduce_closed_bv_simplify :=
  idtac;
  reduce_closed_bv_simplify_tac;
  (* reduce closed logical operators that lia does not understand *)
  repeat match goal with
  | |- context [Z.lor ?a ?b] => progress reduce_closed (Z.lor a b)
  | H : context [Z.lor ?a ?b] |- _ => progress reduce_closed (Z.lor a b)
  | |- context [Z.land ?a ?b] => progress reduce_closed (Z.land a b)
  | H : context [Z.land ?a ?b] |- _ => progress reduce_closed (Z.land a b)
  | |- context [Z.lxor ?a ?b] => progress reduce_closed (Z.lxor a b)
  | H : context [Z.lxor ?a ?b] |- _ => progress reduce_closed (Z.lxor a b)
  end.

(** * [bv_simplify] tactic *)
Tactic Notation "bv_simplify" :=
  unfold_lets_in_context;
  (* We need to reduce operations on N in indices of bv because
  otherwise lia can get confused (it does not perform unification when
  finding identical subterms). This sometimes leads to problems
  with length of lists of bytes. *)
  reduce_closed_N;
  autorewrite with bv_simplify;
  lazymatch goal with
  | |- _ =@{bv _} _ => apply bv_eq_wrap
  | |- not (_ =@{bv _} _) => apply bv_neq_wrap
  | _ => idtac
  end;
  bv_unfold;
  autorewrite with bv_unfolded_simplify.

Tactic Notation "bv_simplify" ident(H) :=
  unfold_lets_in_context;
  autorewrite with bv_simplify in H;
  lazymatch (type of H) with
  | _ =@{bv _} _ => apply bv_eq in H
  | not (_ =@{bv _} _) => apply bv_neq in H
  | _ => idtac
  end;
  do [bv_unfold] in H;
  autorewrite with bv_unfolded_simplify in H.
Tactic Notation "bv_simplify" "select" open_constr(pat) :=
  select pat (fun H => bv_simplify H).

Tactic Notation "bv_simplify_arith" :=
  bv_simplify;
  autorewrite with bv_unfolded_to_arith;
  reduce_closed_bv_simplify.
Tactic Notation "bv_simplify_arith" ident(H) :=
  bv_simplify H;
  autorewrite with bv_unfolded_to_arith in H;
  reduce_closed_bv_simplify.
Tactic Notation "bv_simplify_arith" "select" open_constr(pat) :=
  select pat (fun H => bv_simplify_arith H).

(** * [bv_solve] tactic *)
Ltac bv_solve_unfold_tac := idtac.
Ltac bv_solve :=
  bv_simplify_arith;
  (* we unfold signed so we just need to saturate unsigned *)
  bv_saturate_unsigned;
  bv_solve_unfold_tac;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl;
  lia.

Class BvSolve (P : Prop) : Prop := bv_solve_proof : P.
Global Hint Extern 1 (BvSolve ?P) => (change P; bv_solve) : typeclass_instances.
