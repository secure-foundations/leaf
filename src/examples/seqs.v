From iris.base_logic.lib Require Import invariants.
From BurrowLang Require Import lang simp adequacy primitive_laws.
From Tpcms Require Import rwlock.
Require Import Burrow.tpcms.
Require Import Burrow.ra.
Require Import Burrow.rollup.
Require Import Burrow.CpdtTactics.
Require Import Burrow.tactics.

From iris.base_logic Require Export base_logic.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From BurrowLang Require Import notation tactics class_instances.
From BurrowLang Require Import heap_ra.
From BurrowLang Require Import lang.
From iris Require Import options.

(* really crummy sequence library *)

Definition seq_idx : lang.expr :=
  (rec: "seq_idx" "i" "array" :=
      if: (BinOp EqOp "i" #0) then
        Fst "array"
      else
        "seq_idx" ("i" + #(-1)) (Snd "array")
  ).
  
Fixpoint has_elem (v: lang.val) (i: nat) : Prop :=
  match i, v with
  | O, (PairV l _ ) => True
  | S i, (PairV _ r ) => has_elem r i
  | _, _ => False
  end.

Fixpoint elem (v: lang.val) (i: nat) :=
  match i, v with
  | O, (PairV l _ ) => l
  | S i, (PairV _ r ) => elem r i
  | _, _ => #()
  end.
  
Section SeqProof.

Context `{!simpGS 𝜇 Σ}.

Lemma wp_seq_idx (seq: lang.val) (i: nat)
  (he: has_elem seq i) :
      {{{ True }}}
      seq_idx #i seq
      {{{ RET (elem seq i); True }}}.
Proof.
  iIntros (P) "_ P". unfold seq_idx. wp_pures.
  generalize he. generalize i. clear he. clear i. induction seq; intros i he.
    - cbn [has_elem] in he. destruct i; contradiction.
    - cbn [has_elem] in he. destruct i; contradiction.
    - cbn [has_elem] in he. destruct i.
      + wp_pures. unfold elem.
        iModIntro. iApply "P". trivial.
      + wp_pures.
        replace ((Z.add (S i) (Zneg xH))) with (i : Z) by lia.
        cbn [elem].
        apply IHseq2; trivial.
Qed.

End SeqProof.
