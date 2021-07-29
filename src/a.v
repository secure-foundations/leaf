Require Import Arith.

Lemma stuff (n: nat) (l: list nat)
  : length l = n -> l = l.
Proof.
  induction n as [n IHn] using lt_wf_ind.
