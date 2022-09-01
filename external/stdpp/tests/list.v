From stdpp Require Import list.

Lemma last_simpl_test_nil : last [] =@{option nat} None.
Proof. simpl. Show. done. Qed.

Lemma last_simpl_test_singleton : last [10] = Some 10.
Proof. simpl. Show. done. Qed.

Lemma last_simpl_test_double : last [10; 11] = Some 11.
Proof. simpl. Show. done. Qed.

Lemma last_simpl_test_cons_cons l : last (10 :: 11 :: l) = last (11 :: l).
Proof. simpl. Show. done. Qed.

(* The following should not [simpl] and result in a [match]. *)
Lemma last_simpl_test_cons l : last (10 :: l) = last (10 :: l).
Proof. simpl. Show. done. Qed.
