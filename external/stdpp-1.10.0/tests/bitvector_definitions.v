From stdpp Require Import strings.
From stdpp.bitvector Require Import definitions.

Check "notation_test".
Check (BV 10 3 = BV 10 5).
Fail Check (BV 2 3 = BV 10 5).
Check (BV 2 3 =@{bvn} BV 10 5).
Check (4%bv = BV 4 4).
Check ((-1)%bv = Z_to_bv 7 (-1)).
Goal (-1 =@{bv 5} 31)%bv. compute_done. Qed.

Check "bvn_to_bv_test".
Goal bvn_to_bv 2 (BV 2 3) = Some (BV 2 3). Proof. simpl. Show. done. Abort.
