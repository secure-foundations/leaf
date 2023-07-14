From stdpp Require base numbers prelude.

(** Check that we always get the [le] and [lt] functions on [nat]. *)
Module test1.
  Import stdpp.base.
  Check le.
  Check lt.
End test1.

Module test2.
  Import stdpp.prelude.
  Check le.
  Check lt.
End test2.

Module test3.
  Import stdpp.numbers.
  Check le.
  Check lt.
End test3.

Module test4.
  Import stdpp.list.
  Check le.
  Check lt.
End test4.
