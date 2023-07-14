From stdpp Require prelude strings list.

(** Check that we always get the [length] function on lists, not on strings. *)
Module test1.
  Import stdpp.base.
  Check length.
  Import stdpp.strings.
  Check length.
  Import stdpp.base.
  Check length.
End test1.

Module test2.
  Import stdpp.prelude.
  Check length.
  Import stdpp.strings.
  Check length.
  Import stdpp.prelude.
  Check length.
End test2.

Module test3.
  Import stdpp.strings.
  Check length.
  Import stdpp.prelude.
  Check length.
End test3.

Module test4.
  Import stdpp.list.
  Check length.
  Import stdpp.strings.
  Check length.
  Import stdpp.list.
  Check length.
End test4.
