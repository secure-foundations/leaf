module RWLock {
  /* Assume a type of object to be stored */

  type X

  /* Auxilliary defs */

  datatype Exc<T> = ExcEmpty | ExcOne(t: T) | ExcFail

  function exc_unit<T>(): Exc<T> {
      ExcEmpty
  }

  function exc_dot<T>(x: Exc<T>, y: Exc<T>): Exc<T> {
      if x == ExcEmpty then y
      else if y == ExcEmpty then x
      else ExcFail
  } 

  predicate exc_valid<T>(x: Exc<T>) {
      x != ExcFail
  }

  type positive_nat = n: nat | n >= 1 witness 1
  datatype Agn<T> = Zero | Have(t: T, n: positive_nat) | AgnFail

  function agn_unit<T>(): Agn<T> {
      Zero
  }

  function agn_dot<T>(x: Agn<T>, y: Agn<T>): Agn<T> {
      match x {
          case Zero => y
          case Have(tx, nx) => match y {
              case Zero => x
              case Have(ty, ny) => if tx == ty then Have(tx, nx + ny) else AgnFail
              case AgnFail => AgnFail
          }
          case AgnFail => AgnFail
      }
  }

  predicate agn_valid<T>(x: Agn<T>) {
      x != AgnFail
  }

  /* The Base monoid */

  type B = Exc<X>

  function base_unit() : B {
      exc_unit()
  }

  function base_dot(x: B, y: B) : B {
      exc_dot(x, y)
  }

  predicate base_V(x: B) {
      exc_valid(x)
  }

  lemma base_commutative(a: B, b: B)
  ensures base_dot(a, b) == base_dot(b, a)
  {
  }

  lemma base_associative(a: B, b: B, c: B)
  ensures base_dot(a, base_dot(b, c)) == base_dot(base_dot(a, b), c)
  {
  }

  lemma base_dot_unit(a: B)
  ensures base_dot(a, base_unit()) == a
  {
  }

  lemma base_valid_monotonic(a: B, b: B)
  requires base_V(base_dot(a, b))
  ensures base_V(a)
  {
  }

  lemma base_valid_unit()
  ensures base_V(base_unit())
  {
  }

  /* Define the RwLock storage protocol */

  datatype FieldsState = FieldsState(
    exc: bool,
    rc: int,
    x: X
  )

  datatype F = F(
    fields: Exc<FieldsState>,
    exc_pending: Exc<()>,
    exc_taken: Exc<()>,
    shared_pending_handles: nat,
    shared_taken_handles: Agn<X>
  )

  function unit() : F
  {
    F(exc_unit(), exc_unit(), exc_unit(), 0, agn_unit())
  }

  function dot(a: F, b: F) : F
  {
    F(
        exc_dot(a.fields, b.fields),
        exc_dot(a.exc_pending, b.exc_pending),
        exc_dot(a.exc_taken, b.exc_taken),
        a.shared_pending_handles + b.shared_pending_handles,
        agn_dot(a.shared_taken_handles, b.shared_taken_handles)
    )
  }

  /* Validity predicate */

  function agn_count<T>(x: Agn<T>): nat {
      if x.Have? then x.n else 0
  }

  predicate Inv(f: F) {
    && exc_valid(f.fields)
    && exc_valid(f.exc_pending)
    && exc_valid(f.exc_taken)
    && agn_valid(f.shared_taken_handles)

    && f.fields.ExcOne?
    && f.fields.t.rc == f.shared_pending_handles + agn_count(f.shared_taken_handles)
    && (!f.fields.t.exc ==> !f.exc_pending.ExcOne? && !f.exc_taken.ExcOne?)
    && (f.fields.t.exc ==> (f.exc_pending.ExcOne? || f.exc_taken.ExcOne?)
                       && !(f.exc_pending.ExcOne? && f.exc_taken.ExcOne?))
    && (f.exc_taken.ExcOne? ==> f.shared_taken_handles == Zero)
    && (f.shared_taken_handles.Have? ==> f.shared_taken_handles.t == f.fields.t.x)
  }

  /* Storage function */

  function Storage(f: F) : B
  requires Inv(f)
  {
    if f.exc_taken.ExcOne? then
        ExcEmpty
    else
        ExcOne(f.fields.t.x)
  }

  /* PCM properties */

  lemma commutative(x: F, y: F)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x, y).F? {
      assert dot(x, y).fields == dot(y, x).fields;
      assert dot(x, y).exc_pending == dot(y, x).exc_pending;
      assert dot(x, y).exc_taken == dot(y, x).exc_taken;
      assert dot(x, y).shared_pending_handles == dot(y, x).shared_pending_handles;
      assert dot(x, y).shared_taken_handles == dot(y, x).shared_taken_handles;
    }
  }

  lemma associative(x: F, y: F, z: F)
  ensures dot(x, dot(y, z)) == dot(dot(x, y), z)
  {
    if dot(x, dot(y, z)).F? {
      assert dot(x, dot(y, z)).fields == dot(dot(x, y), z).fields;
      assert dot(x, dot(y, z)).exc_pending == dot(dot(x, y), z).exc_pending;
      assert dot(x, dot(y, z)).exc_taken == dot(dot(x, y), z).exc_taken;
      assert dot(x, dot(y, z)).shared_pending_handles == dot(dot(x, y), z).shared_pending_handles;
      assert dot(x, dot(y, z)).shared_taken_handles == dot(dot(x, y), z).shared_taken_handles;
    }
  }

  lemma dot_unit(x: F)
  ensures dot(x, unit()) == x
  {
  }

  /* Derived operators */

  predicate exchange(p1: F, p2: F, b1: B, b2: B) {
    forall q :: Inv(dot(p1, q)) ==>
        && Inv(dot(p2, q))
        && base_V(base_dot(Storage(dot(p1, q)), b1))
        && base_dot(Storage(dot(p1, q)), b1) == base_dot(Storage(dot(p2, q)), b2)
  }

  predicate withdraw(p1: F, p2: F, b2: B) {
    forall q :: Inv(dot(p1, q)) ==>
        && Inv(dot(p2, q))
        && Storage(dot(p1, q)) == base_dot(Storage(dot(p2, q)), b2)
  }

  predicate deposit(p1: F, p2: F, b1: B) {
    forall q :: Inv(dot(p1, q)) ==>
        && Inv(dot(p2, q))
        && base_V(base_dot(Storage(dot(p1, q)), b1))
        && base_dot(Storage(dot(p1, q)), b1) == Storage(dot(p2, q))
  }

  predicate transition(a: F, b: F) {
    forall p :: Inv(dot(a, p)) ==>
        Inv(dot(b, p)) && Storage(dot(a, p)) == Storage(dot(b, p))
  }

  predicate guards(f: F, m: B)
  {
    forall q :: Inv(dot(f, q)) ==>
      exists z :: base_dot(m, z) == Storage(dot(f, q))
  }

  /* Fields, ExcPending, ExcGuard, ShPending, ShGuard */

  function Fields(exc: bool, rc: int, x: X) : F {
    F(ExcOne(FieldsState(exc, rc, x)), ExcEmpty, ExcEmpty, 0, Zero)
  }

  const ExcPending : F := F(ExcEmpty, ExcOne(()), ExcEmpty, 0, Zero);

  const ExcGuard : F := F(ExcEmpty, ExcEmpty, ExcOne(()), 0, Zero);

  const ShPending : F := F(ExcEmpty, ExcEmpty, ExcEmpty, 1, Zero);

  function ShGuard(elem: X) : F {
    F(ExcEmpty, ExcEmpty, ExcEmpty, 0, Have(elem, 1))
  }

  /* RwLock-Init */

  lemma RwLockInit(x: X)
  ensures Inv(Fields(false, 0, x))
  {
  }

  /* RwLock-Exc-Begin */

  lemma RwLockExcBegin(rc: nat, x: X)
  ensures transition(
      Fields(false, rc, x),
      dot(Fields(true, rc, x), ExcPending)
    )
  {
  }

  /* RwLock-Exc-Acquire */

  lemma RwLockExcAcquire(exc: bool, x: X)
  ensures withdraw(
      dot(Fields(exc, 0, x), ExcPending),
      dot(Fields(exc, 0, x), ExcGuard),
      ExcOne(x)
    )
  {
  }

  /* RwLock-Exc-Release */

  lemma RwLockExcRelease(exc: bool, rc: nat, x: X, y: X)
  ensures deposit(
      dot(Fields(exc, rc, y), ExcGuard),
      Fields(false, rc, x),
      ExcOne(x)
    )
  {
  }

  /* RwLock-Shared-Begin */

  lemma RwLockSharedBegin(exc: bool, rc: nat, x: X)
  ensures transition(
      Fields(exc, rc, x),
      dot(Fields(exc, rc + 1, x), ShPending)
    )
  {
  }

  /* RwLock-Shared-Acquire */

  lemma RwLockSharedAcquire(exc: bool, rc: nat, x: X)
  ensures transition(
      dot(Fields(false, rc, x), ShPending),
      dot(Fields(false, rc, x), ShGuard(x))
    )
  {
  }

  /* RwLock-Shared-Release */

  lemma RwLockSharedRelease(exc: bool, rc: nat, x: X, y: X)
  ensures transition(
      dot(Fields(exc, rc, x), ShGuard(y)),
      Fields(exc, rc - 1, x)
    )
  {
  }

  /* RwLock-Shared-Retry */

  lemma RwLockSharedRetry(exc: bool, rc: nat, x: X)
  ensures transition(
      dot(Fields(exc, rc, x), ShPending),
      Fields(exc, rc - 1, x)
    )
  {
  }

  /* RwLock-Shared-Borrow */

  lemma RwLockSharedGuards(x: X)
  ensures guards(ShGuard(x), ExcOne(x))
  {
    forall q | Inv(dot(ShGuard(x), q)) ensures
      exists z :: base_dot(ExcOne(x), z) == Storage(dot(ShGuard(x), q))
    {
      var z := base_unit();
      assert base_dot(ExcOne(x), z) == Storage(dot(ShGuard(x), q));
    }
  }
}
