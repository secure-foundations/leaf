include "HashTableDerivation.dfy"

module RWLock {
  /* Define the RwLock TPCM Extension */

  import Base = HashTable

  datatype CentralState = CentralState(
    exc: bool,
    rc: nat,
    held_value: Base.M
  ) | None

  predicate IsFull<K(!new), V>(m: imap<K, V>) {
    forall k :: k in m
  }

  type FullMap<K(!new), V> = m : imap<K, V> | IsFull(m)
    witness *

  datatype F = F(
    central: CentralState,
    exc_pending: bool,
    exc_taken: bool,
    shared_pending_handles: nat,
    ghost shared_taken_handles: FullMap<Base.M, nat>
  ) | Bot

  function zero_map() : imap<Base.M, nat> {
    imap k | true :: 0
  }

  function unit() : F
  {
    F(None, false, false, 0, zero_map())
  }

  function add_fns(f: FullMap<Base.M, nat>, g: FullMap<Base.M, nat>) : FullMap<Base.M, nat> {
    imap b | true :: f[b] + g[b]
  }

  function dot(a: F, b: F) : F
  {
    if a.F? && b.F?
      && !(a.central.CentralState? && b.central.CentralState?)
      && !(a.exc_pending && b.exc_pending)
      && !(a.exc_taken && b.exc_taken)
    then
      F(
        if a.central.CentralState? then a.central else b.central,
        a.exc_pending || b.exc_pending,
        a.exc_taken || b.exc_taken,
        a.shared_pending_handles + b.shared_pending_handles,
        add_fns(a.shared_taken_handles, b.shared_taken_handles))
    else
      Bot
  }

  /* Validity predicate */

  predicate P(f: F) {
    && f != Bot
    && f.central.CentralState?
    && f.central.rc == f.shared_pending_handles + f.shared_taken_handles[f.central.held_value]
    && (!f.central.exc ==> !f.exc_pending && !f.exc_taken)
    && (f.central.exc ==> (f.exc_pending || f.exc_taken)
                       && !(f.exc_pending && f.exc_taken))
    && (f.exc_taken ==> forall y :: f.shared_taken_handles[y] == 0)
    && (forall y :: f.shared_taken_handles[y] != 0 ==> f.central.held_value == y)
  }

  predicate V(a: F) {
    exists p :: P(dot(a, p))
  }

  /* Interpretation function */

  // I_defined(f) means I(f) != bot
  predicate I_defined(f: F) {
    f == unit() || P(f)
  }

  function I(f: F) : Base.M
  requires I_defined(f)
  {
    if f == unit() then
      Base.unit()
    else if f.exc_taken then
      Base.unit()
    else
      f.central.held_value
  }

  /* Transitions predicate */

  predicate transitions(a: F, b: F) {
    forall p :: I_defined(dot(a, p)) ==>
        I_defined(dot(b, p)) && I(dot(a, p)) == I(dot(b, p))
  }

  /* TPCM properties */

  lemma commutative(x: F, y: F)
  ensures dot(x, y) == dot(y, x)
  {
    if dot(x, y).F? {
      assert dot(x, y).central == dot(y, x).central;
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
      assert dot(x, dot(y, z)).central == dot(dot(x, y), z).central;
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

  lemma valid_monotonic(a: F, b: F)
  requires V(dot(a, b))
  ensures V(a)
  {
    var c :| P(dot(dot(a, b), c));
    associative(a, b, c);
    assert P(dot(a, dot(b, c)));
  }

  lemma valid_unit()
  ensures V(unit())
  {
    assert P(dot(unit(), Central(false, 0, Base.unit())));
  }

  lemma reflexive(a: F)
  ensures transitions(a, a)
  {
  }

  lemma transitive(a: F, b: F, c: F)
  requires transitions(a, b)
  requires transitions(b, c)
  ensures transitions(a, c)
  {
  }

  lemma monotonic(a: F, b: F, c: F)
  requires transitions(a, b)
  requires V(dot(a, c))
  ensures V(dot(b, c))
  ensures transitions(dot(a, c), dot(b, c))
  {
    assert V(dot(b, c)) by {
      if dot(b, c) == unit() {
        valid_unit();
      } else {
        var p :| I_defined(dot(dot(a, c), p));
        associative(a, c, p);
        associative(b, c, p);
        assert I_defined(dot(dot(b, c), p));
      }
    }
    assert transitions(dot(a, c), dot(b, c)) by {
      forall p | I_defined(dot(dot(a, c), p))
      ensures I_defined(dot(dot(b, c), p)) && I(dot(dot(a, c), p)) == I(dot(dot(b, c), p))
      {
        associative(a, c, p);
        associative(b, c, p);
      }
    }
  }

  /* Central, ExcPending, ExcGuard, ShPending, ShGuard */

  function Central(exc: bool, rc: nat, x: Base.M) : F {
    F(CentralState(exc, rc, x), false, false, 0, zero_map())
  }

  const ExcPending : F := F(None, true, false, 0, zero_map());

  const ExcGuard : F := F(None, false, true, 0, zero_map());

  function unit_fn(elem: Base.M) : FullMap<Base.M, nat> {
    imap b | true :: (if elem == b then 1 else 0)
  }

  const ShPending : F := F(None, false, false, 1, zero_map());

  function ShGuard(elem: Base.M) : F {
    F(None, false, false, 0, unit_fn(elem))
  }

  /* TPCM Extension properties */

  lemma valid_domain(f: F)
  requires I_defined(f)
  ensures V(f)
  {
    if f != unit() {
      dot_unit(f);
      assert P(dot(f, unit()));
      assert V(f);
    } else {
      assert P(dot(f, Central(false, 0, Base.unit())));
    }
  }

  lemma extension_unit(f: F)
  ensures I_defined(unit())
  ensures I(unit()) == Base.unit()
  {
  }

  lemma respects_transitions(f: F, f': F)
  requires I_defined(f) && transitions(f, f')
  ensures I_defined(f')
  ensures Base.transitions(I(f), I(f'))
  {
    dot_unit(f);
    assert I_defined(dot(f, unit()));
    assert I_defined(dot(f', unit()));
    dot_unit(f');
    assert I_defined(f');
    assert Base.transitions(I(f), I(f'));
  }

  /* RwLock-Init */

  lemma RwLockInit(x: Base.M)
  ensures V(Central(false, 0, x))
  {
    assert P(dot(Central(false, 0, x), unit()));
  }

  /* RwLock-Exc-Begin */

  lemma RwLockExcBegin(rc: nat, x: Base.M)
  ensures transitions(
      Central(false, rc, x),
      dot(Central(true, rc, x), ExcPending)
    )
  {
  }

  /* RwLock-Exc-Acquire */

  predicate ExtExchangeCondition(f: F, m: Base.M, f': F, m': Base.M)
  {
    forall p :: I_defined(dot(f, p)) && Base.V(Base.dot(m, I(dot(f, p)))) ==>
      I_defined(dot(f', p)) &&
        Base.transitions(Base.dot(m, I(dot(f, p))), Base.dot(m', I(dot(f', p))))
  }

  lemma RwLockExcAcquire(exc: bool, x: Base.M)
  ensures ExtExchangeCondition(
      dot(Central(exc, 0, x), ExcPending),
      Base.unit(),
      dot(Central(exc, 0, x), ExcGuard),
      x
    )
  {
    var f := dot(Central(exc, 0, x), ExcPending);
    var m := Base.unit();
    var f' := dot(Central(exc, 0, x), ExcGuard);
    var m' := x;
    forall p | I_defined(dot(f, p)) && Base.V(Base.dot(m, I(dot(f, p))))
    ensures I_defined(dot(f', p))
    ensures Base.transitions(Base.dot(m, I(dot(f, p))), Base.dot(m', I(dot(f', p))))
    {
      assert m == I(dot(f', p));
      assert m' == I(dot(f, p));
      Base.commutative(m, m');
      assert Base.dot(m, I(dot(f, p))) == Base.dot(m', I(dot(f', p)));
    }
  }

  /* RwLock-Exc-Release */

  lemma RwLockExcRelease(exc: bool, rc: nat, x: Base.M, y: Base.M)
  ensures ExtExchangeCondition(
      dot(Central(exc, rc, y), ExcGuard),
      x,
      Central(false, rc, x),
      Base.unit()
    )
  {
    var f := dot(Central(exc, rc, y), ExcGuard);
    var m := x;
    var f' := Central(false, rc, x);
    var m' := Base.unit();
    forall p | I_defined(dot(f, p)) && Base.V(Base.dot(m, I(dot(f, p))))
    ensures I_defined(dot(f', p))
    ensures Base.transitions(Base.dot(m, I(dot(f, p))), Base.dot(m', I(dot(f', p))))
    {
      assert forall b :: dot(f',p).shared_taken_handles[b] == dot(f,p).shared_taken_handles[b];

      assert m == I(dot(f', p));
      assert m' == I(dot(f, p));
      Base.commutative(m, m');
      assert Base.dot(m, I(dot(f, p))) == Base.dot(m', I(dot(f', p)));
    }
  }

  /* RwLock-Shared-Begin */

  lemma RwLockSharedBegin(exc: bool, rc: nat, x: Base.M)
  ensures transitions(
      Central(exc, rc, x),
      dot(Central(exc, rc + 1, x), ShPending)
    )
  {
    var a := Central(exc, rc, x);
    var b := dot(Central(exc, rc + 1, x), ShPending);
    forall p | I_defined(dot(a, p))
    ensures I_defined(dot(b, p))
    ensures I(dot(a, p)) == I(dot(b, p))
    {
      assert forall y :: dot(b,p).shared_taken_handles[y] == dot(a,p).shared_taken_handles[y];
    }
  }

  /* RwLock-Shared-Acquire */

  lemma RwLockSharedAcquire(exc: bool, rc: nat, x: Base.M)
  ensures transitions(
      dot(Central(false, rc, x), ShPending),
      dot(Central(false, rc, x), ShGuard(x))
    )
  {
    var a := dot(Central(false, rc, x), ShPending);
    var b := dot(Central(false, rc, x), ShGuard(x));
    forall p | I_defined(dot(a, p))
    ensures I_defined(dot(b, p))
    ensures I(dot(a, p)) == I(dot(b, p))
    {
      assert forall y :: y != x ==>
        dot(b,p).shared_taken_handles[y] == dot(a,p).shared_taken_handles[y];
    }
  }

  /* RwLock-Shared-Release */

  lemma RwLockSharedRelease(exc: bool, rc: nat, x: Base.M, y: Base.M)
  requires V(dot(Central(exc, rc, x), ShGuard(y)))
  ensures rc >= 1
  ensures transitions(
      dot(Central(exc, rc, x), ShGuard(y)),
      Central(exc, rc - 1, x)
    )
  {
    assert rc >= 1 by {
      var p :| P(dot(dot(Central(exc, rc, x), ShGuard(y)), p));
      assert dot(dot(Central(exc, rc, x), ShGuard(y)), p).shared_taken_handles[y] >= 1;
      assert x == y;
    }

    var a := dot(Central(exc, rc, x), ShGuard(y));
    var b := Central(exc, rc - 1, x);
    forall p | I_defined(dot(a, p))
    ensures I_defined(dot(b, p)) && I(dot(a, p)) == I(dot(b, p))
    {
      var f := dot(a, p);
      var f' := dot(b, p);
      assert f.shared_taken_handles[y] > 0;
      assert y == f.central.held_value;
      assert forall b :: b != f.central.held_value ==>
          f'.shared_taken_handles[b] == f.shared_taken_handles[b];
    }
  }

  /* RwLock-Shared-Retry */

  lemma RwLockSharedRetry(exc: bool, rc: nat, x: Base.M)
  requires V(dot(Central(exc, rc, x), ShPending))
  ensures rc >= 1
  ensures transitions(
      dot(Central(exc, rc, x), ShPending),
      Central(exc, rc - 1, x)
    )
  {
    assert rc >= 1;

    var a := dot(Central(exc, rc, x), ShPending);
    var b := Central(exc, rc - 1, x);
    forall p | I_defined(dot(a, p))
    ensures I_defined(dot(b, p)) && I(dot(a, p)) == I(dot(b, p))
    {
      var f := dot(a, p);
      var f' := dot(b, p);
      assert forall b :: b != f.central.held_value ==>
          f'.shared_taken_handles[b] == f.shared_taken_handles[b];
    }
  }

  /* RwLock-Shared-Borrow */

  predicate BorrowBackCondition(f: F, m: Base.M)
  {
    forall p :: I_defined(dot(f, p)) ==>
      exists z :: Base.dot(m, z) == I(dot(f, p))
  }

  lemma RwLockSharedBorrow(x: Base.M)
  ensures BorrowBackCondition(ShGuard(x), x)
  {
    var f := ShGuard(x);
    forall p | I_defined(dot(f, p))
    ensures exists z :: Base.dot(x, z) == I(dot(f, p))
    {
      assert dot(f, p).shared_taken_handles[x] >= 1;
      assert x == I(dot(f, p));

      Base.dot_unit(x);
      assert Base.dot(x, Base.unit()) == I(dot(f, p));
    }
  }
}
