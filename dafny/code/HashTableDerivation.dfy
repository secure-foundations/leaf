module HashTable {
  /* Define the HashTable (T)PCM */

  const L: nat

  type Key
  type Value

  function Hash(k: Key) : nat

  datatype KV =
      | KV(key: Key, value: Value)
      | Empty

  datatype Option<V> = Some(value: V) | None

  datatype M =
    | M(ghost s: map<nat, Option<KV>>,
        ghost m: map<Key, Option<Option<Value>>>)

  /* dot definition */

  function map_union<K, T>(m1: map<K, Option<T>>, m2: map<K, Option<T>>) : map<K, Option<T>> {
      map k | k in m1.Keys + m2.Keys ::
          (if k !in m2.Keys then m1[k]
           else if k !in m1.Keys then m2[k]
           else None)
  }

  function dot(a: M, b: M) : M {
      M(map_union(a.s, b.s), map_union(a.m, b.m))
  }

  /* unit */

  function unit() : M {
    M(map[], map[])
  }

  /* Validity predicate */

  predicate map_valid<K, T>(m1: map<K, Option<T>>) {
      forall k | k in m1 :: m1[k].Some?
  }

  predicate LBound(a: M)
  {
    && (forall i :: i in a.s ==> 0 <= i < L)
  }

  predicate KeysDistinct(a: M)
  {
    && (forall i1, i2 :: i1 in a.s && i2 in a.s && i1 != i2
        && a.s[i1].Some?
        && a.s[i1].value.KV?
        && a.s[i2].Some?
        && a.s[i2].value.KV?
            ==> a.s[i1].value.key != a.s[i2].value.key)
  }

  predicate MapConsistent(a: M)
  {
    && (forall k :: k in a.m && a.m[k].Some? && a.m[k].value.Some? ==>
        exists i :: i in a.s && a.s[i] == Some(KV(k, a.m[k].value.value)))
  }

  predicate SlotsConsistent(a: M)
  {
    && (forall i :: i in a.s && a.s[i].Some? && a.s[i].value.KV? ==>
        a.s[i].value.key in a.m && a.m[a.s[i].value.key] != Some(None))
  }

  predicate RangeFull(a: M, i: nat)
  requires i in a.s && a.s[i].Some? && a.s[i].value.KV?
  {
    forall j :: Hash(a.s[i].value.key) <= j <= i ==> j in a.s && a.s[j].Some? && a.s[j].value.KV?
  }

  predicate Contiguous(a: M)
  {
    && (forall i :: i in a.s && a.s[i].Some? && a.s[i].value.KV? ==>
        && Hash(a.s[i].value.key) <= i
        && RangeFull(a, i)
    )
  }

  predicate P(a: M)
  {
    && map_valid(a.s)
    && map_valid(a.m)
    && LBound(a)
    && KeysDistinct(a)
    && MapConsistent(a)
    && SlotsConsistent(a)
    && Contiguous(a)
  }

  predicate V(a: M) {
    exists p :: P(dot(a, p))
  }

  /* PCM definitions */

  predicate transitions(a: M, b: M) {
    forall c :: V(dot(a, c)) ==> V(dot(b, c))
  }

  predicate le(a: M, b: M) {
    exists z :: dot(a, z) == b
  }

  predicate overlapping_conjunct(a: M, b: M, c: M) {
    forall r :: V(r) ==> le(a, r) ==> le(b, r) ==> le(c, r)
  }

  /* PCM properties */

  lemma commutative(a: M, b: M)
  ensures dot(a, b) == dot(b, a)
  {
  }

  lemma associative(a: M, b: M, c: M)
  ensures dot(a, dot(b, c)) == dot(dot(a, b), c)
  {
  }

  lemma dot_unit(a: M)
  ensures dot(a, unit()) == a
  {
  }

  lemma valid_monotonic(a: M, b: M)
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
    assert P(dot(unit(), unit()));
  }

  /* HT-specific definitions */

  function s(i: nat, e: KV) : M {
    var m: map<nat, Option<KV>>  := map[];
    M(m[i := Some(e)], map[])
  }

  function m(k: Key, v: Option<Value>) : M {
    M(map[], map[k := Some(v)])
  }

  predicate Full(a: M, k: Key, i: nat, j: nat)
  {
    && i <= j
    && (forall l :: i <= l < j ==> l in a.s && a.s[l].Some? && a.s[l].value.KV? && a.s[l].value.key != k)
    && (forall l :: l in a.s ==> i <= l < j)
    && a.m == map[]
  }

  function initial_value(key_set: set<Key>) : M {
     M(
        map i: nat | 0 <= i < L :: Some(Empty),
        map k: Key | k in key_set :: Some(None)
     )
  }

  /* Initial valid */

  lemma InitValid(key_set: set<Key>)
  ensures V(initial_value(key_set))
  {
      assert P(dot(initial_value(key_set), unit()));
  }

  /* QueryFound */

  lemma QueryFound(j: nat, k: Key, v0: Value, v: Option<Value>)
  requires V(dot(s(j, KV(k, v0)), m(k, v)))
  ensures v == Some(v0)
  {
    var p :| P(dot(dot(s(j, KV(k, v0)), m(k, v)), p));
    var a := dot(dot(s(j, KV(k, v0)), m(k, v)), p);
    assert a.s[j].value.KV?;
    assert a.m[k].Some?;
    var i :| i in a.s && a.s[i] == Some(KV(k, a.m[k].value.value));
    assert i == j;
  }

  /* QueryReachedEnd */

  lemma QueryReachedEnd(k: Key, a: M, v: Option<Value>, p: M)
  requires Full(a, k, Hash(k), L)
  requires V(dot(a, m(k, v)))
  ensures v == None
  {
    var p :| P(dot(dot(a, m(k, v)), p));
    var b := dot(dot(a, m(k, v)), p);
    if v.Some? {
      assert k in b.m;
      var i :| i in b.s && b.s[i] == Some(KV(k, b.m[k].value.value));
      assert i >= L;
      assert i < L;
      assert false;
    }
  }

  /* QueryNotFound */

  lemma QueryNotFound(k: Key, a: M, v: Option<Value>, j: nat, p: M)
  requires Full(a, k, Hash(k), j)
  requires V(dot(dot(a, s(j, Empty)), m(k, v)))
  ensures v == None
  {
    var p :| P(dot(dot(dot(a, s(j, Empty)), m(k, v)), p));
    var b := dot(dot(dot(a, s(j, Empty)), m(k, v)), p);
    if v.Some? {
      var i :| i in b.s && b.s[i] == Some(KV(k, b.m[k].value.value));
      if i < j {
        if i < Hash(k) {
          assert b.s[i].Some?;
          assert b.s[i].value.KV?;
          assert Hash(b.s[i].value.key) <= i;
          assert false;
        } else {
          assert false;
        }
      } else if i >= j {
        assert RangeFull(b, i);
        assert Hash(b.s[i].value.key) <= j <= i;
        assert b.s[j].value.KV?;
        assert false;
      }
      assert i == j;
      assert false;
    }
  }

  /* UpdateExisting */

  lemma UpdateExisting_Helper(j: nat, k: Key, v0: Option<Value>, v1: Value, v: Value, p: M)
  requires P(dot(dot(s(j, KV(k, v1)), m(k, v0)), p))
  ensures P(dot(dot(s(j, KV(k, v)), m(k, Some(v))), p))
  {
    var a := dot(dot(s(j, KV(k, v1)), m(k, v0)), p);
    var a' := dot(dot(s(j, KV(k, v)), m(k, Some(v))), p);

    assert P(a);

    assert forall i :: i in a'.s <==> i in a.s;
    assert forall k0 :: k0 in a'.m <==> k0 in a.m;

    assert LBound(a');
    assert KeysDistinct(a');

    assert MapConsistent(a') by {
      forall k0 | k0 in a'.m && a'.m[k0].Some? && a'.m[k0].value.Some?
      ensures exists i :: i in a'.s && a'.s[i] == Some(KV(k0, a'.m[k0].value.value))
      {
        if k0 == k {
          assert j in a'.s && a'.s[j] == Some(KV(k0, a'.m[k0].value.value));
        } else {
          var i :| i in a.s && a.s[i] == Some(KV(k0, a.m[k0].value.value));
          assert i in a'.s && a'.s[i] == Some(KV(k0, a'.m[k0].value.value));
        }
      }
    }

    assert SlotsConsistent(a');

    assert Contiguous(a') by {
      forall i | i in a'.s && a'.s[i].value.KV?
      ensures Hash(a'.s[i].value.key) <= i
      ensures RangeFull(a', i)
      {
        assert Hash(a.s[i].value.key) <= i;
        assert RangeFull(a, i);
        forall l | Hash(a'.s[i].value.key) <= l <= i ensures l in a'.s && a'.s[l].value.KV?
        {
        }
      }
    }
  }

  lemma UpdateExisting(j: nat, k: Key, v0: Option<Value>, v1: Value, v: Value)
  ensures transitions(
    dot(s(j, KV(k, v1)), m(k, v0)),
    dot(s(j, KV(k, v)), m(k, Some(v)))
  )
  {
    forall c | V(dot(dot(s(j, KV(k, v1)), m(k, v0)), c))
    ensures V(dot(dot(s(j, KV(k, v)), m(k, Some(v))), c))
    {
      var p :| P(dot(dot(dot(s(j, KV(k, v1)), m(k, v0)), c), p));
      associative(dot(s(j, KV(k, v1)), m(k, v0)), c, p);
      UpdateExisting_Helper(j, k, v0, v1, v, dot(c, p));
      associative(dot(s(j, KV(k, v)), m(k, Some(v))), c, p);
    }
  }

  /* UpdateNew */

  lemma UpdateNew_Helper(j: nat, k: Key, v0: Option<Value>, v: Value, a: M, p: M)
  requires Full(a, k, Hash(k), j)
  requires P(dot(dot(dot(a, s(j, Empty)), m(k, v0)), p))
  ensures P(dot(dot(dot(a, s(j, KV(k, v))), m(k, Some(v))), p))
  {
    var x := dot(dot(a, s(j, Empty)), m(k, v0));
    var y := dot(dot(a, s(j, KV(k, v))), m(k, Some(v)));
    var a := dot(x, p);
    var a' := dot(y, p);

    assert P(a);

    assert forall i :: i in a'.s <==> i in a.s;
    assert forall k0 :: k0 in a'.m <==> k0 in a.m;

    assert LBound(a');
    assert KeysDistinct(a');

    assert MapConsistent(a') by {
      forall k0 | k0 in a'.m && a'.m[k0].Some? && a'.m[k0].value.Some?
      ensures exists i :: i in a'.s && a'.s[i] == Some(KV(k0, a'.m[k0].value.value))
      {
        if k0 == k {
          assert j in a'.s && a'.s[j] == Some(KV(k0, a'.m[k0].value.value));
        } else {
          var i :| i in a.s && a.s[i] == Some(KV(k0, a.m[k0].value.value));
          assert i in a'.s && a'.s[i] == Some(KV(k0, a'.m[k0].value.value));
        }
      }
    }

    assert SlotsConsistent(a');

    assert Contiguous(a') by {
      forall i | i in a'.s && a'.s[i].value.KV?
      ensures Hash(a'.s[i].value.key) <= i
      ensures RangeFull(a', i)
      {
        if i == j {
          assert Hash(a'.s[i].value.key) <= i;
          assert RangeFull(a', i);
        } else {
          assert Hash(a.s[i].value.key) <= i;
          assert RangeFull(a, i);
          forall l | Hash(a'.s[i].value.key) <= l <= i ensures l in a'.s && a'.s[l].value.KV?
          {
          }
        }
      }
    }
  }

  lemma UpdateNew(j: nat, k: Key, v0: Option<Value>, v: Value, a: M)
  requires Full(a, k, Hash(k), j)
  ensures transitions(
    dot(dot(a, s(j, Empty)), m(k, v0)),
    dot(dot(a, s(j, KV(k, v))), m(k, Some(v)))
  )
  {
    forall c | V(dot(dot(dot(a, s(j, Empty)), m(k, v0)), c))
    ensures V(dot(dot(dot(a, s(j, KV(k, v))), m(k, Some(v))), c))
    {
      var p :| P(dot(dot(dot(dot(a, s(j, Empty)), m(k, v0)), c), p));
      associative(dot(dot(a, s(j, Empty)), m(k, v0)), c, p);
      UpdateNew_Helper(j, k, v0, v, a, dot(c, p));
      associative(dot(dot(a, s(j, KV(k, v))), m(k, Some(v))), c, p);
    }
  }

  /* Compositions with PCM-And */

  predicate map_le<K, T>(a: map<K, Option<T>>, b: map<K, Option<T>>) {
      forall k :: k in a && a[k].Some? ==>
          k in b && (b[k].Some? ==> b[k] == a[k])
  }

  lemma map_valid_left<K, T>(a: map<K, Option<T>>, b: map<K, Option<T>>)
    requires map_valid(map_union(a, b))
    ensures map_valid(a)
  {
    forall k | k in a ensures a[k].Some? {
      assert map_union(a, b)[k].Some?;
    }
  }

  lemma submap_implies_overlapping_conjunct(a: M, b: M)
    requires a.s.Keys !! b.s.Keys
    requires a.m.Keys !! b.m.Keys
    ensures overlapping_conjunct(a, b, dot(a, b))
  {
    var c := dot(a, b);
    forall r: M | map_valid(r.s) && map_valid(r.m) && le(a, r) && le(b, r) ensures le(c, r)
    {
      var z_s := map k | k in r.s && k !in c.s :: r.s[k];
      var z_m := map k | k in r.m && k !in c.m :: r.m[k];

      //assert map_union(c.s, z_s) == r.s;
      //assert map_union(c.m, z_m) == r.m;

      var z := M(z_s, z_m);
      assert dot(c, z) == r;
    }

    forall r: M | V(r) ensures map_valid(r.s) && map_valid(r.m) {
      var p :| P(dot(r, p));

      var s1 :| map_union(r.s, s1) == dot(r, p).s;
      map_valid_left(r.s, s1);

      var m1 :| map_union(r.m, m1) == dot(r, p).m;
      map_valid_left(r.m, m1);
    }
  }

  lemma overlapping_conjunct_m_s(k: Key, v: Option<Value>, i: nat, slot: KV)
    ensures overlapping_conjunct(
      m(k, v), s(i, slot),
      dot(m(k, v), s(i, slot))
    )
  {
    submap_implies_overlapping_conjunct(m(k, v), s(i, slot));
  }

  lemma overlapping_conjunct_full_s(a: M, k: Key, i: nat, j: nat, slot: KV)
    requires Full(a, k, i, j)
    ensures overlapping_conjunct(
      a, s(j, slot),
      dot(a, s(j, slot))
    )
  {
    submap_implies_overlapping_conjunct(a, s(j, slot));
  }

  lemma overlapping_conjunct_full_m(a: M, k: Key, i: nat, j: nat, k1: Key, v1: Option<Value>)
    requires Full(a, k, i, j)
    ensures overlapping_conjunct(
      a, m(k1, v1),
      dot(a, m(k1, v1))
    )
  {
    submap_implies_overlapping_conjunct(a, m(k1, v1));
  }

  lemma overlapping_conjunct_full_s_m(a: M, k: Key, i: nat, j: nat, slot: KV, k1: Key, v1: Option<Value>)
    requires Full(a, k, i, j)
    ensures overlapping_conjunct(
      a, dot(s(j, slot), m(k1, v1)),
      dot(a, dot(s(j, slot), m(k1, v1)))
    )
  {
    submap_implies_overlapping_conjunct(a, dot(s(j, slot), m(k1, v1)));
  }


}
