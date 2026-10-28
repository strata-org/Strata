/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.EndToEndTests.Verification.Algorithms.BenchmarkOptions

open StrataTest.Util
open StrataTest.Util.Algorithms
open Strata

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

composite Observer {
  var cache: int
}

composite Subject {
  var value: int
  var observers: Sequence<Observer>
}

procedure synced(s: Subject): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(s#observers) ==> seqSelect(s#observers, i)#cache == s#value
};

procedure syncedBelow(s: Subject, hi: int): bool
{
  forall(i: int) => 0 <= i ==> i < hi ==> i < seqLength(s#observers) ==> seqSelect(s#observers, i)#cache == s#value
};

procedure register(s: Subject, o: Observer)
  requires synced(s)
  opaque
  ensures synced(s)
  ensures seqLength(s#observers) == old(seqLength(s#observers)) + 1
  modifies *
{
  o#cache := s#value;
  s#observers := seqBuild(s#observers, o)
};

procedure notifyAll(s: Subject, v: int)
  requires synced(s)
  opaque
  ensures synced(s)
  ensures s#value == v
  modifies *
{
  s#value := v;
  var i: int := 0;
  while (i < seqLength(s#observers))
    invariant 0 <= i
    invariant s#value == v
    invariant syncedBelow(s, i)
  {
    var o: Observer := seqSelect(s#observers, i);
    o#cache := v;
    i := i + 1
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

composite Observer {
  var cache: int
}

composite Subject {
  var value: int
  var observers: Sequence<Observer>
}

procedure synced(s: Subject): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(s#observers) ==> seqSelect(s#observers, i)#cache == s#value
};

procedure syncedBelow(s: Subject, hi: int): bool
{
  forall(i: int) => 0 <= i ==> i < hi ==> i < seqLength(s#observers) ==> seqSelect(s#observers, i)#cache == s#value
};

procedure register(s: Subject, o: Observer)
  requires synced(s)
  opaque
  ensures synced(s)
  ensures seqLength(s#observers) == old(seqLength(s#observers)) + 1
  modifies *
{
  o#cache := s#value;
  s#observers := seqBuild(s#observers, o)
};

procedure notifyAll(s: Subject, v: int)
  requires synced(s)
  opaque
  ensures synced(s)
//        ^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures s#value == v
  modifies *
{
  s#value := v;
  var i: int := 0;
  while (i < seqLength(s#observers) - 1)
    invariant 0 <= i
    invariant s#value == v
    invariant syncedBelow(s, i)
  {
    var o: Observer := seqSelect(s#observers, i);
    o#cache := v;
    i := i + 1
  }
};
#end
