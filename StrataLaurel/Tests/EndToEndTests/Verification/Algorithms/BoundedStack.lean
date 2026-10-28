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

composite Stack {
  var buf: Sequence<int>
  var size: int
}

procedure push(s: Stack, v: int)
  requires 0 <= s#size
  requires s#size < seqLength(s#buf)
  opaque
  ensures s#size == old(s#size) + 1
  ensures seqLength(s#buf) == old(seqLength(s#buf))
  ensures seqSelect(s#buf, s#size - 1) == v
  ensures forall(k: int) => 0 <= k ==> k < old(s#size) ==> seqSelect(s#buf, k) == old(seqSelect(s#buf, k))
  modifies s
{
  s#buf := seqUpdate(s#buf, s#size, v);
  s#size := s#size + 1
};

procedure pop(s: Stack) returns (r: int)
  requires 0 < s#size
  requires s#size <= seqLength(s#buf)
  opaque
  ensures r == old(seqSelect(s#buf, s#size - 1))
  ensures s#size == old(s#size) - 1
  modifies s
{
  s#size := s#size - 1;
  r := seqSelect(s#buf, s#size)
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

composite Stack {
  var buf: Sequence<int>
  var size: int
}

procedure push(s: Stack, v: int)
  requires 0 <= s#size
  requires s#size < seqLength(s#buf)
  opaque
  ensures s#size == old(s#size) + 1
  ensures seqLength(s#buf) == old(seqLength(s#buf))
  ensures seqSelect(s#buf, s#size - 1) == v
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures forall(k: int) => 0 <= k ==> k < old(s#size) ==> seqSelect(s#buf, k) == old(seqSelect(s#buf, k))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  modifies s
{
  s#buf := seqUpdate(s#buf, s#size - 1, v);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
  s#size := s#size + 1
};

procedure pop(s: Stack) returns (r: int)
  requires 0 < s#size
  requires s#size <= seqLength(s#buf)
  opaque
  ensures r == old(seqSelect(s#buf, s#size - 1))
  ensures s#size == old(s#size) - 1
  modifies s
{
  s#size := s#size - 1;
  r := seqSelect(s#buf, s#size)
};
#end
