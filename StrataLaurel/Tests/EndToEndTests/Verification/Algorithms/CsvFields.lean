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

procedure quoted(s: Sequence<int>, hi: int): bool;
procedure seps(s: Sequence<int>, hi: int): int;

procedure csvAxioms(): bool
{
  (forall(s: Sequence<int>) => !quoted(s, 0) && seps(s, 0) == 0)
  && (forall(s: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(s) ==>
        quoted(s, h) == (quoted(s, h - 1) != (seqSelect(s, h - 1) == 34))
        && seps(s, h) == seps(s, h - 1) + (if seqSelect(s, h - 1) == 44 && !quoted(s, h - 1) then 1 else 0))
};

procedure countFields(input: Sequence<int>) returns (fields: int)
  requires csvAxioms()
  opaque
  ensures fields == -1 || fields == seps(input, seqLength(input)) + 1
{
  var n: int := 0;
  var q: bool := false;
  var i: int := 0;
  while (i < seqLength(input))
    invariant 0 <= i
    invariant i <= seqLength(input)
    invariant q == quoted(input, i)
    invariant n == seps(input, i)
  {
    var c: int := seqSelect(input, i);
    if c == 34 && q && i + 1 < seqLength(input) && seqSelect(input, i + 1) == 34 then {
      i := i + 2
    } else {
      if c == 34 then { q := !q } else if c == 44 && !q then { n := n + 1 };
      i := i + 1
    }
  };
  if q then { fields := -1 } else { fields := n + 1 }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure quoted(s: Sequence<int>, hi: int): bool;
procedure seps(s: Sequence<int>, hi: int): int;

procedure csvAxioms(): bool
{
  (forall(s: Sequence<int>) => !quoted(s, 0) && seps(s, 0) == 0)
  && (forall(s: Sequence<int>) => forall(h: int) => 1 <= h ==> h <= seqLength(s) ==>
        quoted(s, h) == (quoted(s, h - 1) != (seqSelect(s, h - 1) == 34))
        && seps(s, h) == seps(s, h - 1) + (if seqSelect(s, h - 1) == 44 && !quoted(s, h - 1) then 1 else 0))
};

procedure countFields(input: Sequence<int>) returns (fields: int)
  requires csvAxioms()
  opaque
  ensures fields == -1 || fields == seps(input, seqLength(input)) + 1
{
  var n: int := 0;
  var q: bool := false;
  var i: int := 0;
  while (i < seqLength(input))
    invariant 0 <= i
    invariant i <= seqLength(input)
//            ^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant q == quoted(input, i)
//            ^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant n == seps(input, i)
//            ^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
  {
    var c: int := seqSelect(input, i);
    if c == 34 && q && seqSelect(input, i + 1) == 34 then {
//                     ^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
      i := i + 2
    } else {
      if c == 34 then { q := !q } else if c == 44 && !q then { n := n + 1 };
      i := i + 1
    }
  };
  if q then { fields := -1 } else { fields := n + 1 }
};
#end
