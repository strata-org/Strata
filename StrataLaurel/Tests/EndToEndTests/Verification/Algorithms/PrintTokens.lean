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

procedure isLetter(c: int): bool
{
  (97 <= c && c <= 122) || (65 <= c && c <= 90) || c == 95
};

procedure isDigit(c: int): bool
{
  48 <= c && c <= 57
};

procedure spansOk(st: Sequence<int>, en: Sequence<int>, upTo: int): bool
{
  seqLength(st) == seqLength(en)
  && (forall(t: int) => 0 <= t ==> t < seqLength(st) ==> seqSelect(st, t) < seqSelect(en, t) && seqSelect(en, t) <= upTo)
  && (forall(t: int) => 0 < t ==> t < seqLength(st) ==> seqSelect(en, t - 1) <= seqSelect(st, t))
  && (forall(t: int) => 0 <= t ==> t < seqLength(st) ==> 0 <= seqSelect(st, t))
};

procedure tokenize(input: Sequence<int>) returns (st: Sequence<int>, en: Sequence<int>)
  opaque
  ensures spansOk(st, en, seqLength(input))
{
  var s: Sequence<int> := seqEmpty();
  var e: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < seqLength(input))
    invariant 0 <= i
    invariant i <= seqLength(input)
    invariant spansOk(s, e, i)
  {
    var c: int := seqSelect(input, i);
    if c == 32 || c == 10 || c == 9 then { i := i + 1 }
    else {
      var j: int := i + 1;
      if isLetter(c) then {
        while (j < seqLength(input) && (isLetter(seqSelect(input, j)) || isDigit(seqSelect(input, j))))
          invariant i < j
          invariant j <= seqLength(input)
//                  ^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
        { j := j + 1 }
      } else if isDigit(c) then {
        while (j < seqLength(input) && isDigit(seqSelect(input, j)))
          invariant i < j
          invariant j <= seqLength(input)
//                  ^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
        { j := j + 1 }
      };
      s := seqBuild(s, i);
      e := seqBuild(e, j);
      i := j
    }
  };
  st := s;
  en := e
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure isLetter(c: int): bool
{
  (97 <= c && c <= 122) || (65 <= c && c <= 90) || c == 95
};

procedure isDigit(c: int): bool
{
  48 <= c && c <= 57
};

procedure spansOk(st: Sequence<int>, en: Sequence<int>, upTo: int): bool
{
  seqLength(st) == seqLength(en)
  && (forall(t: int) => 0 <= t ==> t < seqLength(st) ==> seqSelect(st, t) < seqSelect(en, t) && seqSelect(en, t) <= upTo)
  && (forall(t: int) => 0 < t ==> t < seqLength(st) ==> seqSelect(en, t - 1) <= seqSelect(st, t))
  && (forall(t: int) => 0 <= t ==> t < seqLength(st) ==> 0 <= seqSelect(st, t))
};

procedure tokenize(input: Sequence<int>) returns (st: Sequence<int>, en: Sequence<int>)
  opaque
  ensures spansOk(st, en, seqLength(input))
{
  var s: Sequence<int> := seqEmpty();
  var e: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < seqLength(input))
    invariant 0 <= i
    invariant i <= seqLength(input)
    invariant spansOk(s, e, i)
  {
    var c: int := seqSelect(input, i);
    if c == 32 || c == 10 || c == 9 then { i := i + 1 }
    else {
      var j: int := i + 1;
      if isLetter(c) then {
        while (isLetter(seqSelect(input, j)) || isDigit(seqSelect(input, j)))
//                      ^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                      ^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
          invariant i < j
          invariant j <= seqLength(input)
//                  ^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
        { j := j + 1 }
      } else if isDigit(c) then {
        while (j < seqLength(input) && isDigit(seqSelect(input, j)))
          invariant i < j
          invariant j <= seqLength(input)
//                  ^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
        { j := j + 1 }
      };
      s := seqBuild(s, i);
      e := seqBuild(e, j);
      i := j
    }
  };
  st := s;
  en := e
};
#end
