/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def seqProgram := r"
// Literal construction and select
procedure literalSelect() returns (r: int)
  opaque
{
  var s: Seq<int> := [10, 20, 30];
  r := Sequence.select(s, 1);
  assert r == 20
};

// Empty sequence has length 0
procedure emptyLength()
  opaque
{
  var s: Seq<int> := [];
  assert Sequence.length(s) == 0
};

// Build and length
procedure buildLength()
  opaque
{
  var s: Seq<int> := [1, 2, 3];
  assert Sequence.length(s) == 3
};

// Functional update preserves length
procedure updateLength()
  opaque
{
  var s: Seq<int> := [1, 2, 3];
  var t: Seq<int> := s[0 := 99];
  assert Sequence.length(t) == 3
};

// Functional update changes element
procedure updateSelect()
  opaque
{
  var s: Seq<int> := [1, 2, 3];
  var t: Seq<int> := s[0 := 99];
  assert Sequence.select(t, 0) == 99
};

// Subscript read sugar
procedure subscriptRead(s: Seq<int>)
  requires Sequence.length(s) > 0
  opaque
{
  var x: int := s[0];
  assert x == Sequence.select(s, 0)
};

// Subscript update sugar
procedure subscriptUpdate(s: Seq<int>)
  requires Sequence.length(s) > 0
  opaque
{
  var t: Seq<int> := s[0 := 42];
  assert Sequence.select(t, 0) == 42
};

// Sequence in requires/ensures
procedure contractSeq(s: Seq<int>) returns (r: int)
  requires Sequence.length(s) > 0
  opaque
  ensures r == Sequence.select(s, 0)
{
  r := s[0]
};

// Sequence in quantifiers
procedure quantifierSeq(s: Seq<int>)
  requires Sequence.length(s) > 0
  requires forall(i: int) => 0 <= i && i < Sequence.length(s) ==> s[i] >= 0
  opaque
{
  assert s[0] >= 0
};

// Bool element type
procedure seqBool()
  opaque
{
  var s: Seq<bool> := [true, false];
  assert Sequence.select(s, 0) == true
};

// Nested sequences
procedure seqNested()
  opaque
{
  var s: Seq<Seq<int>> := [[1, 2], [3, 4]];
  assert Sequence.select(Sequence.select(s, 0), 1) == 2
};

// Append length
procedure appendLength()
  opaque
{
  var a: Seq<int> := [1, 2];
  var b: Seq<int> := [3, 4, 5];
  var c: Seq<int> := Sequence.append(a, b);
  assert Sequence.length(c) == 5
};

// Append select from first half
procedure appendSelectFirst()
  opaque
{
  var a: Seq<int> := [10, 20];
  var b: Seq<int> := [30];
  var c: Seq<int> := Sequence.append(a, b);
  assert c[0] == 10;
  assert c[1] == 20
};

// Append select from second half
procedure appendSelectSecond()
  opaque
{
  var a: Seq<int> := [10, 20];
  var b: Seq<int> := [30];
  var c: Seq<int> := Sequence.append(a, b);
  assert c[2] == 30
};

// Take length
procedure takeLength()
  opaque
{
  var s: Seq<int> := [10, 20, 30, 40];
  var t: Seq<int> := Sequence.take(s, 2);
  assert Sequence.length(t) == 2
};

// Take preserves elements
procedure takeSelect()
  opaque
{
  var s: Seq<int> := [10, 20, 30, 40];
  var t: Seq<int> := Sequence.take(s, 2);
  assert t[0] == 10;
  assert t[1] == 20
};

// Drop length
procedure dropLength()
  opaque
{
  var s: Seq<int> := [10, 20, 30, 40];
  var d: Seq<int> := Sequence.drop(s, 2);
  assert Sequence.length(d) == 2
};

// Drop selects from offset
procedure dropSelect()
  opaque
{
  var s: Seq<int> := [10, 20, 30, 40];
  var d: Seq<int> := Sequence.drop(s, 2);
  assert d[0] == 30;
  assert d[1] == 40
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Sequences" seqProgram 14 processLaurelFile

-- Negative cases: misuses of Seq<T> flagged by ValidateSubscriptUsage.

def seqNegativeProgram := r"
// Diagnostic 2: destructive update on Seq<T>
procedure seqDestructiveUpdate()
  opaque
{
  var s: Seq<int> := [1, 2, 3];
  s[0] := 42
//^^^^^^^^^^ error: immutable
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "SeqNegatives" seqNegativeProgram 14 processLaurelFile

end Laurel
end Strata
