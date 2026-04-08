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
procedure literalSelect() returns (r: int) {
  var s: Seq<int> := [10, 20, 30];
  r := Sequence.select(s, 1);
  assert r == 20
};

// Empty sequence has length 0
procedure emptyLength() {
  var s: Seq<int> := [];
  assert Sequence.length(s) == 0
};

// Build and length
procedure buildLength() {
  var s: Seq<int> := [1, 2, 3];
  assert Sequence.length(s) == 3
};

// Functional update preserves length
procedure updateLength() {
  var s: Seq<int> := [1, 2, 3];
  var t: Seq<int> := s[0 := 99];
  assert Sequence.length(t) == 3
};

// Functional update changes element
procedure updateSelect() {
  var s: Seq<int> := [1, 2, 3];
  var t: Seq<int> := s[0 := 99];
  assert Sequence.select(t, 0) == 99
};

// Subscript read sugar
procedure subscriptRead(s: Seq<int>)
  requires Sequence.length(s) > 0
{
  var x: int := s[0];
  assert x == Sequence.select(s, 0)
};

// Subscript update sugar
procedure subscriptUpdate(s: Seq<int>)
  requires Sequence.length(s) > 0
{
  var t: Seq<int> := s[0 := 42];
  assert Sequence.select(t, 0) == 42
};

// Sequence in requires/ensures
procedure contractSeq(s: Seq<int>) returns (r: int)
  requires Sequence.length(s) > 0
  ensures r == Sequence.select(s, 0)
{
  r := s[0]
};

// Sequence in quantifiers
procedure quantifierSeq(s: Seq<int>)
  requires Sequence.length(s) > 0
  requires forall(i: int) => 0 <= i && i < Sequence.length(s) ==> s[i] >= 0
{
  assert s[0] >= 0
};

// Invalid assertion should fail
procedure failingAssert() {
  var s: Seq<int> := [1, 2, 3];
  assert Sequence.select(s, 0) == 999
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};

// Bool element type
procedure seqBool() {
  var s: Seq<bool> := [true, false];
  assert Sequence.select(s, 0) == true
};

// Nested sequences
procedure seqNested() {
  var s: Seq<Seq<int>> := [[1, 2], [3, 4]];
  assert Sequence.select(Sequence.select(s, 0), 1) == 2
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "Sequences" seqProgram 14 processLaurelFile

end Laurel
end Strata
