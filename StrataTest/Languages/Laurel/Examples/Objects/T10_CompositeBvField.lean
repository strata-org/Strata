/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Test: bitvector types as composite fields. Verifies that the heap
parameterization pass correctly boxes/unboxes bv-typed fields.
-/

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util
open Strata

namespace Strata.Laurel

def compositeBv32Field := r"
composite Register {
  var value: bv 32
}

procedure writeAndRead(r: Register, x: bv 32)
  opaque
  ensures r#value == x
  modifies r
{
  r#value := x
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "CompositeBv32Field" compositeBv32Field 23 processLaurelFile

end Laurel
