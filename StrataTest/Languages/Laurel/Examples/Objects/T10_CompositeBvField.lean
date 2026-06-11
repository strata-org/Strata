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

def compositeBv16Field := r"
composite Register {
  var value: bv 16
}

procedure writeValue(r: Register, x: bv 16)
  opaque
  ensures r#value == x
  modifies r
{
  r#value := x
};

// Test using bv literal directly
procedure writeLiteral(r: Register)
  opaque
  ensures r#value == 100 bv 16
  modifies r
{
  r#value := 100 bv 16
};

// Error: postcondition claims field equals wrong literal
procedure writeWrongLiteral(r: Register)
  opaque
  ensures r#value == 100 bv 16
//        ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  modifies r
{
  r#value := 200 bv 16
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "CompositeBv16Field" compositeBv16Field 23 processLaurelFile

end Laurel
