/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Test: bitvector types as composite fields. Verifies that the heap
parameterization pass correctly boxes/unboxes bv-typed fields.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata

program Laurel;

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
#end
