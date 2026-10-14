/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Test: bitvector types as composite fields. Verifies that the heap
parameterization pass correctly boxes/unboxes bv-typed fields.
-/

meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- No Core interpreter: it fails with "assert condition did not reduce to bool" on this program.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
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
//        ^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
  modifies r
{
  r#value := 200 bv 16
};

procedure runAll() entry
  opaque
  modifies *
{
  var r: Register := new Register;
  writeValue(r, 7 bv 16);
  writeLiteral(r);
  writeWrongLiteral(r)
};
#end
