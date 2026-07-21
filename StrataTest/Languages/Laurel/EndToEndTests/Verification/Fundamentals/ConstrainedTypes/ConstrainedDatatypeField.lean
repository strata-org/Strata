/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

-- Lowering fix: a constrained type (e.g. `int32`) used as a datatype
-- constructor field now translates to its base Core type (`int`)
-- instead of poisoning translation. The datatype is verifiable: the
-- field value is modelled, so a correct assertion passes and a false
-- one is genuinely caught. (`int32` is exactly what the Java frontend
-- emits for a Java `int` record field.)

#eval testLaurel <|
#strata
program Laurel;
constrained int32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0

datatype Cell {
  MkCell(val: int32)
}

// Constructor/destructor over a constrained-type field works.
procedure fieldRoundTrips()
  opaque
{
  var b: Cell := MkCell(5);
  assert Cell..val(b) == 5
};

// And a false assertion is genuinely caught (not vacuously passed).
procedure falseAssertionIsCaught()
  opaque
{
  var b: Cell := MkCell(5);
  assert Cell..val(b) == 999
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end


-- Wrapped form (Heimdall, rev 1): a constrained type nested inside a `Map`
-- datatype field must also be lowered (`Map int32 string` -> `Map int string`),
-- exercising `resolveBaseType`'s `.TMap` recursion. Without it the `int32`
-- reference dangles after the constrained-type definition is dropped and the
-- Laurel-to-Core translator fails. (Laurel surface `Set` carries no element
-- type, so `Map` is the vehicle for wrapping the constrained type.)
#eval testLaurel <|
#strata
program Laurel;
constrained int32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0

datatype Boxed {
  MkBoxed(m: Map int32 string)
}

// Construct a `Boxed` with a known map entry and read it back through the
// destructed field: the concrete value round-trips, so the field value is
// genuinely modelled (not just type-checked).
procedure wrappedFieldValueIsModelled(m: Map int32 string)
  opaque
{
  var b: Boxed := MkBoxed(update(m, 5, "hi"));
  assert select(Boxed..m(b), 5) == "hi"
};

// And a false assertion about the map entry fails (not vacuously passed),
// mirroring `falseAssertionIsCaught` above. (With an SMT string-theory map
// value the solver's counterexample is inconclusive, so this reports "could
// not be proved" rather than "does not hold" — as in the sibling
// `ConstrainedField.lean` negative tests.)
procedure falseWrappedAssertionIsCaught(m: Map int32 string)
  opaque
{
  var b: Boxed := MkBoxed(update(m, 5, "hi"));
  assert select(Boxed..m(b), 5) == "bye"
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
