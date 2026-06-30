/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! Regression: two `Seq<T>` fields with different `T` on the same composite
must produce distinct Box constructor names in HeapParameterization.
Before the fix, both shared the name "BoxSeq" and Core type-checking
failed on the element-type mismatch. After the fix the name encodes the
element type (`BoxSeq_int`, `BoxSeq_bool`, ...). -/

#eval testLaurel
#strata
program Laurel;
composite Both {
  var a: Seq<int>
  var b: Seq<bool>
}

procedure touch(x: Both)
  opaque
  modifies x
{
  x#a := [1];
  x#b := [true]
};
#end
