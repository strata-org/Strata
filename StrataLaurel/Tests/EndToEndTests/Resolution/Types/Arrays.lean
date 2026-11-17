/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! Resolution types the array constructs: the array of an element must have an array type,
an index must be an `int`, and `#length()` is an array's length only on an array. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure main()
  entry
  opaque
  modifies *
{
  var n: int := 3;
  var b: bool := true;
  var a: Array<int> := new Array<int>(2);
  var x: int := n[0];
//              ^ error: expected an array type, got 'int'
  var y: int := n#length();
//              ^^^^^^^^^^ error: 'length' is called with '#' on a non-composite receiver; instance-method calls require a composite receiver
  var z: int := a[b]
//                ^ error: expected 'int', got 'bool'
};
#end

/-! Resolution resolves the element type of an array type. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure f(a: Array<Nope>)
//                   ^^^^ error: 'Nope' is not defined
  opaque
{
};

procedure main()
  entry
  opaque
{
};
#end

/-! A call infers a type parameter that only an array type mentions. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure first<T>(a: Array<T>) returns (r: T)
  opaque
{
  r := a[0]
};

procedure main()
  entry
  opaque
  modifies *
{
  var a: Array<int> := new Array<int>(1);
  var x: int := first(a);
  assert x == 0
};
#end

/-! An array element cannot be the target of `++`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure main()
  entry
  opaque
  modifies *
{
  var a: Array<int> := new Array<int>(1);
  a[0]++
//^^^^ error: an array element cannot be incremented or decremented in place
};
#end

/-! An array construct in the initializer of a global is a heap effect, which a global's
initializer may not have. -/

#eval testLaurelResolution <|
#strata
program Laurel;
var g: Array<int> := new Array<int>(3)
//                   ^^^^^^^^^^^^^^^^^ error: the initializer of file-scope global 'g' must be effect-free (no assignments or declarations, no allocation with 'new', no field reads, and no calls to heap-reading or heap-writing procedures)

procedure main()
  entry
  opaque
{
  assert true
};
#end
