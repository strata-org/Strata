/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! `Array<T>` is allowed as a datatype constructor argument. Because an array
is a heap reference, a datatype that stores one compares by reference on
that field: two datatype values built from the *same* array are equal,
while two values built from *different* arrays are not — even if those
arrays have identical contents.

Same array in both wrappers ⇒ the datatype values are equal. -/

#eval testLaurel
#strata
program Laurel;
datatype Wrapped {
  Wrap(arr: Array<int>)
}

procedure cmp()
  opaque
{
  var a: Array<int> := [1, 2, 3];
  var w1: Wrapped := Wrap(a);
  var w2: Wrapped := Wrap(a);
  assert w1 == w2
};
#end

/-! Different arrays, even with identical contents, are distinct references, so
the wrapping datatype values are not equal. -/

#eval testLaurel
#strata
program Laurel;
datatype Wrapped {
  Wrap(arr: Array<int>)
}

procedure cmp()
  opaque
{
  var a1: Array<int> := [1, 2, 3];
  var a2: Array<int> := [1, 2, 3];
  var w1: Wrapped := Wrap(a1);
  var w2: Wrapped := Wrap(a2);
  assert w1 != w2
};
#end

/-! Contrast: a `Seq<int>` constructor argument has value semantics — two
datatype values built from equal sequences are equal regardless of how the
sequences were constructed. -/

#eval testLaurel
#strata
program Laurel;
datatype WrappedSeq {
  WrapSeq(items: Seq<int>)
}

procedure constructAndCompare()
  opaque
{
  var s1: Seq<int> := [1, 2, 3];
  var s2: Seq<int> := [1, 2, 3];
  var w1: WrappedSeq := WrapSeq(s1);
  var w2: WrappedSeq := WrapSeq(s2);
  assert w1 == w2
};
#end
