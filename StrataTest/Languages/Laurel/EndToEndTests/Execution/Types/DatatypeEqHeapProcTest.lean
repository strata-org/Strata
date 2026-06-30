/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Regression: datatype `==` / `!=` inside a heap-writing procedure

`HeapParameterization` rewrites `==`/`!=` on heap references into a
`Composite..ref!` reference comparison. The operand-type check used
`.UserDefined _`, which matches BOTH composites (heap references, where
`ref!` is correct) AND datatypes (values, where `ref!` is wrong: it would
unify a datatype value against the `Composite` (= int) type).

The bug only surfaces inside a procedure that writes the heap, because only
then does the heap-rewriting pass descend into the body and reach the `==`
arm. Allocating a composite (`new C`) is enough to make the procedure a heap
writer, so a datatype comparison sitting next to it used to fail Core type
checking with:

  Impossible to unify (arrow Composite int) with (arrow <Datatype> ...)

The fix guards the `ref!` rewrite on `!isDatatype`, letting datatype
equality fall through to structural comparison. These programs verify
cleanly with the fix and fail Core type checking without it.

A datatype compared with `==` inside a heap-writing procedure. The `new C`
makes `cmp` a heap writer; the datatype values must still compare
structurally rather than being wrongly reference-compared. -/

#eval testLaurel
#strata
program Laurel;
composite C { var x: int }
datatype Pair { MkPair(a: int, b: int) }

procedure cmp()
  opaque
{
  var c: C := new C;
  var p1: Pair := MkPair(1, 2);
  var p2: Pair := MkPair(1, 2);
  assert p1 == p2
};
#end

/-! Same shape with `!=`: two structurally-distinct datatype values are not
equal, so the inequality holds. Exercises the `.Neq` arm of the same fix. -/

#eval testLaurel
#strata
program Laurel;
composite C { var x: int }
datatype Pair { MkPair(a: int, b: int) }

procedure cmp()
  opaque
{
  var c: C := new C;
  var p1: Pair := MkPair(1, 2);
  var p2: Pair := MkPair(3, 4);
  assert p1 != p2
};
#end
