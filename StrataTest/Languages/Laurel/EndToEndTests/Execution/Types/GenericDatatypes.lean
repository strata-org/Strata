/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Generic datatypes under concrete interpretation

`UnitTests/GenericDatatypeTest.lean` covers generic datatypes on the verification
path. Generic datatypes lower to native parametric Core sorts rather than being
monomorphized, so they are the part of user-level polymorphism that the concrete
interpreter can actually run — these tests drive them through `testLaurelExecution { skipCoreInterpreter := false }`
(translate + all lowering passes + verify + interpret).

Values are observed with a SELECTOR and then compared at a primitive type, rather
than by comparing two datatype values with `==`. The verification path pins
structural equality already; here the point is that the interpreter reconstructs the
right payload, and a selector read states that directly.

NB: `Bx`/`Lst` merely keep these programs short — `Box` would be legal. The generated boxing
datatype is `$Box`, in the reserved `$`-namespace, so user `datatype Box`, `datatype Box<T>` and
`composite Box` are all accepted; that is pinned by the source-compatibility cases in
`UnitTests/GenericCompositeTest.lean`. -/

#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }
datatype Lst<T> { Nil(), Cons(head: T, tail: Lst<T>) }

// ONE parametric datatype declaration used at two different instantiations in one
// program: each value must carry its own payload back out through the selector.
procedure testSelectorReadAtTwoInstantiations() entry opaque {
  var bi: Bx<int> := MkBx(5);
  assert Bx..v(bi) == 5;
  var bb: Bx<bool> := MkBx(true);
  assert Bx..v(bb) == true
};

// A recursive generic datatype, built two levels deep and walked back with
// selectors and constructor testers.
procedure testRecursive() entry opaque {
  var xs: Lst<int> := Cons(1, Cons(2, Nil()));
  assert Lst..isCons(xs);
  assert Lst..head(xs) == 1;
  var t: Lst<int> := Lst..tail(xs);
  assert Lst..head(t) == 2;
  assert Lst..isNil(Lst..tail(t))
};
#end

/-! ## The reconstructed payload is really observed

A wrong expected payload must FAIL, so the selector reads above are pinning an
evaluated value rather than passing vacuously. -/

#eval testLaurelExecution { skipCoreInterpreter := false }
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }
procedure caller() entry opaque {
  var bi: Bx<int> := MkBx(5);
  assert Bx..v(bi) == 6
//^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Two type parameters, each payload read back at its own type

`Pr<A, B>` mirrors the multi-parameter datatype the verification corpus covers. Both fields are
read back with selectors at different concrete types, so a reconstruction that confused the two
payloads — or applied one parameter's instantiation to the other — returns the wrong value here
rather than failing to typecheck. -/

#eval testLaurelExecution { skipCoreInterpreter := false } <|
#strata
program Laurel;
datatype Pr<A, B> { MkPr(a: A, b: B) }

procedure twoTypeParams() entry opaque {
  var p: Pr<int, bool> := MkPr(7, true);
  assert Pr..a(p) == 7;
  assert Pr..b(p) == true;
  var q: Pr<bool, int> := MkPr(false, 9);
  assert Pr..a(q) == false;
  assert Pr..b(q) == 9
};
#end

/-! ## The two-parameter payloads are really observed

As above, an annotation-free block passes only when the diagnostic set is empty — so without an
annotated failure a block would also pass if the interpreter produced nothing at all. This twin
asserts a wrong concrete value for one selector, which must FAIL. -/

#eval testLaurelExecution { skipCoreInterpreter := false } <|
#strata
program Laurel;
datatype Pr<A, B> { MkPr(a: A, b: B) }

procedure twoTypeParamsWrong() entry opaque {
  var p: Pr<int, bool> := MkPr(7, true);
  assert Pr..a(p) == 8
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Nested generic instantiation

`Bx<Bx<int>>` is a type argument that is itself a generic application, so it reaches the
`.Applied` arm of the box constructor/destructor naming — the arm whose `$Box..` prefix this
change renames. No other case here has a type argument that is itself applied. -/

#eval testLaurelExecution { skipCoreInterpreter := false } <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }

procedure testNested() entry opaque {
  var nested: Bx<Bx<int>> := MkBx(MkBx(42));
  assert Bx..v(Bx..v(nested)) == 42
};
#end

#eval testLaurelExecution { skipCoreInterpreter := false } <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }

procedure testNestedWrong() entry opaque {
  var nested: Bx<Bx<int>> := MkBx(MkBx(42));
  assert Bx..v(Bx..v(nested)) == 43
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

