/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
# Override postconditions

An override's postcondition is available through a base-typed receiver after dynamic
dispatch. The dispatcher must interpret the receiver at the overriding type so the
postcondition can read fields declared only by that type.
-/

/-! ## An override-only field is visible through the dispatcher

The first assertion fails if the override's postcondition is dropped. The annotated false
assertion guards against a contract that lets both values verify.
-/

#eval testLaurelVerification <|
#strata
program Laurel;

composite Shape {
  procedure area(self: Shape) returns (r: int)
    opaque
    ensures true;
}

composite Square extends Shape {
  var side: int

  procedure area(self: Square) returns (r: int)
    opaque
    ensures r == self#side
  {
    r := self#side
  };
}

procedure useOverride() opaque {
  var q: Square := new Square;
  q#side := 5;
  var s: Shape := q;
  var o: int := s#area();
  assert o == 5;
  assert o == 6
//^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## Generic overriding families use the applied branch type

For a generic family the receiver cast must be the applied `SquareBox<T>`, not the bare
generic head `SquareBox`; monomorphization later instantiates `T` with `int`.
-/

#eval testLaurelVerification <|
#strata
program Laurel;

composite ShapeBox<T> {
  procedure area(self: ShapeBox<T>) returns (r: int)
    opaque
    ensures true;
}

composite SquareBox<T> extends ShapeBox<T> {
  var side: int

  procedure area(self: SquareBox<T>) returns (r: int)
    opaque
    ensures r == self#side
  {
    r := self#side
  };
}

procedure useGenericOverride() opaque {
  var q: SquareBox<int> := new SquareBox<int>;
  q#side := 7;
  var s: ShapeBox<int> := q;
  var o: int := s#area();
  assert o == 7
};
#end

/-! ## A quantifier binder may share the base receiver's spelling

The base receiver is named `me`, while the override uses `self` and binds an unrelated
integer named `me`. Matching receiver references by resolved identity leaves that binder
alone instead of trying to cast it to `Child`.
-/

#eval testLaurelVerification <|
#strata
program Laurel;

composite Parent {
  procedure value(me: Parent) returns (r: int)
    opaque
    ensures true
  {
    r := 0
  };
}

composite Child extends Parent {
  procedure value(self: Child) returns (r: int)
    opaque
    ensures r >= 0
    ensures forall(me: int) => me + 0 == me
  {
    r := 0
  };
}

procedure quantifierBinderDoesNotShadowReceiver() opaque {
  var child: Child := new Child;
  var parent: Parent := child;
  var o: int := parent#value();
  assert o >= 0
};
#end
