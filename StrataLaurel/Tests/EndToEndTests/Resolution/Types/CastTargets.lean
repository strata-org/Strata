/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `as` / `is` reject a target that cannot be a composite

Both operators against both reasons, plus the alias that makes the type-parameter reason's subject
differ from what it resolves to, and a composite target as the control that must stay accepted. The
wording differs by reason because the claims differ: `int` genuinely is not a composite, whereas a
type parameter might be one and is refused only because that cannot be decided here.
The remaining non-composite target kinds — a datatype and a constrained type — and the
generic-instantiation rule are in `TypeTestAndCastTargets.lean`; these pin what each reason
says and where it points. -/

#eval testLaurelResolution <|
#strata
program Laurel;
type Ident<T> = T
composite Animal { var legs: int }
composite Dog extends Animal { var breed: int }
procedure downToDog(x: Animal) returns (r: Dog) {
  r := x as Dog
};
procedure castToNonComposite(x: int) {
  var r: int := x as int
//                   ^^^ error: 'as' is only supported for composite (class) types; 'int' is not a composite type
};
procedure testNonComposite(x: int) {
  var r: bool := x is int
//                    ^^^ error: 'is' is only supported for composite (class) types; 'int' is not a composite type
};
procedure castToTypeParameter<T>(x: T) {
  var r: T := x as T
//                 ^ error: 'as' is only supported for composite (class) types; 'T' resolves to a type parameter, which has no declared bound and so may be instantiated at a non-composite type
};
procedure testTypeParameter<T>(x: T) {
  var r: bool := x is T
//                    ^ error: 'is' is only supported for composite (class) types; 'T' resolves to a type parameter, which has no declared bound and so may be instantiated at a non-composite type
};
procedure castToAliasOfTypeParameter<T>(x: T) {
  var r: T := x as Ident<T>
//                 ^^^^^^^^ error: 'as' is only supported for composite (class) types; 'Ident<T>' resolves to a type parameter, which has no declared bound and so may be instantiated at a non-composite type
};
#end
