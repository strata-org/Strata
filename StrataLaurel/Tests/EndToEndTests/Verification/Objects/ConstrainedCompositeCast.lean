/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # `is` and `as` against a constrained type over a composite

`x is PB` tests `PB`'s whole constraint, the composite's type tag included, and `x as PB`
requires it. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box { var n: int }
constrained PB = b: Box where true witness <??>

procedure castAndTest(x: Box) opaque { var y: PB := x as PB; assert x is PB };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box { var n: int }
constrained PositiveBox = b: Box where b#n > 0 witness <??>
//                                                     ^^^^ error: assertion does not hold

procedure guardedCast(x: Box) opaque {
  if (x#n > 0) then { var y: PositiveBox := x as PositiveBox; assert y is PositiveBox } else { }
};
procedure unguardedCast(x: Box) opaque { var y: PositiveBox := x as PositiveBox };
//                                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
//                                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
procedure testIsTheConstraint(x: Box) opaque { assert x is PositiveBox };
//                                             ^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var v: T }
constrained CB = b: Box<int> where true witness <??>

procedure genericCastAndTest(x: Box<int>) opaque { var y: CB := x as CB; assert x is CB };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { var name: int }
composite Cat extends Animal { var lives: int }
constrained PD = d: Dog where true witness <??>

procedure ancestorIsPD(a: Animal) opaque { assert a is PD };
//                                         ^^^^^^^^^^^^^^ error: assertion does not hold
procedure ancestorAsPD(a: Animal) opaque { var p: PD := a as PD };
//                                         ^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
//                                         ^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
procedure catIsNotPD() opaque { var c: Animal := new Cat; assert !(c is PD) };
procedure dogIsPD() opaque { var d: Animal := new Dog; assert d is PD; var p: PD := d as PD };
procedure dogParamIsPD(d: Dog) opaque { assert d is PD };
#end
