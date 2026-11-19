/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Solved type arguments reach Core

A type argument that only the surrounding call or the expected type determines is recorded at
its call once solved, so the program lowers like a fully annotated one. -/

/-! ## An `if` writes the type argument it solves back into its branches

Here no enclosing call does it either: a precondition's `if`, and a body's last statement. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Box<T> { var v: T }
procedure mkBox<T>() returns (r: Box<T>) opaque;
procedure inPrecondition(c: bool, b: Box<int>) requires (if c then mkBox() else b)#v > 0 opaque { };
procedure inLastStatement(c: bool, b: Box<int>) opaque modifies * {
  var y := (if c then mkBox() else b)#v
};
#end

/-! ## A call writes what it solves into its arguments

`same` solves `mk`'s `T`, four calls down, to `int`; the arguments carry it, so the passes that read
the recorded type arguments see `int`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
datatype Opt<T> { Som(v: T), Non() }
procedure mk<T>() returns (r: T) opaque;
procedure idp<T>(x: T) returns (r: T) opaque;
procedure wrap<T>(x: T) returns (r: Opt<T>) opaque;
procedure same<T>(a: T, b: T) returns (r: bool) opaque;
procedure p() opaque { var b := same(wrap(wrap(idp(mk()))), Som(Som(1))) };
#end

/-! ## A destructor's receiver solves a generic call there

`LowerComposite` compares composites through their `Composite..ref!`, so `ct == mk()` puts `mk()`
at a destructor's receiver, which is that datatype. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Cat { }
procedure mk<T>() returns (r: T) opaque;
procedure p(ct: Cat) opaque { var b := ct == mk(); var c := mk() == ct };
#end

/-! ## A destructor's receiver is solved whatever a pass makes of it

Contracts wraps `mkPre(1)` in a block, and `LowerComposite` makes `ct == (if c then ct else mk())`
a destructor read of an `if`; the receiver is solved at the destructor's datatype all the same, and
the precondition is still checked. -/

#eval testLaurelVerification <|
#strata
program Laurel;
datatype D { MkD(ref: int), NoD() }
composite Cat { }
procedure mk<T>() returns (r: T) opaque;
procedure mkPre<T>(n: int) returns (r: T) requires n > 0 opaque;
procedure throughContracts() opaque { var x := D..ref!(mkPre(1)) };
procedure preconditionStillChecked() opaque {
  var x := D..ref!(mkPre(0))
//                 ^^^^^^^^ error: precondition does not hold
};
procedure throughAnIf(c: bool, d: D) opaque { var x := D..ref!(if c then d else mk()) };
procedure comparedThroughAnIf(c: bool, ct: Cat) opaque {
  assert ct == (if c then ct else mk())
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## An ambiguous diamond is reported at the call

With no expected type to pick one, `d` reaches `Base` at two instantiations. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Base<T> { var v: T }
composite L extends Base<int> { }
composite R extends Base<bool> { }
composite D extends L, R { }
procedure getV<T>(b: Base<T>) returns (r: T) opaque;
procedure p(d: D) opaque {
  getV(d)
//     ^ error: ambiguous type argument for inherited method: 'D' reaches 'Base' at both 'Base<int>' and 'Base<bool>', so the type argument cannot be determined. Upcast the receiver to the intended one (e.g. `var b: Base<int> := …`) to disambiguate.
};
#end

/-! ## An unsolved type argument is reported, not lowered

A call whose argument is a hole records no instantiation, so the passes before hole typing read
its callee's type parameters as unknown, here through the callee's `throws`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure g<T>(x: T) returns (r: T) throws (e: T) opaque;
procedure p() opaque { try { var y: int := g(<?>) } catch c { assert true } };
//                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: the `catch` binding of this `try` cannot be typed: the body throws a value of unknown type
#end
