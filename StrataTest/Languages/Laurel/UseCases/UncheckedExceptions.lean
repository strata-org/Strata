/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Modeling Java's runtime exceptions with the current exception feature set.

A *use case* rather than a semantics test (hence `UseCases/`, see the test README):
it claims that the pattern a Java front end needs is expressible and reads
reasonably, not that a particular construct behaves a particular way. The rules for
the individual constructs live under `EndToEndTests/Execution/Exceptions` and
`EndToEndTests/Resolution/Exceptions`.

Laurel has no implicit exceptions, no first-class null, and no native arrays, so
a runtime failure that Java raises implicitly is modeled as an explicit
check-and-`throw` — exactly what a Java front-end would emit when it desugars the
operation. Each procedure below is the desugaring of a one-line Java method, and each
`throwsOn C { ensures e is X }` reads as the behavior case "when `C` holds on entry the
procedure throws, and what it throws is an `X`". With the exhaustiveness claim over the
cases, that also gives the converse — throwing implies `C` held — so the "exactly when"
in the table below is stated in both directions:

  * NullPointerException        e.f            thrown exactly when the reference is null
  * IndexOutOfBoundsException   a[i]           thrown exactly when the index is out of bounds
  * ArithmeticException         a / b          thrown exactly when the divisor is zero
  * ClassCastException          (Sub) x        thrown exactly when x is not a Sub

Conventions forced by the current feature set: nullness/arrays are modeled
explicitly (a boolean flag for null, a `Map int int` + length for an array), and
`throws Exception` is the coarse declaration standing in for these otherwise
undeclared runtime exceptions.
-/

/-! ## NullPointerException — `x.f`

Java:
    int getF(Obj x) { return x.f; }
`x.f` throws a `NullPointerException` when `x` is null. The contract records
that the result equals `x.f` on the normal path, and that an escaping
`NullPointerException` implies `x` was null. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Exception {}
composite NullPointerException extends Exception {}
composite Obj {
  f: int
}
procedure getF(xIsNull: bool, x: Obj)
  returns (r: int)
  throws (e: Exception)
  opaque
  ensures r == x#f
  throwsOn xIsNull {
    ensures e is NullPointerException
  }
{
  if xIsNull then {
    var npe: NullPointerException := new NullPointerException;
    throw npe
  };
  r := x#f
};
#end

-- Negative: the contract claims an escaping NPE implies the reference was
-- NON-null, contradicting the guard, so it cannot be proved.
#eval testLaurelVerification <|
#strata
program Laurel;
composite Exception {}
composite NullPointerException extends Exception {}
composite Obj {
  f: int
}
procedure getFBad(xIsNull: bool, x: Obj)
  returns (r: int)
  throws (e: Exception)
  opaque
  ensures r == x#f
  throwsOn xIsNull {
    ensures e is NullPointerException ==> !xIsNull
//          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  }
{
  if xIsNull then {
    var npe: NullPointerException := new NullPointerException;
    throw npe
  };
  r := x#f
};
#end

/-! ## IndexOutOfBoundsException — `a[i]`

Java:
    int get(int[] a, int i) { return a[i]; }
`a[i]` throws when `i < 0 || i >= a.length`. One `throwsOn` case states both
directions a caller needs:
  * forwards, from the guard: "if the index is out of bounds on entry, it *does*
    throw an `IndexError`" — so a caller with a bad index knows the call throws;
  * backwards, from the exhaustiveness claim over the cases: "if it threw, the index
    was out of bounds" — so a caller that caught the exception can reason back, and one
    with an in-bounds index knows the call cannot have thrown. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Exception {}
composite IndexError extends Exception {}
procedure get(a: Map int int, alen: int, i: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  ensures r == select(a, i)
  throwsOn (i < 0) || (i >= alen) {
    ensures e is IndexError
  }
{
  if (i < 0) || (i >= alen) then {
    var ei: IndexError := new IndexError;
    throw ei
  };
  r := select(a, i)
};
#end

/-! ## ArithmeticException — `a / b`

Java:
    int div(int a, int b) { return a / b; }
`a / b` throws when `b == 0`; the contract records that an escaping
`ArithmeticException` implies the divisor was zero. The guard makes the division
provably safe on the normal path (it also discharges Laurel's built-in
division-by-zero obligation). A postcondition mentioning `a / b` directly is
avoided, since evaluating a partial operation in a contract raises the safety
obligation outside the guard's scope. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Exception {}
composite ArithmeticException extends Exception {}
procedure div(a: int, b: int)
  returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn b == 0 {
    ensures e is ArithmeticException
  }
{
  if b == 0 then {
    var ae: ArithmeticException := new ArithmeticException;
    throw ae
  };
  r := a / b
};
#end

/-! ## ClassCastException — `(Sub) x`

Java:
    int useAsSub(Base x) { return ((Sub) x).v; }
The cast `(Sub) x` throws when `x` is not actually a `Sub`; the contract records
that an escaping `ClassCastException` implies `x` was not a `Sub`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Exception {}
composite ClassCastException extends Exception {}
composite Base {}
composite Sub extends Base {
  v: int
}
procedure useAsSub(x: Base)
  returns (r: int)
  throws (e: Exception)
  opaque
  throwsOn !(x is Sub) {
    ensures e is ClassCastException
  }
{
  if !(x is Sub) then {
    var cce: ClassCastException := new ClassCastException;
    throw cce
  };
  r := (x as Sub)#v
};
#end
