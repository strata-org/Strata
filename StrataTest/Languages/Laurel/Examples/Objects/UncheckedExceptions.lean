/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Modeling Java's runtime exceptions with the current exception feature set.

Laurel has no implicit exceptions, no first-class null, and no native arrays, so
a runtime failure that Java raises implicitly is modeled as an explicit
check-and-`throw` — exactly what a Java front-end would emit when it desugars the
operation. Each procedure below is the desugaring of a one-line Java method, and
each `onThrow (e) e is X ==> C` reads as an exceptional postcondition: "if the
procedure exits by throwing an `X`, then condition `C` held". That is the
property attached to each risky operation:

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

#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite NullPointerException extends Exception {}
composite Obj {
  f: int
}
procedure getF(xIsNull: bool, x: Obj)
  returns (r: int)
  throws Exception
  onThrow (e) e is NullPointerException ==> xIsNull
  opaque
  ensures r == x#f
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
#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite NullPointerException extends Exception {}
composite Obj {
  f: int
}
procedure getFBad(xIsNull: bool, x: Obj)
  returns (r: int)
  throws Exception
  onThrow (e) e is NullPointerException ==> !xIsNull
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  opaque
  ensures r == x#f
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
`a[i]` throws when `i < 0 || i >= a.length`. The contract records that the
result equals `a[i]` on the normal path, and that an escaping `IndexError`
implies the index was out of bounds. -/

#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite IndexError extends Exception {}
procedure get(a: Map int int, alen: int, i: int)
  returns (r: int)
  throws Exception
  onThrow (e) e is IndexError ==> (i < 0) || (i >= alen)
  opaque
  ensures r == select(a, i)
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

#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite ArithmeticException extends Exception {}
procedure div(a: int, b: int)
  returns (r: int)
  throws Exception
  onThrow (e) e is ArithmeticException ==> b == 0
  opaque
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

#eval testLaurel <|
#strata
program Laurel;
composite Exception extends BaseException {}
composite ClassCastException extends Exception {}
composite Base {}
composite Sub extends Base {
  v: int
}
procedure useAsSub(x: Base)
  returns (r: int)
  throws Exception
  onThrow (e) e is ClassCastException ==> !(x is Sub)
  opaque
{
  if !(x is Sub) then {
    var cce: ClassCastException := new ClassCastException;
    throw cce
  };
  r := (x as Sub)#v
};
#end
