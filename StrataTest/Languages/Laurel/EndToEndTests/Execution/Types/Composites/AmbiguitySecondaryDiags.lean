/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/- An ambiguous inherited call must report the ambiguity and nothing derived from a
   guessed callee. Candidates may differ in arity, parameter type and return type, so
   any check against one contradicts the ambiguity; a propagated return type is worst,
   since the enclosing mismatch hides the ambiguity altogether (S3). Errors independent
   of the callee must still surface, so an ambiguous call does not mask a bad argument
   (S4). The same-signature diamond is InheritedCallProbes P2. -/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! S1: candidates disagree on ARITY (LS.m takes only self; RS.m takes self + n).
    Must not add "expects 0 argument(s) but 1 were provided". -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite LS {
  procedure m(self: LS) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite RS {
  procedure m(self: RS, n: int) returns (r: int)
    opaque ensures r == n { return n };
}
composite DS extends LS, RS { }
procedure goS(d: DS)
  opaque
{
  var x: int := d#m(42);
//              ^^^^^^^ error: call to 'm' is ambiguous: 'DS' inherits it from the unrelated types LS, RS
  assert x == 1
};
#end

/-! S2: candidates disagree on PARAMETER TYPE (int vs bool).
    Must not add "expected 'bool', got 'int'". -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite LT {
  procedure m(self: LT, a: int) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite RT {
  procedure m(self: RT, a: bool) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite DT extends LT, RT { }
procedure goT(d: DT)
  opaque
{
  var x: int := d#m(42);
//              ^^^^^^^ error: call to 'm' is ambiguous: 'DT' inherits it from the unrelated types LT, RT
  assert x == 1
};
#end

/-! S3: candidates disagree on RETURN type (int vs bool). No candidate's result type
    may propagate: the enclosing expression would report "expected 'bool', got
    'int'" instead of the ambiguity, hiding the cause. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite LR {
  procedure m(self: LR) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite RR {
  procedure m(self: RR) returns (r: bool)
    opaque ensures r == true { return true };
}
composite DR extends LR, RR { }
procedure goR(d: DR)
  opaque
{
  var x: bool := d#m();
//               ^^^^^ error: call to 'm' is ambiguous: 'DR' inherits it from the unrelated types LR, RR
  assert x == true
};
#end

/-! S4: a genuine error INSIDE an argument of an ambiguous call is still reported.
    Arguments are resolved against `Unknown` rather than skipped, so the ambiguity
    does not mask an undefined name. -/
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite LU {
  procedure m(self: LU, a: int) returns (r: int)
    opaque ensures r == 1 { return 1 };
}
composite RU {
  procedure m(self: RU, a: bool) returns (r: int)
    opaque ensures r == 2 { return 2 };
}
composite DU extends LU, RU { }
procedure goU(d: DU)
  opaque
{
  var x: int := d#m(nosuchVar);
//              ^^^^^^^^^^^^^^ error: call to 'm' is ambiguous: 'DU' inherits it from the unrelated types LU, RU
//                  ^^^^^^^^^ error: not defined
  assert x == 1
};
#end
