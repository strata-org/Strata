/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for overloaded static procedures: multiple procedures may share a name as
long as their signatures don't conflict. Two signatures conflict when they have
the same arity and every parameter pair's types *overlap* (one is a consistent
subtype of the other in either direction), which is what guarantees no call can
match more than one overload. A call is resolved to the unique overload whose
parameter types accept the argument types.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Overloads that differ in a parameter type are accepted (no error) -/

#eval testLaurelResolution
#strata
program Laurel;
procedure foo(x: int) opaque { };
procedure foo(x: bool) opaque { };
#end

/-! ## Multi-parameter overloads select on *all* parameters

Both overloads have arity two, so `signaturesConflict` / `overloadAccepts` must
compare *every* parameter pair rather than passing vacuously after the first.
The parameter lists are swapped (`(int, bool)` vs `(bool, int)`), so no argument
tuple matches both, and `f(1, true)` must resolve to the first overload and
`f(true, 1)` to the second. Each overload returns a different type; picking the
wrong one (or none) would produce a type-mismatch diagnostic on the assignment. -/

#eval testLaurelResolution
#strata
program Laurel;
procedure f(x: int, y: bool) returns (r: int)
  opaque
  ensures r == x;
procedure f(x: bool, y: int) returns (r: bool)
  opaque
  ensures r == x;
procedure caller()
  opaque
{
  var a: int := f(1, true);
  var b: bool := f(true, 1)
};
#end

/-! ## Overloads that differ in arity are accepted (no error) -/

#eval testLaurelResolution
#strata
program Laurel;
procedure foo() opaque { };
procedure foo(x: int) opaque { };
procedure foo(x: int, y: int) opaque { };
#end

/-! ## A call resolves to the overload whose parameter type matches

Each overload returns a different type. If the call picked the wrong overload
(or failed to pick one), the assignment to the typed target would produce a
type-mismatch diagnostic. No diagnostics means selection worked. -/

#eval testLaurelResolution
#strata
program Laurel;
procedure f(x: int) returns (r: int)
  opaque
  ensures r == x;
procedure f(x: bool) returns (r: bool)
  opaque
  ensures r == x;
procedure caller()
  opaque
{
  var a: int := f(1);
  var b: bool := f(true)
};
#end

/-! ## Two overloads with identical signatures are still rejected

Overloading only relaxes the duplicate-name rule when signatures differ; two
procedures with the same name and the same parameter types still conflict. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(x: int) opaque { };
procedure foo(x: int) opaque { };
//        ^^^ error: Duplicate definition 'foo' is already defined in this scope
#end

/-! ## Overloads with subtype-related parameter types conflict

`Bottom` is a subtype of `Top`, so a value could satisfy either parameter and a
call would be ambiguous. The two signatures therefore conflict even though their
parameter types are not structurally equal. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Top {}
composite Bottom extends Top {}
procedure foo(x: Top) opaque { };
procedure foo(x: Bottom) opaque { };
//        ^^^ error: Duplicate definition 'foo' is already defined in this scope
#end

/-! ## A call with no matching overload is an error -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure f(x: int) opaque { };
procedure f(x: bool) opaque { };
procedure caller()
  opaque
{
  f("hello")
//^^^^^^^^^^ error: no overload of 'f' matches the argument types
};
#end

/-! ## An overloaded procedure name coexists with an unrelated procedure

Selecting among `f` overloads must not disturb resolution of other names. -/

#eval testLaurelResolution
#strata
program Laurel;
procedure f(x: int) returns (r: int)
  opaque
  ensures r == x;
procedure f(x: bool) returns (r: bool)
  opaque
  ensures r == x;
procedure g(x: int) returns (r: int)
  opaque
  ensures r == x;
procedure caller()
  opaque
{
  var a: int := f(1);
  var b: int := g(2)
};
#end

/-! ## A call matching more than one overload is ambiguous

Registration only rejects *pairwise* parameter overlap, which is not enough to
guarantee a unique match. In the diamond below `Top1` and `Top2` are unrelated
(neither is a subtype of the other), so `f(x: Top1)` and `f(x: Top2)` do not
conflict and both register. But `C extends Top1, Top2`, so a `C` value is a
consistent subtype of both parameter types and `f(c)` matches both overloads.
Rather than silently pick the first declaration, the call is reported as
ambiguous. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Top1 {}
composite Top2 {}
composite C extends Top1, Top2 {}
procedure f(x: Top1) returns (r: int) opaque { };
procedure f(x: Top2) returns (r: bool) opaque { };
procedure caller(c: C)
  opaque
{
  var a: int := f(c)
//              ^^^^ error: ambiguous call to 'f': the argument types match more than one overload
};
#end

/-! ## A procedure name colliding with a non-procedure definition is a duplicate

Overloading only relaxes the duplicate-name rule for two *procedures* with
non-conflicting signatures. A procedure sharing its name with a composite type
(any non-procedure definition) still collides — this exercises the
`nameTaken && existing.isEmpty` arm of `preRegisterStaticProcedure`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite foo {}
procedure foo(x: int) opaque { };
//        ^^^ error: Duplicate definition 'foo' is already defined in this scope
#end

/-! ## Overloads differing only in return type still conflict

Only parameter types participate in a signature. Two procedures with the same
name and the same parameter types conflict even when their return types differ,
so overloads cannot be distinguished by return type alone. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure f(x: int) returns (r: int) opaque { };
procedure f(x: int) returns (r: bool) opaque { };
//        ^ error: Duplicate definition 'f' is already defined in this scope
#end

/-! ## An `Unknown`-typed argument does not make an overloaded call ambiguous

When an argument synthesizes to `.Unknown` (here an untyped hole `<?>`), overload
selection is meaningless — `.Unknown` is a consistent subtype of every parameter
type, so every candidate would "accept" it. The call must therefore *not* report
a spurious ambiguity; the result is treated as `Unknown` and the only diagnostics
are those the argument itself raises (a bare hole raises none). Same behavior for
`f(undefined_id)` and `f(if b then <?> else <?>)`. -/

#eval testLaurelResolution
#strata
program Laurel;
procedure f(x: int) returns (r: int) opaque ensures r == x;
procedure f(x: bool) returns (r: bool) opaque ensures r == x;
procedure caller() opaque {
  var a: int := f(<?>)
};
#end

/-! ## External procedures cannot be overloaded -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure foo(x: int) external;
procedure foo(x: bool) opaque { };
//        ^^^ error: A set of procedure overloads must not have any external procedures
#end
