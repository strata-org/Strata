/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Inferred `throws` clauses: `throws (e: inferred)` and `throws (e: T inferred)`.

The thrown type is the join of the declared type (if any) and every exception type
that may escape the body uncaught, computed together for all inferred procedures so
that a call to an inferred procedure contributes the type inferred for it. Once
inferred the clause is an ordinary `throws`, so callers are checked exactly as in
`ThrowsClause.lean` and `UncaughtExceptions.lean`: a caller that neither catches nor
throws must prove the call does not throw.

When nothing escapes, the clause is dropped and the procedure declares no `throws`.

Each accepted program also runs on both interpreters, through an `entry` that takes
the throwing path and handles the exception. The entries assert nothing about the
result: the callees are opaque, so the verifier could not prove it. Two kinds of
block skip the interpreters: those expecting a verifier-only diagnostic ("could
not be proved"), which a single concrete run cannot produce, and those whose
program Laurel rejects, which cannot run at all.
-/

/-! ## Inferred from a `throw` -/

-- `div` throws `ArithError` when `b == 0`; with an inferred clause that is its
-- `throws` type, so the throw is no longer an uncaught-exception failure in `div`,
-- and `caller` handles it.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ArithError {}
procedure div(a: int, b: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  if b == 0 then {
    var x: ArithError := new ArithError;
    throw x
  };
  r := a / b
};
procedure caller(x: int) returns (r: int)
  opaque
{
  try {
    r := div(10, x)
  } catch c when c is ArithError {
    r := 0
  }
};
procedure main() entry opaque modifies *
{
  var r: int := caller(0)
};
#end

-- A caller that does not catch the inferred exception, and declares no `throws`,
-- must prove the call does not throw, which `div` gives it no way to do.
-- Verifier-only: the diagnostic ranges over all inputs.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite ArithError {}
procedure div(a: int, b: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  if b == 0 then {
    var x: ArithError := new ArithError;
    throw x
  };
  r := a / b
};
procedure caller(x: int) returns (r: int)
  opaque
{
  r := div(10, x)
//     ^^^^^^^^^^ error: call does not throw an uncaught 'ArithError' does not hold
};
#end

/-! ## Inferred through calls -/

-- `middle` neither throws nor catches; its type comes from `div`'s inferred type.
-- `top` is recursive, so the types are a fixpoint over the call graph.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ArithError {}
procedure div(a: int, b: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  if b == 0 then {
    var x: ArithError := new ArithError;
    throw x
  };
  r := a / b
};
procedure middle(x: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  r := div(10, x)
};
procedure top(n: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  if n > 0 then {
    r := top(n - 1)
  } else {
    r := middle(n)
  }
};
procedure caller(n: int) returns (r: int)
  opaque
{
  try {
    r := top(n)
  } catch c when c is ArithError {
    r := 0
  }
};
procedure main() entry opaque modifies *
{
  var r: int := caller(0)
};
#end

-- An exception that is caught inside the body does not escape, so nothing is
-- inferred and the clause is dropped: a caller needs no `try`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ArithError {}
procedure safeDiv(a: int, b: int) returns (r: int)
  throws (e: inferred)
  opaque
  ensures b == 0 ==> r == 0
{
  try {
    if b == 0 then {
      var x: ArithError := new ArithError;
      throw x
    };
    r := a / b
  } catch c {
    r := 0
  }
};
procedure main() entry opaque modifies *
{
  var r: int := safeDiv(1, 0)
};
#end

-- A rethrow from a handler around an inferred callee contributes the callee's
-- inferred type: the `catch` binding is typed from it, so `rethrower` is inferred
-- as `throws (e: ArithError)` too.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ArithError {}
procedure div(b: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  if b == 0 then {
    var x: ArithError := new ArithError;
    throw x
  };
  r := 10 / b
};
procedure rethrower(b: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  try {
    r := div(b)
  } catch c {
    throw c
  }
};
procedure main() entry opaque modifies *
{
  var r: int := 0;
  try {
    r := rethrower(0)
  } catch c when c is ArithError {
    r := 5
  }
};
#end

-- Instance procedures are inferred too: `risky` gets `throws (e: ArithError)`, so
-- a caller that declares an unrelated `throws` type is rejected.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite ArithError {}
composite ParseError {}
composite Calc {
  var total: int
  procedure risky(self: Calc)
    throws (e: inferred)
    opaque
  {
    var x: ArithError := new ArithError;
    throw x
  };
}
procedure caller()
  throws (e: ParseError)
  opaque
{
  var c: Calc := new Calc;
  c#risky()
//^^^^^^^^^ error: procedure 'caller' may throw 'ArithError', which is not a subtype of its declared `throws` type 'ParseError'
};
#end

/-! ## Joining several exception types -/

-- Two sibling exceptions join to their common supertype `Exc`, which a caller can
-- catch.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exc {}
composite ArithError extends Exc {}
composite IndexError extends Exc {}
procedure risky(x: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  if x == 0 then {
    var a: ArithError := new ArithError;
    throw a
  };
  if x < 0 then {
    var i: IndexError := new IndexError;
    throw i
  };
  r := x
};
procedure caller(x: int) returns (r: int)
  opaque
{
  try {
    r := risky(x)
  } catch c when c is Exc {
    r := 0
  }
};
procedure main() entry opaque modifies *
{
  var r: int := caller(-1)
};
#end

-- A declared type is kept and joined with what is inferred: `Exc` covers the
-- inferred `ArithError`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exc {}
composite ArithError extends Exc {}
procedure risky(x: int) returns (r: int)
  throws (e: Exc inferred)
  opaque
{
  if x == 0 then {
    var a: ArithError := new ArithError;
    throw a
  };
  r := x
};
procedure caller(x: int) returns (r: int)
  opaque
{
  try {
    r := risky(x)
  } catch c when c is Exc {
    r := 0
  }
};
procedure main() entry opaque modifies *
{
  var r: int := caller(0)
};
#end

-- The declared part is a lower bound, not an upper bound: an escape outside it
-- widens the inferred type (`ParseError` and `ArithError` join at `Exc`) instead
-- of being rejected.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exc {}
composite ArithError extends Exc {}
composite ParseError extends Exc {}
procedure risky(x: int) returns (r: int)
  throws (e: ParseError inferred)
  opaque
{
  if x == 0 then {
    var a: ArithError := new ArithError;
    throw a
  };
  r := x
};
procedure caller(x: int) returns (r: int)
  opaque
{
  try {
    r := risky(x)
  } catch c when c is Exc {
    r := 0
  }
};
procedure main() entry opaque modifies *
{
  var r: int := caller(0)
};
#end

-- A handler can read the fields of an exception thrown by an inferred callee: the
-- catch binding gets the inferred type, as it would with a declared one.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ArithError { var code: int }
procedure div(b: int) returns (r: int)
  throws (e: inferred)
  opaque
{
  if b == 0 then {
    var x: ArithError := new ArithError;
    x#code := 7;
    throw x
  };
  r := 10 / b
};
procedure main() entry opaque modifies *
{
  var r: int := 0;
  try {
    r := div(0)
  } catch c {
    r := c#code
  }
};
#end

/-! ## Overriding families -/

-- Each member of an overriding family is inferred from its own body. `Base.m` may
-- throw `ArithError` or `ParseError`, so it gets their join `Exc`. An override may
-- throw less than the method it overrides: `Sub.m` gets `ArithError`, and
-- `Quiet.m` lets nothing escape, so it has no `throws`. A call through `Base` may
-- throw `Exc`.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Exc {}
composite ArithError extends Exc {}
composite ParseError extends Exc {}
composite Base {
  procedure m(self: Base, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    if x == 0 then {
      var a: ArithError := new ArithError;
      throw a
    };
    if x < 0 then {
      var p: ParseError := new ParseError;
      throw p
    };
    r := 0
  };
}
composite Sub extends Base {
  procedure m(self: Sub, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    if x == 0 then {
      var a: ArithError := new ArithError;
      throw a
    };
    r := 1
  };
}
composite Quiet extends Base {
  procedure m(self: Quiet, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    r := 2
  };
}
procedure caller(b: Base, x: int) returns (r: int)
  throws (e: Exc)
  opaque
{
  r := b#m(x)
};
procedure main() entry opaque modifies *
{
  var s: Sub := new Sub;
  var r: int := 0;
  try {
    r := caller(s, 0)
  } catch c when c is Exc {
    r := 5
  };
  var q: Quiet := new Quiet;
  try {
    r := caller(q, 0)
  } catch c when c is Exc {
    r := 6
  }
};
#end

-- An override is capped at the type of the method it overrides, so a call through
-- the base never sees more than the base's type. `Base.m` lets nothing escape, so
-- `Sub.m` may not throw at all, and its `throw` is reported as uncaught. A call
-- through `Base` needs no handler. Verifier-only, like the uncaught call above.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite ArithError {}
composite Base {
  procedure m(self: Base, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    r := 0
  };
}
composite Sub extends Base {
  procedure m(self: Sub, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    if x == 0 then {
      var a: ArithError := new ArithError;
      throw a
//    ^^^^^^^ error: uncaught exception 'ArithError' is not thrown does not hold
    };
    r := 1
  };
}
procedure unhandled(b: Base, x: int) returns (r: int)
  opaque
{
  r := b#m(x)
};
#end

-- What an override lets escape within the cap stays in its `throws`; only the rest
-- is reported. `Sub.m` is capped at `ArithError`: its `ParseError` throw is
-- reported, and so is a call that may throw the wider `Exc`, unless the exception
-- is an `ArithError`.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exc {}
composite ArithError extends Exc {}
composite ParseError extends Exc {}
procedure risky(x: int) returns (r: int)
  throws (e: Exc)
  opaque
{
  if x == 1 then {
    var a: Exc := new Exc;
    throw a
  };
  r := x
};
composite Base {
  procedure m(self: Base, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    if x == 0 then {
      var a: ArithError := new ArithError;
      throw a
    };
    r := 0
  };
}
composite Sub extends Base {
  procedure m(self: Sub, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    if x == 0 then {
      var a: ArithError := new ArithError;
      throw a
    };
    if x < 0 then {
      var p: ParseError := new ParseError;
      throw p
//    ^^^^^^^ error: uncaught exception 'ParseError' is not thrown does not hold
    };
    r := risky(x)
//       ^^^^^^^^ error: call does not throw an uncaught 'Exc' does not hold
  };
}
#end

-- The cap applies inside a `try` that only has a `finally`, which passes on what
-- its body throws: `Sub.m`'s `ParseError` is reported there too, and so is a
-- `ParseError` that escapes a nested `try` whose handler does not catch it.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exc {}
composite ArithError extends Exc {}
composite ParseError extends Exc {}
composite Base {
  procedure m(self: Base, x: int) returns (r: int)
    throws (e: ArithError)
    opaque;
}
composite Sub extends Base {
  procedure m(self: Sub, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    r := 1;
    if x < 0 then {
      try {
        var p: ParseError := new ParseError;
        throw p
//      ^^^^^^^ error: uncaught exception 'ParseError' is not thrown does not hold
      } finally {
        r := 9
      }
    };
    if x == 0 then {
      try {
        try {
//      ^ error: an exception escaping this `try` is a 'ArithError' does not hold
          var q: ParseError := new ParseError;
          throw q
        } catch c when c is ArithError {
          r := 2
        }
      } finally {
        r := 8
      }
    }
  };
}
#end

-- A method without a body has nothing to infer its type from, and taking it from
-- its overrides would make its contract depend on them, so it must declare it.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Base {
  procedure m(self: Base, x: int) returns (r: int)
//          ^ error: cannot infer the `throws` type of procedure 'Base.m': it has no body. Declare the `throws` type instead.
    throws (e: inferred)
    opaque;
}
#end

-- A declared type on a method without a body is the cap for its overrides.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ArithError {}
composite Base {
  procedure m(self: Base, x: int) returns (r: int)
    throws (e: ArithError)
    opaque;
}
composite Sub extends Base {
  procedure m(self: Sub, x: int) returns (r: int)
    throws (e: inferred)
    opaque
  {
    if x == 0 then {
      var a: ArithError := new ArithError;
      throw a
    };
    r := 1
  };
}
procedure callThrough(b: Base, x: int) returns (r: int)
  throws (e: ArithError)
  opaque
{
  r := b#m(x)
};
procedure main() entry opaque modifies *
{
  var s: Sub := new Sub;
  var r: int := 0;
  try {
    r := callThrough(s, 0)
  } catch c when c is ArithError {
    r := 5
  }
};
#end

/-! ## Inference failures -/

-- Unrelated exception types have no common supertype, so no `throws` type exists.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite ArithError {}
composite ParseError {}
procedure mixed(x: int) returns (r: int)
//        ^^^^^ error: cannot infer the `throws` type of procedure 'mixed': the exceptions that may escape it ('ArithError', 'ParseError') have no common supertype
  throws (e: inferred)
  opaque
{
  if x == 0 then {
    var a: ArithError := new ArithError;
    throw a
  };
  if x < 0 then {
    var p: ParseError := new ParseError;
    throw p
  };
  r := x
};
#end

-- The same with `throwsOn` cases: only the missing join is reported, not that
-- nothing can escape.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite ArithError {}
composite ParseError {}
procedure mixed(x: int) returns (r: int)
//        ^^^^^ error: cannot infer the `throws` type of procedure 'mixed': the exceptions that may escape it ('ArithError', 'ParseError') have no common supertype
  throws (e: inferred)
  opaque
  throwsOn x < 0 {
    ensures true
  }
{
  if x == 0 then {
    var a: ArithError := new ArithError;
    throw a
  };
  if x < 0 then {
    var p: ParseError := new ParseError;
    throw p
  };
  r := x
};
#end

-- `throwsOn` cases need a `throws` type, and nothing escapes this body.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure neverThrows(x: int) returns (r: int)
//        ^^^^^^^^^^^ error: procedure 'neverThrows' states `throwsOn` cases, but no exception can escape its body, so it has no inferred `throws` type
  throws (e: inferred)
  opaque
  throwsOn x < 0 {
    ensures true
  }
{
  r := x
};
#end

-- A thrown value of a type-variable type is not concrete until monomorphization,
-- so no type can be inferred for it.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure thrower<T>(x: T)
//        ^^^^^^^ error: cannot infer the `throws` type of procedure 'thrower': the exception type 'T' that may escape it mentions a type variable. Declare the `throws` type instead.
  throws (e: inferred)
  opaque
{
  throw x
};
#end

-- A call to a generic callee escapes the callee's `throws` type at the call's type
-- arguments: `thrower(a)` at `a : ArithError` throws `ArithError`, so `caller` is
-- inferred as `throws (e: ArithError)` and `main` handles it.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite ArithError {}
procedure thrower<T>(x: T)
  throws (e: T)
  opaque
{
  throw x
};
procedure caller()
  throws (e: inferred)
  opaque
{
  var a: ArithError := new ArithError;
  thrower(a)
};
procedure main() entry opaque modifies *
{
  try {
    caller()
  } catch c when c is ArithError {
  }
};
#end

-- `throwsOn` cases are stated for the declared type. An escape outside it would
-- widen the type, and the cases' binding with it (`e#line` would no longer
-- resolve), so that is an error.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Exc {}
composite ArithError extends Exc {}
composite ParseError extends Exc { var line: int }
procedure risky(x: int) returns (r: int)
//        ^^^^^ error: cannot infer the `throws` type of procedure 'risky': its `throwsOn` cases are stated for the declared type 'ParseError', but other exceptions may escape too, which would widen the type to 'Exc'. Catch the other exceptions in the body, or remove the `throwsOn` cases.
  throws (e: ParseError inferred)
  opaque
  throwsOn x < 0 {
    ensures e#line == 3
  }
{
  if x == 0 then {
    var a: ArithError := new ArithError;
    throw a
  };
  if x < 0 then {
    var p: ParseError := new ParseError;
    p#line := 3;
    throw p
  };
  r := x
};
#end
