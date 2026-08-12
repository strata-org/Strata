/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel
import StrataDDM.Integration.Lean.HashCommands

open StrataTest.Util
open Strata

/-
Minimal generic (polymorphic) datatypes for Laurel. Laurel's surface gains
type-parameter lists on `datatype` (`Option<T>`, `Result<Val, Err>`) and generic
type application in type positions (`Option<int>`), lowering to Strata Core's
already-existing polymorphic datatypes (SMT `(declare-datatype … (par …))`).

Laurel resolution performs the static checks for this surface (type-application
arity, bare/unapplied generic references, a type parameter applied to arguments,
and constructor arguments against their declared field types); type parameters
are resolved through scope like other type names. Type arguments are erased only
in Laurel's subtype/consistency relation (so `Option<int>` relates as `Option`)
and forwarded to Core's polymorphic datatypes, which perform the deep
type-argument check. This unblocks the `Result<Val, Err>` lowering of the
exceptional channel.
-/

-- Single type parameter: construct, test, and destruct a generic `Option`.
#eval testLaurel <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure useOption()
  opaque
{
  var o: Option<int> := Some(42);
  assert Option..isSome(o);
  assert Option..value(o) == 42;
  var n: Option<int> := Nothing();
  assert Option..isNothing(n)
};
#end

-- Two type parameters: the `Result<Val, Err>` shape that exception lowering targets.
-- Exercised here under a distinct name (`Either<A, B>`) to keep it independent of
-- the exception lowering: `EliminateExceptions` injects its own `Result` datatype
-- into any program that uses exceptions, which a user-declared `Result` would
-- collide with.
#eval testLaurel <|
#strata
program Laurel;
datatype Either<A, B> {
  First(a: A),
  Second(b: B)
}
procedure useEither()
  opaque
{
  var ok: Either<int, string> := First(7);
  assert Either..isFirst(ok);
  assert Either..a(ok) == 7;
  var err: Either<int, string> := Second("boom");
  assert Either..isSecond(err);
  assert Either..b(err) == "boom"
};
#end

/-! ### Transitional shim: both datatype arities parse

`parseDatatype` accepts the current 3-argument shape (`name, typeParams,
constructors`) and a legacy 2-argument shape (`name, constructors`), treating the
absent type parameters as none — so a binary built from this grammar still
consumes Ion artifacts emitted by one without type parameters, mirroring
`parseProcedure`'s cross-version shims. `#strata` always emits the 3-arg form, so
the 2-arg shape is synthesized here by dropping the `typeParams` arg from a parsed
datatype op. -/

private def legacyDatatypePgm : StrataDDM.Program :=
#strata
program Laurel;
datatype Color {
  Red(),
  Green()
}
procedure noop() opaque { assert true };
#end

/-- Extract the inner `Laurel.datatype` operation from the first (datatype)
    command in a parsed program. -/
private def datatypeOp (prog : StrataDDM.Program) : Option StrataDDM.Operation := do
  let cmd ← prog.commands[0]?
  match (cmd.args[0]? : Option StrataDDM.Arg) with
  | some (.op dtOp) => some dtOp
  | _ => none

/-- Reproduce the legacy pre-`typeParams` 2-argument datatype shape from the
    current 3-argument op by keeping only `name, constructors` (indices 0, 2);
    the transitional shim upgrades it back by splicing in an absent `typeParams`. -/
private def dropTypeParams (op : StrataDDM.Operation) : StrataDDM.Operation :=
  { op with args := #[0, 2].filterMap (fun i => op.args[i]?) }

-- The legacy 2-arg datatype shape parses without error, yielding a datatype with
-- no type parameters, rather than a "parseDatatype expects datatype" failure.
/-- info: 2-arg parse ok: datatype 'Color' with 0 type params
-/
#guard_msgs in
#eval do
  let some op := datatypeOp legacyDatatypePgm | IO.println "no datatype op"
  let legacy := dropTypeParams op
  match Laurel.TransM.run (Strata.Uri.file "<#strata>") (Laurel.parseDatatype (.op legacy)) with
  | .ok (.Datatype dt) => IO.println s!"{legacy.args.size}-arg parse ok: datatype '{dt.name.text}' with {dt.typeArgs.length} type params"
  | .ok _ => IO.println "parsed, but not a datatype"
  | .error e => IO.println s!"parse error: {e}"

-- Nested type-parameter reference in a constructor argument: `Option<T>` inside
-- `Box<T>`. Exercises the `.Applied` recursion in `resolveHighType` and
-- `translateType` — the inner `T` (a scoped type parameter) lowers to a Core
-- `.ftvar` while the surrounding `Option` lowers to a `.tcons` carrying it.
#eval testLaurel <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
datatype Container<T> {
  Mk(inner: Option<T>)
}
procedure useContainer()
  opaque
{
  var b: Container<int> := Mk(Some(3));
  assert Container..isMk(b)
};
#end

-- A type parameter whose name shadows an in-scope datatype: inside `Foo<Color>`
-- the constructor argument `c: Color` must resolve to the *type parameter* (and
-- lower to a Core `.ftvar`), not the concrete `Color` datatype. If the two passes
-- disagreed on precedence (resolution keeping the marker, translation lowering to
-- the concrete `Color`), the `Foo<int> := Mk(5)` construction would fail Core
-- type-checking (`int` vs `Color`); its success pins the typeParams-first rule.
#eval testLaurel <|
#strata
program Laurel;
datatype Color {
  Red(),
  Green()
}
datatype Foo<Color> {
  Mk(c: Color)
}
procedure useFoo()
  opaque
{
  var f: Foo<int> := Mk(5);
  assert Foo..isMk(f)
};
#end

-- Negative: the type argument itself is *not* checked at resolution — a
-- polymorphic `value: T` slot accepts any argument, so `Some(true)` type-checks
-- against both `Option<int>` and `Option<bool>` here. Core is the only thing that
-- catches the mismatch, which is exactly why it is worth pinning: if a future
-- change stopped forwarding type arguments to Core, this test fails instead of
-- silently accepting an ill-typed program. The pinned wording is Core's
-- (`Impossible to unify (Option int) with (Option bool)`), so it is deliberately
-- matched loosely on the first line.
#eval testLaurel <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure mismatchedTypeArg()
  opaque
{
  var a: Option<int> := Some(true);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: ❌ Type checking error.
  assert Option..isSome(a)
};
#end
