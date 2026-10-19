/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation
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
#eval testLaurelVerification <|
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
#eval testLaurelVerification <|
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
#eval testLaurelVerification <|
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
#eval testLaurelVerification <|
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

-- A generic datatype constructor passed straight to a polymorphic procedure. `ContractPass`
-- gives the call's argument a temp whose type it asks `computeExprType` for, so the constructor
-- call has to report `Option<int>` and not the bare `Option` head — a bare head is re-resolved
-- after the pass and rejected as an unapplied generic datatype.
#eval testLaurelVerification <|
#strata
program Laurel;
datatype Option<T> {
  Nothing(),
  Some(value: T)
}
procedure consume<T>(x: T) returns (r: int)
  requires true
  opaque;
procedure useConsume()
  opaque
{
  var r: int := consume(Some(1));
  assert r == r
};
#end

-- Negative: the mismatched type argument is caught at RESOLUTION. The polymorphic `value: T`
-- slot still accepts any argument, but the argument determines the instantiation, so `Some(true)`
-- is an `Option<bool>` and the `Option<int>` binding rejects it — with a Laurel diagnostic naming
-- both types, rather than Core's `Impossible to unify (Option int) with (Option bool)`.
--
-- This program is rejected before Core translation, so Core forwarding of a generic datatype is
-- pinned by the resolving generic-datatype cases in `Execution/Types/GenericDatatypes.lean`.
#eval testLaurelVerification <|
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
//                      ^^^^^^^^^^ error: expected 'Option<int>', got 'Option<bool>'
  assert Option..isSome(a)
};
#end

/-! ## Equality between whole datatype values

`Execution/Types/GenericDatatypes.lean` deliberately reads payloads back with SELECTORS and
compares at a primitive type, because that is what the concrete interpreter can check.
Equality between two whole datatype values is a different obligation — it goes to the SMT
datatype theory rather than through a selector — so it is pinned here, on the verification
path, with a false twin per shape so the equality cannot be passing on an unconstrained
value. -/

#eval testLaurelVerification <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }

// Two separately constructed values with the same payload are equal.
procedure equalPayloads()
  opaque
{
  var b1: Bx<int> := MkBx(5);
  var b2: Bx<int> := MkBx(5);
  assert b1 == b2
};

// ONE parametric declaration used at two instantiations — there is no per-instantiation
// clone, so each value has to equal its own reconstruction without the other's equality
// leaking in.
procedure equalityAtTwoInstantiations()
  opaque
{
  var bi: Bx<int> := MkBx(5);
  var bb: Bx<bool> := MkBx(true);
  assert bi == MkBx(5) && bb == MkBx(true)
};
#end

-- SOUNDNESS twin: values with DIFFERENT payloads must not be equal. Without this,
-- `equalPayloads` would also pass if datatype equality were trivially true.
#eval testLaurelVerification <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }

procedure distinctPayloadsNotEqual()
  opaque
{
  var b1: Bx<int> := MkBx(5);
  var b2: Bx<int> := MkBx(6);
  assert b1 == b2
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A RECURSIVE generic datatype compared by equality rather than walked with selectors:
-- the whole spine has to be constrained, not just the head the selector reads.
#eval testLaurelVerification <|
#strata
program Laurel;
datatype Lst<T> { Nil(), Cons(head: T, tail: Lst<T>) }

procedure recursiveEquality()
  opaque
{
  var xs: Lst<int> := Cons(1, Nil());
  assert xs == Cons(1, Nil())
};
#end

-- SOUNDNESS twin for the recursive spine: a wrong head must make the equality fail.
#eval testLaurelVerification <|
#strata
program Laurel;
datatype Lst<T> { Nil(), Cons(head: T, tail: Lst<T>) }

procedure recursiveEqualityFalse()
  opaque
{
  var xs: Lst<int> := Cons(1, Nil());
  assert xs == Cons(2, Nil())
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A datatype with NO type parameters still works now that the grammar takes an optional
-- type-parameter list: the absent list must read as "none", not as a parse failure or an
-- empty application.
#eval testLaurelVerification <|
#strata
program Laurel;
datatype Pr { MkPr(a: int, b: int) }

procedure monomorphicDatatypeUnaffected()
  opaque
{
  var p1: Pr := MkPr(1, 2);
  var p2: Pr := MkPr(1, 2);
  assert p1 == p2
};
#end

/-! ## A generic datatype stored in a composite FIELD

A field whose type is a generic application routes through `HeapParameterization`'s box
wrapper via its `.Applied` arm, which emits one box variant per instantiation. So the
write/read round-trip below is checking the box naming as much as the datatype: two
instantiations used as two fields must get two distinct variants, or one field's write
would be readable through the other. -/

#eval testLaurelVerification <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }
composite Holder { var b: Bx<int> }

procedure datatypeFieldRoundTrip()
  opaque
  modifies *
{
  var h: Holder := new Holder;
  var x: Bx<int> := MkBx(9);
  h#b := x;
  var y: Bx<int> := h#b;
  assert y == x
};
#end

-- SOUNDNESS twin: the value read back is the one written, not an unconstrained box.
#eval testLaurelVerification <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }
composite Holder { var b: Bx<int> }

procedure datatypeFieldRoundTripFalse()
  opaque
  modifies *
{
  var h: Holder := new Holder;
  var x: Bx<int> := MkBx(9);
  var z: Bx<int> := MkBx(8);
  h#b := x;
  var y: Bx<int> := h#b;
  assert y == z
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Two instantiations of one generic datatype as two fields of one composite: each gets its
-- own box variant, so writing the `bool` field cannot disturb the `int` one.
#eval testLaurelVerification <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }
composite Holder { var bi: Bx<int>
 var bb: Bx<bool> }

procedure twoInstantiationsAsFields()
  opaque
  modifies *
{
  var h: Holder := new Holder;
  h#bi := MkBx(1);
  h#bb := MkBx(true);
  var yi: Bx<int> := h#bi;
  assert yi == MkBx(1)
};
#end
