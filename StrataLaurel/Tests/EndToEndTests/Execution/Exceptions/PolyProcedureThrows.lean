/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A polymorphic procedure that also `throws`

Two mechanisms meet here. Monomorphization clones the procedure per instantiation, and
`EliminateExceptions` rewrites its `throws` into a `Result<Val, Err>` encoding. The order matters:
the clone is produced first, so `cloneProcAt` has to substitute the EXCEPTION contract too —
`throwsType`, the name it binds for the thrown value, and any `throwsOn` cases. Miss that, and the
clone keeps a `.TVar T` and the lowering builds `Result<Val, T>` around a type variable that no
longer has a binder.

The cases go up in difficulty by what the `throws` type is made of: a concrete type (the baseline
that always worked), the bare type variable, and a generic composite instantiated at it — the last
of which also has to be SEEDED for monomorphization from the `throws` clause, a position the
collector could easily not walk.

The escape cases are separate because they take a different path. Everything else here wraps the
call in `try`/`catch`, so the exception never leaves the caller. When it escapes into a caller that
declares its own `throws`, the check is a subtype comparison — and it cannot be made at the first
resolution, because at that point the callee's `throws` is still `.TVar T`. So it is deferred and
re-checked after monomorphization. The mismatch case is the soundness guard for that deferral.

Every block but the last marks an `entry`, so the lowered clone is also EXECUTED: the
`try`/`catch` runs, the `Result` encoding is unwrapped concretely, and the normal-path
assertion (or, for the false twin, its failure) is observed by two interpreters as well as by
the verifier. The last block is the exception — it pins a REJECTION, so there is no program to
run; it says so at the block.
-/

/-! ## The `throws` type is CONCRETE

The baseline: no substitution needed in the exception contract, so this pins that adding the
substitution did not break the case that already worked. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite E {}
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: E) opaque ensures r == b#val { r := b#val };

procedure catchesConcreteThrows() returns (out: int)
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  try { out := unbox(bx); assert out == 7 } catch c { out := 0 }
};
#end

/-! ## The `throws` type IS the type variable

`throws (e: T)` at the `int` instantiation has to become `throws (e: int)` in the clone, so the
`Result`'s error side carries a concrete type. If the substitution were skipped, the lowering would
produce a `Result` over a dangling `T`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };

procedure catchesTypeVariableThrows() returns (out: int)
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  try { out := unbox(bx); assert out == 7 } catch c { out := 0 }
};
#end

-- SOUNDNESS twin: the value on the normal path is still the field's, so a false claim about it
-- must fail. Without this, the case above would also pass if the `Result` encoding left the
-- normal-path value unconstrained.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };

procedure catchesTypeVariableThrowsFalse() returns (out: int)
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  try { out := unbox(bx); assert out == 999 } catch c { out := 0 }
//                        ^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A GENERIC COMPOSITE in the `throws` type only

`throws (e: Box<int>)` is the only mention of `Box<int>` in the program, so the monomorphization
seed has to be collected from the `throws` clause. A collector that walked signatures and bodies but
not exception contracts leaves `Box` un-lowered, and re-resolution then reports `'Box' is not
defined` — a confusing error a long way from the omission. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure mayThrow(x: int) returns (r: int) throws (e: Box<int>) opaque ensures r == x { r := x };

procedure catchesGenericCompositeThrows() returns (out: int)
  entry
  opaque
  modifies *
{
  try { out := mayThrow(3); assert out == 3 } catch c { out := 0 }
};
#end

/-! ## The exception ESCAPES into a caller that declares its own `throws`

No `try` around the inner call, so the subtype check between the callee's `throws` and the
caller's is what decides the program. At the first resolution the callee throws `.TVar T`, which
cannot be compared to anything, so the check is deferred; after monomorphization the clone throws
`int` and the caller declares `throws int`, so it passes.

The second case generalizes the deferral: `throws Box<T>` MENTIONS a type variable without being
one, so the deferral test has to recurse into the application. A bare-`.TVar`-only test would
reject this at the first resolution with `'T' is not defined`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };
procedure caller(b: Box<int>) returns (r: int) throws (e: int) opaque ensures r == b#val { r := unbox(b) };

procedure escapesIntoMatchingThrows() returns (out: int)
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  try { out := caller(bx); assert out == 7 } catch c { out := 0 }
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure mayThrow<T>(b: Box<T>) returns (r: T) throws (e: Box<T>) opaque ensures r == b#val { r := b#val };
procedure caller(b: Box<int>) returns (r: int) throws (e: Box<int>) opaque ensures r == b#val { r := mayThrow(b) };

procedure escapesWithAppliedTypeVariable() returns (out: int)
  entry
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  try { out := caller(bx); assert out == 7 } catch c { out := 0 }
};
#end

/-! ## The deferral is not a hole: a MISMATCHED escape is still rejected

Same shape, but the caller declares `throws bool` while the callee throws `T` at `int`. This is the
guard for the whole deferral scheme — deferring the check at the first resolution is only sound if it
actually runs later. Two things are pinned at once: that the program is REJECTED, and that the
rejection is a clean user error rather than the internal-error net firing on a diagnostic that
appeared after re-resolution. If the deferral regressed, this would be rejected too early (before
monomorphization) and the reported type would be `T`; if the exemption for exception contracts
drifted, the kind would flip to `strata-bug`. -/

-- Verification-only: this block pins a REJECTION. The deferred subtype check fires during
-- Laurel→Core ("procedure 'caller' may throw 'int', which is not a subtype of its declared
-- `throws` type 'bool'"), so there is no lowered program for either interpreter to run.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure unbox<T>(b: Box<T>) returns (r: T) throws (e: T) opaque ensures r == b#val { r := b#val };
procedure caller(b: Box<int>) returns (r: int) throws (e: bool) opaque ensures r == b#val { r := unbox(b) };
//                                                                                               ^^^^^^^^ error: may throw 'int', which is not a subtype of its declared `throws` type 'bool'

procedure escapesIntoMismatchedThrows() returns (out: int)
  opaque
  modifies *
{
  var bx: Box<int> := new Box<int>;
  bx#val := 7;
  try { out := caller(bx); assert out == 7 } catch c { out := 0 }
};
#end
