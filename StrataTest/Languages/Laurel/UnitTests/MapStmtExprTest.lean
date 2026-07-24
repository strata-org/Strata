/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the generic `mapStmtExprM` traversal. Verifies that `mapStmtExpr id`
is the identity: applying it to a parsed program produces identical output.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def parseAndResolve (program : StrataDDM.Program) : IO Program := do
  let laurelProgram ← translateLaurel program
  pure (resolve laurelProgram).program

private def printProcs (program : Program) : IO String := do
  let mut out := ""
  for proc in program.staticProcedures do
    let s := toString (Std.Format.pretty (Std.ToFormat.format proc))
    out := out ++ s ++ "\n"
  pure out

/-- Verify `mapStmtExpr id` is the identity by comparing printed output before
    and after the transformation. -/
private def testMapStmtExprId (program : StrataDDM.Program) : IO Unit := do
  let parsed ← parseAndResolve program
  let mapped := mapProgram (mapStmtExpr id) parsed
  let before ← printProcs parsed
  let after ← printProcs mapped
  if before == after then
    IO.println "ok: mapStmtExpr id ≡ id"
  else
    IO.println s!"MISMATCH\nbefore:\n{before}\nafter:\n{after}"

-- Exercises: IfThenElse, Block, Var Declare, While, Return, Assign,
-- PrimitiveOp, Assert, Assume, Forall, Exists, LiteralInt, LiteralBool, Identifier.

/--
info: ok: mapStmtExpr id ≡ id
-/
#guard_msgs in
#eval! testMapStmtExprId
#strata
program Laurel;
procedure test(x: int, b: bool) returns (r: int)
  requires x > 0
  opaque
  ensures r >= 0
{
  var y: int := x;
  if b then {
    y := y + 1
  } else {
    y := y - 1
  };
  while(y > 0)
    invariant y >= 0
  {
    y := y - 1
  };
  assert y == 0;
  assume y >= 0;
  var q: bool := forall(i: int) => i >= 0;
  var p: bool := exists(j: int) => j > 0;
  return y
};
#end


-- Direct coverage for `HighType.mapType`'s recursion — including the
-- `.Applied` branch `ConstrainedTypeElim.resolveBaseType` relies on to lower a
-- constrained type nested inside a generic type application. Laurel has no
-- surface syntax for a generic/`.Applied`-typed datatype field, so it is
-- exercised here at the `HighType` level via the shared combinator; the
-- callback lowers `int32` to `int` (`.TInt`), mirroring `resolveBaseType`'s
-- lookup. The `.TSet`/`.TMap`/`.Intersection`/`.MultiValuedExpr`
-- recursive branches are pinned below (`.TMap` is additionally covered
-- end-to-end by `ConstrainedTypes/ConstrainedDatatypeField.lean`).
section MapTypeCoverage

private def lowerInt32 : HighType → HighType
  | .UserDefined name => if name.text == "int32" then .TInt else .UserDefined name
  | t => t

-- `Box int32` -> `Box int`: the callback fires inside `.Applied`'s type argument;
-- the generic base `Box` is left untouched.
#guard HighType.mapType lowerInt32
    (.Applied ⟨.UserDefined (mkId "Box"), none⟩ [⟨.UserDefined (mkId "int32"), none⟩])
  == .Applied ⟨.UserDefined (mkId "Box"), none⟩ [⟨.TInt, none⟩]

-- `Box (Wrap int32)` -> `Box (Wrap int)`: recursion through two `.Applied` layers.
#guard HighType.mapType lowerInt32
    (.Applied ⟨.UserDefined (mkId "Box"), none⟩
      [⟨.Applied ⟨.UserDefined (mkId "Wrap"), none⟩ [⟨.UserDefined (mkId "int32"), none⟩], none⟩])
  == .Applied ⟨.UserDefined (mkId "Box"), none⟩
      [⟨.Applied ⟨.UserDefined (mkId "Wrap"), none⟩ [⟨.TInt, none⟩], none⟩]

-- `Set int32` -> `Set int`: recursion through `.TSet`'s element type.
#guard HighType.mapType lowerInt32 (.TSet ⟨.UserDefined (mkId "int32"), none⟩)
  == HighType.TSet ⟨.TInt, none⟩

-- `Map int32 string` -> `Map int string`: recursion through `.TMap`'s key and
-- value types (the non-constrained value type is untouched). Also covered
-- end-to-end by `ConstrainedTypes/ConstrainedDatatypeField.lean`.
#guard HighType.mapType lowerInt32
    (.TMap ⟨.UserDefined (mkId "int32"), none⟩ ⟨.TString, none⟩)
  == HighType.TMap ⟨.TInt, none⟩ ⟨.TString, none⟩

-- `int32 & T` -> `int & T`: recursion through `.Intersection`'s components;
-- the non-constrained component is untouched.
#guard HighType.mapType lowerInt32
    (.Intersection [⟨.UserDefined (mkId "int32"), none⟩, ⟨.UserDefined (mkId "T"), none⟩])
  == HighType.Intersection [⟨.TInt, none⟩, ⟨.UserDefined (mkId "T"), none⟩]

-- `(int32, bool)` -> `(int, bool)`: recursion through `.MultiValuedExpr`'s
-- components; the non-constrained component is untouched.
#guard HighType.mapType lowerInt32
    (.MultiValuedExpr [⟨.UserDefined (mkId "int32"), none⟩, ⟨.TBool, none⟩])
  == HighType.MultiValuedExpr [⟨.TInt, none⟩, ⟨.TBool, none⟩]

end MapTypeCoverage


end Strata.Laurel
