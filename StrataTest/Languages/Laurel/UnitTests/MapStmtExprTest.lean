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
-- Assert, Assume, Forall, Exists, LiteralInt, LiteralBool, Identifier.

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
    (.Applied ⟨.UserDefined (mkId "Box"), default⟩ [⟨.UserDefined (mkId "int32"), default⟩])
  == .Applied ⟨.UserDefined (mkId "Box"), default⟩ [⟨.TInt, default⟩]

-- `Box (Wrap int32)` -> `Box (Wrap int)`: recursion through two `.Applied` layers.
#guard HighType.mapType lowerInt32
    (.Applied ⟨.UserDefined (mkId "Box"), default⟩
      [⟨.Applied ⟨.UserDefined (mkId "Wrap"), default⟩ [⟨.UserDefined (mkId "int32"), default⟩], default⟩])
  == .Applied ⟨.UserDefined (mkId "Box"), default⟩
      [⟨.Applied ⟨.UserDefined (mkId "Wrap"), default⟩ [⟨.TInt, default⟩], default⟩]

-- `Set int32` -> `Set int`: recursion through `.TSet`'s element type.
#guard HighType.mapType lowerInt32 (.TSet ⟨.UserDefined (mkId "int32"), default⟩)
  == HighType.TSet ⟨.TInt, default⟩

-- `TotalMap int32 string` -> `TotalMap int string`: recursion through `.TMap`'s key and
-- value types (the non-constrained value type is untouched). Also covered
-- end-to-end by `ConstrainedTypes/ConstrainedDatatypeField.lean`.
#guard HighType.mapType lowerInt32
    (.TMap ⟨.UserDefined (mkId "int32"), default⟩ ⟨.TString, default⟩)
  == HighType.TMap ⟨.TInt, default⟩ ⟨.TString, default⟩

-- `int32 & T` -> `int & T`: recursion through `.Intersection`'s components;
-- the non-constrained component is untouched.
#guard HighType.mapType lowerInt32
    (.Intersection [⟨.UserDefined (mkId "int32"), default⟩, ⟨.UserDefined (mkId "T"), default⟩])
  == HighType.Intersection [⟨.TInt, default⟩, ⟨.UserDefined (mkId "T"), default⟩]

-- `(int32, bool)` -> `(int, bool)`: recursion through `.MultiValuedExpr`'s
-- components; the non-constrained component is untouched.
#guard HighType.mapType lowerInt32
    (.MultiValuedExpr [⟨.UserDefined (mkId "int32"), default⟩, ⟨.TBool, default⟩])
  == HighType.MultiValuedExpr [⟨.TInt, default⟩, ⟨.TBool, default⟩]

end MapTypeCoverage

section ProcedureTraversalCoverage

private def testMd (expr : StmtExpr) : StmtExprMd := ⟨expr, default⟩
private def taggedType (name : String) : HighTypeMd :=
  ⟨.UserDefined (mkId name), default⟩

private def specificationFixture : Procedure :=
  { name := mkId "specificationFixture"
    inputs := []
    outputs := []
    preconditions := [{ condition := testMd (.LiteralInt 1) }]
    decreases := some (testMd (.LiteralInt 2))
    invokeOn := some (testMd (.LiteralInt 3))
    axioms := [testMd (.LiteralInt 4)]
    body := .Transparent (testMd (.LiteralInt 5)) }

private def literalIntValue (expr : StmtExprMd) : Option Int :=
  match expr.val with
  | .LiteralInt value => some value
  | _ => none

#guard (procedureSpecificationExprs specificationFixture).map literalIntValue ==
  [some 1, some 2, some 3, some 4]

private def incrementLiteral (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .LiteralInt value => { expr with val := .LiteralInt (value + 10) }
  | _ => expr

private def mappedSpecificationFixture : Procedure :=
  mapProcedureSpecificationsM (m := Id) incrementLiteral specificationFixture

#guard (procedureSpecificationExprs mappedSpecificationFixture).map literalIntValue ==
  [some 11, some 12, some 13, some 14]
#guard match mappedSpecificationFixture.body with
  | .Transparent body => literalIntValue body == some 5
  | _ => false

private def procedureExpressionOrder (proc : Procedure) : List Int :=
  let visit (expr : StmtExprMd) : StateM (List Int) Unit :=
    match expr.val with
    | .LiteralInt value => modify (· ++ [value])
    | _ => pure ()
  (foldProcedureExprsM visit proc).run [] |>.2

private def withSpecifications (body : Body) : Procedure :=
  { name := mkId "wholeProcedure"
    inputs := []
    outputs := []
    preconditions := [{ condition := testMd (.LiteralInt 5) }]
    decreases := some (testMd (.LiteralInt 6))
    invokeOn := some (testMd (.LiteralInt 7))
    axioms := [testMd (.LiteralInt 8)]
    body }

#guard procedureExpressionOrder
    (withSpecifications (.Transparent (testMd (.LiteralInt 1)))) ==
  [1, 5, 6, 7, 8]

#guard procedureExpressionOrder
    (withSpecifications (.Opaque
      [{ condition := testMd (.LiteralInt 1) }]
      (some (testMd (.LiteralInt 2)))
      [{ targets := [testMd (.LiteralInt 3), testMd (.LiteralInt 4)] }])) ==
  [1, 2, 3, 4, 5, 6, 7, 8]

#guard procedureExpressionOrder
    (withSpecifications (.Abstract [{ condition := testMd (.LiteralInt 1) }])) ==
  [1, 5, 6, 7, 8]

#guard procedureExpressionOrder (withSpecifications .External) ==
  [5, 6, 7, 8]

private def highTypeOrderFixture : Procedure :=
  { name := mkId "highTypeOrder"
    inputs := [{ name := mkId "input", type := taggedType "input" }]
    outputs := [{ name := mkId "output", type := taggedType "output" }]
    preconditions := [{ condition := testMd (.IsType (testMd (.LiteralInt 0)) (taggedType "pre")) }]
    decreases := some (testMd (.IsType (testMd (.LiteralInt 0)) (taggedType "decreases")))
    invokeOn := some (testMd (.IsType (testMd (.LiteralInt 0)) (taggedType "invokeOn")))
    axioms := [testMd (.IsType (testMd (.LiteralInt 0)) (taggedType "axiom"))]
    body := .Transparent (testMd (.AsType (testMd (.LiteralInt 0)) (taggedType "body"))) }

private def highTypeTraversalOrder : List String :=
  let visit (type : HighTypeMd) : StateM (List String) HighTypeMd := do
    let name := match type.val with
      | .UserDefined id => id.text
      | _ => "unexpected"
    modify (· ++ [name])
    pure type
  (mapProcedureHighTypesM visit highTypeOrderFixture).run [] |>.2

#guard highTypeTraversalOrder ==
  ["body", "input", "output", "pre", "decreases", "invokeOn", "axiom"]

end ProcedureTraversalCoverage

section ResultUseCoverage

private def resultCall (name : String) : StmtExprMd :=
  ⟨.StaticCall (mkId name) [], default⟩

private def exposeResultUsed (used : Bool) (node : StmtExprMd) : StmtExprMd :=
  match node.val with
  | .StaticCall _ _ => ⟨.LiteralBool used, node.source⟩
  | _ => node

private def assignedOperandIsIgnored : Bool :=
  match (mapStmtExprUsed exposeResultUsed true
      ⟨.Assigned (resultCall "ignored"), default⟩).val with
  | .Assigned ⟨.LiteralBool false, _⟩ => true
  | _ => false

#guard assignedOperandIsIgnored

private def proveByProofIsIgnored : Bool :=
  match (mapStmtExprUsed exposeResultUsed true
      ⟨.ProveBy (resultCall "value") (resultCall "proof"), default⟩).val with
  | .ProveBy ⟨.LiteralBool true, _⟩ ⟨.LiteralBool false, _⟩ => true
  | _ => false

#guard proveByProofIsIgnored

private def exposeFlattenResultUsed (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExprFlattenM (m := Id)
    (fun _ _ => none)
    (fun used node => [exposeResultUsed used node]) true expr

private def flattenAssignedOperandIsIgnored : Bool :=
  match (exposeFlattenResultUsed ⟨.Assigned (resultCall "ignored"), default⟩).val with
  | .Assigned ⟨.LiteralBool false, _⟩ => true
  | _ => false

#guard flattenAssignedOperandIsIgnored

private def flattenProveByProofIsIgnored : Bool :=
  match (exposeFlattenResultUsed
      ⟨.ProveBy (resultCall "value") (resultCall "proof"), default⟩).val with
  | .ProveBy ⟨.LiteralBool true, _⟩ ⟨.LiteralBool false, _⟩ => true
  | _ => false

#guard flattenProveByProofIsIgnored

end ResultUseCoverage

end Strata.Laurel
