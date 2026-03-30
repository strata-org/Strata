/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Type Operation Tests

Tests for IsType, AsType, and ReferenceEquals — all programmatic AST
since these constructs have no concrete syntax.
-/

namespace Strata.Laurel.ConcreteEval.TypeOpsTest

open Strata.Laurel.ConcreteEval.TestHelper
open Strata.Laurel

/-! ## Test 1: IsType — correct type → true

Allocate a Point object, check `IsType target "Point"`.
-/

#guard
  let body := StmtExpr.Block [
    mk (.LocalVariable "p" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.Return (some (mk (.IsType (mk (.Identifier "p")) ⟨.UserDefined "Point", emd⟩))))
  ] none
  let pointType : TypeDefinition := .Composite {
    name := "Point", extending := [], fields := [], instanceProcedures := []
  }
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := [], types := [pointType], constants := []
  }
  getOutcome (interpProgram prog) = some (.vBool true)

/-! ## Test 2: IsType — wrong type → false

Allocate a Point object, check `IsType target "Box"`.
-/

#guard
  let body := StmtExpr.Block [
    mk (.LocalVariable "p" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.Return (some (mk (.IsType (mk (.Identifier "p")) ⟨.UserDefined "Box", emd⟩))))
  ] none
  let pointType : TypeDefinition := .Composite {
    name := "Point", extending := [], fields := [], instanceProcedures := []
  }
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := [], types := [pointType], constants := []
  }
  getOutcome (interpProgram prog) = some (.vBool false)

/-! ## Test 3: AsType — identity cast

`AsType (vRef addr) someType` returns the same `vRef addr`.
-/

#guard
  let body := StmtExpr.Block [
    mk (.LocalVariable "p" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.Return (some (mk (.AsType (mk (.Identifier "p")) ⟨.UserDefined "Point", emd⟩))))
  ] none
  let pointType : TypeDefinition := .Composite {
    name := "Point", extending := [], fields := [], instanceProcedures := []
  }
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := [], types := [pointType], constants := []
  }
  -- AsType returns the value unchanged; the ref address is 0 (first allocation)
  getOutcome (interpProgram prog) = some (.vRef 0)

/-! ## Test 4: ReferenceEquals — same object → true, different objects → false -/

#guard
  let body := StmtExpr.Block [
    mk (.LocalVariable "a" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.LocalVariable "b" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    -- same ref: a === a → true
    mk (.Return (some (mk (.ReferenceEquals (mk (.Identifier "a")) (mk (.Identifier "a"))))))
  ] none
  let pointType : TypeDefinition := .Composite {
    name := "Point", extending := [], fields := [], instanceProcedures := []
  }
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := [], types := [pointType], constants := []
  }
  getOutcome (interpProgram prog) = some (.vBool true)

-- different refs: a === b → false
#guard
  let body := StmtExpr.Block [
    mk (.LocalVariable "a" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.LocalVariable "b" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.Return (some (mk (.ReferenceEquals (mk (.Identifier "a")) (mk (.Identifier "b"))))))
  ] none
  let pointType : TypeDefinition := .Composite {
    name := "Point", extending := [], fields := [], instanceProcedures := []
  }
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body]
    staticFields := [], types := [pointType], constants := []
  }
  getOutcome (interpProgram prog) = some (.vBool false)

end Strata.Laurel.ConcreteEval.TypeOpsTest
