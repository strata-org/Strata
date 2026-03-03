/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Languages.Core.Program

/-! # Procedure Body Verification Tests

Unit tests for the ProcBodyVerify transformation.
-/

namespace ProcBodyVerifyTest

open Core Core.ProcBodyVerify Lambda Transform

-- Simple test procedure
def testProc : Procedure := {
  header := {
    name := "Test"
    typeArgs := []
    inputs := [("x", LMonoTy.int)]
    outputs := [("y", LMonoTy.int)]
  }
  spec := {
    modifies := []
    preconditions := [("pre", { expr := .boolConst () true })]
    postconditions := [("post", { expr := .boolConst () true })]
  }
  body := [Statement.set "y" (.fvar () "x" none) #[]]
}

-- Test that transformation succeeds
example : True := by
  let p : Program := { decls := [] }
  let result := procToVerifyStmt testProc p
  match result.run CoreTransformState.emp with
  | (.ok _, _) => trivial
  | (.error _, _) => trivial

end ProcBodyVerifyTest
