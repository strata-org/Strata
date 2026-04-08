/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.ToOrderedProgram

/-!
# Function Postcondition Check

A Laurel-to-Laurel pass that generates check procedures for function
postconditions. For each function with `ensures` clauses:

1. Generates a `$check` procedure that inlines the function body and
   asserts the postconditions hold.

Postconditions are NOT stripped from the function — they are consumed later by
`toLaurelOrdered` to generate axioms on the `OrderedProgram` IR.

This pass runs after `ConstrainedTypeElim`, which converts constrained return
types into postconditions on `Transparent` bodies.
-/

namespace Strata.Laurel

open Strata

/-- Collected postconditions for a function -/
structure FuncPostconds where
  /-- The function procedure -/
  proc : Procedure
  /-- All postconditions (ensures clauses, including those derived from constrained return types) -/
  postconditions : List StmtExprMd
  /-- The output parameter (result) -/
  resultParam : Parameter
  /-- Whether the function has a body (used to decide if a check procedure is needed) -/
  hasBody : Bool

/-- Collect postconditions from a functional procedure.
    Returns `none` if the procedure has no postconditions or no output parameter. -/
def collectFuncPostconds (proc : Procedure) : Option FuncPostconds :=
  if !proc.isFunctional then none
  else
    let (posts, hasBody) := match proc.body with
      | .Transparent _ posts => (posts, true)
      | .Opaque posts (some _) _ => (posts, true)
      | .Opaque posts none _ => (posts, false)
      | _ => ([], false)
    match proc.outputs.head?, posts.isEmpty with
    | some resultParam, false => some { proc, postconditions := posts, resultParam, hasBody }
    | _, _ => none

/-- Generate a check procedure that inlines the function body and asserts the postconditions.
    Returns `none` for functions without a body. -/
def mkCheckProc (fpc : FuncPostconds) : Option Procedure :=
  if !fpc.hasBody then none
  else
    let md := fpc.proc.md
    let resultId := mkId "$result"
    let resultType := fpc.resultParam.type
    let initExpr := match fpc.proc.body with
      | .Opaque _ (some impl) _ => impl
      | .Transparent impl _ => impl
      | _ => ⟨.LiteralBool false, md⟩
    let initResult : StmtExprMd := ⟨.LocalVariable resultId resultType (some initExpr), md⟩
    -- Inline postconditions with result substituted by $result
    let substPosts := fpc.postconditions.map (substIdentifier fpc.resultParam.name ⟨.Identifier resultId, md⟩)
    let assertPost : StmtExprMd := ⟨.Assert (conjoin substPosts md), md⟩
    some {
      name := mkId s!"{fpc.proc.name.text}$check"
      inputs := fpc.proc.inputs
      outputs := []
      preconditions := fpc.proc.preconditions
      body := .Transparent ⟨.Block [initResult, assertPost] none, md⟩ []
      isFunctional := false
      decreases := none
      md := md }

/-- Main entry point: generate check procedures for function postconditions.
    Postconditions are left on the original functions for axiom generation
    by `toLaurelOrdered`. -/
public def functionPostcondCheck (program : Program)
    : Program × List DiagnosticModel :=
  let funcPostconds := program.staticProcedures.filterMap collectFuncPostconds
  if funcPostconds.isEmpty then (program, []) else
  let checkProcs := funcPostconds.filterMap mkCheckProc
  ({ program with
    staticProcedures := program.staticProcedures ++ checkProcs }, [])

end Strata.Laurel
