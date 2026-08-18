/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FunctionInlining
import all Strata.Transform.FunctionInlining
public import Strata.Languages.Core.ProcedureProps
import all Strata.Languages.Core.ProcedureProps

/-! # Properties of the function-inlining transform

Key results:

- `FunctionInlining.mapProgramExprs_id` — the program-level expression mapper
  with the identity is the identity (on top of `Procedure.mapExprs_id`, the
  program-level analog of `Statements.mapExprs_id`).
-/

public section

namespace Core

/-- `FunctionInlining.mapProgramExprs` with the identity is the identity. -/
theorem FunctionInlining.mapProgramExprs_id (pgm : Program) :
    FunctionInlining.mapProgramExprs id pgm = pgm := by
  simp only [FunctionInlining.mapProgramExprs]
  congr 1
  refine Eq.trans (List.map_congr_left ?_) (List.map_id pgm.decls)
  intro d _
  cases d with
  | ax a md => cases a; rfl
  | proc p md =>
    show Decl.proc (Procedure.mapExprs id p) md = id (Decl.proc p md)
    rw [Procedure.mapExprs_id]
    rfl
  | _ => rfl

end Core

end -- public section
