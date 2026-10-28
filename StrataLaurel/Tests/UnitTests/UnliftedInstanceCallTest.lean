/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation.LaurelToCoreSchemaPass

/-! Core translation reports an `InstanceCall` in each position it can occupy. The calls are built
directly, since a source program reaches Core translation with one only through a gap in
resolution. -/

open Strata
open Strata.Laurel

private def nn (e : StmtExpr) : StmtExprMd := ⟨e, .unknown⟩

private def target (name : String) : VariableMd := ⟨.Local (mkId name), .unknown⟩

private def call : StmtExprMd := nn (.InstanceCall (nn (.Var (.Local (mkId "c")))) (mkId "m") [])

private def report {α : Type} (m : TranslateM α) : IO Unit := do
  let (_, s) := runTranslateM { model := { nextId := 0, compositeCount := 0, refToDef := {} } } m
  for d in s.diagnostics do
    let kind := if d.kind == MessageKind.strataBug then "strata-bug" else toString d.kind
    IO.println s!"{kind}: {d.message}"

/-- info: strata-bug: instance call bound to a non-instance procedure reached Core translation -/
#guard_msgs in #eval report (translateStmt call)

/-- info: strata-bug: instance call bound to a non-instance procedure reached Core translation -/
#guard_msgs in #eval report (translateStmt (nn (.Assign [target "y"] call)))

/-- info: strata-bug: instance call bound to a non-instance procedure reached Core translation -/
#guard_msgs in #eval report (translateStmt (nn (.Assign [target "a", target "b"] call)))

/-- info: strata-bug: instance call bound to a non-instance procedure reached Core translation -/
#guard_msgs in #eval report (translateExpr call)
