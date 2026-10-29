/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation.LaurelCompilationPipeline

namespace Strata.Laurel

private def dropping (names : List String) : List String :=
  defaultPassNames.filter (!names.contains ·)

private def swapping (a b : String) : List String :=
  defaultPassNames.map fun n => if n == a then b else if n == b then a else n

private def movingAfter (name anchor : String) : List String :=
  (defaultPassNames.filter (· != name)).flatMap fun n => if n == anchor then [n, name] else [n]

private def report (r : Except String (List String)) : IO Unit :=
  match r with
  | .ok _ => IO.println "composes"
  | .error msg => IO.println msg

private def emptyProgram : LaurelProgram := { staticProcedures := [], staticFields := [], types := [] }

private def aliasProgram : LaurelProgram :=
  { staticProcedures := [
      { name := mkId "test", inputs := [{ name := mkId "x", type := ⟨.UserDefined (mkId "A"), default⟩ }],
        outputs := [{ name := mkId "r", type := ⟨.TInt, default⟩ }], preconditions := [], decreases := none,
        body := .Transparent ⟨.Return (some ⟨.Var (.Local (mkId "x")), default⟩), default⟩ }]
    staticFields := []
    types := [.Alias { name := mkId "A", target := ⟨.TInt, default⟩ }] }

private def holeProgram (deterministic : Bool) : LaurelProgram :=
  { staticProcedures := [
      { name := mkId "test", inputs := [], outputs := [{ name := mkId "r", type := ⟨.TInt, default⟩ }],
        preconditions := [], decreases := none,
        body := .Opaque [] (some ⟨.Assign [⟨.Local (mkId "r"), default⟩] ⟨.Hole deterministic none, default⟩, default⟩) [] }]
    staticFields := []
    types := [] }

private def coroutineProgram : LaurelProgram :=
  { staticProcedures := [
      { name := mkId "c", inputs := [], outputs := [], preconditions := [], decreases := none,
        contracts := .Coroutine [] [{ condition := ⟨.LiteralBool false, default⟩ }] [] [],
        body := .Opaque [] (some ⟨.Block [⟨.Assert ⟨.LiteralBool true, default⟩ none, default⟩] none, default⟩) [] }]
    staticFields := []
    types := [] }

private def translated (passes : Option (List String)) (p : LaurelProgram) : IO Unit := do
  let (core, diags) ← translate { passes } p
  IO.println s!"{core.isSome} {diags.map (·.message)}"

/-- info: true -/
#guard_msgs in
#eval IO.println ((checkPassSelection defaultPassNames).toOption ==
  some (laurelPipeline.toList.map (·.name)))

/-- info: true -/
#guard_msgs in
#eval IO.println ((checkPassSelection (swapping "PushOldInward" "InferHoleTypes")).toOption ==
  some ((laurelPipeline.toList.map (·.name)).map fun n =>
    if n == "PushOldInward" then "InferHoleTypes" else if n == "InferHoleTypes" then "PushOldInward" else n))

/-- info: composes -/
#guard_msgs in
#eval report (checkPassSelection (dropping ["EliminateDoWhile"]))

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 22 'Contracts' does not support Pseudo.overload, which is still present when it runs. 'UniqueOverloadNames' removes it; insert it before position 22.
  Phase 23 'Transparency' does not support Pseudo.overload, which is still present when it runs. 'UniqueOverloadNames' removes it; insert it before position 23.
-/
#guard_msgs in
#eval report (checkPassSelection (dropping ["UniqueOverloadNames"]))

private def requirements (names : List String) : Except String (List String) :=
  (resolvePassOrder names).map (·.2.map fun r => s!"{r.kind} <- {r.position} {r.pass}")

/-- info: Except.ok [] -/
#guard_msgs in
#eval requirements defaultPassNames

/--
info: Except.ok ["StmtExpr.Hole.type.none <- 15 UniqueOverloadNames", "StmtExpr.Yield <- 25 LaurelToCoreSchema",
 "StmtExpr.Resume <- 25 LaurelToCoreSchema", "StmtExpr.HasNext <- 25 LaurelToCoreSchema",
 "StmtExpr.Hole.deterministic.true <- 25 LaurelToCoreSchema", "Procedure.contracts.Coroutine <- 25 LaurelToCoreSchema",
 "StmtExpr.OldGuarantee <- 25 LaurelToCoreSchema", "StmtExpr.OldRelies <- 25 LaurelToCoreSchema"]
-/
#guard_msgs in
#eval requirements (dropping ["CoroutineElaboration", "YieldElim", "InferHoleTypes",
  "EliminateDeterministicHoles"])

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 22 'Contracts' does not support StmtExpr.Return, which is still present when it runs. 'EliminateReturnStatements' removes it; insert it before position 22.
-/
#guard_msgs in
#eval report (checkPassSelection (dropping ["EliminateReturnStatements"]))

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 28 'LaurelToCoreSchema' does not support Pseudo.needsLoopInvariantChecks, which is still present when it runs. 'LoopInvariantWellFormedness' removes it; insert it before position 28.
-/
#guard_msgs in
#eval report (checkPassSelection (dropping ["LoopInvariantWellFormedness"]))

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 25 'LiftImperativeExpressions' does not support Pseudo.imperativeShortCircuit, which is still present when it runs. 'DesugarShortCircuit' removes it; insert it before position 25.
-/
#guard_msgs in
#eval report (checkPassSelection (dropping ["DesugarShortCircuit"]))

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 2 'LiftInstanceProcedures' does not support Pseudo.needsOverrideRules, which is still present when it runs. 'CheckOverrideRefinement' removes it; insert it before position 2.
-/
#guard_msgs in
#eval report (checkPassSelection (dropping ["CheckOverrideRefinement"]))

#guard NodeKind.Pseudo.needsLoopInvariantChecks.isPseudo
#guard !NodeKind.StmtExpr.Return.isPseudo
#guard laurelPipeline.all fun p => (p.creates ++ p.removes ++ p.unsupported).all
  fun k => k.isPseudo == (NodeKind.name k).startsWith "Pseudo."

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 28 'LaurelToCoreSchema' does not support Pseudo.imperativeFunction, which is still present when it runs. 'FunctionalRewritePass' removes it; insert it before position 28.
-/
#guard_msgs in
#eval report (checkPassSelection (dropping ["FunctionalRewritePass"]))

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 28 'LaurelToCoreSchema' does not support StmtExpr.OldGuarantee, which is still present when it runs. 'YieldElim' removes it; insert it before position 28.
  Phase 28 'LaurelToCoreSchema' does not support StmtExpr.OldRelies, which is still present when it runs. 'YieldElim' removes it; insert it before position 28.
-/
#guard_msgs in
#eval report (checkPassSelection (dropping ["YieldElim"]))

/--
info: This phase order does not satisfy the phases' declarations:
  Phase 22 'Contracts' does not support Pseudo.overload, which is still present when it runs. 'UniqueOverloadNames' at position 23 removes it; move it before position 22.
-/
#guard_msgs in
#eval report (checkPassSelection (movingAfter "UniqueOverloadNames" "Contracts"))

/-- info: Unknown phase name 'Bogus'. See the list. -/
#guard_msgs in
#eval report (checkPassSelection ["Bogus"] (hint := "See the list."))

/--
info: Phase 'HeapParameterization' is named more than once; each phase may be named only once.
-/
#guard_msgs in
#eval report (checkPassSelection (defaultPassNames ++ ["HeapParameterization"]))

/-- info: Phase 'Transparency' always runs and cannot be named. -/
#guard_msgs in
#eval report (checkPassSelection ["Transparency"])

/-- info: Phase 'Ordering' always runs and cannot be named. -/
#guard_msgs in
#eval IO.println (unselectablePassName "Ordering" "")

/-- info: Unknown phase name 'Bogus'. -/
#guard_msgs in
#eval IO.println (unselectablePassName "Bogus" "")

/--
info: Phase 'Contracts' runs before Transparency, so it cannot follow 'InlineLocalVariables', which runs after it.
-/
#guard_msgs in
#eval report (checkPassSelection ["InlineLocalVariables", "Contracts"])

/-- info: false [Unknown phase name 'Bogus'.] -/
#guard_msgs in
#eval translated (some ["Bogus"]) emptyProgram

/-- info: true [] -/
#guard_msgs in
#eval translated (some (swapping "PushOldInward" "InferHoleTypes")) aliasProgram

/--
info: false [The program contains TypeDefinition.Alias, which phase 28 'LaurelToCoreSchema' does not support. 'TypeAliasElim' removes it; insert it before position 28.]
-/
#guard_msgs in
#eval translated (some (dropping ["TypeAliasElim"])) aliasProgram

/-- info: true [] -/
#guard_msgs in
#eval translated (some (dropping ["InferHoleTypes"])) (holeProgram false)

/--
info: false [The program contains StmtExpr.Hole.deterministic.true, which phase 28 'LaurelToCoreSchema' does not support. 'EliminateDeterministicHoles' removes it; insert it before position 28.]
-/
#guard_msgs in
#eval translated (some (dropping ["EliminateDeterministicHoles"])) (holeProgram true)

/-- info: true [] -/
#guard_msgs in
#eval translated (some (dropping ["CoroutineElaboration", "YieldElim", "InferHoleTypes",
  "EliminateDeterministicHoles"])) aliasProgram

/--
info: false [The program contains Procedure.contracts.Coroutine, which phase 27 'LaurelToCoreSchema' does not support. 'CoroutineElaboration' removes it; insert it before position 27.]
-/
#guard_msgs in
#eval translated (some (dropping ["CoroutineElaboration", "YieldElim"])) coroutineProgram

/--
info: false [This phase order does not satisfy the phases' declarations:
  Phase 28 'LaurelToCoreSchema' does not support Pseudo.needsLoopInvariantChecks, which is still present when it runs. 'LoopInvariantWellFormedness' removes it; insert it before position 28.]
-/
#guard_msgs in
#eval translated (some (dropping ["LoopInvariantWellFormedness"])) aliasProgram

end Strata.Laurel
