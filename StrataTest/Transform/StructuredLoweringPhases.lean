/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core
import Strata.Transform.LoopInitHoist
import Strata.Transform.StructuredToUnstructured
-- The `#eval`s below run the phases, which needs the compiled code of the
-- modules they are defined in.
meta import Strata.Languages.Core
meta import Strata.Transform.LoopInitHoist
meta import Strata.Transform.StructuredToUnstructured

/-! ## Loop-init-hoist and structured-to-unstructured phases

Runs `Core.LoopInitHoist.loopInitHoistPipelinePhase` and
`Core.StructuredToUnstructured.structuredToUnstructuredPipelinePhase` on small
programs. Each run reports the change flag, the facts whose checks accept the
output, and whether every fact the phase claims (its `establishes` facts and
the `preserves` facts that held on the input) is accepted on the output. The
declaration-level paths of each pass (passthrough, call rejection, CFG
rejection, and the lowering's shape-check rejections) are exercised too. -/

open Core

private def guardExpr : Expression.Expr := Transform.createFvar "b"

private def intTy : Expression.Ty := Imperative.HasInt.intTy

/-- Wrap `body` as the single procedure of a program. -/
private def progOf (body : List Statement) : Program :=
  { decls := [.proc { (default : Procedure) with body := .structured body } default] }

/-- Whether the executable check of `f` accepts `p`; facts without a check are
    treated as accepted, since nothing can refute them here. -/
private def accepts (f : ProgramFact) (p : Program) : Bool :=
  match f.check? with
  | some c => c p
  | none => true

/-- The facts whose executable checks accept `p`, on one line. -/
private def factNames (p : Program) : String :=
  ", ".intercalate ((ProgramFact.all.filter fun f =>
    match f.check? with
    | some c => c p
    | none => false).map ProgramFact.name)

/-- Run `phase` on `p` and report its result. -/
private def runPhase (phase : PipelinePhase) (p : Program) : String :=
  match Core.Transform.run p phase.transform with
  | .error e => s!"error: {e}"
  | .ok (changed, q) =>
    let claimed := phase.establishes.facts ++
      phase.preserves.facts.filter (accepts · p)
    s!"changed: {changed}\nfacts: {factNames q}\n\
       claims hold: {claimed.all (accepts · q)}"

/-- A program whose only procedure already has a CFG body. -/
private def cfgProgram : Program :=
  let cfg : Imperative.CFG String (Imperative.DetBlock String Command Expression) :=
    { entry := "entry", blocks := [("entry", { cmds := [], transfer := .finish {} })] }
  { decls := [.proc { (default : Procedure) with body := .cfg cfg } default] }

/-- A loop whose body declares `x`, so the hoist moves the declaration out. -/
private def loopWithInit : Program :=
  progOf [.loop (.det guardExpr) none []
    [Statement.init "x" intTy .nondet {}, Statement.set "x" guardExpr {}] {}]

/-! ### Loop-init hoist -/

/-- info: wellFormedCalls, noCFGBodies, noCalls, noLoopInvariants, noLoopMeasures, uniqueInits, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, exitsCovered, armsHaveObligations -/
#guard_msgs in
#eval IO.println (factNames loopWithInit)

/--
info: changed: true
facts: wellFormedCalls, noCFGBodies, noCalls, noLoopInvariants, noLoopMeasures, uniqueInits, loopBodyNoInits, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, exitsCovered, armsHaveObligations
claims hold: true
-/
#guard_msgs in
#eval IO.println (runPhase LoopInitHoist.loopInitHoistPipelinePhase loopWithInit)

/-! A program without loops is unchanged. -/

/--
info: changed: false
facts: wellFormedCalls, noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, uniqueInits, loopBodyNoInits, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, treeForm, exitsCovered, armsHaveObligations
claims hold: true
-/
#guard_msgs in
#eval IO.println (runPhase LoopInitHoist.loopInitHoistPipelinePhase
  (progOf [Statement.init "x" intTy .nondet {}]))

/-- info: error: loopInitHoist: procedure '_' contains a call; loopInitHoist expects call-free structured bodies. -/
#guard_msgs in
#eval IO.println (runPhase LoopInitHoist.loopInitHoistPipelinePhase
  (progOf [Statement.call "f" [] {}]))

/-- info: error: loopInitHoist: CFG procedure bodies are not supported (procedure '_'); loopInitHoist expects structured bodies. -/
#guard_msgs in
#eval IO.println (runPhase LoopInitHoist.loopInitHoistPipelinePhase
  cfgProgram)

/-! ### Structured-to-unstructured lowering -/

/--
info: changed: true
facts: wellFormedCalls, noCalls, noLoops, noLoopInvariants, noLoopMeasures, uniqueInits, loopBodyNoInits, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, treeForm, exitsCovered, armsHaveObligations
claims hold: true
-/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf [Statement.init "x" intTy .nondet {},
    .loop (.det guardExpr) none [] [Statement.set "x" guardExpr {}] {}]))

/--
info: changed: false
facts: wellFormedCalls, noCFGBodies, noCalls, noLoops, noLoopInvariants, noLoopMeasures, uniqueInits, loopBodyNoInits, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, noInits, treeForm, exitsCovered, armsHaveObligations
claims hold: true
-/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf []))

/-- info: error: structuredToUnstructured: procedure '_' contains a call; structuredToUnstructured expects call-free structured bodies. -/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf [Statement.call "f" [] {}]))

/-- info: error: structuredToUnstructured: procedure '_' already has a CFG body; structuredToUnstructured expects structured bodies. -/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  cfgProgram)

/-! The lowering rejects bodies that fail a shape condition of its correctness
theorem: an `exit` with no enclosing block of that label, duplicate sibling
block labels, a block label shaped like a generated one, and an initialized
name under a reserved prefix. -/

private def assertTrue : Statement := Statement.assert "a" guardExpr {}

/-- info: error: structuredToUnstructured: procedure '_' contains an exit with no enclosing block of that label. -/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf [.exit "nolabel" {}, assertTrue]))

/-- info: error: structuredToUnstructured: procedure '_' has duplicate block labels or a block label ending in '_<digits>'; structuredToUnstructured expects distinct labels that cannot collide with generated ones. -/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf [.block "b" [assertTrue] {}, .block "b" [assertTrue] {}]))

/-- info: error: structuredToUnstructured: procedure '_' has duplicate block labels or a block label ending in '_<digits>'; structuredToUnstructured expects distinct labels that cannot collide with generated ones. -/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf [.block "end$_0" [assertTrue] {}, assertTrue]))

/-- info: error: structuredToUnstructured: procedure '_' initializes a variable whose name starts with a prefix reserved for generated labels. -/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf [Statement.init "loop_measure$x" intTy .nondet {}]))

/-! An `exit` covered by its block, and a label ending in a digit without a
preceding `_`, are accepted. -/

/--
info: changed: true
facts: wellFormedCalls, noCalls, noLoops, noLoopInvariants, noLoopMeasures, uniqueInits, loopBodyNoInits, staticSingleAssignment, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, hasObligationForm, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, noInits, treeForm, exitsCovered, armsHaveObligations
claims hold: true
-/
#guard_msgs in
#eval IO.println (runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase
  (progOf [.block "b1" [.exit "b1" {}, assertTrue] {}, assertTrue]))

/-! ### Hoist then lower

The hoist establishes `loopBodyNoInits`, which the lowering requires. -/

/--
info: changed: true
facts: wellFormedCalls, noCalls, noLoops, noLoopInvariants, noLoopMeasures, uniqueInits, loopBodyNoInits, noBetaRedexes, noPrecondsFromFuncs, noNondetGuards, noProcedureContracts, noPolymorphicProcedures, noPolymorphicFunctions, treeForm, exitsCovered, armsHaveObligations
claims hold: true
-/
#guard_msgs in
#eval IO.println <|
  match Core.Transform.run loopWithInit
      LoopInitHoist.loopInitHoistPipelinePhase.transform with
  | .error e => s!"error: {e}"
  | .ok (_, q) =>
    runPhase StructuredToUnstructured.structuredToUnstructuredPipelinePhase q
