/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreProgram
public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.SSA.SSA

/-! # The SSA phase on Core procedures and programs

The SSA phase of `Imperative.WP.ssaEntry` lifted to Core procedures and programs: the SSA phase
of a procedure (`ssaLoopFree`, `ssaProc`: every parameter of `Procedure.entryParams` to a fresh
name, and every `old x` of `Procedure.oldAliases` to the entry name of `x`) and of a program
(`ssaProgram`), the SSA phase of a program with the names of a factory's functions reserved
(`Core.ssaProgramOf`), and the pipeline phase that runs it (`Core.ssaPipelinePhase`).

Key definitions: `ssaLoopFree`, `ssaProgram`, `Core.ssaPipelinePhase`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Lambda

public section

/-- **The SSA phase of a guarded statement list** `lay` of the procedure `p`: `ssaEntry` with the
    parameter types of `p`, its parameters (`Procedure.entryParams`) and the aliases `old x` of
    its in-out parameters (`Procedure.oldAliases`), the fresh names avoiding every identifier of
    `lay` and of the parameters of `p` and every name of `G`. -/
@[expose] def ssaLoopFree (G : IdSet Expression) (p : Procedure) (lay : Statements) :
    Except String (Ren Expression × SOut Expression) :=
  ssaEntry G p.paramTys p.entryParams p.oldAliases lay

/-- The SSA phase of one procedure of a guarded program: an obligation procedure of the same name
    without parameters. -/
@[expose] def ssaProc (G : IdSet Expression) (q : Procedure) : Except String Decl := do
  match q.body with
  | .cfg _ => throw s!"SSA: procedure '{q.header.name.name}' has a CFG body"
  | .structured lay =>
    let (_, so) ← ssaLoopFree G q lay
    pure (Decl.obligationProc q.header.name so.out)

/-- **The SSA phase of a program**: every procedure through `ssaProc`, its fresh names avoiding
    the names of `reserved` and those the program declares (one hash set built once); every
    other declaration kept, in order. -/
@[expose] def ssaProgram (reserved : List Expression.Ident) (mid : Program) :
    Except String Program := do
  let G := IdSet.ofList (avoidOf [] (reserved ++ declNames mid))
  let decls ← mid.decls.mapM fun d => match d with
    | .proc q _ => ssaProc G q
    | d => pure d
  pure { decls := decls }

end -- public section

end WP

open Strata

public section

/-- **The SSA phase of a program** (`Core.WP.ssaProgram`): each guarded procedure becomes an
    obligation procedure of the same name; the names it introduces avoid the names of the
    factory's functions and those the program declares. -/
def ssaProgramOf (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) : Except Message Program := do
  let factory ← Core.Factory.addFactory moreFns
  let reserved := factory.toArray.toList.map (·.name)
  match WP.ssaProgram reserved program with
  | .ok p => return p
  | .error e => throw (Message.fromString e)

/-- The SSA pipeline phase: each guarded procedure becomes an obligation procedure. It emits
    only `init`, `assume`, `assert`, `cover` and `ite *`, and no `set`; it drops the
    procedures' specifications, so it requires none. The obligation program declares its
    variables in place, so it does not establish `noInits`, and `commonSubexprElim`, which
    requires `noInits`, cannot follow it. It requires every `ite` arm to contain an obligation:
    it drops an arm without one and inlines the other arm, so a run through the dropped arm
    would be replayed by running the other arm's definitions. It keeps every obligation and
    emits an `ite *` only when both arms are nonempty, so its output keeps that fact. -/
def ssaPipelinePhase
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : PipelinePhase :=
  modelPreservingPipelinePhase "ssa"
    (requires := factSet![.noCFGBodies, .noProcedureContracts, .typeAnnotated, .treeForm,
      .armsHaveObligations])
    (establishes := factSet![.staticSingleAssignment, .hasObligationForm])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .noPrecondsFromFuncs, .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated, .exitsCovered,
                         .armsHaveObligations])
    fun prog => do
      let prog' ← Transform.liftDiag
        (Core.ssaProgramOf prog moreFns |>.mapError fun err =>
          { err with message := s!"❌ SSA error.\n{err.message}" })
      return (true, prog')

end -- public section

end Core
