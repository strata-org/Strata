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
    `lay` and of the parameters of `p` and every name of `G`, operator applications on constants
    evaluated under the factory `fac`. -/
@[expose] def ssaLoopFree (fac : Lambda.Factory CoreLParams) (G : IdSet Expression)
    (p : Procedure) (lay : Statements) : Except String (Ren Expression × SOut Expression) :=
  ssaEntry fac G p.paramTys p.entryParams p.oldAliases lay

/-- The SSA phase of one procedure of a guarded program under the factory `fac`: an obligation
    procedure of the same name without parameters. An abstract procedure has no body to check,
    and call elimination has removed every call to it, so it produces no declaration (`none`). -/
@[expose] def ssaProc (fac : Lambda.Factory CoreLParams) (G : IdSet Expression) (q : Procedure) :
    Except String (Option Decl) := do
  match q.body with
  | .cfg _ _ => throw s!"SSA: procedure '{q.header.name.name}' has a CFG body"
  | .structured lay _ =>
    let (_, so) ← ssaLoopFree fac G q lay
    pure (some (Decl.obligationProc q.header.name so.out))
  | .abstract => pure none

/-- **The SSA phase of a program** under the factory `fac`: every procedure through `ssaProc`
    (an abstract procedure dropped), its fresh names avoiding the names of `reserved` and those
    the program declares (one hash set built once); every other declaration kept, in order. -/
@[expose] def ssaProgram (fac : Lambda.Factory CoreLParams) (reserved : List Expression.Ident)
    (mid : Program) : Except String Program := do
  let G := IdSet.ofList (avoidOf [] (reserved ++ declNames mid))
  let decls ← mid.decls.mapM fun d => match d with
    | .proc q _ => ssaProc fac G q
    | d => pure (some d)
  pure { decls := decls.filterMap id }

end -- public section

end WP

open Strata

public section

/-- **The SSA phase of a program** (`Core.WP.ssaProgram`): each guarded procedure becomes an
    obligation procedure of the same name; operator applications on constants are evaluated
    under the factory of the WP pipeline on the program (`Core.wpFactory`), and the names the
    phase introduces avoid the names of the factory's functions and those the program
    declares. -/
def ssaProgramOf (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) : Except Message Program := do
  let factory ← wpFactory moreFns program
  let reserved := factory.toArray.toList.map (·.name)
  match WP.ssaProgram factory reserved program with
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
