/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreProgram
public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.WP.WP

/-! # The WP phase on Core procedures and programs

The WP phase of `Imperative.WP.wpEntry` lifted to Core procedures and programs:

* the check of the syntactic conditions the WP phase relies on (`checkLoopFree`), on the
  contract-wrapped body of a procedure (`Procedure.contractWrapped`);
* the global names the procedures of a program avoid (`programGlobals`);
* the WP phase of a procedure (`wpLoopFree`, `wpProc`: same header, empty contract, the guarded
  program as body) and of a program (`wpProcsProgram`: one guarded procedure per procedure that
  is not an obligation unit, `isObligationUnit`, every other declaration kept), and the
  declaration phase and the WP phase of a program in sequence (`wpProgramWith`);
* the WP phase of a program with the names of a factory's functions reserved
  (`Core.wpProgram`), and the pipeline phase that runs it (`Core.wpPipelinePhase`).

Their properties are in `WPCoreProgramProps.lean`.

Key definitions: `checkLoopFree`, `wpLoopFree`, `wpProcsProgram`, `wpProgramWith`,
`Core.wpPipelinePhase`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Lambda

public section

/-- The syntactic conditions on a loop-free statement list `ss` of the procedure `p` under
    which the WP phase over-approximates it, checked: `ss` reads only variables of
    `p.entryScope`, `ss` is well scoped from `p.entryScope` with its assigned variables
    as locals (`Block.wellScopedB`: no loops, calls or nondeterministic guards, each `init`
    declares a name not in scope, each `set` and each read is of a name in scope), and every
    `exit` of `ss` targets an enclosing block (`Block.checkExitsCoveredByBlocks`). -/
@[expose] def checkLoopFree (p : Procedure) (ss : Statements) : Except String Unit :=
  let pre := s!"WP: procedure '{p.header.name.name}':"
  match (Block.freeVarsH ss).find? (!p.entryScope.contains ·) with
  | some x => throw s!"{pre} '{x.name}' is read but is neither a parameter nor a local in scope"
  | none =>
    if !Block.wellScopedH (Block.assignedVarsH ss) p.entryScope ss then
      throw s!"{pre} not well scoped (a local declared twice in a scope or named as a \
        parameter, or a variable read or assigned outside the scope of its declaration)"
    else if !Block.checkExitsCoveredByBlocks [] ss then
      throw s!"{pre} an 'exit' targets no enclosing block"
    else pure ()

/-- **The WP phase of a loop-free statement list** `ss` of the procedure `p` (for instance
    `p.contractWrapped body`): `ss` passes `checkLoopFree`, then `wpEntry` with the parameter types
    of `p`, the fresh names avoiding every identifier of `ss` and of the parameters of `p` and
    every name of `G` (the program's global names, which the variables of the output must not
    denote). -/
@[expose] def wpLoopFree (G : IdSet Expression) (p : Procedure) (ss : Statements) :
    Except String (WOut Expression) := do
  checkLoopFree p ss
  wpEntry G p.paramTys ss

/-- The WP phase of one procedure: the same header, an empty contract, the guarded program of
    its loop-free statement list as body, the same metadata. -/
@[expose] def wpProc (G : IdSet Expression) (p : Procedure) (md : Imperative.MetaData Expression) :
    Except String Decl := do
  match p.body with
  | .cfg _ => throw s!"WP: procedure '{p.header.name.name}' has a CFG body"
  | .structured body =>
    let w ← wpLoopFree G p (p.contractWrapped body)
    pure (Decl.proc {
        header := p.header,
        spec := { preconditions := [], postconditions := [] },
        body := .structured w.lay } md)

/-- The global names the procedures of `wpProcsProgram reserved program` avoid: the names of
    `reserved` and those `program` declares, kept when they can equal an introduced name
    (`avoidOf`). -/
@[expose] def programGlobals (reserved : List Expression.Ident) (program : Program) :
    List Expression.Ident :=
  avoidOf [] (reserved ++ declNames program)

/-- Is the procedure an obligation unit: no type parameter, no parameter, an empty contract and a
    body that is one `assert` or one `cover` (the shape of `lemmaUnit`)? -/
@[expose] def isObligationUnit (p : Procedure) : Bool :=
  match p.header.typeArgs, p.header.inputs, p.header.outputs, p.spec.preconditions,
      p.spec.postconditions, p.body with
  | [], [], [], [], [], .structured [.cmd (.cmd (.assert _ _ _))]
  | [], [], [], [], [], .structured [.cmd (.cmd (.cover _ _ _))] => true
  | _, _, _, _, _, _ => false

/-- **The WP phase of a program**: every procedure that is not an obligation unit
    (`isObligationUnit`) becomes its guarded procedure (`wpProc`, with the same header); every
    other declaration is kept, in order.  An obligation unit is already an obligation procedure,
    whose free variables are those of a lemma's obligation, not parameters.  The names the
    procedures introduce avoid the names `program` declares (`declNames`) and the names of
    `reserved` (the functions of the factory the obligations are encoded with), as one hash set
    built once. -/
@[expose] def wpProcsProgram (reserved : List Expression.Ident) (program : Program) :
    Except String Program := do
  let G := IdSet.ofList (programGlobals reserved program)
  let decls ← program.decls.mapM fun d => match d with
    | .proc p md => if isObligationUnit p then pure d else wpProc G p md
    | d => pure d
  pure { decls := decls }

/-- The declaration phase of a program (`declObligationsProgramWith`), then its WP phase
    (`wpProcsProgram`). -/
@[expose] def wpProgramWith (reserved : List Expression.Ident) (declProgram : Program)
    (lemmaObls : List (Imperative.ProofObligation Expression)) (program : Program) :
    Except String Program := do
  let mid ← declObligationsProgramWith declProgram lemmaObls program
  wpProcsProgram reserved mid

end -- public section

end WP

open Strata

public section

/-- **The WP phase of a program** (`Core.WP.wpProcsProgram`): each procedure that is not an
    obligation unit becomes a guarded procedure of the same name and header; every other
    declaration is kept.  The names the procedures introduce avoid the names of the factory's
    functions and those the program declares. -/
def wpProgram (program : Program)
    (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default) : Except Message Program := do
  let factory ← Core.Factory.addFactory moreFns
  let reserved := factory.toArray.toList.map (·.name)
  match WP.wpProcsProgram reserved program with
  | .ok p => return p
  | .error e => throw (Message.fromString e)

/-- The WP pipeline phase: each procedure that is not an obligation unit becomes a guarded
    procedure, every other declaration is kept (`--vcgen wp` runs it after
    `declObligationsPipelinePhase`, then `ssaPipelinePhase`). It requires a program without
    calls, since it rejects every call, and bodies whose every `exit` targets an enclosing
    block, which it checks of each procedure again (`WP.checkLoopFree`). It empties every
    contract, emits only guarded-form bodies whose every `ite` arm contains an obligation
    (`Imperative.WP.wpEntry_armsHaveObl`; each obligation unit it keeps is one `assert` or
    `cover`), emits no loop and no `exit`, keeps headers, touches no function and builds only
    annotated variables, literals and `ite`s. -/
def wpPipelinePhase
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) : PipelinePhase :=
  modelPreservingPipelinePhase "wp"
    (requires := factSet![.noCFGBodies, .noCalls, .noLoops, .noNondetGuards, .typeAnnotated,
      .exitsCovered])
    (establishes := factSet![.noProcedureContracts, .treeForm, .armsHaveObligations])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants, .noLoopMeasures,
                         .noPrecondsFromFuncs,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated, .exitsCovered])
    fun prog => do
      let prog' ← Transform.liftDiag
        (Core.wpProgram prog moreFns |>.mapError fun err =>
          { err with message := s!"❌ WP error.\n{err.message}" })
      return (true, prog')

end -- public section

end Core
