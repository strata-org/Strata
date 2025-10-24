/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.HasInputContext
import Strata.DDM.Integration.Lean.Quote
import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.TaggedRegions

open Lean
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM elabCommand)
open Lean.Elab.Term (TermElab)
open System (FilePath)

open Strata.Integration.Lean

namespace Strata

/--
Declare dialect and add to environment.
-/
def declareDialect (d : Dialect) : CommandElabM Unit := do
  let scope ← getCurrNamespace
  let dialectRelName := Lean.Name.anonymous |>.str d.name
  let dialectFullName := scope ++ dialectRelName
  let env ← getEnv
  if env.contains dialectFullName then
    throwError "Cannot define {dialectRelName}: {dialectFullName} already exists."
  let dialectIdent := Lean.mkScopedIdent scope dialectRelName
  let cmd ← `(command| def $dialectIdent := $(quote d))
  tryCatch (elabCommand cmd) fun _ =>
    panic! "Elab command failed: {e}"
  modifyEnv fun env =>
    dialectExt.modifyState env (·.addDialect! d (isNew := true))

declare_tagged_region command strataDialectCommand "#dialect" "#end"

@[command_elab strataDialectCommand]
def strataDialectImpl: Lean.Elab.Command.CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← getInputContext
  let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
  let (_, d, s) ← Strata.Elab.elabDialect {} loaded inputCtx p e
  if !s.errors.isEmpty then
    for e in s.errors do
      logMessage e
    return
  -- Add dialect to command environment
  declareDialect d

declare_tagged_region term strataProgram "#strata" "#end"

 @[term_elab strataProgram]
def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← (getInputContext : CoreM _)
  let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Elab.elabProgram loaded leanEnv inputCtx p e with
  | .ok pgm =>
    return toExpr pgm
  | .error errors =>
    for e in errors do
      logMessage e
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr Program) (toExpr true)

syntax (name := loadDialectCommand) "#load_dialect" str : command

@[command_elab loadDialectCommand]
def loadDialectImpl: CommandElab := fun (stx : Syntax) => do
  match stx with
  | `(command|#load_dialect $pathStx) =>
    let dialectPath : FilePath := pathStx.getString
    let absPath ← resolveLeanRelPath dialectPath
    if ! (←absPath.pathExists) then
      throwError "Could not find file {dialectPath}"
    let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
    let (_, r) ← Elab.loadDialectFromPath {} loaded #[]
                        (path := dialectPath) (actualPath := absPath) (expected := .none)
    -- Add dialect to command environment
    match r with
    | .ok d =>
        declareDialect d
    | .error errorMessages =>
      assert! errorMessages.size > 0
      throwError (← Elab.mkErrorReport errorMessages)
  | _ =>
    throwUnsupportedSyntax

end Strata
